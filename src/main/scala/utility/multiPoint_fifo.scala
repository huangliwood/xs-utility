package utility_hl

import chipsalliance.rocketchip.config.Parameters
import chisel3._
import chisel3.util._
import utility_hl._
trait hasFifoParameters{
  val entries: Int = 16
  val entriesBits : Int = log2Up(entries)
  val deq_num : Int = 1
  val enq_num : Int = 4
  val beatBytes : Int = 1
  val dataBits : Int = 36
}
class multiPoint_fifo[T<:Data](gen:T,deq_num:Int=1,enq_num:Int=4,dataBits:Int=36,entries:Int=16)(implicit val p: Parameters) extends Module
with hasFifoParameters
with HasCircularQueuePtrHelper {
    val io = IO(new Bundle() {
      val enq = new Bundle() {
        val canAccept = Output(Bool())
        val req = Vec(enq_num, Flipped(DecoupledIO(gen)))
      }
      val deq = Vec(deq_num,DecoupledIO(gen))
    })
    class FIFO_Ptr extends CircularQueuePtr[FIFO_Ptr](entries) with HasCircularQueuePtrHelper {}
  
    // head: first valid entry
    val headPtr = RegInit(VecInit((0 until deq_num).map(_.U.asTypeOf(new FIFO_Ptr))))
    val headPtrOH = RegInit(1.U(entries.W))
    val headPtrOHShift = CircularShift(headPtrOH)
    val headPtrOHVec = VecInit.tabulate(deq_num+1)(headPtrOHShift.left);dontTouch(headPtrOHVec)
    val headPtrNext = Wire(Vec(deq_num, new FIFO_Ptr))
    // tail: first invalid entry
    val tailPtr = RegInit(VecInit((0 until enq_num).map(_.U.asTypeOf(new FIFO_Ptr))))
    val tailPtrOH = RegInit(1.U(entries.W))
    val tailPtrOHShift = CircularShift(tailPtrOH)
    val tailPtrOHVec = VecInit.tabulate(enq_num+1)(tailPtrOHShift.left) //todo: this is important,need a extra bits for selecting

    val allowEnqueue = RegInit(true.B)
    val currentValidCounter = distanceBetween(tailPtr(0), headPtr(0)) //todo can optimize bits?
    val numDeq = Mux(currentValidCounter > deq_num.U, deq_num.U, currentValidCounter)
    val num_acqDeq = PopCount(io.deq.map(_.ready))
    val numEnq = Mux(io.enq.canAccept, PopCount(io.enq.req.map(_.valid)), 0.U)
  
    val enqOffset = VecInit((0 until enq_num).map(i => PopCount(io.enq.req.map(_.valid).take(i))))
    val enqIndexOH = VecInit((0 until enq_num).map(i => tailPtrOHVec(enqOffset(i))))
    dontTouch(enqOffset)
    dontTouch(enqIndexOH)
  
    //  data array
    val dataModule = Module(new SyncDataModuleTemplate(gen, entries, numRead = deq_num, numWrite = enq_num))
    dontTouch(dataModule.io)
    for (i <- 0 until enq_num) {
      dataModule.io.wen(i) := allowEnqueue && io.enq.req(i).valid
      dataModule.io.waddr(i) := tailPtr(enqOffset(i)).value
      for (j <- 0 until beatBytes) {
        dataModule.io.wdata(i) := io.enq.req(i).bits
      }
    }
    for (i <- 0 until enq_num) {
        for(j <- i+1 until enq_num){
            assert(!(dataModule.io.wen(i) && dataModule.io.wen(j) && dataModule.io.waddr(i)===dataModule.io.waddr(j)))
        }
    }
    dataModule.io.raddr := headPtrNext.map(_.value)
    
    val s_invalid :: s_valid :: Nil = Enum(2)
    val stateEntries = RegInit(VecInit(Seq.fill(entries)(s_invalid)));dontTouch(stateEntries)
    val isTrueEmpty = !VecInit(stateEntries.map(_ === s_valid)).asUInt.orR
  

  for (i <- 0 until entries) {
    val enq_updateVec = WireInit(VecInit(io.enq.req.map(_.valid).zip(enqIndexOH).map{ case (v, oh) => v && oh(i) }).asUInt)//todo understand
    dontTouch(enq_updateVec)
    when(enq_updateVec.orR && allowEnqueue) {
      stateEntries(i) := s_valid
    }
  }
  //update pointer enqueue, no matter how many enq pointer, all pointers must be updated
  val update_pointer = io.enq.req.map(_.fire).reduce(_||_)
  for (i <- 0 until enq_num) {
    tailPtr(i) := Mux(update_pointer,tailPtr(i) + numEnq,tailPtr(i))
  }
  tailPtrOH := tailPtrOHVec(numEnq)
  // dequeue
  for (i <- 0 until entries) {
    val deq_updateVec = WireInit(VecInit(io.deq.map(_.fire).zip(headPtrOHVec).map{ case (v, oh) => v && oh(i) }).asUInt)
    dontTouch(deq_updateVec)
    when(deq_updateVec.orR) {
      stateEntries(i) := s_invalid
    }
  }
  val maxDeqNum=Mux(num_acqDeq < numDeq,num_acqDeq,numDeq)
  for (i <- 0 until deq_num) {
    headPtrNext(i) := Mux(io.deq.map(_.fire).reduce(_||_),headPtr(i) + maxDeqNum,headPtr(i))
  }
  headPtr := headPtrNext
  headPtrOH := headPtrOHVec(numDeq)//ParallelPriorityMux(validMask.asUInt, headPtrOHVec)
  
  //set output valid and data bits
  val nextStepData = Wire(Vec(deq_num, gen))
  val ptrMatch = new QPtrMatchMatrix(headPtr, tailPtr)
  val deqNext = Wire(Vec(deq_num, gen))
  deqNext.zipWithIndex.map({ case (d, index) => d := nextStepData(index) }) //ParallelPriorityMux(validMask.asUInt, nextStepData.drop(index).take(deq_num + 1))})//todo:why?
  
  for (i <- 0 until deq_num) {
    io.deq(i).bits:=deqNext(i).asUInt & Fill(deqNext(i).asUInt.getWidth,io.deq(i).fire)
    io.deq(i).valid := Mux1H(headPtrOHVec(i), stateEntries) === s_valid
  }
  io.deq.map(x=>{dontTouch(x.bits)})

  for (i <- 0 until  deq_num) {
    val enqMatchVec = VecInit(ptrMatch(i))
    val enqBypassEnVec = io.enq.req.map(_.valid).zip(enqOffset).map { case (v, o) => v && enqMatchVec(o) }
    val enqBypassEn = io.enq.canAccept && (VecInit(enqBypassEnVec).asUInt.orR)
    val enqBypassData = Mux1H(enqBypassEnVec, io.enq.req.map(_.bits))
    val readData = dataModule.io.rdata(i)
    nextStepData(i) :=readData
  }
  
  allowEnqueue := Mux(currentValidCounter > (entries - enq_num).U, false.B, numEnq <= (entries - enq_num).U - currentValidCounter)
  io.enq.req.foreach(_.ready:=allowEnqueue)
  io.enq.canAccept := allowEnqueue
}
