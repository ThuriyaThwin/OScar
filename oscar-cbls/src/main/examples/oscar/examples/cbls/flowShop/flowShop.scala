package oscar.examples.cbls.flowShop

import oscar.cbls.invariants.core.computation.{CBLSSetVar, CBLSIntConst, CBLSIntVar, IntValue}
import oscar.cbls.invariants.lib.logic.SelectLESetQueue
import oscar.cbls.modeling.CBLSModel
import oscar.cbls.objective.Objective
import oscar.cbls.search.move.ShiftMove
import oscar.examples.cbls.flowShop.flowShopShiftRestart._

object flowShop  extends CBLSModel with App {

  val machineToJobToDuration:Array[Array[Int]] =
    Array(
      Array(1,2,1,7,2,5,5,6),
      Array(4,5,3,1,8,3,7,8),
      Array(6,8,2,5,3,1,2,2),
      Array(4,1,7,2,5,5,6,4))

  val nbMachines = 4
  val nbJobs = 7

  val jobs = 0 until nbJobs
  val machines = 0 until nbMachines

  val jobSequence:Array[CBLSIntVar] = Array.tabulate(nbJobs)(p => CBLSIntVar(p,jobs,"jobStartingAtPosition" + p))

  //posting the model
  val MachineToJobToStartingTimes:Array[Array[IntValue]] = Array.fill(nbMachines,nbJobs)(null)

  for(m <- machines){
    for(jPos <- jobs){
      MachineToJobToStartingTimes(m)(jPos) = (m,jPos) match{
        case (0,0) => CBLSIntConst(0)
        case (0,_) => machineToJobToDuration(0).element(jobSequence(jPos-1)) + MachineToJobToStartingTimes(0)(jPos-1)
        case (_ , 0) => machineToJobToDuration(m-1).element(jobSequence(0)) + MachineToJobToStartingTimes(m-1)(0)
        case (_,_) => max2(
          machineToJobToDuration(m).element(jobSequence(jPos-1)) + MachineToJobToStartingTimes(m)(jPos-1),
          machineToJobToDuration(m-1).element(jobSequence(jPos)) + MachineToJobToStartingTimes(m-1)(jPos))
      }
    }
  }

  println("closing model")

  val obj:Objective =
    MachineToJobToStartingTimes(nbMachines-1)(nbJobs-1) + machineToJobToDuration(nbMachines-1).element(jobSequence(nbJobs-1))

  val tabu = Array.tabulate(nbJobs)(j => CBLSIntVar(0,name = "tabu_" + j))
  val it = CBLSIntVar(0,name="it")
  val nonTabu = SelectLESetQueue(tabu,it)
  val tabulength = 2

  s.close()

  val shiftRestart = (shiftNeighborhood(jobSequence)
    onExhaustRestartAfter (shuffleNeighborhood(jobSequence, numberOfShuffledPositions=() => nbJobs/2),5,obj))

  val tabuShift = (shiftNeighborhood(jobSequence, searchZone1 = nonTabu, maxShiftSize = 1, best=true)
    afterMoveOnMove((s:ShiftMove) => {s.shiftedElements.foreach(tabu(_) := it.value + tabulength) ; it:+=1})
    acceptAll()
    maxMoves 10 withoutImprovementOver obj
    saveBestAndRestoreOnExhaust obj)


  val search = shiftRestart //shiftRestart

  search.verbose = 1

  search.doAllMoves(_ => false,obj)
  println(s.stats)
  println("job sequence:" + jobSequence.map(_.value).mkString(","))
  println(obj)

  println("startingTimes:\n" + MachineToJobToStartingTimes.map(_.map(_.value).mkString("\t")).mkString("\n"))
}