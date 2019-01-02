package oscar.examples.cbls.routing

import oscar.cbls._
import oscar.cbls.business.routing._
import oscar.cbls.business.routing.invariants.TimeWindowConstraint
import oscar.cbls.core.objective.CascadingObjective
import oscar.cbls.core.search.{Best, First}

object VRPWithOnlyTimeWindow extends App {

  def runConfiguration(ns: List[Int], vs: List[Int],
                       timeWindowConstraints: List[Boolean],
                       bests: List[Boolean], procedures: List[Int],
                       iterations: Int): Unit ={
    for(twc <- timeWindowConstraints){
      println("================================================")
      println(if(twc) "Using old invariant ..." else "Using new invariant ...")
      for(best <- bests){
        println(if(best) "\n\nStarting best mod !" else "Starting first mod !")
        for(procedure <- procedures){
          procedure match {
            case 1 => println("\nStarting insertPoint procedure")
            case 2 => println("\nStarting insertPoint exhaust onePtMove procedure")
            case 3 => println("\nStarting insertPoint exhaust threeOpt procedure")
          }
          for(n <- ns){
            for(v <- vs){
              println("Run with " + v + " vehicles and " + n + " nodes.")
              val res = List.fill(iterations)(
                procedure match {
                  case 1 => new VRPWithOnlyTimeWindow(twc, n, v).run1(best)
                  case 2 => new VRPWithOnlyTimeWindow(twc, n, v).run2(best)
                  case 3 => new VRPWithOnlyTimeWindow(twc, n, v).run3(best)
                }).
                foldLeft(Array(0,0))((acc,item) =>
                  Array(acc(0) + item._1,acc(1) + item._2)).toList.map(_/iterations)
              println("Average quality : " + res.head + "\nAverage duration : " + res.last + "\n")
            }
          }
        }
      }
    }
  }

  // Add false for global time window constraint and/or true for naive one
  val timeWindowConstraints = List(false, true)
  // Add true if you want to run with Best and/or false if you want to run with First
  val bests = List(false, true)
  // Add the procedures you want (see at the end of this files for more informations)
  val procedures = List(1,2,3)
  // The variations of n values
  val ns = List(100, 500, 1000)
  // The variations of v values
  val vs = List(1,2,5,10)
  // The number of iterations of each configuration
  val iterations = 5
  runConfiguration(ns,vs,timeWindowConstraints,bests, procedures,iterations)
}

class VRPWithOnlyTimeWindow(oldVersion: Boolean, n: Int = 100, v: Int = 10){
  val m = new Store(noCycle = false)
  val penaltyForUnrouted = 10000
  val symmetricDistance = RoutingMatrixGenerator.apply(n)._1
  val travelDurationMatrix = RoutingMatrixGenerator.generateLinearTravelTimeFunction(n,symmetricDistance)
  var (earlylines, deadlines, taskDurations, maxWaitingDurations) = RoutingMatrixGenerator.generateFeasibleTimeWindows(n,v,travelDurationMatrix)
  deadlines = deadlines.take(v).map(x => Math.min(deadlines.drop(v).max*2, Int.MaxValue/10*9)) ++ deadlines.drop(v)

  val myVRP =  new VRP(m,n,v)
  var timeWindowConstraint: Option[TimeWindowConstraint] = None

  // Distance
  val totalRouteLength = constantRoutingDistance(myVRP.routes,n,v,false,symmetricDistance,true,true,false)(0)

  // This class isn't meant to last but given the time left I don't want to modify it.
  // It uses an old representation of time windows with earlylines and deadlines.
  val timeWindowExtension: TimeWindow = timeWindow(earlylines,deadlines,taskDurations,maxWaitingDurations)

  // Defintion of the objective function using naive constraint or global contraint
  val obj: CascadingObjective =
    if(oldVersion){
      // Naive constraint
      val oldTimeWindowInvariant = forwardCumulativeIntegerIntegerDimensionOnVehicle(
        myVRP.routes,n,v,
        (fromNode,toNode,arrivalTimeAtFromNode,leaveTimeAtFromNode)=> {
          val arrivalTimeAtToNode = leaveTimeAtFromNode + travelDurationMatrix.getTravelDuration(fromNode,0,toNode)
          val leaveTimeAtToNode =
            if(toNode < v) 0
            else Math.max(arrivalTimeAtToNode,earlylines(toNode)) + taskDurations(toNode)
          (arrivalTimeAtToNode,leaveTimeAtToNode)
        },
        Array.tabulate(v)(x => new CBLSIntConst(0)),
        Array.tabulate(v)(x => new CBLSIntConst(earlylines(x)+taskDurations(x))),
        0,
        0,
        contentName = "Time at node"
      )
      val constraints = new ConstraintSystem(myVRP.routes.model)
      val arrivalTimes = oldTimeWindowInvariant.content1AtNode
      val leaveTimes = oldTimeWindowInvariant.content2AtNode
      val arrivalTimesAtEnd = oldTimeWindowInvariant.content1AtEnd

      // Verification of violations
      for(i <- 0 until n){
        if(i < v && deadlines(i) != Int.MaxValue) {
          constraints.post(arrivalTimesAtEnd(i).le(deadlines(i)).nameConstraint("end of time for vehicle " + i))
        } else {
          if(deadlines(i) != Int.MaxValue)
            constraints.post(leaveTimes(i).le(deadlines(i)).nameConstraint("end of time window on node " + i))
          if(maxWaitingDurations(i) != Int.MaxValue)
            constraints.post(arrivalTimes(i).ge(earlylines(i)).nameConstraint("start of time window on node (with duration)" + i))
        }
      }

      new CascadingObjective(constraints,
        totalRouteLength + (penaltyForUnrouted*(n - length(myVRP.routes))))
    }
    else{
      // Global constraint
      val violations = Array.fill(v)(new CBLSIntVar(m, 0, Domain.coupleToDomain((0,1))))
      val timeMatrix = Array.tabulate(n)(from => Array.tabulate(n)(to => travelDurationMatrix.getTravelDuration(from, 0, to)))
      val smartTimeWindowInvariant =
        TimeWindowConstraint(myVRP.routes, n, v,
          timeWindowExtension.earlylines,
          timeWindowExtension.deadlines,
          timeWindowExtension.taskDurations,
          timeMatrix, violations)
      timeWindowConstraint = Some(smartTimeWindowInvariant)
      new CascadingObjective(sum(violations),
        totalRouteLength + (penaltyForUnrouted*(n - length(myVRP.routes))))
    }
  m.close()

  // Building the relevant predecessors of each node based on time window
  val relevantPredecessorsOfNodes: Map[Int,Set[Int]] = TimeWindowHelper.relevantPredecessorsOfNodes(myVRP, timeWindowExtension, travelDurationMatrix)

  // A post filter that prevents insertion after unrouted nodes
  def postFilter(node:Int): (Int) => Boolean = {
    (neighbor: Int) => {
      myVRP.isRouted(neighbor)
    }
  }

  // Given the relevant predecessors we sort them by distance
  val closestRelevantPredecessorsByDistance = Array.tabulate(n)(DistanceHelper.lazyClosestPredecessorsOfNode(symmetricDistance,relevantPredecessorsOfNodes(_)))

  // InsertPoint neighborhood
  def insertPoint(best: Boolean) = insertPointUnroutedFirst(
    () => myVRP.unrouted.value,
    ()=> myVRP.kFirst(if (best) n else 20,closestRelevantPredecessorsByDistance, postFilter),
    myVRP,
    selectInsertionPointBehavior = if(best) Best() else First(),
    neighborhoodName = "InsertUF")

  // OnePointMove neighborhood
  def onePtMove(best: Boolean) = onePointMove(
    () => myVRP.routed.value,
    ()=> myVRP.kFirst(if (best) n else 20,closestRelevantPredecessorsByDistance,postFilter),
    myVRP,
    selectDestinationBehavior = if(best) Best() else First(),

    neighborhoodName = "OnePtMove")

  // ThreeOpt neighborhood
  def threeOptMove(best: Boolean) = threeOpt(
    myVRP.routed,
    ()=>myVRP.kFirst(if (best) n else 20,closestRelevantPredecessorsByDistance,postFilter),
    myVRP,
    neighborhoodName = "ThreeOpt(k=" + v*2 + ")",
    selectInsertionPointBehavior = if(best) Best() else First())

  // Simple InsertPoint procedure
  def run1(best: Boolean): (Int,Int) ={
    val search = insertPoint(best)
    val start = System.nanoTime()
    search.doAllMoves(obj=obj)
    val end = System.nanoTime()
    val duration = ((end - start)/1000000).toInt
    (obj.value, duration)
  }

  // Simple InsertPoint exhaust OnePoitnMove procedure
  def run2(best: Boolean): (Int,Int) ={
    val search = insertPoint(best) exhaust onePtMove(best)
    val start = System.nanoTime()
    search.doAllMoves(obj=obj)
    val end = System.nanoTime()
    val duration = ((end - start)/1000000).toInt
    (obj.value, duration)
  }

  // Simple InsertPoint exhaust ThreeOpt procedure
  def run3(best: Boolean): (Int,Int) ={
    val search = insertPoint(best) exhaust threeOptMove(best)
    val start = System.nanoTime()
    search.doAllMoves(obj=obj)
    val end = System.nanoTime()
    val duration = ((end - start)/1000000).toInt
    (obj.value, duration)
  }

}