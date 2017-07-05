package oscar.cbls.test.routing

/*******************************************************************************
  * OscaR is free software: you can redistribute it and/or modify
  * it under the terms of the GNU Lesser General Public License as published by
  * the Free Software Foundation, either version 2.1 of the License, or
  * (at your option) any later version.
  *
  * OscaR is distributed in the hope that it will be useful,
  * but WITHOUT ANY WARRANTY; without even the implied warranty of
  * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
  * GNU Lesser General Public License  for more details.
  *
  * You should have received a copy of the GNU Lesser General Public License along with OscaR.
  * If not, see http://www.gnu.org/licenses/lgpl-3.0.en.html
  ******************************************************************************/

import oscar.cbls.business.routing.model.{ClosestNeighbors, RoutedAndUnrouted, TotalConstantDistance, VRP}
import oscar.cbls.business.routing.neighborhood.{InsertPointRoutedFirst, InsertPointUnroutedFirst, OnePointMove, OnePointMoveMove, ThreeOpt, TwoOpt1, _}
import oscar.cbls.core.computation.{CBLSIntVar, Store}
import oscar.cbls.core.objective.{CascadingObjective, Objective}
import oscar.cbls.core.propagation.ErrorChecker
import oscar.cbls.lib.constraint.LE
import oscar.cbls.lib.invariant.routing.capa.{ForwardCumulativeIntegerDimensionOnVehicle, ForwardCumulativeConstraintOnVehicle}
import oscar.cbls.lib.invariant.routing.{MovingVehicles, RouteSuccessorAndPredecessors}
import oscar.cbls.lib.invariant.seq.Size
import oscar.cbls.lib.search.combinators.{RoundRobin, BestSlopeFirst, Mu, Profile}
import oscar.cbls.modeling.Algebra._

class MySimpleRoutingWithCumulatives(n:Int,v:Int,symmetricDistance:Array[Array[Int]],m:Store, maxPivot:Int, deltaAtNode:Array[Int], maxCapa:Int)
  extends VRP(n,v,m,maxPivot) with TotalConstantDistance with ClosestNeighbors with RoutedAndUnrouted{

  setSymmetricDistanceMatrix(symmetricDistance)

  override protected def getDistance(from : Int, to : Int) : Int = symmetricDistance(from)(to)

  val penaltyForUnrouted  = 10000

  val maxNodes = LE(Size(routes),n-3).violation

  val violation = new CBLSIntVar(routes.model, 0, 0 to Int.MaxValue, "violation of capacity test")

  val contentConstraint = new ForwardCumulativeConstraintOnVehicle(
  routes,
  n,
  v,
  {case (fromNode,toNode,content) => content + deltaAtNode(fromNode)},
  maxCapa,
  Array.tabulate(v)(deltaAtNode),
  violation,
  6)

  val contentAtStart = Array.tabulate(v)(vehicle => CBLSIntVar(m,0,0 to 10,"start content of vehicle " + vehicle))
  //  val cumulative2 = ForwardCumulativeIntegerDimensionOnVehicle(routes,n,v,{case (fromNode,toNode,fromContent) => fromNode+toNode+(2*fromContent)},contentAtStart,-1)

  val obj = new CascadingObjective(
    contentConstraint.violation,
    new CascadingObjective(maxNodes,
      Objective(/*cumulative2._3(1) + cumulative2._2(1) + */ totalDistance + (penaltyForUnrouted*(n - Size(routes))))))


  val closestNeighboursForward = computeClosestNeighborsForward()

  def size = routes.value.size


  val (next,prev) = RouteSuccessorAndPredecessors(routes,v,n)

  val movingVehicles = MovingVehicles(routes,v)

  override def toString : String = super.toString +
    "objective: " + obj.value + "\n" +
    "next: [" + next.map(_.value).mkString(",") + "]" + "\n" +
    "prev: [" + prev.map(_.value).mkString(",") + "]" + "\n" +
    "content: [" + contentConstraint.contentAtNodes.mkString(",") + "]" + "\n" +
    "routed:" + this.routed.value + "\n" +
    "unRouted:" + this.unrouted.value + "\n"
}

object TestCumulatives extends App{

  val n = 30
  val v = 5
  val delta = Array(0,1,1,2,2,3,-3,4,-4,0,0,1,-1,2,-2,3,-3,4,-4,0,0,1,-1,2,-2,3,-3,4,-4,0)
  val maxPivotPerValuePercent = 4
  val maxcapa = 15
  println("VRP(n:" + n + " v:" + v + ")")

  val (symmetricDistanceMatrix,pointsList) = RoutingMatrixGenerator(n)
  //  println("restrictions:" + restrictions)
  val model = new Store(checker = Some(new ErrorChecker()))

  val myVRP = new MySimpleRoutingWithCumulatives(n,v,symmetricDistanceMatrix,model,maxPivotPerValuePercent,delta,maxcapa)

  model.close()

  def routeUnroutedPoint(k:Int) =  new InsertPointUnroutedFirst(myVRP.unrouted,()=>myVRP.kFirst(k,myVRP.closestNeighboursForward,myVRP.isRouted), myVRP,neighborhoodName = "InsertUF",best=true)

  //TODO: using post-filters on k-nearest is probably crap
  val routeUnroutedPoint2 =  Profile(new InsertPointRoutedFirst(myVRP.routed,()=>myVRP.kFirst(10,myVRP.closestNeighboursForward,x => !myVRP.isRouted(x)),myVRP,neighborhoodName = "InsertRF")  guard(() => myVRP.size < n/2))

  def onePtMove(k:Int) = Profile(new OnePointMove(myVRP.routed, () => myVRP.kFirst(k,myVRP.closestNeighboursForward,myVRP.isRouted), myVRP))

  val twoOpt = Profile(new TwoOpt1(myVRP.routed, ()=>myVRP.kFirst(40,myVRP.closestNeighboursForward,myVRP.isRouted), myVRP))

  def threeOpt(k:Int, breakSym:Boolean) = Profile(new ThreeOpt(myVRP.routed, ()=>myVRP.kFirst(k,myVRP.closestNeighboursForward,myVRP.isRouted), myVRP,breakSymmetry = breakSym, neighborhoodName = "ThreeOpt(k=" + k + ")"))

  val vlsn1pt = Profile(Mu[OnePointMoveMove](
    OnePointMove(myVRP.routed, () => myVRP.kFirst(10,myVRP.closestNeighboursForward,myVRP.isRouted),myVRP),
    l => Some(OnePointMove(() => List(l.head.newPredecessor).filter(_ >= v), () => myVRP.kFirst(10,myVRP.closestNeighboursForward,myVRP.isRouted),myVRP, hotRestart = false)),
    intermediaryStops = true,
    maxDepth = 3))


  val vlsnInsert = Mu[InsertPointMove](
  routeUnroutedPoint(3),
  l => if (myVRP.unroutedNodes.isEmpty) None else Some(routeUnroutedPoint(5)),
  intermediaryStops = false,
  maxDepth = 2)

  val remove = RemovePoint(() => myVRP.routed.value.filter(_>=v), myVRP,best=true)

  val swapInOut = Profile((remove andThen routeUnroutedPoint(10)) name ("SWAPInsert"))
  val search = new RoundRobin(List(swapInOut,vlsnInsert,threeOpt(5,false),twoOpt)) exhaust onePtMove(10) //(BestSlopeFirst(List(vlsnInsert, routeUnroutedPoint2, routeUnroutedPoint(10), swapInOut, onePtMove(10),twoOpt, threeOpt(10,true),vlsn1pt, routeUnroutedPoint)) exhaust threeOpt(20,true))// afterMove(/*myVRP.drawRoutes()*/)

  search.verbose = 1
  //search.verboseWithExtraInfo(3, ()=> "" + myVRP)

  print("Doing all moves ...")


  search.doAllMoves(obj = myVRP.obj)
  model.propagate()
  println(search.profilingStatistics)

  println(myVRP)
}