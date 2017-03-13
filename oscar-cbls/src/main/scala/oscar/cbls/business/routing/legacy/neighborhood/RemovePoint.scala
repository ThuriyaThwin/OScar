/**
 * *****************************************************************************
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
 * ****************************************************************************
 */
/**
 * *****************************************************************************
 * Contributors:
 *     This code has been initially developed by Ghilain Florent.
 *     Refactored (in respect with the new architecture) by Yoann Guyot.
 * ****************************************************************************
 */

package oscar.cbls.business.routing.legacy.neighborhood

import oscar.cbls.algo.search.HotRestart
import oscar.cbls.business.routing.legacy.model.VRP

/**
 * Removes a point of route.
 * The search complexity is O(n).
 * @param predecessorsOfRoutedPointsToRemove: the predecessors ofthe points that we will try to remove
 * @param vrp the routing problem
 * @param neighborhoodName the name of the neighborhood, for verbosities
 * @param best true for the best move, false for the first move
 * @param hotRestart true if hotRestart is needed, false otherwise
 * @author renaud.delandtsheer@cetic.be
 * @author yoann.guyot@cetic.be
 * @author Florent Ghilain (UMONS)
 */
case class RemovePoint(predecessorsOfRoutedPointsToRemove:()=>Iterable[Int],
                       override val vrp: VRP,
                       neighborhoodName:String = null,
                       best:Boolean = false,
                       hotRestart:Boolean = true) extends EasyRoutingNeighborhood[RemovePointMove](best,vrp, neighborhoodName) {

  //the indice to start with for the exploration
  var startIndice: Int = 0

  var beforeRemovedPoint:Int = 0;
  var removedPoint:Int = 0;

  override def exploreNeighborhood(): Unit = {

    val iterationSchemeOnZone =
      if (hotRestart && !best) HotRestart(predecessorsOfRoutedPointsToRemove(), startIndice)
      else predecessorsOfRoutedPointsToRemove()

    cleanRecordedMoves()

    val it = iterationSchemeOnZone.iterator
    while (it.hasNext) {
      beforeRemovedPoint = it.next()
      assert(vrp.isRouted(beforeRemovedPoint),
        "The search zone should be restricted to before routed nodes when removing.")
      removedPoint = vrp.next(beforeRemovedPoint).value
      require(!vrp.isADepot(removedPoint),
        "a point to remove is a depot: beforeRemovedPoint:" + beforeRemovedPoint + " removedPoint:" + removedPoint)

      encode(beforeRemovedPoint)
      val newObj = evalObjOnEncodedMove()

      if (evaluateCurrentMoveObjTrueIfStopRequired(newObj)) {
        startIndice = beforeRemovedPoint + 1
        return
      }
    }
  }

  override def instantiateCurrentMove(newObj: Int) =
    RemovePointMove(beforeRemovedPoint, removedPoint, newObj, this, neighborhoodNameToString)

  def encode(beforeRemovedPoint: Int) {
    unroute(cutNodeAfter(beforeRemovedPoint))
  }

  //this resets the internal state of the Neighborhood
  override def reset(){startIndice = 0}
}

/**
 * Models a remove-point operator of a given VRP problem.
 * @param beforeRemovedPoint the predecessor of the point that will be removed.
 * @param objAfter the objective value if we performed this remove-point operator.
 * @param neighborhood the originating neighborhood
 * @author renaud.delandtsheer@cetic.be
 * @author yoann.guyot@cetic.be
 * @author Florent Ghilain (UMONS)
 */
case class RemovePointMove(
                        beforeRemovedPoint: Int,
                        removedPoint:Int,
                        override val objAfter: Int,
                        override val neighborhood:RemovePoint,
                        override val neighborhoodName:String = null)
  extends VRPMove(objAfter, neighborhood, neighborhoodName){

  override def impactedPoints: List[Int] = List(beforeRemovedPoint,removedPoint)

  override def encodeMove() {
    neighborhood.encode(beforeRemovedPoint)
  }
  override def toString: String = "RemovePoint(point = " + neighborhood.vrp.next(beforeRemovedPoint).value + objToString + ")"
}