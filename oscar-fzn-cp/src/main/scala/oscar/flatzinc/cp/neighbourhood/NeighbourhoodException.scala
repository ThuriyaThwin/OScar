/*
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

package oscar.flatzinc.cp.neighbourhood

/**
  * @author Gustav Bjordal
  */
abstract class NeighbourhoodException extends RuntimeException

case class BoundedMoveVariableException(id: String) extends NeighbourhoodException

case class MoveNotSupportedException(id: String) extends NeighbourhoodException

case class UnableToInitialiseException() extends NeighbourhoodException
case class TooManyNeighbourhoodsException() extends NeighbourhoodException

case class SatisfactionProblemNotSupported() extends NeighbourhoodException

case class InfeasibleSolution() extends NeighbourhoodException

case class SatisfyingSolution() extends NeighbourhoodException
case class OptimalSolution() extends NeighbourhoodException


case class PartialCurrentSolutionsNotSupportedInThisWay() extends NeighbourhoodException
