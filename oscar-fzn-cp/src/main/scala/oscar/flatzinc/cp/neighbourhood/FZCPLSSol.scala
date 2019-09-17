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

import oscar.flatzinc.model.Variable

/**
  * @author Gustav Bjordal
  */
trait FZCPLSSol {
  def valid:Boolean
  def getLexObjective:LexObj
  def getSolution:Map[Variable, Int]
}

case class Solution(objective: Int, solution: Map[Variable, Int],
                    modifiedVariables: Iterable[Variable] = List.empty) extends FZCPLSSol{
  override def valid: Boolean = true
  override def getLexObjective: LexObj = LexObj(0, objective)
  override def getSolution: Map[Variable, Int] = solution
}

case class ViolatingSolution(violation:Int, objective:Int, solution: Map[Variable, Int],
                             modifiedVariables: Iterable[Variable] = List.empty)extends FZCPLSSol{
  override def valid: Boolean = true // well...
  override def getLexObjective: LexObj = LexObj(violation, objective)
  override def getSolution: Map[Variable, Int] = solution
}

case class NoSolution() extends FZCPLSSol{
  override def valid: Boolean = false
  override def getLexObjective: LexObj = LexObj(Int.MaxValue,Int.MaxValue)
  override def getSolution: Map[Variable, Int] = Map.empty
}

//Ordering hack makes the order of the arguments improtant
case class LexObj(violation:Int, objective:Int)
object LexObj {
  implicit val ord = Ordering.by(unapply)
}