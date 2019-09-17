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

import oscar.cp.{CPIntVar, CPSolver}
import oscar.flatzinc.model.{FZProblem, Objective, Variable}

import scala.collection.mutable.{Map => MMap}

/**
  * @author Gustav Bjordal
  */
object Helper {
  @inline
  def getObjectiveFromIntMap(fzModel:FZProblem, map:Map[Variable,Int]): Int = {
    fzModel.search.obj match {
      case Objective.MINIMIZE =>
        map(fzModel.search.variable.get)
      case Objective.MAXIMIZE =>
        -map(fzModel.search.variable.get)
      case Objective.SATISFY =>
        0
    }
  }
  @inline
  def getObjectiveFromIntMap(fzModel:FZProblem, map:MMap[Variable,Int]): Int = {
    fzModel.search.obj match {
      case Objective.MINIMIZE =>
        map(fzModel.search.variable.get)
      case Objective.MAXIMIZE =>
        -map(fzModel.search.variable.get)
      case Objective.SATISFY =>
        0
    }
  }
  
  @inline
  def getObjectiveFromIntBoolMap(fzModel:FZProblem, map:Map[Variable,(Int,Boolean)]):Int = {
    fzModel.search.obj match {
      case Objective.MINIMIZE =>
        map(fzModel.search.variable.get)._1
      case Objective.MAXIMIZE =>
        -map(fzModel.search.variable.get)._1
      case Objective.SATISFY =>
        0
    }
  }
  @inline
  def getObjectiveFromCPVarMap(fzModel:FZProblem, solver:CPSolver, map:MMap[Variable,CPIntVar]):CPIntVar = {
    fzModel.search.obj match {
      case Objective.MINIMIZE =>
        map(fzModel.search.variable.get)
      case Objective.MAXIMIZE =>
        -map(fzModel.search.variable.get)
      case Objective.SATISFY =>
        CPIntVar(0)(solver)
    }
  }
  
}
