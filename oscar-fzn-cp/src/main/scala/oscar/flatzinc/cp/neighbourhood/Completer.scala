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

import oscar.algo.Inconsistency
import oscar.algo.search.Branching
import oscar.cp.CPIntVar
import oscar.cp.core.{CPPropagStrength, NoSolutionException}
import oscar.flatzinc.cp.FZCPBasicModel
import oscar.flatzinc.model._

/**
  * @author Gustav Bjordal
  */
class Completer(val fzModel: FZProblem,
                val annotatedStrategy: Option[Map[Variable, CPIntVar] => Branching] = None,
                val useSoftConstraints: Boolean = true) {
  
  val completeModel = new FZCPBasicModel(pstrength = CPPropagStrength.Strong)
  
  
  val optMode: Objective.Value = fzModel.search.obj
  var bestObj: Int = Int.MaxValue
  val objectiveVariable: Option[IntegerVariable] = fzModel.search.variable
  val solutionPrinter: FZSolution = fzModel.solution
  
  completeModel.createVariables(fzModel.variables)
  
  //TODO: do we really want soft constraints here?
  
  if (useSoftConstraints) {
    val auxVars = fzModel.variables.filter(!_.isDefined).filter(!fzModel.neighbourhoods.head.getSearchVariables.contains(_))
    val (hardConstraints, softConstraints) = fzModel.constraints.toArray.partition(c => c.definedVar.isDefined || c.getVariables.exists(auxVars.contains))
    completeModel.createConstraints(hardConstraints)
    completeModel.createSoftAndHardConstraints(softConstraints)
  } else {
    completeModel.createConstraints(fzModel.constraints)
  }
  
  completeModel.createObjective(fzModel.search.obj, fzModel.search.variable)
  
  val mainSearchStrategy = if (annotatedStrategy.isDefined) {
    annotatedStrategy.get.apply(completeModel.dictVars.toMap)
  } else {
    completeModel.getPhaseAssignFirstFail()
  }
  
  if (useSoftConstraints) {
    completeModel.setSearch(oscar.cp.binarySplit(Array(completeModel.GlobalViolation.get))
      ++ mainSearchStrategy
      ++ oscar.cp.binarySplit(Array(Helper.getObjectiveFromCPVarMap(fzModel, completeModel.solver,
                                                                     completeModel.dictVars))))
  } else {
    completeModel.setSearch(mainSearchStrategy
      ++ oscar.cp.binarySplit(Array(Helper.getObjectiveFromCPVarMap(fzModel, completeModel.solver,
                                                                     completeModel.dictVars))))
  }
  
  
  private def improvesOnObjective(newObj: Int): Boolean = {
    newObj < bestObj
  }
  
  def getCompleteSolution(targetObjective: Option[Int], fixedMap: Map[Variable, Int], printBest: Boolean = false,
                          verbose: Boolean = false, maxTime:Long = Long.MaxValue): FZCPLSSol = {
    completeModel.solutionPrinter = fzModel.solution
    
    val startTime: Long = System.currentTimeMillis()
    completeModel.push()
    val fixings = for ((k, v) <- fixedMap if !k.isBound && completeModel.dictVars.contains(k) && !(objectiveVariable.isDefined && objectiveVariable.get == k)) yield {
      (completeModel.dictVars(k) === v).asInstanceOf[oscar.cp.Constraint]
    }
    try {
      completeModel.add(fixings.toArray)
      completeModel.solver.update()
      
      /*
      for(c <- fixings){
        completeModel.add(c)
        completeModel.solver.update()
      }*/
    } catch {
      case Inconsistency =>
        return NoSolution()
      case e: NoSolutionException =>
        return NoSolution()
    }
    val (sol, solutionMap) = completeModel.startSearch(targetObjective, firstImproving = false,
                                                        canExceedTimeLimit = true, timeLimit = 10, flipBooleans = false,
                                                        verbose = false, maxTime = maxTime)
    completeModel.pop()
    if (sol) {
      val newObj = Helper.getObjectiveFromIntMap(fzModel, solutionMap) //solutionMap(objectiveVariable)
      val violation = if (useSoftConstraints) solutionMap(completeModel.ViolationVariable.get) else 0
      if (printBest && violation == 0 && improvesOnObjective(newObj)) {
        bestObj = newObj
        // TODO: flip objective in case on maximisation problem?
        solutionPrinter.handleSolution(solutionMap.map { case (key: Variable, value: Int) => key.id -> value.toString })
        if (fzModel.search.obj == Objective.SATISFY) {
          throw SatisfyingSolution()
        }
      }
//      println("% Spent: " + (System.currentTimeMillis() - startTime) + "ms")
      if (violation == 0) {
        Solution(newObj, solutionMap.toMap)
      } else {
        ViolatingSolution(violation, newObj, solutionMap.toMap)
      }
    } else {
      NoSolution()
    }
  }
}
