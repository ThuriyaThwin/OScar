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

import oscar.algo.branchings.LCSearchSimplePhaseAssign
import oscar.algo.search.Branching
import oscar.cp.core.CPPropagStrength
import oscar.cp.{CPBoolVar, CPIntVar}
import oscar.flatzinc.cp.FZCPBasicModel
import oscar.flatzinc.model.{Variable, _}

import scala.collection.mutable.{Map => MMap}

/**
  * @author Gustav Bjordal
  */
class Initialiser(val fzModel: FZProblem,
                  val neighbourhood: FZNeighbourhood,
                  val annotatedStrategy: Option[Map[Variable, CPIntVar] => Branching],
                  val useSoftConstraints:Boolean = true) {
  
  val initModel = new FZCPBasicModel(pstrength = CPPropagStrength.Strong)
  var searchStrategy:Branching = _
  def init(): Unit = {
    initModel.createVariables(neighbourhood.initVariables ++ neighbourhood.initConstraints.flatMap(_.getVariables) ++ fzModel.variables)
    //initModel.createConstraints(fzModel.constraints)
    initModel.createConstraints(neighbourhood.initConstraints)
    
    val auxVars = fzModel.variables.filter(!_.isDefined).filter(!fzModel.neighbourhoods.head.getSearchVariables.contains(_))
    if(useSoftConstraints) {
      val (hardConstraints, softConstraints) = fzModel.constraints.toArray.partition(c => c.definedVar.isDefined || c.getVariables.exists(auxVars.contains))
      //completeModel.createSoftAndHardConstraints(fzModel.constraints)
      initModel.createConstraints(hardConstraints)
      initModel.createSoftAndHardConstraints(softConstraints)
    }else{
      initModel.createConstraints(fzModel.constraints)
    }
    
    val basicStrategy = if (annotatedStrategy.isDefined) {
      annotatedStrategy.get.apply(initModel.dictVars.toMap)
    } else {
      val searchVars = neighbourhood.getSearchVariables.map(initModel.dictVars)
      oscar.cp.binaryFirstFail(searchVars, _.randomValue)
    }
    
    searchStrategy = basicStrategy
    if(initModel.GlobalViolation.isDefined)
      searchStrategy = searchStrategy ++ oscar.cp.binarySplit(Array(initModel.GlobalViolation.get))
    searchStrategy = searchStrategy ++ initModel.getPhaseAssignFirstFail(initModel.dictVars.filterKeys(v => !v.isIntroduced && !v.isDefined).values.toArray)
    
    if(fzModel.search.variable.isDefined){
      searchStrategy = searchStrategy ++ oscar.cp.binary(Array(initModel.dictVars(fzModel.search.variable.get)))
    }
    initModel.setSearch(searchStrategy)
  
    initModel.createObjective(fzModel.search.obj, fzModel.search.variable)
  }
  
  def getInitialSolution(timeLimit:Int = 10, maxTime:Long = Long.MaxValue): Map[Variable, Int] = {
    initModel.solutionPrinter = fzModel.solution
    initModel.push()
    val (sol, solutionMap) =
      initModel.startSearch(None, firstImproving = false,
                             flipBooleans = false,
                             timeLimit = timeLimit,
                             canExceedTimeLimit = true,
                             verbose = false,
                             resetBoundsOnSol = false,
                             maxTime = maxTime)
    initModel.pop()
    if (sol) {
      solutionMap.toMap
    } else {
      throw UnableToInitialiseException()
    }
  }
  
  def getImprovingSolution(obj: Int, bestSolution:Map[Variable, Int]): Map[Variable, Int] = {
    System.err.println("% Warning: Improving initialisation not yet implemented")
    initModel.push()
    initModel.tightenBestObj(obj, fzModel.search.obj == Objective.MINIMIZE)
    println(bestSolution(fzModel.search.variable.get))
    val vars = bestSolution.keys.toArray
    val searchVars:Array[CPIntVar] = vars.map(initModel.dictVars)
    val phaseSearch = new LCSearchSimplePhaseAssign(searchVars, searchVars(_).size, searchVars(_).min)
    initModel.setSearch(phaseSearch)
    
    val (sol, solutionMap) =
      initModel.startSearch(None, flipBooleans = false, timeLimit = 10, canExceedTimeLimit = true,
                             nSols = 1, verbose = false)
    initModel.pop()
    println(solutionMap(fzModel.search.variable.get))
    if (sol) {
      solutionMap.toMap
    } else {
      throw UnableToInitialiseException()
    }
  }
  
  def completeLSBoundingSearch(improve: Map[Variable, Int] => Int): Int = {
    var bestFound: Int = 0
    initModel.push()
    if (annotatedStrategy.isDefined) {
      initModel.setSearch(annotatedStrategy.get.apply(initModel.dictVars.toMap))
    }
    initModel.solver.onSolution {
      val solutionMap: MMap[Variable, Int] = MMap.empty[Variable, Int]
      for ((k, v) <- initModel.dictVars if v.isBound) {
        v match {
          case b: CPBoolVar =>
            solutionMap(k) = b.min
          case i: CPIntVar =>
            solutionMap(k) = i.min
        }
      }
      println("Best found: " + initModel.dictVars(fzModel.search.variable.get))
      val newBest = improve(solutionMap.toMap)
      initModel.tightenCutBestObj(newBest, fzModel.search.obj == Objective.MINIMIZE)
      initModel.solver.objective.objs.foreach(_.best = newBest)
      bestFound = newBest
    }
    initModel.solver.silent = false
    val stats = initModel.solver.start()
    println(stats)
    initModel.pop()
    bestFound
  }
  
}
