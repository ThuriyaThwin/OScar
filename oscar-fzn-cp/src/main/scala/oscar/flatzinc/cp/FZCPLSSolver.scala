/** *****************************************************************************
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
  * *****************************************************************************/
/**
  * @author Gustav Björdal
  */
package oscar.flatzinc.cp


import oscar.algo.search.Branching
import oscar.cp._
import oscar.flatzinc.Options
import oscar.flatzinc.cp.neighbourhood._
import oscar.flatzinc.model.{ValueStrategy, _}
import oscar.flatzinc.parser.FZParser
import oscar.flatzinc.transformation.FZModelTransformations

import scala.collection.mutable.{Map => MMap}
import scala.util.Random


class FZCPLSSolver {
  // Parameters
  // val allowPartialCurrentSolutions = false //TODO: Deprecated by violating solutions
  var limitNeighbourhoodExploration = true
  //val improvingRestart = false
  
  var softenConstraints = true
  
  val completeLocalSearch = false
  
  var optimalValue: Int = _
  
  var totalNumberOfIterations = 0
  var startTime: Long = _
  var timeLimitMs: Int = _
  
  def solve(opts: Options) {
    val log = opts.log()
    log("start")
    val model = FZParser.readFlatZincModelFromFile(opts.fileName, log, false).problem
    
    if (opts.is("hard")) {
      softenConstraints = false
    }
    
    startTime = System.currentTimeMillis()
    timeLimitMs = opts.timeOut * 1000
    
    log("Parsed.")
    FZModelTransformations.propagate(model)(log)
    FZModelTransformations.simplify(model)(log)
    val searchVars = model.neighbourhoods.flatMap(_.getSearchVariables)
    FZModelTransformations.findInvariants(model, log, searchVars)
    log("initial variable reduction (to avoid overflows)")
    
    if (model.search.variable.isDefined) {
      if (model.search.obj == Objective.MAXIMIZE) {
        optimalValue = model.search.variable.get.max
      } else {
        optimalValue = model.search.variable.get.min
      }
    }
    
    // TODO: Currently only supports one neighbourhood (with multiple sub-neighbourhoods)
    //       Generalise this.
    
    
    if (model.neighbourhoods.size > 1) {
      println("Error: Too many neighbourhoods")
    }
    val neighbourhood = model.neighbourhoods.head
    
    try {
      LSRun(model, neighbourhood)
    } catch {
      case SatisfyingSolution() =>
        println("==========")
      case OptimalSolution() =>
        println("==========")
    }
    println(s"% nbMoves: $totalNumberOfIterations")
    println(s"% runtime: ${System.currentTimeMillis()-startTime}")
    println("% Done")
  }
  
  
  def LSRun(model: FZProblem, neighbourhood: FZNeighbourhood): Unit = {
    
    val initialiser = new Initialiser(model, model.neighbourhoods.head, getSearchAnnotation(model),
                                       useSoftConstraints = softenConstraints)
    initialiser.init()
  
    if (model.search.variable.isDefined) {
      if (model.search.obj == Objective.MAXIMIZE) {
        optimalValue = initialiser.initModel.dictVars(model.search.variable.get).max
      } else {
        optimalValue = initialiser.initModel.dictVars(model.search.variable.get).min
      }
    }
    
    val completer = new Completer(model, getSearchAnnotation(model), useSoftConstraints = softenConstraints)
    
    var bestObj = LexObj(Int.MaxValue, Int.MaxValue)
    
    
    val subNeighbourhoods = neighbourhood.subNeighbourhoods.map(sn => {
      new MoveMaker(neighbourhood.getSearchVariables.toSet,
                     model,
                     sn,
                     useSoftConstraints = softenConstraints,
                     debugMode = false)
    })
    
    var timeLimit = 10
    //    val initialSolutionMap = initialiser.getInitialSolution(timeLimit)
    var currentSolution: Map[Variable, Int] = Map.empty
    while (System.currentTimeMillis() - startTime < timeLimitMs) {
      currentSolution = initialiser.getInitialSolution(timeLimit,
                                                        maxTime = startTime + timeLimitMs - System.currentTimeMillis())
      val (newBestObjective, bestSolution) = LSExhaust(model, bestObj, neighbourhood, subNeighbourhoods,
                                                        currentSolution, completer)
      bestObj = newBestObjective
      //TODO: Implement improving restarts
      timeLimit += 10
    }
  }
  
  def LSExhaust(model: FZProblem, currentBestObj: LexObj, neighbourhood: FZNeighbourhood,
                moveMakers: Iterable[MoveMaker],
                initialSolutionMap: Map[Variable, Int], completer: Completer): (LexObj, Map[Variable, Int]) = {
    
    val initialSolution = completer.getCompleteSolution(None, initialSolutionMap, printBest = true,
                                                         maxTime = startTime + timeLimitMs - System.currentTimeMillis())
    
    var bestObj = currentBestObj
    var localBestObj = LexObj(Int.MaxValue, Int.MaxValue)
    
    initialSolution match {
      case Solution(objective, _, _) if isBetterThan(model, LexObj(0, objective), currentBestObj) =>
        bestObj = LexObj(0, objective)
        localBestObj = LexObj(0, objective)
      case NoSolution() =>
        System.err.println("Initial solution is illegal.")
        return (bestObj, Map.empty)
      case ViolatingSolution(viol, obj, _, _)
        if isBetterThan(model, LexObj(viol, obj), currentBestObj) =>
        bestObj = LexObj(viol, obj)
        localBestObj = LexObj(viol, obj)
      case _ =>
    }
    
    var currentObj = localBestObj
    
    var bestSolution: Map[Variable, Int] = Map.empty
    var currentSolution = initialSolution.getSolution
    var it = 0
    
    // Tabu Search
    var tabuList: MMap[Variable, Int] = MMap(neighbourhood.getSearchVariables.distinct.map(_ -> 0): _*)
    val tenure: Int = Math.max(Math.ceil(tabuList.size * 0.1).toInt, 2)
    
    // Random restarts
    var nNoSolution = 0
    val maxNoSolution = 3 * tenure
    var itOfBest = 0
    val maxItWithoutBest = 1000
    var onlyImprovingMoves = true
    
    
    var exit = false
    //System.err.println("Warning Tabu disabled")
    while (!exit && (System.currentTimeMillis() - startTime < timeLimitMs)) {
//      println("Current best: " + bestObj)
      it += 1
      totalNumberOfIterations += 1
      val timeBeforeMoves = System.currentTimeMillis()
      val solutions = moveMakers.map(_.getMoves(currentSolution,
                                                 tabuList.filter(_._2 > it).keys,
                                                 currentObj = currentObj,
                                                 bestObj = localBestObj,
                                                 improving = onlyImprovingMoves,
                                                 maxTime = startTime + timeLimitMs - System.currentTimeMillis()))
      //      println("Exploring neighbourhoods took total of: " + (System.currentTimeMillis() - timeBeforeMoves) + "ms")
      
      moveMakers.foreach{
        case m => println("Avg time: " + (m.runtimes.sum.toFloat/m.runtimes.length))
      }
      
      val timeBeforeComplete = System.currentTimeMillis()
      val completedSolutions: Iterable[(FZCPLSSol, Iterable[Variable])] =
        solutions.filter(_.valid).map {
          case Solution(obj, solutionMap, modifiedVars) =>
            (completer.getCompleteSolution(Some(obj), solutionMap, printBest = true,
                                            maxTime = startTime + timeLimitMs - System.currentTimeMillis()), modifiedVars)
          case ViolatingSolution(viol, obj, solutionMap, modifiedVars) =>
            (completer.getCompleteSolution(Some(obj), solutionMap, printBest = true,
                                            maxTime = startTime + timeLimitMs - System.currentTimeMillis()), modifiedVars)
        }.filter(_._1.valid)
//      println("Completing moves took: " + (System.currentTimeMillis() - timeBeforeComplete) + "ms")
      if (completedSolutions.nonEmpty) {
        val (bestMove, modifiedVars) = completedSolutions.minBy(_._1.getLexObjective)
        currentObj = bestMove.getLexObjective
        val newSolution = bestMove.getSolution
        currentSolution = newSolution
        modifiedVars.foreach {
          v => tabuList += v -> (it + tenure + Random.nextInt(tenure))
        }
        if (currentObj.violation == 0 && currentObj.objective == optimalValue) {
          throw OptimalSolution()
        }
        if (isBetterThan(model, currentObj, bestObj)) {
          bestObj = currentObj
          bestSolution = currentSolution
          itOfBest = it
//          onlyImprovingMoves = true
        }
        if (isBetterThan(model, currentObj, localBestObj)) {
          localBestObj = currentObj
          itOfBest = it
          System.err.println("% " + bestObj)
        }
        nNoSolution = 0
        
      } else if (!solutions.exists(_.valid)) { // If all neighbourhoods were empty
        nNoSolution += 1
        onlyImprovingMoves = false
        limitNeighbourhoodExploration = false
      } else {
        onlyImprovingMoves = false
        val vs = solutions.filter(_.valid)
        vs.toList(Random.nextInt(vs.size)) match {
          case Solution(obj, solutionMap, modifiedVars) =>
            modifiedVars.foreach {
              v => tabuList += v -> (it + tenure + Random.nextInt(tenure))
            }
          case ViolatingSolution(viol, obj, solutionMap, modifiedVars) =>
            modifiedVars.foreach {
              v => tabuList += v -> (it + tenure + Random.nextInt(tenure))
            }
        }
        
      }
      
      //TODO: Intensification
      
      if ((tabuList.count(_._2 > it) == 0 && nNoSolution > maxNoSolution) || it - itOfBest > maxItWithoutBest) {
        System.err.println("% Restart")
        exit = true
      }
    }
    (bestObj, bestSolution)
  }
  
  @deprecated
  private def isBetterThan(model: FZProblem, obj: Int,
                           bestObj: Int): Boolean = {
    //model.search.obj == Objective.MINIMIZE && obj < bestObj || (model.search.obj == Objective.MAXIMIZE && obj > bestObj)
    obj < bestObj
  }
  
  private def isBetterThan(model: FZProblem, obj: LexObj,
                           bestObj: LexObj): Boolean = {
    obj.violation < bestObj.violation || (obj.violation == bestObj.violation && obj.objective < bestObj.objective)
  }
  
  //TODO: The Option type here is a bit ugly...
  def getSearchAnnotation(fzModel: FZProblem): Option[Map[Variable, CPIntVar] => Branching] = {
    if (fzModel.search.getSearchStrategy.nonEmpty) {
      Some({ varMap: Map[Variable, CPIntVar] => {
        def valueStrategyToFun(valueStrategy: ValueStrategy.Value, vars: Array[CPIntVar]): Int => Int = {
          valueStrategy match {
            case ValueStrategy.INDOMAIN_MIN => i: Int => vars(i).min
            case ValueStrategy.INDOMAIN_MAX => i: Int => vars(i).max
            case ValueStrategy.INDOMAIN_MEDIAN => i: Int => vars(i).median
            case ValueStrategy.INDOMAIN_RANDOM => i: Int => vars(i).randomValue
            case ValueStrategy.INDOMAIN_SPLIT => i: Int => (vars(i).min + vars(i).max) / 2
            
          }
        }
        
        def varStrategyToFun(variableStrategy: VariableStrategy.Value, vars: Array[CPIntVar]): Int => Int = {
          variableStrategy match {
            case VariableStrategy.INPUT_ORDER => i: Int => i
            case VariableStrategy.FIRST_FAIL => i: Int => vars(i).size
            case VariableStrategy.ANTI_FIRST_FAIL => i: Int => -vars(i).size
            case VariableStrategy.SMALLEST => i: Int => vars(i).min
            case VariableStrategy.LARGEST => i: Int => -vars(i).max
            case VariableStrategy.MAX_REGRET => i: Int => -vars(i).regret
          }
        }
        
        def fzStrategyToCPStrategy(strategy: CompleteSearchStrategy): Branching = {
          strategy match {
            case IntSearch(variables, variableStrategy, valueStrategy) =>
              val searchVars = variables.filterNot(_.isBound).map(varMap).toArray
              valueStrategy match {
                case ValueStrategy.INDOMAIN_SPLIT =>
                  oscar.cp.binarySplitIdx(searchVars, varStrategyToFun(variableStrategy, searchVars),
                                           valueStrategyToFun(valueStrategy, searchVars))
                case ValueStrategy.INDOMAIN_REVERSE_SPLIT =>
                  System.err.println("% INDOMAIN_REVERSE_SPLIT not implemented")
                  oscar.cp.binarySplitIdx(searchVars, varStrategyToFun(variableStrategy, searchVars),
                                           valueStrategyToFun(valueStrategy, searchVars))
                case _ =>
                  oscar.cp.binaryIdx(searchVars, varStrategyToFun(variableStrategy, searchVars),
                                      valueStrategyToFun(valueStrategy, searchVars))
              }
            case BoolSearch(variables, variableStrategy, valueStrategy) =>
              fzStrategyToCPStrategy(IntSearch(variables, variableStrategy, valueStrategy))
            case SeqSearch(strategies) =>
              strategies.map(fzStrategyToCPStrategy).reduce(_ ++ _)
          }
        }
        
        fzModel.search.getSearchStrategy.map(fzStrategyToCPStrategy).reduce(_ ++ _)
      }
      })
    } else {
      None
    }
  }
}
