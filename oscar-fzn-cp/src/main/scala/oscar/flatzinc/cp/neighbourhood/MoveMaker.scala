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


import oscar.algo.search.DFSearch
import oscar.cp.constraints._
import oscar.cp.core.variables.CPIntVarSingleton
import oscar.cp.core.{CPPropagStrength, CPSolver}
import oscar.cp.{CPBoolVar, CPIntVar, elementVar, sum}
import oscar.flatzinc.cp._
import oscar.flatzinc.model._

import scala.collection.mutable.{Map => MMap, Queue => MQueue}

/**
  * @author Gustav Bjordal
  */
class MoveMaker(val sharedSearchVariables: Set[Variable],
                val fzModel: FZProblem,
                val neighbourhood: FZSubNeighbourhood,
                debugMode: Boolean = false,
                val useSoftConstraints: Boolean = true) {
  
  private case class Write(targetedVariables: Array[Variable], indices: Option[Array[CPIntVar]],
                           values: Array[CPIntVar])
  
  if (debugMode) {
    println("% Creating move maker for " + neighbourhood.name)
  }
  implicit val solver: CPSolver = CPSolver(CPPropagStrength.Strong)
  val poster = new CPConstraintPoster(CPPropagStrength.Strong)
  
  //TODO: These dependent vars and cons are deprecated, use neighbourhood.getDependentVariables instead.
  // We no longer need the dependency tree of variables.
  var dependentVariables: Array[Variable] = Array.empty
  var dependentConstraints: Array[Constraint] = Array.empty
  findDependentVarsAndCons()
  
  val preMoveDependentVariables: Array[Variable] = (neighbourhood.getControlledAndDeclaredVariables ++
    dependentVariables).distinct
  val preVariableMap: MMap[Variable, CPIntVar] = createVariableMap(preMoveDependentVariables)
  
  val postMoveDependentVariables: Array[Variable] =
  //    (neighbourhood.getControlledAndDeclaredVariables ++ dependentVariables).distinct.filterNot(
  //      neighbourhood.itVariables.contains(_))
    fzModel.variables.filterNot(v => neighbourhood.itVariables.contains(v) || neighbourhood.whereVariables.contains(v)).toArray
  val postVariableMap: MMap[Variable, CPIntVar] = createVariableMap(postMoveDependentVariables) ++
    (preVariableMap filterKeys (neighbourhood.itVariables.toSet union neighbourhood.whereVariables.toSet))
  
  
  if(neighbourhood.getSearchVariables.exists(_.isDefined)){
    throw new RuntimeException("A search variable is functionally defined.")
  }
  // Variables that are fixed by a move and returned by a MoveMaker
  val inputVariables: Map[Variable, CPIntVar] =
    (dependentVariables ++ neighbourhood.getSearchVariables)
      .filterNot(v => v.isBound)
      .distinct
      .filter(fzModel.variables.contains)
      .map(v => v -> preVariableMap(v))
      .toMap
  //  val outputVariables: Map[Variable, CPIntVar] = fzModel.variables.map(v => v -> postVariableMap(v)).toMap
  //TODO: is this safe?
  // Should outputVars contain objective?
  val outputVariables: Map[Variable, CPIntVar] =
  (fzModel.neighbourhoods.head.getSearchVariables ++  (if (fzModel.search.variable.isDefined){
    Array(fzModel.search.variable.get)
  } else{
    Array.empty[Variable]
  })).filterNot(_.isBound)
    .map(v => v -> postVariableMap(v))
    .toMap
  
  val postObjectiveVar = Helper.getObjectiveFromCPVarMap(fzModel, solver,
                                                          postVariableMap) //postVariableMap(fzModel.search.variable.get)
  
  val indicatorMap: Map[Variable, CPBoolVar] = sharedSearchVariables.map(v => v -> CPBoolVar(v.id)).toMap
  var noOps: List[CPBoolVar] = List.empty
  
  var numTargetedVariables: Int = 0
  
  //TODO does this make any actual difference?
//  solver.addDecisionVariables(neighbourhood.getSearchVariables.map(postVariableMap))
//  solver.addDecisionVariables(postObjectiveVar)
  
  neighbourhood.whereConstraints.foreach { addConstraint(_, preVariableMap) }
  //dependentConstraints.foreach { addConstraint(_, postVariableMap) }
  
  var viols = Array(CPIntVar(0))
  if(useSoftConstraints) {
    val auxVariables = postVariableMap.filterKeys(!_.isDefined).filterKeys(!neighbourhood.getSearchVariables.contains(_)).keys.toSet
    //  //TODO: Do we filter the dependent constraints?
    //  //TODO: Soften these constraints
    val (hardConstraints, softConstraints) = fzModel.constraints.toArray.partition(c => c.definedVar.isDefined || c.getVariables.exists(auxVariables.contains))
    viols = softConstraints.map(c => addSoftConstraint(c, postVariableMap)).filterNot(_.isBoundTo(0))
    hardConstraints.foreach { addConstraint(_, postVariableMap) }
  }else{
    fzModel.constraints.foreach { addConstraint(_, postVariableMap) }
  }
  
  //TODO: What is a good ub here?
  val GlobalViolation = CPIntVar(0, viols.map(_.max).sum + (postObjectiveVar.max - postObjectiveVar.min), "GlobalViolation")
 
  val CurrentBest = CPIntVar(postObjectiveVar.min, postObjectiveVar.max+1, "CurrentBest")
  
  solver.add(oscar.cp.sum(viols ++ Array(oscar.cp.maximum(Array(oscar.cp.plus(postObjectiveVar,1) - CurrentBest, CPIntVar(0)))), GlobalViolation))
  
  neighbourhood.ensureConstraints.foreach { addConstraint(_, postVariableMap) }
  private var encodedMoves: Array[Write] = Array.empty
//  addMoveConstraints()
  addMoveConstraintsWithWrites()
  
  val preItVars: Array[CPIntVar] = neighbourhood.itVariables.map(preVariableMap)
  val postItVars: Array[CPIntVar] = neighbourhood.itVariables.map(postVariableMap)
  
  val preSearchVars: Array[CPIntVar] = neighbourhood.getSearchVariables.map(preVariableMap)
  val postSearchVars: Array[CPIntVar] = neighbourhood.getSearchVariables.map(postVariableMap)
  
  // Search on iterator variables first.
  val branchingVars: Array[CPIntVar] = //neighbourhood.getSearchVariables.map(postVariableMap)
    neighbourhood.itVariables.map(preVariableMap) //++ postVariableMap.values.toArray.asInstanceOf[Array[CPIntVar]]
   
  
  // SEARCH
  val outputArray = outputVariables.filterKeys(!_.isIntroduced).values.toArray
    solver.search(
                   oscar.cp.binarySplit(branchingVars, _ => solver.random.nextInt(branchingVars.length))
//    solver.search(oscar.cp.binary(branchingVars)
      ++ oscar.cp.binarySplit(viols ++ Array(GlobalViolation), _ => solver.random.nextInt(viols.length+1))
      ++ oscar.cp.binaryLastConflictPhaseSaving(postVariableMap.filterKeys(!_.isDefined).values.filterNot(_ == postObjectiveVar).toArray)
      ++ oscar.cp.binarySplit(Array(postObjectiveVar))
      ++ oscar.cp.binaryLastConflictPhaseSaving(outputArray)
                 )
  
  
  var solutionMap: Map[Variable, (Int, Boolean)] = Map.empty
  var modifiedVars: Iterable[Variable] = Iterable.empty
  private var _currentObj = LexObj(Int.MaxValue, Int.MaxValue)
  var solutionViolation = Int.MaxValue
  
  solver.onSolution {
//    println("Printing on MoveMaker on Solution")
//    fzModel.solution.handleSolution(postVariableMap.map { case (key: Variable, value: CPIntVar) => key.id -> value.min.toString })
    solutionMap = outputVariables
                  .map {
                    case (k, v) => k -> (v.min, v.isBound)
                  }
    if (GlobalViolation.min < _currentObj.violation ||
      (GlobalViolation.min == _currentObj.violation && postObjectiveVar.min < _currentObj.objective)) {
      foundImproving = true
//      println("Looking for best")
//      println(postObjectiveVar.min)
    }
    solutionViolation = GlobalViolation.min
    modifiedVars = encodedMoves.flatMap {
      case Write(targets, Some(indices), _) =>
        indices.map((intVar: CPIntVar) => targets(intVar.min))
      case Write(target, None, _) => Array(target.head)
    }
    // A CBLS solver could be called here...
  }
  solver.silent = true
  
  fzModel.search.obj match {
    case Objective.MINIMIZE | Objective.MAXIMIZE =>
//      solver.minimize(GlobalViolation, postObjectiveVar)
      solver.minimize(oscar.cp.plus(GlobalViolation, postObjectiveVar))
//      solver.paretoMinimize(GlobalViolation, postObjectiveVar)
    case Objective.SATISFY => solver.minimize(GlobalViolation)
  }
  private var foundImproving = false
  
  private def firstImproving(maxTime: Long): DFSearch => Boolean = {
    foundImproving = false
    val maxTimeout = System.currentTimeMillis() + maxTime
    val objVar = postObjectiveVar
    (s: DFSearch) => {
      var stop = false
      stop |= System.currentTimeMillis() >= maxTimeout
      stop |= (s.nSolutions > 0 && foundImproving)
      stop
    }
  }
  
  var runtimes:List[Long] = List.empty
  /*
  * This function does no perform a conversion on Boolean variables w.r.t the fzn-oscar-cbls representation
  * */
  def getMoves(fixingMap: Map[Variable, Int], tabuVariables: Iterable[Variable] = Iterable.empty,
               currentObj: LexObj,
               bestObj: LexObj,
               improving: Boolean = true,
               maxTime:Long = Long.MaxValue): FZCPLSSol = {
    
    def fixPreviousIt(): Unit = {
      if (debugMode) {
        for ((k, v) <- inputVariables) {
          try {
            solver.add(preVariableMap(k) === fixingMap(k))
          } catch {
            case _: NoSuchElementException =>
              println("% Failed to fix: " + k + " to " + v)
          }
        }
      } else {
        solver.add(inputVariables.map {
          case (k: Variable, _: CPIntVar) =>
            preVariableMap(k) === fixingMap(k)
        })
      }
    }
    
    def onlyImprovingNeighbours(): Unit = {
      if(fzModel.search.obj == Objective.MINIMIZE || fzModel.search.obj == Objective.MAXIMIZE)
        solver.add(postObjectiveVar < currentObj.objective)
      solver.add(GlobalViolation <= currentObj.violation)
    }
    
    def postTabu(): Unit = {
      val aspiration = true
      if (aspiration) {
        val b = CPBoolVar()
        solver.add(new And(tabuVariables.map(v => preVariableMap(v) ?=== postVariableMap(v)).toArray, b))
        
        val b2 = CPBoolVar()
        fzModel.search.obj match {
          case Objective.MINIMIZE | Objective.MAXIMIZE =>
            solver.add(new And(Array(postObjectiveVar ?< bestObj.objective, GlobalViolation ?<= bestObj.violation), b2))
          case Objective.SATISFY =>
            solver.add(new And(Array(GlobalViolation ?< bestObj.violation), b2))
        }
        solver.add(new Or(Array(b, b2)))
      } else {
        tabuVariables.foreach(v => solver.add(preVariableMap(v) === postVariableMap(v)))
      }
    }
    
    solver.pushState()
    solutionMap = Map.empty
    
      _currentObj = currentObj
  
    val stats = solver.startSubjectTo(firstImproving(maxTime = Math.min(15000,maxTime)),
                                       maxDiscrepancy = Int.MaxValue,
                                       listener = null) {
      if (bestObj.violation == 0 && CurrentBest.hasValue(bestObj.objective)) {
        CurrentBest.assign(bestObj.objective)
      }
      
      fixPreviousIt()
      if(improving)
        onlyImprovingNeighbours()
      
      if (tabuVariables.nonEmpty) {
        postTabu()
      }
//      if(currentObj.violation == 0)
//        solver.add(postObjectiveVar !== currentObj.objective)
    }
    //println(neighbourhood.name)
//   println(stats)
    runtimes +:= stats.time
    solver.pop()
    solver.objective.objs.foreach(_.relax())
    solver.objective.objs.foreach(_.ensureBest())
    
    if (stats.nSols == 0) {
//      if(!stats.completed)
//        println("Search did not exhaust")
//      println("No neighbour")
      return NoSolution()
    }

//    println("Objective: " + Helper.getObjectiveFromIntBoolMap(fzModel, solutionMap))
//    println("Violation: " + solutionViolation)
    if (solutionViolation == 0) {
      Solution(Helper.getObjectiveFromIntBoolMap(fzModel, solutionMap), //solutionMap(fzModel.search.variable.get)._1,
                solutionMap.filter(kv => kv._2._2).mapValues(_._1),
                modifiedVars)
    } else {
      ViolatingSolution(solutionViolation, Helper.getObjectiveFromIntBoolMap(fzModel,
                                                                              solutionMap), //solutionMap(fzModel.search.variable.get)._1,
                         solutionMap.filter(kv => kv._2._2).mapValues(_._1),
                         modifiedVars)
    }
  }
  
  private def findDependentVarsAndCons(): Unit = {
    val exploredVars: MMap[Variable, Unit] = MMap.empty
    val exploredConstraints: MMap[Constraint, Unit] = MMap.empty
    
    // Make controlled variables terminal nodes
    for (v <- neighbourhood.getControlledAndDeclaredVariables)
      exploredVars += (v -> ())
    
    val queue: MQueue[Variable] = MQueue.empty
    neighbourhood.getDependentVariables.foreach(queue.enqueue(_))
    
    while (queue.nonEmpty) {
      val e = queue.dequeue()
      if (!exploredVars.contains(e)) {
        exploredVars += (e -> ())
        val constraints = e.cstrs
                          .filterNot(exploredConstraints.contains)
        constraints
        .foreach(c => exploredConstraints += (c -> ()))
        constraints
        .flatMap(_.getVariables)
        .filterNot(exploredVars.contains)
        .foreach(queue.enqueue(_))
      }
    }
    if (fzModel.neighbourhoods.size > 1) {
      throw new TooManyNeighbourhoodsException
    }
    dependentVariables =
      exploredVars
      .keys
      .filterNot(v => {
        v.isBound  ||
          neighbourhood.getControlledAndDeclaredVariables.contains(v) ||
          fzModel.neighbourhoods.head.subNeighbourhoods.exists(n =>
            n != neighbourhood && (n.whereVariables.contains(v) || n.itVariables.contains(v))) //|| fzModel.neighbourhoods.head.subNeighbourhoods.exists(n => n.getControlledAndDeclaredVariables.contains(v))
      }).toArray
    dependentConstraints = exploredConstraints.keys.toArray
//    println(exploredConstraints.keys.mkString(", "))
//    println(exploredVars.keys.mkString(", "))
  }
  
  private def createVariableMap(vars: Iterable[Variable]): MMap[Variable, CPIntVar] = {
    MMap(vars.map {
      case b: BooleanVariable =>
        b -> CPBoolVar(b.id)
      case v: IntegerVariable =>
        v.domain match {
          case FzDomainRange(min, max) =>
            v -> CPIntVar(min, max, v.id)
          case FzDomainSet(s) =>
            v -> CPIntVar(s, v.id)
        }
    }.toSeq: _*)
  }
  
  def getIntVar(varMap: MMap[Variable, CPIntVar])(v: Variable): CPIntVar = {
    varMap.get(v) match {
      case None if v.isBound =>
        val c = v match {
          case v: IntegerVariable if v.isBound => new CPIntVarSingleton(solver, v.value);
          case v: IntegerVariable => CPIntVar(v.value);
          case v: BooleanVariable => CPBoolVar(v.boolValue);
        }
        //println("% created new int var for " + v)
        varMap += v -> c
        c
      case Some(c) => c;
      case None => println(v)
        throw new RuntimeException
    }
  }
  
  def getBoolVar(varMap: MMap[Variable, CPIntVar])(v: Variable): CPBoolVar = {
    varMap.get(v) match {
      case None if v.isBound =>
        val c = v match {
          case v: BooleanVariable => CPBoolVar(v.boolValue);
        }
        println("% created new bool var for " + v)
        varMap += v -> c
        c
      case Some(c) => c.asInstanceOf[CPBoolVar];
    }
  }
  
  private def addConstraint(c: Constraint, varMap: MMap[Variable, CPIntVar]) {
    val cons = poster.getConstraint(c, getIntVar(varMap), getBoolVar(varMap))
    for (cs <- cons) {
      solver.add(cs._1, cs._2)
    }
  }
  
  /**
    * Returns a CPIntVar that is constrained to be equal to the violation of the posted constraint.
    */
  private def addSoftConstraint(c: Constraint, varMap: MMap[Variable, CPIntVar]): CPIntVar = {
    val (viol, cons) = poster.getSoftConstraint(c, getIntVar(varMap), getBoolVar(varMap), solver)
    for (cs <- cons) {
      solver.add(cs._1, cs._2)
    }
    viol
  }
  
  private def addMoveConstraints(): Unit = {
    neighbourhood.moves
    .foreach {
      // Warning: Don't forget that indexing starts at one!
      case FZAssignMove(lhs, rhs) =>
        solver.add(postVariableMap(lhs) === preVariableMap(rhs))
        // Set indicator variable to specify target
        solver.add(indicatorMap(lhs).constraintTrue)
        numTargetedVariables += 1
        noOps +:= (postVariableMap(lhs) ?!== preVariableMap(lhs))
      // No-op when lhs is unchanged
      case FZAssignArrayMove(lhs, index, rhs) =>
        val accessedLHS = elementVar(lhs.map(postVariableMap), preVariableMap(index) - 1)
        solver.add(accessedLHS === preVariableMap(rhs))
        // Set indicator variable to specify target
        solver.add(elementVar(lhs.map(indicatorMap), preVariableMap(index) - 1, 1))
        numTargetedVariables += 1
        // No-op when lhs is unchanged
        noOps +:= (accessedLHS
          ?!== elementVar(lhs.map(preVariableMap), preVariableMap(index) - 1))
      case FZSwapMove(lhs, rhs) =>
        solver.add(postVariableMap(lhs) === preVariableMap(rhs))
        solver.add(postVariableMap(rhs) === preVariableMap(lhs))
        // Set indicator variable to specify target
        solver.add(indicatorMap(lhs).constraintTrue)
        solver.add(indicatorMap(rhs).constraintTrue)
        numTargetedVariables += 2
        // No-op when lhs is unchanged (this implies rhs is unchanged as well)
        noOps +:= (postVariableMap(lhs) ?!== preVariableMap(lhs))
      case FZSwapArrayMove(lhs, idx1, rhs, idx2) =>
        val accessedPreLHS = elementVar(lhs.map(preVariableMap), preVariableMap(idx1) - 1)
        val accessedPostLHS = elementVar(lhs.map(postVariableMap), preVariableMap(idx1) - 1)
        val accessedPreRHS = elementVar(rhs.map(preVariableMap), preVariableMap(idx2) - 1)
        val accessedPostRHS = elementVar(rhs.map(postVariableMap), preVariableMap(idx2) - 1)
        
        solver.add(accessedPostLHS === accessedPreRHS)
        solver.add(accessedPostRHS === accessedPreLHS)
        // Set indicator variable to specify target
        solver.add(elementVar(lhs.map(indicatorMap), preVariableMap(idx1) - 1, 1))
        solver.add(elementVar(rhs.map(indicatorMap), preVariableMap(idx2) - 1, 1))
        numTargetedVariables += 2
        
        // No-op when lhs is unchanged (this implies rhs is unchanged as well)
        noOps +:= (accessedPreLHS ?!== accessedPostLHS)
      
      case e => throw MoveNotSupportedException(e.toString)
    }
    
    solver.add(sum(indicatorMap.values) === numTargetedVariables)
    solver.add(sum(noOps) > 0)
    
    indicatorMap.foreach {
      case (variable: Variable, boolVar: CPBoolVar) =>
        solver.add(boolVar.not implies (preVariableMap(variable) ?=== postVariableMap(variable)))
    }
    
    val (indicatorKeys, indicatorValues) = indicatorMap.toArray.unzip
    
    val targets = neighbourhood.moves
                  .flatMap {
                    // Warning: Don't forget that indexing starts at one!
                    case FZAssignMove(lhs, rhs) =>
                      Array(CPIntVar(indicatorKeys.indexOf(lhs)))
                    case FZAssignArrayMove(lhs, index, rhs) =>
                      val usedIndices = lhs.map(indicatorKeys.indexOf(_))
                      // Using modelling package here to do the element
                      Array(usedIndices(preVariableMap(index) - 1))
                    case FZSwapMove(lhs, rhs) =>
                      Array(CPIntVar(indicatorKeys.indexOf(lhs)), CPIntVar(indicatorKeys.indexOf(rhs)))
                    case FZSwapArrayMove(lhs, idx1, rhs, idx2) =>
                      val usedIndicesLHS = lhs.map(indicatorKeys.indexOf(_))
                      val usedIndicesRHS = rhs.map(indicatorKeys.indexOf(_))
                      Array(usedIndicesLHS(preVariableMap(idx1) - 1), usedIndicesRHS(preVariableMap(idx2) - 1))
                    case e => throw MoveNotSupportedException(e.toString)
                  }
                  .toArray
    solver.add(new AntiElement(targets, indicatorValues, Array.tabulate(indicatorValues.length)(_ => 0)))
  }
  
  
  private def addMoveConstraintsWithWrites(): Unit = {
    def arrayEq(x: Array[_ <: Any], y: Array[_ <: Any]): Boolean = {
      if (x.length != y.length) return false
      x.indices.forall(i => x(i) == y(i))
    }
    
    val genericWrites = neighbourhood.moves
                        .flatMap {
                          // Warning: Don't forget that indexing starts at one!
                          case FZAssignMove(lhs, rhs) =>
                            noOps +:= (postVariableMap(lhs) ?!== preVariableMap(lhs))
                            List(Write(Array(lhs), None, Array(preVariableMap(rhs))))
                          // No-op when lhs is unchanged
      
                          case FZAssignArrayMove(lhs, index, rhs) =>
                            val accessedLHS = elementVar(lhs.map(postVariableMap), preVariableMap(index) - 1)
                            // No-op when lhs is unchanged
                            noOps +:= (accessedLHS
                              ?!== elementVar(lhs.map(preVariableMap), preVariableMap(index) - 1))
                            List(Write(lhs, Some(Array(preVariableMap(index) - 1)), Array(preVariableMap(rhs))))
      
                          case FZSwapMove(lhs, rhs) =>
                            // No-op when lhs is unchanged (this implies rhs is unchanged as well)
                            noOps +:= (postVariableMap(lhs) ?!== preVariableMap(lhs))
                            List(Write(Array(lhs), None, Array(preVariableMap(rhs))),
                                  Write(Array(rhs), None, Array(preVariableMap(lhs))))
      
                          case FZSwapArrayMove(lhs, idx1, rhs, idx2) =>
                            val accessedPreLHS = elementVar(lhs.map(preVariableMap), preVariableMap(idx1) - 1)
                            val accessedPostLHS = elementVar(lhs.map(postVariableMap), preVariableMap(idx1) - 1)
                            val accessedPreRHS = elementVar(rhs.map(preVariableMap), preVariableMap(idx2) - 1)
                            val accessedPostRHS = elementVar(rhs.map(postVariableMap), preVariableMap(idx2) - 1)
        
                            solver.add(accessedPostLHS === accessedPreRHS)
                            solver.add(accessedPostRHS === accessedPreLHS)
                            // Set indicator variable to specify target
                            solver.add(elementVar(lhs.map(indicatorMap), preVariableMap(idx1) - 1, 1))
                            solver.add(elementVar(rhs.map(indicatorMap), preVariableMap(idx2) - 1, 1))
                            numTargetedVariables += 2
        
                            // No-op when lhs is unchanged (this implies rhs is unchanged as well)
                            noOps +:= (accessedPreLHS ?!== accessedPostLHS)
                            if (arrayEq(lhs, rhs)) {
                              List(Write(lhs, Some(Array(preVariableMap(idx1) - 1, preVariableMap(idx2) - 1)),
                                          Array(accessedPreRHS, accessedPreLHS)))
                            } else {
                              println("% In Corner Case: Swapping variables in different arrays.")
                              List(Write(lhs, Some(Array(preVariableMap(idx1) - 1)), Array(accessedPreRHS)),
                                    Write(rhs, Some(Array(preVariableMap(idx2) - 1)), Array(accessedPreLHS)))
                            }
      
                          case e => throw MoveNotSupportedException(e.toString)
                        }
    
    var canSimplify = true
    var writesQueue = genericWrites.sortBy(-_.targetedVariables.length)
    var finalWrites = List.empty[Write]
    
    while (canSimplify) {
      canSimplify = false
      // pick head, pull all eq or elem constraints and push into final writes and remove from current. Repeat.
      val currentWrite = writesQueue.head
      val (in, out) = writesQueue.partition(w => {
        if (w.indices.isEmpty) {
          currentWrite.targetedVariables.contains(w.targetedVariables.head)
        } else {
          arrayEq(currentWrite.targetedVariables, w.targetedVariables)
        }
      })
      if (out.nonEmpty) {
        writesQueue = out.sortBy(-_.targetedVariables.length)
        canSimplify = true
      }
      if (in.length > 1) {
        finalWrites :+=
          in.foldLeft(Write(currentWrite.targetedVariables, Some(Array.empty), Array.empty)) {
            (Acc, W) => {
              W match {
                case Write(targets, Some(idx), values) =>
                  Write(Acc.targetedVariables,
                         Some(Acc.indices.get ++ idx),
                         Acc.values ++ values)
                case Write(targets, None, value) =>
                  Write(Acc.targetedVariables,
                         Some(Acc.indices.get :+ CPIntVar(Acc.targetedVariables.indexOf(targets.head))),
                         Acc.values ++ value)
              }
            }
          }
      } else {
        finalWrites ++= in
      }
    }
    
    if(finalWrites.size > 1){
      if(finalWrites.exists(w =>
        finalWrites.filterNot(_ == w).exists(w2 =>
          w2.targetedVariables.filterNot(_.isBound).exists(v =>
            w.targetedVariables.contains(v))))){
        throw new RuntimeException("Writes constraints overlap, yielding invalid encoding. Correct merging not yet implemented.")
      }
    }
//    % LexObj(0,1334)
//Avg time: 76.254906
//Avg time: 38.35294
//objective = 1262;
//period_of = array1d(1..139, [1, 1, 5, 4, 2, 2, 2, 1, 1, 2, 1, 3, 3, 3, 1, 3, 3, 3, 3, 4, 4, 4, 2, 1, 2, 3, 3, 3, 3, 3, 4, 2, 4, 4, 4, 4, 1, 1, 1, 4, 5, 6, 3, 2, 6, 3, 2, 3, 2, 3, 4, 6, 4, 3, 5, 1, 4, 6, 2, 3, 2, 5, 1, 6, 1, 5, 3, 2, 2, 2, 1, 4, 5, 1, 5, 2, 2, 3, 6, 2, 2, 4, 2, 5, 3, 3, 3, 3, 4, 1, 1, 1, 3, 6, 2, 3, 5, 5, 2, 2, 3, 5, 3, 3, 1, 3, 4, 1, 4, 3, 4, 5, 5, 3, 5, 5, 6, 5, 6, 4, 5, 5, 5, 1, 6, 1, 6, 6, 6, 1, 1, 6, 2, 3, 6, 6, 6, 6, 6 ]);
//----------
    solver.add(sum(noOps) > 0)
    finalWrites.foreach {
      case Write(targets, Some(indices), values) =>
        solver.add(new Writes(targets.map(postVariableMap), targets.map(preVariableMap), indices, values))
      case Write(target, None, value) =>
        solver.add(postVariableMap(target.head) === value.head)
    }
    encodedMoves = finalWrites.toArray
  }
}


