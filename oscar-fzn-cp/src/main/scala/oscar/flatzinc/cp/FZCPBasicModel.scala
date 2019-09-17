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

package oscar.flatzinc.cp

import oscar.algo.branchings.LCSearchSimplePhaseAssign
import oscar.algo.search.{Branching, DFSearch}
import oscar.cp._
import oscar.cp.core.CPPropagStrength
import oscar.flatzinc.model.{Constraint, _}

import scala.collection.mutable.{Map => MMap}


/**
  * @author Gustav Bjordal
  * @author Jean-Noel Monette
  */
class FZCPBasicModel(val pstrength: oscar.cp.core.CPPropagStrength = CPPropagStrength.Automatic,
                     val ignoreUnkownConstraints: Boolean = false) {
  
  def printVars(): Unit = {
    println(dictVars.mkString("\n"))
  }
  
  implicit val solver: CPSolver = CPSolver(pstrength)
  solver.silent = true
  val poster = new CPConstraintPoster(pstrength)
  
  
  val dictVars: MMap[Variable, CPIntVar] = MMap.empty[Variable, CPIntVar]
  val solutionMap: MMap[Variable, Int] = MMap.empty[Variable, Int]
  
  def getIntVar(v: Variable): CPIntVar = {
    dictVars.get(v) match {
      case None if v.isBound =>
        val c = v match {
          case v: IntegerVariable => CPIntVar(v.value);
          case v: BooleanVariable => CPBoolVar(v.boolValue);
        }
        dictVars += v -> c
        c
      case Some(c) => c;
      
    }
  }
  
  def getBoolVar(v: Variable): CPBoolVar = {
    dictVars.get(v) match {
      case None if v.isBound =>
        val c = v match {
          case v: BooleanVariable => CPBoolVar(v.boolValue);
        }
        dictVars += v -> c
        c
      case Some(c) => c.asInstanceOf[CPBoolVar];
    }
  }
  
  def createVariables(variables: Iterable[Variable]) {
    for (v <- variables) {
      dictVars(v) = v match {
        case bv: BooleanVariable if bv.isTrue => CPBoolVar(b = true, v.id)
        case bv: BooleanVariable if bv.isFalse => CPBoolVar(b = false, v.id)
        case _: BooleanVariable => CPBoolVar(v.id)
        case iv: IntegerVariable => iv.domain match {
          case FzDomainRange(min, max) => CPIntVar(min, max, v.id)
          case FzDomainSet(s) => CPIntVar(s, v.id)
          case _ => throw new RuntimeException("unknown domain")
        }
      }
    }
  }
  
  def createConstraints(constraints: Iterable[Constraint]) {
    //TODO: Put all the added cstrs in a ArrayBuffer and then post them all at once.
    for (c <- constraints) {
      //TODO: Take consistency annotation to post constraints.
      try {
        val cons = poster.getConstraint(c, getIntVar, getBoolVar)
        add(cons)
      } catch {
        case _: scala.MatchError if ignoreUnkownConstraints => Console.err.println("% ignoring in CP: " + c)
      }
    }
  }
  
  var GlobalViolation: Option[CPIntVar] = None
  var ViolationVariable: Option[Variable] = None
  
  def createSoftAndHardConstraints(constraints: Iterable[Constraint]) {
    var violVars: Array[CPIntVar] = Array.empty
    for (c <- constraints) {
      if (c.definedVar.isDefined) {
        val cons = poster.getConstraint(c, getIntVar, getBoolVar)
        add(cons)
      } else {
        val (violVar, cons) = poster.getSoftConstraint(c, getIntVar, getBoolVar, solver)
        add(cons)
        if (!violVar.isBound) {
          violVars :+= violVar
        }
      }
    }
    val maxViol = 10000
    GlobalViolation = Some(CPIntVar(0, maxViol, "GlobalViolation"))
    solver.add(oscar.cp.sum(violVars, GlobalViolation.get))
    ViolationVariable = Some(IntegerVariable("GlobalViolation", FzDomainRange(0, maxViol)))
    dictVars(ViolationVariable.get) = GlobalViolation.get
  }
  
  def add(c: Array[(oscar.cp.Constraint, oscar.cp.core.CPPropagStrength)]) {
    for (cs <- c) {
      solver.add(cs._1, cs._2)
    }
  }
  
  def add(c: oscar.cp.Constraint) {
    solver.add(c)
  }
  
  def add(cs: Array[oscar.cp.Constraint]) {
    solver.add(cs)
  }
  
  var ObjectiveVariable:Option[oscar.flatzinc.model.Variable] = None
  var ObjectiveMode:oscar.flatzinc.model.Objective.Value = _
  
  def createObjective(obj: oscar.flatzinc.model.Objective.Value, objVar: Option[Variable] = None) {
    ObjectiveVariable = objVar
    ObjectiveMode = obj
    if (GlobalViolation.isDefined) {
      obj match {
        case Objective.SATISFY =>
          solver.minimize(GlobalViolation.get)
        case Objective.MAXIMIZE =>
//          solver.minimize(GlobalViolation.get, -getIntVar(objVar.get))
          solver.minimize(oscar.cp.plus(GlobalViolation.get, -getIntVar(objVar.get)))
        case Objective.MINIMIZE =>
//          solver.minimize(GlobalViolation.get, getIntVar(objVar.get))
        solver.minimize(oscar.cp.plus(GlobalViolation.get, getIntVar(objVar.get)))
          //TODO: Pareto should be used but currently does not work because I cannot reset it.
          //  as a result, the violation is never allowed to go up.
//          solver.paretoMinimize(GlobalViolation.get, getIntVar(objVar.get))
      }
    }
    else {
      obj match {
        case Objective.SATISFY => solver.minimize(GlobalViolation.get)
        case Objective.MAXIMIZE => minimize(-getIntVar(objVar.get))
        case Objective.MINIMIZE => minimize(getIntVar(objVar.get))
      }
    }
  }
  
  def getMinFor(v: IntegerVariable): Int = {
    getIntVar(v).getMin
  }
  
  def getMaxFor(v: IntegerVariable): Int = {
    getIntVar(v).getMax
  }
  
  def getMinFor(v: BooleanVariable): Int = {
    getBoolVar(v).getMin
  }
  
  def getMaxFor(v: BooleanVariable): Int = {
    getBoolVar(v).getMax
  }
  
  def createDefaultSearch(): Unit = {
    //TODO: Take into account the search annotations
    solver.search(oscar.cp.binaryLastConflict(dictVars.filterKeys(!_.isIntroduced).values.toArray))
  }
  
  def createPhaseAssignSearch(): Unit = {
    val searchVars = dictVars.filterKeys(!_.isIntroduced).values.toArray
    solver.search(new LCSearchSimplePhaseAssign(searchVars, searchVars(_).size, searchVars(_).min))
  }
  
  def getPhaseAssignFirstFail():LCSearchSimplePhaseAssign = {
    val searchVars = dictVars.filterKeys(!_.isIntroduced).values.toArray
    new LCSearchSimplePhaseAssign(searchVars, searchVars(_).size, searchVars(_).min)
  }
  
  def getPhaseAssignFirstFail(searchVars:Array[CPIntVar]):LCSearchSimplePhaseAssign = {
    new LCSearchSimplePhaseAssign(searchVars, searchVars(_).size, searchVars(_).min)
  }
  
  def createRandomSearch(): Unit = {
    //TODO: Take into account the search annotations
    val searchVars = dictVars.filterKeys(!_.isIntroduced).values.toArray
    solver.search(oscar.cp.conflictOrderingSearch(searchVars, searchVars(_).size, searchVars(_).randomValue))
  }
  
  def createRandomSearch(searchVars: Array[CPIntVar]): Unit = {
    //TODO: Take into account the search annotations
    //solver.search(oscar.cp.conflictOrderingSearch(searchVars, searchVars(_).size, searchVars(_).min))
    solver.search(oscar.cp.binaryFirstFail(searchVars, _.randomValue))
  }
  
  def setSearch(search: Branching): Unit = {
    solver.search(search)
  }
  
  @deprecated
  def tightenBestObj(obj: Int, isMinimize: Boolean): Unit = {
    if (isMinimize) {
      solver.objective.objs.foreach(o => solver.add(o.objVar < obj))
    } else {
      solver.objective.objs.foreach(o => solver.add(o.objVar > obj))
    }
  }
  
  @deprecated
  def tightenCutBestObj(obj: Int, isMinimize: Boolean): Unit = {
    if (isMinimize) {
      solver.objective.objs.foreach(o => solver.addCut(o.objVar < obj))
    } else {
      solver.objective.objs.foreach(o => solver.addCut(o.objVar > obj))
    }
  }
  
  private def resetBounds(): Unit = {
    solver.objective.objs.foreach(_.relax())
    solver.objective.objs.foreach(_.ensureBest())
  }
  
  var solutionPrinter: FZSolution = _
  var currentFoundViolation = GlobalViolation.getOrElse(CPIntVar(0)).max
  var foundSolution = false
  var currentFoundObjective:Int = _

  def startSearch():(Boolean,MMap[Variable,Int]) = {
    onSolution {
      for((k,v) <- dictVars){
        v match {
          case b:CPBoolVar =>
            solutionMap(k) = 1-b.min //0 is true and >0 is false in CBLS solver.
          case i:CPIntVar =>
            solutionMap(k) = i.min
        }
      }
    }

    val stats = solver.start(nSols = 1)

    if(stats.nSols == 0){
      println("% No solution found")
      return (false, MMap.empty)
    }
    (true, solutionMap)
  }

  def startSearch(targetObjective:Option[Int],
                  firstImproving:Boolean = true,
                   flipBooleans: Boolean = true,
                  verbose: Boolean = false,
                  timeLimit: Int = Int.MaxValue,
                  canExceedTimeLimit: Boolean = false,
                  nSols: Int = 1,
                  resetBoundsOnSol:Boolean = true,
                  maxTime:Long = Long.MaxValue): (Boolean, MMap[Variable, Int]) = {
    onSolution {
      // TODO this could be faster if we specify outputVariables (like all non-defined vars)
      for ((k, v) <- dictVars if v.isBound) {
        v match {
          case b: CPBoolVar if flipBooleans =>
            solutionMap(k) = 1 - b.min //0 is true and >0 is false in CBLS solver.
          case b: CPBoolVar =>
            solutionMap(k) = b.min
          case i: CPIntVar =>
            solutionMap(k) = i.min
        }
      }
      currentFoundViolation = if(ViolationVariable.isDefined) dictVars(ViolationVariable.get).min else 0
      foundSolution = true
      if(ObjectiveVariable.isDefined)
        currentFoundObjective = dictVars(ObjectiveVariable.get).min
    }
    
    foundSolution = false
    val stats = if (canExceedTimeLimit) {
      //TODO: This is experimental
      val stopTime = Math.min(maxTime,(timeLimit * 1000)) + System.currentTimeMillis()
      solver.startSubjectTo((s: DFSearch) => {
        var stop = false
        stop |= s.nSolutions > 0 && System.currentTimeMillis() >= stopTime
        stop |= firstImproving && foundSolution &&
          currentFoundViolation == 0 &&
          (ObjectiveVariable.isEmpty || targetObjective.isEmpty || (ObjectiveMode match {
            case Objective.MINIMIZE =>
              currentFoundObjective <= targetObjective.get
            case Objective.MAXIMIZE =>
              currentFoundObjective >= -targetObjective.get // negative because
          }))
        stop
      }, Int.MaxValue, null){
//        if(targetObjective.isDefined)
//          solver.add(dictVars(ObjectiveVariable.get) <= targetObjective.get)
      }
    } else {
      solver.start(nSols = nSols, timeLimit = Math.min(timeLimit,maxTime).toInt)
    }
    if(resetBoundsOnSol)
      resetBounds()
    solver.searchEngine.clearOnSolution()
    if (verbose) {
      println("Solving Done")
      println(stats)
    }
    if (stats.nSols == 0) {
      println("% No solution found")
      return (false, MMap.empty)
    }
    (true, solutionMap)
  }
  
  def push(): Unit = solver.pushState()
  
  def pop(): Unit = solver.pop()
}