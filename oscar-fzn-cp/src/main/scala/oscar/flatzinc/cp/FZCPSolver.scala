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
/**
 * @author Jean-Noel Monette
 */
package oscar.flatzinc.cp


import oscar.algo.Inconsistency
import oscar.cp._
import oscar.flatzinc.Options
import oscar.flatzinc.parser.FZParser

import scala.collection.mutable.{Map => MMap, Set => MSet}
import oscar.flatzinc.model._
import oscar.flatzinc.UnsatException
import oscar.flatzinc.transformation.FZModelTransformations

import scala.util.Random
class FZCPModel(val model:oscar.flatzinc.model.FZProblem, val pstrength: oscar.cp.core.CPPropagStrength = oscar.cp.Medium, val ignoreUnkownConstraints: Boolean = false) {






  def printVars() = {
    println(dictVars.mkString("\n"))
  }

  implicit val solver: CPSolver = CPSolver(pstrength)
  solver.pushState()
  solver.silent = true
  val poster = new CPConstraintPoster(pstrength);
  val dictVars = MMap.empty[String,CPIntVar]
  val dictConstraints = MMap.empty[oscar.flatzinc.model.Constraint, Array[oscar.cp.Constraint]]
  val dictGuards = MMap.empty[oscar.flatzinc.model.Constraint, oscar.cp.CPBoolVar]

  var completeModel:Boolean = true

  def getIntVar(v:Variable):CPIntVar = {
    dictVars.get(v.id) match {
      case None if v.isBound =>
        val c = v match{
          case v:IntegerVariable => CPIntVar(v.value);
          case v:BooleanVariable => CPBoolVar(v.boolValue);
        }
        dictVars += v.id -> c;
        c
  	  case Some(c) => c;
	  }
  }
  def getBoolVar(v:Variable):CPBoolVar = {
	dictVars.get(v.id) match {
	  case None if v.isBound =>
	    val c = v match{
	      case v:BooleanVariable => CPBoolVar(v.boolValue);
	    }
	    dictVars += v.id -> c;
	    c
	  case Some(c) => c.asInstanceOf[CPBoolVar];
	}
  }
  def createVariables(){
    for(v <- model.variables){
      dictVars(v.id) = v match{
        case bv:BooleanVariable if bv.isTrue => CPBoolVar(true)
        case bv:BooleanVariable if bv.isFalse => CPBoolVar(false)
        case bv:BooleanVariable => CPBoolVar()
        case iv:IntegerVariable => iv.domain match{
          case FzDomainRange(min, max) => CPIntVar(min, max)
          case FzDomainSet(v) => CPIntVar(v)
          case _ => throw new RuntimeException("unknown domain")
        }
      }
    }
  }
  def createConstraints(constraints:MSet[oscar.flatzinc.model.Constraint]){
    //TODO: Add a try catch for if the problem fails at the root.
    //TODO: Put all the added cstrs in a ArrayBuffer and then post them all at once.
    for(c <- constraints){
      //TODO: Take consistency annotation to post constraints.
      try{
        val cons = poster.getConstraint(c,getIntVar,getBoolVar)
        dictConstraints += c -> cons.map(_._1)
        if(cons.isEmpty)
          completeModel = false
        else
          add(cons)
      }catch{
        case e: scala.MatchError if ignoreUnkownConstraints => Console.err.println("% ignoring in CP: "+c)
      }
    }
  }
  //TODO: why do we need a separate method?
  def add(c:Array[(oscar.cp.Constraint,oscar.cp.core.CPPropagStrength)]){
    for(cs <- c){
      solver.add(cs._1,cs._2)
    }
  }

  def add(c:Array[(oscar.cp.Constraint,oscar.cp.core.CPPropagStrength)],guard:CPBoolVar){
    for(cs <- c){
      solver.add(cs._1 when guard,cs._2)
    }
  }

  def disableSlowConstraints(constraints:List[oscar.flatzinc.model.Constraint]): Unit = {
    def isSlow(c:oscar.flatzinc.model.Constraint):Boolean = {
      c.isInstanceOf[oscar.flatzinc.model.circuit] ||
        c.isInstanceOf[oscar.flatzinc.model.subcircuit] ||
        c.isInstanceOf[oscar.flatzinc.model.all_different_int] ||
          c.isInstanceOf[oscar.flatzinc.model.inverse]
    }
    solver.popAll()
    solver.pushState()
    val filteredConstraints = model.constraints.filterNot( c => constraints.contains(c)
      && isSlow(c)
    )
    createConstraints(filteredConstraints)
  }

  def createObjective(){
    model.search.obj match{
     case Objective.SATISFY =>
     case Objective.MAXIMIZE => maximize(getIntVar(model.search.variable.get))
     case Objective.MINIMIZE => minimize(getIntVar(model.search.variable.get))
    }
  }

  def fix(vars: Iterable[(String,Int)]):(Boolean,List[String]) = {
    var fixedVariables = List.empty[String]
    solver.pushState()
    try {
      for ((name, v) <- Random.shuffle(vars)) {
        fixedVariables = name :: fixedVariables
        //println("Fixing " + name + " to " + v)
        solver.add(dictVars(name) === v)
        //dictVars(name).assign(v)
      }
    }catch{
      case e:RuntimeException =>
        //println(e)
        solver.pop()
        return (false, fixedVariables)
    }
    return (true,fixedVariables)
  }

  def fixAndSolve(vars: Iterable[(String,Int)]):(Boolean,List[String],MMap[String,Int]) = {

    val verbose = true

    //println("Fixing variables. Current stack size is: " + solver.asInstanceOf[ReversibleContext].toString)
    var fixedVariables = List.empty[String]
    var solutionMap = MMap.empty[String,Int]
    solver.pushState() // PUSH FIX VARS
    try {
      for ((name, v) <- Random.shuffle(vars)) {
        fixedVariables = name :: fixedVariables
        //println("Fixing " + name + " to " + v)
        solver.add(dictVars(name) === v)
        //dictVars(name).assign(v)
        solver.update()
      }
    }catch{
      case inconsistency:Inconsistency =>
        //println("Inconsistency after adding: " + fixedVariables.mkString(", "))
        solver.pop()
        return (false, fixedVariables,solutionMap)
      case e:RuntimeException =>
        //println(e + " after fixing " + fixedVariables.mkString(", "))
        solver.pop()
        return (false, fixedVariables,solutionMap)
      case e:Exception =>
        println("% Something is wrong in FZCPSolver.fixAndSolve")
    }
    solver.pushState() // PUSH SEARCH

    if(model.search.variable.isDefined) {
      minimize(dictVars(model.search.variable.get.id))
    }

    val searchVars = dictVars.values.toArray
    onSolution {
                 for((k,v) <- dictVars){
                    v match {
                      case b:CPBoolVar =>
                        solutionMap(k) = 1-b.min
                      case i:CPIntVar =>
                        solutionMap(k) = i.min
                    }
                 }
               }

    search {
             oscar.cp.conflictOrderingSearch(searchVars,searchVars(_).size, searchVars(_).randomValue)
             //oscar.cp.binaryFirstFail(dictVars.values.toSeq)
           }

    //TODO: better failure limit?
    val stats = solver.start(failureLimit = 100000, timeLimit=120)

    solver.pop() // POP SEARCH

    if(stats.nSols == 0){
      solver.pop() // POP FIX VARS
      if(verbose)
        println("% No solution found after failures: " + stats.nFails)
      return (false, List.empty,solutionMap)
    }

    if(verbose) {
      if (stats.completed) println("##########")
      println(stats)
      //println(solutionMap.mkString(", "))
    }
    solver.pop() // POP FIX VARS

    return (true,List.empty,solutionMap)
  }

  def updateBestObjectiveValue(value: Int): Boolean = {
    try{
      model.search.obj match{
     case Objective.SATISFY =>
     case Objective.MAXIMIZE => getIntVar(model.search.variable.get).updateMin(value+1)
     case Objective.MINIMIZE => getIntVar(model.search.variable.get).updateMax(value-1)
    }
      solver.propagate()
      true
    }catch{
      case incons: Inconsistency =>
        false
    }
  }
  def getMinFor(v:IntegerVariable): Int = {
    getIntVar(v).getMin
  }
  def getMaxFor(v:IntegerVariable): Int = {
    getIntVar(v).getMax
  }
  def getMinFor(v:BooleanVariable): Int = {
    getBoolVar(v).getMin
  }
  def getMaxFor(v:BooleanVariable): Int = {
    getBoolVar(v).getMax
  }
  def handleSolution() = {
     model.solution.handleSolution(
      (s: String) => dictVars.get(s) match {
        case Some(intVar) =>
          intVar.value + ""
        case r => if(s=="true" || s=="false") s
        else try{
          s.toInt.toString()
        }catch{
          case e: NumberFormatException => {
            throw new Exception("Unhappy: "+r+ " "+s)
          }
        }
     });
   }
  def createSearch() = {
    //TODO: Take into account the search annotations
    val searchVars = dictVars.values.toArray
    solver.search(oscar.cp.conflictOrderingSearch(searchVars, searchVars(_).size, searchVars(_).min))
  }

  //Not clear if there is any advantage to keep this over setIntermediate..
  def updateIntermediateModelDomains(): Boolean ={
    var tmpV:Variable = null;
    try{
      for(v <- model.variables){
        tmpV = v
        v match{
          case bv:BooleanVariable =>
            if(getMinFor(bv)>=1)bv.bind(true)
            if(getMaxFor(bv)<=0)bv.bind(false)
          case iv:IntegerVariable =>
            if(getIntVar(iv).isContinuous) {
              iv.geq(getMinFor(iv))
              iv.leq(getMaxFor(iv))
            }else{
              iv.intersect(FzDomainSet(getIntVar(iv).iterator.toSet))
            }
        }
      }
    }catch{
      case e:UnsatException =>
        println(e)
        println(tmpV)
        println("Failed to update intermediate model domains")
        false
    }
    true
  }

  def setIntermediateModelDomains(): Boolean ={
    var tmpV:Variable = null;
    try{
      for(v <- model.variables){
        tmpV =v
        v match{
          case bv:BooleanVariable =>
            bv.setDomain(getBoolVar(bv).iterator.toSet)
          case iv:IntegerVariable =>
            if(getIntVar(iv).isContinuous) {
              iv.setDomain(getMinFor(iv) to getMaxFor(iv))
            }else{
              iv.setDomain(getIntVar(iv).iterator.toSet)
            }
        }
      }
    }catch{
      case e:UnsatException =>
        println("Failed to set intermediate model domains")
        false
    }
    true
  }
}

class FZCPSolver {
  val pstrength = oscar.cp.Medium

  def solve(opts: Options){
    val log = opts.log();
    log("start")
    val model = FZParser.readFlatZincModelFromFile(opts.fileName,log, false).problem;


    log("Parsed.")
    FZModelTransformations.propagate(model)(log)
    FZModelTransformations.simplify(model)(log)
    log("initial variable reduction (to avoid overflows)")

    //TODO: Find binary constraints that can be used for views.
    val cpmodel = new FZCPModel(model)

    cpmodel.createVariables();
    log("created variables")

    cpmodel.createConstraints(model.constraints);
    log("constraints posted")

    cpmodel.createObjective();
    log("objective created")

    cpmodel.createSearch()
    log("search created")

    cpmodel.solver.onSolution{
      //println("found")
      cpmodel.handleSolution()
    }

    //TODO: search for more than one solution for optimisation
    //TODO: Remove the time spent in parsing and posting
    val stats = cpmodel.solver.start(nSols= Int.MaxValue,timeLimit=60*15)
    if(stats.completed) println("==========")
    log(stats.toString)



  }
}
