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

import oscar.algo.Inconsistency
import oscar.cp.{Constraint, _}
import oscar.flatzinc.Options
import oscar.flatzinc.parser.FZParser

import scala.collection.mutable.{Map => MMap, Set => MSet}
import oscar.flatzinc.model.{Constraint, _}
import oscar.flatzinc.UnsatException
import oscar.flatzinc.transformation.FZModelTransformations

import scala.util.Random

/**
  * CP model specialised for solving a partial assignment
  * is essentially a cleaned version of FZCPSolver
  *
  * @author Gustav Bjordal
  */
class FZCPCompletionSolver(val model:oscar.flatzinc.model.FZProblem,
                           val pstrength: oscar.cp.core.CPPropagStrength = oscar.cp.Medium,
                           val ignoreUnkownConstraints: Boolean = false) {
  def printVars(): Unit = {
    println(dictVars.mkString("\n"))
  }

  implicit val solver: CPSolver = CPSolver(pstrength)
  solver.pushState()
  solver.silent = true

  val poster = new CPConstraintPoster(pstrength)
  val dictVars: MMap[String, CPIntVar] = MMap.empty[String,CPIntVar]
  val dictConstraints: MMap[oscar.flatzinc.model.Constraint, Array[oscar.cp.Constraint]] = MMap.empty[oscar.flatzinc.model.Constraint, Array[oscar.cp.Constraint]]

  var completeModel:Boolean = true

  def getIntVar(v:Variable):CPIntVar = {
    dictVars.get(v.id) match {
      case None if v.isBound =>
        val c = v match{
          case v:IntegerVariable => CPIntVar(v.value);
          case v:BooleanVariable => CPBoolVar(v.boolValue);
        }
        dictVars += v.id -> c
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
        dictVars += v.id -> c
        c
      case Some(c) => c.asInstanceOf[CPBoolVar];
    }
  }
  def createVariables(){
    for(v <- model.variables){
      dictVars(v.id) = v match{
        case bv:BooleanVariable if bv.isTrue => CPBoolVar(b = true)
        case bv:BooleanVariable if bv.isFalse => CPBoolVar(b = false)
        case bv:BooleanVariable => CPBoolVar()
        case iv:IntegerVariable => iv.domain match{
          case FzDomainRange(min, max) => CPIntVar(min, max)
          case FzDomainSet(s) => CPIntVar(s)
          case _ => throw new RuntimeException("unknown domain")
        }
      }
    }
  }
  def createConstraints(constraints:Array[oscar.flatzinc.model.Constraint]){
    //TODO: Add a try catch for if the problem fails at the root.
    //TODO: Put all the added cstrs in a ArrayBuffer and then post them all at once.
    for(c <- constraints){
      //TODO: Take consistency annotation to post constraints.
      val cons = poster.getConstraint(c,getIntVar,getBoolVar)
      dictConstraints += c -> cons.map(_._1)
      add(cons)
    }
  }

  def add(c:Array[(oscar.cp.Constraint,oscar.cp.core.CPPropagStrength)]){
    for(cs <- c){
      solver.add(cs._1,cs._2)
    }
  }
  
  private def resetBounds(): Unit = {
    solver.objective.objs.foreach(_.relax())
    solver.objective.objs.foreach(_.ensureBest())
  }
  
  
  def createObj() = {
    if (model.search.variable.isDefined) {
      model.search.obj match {
        case Objective.MAXIMIZE => maximize(dictVars(model.search.variable.get.id))
        case Objective.MINIMIZE => minimize(dictVars(model.search.variable.get.id))
      }
    }
  }

  def fixAndSolve(vars: Iterable[(String,Int)], failureLimit:Int = 10000, nSols: Int = 2):(Boolean, String, MMap[String,Int]) = {
    val verbose = false
    var fixedVariables = List.empty[String]
    var solutionMap = MMap.empty[String,Int]
    var lastFixed = vars.head._1
    solver.pushState() // PUSH FIX VARS
    
    try {
//      solver.add(vars.map(v => dictVars(v._1) === v._2))
//      solver.update()
      for ((name, v) <- Random.shuffle(vars)) {
        lastFixed = name
     //   println("Fixing " + name + " to " + v + ". Fixed " + fixedVariables.length)
        solver.add(dictVars(name) === v)
        solver.update()
      }

    }catch{
      case inconsistency:Inconsistency =>
        solver.pop() // POP FIX VARS
        return (false, lastFixed, solutionMap)
      case e:RuntimeException =>
        solver.pop() // POP FIX VARS
        return (false, lastFixed, solutionMap)
      case e:Exception =>
        println("% Something is wrong in FZCPCompletionSolver.fixAndSolve")
    }
    solver.pushState() // PUSH SEARCH
    
    val searchVars = dictVars.values.toArray
    onSolution {
                 for((k,v) <- dictVars){
                   v match {
                     case b:CPBoolVar =>
                       solutionMap(k) = b.min
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
    val stats = solver.start(failureLimit = failureLimit, timeLimit=30,  nSols = nSols)
    

    solver.pop() // POP SEARCH
    solver.searchEngine.clearOnSolution()
//    solver.resetCuts()
    resetBounds()

    if(stats.nSols == 0){
      solver.pop() // POP FIX VARS
      if(verbose)
        println("% No solution found after failures: " + stats.nFails + ", time: " + stats.time)
      return (false, "", solutionMap)
    }

    if(verbose) {
      if (stats.completed) println("% #########")
      //println(stats)
      if(model.search.variable.isDefined)
        println("% CP solver Objective: " + solutionMap(model.search.variable.get.id))
    }
    solver.pop() // POP FIX VARS

    //println("Objective bounds: " + dictVars(model.search.variable.get.id).min + " .. " + dictVars(model.search.variable.get.id).max )

    (true, "", solutionMap)
  }

  def updateObjBounds(): Boolean = {
      model.search.obj match{
        case Objective.SATISFY =>
        case Objective.MAXIMIZE =>
          getIntVar(model.search.variable.get).updateMin(model.search.variable.get.min)
        case Objective.MINIMIZE =>
          getIntVar(model.search.variable.get).updateMax(model.search.variable.get.max)
      }
      try{
        solver.propagate()
        true
      }catch{
        case incons: Inconsistency =>
          false
      }
  }
}