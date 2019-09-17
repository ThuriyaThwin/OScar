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
 * @author Gustav Björdal
 * @author Jean-Noël Monette
 */
package oscar.flatzinc.cbls.support

import scala.collection.mutable.{Map => MMap, Set => MSet}
import oscar.cbls.IntVarObjective
import oscar.cbls.core.computation.{AbstractVariable, CBLSIntVar, ChangingIntValue, IntValue}
import oscar.cbls.core.constraint.ConstraintSystem
import oscar.cbls.lib.invariant.logic._
import oscar.flatzinc.cbls.FZCBLSModel
import oscar.cbls.core.computation.IntValue
import oscar.cbls.core.objective.{Objective => CBLSObjective}
import oscar.cbls.lib.invariant.numeric._
import oscar.cbls.lib.search.LinearSelectors
import oscar.flatzinc.cp.FZCPCompletionSolver
import oscar.flatzinc.model.{BooleanVariable, Objective}

import scala.collection.mutable




abstract class SearchProcedure extends LinearSelectors{
  
  def run(): Unit
  def selectMinImb[R,S](r: Iterable[R] , s: R => Iterable[S],f: (R,S) => Int, st: ((R,S) => Boolean) = ((r:R, s:S) => true)): (R,S) = {
    //TODO: check that it is fine
    val flattened:Iterator[(R,S)] = for (rr <- r.toIterator; ss <- s(rr).toIterator) yield (rr,ss)
    selectMin[(R,S)](flattened.toIterable)((rands:(R,S)) => {/*Console.err.println(rands);*/ f(rands._1,rands._2)}, (rands:(R,S)) => st(rands._1,rands._2))
  }
  
  def showViolatedConstraints(c: ConstraintSystem){
    for(cc <- c.violatedConstraints){
      println(cc + " "+cc.violation.value)
    }
  }
  def getNumIterations(): Int
}

class Chain(val a: SearchProcedure*) extends SearchProcedure {
  def run() = {
    a.foreach(_.run())
  }

  override def getNumIterations(): Int = a.map(_.getNumIterations()).sum
}

class ActionSearch(action:() => Unit) extends SearchProcedure {
  def run() = action()
  override def getNumIterations(): Int = 0
}
class FakeSearch extends SearchProcedure {
  def run() = {}
  override def getNumIterations(): Int = 0
}

class GreedySearch(val level: Int = 1, val m: FZCBLSModel,val sc: SearchControl) extends SearchProcedure {
  assert(level > 0 && level < 4)
  val log = m.log
  var it = 0
  def run(){
    it = 0
    log("Starting Greedy Search level "+level)
    log("Starting Violation: "+m.objective.violation.value)
    //val varval = for (x <- m.vars; v <- x.domain) yield (x,v)
    if(m.vars.length>0){
      sc.handlePossibleSolution();
      var cont = true;
      while(cont && !sc.stop()){
        val varval = for (x <- m.vars.filter(m.c.violation(_).value>0); v <- x.domain) yield (x,v)
        val cur = m.objective.objective.value
        val move = level match {
          case 1 => selectFirst(varval.map(List(_)),(vv:List[(CBLSIntVar,Int)]) => cur > m.objective.objective.assignVal(vv))
          case 2 => val x:Iterator[List[(CBLSIntVar,Int)]] = varval.iterator.flatMap(v => varval.iterator.map(v2 => List(v,v2)))
            selectFirst(x.toIterable,(vv:List[(CBLSIntVar,Int)]) => cur > m.objective.objective.assignVal(vv))
          case 3 => val x:Iterator[List[(CBLSIntVar,Int)]] = varval.iterator.flatMap(v1 => varval.iterator.flatMap(v => varval.iterator.map(v2 => List(v1,v,v2))))
            selectFirst(x.toIterable,(vv:List[(CBLSIntVar,Int)]) => cur > m.objective.objective.assignVal(vv))
        }
        if(move != null && m.objective.objective.assignVal(move)<cur){
          move.foreach{ case (x,v) => x := v}
          sc.handlePossibleSolution
          it +=1;
        }else cont = false
      }
    }
    log("Done Greedy Search at "+m.getWatch())
    log("Ending Violation: "+m.objective.violation.value)
    log("Nb Moves: "+it)
  }

  override def getNumIterations(): Int = it
}

class SimpleLocalSearch(val m:FZCBLSModel,val sc: SearchControl, improvingRounds:Int = 3) extends SearchProcedure {
  val violation: Array[IntValue] = m.vars.map(m.c.violation(_)).toArray;
  val log = m.log
  var it = 0
  def run(){
    it = 0
    if(m.vars.length>0) {
      var improving = improvingRounds;
      var i = RandomGenerator.nextInt(violation.length);
      var lastImproved = i;
      var bestObj = Int.MaxValue

      log("Starting Simple Local Search")
      log("Starting Violation: " + m.objective.violation.value)
      if (m.vars.length > 0 ) {
        sc.handlePossibleSolution();
        while (improving > 0 && !sc.stopOnTime()) {
          val currentVar = m.vars(i);
          if (violation(i).value > 0) {
            //val k = selectMin(currentVar.domain)(k=> m.objective.objective.assignVal(currentVar,k))
            val currentObj = m.objective.objective.value
            val k = if (currentVar.domain.size > 50000) {
              selectMin(RandomGenerator.shuffle(currentVar.domain).take(50000))((k: Int) => m.objective.objective.assignVal(currentVar, k))
            } else {
              selectMin(currentVar.domain)(k => m.objective.objective.assignVal(currentVar, k))
            }
            if (k != currentVar.value) {
              val obj = m.objective.objective.value
              currentVar := k;
              sc.handlePossibleSolution();
              it += 1;
              if (m.objective.objective.value < bestObj) {
                lastImproved = i;
                improving = improvingRounds
                bestObj = m.objective.objective.value
              }
            }
          }
          i += 1;
          if (i == m.vars.length) {
            i = 0;
            //log(2,"turned around "+m.objective.objective.value)
          }
          if (i == lastImproved)
            improving -= 1;
        }
      }
    }
    log("Done Simple Local Search at "+m.getWatch())
    log("Ending Violation: "+m.objective.violation.value)
    log("Nb Moves: "+it)
  }

  override def getNumIterations(): Int = it
}

class SearchControl(val m: FZCBLSModel, val objLB:Int, val MaxTimeMilli: Int,val stopOnSat:Boolean){

  //TODO: Set the timeout to be runtime based rather than deadline based.
  val searchVariables = m.neighbourhoods.foldLeft(Set.empty[CBLSIntVar])((acc: Set[CBLSIntVar], x: Neighbourhood) => acc ++ x.getVariables().filterNot(_.isInstanceOf[StoredCBLSIntConst])).toArray

  var bestSolution = Array.empty[Int]
  var bestSolutionOutput = ""
  var foundSolution = false

  var lastBestKnownObjective = Int.MaxValue
  var bestKnownObjective = Int.MaxValue
  var timeOfBestObjective = -1l
  //var bestKnownViolation = Int.MaxValue
  var bestPair = (Int.MaxValue/10,Int.MaxValue/10)


  def stopOnTime(): Boolean = {
    m.getWatch() >= MaxTimeMilli //ran out of time
  }

  def stop(): Boolean = {
    val newSolution = bestKnownObjective < lastBestKnownObjective;
    lastBestKnownObjective = bestKnownObjective
    val outOfTime = m.getWatch() >= MaxTimeMilli //ran out of time
    val satProblem = (newSolution && stopOnSat) //sat problem
    val ignoreObj = (newSolution && m.objective.objectiveWeight.value==0)
    val lowestValue = (m.objective.violation.value == 0 && m.objective.getObjectiveValue() == objLB) //reached the lower bound
    val alreadyFoundOpt = bestKnownObjective == objLB
    return outOfTime || satProblem || ignoreObj || lowestValue || alreadyFoundOpt
  }


  def handlePossibleSolution(){
    if(m.objective().value < weightedBest){
      bestPair = (m.objective.violation.value,m.objective.getObjectiveValue())
    }
    if(m.objective.violation.value==0 && m.objective.getObjectiveValue() < bestKnownObjective){
      //bestKnownViolation = 0
      bestKnownObjective = m.objective.getObjectiveValue();
      timeOfBestObjective = m.getWatch()
      saveBestSolution()
      foundSolution = true
      m.handleSolution();
      if(bestKnownObjective==objLB && !stopOnSat)println("==========")//added !stopOnSat to not print it on Satisfaction problems.
      if(m.objective.getObjectiveValue() != bestKnownObjective){
        //If propagation changed the objective value, we may have a new solution
        handlePossibleSolution()
      }
    }else if(bestKnownObjective == Int.MaxValue){
      m.log("Violation: "+m.objective.violation.value+ "\tat "+m.getWatch()+ " ms")
    }
  }
  def weightedBest = bestPair._1 * m.objective.violationWeight.value + bestPair._2 * m.objective.objectiveWeight.value
  def cancelObjective() = {
    m.objective.objectiveWeight := 0
  }
  def restoreObjective() = {
    m.objective.objectiveWeight := 1
  }

  def saveBestSolution() = {
    bestSolution = searchVariables.map(_.value)
    if(m.opts.quietMode)
      bestSolutionOutput = m.getOutputOfCurrentAssignment
  }

  /*
  Warning: A solution cannot be restored if the CBLS engine is interrupted, as its internal state will be broken.
   */
  def restoreBestSolution() = {
    for( i <- bestSolution.indices){
      searchVariables(i) := bestSolution(i)
    }
  }
  
  def printBestSolution() = {
    println(bestSolutionOutput)
    System.out.flush()
  }

  def forcePrintCurrentAssignment = {
    m.printCurrentAssignment
  }

}


abstract class NeighbourhoodSearch(val m: FZCBLSModel,val sc: SearchControl) extends SearchProcedure {
  val log = m.log
  val neighbourhoods: List[Neighbourhood] = m.neighbourhoods 
  val searchVariables = neighbourhoods.flatMap(_.getVariables()).toSet.toArray.asInstanceOf[Array[CBLSIntVar]]
    //neighbourhoods.foldLeft(Set.empty[CBLSIntVar])((acc: Set[CBLSIntVar], x: Neighbourhood) => acc ++ x.getVariables().filterNot(_.isInstanceOf[StoredCBLSIntConst])).toArray
}


abstract class NeighbourhoodTabuSearch(m: FZCBLSModel, sc: SearchControl) extends NeighbourhoodSearch(m,sc){
  
  val variableMap = (0 until searchVariables.length).foldLeft(Map.empty[CBLSIntVar, Int])((acc, x) => acc + (searchVariables(x) -> x));  
  
  val it = CBLSIntVar(m.m, 1, 0 to Int.MaxValue, "it");
  val tabu: Array[CBLSIntVar] = searchVariables.map(v => CBLSIntVar(sc.m.m, 0, 0 to Int.MaxValue,  "Tabu_" + v.name)).toArray;
  val nonTabuVariables = SelectLEHeapHeap(tabu.asInstanceOf[Array[IntValue]], it);
  val MaxTenure = (searchVariables.length * 0.6).toInt
  val MinTenure = 2
  val tenureIncrement = Math.max(1, (MaxTenure - MinTenure) / 10);
  var tenure = MinTenure
  var ecnt = 0;
  var bcnt = 0;
  val baseSearchSize = 100;
  val searchFactor = 20;

  var currentNeighbour = 0

  val visitedStates = mutable.TreeSet.empty[Int]

  val objectiveFun = m.objective.objective

  var lastTime = System.currentTimeMillis()
  def acceptMove(best: Int,nonTabuSet: Set[CBLSIntVar])(m:Move): Boolean = {
    //changed forall to exists after a suggestion of Gustav.
    m.getModified.exists(nonTabuSet.contains(_)) || m.value < best 
  }
  def acceptVar(nonTabuSet: Set[CBLSIntVar])(v:CBLSIntVar): Boolean ={
    nonTabuSet.contains(v)
  }
  def makeMove(extendedSearch: Boolean){
    val nonTabuSet = nonTabuVariables.value.map(searchVariables(_));
    val bestValue = sc.weightedBest
    if(extendedSearch) ecnt+=1 else bcnt+=1

//    if(it.value % 100 == 0){
//      println(it.value + " - "+ (neighbourhoods(0).asInstanceOf[AllDifferent].accumulatedTime) +
//      " ratio " + (neighbourhoods(0).asInstanceOf[AllDifferent].accumulatedTime.toFloat/it.value))
//    }



    val foo  = m.c.getPostedConstraints.map(_._1).filter(_.violation.value>0)
    //m.printCurrentAssignment

    //log("IT time: " + (System.currentTimeMillis() - lastTime))
    lastTime = System.currentTimeMillis()
    val bestNeighbour = selectMin(neighbourhoods.map((n: Neighbourhood) =>
      if (extendedSearch) {

        n.getExtendedMinObjective(objectiveFun,it.value, acceptMove(bestValue,nonTabuSet), acceptVar(nonTabuSet))
      } else {

        n.getMinObjective(objectiveFun,it.value, acceptMove(bestValue,nonTabuSet), acceptVar(nonTabuSet))
      }))(_.value)
    if(bestNeighbour!=null){
      //TODO: Aspiration sometimes accepts moves that do not improve but seem to improve because of changing weights. 
      if(log.level > 0 && bestNeighbour.getModified.forall(!nonTabuSet.contains(_))){
        log(2,"Aspiration");
        log(3,bestNeighbour.value.toString +" < "+bestValue.toString +" ; "+m.objective().value)
      }
      log(3,bestNeighbour.toString)
      log(4,tabu.filter(t => t.value > it.value).toList.toString())

      //log("Current violation: " + m.c.violation.value)
      bestNeighbour.commit()
      sc.handlePossibleSolution()

    }else
      log("No move exists!")
    val modifiedVars = if(bestNeighbour!=null) bestNeighbour.getModified else Set.empty[CBLSIntVar]
    for (v <- modifiedVars) {
      val index = variableMap(v);
      //This could be it.value + tenure + random(tenureIncrement) to introduce more randomness
      //tabu(index) := it.value + tenure;
      tabu(index) := it.value + Math.min(MaxTenure, tenure + RandomGenerator.nextInt(tenureIncrement));
    }

    /*val hc = searchVariables.toList.map(_.value).hashCode
    if(visitedStates.contains(hc)){
      log("hash code: " + hc + " has been visited before - "+"Storing " + visitedStates.size + " violation: " +m.c.violation.value)
      //log(searchVariables.map(_.value).mkString(", "))
    }
    //log("Storing " + visitedStates.size + " solutions at it "+it.value)
    visitedStates += hc
*/

    it++
  }

  override def getNumIterations(): Int = it.value
}

class NeighbourhoodSearchOPT(m:FZCBLSModel, sc: SearchControl) extends NeighbourhoodTabuSearch(m,sc) {
  
  override def run()= {
    log("Starting Optimization Search")
    
    var bestNow = Int.MaxValue;
    var best = bestNow;
    var itSinceBest = 0;
    var numOfMaxTenure = 0;

    var timeOfBest = m.getWatch();
    var itOfBalance = 0;
    var minViolationSinceBest = Int.MaxValue;
    var minObjectiveSinceBest = Int.MaxValue;
    var lastMinObjective = Int.MinValue;


    var wait = 0;
    val waitDec = 1;


    //m.objective.objectiveWeight := 0;//TODO: What is this??? Remove it?
    while (!sc.stop()) {
      makeMove(true)
      val tenureBefore = tenure
      //log("Violation " + m.c.violation.value)

      if (wait > 0) {
        wait -= waitDec;
      } else {
        itSinceBest += 1;
      }

      // Minimize the problem
      // There are two special cases to look out for here.
      // 1) The violation is within such a small range (compared with the objectiveFun) that the violation is ignored by the search.
      //	- This shows when the violation is above 0 for a long time (possibly forever) and the objectiveFun is at a "good" low value
      // 2) The violation can grow so quickly that it overshadows the objectiveFun (ie the opposite of 1).
      //  - This shows when the violation is 0 for a long time (possibly forever) and the objectiveFun does not decrease
      //
      // There is of course also the problem of the dynamic tenure behaving badly but that is waaaaay harder to detect and do something about.
      minViolationSinceBest = Math.min(minViolationSinceBest, m.c.violation.value)
      minObjectiveSinceBest = Math.min(minObjectiveSinceBest, m.objective.getObjectiveValue())
      if (m.objective.getObjectiveValue() < bestNow || sc.bestKnownObjective < best) {
        bestNow = m.objective.getObjectiveValue()
        tenure = Math.max(MinTenure, tenure - 1)
        if (sc.bestKnownObjective < best) {
          best = sc.bestKnownObjective;
          timeOfBest = m.getWatch();
          itOfBalance = it.value
          minViolationSinceBest = Int.MaxValue
          minObjectiveSinceBest = Int.MaxValue
          lastMinObjective = bestNow;
          tenure = Math.max(MinTenure, tenure / 2)
        }
        itSinceBest = 0;
      }

      if (it.value - itOfBalance > baseSearchSize * 2 && wait == 0) {
        if (minViolationSinceBest > 0) { // 1)
          m.objective.increaseViolationWeight(minObjectiveSinceBest)
        } else if (bestNow <= lastMinObjective) { // 2)
          m.objective.increaseObjectiveWeight(minObjectiveSinceBest)
        }
        lastMinObjective = bestNow
        minViolationSinceBest = Int.MaxValue
        minObjectiveSinceBest = Int.MaxValue

        itOfBalance = it.value;
      }
      if (itSinceBest > tenure + baseSearchSize + searchFactor * (tenure / tenureIncrement)) {
        itSinceBest = 0;
        tenure = Math.min(MaxTenure, tenure + tenureIncrement);
        if (tenure == MaxTenure) {
          //Wait will be long enough to clear the tabu list.
          if (m.getWatch() - timeOfBest > sc.MaxTimeMilli / 8) {
            //println("% Reset");
            timeOfBest = m.getWatch();
            log("Reset neighourhoods")
            for (n <- neighbourhoods)
              n.reset();
          }
          wait = tenure + baseSearchSize;
          tenure = MinTenure;
          bestNow = m.objective.getObjectiveValue()
        }
      }
      if(tenure != tenureBefore)
        log("Updated tenure: " + tenure)
      if(m.getWatch() > timeOfBest + 300000){
        timeOfBest = m.getWatch()
        log("Reset neighourhoods 5 minutes")
        for (n <- neighbourhoods)
          n.reset();
        tenure = MinTenure
      }
    }
    log("Completed Optimization Search at "+m.getWatch())
    log("nb moves " + it.value)
    log("\tnb extended moves: " + ecnt)
    log("\tnb basic moves:" + bcnt)
  }
}

class NeighbourhoodSearchSAT(m:FZCBLSModel, sc: SearchControl) extends NeighbourhoodTabuSearch(m,sc) {
  override def run()= {
    log("Starting Satisfaction Search")
    var extendedSearch = false
    var roundsWithoutSat = 0
    val maxRounds = 5

    var timeOfBest = m.getWatch()
    var itSinceBest = 0
    var bestViolation = Int.MaxValue


    var wait = 0
    val waitDec = 1


    while (!sc.stop()) {
      makeMove(extendedSearch)
      if (wait > 0) {
        wait -= waitDec;
      } else {
        itSinceBest += 1;
      }
      if (m.c.violation.value < bestViolation) {
        bestViolation = m.c.violation.value
        itSinceBest = 0
        timeOfBest = m.getWatch()
        tenure = Math.max(MinTenure, tenure - 1)
        if (tenure == MinTenure) {
          extendedSearch = false;
        }
      }
      if (m.c.violation.value > bestViolation * 2) {
        extendedSearch = true;
      }

      //log(itSinceBest + ">" + (tenure + baseSearchSize + searchFactor * (tenure / tenureIncrement)))

      if (itSinceBest > tenure + baseSearchSize + searchFactor * (tenure / tenureIncrement)) {
        extendedSearch = true;
        itSinceBest = 0;
        tenure = Math.min(MaxTenure, tenure + tenureIncrement);
        if (tenure == MaxTenure) {
          //Wait will be long enough to clear the tabu list.
          wait = tenure + baseSearchSize;
          bestViolation = Int.MaxValue
          tenure = MinTenure;
          roundsWithoutSat += 1;
          if (roundsWithoutSat >= maxRounds) {
            log("Reset neighourhoods")
            for (n <- neighbourhoods)
              n.reset();
            roundsWithoutSat = 0;
            bestViolation = m.c.violation.value
          }
        }
      }
      if(m.getWatch() > timeOfBest + 300000){
        timeOfBest = m.getWatch()
        log("Reset neighourhoods 5 minutes")
        for (n <- neighbourhoods)
          n.reset();
      }
    }

    log("Completed Satisfaction Search at "+m.getWatch())
    log("nb moves "+ecnt+"\t"+bcnt)
  }
}

class NeighbourhoodSearchOPTbySAT(m:FZCBLSModel, sc: SearchControl) extends NeighbourhoodTabuSearch(m,sc) {
  override def run()= {
    log("Starting Optimisation by Satisfaction Search")
    var extendedSearch = false;
    var roundsWithoutSat = 0;
    val maxRounds = 5;

    var timeOfBest = m.getWatch();
    var itSinceBest = 0;
    var bestViolation = Int.MaxValue


    var wait = 0;
    val waitDec = 1;

    sc.cancelObjective()

    while (!(m.getWatch() >= sc.MaxTimeMilli || (m.objective.violation.value==0 && m.objective.getObjectiveValue() == sc.objLB))) {
      makeMove(extendedSearch)
      
      if (wait > 0) {
        wait -= waitDec;
      } else {
        itSinceBest += 1;
      }
      if (m.c.violation.value < bestViolation) {
        bestViolation = m.c.violation.value
        itSinceBest = 0;
        timeOfBest = m.getWatch()
        tenure = Math.max(MinTenure, tenure - 1)
        if (tenure == MinTenure) {
          extendedSearch = false;
        }
        if(m.c.violation.value == 0){
          bestViolation = Int.MaxValue
        /*  m.objectiveFun.objectiveBound := (m.fzModel.search.obj match{
            case FZObjective.MINIMIZE => m.objectiveFun.objectiveVar.value-1
            case FZObjective.MAXIMIZE => m.objectiveFun.objectiveVar.value+1
          })
          println("Objective bound is now: " +m.objectiveFun.objectiveBound.value)*/
        }
      }
      if (m.c.violation.value > bestViolation * 10) {
        extendedSearch = true;
      }
      if (itSinceBest > tenure + baseSearchSize + searchFactor * (tenure / tenureIncrement)) {
        extendedSearch = true;
        itSinceBest = 0;
        tenure = Math.min(MaxTenure, tenure + tenureIncrement);
        if (tenure == MaxTenure) {
          //Wait will be long enough to clear the tabu list.
          wait = tenure + baseSearchSize;
          bestViolation = Int.MaxValue
          tenure = MinTenure;
          roundsWithoutSat += 1;
          if (roundsWithoutSat >= maxRounds) {
            log("Reset neighourhoods")
            for (n <- neighbourhoods)
              n.reset();
            roundsWithoutSat = 0;
            bestViolation = m.c.violation.value
          }
        }
      }
      if(m.getWatch() > timeOfBest + 300000){
        timeOfBest = m.getWatch()
        log("Reset neighourhoods 5 minutes")
        for (n <- neighbourhoods)
          n.reset();
      }
    }
  }

  override def makeMove(extendedSearch: Boolean){
    val nonTabuSet = nonTabuVariables.value.map(searchVariables(_).asInstanceOf[CBLSIntVar]);
    val bestValue = sc.weightedBest
    if(extendedSearch) ecnt+=1 else bcnt+=1
    val bestNeighbour = selectMin(neighbourhoods.map((n: Neighbourhood) =>
      if (extendedSearch) {
        n.getExtendedMinObjective(objectiveFun, it.value, acceptMove(bestValue, nonTabuSet))
      } else {
        n.getMinObjective(objectiveFun, it.value, acceptMove(bestValue, nonTabuSet))
      }))(_.value)
    if(bestNeighbour!=null){
      //TODO: Aspiration sometimes accepts moves that do not improve but seem to improve because of changing weights.
      if(log.level > 0 && bestNeighbour.getModified.forall(!nonTabuSet.contains(_))){
        log(2,"Aspiration");
        log(3,bestNeighbour.value.toString +" < "+bestValue.toString +" ; "+m.objective().value)
      }
      log(3,bestNeighbour.toString)
      log(4,tabu.filter(t => t.value > it.value).toList.toString())
      bestNeighbour.commit()
      sc.handlePossibleSolution()
    }else
      log("No move exists!")
    val modifiedVars = if(bestNeighbour!=null) bestNeighbour.getModified else Set.empty[CBLSIntVar]
    for (v <- modifiedVars) {
      val index = variableMap(v);
      //This could be it.value + tenure + random(tenureIncrement) to introduce more randomness
      //tabu(index) := it.value + tenure;
      tabu(index) := it.value + Math.min(MaxTenure, tenure + RandomGenerator.nextInt(tenureIncrement));
    }
    it++
  }
}

class GLSSAT(m:FZCBLSModel,sc: SearchControl) extends NeighbourhoodSearch(m,sc) {
  val it = CBLSIntVar(m.m, 1, 0 to Int.MaxValue, "it");
  val objectiveFun = m.objective.objective

  def run(){

    var improved = true

    var best = Int.MaxValue


    log("Starting GLSSAT Search")
    log("Starting Violation: "+m.objective.violation.value)

    sc.handlePossibleSolution();
    while(!sc.stop()) {
      improved = true
      while (improved && !sc.stop()) {
        improved = false

        val bestNeighbour =
          selectMin(neighbourhoods.map((n: Neighbourhood) =>
                                         n.getExtendedMinObjective(objectiveFun, it.value, _.value < best)))(_.value)

        if (!bestNeighbour.isInstanceOf[NoMove]) {
          if(m.objective.objective.value > bestNeighbour.value){
            improved = true
          }
          bestNeighbour.commit()

          if (m.c.violation.value == 0) {
            sc.handlePossibleSolution()
          }
          //log("improved violation: " + m.objectiveFun.violation.value)
          best = m.objective.objective.value
        }
      }
      sc.handlePossibleSolution()
      if (m.objective.violation.value > 0) {

        /*val  (c,w) = selectMax(m.c.getPostedConstraints,
                               (t:(Constraint,IntValue)) =>
                                 ((t._1.violation.value.toFloat/t._2.value)*100).toInt,
                               (t:(Constraint,IntValue)) =>
                                 t._1.violation.value>0)
        if (w.isInstanceOf[CBLSIntVar]) {
          w.asInstanceOf[CBLSIntVar] :+= c.violation.value
        }*/

        //log("violation before weights increased: " + m.objectiveFun.violation.value)
        for ((c, w) <- m.c.getPostedConstraints) {
          if (c.violation.value > 0) {
            if (w.isInstanceOf[CBLSIntVar]) {
              w.asInstanceOf[CBLSIntVar] :+= c.violation.value
            }
          }
        }

        //log("violation after weights increased: " + m.objectiveFun.violation.value)
        if (RandomGenerator.nextInt(1000) < 2) {
          neighbourhoods.foreach(_.reset())
          log("Rest neighbourhoods")
        }
        //log("Best " + best)
        best = m.objective.objective.value
        //log("New Best " + best)
      }
    }



    log("Done GLSSAT at "+m.getWatch())
    log("Ending Violation: "+m.objective.violation.value)
    log("Nb Moves: "+it)
  }
  override def getNumIterations(): Int = it.value
}


//@Deprecated
//class RestrictedNeighbourhoodSearch(m:FZCBLSModel, sc: SearchControl) extends NeighbourhoodTabuSearch(m,sc) {
//
//  val (defaultNeighbourhoods,constraintNeighbourhoods) = neighbourhoods.partition(_.isInstanceOf[GenericNeighbourhood])
//  val defaultVariables = defaultNeighbourhoods.flatMap(_.searchVariables).toSet.toList
//  val constraintVariables = constraintNeighbourhoods.flatMap(_.searchVariables).toSet.toList //Remove duplicates: I am too lazy to do it properly.
//  var criticalVars = Set.empty[IntValue];
//
//  var itOfBest = 0
//
//  override def acceptVar(nonTabuSet: Set[CBLSIntVar])(v:CBLSIntVar): Boolean = {
//    if(criticalVars.isEmpty)
//      nonTabuSet.contains(v)
//    else
//      criticalVars.contains(v) && nonTabuSet.contains(v)
//  }
//  override def acceptMove(best: Int, nonTabuSet: Set[CBLSIntVar])(m:Move): Boolean = {
//
//    if(criticalVars.isEmpty)
//      m.getModified.exists(nonTabuSet.contains(_)) // || m.value < best
//    else
//      (m.getModified.exists(v => criticalVars.contains(v)) && m.getModified.exists(nonTabuSet.contains(_))) //|| m.value < best
//  }
//
//  override def run()= {
//    log("Starting Restricted Neighbourhood Search")
//
//    var bestViolation = Int.MaxValue
//
//
//
//    var itWithoutSuccess = 0
//
//    sc.cancelObjective()
//    while (!(m.getWatch() >= sc.MaxTimeMilli || (m.objective.violation.value==0 && m.objective.getObjectiveValue() == sc.objLB))) {
//
//
//      /*
//        1. Make a move from a non-generic neighbourhood
//        2. Freeze variables of non-generic neighbourhood
//          2.1 If fail then goto step 3
//          2.2 Otherwise, Make 2*N moves from the generic neighbourhoods where N is the number of searchvariables in the
//            generic neighbourhoods. -- Play with different multiples of N
//            2.2.1 Update tabu after every move.
//          2.3 If We find a new solution, accept and go to step 3
//        3. update tabu of the non-generic move, maybe use different tenure? Or tenure+2N??
//        4. Go to 1.
//
//       */
//
//      //IDEA: cancel the objectiveFun in the outer loop and restore it in the inner loop.
//      //      This helps a lot for SAP.fzn but backfires for tdtsp.fzn
//
//     /* println("Critical Vars: " +criticalVars.mkString(", "))
//      println("Assignment:  " + constraintNeighbourhoods.flatMap(_.searchVariables).map(_.value).mkString(", "))
//      log("Viol: " + m.objectiveFun.violation.value)
//      log("Obj: " + m.objectiveFun.getObjectiveValue())
//      */
//
//
//      val move = makeMove(constraintNeighbourhoods, tenure);
//
//      it++;
//
//     // if( m.objectiveFun.violation.value == 0){
//        sc.handlePossibleSolution()
//      // itOfBest = it.value
//      /*} else*/
//      if(move.isInstanceOf[NoMove]){
//        tenure = MinTenure
//        log(2, "No Move")
//      }else{
//        var foundSolution = true
//        while(foundSolution) {
//          val (success, varsFixed) = m.cpmodel.fix(constraintVariables.map( v => (v.name,v.value)))
//          if(success){
//            //sc.restoreObjective()
//            itWithoutSuccess = 0
//            doGenericMoves()
//            foundSolution = m.objective.violation.value == 0
//            sc.handlePossibleSolution()
//          }else{
//            foundSolution = false
//            itWithoutSuccess += 1
//            criticalVars = varsFixed.map(name => m.cblsIntMap(name)).toSet
//            if (itWithoutSuccess > tenure + baseSearchSize + searchFactor * (tenure / tenureIncrement)) {
//              itOfBest = it.value
//              tenure = Math.max(MinTenure,Math.min(MaxTenure,tenure + tenureIncrement)%MaxTenure)
//              log("Tenure: " + tenure)
//              itWithoutSuccess = 0
//
//            }
//            //log("Failed to fix variables, no solution with this assignment.")
//
//          }
//        }
//      }
//    }
//  }
//
//  def doGenericMoves() = {
//    criticalVars = Set.empty
//    m.cpmodel.updateIntermediateModelDomains() // pushing fix from cpVars to fzVars
//    m.restrictVarDomains() // pushing fix from fzVars to cblsVars
//
//    //Do stuff
//    var localIts = defaultVariables.length*2
//    var itOfBest = Int.MaxValue
//    var bestViol = Int.MaxValue
//    while (localIts > 0 && m.getWatch() < sc.MaxTimeMilli  && m.objective.violation.value != 0) {
//      val localMove = makeMove(defaultNeighbourhoods, tenure)
//      if (m.objective.violation.value < bestViol) {
//        localIts = Math.max(localIts,defaultVariables.length)
//        itOfBest = it.value
//        bestViol = m.objective.violation.value
//      }
//      if (itOfBest - it.value > 50) {
//        //tenure = Math.max(MinTenure,Math.min(MaxTenure,tenure + tenureIncrement)%MaxTenure)
//        log("Tenure: " + tenure)
//        itOfBest = it.value
//      }
//      //log(localMove.toString)
//      //log("Violation: " + m.objectiveFun.violation.value)
//      localIts -= 1
//      it ++;
//    }
//
//    if (m.objective.violation.value == 0) {
//      log("Found solution")
//      itOfBest = it.value
//    } else {
//      tenure = Math.max(MinTenure, Math.min(MaxTenure, tenure + tenureIncrement) % MaxTenure)
//      log("Violation: " + m.objective.violation.value)
//      log("Tenure: " + tenure)
//    }
//
//    m.cpmodel.solver.pop() //undo fix
//    m.cpmodel.setIntermediateModelDomains() // push undo from cpVars to fzVars
//    m.relaxVarDomains() // push undo from fzVars to cblsVars
//  }
//
//  def makeMove(neigh: List[Neighbourhood], localTenure:Int):Move = {
//    val nonTabuSet = nonTabuVariables.value.map(searchVariables(_));
//    val bestValue = sc.weightedBest
//
//    val bestNeighbour = selectMin(
//      neigh.map(_.getExtendedMinObjective(objectiveFun, it.value, acceptMove(bestValue, nonTabuSet)))
//    )(_.value)
//
//    //println("Iteration: " + it.value)
//    //println("Move: " + bestNeighbour)
//    if (bestNeighbour != null) {
//      bestNeighbour.commit()
//    } else
//      log("No move exists in " + neigh.map(_.toString).mkString(", "))
//
//    val modifiedVars = if (bestNeighbour != null) bestNeighbour.getModified else Set.empty[CBLSIntVar]
//    for (v <- modifiedVars) {
//      val index = variableMap(v);
//      //val tabuBefore = tabu(index).value
//      tabu(index) := it.value + Math.min(MaxTenure, localTenure + RandomGenerator.nextInt(tenureIncrement));
//      //println(tabu(index) + " from " +tabuBefore)
//    }
//
//    bestNeighbour
//  }
//}

class CompoundMoveGenerationSearch(m:FZCBLSModel,
                                   sc: SearchControl,
                                   probeWithCP:Boolean = true,
                                   useCriticalVars:Boolean = true) extends NeighbourhoodTabuSearch(m,sc) {

  var itOfBest = 0
  var accTime:Long = 0l
  var tryCPProbe:Int = 0
  var nUsedFailingVars:Int = 0

  val cancelObjective = false

  val (defaultNeighbourhoods,constraintNeighbourhoods) = neighbourhoods.partition(n => n.isInstanceOf[GenericNeighbourhood])
  val auxVariables = defaultNeighbourhoods.flatMap(_.searchVariables).distinct
  val coreVariables = constraintNeighbourhoods.flatMap(_.searchVariables).distinct.filterNot(_.isInstanceOf[StoredCBLSIntConst])
  var criticalVars = Set.empty[IntValue];


  override val MaxTenure = (coreVariables.length * 0.6).toInt
  override val tenureIncrement = Math.max(1, (MaxTenure - MinTenure) / 10);

  val coreVariablesNames = coreVariables.map(_.name)
  
  private val constraintsForCPSolver = m.fzModel.constraints.filterNot(c => c.definedVar.isEmpty &&
    c.variables.flatMap(m.fzModel.getDefiningVariables(_)).forall( v => v.isBound || coreVariablesNames.exists(_ == v.id))).toArray

  val experimentalObjective = new CPProbingObjective(m.objective.objective.asInstanceOf[IntVarObjective].objective,
                                                     m.fzModel,
                                                     constraintsForCPSolver,
                                                     coreVariables,
                                                     auxVariables)
  

  override def acceptVar(nonTabuSet: Set[CBLSIntVar])(v:CBLSIntVar): Boolean = {
    if(criticalVars.isEmpty)
      nonTabuSet.contains(v)
    else
      criticalVars.contains(v) && nonTabuSet.contains(v)
  }
  override def acceptMove(best: Int, nonTabuSet: Set[CBLSIntVar])(m:Move): Boolean = {

    if(criticalVars.isEmpty)
      m.getModified.exists(nonTabuSet.contains(_)) || m.value < best
    else
      (m.getModified.exists(v => criticalVars.contains(v)) && m.getModified.exists(nonTabuSet.contains(_))) || m.value < best
  }
  def hasTimedout():Boolean = m.getWatch() >= sc.MaxTimeMilli
  override def run()= {
    log("Starting Search with Compound-Move Generation")

    var bestViolation = Int.MaxValue
    var itWithoutSuccess = 0

    var failingVar:mutable.Map[String,Int] = scala.collection.mutable.Map.empty
    val CPProbeIsExpensive = constraintNeighbourhoods.exists(n => n.isInstanceOf[ThreeOpt] && n.searchVariables.length > 40)
    experimentalObjective.updateObjBounds()
    if(cancelObjective)
      sc.cancelObjective()
    while (!sc.stop()) {
      val move = makeMove(constraintNeighbourhoods, tenure, !CPProbeIsExpensive) // Quick hack to always use CP probe when not expensive... // && (probeWithCP || tryCPProbe > 0))
      //println(m.c.violation.value + " actuallly -> " + reducedConstraintSystem.violation.value)
      it++;
      if(tryCPProbe > 0)
        tryCPProbe -= 1
      sc.handlePossibleSolution()
      for (v <- move.getModified)
        failingVar.remove(v.name)

      if(move.isInstanceOf[NoMove]){
        //tenure = MinTenure
        itWithoutSuccess = checkItwithoutSuccess(itWithoutSuccess + 1)
        tenure = Math.max(MinTenure,tenure-1)
        criticalVars = Set.empty
        failingVar = scala.collection.mutable.Map.empty //Should we really clear the FailingVars here?
        log(1, "No Move")
      } else if( true /*reducedConstraintSystem.violation.value == 0*/){

        //log("Fixing")
        val before = System.currentTimeMillis()
        //val (success, varsFixed, solution) = m.cpmodel.fixAndSolve(coreVariables.map( v => {
        val (success, lastFixed, solution) = experimentalObjective.CPSolver.fixAndSolve(coreVariables.map(v => {
          val value = v match{
            case b:CBLSBoolVar => b.truthValue
            case i:CBLSIntVar => i.value
          }
          (v.name, value)
        }), 100000, Int.MaxValue)
        val after = System.currentTimeMillis()
        accTime += after-before
        //log("Spent " + (after-before) + "ms in CP solver")

        if(experimentalObjective.foundObj && !success){
          for(v <- auxVariables ++ coreVariables){
            v match {
              case b:CBLSBoolVar => b.assignTruthValue(experimentalObjective.bestSolution(v.name))
              case i:CBLSIntVar => v := experimentalObjective.bestSolution(v.name)
            }
          }
          sc.handlePossibleSolution()

          experimentalObjective.updateObjBounds()
        }
        val foo  = m.c.getPostedConstraints.map(_._1).filter(_.violation.value>0)

        if(success){
          log("Found solution in CP solver.")
          for(v <- auxVariables){
            v match {
              case b:CBLSBoolVar => b.assignTruthValue(solution(v.name))
              case i:CBLSIntVar => v := solution(v.name)
            }
          }

          if(cancelObjective && m.c.violation.value == 0){ // If solution
            tenure = Math.max(MinTenure,tenure-1)
            sc.restoreObjective()
          }
          
          if(m.c.violation.value == 0 && tryCPProbe > 0){
            tryCPProbe = 10
          }

          sc.handlePossibleSolution()
          criticalVars = Set.empty
          itWithoutSuccess = 0
          //TODO: do I want to update the bounds really?
          experimentalObjective.updateObjBounds()


          failingVar = scala.collection.mutable.Map.empty

        }else{
          if(useCriticalVars){
              //criticalVars = varsFixed.map(name => m.cblsIntMap(name)).toSet
            if(lastFixed != "")
              failingVar(lastFixed) = failingVar.getOrElse(lastFixed, 0) + 1
              //println(failingVar.values.map( "#" * _).mkString("\n"))

            if(failingVar.nonEmpty && failingVar.values.max > 2){
              criticalVars = failingVar.keys.map(name => m.cblsIntMap(name)).toSet
              log("Using failingVars")
              nUsedFailingVars += 1
            }
            if(nUsedFailingVars > 20){
              nUsedFailingVars = 0
              tryCPProbe = 10
            }
          }

          //println("Critical vars: " + criticalVars.mkString(", "))
          itWithoutSuccess = checkItwithoutSuccess(itWithoutSuccess + 1)
          val fallbackMove = makeMove(defaultNeighbourhoods, tenure, false)
          sc.handlePossibleSolution()
        }
      }else{
        //log("Skipped CP solver step")
        itWithoutSuccess = checkItwithoutSuccess(itWithoutSuccess + 1)
      }
    }

    log("Spent " + experimentalObjective.accTime + "ms probing with CP solver")
    log("Spent " + accTime + "ms completing with CP solver")
    log("spent " + (experimentalObjective.accTime+accTime) + "ms in CP solver")

  }

  def checkItwithoutSuccess(itWithoutSuccess:Int):Int = {
    if (itWithoutSuccess > tenure + baseSearchSize/2 + searchFactor * (tenure / tenureIncrement)) {
      itOfBest = it.value
      tenure = Math.max(MinTenure,Math.min(MaxTenure,tenure + tenureIncrement)%MaxTenure)
      log("Tenure: " + tenure)
      tryCPProbe = 10
      if(cancelObjective)
        sc.cancelObjective()
      0
    }else{
      itWithoutSuccess
    }
  }

  def makeMove(neigh: List[Neighbourhood], localTenure:Int, probeWithCP:Boolean = true):Move = {
    val nonTabuSet = nonTabuVariables.value.map(searchVariables(_));
    val bestValue = sc.weightedBest

    val foo = nonTabuSet.intersect(coreVariables.toSet)

    experimentalObjective.resetBestObj()
    val objFun = if(probeWithCP) experimentalObjective else objectiveFun
    val bestNeighbour = selectMin(
      neigh.map(n => n.getExtendedMinObjective(objFun, it.value, acceptMove(bestValue, nonTabuSet)))
    )(_.value)

    if(bestNeighbour.value > experimentalObjective.bestObj){
      log(s"explored with ${experimentalObjective.bestObj} but got ${bestNeighbour.value}")
    }
    //println("Iteration: " + it.value)
    //println("Move: " + bestNeighbour)
    //println("Obj: " + bestNeighbour.value)
    if (bestNeighbour != null) {
      bestNeighbour.commit()
    } else
      log("No move exists in " + neigh.map(_.toString).mkString(", "))

    val modifiedVars = if (bestNeighbour != null) bestNeighbour.getModified else Set.empty[CBLSIntVar]
    for (v <- modifiedVars) {
      val index = variableMap(v);
      //val tabuBefore = tabu(index).value
      tabu(index) := it.value + Math.min(MaxTenure, localTenure + RandomGenerator.nextInt(tenureIncrement));
      //println(tabu(index) + " from " +tabuBefore)
    }

    bestNeighbour
  }


  private def createReducedConstraintSystem():ConstraintSystem = {
    // All constraints that only touch the CBLS variables
    val cnConstraints = m.c.getPostedConstraints.filter(
      c => c._1.constrainedVariables.flatMap(m.m.sourceVariables(_)).forall( v =>
                                                                               coreVariables.contains(v) || v.isInstanceOf[StoredCBLSIntConst])) // only constraints over CN

    // for t-scheduling.fzn
//    val bar = cnConstraints(0)._1.constrainedVariables(1)
//    val baz = (m.m.sourceVariables(bar))

//    val foo = m.c.getPostedConstraints(0)._1.constrainedVariables(1)
//    val bar = m.m.sourceVariables(foo)

    // We only call the CP solver when all constraints that only touch the CN variables are satisfied.
    // This reducedConstraintSystem maintains the violation of those constraints.
    val cs = new ConstraintSystem(m.m)
    for (c <- cnConstraints) {
      cs.add(c._1, c._2)
    }
    cs.close()
    cs
  }

  class CPProbingObjective(obj: ChangingIntValue,
                           model: oscar.flatzinc.model.FZProblem,
                           constraints: Array[oscar.flatzinc.model.Constraint],
                           searchVariables:List[CBLSIntVar],
                           controlledVariables:List[CBLSIntVar])
    extends IntVarObjective(obj) {

    val CPSolver = new FZCPCompletionSolver(model)
    CPSolver.createVariables()
    CPSolver.createConstraints(constraints)
    CPSolver.createObj()
    log( "Removed " + (model.constraints.size - constraints.length) + " constraints when splitting")

    var accTime = 0

    var bestObj = Int.MaxValue
    var foundObj = false
    var bestSolution:MMap[String,Int] = MMap.empty
    def resetBestObj() = {
      foundObj = false
      bestObj = Int.MaxValue
      bestSolution = MMap.empty
    }

    val reducedCS = createReducedConstraintSystem()

    override def probe:Int = {
      if (!hasTimedout()) {
        val before = System.currentTimeMillis()
        val (success, _, solution) = CPSolver.fixAndSolve(searchVariables.map(v => {
          val varValue = v match {
            case b: CBLSBoolVar => b.truthValue
            case i: CBLSIntVar => i.value
          }
          (v.name, varValue)
        }))
        val deltaT = System.currentTimeMillis() - before
        accTime += deltaT.toInt
        //log("Objective probe spent " + deltaT + "ms in CP solver. Acc time: " + accTime)

        if (!success) {
          value
        } else {
          //TODO: need to take into account the violation over the search variables
          if (solution(model.search.variable.get.id) < bestObj) {
            foundObj = true
            bestSolution = solution
          }
          bestObj = Math.min(solution(model.search.variable.get.id), bestObj)
          solution(model.search.variable.get.id) + reducedCS.violation.value

          /* TODO: We do not need to do this assignment. We know what the objective value is from the CP solver, so we can take that value plus the violation of the constraints that are only over the search variables. This should save a lot of computation.*/
          /*
          val a:Iterable[(CBLSIntVar, Int)] = controlledVariables.map(v => (v, solution(v.name)))
          val oldvals: Iterable[(CBLSIntVar, Int)] = a.foldLeft(List.empty[(CBLSIntVar, Int)])(
            (acc, IntVarAndInt) => ((IntVarAndInt._1, IntVarAndInt._1.value)) :: acc)
          for (assign <- a)
            assign._1 := assign._2
          val newObj = value
          //undo
          for (assign <- oldvals)
            assign._1 := assign._2
          newObj*/
        }
      }else{
        Int.MaxValue
      }
    }

    def updateObjBounds() = {
      CPSolver.updateObjBounds()
    }
  }
}