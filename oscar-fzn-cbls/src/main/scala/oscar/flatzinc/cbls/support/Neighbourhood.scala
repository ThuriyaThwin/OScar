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
  * @author Jean-Noël Monette
  */
package oscar.flatzinc.cbls.support

import oscar.cbls.core.computation.{CBLSIntVar, IntValue}
import oscar.cbls.core.constraint.ConstraintSystem
import oscar.cbls.core.objective.{Objective => CBLSObjective}
import oscar.cbls.lib.invariant.logic.Cluster
import oscar.cbls.lib.invariant.set.Cardinality
import oscar.cbls.lib.search.LinearSelectors
import oscar.flatzinc.cbls.FZCBLSModel
import oscar.flatzinc.cp.FZCPBasicModel
import oscar.flatzinc.model._

import scala.collection.mutable.{Map => MMap}


trait GenericNeighbourhood

//Extends SearchEngine to access the selectors
abstract class Neighbourhood(val searchVariables: Array[CBLSIntVar]) extends LinearSelectors {
  //var minObjective: Int = Int.MaxValue;
  def getVariables(): Array[CBLSIntVar] = searchVariables

  def getMinObjective(objective: CBLSObjective, it: Int, accept: Move => Boolean,
                      acceptVar: CBLSIntVar => Boolean = { (x: CBLSIntVar) => true }): Move;

  def getExtendedMinObjective(objective: CBLSObjective, it: Int, accept: Move => Boolean,
                              acceptVar: CBLSIntVar => Boolean = { (x: CBLSIntVar) => true }): Move;

  def randomMove(objective: CBLSObjective, it: Int): Move;

  // def init(): Unit;
  def reset(): Unit;

  def violation(): Int;

  //TODO used in only one place. Useful?

  def acceptOr(m: Move, accept: Move => Boolean) = {
    if (accept(m)) {
      m
    } else {
      new NoMove()
    }
  }

  def selectMinImb[R, S](r: Iterable[R], s: R => Iterable[S], f: ((R, S)) => Int,
                         st: ((R, S) => Boolean) = ((r: R, s: S) => true)): (R, S) = {
    //TODO: check that it is fine
    val flattened: Iterator[(R, S)] = for (rr <- r.toIterator; ss <- s(rr).toIterator) yield (rr, ss)
    selectMin[(R, S)](flattened.toIterable)(f //(rands:(R,S)) => {/*Console.err.println(rands);*/ f(rands._1,rands._2)}
                                            , (rands: (R, S)) => st(rands._1, rands._2))
  }

  def selectMinMove2[R,S](r: Iterable[R], s: Iterable[S], getMove: (R,S) => Move,
                          st: ((R, S) => Boolean) = ((r: R, s: S) => true)): (Move,R,S) = {
    var bestValue = Int.MaxValue
    var bestMoves:List[(Move,R,S)] = List.empty

    for(i <- r; j <- s if st(i,j)){
      val m = getMove(i,j)
      if (m.value < bestValue){
        bestMoves = List((m,i,j))
        bestValue = m.value
      }else if( m.value == bestValue){
        bestMoves = (m,i,j) :: bestMoves
      }
    }

    if(bestMoves.isEmpty){
      (new NoMove(), r.head, s.head)
    }else{
      bestMoves(RandomGenerator.nextInt(bestMoves.length))    }
  }
}


//assumes that all variables have a range domain!
class SumNeighborhood(val variables: Array[CBLSIntVar], val coeffs: Array[Int], val sum: Int,
                      cs: ConstraintSystem) extends Neighbourhood(variables) {
  val variableViolation: Array[IntValue] = variables.map(cs.violation(_)).toArray

  def violation() = {
    variableViolation.foldLeft(0)((acc, x) => acc + x.value)
  };

  reset();

  def reset() {
    var s = 0
    val vals = new Array[Int](variables.length)
    for (i <- 0 until variables.length) {
      vals(i) = variables(i).min
      s += coeffs(i) * vals(i)
    }
    //TODO: Improve this stupid code!
    while (s != sum) {
      val i = RandomGenerator.nextInt(variables.length)
      if (s < sum && coeffs(i) > 0 && vals(i) < variables(i).max) {
        vals(i) += 1
        s += coeffs(i) * 1
      } else if (s > sum && coeffs(i) < 0 && vals(i) < variables(i).max) {
        vals(i) += 1
        s += coeffs(i) * 1
      }
    }
    for (i <- 0 until variables.length) {
      if (variables(i).min > vals(i) || variables(i).max < vals(i)) throw new Exception("Problem")
      variables(i) := vals(i)
    }
  }

  def getMove(objective: CBLSObjective, idx1: Int, diff: Int, idx2: Int, accept: Move => Boolean): Move = {
    val mv = List((variables(idx1), variables(idx1).value + diff),
                  (variables(idx2), variables(idx2).value - coeffs(idx1) * coeffs(idx2) * diff))
    val move = new AssignsMove(mv, objective.assignVal(mv))
    if (accept(move)) {
      move
    } else {
      new NoMove()
    }
  }

  def randomMove(objective: CBLSObjective, it: Int): Move = {
    new NoMove()
  }

  def getMinObjective(objective: CBLSObjective, it: Int, accept: Move => Boolean, acceptVar: CBLSIntVar => Boolean): Move = {
    getExtendedMinObjective(objective, it, accept)
  }

  def getExtendedMinObjective(objective: CBLSObjective, it: Int, accept: Move => Boolean, acceptVar: CBLSIntVar => Boolean): Move = {
    val rng = 0 until variables.length;
    val part1 = selectMinImb(rng, (i: Int) => variables(i).min to variables(i).max,
                             (iv: (Int, Int)) => objective.assignVal(variables(iv._1), iv._2))
    part1 match {
      case (i1, v1) =>
        val diff = v1 - variables(i1).value
        val part2 = selectMin(List(0), rng)((k: Int, i2: Int) => getMove(objective, i1, diff, i2, accept).value,
                                            (k: Int, i2: Int) => {
                                              val nv = variables(i2).value - coeffs(i1) * coeffs(
                                                i2) * diff; i1 != i2 && nv >= variables(i2).min && nv <= variables(
                                                i2).max
                                            })
        part2 match {
          case (0, i2) =>
            if (diff == 0) {
              new NoMove()
            } else {
              getMove(objective, i1, diff, i2, accept)
            }
          case _ => new NoMove()
        }
      case _ => new NoMove()
    }
  }


}


class GCCNeighborhood(val variables: Array[CBLSIntVar], val vals: Array[Int], val low: Array[Int],
                      val up: Array[Int], val closed: Boolean,
                      cs: ConstraintSystem) extends Neighbourhood(variables) {
  val variableViolation: Array[IntValue] = variables.map(cs.violation(_)).toArray

  val clusters = Cluster.makeSparse(variables.map(c => c), vals).Clusters
  val counts = clusters.foldLeft(Map.empty[Int, IntValue])((map, ic) => map + (ic._1 -> Cardinality(ic._2)))
  //foldLeft(Map.empty[Int,CBLSIntVar])((map,ic) => map + (ic._1 -> Cardinality(ic._2).output))
  val lows = vals.toList.zip(low).foldLeft(Map.empty[Int, Int])((map, vl) => map + (vl._1 -> vl._2))
  val ups = vals.toList.zip(up).foldLeft(Map.empty[Int, Int])((map, vl) => map + (vl._1 -> vl._2))
  val alldoms = variables.foldLeft((Int.MaxValue, Int.MinValue))(
    (set, v) => (math.min(set._1, v.domain.min), math.max(set._2, v.domain.max)))
  reset();

  //TODO: reset() should only be called after the fzModel is closed, in case it makes use of invariants!
  def reset():Unit = {
    //TODO: Use the CP solver to initialize.
    //TODO: This reset does not respect the domains of the variables! is it?
    var cur = variables.map(_.value)
    var cnts = cur.foldLeft(MMap.empty[Int, Int])((map, v) => map + (v -> (map.getOrElse(v, 0) + 1)))

    def cand(): List[Int] = {
      List.tabulate(cur.length)(i => i).filter(i => cnts(cur(i)) > lows.getOrElse(cur(i), 0))
    }

    var cands = cand()
    //reaching the lowerbounds
    for (v <- vals) {
      while (cnts.getOrElse(v, 0) < lows(v)) {
        if (cands.isEmpty) throw new Exception("GCC cannot be satisfied")
        val curvar = cands.head
        cands = cands.tail
        if (variables(curvar).inDomain(v) && cnts(cur(curvar)) > lows.getOrElse(cur(curvar), 0)) {
          cnts(cur(curvar)) = cnts(cur(curvar)) - 1
          cnts(v) = cnts.getOrElse(v, 0) + 1
          cur(curvar) = v
        }
      }
      cands = cand()
    }
    //reaching the upperbounds
    for (v <- vals) {
      var cands = List.tabulate(cur.length)(i => i).filter(i => cur(i) == v)
      while (cnts.getOrElse(v, 0) > ups(v)) {
        if (cands.isEmpty) throw new Exception("GCC cannot be satisfied")
        val curvar = cands.head
        cands = cands.tail
        val candval = variables(curvar).domain.find(
          k => if (ups.contains(k)) cnts.getOrElse(k, 0) < ups(k) else !closed)
        if (candval.isDefined) {
          val k = candval.get
          cnts(v) = cnts(v) - 1
          cnts(k) = cnts.getOrElse(k, 0) + 1
          cur(curvar) = k
        }
      }
    }
    //updating the variables
    for (i <- 0 until variables.length) {
      if (variables(i).min > cur(i) || variables(i).max < cur(i)) throw new Exception("Problem")
      variables(i) := cur(i)
    }
  }

  def getSwapMove(idx1: Int, idx2: Int, accept: Move => Boolean,objective: CBLSObjective): Move = {
    //Swap will always respect the constraint is it was already satisfied
    if( variables(idx1).value == variables(idx2).value)
      return new NoMove()
    if(variableViolation(idx1).value == 0 && variableViolation(idx2).value == 0 && RandomGenerator.nextInt(100) >25){
      return new NoMove
    }
    acceptOr(new SwapMove(variables(idx1), variables(idx2), objective.swapVal(variables(idx1), variables(idx2))),
             accept)

  }

  def getAssignMove(idx1: Int, v: Int, accept: Move => Boolean, objective: CBLSObjective): Move = {
    val cur = variables(idx1).value
    if (cur == v)
      return new NoMove()
    if(variableViolation(idx1).value == 0  && RandomGenerator.nextInt(100) >25){
      return new NoMove
    }
    val cnt = counts.get(cur) match {
      case None => 1
      case Some(x) => x.value
    }
    val lb = lows.getOrElse(cur, 0)
    if (cnt <= lb) return new NoMove();
    //using <= to protect from potential errors?
    val cnt2 = counts.get(v) match {
      case None => 0
      case Some(x) => x.value
    }
    val ub = ups.getOrElse(v, 1)
    if (cnt2 >= ub) return new NoMove(); //using >= to protect from potential errors?
    acceptOr(new AssignMove(variables(idx1), v, objective.assignVal(variables(idx1), v)), accept)
  }

  def randomMove(objective: CBLSObjective, it: Int): Move = {
    //TODO: respect the domains
    return getSwapMove(RandomGenerator.nextInt(variables.length),
                       RandomGenerator.nextInt(variables.length),
                       _ => true,
                       objective)
  }

  def getMinObjective(objective: CBLSObjective, it: Int, accept: Move => Boolean, acceptVar: CBLSIntVar => Boolean): Move = {
    val rng2 = 0 until variables.length;
    val idx = selectMax(rng2, (i: Int) => variableViolation(i).value);
    getBest(List(idx), rng2, accept, objective)
  }

  def getExtendedMinObjective(objective: CBLSObjective, it: Int, accept: Move => Boolean, acceptVar: CBLSIntVar => Boolean): Move = {
    val rng2 = 0 until variables.length
    getBest(rng2, rng2, accept, objective)
  }

  def getBest(rng1: Iterable[Int], rng2: Iterable[Int], accept: Move => Boolean, objective: CBLSObjective): Move = {
    val bestSwap = selectMin2(rng1, rng2, (idx: Int, next: Int) => getSwapMove(idx, next, accept, objective).value,
                              (idx: Int, v: Int) => idx < v && variables(idx).domain.contains(variables(v).value) && variables(
                                v).inDomain(variables(idx).value))
    val swap = bestSwap match {
      case (i1, i2) => getSwapMove(i1, i2, accept, objective)
      case _ => new NoMove(Int.MaxValue)
    }
    val bestMove = if (!closed) {
      selectMin2(rng1, alldoms._1 to alldoms._2, (idx: Int, v: Int) => getAssignMove(idx, v, accept,objective).value,
                 (idx: Int, v: Int) => variables(idx).inDomain(v))
    } else {
      selectMin2(rng1, vals, (idx: Int, v: Int) => getAssignMove(idx, v, accept,objective ).value,
                 (idx: Int, v: Int) => variables(idx).inDomain(v))
    }
    val move = bestMove match {
      case (i1, i2) => getAssignMove(i1, i2, accept,objective)
      case _ => new NoMove(Int.MaxValue)
    }
    if (swap.value < move.value) swap else move
  }

  def violation() = {
    variableViolation.foldLeft(0)((acc, x) => acc + x.value)
  };
}

//TODO: Take into account fixed variables!
class ThreeOpt(val variables: Array[CBLSIntVar],  cs: ConstraintSystem,
               val offset: Int) extends Neighbourhood(variables) {

  val variableViolation: Array[IntValue] = variables.map(cs.violation(_)).toArray
  val rng = offset until (offset + variables.length)

  reset();

  def reset() {
    val tmpVars:Array[Int] = variables.map(_.value - offset)
    val start = Array.tabulate(tmpVars.length)(i => i)
    val end = Array.tabulate(tmpVars.length)(i => i)
    val length = Array.tabulate(tmpVars.length)( _ => 0)
    val isFixed:Array[Boolean] = Array.tabulate(tmpVars.length)(i => variables(i).isInstanceOf[StoredCBLSIntConst])
    val isUsed:Array[Boolean] = Array.tabulate(tmpVars.length)(i =>
                                                                 isFixed.indices.exists( j => isFixed(j) && tmpVars(j)  == i)
    )
    var numUsed:Int = isUsed.count((b:Boolean) => b)

    for(i <- isFixed.indices if isFixed(i)){
      end(i) = end(tmpVars(i))
      start(end(i)) = i
      length(i) = length(tmpVars(i)) + 1
    }

    while(!isFixed.forall(_ == true)){
      val unfixedIdx = isFixed.indices.filterNot(isFixed(_))
      val idx = unfixedIdx(RandomGenerator.nextInt(unfixedIdx.length))
      val possibleSucc = RandomGenerator.shuffle(isUsed.indices.filterNot(isUsed(_))).iterator
      var succ = possibleSucc.next
      while(numUsed < tmpVars.length - 1  && end(succ) == idx){
        if(!possibleSucc.hasNext){
          throw new RuntimeException("Unable to initialize ThreeOpt neighbourhood");
        }
        succ = possibleSucc.next
      }
      tmpVars(idx) = succ
      isFixed(idx) = true
      isUsed(succ) = true
      start(end(succ)) = start(idx)
      end(start(idx)) = end(succ)
      length(end(succ)) += 1+length(idx)
      numUsed += 1
    }

    for(i <- tmpVars.indices)
      variables(i) := tmpVars(i)+offset
  }

  def isSatisfied(doPrint:Boolean):Boolean = {
    var nVisited = 0;
    var current = 1;
    do{
      if(doPrint)
        print(current + " -> ")
      current = vars(current).value
      nVisited += 1;
    }while(current != 1 && nVisited <= variables.length+10); // +10 so that we stop after valid length
    if(doPrint)
      println(current)
    nVisited == variables.length && current == 1
  }

  def localObjAssignVal(a: Iterable[(CBLSIntVar, Int)], objective: CBLSObjective): Int = {
    //memorize
    val oldvals: Iterable[(CBLSIntVar, Int)] = a.foldLeft(List.empty[(CBLSIntVar, Int)])(
      (acc, IntVarAndInt) => ((IntVarAndInt._1, IntVarAndInt._1.value)) :: acc)
    //excurse
    for (assign <- a)
      assign._1 := assign._2
    val newObj = objective.probe

    /* Use this for extensive debugging
    Note that subcircuit also calls this method and will then report an error!
    val isSat = isSatisfied(false)
    if(!isSat){
      isSatisfied(true)
      println("Something is wrong")
    }

    */
    //undo
    for (assign <- oldvals)
      assign._1 := assign._2
    newObj
  }

  def vars(idx: Int): CBLSIntVar = {
    variables(idx - offset)
  }

  def randomMove(objective: CBLSObjective, it: Int): Move = {
    val idx = rng(RandomGenerator.nextInt(variables.length))
    val next = rng(RandomGenerator.nextInt(variables.length))
    getMove(idx, next, _ => true, objective)
  }

  def getMove(idx: Int, newNext: Int, accept: Move => Boolean, objective: CBLSObjective): Move = {
    if (idx == newNext) return new NoMove()
    //would break the chain
    val next = vars(idx).value
    if (next == newNext) return new NoMove()
    //would break the chain
    val k = vars(next).value
    if(vars(idx).isInstanceOf[StoredCBLSIntConst] ||
      vars(next).isInstanceOf[StoredCBLSIntConst] ||
      vars(newNext).isInstanceOf[StoredCBLSIntConst])
      return new NoMove()
    val last = vars(newNext).value
    val list = List((vars(idx), k), (vars(next), last), (vars(newNext), next))
    val obj = objective.assignVal(list)
    acceptOr(new AssignsMove(list, obj), accept)
  }

  def getMinObjective(objective: CBLSObjective,it: Int, accept: Move => Boolean, acceptVar: CBLSIntVar => Boolean): Move = {
    val idx = selectMax(rng, (i: Int) => variableViolation(i - offset).value);
    val next = selectMin(rng)(next => getMove(idx, next, accept, objective).value)

    val aMove = getMove(idx, next, accept,objective)
    aMove
  }

  def getExtendedMinObjective(objective: CBLSObjective,it: Int, accept: Move => Boolean, acceptVar: CBLSIntVar => Boolean): Move = {

    val currentValue = objective.value
    
    val res = selectMin2(rng, rng, (idx: Int, next: Int) => getMove(idx, next, accept, objective).value, (idx: Int, next: Int) => idx != next) // do not use idx < next here as it is not symmetrical
    val best = res match {
      case (idx, next) => getMove(idx, next, accept, objective)
      case _ => new NoMove() //res is null when the NON TABU list is empty //Should not happen anymore now
    }
    best
  }

  def violation() = {
    variableViolation.foldLeft(0)((acc, x) => acc + x.value)
  };
}

class ThreeOptSub(variables: Array[CBLSIntVar],  cs: ConstraintSystem,
                  offset: Int) extends ThreeOpt(variables,  cs, offset) {
  //needed to add the allloop variable to be able to reinsert into the chain when the chain is only 1 element long.
  var allloop = false;

  override def reset() {
    super.reset();
    allloop = false;
  }
  def isConst(i:Int):Boolean = {
    vars(i).isInstanceOf[StoredCBLSIntConst]
  }
  override def getMove(idx:Int, newNext:Int, accept: Move => Boolean, objective: CBLSObjective): Move = {
    if(allloop){ // If everything is a selfloop
      if(vars(idx).isInstanceOf[StoredCBLSIntConst] || vars(idx).isInstanceOf[StoredCBLSIntConst]){
        //Cannot change a constant
        NoMove()
      }else if(idx != newNext){
        //The two nodes now become the main loop
        val list = List((vars(idx),newNext),(vars(newNext),idx))
        acceptOr(BeforeMove(AssignsMove(list, objective.assignVal(list)),
                                () =>{
                                  allloop = false
                                }), accept)
      }else{
        NoMove()
      }
    }else{
      if(idx == vars(idx).value){ // idx cannot be a self-loop
        NoMove()
      }else if(newNext == vars(newNext).value && !isConst(idx) && !isConst(newNext)) {
        //newNext is a self-loop that we want to put into the circuit

        val list = List((vars(idx),newNext),(vars(newNext), vars(idx).value))
        acceptOr(BeforeMove(AssignsMove(list, objective.assignVal(list)),
                                () => {
                                  allloop = false
                                }), accept)
      }else if(idx == newNext && !isConst(idx) && !isConst(vars(idx).value)){
        // Make vars(idx).value self-loop (a bit strange but we don't know prev of idx)

        val next = vars(idx).value
        val nextnext = vars(next).value
        val list = List((vars(idx),nextnext),(vars(next),next))

        acceptOr(BeforeMove(AssignsMove(list, objective.assignVal(list)),
                                () => {
                                  allloop = idx == nextnext
                                }), accept)
      }else if(!isConst(idx) && ! isConst(newNext) && !isConst(vars(idx).value)){
        super.getMove(idx,newNext,accept, objective)
      }else
        NoMove()
    }
  }
  def getMoveOld(idx: Int, newNext: Int, accept: Move => Boolean, objective: CBLSObjective): Move = {
    val next = vars(idx).value
    val k = vars(next).value
    val last = vars(newNext).value

    if (idx == next && last == newNext && !allloop) {
      //println("oops")
      return new NoMove() //cannot join two selfloops unless there are only selfloops
    }
    if (idx == newNext && idx == next) {
      return new NoMove() //cannot insert a selfloop into itself
    }
    //println("yep")
    if (idx == next && idx != newNext) {
      //idx is not in the chain, this should be an inclusion of idx after newNext

      val list = List((vars(idx), last), (vars(newNext), idx))
      return acceptOr(new BeforeMove(new AssignsMove(list, objective.assignVal(list)),
                                     () => allloop = false), accept);
    }
    if (last == newNext && idx != newNext) {
      //newNext is not in the chain, this should be an inclusion of newNext after idx
      val list = List((vars(idx), newNext), (vars(newNext), next))
      return acceptOr(new BeforeMove(new AssignsMove(list, objective.assignVal(list)),
                                     () => allloop = false), accept);
    }
    if (idx == newNext && idx != next) {
      //assumes this is a removal of next
      val list = List((vars(idx), k), (vars(next), next))
      return acceptOr(new BeforeMove(new AssignsMove(list, objective.assignVal(list)),
                                     () => if (idx == k) {
                                       // println(allloop)
                                       allloop = true
                                       //println(variables.map(v => v.value).mkString(","))
                                     }), accept);
    }
    if (next == newNext && idx != next) {
      //assumes this is a removal of next
      val list = List((vars(idx), k), (vars(next), next))
      return acceptOr(new BeforeMove(new AssignsMove(list, objective.assignVal(list)),
                                     () => if (idx == k) {
                                       //println(allloop)
                                       allloop = true
                                       //println(variables.map(v => v.value).mkString(","))
                                     }), accept);
    }
    val list = List((vars(idx), k), (vars(next), last), (vars(newNext), next))
    return acceptOr(new AssignsMove(list, objective.assignVal(list)), accept);
  }
}


class MaxViolating(searchVariables: Array[CBLSIntVar],
                   constraintSystem: ConstraintSystem) extends Neighbourhood(searchVariables) {

  val indexRange = 0 until searchVariables.length;
  val variableViolation: Array[IntValue] = searchVariables.map(constraintSystem.violation(_)).toArray
  var start = 0;

  def reset() = {
    for (v: CBLSIntVar <- searchVariables)
      v.setValue(v.domain.randomValue())
  }

  def randomMove(objective: CBLSObjective, it: Int): Move = {
    val bestIndex = indexRange(RandomGenerator.nextInt(indexRange.length))
    val bestValue = searchVariables(bestIndex).domain.randomValue()
    val minObjective = objective.assignVal(searchVariables(bestIndex), bestValue);
    return new AssignMove(searchVariables(bestIndex), bestValue, minObjective)
  }

  def getMinObjective(objective: CBLSObjective, it: Int, accept: Move => Boolean, acceptVar: CBLSIntVar => Boolean): Move = {
    val bestIndex = selectMax(indexRange,
                              (i: Int) => variableViolation(i).value,
                              (i:Int) => acceptVar(searchVariables(i)));

    val bestValue = if (searchVariables(bestIndex).domain.size < 1000000) {
      selectMin(searchVariables(bestIndex).domain)((i: Int) =>
                                                          acceptOr(new AssignMove(searchVariables(bestIndex), i,
                                                                                  objective.assignVal(
                                                                                    searchVariables(bestIndex), i)),
                                                                   accept).value,
                                                        _ != searchVariables(bestIndex).value)
    } else {
      val objVal = objective.value
      selectFirst(RandomGenerator.shuffle(searchVariables(bestIndex).domain), (i: Int) =>
        acceptOr(new AssignMove(searchVariables(bestIndex), i, objective.assignVal(searchVariables(bestIndex), i)),
                 accept).value < objVal
          && i != searchVariables(bestIndex).value
      )
    }
    return acceptOr(
      new AssignMove(searchVariables(bestIndex), bestValue, objective.assignVal(searchVariables(bestIndex), bestValue)),
      accept)
  }

  def getExtendedMinObjective(objective: CBLSObjective, it: Int, accept: Move => Boolean, acceptVar: CBLSIntVar => Boolean): Move = {

    var bMv = List.empty[Move]
    var bObj = Int.MaxValue
    var cVar = start
    var looped = false
    val oObj = objective.value
    while (!(looped && cVar == start)) {
      val v = searchVariables(cVar)
      if (acceptVar(v)
        && (variableViolation(cVar).value > 0 || RandomGenerator.nextInt(100) < 25)
        && v.domain.size < 10000000) {
        //TODO: Do something about this!
        val variableValue = v.value
        for (cVal <- v.domain if variableValue != cVal) {
          val mv = new AssignMove(v, cVal, objective.assignVal(v, cVal))
          if (accept(mv)) {
            val cObj = mv.value
            if (cObj < bObj) {
              bObj = cObj
              bMv = List(mv)
            }else if(cObj == bObj){
              bMv +:= mv
            }
          }
        }
        if (bObj < oObj) {
          start = cVar
          return bMv.head
        }
      }
      cVar += 1
      if (cVar == searchVariables.length) {
        looped = true
        cVar = 0
      }
    }
    if (bMv.isEmpty) {
      return new NoMove()
    } else {
      return bMv(RandomGenerator.nextInt(bMv.length))
    }
  }

  def violation() = {
    variableViolation.foldLeft(0)((acc, x) => acc + x.value)
  };
}


//This neighborhood assumes that all variables have the same domain
class MaxViolatingSwap(searchVariables: Array[CBLSIntVar],
                       constraintSystem: ConstraintSystem) extends Neighbourhood(searchVariables) {
  val indexRange = 0 until searchVariables.length;
  val variableViolation: Array[IntValue] = searchVariables.map(constraintSystem.violation(_))

  //TODO: Might be made more efficient by maintaining the two sets of variables, the ones assigned to true and the
  // ones assigned to false.
  def reset() = {

  }

  def randomMove(objective: CBLSObjective, it: Int): Move = {
    val bestIndex1 = indexRange(RandomGenerator.nextInt(indexRange.length))
    val bestIndex2 = indexRange(RandomGenerator.nextInt(indexRange.length))
    val minObjective = objective.swapVal(searchVariables(bestIndex1), searchVariables(bestIndex2))
    return new SwapMove(searchVariables(bestIndex1), searchVariables(bestIndex2), minObjective);
  }

  def getMinObjective(objective: CBLSObjective, it: Int, accept: Move => Boolean, acceptVar: CBLSIntVar => Boolean): Move = {

    //TODO: Only takes into account the violation for the first
    val bestIndex1 = selectMax(indexRange, (i: Int) => variableViolation(i).value,
                               (i:Int) => acceptVar(searchVariables(i)));
    val bestIndex2 = selectMin(indexRange)(
      (i: Int) => acceptOr(
                      new SwapMove(searchVariables(bestIndex1), searchVariables(i),
                            objective.swapVal(searchVariables(bestIndex1), searchVariables(i))), accept).value,
      (i: Int) => searchVariables(i).value != searchVariables(bestIndex1).value && i != bestIndex1);
    return acceptOr(new SwapMove(searchVariables(bestIndex1), searchVariables(bestIndex2),
                                 objective.swapVal(searchVariables(bestIndex1), searchVariables(bestIndex2))), accept)
  }

  def getExtendedMinObjective(objective: CBLSObjective, it: Int, accept: Move => Boolean, acceptVar: CBLSIntVar => Boolean): Move = {
    getMinObjective(objective, it, accept)
    //Seems too costly
    //    val bestPair = selectMin2(indexRange, indexRange, (v:Int,i:Int) => acceptOr(new FZSwapMove(searchVariables
    // (v),searchVariables(i),objectiveFun.swapVal(searchVariables(v),searchVariables(i))),accept).value)
    //    bestPair match{
    //      case (v,i)  => new FZSwapMove(searchVariables(v),searchVariables(i),objectiveFun.swapVal(searchVariables(v),
    // searchVariables(i)))
    //      case _ => new NoMove()
    //    }
  }

  def violation() = {
    variableViolation.foldLeft(0)((acc, x) => acc + x.value)
  };
}


//This neighborhood is not totally "holes in the domain"-proof!
class AllDifferent(searchVariables: Array[CBLSIntVar],
                   constraintSystem: ConstraintSystem) extends Neighbourhood(searchVariables) {
  /**/


  val (constants, variables) = searchVariables.partition((x) => x.min == x.max)
  val indexRange: Range = 0 until variables.length;
  val variableViolation: Array[IntValue] = variables.map(constraintSystem.violation(_)).toArray
  var freeValues: Set[Int] = Set.empty[Int]
  val (minVal, maxVal) = variables.foldLeft((Int.MaxValue, Int.MinValue))(
    (acc, v) => (math.min(acc._1, v.min), math.max(acc._2, v.max)))
  reset();

  def reset() = {
    freeValues = Set.empty[Int]
    for (i <- minVal to maxVal) {
      freeValues += i;
    }
    val cur = variables.map(_.value)
    val cnt = MMap.empty[Int, Int]
    var nbprob = 0;
    for (c <- constants) {
      freeValues -= c.value;
      cnt(c.value) = cnt.getOrElse(c.value, 0) + 1
      if (cnt(c.value) > 1) {
        throw new Exception("Unsat all_different");
      }
    }

    for (i <- indexRange) {
      cur(i) = variables(i).domain.randomValue()
      cnt(cur(i)) = cnt.getOrElse(cur(i), 0) + 1
      if (cnt(cur(i)) > 1) nbprob += 1
    }
    //TODO: Correct this code to avoid an infinite loop!
    //TODO: We actually need to make a max matching as in the CP propagator.
    var i = 0
    while (nbprob > 0) {
      if (cnt(cur(i)) > 1) {
        cnt(cur(i)) -= 1
        nbprob -= 1
        cur(i) = variables(i).domain.randomValue()
        cnt(cur(i)) = cnt.getOrElse(cur(i), 0) + 1
        if (cnt(cur(i)) > 1) nbprob += 1
      }
      i = (i + 1) % variables.length
    }

    for (i <- indexRange) {
      variables(i) := cur(i)
      //  println(variables(i))
      freeValues -= cur(i);
    }
    //  println(freeValues)
  }

  def getSwapMove(idx1: Int, idx2: Int, accept: Move => Boolean, objective: CBLSObjective) = {
    val v1 = variables(idx1).value
    val v2 = variables(idx2).value
    if (variables(idx1).inDomain(v2) && variables(idx2).inDomain(v1)) {
      acceptOr(new SwapMove(variables(idx1), variables(idx2),
                            objective.swapVal(variables(idx1), variables(idx2))), accept)
    };
    else {
      new NoMove()
    }
  }

  def getAssignMove(idx: Int, v: Int, accept: Move => Boolean, objective: CBLSObjective) = {
    if (variables(idx).inDomain(v) && freeValues.contains(v)) {
      acceptOr(new BeforeMove(new AssignMove(variables(idx), v, objective.assignVal(variables(idx), v)),
                              () => {
                                freeValues += variables(idx).value;
                                freeValues -= v;
                              }), accept)
    };
    else {
      new NoMove()
    }
  }

  def randomMove(objective: CBLSObjective, it: Int): Move = {
    if (freeValues.size == 0 || RandomGenerator.nextBoolean()) {
      val selectedIndex1 = indexRange(RandomGenerator.nextInt(indexRange.length))
      val selectedIndex2 = indexRange(RandomGenerator.nextInt(indexRange.length))
      getSwapMove(selectedIndex1, selectedIndex2, _ => true, objective)
    } else {
      val selectedIndex = indexRange(RandomGenerator.nextInt(indexRange.length))
      val selectedValue = variables(selectedIndex).domain.randomValue()
      getAssignMove(selectedIndex, selectedValue, _ => true, objective)
    }
  }

  def getMinObjective(objective: CBLSObjective, it: Int, accept: Move => Boolean, acceptVar: CBLSIntVar => Boolean): Move = {
    val rng2 = (0 until variables.length);
    val idx = selectMax(rng2, (i: Int) => variableViolation(i).value);
    getBest(List(idx), rng2, accept, objective)
  }

  def getExtendedMinObjective(objective: CBLSObjective, it: Int, accept: Move => Boolean, acceptVar: CBLSIntVar => Boolean): Move = {
    val rng2 = (0 until variables.length);
    //val before = System.currentTimeMillis()
    val mv = getBest(rng2, rng2, accept, objective)
    //accumulatedTime += System.currentTimeMillis() - before
    mv
  }

  var accumulatedTime:Long = 0l

  def getBest(rng1: Iterable[Int], rng2: Iterable[Int], accept: Move => Boolean, objective: CBLSObjective): Move = {
    val bestSwap = selectMin2(rng1, rng2, (idx: Int, next: Int) => getSwapMove(idx, next, accept,objective ).value,
                              (idx: Int, v: Int) =>
                                idx != v &&
                                  (variableViolation(idx).value > 0 || variableViolation(v).value > 0 || RandomGenerator.nextInt(100)<25) &&
                                  variables(idx).inDomain(variables(v).value) &&
                                  variables(v).inDomain(variables(idx).value))
    val swap = bestSwap match {
      case (i1, i2) => getSwapMove(i1, i2, accept, objective)
      case _ => new NoMove(Int.MaxValue)
    }
    if(freeValues.isEmpty) return swap

    val bestMove = selectMin2(rng1, freeValues, (idx: Int, v: Int) => getAssignMove(idx, v, accept, objective).value,
                              (idx: Int, v: Int) =>
                                (variableViolation(idx).value > 0 || RandomGenerator.nextInt(100)<25) &&
                                  variables(idx).inDomain(v))
    val move = bestMove match {
      case (i1, i2) => getAssignMove(i1, i2, accept, objective)
      case _ => new NoMove(Int.MaxValue)
    }
    if (swap.value < move.value) swap else move
  }

  def violation() = {
    variableViolation.foldLeft(0)((acc, x) => acc + x.value)
  };
}

class Inverse(xs: Array[CBLSIntVar], invXs: Array[CBLSIntVar],
              constraintSystem: ConstraintSystem, offset: Int = 0,
              fznXs: Array[IntegerVariable] = Array.empty,
              fznInvXs: Array[IntegerVariable] = Array.empty,
              cblsModel: FZCBLSModel) extends Neighbourhood(xs ++ invXs) {
  /**/

  val xsViolation: Array[IntValue] = xs.map(constraintSystem.violation(_))
  val invXsViolation: Array[IntValue] = invXs.map(constraintSystem.violation(_))
  val variableViolation: Array[IntValue] = xsViolation ++ invXsViolation


  val initCPModel = new FZCPBasicModel()
  initCPModel.createVariables(fznXs++fznInvXs)
  initCPModel.createConstraints(Array(inverse(fznXs,fznInvXs)))

  reset();
  def reset() = {
    initCPModel.push()
    initCPModel.createObjective(Objective.SATISFY)
    initCPModel.createRandomSearch()
    val (foundSolution, solutionMap) = initCPModel.startSearch()
    initCPModel.pop()
    if (foundSolution){
      for ((k,v) <- solutionMap) {
        if(!k.isBound && !k.isDefined) {
          val cblsVar = cblsModel.getCBLSVar(k)
          cblsVar match {
            case b:CBLSBoolVar =>
              println("% Neighbourhood initalization of inverse cannot be over Boolean variables. Aborting")
              System.exit(-1)
            case i:CBLSIntVar => i := v
          }
        }else if(k.isDefined){
          println("% Something is wrong, " + k.id + " is defined: " + k.isDefined)
        }
      }
    }else{
      println("% Neighbourhood initalization of inverse is UNSATISFIABLE. Aborting")
      System.exit(-1)
    }
  }

  /*

  def reset() = {
    //Awful bruteforce method:
    var tmpXs = Array.tabulate(xs.length)(i => 0)

    def recursiveFind(possibleValue: List[Int], index: Int): Boolean = {
      if (index == xs.length) return true
      for (v <- possibleValue if xs(index).inDomain(v) && invXs(v + offset).inDomain(index - offset)) {
        tmpXs(index) = v
        if (recursiveFind(possibleValue.filterNot(_ == v), index + 1)) {
          return true
        }
      }
      return false
    }

    val possibleValues = RandomGenerator.shuffle((-offset to xs.length - offset).toList)
    if (!recursiveFind(possibleValues, 0)) {
      throw new Exception("Unable to initialize inverse neighbourhood")
    }


    for (i <- xs.indices) {
      xs(i) := tmpXs(i)
      invXs(tmpXs(i) + offset) := i - offset
    }
  }*/

  def getSwapMove(idx1: Int, idx2: Int, accept: Move => Boolean, objective: CBLSObjective) = {
    val v1 = xs(idx1).value
    val v2 = xs(idx2).value
    if (xs(idx1).inDomain(v2) && xs(idx2).inDomain(v1)) {
      val invV1 = invXs(v1 + offset).value
      val invV2 = invXs(v2 + offset).value
      if (invXs(v1 + offset).inDomain(invV2) && invXs(v2 + offset).inDomain(invV1)) {
        assert(invV1 + offset == idx1 && invV2 + offset == idx2)
        if(!(invV1 + offset == idx1 && invV2 + offset == idx2)){
          throw new RuntimeException("Invers neighbourhood is not satisfied...")
        }
        xs(idx1) :=: xs(idx2)
        invXs(v1 + offset) :=: invXs(v2 + offset)
        val newObj = objective.probe
        xs(idx1) :=: xs(idx2)
        invXs(v1 + offset) :=: invXs(v2 + offset)
        acceptOr(new ChainMoves(Array(new SwapMove(xs(idx1), xs(idx2), newObj),
                                      new SwapMove(invXs(v1 + offset), invXs(v2 + offset), newObj)),
                                newObj),
                 accept)
      } else {
        new NoMove()
      }
    }
    else {
      new NoMove()
    }
  }

  def randomMove(objective: CBLSObjective, it: Int): Move = {
    val i1 = RandomGenerator.nextInt(xs.length)
    var i2 = RandomGenerator.nextInt(xs.length - 1)
    if (i2 >= i1) {
      i2 = i2 + 1
    }
    getSwapMove(i1, i2, m => true, objective)
  }

  def getMinObjective(objective: CBLSObjective, it: Int, accept: Move => Boolean, acceptVar: CBLSIntVar => Boolean): Move = {
    val rng2 = (0 until xs.length);
    val idx = selectMax(rng2, (i: Int) => xsViolation(i).value);
    getBest(List(idx), rng2, accept,acceptVar, objective)
  }

  def getExtendedMinObjective(objective: CBLSObjective, it: Int, accept: Move => Boolean, acceptVar: CBLSIntVar => Boolean): Move = {
    val rng2 = (0 until xs.length);
    getBest(rng2, rng2, accept, acceptVar, objective)
  }

  def getBest(rng1: Iterable[Int], rng2: Iterable[Int], accept: Move => Boolean,acceptVar: CBLSIntVar => Boolean = (v) => true, objective: CBLSObjective): Move = {

    //TODO: Iterate over every variable in index range and for each variable swap with variable form domain...
    val bestSwap = selectMinMove2(rng1, rng2, (idx1: Int, idx2: Int) => getSwapMove(idx1, idx2, accept, objective),
                              (idx1: Int, idx2: Int) =>
                                idx1 != idx2 && //should not be <
                                  ((xsViolation(idx1).value > 0 && xsViolation(idx2).value > 0) || RandomGenerator.nextInt(100) < 10) &&
                                  xs(idx1).inDomain(xs(idx2).value) && xs(idx2).inDomain(xs(idx1).value))
    bestSwap._1
  }

  def violation() = {
    variableViolation.foldLeft(0)((acc, x) => acc + x.value)
  };
}


class FlatNeighbourhood(val fzNeighbourhood: FZNeighbourhood,
                            subNeighbourhoodConstructors:Array[(CBLSObjective,ConstraintSystem) => FlatSubNeighbourhood],
                            objective: CBLSObjective,
                            val cblsModel: FZCBLSModel)
  extends Neighbourhood(fzNeighbourhood.getSearchVariables.map(v => cblsModel.getCBLSVar(v))) {

  val variableViolation: Array[IntValue] = searchVariables.map(cblsModel.c.violation(_))

  val subNeighbourhoods = subNeighbourhoodConstructors.map(_(objective,cblsModel.c))

  val initCPModel = new FZCPBasicModel()
  initCPModel.createVariables(fzNeighbourhood.getInitVariables)
  initCPModel.createConstraints(fzNeighbourhood.initConstraints)



  //reset();
  def reset() = {
    initCPModel.push()
    initCPModel.createObjective(Objective.SATISFY)
    initCPModel.createRandomSearch()
    val (foundSolution, solutionMap) = initCPModel.startSearch()
    initCPModel.pop()
    if (foundSolution){
      for ((k,v) <- solutionMap) {
        if(!k.isBound && !k.isDefined) {
          val cblsVar = cblsModel.getCBLSVar(k)
          cblsVar match {
            case b:CBLSBoolVar => b.assignTruthValue(v)
            case i:CBLSIntVar => i := v
          }
        }
      }
      for ((k,v) <- solutionMap) {
        if(k.isDefined)
          if(k.isInstanceOf[BooleanVariable]){
            if ((cblsModel.getIntValue(k).value == 0 && v != 0) || (cblsModel.getIntValue(k).value != 0 && v == 0)) {
              println("% Neighbourhood initalization failed, boolean invariant does not have the right value. Aborting")
              println("% " + k + " assigned to " + v + " but is " + cblsModel.getIntValue(k))
              System.exit(-1)
            }
          }else {
            if (!(cblsModel.getIntValue(k).value == v)) {
              println("% Neighbourhood initalization failed, invariant does not have the right value. Aborting")
              println("% " + k + " assigned to " + v + " but is " + cblsModel.getIntValue(k))
              System.exit(-1)
            }
          }
      }
    }else{
      println("% Neighbourhood initalization is UNSATISFIABLE. Aborting")
      System.exit(-1)
    }
  }

  def debugPrintVariables() = {
    System.out.println("% Current assignment in " + fzNeighbourhood.name + ": " + searchVariables.mkString("[",", ","]"))
  }

  def debugPrintValues() = {
    System.out.println("% Current values in " + fzNeighbourhood.name + ": " + searchVariables.map(_.value).mkString("[",", ","]"))
  }

  def debugPrintMove(m:Move) = {
    System.out.println("% Move in " + fzNeighbourhood.name + ": " +  m.toString)
  }

  def randomMove(objective: CBLSObjective, it: Int): Move = {
    getExtendedMinObjective(objective, it, _ => true, _ => true)
  }

  def getMinObjective(objective: CBLSObjective, it: Int, accept: Move => Boolean, acceptVar: CBLSIntVar => Boolean): Move = {
    //getExtendedMinObjective(it,accept,acceptVar)
    def acceptFun(v:CBLSIntVar):Boolean = {
      acceptVar(v) && (cblsModel.c.violation(v).value > 0)
    }
    val bestMoves = subNeighbourhoods.map(_.getMinObjective(objective, it,accept,acceptFun))
    val bestIdx = selectMin(bestMoves.indices)(i => bestMoves(i).value)
    //debugPrintMove(bestMoves(bestIdx))
    bestMoves(bestIdx)
  }

  def getExtendedMinObjective(objective: CBLSObjective, it: Int, accept: Move => Boolean, acceptVar: CBLSIntVar => Boolean): Move = {
    //debugPrintValues()
    def acceptFun(v:CBLSIntVar):Boolean = {
      acceptVar(v) && (cblsModel.c.violation(v).value > 0 || RandomGenerator.nextInt(1000)< 5)
    }
    val bestMoves = subNeighbourhoods.map(_.getExtendedMinObjective(objective, it,accept,acceptFun))
    val bestIdx = selectMin(bestMoves.indices)(i => bestMoves(i).value)
    //debugPrintMove(bestMoves(bestIdx))
    bestMoves(bestIdx)
  }

  def violation() = {
    variableViolation.foldLeft(0)((acc, x) => acc + x.value)
  };
}

class FlatSubNeighbourhood(val fzNeighbourhood: FZSubNeighbourhood,
                              whereConstraintSystem: ConstraintSystem,
                              ensureConstraintSystem: ConstraintSystem,
                              searchVariables: Array[CBLSIntVar],
                              val cblsModel: FZCBLSModel)
  extends Neighbourhood(fzNeighbourhood.getSearchVariables.map(v => cblsModel.getCBLSVar(v))) {

  val variableViolation: Array[IntValue] = searchVariables.map(cblsModel.c.violation(_))


  //TODO: Move to CBLSBuilder
  val itVariables: Array[CBLSIntVar] = fzNeighbourhood.itVariables.map(v => cblsModel.getCBLSVar(v))
  var itIterators: Array[Iterator[Int]] = itVariables.map(_.domain.iterator)
  for (i <- itVariables.indices) {
    itVariables(i) := itIterators(i).next()
  }

  var currentIterator = 0;
  val numIterators = itVariables.length

  //TODO: Move to CBLSBuilder, FZ stuff should not leak into neighbourhoods
  val moveActions = fzNeighbourhood.moves.map((m: oscar.flatzinc.model.FZMove) =>
                                                m match {
                                                  case FZAssignMove(lhs, rhs) =>
                                                    AssignAction(cblsModel.getCBLSVar(lhs),
                                                                 cblsModel.getIntValue(rhs))
                                                  case FZAssignArrayMove(lhs, index, rhs) =>
                                                    AssignArrayAction(lhs.map(cblsModel.getCBLSVar(_)),
                                                                      cblsModel.getIntValue(index),
                                                                      cblsModel.getIntValue(rhs))
                                                  case FZSwapMove(lhs, rhs) =>
                                                    SwapAction(cblsModel.getCBLSVar(lhs),
                                                               cblsModel.getCBLSVar(rhs))
                                                  case FZSwapArrayMove(lhs, leftIndex, rhs, rightIndex) =>
                                                    SwapArrayAction(lhs.map(cblsModel.getCBLSVar(_)),
                                                                    cblsModel.getIntValue(leftIndex),
                                                                    rhs.map(cblsModel.getCBLSVar(_)),
                                                                    cblsModel.getIntValue(rightIndex))
                                                }
  ).toArray

  private def increment(): Boolean = {
    if (itIterators(currentIterator).hasNext) {
      itVariables(currentIterator) := itIterators(currentIterator).next()
      true
    } else {
      itIterators(currentIterator) = itVariables(currentIterator).domain.iterator
      itVariables(currentIterator) := itIterators(currentIterator).next()
      currentIterator += 1
      val result = if (currentIterator >= numIterators) {
        false
      } else {
        increment()
      }
      currentIterator -= 1
      result
    }
  }

  def reset() = {

  }

  def randomMove(objective: CBLSObjective, it: Int): Move = {
    getExtendedMinObjective(objective, it, _ => true, _ => true)
  }

  def getMinObjective(objective: CBLSObjective, it: Int, accept: Move => Boolean, acceptVar: CBLSIntVar => Boolean): Move = {
    //getExtendedMinObjective(it, accept, acceptVar)
    val currentObj = objective.value
    var bestObj = Int.MaxValue
    var bestMove: List[Move] = List(NoMove())

    //println(fzNeighbourhood.getSearchVariables.map(cblsModel.getCBLSVar(_)).mkString("\n"))
    while (increment()) {
      if (whereConstraintSystem.violation.value == 0) {
        // Compute the current values of all variables
        for (m <- moveActions) {
          m.computeAssignment()
        }
        //Ignore No-Op moves
        if(moveActions.exists(_.modifies()) && moveActions.forall(_.isValid(acceptVar))) {
          // Perform the assignment (depends on all values being already computed)
          for (m <- moveActions) {
            m.performAssignment()
          }
          val newObj = objective.probe
          if (newObj <= bestObj && ensureConstraintSystem.violation.value == 0) {
            if(newObj < currentObj) {
              val returnMove = ChainMoves(moveActions.map(_.getCurrentMove(newObj)), newObj)
              for (m <- moveActions)
                m.undo()
              return returnMove
            }
            // generates a move of the type that other neighbourhoods use
            val tmp = ChainMoves(moveActions.map(_.getCurrentMove(newObj)), newObj)
            if (accept(tmp)) {
              //for (m <- moveActions) {
              //  m.saveBest()
              //}
              if (newObj < bestObj) {
                bestMove = List(tmp)
              } else {
                bestMove :+= tmp
              }
              bestObj = newObj
            }
          }

          // Undo the assignment so that we do not commit to it.
          for (m <- moveActions) {
            m.undo()
          }
        }
      }
    }
    bestMove(RandomGenerator.nextInt(bestMove.length))
  }

  def debugPrintValues() = {
    System.out.println("% Current values in " + fzNeighbourhood.name + ": " + searchVariables.map(_.value).mkString("[",", ","]"))
  }

  def getExtendedMinObjective(objective: CBLSObjective, it: Int, accept: Move => Boolean, acceptVar: CBLSIntVar => Boolean): Move = {
    var bestObj = Int.MaxValue
    var bestMove: List[Move] = List(NoMove())

    //println(fzNeighbourhood.getSearchVariables.map(cblsModel.getCBLSVar(_)).mkString("\n"))
    while (increment()) {
      if (whereConstraintSystem.violation.value == 0) {
        // Compute the current values of all variables
        for (m <- moveActions) {
          m.computeAssignment()
        }
        //Ignore No-Op moves
        if(moveActions.exists(_.modifies()) && moveActions.forall(_.isValid(acceptVar))) {
          // Perform the assignment (depends on all values being already computed)
          for (m <- moveActions) {
            m.performAssignment()
          }
          val newObj = objective.probe
          if (newObj <= bestObj && ensureConstraintSystem.violation.value == 0) {
            // generates a move of the type that other neighbourhoods use
            val tmp = ChainMoves(moveActions.map(_.getCurrentMove(newObj)), newObj)
            if (accept(tmp)) {
              //for (m <- moveActions) {
              //  m.saveBest()
              //}
              if (newObj < bestObj) {
                bestMove = List(tmp)
              } else {
                bestMove :+= tmp
              }
              bestObj = newObj
            }
          }

          // Undo the assignment so that we do not commit to it.
          for (m <- moveActions) {
            m.undo()
          }
        }
      }
    }
    bestMove(RandomGenerator.nextInt(bestMove.length))
  }

  def violation() = {
    variableViolation.foldLeft(0)((acc, x) => acc + x.value)
  };
}