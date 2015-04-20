package oscar.cp.constraints

import oscar.algo.search.Objective
import oscar.cp.core.Constraint
import oscar.cp._
import oscar.cp.core.CPOutcome._
import oscar.cp.core.CPOutcome
import oscar.cp.core.CPPropagStrength
import oscar.cp.core.CPSolver

class CPObjectiveLexicographic(val solver: CPSolver, val variables: Array[CPIntVar])
extends Constraint(solver, "CPObjectiveLexicographic") {
  val n = variables.length
  
  val best = Array.ofDim[Int](n)

  override def setup(strength: CPPropagStrength): CPOutcome = {
    variables.foreach(_.callPropagateWhenBoundsChange(this))
    
    // Here we minimize, so the worst value is all max
    for (i <- 0 until n) best(i) = variables(i).max
    best(n - 1) += 1 // we do not know whether the worst objective has a solution!
    
    propagate()
  }
  
  solver.postCut(this)
  solver.onSolution(this.tighten())

  override def propagate(): CPOutcome = {
    var p = 0
    
    while (p < n && variables(p).isBoundTo(best(p))) p += 1
    
    if (p == n) return Failure
    
    val oc = if (p + 1 == n || (p + 1 < n && variables(p+1).min > best(p+1) )) {
      variables(p).updateMax(best(p) - 1)
    }
    else {
      variables(p).updateMax(best(p))
    }
    
    if (oc == Failure) Failure else Suspend   
  }
  
  // Called on solution to record best value so far
  def tighten(): Unit = {
    for (i <- 0 until n) {
      val obj = variables(i)
      if (!obj.isBound) {
        throw new RuntimeException("objective" + i + " not bound:" + obj)
      }
      else {
        best(i) = obj.min
      }
    }
    
    if (!solver.silent) {
      println("objective tightened to " + best.mkString("(", ", ", ")"))
    }
  }
  
}