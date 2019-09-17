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
  * @author Jean-Noel Monette
  */
package oscar.flatzinc.cp

import oscar.cp._
import oscar.cp.constraints.SumLeEq
import oscar.flatzinc.model._

import scala.language.implicitConversions

class CPConstraintPoster(val pstrength: oscar.cp.core.CPPropagStrength) {
  implicit def c2ca(c: oscar.cp.Constraint):
  Array[(oscar.cp.Constraint, oscar.cp.core.CPPropagStrength)] = {
    Array[(oscar.cp.Constraint, oscar.cp.core.CPPropagStrength)]((c, pstrength))
  }
  
  implicit def c2cs(c: oscar.cp.Constraint): (oscar.cp.Constraint, oscar.cp.core.CPPropagStrength) = (c, pstrength)
  
  implicit def c2ca(c: (oscar.cp.Constraint, oscar.cp.core.CPPropagStrength)):
  Array[(oscar.cp.Constraint, oscar.cp.core.CPPropagStrength)] = {
    Array[(oscar.cp.Constraint, oscar.cp.core.CPPropagStrength)](c)
  }
  
  implicit def ca2cs(c: Array[oscar.cp.Constraint]):
  Array[(oscar.cp.Constraint, oscar.cp.core.CPPropagStrength)] = {
    c.map(c2cs)
  }
  
  def getConstraint(cstr: oscar.flatzinc.model.Constraint, getVar: Variable => CPIntVar,
                    getBoolVar: Variable => CPBoolVar): Array[(oscar.cp.Constraint, oscar.cp.core.CPPropagStrength)] = {
    
    def getVarArray(x: Array[Variable]) = {
      x.map(getVar)
    }
    
    cstr match {
      case cumulative(s, d, r, capa, _) if r.forall(v => 2 * v.min > capa.max) =>
        unaryResource(s.map(getVar), d.map(getVar), s.zip(d).map(vv => getVar(vv._1) + getVar(vv._2)))
      //TODO: We create variables in cumulative but we might want to memoize those as well!
      case cumulative(s, d, r, capa, _) =>
        oscar.cp.maxCumulativeResource(s.map(getVar), d.map(getVar), s.zip(d).map(vv => getVar(vv._1) + getVar(vv._2)),
                                        r.map(getVar), getVar(capa))
      case maximum_int(x, y, _) =>
        c2ca(oscar.cp.maximum(y.map(getVar), getVar(x))) ++ ca2cs(y.map(v => getVar(v) <= getVar(x)))
      case minimum_int(x, y, _) =>
        c2ca(oscar.cp.minimum(y.map(getVar), getVar(x))) ++ ca2cs(y.map(v => getVar(v) >= getVar(x)))
      
      case all_different_int(x, _) => (oscar.cp.allDifferent(x.map(getVar)), Medium) //Weak, Strong, Medium
      case at_least_int(c, x, v, _) => oscar.cp.atLeast(c.value, x.map(getVar), v.value)
      case at_most_int(c, x, v, _) => oscar.cp.atMost(c.value, x.map(getVar), v.value)
      case exactly_int(c, x, v, _) =>
        oscar.cp.countEq(getVar(c), x.map(getVar), v.value) //TODO: use a version with fixed c
      case count_eq(x, v, c, _) => oscar.cp.countEq(getVar(c), x.map(getVar), getVar(v))
      case inverse(xs, ys, _) => oscar.cp.inverse(xs.map(getVar(_) - 1), ys.map(getVar(_) - 1))
      
      case bin_packing_load(load, bin, w, _) =>
        new oscar.cp.constraints.BinPacking(bin.map(getVar(_) - 1), w.map(_.value), load.map(getVar))
      case circuit(xs, _) => {
//        val foo = xs.map(_.cstrs).reduce(_ intersect _)
        new oscar.cp.constraints.Circuit(xs.map(v => getVar(v) - 1), false)
      }
      case subcircuit(xs, _) => oscar.cp.constraints.SubCircuit(xs.map(getVar), 1)
      
      case global_cardinality(xs, cover, count, _)
        if count.forall(_.isBound)
          && cover.map(_.value).max - cover.map(_.value).min + 1 == cover.length =>
        val coverMin = cover.map(_.value).min
        val coverMax = cover.map(_.value).max
        val fullCount = Array.tabulate(coverMax - coverMin + 1)(i => {
          val idx = cover.map(_.value).indexOf(i + coverMin)
          if (idx < 0) 0 else count(idx).value
        })
        new oscar.cp.constraints.GCC(xs.map(getVar), coverMin, Array.tabulate(fullCount.length)(_ => 0), fullCount)
      
      case global_cardinality(xs, cover, count, _) =>
        val store = getVar(xs(0)).store
        val coverMin = cover.map(_.value).min
        val coverMax = cover.map(_.value).max
        val fullCount = Array.tabulate(coverMax - coverMin + 1)(i => {
          val idx = cover.map(_.value).indexOf(i + coverMin)
          if (idx < 0) CPIntVar(0, xs.length)(store) else getVar(count(idx))
        })
        new oscar.cp.constraints.GCCVar(xs.map(getVar), coverMin, fullCount)
      case global_cardinality_low_up(xs, cover, lbound, ubound, _) =>
        val coverMin = cover.map(_.value).min
        val coverMax = cover.map(_.value).max
        val fullLBound = Array.tabulate(coverMax - coverMin + 1)(i => {
          val idx = cover.map(_.value).indexOf(i + coverMin)
          if (idx < 0) 0 else lbound(idx).value
        })
        val fullUBound = Array.tabulate(coverMax - coverMin + 1)(i => {
          val idx = cover.map(_.value).indexOf(i + coverMin)
          if (idx < 0) xs.length else ubound(idx).value
        })
        new oscar.cp.constraints.GCCFWC(xs.map(getVar), coverMin, fullLBound, fullUBound)
      case nvalue_int(y, xs, _) => new oscar.cp.constraints.AtLeastNValue(xs.map(getVar), getVar(y))
      
      case array_bool_and(as, r, _) => new oscar.cp.constraints.And(as.map(getBoolVar), getBoolVar(r))
      case array_bool_element(b, as, r, _) => oscar.cp.elementVar(as.map(getVar), getVar(b) - 1, getVar(r))
      case array_bool_or(as, r, _) => oscar.cp.or(as.map(getBoolVar), getBoolVar(r))
      // case array_bool_xor(as, _)                    =>
      case array_int_element(b, as, r, _) => oscar.cp.element(as.map(_.value), getVar(b) - 1, getVar(r))
      case array_var_bool_element(b, as, r, _) => oscar.cp.elementVar(as.map(getBoolVar), getVar(b) - 1,
                                                                       getBoolVar(r))
      case array_var_int_element(b, as, r, _) => oscar.cp.elementVar(as.map(getVar), getVar(b) - 1, getVar(r))
      
      case bool2int(x, y, _) => getBoolVar(x) === getVar(y)
      case bool_and(a, b, r, _) => new oscar.cp.constraints.And(Array(getBoolVar(a), getBoolVar(b)), getBoolVar(r))
      case bool_clause(a, b, _) => oscar.cp.or(a.map(getBoolVar) ++ b.map(getBoolVar(_).not))
      case reif(bool_clause(a, b, _), c) => oscar.cp.or(a.map(getBoolVar) ++ b.map(getBoolVar(_).not), getBoolVar(c))
      case bool_eq(a, b, _) => getBoolVar(a) === getBoolVar(b)
      case bool_le(a, b, _) => getBoolVar(a) <= getBoolVar(b)
      case bool_lin_eq(params, vars, sum, _) =>
        oscar.cp.weightedSum(params.map(_.value), vars.map(getVar), getVar(sum))
      case bool_lin_le(params, vars, sum, _) =>
        oscar.cp.weightedSum(params.map(_.value), vars.map(getVar)) <= getVar(sum) //TODO: make it native
      case bool_lt(a, b, _) => getBoolVar(a) < getBoolVar(b)
      case reif(bool_lt(a, b, _), c) =>
        getBoolVar(c) === (getBoolVar(a) ?< getBoolVar(b)) //TODO: There might exist a better expression for this.
      case reif(bool_eq(a, b, _), c) =>
        getBoolVar(c) === (getBoolVar(a) ?=== getBoolVar(b)) //TODO: There might exist a better expression for this.
      case bool_not(a, b, _) => getBoolVar(a) === getBoolVar(b).not
      case bool_or(a, b, r, _) => oscar.cp.or(Array(getBoolVar(a), getBoolVar(b)), getBoolVar(r))
      case bool_xor(a, b, r, _) => getBoolVar(r) === (getVar(a) ?!== getVar(b))
      
      case int_abs(x, y, _) => new oscar.cp.constraints.Abs(getVar(x), getVar(y))
      case int_div(x, y, z, _) if y.max == y.min =>
        new oscar.cp.constraints.Div(getVar(x),y.value,getVar(z))
//        new DivBND(getVar(x),y.value,getVar(z))
      //  (getVar(x) - (getVar(x) mod y.max)) === getVar(z) * y.max
      case int_eq(x, y, _) => getVar(x) === getVar(y)
      case int_le(x, y, _) => getVar(x) <= getVar(y)
      case int_lt(x, y, _) => getVar(x) < getVar(y)
      case reif(int_eq(x, y, _), b) => new oscar.cp.constraints.EqReifVar(getVar(x),getVar(y),getBoolVar(b))
      case reif(int_le(x, y, _), b) => getBoolVar(b) === (getVar(x) ?<= getVar(y))
      case reif(int_lt(x, y, _), b) => getBoolVar(b) === (getVar(x) ?< getVar(y))
      case reif(int_ne(x, y, _), b) => getBoolVar(b) === (getVar(x) ?!== getVar(y))
      
      // TODO: Handle binary and ternary cases, as well as all unit weights
      case int_lin_eq(params, vars, sum, _) =>
        val weightedVars = params.map(_.value).zip(vars.map(getVar)).map(v => {
          if (v._1 == 1) {
            v._2
          } else {
            oscar.cp.mul(v._2, v._1)
          }
        })
        oscar.cp.sum(weightedVars, getVar(sum))
      
      case int_lin_le(params, vars, sum, _) =>
        val weightedVars = params.map(_.value).zip(vars.map(getVar)).map(
                                                                          v => {
                                                                            if (v._1 == 1) {
                                                                              v._2
                                                                            } else {
                                                                              oscar.cp.mul(v._2,
                                                                                            v._1)
                                                                            }
                                                                          })
        new SumLeEq(weightedVars, getVar(sum))
      
      case int_lin_ne(params, vars, sum, _) =>
        oscar.cp.weightedSum(params.map(_.value), vars.map(getVar)) !== getVar(sum) //TODO: make it native
      
      case reif(int_lin_eq(params, vars, sum, _), b) =>
        getBoolVar(b) === (oscar.cp.weightedSum(params.map(_.value), vars.map(getVar)) ?=== getVar(sum))
      case reif(int_lin_le(params, vars, sum, _), b) =>
        getBoolVar(b) === (oscar.cp.weightedSum(params.map(_.value), vars.map(getVar)) ?<= getVar(sum))
      case reif(int_lin_ne(params, vars, sum, _), b) =>
        getBoolVar(b) === (oscar.cp.weightedSum(params.map(_.value), vars.map(getVar)) ?!== getVar(sum))
      case int_max(x, y, z, _) => oscar.cp.maximum(Array(getVar(x), getVar(y)), getVar(z))
      case int_min(x, y, z, _) => oscar.cp.minimum(Array(getVar(x), getVar(y)), getVar(z))
      case int_mod(x, y, z, _) if y.isBound => getVar(x) % y.value == getVar(z)
      case int_ne(x, y, _) => getVar(x) !== getVar(y)
      case int_plus(x, y, z, _) =>
        new oscar.cp.constraints.BinarySum(getVar(x), getVar(y), getVar(z))
      case int_times(x, y, z, _) => new oscar.cp.constraints.MulVar(getVar(x), getVar(y), getVar(z))
      case set_in(x, s, _) => new oscar.cp.constraints.InSet(getVar(x), s.toSortedSet)
      case reif(set_in(x, s, _), b) => new oscar.cp.constraints.InSetReif(getVar(x), s.toSortedSet, getBoolVar(b))
      case table_int(xs, ts, _) =>
        oscar.cp.table(
                        xs.map(getVar(_)),
                        Array.tabulate(ts.length / xs.length)(row => {
                          Array.tabulate(xs.length)(i => ts(row * xs.length + i).value)
                        }))
      case default => Console.err.println("% Could not perform initial domain reduction using " + default)
        Array.empty
    }
  }
  
  
  def getSoftConstraint(cstr: oscar.flatzinc.model.Constraint, getVar: Variable => CPIntVar,
                        getBoolVar: Variable => CPBoolVar,store:CPSolver): (CPIntVar, Array[(oscar.cp.Constraint, oscar.cp.core.CPPropagStrength)]) = {
    def getVarArray(x: Array[Variable]) = {
      x.map(getVar)
    }
    
    cstr match {
      case int_lin_eq(params, vars, sum, _) =>
        val weightedVars = params.map(_.value).zip(vars.map(getVar)).map(v => {
          if (v._1 == 1) {
            v._2
          } else {
            oscar.cp.mul(v._2, v._1)
          }
        })
        val s = oscar.cp.sum(weightedVars)
        (oscar.cp.absolute(s - getVar(sum)), Array.empty)

//      case bool_clause(a, b, _) =>
//        (oscar.cp.minimum(a.map(getBoolVar).map(_.not) ++ b.map(getBoolVar)),Array.empty)

//      case array_var_int_element(b, as, r, _) =>
//        (oscar.cp.absolute(oscar.cp.elementVar(as.map(getVar), getVar(b) - 1) - getVar(r)), Array.empty)

//      case array_bool_or(as, r, _) =>
//        (oscar.cp.absolute(oscar.cp.maximum(as.map(getBoolVar)) - getVar(r)), Array.empty)
      
      case array_int_element(b, as, r, _) =>
        (oscar.cp.absolute(oscar.cp.element(as.map(_.value), getVar(b) - 1) - getVar(r)), Array.empty)
        
      case int_lin_le(params, vars, sum, _) =>
        val weightedVars = params.map(_.value).zip(vars.map(getVar)).map {
          v => {
            if (v._1 == 1) {
              v._2
            } else {
              oscar.cp.mul(v._2,
                            v._1)
            }
          }
        }
        val s = oscar.cp.sum(weightedVars)
        (oscar.cp.maximum(Array(s - getVar(sum),CPIntVar(0)(store))), Array.empty)
      
      case default =>
        System.err.println("% Unable to soften " + default + ". Creating hard version instead.")
        (CPIntVar(0)(store), getConstraint(cstr, getVar, getBoolVar))
    }
  }
  
  
}
  
