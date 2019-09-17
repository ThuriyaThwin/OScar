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
package oscar.cp.constraints

import oscar.cp.core.{CPPropagStrength, Constraint}
import oscar.cp.core.variables.{CPIntVar, CPVar}

/**
  * @author Gustav Björdal gustav.bjordal@it.uu.se
  */
final class Writes(output: Array[CPIntVar],
                   input: Array[CPIntVar],
                   position: Array[CPIntVar],
                   value: Array[CPIntVar]) extends Constraint(output(0).store, "Writes") {
  
  require(output.length > 0, "no variable.")
  require(output.length == input.length, "input output of different length.")
  require(position.length == value.length, "different number of indices and values to write")
 
  private val dummy = position.length // (maxIndex+1)
  private val S = Array.tabulate(output.length)(i => CPIntVar(0, dummy, "IndexVar_" + i)(s))
  
  override def associatedVars(): Iterable[CPVar] = output ++ input ++ position ++ value ++ S
  
  override def setup(l: CPPropagStrength): Unit = {
    for (i <- output.indices) {
      s.post(S(i).isEq(dummy).implies(output(i).isEq(input(i))))
      for (j <- position.indices) {
        s.post(S(i).isEq(j).implies(position(j).isEq(i)))
        if (!position(j).hasValue(i)) {
          S(i).removeValue(j)
        }
      }
    }
    //s.post(new AllDifferentExcept(S,Set(dummy))) // TODO: AllDifferentExcept is buggy
    s.post(new GCC(S,
                    0,
                    Array.tabulate(position.length+1)(i => if (i == dummy) S.length - position.length else 0),
                    Array.tabulate(position.length+1)(i => if (i == dummy) S.length - 1 else 1)))
    
    // TODO: make decomposition native,
    for (j <- position.indices) {
      s.post(new ElementVar(output, position(j), value(j)), CPPropagStrength.Strong)
    }
    for (i <- output.indices) {
      val inP = position.map(_.isEq(i))
      s.post(new Or(inP ++ Array(output(i).isEq(input(i)))))
    }
  }
}

final class Writes_Bad(output: Array[CPIntVar],
                   input: Array[CPIntVar],
                   position: Array[CPIntVar],
                   value: Array[CPIntVar]) extends Constraint(output(0).store, "Writes") {
  
  require(output.length > 0, "no variable.")
  require(output.length == input.length, "input output of different length.")
  require(position.length == value.length, "different number of indices and values to write")
  
  override def associatedVars(): Iterable[CPVar] = output ++ input ++ position ++ value
  
  override def setup(l: CPPropagStrength): Unit = {
    for (j <- position.indices) {
      s.post(new ElementVar(output, position(j), value(j)), CPPropagStrength.Strong)
    }
    for (i <- output.indices) {
      val inP = position.map(_.isEq(i))
      s.post(new Or(inP ++ Array(output(i).isEq(input(i)))))
    }
  }
}