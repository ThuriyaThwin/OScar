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

package oscar.examples.cp.scheduling

import oscar.cp._

object OptionalTasks extends CPModel with App {

  val horizon = 8
  val durationsData = Array(2, 2, 3, 3, 3, 4, 4, 5, 6, 7)
  val profitsData = Array(1, 2, 4, 3, 2, 5, 3, 6, 4, 8)
  val demandsData = Array(1, 1, 1, 1, 1, 1, 1, 1, 1, 1)
  val capaMax = 2

  val nTasks = durationsData.length
  val Tasks = 0 until nTasks

  val durations = Array.tabulate(nTasks)(t => CPIntVar(durationsData(t)))
  val starts = Array.tabulate(nTasks)(t => CPIntVar(0 to horizon - durations(t).min))
  val ends = Array.tabulate(nTasks)(t => CPIntVar(durations(t).min to horizon))
  val demands = Array.tabulate(nTasks)(t => CPIntVar(demandsData(t)))
  val resources = Array.fill(nTasks)(CPIntVar(0 to 1))

  val profits = Array.tabulate(nTasks)(t => resources(t) * profitsData(t))
  val totalProfit = sum(profits)

  onSolution {
    println("Total profit of " + totalProfit.value)
    for (t <- Tasks) {
      if (resources(t).value == 1) {
        println("Task " + t + " of profit " + profitsData(t) + " and duration " + durationsData(t) + " is executed at time " + starts(t).value)
      }
    }
  }

  // Consistency 
  for (t <- Tasks) {
    add(ends(t) === starts(t) + durations(t))
  }
  // Cumulative
  add(maxCumulativeResource(starts, durations, ends, demands, resources, CPIntVar(capaMax), 1))

  maximize(totalProfit)

  search {
    binaryFirstFail(resources) ++ binaryFirstFail(starts)
  }
  
  println(start())
}
