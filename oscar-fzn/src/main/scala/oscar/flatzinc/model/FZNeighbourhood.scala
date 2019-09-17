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

package oscar.flatzinc.model

/**
  * @author Gustav Bjordal
  */

class FZNeighbourhood(val name: String,
                      val subNeighbourhoods: Seq[FZSubNeighbourhood],
                      val initVariables: Seq[Variable],
                      val initConstraints: Seq[Constraint]) {

  private val controlledVariables = subNeighbourhoods.flatMap(_.getControlledAndDeclaredVariables).distinct.toArray

  def getControlledVariables: Array[Variable] = {
    controlledVariables
  }

  private val searchVariables = subNeighbourhoods.flatMap(_.getSearchVariables).distinct.toArray

  def getSearchVariables: Array[Variable] = {
    searchVariables
  }

  private val allInitVariables = (initConstraints.flatMap(_.variables) ++ initVariables).distinct
  def getInitVariables: Seq[Variable] = {
    allInitVariables
  }
}

class FZSubNeighbourhood(val name: String,
                         val itVariables: Array[Variable],
                         val moves: List[FZMove],
                         val whereVariables: Array[Variable],
                         val whereConstraints: List[Constraint],
                         val ensureVariables: Array[Variable],
                         val ensureConstraints: List[Constraint]) {

  private val controlledVariables =
    (moves.flatMap(_.getControlledVariables) ++ itVariables ++ whereVariables ++ ensureVariables).distinct.toArray

  private val dependentVariables = (moves.flatMap(_.getDependentVariables) ++
    whereConstraints.flatMap(_.getVariables) ++
    ensureConstraints.flatMap(_.getVariables)
    .distinct
    .filterNot(v => ensureVariables.contains(v) || whereVariables.contains(v))).toArray

  def getControlledAndDeclaredVariables: Array[Variable] = {
    controlledVariables
  }

  def getDependentVariables: Array[Variable] = {
    dependentVariables
  }

  private val searchVariables = moves.flatMap(_.getControlledVariables).distinct.toArray

  def getSearchVariables: Array[Variable] = {
    searchVariables
  }

  def debugPrint = {
    println("------ Neighbourhood for " + name + " ------")
    println("Iterator variables: ")
    for (it <- itVariables) {
      println("\t" + it)
    }
    println("Where variables:")
    for (e <- whereVariables) {
      println("\t" + e)
    }
    println("Where constraints:")
    for (e <- whereConstraints) {
      println("\t" + e)
    }
    println("Moves:")
    for (m <- moves) {
      println("\t" + m)
    }
    println("Ensure variables:")
    for (e <- ensureVariables) {
      println("\t" + e)
    }
    println("Ensure constraints:")
    for (e <- ensureConstraints) {
      println("\t" + e)
    }
  }

}
