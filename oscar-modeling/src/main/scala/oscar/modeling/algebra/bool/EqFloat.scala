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

package oscar.modeling.algebra.bool

import oscar.modeling.algebra.Expression
import oscar.modeling.algebra.floating.FloatExpression
import oscar.modeling.algebra.integer.IntExpression
import oscar.modeling.misc.VariableNotBoundException

/**
 * a == b
 */
case class EqFloat(v: Array[FloatExpression]) extends BoolExpression {
  /**
   * Evaluate this expression. All variables referenced have to be bound.
   * @throws VariableNotBoundException when a variable is not bound
   * @return the value of this expression
   */
  override def evaluateBool(): Boolean = {
    val eval = v.map(_.evaluate())
    eval.forall(x => x == eval(0))
  }

  /**
   * Returns an iterable that contains all sub-expressions of this expression
   */
  override def subexpressions(): Iterable[FloatExpression] = v

  /**
   * Apply a function on all sub-expressions of this expression and returns a new expression of the same type.
   * This function should return a value that is of the class as the object that was given to it.
   */
  override def mapSubexpressions(func: (Expression) => Expression): BoolExpression = EqFloat(v.map(func).asInstanceOf[Array[FloatExpression]])

  /**
    * True if the variable is bound
    */
  override def isBound: Boolean = subexpressions().forall(_.isBound)
}

object EqFloat {
  def apply(a: FloatExpression*): EqFloat = EqFloat(a.toArray)

  def apply(v: Iterable[FloatExpression]): EqFloat = EqFloat(v.toArray)

  def apply[A](indices: Iterable[A])(f: A => FloatExpression): EqFloat = EqFloat(indices map f)

  def apply[A, B](indices1: Iterable[A], indices2: Iterable[B])(f: (A, B) => FloatExpression): EqFloat = EqFloat(for (i <- indices1; j <- indices2) yield f(i, j))

  def apply(n1: Int, n2: Int)(f: (Int, Int) => FloatExpression): EqFloat = EqFloat(0 until n1, 0 until n2)(f)
}