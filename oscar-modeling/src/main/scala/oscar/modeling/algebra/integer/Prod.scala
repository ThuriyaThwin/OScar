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

package oscar.modeling.algebra.integer

import oscar.modeling.algebra.Expression

/**
  * Sum of an array of expression
  */
case class Prod(v: Array[IntExpression]) extends IntExpression {
  override def evaluate(): Int = v.foldLeft(1)((acc: Int, e: IntExpression) => acc * e.evaluate())
  override def min: Int = v.foldLeft(1)((acc: Int, e: IntExpression) => acc * e.min)
  override def max: Int = v.foldLeft(1)((acc: Int, e: IntExpression) => acc * e.max)
  override def values(): Iterable[Int] = Range(min, max+1)

  /**
    * Returns an iterable that contains all sub-expressions of this expression
    */
  override def subexpressions(): Iterable[IntExpression] = v

  /**
    * Apply a function on all sub-expressions of this expression and returns a new expression of the same type.
    * This function should return a value that is of the class as the object that was given to it.
    */
  override def mapSubexpressions(func: (Expression) => Expression): IntExpression = new Prod(v.map(func).asInstanceOf[Array[IntExpression]])

  /**
    * True if the variable is bound
    */
  override def isBound: Boolean = subexpressions().forall(_.isBound)
}

object Prod {
  def apply(a: IntExpression*): Prod = Prod(a.toArray)

  def apply(v: Iterable[IntExpression]): Prod = Prod(v.toArray)

  def apply[A](indices: Iterable[A])(f: A => IntExpression): Prod = Prod(indices map f)

  def apply[A, B](indices1: Iterable[A], indices2: Iterable[B])(f: (A, B) => IntExpression): Prod = Prod(for (i <- indices1; j <- indices2) yield f(i, j))

  def apply(n1: Int, n2: Int)(f: (Int, Int) => IntExpression): Prod = Prod(0 until n1, 0 until n2)(f)
}