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

package oscar.modeling.experiences

import oscar.modeling.constraints.AllDifferent
import oscar.modeling.misc.CartesianProduct
import oscar.modeling.models.UninstantiatedModel
import oscar.modeling.solvers.cp.decompositions._
import oscar.modeling.solvers.cp.{Branchings, CPApp, CPAppConfig}
import oscar.modeling.vars.IntVar

object ExperienceDecomp extends CPApp[String] with App {
  def increasing(y: Array[IntVar]) = {
    for (i <- 1 until y.length) {
      post(y(i - 1) < y(i))
    }
  }

  var n = 13

  val m = Array.fill(n)(IntVar(0,(1 << (n - 1))-1))

  post(m(0) === 0)

  increasing(m)

  // Number of marks and differences
  val n_d = (n*n-n)/2

  // Array of differences
  val d = Array.ofDim[IntVar](n_d)

  var k = 0
  for(i <- 0 until n-1) {
    for(j <- i+1 until n) {
      d(k) = (m(j)-m(i)).reify()
      post(d(k) >= ((j-i)*(j-i+1)/2))
      k += 1
    }
  }

  post(AllDifferent(d))

  if (n > 2)
    post(d(0) < d(n_d-1))

  minimize(m(n - 1))

  post(m(n-1) < n*n)

  val decompositions = Array[(String, DecompositionStrategy)](
    //("Depth - ID - nary", new DepthIterativeDeepening(Branching.naryStatic(m))),
    //("Depth - R - nary", new DepthRefinement(Branching.naryStatic(m))),
    ("Depth - ID - binary", new DepthIterativeDeepening(Branchings.binaryStatic(m))),
    ("Depth - R - binary", new DepthRefinement(Branchings.binaryStatic(m)))//,
    //("CartProd - ID - nary", new CartProdIterativeDeepening(m.toList, Branching.naryStatic(m))),
    //("CartProd - R - nary", new CartProdRefinement(m, Branching.naryStatic(m))),
    //("CartProd - ID - binary", new CartProdIterativeDeepening(m.toList, Branching.binaryStatic(m))),
    //("CartProd - R - binary", new CartProdRefinement(m, Branching.binaryStatic(m)))
  )

  decompositions(0)._2.decompose(this.md.getCurrentModel.asInstanceOf[UninstantiatedModel], 500) //start JVM properly

  for((name, decompose) <- decompositions) {
    println("--------------")
    println(name)
    println("--------------")
    var last = 0
    for(count <- 1000 to 63000 by 1000) {
      if(last < count) {
        val s = System.currentTimeMillis()
        for(i <- 0 until 5)
          last = decompose.decompose(this.md.getCurrentModel.asInstanceOf[UninstantiatedModel], count).length
        val e = System.currentTimeMillis()
        println(last.toString+"\t"+((e-s)/5).toString)
      }
    }
    println("")
    println("")
  }
}