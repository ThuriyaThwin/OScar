package oscar.cbls.test.search

import oscar.cbls.core.computation.{CBLSIntVar, Domain, FullRange}
import oscar.cbls.core.objective.Objective
import oscar.cbls.lib.invariant.logic.IntInt2Int
import oscar.cbls.lib.search.combinators.GuidedLocalSearch3
import oscar.cbls.lib.search.neighborhoods.{GradientDescent, NarrowingStepSlide}
import oscar.cbls.{IntValue, Store}

object TestGLS extends App{

  val m = new Store()

  val x = CBLSIntVar(m,10,Domain(0,1000),"x")
  val y = new CBLSIntVar(m,10,Domain(0,1000),"y")

  val f:IntValue = new IntInt2Int(x,y,{case (x,y) => (x - 300)^2 + (y - 100)^2},FullRange)

  val obj1 = Objective(f)

  //trigo are in radiant
  val g:IntValue = new IntInt2Int(x,y,{case (x,y) => math.abs(100*math.sin(x /10) + 50*math.sin(y /10)).floor.toInt},Domain(0,150))

  val obj2 = Objective(f)

  m.close()
  printModel()

  def printModel(): Unit ={
    println(x)
    println(y)
    println("f:" + f)
  }


/*  class GuidedLocalSearch3(a: Neighborhood,
                           additionalConstraint:Objective,
                           weightCorrectionStrategy:WeightCorrectionStrategy,
                           maxAttemptsBeforeStop:Int = 10
                          ) */

    val search = new GuidedLocalSearch3(
    GradientDescent(Array(x,y),
    selectVars = 0L to 1L,
    variableIndiceToDeltaForGradientDefinition = _ => 10L,
    linearSearch = new NarrowingStepSlide(3L, minStep = 1L),
    trySubgradient = true),
      obj2,
      GuidedLocalSearch3.progressive(10,10,40,10,10)
    )


  search.verbose = 2

  search.doAllMoves(obj = obj1)

  printModel()
}
