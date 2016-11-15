package oscar.algo.search

import oscar.algo.vars.{IntVarLike, SetVarLike}

/**
  * A trait to be mixed-in a DFSearchNode to make it accept to "branch", or to "constraint" on IntVarLike instances.
  */
trait SetConstrainableContext extends DFSearchNode {
  /**
    * Post v \in x
    */
  def requires(x: SetVarLike, v: Int): Outcome

  /**
    * Post v \notin x
    */
  def excludes(x: SetVarLike, v: Int): Outcome
}
