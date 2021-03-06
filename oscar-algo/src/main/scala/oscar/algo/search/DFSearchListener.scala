package oscar.algo.search

/**
  * Created by saschavancauwelaert on 23/02/16.
  */
trait DFSearchListener {

  // called on Push events
  def onPush(node : DFSearchNode) : Unit
  // called on Pop events
  def onPop(node : DFSearchNode) : Unit
  // called on branching
  def onBranch(alternative : Alternative) : Unit
  /*//called when a failure occurs
  def performFailureActions(): Unit
  //called when a solution is found
  def performSolutionActions(): Unit*/

}

class DefaultDFSearchListener extends DFSearchListener {

  // Actions to execute in case of solution node
  private[this] var solutionActions : List[() => Unit] = null
  // Actions to execute in case of failed node
  private[this] var failureActions : List[() => Unit] = null

  def onPush(node : DFSearchNode) : Unit = ()
  def onPop(node : DFSearchNode) : Unit = ()
  def onBranch(alternative : Alternative) : Unit = ()

  /** Adds an action to execute when a failed node is found */
  final def onFailure(action: => Unit): Unit = failureActions = (() => action) :: failureActions

  /** Adds an action to execute when a solution node is found */
  final def onSolution(action: => Unit): Unit = solutionActions = (() => action) :: solutionActions

  /** Clear all actions executed when a solution node is found */
  final def clearOnSolution(): Unit = solutionActions = Nil

  /** Clear all actions executed when a failed node is found */
  final def clearOnFailure(): Unit = failureActions = Nil

  final def performSolutionActions() = {
    solutionActions.foreach(_())
  }

  final def performFailureActions() = {
    failureActions.foreach(_())
  }

}