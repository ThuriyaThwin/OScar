package oscar.cp.constraints

import oscar.algo.SortUtils._
import oscar.algo.reversible.ReversibleInt
import oscar.cp._
import oscar.cp.core.variables.CPIntVar
import oscar.cp.core.{CPOutcome, CPPropagStrength, Constraint}
import oscar.cp.scheduling.util.{TransitionLowerBounds, ThetaLambdaTreeWithTransitionTimes}

import scala.collection.mutable

/**
 * Created on 21/01/15.
 * @author Cyrille Dejemeppe (cyrille.dejemeppe@gmail.com)
 * @author Sascha Van Cauwelaert (sascha.vancauwelaert@gmail.com)
 */
class UnaryResourceWithTransitionTimes(starts: Array[CPIntVar], durations: Array[CPIntVar], ends: Array[CPIntVar], ttMatrix: Array[Array[Int]]) extends Constraint(starts(0).store) {
  idempotent = true

  private[this] val nTasks = starts.length
  private[this] val ttMatrixTransposed = Array.tabulate(nTasks)(i => Array.tabulate(nTasks)(j => ttMatrix(j)(i)))
  private[this] val minTransitionTimeFromActivity = Array.tabulate(nTasks)(i => ttMatrix(i).sorted.apply(1))
  private[this] val minTransitionTimeToActivity = Array.tabulate(nTasks)(i => ttMatrixTransposed(i).sorted.apply(1))
  private[this] val transitionSetLowerBounds = new TransitionLowerBounds(ttMatrix).getLowerBounds()
  private[this] val thetaLambdaTree = new ThetaLambdaTreeWithTransitionTimes(nTasks, transitionSetLowerBounds)
  private[this] val thetaLambdaTreeMirror = new ThetaLambdaTreeWithTransitionTimes(nTasks, transitionSetLowerBounds)

  private[this] val indexByIncreasingMinStarts: Array[Int] = Array.tabulate(nTasks)(i => i)
  private[this] val indexByIncreasingMaxStarts: Array[Int] = Array.tabulate(nTasks)(i => i)
  private[this] val indexByIncreasingMinEnds: Array[Int] = Array.tabulate(nTasks)(i => i)
  private[this] val indexByIncreasingMaxEnds: Array[Int] = Array.tabulate(nTasks)(i => i)
  private[this] val indexByIncreasingMinStartMirror: Array[Int] = Array.tabulate(nTasks)(i => i)
  private[this] val indexByIncreasingMaxStartMirror: Array[Int] = Array.tabulate(nTasks)(i => i)
  private[this] val indexByIncreasingMinEndMirror: Array[Int] = Array.tabulate(nTasks)(i => i)
  private[this] val indexByIncreasingMaxEndMirror: Array[Int] = Array.tabulate(nTasks)(i => i)

  private[this] val startsMirror = ends map {-_}
  private[this] val endsMirror = starts map {-_}

  private[this] val currentMinStarts: Array[Int] = Array.ofDim[Int](nTasks)
  private[this] val currentMaxEnds: Array[Int] = Array.ofDim[Int](nTasks)
  private[this] val currentMinEnds: Array[Int] = Array.ofDim[Int](nTasks)
  private[this] val currentMaxStarts: Array[Int] = Array.ofDim[Int](nTasks)
  private[this] val currentMinStartsMirror: Array[Int] = Array.ofDim[Int](nTasks)
  private[this] val currentMaxEndsMirror: Array[Int] = Array.ofDim[Int](nTasks)
  private[this] val currentMinEndsMirror: Array[Int] = Array.ofDim[Int](nTasks)
  private[this] val currentMaxStartsMirror: Array[Int] = Array.ofDim[Int](nTasks)
  private[this] val currentMinDurations: Array[Int] = Array.ofDim[Int](nTasks)

  private[this] val newMinStarts: Array[Int] = Array.ofDim[Int](nTasks)
  private[this] val newMaxEnds: Array[Int] = Array.ofDim[Int](nTasks)
  private[this] val newMinStartsMirror: Array[Int] = Array.ofDim[Int](nTasks)
  private[this] val newMaxEndsMirror: Array[Int] = Array.ofDim[Int](nTasks)

  private[this] val formerMinEnds : Array[ReversibleInt] = Array.fill(nTasks)(new ReversibleInt(starts(0).store,Int.MaxValue))
  private[this] val formerMaxStarts : Array[ReversibleInt] = Array.fill(nTasks)(new ReversibleInt(starts(0).store,Int.MinValue))

  private[this] val boundChangedActivityIds: mutable.BitSet = new mutable.BitSet()

  //array to map a value to its index (tree insertion order mapped to est order)
  //private[this] val indexOfInOrderedEstsIds = Array.fill(nTasks)(-1)

  private[this] var failure = false
  private[this] var changed = true



  override def setup(l: CPPropagStrength): CPOutcome = {
    for (i <- 0 until nTasks) {
      starts(i).callPropagateWhenBoundsChange(this)
      ends(i).callPropagateWhenBoundsChange(this)
    }

    propagate()
  }

  //TODO : USE A SPARSE SET INSTEAD OF HASHSET
  override def propagate(): CPOutcome = {

    failure = false
    changed = true

    boundChangedActivityIds.clear()

    var i = 0
    while(i < nTasks) {
      currentMinDurations(i) = durations(i).min
      currentMinStarts(i) = starts(i).min
      currentMaxEnds(i) = ends(i).max
      currentMinEnds(i) = ends(i).min
      currentMaxStarts(i) = starts(i).max
      currentMinStartsMirror(i) = -currentMaxEnds(i)
      currentMaxEndsMirror(i) = -currentMinStarts(i)
      currentMinEndsMirror(i) = -currentMaxStarts(i)
      currentMaxStartsMirror(i) = -currentMinEnds(i)
      newMinStarts(i) = currentMinStarts(i)
      newMaxEnds(i) = currentMaxEnds(i)
      newMinStartsMirror(i) = currentMinStartsMirror(i)
      newMaxEndsMirror(i) = currentMaxEndsMirror(i)

      if(formerMinEnds(i).value != currentMinEnds(i) || formerMaxStarts(i).value != currentMaxStarts(i)) {
        boundChangedActivityIds += i
      }

      i += 1
    }

    while(!failure && changed) {
      changed = EF() || OC() || DP() || NFNL() || binaryPropagate()
    }

    if(failure)
      CPOutcome.Failure
    else {
      i = 0
      while(i < nTasks) {
        formerMinEnds(i).setValue(currentMinEnds(i))
        formerMaxStarts(i).setValue(currentMaxStarts(i))
        i += 1
      }
      CPOutcome.Suspend
    }

  }

  @inline
  private def OC(): Boolean = overloadChecking(currentMinStarts, currentMaxEnds, thetaLambdaTree, indexByIncreasingMinStarts, indexByIncreasingMaxEnds) || overloadChecking(currentMinStartsMirror, currentMaxEndsMirror, thetaLambdaTreeMirror, indexByIncreasingMinStartMirror, indexByIncreasingMaxEndMirror)


  /**
   * returns true if some domain is changed (here failure), false otherwise
   */
  @inline
  private def overloadChecking(startMins : Array[Int], endMaxs : Array[Int], tree : ThetaLambdaTreeWithTransitionTimes, orderedMinStartIds : Array[Int], orderedMaxEndIds : Array[Int]): Boolean = {
    // Clearing the tree
    mergeSort(orderedMinStartIds, startMins)
    tree.clearAndPlaceLeaves(orderedMinStartIds, startMins, currentMinDurations)

    //sorting activities in non-decreasing lct
    mergeSort(orderedMaxEndIds, endMaxs)

    var i = 0
    while (i < nTasks) {
      tree.insert(orderedMaxEndIds(i))
      if(tree.ect > endMaxs(orderedMaxEndIds(i))) {
        failure = true
        return true
      }
      i += 1
    }

    false
  }

  @inline
  private def DP(): Boolean = {
    detectablePrecedences(currentMinStarts, currentMaxStarts, currentMinEnds,
      currentMaxStartsMirror, currentMaxEndsMirror, newMinStarts, newMaxEndsMirror,
      starts, ends, thetaLambdaTree,
      indexByIncreasingMinStarts, indexByIncreasingMaxStarts, indexByIncreasingMinEnds, minTransitionTimeToActivity) ||
      detectablePrecedences(currentMinStartsMirror, currentMaxStartsMirror, currentMinEndsMirror,
        currentMaxStarts, currentMaxEnds, newMinStartsMirror, newMaxEnds,
        startsMirror, endsMirror, thetaLambdaTreeMirror,
        indexByIncreasingMinStartMirror, indexByIncreasingMaxStartMirror, indexByIncreasingMinEndMirror, minTransitionTimeFromActivity)
  }

  /**
   * returns true if some domain is changed (here failure), false otherwise
   */
  @inline
  private def detectablePrecedences(startMins : Array[Int], startMaxs: Array[Int], endMins : Array[Int],
                                    startMaxsMirror : Array[Int], endMaxsMirror : Array[Int], updatedMinStarts : Array[Int], updatedMaxEndsMirror : Array[Int],
                                    startVars : Array[_ <: CPIntVar], endVars : Array[_ <: CPIntVar], tree : ThetaLambdaTreeWithTransitionTimes,
                                    orderedMinStartIds : Array[Int], orderedMaxStartIds: Array[Int], orderedMinEndIds : Array[Int], minTransitionToActivity: Array[Int]): Boolean = {
    // Clearing the tree
    mergeSort(orderedMinStartIds, startMins)
    tree.clearAndPlaceLeaves(orderedMinStartIds, startMins, currentMinDurations)

    //sorting activities in non-decreasing lst
    mergeSort(orderedMaxStartIds, startMaxs)

    //sorting activities in non-decreasing ect
    mergeSort(orderedMinEndIds, endMins)

    var i, q = 0
    while (i < nTasks) {
      val ectIndex = orderedMinEndIds(i)
      while (q < nTasks && endMins(ectIndex) > startMaxs(orderedMaxStartIds(q))) {
        tree.insert(orderedMaxStartIds(q))
        q += 1
      }
      updatedMinStarts(ectIndex) = math.max(updatedMinStarts(ectIndex), tree.ectWithoutActivity(ectIndex) + minTransitionToActivity(ectIndex))
      i += 1
    }

    updateMins(startMins,endMins,startMaxsMirror,endMaxsMirror, updatedMinStarts, updatedMaxEndsMirror, startVars, endVars)
  }

  @inline
  private def NFNL(): Boolean = {
    notLast(currentMinStarts, currentMaxStarts, currentMaxEnds,
      currentMinStartsMirror, currentMinEndsMirror, newMaxEnds, newMinStartsMirror,
      starts, ends, thetaLambdaTree,
      indexByIncreasingMinStarts, indexByIncreasingMaxStarts, indexByIncreasingMaxEnds, minTransitionTimeFromActivity) ||
      notLast(currentMinStartsMirror, currentMaxStartsMirror, currentMaxEndsMirror,
        currentMinStarts, currentMinEnds, newMaxEndsMirror, newMinStarts,
        startsMirror, endsMirror, thetaLambdaTreeMirror,
        indexByIncreasingMinStartMirror, indexByIncreasingMaxStartMirror, indexByIncreasingMaxEndMirror, minTransitionTimeToActivity)
  }

  /**
   * returns true if some domain is changed (here failure), false otherwise
   */
  @inline
  private def notLast(startMins : Array[Int], startMaxs : Array[Int], endMaxs : Array[Int],
                      startMinsMirror : Array[Int], endMinsMirror : Array[Int], updatedMaxEnds : Array[Int], updatedMinStartsMirror : Array[Int],
                      startVars : Array[_ <: CPIntVar], endVars : Array[_ <: CPIntVar], tree : ThetaLambdaTreeWithTransitionTimes,
                      orderedMinStartIds : Array[Int], orderedMaxStartIds: Array[Int], orderedMaxEndIds : Array[Int], minTransitionFromActivity : Array[Int]) : Boolean = {
    // Clearing the tree
    mergeSort(orderedMinStartIds, startMins)
    tree.clearAndPlaceLeaves(orderedMinStartIds, startMins, currentMinDurations)

    //sorting activities in non-decreasing lst
    mergeSort(orderedMaxStartIds, startMaxs)

    //sorting activities in non-decreasing lct
    mergeSort(orderedMaxEndIds, endMaxs)

    var i, j = 0
    while(i < nTasks) {
      val lctIndex = orderedMaxEndIds(i)
      while(j < nTasks && endMaxs(lctIndex) > startMaxs(orderedMaxStartIds(j))) {
        if(tree.ect > startMaxs(orderedMaxStartIds(j))) {
          updatedMaxEnds(orderedMaxStartIds(j)) = startMaxs(orderedMaxStartIds(j - 1))
        }
        tree.insert(orderedMaxStartIds(j))
        j += 1
      }

      if(tree.ectWithoutActivity(lctIndex) > startMaxs(lctIndex)) {
        updatedMaxEnds(lctIndex) = math.min(startMaxs(orderedMaxStartIds(j - 1)) - minTransitionFromActivity(lctIndex) ,updatedMaxEnds(lctIndex))
      }

      i += 1
    }

    updateMaxs(startMaxs, endMaxs, startMinsMirror, endMinsMirror, updatedMaxEnds, updatedMinStartsMirror, startVars, endVars)

  }

  @inline
  private def EF() : Boolean = {
    edgeFinding(currentMinStarts, currentMaxEnds, currentMinEnds,
      currentMaxStartsMirror,currentMaxEndsMirror, newMinStarts, newMaxEndsMirror,
      starts, ends, thetaLambdaTree,
      indexByIncreasingMinStarts, indexByIncreasingMaxEnds, minTransitionTimeToActivity) ||
      edgeFinding(currentMinStartsMirror, currentMaxEndsMirror, currentMinEndsMirror,
        currentMaxStarts, currentMaxEnds, newMinStartsMirror, newMaxEnds,
        startsMirror,endsMirror, thetaLambdaTreeMirror,
        indexByIncreasingMinStartMirror, indexByIncreasingMaxEndMirror, minTransitionTimeFromActivity)
  }

  /**
   * returns true if some domain is changed (here failure), false otherwise
   */
  @inline
  private def edgeFinding(startMins : Array[Int], endMaxs : Array[Int], endMins : Array[Int],
                          startMaxsMirror : Array[Int], endMaxsMirror : Array[Int], updatedMinStarts : Array[Int], updatedMaxEndsMirror : Array[Int],
                          startVars : Array[_ <: CPIntVar], endVars : Array[_ <: CPIntVar], tree : ThetaLambdaTreeWithTransitionTimes,
                          orderedMinStartIds : Array[Int], orderedMaxEndIds : Array[Int], minTransitionToActivity: Array[Int]) : Boolean = {
    // Inserting all activities in the tree
    mergeSort(orderedMinStartIds, startMins)
    tree.fillAndPlaceLeaves(orderedMinStartIds, startMins, currentMinDurations) // true as we use gray nodes

    //sorting activities in non-decreasing lct
    //NOTE: we sort the array by increasing lct, we just will browse it from left to right
    mergeSort(orderedMaxEndIds, endMaxs)

    var estIndex = 0
    var j = nTasks - 1
    while (j > 0) {
      if(tree.ect > endMaxs(orderedMaxEndIds(j))) {
        failure = true
        return true
      }

      tree.grayActivity(orderedMaxEndIds(j))

      j -= 1
      while(tree.ectBar > endMaxs(orderedMaxEndIds(j))) {
        if (tree.responsibleEctBar < 0) {
          failure = true
          return true
        }
        estIndex = orderedMinStartIds(tree.responsibleEctBar)
        updatedMinStarts(estIndex) = math.max(updatedMinStarts(estIndex), tree.ect + minTransitionToActivity(estIndex))
        tree.remove(estIndex)
      }
    }

    updateMins(startMins, endMins, startMaxsMirror, endMaxsMirror, updatedMinStarts, updatedMaxEndsMirror, startVars, endVars)
  }



  /**
   * returns true if some domain is changed, false otherwise
   */
  @inline
  private def binaryPropagate(): Boolean = {
    var i, j = 0
    var domainModified = false
    while (!failure && boundChangedActivityIds.nonEmpty) {
      while (boundChangedActivityIds.nonEmpty) {
        i = boundChangedActivityIds.head
        j = 0
        while (j < nTasks) {
          if (j != i) {
            // activity i is after activity j
            if (currentMinEnds(i) + ttMatrix(i)(j) > currentMaxStarts(j)) {
              //activity i is not after j nor before => failure
              if (currentMinEnds(j) + ttMatrix(j)(i) > currentMaxStarts(i)) {
                failure = true
                return true
              }
              else {
                newMinStarts(i) = math.max(currentMinEnds(j) + ttMatrix(j)(i), newMinStarts(i))
                newMaxEnds(j) = math.min(currentMaxStarts(i) - ttMatrix(j)(i), newMaxEnds(j))
              }
            }
            // activity j is after activity i
            else {
              if (currentMinEnds(j) + ttMatrix(j)(i) > currentMaxStarts(i)) {
                newMinStarts(j) = math.max(currentMinEnds(i) + ttMatrix(i)(j), newMinStarts(j))
                newMaxEnds(i) = math.min(currentMaxStarts(j) - ttMatrix(i)(j), newMaxEnds(i))
              }
            }
          }
          j += 1
        }
        boundChangedActivityIds.remove(i)
      }
      if (updateBounds())
        domainModified = true
    }
    domainModified
  }


  /**
   * returns true if some domain is changed, false otherwise
   */
  @inline
  private def updateBounds(): Boolean = {
    var domainModified = false
    var i = 0
    while (i < nTasks) {
      if (newMinStarts(i) > currentMinStarts(i)) {
        if (starts(i).updateMin(newMinStarts(i)) == CPOutcome.Failure || ends(i).updateMin(newMinStarts(i) + currentMinDurations(i)) == CPOutcome.Failure) {
          failure = true
          return true
        }
        else {
          domainModified = true
          boundChangedActivityIds += i
          currentMinStarts(i) = newMinStarts(i)
          currentMinEnds(i) = currentMinStarts(i) + currentMinDurations(i)
          currentMaxEndsMirror(i) = -currentMinStarts(i)
          currentMaxStartsMirror(i) = -currentMinEnds(i)
          newMaxEndsMirror(i) = - newMinStarts(i)
        }
      }
      if (newMaxEnds(i) < currentMaxEnds(i)) {
        if (ends(i).updateMax(newMaxEnds(i)) == CPOutcome.Failure || starts(i).updateMax(newMaxEnds(i) - currentMinDurations(i)) == CPOutcome.Failure) {
          failure = true
          return true
        }
        else {
          domainModified = true
          boundChangedActivityIds += i
          currentMaxEnds(i) = newMaxEnds(i)
          currentMaxStarts(i) = currentMaxEnds(i) - currentMinDurations(i)
          currentMinStartsMirror(i) = -currentMaxEnds(i)
          currentMinEndsMirror(i) = -currentMaxStarts(i)
          newMinStartsMirror(i) = - newMaxEnds(i)
        }
      }
      i += 1
    }
    domainModified
  }

  /**
   * returns true if some domain is changed, false otherwise
   */
  @inline
  private def updateMins(startMins : Array[Int], endMins : Array[Int], startMaxsMirror : Array[Int], endMaxsMirror : Array[Int], updatedMinStarts : Array[Int], updatedMaxEndsMirror : Array[Int], startVars : Array[_ <: CPIntVar], endVars : Array[_ <: CPIntVar]): Boolean = {
    var domainModified = false
    var i = 0
    while (i < nTasks) {
      if (updatedMinStarts(i) > startMins(i)) {
        if (startVars(i).updateMin(updatedMinStarts(i)) == CPOutcome.Failure || endVars(i).updateMin(updatedMinStarts(i) + currentMinDurations(i)) == CPOutcome.Failure) {
          failure = true
          return true
        }
        else {
          domainModified = true
          boundChangedActivityIds += i
          startMins(i) = updatedMinStarts(i)
          endMins(i) = startMins(i) + currentMinDurations(i)
          endMaxsMirror(i) = -startMins(i)
          startMaxsMirror(i) = -endMins(i)
          updatedMaxEndsMirror(i) = -updatedMinStarts(i)
        }
      }

      i += 1
    }
    domainModified
  }

  /**
   * returns true if some domain is changed, false otherwise
   */
  @inline
  private def updateMaxs(startMaxs : Array[Int], endMaxs : Array[Int], startMinsMirror : Array[Int], endMinsMirror : Array[Int], updatedMaxEnds : Array[Int], updatedMinStartsMirror : Array[Int], startVars : Array[_ <: CPIntVar], endVars : Array[_ <: CPIntVar]): Boolean = {
    var domainModified = false
    var i = 0
    while (i < nTasks) {
      if (updatedMaxEnds(i) < endMaxs(i)) {
        if (endVars(i).updateMax(updatedMaxEnds(i)) == CPOutcome.Failure || startVars(i).updateMax(updatedMaxEnds(i) - currentMinDurations(i)) == CPOutcome.Failure) {
          failure = true
          return true
        }
        else {
          domainModified = true
          boundChangedActivityIds += i
          endMaxs(i) = updatedMaxEnds(i)
          startMaxs(i) = endMaxs(i) - currentMinDurations(i)
          startMinsMirror(i) = -endMaxs(i)
          endMinsMirror(i) = -startMaxs(i)
          updatedMinStartsMirror(i) = -updatedMaxEnds(i)
        }
      }
      i += 1
    }
    domainModified
  }
}
