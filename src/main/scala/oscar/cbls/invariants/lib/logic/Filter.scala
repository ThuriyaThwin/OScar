/*******************************************************************************
 * This file is part of OscaR (Scala in OR).
 *  
 * OscaR is free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation, either version 2.1 of the License, or
 * (at your option) any later version.
 * 
 * OscaR is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 * 
 * You should have received a copy of the GNU General Public License along with OscaR.
 * If not, see http://www.gnu.org/licenses/gpl-3.0.html
 ******************************************************************************/
 ******************************************************************************/
/*
 * Copyright CETIC 2012 www.cetic.be
 *
 * This file is part of Asteroid.
 *
 * Asteroid is free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation, either version 2.1 of the License, or
 * (at your option) any later version.
 *
 * Asteroid is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with Asteroid.
 * If not, see http://www.gnu.org/licenses/lgpl-2.1-standalone.html
 *
 * Contributors:
 *     This code has been initially developed by CETIC www.cetic.be
 *         by Renaud De Landtsheer
 */

package oscar.cbls.invariants.lib.logic
/**This package proposes a set of logic invariants, which are used to define the structure of the problem*/


import collection.immutable.SortedSet
import oscar.cbls.invariants.core.computation._

/** { i in index(values) | cond(values[i] }
 * @param values is an array of IntVar
 * @param cond is a function that selects values to be includes in the output set.
 * This ''cond'' function cannot depend on any IntVar, as updates to these IntVars will not trigger propagation of this invariant.
 */
case class Filter(var values:Array[IntVar], cond:(Int=>Boolean)) extends IntSetInvariant {
  var output:IntSetVar=null

  for (v <- values.indices) registerStaticAndDynamicDependency(values(v),v)
  finishInitialization()

  def MyMin = values.indices.start
  def MyMax = values.indices.end

  override def setOutputVar(v:IntSetVar){
    output = v
    output.setDefiningInvariant(this)
    output := values.indices.foldLeft(SortedSet.empty[Int])((acc:SortedSet[Int],indice:Int) => if(cond(values(indice))){acc+indice}else{acc})
  }

  @inline
  override def notifyIntChanged(v:IntVar,index:Int, OldVal:Int,NewVal:Int){
    val OldCond = cond(OldVal)
    val NewCond = cond(NewVal)
    if(OldCond  && !NewCond) output.deleteValue(index)
    else if(NewCond && !OldCond) output.insertValue(index)
  }

  override def checkInternals(){
    for(i <- values.indices){
      assert(!cond(values(i).getValue()) ||output.getValue().contains(i))
      assert(cond(values(i).getValue()) || !output.getValue().contains(i))
    }
  }
}
