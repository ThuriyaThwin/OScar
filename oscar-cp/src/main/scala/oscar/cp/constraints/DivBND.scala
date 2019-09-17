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

package oscar.cp.constraints

import oscar.algo.reversible.ReversibleInt
import oscar.cp.core.variables.{CPIntVar, CPVar}
import oscar.cp.core.{CPPropagStrength, Constraint}

/**
  * @author Gustav Bjordal
  */
class DivBND(x:CPIntVar, y:Int, z:CPIntVar) extends Constraint(x.store, "Writes") {

  // If y is negative then negate z instead.
  val _x = x
  val _y = if(y < 0) -y else y
  val _z = if(y < 0) -z else z
  
  override def associatedVars(): Iterable[CPVar] = Array(x,z,_z)
  
  var supportOffset:Int = _
  var supportZ:Array[ReversibleInt] = _
  
  override def setup(l: CPPropagStrength): Unit = {
    val xUB = (_z.max+1)*_y -1
    val XLB = _y*_z.min
    _x.updateMin(XLB)
    _x.updateMax(xUB)
    
    val zUB = _x.max/_y
    val zLB = _x.min/_y
    _z.updateMax(zUB)
    _z.updateMin(zLB)
    
    supportOffset = _z.min
    supportZ = Array.tabulate(_z.max-_z.min+1)(i => {
      if((i + supportOffset) < 0 ){
        val range = -(i + supportOffset) * _y until (-(i + supportOffset) + 1) * _y
        ReversibleInt(range.map(j => if (_x.hasValue(-j)) 1 else 0).sum)(s)
      }else if (i+supportOffset == 0){
        val range = -_y+1 until _y
        ReversibleInt(range.map(j => if (_x.hasValue(j)) 1 else 0).sum)(s)
      }else {
        val range = (i + supportOffset) * _y until (i + supportOffset + 1) * _y
        ReversibleInt(range.map(j => if (_x.hasValue(j)) 1 else 0).sum)(s)
      }
    })
    for(i <- supportZ.indices){
      if(supportZ(i).getValue() == 0){
        _z.removeValue(i+supportOffset)
      }
    }
    for( i <- _z.min to _z.max if !_z.hasValue(i)) {
      valRemove(_z, i)
    }
    _x.callValRemoveWhenValueIsRemoved(this)
    _z.callValRemoveWhenValueIsRemoved(this)
    _x.callValBindWhenBind(this)
  }
  
  override def valRemove(v: CPIntVar, value: Int): Unit = {
    if( v == _x){
      supportZ((value/_y)-supportOffset).decr()
      if(supportZ((value/_y)-supportOffset).getValue() == 0)
        _z.removeValue(value/_y)
    }else{
      val range = Math.abs(value)* _y until (Math.abs(value)+ 1) * _y
      if(value < 0) {
        range foreach( i=> _x.removeValue(-i))
      }else if(value == 0){
        -Math.abs(_y)+1 until Math.abs(_y) foreach _x.removeValue
      }else{
        range foreach _x.removeValue
      }
    }
  }
  
  override def valBind(x: CPIntVar): Unit = {
    _z.assign(_x.min/_y)
  }
}
