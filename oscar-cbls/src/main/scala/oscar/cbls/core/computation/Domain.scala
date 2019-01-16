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
/*******************************************************************************
  * Contributors:
  *     This code has been initially developed by
  *         by Jean Noël Monette, Gustav Björdal
  ******************************************************************************/
package oscar.cbls.core.computation

import scala.collection.immutable.{NumericRange, SortedSet}
import scala.language.implicitConversions
import scala.util.Random

//TODO: remplacer çà par Option(Long,Long)

object Domain{

  def empty:Domain = Domain(0L to 0L)  //TODO: improve!

  implicit def rangeToDomain(r:Range):Domain = {
    DomainRange(r.head,r.last)
  }

  implicit def setToDomain(s:Set[Long]):Domain = {
    DomainSet(s)
  }

  implicit def coupleToDomain(i:(Long,Long)):Domain = {
    if(i._1 == i._2) SingleValueDomain(i._1)
    else DomainRange(i._1,i._2)
  }

  implicit def intToDomain(i:Long) = SingleValueDomain(i)

  def apply(v:Iterable[Long]):Domain =
    v match{
      case r:Range => r
      case s:SortedSet[Long] => (s.firstKey, s.lastKey)
    }
}

sealed abstract class Domain{
  def min: Long
  def max: Long
  def size: Long
  def contains(v:Long): Boolean
  //  def intersect(d:Domain):Domain
  def values:Iterable[Long]
  def randomValue():Long
  def restrict(d:Domain):Domain = intersect(d)
  def intersect(d:Domain):Domain

  def union(d:Domain):Domain

  def iterator: Iterator[Long] = values.iterator

  def isEmpty: Boolean = size == 0L
}


/**this is an inclusive domain*/
case class DomainRange(override val min: Long, override val max: Long) extends Domain {
  if (min > max) throw new EmptyDomainException
  def contains(v:Long): Boolean = min <= v && max >= v
  override def size: Long =
    if(min + Long.MaxValue <= max) Long.MaxValue
    else if(max==Long.MaxValue && min==Long.MinValue) Long.MaxValue
    else math.max(max-min+1L,0L)
  override def values: Iterable[Long] = min to max
  override def randomValue(): Long = (min to max)(Random.nextInt(max-min+1L))
  override def intersect(d: Domain): Domain = {
    val newDomain:Domain = d match{
      case r:DomainRange => math.max(r.min,min) to math.min(r.max,max)
      case FullRange => this
      case d:SingleValueDomain => d.intersect(this)
      case s:DomainSet =>  s.intersect(this)
    }
    if (newDomain.isEmpty) throw new EmptyDomainException
    newDomain
  }

  override def union(d: Domain): Domain = {
    val newDomain:Domain = d match{
      case r:DomainRange =>
          math.min(r.min,min) to math.max(r.max,max)
      case FullRange => FullRange
      case SingleValueDomain(v) =>
        if(v < min) v to max
        else if (max < v) min to v
        else this
      case d:DomainSet =>  d.union(this)
    }
    if (newDomain.isEmpty)
      throw new EmptyDomainException
    newDomain
  }

  def toRange:NumericRange[Long] = min to max

  override def toString(): String = "DomainRange(min:" + min + ", max:" +  max + ")"
}

case class DomainSet(val s:Set[Long]) extends Domain {
  override def min: Long = s.min
  override def max: Long = s.max
  override def size: Long = s.size
  if (min > max) throw new EmptyDomainException

  def contains(v:Long): Boolean = s.contains(v)
  override def values: Iterable[Long] = s
  override def randomValue(): Long = s.toList.apply(Random.nextInt(size))
  override def intersect(d: Domain): Domain = {
    val newDomain:Domain = d match{
      case r:DomainRange =>
        (r.toRange.toSet) intersect s
      case FullRange => this
      case d:SingleValueDomain => d.intersect(this)
      case ds:DomainSet =>  ds.s intersect s
    }
    if (newDomain.isEmpty) throw new EmptyDomainException
    newDomain
  }

  override def union(d: Domain): Domain = {
    val newDomain:Domain = d match{
      case r:DomainRange => r.toRange.toSet union s
      case FullRange => FullRange
      case SingleValueDomain(v) => if(contains(v)){
        this
      }else{
        Set(v) union s
      }
      case d:DomainSet =>  d.s union s
    }
    if (newDomain.isEmpty) throw new EmptyDomainException
    newDomain
  }

  override def toString(): String = "DomainSet(" + s.mkString(", ") + ")"
}

case object FullRange extends Domain{
  override def min: Long = Long.MinValue
  override def max: Long = Long.MaxValue
  override def size: Long = Long.MaxValue
  override def randomValue(): Long = Random.nextInt()
  override def contains(v: Long): Boolean = true
  override def values: Iterable[Long] =  min to max
  override def intersect(d: Domain): Domain = d
  override def union(d: Domain): Domain = this
  override def toString(): String = "FullRange"
}

object PositiveOrNullRange extends DomainRange(0L, Long.MaxValue)


case class SingleValueDomain(value:Long) extends Domain{
  override def min: Long = value
  override def max: Long = value
  override def size: Long = 1
  override def contains(v: Long): Boolean = v == value

  override def randomValue(): Long = value

  override def intersect(d: Domain): Domain =
    if (d.contains(value)) this else throw new EmptyDomainException

  override def union(d: Domain): Domain = {
    d match {
      case SingleValueDomain(v) =>
        if(v == value) this
        else if(math.abs(v-value) == 1L) math.min(v,value) to math.max(v,value)
        else Set(v) union Set(value)
      case _ => d.union(this)
    }
  }
  override def values: Iterable[Long] = List(value)

  override def toString(): String = "SingleValueDomain(" + value + ")"
}

class EmptyDomainException extends Exception("domain is empty")

object DomainHelper{

  def safeAddMax(a:Long,b:Long):Long = {
    val tmp = a.toLong + b.toLong
    if(tmp > Long.MaxValue) Long.MaxValue
    else tmp.toInt
  }

  def safeAddMin(a:Long,b:Long):Long = {
    val tmp = a.toLong + b.toLong
    if(tmp < Long.MinValue) Long.MinValue
    else tmp.toInt
  }

  def safeMulMax(a:Long,b:Long):Long = {
    val tmp = a.toLong * b.toLong
    if(tmp > Long.MaxValue) Long.MaxValue
    else tmp.toInt
  }

  def safeMulMin(a:Long,b:Long):Long = {
    val tmp = a.toLong * b.toLong
    if(tmp < Long.MinValue) Long.MaxValue
    else tmp.toInt
  }
}