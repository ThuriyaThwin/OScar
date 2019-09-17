/** *****************************************************************************
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
  * *****************************************************************************/
/**
  * @author Leonard Debroux
  * @author Gustav Björdal
  * @author Jean-Noël Monette
  */
package oscar.flatzinc.model

import scala.collection.mutable.{Set => MSet}

class FZProblem {
  val variables: MSet[Variable] = MSet.empty[Variable]
  val constraints: MSet[Constraint] = MSet.empty[Constraint]
  val neighbourhoods: MSet[FZNeighbourhood] = MSet.empty[FZNeighbourhood]
  
  val solution: FZSolution = new FZSolution()
  val search = new Search()
  
  def addVariable(variable: Variable) {
    variables += variable
  }
  
  def addConstraint(c: Constraint) {
    constraints += c
  }
  
  def addNeighbourhood(n: FZNeighbourhood): Unit = {
    neighbourhoods += n
  }
  
  
  def addVariable(id: String, dom: FzDomain, bool: Boolean): Variable = {
    if (bool) {
      addBooleanVariable(id, dom)
    } else {
      addIntegerVariable(id, dom)
    }
  }
  
  def addIntegerVariable(id: String, dom: FzDomain): Variable = {
    val variable: Variable = IntegerVariable(id, dom)
    variables += variable
    variable
  }
  
  def addBooleanVariable(id: String, dom: FzDomain): Variable = {
    val variable: Variable = new BooleanVariable(id, dom)
    variables += variable
    variable
  }

  def getDefiningVariables(v:Variable): Set[Variable] = {
    if(v.isDefined){
      v.definingConstraint.get.getVariables.toSet.filterNot(_ == v).flatMap(getDefiningVariables(_))
    }else{
      Set(v)
    }
  }

  
  def satisfy(anns: Iterable[Annotation]) {
    search.obj = Objective.SATISFY
    search.setSearchStrategy(anns)
  }
  
  def minimize(obj: IntegerVariable, anns: Iterable[Annotation]) {
    search.obj = Objective.MINIMIZE
    search.variable = Some(obj)
    search.setSearchStrategy(anns)
  }
  
  def maximize(obj: IntegerVariable, anns: Iterable[Annotation]) {
    search.obj = Objective.MAXIMIZE
    search.variable = Some(obj)
    search.setSearchStrategy(anns)
  }


//  def addSearch(s: Array[Variable],vrh: VariableStrategy.Value,vh: ValueStrategy.Value) {
//    //println("search "+vrh+" "+vh+ " variables:"+s.mkString(","))
//    search.heuristics =  search.heuristics :+ (s,vrh,vh)
//  }
//
//  def nSols(n: Int) {
//    search.nSols = n
//  }
}

//TODO: should go to the CP specific part
trait CompleteSearchStrategy {
  def toFznString: String
}

case class IntSearch(variables: Iterable[Variable], variableStrategy: VariableStrategy.Value,
                     valueStrategy: ValueStrategy.Value) extends CompleteSearchStrategy {
  override def toFznString: String = {
    s"int_search(${
      variables.mkString("[", ", ", "]")
    }, ${variableStrategy.toString}, ${valueStrategy.toString}, complete)"
  }
}

case class BoolSearch(variables: Iterable[Variable], variableStrategy: VariableStrategy.Value,
                      valueStrategy: ValueStrategy.Value) extends CompleteSearchStrategy {
  override def toFznString: String = {
    s"bool_search(${
      variables.mkString("[", ", ", "]")
    }, ${variableStrategy.toString}, ${valueStrategy.toString}, complete)"
  }
}

case class SeqSearch(strategies: Iterable[CompleteSearchStrategy]) extends CompleteSearchStrategy {
  override def toFznString: String = s"seq_search(${strategies.map(_.toFznString).mkString("[", ", ", "]")})"
}


object VariableStrategy extends Enumeration {
  val FIRST_FAIL: VariableStrategy.Value = Value("first_fail")
  val INPUT_ORDER: VariableStrategy.Value = Value("input_order")
  val ANTI_FIRST_FAIL: VariableStrategy.Value = Value("anti_first_fail")
  val SMALLEST: VariableStrategy.Value = Value("smallest")
  val LARGEST: VariableStrategy.Value = Value("largest")
  val OCCURENCE: VariableStrategy.Value = Value("occurence")
  val MOST_CONSTRAINED: VariableStrategy.Value = Value("most_constrained")
  val MAX_REGRET: VariableStrategy.Value = Value("max_regret")
}

object ValueStrategy extends Enumeration {
  val INDOMAIN_MIN: ValueStrategy.Value = Value("indomain_min")
  val INDOMAIN_MAX: ValueStrategy.Value = Value("indomain_max")
  val INDOMAIN_MIDDLE: ValueStrategy.Value = Value("indomain_middle")
  val INDOMAIN_MEDIAN: ValueStrategy.Value = Value("indomain_median")
  val INDOMAIN: ValueStrategy.Value = Value("indomain")
  val INDOMAIN_RANDOM: ValueStrategy.Value = Value("indomain_random")
  val INDOMAIN_SPLIT: ValueStrategy.Value = Value("indomain_split")
  val INDOMAIN_REVERSE_SPLIT: ValueStrategy.Value = Value("indomain_reverse_split")
  val INDOMAIN_INTERVAL: ValueStrategy.Value = Value("indomain_interval")
}

object Objective extends Enumeration {
  val MINIMIZE: Objective.Value = Value("minimize")
  val MAXIMIZE: Objective.Value = Value("maximize")
  val SATISFY: Objective.Value = Value("satisfy")
}


class Search() {
  //var nSols = 0
  var obj: Objective.Value = Objective.SATISFY
  var variable: Option[IntegerVariable] = None
  
  private[this] var completeStrategy: Iterable[CompleteSearchStrategy] = List.empty
  
  def setSearchStrategy(anns: Iterable[Annotation]): Unit = {
    this.completeStrategy = anns.filter(_.name match {
      case "int_search" => true
      case "bool_search" => true
      case "seq_search" => true
      case _ => false
    }).map(parseSearchStrategy)
//    println(completeStrategy.map(_.toFznString).mkString(" :: "))
    //if(this.completeStrategy.size > 0) Console.err.println("% ignoring search annotations")
  }
  
  private def parseSearchStrategy(s: Annotation): CompleteSearchStrategy = {
    s.name match {
      case "int_search" =>
        IntSearch(s.args.head
                  .asInstanceOf[Iterable[Any]]
          .filter(_.isInstanceOf[Variable])
          .asInstanceOf[Iterable[Variable]],
                   VariableStrategy.withName(s.args(1).asInstanceOf[Annotation].name),
                   ValueStrategy.withName(s.args(2).asInstanceOf[Annotation].name))
      case "bool_search" =>
        BoolSearch(s.args.head
                   .asInstanceOf[Iterable[Any]]
          .filter(_.isInstanceOf[Variable])
          .asInstanceOf[Iterable[Variable]],
                    VariableStrategy.withName(s.args(1).asInstanceOf[Annotation].name),
                    ValueStrategy.withName(s.args(2).asInstanceOf[Annotation].name))
      case "seq_search" =>
        SeqSearch(s.args.head.asInstanceOf[List[Annotation]].map(parseSearchStrategy))
    }
  }
  
  def getSearchStrategy: Iterable[CompleteSearchStrategy] = completeStrategy
}
