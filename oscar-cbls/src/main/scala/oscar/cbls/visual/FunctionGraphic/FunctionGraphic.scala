package oscar.examples.cbls.routing.visual.FunctionGraphic

/**
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

import java.awt
import java.awt._
import java.awt.event.{MouseListener, MouseEvent, MouseMotionListener, ActionListener}
import java.awt.geom.Line2D.Double
import java.awt.geom.Rectangle2D
import javax.swing.JButton

import oscar.cbls.search.StopWatch
import oscar.visual.VisualDrawing
import oscar.visual.shapes.{VisualRectangle, VisualLine, VisualText}

import scala.collection.mutable.ListBuffer

/** This abstract class represent the base structure for
  * the classes who'll have the purpose of drawing the curve of a function.
  * It has many variables :
  * maxWidth : it represents the right horizontal drawing limit of the curve
  * minWidth : it represents the left horizontal drawing limit of the curve
  * diffWidth : the difference between the maxWidth and the minWidth
  * maxHeight : it represents the bottom vertical drawing limit of the curve
  * minHeight : it represents the top vertical drawing limit of the curve
  * diffHeight : the difference between the maxHeight and the minHeight
  * xValues : a ListBuffer that contains all the X values encountered so far
  * yValues : a ListBuffer that contains all the Y values encountered so far
  * maxXValueDisplayed : the maximum X value that will be displayed on the graphic
  * minXValueDisplayed : the minimum X value that will be displayed on the graphic
  * diffXValueDisplayed : the difference between the maxXValueDisplayed and the minXValueDisplayed
  * maxYValueDisplayed : the maximum Y value that will be displayed on the graphic
  * minYValueDisplayed : the minimum Y value that will be displayed on the graphic
  * diffYValueDisplayed : the difference between the maxYValueDisplayed and the minYValueDisplayed
  * maxXValue :  the maximum X value registered so far
  * minXValue : the minimum X value registered so far
  * diffXValue : the difference between the maxXValue and the minXValue
  * maxYValue : the maximum Y value registered so far
  * minYValue : the minimum Y value registered so far
  * diffYValue : the difference between the maxYValue and the minYValue
  * widthAdapter : an anonymous function that return the X position of a point in pixel
  *                based on the minXValueDisplayed and the maxXValueDisplayed values
  * heightAdapter : an anonymous function that return the Y position of a point in pixel
  *                based on the minYValueDisplayed and the maxYValueDisplayed
  *
  * @author fabian.germeau@student.vinci.be
  */

abstract class FunctionGraphic() extends VisualDrawing(false,false) with StopWatch{

  val maxWidth = () => getWidth -10
  val minWidth = 70
  val diffWidth = () => maxWidth() - minWidth
  val maxHeight = () => getHeight - 30
  val minHeight = 10
  val diffHeight = () => maxHeight() - minHeight

  val xValues:ListBuffer[Long] = new ListBuffer[Long]
  val yValues:ListBuffer[Int] = new ListBuffer[Int]

  var maxXValueDisplayed:Long = 0
  var minXValueDisplayed:Long = 0
  val diffXValueDisplayed = () => maxXValueDisplayed - minXValueDisplayed
  var maxYValueDisplayed:Long = 0
  var minYValueDisplayed:Long = 0
  val diffYValueDisplayed = () => maxYValueDisplayed - minYValueDisplayed

  val maxXValue = () => if(xValues.isEmpty)0 else xValues.max
  val minXValue = () => if(xValues.isEmpty)0 else xValues.min
  val diffXValue = () => maxXValue() - minXValue()
  val maxYValue = () => if(yValues.isEmpty)0 else yValues.max
  val minYValue = () => if(yValues.isEmpty)0 else yValues.min
  val diffYValue = () => maxYValue() - minYValue()

  val widthAdapter = (value:Long) => {
    ((value - minXValueDisplayed)*diffWidth().toDouble/Math.max(diffWidth(),diffXValueDisplayed())).toInt
  }
  val heightAdapter = (value:Long) => {
    (value - minYValueDisplayed)*diffHeight().toDouble/(maxYValueDisplayed - minYValueDisplayed)
  }

  //A list buffer that contains the color of the neighborhood that has found the current move
  val xColorValues:ListBuffer[Color] = new ListBuffer[Color]


  setLayout(new BorderLayout())

  def notifyNewObjectiveValue(objValue:Int, objTime:Long, color:Color)

  def clear(): Unit ={
    super.clear()
  }

  def drawGlobalCurve()

  def setTimeBorders(position:Int){}

  def setMaxNumberOfObject(percentage:scala.Double){}


}

/** This class has the purpose to draw the objective function curve.
  * It firstly collect all the objective value.
  * To do so, the search procedure has to call the notifyNewObjectiveValue with the objective value and the current time.
  * After that it draws the entire curve with the drawObjectiveCurve method
  *
  * @author fabian.germeau@student.vinci.be
  */

class ObjFunctionGraphic(width:Int,height:Int) extends FunctionGraphic(){

  //A list buffer that contains all the bests objective values encountered during the search
  val bestValues:ListBuffer[Int] = new ListBuffer[Int]

  //The current best objective value of the search
  val best = () => {
    if(bestValues.nonEmpty)
      bestValues.min
    else
      Int.MaxValue
  }

  //A variable and a MouseListener used to allow the user to display or not the best curve
  var displayBest = true
  addMouseListener(new MouseListener{
    override def mouseExited(e: MouseEvent): Unit = {}

    override def mouseClicked(e: MouseEvent): Unit = {
      if(e.getX <= minWidth && e.getY >= maxHeight()){
        displayBest = !displayBest
        drawGlobalCurve()
      }
    }

    override def mouseEntered(e: MouseEvent): Unit = {}

    override def mousePressed(e: MouseEvent): Unit = {}

    override def mouseReleased(e: MouseEvent): Unit = {}
  })


  /**
    * Clear the graphic and reset the different ListBuffers in order to begin another research
    */
  override def clear(): Unit ={
    super.clear()
    yValues.clear()
    xValues.clear()
    bestValues.clear()
    xColorValues.clear()
  }

  /**
    * Save the objective value, the best value encountered so far, the time value of the current state
    * and the color of the neighborhood encountered (also in the xColorMap if it is not already registered)
    */
  def notifyNewObjectiveValue(objValue:Int, time:Long, color:Color): Unit ={
    xValues.append(time)
    yValues.append(objValue)
    bestValues.append(Math.min(best(),objValue))
    xColorValues.append(color)
    maxXValueDisplayed = time
    minYValueDisplayed = best()
    maxYValueDisplayed = yValues.max
  }

  /**
    * Prepare the different values needed to draw the global curve.
    * It's similar to the previous method but this time the goal is to draw the entire curve.
    */
  override def drawGlobalCurve() = {
    super.clear()

    val (bottom,top) = getOrdFloorValues(minYValueDisplayed,maxYValueDisplayed)
    val (left,right) = getAbsFloorValues(minXValueDisplayed,maxXValueDisplayed)

    drawCurve()
    drawAxis(bottom,top,left.toLong,right.toLong)
  }

  /**
    * Draw the global curve, including all the values
    */
  def drawCurve(): Unit = {
    var currentTimeUnit:scala.Double = widthAdapter(0)
    var currentTimeUnitValue:scala.Double = 0.0
    var currentTimeUnitValuesNumber:scala.Double = 0.0
    var currentTimeUnitBestValue:scala.Double = 0.0
    var currentTimeUnitBestValuesNumber:scala.Double = 0.0
    var previousTimeUnitValue:scala.Double = 0.0
    var previousTimeUnitBestValue:scala.Double = 0.0
    var previousTimeUnit:scala.Double = 0.0
    for(i <- yValues.indices){
      if(widthAdapter(xValues(i)) == currentTimeUnit){
        currentTimeUnitValue += heightAdapter(yValues(i))
        currentTimeUnitValuesNumber += 1
        currentTimeUnitBestValue += heightAdapter(bestValues(i))
        currentTimeUnitBestValuesNumber += 1
      }else{
        if(currentTimeUnitValuesNumber != 0) {
          currentTimeUnitValue = maxHeight() - (currentTimeUnitValue/currentTimeUnitValuesNumber) + heightAdapter(minYValueDisplayed)
          currentTimeUnitBestValue = maxHeight() - (currentTimeUnitBestValue/currentTimeUnitBestValuesNumber) + heightAdapter(minYValueDisplayed)
          if(previousTimeUnitValue == 0.0) {
            previousTimeUnitValue = currentTimeUnitValue
            previousTimeUnitBestValue = currentTimeUnitBestValue
            previousTimeUnit = currentTimeUnit
          }
          val line = new VisualLine(this, new Double(previousTimeUnit+70, previousTimeUnitValue, currentTimeUnit+70, currentTimeUnitValue))
          line.outerCol_$eq(xColorValues(i))
          line.borderWidth = 3
          if(displayBest){
            val bestLine = new VisualLine(this,new Double(previousTimeUnit+70, previousTimeUnitBestValue, currentTimeUnit+70, currentTimeUnitBestValue))
            bestLine.outerCol_$eq(Color.green)
          }
          previousTimeUnit = currentTimeUnit
          previousTimeUnitValue = currentTimeUnitValue
          previousTimeUnitBestValue = currentTimeUnitBestValue
          currentTimeUnitValue = 0.0
          currentTimeUnitValuesNumber = 0.0
          currentTimeUnitBestValue = 0.0
          currentTimeUnitBestValuesNumber = 0.0
        }
        while(currentTimeUnit < widthAdapter(xValues(i))){
          currentTimeUnit += 1
        }
        currentTimeUnitValue += heightAdapter(yValues(i))
        currentTimeUnitValuesNumber += 1
        currentTimeUnitBestValue += heightAdapter(bestValues(i))
        currentTimeUnitBestValuesNumber += 1
      }
    }
  }

  /**
    * Return the values of the Y axis's border
    *
    * @param minObjValue The minimum objective value that will be drawn
    * @param maxObjValue The maximum objective value that will be drawn
    * @return The bottom and top border of the Y axis
    */
  def getOrdFloorValues(minObjValue:Long, maxObjValue:Long): (Long,Long) ={
    if(diffYValueDisplayed() == 0){
      (minObjValue - 5, minObjValue + 5)
    }else {
      var diffFloor:Long = 1
      while (diffFloor <= diffYValueDisplayed()){
        diffFloor *= 10
      }
      var minFloor = 1
      //to prevent the case when the min and the max value are too different (like max = 15000 and min 100)
      while (minObjValue / minFloor > 0) {
        minFloor *= 10
      }
      val df = Math.max(diffFloor / 10, 10)
      (Math.max((minObjValue / df) * df, (minObjValue / minFloor) * minFloor), ((maxObjValue / df) * df) + df)
    }
  }

  /**
    * Return the value of the X axis's border
 *
    * @param minTimeValue The minimum objective's time of occurrence that will be drawn
    * @param maxTimeValue The maximum objective's time of occurrence that will be drawn
    * @return The left and right border of the X axis
    */
  def getAbsFloorValues(minTimeValue:scala.Long, maxTimeValue:scala.Long): (scala.Long, scala.Long) ={
    var diffFloor = 1
    while(diffFloor <= diffXValueDisplayed())
      diffFloor *= 10
    var minFloor = 1
    while(minTimeValue/minFloor > 0.0){
      minFloor *= 10
    }
    val df = Math.max(diffFloor / 10, 1)
    (Math.max((minTimeValue / df) * df, (minTimeValue / minFloor) * minFloor), ((maxTimeValue / df) * df) + df)
  }

  /**
    * Draw the axis. We draw blank rectangle to erase the parts of the curve that overstep the axes.
 *
    * @param minY The bottom border of the Y axis
    * @param maxY The top border of the Y axis
    * @param minX The left border of the X axis
    * @param maxX The right border of the X axis
    */
  def drawAxis(minY:Long, maxY:Long, minX:Long, maxX:Long): Unit ={
    val rectLeft = new VisualRectangle(this, new Rectangle2D.Double(0,0,minWidth,getHeight))
    rectLeft.innerCol_=(Color.white)
    rectLeft.outerCol_=(Color.white)
    val rectBottom = new VisualRectangle(this, new Rectangle2D.Double(0,maxHeight(),getWidth,getHeight))
    rectBottom.innerCol_=(Color.white)
    rectBottom.outerCol_=(Color.white)
    val ordLine = new VisualLine(this,new Double(minWidth,minHeight,minWidth,maxHeight()))
    ordLine.outerCol_$eq(Color.black)
    val absLine = new VisualLine(this,new Double(minWidth,maxHeight(),maxWidth(),maxHeight()))
    absLine.outerCol_$eq(Color.black)

    //We determine the step of the scale
    val objStep = (maxY - minY)/10
    for(i <- 1 to 10){
      val scaleHeight = maxHeight() - heightAdapter((i*objStep) + minY)
      new VisualText(this,5,scaleHeight,(minY+(objStep*i)).toString,false,new Rectangle2D.Double(0, 0, 1, 1))
      new VisualLine(this,new Double(minWidth-10,scaleHeight,minWidth,scaleHeight))
    }
    val timeStep = (maxX - minX)/10
    for(i <- 1 to 10){
      val scaleWidth = widthAdapter((i*timeStep) + minX)
      new VisualText(this,scaleWidth,maxHeight()+20,((timeStep*i) + minX).toString,true,new Rectangle2D.Double(0, 0, 1, 1))
      new VisualLine(this,new Double(scaleWidth,maxHeight(),scaleWidth,maxHeight()+10))
    }
    val rectTop = new VisualRectangle(this, new Rectangle2D.Double(minWidth,0,getWidth,10))
    rectTop.innerCol_=(Color.white)
    rectTop.outerCol_=(Color.white)
    val rectRight = new VisualRectangle(this, new Rectangle2D.Double(maxWidth(),0,getWidth,getHeight))
    rectRight.innerCol_=(Color.white)
    rectRight.outerCol_=(Color.white)
    val rectBottomLeft = new VisualRectangle(this, new Rectangle2D.Double(0,maxHeight(),minWidth,getHeight))
    val bestText = new VisualText(this,minWidth/2,maxHeight()+20,"Best",true,new Rectangle2D.Double(0,0,1,1))
    bestText.fontColor= if (displayBest) Color.green else Color.red
  }
}