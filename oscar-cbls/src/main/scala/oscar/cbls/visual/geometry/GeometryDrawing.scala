package oscar.cbls.visual.geometry

import java.awt.Color

import javax.swing.JPanel
import org.locationtech.jts.geom.Geometry

trait GeometryDrawingTrait{
  def drawShapes(boundingBoxOn:Option[Geometry] = None,shapes:List[(Geometry,Option[Color],Option[Color],String)],centers:List[(Int,Int)])
}

object GeometryDrawingTypes extends Enumeration{
  val Simple, OnRealMap = Value
}


object GeometryDrawing {
  def apply(relevantDistances: List[(Int,Int)],
            geometryDrawingType: GeometryDrawingTypes.Value,
            area: Option[List[(Int,Int)]] = None,
            pointOfOrigin: Option[(Double, Double)] = None): JPanel with GeometryDrawingTrait ={
    geometryDrawingType match{
      case GeometryDrawingTypes.Simple=>
        new SimpleGeometryDrawing(relevantDistances)
      case GeometryDrawingTypes.OnRealMap =>
        require(pointOfOrigin.isDefined && area.isDefined,
          "In order to display Geometry drawing on a real map, " +
            "you need to specify the point of origin (lat,lon) and the area of" +
            " the drawing (in cm from origin)")
        val geometryDrawing = new SimpleGeometryDrawing(relevantDistances)
        new GeometryDrawingOnRealMap(pointOfOrigin.get,area.get, geometryDrawing)
    }
  }
}