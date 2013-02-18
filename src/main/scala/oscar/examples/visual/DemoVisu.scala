package oscar.examples.visual

import oscar.visual.VisualFrame
import oscar.visual.VisualDrawing
import oscar.visual.ColoredShape
import oscar.visual.VisualRectangle
import java.awt.Color
import oscar.visual.VisualBinPacking
import scala.util.Random
import oscar.visual.Plot2D
import oscar.visual.VisualMap
import oscar.visual.Geocoder
import oscar.visual.Location
import java.io.IOException





object DemoVisu {

  val f = new VisualFrame("Results");
  def runInThread(p : => Unit) = {
     val thread = new Thread(new Runnable{
		def run = p
	  })
	  thread.start
  }
  
  def main(args: Array[String]): Unit = {
   
	val tb = f.createToolBar()
	
	tb.addButton("rectangles",{runInThread(demoRectangles)})
	tb.addButton("plot",{runInThread(demoPlot)})	
	tb.addButton("bin packing",{runInThread(demoBinPacking)})
	tb.addButton("map",{runInThread(demoMap)})	
	f.pack()
    
  }
  
  def demoBinPacking = {

		val bp = new VisualBinPacking(10, 50)
		
		val inf = f.createFrame("Bin Packing")
		inf.add(bp)
		f.pack()
		
		val items = Array.tabulate(10)(bp.addItem(_, (Math.random*100).toInt))
		
		val rand = new Random()
		
		
		for (i <- 0 until 100) {
			items(rand.nextInt(items.length)).setBin(rand.nextInt(10))
			Thread.sleep(500)
		}
		
  }
  
  def demoRectangles = {
    	val d = new VisualDrawing(false);
		val inf = f.createFrame("Rectangle");
		inf.add(d);
		f.pack();
		val rect = new VisualRectangle(d, 50, 50, 100, 50);

	
		Thread.sleep(1000);
		rect.innerCol_$eq(Color.red);
		Thread.sleep(1000);
		rect.width = 200;
		Thread.sleep(1000);
		rect.height = 100;
		Thread.sleep(1000);
		rect.move(100, 20);
		for (i <- 0 until 20) {
			Thread.sleep(50);
			rect.move(rect.x+5, rect.y);
		}
		rect.toolTip_$eq("Hello");
  }
  
  def demoPlot = {
	val inf = f.createFrame("Plot");
	val demo = new Plot2D("My Plot","xlab","ylab");
	inf.add(demo);
	inf.pack();
	
	
	for (i <- 0 to 10) {
		demo.addPoint(i, Math.random);
		Thread.sleep(1000);
	}
    
  }
  def demoMap = {
        val m = new VisualMap();
		val inf = f.createFrame("VisualMap");
		inf.add(m);
		f.pack();
		
		try {
			val citiesNames = List("Namur", "Bruxelles", "Antwerp", "Arlon", "Mons", "Ottignies", "London")
			var citiesCoord = List[Location]()
	        for ( c <-  citiesNames) {
	        	
	        	val loc = Geocoder.getLocation(c)
	        	citiesCoord = citiesCoord :+ loc
	        	m.createWaypoint(loc.lat,loc.lon);
	        	try {
					Thread.sleep(100)
				} catch  {
				case e :InterruptedException => e.printStackTrace()
				}
	        }
			
			

		
			val l = m.createLine((citiesCoord(6).lat,citiesCoord(6).lon),(citiesCoord(1).lat,citiesCoord(1).lon));
			
			citiesCoord.zipWithIndex.filter(p => p._2 != 1 && p._2 != 6).map(_._1).foreach(lo => m.createPath((lo.lat,lo.lon),(citiesCoord(1).lat,citiesCoord(1).lon)))

			
		} catch  {
		  case e1: IOException => e1.printStackTrace()
		}
		
		
		

		m.refresh()

  }
}