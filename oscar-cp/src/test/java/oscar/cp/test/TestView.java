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
package oscar.cp.test;


import junit.framework.TestCase;
import oscar.cp.core.CPStore;
import oscar.cp.core.variables.CPBoolVar;
import oscar.cp.core.variables.CPIntVar;


/**
 * @author Pierre Schaus pschaus@gmail.com
 */
public class TestView extends TestCase {
	
	private CPStore s;	
	
    public TestView(String name) {
        super(name);
        
    }
    	
	/**
     * setUp() method that initializes common objects
     */
    protected void setUp() throws Exception {
        super.setUp();
        s = new CPStore();
    }

    /**
     * tearDown() method that cleanup the common objects
     */
    protected void tearDown() throws Exception {
        super.tearDown();
        s = null;
    }
    
    public void testView(){  	
    	CPIntVar x = CPIntVar.apply(s,1,5);
    	CPIntVar y = CPIntVar.apply(s,1,5);
        System.out.println(x);

        CPBoolVar b = CPBoolVar.apply(s);


    	CPIntVar x1 = oscar.cp.modeling.constraint.plus(x,0);
    	CPIntVar x2 = oscar.cp.modeling.constraint.plus(x1,y);
    	
    	CPIntVar x3 = oscar.cp.modeling.constraint.plus(x,4);
    	
//    	for(Integer v: x) {
//    		System.out.println(v);
//    	}
    	
    	assertTrue(!s.isFailed());


    }

}
