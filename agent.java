import java.io.*;
import java.util.*;

class agent
{
	static Predicate query=new Predicate();
	static int noofstmt=0;
	static KnowledgeBase kb=new KnowledgeBase();
	public static void main(String args[])
	{
		try
		{
		    /* Read the input file containing the knowledge base and the query */
			Scanner s=new Scanner(new File("input.txt"));
			query.clause=s.next().trim();
			String parts[]=query.clause.split("\\(|\\,|\\)");
			query.predicatename=parts[0].trim();
			query.argument1=parts[1].trim();
			if(parts.length==3)
			{
				query.argument2=parts[2].trim();
			}
			noofstmt=s.nextInt();
			
			int i=0,j=0;
			
			while(s.hasNext())
			{
				String stmt=s.next().trim();
				if(stmt.contains("=>"))
				{
					Statement statemnt=new Statement();
					statemnt.antecedent=stmt.substring(0,stmt.indexOf("=>")).trim();
					statemnt.consequent=stmt.substring(stmt.indexOf("=>")+2,stmt.length()).trim();
					String predicates[]=statemnt.antecedent.split("\\&");
					statemnt.antpredicates=ConvertoPredicateObjects(predicates);
					predicates=statemnt.consequent.split("\\&");
					statemnt.conpredicates=ConvertoPredicateObjects(predicates);
					kb.statements.add(statemnt);
				}
				else
				{
					Predicate f=new Predicate();
					f.clause=stmt;
					
					parts=f.clause.split("\\(|\\,|\\)");
					f.predicatename=parts[0].trim();
					f.argument1=parts[1].trim();
					if(parts.length==3)
					{
						f.argument2=parts[2].trim();
					}
					
					
					kb.facts.add(f);
						
				}
				
			}
			
			/*Call Backward Chaining algorithm on the given query*/
			BackwardChaining(query);
			
			/* Process results of Backward Chaining to see if query can be inferred to be true or 
			   false from the given knowledge base 
			*/
			for(Statement st:kb.statements)
			{
				
				if(st.conpredicates.get(0).predicatename.equals(query.predicatename))
				{
					
					if(query.argument2!=null)
					{
						if(st.conpredicates.get(0).clause.equals(query.clause)||(st.conpredicates.get(0).argument1.equals(query.argument1)&&st.conpredicates.get(0).argument2.equals("x"))||(st.conpredicates.get(0).argument1.equals("x")&&st.conpredicates.get(0).argument2.equals(query.argument2)))
					
					 {   
						  //System.out.println(st.conpredicates.get(0).clause);
					      if(st.conpredicates.get(0).proof==true)
						     query.proof=true;
					 }
					}
					 if(query.argument2==null)
					 {	
						 if(st.conpredicates.get(0).clause.equals(query.clause)||st.conpredicates.get(0).argument1.equals(query.argument1)||st.conpredicates.get(0).argument1.equals("x"))
						 {
							 //System.out.println(st.conpredicates.get(0).clause);
						 
						     if(st.conpredicates.get(0).proof==true)
						 	   query.proof=true;
						 }
					 }
			   }  
			}
			PrintWriter out=new PrintWriter(new File("output.txt"));
			out.println(new Boolean(query.proof).toString().toUpperCase());
			out.close();
		}
		catch(Exception e)
		{
			//e.printStackTrace();
		}
	}
	
	private static ArrayList<Predicate> ConvertoPredicateObjects(String[] predicates) {
		// TODO Auto-generated method stub
		ArrayList<Predicate> pred=new ArrayList<Predicate>();
		for(String p:predicates)
		{
			
			String parts[]=p.split("\\(|\\,|\\)");
			Predicate curr=new Predicate();
			curr.clause=p;
			curr.predicatename=parts[0];
			curr.argument1=parts[1];
			if(parts.length==3)
				curr.argument2=parts[2];
		
		    pred.add(curr);
		}
		return pred;
	
	}

	public static void BackwardChaining(Predicate q)
	{
	
	/* Check if query is already present in the Knowledge Base, if it is, return true.
	   Else, check if it matches the consequent of any statement with implication, if it does 
	   then call Backward Chaining on each of the antecedents in the statement
	   with the variables substituted or Unified with the constants in the query
	   Continue till all statements in the Knowledge Base have been visited 
	*/
	try
	{	Boolean found=false;
		for(Predicate po:kb.facts)
		{
			if(q.clause.equals(query.clause))
			{
				if(po.clause.equals(q.clause))
				{	
					
					q.proof=true;
				    found=true;
				    return;
			
				}
			}
			else if(!q.clause.equals(query.clause))
			{
				
			
				if(po.predicatename.equals(q.predicatename))
				{
						if(q.argument2!=null)
						{
							if(po.argument1.equals(q.argument1)||po.argument2.equals(q.argument2))
							{
								 
						         q.proof=true;
						         found=true;
				
						         return;
							}
						}
						else if(q.argument2==null)
						{
							
					         q.proof=true;
					         found=true;
			
					         return;
						}
				}
			}
		}
	
		if(found!=true)
		{
			Statement st=new Statement();
		for(Statement stmt:kb.statements)
		   {
			
		    if(stmt.visited==false&&stmt.conpredicates.get(0).predicatename.equals(q.predicatename)&&stmt.conpredicates.get(0).proof==false)
		    {
		    	
               String x="x";
               if(stmt.conpredicates.get(0).argument1.equals("x")||stmt.conpredicates.get(0).argument1.equals(q.argument1))
		    	     x=q.argument1;
		    	if(stmt.conpredicates.get(0).argument2!=null)
		    	{
		    		
		    	    if(stmt.conpredicates.get(0).argument2.equals("x"))
		    		 x=q.argument2;
		    	    
		    	}
		    	String us=Unify(stmt.consequent,x);
		    	if(stmt.conpredicates.get(0).argument2!=null)
		    	{
		    	  
		    		if(stmt.conpredicates.get(0).argument1.equals(q.argument1)&&stmt.conpredicates.get(0).argument2.equals(q.argument2))
		    			us=q.clause;
		    	}
		        
		    	if(us.equals(q.clause))
		    	{ 
		    		
		    	    st=stmt;
		    	    
		    	
		    
		     if(st.visited==false)
		     {	x="x";
		    	
		     if(st.conpredicates.get(0).argument1.equals("x"))
	    	     x=q.argument1;
	    	if(st.conpredicates.get(0).argument2!=null)
	    	{
	    		
	    	    if(st.conpredicates.get(0).argument2.equals("x"))
	    		 x=q.argument2;
	    	    
	    	}
	    	
		    	boolean flag=true;
		    	String u=Unify(st.antecedent,x);
		    	
		    	for(String ant:u.split("\\&"))
		    	{
		    		
		    		Predicate p=new Predicate();
		    		p.clause=ant;
		    		
		    		p.predicatename=ant.split("\\(|\\,|\\)")[0];
		    		p.argument1=ant.split("\\(|\\,|\\)")[1];
		    		if(ant.contains(","))
		    		{
		    			  p.argument2=p.clause.split("\\(|\\,|\\)")[2];
		    		}
		    		
		    		st.visited=true;
		    		
		    	    BackwardChaining(p);
		    		
		    		if(p.proof==false)
		    		{
		    			flag=false;
		    			
		    		}
		    	}
		    	if(flag==true)
		    	{
		    		st.conpredicates.get(0).proof=true;
		    		st.proof=true;
		    	}
		    	
		    
		    
		    if(st.conpredicates.get(0).proof==true)
		    {
		    	
		    	
		    	if(st.conpredicates.get(0).predicatename.equals(q.predicatename))
		    	{
		    		q.proof=true;
		    		return;
		    	}
		    	return;
		    }
		    
		
		     }
		    }
		    }
		   }
		}
	    return;
	}
	catch(Exception e)
	{
		//e.printStackTrace();
		return;
	}
 }
	/* Replace variables in statement with constants in query */
	public static String Unify(String ant,String x)
	{
		ant=ant.trim();
		
		String r=ant.replaceAll("x",x);
	   return r;
		
	}
	
}
/* Knowledge Base contains set of statements with implications and set of facts*/
class KnowledgeBase
{
	ArrayList<Statement> statements=new ArrayList<Statement>();
	ArrayList<Predicate> facts=new ArrayList<Predicate>();
}
class Statement
{
	boolean visited=false;
	boolean proof=false;
	String antecedent=null;
	String consequent=null;
	ArrayList<Predicate> antpredicates=new ArrayList<Predicate>();
	ArrayList<Predicate> conpredicates=new ArrayList<Predicate>();	
}

class Predicate
{
	boolean visited=false;
	boolean proof=false;
	String clause=null;
	String predicatename=null;
	String argument1=null;
	String argument2=null;
}
