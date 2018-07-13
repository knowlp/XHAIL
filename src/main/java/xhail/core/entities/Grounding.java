/**
 * 
 */
package xhail.core.entities;
import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileOutputStream;
import java.io.FileReader;
import java.io.FileWriter;
import java.io.IOException;
import java.io.InputStreamReader;
import java.io.OutputStream;
import java.io.UnsupportedEncodingException;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;
import java.util.TreeSet;
import java.util.TreeMap;
import java.util.Iterator;
import java.lang.Math;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.nio.file.StandardCopyOption;

import org.apache.commons.lang3.StringUtils;
import org.apache.commons.lang3.tuple.Pair;
import org.json.* ;

import xhail.core.Buildable;
import xhail.core.Config;
import xhail.core.Dialler;
import xhail.core.Logger;
import xhail.core.Utils;
import xhail.core.parser.Parser;
import xhail.core.statements.Display;
import xhail.core.statements.Example;
import xhail.core.statements.ModeB;
import xhail.core.statements.ModeH;
import xhail.core.terms.Atom;
import xhail.core.terms.Clause;
import xhail.core.terms.Literal;
import xhail.core.terms.Scheme;
import xhail.core.terms.SchemeTerm;
import xhail.core.terms.Term;
import xhail.core.terms.Variable;

public class Grounding implements Solvable {


	public static class Builder implements Buildable<Grounding> {

		private Set<Literal> covered = new HashSet<>();
		private Set<Atom> delta = new HashSet<>();
		private Set<Atom> facts = new HashSet<>();
		private Set<Atom> model = new HashSet<>();
		private Problem problem;
		private Set<Literal> uncovered = new HashSet<>();

		public Builder(Problem problem) {
			if (null == problem)
				throw new IllegalArgumentException("Illegal 'problem' argument in Grounding.Builder(Problem): " + problem);
			this.problem = problem;
		}

		public Builder addAtom(Atom atom) {
			if (null == atom)
				throw new IllegalArgumentException("Illegal 'atom' argument in Grounding.Builder.addAtom(Atom): " + atom);
			if (atom.getIdentifier().startsWith("abduced_")) {
				delta.add(new Atom.Builder(atom.getIdentifier().substring("abduced_".length())).addTerms(atom.getTerms()).build());
			} else {
				if (problem.getConfig().isFull() && problem.hasDisplays() && problem.lookup(atom))
					model.add(atom);
				facts.add(atom);
			}
			return this;
		}

		public Builder addAtoms(Collection<Atom> atoms) {
			if (null == atoms)
				throw new IllegalArgumentException("Illegal 'atoms' argument in Grounding.Builder.addAtoms(Collection<Atom>): " + atoms);
			for (Atom atom : atoms)
				addAtom(atom);
			return this;
		}

		@Override
		public Grounding build() {
			covered.clear();
			uncovered.clear();
			for (Example example : problem.getExamples()) {
				Atom atom = example.getAtom();
				if (example.isNegated() != facts.contains(atom))
					covered.add(new Literal.Builder(atom).setNegated(example.isNegated()).build());
				else
					uncovered.add(new Literal.Builder(atom).setNegated(example.isNegated()).build());
			}
			return new Grounding(this);
		}

		public Builder clear() {
			this.covered.clear();
			this.delta.clear();
			this.facts.clear();
			this.model.clear();
			this.uncovered.clear();
			return this;
		}

		public Builder parse(Collection<String> answer) {
			if (null == answer)
				throw new IllegalArgumentException("Illegal 'answer' argument in Grounding.Builder.parse(Collection<String>): " + answer);
			for (String atom : answer)
				addAtom(Parser.parseToken(atom));
			return this;
		}

		public Builder removeAtom(Atom atom) {
			if (null == atom)
				throw new IllegalArgumentException("Illegal 'atom' argument in Grounding.Builder.removeAtom(Atom): " + atom);
			if (atom.getIdentifier().startsWith("abduced_")) {
				delta.remove(new Atom.Builder(atom.getIdentifier().substring("abduced_".length())).addTerms(atom.getTerms()).build());
			} else {
				if (problem.getConfig().isFull() && problem.hasDisplays() && problem.lookup(atom))
					model.remove(atom);
				facts.remove(atom);
			}
			return this;
		}

		public Builder removeAtoms(Collection<Atom> atoms) {
			if (null == atoms)
				throw new IllegalArgumentException("Illegal 'atoms' argument in Grounding.Builder.removeAtoms(Collection<Atom>): " + atoms);
			for (Atom atom : atoms)
				removeAtom(atom);
			return this;
		}

	}
	
	

	private final Config config;

	private final int count;

	private final Literal[] covered;

	private final Atom[] delta;

	private final Set<Atom> facts;

	private Clause[] generalisation;

	private Clause[] kernel;

	private final Atom[] model;

	private final Problem problem;

	private final Map<SchemeTerm, Set<Atom>> table;

	private final Literal[] uncovered;

  private final int BASEPRIO = 0; // see also Modeh.java, add this to weak constraint priority

	private Grounding(Builder builder) {
		if (null == builder)
			throw new IllegalArgumentException("Illegal 'builder' argument in Grounding(Grounding.Builder): " + builder);
		this.config = builder.problem.getConfig();
		this.count = builder.delta.size();
		this.covered = builder.covered.toArray(new Literal[builder.covered.size()]);
		this.delta = builder.delta.toArray(new Atom[builder.delta.size()]);
		this.facts = builder.facts;
		this.model = builder.model.toArray(new Atom[builder.model.size()]);
		this.problem = builder.problem;
		this.table = SchemeTerm.lookup(builder.problem.getModeHs(), builder.problem.getModeBs(), builder.facts);
		this.uncovered = builder.uncovered.toArray(new Literal[builder.uncovered.size()]);
	}

	public final String asBadSolution() {
		return String.format("bad_solution:-%snumber_abduced(%d).", count > 0 ? StringUtils.join(delta, ",") + "," : "", count);
	}
	
  
	public String[] asClauses() {
		Set<String> result = new LinkedHashSet<>();
		Clause[] clauses = getGeneralisation();
		if (clauses.length > 0) {
			result.add("{ use_clause_literal(V1,0) }:-clause(V1).");

			boolean hasLiterals = false;
			for (int clauseId = 0; !hasLiterals && clauseId < clauses.length; clauseId++)
				hasLiterals = clauses[clauseId].getBody().length > 0;

			if (hasLiterals)
				result.add("{ use_clause_literal(V1,V2) }:-clause(V1),literal(V1,V2).");

			for (int clauseId = 0; clauseId < clauses.length; clauseId++) {
				result.add(String.format("%% %s", clauses[clauseId]));
				Literal[] literals = clauses[clauseId].getBody();
				result.add(String.format("clause(%d).", clauseId));
				for (int literalId = 1; literalId <= literals.length; literalId++)
					result.add(String.format("literal(%d,%d).", clauseId, literalId));

				for (int level = 0; level < clauses[clauseId].getLevels(); level++)
					result.add(String.format(":-not clause_level(%d,%d),clause_level(%d,%d).", clauseId, level, clauseId, 1 + level));

				result.add(String.format("clause_level(%d,0):-use_clause_literal(%d,0).", clauseId, clauseId));
				for (int literalId = 1; literalId <= literals.length; literalId++)
					result.add(String.format("clause_level(%d,%d):-use_clause_literal(%d,%d).", clauseId, literals[literalId - 1].getLevel(), clauseId,
							literalId));

				Atom head = clauses[clauseId].getHead();
				//result.add(String.format("#minimize[ use_clause_literal(%d,0) =%d @%d ].", clauseId, head.getWeight(), head.getPriority()));
				result.add(String.format(":~ use_clause_literal(%d,0). [%d@%d,%d]", clauseId, head.getWeight(), head.getPriority()+BASEPRIO, clauseId));

				for (int literalId = 1; literalId <= literals.length; literalId++)
					//result.add(String.format("#minimize[ use_clause_literal(%d,%d) =%d @%d ].", clauseId, literalId, //
					//		literals[literalId - 1].getWeight(), literals[literalId - 1].getPriority()));
					result.add(String.format(":~ use_clause_literal(%d,%d). [%d@%d,use_clause_literal(%d,%d)]",
						clauseId, literalId,
						literals[literalId - 1].getWeight(), literals[literalId - 1].getPriority()+BASEPRIO,
						clauseId, literalId));

				Set<String> set = new LinkedHashSet<>();
				for (String type : head.getTypes())
					set.add(type);
				String[] array = new String[literals.length];
				for (int literalId = 1; literalId <= literals.length; literalId++) {
					String variables = literals[literalId - 1].hasVariables() ? "," + StringUtils.join(literals[literalId - 1].getVariables(), ",") : "";
					array[literalId - 1] = String.format("try_clause_literal(%d,%d%s)", clauseId, literalId, variables);
					for (String type : literals[literalId - 1].getTypes())
						set.add(type);
				}
				String typesAll = !set.isEmpty() ? "," + StringUtils.join(set, ",") : "";
				String literalsAll = array.length > 0 ? "," + StringUtils.join(array, ",") : "";
				result.add(String.format("%s:-use_clause_literal(%d,0)%s%s.", head, clauseId, literalsAll, typesAll));

				for (int literalId = 1; literalId <= literals.length; literalId++) {
					String variables = literals[literalId - 1].hasVariables() ? "," + StringUtils.join(literals[literalId - 1].getVariables(), ",") : "";
					String types = literals[literalId - 1].hasTypes() ? "," + StringUtils.join(literals[literalId - 1].getTypes(), ",") : "";
					result.add(String.format("try_clause_literal(%d,%d%s):-use_clause_literal(%d,%d),%s%s.", //
							clauseId, literalId, variables, clauseId, literalId, literals[literalId - 1], types));
					result.add(String.format("try_clause_literal(%d,%d%s):-not use_clause_literal(%d,%d)%s.", //
							clauseId, literalId, variables, clauseId, literalId, types));
				}

        // For modeB count restrictions, add constraints to limit how many literals are used in solutions
        for (ModeB mode : problem.getModeBs()) {
          Scheme scheme = mode.getScheme();
          if (mode.getUpper() != Integer.MAX_VALUE) {
            //Logger.message(String.format("Grounding::asClauses checking ModeB %s scheme %s with limit %d", mode.toString(), scheme.toString(), mode.getUpper()));
            // find out which literals are from this mode and limit them
            Set<String> literalsToLimit = new LinkedHashSet<>();
            for (int literalId = 1; literalId <= literals.length; literalId++) {
              Literal literal = literals[literalId-1];
              //Logger.message(String.format("checking literal %s/atom %s", literal.toString(), literal.getAtom().toString()));
              // XXX there is mode.isNegated(), scheme.isNegated(), literal.isNegated() but the second seems unused
              if (literal.isNegated() == mode.isNegated() && SchemeTerm.isMatching(scheme, literal.getAtom())) {
                String limitLiteral = String.format("%d:use_clause_literal(%d,%d)", literalId, clauseId, literalId);
                literalsToLimit.add(limitLiteral);
                //Logger.message("matching! added "+limitLiteral);
              }
            }
            if( !literalsToLimit.isEmpty() ) {
              // need to apply modeB restriction (cannot use more than <limit> at once)
              result.add(String.format(":- %d < #count { %s }.",
                  mode.getUpper(), StringUtils.join(literalsToLimit, ";")));
            }
          }
        }
			}
		}
		return result.toArray(new String[result.size()]);
	}

	@Override
	public boolean equals(Object obj) {
		if (this == obj)
			return true;
		if (obj == null)
			return false;
		if (getClass() != obj.getClass())
			return false;
		Grounding other = (Grounding) obj;
		if (!Arrays.equals(covered, other.covered))
			return false;
		if (!Arrays.equals(delta, other.delta))
			return false;
		if (facts == null) {
			if (other.facts != null)
				return false;
		} else if (!facts.equals(other.facts))
			return false;
		if (!Arrays.equals(generalisation, other.generalisation))
			return false;
		if (!Arrays.equals(kernel, other.kernel))
			return false;
		if (!Arrays.equals(model, other.model))
			return false;
		if (table == null) {
			if (other.table != null)
				return false;
		} else if (!table.equals(other.table))
			return false;
		if (problem == null) {
			if (other.problem != null)
				return false;
		} else if (!problem.equals(other.problem))
			return false;
		if (!Arrays.equals(uncovered, other.uncovered))
			return false;
		return true;
	}

	public final String[] getBackground() {
		return problem.getBackground();
	}

	public final Config getConfig() {
		return config;
	}

	public final int getCount() {
		return count;
	}

	public final Literal[] getCovered() {
		return covered;
	}

	public final Atom[] getDelta() {
		return delta;
	}

	public final Display[] getDisplays() {
		return problem.getDisplays();
	}

	public final String[] getDomains() {
		return problem.getDomains();
	}

	public final Example[] getExamples() {
		return problem.getExamples();
	}

	public final Collection<Atom> getFacts() {
		return facts;
	}

	public final Collection<String> getFilters() {
		Set<String> result = new TreeSet<>();
		//result.add("#hide.");
		result.add("#show.");
		// result.add("#show display_fact/1.");
		// result.add("#show covered_example/2.");
		// result.add("#show number_abduced/1.");
		// result.add("#show uncovered_example/2.");
		result.add("#show use_clause_literal/2.");
		for (Display display : problem.getDisplays())
			result.add(String.format("#show %s/%d.", display.getIdentifier(), display.getArity()));
		for (Example example : problem.getExamples())
			result.add(String.format("#show %s/%d.", example.getAtom().getIdentifier(), example.getAtom().getArity()));
		return result;
	}
	/*
	public final void getRuleFromAnswerset(Object ras, boolean structured, boolean debugCosts)
	{
		 
		  ras = [getTuple(a) for a in ras];
				  
		  String head = "";
		  Map<String,String> pbodies = new HashMap<String,String>();
		  Map<String,String> nbodies = new HashMap<String,String>();
		  Map<String,String> variables = new HashMap<String,String>();


		  ArrayList<String> predatoms = new ArrayList<String>();
		  ArrayList<String> varatoms = new ArrayList<String>();
		  int totalcost = 0;
		  
		  Map<Integer,Integer> detailedcosts = new HashMap<Integer,Integer>();
		  for(atm in ras)
		  {
		    apred = atm[0];
		    if (atm[0].Equals("totalcost"))
		      totalcost = (int) atm[1];
		    else if(apred in ['use_head_pred', 'use_body_pred'])
		      predatoms.append(atm);
		    else if (apred in ['use_var_type', 'bind_hvar', 'bind_bvar'])
		      varatoms.append(atm);
		   else if (apred in ['cost'] and debugCosts)
		      detailedcosts[atm[1]].append(atm[2:]);
		  }
		  
		  for atm in predatoms:
		    apred = atm[0]
		    aargs = atm[1:]
		    if apred == 'use_head_pred':
		      predid, pred, arity = aargs
		      arity = int(arity)
		      head = [pred] + [None]*arity
		    elif apred == 'use_body_pred':
		      id_idx, pred, polarity, arity = aargs
		      arity = int(arity)
		      dummy, predid, idx = id_idx
		      if polarity == 'pos':
		        bodies = pbodies
		      else:
		        bodies = nbodies
		      bodies[tuple(id_idx)] = [pred] + [None]*arity

		  # get variables
		  for atm in varatoms:
		    apred = atm[0]
		    aargs = atm[1:]
		    if apred == 'use_var_type':
		      v_idx, type_ = aargs
		      v, idx = v_idx
		      variables[int(idx)] = type_
		    elif apred == 'bind_hvar':
		      pos, v_idx = aargs
		      v, idx = v_idx
		      head[int(pos)] = makeVar(idx)
		    elif apred == 'bind_bvar':
		      id_idx, polarity, position, v_idx = aargs
		      dummy, predid, idx = id_idx
		      v, idx = v_idx
		      if polarity == 'pos':
		        bodies = pbodies
		      else:
		        bodies = nbodies
		      bodies[tuple(id_idx)][int(position)] = makeVar(idx)

		  safevars = map(makeVarSafe, variables.iteritems())
		  #warn('safevars:'+repr(safevars))

		  if debugCosts:
		    #warn('detailedcosts:')
		    for ct in detailedcosts.iterkeys():
		      warn('  {}:'.format(ct))
		      for c in detailedcosts[ct]:
		        #warn('    '+' | '.join(map(repr, c)))
		        warn('    '+' | '.join(map(makeAtom, c)))

		  if structured:
		    # structured output
		    rule = {
		      "head": head,
		      "pbody":pbodies.values() + safevars,
		      "nbody":nbodies.values()
		    }

		    return rule, totalcost
		  else:
		    # string output
		    rule = makeAtom(head)
		    if len(pbodies) + len(safevars) + len(nbodies) == 0:
		      rule += '.'
		    else:
		      lits = sorted([ makeLiteral(lit, True) for lit in (pbodies.values()+safevars) ])
		      lits += sorted([ makeLiteral(lit, False) for lit in nbodies.values() ])
		      rule += " :- " + ",".join(lits) + "."
		    ret = rule, totalcost
		    if debugCosts:
		      warn('[{}] {}\n'.format(totalcost, rule))
		    return ret
		    		
	}
	
	*/
    public final List<Entry<JSONObject, JSONObject>> getAnswerSets(String program, String args, boolean withCost) {

    	
    	//System.out.println(program);
    	
    	if(args.equals(""))
    		args="0";
    	File temp=null;
		try {
			temp = File.createTempFile("tmpf", ".lp");
		} catch (IOException e1) {
			// TODO Auto-generated catch block
			e1.printStackTrace();
		} 
    	BufferedWriter bw=null;
		try {
			bw = new BufferedWriter(new FileWriter(temp));
		} catch (IOException e1) {
			// TODO Auto-generated catch block
			e1.printStackTrace();
		}
	    try {
			bw.write(program);
		} catch (IOException e1) {
			// TODO Auto-generated catch block
			e1.printStackTrace();
		}
	    try {
			bw.close();
		} catch (IOException e1) {
			// TODO Auto-generated catch block
			e1.printStackTrace();
		}
	    
        System.out.println("wrote ASP to "+temp.getAbsolutePath());
        String command= "clingo --outf=2 "+ args + " " +temp.getAbsolutePath();
        //System.out.println(command);
        List<String> li= new ArrayList<String>(Arrays.asList(command.split(" ")));
		ProcessBuilder bld = new ProcessBuilder(li);
		bld.redirectErrorStream(true);
        try {
			Process p = bld.start();
		} catch (IOException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
		Runtime rt = Runtime.getRuntime();
		Process pr=null;
		try {
			pr = rt.exec(command);
		} catch (IOException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
	    BufferedReader stdInput = new BufferedReader(new InputStreamReader(pr.getInputStream()));  
		String output="";
		String line="";
		while (line != null)
		{
		output+=line+"\n";
		try {
			line=stdInput.readLine();
		} catch (IOException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
		}
		//System.out.println("asp output:" + output);
		JSONObject out=null;
		try {
			out = new JSONObject(output);
		} catch (JSONException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
		
		ArrayList<JSONObject> answersets=null;
		System.out.println(out);
       /*
		JSONArray tmp=null;
		try {
			tmp = (JSONArray) out.get("Call");
		} catch (JSONException e3) {
			// TODO Auto-generated catch block
			e3.printStackTrace();
		}
		JSONObject obj=null;
		try {
			obj = (JSONObject) tmp.get(0);
		} catch (JSONException e3) {
			// TODO Auto-generated catch block
			e3.printStackTrace();
		}
		
		try {
			obj.get("Witnesses");
		
		if((boolean) obj.get("Witnesses"))
		{
			try {
				answersets=(ArrayList<JSONObject>) obj.get("Witnesses");
			} catch (JSONException e2) {
				// TODO Auto-generated catch block
				e2.printStackTrace();
			}
			try {
				JSONObject tmp2 = (JSONObject) out.get("Models");
			} catch (JSONException e1) {
				// TODO Auto-generated catch block
				e1.printStackTrace();
			}
			//if ((boolean)tmp2.get("Optimal"))
			     // answersets = answersets[-tmp2.get("Optimal"):];
			    if (withCost)
			    {	
			    	java.util.List<java.util.Map.Entry<JSONObject,JSONObject>> tmp1= new java.util.ArrayList<>();
			    	for(JSONObject witness : answersets)
						try {
							tmp1.add(new java.util.AbstractMap.SimpleEntry(witness.get("Value"), witness.get("cost")));
						} catch (JSONException e) {
							// TODO Auto-generated catch block
							e.printStackTrace();
						}
			    	 return tmp1;
			     // return [ (witness["Value"], witness["Costs"]) for witness in answersets];
			    		  }
			    else
			    {
			    	java.util.List<java.util.Map.Entry<JSONObject,JSONObject>> tmp1= new java.util.ArrayList<>();
			    	for(JSONObject witness : answersets)
						try {
							tmp1.add(new java.util.AbstractMap.SimpleEntry(witness.get("Value"), 0));
						} catch (JSONException e) {
							// TODO Auto-generated catch block
							e.printStackTrace();
						}
			    	 return tmp1;
			      //return [witness["Value"] for witness in answersets];
			    }
		}
		
		
		else
			return null;
		} catch (JSONException e3) {
			// TODO Auto-generated catch block
			e3.printStackTrace();
		}
		*/
		return null;
    	
    }
	public final Clause[] getGeneralisation() {
		if (null == generalisation) {
      //Logger.message("getGeneralization");
			Map<Clause,Integer> gmap = new HashMap<>();
			Integer largestSupport = 0;
			for (Clause clause : getKernel()) {
				Map<Term, Variable> map = new HashMap<>();
				Clause.Builder builder = new Clause.Builder();
				Atom atom = clause.getHead();
				for (ModeH mode : problem.getModeHs()) {
					Scheme scheme = mode.getScheme();
					if (SchemeTerm.subsumes(scheme, atom, facts))
						builder.setHead((Atom) scheme.generalises(atom, map));
				}
				for (Literal literal : clause.getBody()) {
					atom = literal.getAtom();
					for (ModeB mode : problem.getModeBs()) {
						Scheme scheme = mode.getScheme();
						if (SchemeTerm.subsumes(scheme, atom, facts))
							builder.addLiteral(new Literal.Builder((Atom) scheme.generalises(atom, map)).setNegated(literal.isNegated())
									.setLevel(literal.getLevel()).build());
					}
				}

				Clause genClause = builder.build();
				//set.add(genClause);
				if (gmap.containsKey(genClause)) {
					Integer newsup = gmap.get(genClause) + 1;
					largestSupport = Math.max(largestSupport, newsup);
					gmap.put(genClause, newsup);
				} else {
				    gmap.put(genClause, 1);
				}
			}
			Iterator it = gmap.entrySet().iterator();
			while(it.hasNext()) {
				Map.Entry<Clause, Integer> entry = (Map.Entry<Clause, Integer>)it.next();
				String msg = "";
				long prune = problem.getConfig().getPrune();
				if (largestSupport > 2*prune && entry.getValue() <= prune) {
					// erase those generalization clauses that have less than "prune" supporting instances
					// but only if the largest support is higher than 2*prune (to avoid pruning (nearly) everything)
					// (if prune = 0 this does not prune anything)
					it.remove();
					msg = " (pruned)";
				}
				Logger.message(String.format("Generalization %2d support for %s%s", entry.getValue(), entry.getKey(), msg));
			}
			generalisation = gmap.keySet().toArray(new Clause[gmap.size()]);
		}
		return generalisation;
	}

	
	public final Clause[] getKernel() {
		if (null == kernel) {
			//Logger.message("getKernel");
			
			Set<Clause> set = new LinkedHashSet<>();
			//
		
			String insp="";
				
			/*
			 * % head predicates and args
				hpred(I,P,N) :- tpred(I,P,N).
				harg(I,J,T) :- targ(I,J,T).

				% body predicates and args
				% bpred(PredIdentifier,Predicate,NumberOfArguments)
				% barg(PredIdentifier,ArgumentPosition,Type)
				bpred(I,P,N) :- rpred(I,P,N).
				barg(I,J,T) :- rarg(I,J,T).
				
				#modeh flies(+bird).
                #modeb penguin(+bird).
				#modeb not penguin(+bird).
			 */
			
			String modeH=null;
			String headt=null;
			String htmp= null;
			String[] hargs=null;
			int counter=0;
			for(int i=0;i<getModeHs().length;i++)
			{
				modeH = getModeHs()[i].toString();
				if(modeH.contains("not"))
					htmp = modeH.split(" ")[2].toString();
				else
					htmp = modeH.split(" ")[1].toString();
				headt = htmp.split("\\(")[0];
			    hargs = htmp.split("\\(")[1].split(",");
			    if(modeH.contains("not"))
			    	insp+="not tpred("+ counter + "," + headt + "," + hargs.length +").\n";
			    else
			    	insp+="tpred("+ counter + "," + headt + "," + hargs.length +").\n";
				hargs[0]=hargs[0].replaceAll("[^A-Za-z]+", "");
				hargs[hargs.length-1]=hargs[hargs.length-1].replaceAll("[^A-Za-z]+", "");
				
				for(int k=1;k<hargs.length;k++)
					{insp+="targ("+ counter + "," + k + "," + hargs[k] +").\n";}
				counter+=1;
			}
			
			insp+="\n";
			String modeB=null;
			String body=null;
			String btmp= null;
			String[] bargs=null;
			for(int i=0;i<getModeBs().length;i++)
				{
				modeB = getModeBs()[i].toString();
				if(modeB.contains("not"))
					btmp = modeB.split(" ")[2].toString();
				else
					btmp = modeB.split(" ")[1].toString();
				body = btmp.split("\\(")[0];
				bargs = btmp.split("\\(")[1].split(",");
				if(modeB.contains("not"))
					insp+="not rpred("+ counter + "," + body + "," + bargs.length +").\n";
				else
					insp+="rpred("+ counter + "," + body + "," + bargs.length +").\n";
				bargs[0]=bargs[0].replaceAll("[^A-Za-z]+", "");
				bargs[bargs.length-1]=bargs[bargs.length-1].replaceAll("[^A-Za-z]+", "");
				for(int j=1;j<bargs.length;j++)
					insp+="rarg("+ counter + "," + j + "," + bargs[j] +").\n";
				counter+=1;
				}
			
			insp+="\n";
			
			//System.out.println(insp);
			int costlimit=4;
			String line="";
			
		    FileReader fr=null;
			try {
				fr = new FileReader("hypgen.lp");
			} catch (FileNotFoundException e) {
				// TODO Auto-generated catch block
				e.printStackTrace();
			}
			BufferedReader br = new BufferedReader(fr);
			try {
				while ((line = br.readLine()) != null) 
					insp+=line+"\n";
			} catch (IOException e) {
				// TODO Auto-generated catch block
				e.printStackTrace();
			}
			
			
			List<Map.Entry<JSONObject,JSONObject>> hyp_as = getAnswerSets(insp,"--const maxcost="+costlimit+" 1",false);
			
			/*
			String[] allrules = null;
			String[] candidateRules;
				
			for(Object ras : hyp_as)
			{
			   if(true)
		        {
		          int nsrule, nscost = getRuleFromAnswerset(ras, structured=False, debugCosts=False);
		        }
				int rule, cost = getRuleFromAnswerset(ras, structured=True);
				allrules.append(Pair.of(rule.toString(),cost.toString)));
			}  
			
			//
	*/
			for (Atom alpha : delta)
				for (ModeH head : problem.getModeHs()) {
					Scheme scheme = head.getScheme();
					if (SchemeTerm.subsumes(scheme, alpha, facts)) {
						Clause.Builder builder = new Clause.Builder().setHead(//
								new Atom.Builder(alpha).setWeight(head.getWeigth()).setPriority(head.getPriority()).build());//uses examples
                        
						Collection<Term> substitutes = SchemeTerm.findSubstitutes(scheme, alpha);
						if (null != substitutes) {
							int level = 0;
							Set<Term> usables = new HashSet<>(substitutes);
							Set<Term> used = new HashSet<Term>();
							Set<Term> next = new HashSet<Term>();
							while (!usables.isEmpty()) {
								level += 1;
								for (ModeB mode : problem.getModeBs()) {
									scheme = mode.getScheme();
									if (mode.isNegated()) {
										Map<Atom, Collection<Term>> found = SchemeTerm.generateAndOutput(scheme, usables, table, facts);
										for (Atom atom : found.keySet()) {
											builder.addLiteral(new Literal.Builder( //
													new Atom.Builder(atom).setWeight(mode.getWeigth()).setPriority(mode.getPriority()).build() //uses examples
											).setNegated(mode.isNegated()).setLevel(level).build());
											next.addAll(found.get(atom));
										}
									} else {
										Map.Entry<Collection<Atom>, Collection<Term>> found = SchemeTerm.matchAndOutput(scheme, table.get(scheme), usables);
										for (Atom atom : found.getKey())
											builder.addLiteral(new Literal.Builder( //
													new Atom.Builder(atom).setWeight(mode.getWeigth()).setPriority(mode.getPriority()).build() //uses examples
											).setNegated(mode.isNegated()).setLevel(level).build());
										next.addAll(found.getValue());
									}
								}
								used.addAll(usables);
								next.removeAll(used);
								usables.clear();
								usables.addAll(next);
								next.clear();
							}
						}
						set.add(builder.build());
						kernel = set.toArray(new Clause[set.size()]);
					}
				}
			kernel = set.toArray(new Clause[set.size()]);
		
		}
		return kernel;
	}

	public final ModeB[] getModeBs() {
		return problem.getModeBs();
	}

	public final String[] getBackg() {
		return problem.getBackground();
	} 
	
	public final ModeH[] getModeHs() {
		return problem.getModeHs();
	}

	public final Atom[] getModel() {
		return model;
	}

	public final Problem getProblem() {
		return problem;
	}

	public final Map<SchemeTerm, Set<Atom>> getTable() {
		return table;
	}

	public final Literal[] getUncovered() {
		return uncovered;
	}

	public final boolean hasBackground() {
		return problem.hasBackground();
	}

	public final boolean hasCovered() {
		return covered.length > 0;
	}

	public final boolean hasDelta() {
		return delta.length > 0;
	}

	public final boolean hasDisplays() {
		return problem.hasDisplays();
	}

	public final boolean hasDomains() {
		return problem.getDomains().length > 0;
	}

	public final boolean hasExamples() {
		return problem.hasExamples();
	}

	public final boolean hasGeneralisation() {
		return getGeneralisation().length > 0;
	}

	@Override
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = prime * result + Arrays.hashCode(covered);
		result = prime * result + Arrays.hashCode(delta);
		result = prime * result + ((facts == null) ? 0 : facts.hashCode());
		result = prime * result + Arrays.hashCode(generalisation);
		result = prime * result + Arrays.hashCode(kernel);
		result = prime * result + Arrays.hashCode(model);
		result = prime * result + ((table == null) ? 0 : table.hashCode());
		result = prime * result + ((problem == null) ? 0 : problem.hashCode());
		result = prime * result + Arrays.hashCode(uncovered);
		return result;
	}

	public final boolean hasKernel() {
		return getKernel().length > 0;
	}

	public final boolean hasModel() {
		return model.length > 0;
	}

	public final boolean hasModes() {
		return problem.hasModes();
	}

	public final boolean hasUncovered() {
		return uncovered.length > 0;
	}

	public final boolean lookup(Atom atom) {
		if (null == atom)
			throw new IllegalArgumentException("Illegal 'atom' argument in Grounding.lookup(Atom): " + atom);
		return problem.lookup(atom);
	}

	public final boolean needsInduction() {
		return getGeneralisation().length > 0;
	}

	@Override
	public boolean save(int iter, OutputStream stream) {
		return Utils.save(this, iter, stream);
	}

	public Values solve(Values values, Answers.Builder builder) {
		if (null == values)
			throw new IllegalArgumentException("Illegal 'values' argument in Grounding.solve(int, Values, Answers.Builder): " + values);
		if (null == builder)
			throw new IllegalArgumentException("Illegal 'builder' argument in Grounding.solve(int, Values, Answers.Builder): " + builder);
		Values result = values;
		if (this.needsInduction()) {
			if (config.isDebug())
				Logger.message(String.format("*** Info  (%s): need induction with this %s", Logger.SIGNATURE, this.toString()));
			Dialler dialler = new Dialler.Builder(config, this, values).build();
			Map.Entry<Values, Collection<Collection<String>>> entry = Answers.timeInduction(1, dialler);
			result = entry.getKey();
			for (Collection<String> output : entry.getValue()) {
				if (builder.size() > 0 && config.isTerminate())
					break;
				if (config.isDebug())
					Logger.message(String.format("*** Info  (%s): deduction with output %s", Logger.SIGNATURE, StringUtils.join(output, " ")));
				Hypothesis hypothesis = Answers.timeDeduction(this, output);
				if (config.isDebug()) {
					//Logger.message(String.format("*** Info  (%s): found hypothesis: %s", Logger.SIGNATURE, StringUtils.join(hypothesis.getHypotheses(), " ")));
					for(Clause c : hypothesis.getHypotheses()) {
						Logger.message(String.format("*** Info  (%s): hypothesis clause: %s", Logger.SIGNATURE, c.toString()));
					}
				}
				builder.put(entry.getKey(), new Answer.Builder(this).setHypothesis(hypothesis).build());
			}
		} else
			builder.put(new Values(), new Answer.Builder(this).build());
		return result;
	}

	@Override
		public String toString() {
			return "Grounding [\n  covered=" + Arrays.toString(covered) + ",\n  delta=" + Arrays.toString(delta) + ",\n  facts=" + facts + ",\n  generalisation="
				+ Arrays.toString(generalisation) + ",\n  kernel=" + Arrays.toString(kernel) + ",\n  model=" + Arrays.toString(model) + ",\n  table=" + table
				+ ",\n  problem=" + problem + ",\n  uncovered=" + Arrays.toString(uncovered) + "\n]";
		}

}
