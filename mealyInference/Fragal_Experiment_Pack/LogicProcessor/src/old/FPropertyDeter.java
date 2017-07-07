package old;

import java.util.HashMap;
import java.util.Map;

import br.usp.icmc.ffsm.FFSM;
import br.usp.icmc.ffsm.FTransition;
import br.usp.icmc.fsm.common.FiniteStateMachine;
import br.usp.icmc.fsm.common.State;
import br.usp.icmc.fsm.common.Transition;

public class FPropertyDeter {

	public String getZ3Property(FFSM ffsm){
		
		//read a feature model first!!!
		//get features , tree, etc.
		
		String header = "(define-sort Feature () Bool)\n";
		/*
		header = header.concat("(declare-const f1 Feature)\n");
		header = header.concat("(declare-const f2 Feature)\n");
		header = header.concat("(declare-const f3 Feature)\n\n");
		
		header = header.concat("; assert feature root as true \n");
		header = header.concat("(assert f1)\n");
		header = header.concat("(assert (and\n");
		header = header.concat("   (= (or f2 f3) f1)\n");
		header = header.concat("   (not (and f2 f3))\n");
		header = header.concat("))\n\n");
		*/
		
		header = header.concat("(declare-const f1 Feature)\n");
		header = header.concat("(declare-const f2 Feature)\n");
		header = header.concat("(declare-const f3 Feature)\n");
		header = header.concat("(declare-const f4 Feature)\n");
		header = header.concat("(declare-const f5 Feature)\n\n");
		
		header = header.concat("; assert feature root as true \n");
		header = header.concat("(assert f1)\n");
		header = header.concat("(assert (and\n");
		header = header.concat("   (= (or f2 f3 f4) f1)\n");
		header = header.concat("   (not (and f2 f3))\n");
		header = header.concat("   (not (and f2 f4))\n");
		header = header.concat("   (not (and f3 f4))\n");
		header = header.concat("   (=> f5 f1)\n");		
		header = header.concat("))\n\n");
		
		/*		
		String clause = "";
								
		//set transitions 
		for(FTransition t: ffsm.getFTransitions()){
			//clause = clause.concat("(assert (Transition "+ t+"\n");
			clause = clause.concat("(assert (Transition "+
					"))\n");
		}
			
		clause = clause.concat("))\n");
		header = header.concat(clause);
		*/
		return header;
	}
}
