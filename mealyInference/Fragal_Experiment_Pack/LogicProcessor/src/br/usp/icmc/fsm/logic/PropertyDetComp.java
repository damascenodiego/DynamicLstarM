package br.usp.icmc.fsm.logic;

import java.util.HashMap;
import java.util.Map;

import br.usp.icmc.fsm.common.FiniteStateMachine;
import br.usp.icmc.fsm.common.State;
import br.usp.icmc.fsm.common.Transition;

public class PropertyDetComp {

	public String getZ3Property(FiniteStateMachine fsm){
		
		String header = "(define-sort State () Int)\n";
		header = header.concat("(define-sort Input () Int)\n");
		header = header.concat("(define-sort Output () Int)\n\n");
		header = header.concat("(declare-fun NextState (State Input) State)\n");
		header = header.concat("(declare-fun Domain (State Input) State)\n");
		header = header.concat("(declare-fun Transition (State Input Output State) Bool)\n\n");
		header = header.concat("; initialize transitions\n");
		header = header.concat("(assert (forall ((x State) (i Input) (o Output) (y State)) (\n");
		header = header.concat("  => (Transition x i o y)\n");
		header = header.concat("   (and (= y (NextState x i)) (= i (Domain x i)) ))))\n\n");
		header = header.concat("; deterministic property\n");
		header = header.concat("(assert (forall ((x State) (i Input) (y State) (z State)\n");
		header = header.concat("    (o1 Output) (o2 Output)) (\n");
		header = header.concat("  => (and (= y (NextState x i)) (= z (NextState x i))\n");
		header = header.concat("          (Transition x i o1 y) (Transition x i o2 z))\n");
		header = header.concat("     (and (= y z) (= o1 o2))\n");
		header = header.concat("  ))) \n\n");
		header = header.concat("; the mapping is handled by java implementation\n");
		String clause = "";
			
		//map states, inputs and outputs to integers
		int i = 1;
		Map<State, Integer> map_state = new HashMap<State, Integer>();
		for(State s: fsm.getStates()){
			map_state.put(s, i);
			i++;
		}	
		i = 1;
		Map<String, Integer> map_input = new HashMap<String, Integer>();
		for(String p: fsm.getInputAlphabet()){
			map_input.put(p, i);
			i++;
		}
		i = 1;
		Map<String, Integer> map_output = new HashMap<String, Integer>();
		for(String o: fsm.getOutputAlphabet()){
			map_output.put(o, i);
			i++;
		}
			
		//set transitions 
		for(Transition t: fsm.getTransitions()){
			//clause = clause.concat("(assert (Transition "+ t+"\n");
			clause = clause.concat("(assert (Transition "+
					map_state.get(t.getIn())+" "+
					map_input.get(t.getInput())+" "+
					map_output.get(t.getOutput())+" "+
					map_state.get(t.getOut())+"))\n");
		}
		clause = clause.concat("(check-sat)\n");
		clause = clause.concat("(eval (and \n");
		for(State s: fsm.getStates()){
			for(String p: fsm.getInputAlphabet()){
				clause = clause.concat("  (=  "+
						map_input.get(p)+" (Domain "+
						map_state.get(s)+ " " +
						map_input.get(p)+"))\n");
			}
		}			
		clause = clause.concat("))\n");
		header = header.concat(clause);
		
		return header;
	}
}
