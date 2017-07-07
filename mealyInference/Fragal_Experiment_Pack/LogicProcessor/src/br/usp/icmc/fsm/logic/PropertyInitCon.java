package br.usp.icmc.fsm.logic;

import java.util.HashMap;
import java.util.Map;

import br.usp.icmc.fsm.common.FiniteStateMachine;
import br.usp.icmc.fsm.common.State;
import br.usp.icmc.fsm.common.Transition;

public class PropertyInitCon {

	public String getZ3Property(FiniteStateMachine fsm){
		
		String header = "(define-sort State () Int)\n";
		header = header.concat("(define-sort Input () Int)\n");
		header = header.concat("(define-sort Output () Int)\n\n");
		header = header.concat("(declare-fun NextState (State Input) State)\n");
		header = header.concat("(declare-fun Path (State State) State)\n");
		header = header.concat("(declare-fun Transition (State Input Output State) Bool)\n");
		header = header.concat("(declare-var initialState State)\n\n");
		header = header.concat("; initialize transitions\n");
		header = header.concat("(assert (forall ((x State) (i Input) (o Output) (y State)) (\n");
		header = header.concat("  => (and (Transition x i o y) (not (= x y)) )\n");
		header = header.concat("    (and (= y (NextState x i)) (= y (Path x y)) ))))\n\n");
		header = header.concat("; find all paths\n");
		header = header.concat("(assert (forall ((s1 State) (s2 State) (s3 State))\n");
		header = header.concat("   (=> (and (= s2 (Path s1 s2)) (= s3 (Path s2 s3))) \n");
		header = header.concat("    (= s3 (Path s1 s3)) ))) \n\n");
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
		clause = clause.concat("(assert (= initialState "+map_state.get(fsm.getInitialState())+"))\n");
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
			if(!s.equals(fsm.getInitialState()))
				clause = clause.concat("  (=  "+
					map_state.get(s)+" (Path initialState "+					
					map_state.get(s)+"))\n");			
		}			
		clause = clause.concat("))\n");
		header = header.concat(clause);
		
		return header;
	}
}
