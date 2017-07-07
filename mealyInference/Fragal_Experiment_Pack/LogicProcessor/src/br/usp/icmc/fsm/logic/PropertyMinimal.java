package br.usp.icmc.fsm.logic;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.Map;

import br.usp.icmc.fsm.common.FiniteStateMachine;
import br.usp.icmc.fsm.common.State;
import br.usp.icmc.fsm.common.Transition;

public class PropertyMinimal {

	public String getZ3Property(FiniteStateMachine fsm){
		
		String header = "(define-sort State () Int)\n";
		header = header.concat("(define-sort Input () Int)\n");
		header = header.concat("(define-sort Output () Int)\n\n");
		header = header.concat("(declare-fun NextState (State Input) State)\n");
		header = header.concat("(declare-fun TheOutput (State Input) Output)\n");
		header = header.concat("(declare-fun Transition (State Input Output State) Bool)\n");
		header = header.concat("(declare-fun Separe (State State Input) Bool)\n\n");
		header = header.concat("; initialize transitions\n");
		header = header.concat("(assert (forall ((x State) (i Input) (o Output) (y State)) (\n");
		header = header.concat("  => (Transition x i o y)\n");
		header = header.concat("    (and (= y (NextState x i)) (= o (TheOutput x i)) ))))\n\n");
		header = header.concat("; the minimal property\n");
		header = header.concat("(assert (forall ((x1 State) (y1 State) \n");
		header = header.concat("    (i1 Input) (i2 Input) ) ( \n");
		header = header.concat("  or\n");
		header = header.concat("     ;(chain 1)\n");
		header = header.concat("     (=> (and \n");
		header = header.concat("        (= false (Separe x1 y1 i1)) \n");
		header = header.concat("        (not (= x1 y1)) \n");
		header = header.concat("        (not (= i1 i2))  \n");
		header = header.concat("     )  \n");
		header = header.concat("     (= true (Separe x1 y1 i2))\n");
		header = header.concat("     ) \n");	
		
		String extra = "";
		int stn;
		for(stn=2; stn<fsm.getNumberOfStates();stn++){
			extra = extra.concat("     ;(chain "+stn+")\n");
			extra = extra.concat("     (forall (");
			for(int j=2; j<=stn;j++){
				extra = extra.concat("(x"+j+" State)(y"+j+" State)");
			}
			extra = extra.concat(")\n");
			extra = extra.concat("       (=> (and \n");
			extra = extra.concat("              ; base\n");
			extra = extra.concat("              (= false (Separe x1 y1 i1)) \n");
			extra = extra.concat("              (= false (Separe x1 y1 i2)) \n");
			extra = extra.concat("              (not (= x1 y1))  \n");
			extra = extra.concat("              (not (= i1 i2)) \n");
			for(int j=2; j<stn;j++){
				extra = extra.concat("              ; block "+j+"\n");
				extra = extra.concat("              (= x"+j+" (NextState x"+(j-1)+" i1))\n");
				extra = extra.concat("              (= y"+j+" (NextState y"+(j-1)+" i1)) \n");
				extra = extra.concat("              (not (= x"+j+" y"+stn+")) \n");
				extra = extra.concat("              (not (and (= x"+(j-1)+" x"+j+") (= y"+(j-1)+" y"+j+"))) \n");
				extra = extra.concat("	      		(= false (Separe x"+j+" y"+j+" i1)) \n");
				extra = extra.concat("              (= false (Separe x"+j+" y"+j+" i2))\n");
			}			
			extra = extra.concat("              ; block "+stn+"\n");
			extra = extra.concat("              (= x"+stn+" (NextState x"+(stn-1)+" i1))\n");
			extra = extra.concat("              (= y"+stn+" (NextState y"+(stn-1)+" i1)) \n");
			extra = extra.concat("              (not (= x"+stn+" y"+stn+")) \n");
			extra = extra.concat("              (not (and (= x"+(stn-1)+" x"+stn+") (= y"+(stn-1)+" y"+stn+"))) \n");
			extra = extra.concat("           )\n");
			extra = extra.concat("           (=> (and \n");
			extra = extra.concat("               (= false (Separe x"+stn+" y"+stn+" i1)) \n");
			extra = extra.concat("               (not (= x"+stn+" y"+stn+")) \n");
			extra = extra.concat("               (not (= i1 i2)) \n");
			extra = extra.concat("             )  \n");
			extra = extra.concat("             (= true (Separe x"+stn+" y"+stn+" i2)) \n");
			extra = extra.concat("           )  \n");
			extra = extra.concat("       )\n");
			extra = extra.concat("     )\n");							
		}
		extra = extra.concat("  )))\n");	
		
		header = header.concat(extra);
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
		
		// set separating pairs
		ArrayList<State> stx1 = (ArrayList<State>) fsm.getStates().clone();
		ArrayList<State> stx2 = (ArrayList<State>) fsm.getStates().clone();
		for(State s1: stx1){	
			stx2.remove(s1);
			for(State s2: stx2){					
				for(String in: fsm.getInputAlphabet()){	
					String separate = "false";
					if(fsm.isDefinedSeq(in, s1) && fsm.isDefinedSeq(in, s2)){
						if(!fsm.nextOutput(s1, in).equals(fsm.nextOutput(s2, in))){
							separate= "true";
						}							
					}
					clause = clause.concat("(assert (= "+
							separate+" (Separe "+
							map_state.get(s1)+" "+
							map_state.get(s2)+" "+
							map_input.get(in)+" "+
							")))\n");						
				}
			}
			
		}					
		clause = clause.concat("(check-sat)\n");
		header = header.concat(clause);
		
		return header;
	}
}
