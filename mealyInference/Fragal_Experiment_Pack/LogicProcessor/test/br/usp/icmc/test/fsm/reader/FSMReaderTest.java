package br.usp.icmc.test.fsm.reader;

import static org.junit.Assert.fail;

import java.io.BufferedReader;
import java.io.File;
import java.io.InputStreamReader;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.Map;

import org.junit.Test;

import br.usp.icmc.fsm.common.FiniteStateMachine;
import br.usp.icmc.fsm.common.State;
import br.usp.icmc.fsm.common.Transition;
import br.usp.icmc.fsm.logic.PropertyDetComp;
import br.usp.icmc.fsm.logic.PropertyInitCon;
import br.usp.icmc.fsm.logic.PropertyMinimal;
import br.usp.icmc.fsm.reader.FsmModelReader;

public class FSMReaderTest 
{
	@Test
	public void test003()
	{
		try
		{
			File file = new File("./fsm/fsm2.txt");
			FsmModelReader reader = new FsmModelReader(file, true);
			FiniteStateMachine fsm = reader.getFsm();
			
			//headers for minimal
			System.out.println(fsm.getTransitions());
			PropertyMinimal property = new PropertyMinimal();
			String prop = property.getZ3Property(fsm);
				
			// print stm2 file and execute
			String path = "./fsm/minimal.smt2";
			fsm.print_file(prop, path);
			
			String[] commands = {"./fsm/z3","./fsm/minimal.smt2"};
			String result = fsm.getProcessOutput(commands);
			//System.out.println(result);
			String[] outs = result.split("\n");
										
			System.out.println("Is the FSM Minimal?");			
			if(outs[0].equals("sat")){
				System.out.println("true");			
			}else System.out.println("unsat");
		}
		catch(Exception ex)
		{
			ex.printStackTrace();
			fail();
		}		
	}
	
	@Test
	public void test002()
	{
		try
		{
			File file = new File("./fsm/fsm1.txt");
			FsmModelReader reader = new FsmModelReader(file, true);
			FiniteStateMachine fsm = reader.getFsm();
			
			//headers for innitially connected
			System.out.println(fsm.getTransitions());
			PropertyInitCon property = new PropertyInitCon();
			String prop = property.getZ3Property(fsm);
				
			// print stm2 file and execute
			String path = "./fsm/init_con.smt2";
			fsm.print_file(prop, path);
			
			String[] commands = {"./fsm/z3","./fsm/init_con.smt2"};
			String result = fsm.getProcessOutput(commands);
			//System.out.println(result);
			String[] outs = result.split("\n");
										
			System.out.println("Is the FSM Innitially Connected?");			
			if(outs[0].equals("sat")){
				System.out.println(outs[1]);			
			}else System.out.println("unsat");
		}
		catch(Exception ex)
		{
			ex.printStackTrace();
			fail();
		}		
	}
	
	@Test
	public void test001()
	{
		try
		{
			File file = new File("./fsm/fsm1.txt");
			FsmModelReader reader = new FsmModelReader(file, true);
			FiniteStateMachine fsm = reader.getFsm();
			
			//headers for deterministic and complete
			System.out.println(fsm.getTransitions());
			PropertyDetComp property = new PropertyDetComp();
			String prop = property.getZ3Property(fsm);
				
			// print stm2 file and execute
			String path = "./fsm/deter_comp.smt2";
			fsm.print_file(prop, path);
			
			String[] commands = {"./fsm/z3","./fsm/deter_comp.smt2"};
			String result = fsm.getProcessOutput(commands);
			//System.out.println(result);
			String[] outs = result.split("\n");
			
			System.out.println("Is the FSM deterministic?");
			//System.out.println(outs[0]);
			if(outs[0].equals("sat")){
				System.out.println("true");			
			}else System.out.println("false");	
			System.out.println("Is the FSM complete?");
			System.out.println(outs[1]);			
		}
		catch(Exception ex)
		{
			ex.printStackTrace();
			fail();
		}		
	}	
	
	
	@Test
	public void test00()
	{
		try
		{
			File file = new File("./fsm/fsm1.txt");
			FsmModelReader reader = new FsmModelReader(file, true);
			FiniteStateMachine fsm = reader.getFsm();
			
			System.out.println(fsm.getTransitions());
			//System.out.println(fsm.nextState(current, inputsymbol));
			//for every state there must be an transitions that uses every input
			//FSM={S,s0,I,O,D,delta,lambda}
			//D=SXI then is complete
			String clause = "";
			
			//checking innitially connected
			
			
			//checking complete
			Boolean isComplete = true;
			complete: for(State s: fsm.getStates()){
				for(String i: fsm.getInputAlphabet()){
					if (fsm.nextState(s, i) == null){
						isComplete = false;
						System.out.println("Not "+ s +" " +i);
						System.out.println("Not complete!");
						break complete;
					}else{
						clause = "" +s+ " & " +i+  " => "+ fsm.nextState(s, i);
						System.out.println(clause);
					}
				}
			}
			if(isComplete) System.out.println("The FSM is complete!");
			
			/*
			//checking deterministic
			//forall x,y,z in S and i in I 
			//delta x i = y and delta x i = z 
			//=> y = z
			String formula = "delta x i = y";
			Boolean isDeterministic = true;
			deter: for(State s: fsm.getStates()){				
				for(String i: fsm.getInputAlphabet()){
					if (fsm.nextState(s, i) == null){
						isDeterministic = false;
						System.out.println("Not "+ s +" " +i);
						System.out.println("Not complete!");
						break deter;
					}else{
						clause = "" +s+ " & " +i+  " => "+ fsm.nextState(s, i);
						System.out.println(clause);
					}
				}
			}
			if(isDeterministic) System.out.println("The FSM is complete!");
			*/
			
		}
		catch(Exception ex)
		{
			ex.printStackTrace();
			fail();
		}		
	}	
}
