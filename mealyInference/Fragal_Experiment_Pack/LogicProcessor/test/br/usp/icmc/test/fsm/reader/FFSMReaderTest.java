package br.usp.icmc.test.fsm.reader;

import static org.junit.Assert.fail;

import java.io.BufferedReader;
import java.io.File;
import java.io.IOException;
import java.io.InputStreamReader;
import java.util.ArrayList;
import java.util.Date;
import java.util.HashMap;
import java.util.Map;
import java.util.Random;
import java.util.logging.Level;
import java.util.logging.Logger;

import logger.FFSMLogger;
import logger.MyLogger;
import logger.MyLoggerFFSM;
import old.FPropertyComplete;
import old.FPropertyDeter;

import org.junit.Test;

import br.ups.icmc.increase.FFSMModel;
import br.ups.icmc.increase.FFeatureModel;
import br.ups.icmc.increase.FsmModel;
import br.usp.icmc.ffsm.FFSM;
import br.usp.icmc.ffsm.FState;
import br.usp.icmc.ffsm.FTransition;
import br.usp.icmc.fsm.common.FileHandler;
import br.usp.icmc.fsm.common.FiniteStateMachine;
import br.usp.icmc.fsm.common.State;
import br.usp.icmc.fsm.common.Transition;
import br.usp.icmc.fsm.logic.FFSMProperties;
import br.usp.icmc.fsm.logic.FSMProperties;
import br.usp.icmc.fsm.logic.PropertyDetComp;
import br.usp.icmc.fsm.logic.PropertyInitCon;
import br.usp.icmc.fsm.logic.PropertyMinimal;
import br.usp.icmc.fsm.reader.FFSMModelReader;
import br.usp.icmc.fsm.reader.FsmModelReader;

public class FFSMReaderTest 
{	
	//private static Logger logger = Logger.getAnonymousLogger();
	private final static Logger LOGGER = Logger.getLogger(Logger.GLOBAL_LOGGER_NAME);
	
	//public static Logger getLogger() {
	//	return logger;
	//}
	
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
	public void test001_deterministic()
	{
		try
		{
			File file = new File("./ffsm/ffsm2.txt");
			FFSMModelReader reader = new FFSMModelReader(file);
			FFSM ffsm = reader.getFFSM();
			//System.out.println(ffsm.getFInitialState().getStateName());
			//System.out.println(ffsm.getFInitialState().getCondition());
			//System.out.println(ffsm.getNumberOfFStates());
			//System.out.println(ffsm.getNumberOfFTransitions());			
			System.out.println("Conditional States "+ffsm.getFStates());
			System.out.println("Conditional Transitions "+ffsm.getFTransitions());
			System.out.println("Conditional Inputs "+ffsm.getInputAlphabet());
			System.out.println("Outputs "+ffsm.getOutputAlphabet());
			//System.out.println(ffsm.getFStates().get(1).getOut());
			//for(FTransition ft : ffsm.getFTransitions()){
			//	System.out.println(ft);
			//}
			
			/*; feature model f1 = root
			;     f1
			;    /_\
			;   /  \
			;  f2  f3
			; exp= ((f2||f3 <=> f1) && !(f2&&f3))
			*/
			FPropertyDeter property = new FPropertyDeter();
			String prop = property.getZ3Property(ffsm);
			boolean deterministic = true;
			int count = 0;
			
			deter:for(FState fst : ffsm.getFStates()){
				System.out.println("Conditional State "+fst);
				ArrayList<FTransition> stx1 = (ArrayList<FTransition>) fst.getOut().clone();
				ArrayList<FTransition> stx2 = (ArrayList<FTransition>) fst.getOut().clone();				
				for(FTransition ft: stx1){
					System.out.println("		"+ft);
					stx2.remove(ft);					
					for(FTransition ft2 : stx2){
						if(ft.getCInput().getIn().equals(ft2.getCInput().getIn())){
							count++;
							String clause = "";
							System.out.println("		"+ft2);
							clause = clause.concat("(assert (and \n");
							clause = clause.concat("    (and "+
									ft.getSource().getCondition()+" "+
									ft.getCInput().getCond()+" "+
									ft.getTarget().getCondition()+")\n");
							clause = clause.concat("    (and "+
									ft2.getSource().getCondition()+" "+
									ft2.getCInput().getCond()+" "+
									ft2.getTarget().getCondition()+")\n");
							clause = clause.concat("))\n");
							clause = clause.concat("(check-sat)");
							String prop_aux = prop.concat(clause);
							// print stm2 file and execute
							String path = "./ffsm/f_deter_"+count+".smt2";
							FileHandler fh = new FileHandler();
							fh.print_file(prop_aux, path);
							
							String[] commands = {"./ffsm/z3","./ffsm/f_deter_"+count+".smt2"};
							String result = fh.getProcessOutput(commands);
							//System.out.println(result);
							String[] outs = result.split("\n");
							
							System.out.println("Is the FFSM still deterministic?");
							//System.out.println(outs[0]);
							if(outs[0].equals("unsat")){
								System.out.println("true");								
							}else{
								System.out.println("false");
								deterministic = false; 
								break deter;
							}
						}						
					}					
				}
			}
			System.out.println("RESULT: Is the FFSM deterministic?");
			System.out.println(deterministic);
			
		}
		catch(Exception ex)
		{
			ex.printStackTrace();
			fail();
		}		
	}	
	
	@Test
	public void test002_ndeterministic()
	{
		try
		{
			File file = new File("./ffsm/ffsm_ndeter.txt");
			FFSMModelReader reader = new FFSMModelReader(file);
			FFSM ffsm = reader.getFFSM();						
			System.out.println("Conditional States "+ffsm.getFStates());
			System.out.println("Conditional Transitions "+ffsm.getFTransitions());
			System.out.println("Conditional Inputs "+ffsm.getInputAlphabet());
			System.out.println("Outputs "+ffsm.getOutputAlphabet());
			
			FPropertyDeter property = new FPropertyDeter();
			String prop = property.getZ3Property(ffsm);
			boolean deterministic = true;
			int count = 0;
			
			deter:for(FState fst : ffsm.getFStates()){
				System.out.println("Conditional State "+fst);
				ArrayList<FTransition> stx1 = (ArrayList<FTransition>) fst.getOut().clone();
				ArrayList<FTransition> stx2 = (ArrayList<FTransition>) fst.getOut().clone();				
				for(FTransition ft: stx1){
					System.out.println("		"+ft);
					stx2.remove(ft);					
					for(FTransition ft2 : stx2){
						if(ft.getCInput().getIn().equals(ft2.getCInput().getIn())){
							count++;
							String clause = "";
							clause = clause.concat("(assert "+ft.getSource().getCondition()+")\n");
							System.out.println("		"+ft2);
							clause = clause.concat("(assert (and \n");
							clause = clause.concat("    (and "+									
									ft.getCInput().getCond()+" "+
									ft.getTarget().getCondition()+")\n");
							clause = clause.concat("    (and "+									
									ft2.getCInput().getCond()+" "+
									ft2.getTarget().getCondition()+")\n");
							clause = clause.concat("))\n");
							clause = clause.concat("(check-sat)");
							String prop_aux = prop.concat(clause);
							// print stm2 file and execute
							String path = "./ffsm/f_deter_"+count+".smt2";
							FileHandler fh = new FileHandler();
							fh.print_file(prop_aux, path);
							
							String[] commands = {"./ffsm/z3","./ffsm/f_deter_"+count+".smt2"};
							String result = fh.getProcessOutput(commands);
							//System.out.println(result);
							String[] outs = result.split("\n");
							
							System.out.println("Is the FFSM still deterministic?");
							//System.out.println(outs[0]);
							if(outs[0].equals("unsat")){
								System.out.println("true");								
							}else{
								System.out.println("false");
								deterministic = false; 
								break deter;
							}
						}						
					}					
				}
			}
			System.out.println("RESULT: Is the FFSM deterministic?");
			System.out.println(deterministic);
			
		}
		catch(Exception ex)
		{
			ex.printStackTrace();
			fail();
		}		
	}	
	
	@Test
	public void test003_deterministic()
	{
		try
		{
			File file = new File("./ffsm/ffsm_deter.txt");
			FFSMModelReader reader = new FFSMModelReader(file);
			FFSM ffsm = reader.getFFSM();						
			System.out.println("Conditional States "+ffsm.getFStates());
			System.out.println("Conditional Transitions "+ffsm.getFTransitions());
			System.out.println("Conditional Inputs "+ffsm.getInputAlphabet());
			System.out.println("Outputs "+ffsm.getOutputAlphabet());
			
			FPropertyDeter property = new FPropertyDeter();
			String prop = property.getZ3Property(ffsm);
			boolean deterministic = true;
			int count = 0;
			
			deter:for(FState fst : ffsm.getFStates()){
				System.out.println("Conditional State "+fst);
				ArrayList<FTransition> stx1 = (ArrayList<FTransition>) fst.getOut().clone();
				ArrayList<FTransition> stx2 = (ArrayList<FTransition>) fst.getOut().clone();				
				for(FTransition ft: stx1){
					System.out.println("		"+ft);
					stx2.remove(ft);					
					for(FTransition ft2 : stx2){
						if(ft.getCInput().getIn().equals(ft2.getCInput().getIn())){
							count++;
							String clause = "";
							clause = clause.concat("(assert "+ft.getSource().getCondition()+")\n");
							System.out.println("		"+ft2);
							clause = clause.concat("(assert (and \n");
							clause = clause.concat("    (and "+									
									ft.getCInput().getCond()+" "+
									ft.getTarget().getCondition()+")\n");
							clause = clause.concat("    (and "+									
									ft2.getCInput().getCond()+" "+
									ft2.getTarget().getCondition()+")\n");
							clause = clause.concat("))\n");
							clause = clause.concat("(check-sat)");
							String prop_aux = prop.concat(clause);
							// print stm2 file and execute
							String path = "./ffsm/f_deter_"+count+".smt2";
							FileHandler fh = new FileHandler();
							fh.print_file(prop_aux, path);
							
							String[] commands = {"./ffsm/z3","./ffsm/f_deter_"+count+".smt2"};
							String result = fh.getProcessOutput(commands);
							//System.out.println(result);
							String[] outs = result.split("\n");
							
							System.out.println("Is the FFSM still deterministic?");
							//System.out.println(outs[0]);
							if(outs[0].equals("unsat")){
								System.out.println("true");								
							}else{
								System.out.println("false");
								deterministic = false; 
								break deter;
							}
						}						
					}					
				}
			}
			System.out.println("RESULT: Is the FFSM deterministic?");
			System.out.println(deterministic);
			
		}
		catch(Exception ex)
		{
			ex.printStackTrace();
			fail();
		}		
	}	
	
	@Test
	public void test005_ncomplete()
	{
		try
		{
			File file = new File("./ffsm/ffsm_ncomplete.txt");
			FFSMModelReader reader = new FFSMModelReader(file);
			FFSM ffsm = reader.getFFSM();						
			System.out.println("Conditional States "+ffsm.getFStates());
			System.out.println("Conditional Transitions "+ffsm.getFTransitions());
			System.out.println("Conditional Inputs "+ffsm.getInputAlphabet());
			System.out.println("Outputs "+ffsm.getOutputAlphabet());
			
			FPropertyComplete property = new FPropertyComplete();
			String prop = property.getZ3Property(ffsm);
			boolean complete = true;
			int count = 0;
			
			complete:for(FState fst : ffsm.getFStates()){
				System.out.println("Conditional State "+fst);
				//ArrayList<FTransition> stx1 = (ArrayList<FTransition>) fst.getOut().clone();
				//ArrayList<FTransition> stx2 = (ArrayList<FTransition>) fst.getOut().clone();
				for(String in: ffsm.getInputAlphabet()){
					System.out.println("		"+in);
					count++;
					String clause = "";
					clause = clause.concat("(assert "+fst.getCondition()+")\n");
					clause = clause.concat("(assert (and \n");
					boolean in_found = false;
					for(FTransition ft: fst.getOut()){							
						if(ft.getCInput().getIn().equals(in)){
							in_found = true;
							clause = clause.concat("    (not (and "+									
									ft.getCInput().getCond()+" "+
									ft.getTarget().getCondition()+"))\n");
						}						
					}
					if(in_found){
						clause = clause.concat("))\n");
						clause = clause.concat("(check-sat)");
						String prop_aux = prop.concat(clause);
						// print stm2 file and execute
						String path = "./ffsm/f_comp_"+count+".smt2";
						FileHandler fh = new FileHandler();
						fh.print_file(prop_aux, path);
						
						String[] commands = {"./ffsm/z3","./ffsm/f_comp_"+count+".smt2"};
						String result = fh.getProcessOutput(commands);
						//System.out.println(result);
						String[] outs = result.split("\n");
						
						System.out.println("Is the FFSM still complete?");
						//System.out.println(outs[0]);
						if(outs[0].equals("unsat")){
							System.out.println("true");								
						}else{
							System.out.println("false");
							complete = false; 
							break complete;
						}						
					}else{
						complete = false;
						System.out.println("Is the FFSM still complete?");
						System.out.println(complete);						 
						break complete;						
					}
				}
			}
			System.out.println("RESULT: Is the FFSM complete?");
			System.out.println(complete);
			
		}
		catch(Exception ex)
		{
			ex.printStackTrace();
			fail();
		}		
	}	
	
	@Test
	public void test004_complete()
	{
		try
		{
			File file = new File("./ffsm/ffsm_complete.txt");
			FFSMModelReader reader = new FFSMModelReader(file);
			FFSM ffsm = reader.getFFSM();						
			System.out.println("Conditional States "+ffsm.getFStates());
			System.out.println("Conditional Transitions "+ffsm.getFTransitions());
			System.out.println("Conditional Inputs "+ffsm.getInputAlphabet());
			System.out.println("Outputs "+ffsm.getOutputAlphabet());
			
			FPropertyComplete property = new FPropertyComplete();
			String prop = property.getZ3Property(ffsm);
			boolean complete = true;
			int count = 0;
			
			complete:for(FState fst : ffsm.getFStates()){
				System.out.println("Conditional State "+fst);
				//ArrayList<FTransition> stx1 = (ArrayList<FTransition>) fst.getOut().clone();
				//ArrayList<FTransition> stx2 = (ArrayList<FTransition>) fst.getOut().clone();
				for(String in: ffsm.getInputAlphabet()){
					System.out.println("		"+in);
					count++;
					String clause = "";
					clause = clause.concat("(assert "+fst.getCondition()+")\n");
					clause = clause.concat("(assert (and \n");
					boolean in_found = false;
					for(FTransition ft: fst.getOut()){							
						if(ft.getCInput().getIn().equals(in)){
							in_found = true;
							clause = clause.concat("    (not (and "+									
									ft.getCInput().getCond()+" "+
									ft.getTarget().getCondition()+"))\n");
						}						
					}
					if(in_found){
						clause = clause.concat("))\n");
						clause = clause.concat("(check-sat)");
						String prop_aux = prop.concat(clause);
						// print stm2 file and execute
						String path = "./ffsm/f_comp_"+count+".smt2";
						FileHandler fh = new FileHandler();
						fh.print_file(prop_aux, path);
						
						String[] commands = {"./ffsm/z3","./ffsm/f_comp_"+count+".smt2"};
						String result = fh.getProcessOutput(commands);
						//System.out.println(result);
						String[] outs = result.split("\n");
						
						System.out.println("Is the FFSM still complete?");
						//System.out.println(outs[0]);
						if(outs[0].equals("unsat")){
							System.out.println("true");								
						}else{
							System.out.println("false");
							complete = false; 
							break complete;
						}						
					}else{
						complete = false;
						System.out.println("Is the FFSM still complete?");
						System.out.println(complete);						 
						break complete;						
					}
				}
			}
			System.out.println("RESULT: Is the FFSM complete?");
			System.out.println(complete);
			
		}
		catch(Exception ex)
		{
			ex.printStackTrace();
			fail();
		}		
	}	
	
	@Test
	public void test007_init_connect()
	{
		FFSMProperties p = new FFSMProperties("ffsm");
		String header = p.read_XML_FeatureModel("./ffsm/example_fm.xml");
		String file = "./ffsm/ffsm_init_connect.txt";
		try {
			if(p.set_checkFFSM(file, header)){
				System.out.println("Invalid FFSM!!!");
				return;
			}
		} catch (InterruptedException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		} catch (IOException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
		boolean is = p.is_initially_connected();
		System.out.println("\nIs the FFSM initially connected?");
		System.out.println(is);
	}
	
	@Test
	public void test008_minimal()
	{
		FFSMProperties p = new FFSMProperties("ffsm");
		String header = p.read_XML_FeatureModel("./ffsm/example_fm.xml");		
		String file = "./ffsm/ffsm_minimal.txt";		
		try {
			if(p.set_checkFFSM(file, header)){
				System.out.println("Invalid FFSM!!!");
				return;
			}
		} catch (InterruptedException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		} catch (IOException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
		
		boolean is = p.is_minimal();
		System.out.println("\nIs the FFSM minimal?");
		System.out.println(is);
	}
	
	@Test
	public void test009_all()
	{
		FFSMProperties p = new FFSMProperties("ffsm");
		System.out.println("Reading Feature Model (.xml)");
		String header = p.read_XML_FeatureModel("./ffsm/example_fm.xml");
		
		String file = "./ffsm/ffsm_all_properties.txt";
		try {
			if(p.set_checkFFSM(file, header)){
				System.out.println("Invalid FFSM!!!");
				return;
			}
		} catch (InterruptedException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		} catch (IOException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
		
		System.out.println("\nIdentify Deterministic...\n");
		boolean is1 = p.is_deterministic();	
		System.out.println("\nIdentify Complete...\n");
		boolean is2 = p.is_complete();
		System.out.println("\nIdentify Initially Connected...\n");
		boolean is3 = p.is_initially_connected();
		System.out.println("\nIdentify Minimal...\n");
		boolean is4 = p.is_minimal();
		
		System.out.println("\nIs the FFSM deterministic?");
		System.out.println(is1);
		System.out.println("\nIs the FFSM complete?");
		System.out.println(is2);
		System.out.println("\nIs the FFSM initially connected?");
		System.out.println(is3);
		System.out.println("\nIs the FFSM minimal?");
		System.out.println(is4);
	}
	
	@Test
	public void test010_XMLReader()
	{
		FFSMProperties p = new FFSMProperties("ffsm");
		String header = p.read_XML_FeatureModel("./ffsm/agm_fm.xml");
	}
	
	@Test
	public void test011_audiocar_all()
	{
		FFSMProperties p = new FFSMProperties("audiocar");
		System.out.println("Reading Feature Model (.xml)");
		String header = p.read_XML_FeatureModel("./audiocar/fm_audiocar.xml");
		
		String file = "./audiocar/ffsm_audiocar.txt";
		try {
			if(p.set_checkFFSM(file, header)){
				System.out.println("Invalid FFSM!!!");
				return;
			}
		} catch (InterruptedException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		} catch (IOException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
		
		System.out.println("\nIdentify Deterministic...\n");
		boolean is1 = p.is_deterministic();	
		System.out.println("\nIdentify Complete...\n");
		boolean is2 = p.is_complete();
		System.out.println("\nIdentify Initially Connected...\n");
		boolean is3 = p.is_initially_connected();
		System.out.println("\nIdentify Minimal...\n");
		boolean is4 = p.is_minimal();
		
		System.out.println("\nIs the FFSM deterministic?");
		System.out.println(is1);
		System.out.println("\nIs the FFSM complete?");
		System.out.println(is2);
		System.out.println("\nIs the FFSM initially connected?");
		System.out.println(is3);
		System.out.println("\nIs the FFSM minimal?");
		System.out.println(is4);
	}
	
	@Test
	public void test011_agm_all()
	{
		String folder = "agm";
		FFSMProperties p = new FFSMProperties(folder);
		//FFSMProperties p = new FFSMProperties(folder, true, true);
		System.out.println("Reading Feature Model (.xml)");
		String header = p.read_XML_FeatureModel("./"+folder+"/fm_agm.xml");
		
		String file = "./"+folder+"/ffsm_agm.txt";
		try {
			if(!p.set_checkFFSM(file, header)){
				System.out.println("Invalid FFSM!!!");
				return;
			}
		} catch (InterruptedException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		} catch (IOException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
		
		System.out.println("\nIdentify Deterministic...\n");
		boolean is1 = p.is_deterministic();	
		System.out.println("\nIdentify Complete...\n");
		boolean is2 = p.is_complete();
		System.out.println("\nIdentify Initially Connected...\n");
		boolean is3 = p.is_initially_connected();
		System.out.println("\nIdentify Minimal...\n");
		boolean is4 = p.is_minimal();
		
		System.out.println("\nIs the FFSM deterministic?");
		System.out.println(is1);
		System.out.println("\nIs the FFSM complete?");
		System.out.println(is2);
		System.out.println("\nIs the FFSM initially connected?");
		System.out.println(is3);
		System.out.println("\nIs the FFSM minimal?");
		System.out.println(is4);
	}
	
	@Test
	public void test012_agm_all_fsm() throws Exception
	{
		//logger.setLevel(Level.INFO);
		String folder = "agmfsm";
		//FSMProperties p = new FSMProperties(folder);		
		
		for(int i=1; i<=1; i++){
			String file = "./"+folder+"/prod2.txt";			
			FSMProperties p = new FSMProperties(folder, false, false, file);
			
			System.out.println("\nIdentify Deterministic...\n");
			boolean is1 = p.is_deterministic();	
			System.out.println("\nIdentify Complete...\n");
			boolean is2 = p.is_complete();
			System.out.println("\nIdentify Initially Connected...\n");
			boolean is3 = p.is_initially_connected();
			System.out.println("\nIdentify Minimal...\n");
			boolean is4 = p.is_minimal();
			
			System.out.println("\nIs the FSM deterministic?");
			System.out.println(is1);
			System.out.println("\nIs the FSM complete?");
			System.out.println(is2);
			System.out.println("\nIs the FSM initially connected?");
			System.out.println(is3);
			System.out.println("\nIs the FSM minimal?");
			System.out.println(is4);
		}
		
	}
	
	@Test
	public void test013_logger() throws Exception
	{
		FFSMReaderTest tester = new FFSMReaderTest();
	    try {
	      MyLogger.setup();
	    } catch (IOException e) {
	      e.printStackTrace();
	      throw new RuntimeException("Problems with creating the log files");
	    }
	    tester.checkFSM();

	}
	
	public void checkFSM() throws Exception {
	    
		//logger.setLevel(Level.OFF);
		//logger.setLevel(Level.INFO);
		String log = "";
		boolean islog = true;
		boolean debug = false;
		//LOGGER.info("Starting");
		
		String folder = "agmfsm";
		for(int i=1; i<=500; i++){
			String file = "./"+folder+"/prod2.txt";
			FSMProperties p = new FSMProperties(folder, islog, debug, file);
			
			if(islog) log = log.concat("---------------------------------------\n");
			if(islog) log = log.concat("\nIdentify Deterministic...\n");
			boolean is1 = p.is_deterministic();	
			
			if(islog) log = log.concat("---------------------------------------\n");
			if(islog) log = log.concat("\nIdentify Complete...\n");			
			boolean is2 = p.is_complete();
			
			if(islog) log = log.concat("---------------------------------------\n");
			if(islog) log = log.concat("\nIdentify Initially Connected...\n");					
			boolean is3 = p.is_initially_connected();
			if(islog) log = log.concat(p.getlog()+"\n");
			
			if(islog) log = log.concat("---------------------------------------\n");
			if(islog) log = log.concat("\nIdentify Minimal...\n");			
			boolean is4 = p.is_minimal();
			if(islog) log = log.concat(p.getlog()+"\n");
			
			if(islog) log = log.concat("---------------------------------------\n");
			if(islog) log = log.concat("\nIs the FSM deterministic?\n");
			if(islog) log = log.concat(is1+"\n");
			
			if(islog) log = log.concat("\nIs the FSM complete?\n");					
			if(islog) log = log.concat(is2+"\n");
			
			if(islog) log = log.concat("\nIs the FSM initially connected?\n");	
			if(islog) log = log.concat(is3+"\n");			
			
			if(islog) log = log.concat("\nIs the FSM minimal?\n");			
			if(islog) log = log.concat(is4+"\n");
			
			if(islog) LOGGER.info(""+log);			
		}
		//LOGGER.info("Finishing");
		//LOGGER.severe("Info Log");
	    //LOGGER.warning("Info Log");
	    //LOGGER.info("Info Log");
		
	  }

	@Test
	public void test014_ffsm_logger()
	{
		FFSMReaderTest tester = new FFSMReaderTest();
	    try {
	      MyLoggerFFSM.setup();
	    } catch (IOException e) {
	      e.printStackTrace();
	      throw new RuntimeException("Problems with creating the log files");
	    }
	    tester.checkFFSM();

	}
		
	public void checkFFSM() {	   
		String log = "";
		boolean islog = true;
		boolean debug = true;
		
		String folder = "agm";
		FFSMProperties p = new FFSMProperties(folder, islog, debug);		
		if(islog) log = log.concat("Reading Feature Model (.xml)"+"\n");
		String header = p.read_XML_FeatureModel("./"+folder+"/fm_agm.xml");
		if(islog) log = log.concat(p.getlog()+"\n");
		
		for(int i=1; i<=1; i++){
			String file = "./"+folder+"/ffsm_agm.txt";
			try {
				if(!p.set_checkFFSM(file, header)){
					System.out.println("Invalid FFSM!!!");
					return;
				}
			} catch (InterruptedException e) {
				// TODO Auto-generated catch block
				e.printStackTrace();
			} catch (IOException e) {
				// TODO Auto-generated catch block
				e.printStackTrace();
			}
			
			if(islog) log = log.concat("---------------------------------------\n");
			if(islog) log = log.concat("\nIdentify Deterministic...\n");
			boolean is1 = p.is_deterministic();	
			if(islog) log = log.concat(p.getlog()+"\n");
			
			if(islog) log = log.concat("---------------------------------------\n");
			if(islog) log = log.concat("\nIdentify Complete...\n");			
			boolean is2 = p.is_complete();
			if(islog) log = log.concat(p.getlog()+"\n");
			//System.out.println("complete");
			
			if(islog) log = log.concat("---------------------------------------\n");
			if(islog) log = log.concat("\nIdentify Initially Connected...\n");					
			boolean is3 = p.is_initially_connected();
			if(islog) log = log.concat(p.getlog()+"\n");
			//System.out.println("init");
			
			if(islog) log = log.concat("---------------------------------------\n");
			if(islog) log = log.concat("\nIdentify Minimal...\n");			
			boolean is4 = p.is_minimal();
			if(islog) log = log.concat(p.getlog()+"\n");
			//System.out.println("minimal");
			
			if(islog) log = log.concat("---------------------------------------\n");
			if(islog) log = log.concat("\nIs the FSM deterministic?\n");
			if(islog) log = log.concat(is1+"\n");
			
			if(islog) log = log.concat("\nIs the FSM complete?\n");					
			if(islog) log = log.concat(is2+"\n");
			
			if(islog) log = log.concat("\nIs the FSM initially connected?\n");	
			if(islog) log = log.concat(is3+"\n");			
			
			if(islog) log = log.concat("\nIs the FSM minimal?\n");			
			if(islog) log = log.concat(is4+"\n");
			
			if(islog) LOGGER.info(""+log);			
		}
	  }
	
	
	@Test
	public void test015_largeFSMs() throws Exception
	{
		FFSMReaderTest tester = new FFSMReaderTest();
	    try {
	      MyLogger.setup();
	    } catch (IOException e) {
	      e.printStackTrace();
	      throw new RuntimeException("Problems with creating the log files");
	    }
	    tester.checkFSM_large();

	}
	
	public void checkFSM_large() throws Exception {
	    
		//logger.setLevel(Level.OFF);
		//logger.setLevel(Level.INFO);
		String log = "";
		boolean islog = false;
		boolean debug = false;
		//LOGGER.info("Starting");
		
		String folder = "largeSPL_FSM";		
		for(int i=1; i<=65536; i++){
			//System.out.println("Count "+i);
			String file = "./"+folder+"/prod1.txt";
			FSMProperties p = new FSMProperties(folder, islog, debug, file);
			
			if(islog) log = log.concat("---------------------------------------\n");
			if(islog) log = log.concat("\nIdentify Deterministic...\n");
			boolean is1 = p.is_deterministic();
			if(!is1){
				System.out.println("Not deterministic!");
				return;
			}
			
			if(islog) log = log.concat("---------------------------------------\n");
			if(islog) log = log.concat("\nIdentify Complete...\n");			
			boolean is2 = p.is_complete();
			
			if(islog) log = log.concat("---------------------------------------\n");
			if(islog) log = log.concat("\nIdentify Initially Connected...\n");					
			boolean is3 = p.is_initially_connected();
			if(islog) log = log.concat(p.getlog()+"\n");
			if(!is3){
				System.out.println("Not initially connected!");
				return;
			}
			
			if(islog) log = log.concat("---------------------------------------\n");
			if(islog) log = log.concat("\nIdentify Minimal...\n");			
			boolean is4 = p.is_minimal();
			if(islog) log = log.concat(p.getlog()+"\n");
			
			if(islog) log = log.concat("---------------------------------------\n");
			if(islog) log = log.concat("\nIs the FSM deterministic?\n");
			if(islog) log = log.concat(is1+"\n");
			
			if(islog) log = log.concat("\nIs the FSM complete?\n");					
			if(islog) log = log.concat(is2+"\n");
			
			if(islog) log = log.concat("\nIs the FSM initially connected?\n");	
			if(islog) log = log.concat(is3+"\n");			
			
			if(islog) log = log.concat("\nIs the FSM minimal?\n");			
			if(islog) log = log.concat(is4+"\n");
			
			if(islog) LOGGER.info(""+log);			
		}		
		
	  }
	
	@Test
	public void test016_ffsm_large()
	{
		FFSMReaderTest tester = new FFSMReaderTest();
	    try {
	      MyLoggerFFSM.setup();
	    } catch (IOException e) {
	      e.printStackTrace();
	      throw new RuntimeException("Problems with creating the log files");
	    }
	    tester.checkFFSM_large();

	}
		
	public void checkFFSM_large() {	   
		String log = "";
		boolean islog = false;
		boolean debug = false;
		
		String folder = "largeSPL";
		FFSMProperties p = new FFSMProperties(folder, islog, debug);		
		if(islog) log = log.concat("Reading Feature Model (.xml)"+"\n");
		String header = p.read_XML_FeatureModel("./"+folder+"/example_fm.xml");
		if(islog) log = log.concat(p.getlog()+"\n");
		
		for(int i=1; i<=1; i++){
			String file = "./"+folder+"/ffsm_largeSPL.txt";
			try {
				if(!p.set_checkFFSM(file, header)){
					System.out.println("Invalid FFSM!!!");
					return;
				}
			} catch (InterruptedException e) {
				// TODO Auto-generated catch block
				e.printStackTrace();
			} catch (IOException e) {
				// TODO Auto-generated catch block
				e.printStackTrace();
			}
			
			if(islog) log = log.concat("---------------------------------------\n");
			if(islog) log = log.concat("\nIdentify Deterministic...\n");
			boolean is1 = p.is_deterministic();	
			if(islog) log = log.concat(p.getlog()+"\n");
			if(!is1){
				System.out.println("Not deterministic!");
				return;
			}
			
			if(islog) log = log.concat("---------------------------------------\n");
			if(islog) log = log.concat("\nIdentify Complete...\n");			
			boolean is2 = p.is_complete();
			if(islog) log = log.concat(p.getlog()+"\n");
			System.out.println("complete");
			
			if(islog) log = log.concat("---------------------------------------\n");
			if(islog) log = log.concat("\nIdentify Initially Connected...\n");					
			boolean is3 = p.is_initially_connected();
			if(islog) log = log.concat(p.getlog()+"\n");
			System.out.println("init");
			if(!is3){
				System.out.println("Not initially connected!");
				return;
			}
			
			if(islog) log = log.concat("---------------------------------------\n");
			if(islog) log = log.concat("\nIdentify Minimal...\n");			
			boolean is4 = p.is_minimal();
			if(islog) log = log.concat(p.getlog()+"\n");
			System.out.println("minimal");
			
			if(islog) log = log.concat("---------------------------------------\n");
			if(islog) log = log.concat("\nIs the FSM deterministic?\n");
			if(islog) log = log.concat(is1+"\n");
			
			if(islog) log = log.concat("\nIs the FSM complete?\n");					
			if(islog) log = log.concat(is2+"\n");
			
			if(islog) log = log.concat("\nIs the FSM initially connected?\n");	
			if(islog) log = log.concat(is3+"\n");			
			
			if(islog) log = log.concat("\nIs the FSM minimal?\n");			
			if(islog) log = log.concat(is4+"\n");
			
			if(islog) LOGGER.info(""+log);			
		}
	  }
	
	
	@Test
	public void test017_generate_featuremodels()
	{
		FFeatureModel gen = new FFeatureModel();
	    try {
	      //gen.gen_FM("increase/feature_models", 70);
	      //gen.gen_FM_best("increase/feature_models_best", 70);
	      gen.gen_FM_mid("increase/feature_models_mid", 70);
	    } catch (IOException e) {
	      e.printStackTrace();
	      throw new RuntimeException("Problems with creating the feature model files");
	    } 
	}
	
	@Test
	public void test018_generate_ffsms()
	{
		FFSMModel gen = new FFSMModel();
	    try {
	      //gen.gen_FFSM("increase/ffsms", 70);
	      //gen.gen_FFSM_best("increase/ffsms_best", 70);
	      gen.gen_FFSM_mid("increase/ffsms_mid", 70);
	    } catch (IOException e) {
	      e.printStackTrace();
	      throw new RuntimeException("Problems with creating the ffsm model files");
	    } 
	}
	
	@Test
	public void test019_generate_fsm_models()
	{
		FsmModel gen = new FsmModel();
	    try {
	      //gen.gen_FSM("increase/fsm", 70);
	      //gen.gen_FSM_best("increase/fsm_best", 70);
	      gen.gen_FSM_mid("increase/fsm_mid", 70);
	    } catch (IOException e) {
	      e.printStackTrace();
	      throw new RuntimeException("Problems with creating the fsm model files");
	    } 
	}
	
	@Test
	public void test020_ffsm_large_increase_extensive() throws Exception
	{
		try {
	    	FFSMLogger.set_filepath("./logs/increaseFFSM.txt");
	    	FFSMLogger.setup();	     
	    } catch (IOException e) {
	      e.printStackTrace();
	      throw new RuntimeException("Problems with creating the log files");
	    }
	    
	    String log = "";
		boolean islog = false;
		boolean debug = false;
		int amount = 100;
		String timelog = "";
		
		String folder0 = "increase/aux";
		String folder1 = "increase/feature_models";
		String folder2 = "increase/ffsms";
		//String folder3 = "increase/fsm";
		String folder4 = "increase/logs";
		timelog = timelog.concat("ffsm = c(");
		for(int i=1; i<=amount; i++){
			long startTime = System.currentTimeMillis();
			
			FFSMProperties p = new FFSMProperties(folder0, islog, debug);		
			if(islog) log = log.concat("Reading Feature Model (.xml)"+"\n");
			String header = p.read_XML_FeatureModel("./"+folder1+"/example"+i+".xml");
			if(islog) log = log.concat(p.getlog()+"\n");
			
			String file = "./"+folder2+"/ffsm"+i+".txt";
			try {
				if(!p.set_checkFFSM(file, header)){
					System.out.println("Invalid FFSM!!!");
					return;
				}
			} catch (InterruptedException e) {
				// TODO Auto-generated catch block
				e.printStackTrace();
			}
			
			if(islog) log = log.concat("---------------------------------------\n");
			if(islog) log = log.concat("\nIdentify Deterministic...\n");
			boolean is1 = p.is_deterministic();	
			if(islog) log = log.concat(p.getlog()+"\n");
			if(!is1){
				System.out.println("Not deterministic!");
				return;
			}
			
			if(islog) log = log.concat("---------------------------------------\n");
			if(islog) log = log.concat("\nIdentify Complete...\n");			
			boolean is2 = p.is_complete();
			if(islog) log = log.concat(p.getlog()+"\n");
			//System.out.println("complete");
			
			if(islog) log = log.concat("---------------------------------------\n");
			if(islog) log = log.concat("\nIdentify Initially Connected...\n");					
			boolean is3 = p.is_initially_connected();
			if(islog) log = log.concat(p.getlog()+"\n");
			//System.out.println("init");
			if(!is3){
				System.out.println("Not initially connected!");
				return;
			}
			
			if(islog) log = log.concat("---------------------------------------\n");
			if(islog) log = log.concat("\nIdentify Minimal...\n");			
			boolean is4 = p.is_minimal();
			if(islog) log = log.concat(p.getlog()+"\n");
			//System.out.println("minimal");
			
			if(islog) log = log.concat("---------------------------------------\n");
			if(islog) log = log.concat("\nIs the FFSM deterministic?\n");
			if(islog) log = log.concat(is1+"\n");
			
			if(islog) log = log.concat("\nIs the FFSM complete?\n");					
			if(islog) log = log.concat(is2+"\n");
			
			if(islog) log = log.concat("\nIs the FFSM initially connected?\n");	
			if(islog) log = log.concat(is3+"\n");			
			
			if(islog) log = log.concat("\nIs the FFSM minimal?\n");			
			if(islog) log = log.concat(is4+"\n");
			
			if(islog) LOGGER.info(""+log);	
			
			long stopTime = System.currentTimeMillis();
		    long elapsedTime = stopTime - startTime;
		    timelog = timelog.concat(elapsedTime+",");
		    //System.out.println(elapsedTime);
		}
		timelog = timelog.substring(0,timelog.length()-1);
		timelog = timelog.concat(")\n");
				
		String fpath = "./"+folder4+"/timelog_extensive.txt";
		FileHandler fh = new FileHandler();
		fh.print_file(timelog, fpath);
	}
	
	@Test
	public void test020_ffsm_large_increase_worst() throws Exception
	{
		try {
	    	FFSMLogger.set_filepath("./logs/increaseFFSM.txt");
	    	FFSMLogger.setup();	     
	    } catch (IOException e) {
	      e.printStackTrace();
	      throw new RuntimeException("Problems with creating the log files");
	    }
	    
	    String log = "";
		boolean islog = false;
		boolean debug = false;
		int amount = 20;
		int step = 1;
		int start = 5;
		String timelog = "";
		
		String folder0 = "increase/aux";
		String folder1 = "increase/feature_models";
		String folder2 = "increase/ffsms";
		String folder3 = "increase/fsm";
		String folder4 = "increase/logs";
		timelog = timelog.concat("ffsm = c(");
		for(int i=start; i<=amount; i=i+step){
			long startTime = System.currentTimeMillis();
			
			FFSMProperties p = new FFSMProperties(folder0, islog, debug);		
			if(islog) log = log.concat("Reading Feature Model (.xml)"+"\n");
			String header = p.read_XML_FeatureModel("./"+folder1+"/example"+i+".xml");
			if(islog) log = log.concat(p.getlog()+"\n");
			
			String file = "./"+folder2+"/ffsm"+i+".txt";
			try {
				if(!p.set_checkFFSM(file, header)){
					System.out.println("Invalid FFSM!!!");
					return;
				}
			} catch (InterruptedException e) {
				// TODO Auto-generated catch block
				e.printStackTrace();
			}
			
			if(islog) log = log.concat("---------------------------------------\n");
			if(islog) log = log.concat("\nIdentify Deterministic...\n");
			boolean is1 = p.is_deterministic();	
			if(islog) log = log.concat(p.getlog()+"\n");
			if(!is1){
				System.out.println("Not deterministic!");
				return;
			}
			
			if(islog) log = log.concat("---------------------------------------\n");
			if(islog) log = log.concat("\nIdentify Complete...\n");			
			boolean is2 = p.is_complete();
			if(islog) log = log.concat(p.getlog()+"\n");
			//System.out.println("complete");
			
			if(islog) log = log.concat("---------------------------------------\n");
			if(islog) log = log.concat("\nIdentify Initially Connected...\n");					
			boolean is3 = p.is_initially_connected();
			if(islog) log = log.concat(p.getlog()+"\n");
			//System.out.println("init");
			if(!is3){
				System.out.println("Not initially connected!");
				return;
			}
			
			if(islog) log = log.concat("---------------------------------------\n");
			if(islog) log = log.concat("\nIdentify Minimal...\n");			
			boolean is4 = p.is_minimal();
			if(islog) log = log.concat(p.getlog()+"\n");
			//System.out.println("minimal");
			
			if(islog) log = log.concat("---------------------------------------\n");
			if(islog) log = log.concat("\nIs the FSM deterministic?\n");
			if(islog) log = log.concat(is1+"\n");
			
			if(islog) log = log.concat("\nIs the FSM complete?\n");					
			if(islog) log = log.concat(is2+"\n");
			
			if(islog) log = log.concat("\nIs the FSM initially connected?\n");	
			if(islog) log = log.concat(is3+"\n");			
			
			if(islog) log = log.concat("\nIs the FSM minimal?\n");			
			if(islog) log = log.concat(is4+"\n");
			
			if(islog) LOGGER.info(""+log);	
			
			long stopTime = System.currentTimeMillis();
		    long elapsedTime = stopTime - startTime;
		    timelog = timelog.concat(elapsedTime+",");
		    //System.out.println(elapsedTime);
		}
		timelog = timelog.substring(0,timelog.length()-1);
		timelog = timelog.concat(")\n");
		
		//-----------------------------------------
		 log = "";
		 timelog = timelog.concat("fsm = c(");
		for(int k=start; k<=amount; k=k+step){
			int pbp = (int) Math.pow(2, k);
			long startTime = System.nanoTime();
			//for(int i=1; i<=pbp; i++){
				//System.out.println("Count "+i);						
				String file = "./"+folder3+"/fsm"+k+".txt";
				FSMProperties p = new FSMProperties(folder0, islog, debug, file);
				
				if(islog) log = log.concat("---------------------------------------\n");
				if(islog) log = log.concat("\nIdentify Deterministic...\n");
				boolean is1 = p.is_deterministic();
				if(!is1){
					System.out.println("Not deterministic!");
					return;
				}
				
				if(islog) log = log.concat("---------------------------------------\n");
				if(islog) log = log.concat("\nIdentify Complete...\n");			
				boolean is2 = p.is_complete();
				
				if(islog) log = log.concat("---------------------------------------\n");
				if(islog) log = log.concat("\nIdentify Initially Connected...\n");					
				boolean is3 = p.is_initially_connected();
				if(islog) log = log.concat(p.getlog()+"\n");
				if(!is3){
					System.out.println("Not initially connected!");
					return;
				}
				
				if(islog) log = log.concat("---------------------------------------\n");
				if(islog) log = log.concat("\nIdentify Minimal...\n");			
				boolean is4 = p.is_minimal();
				if(islog) log = log.concat(p.getlog()+"\n");
				
				if(islog) log = log.concat("---------------------------------------\n");
				if(islog) log = log.concat("\nIs the FSM deterministic?\n");
				if(islog) log = log.concat(is1+"\n");
				
				if(islog) log = log.concat("\nIs the FSM complete?\n");					
				if(islog) log = log.concat(is2+"\n");
				
				if(islog) log = log.concat("\nIs the FSM initially connected?\n");	
				if(islog) log = log.concat(is3+"\n");			
				
				if(islog) log = log.concat("\nIs the FSM minimal?\n");			
				if(islog) log = log.concat(is4+"\n");
				
				if(islog) LOGGER.info(""+log);	
			//}	
			long stopTime = System.nanoTime();
		    long elapsedTime = stopTime - startTime;
		    elapsedTime = (elapsedTime * pbp) / 1000000;
		    timelog = timelog.concat(elapsedTime+",");
		}	
		timelog = timelog.substring(0,timelog.length()-1);
		timelog = timelog.concat(")\n");
		//----------------------------------------------

		String fpath = "./"+folder4+"/timelog_worst.txt";
		FileHandler fh = new FileHandler();
		fh.print_file(timelog, fpath);
	}
	
	@Test
	public void test020_1_ffsm_large_increase_best_extensive() throws Exception
	{
		try {
	    	FFSMLogger.set_filepath("./logs/increaseFFSM.txt");
	    	FFSMLogger.setup();	     
	    } catch (IOException e) {
	      e.printStackTrace();
	      throw new RuntimeException("Problems with creating the log files");
	    }
	    
	    String log = "";
		boolean islog = false;
		boolean debug = false;
		int amount = 70;
		String timelog = "";		
		int step = 5;
		int start = 25;
		
		String folder0 = "increase/aux";
		String folder1 = "increase/feature_models_best";
		String folder2 = "increase/ffsms_best";
		String folder3 = "increase/fsm_best";
		String folder4 = "increase/logs";
		
		/*
		timelog = timelog.concat("ffsm = c(");
		for(int i=start; i<=amount; i=i+step){
			long startTime = System.currentTimeMillis();
			if(islog) log = log.concat("Iteration "+i);
			FFSMProperties p = new FFSMProperties(folder0, islog, debug);		
			if(islog) log = log.concat("Reading Feature Model (.xml)"+"\n");
			String header = p.read_XML_FeatureModel("./"+folder1+"/example"+i+".xml");
			if(islog) log = log.concat(p.getlog()+"\n");
			
			String file = "./"+folder2+"/ffsm"+i+".txt";
			try {
				if(!p.set_checkFFSM(file, header)){
					System.out.println("Invalid FFSM!!!");
					return;
				}
			} catch (InterruptedException e) {
				// TODO Auto-generated catch block
				e.printStackTrace();
			}
			
			if(islog) log = log.concat("---------------------------------------\n");
			if(islog) log = log.concat("\nIdentify Deterministic...\n");
			boolean is1 = p.is_deterministic();	
			if(islog) log = log.concat(p.getlog()+"\n");
			if(!is1){
				System.out.println("Not deterministic!");
				return;
			}
			
			if(islog) log = log.concat("---------------------------------------\n");
			if(islog) log = log.concat("\nIdentify Complete...\n");			
			boolean is2 = p.is_complete();
			if(islog) log = log.concat(p.getlog()+"\n");
			//System.out.println("complete");
			
			if(islog) log = log.concat("---------------------------------------\n");
			if(islog) log = log.concat("\nIdentify Initially Connected...\n");					
			boolean is3 = p.is_initially_connected();
			if(islog) log = log.concat(p.getlog()+"\n");
			//System.out.println("init");
			if(!is3){
				System.out.println("Not initially connected!");
				return;
			}
			
			if(islog) log = log.concat("---------------------------------------\n");
			if(islog) log = log.concat("\nIdentify Minimal...\n");			
			boolean is4 = p.is_minimal();
			if(islog) log = log.concat(p.getlog()+"\n");
			//System.out.println("minimal");
			
			if(islog) log = log.concat("---------------------------------------\n");
			if(islog) log = log.concat("\nIs the FSM deterministic?\n");
			if(islog) log = log.concat(is1+"\n");
			
			if(islog) log = log.concat("\nIs the FSM complete?\n");					
			if(islog) log = log.concat(is2+"\n");
			
			if(islog) log = log.concat("\nIs the FSM initially connected?\n");	
			if(islog) log = log.concat(is3+"\n");			
			
			if(islog) log = log.concat("\nIs the FSM minimal?\n");			
			if(islog) log = log.concat(is4+"\n");
			
			if(islog) LOGGER.info(""+log);	
			
			long stopTime = System.currentTimeMillis();
		    long elapsedTime = stopTime - startTime;
		    timelog = timelog.concat(elapsedTime+",");
		    //System.out.println(elapsedTime);
		}
		timelog = timelog.substring(0,timelog.length()-1);
		timelog = timelog.concat(")\n");
		*/
		//-----------------------------------------

		 log = "";
		 timelog = timelog.concat("fsm = c(");
		for(int k=start; k<=amount; k=k+step){
			int pbp = amount + 1;
			long startTime = System.nanoTime();
			//for(int i=1; i<=pbp; i++){
				//System.out.println("Count "+i);						
				String file = "./"+folder3+"/fsm"+k+".txt";
				FSMProperties p = new FSMProperties(folder0, islog, debug, file);
				
				if(islog) log = log.concat("---------------------------------------\n");
				if(islog) log = log.concat("\nIdentify Deterministic...\n");
				boolean is1 = p.is_deterministic();
				if(!is1){
					System.out.println("Not deterministic!");
					return;
				}
				
				if(islog) log = log.concat("---------------------------------------\n");
				if(islog) log = log.concat("\nIdentify Complete...\n");			
				boolean is2 = p.is_complete();
				
				if(islog) log = log.concat("---------------------------------------\n");
				if(islog) log = log.concat("\nIdentify Initially Connected...\n");					
				boolean is3 = p.is_initially_connected();
				if(islog) log = log.concat(p.getlog()+"\n");
				if(!is3){
					System.out.println("Not initially connected!");
					return;
				}
				
				if(islog) log = log.concat("---------------------------------------\n");
				if(islog) log = log.concat("\nIdentify Minimal...\n");			
				boolean is4 = p.is_minimal();
				if(islog) log = log.concat(p.getlog()+"\n");
				
				if(islog) log = log.concat("---------------------------------------\n");
				if(islog) log = log.concat("\nIs the FSM deterministic?\n");
				if(islog) log = log.concat(is1+"\n");
				
				if(islog) log = log.concat("\nIs the FSM complete?\n");					
				if(islog) log = log.concat(is2+"\n");
				
				if(islog) log = log.concat("\nIs the FSM initially connected?\n");	
				if(islog) log = log.concat(is3+"\n");			
				
				if(islog) log = log.concat("\nIs the FSM minimal?\n");			
				if(islog) log = log.concat(is4+"\n");
				
				if(islog) LOGGER.info(""+log);	
			//}	
			long stopTime = System.nanoTime();
		    long elapsedTime = stopTime - startTime;
		    elapsedTime = (elapsedTime * pbp) / 1000000;
		    timelog = timelog.concat(elapsedTime+",");
		}	
		timelog = timelog.substring(0,timelog.length()-1);
		timelog = timelog.concat(")\n");
		//----------------------------------------------

		String fpath = "./"+folder4+"/timelog_best_part111.txt";
		FileHandler fh = new FileHandler();
		fh.print_file(timelog, fpath);
	}
	
	
	@Test
	public void test020_1_ffsm_large_increase_best() throws Exception
	{
		try {
	    	FFSMLogger.set_filepath("./logs/increaseFFSM.txt");
	    	FFSMLogger.setup();	     
	    } catch (IOException e) {
	      e.printStackTrace();
	      throw new RuntimeException("Problems with creating the log files");
	    }
	    
	    String log = "";
		boolean islog = false;
		boolean debug = false;
		int amount = 10;
		String timelog = "";
		
		String folder0 = "increase/aux";
		String folder1 = "increase/feature_models_best";
		String folder2 = "increase/ffsms_best";
		String folder3 = "increase/fsm_best";
		String folder4 = "increase/logs";
		timelog = timelog.concat("ffsm = c(");
		for(int i=1; i<=amount; i++){
			long startTime = System.currentTimeMillis();
			if(islog) log = log.concat("Iteration "+i);
			FFSMProperties p = new FFSMProperties(folder0, islog, debug);		
			if(islog) log = log.concat("Reading Feature Model (.xml)"+"\n");
			String header = p.read_XML_FeatureModel("./"+folder1+"/example"+i+".xml");
			if(islog) log = log.concat(p.getlog()+"\n");
			
			String file = "./"+folder2+"/ffsm"+i+".txt";
			try {
				if(!p.set_checkFFSM(file, header)){
					System.out.println("Invalid FFSM!!!");
					return;
				}
			} catch (InterruptedException e) {
				// TODO Auto-generated catch block
				e.printStackTrace();
			}
			
			if(islog) log = log.concat("---------------------------------------\n");
			if(islog) log = log.concat("\nIdentify Deterministic...\n");
			boolean is1 = p.is_deterministic();	
			if(islog) log = log.concat(p.getlog()+"\n");
			if(!is1){
				System.out.println("Not deterministic!");
				return;
			}
			
			if(islog) log = log.concat("---------------------------------------\n");
			if(islog) log = log.concat("\nIdentify Complete...\n");			
			boolean is2 = p.is_complete();
			if(islog) log = log.concat(p.getlog()+"\n");
			//System.out.println("complete");
			
			if(islog) log = log.concat("---------------------------------------\n");
			if(islog) log = log.concat("\nIdentify Initially Connected...\n");					
			boolean is3 = p.is_initially_connected();
			if(islog) log = log.concat(p.getlog()+"\n");
			//System.out.println("init");
			if(!is3){
				System.out.println("Not initially connected!");
				return;
			}
			
			if(islog) log = log.concat("---------------------------------------\n");
			if(islog) log = log.concat("\nIdentify Minimal...\n");			
			boolean is4 = p.is_minimal();
			if(islog) log = log.concat(p.getlog()+"\n");
			//System.out.println("minimal");
			
			if(islog) log = log.concat("---------------------------------------\n");
			if(islog) log = log.concat("\nIs the FSM deterministic?\n");
			if(islog) log = log.concat(is1+"\n");
			
			if(islog) log = log.concat("\nIs the FSM complete?\n");					
			if(islog) log = log.concat(is2+"\n");
			
			if(islog) log = log.concat("\nIs the FSM initially connected?\n");	
			if(islog) log = log.concat(is3+"\n");			
			
			if(islog) log = log.concat("\nIs the FSM minimal?\n");			
			if(islog) log = log.concat(is4+"\n");
			
			if(islog) LOGGER.info(""+log);	
			
			long stopTime = System.currentTimeMillis();
		    long elapsedTime = stopTime - startTime;
		    timelog = timelog.concat(elapsedTime+",");
		    //System.out.println(elapsedTime);
		}
		timelog = timelog.substring(0,timelog.length()-1);
		timelog = timelog.concat(")\n");
		
		//-----------------------------------------

		 log = "";
		 timelog = timelog.concat("fsm = c(");
		for(int k=1; k<=amount; k++){
			int pbp = amount + 1;
			long startTime = System.nanoTime();
			//for(int i=1; i<=pbp; i++){
				//System.out.println("Count "+i);						
				String file = "./"+folder3+"/fsm"+k+".txt";
				FSMProperties p = new FSMProperties(folder0, islog, debug, file);
				
				if(islog) log = log.concat("---------------------------------------\n");
				if(islog) log = log.concat("\nIdentify Deterministic...\n");
				boolean is1 = p.is_deterministic();
				if(!is1){
					System.out.println("Not deterministic!");
					return;
				}
				
				if(islog) log = log.concat("---------------------------------------\n");
				if(islog) log = log.concat("\nIdentify Complete...\n");			
				boolean is2 = p.is_complete();
				
				if(islog) log = log.concat("---------------------------------------\n");
				if(islog) log = log.concat("\nIdentify Initially Connected...\n");					
				boolean is3 = p.is_initially_connected();
				if(islog) log = log.concat(p.getlog()+"\n");
				if(!is3){
					System.out.println("Not initially connected!");
					return;
				}
				
				if(islog) log = log.concat("---------------------------------------\n");
				if(islog) log = log.concat("\nIdentify Minimal...\n");			
				boolean is4 = p.is_minimal();
				if(islog) log = log.concat(p.getlog()+"\n");
				
				if(islog) log = log.concat("---------------------------------------\n");
				if(islog) log = log.concat("\nIs the FSM deterministic?\n");
				if(islog) log = log.concat(is1+"\n");
				
				if(islog) log = log.concat("\nIs the FSM complete?\n");					
				if(islog) log = log.concat(is2+"\n");
				
				if(islog) log = log.concat("\nIs the FSM initially connected?\n");	
				if(islog) log = log.concat(is3+"\n");			
				
				if(islog) log = log.concat("\nIs the FSM minimal?\n");			
				if(islog) log = log.concat(is4+"\n");
				
				if(islog) LOGGER.info(""+log);	
			//}	
			long stopTime = System.nanoTime();
		    long elapsedTime = stopTime - startTime;
		    elapsedTime = (elapsedTime * pbp) / 1000000;
		    timelog = timelog.concat(elapsedTime+",");
		}	
		timelog = timelog.substring(0,timelog.length()-1);
		timelog = timelog.concat(")\n");
		//----------------------------------------------

		String fpath = "./"+folder4+"/timelog_best.txt";
		FileHandler fh = new FileHandler();
		fh.print_file(timelog, fpath);
	}
	
	@Test
	public void test020_1_ffsm_large_increase_mid_extensive() throws Exception
	{
		try {
	    	FFSMLogger.set_filepath("./logs/increaseFFSM_mid.txt");
	    	FFSMLogger.setup();	     
	    } catch (IOException e) {
	      e.printStackTrace();
	      throw new RuntimeException("Problems with creating the log files");
	    }
	    
		String log = "";
		boolean islog = false;
		boolean debug = false;
		int amount = 70;
		String timelog = "";		
		int step = 5;
		int start = 25;
		
		String folder0 = "increase/aux";
		String folder1 = "increase/feature_models_mid";
		String folder2 = "increase/ffsms_mid";
		String folder3 = "increase/fsm_mid";
		String folder4 = "increase/logs";
		
		/*
		timelog = timelog.concat("ffsm = c(");
		for(int i=start; i<=amount; i=i+step){
			long startTime = System.currentTimeMillis();
			if(islog) log = log.concat("Iteration "+i);
			FFSMProperties p = new FFSMProperties(folder0, islog, debug);		
			if(islog) log = log.concat("Reading Feature Model (.xml)"+"\n");
			String header = p.read_XML_FeatureModel("./"+folder1+"/example"+i+".xml");
			if(islog) log = log.concat(p.getlog()+"\n");
			
			String file = "./"+folder2+"/ffsm"+i+".txt";
			try {
				if(!p.set_checkFFSM(file, header)){
					System.out.println("Invalid FFSM!!!");
					return;
				}
			} catch (InterruptedException e) {
				// TODO Auto-generated catch block
				e.printStackTrace();
			}
			
			if(islog) log = log.concat("---------------------------------------\n");
			if(islog) log = log.concat("\nIdentify Deterministic...\n");
			boolean is1 = p.is_deterministic();	
			if(islog) log = log.concat(p.getlog()+"\n");
			if(!is1){
				System.out.println("Not deterministic!");
				return;
			}
			
			if(islog) log = log.concat("---------------------------------------\n");
			if(islog) log = log.concat("\nIdentify Complete...\n");			
			boolean is2 = p.is_complete();
			if(islog) log = log.concat(p.getlog()+"\n");
			//System.out.println("complete");
			
			if(islog) log = log.concat("---------------------------------------\n");
			if(islog) log = log.concat("\nIdentify Initially Connected...\n");					
			boolean is3 = p.is_initially_connected();
			if(islog) log = log.concat(p.getlog()+"\n");
			//System.out.println("init");
			if(!is3){
				System.out.println("Not initially connected!");
				return;
			}
			
			if(islog) log = log.concat("---------------------------------------\n");
			if(islog) log = log.concat("\nIdentify Minimal...\n");			
			boolean is4 = p.is_minimal();
			if(islog) log = log.concat(p.getlog()+"\n");
			//System.out.println("minimal");
			
			if(islog) log = log.concat("---------------------------------------\n");
			if(islog) log = log.concat("\nIs the FSM deterministic?\n");
			if(islog) log = log.concat(is1+"\n");
			
			if(islog) log = log.concat("\nIs the FSM complete?\n");					
			if(islog) log = log.concat(is2+"\n");
			
			if(islog) log = log.concat("\nIs the FSM initially connected?\n");	
			if(islog) log = log.concat(is3+"\n");			
			
			if(islog) log = log.concat("\nIs the FSM minimal?\n");			
			if(islog) log = log.concat(is4+"\n");
			
			if(islog) LOGGER.info(""+log);	
			
			long stopTime = System.currentTimeMillis();
		    long elapsedTime = stopTime - startTime;
		    timelog = timelog.concat(elapsedTime+",");
		    //System.out.println(elapsedTime);
		}
		timelog = timelog.substring(0,timelog.length()-1);
		timelog = timelog.concat(")\n");
		*/
		//-----------------------------------------

		 log = "";
		 timelog = timelog.concat("fsm = c(");
		for(int k=start; k<=amount; k=k+step){
			//int pbp = amount + 1;
			FFSMModel gen = new FFSMModel();
			int configs = gen.get_configs_for_ffsm("./increase/fsm_mid/fsm"+k+".txt");			
			long startTime = System.nanoTime();
			//for(int i=1; i<=pbp; i++){
				//System.out.println("Count "+i);						
				String file = "./"+folder3+"/fsm"+k+".txt";
				FSMProperties p = new FSMProperties(folder0, islog, debug, file);
				
				if(islog) log = log.concat("---------------------------------------\n");
				if(islog) log = log.concat("\nIdentify Deterministic...\n");
				boolean is1 = p.is_deterministic();
				if(!is1){
					System.out.println("Not deterministic!");
					return;
				}
				
				if(islog) log = log.concat("---------------------------------------\n");
				if(islog) log = log.concat("\nIdentify Complete...\n");			
				boolean is2 = p.is_complete();
				
				if(islog) log = log.concat("---------------------------------------\n");
				if(islog) log = log.concat("\nIdentify Initially Connected...\n");					
				boolean is3 = p.is_initially_connected();
				if(islog) log = log.concat(p.getlog()+"\n");
				if(!is3){
					System.out.println("Not initially connected!");
					return;
				}
				
				if(islog) log = log.concat("---------------------------------------\n");
				if(islog) log = log.concat("\nIdentify Minimal...\n");			
				boolean is4 = p.is_minimal();
				if(islog) log = log.concat(p.getlog()+"\n");
				
				if(islog) log = log.concat("---------------------------------------\n");
				if(islog) log = log.concat("\nIs the FSM deterministic?\n");
				if(islog) log = log.concat(is1+"\n");
				
				if(islog) log = log.concat("\nIs the FSM complete?\n");					
				if(islog) log = log.concat(is2+"\n");
				
				if(islog) log = log.concat("\nIs the FSM initially connected?\n");	
				if(islog) log = log.concat(is3+"\n");			
				
				if(islog) log = log.concat("\nIs the FSM minimal?\n");			
				if(islog) log = log.concat(is4+"\n");
				
				if(islog) LOGGER.info(""+log);	
			//}	
			long stopTime = System.nanoTime();
		    long elapsedTime = stopTime - startTime;
		    elapsedTime = (elapsedTime * configs) / 1000000;
		    timelog = timelog.concat(elapsedTime+",");
		}	
		timelog = timelog.substring(0,timelog.length()-1);
		timelog = timelog.concat(")\n");
		//----------------------------------------------

		String fpath = "./"+folder4+"/timelog_mid_part111.txt";
		FileHandler fh = new FileHandler();
		fh.print_file(timelog, fpath);
	}
	
	@Test
	public void test021_power_op()
	{
		System.out.println(Math.pow(2, 10));

	}
	
	
	
	@Test
	public void test022_ffsm_large_increase_random() throws Exception
	{			 
		boolean islog = false;
		boolean debug = false;
	   	int amount = 13;
		String timelog = "";
		
		String folder0 = "increase_random/aux";
		String folder1 = "increase_random/feature_models";
		String folder2 = "increase_random/ffsms";
		String folder3 = "increase_random/fsm";
		String folder4 = "increase_random/logs";
		timelog = timelog.concat("ffsm = c(");
		for(int i=1; i<=amount; i++){
			long startTime = System.currentTimeMillis();
			
			FFSMProperties p = new FFSMProperties(folder0, islog, debug);			
			String header = p.read_XML_FeatureModel("./"+folder1+"/example"+i+".xml");			
			
			//random number of c. states per feature 1-n
			//random number of inputs per c. state 1-m
			//random number of outputs 
			
			// n features
			// n - 2n inputs, outputs
			// n+1 - 2n+1 c. states
			// 
			
			String file = "./"+folder2+"/ffsm"+i+".txt";
			try {
				if(!p.set_checkFFSM(file, header)){
					System.out.println("Invalid FFSM!!!");
					return;
				}
			} catch (InterruptedException e) {
				// TODO Auto-generated catch block
				e.printStackTrace();
			}
		
			boolean is1 = p.is_deterministic();				
			if(!is1){
				System.out.println("Not deterministic!");
				return;
			}					
			boolean is2 = p.is_complete();
			boolean is3 = p.is_initially_connected();			
			if(!is3){
				System.out.println("Not initially connected!");
				return;
			}
					
			boolean is4 = p.is_minimal();
			if(!is4){
				System.out.println("Not minimal!");
				return;
			}	
			
			long stopTime = System.currentTimeMillis();
		    long elapsedTime = stopTime - startTime;
		    timelog = timelog.concat(elapsedTime+",");		    
		}
		timelog = timelog.substring(0,timelog.length()-1);
		timelog = timelog.concat(")\n");
		
		//-----------------------------------------

		 timelog = timelog.concat("fsm = c(");
		for(int k=1; k<=amount; k++){
			int pbp = (int) Math.pow(2, k);
			long startTime = System.currentTimeMillis();
			for(int i=1; i<=pbp; i++){
				//System.out.println("Count "+i);					
				String file = "./"+folder3+"/fsm"+k+".txt";
				FSMProperties p = new FSMProperties(folder0, islog, debug, file);	
								
				boolean is1 = p.is_deterministic();
				if(!is1){
					System.out.println("Not deterministic!");
					return;
				}
										
				boolean is2 = p.is_complete();							
				boolean is3 = p.is_initially_connected();				
				if(!is3){
					System.out.println("Not initially connected!");
					return;
				}
										
				boolean is4 = p.is_minimal();
				if(!is4){
					System.out.println("Not minimal!");
					return;
				}				
			}	
			long stopTime = System.currentTimeMillis();
		    long elapsedTime = stopTime - startTime;
		    timelog = timelog.concat(elapsedTime+",");
		}	
		timelog = timelog.substring(0,timelog.length()-1);
		timelog = timelog.concat(")\n");
		//----------------------------------------------

		String fpath = "./"+folder4+"/timelog.txt";
		FileHandler fh = new FileHandler();
		fh.print_file(timelog, fpath);
	}
	
	@Test
	public void test023_generate_random_ffsms() throws InterruptedException
	{
		FFSMModel gen = new FFSMModel();
	    try {
	    	for(int features=3; features<=10; features++){
	    		 int random_ffsm = 10;
	   	      gen.gen_random_FFSM("increase_random", random_ffsm, features);
	    	}
	    } catch (IOException e) {
	      e.printStackTrace();
	      throw new RuntimeException("Problems with creating the ffsm model files");
	    } 
	}
	
	@Test
	public void test0235_random_number() throws InterruptedException
	{
		Random ran = new Random();
		for(int i=0; i<=20; i++){
			int x = ran.nextInt(6) + 5;
			System.out.println(x);
		}
		
	}
	
	@Test
	public void test024_randomFSMs() throws Exception
	{
		FFSMReaderTest tester = new FFSMReaderTest();
	    try {
	    	FFSMLogger.set_filepath("./increase_random/logs/randomFSM.txt");
	    	FFSMLogger.setup();
	    } catch (IOException e) {
	      e.printStackTrace();
	      throw new RuntimeException("Problems with creating the log files");
	    }
	    String log = "";
		boolean islog = false;
		boolean debug = false;
		//LOGGER.info("Starting");
		
		String folder = "increase_random/fsm";				
		
		for(int i=1; i<=20; i++){
			System.out.println("Count "+i);
			String file = "./"+folder+"/fsm"+i+".txt";
			FSMProperties p = new FSMProperties(folder, islog, debug, file);
			
			if(islog) log = log.concat("---------------------------------------\n");
			if(islog) log = log.concat("\nIdentify Deterministic...\n");
			boolean is1 = p.is_deterministic();
			if(!is1){
				System.out.println("Not deterministic!");
				return;
			}
			
			if(islog) log = log.concat("---------------------------------------\n");
			if(islog) log = log.concat("\nIdentify Complete...\n");			
			boolean is2 = p.is_complete();
			
			if(islog) log = log.concat("---------------------------------------\n");
			if(islog) log = log.concat("\nIdentify Initially Connected...\n");					
			boolean is3 = p.is_initially_connected();
			if(islog) log = log.concat(p.getlog()+"\n");
			if(!is3){				
				System.out.println("Not initially connected!");
				return;
			}
			
			if(islog) log = log.concat("---------------------------------------\n");
			if(islog) log = log.concat("\nIdentify Minimal...\n");	
			boolean is4 = false;
			try {
				 is4 = p.is_minimal();
		    } catch (Exception e) {
		    	System.out.println("Number "+i);
		    	System.out.println(p.getFSMTransitions());
		    }
			if(!is4){
				System.out.println("Not minimal!");
				return;
			}
			if(islog) log = log.concat(p.getlog()+"\n");
			
			if(islog) log = log.concat("---------------------------------------\n");
			if(islog) log = log.concat("\nIs the FSM deterministic?\n");
			if(islog) log = log.concat(is1+"\n");
			
			if(islog) log = log.concat("\nIs the FSM complete?\n");					
			if(islog) log = log.concat(is2+"\n");
			
			if(islog) log = log.concat("\nIs the FSM initially connected?\n");	
			if(islog) log = log.concat(is3+"\n");			
			
			if(islog) log = log.concat("\nIs the FSM minimal?\n");			
			if(islog) log = log.concat(is4+"\n");
			
			if(islog) LOGGER.info(""+log);			
		}	
	}
	
	@Test
	public void test025_check_random_ffsms() throws Exception
	{
		FFSMModel gen = new FFSMModel();
	    	    
	    boolean islog = false;
		boolean debug = false;
	   	int features = 15;
	   	int random_models = 50;
	   	int step = 1;
		String timelog = "data<-data.frame(";
		
		String folder0 = "increase_random/aux";
		String folder1 = "increase_random/feature_models";
		String folder2 = "increase_random/ffsms";
		String folder3 = "increase_random/fsm";
		String folder4 = "increase_random/logs";
		
		for(int i=10; i<=features; i=i+step){			
			gen.gen_random_FFSM("increase_random", random_models, i);	   	    
			timelog = timelog.concat("ffsm"+i+" = c(");
			
			for(int k=1; k<=random_models; k++){	
				long startTime = System.currentTimeMillis();			
				
				FFSMProperties p = new FFSMProperties(folder0, islog, debug);			
				String header = p.read_XML_FeatureModel("./"+folder1+"/example_"+i+"_"+k+".xml");			
							
				String file = "./"+folder2+"/ffsm_"+i+"_"+k+".txt";
				try {
					//System.out.println(header);
					if(!p.set_checkFFSM(file, header)){
						System.out.println("Invalid FFSM!!! " + file);
						return;
					}
				} catch (InterruptedException e) {
					// TODO Auto-generated catch block
					e.printStackTrace();
				}
			
				boolean is1 = p.is_deterministic();				
				if(!is1){
					System.out.println("Not deterministic!");
					return;
				}					
				boolean is2 = p.is_complete();
				boolean is3 = p.is_initially_connected();			
				if(!is3){
					System.out.println("Not initially connected!"+ i + " "+k);
					return;
				}
						
				boolean is4 = p.is_minimal();
				if(!is4){
					System.out.println("Not minimal!");
					return;
				}	
				
				long stopTime = System.currentTimeMillis();
			    long elapsedTime = stopTime - startTime;
			    //elapsedTime = elapsedTime / 1000;
			    timelog = timelog.concat(elapsedTime+",");
			}
			timelog = timelog.substring(0,timelog.length()-1);
			timelog = timelog.concat("),\n");
			
			timelog = timelog.concat("fsm"+i+" = c(");
			HashMap<String, Integer> map = gen.getMap();
			for(String fsm_path : map.keySet()){
				long startTime = System.nanoTime();
				
				//for(int l=1; l<=map.get(fsm_path); l++){
					String file = fsm_path;
					FSMProperties p = new FSMProperties(folder0, islog, debug, file);					
					
					boolean is1 = p.is_deterministic();
					if(!is1){
						System.out.println("Not deterministic!");
						return;
					}
											
					boolean is2 = p.is_complete();							
					boolean is3 = p.is_initially_connected();				
					if(!is3){
						System.out.println("Not initially connected!");
						return;
					}
											
					boolean is4 = p.is_minimal();
					if(!is4){
						System.out.println("Not minimal!");
						return;
					}
				//}
				
				long stopTime = System.nanoTime();
			    long elapsedTime = stopTime - startTime;
			    // one execution of the worst fsm size for ffsm times the ammount of possible configurations
			    System.out.println("File"+fsm_path+" Elapsed time "+elapsedTime+" configs "+map.get(fsm_path));
			    elapsedTime = (elapsedTime * map.get(fsm_path)) / 1000000;	
			    //elapsedTime = elapsedTime / 1000;	
			    timelog = timelog.concat(elapsedTime+",");
			}		
			timelog = timelog.substring(0,timelog.length()-1);
			timelog = timelog.concat("),\n");
		}		
		timelog = timelog.substring(0,timelog.length()-2);
		timelog = timelog.concat(")\nboxplot(data)");		
		//----------------------------------------------

		String fpath = "./"+folder4+"/timelog.txt";
		FileHandler fh = new FileHandler();
		fh.print_file(timelog, fpath);	    
	}
	
	@Test
	public void test026_generate_dot_ffsms() throws InterruptedException
	{
		FFSMModel gen = new FFSMModel();
	    try {
	    	String dotpath = "./increase_random/dots/ffsm.dot";
	    	String ffsm_path = "./increase_random/dots/ffsm.txt";
	    	gen.gen_dot_FFSM(ffsm_path, dotpath);
	    } catch (IOException e) {
	      e.printStackTrace();
	      throw new RuntimeException("Problems with creating the ffsm model files");
	    } 
	}	
	
	@Test
	public void test026_1_generate_dot_ffsms_BCS() throws InterruptedException
	{
		FFSMModel gen = new FFSMModel();
	    try {
	    	String dotpath = "./BCS/ffsm.dot";
	    	String ffsm_path = "./BCS/ffsm.txt";
	    	gen.gen_dot_FFSM(ffsm_path, dotpath);
	    } catch (IOException e) {
	      e.printStackTrace();
	      throw new RuntimeException("Problems with creating the ffsm model files");
	    } 
	}
	
	@Test
	public void test027_check_random_ffsms_sample() throws Exception
	{
		FFSMModel gen = new FFSMModel();
	    	    
	    boolean islog = false;
		boolean debug = false;
	   	//int features = 17;
	   	int population = 60000;
	   	int sample = 1;
	   	int step = 4;
	   	int start = 8;
	   	int end = 12;	   			
		String timelog = "data<-data.frame(";
		
		String folder0 = "increase_random/aux";
		String folder1 = "increase_random/feature_models";
		String folder2 = "increase_random/ffsms";
		String folder3 = "increase_random/fsm";
		String folder4 = "increase_random/logs";
		
		for(int i=start; i<=end; i=i+step){	
			population = population + 2000;
			int samples = gen.gen_random_FFSM_sample("increase_random", population, sample, i);	   	    
			timelog = timelog.concat("ffsm"+i+" = c(");
			
			for(int k=1; k<=samples; k++){	
				long startTime = System.currentTimeMillis();			
				
				FFSMProperties p = new FFSMProperties(folder0, islog, debug);			
				String header = p.read_XML_FeatureModel("./"+folder1+"/example_"+i+"_"+k+".xml");			
							
				String file = "./"+folder2+"/ffsm_"+i+"_"+k+".txt";
				try {
					//System.out.println(header);
					if(!p.set_checkFFSM(file, header)){
						System.out.println("Invalid FFSM!!! " + file);
						return;
					}
				} catch (InterruptedException e) {
					// TODO Auto-generated catch block
					e.printStackTrace();
				}
			
				boolean is1 = p.is_deterministic();				
				if(!is1){
					System.out.println("Not deterministic!");
					return;
				}					
				boolean is2 = p.is_complete();
				boolean is3 = p.is_initially_connected();			
				if(!is3){
					System.out.println("Not initially connected!"+ i + " "+k);
					return;
				}
						
				boolean is4 = p.is_minimal();
				if(!is4){
					System.out.println("Not minimal!");
					return;
				}	
				
				long stopTime = System.currentTimeMillis();
			    long elapsedTime = stopTime - startTime;
			    //elapsedTime = elapsedTime / 1000;
			    timelog = timelog.concat(elapsedTime+",");
			}
			timelog = timelog.substring(0,timelog.length()-1);
			timelog = timelog.concat("),\n");
			
			timelog = timelog.concat("fsm"+i+" = c(");
			HashMap<String, Integer> map = gen.getMap();
			for(String fsm_path : map.keySet()){
				long startTime = System.nanoTime();				
				
				String file = fsm_path;
				FSMProperties p = new FSMProperties(folder0, islog, debug, file);					
				
				boolean is1 = p.is_deterministic();
				if(!is1){
					System.out.println("Not deterministic!");
					return;
				}
										
				boolean is2 = p.is_complete();							
				boolean is3 = p.is_initially_connected();				
				if(!is3){
					System.out.println("Not initially connected!");
					return;
				}
										
				boolean is4 = p.is_minimal();
				if(!is4){
					System.out.println("Not minimal!");
					return;
				}				
				
				long stopTime = System.nanoTime();
			    long elapsedTime = stopTime - startTime;
			    // one execution of the worst fsm size for ffsm times the ammount of possible configurations
			    System.out.println("File"+fsm_path+" Elapsed time "+elapsedTime+" configs "+map.get(fsm_path));
			    elapsedTime = (elapsedTime * map.get(fsm_path)) / 1000000;	
			    //elapsedTime = elapsedTime / 1000;	
			    timelog = timelog.concat(elapsedTime+",");
			}		
			timelog = timelog.substring(0,timelog.length()-1);
			timelog = timelog.concat("),\n");
		}		
		timelog = timelog.substring(0,timelog.length()-2);
		timelog = timelog.concat(")\nboxplot(data)");		
		//----------------------------------------------

		String fpath = "./"+folder4+"/timelog_sample_1_sample.txt";
		FileHandler fh = new FileHandler();
		fh.print_file(timelog, fpath);	    
	}
	
	@Test
	public void test028_check_number_configurations() throws Exception
	{
		FFSMModel gen = new FFSMModel();
		int configs = gen.get_configs_for_ffsm("confs", 14);
		System.out.println(configs);
	}
	
	@Test
	public void test028_check_number_configurations_fsm() throws Exception
	{
		FFSMModel gen = new FFSMModel();
		int configs = gen.get_configs_for_ffsm("./increase/fsm_mid/fsm21.txt");
		System.out.println(configs);
	}
	
	
}
