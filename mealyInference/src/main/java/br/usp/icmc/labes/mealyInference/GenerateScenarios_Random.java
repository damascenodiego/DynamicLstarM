package br.usp.icmc.labes.mealyInference;

import java.io.BufferedReader;
import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.io.InputStreamReader;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.HashSet;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Random;
import java.util.Set;

import com.google.common.collect.MoreCollectors;

import br.usp.icmc.labes.mealyInference.utils.Utils;
import net.automatalib.automata.concepts.InputAlphabetHolder;
import net.automatalib.automata.transout.MutableMealyMachine;
import net.automatalib.automata.transout.impl.FastMealy;
import net.automatalib.automata.transout.impl.FastMealyState;
import net.automatalib.automata.transout.impl.MealyTransition;
import net.automatalib.automata.transout.impl.compact.CompactMealy;
import net.automatalib.automata.transout.impl.compact.CompactMealyTransition;
import net.automatalib.serialization.dot.GraphDOT;
import net.automatalib.util.automata.builders.AutomatonBuilder;
import net.automatalib.util.automata.builders.MealyBuilder;
import net.automatalib.util.automata.copy.AutomatonCopyMethod;
import net.automatalib.util.automata.copy.AutomatonLowLevelCopy;
import net.automatalib.util.automata.minimizer.hopcroft.HopcroftMinimization;
import net.automatalib.util.automata.minimizer.hopcroft.HopcroftMinimization.PruningMode;
import net.automatalib.util.automata.random.RandomAutomata;
import net.automatalib.util.graphs.traversal.DFSVisitor;
import net.automatalib.util.graphs.traversal.GraphTraversal;
import net.automatalib.words.Alphabet;
import net.automatalib.words.Word;
import net.automatalib.words.impl.Alphabets;

public class GenerateScenarios_Random {
	
	private static final int MIN_TOT_STATES = 10;
	private static final int MAX_TOT_STATES = 100;
	private static final int TOT_RND_FSM = 20;
	private static final double PERCENT_TO_RM = 0.40;
	
	private static final boolean RM_INPUTS 			= true;
	private static final boolean RM_STATES 			= true;
	private static final boolean RM_STATES_INPUTS 	= true;


	public static void main(String[] args) {
		try {
			// load mealy machine
			
			Random rand = new Random(1234);

			for (int i = MIN_TOT_STATES; i <= MAX_TOT_STATES; i+=10) {
				
				Alphabet<String> inputs = Alphabets.fromCollection(mkSetOfIntStrings(10));
				Set<Word<String>> outputs = mkSetOfWords(2);
				int numStates=i;
				boolean minimize = true;
				CompactMealy<String, Word<String>> mealy = RandomAutomata.randomMealy(rand, numStates, inputs, outputs, minimize);
				if(mealy.getStates().size()==1){
					i--;
					continue;
				}
				
				
				File folder = new File("./experiments_scenarios_random"+String.join("_", Integer.toString(MIN_TOT_STATES),Integer.toString(MAX_TOT_STATES),Integer.toString(TOT_RND_FSM),Double.toString(PERCENT_TO_RM))+"/ex_"+String.join("_", Integer.toString(inputs.size()), Integer.toString(outputs.size()), Integer.toString(numStates)));
				folder.mkdirs();

				File fsm = new File(folder,"/ex_"+String.join("_", Integer.toString(inputs.size()), Integer.toString(outputs.size()), Integer.toString(numStates)));
				saveDot(fsm, mealy);
				saveFSM(fsm, mealy);

//				folder = new File(folder,"/rnd_fsm/");
				folder.mkdirs();
				
				for (int rndFsmID = 0; rndFsmID < TOT_RND_FSM; rndFsmID++) {
					FastMealy<String, Word<String>> fMealy = null;
					Alphabet<String> abc = null;
					
					if(RM_INPUTS){
						fMealy = removeInputs(mealy); 
						fsm = new File(folder,"/rmInputs/ex_"+String.join("_", Integer.toString(inputs.size()), Integer.toString(outputs.size()), Integer.toString(numStates))+"-"+Integer.toString(rndFsmID));
						abc = fMealy.getInputAlphabet();
						fsm.getParentFile().mkdirs();						
						
						CompactMealy<String, Word<String>> cMealy = HopcroftMinimization.minimizeMealy(fMealy, abc,PruningMode.PRUNE_AFTER);
						
						if(cMealy.getStates().size()==1){
							rndFsmID--;
							continue;
						}
						saveDot(fsm, cMealy);
						saveFSM(fsm, cMealy);
					}
					if(RM_STATES){
						fMealy = removeStates(mealy);
						fsm = new File(folder,"/rmStates/ex_"+String.join("_", Integer.toString(inputs.size()), Integer.toString(outputs.size()), Integer.toString(numStates))+"-"+Integer.toString(rndFsmID));
						abc = fMealy.getInputAlphabet();
						fsm.getParentFile().mkdirs();					
						
						CompactMealy<String, Word<String>> cMealy = HopcroftMinimization.minimizeMealy(fMealy, abc,PruningMode.PRUNE_AFTER);
						
						if(cMealy.getStates().size()==1){
							rndFsmID--;
							continue;
						}
						saveDot(fsm, cMealy);
						saveFSM(fsm, cMealy);
					}
					if(RM_STATES_INPUTS){
						fMealy = removeInputsStates(mealy);
						fsm = new File(folder,"/rmInputsStates/ex_"+String.join("_", Integer.toString(inputs.size()), Integer.toString(outputs.size()), Integer.toString(numStates))+"-"+Integer.toString(rndFsmID));
						abc = fMealy.getInputAlphabet();
						fsm.getParentFile().mkdirs();					
						
						CompactMealy<String, Word<String>> cMealy = HopcroftMinimization.minimizeMealy(fMealy, abc,PruningMode.PRUNE_AFTER);
						
						if(cMealy.getStates().size()==1){
							rndFsmID--;
							continue;
						}
						saveDot(fsm, cMealy);
						saveFSM(fsm, cMealy);
					}
					
					
				}

			}
		} catch (Exception e) {
			e.printStackTrace();
		}
	}
	
	private static FastMealy<String, Word<String>> removeStates(CompactMealy<String, Word<String>> mealy) {
		List<String> abcCol = new ArrayList<>(mealy.getInputAlphabet().size());
		abcCol.addAll(mealy.getInputAlphabet());

		// remainder inputs
		Alphabet<String> abc = Alphabets.fromCollection(abcCol);

		// copy the FSM by excluding a part of the inputs
		FastMealy<String, Word<String>> fMealy = new FastMealy<>(abc);
		AutomatonLowLevelCopy.copy(AutomatonCopyMethod.DFS, mealy, abc, fMealy); 

		// remove a subset of all states
		List<FastMealyState<Word<String>>> statesCol = new ArrayList<>(fMealy.getStates().size());
		statesCol.addAll(fMealy.getStates());
		statesCol.remove(fMealy.getInitialState());
		// shuffle to remove the last 'percent2Rm'% states
		Collections.shuffle(statesCol);
		int lastState2Rm = (int)Math.round(statesCol.size()*(PERCENT_TO_RM));
		for (int ii = 0; ii < lastState2Rm ; ii++){
			statesCol.remove(0);
		}
		// find remainder states by removing the states from statesCol 
		for (FastMealyState<Word<String>> toRm : statesCol) {
			for (FastMealyState<Word<String>> si : fMealy.getStates()) {
				for (String in : fMealy.getInputAlphabet()) {
					MealyTransition<FastMealyState<Word<String>>, Word<String>> tr = fMealy.getTransition(si, in);
					if(tr!=null){
						FastMealyState<Word<String>> sj = tr.getSuccessor();
						if(sj.equals(toRm)){
							fMealy.removeAllTransitions(si, in);
							fMealy.setTransition(si, in, si, tr.getOutput());
						}
					}
				}
			}
			fMealy.removeAllTransitions(toRm);
			fMealy.removeState(toRm);	
		}
		return fMealy;
	}

	private static FastMealy<String, Word<String>> removeInputs(CompactMealy<String, Word<String>> mealy) {
		// remove a subset of all inputs
		List<String> abcCol = new ArrayList<>(mealy.getInputAlphabet().size());
		abcCol.addAll(mealy.getInputAlphabet());
		
		// shuffle to remove 'percent2Rm'% inputs
		Collections.shuffle(abcCol);
		int lastIn2Rm = (int)Math.round(abcCol.size()*(PERCENT_TO_RM));
		for (int ii = 0; ii < lastIn2Rm ; ii++){
			abcCol.remove(0);
		}
		// remainder inputs
		Alphabet<String> abc = Alphabets.fromCollection(abcCol);

		// copy the FSM by excluding a part of the inputs
		FastMealy<String,Word<String>> fMealy = new FastMealy<>(abc);
		AutomatonLowLevelCopy.copy(AutomatonCopyMethod.DFS, mealy, abc, fMealy);
		return fMealy;
	}
	
	private static FastMealy<String, Word<String>> removeInputsStates(CompactMealy<String, Word<String>> mealy) {
		List<String> abcCol = new ArrayList<>(mealy.getInputAlphabet().size());
		abcCol.addAll(mealy.getInputAlphabet());

		// remainder inputs
		Alphabet<String> abc = Alphabets.fromCollection(abcCol);

		// copy the FSM by excluding a part of the inputs
		FastMealy<String, Word<String>> fMealy = new FastMealy<>(abc);
		AutomatonLowLevelCopy.copy(AutomatonCopyMethod.DFS, mealy, abc, fMealy); 

		// remove a subset of all states
		List<FastMealyState<Word<String>>> statesCol = new ArrayList<>(fMealy.getStates().size());
		statesCol.addAll(fMealy.getStates());
		statesCol.remove(fMealy.getInitialState());
		// shuffle to remove the last 'percent2Rm'% states
		Collections.shuffle(statesCol);
		int lastState2Rm = (int)Math.round(statesCol.size()*(PERCENT_TO_RM));
		for (int ii = 0; ii < lastState2Rm ; ii++){
			statesCol.remove(0);
		}
		// find remainder states by removing the states from statesCol 
		for (FastMealyState<Word<String>> toRm : statesCol) {
			for (FastMealyState<Word<String>> si : fMealy.getStates()) {
				for (String in : fMealy.getInputAlphabet()) {
					MealyTransition<FastMealyState<Word<String>>, Word<String>> tr = fMealy.getTransition(si, in);
					if(tr!=null){
						FastMealyState<Word<String>> sj = tr.getSuccessor();
						if(sj.equals(toRm)){
							fMealy.removeAllTransitions(si, in);
							fMealy.setTransition(si, in, si, tr.getOutput());
						}
					}
				}
			}
			fMealy.removeAllTransitions(toRm);
			fMealy.removeState(toRm);	
		}
		
		// shuffle to remove 'percent2Rm'% inputs
		Collections.shuffle(abcCol);
		int lastIn2Rm = (int)Math.round(abcCol.size()*(PERCENT_TO_RM));
		for (int ii = 0; ii < lastIn2Rm ; ii++){
			abcCol.remove(0);
		}
		// remainder inputs
		abc = Alphabets.fromCollection(abcCol);

		// copy the FSM by excluding a part of the inputs
		fMealy = new FastMealy<>(abc);
		AutomatonLowLevelCopy.copy(AutomatonCopyMethod.DFS, mealy, abc, fMealy);
		return fMealy;
	}

	private static Set<Word<String>> mkSetOfWords(int n_val) {
		Set<String> intCol = mkSetOfIntStrings(n_val);
		Set<Word<String>> outCol = new HashSet<>(n_val);
		
		Word<String> w;
		for (String string : intCol) {
			w = Word.epsilon();
			w=w.append(string);
			outCol.add(w);
		}
		return outCol;
	}

	private static Set<String> mkSetOfIntStrings(int n_val) {
		Set<String> outCol = new HashSet<>(n_val);
		
		for (int i = 0; i < n_val; i++) {
			outCol.add(Integer.toString(i));
		}
		
		return outCol;
	}

	private static void saveDot(File fsm, MutableMealyMachine mealy) throws IOException, InterruptedException {
		// save sul as dot (i.e., mealyss)
		File sul_model = new File(fsm.getParentFile(),fsm.getName()+".dot");
		FileWriter fw = new FileWriter(sul_model);
		Alphabet<String> abc = ((InputAlphabetHolder<String>)mealy).getInputAlphabet();
		GraphDOT.write(mealy, abc, fw);
		
//		String[] commands0 = {"dot","-T", "png", "-o", sul_model.getParentFile().getAbsolutePath()+"/"+fsm.getName()+".png", sul_model.getAbsolutePath()};
//		System.out.println(String.join("\n",commands0));
//		String result0 = getProcessOutput(commands0);
//		System.out.println(result0);
		
	}
	
	private static void saveFSM(File fsm, FastMealy<String, Word<String>> mealy) throws IOException, InterruptedException {
		// save sul as dot (i.e., mealyss)
		File sul_model = new File(fsm.getParentFile(),fsm.getName()+".fsm");
		FileWriter fw = new FileWriter(sul_model);
		
		List<FastMealyState<Word<String>>> states = new ArrayList<>();
		states.addAll(mealy.getStates());
		states.remove(mealy.getInitialState());
		states.add(0, mealy.getInitialState());
		for (FastMealyState<Word<String>> si : mealy.getStates()) {
			for (String in : mealy.getInputAlphabet()) {
				MealyTransition<FastMealyState<Word<String>>, Word<String>> tr = mealy.getTransition(si, in);
				if(tr!=null){
					FastMealyState<Word<String>> sj = tr.getSuccessor();
					
					fw.append(si.toString());
					fw.append(" -- ");
					fw.append(in);
					fw.append(" / ");
					fw.append(tr.getOutput().toString());
					fw.append(" -> ");
					fw.append(sj.toString());
					fw.append("\n");
				}
			}
		}
		fw.close();
	}
	
	
	private static void saveFSM(File fsm, CompactMealy<String, Word<String>> mealy) throws IOException, InterruptedException {
		// save sul as dot (i.e., mealyss)
		File sul_model = new File(fsm.getParentFile(),fsm.getName()+".fsm");
		FileWriter fw = new FileWriter(sul_model);
		
		List<Integer> states = new ArrayList<>();
		states.addAll(mealy.getStates());
		states.remove(mealy.getIntInitialState());
		states.add(0, mealy.getIntInitialState());
		for (Integer si : states) {
			for (String in : mealy.getInputAlphabet()) {
				CompactMealyTransition<Word<String>> tr = mealy.getTransition(si, in);
				if(tr!=null){
					Integer sj = tr.getSuccId();
					
					fw.append(mealy.getState(si).toString());
					fw.append(" -- ");
					fw.append(in);
					fw.append(" / ");
					fw.append(tr.getOutput().toString());
					fw.append(" -> ");
					fw.append(mealy.getState(sj).toString());
					fw.append("\n");
				}
			}
		}
		fw.close();
	}

	public static String getProcessOutput(String[] commands) throws IOException, InterruptedException
    {
        ProcessBuilder processBuilder = new ProcessBuilder(commands);

        processBuilder.redirectErrorStream(true);

        Process process = processBuilder.start();
        StringBuilder processOutput = new StringBuilder();

        try (BufferedReader processOutputReader = new BufferedReader(
                new InputStreamReader(process.getInputStream()));)
        {
            String readLine;

            while ((readLine = processOutputReader.readLine()) != null)
            {
                processOutput.append(readLine + System.lineSeparator());
            }

            process.waitFor();
        }

        return processOutput.toString().trim();
    }

}
