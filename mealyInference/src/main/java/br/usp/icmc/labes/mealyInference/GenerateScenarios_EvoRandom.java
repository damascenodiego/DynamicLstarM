package br.usp.icmc.labes.mealyInference;

import java.io.BufferedReader;
import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.io.InputStreamReader;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Random;
import java.util.Set;


import net.automatalib.automata.concepts.InputAlphabetHolder;
import net.automatalib.automata.transout.MutableMealyMachine;
import net.automatalib.automata.transout.impl.FastMealy;
import net.automatalib.automata.transout.impl.FastMealyState;
import net.automatalib.automata.transout.impl.MealyTransition;
import net.automatalib.automata.transout.impl.compact.CompactMealy;
import net.automatalib.automata.transout.impl.compact.CompactMealyTransition;
import net.automatalib.serialization.dot.GraphDOT;
import net.automatalib.util.automata.Automata;
import net.automatalib.util.automata.copy.AutomatonCopyMethod;
import net.automatalib.util.automata.copy.AutomatonLowLevelCopy;
import net.automatalib.util.automata.random.RandomAutomata;
import net.automatalib.util.automata.minimizer.hopcroft.HopcroftMinimization;
import net.automatalib.util.automata.minimizer.hopcroft.HopcroftMinimization.PruningMode;
import net.automatalib.words.Alphabet;
import net.automatalib.words.Word;
import net.automatalib.words.impl.Alphabets;

public class GenerateScenarios_EvoRandom {
	
	private static final int MIN_TOT_STATES = 100;
	private static final int MAX_TOT_STATES = 5000;
	private static final int TOT_RND_FSM = 10;
	private static final int TOT_VER_FSM = 5;
	
	public static Random rand = new Random(1234);

	public static List<Word<String>> zerone = new ArrayList<>();
	
	public static void main(String[] args) {
		try {
			// load mealy machine

			Word<String> wordIn = Word.epsilon();
			zerone.add(wordIn.append("0"));
			zerone.add(wordIn.append("1"));
			
			
			for (int prog = 0; prog < TOT_RND_FSM; prog++) {

				for (int s_size = MIN_TOT_STATES; s_size <= MAX_TOT_STATES; s_size+=MIN_TOT_STATES) {
					File folder = new File("./experiments_scenarios_EvoRandom/evoRandom_"+String.join("_", 
							"s",Integer.toString(MIN_TOT_STATES),Integer.toString(MAX_TOT_STATES), 
							"p",Integer.toString(TOT_RND_FSM),
							"v",Integer.toString(TOT_VER_FSM)
							)+"/s_"+String.format("%04d", s_size)+"/");
					folder.mkdirs();
					Alphabet<String> i_set = Alphabets.fromCollection(mkSetOfIntStrings(10));
					Set<Word<String>> o_set = new HashSet<>(zerone);
					boolean minimize = true;
					CompactMealy<String, Word<String>> evo_mealy = null;
					do{
						evo_mealy = RandomAutomata.randomMealy(rand, s_size, i_set, o_set,minimize);
					}while(evo_mealy.getStates().size()==1);

					File fsm = new File(folder,"p_"+String.format("%03d", prog)+"/v_000");
					fsm.getParentFile().mkdirs();
					saveFSM(fsm, evo_mealy);
					saveDot(fsm, evo_mealy);

					for (int version = 1; version < TOT_VER_FSM; version++) {

						fsm = new File(folder,"p_"+String.format("%03d", prog)+"/v_"+String.format("%03d", version));
						int opt = rand.nextInt(5);
						switch (opt) {
						case 0: // add new state
							evo_mealy = op_addState(evo_mealy);
							break;
						case 1: // remove existing state
							evo_mealy = op_rmState(evo_mealy);
							break;
						case 2: // add input symbol
							evo_mealy = op_addInput(evo_mealy);
							break;
						case 3: // remove input symbol
							evo_mealy = op_rmInput(evo_mealy);
							break;
						case 4: // change tail state
							evo_mealy = op_changeTail(evo_mealy);
							break;
						}
						if(evo_mealy!=null){
							saveFSM(fsm, evo_mealy);
							saveDot(fsm, evo_mealy);
						}
					}
				}
			}
		} catch (Exception e) {
			e.printStackTrace();
		}
	}
	
	private static CompactMealy<String, Word<String>> op_addState(CompactMealy<String, Word<String>> in_mealy) {
		// inputs
		Alphabet<String> abc = in_mealy.getInputAlphabet();
		// copy the FSM 
		FastMealy<String, Word<String>> fMealy = new FastMealy<>(abc);
		AutomatonLowLevelCopy.copy(AutomatonCopyMethod.DFS, in_mealy, abc, fMealy);
		
		List<FastMealyState<Word<String>>> qSet = new ArrayList<>(fMealy.getStates());
		
		// select random transition (i.e, origin state + input)
		FastMealyState<Word<String>> si = qSet.get(rand.nextInt(qSet.size()));
		String in  = abc.getSymbol(rand.nextInt(abc.size()));

		// get transition 'tr'
		MealyTransition<FastMealyState<Word<String>>, Word<String>> tr = fMealy.getTransition(si, in);
		// get tail state + output symbol
		FastMealyState<Word<String>> sj = tr.getSuccessor();
		Word<String> out = tr.getOutput();

		// remove 'tr'
		fMealy.removeAllTransitions(si,in);
		
		FastMealyState<Word<String>> newState = fMealy.addState();
		MealyTransition<FastMealyState<Word<String>>, Word<String>> new_tr = null; 
		for (String symbol : abc) {
			if(symbol == in){
				new_tr = new MealyTransition<FastMealyState<Word<String>>, Word<String>>(newState, out);
				fMealy.addTransition(si, symbol, new_tr);
			}
			new_tr = new MealyTransition<FastMealyState<Word<String>>, Word<String>>(qSet.get(rand.nextInt(qSet.size())), (rand.nextBoolean()?zerone.get(0):zerone.get(1)));
			fMealy.addTransition(newState, symbol, new_tr);

		}

		CompactMealy<String, Word<String>> cMealy = HopcroftMinimization.minimizeMealy(fMealy, abc,PruningMode.PRUNE_AFTER);
		return cMealy;
	}

	private static CompactMealy<String, Word<String>> op_rmState(CompactMealy<String, Word<String>> in_mealy) {
		// remainder inputs
		Alphabet<String> abc = in_mealy.getInputAlphabet();
	
		List<Integer> qSet = new ArrayList<>(in_mealy.getStates());
		qSet.remove(in_mealy.getInitialState());
		
		Collections.shuffle(qSet);
	
		Integer state2Rm = qSet.remove(0);
		qSet.add(in_mealy.getInitialState());
		
		// copy the FSM 
		FastMealy<String, Word<String>> fMealy = new FastMealy<>(abc);
		
		// map of stateId -> FastMealyState
		Map<Integer,FastMealyState<Word<String>>> statesMap = new HashMap<>();
		statesMap.put(in_mealy.getInitialState(), fMealy.addInitialState());		
	
		for (Integer toAdd : qSet) {
			Integer si = in_mealy.getState(toAdd);
			// create state_si, if missing
			if(!statesMap.containsKey(si)) statesMap.put(si, fMealy.addState());
			// get state_si
			FastMealyState<Word<String>> state_si = statesMap.get(si);
			// iterate for each input symbol
			for (String in : in_mealy.getInputAlphabet()) {
				CompactMealyTransition<Word<String>> tr = in_mealy.getTransition(si, in);				
				
				int sj = tr.getSuccId();
				FastMealyState<Word<String>> state_sj = null; 
					
				if(sj == state2Rm){
					sj = nextStateToKeep(in_mealy,si,in,state2Rm);
				}
				if(!statesMap.containsKey(sj)) statesMap.put(sj, fMealy.addState());
				state_sj = statesMap.get(sj);
				
				MealyTransition<FastMealyState<Word<String>>, Word<String>> transition = new MealyTransition<FastMealyState<Word<String>>, Word<String>>(state_sj, (rand.nextBoolean()?zerone.get(0):zerone.get(1)));
				fMealy.addTransition(state_si, in, transition); 
			}
		}
		
		CompactMealy<String, Word<String>> cMealy = HopcroftMinimization.minimizeMealy(fMealy, abc,PruningMode.PRUNE_AFTER);
		return cMealy;
	}

	private static CompactMealy<String, Word<String>> op_addInput(CompactMealy<String, Word<String>> in_mealy) {
		// inputs
		Alphabet<String> abc = in_mealy.getInputAlphabet();
		
				// copy the FSM 
		FastMealy<String, Word<String>> fMealy = new FastMealy<>(abc);
		AutomatonLowLevelCopy.copy(AutomatonCopyMethod.DFS, in_mealy, abc, fMealy);
		
		List<FastMealyState<Word<String>>> qSet = new ArrayList<>(fMealy.getStates());
		
		int max=0;
		for (String in : abc) {
			int val = Integer.valueOf(in);
			if(max < val) max = val;
		}
		max++;
		
		String newInput = Integer.toString(max);
		
		fMealy.addAlphabetSymbol(newInput);
		
		for (FastMealyState<Word<String>> si : qSet) {
			FastMealyState<Word<String>> sj = qSet.get(rand.nextInt(qSet.size()));
			
			MealyTransition<FastMealyState<Word<String>>, Word<String>> transition = new MealyTransition<FastMealyState<Word<String>>, Word<String>>(sj, (rand.nextBoolean()?zerone.get(0):zerone.get(1)));
			fMealy.addTransition(si, newInput, transition);
			
		}
		
		CompactMealy<String, Word<String>> cMealy = HopcroftMinimization.minimizeMealy(fMealy, abc,PruningMode.PRUNE_AFTER);
		return cMealy;
	}

	private static CompactMealy<String, Word<String>> op_rmInput(CompactMealy<String, Word<String>> in_mealy) {
		// remove a subset of all inputs
		List<String> abcCol = new ArrayList<>(in_mealy.getInputAlphabet().size());
		abcCol.addAll(in_mealy.getInputAlphabet());

		// shuffle to remove 'percent2Rm'% inputs
		Collections.shuffle(abcCol);
		abcCol.remove(0);
		
		// remainder inputs
		Alphabet<String> abc = Alphabets.fromCollection(abcCol);

		// copy the FSM by excluding a part of the input set
		CompactMealy<String, Word<String>> cMealy = HopcroftMinimization.minimizeMealy(in_mealy, abc,PruningMode.PRUNE_AFTER);
		return cMealy;
	}

	private static CompactMealy<String, Word<String>> op_changeTail(CompactMealy<String, Word<String>> in_mealy) {
		// inputs
		Alphabet<String> abc = in_mealy.getInputAlphabet();
		// copy the FSM 
		FastMealy<String, Word<String>> fMealy = new FastMealy<>(abc);
		AutomatonLowLevelCopy.copy(AutomatonCopyMethod.DFS, in_mealy, abc, fMealy);
		
		List<FastMealyState<Word<String>>> qSet = new ArrayList<>(fMealy.getStates());
		
		// select random transition (i.e, origin state + input)
		FastMealyState<Word<String>> si = qSet.get(rand.nextInt(qSet.size()));
		String in  = abc.getSymbol(rand.nextInt(abc.size()));
		// remove transition
		fMealy.removeAllTransitions(si,in);
		
		FastMealyState<Word<String>> sj = qSet.get(rand.nextInt(qSet.size()));
		

		MealyTransition<FastMealyState<Word<String>>, Word<String>> new_tr = new MealyTransition<FastMealyState<Word<String>>, Word<String>>(sj, (rand.nextBoolean()?zerone.get(0):zerone.get(1)));
		fMealy.addTransition(si, in, new_tr);
		
		CompactMealy<String, Word<String>> cMealy = HopcroftMinimization.minimizeMealy(fMealy, abc,PruningMode.PRUNE_AFTER);
		return cMealy;
	}

	private static int nextStateToKeep(CompactMealy<String, Word<String>> in_mealy, Integer stateId, String inputIdx, Integer state2Rm) {
		CompactMealyTransition<Word<String>> tr = in_mealy.getTransition(stateId, inputIdx);
		if(tr !=null && tr.getSuccId()!= state2Rm){
			return tr.getSuccId(); 
		}
		return stateId;
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
//		//System.out.println(result0);
		
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
