/**
 * 
 */
package br.usp.icmc.labes.mealyInference;

import java.io.BufferedReader;
import java.io.File;
import java.io.FileOutputStream;
import java.io.FileReader;
import java.io.FileWriter;
import java.io.FilenameFilter;
import java.io.IOException;
import java.io.PrintStream;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Random;
import java.util.Set;
import java.util.logging.FileHandler;
import java.util.logging.Level;
import java.util.logging.LogRecord;
import java.util.logging.SimpleFormatter;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import de.learnlib.algorithms.dhc.mealy.MealyDHC;
import de.learnlib.algorithms.lstargeneric.ce.ObservationTableCEXHandler;
import de.learnlib.algorithms.lstargeneric.ce.ObservationTableCEXHandlers;
import de.learnlib.algorithms.lstargeneric.closing.ClosingStrategies;
import de.learnlib.algorithms.lstargeneric.closing.ClosingStrategy;
import de.learnlib.algorithms.lstargeneric.mealy.ExtensibleLStarMealy;
import de.learnlib.algorithms.lstargeneric.mealy.ExtensibleLStarMealyBuilder;
import de.learnlib.api.EquivalenceOracle;
import de.learnlib.api.LearningAlgorithm;
import de.learnlib.api.MembershipOracle;
import de.learnlib.api.SUL;
import de.learnlib.cache.mealy.MealyCacheOracle;
import de.learnlib.cache.mealy.MealyCaches;
import de.learnlib.eqtests.basic.SimulatorEQOracle;
import de.learnlib.eqtests.basic.mealy.RandomWalkEQOracle;
import de.learnlib.examples.mealy.ExampleCoffeeMachine;
import de.learnlib.examples.mealy.ExampleCoffeeMachine.Input;
import de.learnlib.experiments.Experiment;
import de.learnlib.experiments.Experiment.MealyExperiment;
import de.learnlib.logging.LearnLogger;
import de.learnlib.oracles.DefaultQuery;
import de.learnlib.oracles.ResetCounterSUL;
import de.learnlib.oracles.SULOracle;
import de.learnlib.oracles.SimulatorOracle;
import de.learnlib.oracles.SymbolCounterSUL;
import de.learnlib.simulator.sul.MealySimulatorSUL;
import de.learnlib.statistics.SimpleProfiler;
import de.learnlib.statistics.StatisticSUL;

import net.automatalib.automata.transout.MealyMachine;
import net.automatalib.automata.transout.impl.compact.CompactMealy;
import net.automatalib.graphs.concepts.GraphViewable;
import net.automatalib.util.graphs.dot.GraphDOT;
import net.automatalib.words.Alphabet;
import net.automatalib.words.Word;
import net.automatalib.words.WordBuilder;
import net.automatalib.words.impl.Alphabets;

/**
 * @author damasceno
 *
 */
public class Example {

	private static final String OMEGA_SYMBOL = "Ω";
	private static int total_reps = 30;

	public static void main(String[] args) throws Exception {


		Random rnd_seed = new Random(1);

		// set closing strategy
		ClosingStrategy strategy 			= ClosingStrategies.CLOSE_FIRST;
		// set CE processing approach
		ObservationTableCEXHandler handler 	= ObservationTableCEXHandlers.RIVEST_SCHAPIRE_ALLSUFFIXES;

		// reused inputs
		Set<Word<String>> allSuffixes = new HashSet<Word<String>>();
		
		// sets of FSMs to be inferred
		File[ ] dirs = {
				new File("Fragal_Experiment_Pack/LogicProcessor/increase/fsm"),
				new File("Fragal_Experiment_Pack/LogicProcessor/increase/fsm_mid"),
				new File("Fragal_Experiment_Pack/LogicProcessor/increase/fsm_best"),
				new File("Fragal_Experiment_Pack/LogicProcessor/increase_random/fsm"),
		};
		
		String scenario_name ;
		String config_name;
		String step_id;
		
		// configurations to be considered
		boolean[][] configs =  {
				//				{ true, 	true, 	true }, // ce_cache_rev

				//				{ true, 	false, 	true }, // cache_rev				
				{ false, 	true, 	true }, // ce_cache
				//				{ true, 	true, 	false}, // ce_rev

				{ false, 	false, 	true }, // cache
				{ false, 	true, 	false}, // ce				
				//				{ true, 	false, 	false}, // rev
				{ false, 	false, 	false}, // NONE

		};

		// for each set of FSMs...
		for (File dir : dirs) {

			String [] files = dir.list(new FilenameFilter() {
				@Override
				public boolean accept(File dir, String name) { return name.matches("fsm[0-9_]+.txt");}
			});

			// logfile for each set of FSM 
			FileHandler fh = new FileHandler(dir.getParentFile().getName()+"_"+dir.getName()+".log");
			fh.setFormatter(new SimpleFormatter());

			LearnLogger logger; 

			logger = LearnLogger.getLogger(SimpleProfiler.class);			
			logger.setUseParentHandlers(false);			  
			logger.addHandler(fh);

			logger = LearnLogger.getLogger(Experiment.class);			
			logger.setUseParentHandlers(false);			  
			logger.addHandler(fh);
			
			// for each configuration...
			for(boolean[] conf: configs){

				boolean okReverse  = conf[0];
				boolean okCe	   = conf[1];
				boolean okFilter   = conf[2];

				if(okReverse) {
					Arrays.sort(files,Collections.reverseOrder());
				}else{
					Arrays.sort(files);
				}

				// repeat inference _total_reps_ times
				for (int i = 0; i < total_reps ; i++)
				{		
					// cleanup set with inputs to be reused
					allSuffixes.clear();

					// used for increase_random set
					Set<String> inferred = new HashSet<String>();
					
					for (String file_s : files) {
						
						if(dir != dirs[3]){
							scenario_name = dir.getName();
						}else{
							scenario_name = file_s.replaceFirst("_[0-9]+.txt", "");
							// first FSM inferred from an specific subset of FSMs from increse_random 
							// ( e.g. fsm_003_001.txt, fsm_004_001.txt ... )
							if(!inferred.contains(scenario_name)){
								allSuffixes.clear();
								inferred.add(scenario_name);
							}
							scenario_name = "random"+file_s.replaceFirst("_[0-9]+.txt", "").replaceAll("fsm_", "_");
						}


						StringBuilder sb = new StringBuilder();

						if (okCe) sb.append(".ce");
						if (okFilter) sb.append(".cache");
						if (okReverse) sb.append(".rev");

						if(sb.length()>0){
							config_name = sb.toString().substring(1).replaceAll("_", "");
						}else{
							config_name = "none";
						}
						
						step_id = file_s.replaceFirst("fsm_[0-9]+_", "").replaceAll("[a-z.]", "");
								
						sb.append(".log");

						// load mealy machine
						File f = new File(dir,file_s);
						CompactMealy<String, Word<String>> mealyss = loadMealyMachine(f);

						// SUL simulator
						SUL<String,Word<String>> sulSim = new MealySimulatorSUL(mealyss, OMEGA_SYMBOL);

						// membership oracle for counting queries wraps sul
						StatisticSUL<String, Word<String>>  mqSul_sym = new SymbolCounterSUL<>("membership queries", sulSim);
						StatisticSUL<String, Word<String>>  mqSul_rst = new ResetCounterSUL <>("membership queries", mqSul_sym);			
						MembershipOracle<String, Word<Word<String>>> mqOracle = new SULOracle<String, Word<String>>(mqSul_rst);

						// use caching in order to avoid duplicate queries
						if(okFilter)  mqOracle = MealyCaches.createCache(mealyss.getInputAlphabet(), mqOracle);

						// equivalence oracle for counting queries wraps sul
						StatisticSUL<String, Word<String>> eqSul_sym = new SymbolCounterSUL<>("equivalence queries", sulSim);
						StatisticSUL<String, Word<String>> eqSul_rst = new ResetCounterSUL<>("equivalence queries", eqSul_sym);
						EquivalenceOracle<MealyMachine<?, String, ?, Word<String>>, String, Word<Word<String>>> mealySymEqOracle 
								= new RandomWalkEQOracle<String, Word<String>>(
										0.05, // reset SUL w/ this probability before a step 
										10000, // max steps (overall)
										true, // reset step count after counterexample 
										rnd_seed, // make results reproducible 
										eqSul_rst
										);

						// reuse all inputs (suffixes) using the same alphabet
						Set<Word<String>> initCes = new HashSet<Word<String>>();
						if (okCe){
							for (Word<String> word : allSuffixes) {
								boolean inclOk = true;
								for (String symbol : word) {
									if(!mealyss.getInputAlphabet().containsSymbol(symbol) || initCes.contains(word)){
										inclOk = false;
										break;
									}			
								}
								if(inclOk){
									initCes.add(word);
								}
							}
						}

						logger.logEvent("Scenario name: "+scenario_name);
						logger.logEvent("Configuration: "+config_name);
						logger.logEvent("Step: "+step_id);						
						
						
						///////////////////////////////////////////////
						// Run the experiment using MealyExperiment  //
						///////////////////////////////////////////////

						// Empty list of prefixes 
						List<Word<String>> initialPrefixes = new ArrayList<Word<String>>();

						// Empty list of suffixes => minimal compliant set
						List<Word<String>> initSuffixes = new ArrayList<Word<String>>();
						
						// reuse suffixes previously considered 
						initSuffixes.addAll(initCes);

						// construct L* instance 
						ExtensibleLStarMealyBuilder<String, Word<String>> builder = new ExtensibleLStarMealyBuilder<String, Word<String>>();
						builder.setAlphabet(mealyss.getInputAlphabet());
						builder.setOracle(mqOracle);
						//			builder.setInitialPrefixes(initPrefixes);
						builder.setInitialSuffixes(initSuffixes);
						builder.setCexHandler(handler);
						builder.setClosingStrategy(strategy);

						ExtensibleLStarMealy<String, Word<String>> learner = builder.create();

						// The experiment will execute the main loop of active learning
						MealyExperiment<String, Word<String>> experiment = new MealyExperiment<String, Word<String>> (learner, mealySymEqOracle, mealyss.getInputAlphabet());

						// turn on time profiling
						experiment.setProfile(true);

						// enable logging of models
						experiment.setLogModels(true);

						// run experiment
						experiment.run();

						// save 
						allSuffixes.addAll(learner.getObservationTable().getSuffixes());

						// profiling
						SimpleProfiler.logResults();

						// learning statistics
						logger.logStatistic(mqSul_rst.getStatisticalData());
						logger.logStatistic(mqSul_sym.getStatisticalData());
						logger.logStatistic(eqSul_rst.getStatisticalData());
						logger.logStatistic(eqSul_sym.getStatisticalData());

						if(learner.getHypothesisModel().getStates().size() != mealyss.getStates().size()){
							logger.log(new LogRecord(Level.INFO, "ERROR: Number of states does not match!"));
						}

					}

				}
			}
			fh.close();
		}
		generateTabularLog();
		
	}



	private static CompactMealy<String, Word<String>> loadMealyMachine(File f) throws Exception {

		Pattern kissLine = Pattern.compile("\\W*(\\w+)\\W+--\\W+(\\w+)\\W*/\\W*(\\w+)\\W+->\\W+(\\w+)\\W*");

		BufferedReader br = new BufferedReader(new FileReader(f));

		List<String[]> trs = new ArrayList<String[]>();

		List<String> abc = new ArrayList<>();

		//		int count = 0;

		while(br.ready()){
			String line = br.readLine();
			Matcher m = kissLine.matcher(line);
			if(m.matches()){
				//				System.out.println(m.group(0));
				//				System.out.println(m.group(1));
				//				System.out.println(m.group(2));
				//				System.out.println(m.group(3));
				//				System.out.println(m.group(4));

				String[] tr = new String[4];
				tr[0] = m.group(1);
				tr[1] = m.group(2); 
				if(!abc.contains(tr[1])){
					abc.add(tr[1]);
				}
				tr[2] = m.group(3);
				tr[3] = m.group(4);
				trs.add(tr);
			}
			//			count++;
		}

		br.close();

		Alphabet<String> alphabet = Alphabets.fromCollection(abc);
		CompactMealy<String, Word<String>> mealym = new CompactMealy<String, Word<String>>(alphabet);

		Map<String,Integer> states = new HashMap<String,Integer>();
		Integer si=null,sf=null;

		Map<String,Word<String>> words = new HashMap<String,Word<String>>();		


		WordBuilder<String> aux = new WordBuilder<>();

		aux.clear();
		aux.add(OMEGA_SYMBOL);
		words.put(OMEGA_SYMBOL, aux.toWord());


		for (String[] tr : trs) {
			if(!states.containsKey(tr[0])) states.put(tr[0], mealym.addState());
			if(!states.containsKey(tr[3])) states.put(tr[3], mealym.addState());

			si = states.get(tr[0]);
			sf = states.get(tr[3]);

			if(!words.containsKey(tr[1])){
				aux.clear();
				aux.add(tr[1]);
				words.put(tr[1], aux.toWord());
			}
			if(!words.containsKey(tr[2])){
				aux.clear();
				aux.add(tr[2]);
				words.put(tr[2], aux.toWord());
			}
			mealym.addTransition(si, tr[1], sf, words.get(tr[2]));
		}

		for (Integer st : mealym.getStates()) {
			for (String in : alphabet) {
				//				System.out.println(mealym.getTransition(st, in));
				if(mealym.getTransition(st, in)==null){
					mealym.addTransition(st, in, st, words.get(OMEGA_SYMBOL));
				}
			}
		}


		mealym.setInitialState(states.get(trs.get(0)[0]));

		return mealym;
	}


	public static void removeSelfLoops(CompactMealy<String, Word<String>> mealy){
		for (Integer st : mealy.getStates()) {
			for (String in : mealy.getInputAlphabet()) {
				if(mealy.getOutput(st, in).firstSymbol().equals(OMEGA_SYMBOL)){
					mealy.removeAllTransitions(st, in);
				}
			}
		}
	}
	
	public static void generateTabularLog(){
		try {
			String[] logname_all ={					
					"increase_random_fsm.log",
					"increase_fsm_best.log",
					"increase_fsm_mid.log",
					"increase_fsm.log",
			};

			PrintStream out = new PrintStream(new FileOutputStream("output.txt"));
			System.setOut(out);

			System.out.print("scenario");
			System.out.print("\t");
			System.out.print("config");
			System.out.print("\t");
			System.out.print("step");
			System.out.print("\t");
			System.out.print("mq_resets");
			System.out.print("\t");
			System.out.print("mq_symbol");
			System.out.print("\t");
			System.out.print("eq_resets");
			System.out.print("\t");
			System.out.print("eq_symbol");
			System.out.print("\t");
			System.out.print("learning");
			System.out.print("\t");
			System.out.print("search_ce");
			System.out.println();

			Map<String,Integer> noError = new HashMap<>();
			for (String logname : logname_all) {
				File dir = new File("./");

				File filelog = new File(dir,logname);

				BufferedReader br = new BufferedReader(new FileReader(filelog));

				String line;
				Pattern numberEof = Pattern.compile("INFO: [^:]+: ([a-zA-Z_0-9.]+)");
				Matcher noEof;

				StringBuffer sb = new StringBuffer();
				StringBuffer fname = new StringBuffer();				
				int noReads = 0;
				while (br.ready()) {
					line = br.readLine();
					noEof = numberEof.matcher(line);
					noEof.matches();
					if(line.startsWith("INFO: Scenario name:")){
						sb.append((noEof.group(1)));
						noReads++;
						
						fname.delete(0, fname.length());
						fname.append((noEof.group(1)));
					}else  if(line.startsWith("INFO: Configuration:")){
						sb.append("\t");
						sb.append((noEof.group(1)));
						noReads++;
						
						fname.append("\t");
						fname.append((noEof.group(1)));
					}else  if(line.startsWith("INFO: Step:")){
						sb.append("\t");
						sb.append((noEof.group(1)));
						noReads++;
						
						fname.append("\t");
						fname.append((noEof.group(1)));
						noError.putIfAbsent(fname.toString(), 0);
					}else  if(line.startsWith("INFO: Learning [ms]:")){
						sb.append("\t");
						sb.append((noEof.group(1)));
						noReads++;
					}else  if(line.startsWith("INFO: Searching for counterexample [ms]:")){
						sb.append("\t");
						sb.append((noEof.group(1)));
						noReads++;
					}else if(line.startsWith("INFO: membership queries [resets]:")){
						sb.append("\t");
						sb.append((noEof.group(1)));
						noReads++;
					}else  if(line.startsWith("INFO: membership queries [symbols]:")){
						sb.append("\t");
						sb.append((noEof.group(1)));
						noReads++;
					}else  if(line.startsWith("INFO: equivalence queries [resets]:")){
						sb.append("\t");
						sb.append((noEof.group(1)));
						noReads++;
					}else  if(line.startsWith("INFO: equivalence queries [symbols]:")){
						sb.append("\t");
						sb.append((noEof.group(1)));
						noReads++;
					}else  if(line.startsWith("INFO: ERROR:")){
						noError.put(fname.toString(), noError.get(fname.toString())+1);
					}

					if(noReads == 9){
						System.out.print(sb.toString());
						System.out.println();
						sb.delete(0, sb.length());
						noReads = 0;
					}

				}

				br.close();
			}
			out.close();
			
			out = new PrintStream(new FileOutputStream("noErrors.txt"));
			System.setOut(out);
			System.out.print("scenario");
			System.out.print("\t");
			System.out.print("config");
			System.out.print("\t");
			System.out.print("step");
			System.out.print("\t");
			System.out.print("totErrors");
			System.out.println();
			
			for (String fname : noError.keySet()) {
				System.out.print(fname);
				System.out.print("\t");
				System.out.print(noError.get(fname));
				System.out.println();
			}
			out.close();

			
		} catch (Exception e) {
			e.printStackTrace();
		}
	}
}

