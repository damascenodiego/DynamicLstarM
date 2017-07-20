/**
 * 
 */
package br.usp.icmc.labes.mealyInference;

import java.io.BufferedReader;
import java.io.File;
import java.io.FileReader;
import java.io.FileWriter;
import java.io.FilenameFilter;
import java.io.IOException;
import java.io.Writer;
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
import de.learnlib.algorithms.features.observationtable.OTUtils;
import de.learnlib.algorithms.features.observationtable.writer.ObservationTableASCIIWriter;
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
import de.learnlib.statistics.Counter;
import de.learnlib.statistics.SimpleProfiler;
import de.learnlib.statistics.StatisticSUL;
import net.automatalib.automata.transout.MealyMachine;
import net.automatalib.automata.transout.impl.compact.CompactMealy;
import net.automatalib.graphs.concepts.GraphViewable;
import net.automatalib.util.automata.Automata;
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
	private static final boolean runUsingExperiment = true;
	private static int total_reps = 30;

	public static void main(String[] args) throws Exception {


		Random rnd_seed = new Random(1);

		ClosingStrategy strategy 			= ClosingStrategies.CLOSE_FIRST;
		ObservationTableCEXHandler handler 	= ObservationTableCEXHandlers.RIVEST_SCHAPIRE_ALLSUFFIXES;

		Set<Word<String>> allSuffixes = new HashSet<Word<String>>();

		File[ ] dirs = {
				new File("Fragal_Experiment_Pack/LogicProcessor/increase/fsm"),
				new File("Fragal_Experiment_Pack/LogicProcessor/increase/fsm_mid"),
				new File("Fragal_Experiment_Pack/LogicProcessor/increase/fsm_best"),
		};

		boolean[][] configs =  {
//				{ true, 	true, 	true }, // ce_cache_rev
								
//				{ true, 	false, 	true }, // cache_rev				
//				{ false, 	true, 	true }, // ce_cache
//				{ true, 	true, 	false}, // ce_rev
				
//				{ false, 	false, 	true }, // cache
				{ false, 	true, 	false}, // ce				
//				{ true, 	false, 	false}, // rev
				{ false, 	false, 	false}, // NONE

		};

		for (File dir : dirs) {

			String [] files = dir.list(new FilenameFilter() {
				@Override
				public boolean accept(File dir, String name) { return name.matches("fsm[0-9]+.txt");}
			});


			for(boolean[] conf: configs){

				boolean okReverse  = conf[0];
				boolean okCe	   = conf[1];
				boolean okFilter   = conf[2];

				if(okReverse) {
					Arrays.sort(files,Collections.reverseOrder());
				}else{
					Arrays.sort(files);
				}


				for (int i = 0; i < total_reps ; i++)
				{		
					allSuffixes.clear();
					int step = 0;

					for (String file_s : files) {
						step++;

						FileHandler fh;

						StringBuilder sb = new StringBuilder();
						if (okCe){
							sb.append(".ce");
						}
						if (okFilter){
							sb.append(".cache");				
						}
						if (okReverse){
							sb.append(".rev");				
						}
						sb.append(".log");
						fh = new FileHandler(dir.getName()+ step + sb.toString(), true);
						fh.setFormatter(new SimpleFormatter());

						LearnLogger logger; 

						logger = LearnLogger.getLogger(SimpleProfiler.class);			
						logger.setUseParentHandlers(false);			  
						logger.addHandler(fh);

						logger = LearnLogger.getLogger(Experiment.class);			
						logger.setUseParentHandlers(false);			  
						logger.addHandler(fh);

						File f = new File(dir,file_s);
						CompactMealy<String, Word<String>> mealyss = loadMealyMachine(f);

						// SUL simulator
						SUL<String,Word<String>> sulSim = new MealySimulatorSUL(mealyss, OMEGA_SYMBOL);

						// membership oracle for counting queries wraps sul
						StatisticSUL<String, Word<String>>  mqSul_sym = new SymbolCounterSUL<>("membership queries", sulSim);
						StatisticSUL<String, Word<String>>  mqSul_rst = new ResetCounterSUL <>("membership queries", mqSul_sym);			
						MembershipOracle<String, Word<Word<String>>> mqOracle = new SULOracle<String, Word<String>>(mqSul_rst);

						if(okFilter) {
							// use caching in order to avoid duplicate queries
							mqOracle = MealyCaches.createCache(mealyss.getInputAlphabet(), mqOracle);
						}


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

						// reuse all counterexamples/suffixes using the same FSM alphabet
						Set<Word<String>> initCes = new HashSet<Word<String>>();
						if (okCe)
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


						///////////////////////////////////////////////////////////////
						// Run the experiment (using MealyExperiment or manual setup //
						///////////////////////////////////////////////////////////////

						if(runUsingExperiment){

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

						} else {

							// Empty list of prefixes 
							List<Word<String>> initialPrefixes = new ArrayList<Word<String>>();

							// Empty list of suffixes => minimal compliant set
							List<Word<String>> initSuffixes = new ArrayList<Word<String>>();

							// construct L* instance 
							ExtensibleLStarMealyBuilder<String, Word<String>> builder = new ExtensibleLStarMealyBuilder<String, Word<String>>();
							builder.setAlphabet(mealyss.getInputAlphabet());
							builder.setOracle(mqOracle);
							builder.setInitialSuffixes(initSuffixes);
							builder.setCexHandler(handler);
							builder.setClosingStrategy(strategy);

							ExtensibleLStarMealy<String, Word<String>> learner = builder.create();

							Counter rounds = new Counter("rounds", "#");
							boolean logModel = false;
							boolean logPhase = false;
							boolean profile = false;

							rounds.increment();
							if(logPhase) logger.logPhase("Starting round " + rounds.getCount());
							if(logPhase) logger.logPhase("Learning");
							SimpleProfiler.start("Learning");
							learner.startLearning();
							SimpleProfiler.stop("Learning");

							for (Word<String> word : initCes) {
								String out;
								WordBuilder<String> wbIn = new WordBuilder<>();
								WordBuilder<String> wbOut = new WordBuilder<>();
								sulSim.pre();
								for (String in : word) {
									SimpleProfiler.start("Learning (ce)");
									out = sulSim.step(in).firstSymbol();
									SimpleProfiler.stop("Learning (ce)");
									wbIn.append(in);
									wbOut.append(out);
								}
								sulSim.post();
								DefaultQuery<String, Word< Word<String>>> ce = new DefaultQuery<>(wbIn.toWord());
								ce.answer(new WordBuilder().append(wbOut.toWord()).toWord());
								SimpleProfiler.start("Learning (ce)");
								learner.refineHypothesis(ce);
								SimpleProfiler.stop("Learning (ce)");

							}

							boolean done = false;
							CompactMealy<String, Word<String>> hyp = null;
							while (!done) {
								hyp = learner.getHypothesisModel();
								if (logModel) {
									logger.logModel(hyp);
								}

								if(logPhase) logger.logPhase("Searching for counterexample");
								SimpleProfiler.start("Searching for counterexample");
								DefaultQuery<String, Word<Word<String>>> ce = mealySymEqOracle.findCounterExample(hyp, mealyss.getInputAlphabet());
								SimpleProfiler.stop("Searching for counterexample");
								if (ce == null) {
									done = true;
									continue;
								}

								//logger.logCounterexample(ce.getInput().toString());

								// next round ...
								rounds.increment();
								if(logPhase) logger.logPhase("Starting round " + rounds.getCount());
								if(logPhase) logger.logPhase("Learning");
								SimpleProfiler.start("Learning");
								learner.refineHypothesis(ce);
								SimpleProfiler.stop("Learning");
								allSuffixes.add(ce.getInput());
							}

							logger.logPhase("Total of rounds: " + rounds.getCount());
							logger.logStatistic(mqSul_rst.getStatisticalData());
							logger.logStatistic(mqSul_sym.getStatisticalData());

							logger.logStatistic(eqSul_rst.getStatisticalData());
							logger.logStatistic(eqSul_sym.getStatisticalData());

							SimpleProfiler.logResults();

							if(learner.getHypothesisModel().getStates().size() != mealyss.getStates().size()){
								logger.log(new LogRecord(Level.INFO, "ERROR: Number of states does not match!"));
							}

						}



						//System.exit(0);
						fh.close();
					}

				}
			}
		}
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


	private static void testlstar(CompactMealy<Character, Integer> machine) throws IOException {

		File dir = new File("out");
		if(!dir.exists()){
			dir.mkdir();
		}
		for(ObservationTableCEXHandler<? super Character,? super Integer> handler : ObservationTableCEXHandlers.values()) {
			for(ClosingStrategy<? super Character,? super Integer> strategy : ClosingStrategies.values()) {



				File fout = new File(dir,"out_machine.dot");
				FileWriter fwout = new FileWriter(fout); 
				GraphDOT.write((GraphViewable) machine,fwout);
				fwout.close();

				MembershipOracle<Character,Word<Integer>> oracle = new SimulatorOracle<>(machine);

				// Empty list of suffixes => minimal compliant set
				List<Word<Character>> initSuffixes = new ArrayList();

				SUL sulSim = new MealySimulatorSUL<>(machine);
				EquivalenceOracle<? super MealyMachine<?,Character,?,Integer>, Character, Integer> mealySymEqOracle 
				//						= new SymbolEQOracleWrapper<>(new SimulatorEQOracle<>(machine));
				= new RandomWalkEQOracle(
						0.05, // reset SUL w/ this probability before a step 
						10000, // max steps (overall)
						false, // reset step count after counterexample 
						new Random(46346292), // make results reproducible 
						sulSim 
						);

				LearningAlgorithm<MealyMachine<?,Character,?,Integer>,Character,Word<Integer>> learner
				= new ExtensibleLStarMealy(machine.getInputAlphabet(), oracle, initSuffixes,handler, strategy);

				DefaultQuery counterexample = null;
				do {
					if (counterexample == null) {
						learner.startLearning();
					} else {
						boolean refined = learner.refineHypothesis(counterexample);
						if(!refined) {
							System.err.println("No refinement effected by counterexample!");
						}else{
							System.out.println(counterexample.toString());
						}
					}

					counterexample = mealySymEqOracle.findCounterExample(learner.getHypothesisModel() , machine.getInputAlphabet());

					//					System.out.println(counterexample.toString());

					learner.getHypothesisModel();
					//					fout = new File("out_ClassicLStarMealy"+(count++)+".dot");
					//					fwout = new FileWriter(fout); 
					//					GraphDOT.write((GraphViewable) learner.getHypothesisModel(),fwout);
					//					fwout.close();

				} while (counterexample != null);

				// from here on learner.getHypothesisModel() will provide an accurate model

				if(learner.getHypothesisModel().size() != machine.size()){
					System.err.println("Error!!! :O");	
				}

				fout = new File(dir,handler.toString()+"_"+strategy.toString()+".dot");
				fwout = new FileWriter(fout); 
				GraphDOT.write((GraphViewable) learner.getHypothesisModel(),fwout);
				fwout.close();

			}
		}
	}

	public static void testdhc(CompactMealy<Character, Integer> machine) throws IOException{


		CompactMealy<Input, String> fm = ExampleCoffeeMachine.constructMachine();
		Alphabet<Input> alphabet = fm.getInputAlphabet();

		SimulatorOracle<Input, Word<String>> simoracle = new SimulatorOracle<>(fm);
		SimulatorEQOracle<Input, Word<String>> eqoracle = new SimulatorEQOracle<>(fm);

		MembershipOracle<Input,Word<String>> cache = new MealyCacheOracle<>(alphabet, null, simoracle);
		MealyDHC<Input, String> learner = new MealyDHC<>(alphabet, cache);

		int count = 0 ;
		File fout;
		FileWriter fwout;

		fout = new File("out_MealyDHC"+(count++)+".dot");
		fwout = new FileWriter(fout); 
		GraphDOT.write(fm,fwout);
		fwout.close();


		DefaultQuery<Input, Word<String>> counterexample = null;
		do {
			if (counterexample == null) {
				learner.startLearning();
			} else {
				boolean refined = learner.refineHypothesis(counterexample);
				if(!refined) System.err.println("No refinement effected by counterexample!");
			}

			counterexample = eqoracle.findCounterExample(learner.getHypothesisModel(), alphabet);

			learner.getHypothesisModel();
			fout = new File("out_MealyDHC"+(count++)+".dot");
			fwout = new FileWriter(fout); 
			GraphDOT.write(learner.getHypothesisModel(),fwout);
			fwout.close();

		} while (counterexample != null);

		// from here on learner.getHypothesisModel() will provide an accurate model

		fout = new File("out_MealyDHC"+(count++)+".dot");
		fwout = new FileWriter(fout); 
		GraphDOT.write(learner.getHypothesisModel(),fwout);
		fwout.close();


	}
}
