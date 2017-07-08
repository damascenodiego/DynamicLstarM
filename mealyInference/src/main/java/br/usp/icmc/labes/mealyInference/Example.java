/**
 * 
 */
package br.usp.icmc.labes.mealyInference;

import java.io.BufferedReader;
import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileReader;
import java.io.FileWriter;
import java.io.FilenameFilter;
import java.io.IOException;
import java.io.Writer;
import java.security.spec.EncodedKeySpec;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Random;
import java.util.logging.FileHandler;
import java.util.logging.LogManager;
import java.util.logging.Logger;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import de.learnlib.algorithms.dhc.mealy.MealyDHC;
import de.learnlib.algorithms.features.observationtable.OTUtils;
import de.learnlib.algorithms.features.observationtable.writer.ObservationTableASCIIWriter;
import de.learnlib.algorithms.lstargeneric.ce.ObservationTableCEXHandler;
import de.learnlib.algorithms.lstargeneric.ce.ObservationTableCEXHandlers;
import de.learnlib.algorithms.lstargeneric.closing.ClosingStrategies;
import de.learnlib.algorithms.lstargeneric.closing.ClosingStrategy;
import de.learnlib.algorithms.lstargeneric.mealy.ClassicLStarMealy;
import de.learnlib.algorithms.lstargeneric.mealy.ExtensibleLStarMealy;
import de.learnlib.algorithms.lstargeneric.mealy.ExtensibleLStarMealyBuilder;
import de.learnlib.api.EquivalenceOracle;
import de.learnlib.api.EquivalenceOracle.MealyEquivalenceOracle;
import de.learnlib.api.LearningAlgorithm;
import de.learnlib.api.MembershipOracle;
import de.learnlib.api.MembershipOracle.MealyMembershipOracle;
import de.learnlib.api.SUL;
import de.learnlib.cache.mealy.MealyCacheOracle;
import de.learnlib.drivers.reflect.AbstractMethodInput;
import de.learnlib.drivers.reflect.AbstractMethodOutput;
import de.learnlib.eqtests.basic.EQOracleChain;
import de.learnlib.eqtests.basic.SimulatorEQOracle;
import de.learnlib.eqtests.basic.WpMethodEQOracle;
import de.learnlib.eqtests.basic.mealy.RandomWalkEQOracle;
import de.learnlib.eqtests.basic.mealy.SymbolEQOracleWrapper;
import de.learnlib.examples.mealy.ExampleCoffeeMachine;
import de.learnlib.examples.mealy.ExampleStack;
import de.learnlib.experiments.Experiment;
import de.learnlib.experiments.Experiment.MealyExperiment;
import de.learnlib.logging.LearnLogger;
import de.learnlib.examples.mealy.ExampleCoffeeMachine.Input;
import de.learnlib.mealy.MealyUtil;
import de.learnlib.oracles.DefaultQuery;
import de.learnlib.oracles.ResetCounterSUL;
import de.learnlib.oracles.SULOracle;
import de.learnlib.oracles.SimulatorOracle;
import de.learnlib.oracles.SimulatorOracle.MealySimulatorOracle;
import de.learnlib.oracles.SymbolCounterSUL;
import de.learnlib.simulator.sul.MealySimulatorSUL;
import de.learnlib.statistics.Counter;
import de.learnlib.statistics.SimpleProfiler;
import de.learnlib.statistics.StatisticSUL;
import net.automatalib.automata.transout.MealyMachine;
import net.automatalib.automata.transout.impl.compact.CompactMealy;
import net.automatalib.automata.transout.impl.compact.CompactMealyTransition;
import net.automatalib.commons.dotutil.DOT;
import net.automatalib.graphs.concepts.GraphViewable;
import net.automatalib.util.automata.builders.AutomatonBuilders;
import net.automatalib.util.automata.builders.MealyBuilder;
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
	private static final boolean runUsingExperiment = false;

	public static void main(String[] args) throws Exception {


		File dir = new File("Fragal_Experiment_Pack/LogicProcessor/increase_random/fsm/");

		String [] files = dir.list(new FilenameFilter() {
			@Override
			public boolean accept(File dir, String name) { return name.matches("fsm_30_[0-9]+.txt");}
		});

		Arrays.sort(files);

		File fout;
		FileWriter fwout;

		ClosingStrategy strategy 			= ClosingStrategies.CLOSE_FIRST;
		ObservationTableCEXHandler handler 	= ObservationTableCEXHandlers.RIVEST_SCHAPIRE;


		for (String file_s : files) {
			//			System.out.println(file_s);
			File f = new File(dir,file_s);
			CompactMealy<String, String> mealyss = loadMealyMachine(f);

			//			fout = new File(f.getAbsolutePath()+".dot");
			//			fwout = new FileWriter(fout); 
			//			GraphDOT.write(mealyss,fwout);
			//			fwout.close();
			//
			//			Writer w = DOT.createDotWriter(true);
			//			GraphDOT.write(mealyss,mealyss.getInputAlphabet(),  w);
			//			w.close();

			// SUL simulator
			SUL<String,Word<String>> sulSim = new MealySimulatorSUL(mealyss, OMEGA_SYMBOL);

			// membership oracle for counting queries wraps sul
			StatisticSUL<String, Word<String>>  mqSul_sym = new SymbolCounterSUL<>("membership queries", sulSim);
			StatisticSUL<String, Word<String>>  mqSul_rst = new ResetCounterSUL <>("membership queries", mqSul_sym);			
			MembershipOracle<String, Word<Word<String>>> mqOracle = new SULOracle<String, Word<String>>(mqSul_rst);


			// equivalence oracle for counting queries wraps sul
			StatisticSUL<String, Word<String>> eqSul_sym = new SymbolCounterSUL<>("equivalence queries", sulSim);
			StatisticSUL<String, Word<String>> eqSul_rst = new ResetCounterSUL<>("equivalence queries", eqSul_sym);
			EquivalenceOracle<MealyMachine<?, String, ?, Word<String>>, String, Word<Word<String>>> mealySymEqOracle 
					//								= new SymbolEQOracleWrapper<>(new SimulatorEQOracle(mealyss));
					= new RandomWalkEQOracle<String, Word<String>>(
							0.05, // reset SUL w/ this probability before a step 
							10000, // max steps (overall)
							false, // reset step count after counterexample 
							new Random(1), // make results reproducible 
							eqSul_rst
							);



			// Empty list of suffixes => minimal compliant set
			List<Word<String>> initSuffixes = new ArrayList<Word<String>>();

			// Empty list of preffixes 
			List<Word<String>> initialPrefixes = new ArrayList<Word<String>>();

			ExtensibleLStarMealyBuilder<String, Word<String>> builder = new ExtensibleLStarMealyBuilder<String, Word<String>>();
			builder.setAlphabet(mealyss.getInputAlphabet());
			builder.setOracle(mqOracle);
			//			builder.setInitialPrefixes(initPrefixes);
			builder.setInitialSuffixes(initSuffixes);
			builder.setCexHandler(handler);
			builder.setClosingStrategy(strategy);

			ExtensibleLStarMealy<String, Word<String>> learner = builder.create();

			
			///////////////////////////////////////////////////////////////////////////
			//
			///////////////////////////////////////////////////////////////////////////
			LearnLogger logger; 
			FileHandler fh;

			fh = new FileHandler(file_s+".log");
			logger = LearnLogger.getLogger(SimpleProfiler.class);			
			logger.setUseParentHandlers(false);			  
			logger.addHandler(fh);

			logger = LearnLogger.getLogger(Experiment.class);			
			logger.setUseParentHandlers(false);			  
			logger.addHandler(fh);

			
			if(runUsingExperiment){

				// The experiment will execute the main loop of active learning
				MealyExperiment<String, Word<String>> experiment = new MealyExperiment<String, Word<String>> (learner, mealySymEqOracle, mealyss.getInputAlphabet());
				

				// turn on time profiling
				experiment.setProfile(true);

				// enable logging of models
				experiment.setLogModels(true);

				// run experiment
				experiment.run();
				
				ObservationTableASCIIWriter obsTableWriter = new ObservationTableASCIIWriter<>();
				FileWriter fw_ot = new FileWriter(new File(file_s+".ot"));
				obsTableWriter.write(learner.getObservationTable(), fw_ot);				
				fw_ot.close();
				
				OTUtils.displayHTMLInBrowser(learner.getObservationTable());
				
				// report results
				System.out.println("-------------------------------------------------------");


				// profiling
				SimpleProfiler.logResults();
				System.out.println(SimpleProfiler.getResults());

				// learning statistics
				System.out.println(experiment.getRounds().getSummary());
				System.out.println(mqSul_rst.getStatisticalData().getDetails());
				System.out.println(mqSul_sym.getStatisticalData().getDetails());
				System.out.println(eqSul_rst.getStatisticalData().getDetails());
				System.out.println(eqSul_sym.getStatisticalData().getDetails());

				// get learned model
				CompactMealy result = learner.getHypothesisModel();
				
				// model statistics
				System.out.println("States: " + result.size());
				System.out.println("Sigma: " + mealyss.getInputAlphabet().size());

				removeSelfLoops(mealyss);
				removeSelfLoops(result);

				// save SUL model
				System.out.println();
				System.out.println("Model inferred: ");
				Writer w = new FileWriter(new File(file_s+".sul.dot"));
				GraphDOT.write(mealyss, w);
				w.close();
				
				// save inferred model
				System.out.println();
				System.out.println("Model learned: ");
				w = new FileWriter(new File(file_s+".inf.dot"));
				GraphDOT.write(result, w);
				w.close();

				
			} else {	

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

		        boolean done = false;
		        CompactMealy<String, Word<String>> hyp = null;
		        while (!done) {
		        	hyp = learner.getHypothesisModel();
		            if (logModel) {
		                logger.logModel(hyp);
		            }

		            if(logPhase) logger.logPhase("Searching for counterexample");
		            SimpleProfiler.start("Searching for counterexample");
		            DefaultQuery ce = mealySymEqOracle.findCounterExample(hyp, mealyss.getInputAlphabet());
		            SimpleProfiler.stop("Searching for counterexample");
		            if (ce == null) {
		                done = true;
		                continue;
		            }
		            
		            logger.logCounterexample(ce.getInput().toString());

		            // next round ...
		            rounds.increment();
		            if(logPhase) logger.logPhase("Starting round " + rounds.getCount());
		            if(logPhase) logger.logPhase("Learning");
		            SimpleProfiler.start("Learning");
		            learner.refineHypothesis(ce);
		            SimpleProfiler.stop("Learning");
		        }
				
		        logger.logPhase("Total of rounds: " + rounds.getCount());
		        logger.logStatistic(mqSul_rst.getStatisticalData());
				logger.logStatistic(mqSul_sym.getStatisticalData());

				logger.logStatistic(eqSul_rst.getStatisticalData());
				logger.logStatistic(eqSul_sym.getStatisticalData());

		        SimpleProfiler.logResults();
//		        System.out.println(SimpleProfiler.getResults());
		        
//				if(learner.getHypothesisModel().getStates().size() != mealyss.getStates().size()){
//					System.err.println("Error!!! :O");
//					System.err.println(learner.getHypothesisModel().toString());
//					System.exit(1);
//				}

			}
			fh.close();
			System.exit(0);			
		}

	}



	private static CompactMealy<String, String> loadMealyMachine(File f) throws Exception {

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
		CompactMealy<String, String> mealym = new CompactMealy<String, String>(alphabet);

		Map<String,Integer> states = new HashMap<String,Integer>();
		Integer si=null,sf=null;

		for (String[] tr : trs) {
			if(!states.containsKey(tr[0])) states.put(tr[0], mealym.addState());
			if(!states.containsKey(tr[3])) states.put(tr[3], mealym.addState());

			si = states.get(tr[0]);
			sf = states.get(tr[3]);
			mealym.addTransition(si, tr[1], sf, tr[2]);
		}

		for (Integer st : mealym.getStates()) {
			for (String in : alphabet) {
				//				System.out.println(mealym.getTransition(st, in));
				if(mealym.getTransition(st, in)==null){
					mealym.addTransition(st, in, st, OMEGA_SYMBOL);
				}
			}
		}


		mealym.setInitialState(states.get(trs.get(0)[0]));

		return mealym;
	}


	public static void removeSelfLoops(CompactMealy<String, String> mealy){
		for (Integer st : mealy.getStates()) {
			for (String in : mealy.getInputAlphabet()) {
				if(mealy.getOutput(st, in).equals(OMEGA_SYMBOL)){
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
