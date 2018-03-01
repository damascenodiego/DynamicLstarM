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
import java.io.PrintStream;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.Comparator;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedHashSet;
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

import br.usp.icmc.labes.mealyInference.utils.MyObservationTable;
import br.usp.icmc.labes.mealyInference.utils.OTUtils;
import de.learnlib.algorithms.features.observationtable.reader.SuffixASCIIReader;
import de.learnlib.algorithms.features.observationtable.writer.ObservationTableASCIIWriter;
import de.learnlib.algorithms.features.observationtable.writer.SuffixASCIIWriter;
import de.learnlib.algorithms.lstargeneric.ce.ObservationTableCEXHandler;
import de.learnlib.algorithms.lstargeneric.ce.ObservationTableCEXHandlers;
import de.learnlib.algorithms.lstargeneric.closing.ClosingStrategies;
import de.learnlib.algorithms.lstargeneric.closing.ClosingStrategy;
import de.learnlib.algorithms.lstargeneric.mealy.ExtensibleLStarMealy;
import de.learnlib.algorithms.lstargeneric.mealy.ExtensibleLStarMealyBuilder;
import de.learnlib.api.EquivalenceOracle;
import de.learnlib.api.MembershipOracle;
import de.learnlib.api.SUL;
import de.learnlib.cache.mealy.MealyCaches;
import de.learnlib.eqtests.basic.mealy.RandomWalkEQOracle;
import de.learnlib.experiments.Experiment;
import de.learnlib.experiments.Experiment.MealyExperiment;
import de.learnlib.logging.LearnLogger;
import de.learnlib.oracles.DefaultQuery;
import de.learnlib.oracles.ResetCounterSUL;
import de.learnlib.oracles.SULOracle;
import de.learnlib.oracles.SymbolCounterSUL;
import de.learnlib.simulator.sul.MealySimulatorSUL;
import de.learnlib.statistics.SimpleProfiler;
import de.learnlib.statistics.StatisticSUL;
import net.automatalib.automata.transout.MealyMachine;
import net.automatalib.automata.transout.impl.compact.CompactMealy;
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

	private static final Comparator<Word<String>> wordStringComparator = new Comparator<Word<String>>() {

		@Override
		public int compare(Word<String> o1, Word<String> o2) {
			return o1.toString().compareTo(o2.toString());
		}
	};
	
	public static void main(String[] args) throws Exception {


		Random rnd_seed = new Random(1);

		// set closing strategy
		ClosingStrategy strategy 			= ClosingStrategies.CLOSE_FIRST;
		// set CE processing approach
		ObservationTableCEXHandler handler 	= ObservationTableCEXHandlers.RIVEST_SCHAPIRE;

		// reused inputs
		Set<Word<String>> suffixes = new LinkedHashSet<Word<String>>();
		Set<Word<String>> prefixes = new LinkedHashSet<Word<String>>();

		File splDir = new File("/home/damasceno/git/ffsm_test/br.icmc.ffsm.ui.base/experiments_agm/");

		{
			// first FSM to be inferred
//			File agm = new File(splDir,"/fsm/fsm_agm_1.txt");  // b
			File agm = new File(splDir,"/fsm/fsm_agm_5.txt");  // b + s

//			File agm_n = new File(splDir,"/fsm/fsm_agm_2.txt");  // n
//			File agm_ns = new File(splDir,"/fsm/fsm_agm_6.txt"); // n + s
	
//			File agm_w = new File(splDir,"/fsm/fsm_agm_3.txt");  // w
//			File agm_ws = new File(splDir,"/fsm/fsm_agm_4.txt"); // w + s

			
			// logfile for each set of FSM 
			LearnLogger logger; 
			FileHandler fh = new FileHandler(agm.getName()+".inf.log");
			fh.setFormatter(new SimpleFormatter());
			logger = LearnLogger.getLogger(SimpleProfiler.class); logger.setUseParentHandlers(false); logger.addHandler(fh);
			logger = LearnLogger.getLogger(Experiment.class); logger.setUseParentHandlers(false); logger.addHandler(fh);
			
			// load mealy machine
			CompactMealy<String, Word<String>> m_agm_b = loadMealyMachine(agm);

			// SUL simulator
			SUL<String,Word<String>> sulSim = new MealySimulatorSUL(m_agm_b, OMEGA_SYMBOL);

			// membership oracle for counting queries wraps sul
			StatisticSUL<String, Word<String>>  mqSul_sym = new SymbolCounterSUL<>("membership queries", sulSim);
			StatisticSUL<String, Word<String>>  mqSul_rst = new ResetCounterSUL <>("membership queries", mqSul_sym);			
			MembershipOracle<String, Word<Word<String>>> mqOracle = new SULOracle<String, Word<String>>(mqSul_rst);


			File fout = new File("fsm_agm_1.txt.inf.ot");
			MyObservationTable myot = OTUtils.getInstance().readOT(fout, m_agm_b.getInputAlphabet());
			OTUtils.getInstance().revalidateOT(myot, mqOracle);
			
			// use caching in order to avoid duplicate queries
			mqOracle = MealyCaches.createCache(m_agm_b.getInputAlphabet(), mqOracle);

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

			///////////////////////////////////////////////
			// Run the experiment using MealyExperiment  //
			///////////////////////////////////////////////

			
			// Empty list of prefixes 
			List<Word<String>> initPrefixes = new ArrayList<Word<String>>();
			initPrefixes.add(Word.epsilon());
			
			initPrefixes.clear();initPrefixes.addAll(myot.getPrefixes());

			// Empty list of suffixes => minimal compliant set
			List<Word<String>> initSuffixes = new ArrayList<Word<String>>();

			initSuffixes.addAll(myot.getSuffixes());

			// construct L* instance 
			ExtensibleLStarMealyBuilder<String, Word<String>> builder = new ExtensibleLStarMealyBuilder<String, Word<String>>();
			builder.setAlphabet(m_agm_b.getInputAlphabet());
			builder.setOracle(mqOracle);
			builder.setInitialPrefixes(initPrefixes);
			builder.setInitialSuffixes(initSuffixes);
			builder.setCexHandler(handler);
			builder.setClosingStrategy(strategy);

			ExtensibleLStarMealy<String, Word<String>> learner = builder.create();

			
			// The experiment will execute the main loop of active learning
			MealyExperiment<String, Word<String>> experiment = new MealyExperiment<String, Word<String>> (learner, mealySymEqOracle, m_agm_b.getInputAlphabet());

			// turn on time profiling
			experiment.setProfile(true);

			// enable logging of models
			experiment.setLogModels(true);
			
			// run experiment
			experiment.run();

//			new ObservationTableASCIIWriter().write(learner.getObservationTable(), System.out);
	        
			
//			OTUtils.getInstance().writeOT(learner.getObservationTable(), fout);
	        
			
	        
	        
			// profiling
			SimpleProfiler.logResults();

			// learning statistics
			logger.logStatistic(mqSul_rst.getStatisticalData());
			logger.logStatistic(mqSul_sym.getStatisticalData());
			logger.logStatistic(eqSul_rst.getStatisticalData());
			logger.logStatistic(eqSul_sym.getStatisticalData());

			if(learner.getHypothesisModel().getStates().size() != m_agm_b.getStates().size()){
				logger.log(new LogRecord(Level.INFO, "ERROR: Number of states does not match!"));
			}
			
			
		}

	}

//	DefaultQuery counterexample = null;
//	do {
//		if (counterexample == null) {
//			learner.startLearning();
//		} else {
//			boolean refined = learner.refineHypothesis(counterexample);
//			if(!refined) System.err.println("No refinement effected by counterexample!");
//		}
//
//		counterexample = mealySymEqOracle.findCounterExample(learner.getHypothesisModel(), m_agm_b.getInputAlphabet());
//
//	} while (counterexample != null);
//
//	// from here on learner.getHypothesisModel() will provide an accurate model


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

		//		for (Integer st : mealym.getStates()) {
		//			for (String in : alphabet) {
		//				//				System.out.println(mealym.getTransition(st, in));
		//				if(mealym.getTransition(st, in)==null){
		//					mealym.addTransition(st, in, st, words.get(OMEGA_SYMBOL));
		//				}
		//			}
		//		}


		mealym.setInitialState(states.get(trs.get(0)[0]));

		return mealym;
	}
}

