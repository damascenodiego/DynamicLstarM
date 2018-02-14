/**
 * 
 */
package br.usp.icmc.labes.mealyInference;

import java.io.BufferedReader;
import java.io.File;
import java.io.FileOutputStream;
import java.io.FileReader;
import java.io.FilenameFilter;
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

import br.usp.icmc.labes.mealyInference.utils.Utils;
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
import de.learnlib.oracles.ResetCounterSUL;
import de.learnlib.oracles.SULOracle;
import de.learnlib.oracles.SymbolCounterSUL;
import de.learnlib.simulator.sul.MealySimulatorSUL;
import de.learnlib.statistics.SimpleProfiler;
import de.learnlib.statistics.StatisticSUL;
import net.automatalib.automata.transout.MealyMachine;
import net.automatalib.automata.transout.impl.compact.CompactMealy;
import net.automatalib.words.Alphabet;
import net.automatalib.words.Word;
import net.automatalib.words.WordBuilder;
import net.automatalib.words.impl.Alphabets;

/**
 * @author damasceno
 *
 */
public class Infer_mid_low {

	private static int total_reps = 30;

	public static void main(String[] args) throws Exception {

		Random rnd_seed = new Random(1);

		// set closing strategy
		ClosingStrategy strategy 			= ClosingStrategies.CLOSE_FIRST;
		// set CE processing approach
		ObservationTableCEXHandler handler 	= ObservationTableCEXHandlers.RIVEST_SCHAPIRE;

		
		// set SPL name
		String spl_dir = "mid_low";
		
		// set SPL directory
		File splDir = new File("/home/damasceno/git/ffsm_test/br.icmc.ffsm.ui.base/experiments_"+spl_dir+"/");
		
		// sets of FSMs to be inferred
		File dir = new File(splDir,"fsm");

		String scenario_name ;
		String config_name;

		// configurations to be considered
		boolean[] configs = {false, true};


		// for each spl...
		Map<String, List<String>> splsWithProds = Utils.getInstance().loadConfigurations(new File(splDir,"configurations.txt"));
		for (String spl_name : splsWithProds.keySet()) {
			List<String> value = splsWithProds.get(spl_name); 

			// for each set of FSMs...
			String [] files = new String[value.size()];
			files = value.toArray(files);

			// logfile for each set of FSM 
			File filelog = new File(dir.getPath()+"/"+spl_name+".log");
			FileHandler fh = new FileHandler(filelog.getAbsolutePath());
			fh.setFormatter(new SimpleFormatter());

			LearnLogger logger; 

			logger = LearnLogger.getLogger(SimpleProfiler.class);			
			logger.setUseParentHandlers(false);			  
			logger.addHandler(fh);

			logger = LearnLogger.getLogger(Experiment.class);			
			logger.setUseParentHandlers(false);			  
			logger.addHandler(fh);

			// for each configuration...
			for(boolean okFilter: configs){

				// repeat inference _total_reps_ times
				for (int i = 0; i < total_reps ; i++)
				{		
					for (String file_s : files) {

						scenario_name = file_s.substring(0, file_s.length()-4);

						StringBuilder sb = new StringBuilder();

						if (okFilter) sb.append(".cache");

						if(sb.length()>0){
							config_name = sb.toString().substring(1).replaceAll("_", "");
						}else{
							config_name = "none";
						}

//						step_id = file_s.replaceFirst("fsm_[0-9]+_", "").replaceAll("[a-z._]", "");

						sb.append(".log");

						// load mealy machine
						File f = new File(dir,file_s);
						CompactMealy<String, Word<String>> mealyss = Utils.getInstance().loadMealyMachine(f);

						// SUL simulator
						SUL<String,Word<String>> sulSim = new MealySimulatorSUL(mealyss, Utils.getInstance().OMEGA_SYMBOL);

						// membership oracle for counting queries wraps sul
						StatisticSUL<String, Word<String>>  mqSul_sym = new SymbolCounterSUL<>("membership queries", sulSim);
						StatisticSUL<String, Word<String>>  mqSul_rst = new ResetCounterSUL <>("membership queries", mqSul_sym);			
						MembershipOracle<String, Word<Word<String>>> mqOracle = new SULOracle<String, Word<String>>(mqSul_rst);

						// use caching in order to avoid duplicate queries
						if(okFilter)  mqOracle = MealyCaches.createTreeCache(mealyss.getInputAlphabet(), mqOracle);

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

						logger.logEvent("Scenario name: "+scenario_name);
						logger.logEvent("Configuration: "+config_name);
//						logger.logEvent("Step: "+step_id);						


						///////////////////////////////////////////////
						// Run the experiment using MealyExperiment  //
						///////////////////////////////////////////////

						// Empty list of prefixes 
						List<Word<String>> initialPrefixes = new ArrayList<Word<String>>();

						// Empty list of suffixes => minimal compliant setinitCes
						List<Word<String>> initSuffixes = new ArrayList<Word<String>>();



						// construct L* instance 
						ExtensibleLStarMealyBuilder<String, Word<String>> builder = new ExtensibleLStarMealyBuilder<String, Word<String>>();
						builder.setAlphabet(mealyss.getInputAlphabet());
						builder.setOracle(mqOracle);
//						builder.setInitialPrefixes(initialPrefixes);
//						builder.setInitialSuffixes(initSuffixes);
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
			Utils.getInstance().generateTabularLog(filelog);
			
		}
		

	}
}

