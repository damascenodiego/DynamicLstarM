package experiments.uk.ac.le;

import java.io.BufferedWriter;
import java.io.File;
import java.io.FileWriter;
import java.util.ArrayList;
import java.util.List;
import java.util.Random;

import br.usp.icmc.labes.mealyInference.utils.MyObservationTable;
import br.usp.icmc.labes.mealyInference.utils.OTUtils;
import br.usp.icmc.labes.mealyInference.utils.Utils;
import de.learnlib.algorithms.lstar.ce.ObservationTableCEXHandler;
import de.learnlib.algorithms.lstar.ce.ObservationTableCEXHandlers;
import de.learnlib.algorithms.lstar.closing.ClosingStrategies;
import de.learnlib.algorithms.lstar.closing.ClosingStrategy;
import de.learnlib.algorithms.lstar.mealy.ExtensibleLStarMealy;
import de.learnlib.algorithms.lstar.mealy.ExtensibleLStarMealyBuilder;
import de.learnlib.api.SUL;
import de.learnlib.api.oracle.EquivalenceOracle;
import de.learnlib.api.oracle.MembershipOracle;
import de.learnlib.api.query.DefaultQuery;
import de.learnlib.api.statistic.StatisticSUL;
import de.learnlib.datastructure.observationtable.ObservationTable;
import de.learnlib.datastructure.observationtable.writer.ObservationTableASCIIWriter;
import de.learnlib.driver.util.MealySimulatorSUL;
import de.learnlib.filter.cache.sul.SULCache;
import de.learnlib.filter.statistic.sul.ResetCounterSUL;
import de.learnlib.filter.statistic.sul.SymbolCounterSUL;
import de.learnlib.oracle.equivalence.WMethodEQOracle;
import de.learnlib.oracle.membership.SULOracle;
import de.learnlib.util.Experiment.MealyExperiment;
import net.automatalib.automata.transout.impl.compact.CompactMealy;
import net.automatalib.incremental.mealy.IncrementalMealyBuilder;
import net.automatalib.incremental.mealy.tree.IncrementalMealyTreeBuilder;
import net.automatalib.serialization.dot.GraphDOT;
import net.automatalib.util.automata.Automata;
import net.automatalib.words.Word;

public class LearningBenchmarkEdentifier2 {

	public static void main(String[] args) {
		
		try {
			// set SUL path
			File sul = new File("/home/cdnd1/git/DynamicLstarM/mealyInference/Benchmark/Edentifier2/learnresult_new_Rand_500_10-15_MC_fix.dot");
//			File sul = new File("/home/cdnd1/git/DynamicLstarM/mealyInference/Benchmark/Edentifier2/learnresult_old_500_10-15_fix.dot");
			
					
			File log_file = new File(sul.getAbsolutePath()+".log");
						
			// load mealy machine
			CompactMealy<String, Word<String>> mealyss = Utils.getInstance().loadMealyMachineFromDot(sul);
			//Visualization.visualize(mealyss);
			
			// set closing strategy
			ClosingStrategy strategy 			= ClosingStrategies.CLOSE_FIRST;

			// set CE processing approach
			ObservationTableCEXHandler handler 	= ObservationTableCEXHandlers.RIVEST_SCHAPIRE;
			
			// Empty list of prefixes 
			List<Word<String>> initPrefixes = new ArrayList<Word<String>>();
			initPrefixes.add(Word.epsilon());
						
			// Empty list of suffixes => minimal compliant setinitCes
			List<Word<String>> initSuffixes = new ArrayList<Word<String>>();

			Utils.getInstance();
			// SUL simulator
			SUL<String,Word<String>> sulSim = new MealySimulatorSUL(mealyss, Utils.OMEGA_SYMBOL);
						
			// IncrementalMealyBuilder for caching EQs and MQs together
			IncrementalMealyBuilder<String,Word<String>> cbuilder = new IncrementalMealyTreeBuilder<>(mealyss.getInputAlphabet());			

			// Cache using SULCache
			// Counters for MQs and EQs
			StatisticSUL<String, Word<String>>  mq_sym = new SymbolCounterSUL<>("MQ", sulSim);
			StatisticSUL<String, Word<String>>  mq_rst = new ResetCounterSUL <>("MQ", mq_sym);
			StatisticSUL<String, Word<String>>  eq_sym = new SymbolCounterSUL<>("EQ", sulSim);
			StatisticSUL<String, Word<String>>  eq_rst = new ResetCounterSUL <>("EQ", eq_sym);

			// SULs for associating the IncrementalMealyBuilder 'cbuilder' to MQs and EQs
			SUL<String, Word<String>> mq_sul = new SULCache<>(cbuilder, mq_rst);
			SUL<String, Word<String>> eq_sul = new SULCache<>(cbuilder, eq_rst);
			// MembershipOracles to wrap the SULs for MQs and EQs
			MembershipOracle<String,Word<Word<String>>> oracleForLearner  = new SULOracle<>(mq_sul);
			MembershipOracle<String,Word<Word<String>>> oracleForEQoracle = new SULOracle<>(eq_sul);
			
			// construct L* instance 
			ExtensibleLStarMealyBuilder<String, Word<String>> builder = new ExtensibleLStarMealyBuilder<String, Word<String>>();
			builder.setAlphabet(mealyss.getInputAlphabet());
			builder.setOracle(oracleForLearner);
			builder.setInitialPrefixes(initPrefixes);
			builder.setInitialSuffixes(initSuffixes);
			builder.setCexHandler(handler);
			builder.setClosingStrategy(strategy);

			ExtensibleLStarMealy<String, Word<String>> learner = builder.create();
			
			EquivalenceOracle eqOracle = null;
			Random seed = new Random(); 
			//eqOracle = new IrfanEQOracle<>(eq_sul, mealyss.getStates().size(), seed);
			eqOracle = new WMethodEQOracle<>(oracleForEQoracle, 2);
			//eqOracle = new RandomWordsEQOracle(oracleForEQoracle, 10, 100, 100, seed);
			

			// The experiment will execute the main loop of active learning
			MealyExperiment<String, Word<String>> experiment = new MealyExperiment<String, Word<String>> (learner, eqOracle, mealyss.getInputAlphabet());
		
			// turn on time profiling
			experiment.setProfile(true);
		
			// enable logging of models
			experiment.setLogModels(true);
		
			// run experiment
			experiment.run();
		
			System.out.println("Rounds: "+experiment.getRounds().getCount());
			// learning statistics
			System.out.println(mq_rst.getStatisticalData());
			System.out.println(mq_sym.getStatisticalData());
			System.out.println(eq_rst.getStatisticalData());
			System.out.println(eq_sym.getStatisticalData());


			if(Automata.testEquivalence(learner.getHypothesisModel(), mealyss, mealyss.getInputAlphabet())){
				System.out.println("Equivalent!!!\n");
			}else{
				System.err.println("Non Equivalent!!!\n");
			}
			
		} catch (Exception e) {
			e.printStackTrace();
		}
	}
}
