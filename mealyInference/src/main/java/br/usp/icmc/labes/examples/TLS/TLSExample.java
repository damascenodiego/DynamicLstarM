package br.usp.icmc.labes.examples.TLS;

import java.io.BufferedWriter;
import java.io.File;
import java.io.FileWriter;
import java.util.ArrayList;
import java.util.List;

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
import de.learnlib.api.oracle.EquivalenceOracle.MealyEquivalenceOracle;
import de.learnlib.api.oracle.EquivalenceOracle;
import de.learnlib.api.oracle.MembershipOracle;
import de.learnlib.api.statistic.StatisticSUL;
import de.learnlib.datastructure.observationtable.ObservationTable;
import de.learnlib.datastructure.observationtable.writer.ObservationTableASCIIWriter;
import de.learnlib.driver.util.MealySimulatorSUL;
import de.learnlib.filter.cache.sul.SULCache;
import de.learnlib.filter.statistic.sul.ResetCounterSUL;
import de.learnlib.filter.statistic.sul.SymbolCounterSUL;
import de.learnlib.oracle.equivalence.RandomWpMethodEQOracle;
import de.learnlib.oracle.equivalence.WpMethodEQOracle;
import de.learnlib.oracle.equivalence.WpMethodEQOracle.MealyWpMethodEQOracle;
import de.learnlib.oracle.membership.SULOracle;
import de.learnlib.util.Experiment.MealyExperiment;
import net.automatalib.automata.transout.MealyMachine;
import net.automatalib.automata.transout.impl.compact.CompactMealy;
import net.automatalib.incremental.mealy.IncrementalMealyBuilder;
import net.automatalib.incremental.mealy.tree.IncrementalMealyTreeBuilder;
import net.automatalib.serialization.dot.GraphDOT;
import net.automatalib.visualization.Visualization;
import net.automatalib.words.Alphabet;
import net.automatalib.words.Word;

public class TLSExample {

	public static void main(String[] args) {
		
		try{
			
			for (int i = 0; i < TLSExample_utils.versions.length; i++) {
			
				File file = new File(TLSExample_utils.versions[i]);
				
				// create out_dir
				File out_dir = new File(file.getParent(),file.getName().replaceFirst(".dot$", "")); out_dir.mkdirs();
				
				// load mealy machine
				CompactMealy<String, Word<String>> mealyss = Utils.getInstance().loadMealyMachineFromDot(file);

				// SUL simulator
				SUL<String,Word<String>> sulSim = new MealySimulatorSUL(mealyss, Utils.OMEGA_SYMBOL);
				
				// SUL alphabet
				Alphabet<String> alphabet = mealyss.getInputAlphabet();

				// Empty list of prefixes 
				List<Word<String>> initPrefixes = new ArrayList<Word<String>>();
				initPrefixes.add(Word.epsilon());

				// Empty list of suffixes => minimal compliant setinitCes
				List<Word<String>> initSuffixes = new ArrayList<Word<String>>();

				// set closing strategy
				ClosingStrategy strategy 			= ClosingStrategies.CLOSE_FIRST;

				// set CE processing approach
				ObservationTableCEXHandler handler 	= ObservationTableCEXHandlers.RIVEST_SCHAPIRE;

				// IncrementalMealyBuilder for caching EQs and MQs together
				IncrementalMealyBuilder<String,Word<String>> cbuilder = new IncrementalMealyTreeBuilder<>(alphabet);			

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
				MembershipOracle<String,Word<Word<String>>> oracleForLearner  = new SULOracle<>(mq_rst);
				MembershipOracle<String,Word<Word<String>>> oracleForEQoracle = new SULOracle<>(eq_rst);

				//						Word<String> word = Word.epsilon();
				//						for (String s_word : alphabet) {
				//							word = Word.epsilon();
				//							word=word.append(s_word);
				//							initSuffixes.add(word);
				//						}

				// construct L* instance 
				ExtensibleLStarMealyBuilder<String, Word<String>> builder = new ExtensibleLStarMealyBuilder<String, Word<String>>();
				builder.setAlphabet(alphabet);
				builder.setOracle(oracleForLearner);
				builder.setInitialPrefixes(initPrefixes);
				builder.setInitialSuffixes(initSuffixes);
				builder.setCexHandler(handler);
				builder.setClosingStrategy(strategy);

				ExtensibleLStarMealy<String, Word<String>> learner = builder.create();

				// Equivalence Query Oracle
				EquivalenceOracle<MealyMachine<?, String, ?, Word<String>>, String, Word<Word<String>>> eqOracle = null;
				eqOracle = new WpMethodEQOracle<>(oracleForEQoracle, 2);
				// The experiment will execute the main loop of active learning
				MealyExperiment<String, Word<String>> experiment = new MealyExperiment<String, Word<String>> (learner, eqOracle, alphabet);
				// turn on time profiling
				experiment.setProfile(true);
				// enable logging of models
				experiment.setLogModels(true);
				// run experiment
				experiment.run();

				// learning statistics
				BufferedWriter bw = new BufferedWriter(new FileWriter(new File(out_dir,file.getName()+".ot")));
				bw.write(mq_rst.getStatisticalData().toString());bw.write("\n");
				bw.write(mq_sym.getStatisticalData().toString());bw.write("\n");
				bw.write(eq_rst.getStatisticalData().toString());bw.write("\n");
				bw.write(eq_sym.getStatisticalData().toString());bw.write("\n");
				bw.write(experiment.getRounds().toString());bw.write("\n");
				bw.write("States: "+experiment.getFinalHypothesis().getStates().size());bw.write("\n");

				new ObservationTableASCIIWriter<>().write(learner.getObservationTable(), bw);
				bw.close();
				//				GraphDOT.write(learner.getHypothesisModel(), learner.getHypothesisModel().getInputAlphabet(), System.out);
				File sul_ot = new File(out_dir,file.getName()+".reuse");
				OTUtils.getInstance().writeOT(learner.getObservationTable(), sul_ot);
				bw.close();
			}

		} catch (Exception e) {
			e.printStackTrace();
		}
	}
}
