package experiments.br.usp.icmc.labes;

import java.io.BufferedWriter;
import java.io.File;
import java.io.FileWriter;
import java.text.SimpleDateFormat;
import java.util.ArrayList;
import java.util.List;

import br.usp.icmc.labes.mealyInference.utils.MyObservationTable;
import br.usp.icmc.labes.mealyInference.utils.OTUtils;
import br.usp.icmc.labes.mealyInference.utils.RandomWMethodQsizeEQOracle;
import br.usp.icmc.labes.mealyInference.utils.Utils;
import de.learnlib.algorithms.dlstar.mealy.ExtensibleDLStarMealy;
import de.learnlib.algorithms.dlstar.mealy.ExtensibleDLStarMealyBuilder;
import de.learnlib.algorithms.lstar.ce.ObservationTableCEXHandler;
import de.learnlib.algorithms.lstar.ce.ObservationTableCEXHandlers;
import de.learnlib.algorithms.lstar.closing.ClosingStrategies;
import de.learnlib.algorithms.lstar.closing.ClosingStrategy;
import de.learnlib.algorithms.lstar.mealy.ExtensibleLStarMealy;
import de.learnlib.algorithms.lstar.mealy.ExtensibleLStarMealyBuilder;
import de.learnlib.api.SUL;
import de.learnlib.api.oracle.EquivalenceOracle;
import de.learnlib.api.oracle.MembershipOracle;
import de.learnlib.api.statistic.StatisticSUL;
import de.learnlib.datastructure.observationtable.ObservationTable;
import de.learnlib.datastructure.observationtable.writer.ObservationTableASCIIWriter;
import de.learnlib.driver.util.MealySimulatorSUL;
import de.learnlib.filter.cache.sul.SULCache;
import de.learnlib.filter.statistic.Counter;
import de.learnlib.filter.statistic.sul.ResetCounterSUL;
import de.learnlib.filter.statistic.sul.SymbolCounterSUL;
import de.learnlib.oracle.equivalence.WMethodEQOracle;
import de.learnlib.oracle.membership.SULOracle;
import de.learnlib.util.Experiment.MealyExperiment;
import net.automatalib.automata.transout.MealyMachine;
import net.automatalib.automata.transout.impl.compact.CompactMealy;
import net.automatalib.incremental.mealy.IncrementalMealyBuilder;
import net.automatalib.incremental.mealy.tree.IncrementalMealyTreeBuilder;
import net.automatalib.util.automata.Automata;
import net.automatalib.words.Alphabet;
import net.automatalib.words.Word;

public class ExperimentNordsec16CreateOTs {

	public static void main(String[] args) {

		try{
			ExperimentNordsec16Utils.getInstance().nordsec16_client_rlzdate();
			generate_OTsFromWset();

			ExperimentNordsec16Utils.getInstance().nordsec16_server_rlzdate();
			generate_OTsFromWset();

		} catch (Exception e) {
			e.printStackTrace();
		}
	}

	private static void generate_OTsFromWset() throws Exception {

		for (int i = 0; i < ExperimentNordsec16Utils.getInstance().getVersions().length; i++) {

			File file = new File(ExperimentNordsec16Utils.getInstance().getVersions()[i]);
			// create out_dir
			File out_dir = new File(file.getParent(),file.getName().replaceFirst(".dot$", "")); out_dir.mkdirs();

			File sul_ot = new File(out_dir,file.getName()+".reuse");

			// comment 
			if(sul_ot.exists()) continue;

			// load mealy machine
			CompactMealy<String, Word<String>> mealyss = Utils.getInstance().loadMealyMachineFromDot(file);
			SUL<String,Word<String>> sulSim = new MealySimulatorSUL(mealyss, Utils.OMEGA_SYMBOL);
			Alphabet<String> alphabet = mealyss.getInputAlphabet();
			List<Word<String>> initPrefixes = new ArrayList<Word<String>>();
			initPrefixes.add(Word.epsilon());

			// List of suffixes with W set
			List<Word<String>> initSuffixes = new ArrayList<Word<String>>();
			//			List<Word<String>> wset = Automata.characterizingSet(mealyss, alphabet);
			//			initSuffixes.addAll(wset);

			// set closing strategy and CE processing approach
			ClosingStrategy strategy 			= ClosingStrategies.CLOSE_FIRST;
			ObservationTableCEXHandler handler 	= ObservationTableCEXHandlers.RIVEST_SCHAPIRE;

			MembershipOracle<String,Word<Word<String>>> oracleForLearner  = new SULOracle<>(sulSim);
			MembershipOracle<String,Word<Word<String>>> oracleForEQoracle = new SULOracle<>(sulSim);

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
			eqOracle = new WMethodEQOracle(oracleForEQoracle, 2);

			// The experiment will execute the main loop of active learning
			MealyExperiment<String, Word<String>> experiment = new MealyExperiment<String, Word<String>> (learner, eqOracle, alphabet);
			// turn on time profiling
			experiment.setProfile(true);
			// enable logging of models
			experiment.setLogModels(true);
			// run experiment
			experiment.run();

			boolean success = Automata.testEquivalence(mealyss, learner.getHypothesisModel(), mealyss.getInputAlphabet());
			if(success){
				OTUtils.getInstance().writeOT(learner.getObservationTable(), sul_ot);
			}
		}
		//		bw_comparison.close();

	}
}
