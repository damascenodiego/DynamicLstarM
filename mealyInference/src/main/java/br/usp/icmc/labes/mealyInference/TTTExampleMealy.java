package br.usp.icmc.labes.mealyInference;

import java.io.BufferedWriter;
import java.io.File;
import java.io.FileWriter;
import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Optional;
import java.util.Random;
import java.util.Set;

import br.usp.icmc.labes.mealyInference.utils.MyObservationTable;
import br.usp.icmc.labes.mealyInference.utils.OTUtils;
import br.usp.icmc.labes.mealyInference.utils.Utils;
import de.learnlib.acex.AcexAnalyzer;
import de.learnlib.acex.analyzers.AcexAnalyzers;
import de.learnlib.algorithms.adt.util.ADTUtil;
import de.learnlib.algorithms.lstar.ce.ObservationTableCEXHandler;
import de.learnlib.algorithms.lstar.ce.ObservationTableCEXHandlers;
import de.learnlib.algorithms.lstar.closing.ClosingStrategies;
import de.learnlib.algorithms.lstar.closing.ClosingStrategy;
import de.learnlib.algorithms.lstar.mealy.ExtensibleLStarMealy;
import de.learnlib.algorithms.lstar.mealy.ExtensibleLStarMealyBuilder;
import de.learnlib.algorithms.ttt.dfa.TTTLearnerDFA;
import de.learnlib.algorithms.ttt.dfa.TTTLearnerDFABuilder;
import de.learnlib.algorithms.ttt.mealy.TTTLearnerMealy;
import de.learnlib.algorithms.ttt.mealy.TTTLearnerMealyBuilder;
import de.learnlib.api.SUL;
import de.learnlib.api.oracle.EquivalenceOracle;
import de.learnlib.api.oracle.MembershipOracle;
import de.learnlib.api.query.DefaultQuery;
import de.learnlib.api.statistic.StatisticOracle;
import de.learnlib.api.statistic.StatisticSUL;
import de.learnlib.datastructure.observationtable.ObservationTable;
import de.learnlib.datastructure.observationtable.writer.ObservationTableASCIIWriter;
import de.learnlib.driver.util.MealySimulatorSUL;
import de.learnlib.filter.cache.sul.SULCache;
import de.learnlib.filter.statistic.oracle.CounterOracle.DFACounterOracle;
import de.learnlib.filter.statistic.sul.ResetCounterSUL;
import de.learnlib.filter.statistic.sul.SymbolCounterSUL;
import de.learnlib.oracle.equivalence.RandomWordsEQOracle;
import de.learnlib.oracle.equivalence.RandomWordsEQOracle.DFARandomWordsEQOracle;
import de.learnlib.oracle.membership.SULOracle;
import de.learnlib.oracle.membership.SimulatorOracle;
import de.learnlib.oracle.membership.SimulatorOracle.DFASimulatorOracle;
import de.learnlib.util.Experiment.DFAExperiment;
import net.automatalib.automata.fsa.DFA;
import net.automatalib.automata.fsa.impl.compact.CompactDFA;
import net.automatalib.automata.transout.MealyMachine;
import net.automatalib.automata.transout.impl.compact.CompactMealy;
import net.automatalib.graphs.ads.ADSNode;
import net.automatalib.incremental.mealy.IncrementalMealyBuilder;
import net.automatalib.incremental.mealy.tree.IncrementalMealyTreeBuilder;
import net.automatalib.serialization.dot.DefaultDOTVisualizationHelper;
import net.automatalib.serialization.dot.GraphDOT;
import net.automatalib.util.automata.Automata;
import net.automatalib.util.automata.ads.ADS;
import net.automatalib.util.automata.ads.ADSUtil;
import net.automatalib.util.automata.builders.DFABuilder;
import net.automatalib.visualization.Visualization;
import net.automatalib.words.Alphabet;
import net.automatalib.words.Word;
import net.automatalib.words.abstractimpl.AbstractAlphabet;
import net.automatalib.words.impl.Alphabets;
import de.learnlib.oracle.membership.SULOracle;

public class TTTExampleMealy {

	public static void main(String[] args) {

		try {

			CompactMealy<String,String> mealy = createWipeSystemMealyMachine();
			Alphabet<String> alphabet = mealy.getInputAlphabet();
			
			Set states = new HashSet<>(mealy.getStates());
			Optional<ADSNode> ads_out = ADS.compute(mealy, mealy.getInputAlphabet(), states );
			ADSNode item = ads_out.get();
			Visualization.visualize(item);
			System.out.println(ads_out);


			// set closing strategy
			ClosingStrategy strategy = ClosingStrategies.CLOSE_FIRST;

			// set CE processing approach
			ObservationTableCEXHandler handler 	= ObservationTableCEXHandlers.RIVEST_SCHAPIRE;


			// Empty list of prefixes 
			List<Word<String>> initPrefixes = new ArrayList<Word<String>>();
			initPrefixes.add(Word.epsilon());

			// Empty list of suffixes => minimal compliant setinitCes
			List<Word<String>> initSuffixes = new ArrayList<Word<String>>();

			Utils.getInstance();
			// SUL simulator
			SUL<String,String> sul = new MealySimulatorSUL<>(mealy);

			// IncrementalMealyBuilder for caching EQs and MQs together
			IncrementalMealyBuilder<String,String> cbuilder = new IncrementalMealyTreeBuilder<>(mealy.getInputAlphabet());

			// Cache using SULCache
			StatisticSUL<String, String> mq_rst = new ResetCounterSUL <>("MQ", sul);
			StatisticSUL<String, String> eq_rst = new ResetCounterSUL <>("EQ", sul);
			// SULs for associating the IncrementalMealyBuilder 'cbuilder' to MQs and EQs
			SUL<String, String> mq_sul = new SULCache<>(cbuilder, mq_rst);
			SUL<String, String> eq_sul = new SULCache<>(cbuilder, eq_rst);
			// MembershipOracles to wrap the SULs for MQs and EQs
			MembershipOracle<String,Word<String>> oracleForLearner  = new SULOracle<>(mq_sul);
			MembershipOracle<String,Word<String>> oracleForEQoracle = new SULOracle<>(eq_sul);

			EquivalenceOracle eqOracle = new RandomWordsEQOracle(oracleForEQoracle, 2, 5, 100, new Random(1));

			// construct L* instance 
			TTTLearnerMealyBuilder<String,String> builder = new TTTLearnerMealyBuilder<>();
			builder.setAlphabet(alphabet);
			builder.setAnalyzer(AcexAnalyzers.LINEAR_FWD);
			builder.setOracle(oracleForLearner);

			TTTLearnerMealy<String,String> learner = builder.create();

			// start learning
			learner.startLearning();

			boolean done = false;
			MealyMachine hyp = null;
			DefaultQuery ce = null;
			//            ce = new DefaultQuery<>(Word.epsilon().append("switchPerm"));
			//            ce.answer(oracleForEQoracle.answerQuery(ce.getInput()));
			//            ce = new DefaultQuery<>(Word.epsilon().append("rain"));
			//            ce.answer(oracleForEQoracle.answerQuery(ce.getInput()));
			//            ce = new DefaultQuery<>(Word.epsilon().append("rain").append("switchPerm"));
			//            ce.answer(oracleForEQoracle.answerQuery(ce.getInput()));;
			int id = 0;
			while (!done) {
				File hypFile = new File("hyp"+id+".dot");
				File dtFile = new File("dt"+id+".dot");
				hyp = learner.getHypothesisModel();
				// show hypothesis
				//Visualization.visualize(learner.getHypothesisModel(), alphabet, new DefaultDOTVisualizationHelper<>());
				GraphDOT.write(learner.getHypothesisModel(), alphabet, new BufferedWriter(new FileWriter(hypFile)));
				// show DT
				//Visualization.visualize(learner.getDiscriminationTree());
				GraphDOT.write(learner.getDiscriminationTree(), new BufferedWriter(new FileWriter(dtFile)),new DefaultDOTVisualizationHelper());

				ce = eqOracle.findCounterExample(hyp, alphabet);
				if (ce == null) {
					done = true;
					continue;
				}
				System.out.println(ce.toString());
				learner.refineHypothesis(ce);
				id++;
			}

			// learning statistics
			System.out.println(mq_rst.getStatisticalData().getSummary());
			System.out.println(eq_rst.getStatisticalData().getSummary());

			if(Automata.testEquivalence(learner.getHypothesisModel(), mealy, mealy.getInputAlphabet())){
				System.out.println("Equivalent!!!\n");
			}else{
				System.err.println("Non Equivalent!!!\n");
			}

			// show hypothesis
			Visualization.visualize(learner.getHypothesisModel(), alphabet, new DefaultDOTVisualizationHelper<>());
			// show DT
			Visualization.visualize(learner.getDiscriminationTree());

		} catch (Exception e) {
			e.printStackTrace();
		}
	}

	private static CompactMealy<String, String> createIrfanMealyMachine() {
		String[] symbols = {"a","b"};
		Alphabet<String> alphabet = Alphabets.fromArray(symbols);
		CompactMealy<String,String> mealy = new CompactMealy<>(alphabet);

		Integer q0 = mealy.addInitialState();
		Integer q1 = mealy.addState();
		Integer q2 = mealy.addState();

		mealy.addTransition(q0, "b", q0,"y");
		mealy.addTransition(q1, "b", q0,"y");
		mealy.addTransition(q2, "b", q1,"x");

		mealy.addTransition(q0, "a", q1,"x");
		mealy.addTransition(q1, "a", q2,"x");
		mealy.addTransition(q2, "a", q2,"x");

		return mealy;
	}

	private static CompactMealy<String, String> createWipeSystemMealyMachine() {
		String[] symbols = {"rain","switchIntv","switchPerm"};
		Alphabet<String> alphabet = Alphabets.fromArray(symbols);
		CompactMealy<String,String> mealy = new CompactMealy<>(alphabet);

		Integer q1 = mealy.addInitialState();
		Integer q2 = mealy.addState();
		Integer q3 = mealy.addState();
		Integer q4 = mealy.addState();

		mealy.addTransition(q1, "rain", q1,"0");
		mealy.addTransition(q1, "switchIntv", q2,"1");
		mealy.addTransition(q1, "switchPerm", q3,"1");

		mealy.addTransition(q2, "rain", q2,"0");
		mealy.addTransition(q2, "switchIntv", q3,"1");
		mealy.addTransition(q2, "switchPerm", q1,"0");

		mealy.addTransition(q3, "rain", q4,"1");
		mealy.addTransition(q3, "switchIntv", q1,"0");
		mealy.addTransition(q3, "switchPerm", q2,"1");

		mealy.addTransition(q4, "rain", q3,"0");
		mealy.addTransition(q4, "switchIntv", q4,"1");
		mealy.addTransition(q4, "switchPerm", q4,"0");

		return mealy;
	}
}
