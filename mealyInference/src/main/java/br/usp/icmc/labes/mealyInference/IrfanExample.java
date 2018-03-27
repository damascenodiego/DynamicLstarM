package br.usp.icmc.labes.mealyInference;

import java.io.File;
import java.io.FileWriter;
import java.util.ArrayList;
import java.util.List;
import java.util.Random;

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
import de.learnlib.datastructure.observationtable.writer.ObservationTableASCIIWriter;
import de.learnlib.driver.util.MealySimulatorSUL;
import de.learnlib.filter.cache.mealy.MealyCaches;
import de.learnlib.filter.cache.sul.SULCaches;
import de.learnlib.filter.statistic.sul.ResetCounterSUL;
import de.learnlib.filter.statistic.sul.SymbolCounterSUL;
import de.learnlib.oracle.equivalence.WpMethodEQOracle;
import de.learnlib.oracle.equivalence.mealy.RandomWalkEQOracle;
import de.learnlib.oracle.membership.SULOracle;
import de.learnlib.util.statistics.SimpleProfiler;
import net.automatalib.automata.transout.MealyMachine;
import net.automatalib.automata.transout.impl.compact.CompactMealy;
import net.automatalib.serialization.dot.GraphDOT;
import net.automatalib.words.Word;

public class IrfanExample {

	public static void main(String[] args) {
		
		try {
			// set SUL path
			File sul = new File("./experiments_irfan/example.txt");
						
			// load mealy machine
			CompactMealy<String, Word<String>> mealyss = Utils.getInstance().loadMealyMachine(sul);
			
			// set closing strategy
			ClosingStrategy strategy 			= ClosingStrategies.CLOSE_FIRST;

			// set CE processing approach
			ObservationTableCEXHandler handler 	= ObservationTableCEXHandlers.RIVEST_SCHAPIRE;
			
			// Empty list of prefixes 
			List<Word<String>> initPrefixes = new ArrayList<Word<String>>();
			initPrefixes.add(Word.epsilon());
						
			// Empty list of suffixes => minimal compliant setinitCes
			List<Word<String>> initSuffixes = new ArrayList<Word<String>>();
			for (String abc : mealyss.getInputAlphabet()) {
				Word in = Word.epsilon();
				in = in.append(abc);
				initSuffixes.add(in);
			}

			// SUL simulator
			SUL<String,Word<String>> sulSim = new MealySimulatorSUL(mealyss, Utils.getInstance().OMEGA_SYMBOL);
						
			// membership oracle for counting queries wraps sul
			StatisticSUL<String, Word<String>>  mqSul_sym = new SymbolCounterSUL<>("MQ", sulSim);
			StatisticSUL<String, Word<String>>  mqSul_rst = new ResetCounterSUL <>("MQ", mqSul_sym);			
			MembershipOracle<String, Word<Word<String>>> mqOracle = new SULOracle<String, Word<String>>(mqSul_rst);

			// use caching to avoid duplicate queries
			mqOracle = MealyCaches.createTreeCache(mealyss.getInputAlphabet(), mqOracle);


			// construct L* instance 
			ExtensibleLStarMealyBuilder<String, Word<String>> builder = new ExtensibleLStarMealyBuilder<String, Word<String>>();
			builder.setAlphabet(mealyss.getInputAlphabet());
			builder.setOracle(mqOracle);
			builder.setInitialPrefixes(initPrefixes);
			builder.setInitialSuffixes(initSuffixes);
			builder.setCexHandler(handler);
			builder.setClosingStrategy(strategy);

			ExtensibleLStarMealy<String, Word<String>> learner = builder.create();
			
			// equivalence oracle for counting queries wraps sul
			StatisticSUL<String, Word<String>> eqSul_sym = new SymbolCounterSUL<>("EQ", sulSim);
			StatisticSUL<String, Word<String>> eqSul_rst = new ResetCounterSUL<>("EQ", eqSul_sym);
			SUL<String, Word<String>> eq_sul = SULCaches.createTreeCache(mealyss.getInputAlphabet(), eqSul_rst);
			MembershipOracle<String, Word<Word<String>>> sulEqOracle = new SULOracle<String, Word<String>>(eq_sul);
			EquivalenceOracle eqOracle = new WpMethodEQOracle<>(sulEqOracle, 2);
			
			
			new ObservationTableASCIIWriter<>().write(learner.getObservationTable(), System.out);
			learner.startLearning();
			new ObservationTableASCIIWriter<>().write(learner.getObservationTable(), System.out);
			
			Word<String> word = Word.epsilon();
			word=word.append("a");
			word=word.append("b");
			word=word.append("a");
			word=word.append("b");
			word=word.append("a");
			word=word.append("a");
			word=word.append("b");
			
			System.out.println(word);
			DefaultQuery<String, Word<Word<String>>> ce = new DefaultQuery<>(word);
			ce.answer(mqOracle.answerQuery(word));
			
			learner.refineHypothesis(ce);
				
			new ObservationTableASCIIWriter<>().write(learner.getObservationTable(), System.out);
			
			
			
		} catch (Exception e) {
			e.printStackTrace();
		}
	}
}
