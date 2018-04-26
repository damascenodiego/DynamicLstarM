package br.usp.icmc.labes.mealyInference;

import java.io.File;
import java.util.ArrayList;
import java.util.List;

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
import de.learnlib.oracle.membership.SULOracle;
import net.automatalib.automata.transout.impl.compact.CompactMealy;
import net.automatalib.util.automata.Automata;
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

			Utils.getInstance();
			// SUL simulator
			SUL<String,Word<String>> sulSim = new MealySimulatorSUL(mealyss, Utils.OMEGA_SYMBOL);
						
			// membership oracle for counting queries wraps sul
			StatisticSUL<String, Word<String>>  mqSul_sym = new SymbolCounterSUL<>("MQ", sulSim);
			StatisticSUL<String, Word<String>>  mqSul_rst = new ResetCounterSUL <>("MQ", mqSul_sym);			
			MembershipOracle<String, Word<Word<String>>> mqOracle = new SULOracle<String, Word<String>>(mqSul_rst);

			// use caching to avoid duplicate queries
			MembershipOracle<String, Word<Word<String>>> mq_cache = MealyCaches.createTreeCache(mealyss.getInputAlphabet(), mqOracle);


			// construct L* instance 
			ExtensibleLStarMealyBuilder<String, Word<String>> builder = new ExtensibleLStarMealyBuilder<String, Word<String>>();
			builder.setAlphabet(mealyss.getInputAlphabet());
			builder.setOracle(mq_cache);
			builder.setInitialPrefixes(initPrefixes);
			builder.setInitialSuffixes(initSuffixes);
			builder.setCexHandler(handler);
			builder.setClosingStrategy(strategy);

			ExtensibleLStarMealy<String, Word<String>> learner = builder.create();
			
			// equivalence oracle for counting queries wraps sul
			StatisticSUL<String, Word<String>> eqSul_sym = new SymbolCounterSUL<>("EQ", sulSim);
			StatisticSUL<String, Word<String>> eqSul_rst = new ResetCounterSUL<>("EQ", eqSul_sym);
		
			
			learner.startLearning();
			new ObservationTableASCIIWriter<>().write(learner.getObservationTable(), System.out);
			// learning statistics
			System.out.println(mqSul_rst.getStatisticalData());
			System.out.println(mqSul_sym.getStatisticalData());
			System.out.println(eqSul_rst.getStatisticalData());
			System.out.println(eqSul_sym.getStatisticalData());
	
			
			// creating a second cache (???) --> How can I reuse a cache and separately count EQs and MQs??? 
			SUL<String, Word<String>> eq_cache = //eqSul_rst; 
												 SULCaches.createTreeCache(mealyss.getInputAlphabet(), eqSul_rst);
			
			
			MembershipOracle<String, Word<Word<String>>> sulEqOracle = new SULOracle<String, Word<String>>(eq_cache);
			EquivalenceOracle eqOracle = new WpMethodEQOracle<>(sulEqOracle, 2);
			
			
			// learning statistics
			System.out.println(mqSul_rst.getStatisticalData());
			System.out.println(mqSul_sym.getStatisticalData());
			System.out.println(eqSul_rst.getStatisticalData());
			System.out.println(eqSul_sym.getStatisticalData());
						
			DefaultQuery<String,Word<Word<String>>> ce = eqOracle.findCounterExample(learner.getHypothesisModel(), learner.getHypothesisModel().getInputAlphabet());
//			ce = eqOracle.findCounterExample(learner.getHypothesisModel(), learner.getHypothesisModel().getInputAlphabet());
			if(ce != null){
				learner.refineHypothesis(ce);
				System.out.println(ce);
			}
				
			new ObservationTableASCIIWriter<>().write(learner.getObservationTable(), System.out);
			
			// learning statistics
			System.out.println(mqSul_rst.getStatisticalData());
			System.out.println(mqSul_sym.getStatisticalData());
			System.out.println(eqSul_rst.getStatisticalData());
			System.out.println(eqSul_sym.getStatisticalData());

			if(Automata.testEquivalence(learner.getHypothesisModel(), mealyss, mealyss.getInputAlphabet())){
				System.out.println("Equivalent!!!");
			}else{
				System.out.println("Non Equivalent!!!");
			}
			
		} catch (Exception e) {
			e.printStackTrace();
		}
	}
}
