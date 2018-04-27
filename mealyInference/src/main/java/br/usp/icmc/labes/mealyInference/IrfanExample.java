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
import de.learnlib.api.oracle.MembershipOracle.MealyMembershipOracle;
import de.learnlib.api.query.DefaultQuery;
import de.learnlib.datastructure.observationtable.writer.ObservationTableASCIIWriter;
import de.learnlib.driver.util.MealySimulatorSUL;
import de.learnlib.filter.cache.mealy.MealyCacheOracle;
import de.learnlib.filter.statistic.oracle.JointCounterOracle;
import de.learnlib.oracle.equivalence.WpMethodEQOracle;
import de.learnlib.oracle.membership.SULOracle;
import net.automatalib.automata.transout.MealyMachine;
import net.automatalib.automata.transout.impl.compact.CompactMealy;
import net.automatalib.incremental.mealy.IncrementalMealyBuilder;
import net.automatalib.incremental.mealy.tree.IncrementalMealyTreeBuilder;
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
						
			// IncrementalMealyBuilder for caching EQs and MQs together
			IncrementalMealyBuilder<String,Word<String>> cbuilder = new IncrementalMealyTreeBuilder<>(mealyss.getInputAlphabet());			

			// Cache using MealyCacheOracle
			// MembershipOracle wrapping the SUL for MQs and EQs 
			MembershipOracle<String, Word<Word<String>>> sul_wrapper = new SULOracle<String, Word<String>>(sulSim);

			// Counters for MQs and EQs
			JointCounterOracle<String, Word<Word<String>>> mqStatOracle = new JointCounterOracle<>(sul_wrapper);
			JointCounterOracle<String, Word<Word<String>>> eqStatOracle = new JointCounterOracle<>(sul_wrapper);

			// MembershipOracles for associating the IncrementalMealyBuilder 'cbuilder' to MQs and EQs
			MealyMembershipOracle<String,Word<String>> oracleForLearner = new MealyCacheOracle<>(cbuilder, null, mqStatOracle);
			MealyMembershipOracle<String,Word<String>> oracleForEQoracle = new MealyCacheOracle<>(cbuilder, null, eqStatOracle);
						
			// construct L* instance 
			ExtensibleLStarMealyBuilder<String, Word<String>> builder = new ExtensibleLStarMealyBuilder<String, Word<String>>();
			builder.setAlphabet(mealyss.getInputAlphabet());
			builder.setOracle(oracleForLearner);
			builder.setInitialPrefixes(initPrefixes);
			builder.setInitialSuffixes(initSuffixes);
			builder.setCexHandler(handler);
			builder.setClosingStrategy(strategy);

			ExtensibleLStarMealy<String, Word<String>> learner = builder.create();
			
			learner.startLearning();
			new ObservationTableASCIIWriter<>().write(learner.getObservationTable(), System.out);
			// learning statistics
			System.out.println("MQ [resets]: " +mqStatOracle.getQueryCount());
			System.out.println("MQ [symbols]: "+mqStatOracle.getSymbolCount());
			System.out.println("EQ [resets]: " +eqStatOracle.getQueryCount());
			System.out.println("EQ [symbols]: "+eqStatOracle.getSymbolCount());
	
			
			EquivalenceOracle<MealyMachine<?, String, ?, Word<String>>, String, Word<Word<String>>> eqOracle = null;
			eqOracle = new WpMethodEQOracle<>(oracleForEQoracle, 2);
//			eqOracle = new IrfanEQOracle<>(sulSim, mealyss.getStates().size(), new Random(123));
			
			
			// learning statistics
			System.out.println("MQ [resets]: " +mqStatOracle.getQueryCount());
			System.out.println("MQ [symbols]: "+mqStatOracle.getSymbolCount());
			System.out.println("EQ [resets]: " +eqStatOracle.getQueryCount());
			System.out.println("EQ [symbols]: "+eqStatOracle.getSymbolCount());
						
			DefaultQuery<String,Word<Word<String>>> ce = eqOracle.findCounterExample(learner.getHypothesisModel(), learner.getHypothesisModel().getInputAlphabet());
//			ce = eqOracle.findCounterExample(learner.getHypothesisModel(), learner.getHypothesisModel().getInputAlphabet());
			if(ce != null){
				learner.refineHypothesis(ce);
				System.out.println(ce);
			}
				
			new ObservationTableASCIIWriter<>().write(learner.getObservationTable(), System.out);
			
			// learning statistics
			System.out.println("MQ [resets]: " +mqStatOracle.getQueryCount());
			System.out.println("MQ [symbols]: "+mqStatOracle.getSymbolCount());
			System.out.println("EQ [resets]: " +eqStatOracle.getQueryCount());
			System.out.println("EQ [symbols]: "+eqStatOracle.getSymbolCount());

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
