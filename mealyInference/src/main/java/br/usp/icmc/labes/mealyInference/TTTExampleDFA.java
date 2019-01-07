package br.usp.icmc.labes.mealyInference;

import java.util.ArrayList;
import java.util.List;
import java.util.Random;

import br.usp.icmc.labes.mealyInference.utils.Utils;
import de.learnlib.acex.analyzers.AcexAnalyzers;
import de.learnlib.algorithms.lstar.ce.ObservationTableCEXHandler;
import de.learnlib.algorithms.lstar.ce.ObservationTableCEXHandlers;
import de.learnlib.algorithms.lstar.closing.ClosingStrategies;
import de.learnlib.algorithms.lstar.closing.ClosingStrategy;
import de.learnlib.algorithms.ttt.dfa.TTTLearnerDFA;
import de.learnlib.algorithms.ttt.dfa.TTTLearnerDFABuilder;
import de.learnlib.api.query.DefaultQuery;
import de.learnlib.filter.statistic.oracle.CounterOracle.DFACounterOracle;
import de.learnlib.oracle.equivalence.RandomWordsEQOracle.DFARandomWordsEQOracle;
import de.learnlib.oracle.membership.SimulatorOracle.DFASimulatorOracle;
import de.learnlib.util.Experiment.DFAExperiment;
import net.automatalib.automata.fsa.DFA;
import net.automatalib.automata.fsa.impl.compact.CompactDFA;
import net.automatalib.serialization.dot.DefaultDOTVisualizationHelper;
import net.automatalib.util.automata.Automata;
import net.automatalib.visualization.Visualization;
import net.automatalib.words.Alphabet;
import net.automatalib.words.Word;
import net.automatalib.words.impl.Alphabets;

public class TTTExampleDFA {

	public static void main(String[] args) {
		
		try {
			
			String[] symbols = {"a","b"};
			Alphabet<String> alphabet = Alphabets.fromArray(symbols);
			CompactDFA<String> dfa = new CompactDFA<>(alphabet);
			
			Integer q0 = dfa.addInitialState();
			Integer q1 = dfa.addState();
			Integer q2 = dfa.addState();
			Integer q3 = dfa.addState();
			
			dfa.addTransition(q0, "b", q0);
			dfa.addTransition(q1, "b", q1);
			dfa.addTransition(q2, "b", q2);
			dfa.addTransition(q3, "b", q3);

			dfa.addTransition(q0, "a", q1);
			dfa.addTransition(q1, "a", q2);
			dfa.addTransition(q2, "a", q3);
			dfa.addTransition(q3, "a", q0);
			dfa.setAccepting(q3, true);

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
			DFASimulatorOracle<String> simOracle = new DFASimulatorOracle<>(dfa);

			// Counters for MQs and EQs
			DFACounterOracle<String> mqCounter = new DFACounterOracle<>(simOracle, "MQ");
			DFACounterOracle<String> eqCounter = new DFACounterOracle<>(simOracle, "EQ");
			
			// construct L* instance 
			TTTLearnerDFABuilder<String> builder = new TTTLearnerDFABuilder<>();
			builder.setAlphabet(alphabet);
			builder.setAnalyzer(AcexAnalyzers.LINEAR_FWD);
			builder.setOracle(mqCounter);

			TTTLearnerDFA<String> learner = builder.create();
			
			DFARandomWordsEQOracle<String> eqOracle = new DFARandomWordsEQOracle<>(eqCounter, 9, 9, 100, new Random(1));
			
	        // construct a learning experiment from the learning algorithm and the conformance test.
	        // The experiment will execute the main loop of active learning
	        DFAExperiment<String> experiment = new DFAExperiment<>(learner, eqOracle, alphabet);
	        
	        //experiment.run();
	        
            // start learning
	        learner.startLearning();

            boolean done = false;
            DFA<?, String> hyp = null;
            while (!done) {
                hyp = learner.getHypothesisModel();
                // show hypothesis
    			Visualization.visualize(learner.getHypothesisModel(), alphabet, new DefaultDOTVisualizationHelper<>());
                // show DT
    			Visualization.visualize(learner.getDiscriminationTree());

                DefaultQuery ce = eqOracle.findCounterExample(hyp, alphabet);
//    			DefaultQuery ce = new DefaultQuery<>(Word.epsilon()
//    					.append("b").append("b").append("b")
//    					.append("a").append("a").append("a")
//    					.append("b").append("b").append("b"));
//    			ce.answer(eqCounter.answerQuery(ce.getInput()));;
                if (ce == null) {
                    done = true;
                    continue;
                }
                System.out.println(ce.toString());
                learner.refineHypothesis(ce);
            }

	        // learning statistics
			System.out.println(mqCounter.getCounter().getSummary());
			System.out.println(eqCounter.getCounter().getSummary());

			if(Automata.testEquivalence(learner.getHypothesisModel(), dfa, dfa.getInputAlphabet())){
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
}
