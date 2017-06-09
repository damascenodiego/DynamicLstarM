/**
 * 
 */
package br.usp.icmc.labes.mealyInference;

import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.io.Writer;
import java.util.ArrayList;
import java.util.Collections;
import java.util.List;
import java.util.Random;

import de.learnlib.algorithms.dhc.mealy.MealyDHC;
import de.learnlib.algorithms.lstargeneric.ce.ObservationTableCEXHandler;
import de.learnlib.algorithms.lstargeneric.ce.ObservationTableCEXHandlers;
import de.learnlib.algorithms.lstargeneric.closing.ClosingStrategies;
import de.learnlib.algorithms.lstargeneric.closing.ClosingStrategy;
import de.learnlib.algorithms.lstargeneric.mealy.ClassicLStarMealy;
import de.learnlib.algorithms.lstargeneric.mealy.ExtensibleLStarMealy;
import de.learnlib.api.EquivalenceOracle;
import de.learnlib.api.LearningAlgorithm;
import de.learnlib.api.MembershipOracle;
import de.learnlib.api.MembershipOracle.MealyMembershipOracle;
import de.learnlib.cache.mealy.MealyCacheOracle;
import de.learnlib.eqtests.basic.SimulatorEQOracle;
import de.learnlib.eqtests.basic.mealy.RandomWalkEQOracle;
import de.learnlib.eqtests.basic.mealy.SymbolEQOracleWrapper;
import de.learnlib.examples.mealy.ExampleCoffeeMachine;
import de.learnlib.examples.mealy.ExampleStack;
import de.learnlib.examples.mealy.ExampleCoffeeMachine.Input;
import de.learnlib.mealy.MealyUtil;
import de.learnlib.oracles.DefaultQuery;
import de.learnlib.oracles.SimulatorOracle;
import de.learnlib.oracles.SimulatorOracle.MealySimulatorOracle;
import de.learnlib.simulator.sul.MealySimulatorSUL;
import net.automatalib.automata.transout.MealyMachine;
import net.automatalib.automata.transout.impl.compact.CompactMealy;
import net.automatalib.commons.dotutil.DOT;
import net.automatalib.graphs.concepts.GraphViewable;
import net.automatalib.util.automata.builders.AutomatonBuilders;
import net.automatalib.util.graphs.dot.GraphDOT;
import net.automatalib.words.Alphabet;
import net.automatalib.words.Word;
import net.automatalib.words.impl.Alphabets;

/**
 * @author damasceno
 *
 */
public class Example {

	public static void main(String[] args) throws Exception {

		
		List<Character> abc = new ArrayList<>();
		abc.add('a'); 	abc.add('b');
		
		Alphabet<Character> alphabet = Alphabets.fromCollection(abc);
		
		CompactMealy<Character, Integer> mealym = new CompactMealy<Character, Integer>(alphabet);
		
		CompactMealy<Character, Integer> machine = AutomatonBuilders.forMealy(mealym)
				.withInitial("q0")
				.from("q0")
					.on('a').withOutput(0).to("q0")
					.on('b').withOutput(1).to("q1")
				.from("q1")
					.on('a').withOutput(0).to("q0")
					.on('b').withOutput(1).to("q2")
				.from("q2")
					.on('a').withOutput(2).to("q1")
					.on('b').withOutput(1).to("q2")
				.create();
/*		
		CompactMealy<Character, Integer> machine2 = new CompactMealy<Character, Integer>(alphabet); 
		//CompactMealy<Character, Integer> machine2 = AutomatonBuilders.newMealy(alphabet).withInitial("q0").create();
		
		Integer q0 = machine2.addState();
		Integer q1 = machine2.addState();
		Integer q2 = machine2.addState();
		
		machine2.setInitialState(q0);
		
		machine2.addTransition(q0, 'a', q0, 0);
		machine2.addTransition(q0, 'b', q1, 1);
		
		machine2.addTransition(q1, 'a', q0, 0);
		machine2.addTransition(q1, 'b', q2, 1);
		
		machine2.addTransition(q2, 'a', q1, 2);
		machine2.addTransition(q2, 'b', q2, 1);
		
		System.out.println(machine.equals(machine2));
		
		for(Integer i : machine.getStates()){
			System.out.println(i);
		}
			
		Writer w = DOT.createDotWriter(true);
        GraphDOT.write(machine,alphabet,  w);
        w.close();
*/

//		testdhc(machine);
		testlstar(machine);

	}
	
	private static void testlstar(CompactMealy<Character, Integer> machine) throws IOException {

		for(ObservationTableCEXHandler<? super Character,? super Integer> handler : ObservationTableCEXHandlers.values()) {
			for(ClosingStrategy<? super Character,? super Integer> strategy : ClosingStrategies.values()) {
				

				File fout = new File("out_machine.dot");
				FileWriter fwout = new FileWriter(fout); 
				GraphDOT.write((GraphViewable) machine,fwout);
				fwout.close();
				
				MembershipOracle<Character,Word<Integer>> oracle = new SimulatorOracle<>(machine);

				// Empty list of suffixes => minimal compliant set
				List<Word<Character>> initSuffixes = Collections.emptyList();
			
				EquivalenceOracle<? super MealyMachine<?,Character,?,Integer>, Character, Integer> mealySymEqOracle 
//				= new SymbolEQOracleWrapper<>(new SimulatorEQOracle<>(machine));
				= new RandomWalkEQOracle(
						0.05, // reset SUL w/ this probability before a step 
						10000, // max steps (overall)
						false, // reset step count after counterexample 
						new Random(46346293), // make results reproducible 
						new MealySimulatorSUL<>(machine) // system under learning
						);
				
				LearningAlgorithm<MealyMachine<?,Character,?,Integer>,Character,Word<Integer>> learner
						= new ExtensibleLStarMealy(machine.getInputAlphabet(), oracle, initSuffixes,handler, strategy);
				
				DefaultQuery counterexample = null;
				do {
					if (counterexample == null) {
						learner.startLearning();
					} else {
						boolean refined = learner.refineHypothesis(counterexample);
						if(!refined) System.err.println("No refinement effected by counterexample!");
					}

					counterexample = mealySymEqOracle.findCounterExample(learner.getHypothesisModel() , machine.getInputAlphabet());

					learner.getHypothesisModel();
//					fout = new File("out_ClassicLStarMealy"+(count++)+".dot");
//					fwout = new FileWriter(fout); 
//					GraphDOT.write((GraphViewable) learner.getHypothesisModel(),fwout);
//					fwout.close();

				} while (counterexample != null);

				// from here on learner.getHypothesisModel() will provide an accurate model

				if(learner.getHypothesisModel().size() != machine.size()){
					System.err.println("Error!!! :O");	
				}
				
				fout = new File("out_"+handler.toString()+"_"+strategy.toString()+".dot");
				fwout = new FileWriter(fout); 
				GraphDOT.write((GraphViewable) learner.getHypothesisModel(),fwout);
				fwout.close();
				
			}
		}
	}

	public static void testdhc(CompactMealy<Character, Integer> machine) throws IOException{


		CompactMealy<Input, String> fm = ExampleCoffeeMachine.constructMachine();
		Alphabet<Input> alphabet = fm.getInputAlphabet();

		SimulatorOracle<Input, Word<String>> simoracle = new SimulatorOracle<>(fm);
		SimulatorEQOracle<Input, Word<String>> eqoracle = new SimulatorEQOracle<>(fm);

		MembershipOracle<Input,Word<String>> cache = new MealyCacheOracle<>(alphabet, null, simoracle);
		MealyDHC<Input, String> learner = new MealyDHC<>(alphabet, cache);
		
		int count = 0 ;
		File fout;
		FileWriter fwout;
		
        fout = new File("out_MealyDHC"+(count++)+".dot");
        fwout = new FileWriter(fout); 
        GraphDOT.write(fm,fwout);
        fwout.close();

		
		DefaultQuery<Input, Word<String>> counterexample = null;
		do {
			if (counterexample == null) {
				learner.startLearning();
			} else {
				boolean refined = learner.refineHypothesis(counterexample);
				if(!refined) System.err.println("No refinement effected by counterexample!");
			}

			counterexample = eqoracle.findCounterExample(learner.getHypothesisModel(), alphabet);

			learner.getHypothesisModel();
			fout = new File("out_MealyDHC"+(count++)+".dot");
	        fwout = new FileWriter(fout); 
	        GraphDOT.write(learner.getHypothesisModel(),fwout);
	        fwout.close();
	        
		} while (counterexample != null);

		// from here on learner.getHypothesisModel() will provide an accurate model

		fout = new File("out_MealyDHC"+(count++)+".dot");
        fwout = new FileWriter(fout); 
        GraphDOT.write(learner.getHypothesisModel(),fwout);
        fwout.close();
        

	}
}
