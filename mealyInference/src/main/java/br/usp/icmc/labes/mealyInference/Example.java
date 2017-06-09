/**
 * 
 */
package br.usp.icmc.labes.mealyInference;

import java.io.Writer;
import java.util.ArrayList;
import java.util.List;

import net.automatalib.automata.transout.impl.compact.CompactMealy;
import net.automatalib.commons.dotutil.DOT;
import net.automatalib.util.automata.builders.AutomatonBuilders;
import net.automatalib.util.graphs.dot.GraphDOT;
import net.automatalib.words.Alphabet;
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
		for(Integer i : machine.getStates()){
			System.out.println(i);
		}
			
		Writer w = DOT.createDotWriter(true);
        GraphDOT.write(machine,alphabet,  w);
        w.close();
        
	}
}
