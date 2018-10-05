/* Copyright (C) 2018 Carlos Diego N Damasceno
 */

package br.usp.icmc.labes.mealyInference.utils;

import java.util.ArrayList;
import java.util.Collection;
import java.util.List;
import java.util.Random;

import de.learnlib.api.SUL;
import de.learnlib.api.oracle.EquivalenceOracle.MealyEquivalenceOracle;
import de.learnlib.api.query.DefaultQuery;
import net.automatalib.automata.transout.MealyMachine;
import net.automatalib.automata.transout.impl.compact.CompactMealy;
import net.automatalib.commons.util.collections.CollectionsUtil;
import net.automatalib.util.automata.Automata;
import net.automatalib.util.automata.cover.Covers;
import net.automatalib.words.Word;
import net.automatalib.words.WordBuilder;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

/**
 * This EQ oracle sets two bounds for counterexample search. 
 * (1) the maximum length for a CE is set as five times the number of states in a SUL
 *     if this limit is reached without finding a CE, then the machine is reset, and 
 *     reinitialize the search with a new sequence. 
 * (2) the learning process terminates as soon as the number of states in a hypothesis
 *     becomes equivalent to the SUL. 
 *     
 * @param <I>
 *         input symbol type
 * @param <O>
 *         output symbol type
 *
 * @author damascenodiego
 */


public class RandomWMethodQsizeEQOracle<I, O> implements MealyEquivalenceOracle<I, O> {

    private final Logger LOGGER = LoggerFactory.getLogger(RandomWMethodQsizeEQOracle.class);

    private CompactMealy<String, Word<String>> sul_fsm;
    private Random random;
    private final SUL<I, O> sul;

	private int minimalSize;
	private int rndLength;
	private int bound;

    public RandomWMethodQsizeEQOracle(SUL<I, O> sul,
				              int minimalSize,
				              int rndLength,
				              int bound,
				              CompactMealy<String, Word<String>> fsm,
                              Random random) {
        this.minimalSize = minimalSize;
        this.rndLength = rndLength;
        this.bound = bound;
        this.sul = sul;
        this.sul_fsm = fsm;
        this.random = random;
    }

    public RandomWMethodQsizeEQOracle(SUL<I, O> sul,
            int minimalSize,
            int rndLength,
            int bound,
            CompactMealy<String, Word<String>> fsm) {
    	this(sul, minimalSize, rndLength, bound, fsm, new Random());
    }
    
    @Override
    public DefaultQuery<I, Word<O>> findCounterExample(MealyMachine<?, I, ?, O> hypothesis,
                                                       Collection<? extends I> inputs) {
        return doFindCounterExample(hypothesis, inputs);
    }

    private Word<I> generateSingleTestWord(ArrayList<Word<I>> stateCover,
    		ArrayList<I> arrayAlphabet,
    		ArrayList<Word<I>> globalSuffixes) {
    	final WordBuilder<I> wb = new WordBuilder<>(minimalSize + rndLength + 1);

    	// pick a random state
    	wb.append(stateCover.get(random.nextInt(stateCover.size())));

    	// construct random middle part (of some expected length)
    	int size = minimalSize;
    	while ((size > 0) || (random.nextDouble() > 1 / (rndLength + 1.0))) {
    		wb.append(arrayAlphabet.get(random.nextInt(arrayAlphabet.size())));
    		if (size > 0) {
    			size--;
    		}
    	}

    	// pick a random suffix for this state
    	if (!globalSuffixes.isEmpty()) {
    		wb.append(globalSuffixes.get(random.nextInt(globalSuffixes.size())));
    	}

    	return wb.toWord();
    }
    
    private <S, T> DefaultQuery<I, Word<O>> doFindCounterExample(MealyMachine<S, I, T, O> hypothesis,
                                                                 Collection<? extends I> inputs) {
        if (inputs.isEmpty()) {
            LOGGER.warn("Passed empty set of inputs to equivalence oracle; no counterexample can be found!");
            return null;
        }

        // Note that we want to use ArrayLists because we want constant time random access
        // We will sample from this for a prefix
        ArrayList<Word<I>> stateCover = new ArrayList<>(hypothesis.size());
        Covers.stateCover(hypothesis, inputs, stateCover);

        // Then repeatedly from this for a random word
        ArrayList<I> arrayAlphabet = new ArrayList<>(inputs);

        // Finally we test the state with a suffix
        ArrayList<Word<I>> globalSuffixes = new ArrayList<>();
        Automata.characterizingSet(hypothesis, inputs, globalSuffixes);
        
        


        long steps = 0;

        CompactMealy<String, Word<String>> hyp = (CompactMealy<String, Word<String>>) hypothesis;
        while (!Automata.testEquivalence(sul_fsm, hyp, sul_fsm.getInputAlphabet())) {

        	// break!
        	if ((bound != 0) && (steps == bound)){
        		break;
        	}
        	if (Automata.testEquivalence(sul_fsm, hyp, sul_fsm.getInputAlphabet())){
        		break;
        	}

        	S cur = hypothesis.getInitialState();
        	WordBuilder<I> wbIn = new WordBuilder<>();
        	WordBuilder<O> wbOut_hyp = new WordBuilder<>();
        	WordBuilder<O> wbOut_sul = new WordBuilder<>();

        	// step
        	steps++;
        	Word<I> in = generateSingleTestWord(stateCover, arrayAlphabet, globalSuffixes);
        	O out_symbol;

        	sul.pre();
        	cur = hypothesis.getInitialState();
        	wbIn.clear();
        	wbOut_sul.clear();
        	wbOut_hyp.clear();

        	for (I in_symbol : in) {
        		out_symbol = sul.step(in_symbol);
        		wbOut_sul.add(out_symbol);

        		T hypTrans = hypothesis.getTransition(cur, in_symbol);
        		O outHyp = hypothesis.getTransitionOutput(hypTrans);
        		wbIn.add(in_symbol);
        		wbOut_hyp.add(outHyp);

        		cur = hypothesis.getSuccessor(cur, in_symbol);
        	}
        	sul.post();

        	// ce?
        	if (!wbOut_hyp.equals(wbOut_sul)) {
        		DefaultQuery<I, Word<O>> ce = new DefaultQuery<>(wbIn.toWord());
        		ce.answer(wbOut_sul.toWord());
        		return ce;
        	}

        }
        return null;

        
    }
}
