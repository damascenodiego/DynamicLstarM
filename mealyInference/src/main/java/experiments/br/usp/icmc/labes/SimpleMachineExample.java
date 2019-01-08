package experiments.br.usp.icmc.labes;

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
import de.learnlib.api.oracle.EquivalenceOracle;
import de.learnlib.api.oracle.MembershipOracle;
import de.learnlib.api.query.DefaultQuery;
import de.learnlib.api.statistic.StatisticSUL;
import de.learnlib.datastructure.observationtable.ObservationTable;
import de.learnlib.datastructure.observationtable.writer.ObservationTableASCIIWriter;
import de.learnlib.driver.util.MealySimulatorSUL;
import de.learnlib.filter.cache.sul.SULCache;
import de.learnlib.filter.statistic.sul.ResetCounterSUL;
import de.learnlib.filter.statistic.sul.SymbolCounterSUL;
import de.learnlib.oracle.equivalence.RandomWMethodEQOracle;
import de.learnlib.oracle.membership.SULOracle;
import net.automatalib.automata.transout.MealyMachine;
import net.automatalib.automata.transout.impl.compact.CompactMealy;
import net.automatalib.incremental.mealy.IncrementalMealyBuilder;
import net.automatalib.incremental.mealy.tree.IncrementalMealyTreeBuilder;
import net.automatalib.serialization.dot.GraphDOT;
import net.automatalib.util.automata.Automata;
import net.automatalib.words.Word;

public class SimpleMachineExample {

	public static void main(String[] args) {
		
		try {
			// set SUL path
			File sul 	 = null;
			File ot_file = null;
			
			boolean projection = false;
			String ce_str="switchIntv rain rain rain";
//			String ce_str="switchIntv switchIntv rain rain";
			sul		= new File("./experiments_swipeMachine/wipeSystem_perm.txt");	// case 1
			sul		= new File("./experiments_swipeMachine/wipeSystem_basic.txt");	// case 2
//			sul		= new File("./experiments_swipeMachine/wipeSystem_basic_bkp.txt"); ot_file = new File("./experiments_swipeMachine/wipeSystem_perm.txt.ot");
//			sul		= new File("./experiments_swipeMachine/wipeSystem_perm_bkp.txt"); ot_file = new File("./experiments_swipeMachine/wipeSystem_basic.txt.ot");
			sul		= new File("./experiments_swipeMachine/wipeSystem_perm_bkp.txt"); ot_file = new File("./experiments_swipeMachine/pwset.ot");
			
			File log_file = new File(sul.getAbsolutePath()+".log");
			BufferedWriter bw = new BufferedWriter(new FileWriter(log_file));
						
			// load mealy machine
			CompactMealy<String, Word<String>> mealyss = Utils.getInstance().loadMealyMachine(sul);
			GraphDOT.write(mealyss, mealyss.getInputAlphabet(), new FileWriter(new File(sul.getAbsolutePath().replaceFirst(".txt$", ".dot"))));
			
			// set closing strategy
			ClosingStrategy strategy 			= ClosingStrategies.CLOSE_FIRST;

			// set CE processing approach
			ObservationTableCEXHandler handler 	= ObservationTableCEXHandlers.RIVEST_SCHAPIRE;
			
			// Empty list of prefixes 
			List<Word<String>> initPrefixes = new ArrayList<Word<String>>();
			initPrefixes.add(Word.epsilon());
						
			// Empty list of suffixes => minimal compliant setinitCes
			List<Word<String>> initSuffixes = new ArrayList<Word<String>>();
			for (String word : mealyss.getInputAlphabet()) {
				Word w = Word.epsilon();
				w=w.append(word);
				initSuffixes.add(w);
			}
			

			Utils.getInstance();
			// SUL simulator
			SUL<String,Word<String>> sulSim = new MealySimulatorSUL(mealyss, Utils.OMEGA_SYMBOL);
						
			// IncrementalMealyBuilder for caching EQs and MQs together
			IncrementalMealyBuilder<String,Word<String>> cbuilder = new IncrementalMealyTreeBuilder<>(mealyss.getInputAlphabet());			

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
			
			if(ot_file!=null){
				MyObservationTable myot = OTUtils.getInstance().readOT(ot_file,mealyss.getInputAlphabet(),projection);
				ObservationTable<String, Word<Word<String>>> reval_ot = OTUtils.getInstance().revalidateObservationTable(myot, oracleForLearner,mealyss);
				new ObservationTableASCIIWriter<>().write(reval_ot, bw);
				initSuffixes.clear(); initSuffixes.addAll(myot.getSuffixes());
				initPrefixes.clear(); initPrefixes.addAll(myot.getPrefixes());
				// learning statistics
				bw.write(mq_rst.getStatisticalData().toString());bw.write("\n");
				bw.write(mq_sym.getStatisticalData().toString());bw.write("\n");
				bw.write(eq_rst.getStatisticalData().toString());bw.write("\n");
				bw.write(eq_sym.getStatisticalData().toString());bw.write("\n");
			}
			
						
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
			new ObservationTableASCIIWriter<>().write(learner.getObservationTable(), bw);
			GraphDOT.write(learner.getHypothesisModel(), learner.getHypothesisModel().getInputAlphabet(), new FileWriter(new File(sul.getAbsolutePath().replaceFirst(".txt$", "_1.dot"))));
			// learning statistics
			bw.write(mq_rst.getStatisticalData().toString());bw.write("\n");
			bw.write(mq_sym.getStatisticalData().toString());bw.write("\n");
			bw.write(eq_rst.getStatisticalData().toString());bw.write("\n");
			bw.write(eq_sym.getStatisticalData().toString());bw.write("\n");
	
			//EquivalenceOracle<MealyMachine<?, String, ?, Word<String>>, String, Word<Word<String>>> eqOracle = null;
			//Random seed = new Random(); 
			//eqOracle = new IrfanEQOracle<>(eq_sul, mealyss.getStates().size(), seed);
			//eqOracle = new WpMethodEQOracle<>(oracleForEQoracle, 2);
			//eqOracle = new RandomWordsEQOracle(oracleForEQoracle, 10, 10, 100, seed);
			
			//Word<String> sep_word = Automata.findSeparatingWord(mealyss, learner.getHypothesisModel(), mealyss.getInputAlphabet());
			//DefaultQuery<String,Word<Word<String>>> ce = eqOracle.findCounterExample(learner.getHypothesisModel(), learner.getHypothesisModel().getInputAlphabet());
			//seed.setSeed(123);
			//ce = eqOracle.findCounterExample(learner.getHypothesisModel(), learner.getHypothesisModel().getInputAlphabet());
			//DefaultQuery<String,Word<Word<String>>> ce =  new DefaultQuery<>(sep_word);
			
			if(ot_file==null){
				DefaultQuery<String,Word<Word<String>>> ce = null;
				Word<String> ce_word = Word.epsilon();
				for (String string : ce_str.split(" ")) {
					if(!mealyss.getInputAlphabet().contains(string)) {
						if(projection){
							continue;
						}else{
							break;
						}
					}
					ce_word=ce_word.append(string);	
				}
				ce =  new DefaultQuery<>(ce_word);
				oracleForEQoracle.processQuery(ce);
				
				// Equivalence Query Oracle
				EquivalenceOracle<MealyMachine<?, String, ?, Word<String>>, String, Word<Word<String>>> eqOracle = null;
				eqOracle = new RandomWMethodEQOracle<>(oracleForEQoracle, 0, 1, 100);
//				ce=eqOracle.findCounterExample(learner.getHypothesisModel(), mealyss.getInputAlphabet());
				System.out.println(ce);
				if(ce != null){
					learner.refineHypothesis(ce);
					bw.write(ce.toString());
					bw.write("\n");
				}
					
				new ObservationTableASCIIWriter<>().write(learner.getObservationTable(), bw);
				GraphDOT.write(learner.getHypothesisModel(), learner.getHypothesisModel().getInputAlphabet(), new FileWriter(new File(sul.getAbsolutePath().replaceFirst(".txt$", "_2.dot"))));
				
				// learning statistics
				bw.write(mq_rst.getStatisticalData().toString());bw.write("\n");
				bw.write(mq_sym.getStatisticalData().toString());bw.write("\n");
				bw.write(eq_rst.getStatisticalData().toString());bw.write("\n");
				bw.write(eq_sym.getStatisticalData().toString());bw.write("\n");
			}
			

			System.out.println("W set:\t"+Automata.characterizingSet(mealyss, mealyss.getInputAlphabet()));

			if(Automata.testEquivalence(learner.getHypothesisModel(), mealyss, mealyss.getInputAlphabet())){
				bw.write("Equivalent!!!\n");
			}else{
				bw.write("Non Equivalent!!!\n");
			}

			bw.close();
			File sul_ot = new File(sul.getAbsolutePath()+".ot");
			OTUtils.getInstance().writeOT(learner.getObservationTable(), sul_ot);
			
		} catch (Exception e) {
			e.printStackTrace();
		}
	}
}
