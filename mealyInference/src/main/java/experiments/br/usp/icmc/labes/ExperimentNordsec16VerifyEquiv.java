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
import de.learnlib.api.statistic.StatisticSUL;
import de.learnlib.datastructure.observationtable.ObservationTable;
import de.learnlib.datastructure.observationtable.writer.ObservationTableASCIIWriter;
import de.learnlib.driver.util.MealySimulatorSUL;
import de.learnlib.filter.cache.sul.SULCache;
import de.learnlib.filter.statistic.Counter;
import de.learnlib.filter.statistic.sul.ResetCounterSUL;
import de.learnlib.filter.statistic.sul.SymbolCounterSUL;
import de.learnlib.oracle.equivalence.RandomWMethodEQOracle;
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

public class ExperimentNordsec16VerifyEquiv {

	static BufferedWriter bw_comparison;

	static final int REPETITIONS = 1000;
	
	public static void main(String[] args) {
		
		
		try{
				
			bw_comparison = new BufferedWriter(new FileWriter(new File(new File(ExperimentNordsec16Utils.getInstance().getVersions()[0]).getParentFile(),"equivTesting_client.tab")));
			bw_comparison.write("Equivalent\tSUL\tPrevious\n");
			
			for (int i = 0; i < ExperimentNordsec16Utils.getInstance().getVersions().length; i++) {
				for (int j = 0; j < i; j++) { if (i==j) continue;

				File file_i = new File(ExperimentNordsec16Utils.getInstance().getVersions()[i]);
				CompactMealy<String, Word<String>> model_i = Utils.getInstance().loadMealyMachineFromDot(file_i);
				SUL<String,Word<String>> sul_i = new MealySimulatorSUL(model_i, Utils.OMEGA_SYMBOL);
				
				File file_j = new File(ExperimentNordsec16Utils.getInstance().getVersions()[j]);
				CompactMealy<String, Word<String>> model_j = Utils.getInstance().loadMealyMachineFromDot(file_j);
				SUL<String,Word<String>> sul_j = new MealySimulatorSUL(model_j, Utils.OMEGA_SYMBOL);

				boolean success = Automata.testEquivalence(model_i, model_j, model_i.getInputAlphabet());
				bw_comparison.append(Boolean.toString(success));
				bw_comparison.append("\t");
				bw_comparison.append(file_i.getName());
				bw_comparison.append("\t");
				bw_comparison.append(file_j.getName());
				
				bw_comparison.append("\n");
				}
			}

			bw_comparison.close();
		} catch (Exception e) {
			e.printStackTrace();
		}
	}
	
	private static void generate_OTsFromWset() throws Exception {

		for (int i = 0; i < ExperimentNordsec16Utils.getInstance().getVersions().length; i++) {

			File file = new File(ExperimentNordsec16Utils.getInstance().getVersions()[i]);
			// create out_dir
			File out_dir = new File(file.getParent(),file.getName().replaceFirst(".dot$", "")); out_dir.mkdirs();

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
				File sul_ot = new File(out_dir,file.getName()+".reuse");
				OTUtils.getInstance().writeOT(learner.getObservationTable(), sul_ot);
			}
		}
		//		bw_comparison.close();

	}

	private static void run_LStarM(boolean log,boolean saveOut) throws Exception{
		//bw_comparison = new BufferedWriter(new FileWriter(new File(new File(ExperimentNordsec16Utils.getInstance().getVersions()[0]).getParentFile(),ExperimentNordsec16Utils.getInstance().getTab_filename())));
		//bw_comparison.write("Inferred\tReused\tMQ_Reset_Reval\tEQ_Reset_Reval\tMQ_Reset\tEQ_Reset\tRounds\tSuccess\n");


		for (int i = 0; i < ExperimentNordsec16Utils.getInstance().getVersions().length; i++) {
			for (int j = 0; j < i; j++) { if (i==j) continue;

			File file = new File(ExperimentNordsec16Utils.getInstance().getVersions()[i]);
			// create out_dir
			File out_dir = new File(file.getParent(),file.getName().replaceFirst(".dot$", "")); out_dir.mkdirs();

			// load mealy machine
			CompactMealy<String, Word<String>> mealyss = Utils.getInstance().loadMealyMachineFromDot(file);

			// SUL simulator
			SUL<String,Word<String>> sulSim = new MealySimulatorSUL(mealyss, Utils.OMEGA_SYMBOL);

			// SUL alphabet
			Alphabet<String> alphabet = mealyss.getInputAlphabet();

			// Empty list of prefixes 
			List<Word<String>> initPrefixes = new ArrayList<Word<String>>();
			initPrefixes.add(Word.epsilon());

			// Empty list of suffixes => minimal compliant setinitCes
			List<Word<String>> initSuffixes = new ArrayList<Word<String>>();

			// set closing strategy
			ClosingStrategy strategy 			= ClosingStrategies.CLOSE_FIRST;

			// set CE processing approach
			ObservationTableCEXHandler handler 	= ObservationTableCEXHandlers.RIVEST_SCHAPIRE;

			// IncrementalMealyBuilder for caching EQs and MQs together
			IncrementalMealyBuilder<String,Word<String>> cbuilder = new IncrementalMealyTreeBuilder<>(alphabet);			

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

			long reval_eq = ((Counter)eq_rst.getStatisticalData()).getCount();
			long reval_mq = ((Counter)mq_rst.getStatisticalData()).getCount();
			

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
			//eqOracle = new WpMethodEQOracle<>(oracleForEQoracle, 2);
			//eqOracle = new IrfanEQOracle(eq_sul, mealyss.getStates().size());
			//((IrfanEQOracle)eqOracle).set_maxResets(10000);
			//((IrfanEQOracle)eqOracle).set_maxLength(10);
			eqOracle = new RandomWMethodEQOracle<>(oracleForEQoracle, 17, 17, 1700);


			// The experiment will execute the main loop of active learning
			MealyExperiment<String, Word<String>> experiment = new MealyExperiment<String, Word<String>> (learner, eqOracle, alphabet);
			// turn on time profiling
			experiment.setProfile(true);
			// enable logging of models
			experiment.setLogModels(true);
			// run experiment
			experiment.run();

			if(saveOut){
				// learning statistics
				BufferedWriter bw = new BufferedWriter(new FileWriter(new File(out_dir,file.getName()+".ot")));
				bw.write(mq_rst.getStatisticalData().toString());bw.write("\n");
				bw.write(mq_sym.getStatisticalData().toString());bw.write("\n");
				bw.write(eq_rst.getStatisticalData().toString());bw.write("\n");
				bw.write(eq_sym.getStatisticalData().toString());bw.write("\n");
				bw.write(experiment.getRounds().toString());bw.write("\n");
				bw.write("States: "+experiment.getFinalHypothesis().getStates().size());bw.write("\n");

				new ObservationTableASCIIWriter<>().write(learner.getObservationTable(), bw);
				bw.close();
				//				GraphDOT.write(learner.getHypothesisModel(), learner.getHypothesisModel().getInputAlphabet(), System.out);
				File sul_ot = new File(out_dir,file.getName()+".reuse");
				OTUtils.getInstance().writeOT(learner.getObservationTable(), sul_ot);
				bw.close();
			}
			if(log){
				bw_comparison.write(file.getName().replaceFirst(".dot$", "")+"\t"+"N/A"+"\t"+reval_mq+"\t"+reval_eq);
				bw_comparison.write("\t"+((Counter)mq_rst.getStatisticalData()).getCount()+"\t"+((Counter)eq_rst.getStatisticalData()).getCount());
				bw_comparison.write("\t"+experiment.getRounds().getCount());
				bw_comparison.write("\t"+mealyss.getStates().size());
				bw_comparison.write("\t"+mealyss.getInputAlphabet().size());
				boolean success = Automata.testEquivalence(mealyss, learner.getHypothesisModel(), mealyss.getInputAlphabet());
				bw_comparison.write("\t"+((success)?"OK":"NOK"));
				bw_comparison.write("\n");
//				if(!success) j--;
			}
			}
		}
		//		bw_comparison.close();
	}
	private static void run_DynamicLStarM() throws Exception{
//		bw_comparison = new BufferedWriter(new FileWriter(new File(new File(ExperimentNordsec16Utils.getInstance().getVersions()[0]).getParentFile(),ExperimentNordsec16Utils.getInstance().getTab_filename()),true));
		
	for (int i = 0; i < ExperimentNordsec16Utils.getInstance().getVersions().length; i++) {
		for (int j = 0; j < i; j++) { if (i==j) continue;
			

			File file_i = new File(ExperimentNordsec16Utils.getInstance().getVersions()[i]);
			
			// create out_dir
			File out_dir = new File(file_i.getParent(),file_i.getName().replaceFirst(".dot$", "")); out_dir.mkdirs();
			
			// load mealy machine
			CompactMealy<String, Word<String>> mealyss = Utils.getInstance().loadMealyMachineFromDot(file_i);

			// SUL simulator
			SUL<String,Word<String>> sulSim = new MealySimulatorSUL(mealyss, Utils.OMEGA_SYMBOL);
			
			// SUL alphabet
			Alphabet<String> alphabet = mealyss.getInputAlphabet();

			// Empty list of prefixes 
			List<Word<String>> initPrefixes = new ArrayList<Word<String>>();
			initPrefixes.add(Word.epsilon());

			// Empty list of suffixes => minimal compliant setinitCes
			List<Word<String>> initSuffixes = new ArrayList<Word<String>>();

			// set closing strategy
			ClosingStrategy strategy 			= ClosingStrategies.CLOSE_FIRST;

			// set CE processing approach
			ObservationTableCEXHandler handler 	= ObservationTableCEXHandlers.RIVEST_SCHAPIRE;

			// IncrementalMealyBuilder for caching EQs and MQs together
			IncrementalMealyBuilder<String,Word<String>> cbuilder = new IncrementalMealyTreeBuilder<>(alphabet);			

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

			//						Word<String> word = Word.epsilon();
			//						for (String s_word : alphabet) {
			//							word = Word.epsilon();
			//							word=word.append(s_word);
			//							initSuffixes.add(word);
			//						}
			
			File file_j = new File(ExperimentNordsec16Utils.getInstance().getVersions()[j]); 
			File ot_file = new File(new File(out_dir.getParent(),file_j.getName().replaceFirst(".dot$", "")),file_j.getName()+".reuse");

			// learning statistics
			BufferedWriter bw = new BufferedWriter(new FileWriter(new File(out_dir,file_i.getName()+(ot_file!=null?ot_file.getName():"")+".ot")));

			if(ot_file!=null){
				MyObservationTable myot = OTUtils.getInstance().readOT(ot_file,alphabet,false);
				ObservationTable<String, Word<Word<String>>> reval_ot = OTUtils.getInstance().revalidateObservationTable(myot, oracleForLearner,mealyss);
				initSuffixes.clear(); initSuffixes.addAll(myot.getSuffixes());
				initPrefixes.clear(); initPrefixes.addAll(myot.getPrefixes());
				bw.write("Revalidation\n");
				bw.write(mq_rst.getStatisticalData().toString());bw.write("\n");
				bw.write(mq_sym.getStatisticalData().toString());bw.write("\n");
				bw.write(eq_rst.getStatisticalData().toString());bw.write("\n");
				bw.write(eq_sym.getStatisticalData().toString());bw.write("\n");
				bw.write("|S|_reval: "+reval_ot.numberOfDistinctRows());bw.write("\n");
			}
			
			bw_comparison.write(file_i.getName().replaceFirst(".dot$", "")+"\t"+file_j.getName().replaceFirst(".dot$", "")+"\t"+((Counter)mq_rst.getStatisticalData()).getCount()+"\t"+((Counter)eq_rst.getStatisticalData()).getCount());

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
			//eqOracle = new WpMethodEQOracle<>(oracleForEQoracle, 2);
			//eqOracle = new IrfanEQOracle(eq_sul, mealyss.getStates().size());
			//((IrfanEQOracle)eqOracle).set_maxResets(10000);
			//((IrfanEQOracle)eqOracle).set_maxLength(10);
			eqOracle = new RandomWMethodEQOracle<>(oracleForEQoracle, 17, 17, 1700);

			
			// The experiment will execute the main loop of active learning
			MealyExperiment<String, Word<String>> experiment = new MealyExperiment<String, Word<String>> (learner, eqOracle, alphabet);
			// turn on time profiling
			experiment.setProfile(true);
			// enable logging of models
			experiment.setLogModels(true);
			// run experiment
			experiment.run();

			
			bw.write("Final OT\n");
			bw.write(mq_rst.getStatisticalData().toString());bw.write("\n");
			bw.write(mq_sym.getStatisticalData().toString());bw.write("\n");
			bw.write(eq_rst.getStatisticalData().toString());bw.write("\n");
			bw.write(eq_sym.getStatisticalData().toString());bw.write("\n");
			bw.write(experiment.getRounds().toString());bw.write("\n");
			bw.write("States: "+experiment.getFinalHypothesis().getStates().size());bw.write("\n");

			new ObservationTableASCIIWriter<>().write(learner.getObservationTable(), bw);
			bw.close();
			//				GraphDOT.write(learner.getHypothesisModel(), learner.getHypothesisModel().getInputAlphabet(), System.out);
			File sul_ot = new File(out_dir,file_i.getName()+(ot_file!=null?ot_file.getName():"")+".reuse");
			OTUtils.getInstance().writeOT(learner.getObservationTable(), sul_ot);
			bw.close();
			bw_comparison.write("\t"+((Counter)mq_rst.getStatisticalData()).getCount()+"\t"+((Counter)eq_rst.getStatisticalData()).getCount());
			bw_comparison.write("\t"+experiment.getRounds().getCount());
			bw_comparison.write("\t"+mealyss.getStates().size());
			bw_comparison.write("\t"+mealyss.getInputAlphabet().size());
			boolean success = Automata.testEquivalence(mealyss, learner.getHypothesisModel(), mealyss.getInputAlphabet());
			bw_comparison.write("\t"+((success)?"OK":"NOK"));
			bw_comparison.write("\n");
//			if(!success) j--;
		}
	}
//	bw_comparison.close();

	}
}
