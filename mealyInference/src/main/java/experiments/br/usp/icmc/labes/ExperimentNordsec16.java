package experiments.br.usp.icmc.labes;

import java.io.BufferedWriter;
import java.io.File;
import java.io.FileWriter;
import java.text.SimpleDateFormat;
import java.util.ArrayList;
import java.util.List;

import br.usp.icmc.labes.mealyInference.utils.MyObservationTable;
import br.usp.icmc.labes.mealyInference.utils.OTUtils;
import br.usp.icmc.labes.mealyInference.utils.RandomWMethodQsizeEQOracle;
import br.usp.icmc.labes.mealyInference.utils.Utils;
import de.learnlib.algorithms.dlstar.mealy.ExtensibleDLStarMealy;
import de.learnlib.algorithms.dlstar.mealy.ExtensibleDLStarMealyBuilder;
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

public class ExperimentNordsec16 {

	static BufferedWriter bw_comparison;

//	static final int REPETITIONS = 100000;
	public static int REPETITIONS = 10;
	
	protected static final SimpleDateFormat sdf = new SimpleDateFormat("yyyy_MM_dd_HH_mm_ss_SSS");
	protected static final long tstamp = System.currentTimeMillis();

	
	public static void main(String[] args) {
		
		if (args.length>0) {
			REPETITIONS = Integer.valueOf(args[0]);
		}
		
		
		try{
			ExperimentNordsec16Utils.getInstance().nordsec16_client_rlzdate();
			
			bw_comparison = new BufferedWriter(new FileWriter(new File(new File(ExperimentNordsec16Utils.getInstance().getVersions()[0]).getParentFile(),
					ExperimentNordsec16Utils.getInstance().getTab_filename().replaceAll("\\.tab$", sdf.format(tstamp)+".tab"))));
			bw_comparison.write("Method\tInferred\tReused\tMQ_Reset_Reval\tEQ_Reset_Reval\tMQ_Reset\tEQ_Reset\tMQ_Symbol\tEQ_Symbol\tRounds\tQsize\tIsize\tSuccess\n");

			for (int i = 0; i < REPETITIONS; i++) {
				run_fl_LStarM(true,false);
			}
			//generate_OTsFromWset();
			for (int i = 0; i < REPETITIONS; i++) {
				run_fl_DynamicLStarM();
			}
			
			for (int i = 0; i < REPETITIONS; i++) {
				run_fl_IncrMQs_DynamicLStarM();
			}			
			
			bw_comparison.close();

			
			ExperimentNordsec16Utils.getInstance().nordsec16_server_rlzdate();
			
			bw_comparison = new BufferedWriter(new FileWriter(new File(new File(ExperimentNordsec16Utils.getInstance().getVersions()[0]).getParentFile(),
					ExperimentNordsec16Utils.getInstance().getTab_filename().replaceAll("\\.tab$", sdf.format(tstamp)+".tab"))));
			bw_comparison.write("Method\tInferred\tReused\tMQ_Reset_Reval\tEQ_Reset_Reval\tMQ_Reset\tEQ_Reset\tMQ_Symbol\tEQ_Symbol\tRounds\tQsize\tIsize\tSuccess\n");

			for (int i = 0; i < REPETITIONS; i++) {
				run_fl_LStarM(true,false);
			}
			//generate_OTsFromWset();
			for (int i = 0; i < REPETITIONS; i++) {
				run_fl_DynamicLStarM();
			}
			
			for (int i = 0; i < REPETITIONS; i++) {
				run_fl_IncrMQs_DynamicLStarM();
			}			
			

			bw_comparison.close();
} catch (Exception e) {
			e.printStackTrace();
		}
	}
	
	private static void run_fl_LStarM(boolean log,boolean saveOut) throws Exception{
			//bw_comparison = new BufferedWriter(new FileWriter(new File(new File(ExperimentNordsec16Utils.getInstance().getVersions()[0]).getParentFile(),ExperimentNordsec16Utils.getInstance().getTab_filename())));
			//bw_comparison.write("Inferred\tReused\tMQ_Reset_Reval\tEQ_Reset_Reval\tMQ_Reset\tEQ_Reset\tRounds\tSuccess\n");
	
	
		for (int i = 1; i < ExperimentNordsec16Utils.getInstance().getVersions().length; i++) {
//			int [] vals = {0,i-1};
//			for (int j : vals) 
			{ 
	
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
				MembershipOracle<String,Word<Word<String>>> oracleForLearner  = new SULOracle<>(mq_sul);
				MembershipOracle<String,Word<Word<String>>> oracleForEQoracle = new SULOracle<>(eq_sul);
	
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
//				eqOracle = new IrfanEQOracle(eq_sul, mealyss.getStates().size());
//				((IrfanEQOracle)eqOracle).set_maxResets(1700);
//				((IrfanEQOracle)eqOracle).set_maxLength(1700);
//				eqOracle = new RandomWMethodEQOracle<>(oracleForEQoracle, 17, 17, 1700);
//				eqOracle = new RandomWMethodQsizeEQOracle<>(eq_sul, 17, 17, 1700, mealyss.getStates().size());
				//eqOracle = new RandomWMethodQsizeEQOracle<>(eq_sul, 1, 2, 0, mealyss);
				eqOracle = new RandomWMethodQsizeEQOracle<>(eq_sul, 1, 100, 0, mealyss);
	
	
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
					bw_comparison.write("LStarM\t");
					bw_comparison.write(file.getName().replaceFirst(".dot$", "")+"\t"+"N/A"+"\t"+reval_mq+"\t"+reval_eq);
					bw_comparison.write("\t"+((Counter)mq_rst.getStatisticalData()).getCount()+"\t"+((Counter)eq_rst.getStatisticalData()).getCount());
					bw_comparison.write("\t"+((Counter)mq_sym.getStatisticalData()).getCount()+"\t"+((Counter)eq_sym.getStatisticalData()).getCount());
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

	private static void run_fl_DynamicLStarM() throws Exception{
	//		bw_comparison = new BufferedWriter(new FileWriter(new File(new File(ExperimentNordsec16Utils.getInstance().getVersions()[0]).getParentFile(),ExperimentNordsec16Utils.getInstance().getTab_filename()),true));
			
		for (int i = 1; i < ExperimentNordsec16Utils.getInstance().getVersions().length; i++) {
			int [] vals = {0,i-1};
			for (int j : vals) { 
	
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
				MembershipOracle<String,Word<Word<String>>> oracleForLearner  = new SULOracle<>(mq_sul);
				MembershipOracle<String,Word<Word<String>>> oracleForEQoracle = new SULOracle<>(eq_sul);
	
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
					ObservationTable<String, Word<Word<String>>> reval_ot = OTUtils.getInstance().revalidateObservationTable(myot, oracleForLearner,sulSim,alphabet);
					initSuffixes.clear(); initSuffixes.addAll(myot.getSuffixes());
					initPrefixes.clear(); initPrefixes.addAll(myot.getPrefixes());
					bw.write("Revalidation\n");
					bw.write(mq_rst.getStatisticalData().toString());bw.write("\n");
					bw.write(mq_sym.getStatisticalData().toString());bw.write("\n");
					bw.write(eq_rst.getStatisticalData().toString());bw.write("\n");
					bw.write(eq_sym.getStatisticalData().toString());bw.write("\n");
					bw.write("|S|_reval: "+reval_ot.numberOfDistinctRows());bw.write("\n");
				}
				//bw_comparison.write("DLStarM\t");
				bw_comparison.write("DL*M_v1\t");
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
//				eqOracle = new IrfanEQOracle(eq_sul, mealyss.getStates().size());
//				((IrfanEQOracle)eqOracle).set_maxResets(1700);
//				((IrfanEQOracle)eqOracle).set_maxLength(17uname00);
//				eqOracle = new RandomWMethodEQOracle<>(oracleForEQoracle, 17, 17, 1700);
//				eqOracle = new RandomWMethodQsizeEQOracle<>(eq_sul, 17, 17, 1700, mealyss.getStates().size());
//				eqOracle = new RandomWMethodQsizeEQOracle<>(eq_sul, 17, 17, 0, mealyss.getStates().size());
				//eqOracle = new RandomWMethodQsizeEQOracle<>(eq_sul, 1, 2, 0, mealyss);
				eqOracle = new RandomWMethodQsizeEQOracle<>(eq_sul, 1, 100, 0, mealyss);

	
				
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
				bw_comparison.write("\t"+((Counter)mq_sym.getStatisticalData()).getCount()+"\t"+((Counter)eq_sym.getStatisticalData()).getCount());
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

	private static void run_fl_IncrMQs_DynamicLStarM() throws Exception{
		//		bw_comparison = new BufferedWriter(new FileWriter(new File(new File(ExperimentNordsec16Utils.getInstance().getVersions()[0]).getParentFile(),ExperimentNordsec16Utils.getInstance().getTab_filename()),true));
				
			for (int i = 1; i < ExperimentNordsec16Utils.getInstance().getVersions().length; i++) {
				int [] vals = {0,i-1};
				for (int j : vals) { 
		
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
					MembershipOracle<String,Word<Word<String>>> oracleForLearner  = new SULOracle<>(mq_sul);
					MembershipOracle<String,Word<Word<String>>> oracleForEQoracle = new SULOracle<>(eq_sul);
		
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
						initSuffixes.clear(); initSuffixes.addAll(myot.getSuffixes());
						initPrefixes.clear(); initPrefixes.addAll(myot.getPrefixes());
						bw.write("Revalidation\n");
						bw.write(mq_rst.getStatisticalData().toString());bw.write("\n");
						bw.write(mq_sym.getStatisticalData().toString());bw.write("\n");
						bw.write(eq_rst.getStatisticalData().toString());bw.write("\n");
						bw.write(eq_sym.getStatisticalData().toString());bw.write("\n");
					}
					//bw_comparison.write("gDLStarM\t");
					bw_comparison.write("DL*M_v2\t");
					bw_comparison.write(file_i.getName().replaceFirst(".dot$", "")+"\t"+file_j.getName().replaceFirst(".dot$", "")+"\t"+((Counter)mq_rst.getStatisticalData()).getCount()+"\t"+((Counter)eq_rst.getStatisticalData()).getCount());
		
					// construct L* instance 
					ExtensibleDLStarMealyBuilder<String, Word<String>> builder = new ExtensibleDLStarMealyBuilder<String, Word<String>>();
					builder.setAlphabet(alphabet);
					builder.setOracle(oracleForLearner);
					builder.setInitialPrefixes(initPrefixes);
					builder.setInitialSuffixes(initSuffixes);
					builder.setCexHandler(handler);
					builder.setClosingStrategy(strategy);
		
					ExtensibleDLStarMealy<String, Word<String>> learner = builder.create();
		
					// Equivalence Query Oracle
					EquivalenceOracle<MealyMachine<?, String, ?, Word<String>>, String, Word<Word<String>>> eqOracle = null;
					//eqOracle = new WpMethodEQOracle<>(oracleForEQoracle, 2);
	//				eqOracle = new IrfanEQOracle(eq_sul, mealyss.getStates().size());
	//				((IrfanEQOracle)eqOracle).set_maxResets(1700);
	//				((IrfanEQOracle)eqOracle).set_maxLength(17uname00);
	//				eqOracle = new RandomWMethodEQOracle<>(oracleForEQoracle, 17, 17, 1700);
	//				eqOracle = new RandomWMethodQsizeEQOracle<>(eq_sul, 17, 17, 1700, mealyss.getStates().size());
	//				eqOracle = new RandomWMethodQsizeEQOracle<>(eq_sul, 17, 17, 0, mealyss.getStates().size());
					//eqOracle = new RandomWMethodQsizeEQOracle<>(eq_sul, 1, 2, 0, mealyss);
					eqOracle = new RandomWMethodQsizeEQOracle<>(eq_sul, 1, 100, 0, mealyss);
	
		
					
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
					bw_comparison.write("\t"+((Counter)mq_sym.getStatisticalData()).getCount()+"\t"+((Counter)eq_sym.getStatisticalData()).getCount());
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
