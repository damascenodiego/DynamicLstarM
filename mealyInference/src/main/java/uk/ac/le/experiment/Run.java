package uk.ac.le.experiment;

import java.io.File;
import java.io.IOException;
import java.sql.Timestamp;
import java.text.SimpleDateFormat;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.Date;
import java.util.HashSet;
import java.util.List;
import java.util.Random;
import java.util.Set;

import br.usp.icmc.labes.mealyInference.Infer_LearnLib;
import br.usp.icmc.labes.mealyInference.utils.MyObservationTable;
import br.usp.icmc.labes.mealyInference.utils.OTUtils;
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
import de.learnlib.api.logging.LearnLogger;
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
import de.learnlib.oracle.equivalence.RandomWpMethodEQOracle;
import de.learnlib.oracle.equivalence.WMethodEQOracle;
import de.learnlib.oracle.membership.SULOracle;
import de.learnlib.util.Experiment.MealyExperiment;
import de.learnlib.util.statistics.SimpleProfiler;
import net.automatalib.automata.transout.MealyMachine;
import net.automatalib.automata.transout.impl.compact.CompactMealy;
import net.automatalib.incremental.mealy.IncrementalMealyBuilder;
import net.automatalib.incremental.mealy.tree.IncrementalMealyTreeBuilder;
import net.automatalib.util.automata.Automata;
import net.automatalib.words.Alphabet;
import net.automatalib.words.Word;

public class Run {

	// create log 
	private static LearnLogger logger;
	// set closing strategy
	private static final ClosingStrategy strategy 			= ClosingStrategies.CLOSE_FIRST;
	// set CE processing approach
	private static final ObservationTableCEXHandler handler 	= ObservationTableCEXHandlers.RIVEST_SCHAPIRE;
	private static final SimpleDateFormat sdf = new SimpleDateFormat("yyyy_MM_dd/HH_mm_ss/SSS");
	private static final long tstamp = System.currentTimeMillis();

	private static MealySimulatorSUL sulSim;
	private static IncrementalMealyTreeBuilder cbuilder;
	private static SymbolCounterSUL mq_sym;
	private static ResetCounterSUL mq_rst;
	private static SULOracle<String, Word<String>> mqOracle;
	private static SymbolCounterSUL eq_sym;
	private static ResetCounterSUL eq_rst;
	private static EquivalenceOracle<MealyMachine<?, String, ?, Word<String>>, String, Word<Word<String>>> eqOracle;
	private static File log_dir;

	private static Random rnd_seed;
	private static Timestamp timestamp;
	private static ArrayList<Word<String>> initPrefixes;
	private static ArrayList<Word<String>> initSuffixes;
	private static List<List<MealyPlusFile>> list_of_list_of_suls = new ArrayList<>();
	private static MealyExperiment<String, Word<String>> experiment;
	private static File out_dir;

	public static void main(String[] args) {

		// output directory
		String out_dir_string = "logDir/";
		log_dir = new File(out_dir_string ); 
		out_dir = new File(log_dir,sdf.format(new Date(tstamp))); out_dir.mkdirs();

		// random seed
		rnd_seed = new Random(tstamp);
		// timestamp
		timestamp = new Timestamp(tstamp);


		//Set this before the logger start.
		System.setProperty("logdir", out_dir_string);
		System.setProperty("logtstamp", sdf.format(timestamp).replaceAll("/", "_"));

		logger = LearnLogger.getLogger(Run.class);

		Set<String> argsSet = new HashSet<>(Arrays.asList(args));
		//argsSet.add("ot");

		try {
			list_of_list_of_suls.add(Experiments.NORDSEC16_CLI_load());
			list_of_list_of_suls.add(Experiments.NORDSEC16_SRV_load());
			list_of_list_of_suls.add(Experiments.QUIC_PROTOCOL_load());
			list_of_list_of_suls.add(Experiments.SSH_IMPLEM_load());
			list_of_list_of_suls.add(Experiments.TCP_CLI_IMPLEM_load());
			list_of_list_of_suls.add(Experiments.TCP_SRV_IMPLEM_load());

			if((args.length==1) && args[0].matches("^-ot$")){
				for (List<MealyPlusFile> list_of_suls : list_of_list_of_suls) {
					for (MealyPlusFile sul_i : list_of_suls) {
						logger.logEvent("Start creating OT: "+sul_i.getFile().getName());
						createInitialSetsFromFile(sul_i);
						logger.logEvent("End creating OT: "+sul_i.getFile().getName());
					}
				}
			}else if((args.length==1) && args[0].matches("^-reps=[0-9]+$")){
				int reps = Integer.valueOf(args[0].replaceAll("^-reps=",""));
				for (int i = 0; i < reps; i++) {
					for (List<MealyPlusFile> list_of_suls : list_of_list_of_suls) {
						for (MealyPlusFile sul_i : list_of_suls) {
							{
								logger.logEvent("Start LStar @"+sul_i.getFile().getName());
								setupSUL(sul_i);
								setupMQOracle();
								setupEQOracle();
								setupInitialSetsDefault(sul_i);
								buildAndRunExperiment(sul_i);
								logger.logEvent("End LStar @"+sul_i.getFile().getName());
							}

							{
								logger.logEvent("Start L1 @"+sul_i.getFile().getName());
								setupSUL(sul_i);
								setupMQOracle();
								setupEQOracle();
								setupInitialSetsL1();
								buildAndRunExperiment(sul_i);
								logger.logEvent("End L1 @"+sul_i.getFile().getName());
							}

							for (MealyPlusFile sul_j : list_of_suls) {
								if(sul_i.equals(sul_j)) continue;
								{
									logger.logEvent("Start AdaptiveLstar @"+sul_i.getFile().getName()+" w/"+sul_j.getFile().getName());
									setupSUL(sul_i);
									setupMQOracle();
									setupEQOracle();
									setupInitialSetsFromOT(sul_i,sul_j);
									initPrefixes.clear(); initPrefixes.add(Word.epsilon());
									buildAndRunExperiment(sul_i);
									logger.logEvent("End AdaptiveLstar @"+sul_i.getFile().getName()+" w/"+sul_j.getFile().getName());
								}

								{
									logger.logEvent("Start DLstar_v1 @"+sul_i.getFile().getName()+" w/"+sul_j.getFile().getName());
									setupSUL(sul_i);
									setupMQOracle();
									setupEQOracle();
									setupInitialSetsFromOT(sul_i,sul_j);
									MyObservationTable myot = new MyObservationTable(initPrefixes,initSuffixes);
									logger.logEvent("Revalidate OT");
									ObservationTable<String, Word<Word<String>>> reval_ot = OTUtils.getInstance().revalidateObservationTable(myot, mqOracle,sul_i.getMealyss());
									// learning statistics
									logger.logEvent("Reused queries [resets]: " +((Counter)(mq_rst.getStatisticalData())).getCount());
									logger.logEvent("Reused queries [symbols]: "+((Counter)(mq_sym.getStatisticalData())).getCount());
									initPrefixes.clear(); initPrefixes.addAll(reval_ot.getShortPrefixes());
									initSuffixes.clear(); initSuffixes.addAll(reval_ot.getSuffixes());
									buildAndRunExperiment(sul_i);
									logger.logEvent("End DLstar_v1 @"+sul_i.getFile().getName()+" w/"+sul_j.getFile().getName());
								}

								{
									logger.logEvent("Start DLstar_v2 @"+sul_i.getFile().getName()+" w/"+sul_j.getFile().getName());
									setupSUL(sul_i);
									setupMQOracle();
									setupEQOracle();
									setupInitialSetsFromOT(sul_i,sul_j);
									buildAndRunDynamicExperiment(sul_i);
									logger.logEvent("End DLstar_v2 @"+sul_i.getFile().getName()+" w/"+sul_j.getFile().getName());
								}
							}						
						}
					} // end for-each list_of_list_of_suls
				}
			}else {
				System.err.println("Run [-ot | -reps=<Integer representing the number of repetitions>]");
				System.exit(1);
			}

		}catch (Exception e) {
			e.printStackTrace();
		}

	}

	private static void createInitialSetsFromFile(MealyPlusFile the_sul) throws IOException {
		File sul_ot = new File(log_dir,the_sul.getFile().getName()+".reuse");

		// Empty list of prefixes 
		ArrayList<Word<String>> initPrefixes = new ArrayList<Word<String>>();
		initPrefixes.add(Word.epsilon());
		// Empty list of suffixes => minimal compliant setinitCes
		ArrayList<Word<String>> initSuffixes = new ArrayList<Word<String>>();
		initSuffixes.addAll(Automata.characterizingSet(the_sul.getMealyss(), the_sul.getMealyss().getInputAlphabet()));

		SUL<String,Word<String>> sulSim = new MealySimulatorSUL(the_sul.getMealyss(), Utils.OMEGA_SYMBOL);
		Alphabet<String> alphabet = the_sul.getMealyss().getInputAlphabet();

		// set closing strategy and CE processing approach
		ClosingStrategy strategy 			= ClosingStrategies.CLOSE_FIRST;
		ObservationTableCEXHandler handler 	= ObservationTableCEXHandlers.RIVEST_SCHAPIRE;

		MembershipOracle<String,Word<Word<String>>> oracleForLearner1  = new SULOracle<>(sulSim);
		MembershipOracle<String,Word<Word<String>>> oracleForEQoracle1 = new SULOracle<>(sulSim);

		// construct L* instance 
		ExtensibleLStarMealyBuilder<String, Word<String>> builder1 = new ExtensibleLStarMealyBuilder<String, Word<String>>();
		builder1.setAlphabet(alphabet);
		builder1.setOracle(oracleForLearner1);
		builder1.setInitialPrefixes(initPrefixes);
		builder1.setInitialSuffixes(initSuffixes);
		builder1.setCexHandler(handler);
		builder1.setClosingStrategy(strategy);

		ExtensibleLStarMealy<String, Word<String>> learner1 = builder1.create();

		// Equivalence Query Oracle
		EquivalenceOracle<MealyMachine<?, String, ?, Word<String>>, String, Word<Word<String>>> eqOracle1 = null;
		eqOracle1 = new WMethodEQOracle(oracleForEQoracle1, 2);

		// The experiment will execute the main loop of active learning
		MealyExperiment<String, Word<String>> experiment1 = new MealyExperiment<String, Word<String>> (learner1, eqOracle1, alphabet);
		// turn on time profiling
		experiment1.setProfile(true);
		// enable logging of modelsOT
		experiment1.setLogModels(true);
		// run experiment
		experiment1.run();

		OTUtils.getInstance().writeOT(learner1.getObservationTable(), sul_ot);
	}

	private static void setupInitialSetsL1() {
		// Empty list of prefixes 
		initPrefixes = new ArrayList<Word<String>>();
		initPrefixes.add(Word.epsilon());
		// Empty list of suffixes => minimal compliant setinitCes
		initSuffixes = new ArrayList<Word<String>>();
	}

	private static void setupInitialSetsDefault(MealyPlusFile the_sul) {
		setupInitialSetsL1();		
		for (String input : the_sul.getMealyss().getInputAlphabet()) {
			Word<String> word = Word.epsilon();
			word = word.append(input);
			initSuffixes.add(word);
		}
	}
	
	private static void setupInitialSetsFromOT(MealyPlusFile the_sul, MealyPlusFile the_ot) throws IOException {
		File sul_ot = new File(log_dir,the_ot.getFile().getName()+".reuse");
		logger.logEvent("Reading OT: "+sul_ot.getName());

		MyObservationTable my_ot = OTUtils.getInstance().readOT(sul_ot, the_sul.getMealyss().getInputAlphabet());

		// Empty list of prefixes 
		initPrefixes = new ArrayList<Word<String>>(my_ot.getPrefixes());
		// Empty list of suffixes => minimal compliant setinitCes
		initSuffixes = new ArrayList<Word<String>>(my_ot.getSuffixes());
	}

	private static void setupSUL(MealyPlusFile the_sul) {
		// setup SUL simulator
		logger.logEvent("SUL name: "+the_sul.getFile().getName());
		logger.logEvent("SUL dir: "+the_sul.getFile().getAbsolutePath());
		logger.logEvent("Output dir: "+log_dir);
		logger.logEvent("Seed: "+Long.toString(tstamp));
		logger.logEvent("ClosingStrategy: "+strategy.toString());
		logger.logEvent("ObservationTableCEXHandler: "+handler.toString());
		sulSim = new MealySimulatorSUL<>(the_sul.getMealyss(), Utils.OMEGA_SYMBOL);		

		// use single IncrementalMealyBuilder for caching and avoiding duplicated EQs and MQs
		cbuilder = new IncrementalMealyTreeBuilder<>(the_sul.getMealyss().getInputAlphabet());
		logger.logEvent("Cache: "+(true?"Y":"N"));		
	}

	private static void setupMQOracle() {
		// Counters for MQs 
		mq_sym = new SymbolCounterSUL<>("MQ", sulSim);
		mq_rst = new ResetCounterSUL <>("MQ", mq_sym);

		// SUL for counting queries wraps sul
		SUL<String, Word<String>> mq_sul = mq_rst;

		// SULs for associating the IncrementalMealyBuilder 'cbuilder' to MQs
		mq_sul = new SULCache<>(cbuilder, mq_rst);
		mqOracle = new SULOracle<String, Word<String>>(mq_sul);		
	}

	private static void setupEQOracle() {
		// Counters for EQs
		eq_sym = new SymbolCounterSUL<>("EQ", sulSim);
		eq_rst = new ResetCounterSUL <>("EQ", eq_sym);

		// SUL for counting queries wraps sul
		SUL<String, Word<String>> eq_sul = eq_rst;

		// SULs for associating the IncrementalMealyBuilder 'cbuilder' to EQs
		eq_sul = new SULCache<>(cbuilder, eq_rst);
		SULOracle oracleForEQoracle = new SULOracle<>(eq_sul);
		
		// set EQ oracle ...
		eqOracle = new RandomWpMethodEQOracle<>(oracleForEQoracle, 2, 50, 20000);
		logger.logEvent("EquivalenceOracle: RandomWpMethodEQOracle(2, 50, 20000)");

	}

	private static void buildAndRunExperiment(MealyPlusFile the_sul) throws IOException {
		// construct L* instance 
		ExtensibleLStarMealyBuilder<String, Word<String>> builder = new ExtensibleLStarMealyBuilder<String, Word<String>>();
		builder.setAlphabet(the_sul.getMealyss().getInputAlphabet());
		builder.setOracle(mqOracle);
		builder.setInitialPrefixes(initPrefixes);
		builder.setInitialSuffixes(initSuffixes);
		builder.setCexHandler(handler);
		builder.setClosingStrategy(strategy);
		ExtensibleLStarMealy<String, Word<String>> learner = builder.create();
	
		// The experiment will execute the main loop of active learning
		experiment = new MealyExperiment<String, Word<String>> (learner, eqOracle, the_sul.getMealyss().getInputAlphabet());
	
		// turn on time profiling
		experiment.setProfile(true);
	
		// enable logging of models
		experiment.setLogModels(true);
	
		// run experiment
		experiment.run();
	
		logger.logConfig("Rounds: "+experiment.getRounds().getCount());
		// learning statistics
		logger.logStatistic(mq_rst.getStatisticalData());
		logger.logStatistic(mq_sym.getStatisticalData());
		logger.logStatistic(eq_rst.getStatisticalData());
		logger.logStatistic(eq_sym.getStatisticalData());
	
		// profiling
		SimpleProfiler.logResults();
	
		Word<String> sepWord = Automata.findSeparatingWord(the_sul.getMealyss(), learner.getHypothesisModel(), the_sul.getMealyss().getInputAlphabet());			
		if(sepWord == null){
			logger.logConfig("Equivalent: OK");
		}else{
			logger.logConfig("Equivalent: NOK");
		}
		
		//out_dir = new File(log_dir,sdf.format(new Date(tstamp))); out_dir.mkdirs();
		new ObservationTableASCIIWriter<>().write(learner.getObservationTable(), new File(out_dir,the_sul.getFile().getName()+"."+sdf.format(new Date(System.currentTimeMillis())).replaceAll("/", "")+".ot"));
	}

	private static void buildAndRunDynamicExperiment(MealyPlusFile the_sul) throws IOException {
		// construct L* instance 
		ExtensibleDLStarMealyBuilder<String, Word<String>> builder = new ExtensibleDLStarMealyBuilder<String, Word<String>>();
		builder.setAlphabet(the_sul.getMealyss().getInputAlphabet());
		builder.setOracle(mqOracle);
		builder.setInitialPrefixes(initPrefixes);
		builder.setInitialSuffixes(initSuffixes);
		builder.setCexHandler(handler);
		builder.setClosingStrategy(strategy);
		ExtensibleDLStarMealy<String, Word<String>> learner = builder.create();

		// The experiment will execute the main loop of active learning
		experiment = new MealyExperiment<String, Word<String>> (learner, eqOracle, the_sul.getMealyss().getInputAlphabet());

		// turn on time profiling
		experiment.setProfile(true);

		// enable logging of models
		experiment.setLogModels(true);
		//out_dir = new File(log_dir,sdf.format(new Date(tstamp))); out_dir.mkdirs();
		new ObservationTableASCIIWriter<>().write(learner.getObservationTable(), new File(out_dir,the_sul.getFile().getName()+".reval."+sdf.format(new Date(System.currentTimeMillis())).replaceAll("/", "")+".ot"));

		// run experiment
		experiment.run();

		logger.logConfig("Rounds: "+experiment.getRounds().getCount());
		// learning statistics
		logger.logStatistic(mq_rst.getStatisticalData());
		logger.logStatistic(mq_sym.getStatisticalData());
		logger.logStatistic(eq_rst.getStatisticalData());
		logger.logStatistic(eq_sym.getStatisticalData());

		// profiling
		SimpleProfiler.logResults();

		Word<String> sepWord = Automata.findSeparatingWord(the_sul.getMealyss(), learner.getHypothesisModel(), the_sul.getMealyss().getInputAlphabet());			
		if(sepWord == null){
			logger.logConfig("Equivalent: OK");
		}else{
			logger.logConfig("Equivalent: NOK");
		}

		//out_dir = new File(log_dir,sdf.format(new Date(tstamp))); out_dir.mkdirs();
		new ObservationTableASCIIWriter<>().write(learner.getObservationTable(), new File(out_dir,the_sul.getFile().getName()+"."+sdf.format(new Date(System.currentTimeMillis())).replaceAll("/", "")+".ot"));
	}


}
