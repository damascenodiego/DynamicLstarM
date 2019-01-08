package experiments.uk.ac.le;

import java.io.File;
import java.io.IOException;
import java.sql.Timestamp;
import java.text.SimpleDateFormat;
import java.util.ArrayList;
import java.util.List;
import java.util.Random;

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
import de.learnlib.datastructure.observationtable.ObservationTable;
import de.learnlib.driver.util.MealySimulatorSUL;
import de.learnlib.filter.cache.sul.SULCache;
import de.learnlib.filter.statistic.sul.ResetCounterSUL;
import de.learnlib.filter.statistic.sul.SymbolCounterSUL;
import de.learnlib.oracle.equivalence.RandomWMethodEQOracle;
import de.learnlib.oracle.membership.SULOracle;
import de.learnlib.util.Experiment.MealyExperiment;
import de.learnlib.util.statistics.SimpleProfiler;
import net.automatalib.automata.transout.MealyMachine;
import net.automatalib.automata.transout.impl.compact.CompactMealy;
import net.automatalib.incremental.mealy.tree.IncrementalMealyTreeBuilder;
import net.automatalib.util.automata.Automata;
import net.automatalib.words.Word;

public abstract class RunExperimentAbstract {

	// create log 
	protected static LearnLogger logger;
	// set closing strategy
	protected static final ClosingStrategy<Object,Object>  strategy 			= ClosingStrategies.CLOSE_FIRST;
	// set CE processing approach
	protected static final ObservationTableCEXHandler<Object,Object>  handler 	= ObservationTableCEXHandlers.RIVEST_SCHAPIRE_ALLSUFFIXES;
	protected static final SimpleDateFormat sdf = new SimpleDateFormat("yyyy_MM_dd/HH_mm_ss/SSS");
	protected static final long tstamp = System.currentTimeMillis();

	protected static MealySimulatorSUL<String,Word<String>> sulSim;
	protected static IncrementalMealyTreeBuilder<String,Word<String>>  cbuilder;
	protected static SymbolCounterSUL<String,Word<String>>  mq_sym;
	protected static ResetCounterSUL<String,Word<String>>  mq_rst;
	protected static SULOracle<String, Word<String>> mqOracle;
	protected static SymbolCounterSUL<String,Word<String>>  eq_sym;
	protected static ResetCounterSUL<String,Word<String>> eq_rst;
	protected static EquivalenceOracle<MealyMachine<?, String, ?, Word<String>>, String, Word<Word<String>>> eqOracle;
	protected static File log_dir;

	protected static Random rnd_seed;
	protected static Timestamp timestamp;
	protected static ArrayList<Word<String>> initPrefixes;
	protected static ArrayList<Word<String>> initSuffixes;
	protected static List<List<MealyPlusFile>> list_of_list_of_suls = new ArrayList<>();
	protected static MealyExperiment<String, Word<String>> experiment;
	protected static File out_dir;
	protected static CompactMealy<String, Word<String>> sulMealy;

	
	protected static void setupInitialSetsL1() {
		// Empty list of prefixes 
		initPrefixes = new ArrayList<Word<String>>();
		initPrefixes.add(Word.epsilon());
		// Empty list of suffixes => minimal compliant setinitCes
		initSuffixes = new ArrayList<Word<String>>();
	}

	protected static void setupInitialSetsDefault(MealyPlusFile the_sul) {
		setupInitialSetsL1();		
		for (String input : the_sul.getMealyss().getInputAlphabet()) {
			Word<String> word = Word.epsilon();
			word = word.append(input);
			initSuffixes.add(word);
		}
	}
	
	protected static void setupInitialSetsFromOT(MealyPlusFile the_sul, MealyPlusFile the_ot) throws IOException {
		File sul_ot = new File(log_dir,the_ot.getFile().getName()+".reuse");
		logger.logEvent("Reading OT: "+sul_ot.getName());

		MyObservationTable my_ot = OTUtils.getInstance().readOT(sul_ot, the_sul.getMealyss().getInputAlphabet());

		// Empty list of prefixes 
		initPrefixes = new ArrayList<Word<String>>(my_ot.getPrefixes());
		// Empty list of suffixes => minimal compliant setinitCes
		initSuffixes = new ArrayList<Word<String>>(my_ot.getSuffixes());
	}

	protected static void setupSUL(MealyPlusFile the_sul) {
		// setup SUL simulator
		logger.logEvent("SUL name: "+the_sul.getFile().getName());
		logger.logEvent("SUL dir: "+the_sul.getFile().getAbsolutePath());
		logger.logEvent("Output dir: "+log_dir);
		logger.logEvent("ClosingStrategy: "+strategy.toString());
		logger.logEvent("ObservationTableCEXHandler: "+handler.toString());
		sulMealy = the_sul.getMealyss();
		sulSim = new MealySimulatorSUL<>(the_sul.getMealyss(), Utils.OMEGA_SYMBOL);		

		// use single IncrementalMealyBuilder for caching and avoiding duplicated EQs and MQs
		cbuilder = new IncrementalMealyTreeBuilder<>(the_sul.getMealyss().getInputAlphabet());
//		logger.logEvent("Cache: "+(true?"Y":"N"));		
		logger.logEvent("Cache: Y");
	}

	protected static void setupMQOracle() {
		// Counters for MQs 
		mq_sym = new SymbolCounterSUL<>("MQ", sulSim);
		mq_rst = new ResetCounterSUL <>("MQ", mq_sym);

		// SUL for counting queries wraps sul
		SUL<String, Word<String>> mq_sul = mq_rst;

		// SULs for associating the IncrementalMealyBuilder 'cbuilder' to MQs
		mq_sul = new SULCache<String,Word<String>>(cbuilder, mq_rst);
		mqOracle = new SULOracle<String, Word<String>>(mq_sul);		
	}

	protected static void setupEQOracle() {}

	protected static void buildAndRunExperiment(MealyPlusFile the_sul) throws IOException {
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
		//new ObservationTableASCIIWriter<>().write(learner.getObservationTable(), new File(out_dir,the_sul.getFile().getName()+"."+sdf.format(new Date(System.currentTimeMillis())).replaceAll("/", "")+".ot"));
	}

	protected static void buildAndRunDynamicExperiment(MealyPlusFile the_sul) throws IOException {
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
		//new ObservationTableASCIIWriter<>().write(learner.getObservationTable(), new File(out_dir,the_sul.getFile().getName()+".reval."+sdf.format(new Date(System.currentTimeMillis())).replaceAll("/", "")+".ot"));

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
		//new ObservationTableASCIIWriter<>().write(learner.getObservationTable(), new File(out_dir,the_sul.getFile().getName()+"."+sdf.format(new Date(System.currentTimeMillis())).replaceAll("/", "")+".ot"));
	}


}
