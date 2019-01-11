/**
 * 
 */
package br.usp.icmc.labes.mealyInference;

import java.io.File;
import java.io.IOException;
import java.sql.Timestamp;
import java.text.SimpleDateFormat;
import java.util.ArrayList;
import java.util.List;
import java.util.Random;
import java.util.logging.FileHandler;
import java.util.logging.SimpleFormatter;

import org.apache.commons.cli.BasicParser;
import org.apache.commons.cli.CommandLine;
import org.apache.commons.cli.CommandLineParser;
import org.apache.commons.cli.HelpFormatter;
import org.apache.commons.cli.Options;

import br.usp.icmc.labes.mealyInference.utils.RandomWMethodQsizeEQOracle;
import br.usp.icmc.labes.mealyInference.utils.LearnLibProperties;
import br.usp.icmc.labes.mealyInference.utils.MyObservationTable;
import br.usp.icmc.labes.mealyInference.utils.OTUtils;
import br.usp.icmc.labes.mealyInference.utils.Utils;
import de.learnlib.algorithms.lstar.ce.ObservationTableCEXHandler;
import de.learnlib.algorithms.lstar.ce.ObservationTableCEXHandlers;
import de.learnlib.algorithms.lstar.closing.ClosingStrategies;
import de.learnlib.algorithms.lstar.closing.ClosingStrategy;
import de.learnlib.algorithms.lstar.mealy.ExtensibleLStarMealy;
import de.learnlib.algorithms.lstar.mealy.ExtensibleLStarMealyBuilder;

import de.learnlib.algorithms.ttt.mealy.TTTLearnerMealy;
import de.learnlib.algorithms.ttt.mealy.TTTLearnerMealyBuilder;
import de.learnlib.acex.analyzers.AcexAnalyzers;

import de.learnlib.algorithms.dlstar.mealy.ExtensibleDLStarMealy;
import de.learnlib.algorithms.dlstar.mealy.ExtensibleDLStarMealyBuilder;

import de.learnlib.api.SUL;
import de.learnlib.api.logging.LearnLogger;
import de.learnlib.api.oracle.EquivalenceOracle;
import de.learnlib.api.oracle.EquivalenceOracle.MealyEquivalenceOracle;
import de.learnlib.api.oracle.MembershipOracle;
import de.learnlib.api.statistic.StatisticSUL;

import de.learnlib.datastructure.observationtable.ObservationTable;
import de.learnlib.datastructure.observationtable.writer.ObservationTableASCIIWriter;
import de.learnlib.driver.util.MealySimulatorSUL;

import de.learnlib.filter.cache.sul.SULCache;
import de.learnlib.filter.statistic.sul.ResetCounterSUL;
import de.learnlib.filter.statistic.sul.SymbolCounterSUL;

import de.learnlib.oracle.equivalence.RandomWordsEQOracle;
import de.learnlib.oracle.equivalence.WMethodEQOracle;
import de.learnlib.oracle.equivalence.WpMethodEQOracle;
import de.learnlib.oracle.equivalence.mealy.RandomWalkEQOracle;
import de.learnlib.oracle.membership.SULOracle;

import de.learnlib.util.Experiment.MealyExperiment;
import de.learnlib.util.statistics.SimpleProfiler;

import net.automatalib.automata.transout.MealyMachine;
import net.automatalib.automata.transout.impl.compact.CompactMealy;
import net.automatalib.incremental.mealy.IncrementalMealyBuilder;
import net.automatalib.incremental.mealy.tree.IncrementalMealyTreeBuilder;
import net.automatalib.serialization.dot.GraphDOT;
import net.automatalib.util.automata.Automata;
import net.automatalib.words.Word;

/**
 * @author damasceno
 *
 */
public class Infer_LearnLib {

	public static final String CONFIG = "config";
	public static final String SOT = "sot";
	public static final String SUL = "sul";
	public static final String HELP = "help";
	public static final String HELP_SHORT = "h";
	public static final String OT = "ot";
	public static final String CEXH = "cexh";
	public static final String CLOS = "clos";
	public static final String EQ = "eq";
	public static final String CACHE = "cache";
	public static final String SEED = "seed";
	public static final String OUT = "out";
	public static final String LEARN = "learn";
	public static final String INFO = "info";
	
	public static final SimpleDateFormat sdf = new SimpleDateFormat("yyyyMMddHHmmss");
	
	public static final String[] eqMethodsAvailable = {"rndWalk" , "rndWords", "wp", "w", "weq"};
	public static final String[] closingStrategiesAvailable = {"CloseFirst" , "CloseShortest"};
	private static final String RIVEST_SCHAPIRE_ALLSUFFIXES = "RivestSchapireAllSuffixes";
	public static final String[] cexHandlersAvailable = {"ClassicLStar" , "MalerPnueli", "RivestSchapire", RIVEST_SCHAPIRE_ALLSUFFIXES, "Shahbaz", "Suffix1by1"};
	public static final String[] learningMethodsAvailable = {"lstar" , "l1","adaptive", "dlstar_v2", "dlstar_v1"
			,"ttt"
			};


	public static void main(String[] args) throws Exception {

		// create the command line parser
		CommandLineParser parser = new BasicParser();
		// create the Options
		Options options = createOptions();
		// automatically generate the help statement
		HelpFormatter formatter = new HelpFormatter();

		
		long tstamp = System.currentTimeMillis();
		// random seed
		Random rnd_seed = new Random(tstamp);

		// timestamp
		Timestamp timestamp = new Timestamp(tstamp);

		try {
			
			// parse the command line arguments
			CommandLine line = parser.parse( options, args);

			if(line.hasOption(HELP)){
				formatter.printHelp( "Infer_LearnLib", options );
				System.exit(0);
			}
			
			if(!line.hasOption(SUL)){
				throw new IllegalArgumentException("must provide a SUL");
			}


			// set SUL path
			File sul = new File(line.getOptionValue(SUL));

			// if passed as argument, set OT path 
			File obsTable = null;
			if( line.hasOption(OT)){
				obsTable = new File(line.getOptionValue(OT));
			}

			// set output dir
			File out_dir = sul.getParentFile();
			if( line.hasOption(OUT)){
				out_dir = new File(line.getOptionValue(OUT));
			}
			if(!out_dir.exists()) {
				out_dir.mkdirs();
			}
			
			LearnLibProperties learn_props = LearnLibProperties.getInstance();
			if(line.hasOption(CONFIG)) {
				String pathname = line.getOptionValue(CONFIG);
				learn_props.loadProperties(new File(pathname));				
			}
			
			// create log
			System.setProperty("logdir", out_dir.getAbsolutePath());
			LearnLogger logger = LearnLogger.getLogger(Infer_LearnLib.class);

			// set closing strategy
			ClosingStrategy<Object, Object> strategy 			= getClosingStrategy(line.getOptionValue(CLOS));

			// set CE processing approach
			ObservationTableCEXHandler<Object, Object> handler 	= getCEXHandler(line.getOptionValue(CEXH));
			
			// load mealy machine
			CompactMealy<String, Word<String>> mealyss = Utils.getInstance().loadMealyMachine(sul);
			logger.logEvent("SUL name: "+sul.getName());
			logger.logEvent("SUL dir: "+sul.getAbsolutePath());
			logger.logEvent("Output dir: "+out_dir);
			
			if( line.hasOption( SEED ) )  tstamp = Long.valueOf(line.getOptionValue(SEED));
			rnd_seed.setSeed(tstamp);
			logger.logEvent("Seed: "+Long.toString(tstamp));
			

			Utils.getInstance();
			// SUL simulator
			SUL<String,Word<String>> sulSim = new MealySimulatorSUL<>(mealyss, Utils.OMEGA_SYMBOL);
			
			//////////////////////////////////
			// Setup objects related to MQs	//
			//////////////////////////////////
			
			// Counters for MQs 
			StatisticSUL<String, Word<String>>  mq_sym = new SymbolCounterSUL<>("MQ", sulSim);
			StatisticSUL<String, Word<String>>  mq_rst = new ResetCounterSUL <>("MQ", mq_sym);
			
			// SUL for counting queries wraps sul
			SUL<String, Word<String>> mq_sul = mq_rst;
			
			// IncrementalMealyBuilder for caching MQs
			IncrementalMealyBuilder<String,Word<String>> mq_cbuilder = new IncrementalMealyTreeBuilder<>(mealyss.getInputAlphabet());
			// use caching to avoid duplicate queries
			if(line.hasOption(CACHE))  {
				// SULs for associating the IncrementalMealyBuilder 'mq_cbuilder' to MQs
				mq_sul = new SULCache<>(mq_cbuilder, mq_rst);
			}
			MembershipOracle<String, Word<Word<String>>> mqOracle = new SULOracle<String, Word<String>>(mq_sul);
			
			logger.logEvent("Cache: "+(line.hasOption(CACHE)?"Y":"N"));
			
			//////////////////////////////////
			// Setup objects related to EQs	//
			//////////////////////////////////
			

			logger.logEvent("ClosingStrategy: "+strategy.toString());
			logger.logEvent("ObservationTableCEXHandler: "+handler.toString());
			
			// Counters for EQs 
			StatisticSUL<String, Word<String>>  eq_sym = new SymbolCounterSUL<>("EQ", sulSim);
			StatisticSUL<String, Word<String>>  eq_rst = new ResetCounterSUL <>("EQ", eq_sym);
			
			// SUL for counting queries wraps sul
			SUL<String, Word<String>> eq_sul = eq_rst;

			// IncrementalMealyBuilder for caching EQs
			IncrementalMealyBuilder<String,Word<String>> eq_cbuilder = new IncrementalMealyTreeBuilder<>(mealyss.getInputAlphabet());
			// use caching to avoid duplicate queries
			if(line.hasOption(CACHE))  {
				// SULs for associating the IncrementalMealyBuilder 'cbuilder' to EQs
				eq_sul = new SULCache<>(eq_cbuilder, eq_rst);
			}
			
			
			
			EquivalenceOracle<MealyMachine<?, String, ?, Word<String>>, String, Word<Word<String>>> eqOracle = null;
			eqOracle = buildEqOracle(rnd_seed, line, logger, mealyss, eq_sul);

			/////////////////////////////
			// Setup experiment object //
			/////////////////////////////

			String learnAlgorithm = "lstar";
			MealyExperiment experiment = null;
			
			if(line.hasOption(LEARN)) learnAlgorithm = line.getOptionValue(LEARN).toLowerCase();
			switch (learnAlgorithm) {
			case "l1":
				logger.logConfig("Method: L1");
				experiment = learningL1(mealyss, mqOracle, eqOracle, handler, strategy);
				break;
			case "dlstar_v1":
				if(handler == ObservationTableCEXHandlers.CLASSIC_LSTAR)  throw new Exception("DL*M requires "+ObservationTableCEXHandlers.RIVEST_SCHAPIRE+" CexH");
				logger.logConfig("Method: DL*M_v1");
				logger.logEvent("Revalidate OT");
				experiment = learningDLStarM_v1(mealyss, mqOracle, eqOracle, handler, strategy,obsTable);
				// learning statistics
				logger.logEvent("Reused queries [resets]: " +((ResetCounterSUL)mq_rst).getStatisticalData().getCount());
				logger.logEvent("Reused queries [symbols]: "+((SymbolCounterSUL)mq_sym).getStatisticalData().getCount());
				break;
			case "dlstar_v2":
				
				if(handler == ObservationTableCEXHandlers.CLASSIC_LSTAR)  throw new Exception("DL*M requires "+ObservationTableCEXHandlers.RIVEST_SCHAPIRE+" CexH");
				experiment = learningDLStarM_v2(mealyss, mqOracle, eqOracle, handler, strategy,obsTable);
				logger.logConfig("Method: DL*M_v2");
				break;
			case "ttt":
				experiment = learningTTT(mealyss, mqOracle, eqOracle, handler, strategy);
				break;
			case "lstar":
			default:
				experiment = learningLStarM(mealyss, mqOracle, eqOracle, handler, strategy);
				logger.logConfig("Method: L*M");
				break;
			}
			
			// turn on time profiling
			experiment.setProfile(true);

			// enable logging of models
			experiment.setLogModels(true);
			
			// run experiment
			experiment.run();

			// learning statistics
			logger.logConfig("Rounds: "+experiment.getRounds().getCount());
			logger.logStatistic(mq_rst.getStatisticalData());
			logger.logStatistic(mq_sym.getStatisticalData());
			logger.logStatistic(eq_rst.getStatisticalData());
			logger.logStatistic(eq_sym.getStatisticalData());

			// profiling
			SimpleProfiler.logResults();

			MealyMachine finalHyp = (MealyMachine) experiment.getFinalHypothesis();
			
			logger.logConfig("Qsize: "+mealyss.getStates().size());
			logger.logConfig("Isize: "+mealyss.getInputAlphabet().size());

			Word<String> sepWord = Automata.findSeparatingWord(mealyss,finalHyp, mealyss.getInputAlphabet());			
			if(sepWord == null){
				logger.logConfig("Equivalent: OK");
			}else{
				logger.logConfig("Equivalent: NOK");
			}
			
			if(line.hasOption(INFO))  {
				logger.logConfig("Info: "+line.getOptionValue(INFO));
			}else{
				logger.logConfig("Info: N/A");
			}

		}
		catch( Exception exp ) {
			// automatically generate the help statement
			formatter.printHelp( "Infer_LearnLib", options );
			System.err.println( "Unexpected Exception");
			exp.printStackTrace();
		}

	}


	private static EquivalenceOracle<MealyMachine<?, String, ?, Word<String>>, String, Word<Word<String>>> buildEqOracle(
			Random rnd_seed, CommandLine line, LearnLogger logger, CompactMealy<String, Word<String>> mealyss,
			SUL<String, Word<String>> eq_sul) {
		MembershipOracle<String,Word<Word<String>>> oracleForEQoracle = new SULOracle<>(eq_sul);
		
		EquivalenceOracle<MealyMachine<?, String, ?, Word<String>>, String, Word<Word<String>>> eqOracle;
		if(!line.hasOption(EQ)){
			logger.logEvent("EquivalenceOracle: MealyWpMethodEQOracle("+2+")");
			return new WpMethodEQOracle<>(oracleForEQoracle, 2);
		}
		
		LearnLibProperties learn_props = LearnLibProperties.getInstance();
		
		switch (line.getOptionValue(EQ)) {
		case "rndWalk":
			// create RandomWalkEQOracle
			double restartProbability = learn_props.getRndWalk_restartProbability();
			int maxSteps = learn_props.getRndWalk_maxSteps();
			boolean resetStepCount = learn_props.getRndWalk_resetStepsCount();
			
			eqOracle = new RandomWalkEQOracle<String, Word<String>>(
					eq_sul, // sul
					restartProbability,// reset SUL w/ this probability before a step 
					maxSteps, // max steps (overall)
					resetStepCount, // reset step count after counterexample 
					rnd_seed // make results reproducible 
					);
			logger.logEvent("EquivalenceOracle: RandomWalkEQOracle("+restartProbability+","+maxSteps+","+resetStepCount+")");
			break;
		case "rndWords":
			// create RandomWordsEQOracle
			int maxTests = learn_props.getRndWords_maxTests();
			int maxLength = learn_props.getRndWords_maxLength();
			int minLength = learn_props.getRndWords_minLength();

			eqOracle = new RandomWordsEQOracle<>(oracleForEQoracle, minLength, maxLength, maxTests,rnd_seed);
			logger.logEvent("EquivalenceOracle: RandomWordsEQOracle("+minLength+", "+maxLength+", "+maxTests+")");
			break;
		case "wp":
			int maxDepth = learn_props.getW_maxDepth();
			eqOracle = new WpMethodEQOracle<>(oracleForEQoracle, maxDepth);
			logger.logEvent("EquivalenceOracleAbstractCompactDeterministic<String, CompactMealy: MealyWpMethodEQOracle("+maxDepth+")");
			break;
		case "w":
			int maxDepth1 = learn_props.getW_maxDepth();
			eqOracle = new WMethodEQOracle<>(oracleForEQoracle, maxDepth1);
			logger.logEvent("EquivalenceOracle: WMethodEQOracle("+maxDepth1+")");
			break;
		case "weq":
			int minimalSize = learn_props.getWeq_minLen();
			int rndLength = learn_props.getWeq_rndLen();
			int bound = learn_props.getWeq_bound();
			
			eqOracle = new RandomWMethodQsizeEQOracle<>(eq_sul, minimalSize, rndLength, bound, mealyss, rnd_seed);
			logger.logEvent("EquivalenceOracle: RandomWMethodQsizeEQOracle("+minimalSize+","+rndLength+","+bound+","+rnd_seed+")");
			break;
		default:
			int maxDepth2 = learn_props.getW_maxDepth();
			eqOracle = new WMethodEQOracle<>(oracleForEQoracle,maxDepth2);
			logger.logEvent("EquivalenceOracle: MealyWMethodEQOracle("+maxDepth2+")");
			break;
		}
		return eqOracle;
	}


	private static MealyExperiment<String, Word<String>> learningTTT(CompactMealy<String, Word<String>> mealyss,
			MembershipOracle<String, Word<Word<String>>> mqOracle,
			EquivalenceOracle<MealyMachine<?, String, ?, Word<String>>, String, Word<Word<String>>> eqOracle,
			ObservationTableCEXHandler<Object, Object> handler, ClosingStrategy<Object, Object> strategy) {
		
		// construct TTT instance 
		TTTLearnerMealyBuilder<String,Word<String>> builder = new TTTLearnerMealyBuilder<>();
		builder.setAlphabet(mealyss.getInputAlphabet());
		builder.setAnalyzer(AcexAnalyzers.LINEAR_FWD);
		builder.setOracle(mqOracle);

		TTTLearnerMealy<String,Word<String>> learner = builder.create();

		// The experiment will execute the main loop of active learning
		MealyExperiment<String, Word<String>> experiment = new MealyExperiment<String, Word<String>> (learner, eqOracle, mealyss.getInputAlphabet());
		
		return experiment;
	}


	protected static MyObservationTable loadObservationTable(CompactMealy<String, Word<String>> mealyss, File the_ot) throws IOException {
		// create log 
		LearnLogger logger = LearnLogger.getLogger(Infer_LearnLib.class);
		logger.logEvent("Reading OT: "+the_ot.getName());
		
		MyObservationTable my_ot = OTUtils.getInstance().readOT(the_ot, mealyss.getInputAlphabet());
		
		return my_ot;

	}
	
	private static MealyExperiment<String, Word<String>> learningDLStarM_v1(
			CompactMealy<String, Word<String>> mealyss, 
			MembershipOracle<String, Word<Word<String>>> mqOracle, 
			EquivalenceOracle<? super MealyMachine<?, String, ?, Word<String>>, String, Word<Word<String>>> eqOracle, 
			ObservationTableCEXHandler<Object,Object> handler, 
			ClosingStrategy<Object,Object> strategy,
			File ot_file) throws IOException {
		// create log 
		LearnLogger logger = LearnLogger.getLogger(Infer_LearnLib.class);
		
		MyObservationTable my_ot = loadObservationTable(mealyss, ot_file);

		logger.logEvent("Revalidate OT");
		ObservationTable<String, Word<Word<String>>> reval_ot = OTUtils.getInstance().revalidateObservationTable(my_ot, mqOracle,mealyss);
		
		List<Word<String>> initPrefixes = new ArrayList<>();
		List<Word<String>> initSuffixes = new ArrayList<>();
		
		initPrefixes.addAll(reval_ot.getShortPrefixes());
		initSuffixes.addAll(reval_ot.getSuffixes());

		// construct DL*M v1 instance 
		ExtensibleLStarMealyBuilder<String, Word<String>> builder = new ExtensibleLStarMealyBuilder<String, Word<String>>();
		builder.setAlphabet(mealyss.getInputAlphabet());
		builder.setOracle(mqOracle);
		builder.setInitialPrefixes(initPrefixes);
		builder.setInitialSuffixes(initSuffixes);
		builder.setCexHandler(handler);
		builder.setClosingStrategy(strategy);
		ExtensibleLStarMealy<String, Word<String>> learner = builder.create();

		// The experiment will execute the main loop of active learning
		MealyExperiment<String, Word<String>> experiment = new MealyExperiment<String, Word<String>> (learner, eqOracle, mealyss.getInputAlphabet());

		return experiment;
	}

	
	private static MealyExperiment<String, Word<String>> learningDLStarM_v2(
			CompactMealy<String, Word<String>> mealyss, 
			MembershipOracle<String, Word<Word<String>>> mqOracle, 
			EquivalenceOracle<? super MealyMachine<?, String, ?, Word<String>>, String, Word<Word<String>>> eqOracle,
			ObservationTableCEXHandler<Object,Object> handler, 
			ClosingStrategy<Object,Object> strategy,
			File ot_file) throws IOException {
		
		MyObservationTable my_ot = loadObservationTable(mealyss, ot_file);
		
		List<Word<String>> initPrefixes = new ArrayList<>(my_ot.getPrefixes());
		List<Word<String>> initSuffixes = new ArrayList<>(my_ot.getSuffixes());
		
		// construct DL*M v2 instance 
		ExtensibleDLStarMealyBuilder<String, Word<String>> builder = new ExtensibleDLStarMealyBuilder<String, Word<String>>();
		builder.setAlphabet(mealyss.getInputAlphabet());
		builder.setOracle(mqOracle);
		builder.setInitialPrefixes(initPrefixes);
		builder.setInitialSuffixes(initSuffixes);
		builder.setCexHandler(handler);
		builder.setClosingStrategy(strategy);
		ExtensibleDLStarMealy<String, Word<String>> learner = builder.create();

		// The experiment will execute the main loop of active learning
		MealyExperiment<String, Word<String>> experiment = new MealyExperiment<String, Word<String>> (learner, eqOracle, mealyss.getInputAlphabet());

		return experiment;
	}




	private static MealyExperiment<String, Word<String>> learningL1(
			CompactMealy<String, Word<String>> mealyss, 
			MembershipOracle<String, Word<Word<String>>> mqOracle, 
			EquivalenceOracle<? super MealyMachine<?, String, ?, Word<String>>, String, Word<Word<String>>> eqOracle, 
			ObservationTableCEXHandler<Object,Object> handler, 
			ClosingStrategy<Object,Object> strategy) {
		List<Word<String>> initPrefixes = new ArrayList<>();
		initPrefixes.add(Word.epsilon());
		List<Word<String>> initSuffixes = new ArrayList<>();
		
		// construct L1 instance 
		ExtensibleLStarMealyBuilder<String, Word<String>> builder = new ExtensibleLStarMealyBuilder<String, Word<String>>();
		builder.setAlphabet(mealyss.getInputAlphabet());
		builder.setOracle(mqOracle);
		builder.setInitialPrefixes(initPrefixes );
		builder.setInitialSuffixes(initSuffixes);
		builder.setCexHandler(handler);
		builder.setClosingStrategy(strategy);

		ExtensibleLStarMealy<String, Word<String>> learner = builder.create();

		// The experiment will execute the main loop of active learning
		MealyExperiment<String, Word<String>> experiment = new MealyExperiment<String, Word<String>> (learner, eqOracle, mealyss.getInputAlphabet());

		return experiment;
	}


	private static MealyExperiment<String, Word<String>> learningLStarM(
			CompactMealy<String, Word<String>> mealyss, 
			MembershipOracle<String, Word<Word<String>>> mqOracle, 
			EquivalenceOracle<? super MealyMachine<?, String, ?, Word<String>>, String, Word<Word<String>>> eqOracle, 
			ObservationTableCEXHandler<Object,Object> handler, 
			ClosingStrategy<Object,Object> strategy) {
		List<Word<String>> initPrefixes = new ArrayList<>();
		initPrefixes.add(Word.epsilon());
		List<Word<String>> initSuffixes = new ArrayList<>();
		Word<String> word = Word.epsilon();
		for (String symbol : mealyss.getInputAlphabet()) { 
			initSuffixes.add(word.append(symbol));
		}
		
		// construct standard L*M instance 
		ExtensibleLStarMealyBuilder<String, Word<String>> builder = new ExtensibleLStarMealyBuilder<String, Word<String>>();
		builder.setAlphabet(mealyss.getInputAlphabet());
		builder.setOracle(mqOracle);
		builder.setInitialPrefixes(initPrefixes );
		builder.setInitialSuffixes(initSuffixes);
		builder.setCexHandler(handler);
		builder.setClosingStrategy(strategy);

		ExtensibleLStarMealy<String, Word<String>> learner = builder.create();

		// The experiment will execute the main loop of active learning
		MealyExperiment<String, Word<String>> experiment = new MealyExperiment<String, Word<String>> (learner, eqOracle, mealyss.getInputAlphabet());

		return experiment;		
	}


	private static ClosingStrategy<Object,Object> getClosingStrategy(String optionValue) {
		if(optionValue != null){
			if (optionValue.equals(ClosingStrategies.CLOSE_FIRST.toString())) {
				return ClosingStrategies.CLOSE_FIRST;
			}else if (optionValue.equals(ClosingStrategies.CLOSE_SHORTEST.toString())) {
				return ClosingStrategies.CLOSE_SHORTEST;
			}
		}
		return ClosingStrategies.CLOSE_FIRST;
	}


	private static ObservationTableCEXHandler<Object,Object> getCEXHandler(String optionValue) {
		if(optionValue != null){
			if (optionValue.equals(ObservationTableCEXHandlers.RIVEST_SCHAPIRE.toString())) {
				return ObservationTableCEXHandlers.RIVEST_SCHAPIRE;

			}else if (optionValue.equals(RIVEST_SCHAPIRE_ALLSUFFIXES)) {
				return ObservationTableCEXHandlers.RIVEST_SCHAPIRE_ALLSUFFIXES;
			}else if (optionValue.equals(ObservationTableCEXHandlers.SUFFIX1BY1.toString())) {
				return ObservationTableCEXHandlers.SUFFIX1BY1;
			}else if (optionValue.equals(ObservationTableCEXHandlers.CLASSIC_LSTAR.toString())) {
				return ObservationTableCEXHandlers.CLASSIC_LSTAR;
			}else if (optionValue.equals(ObservationTableCEXHandlers.MALER_PNUELI.toString())) {
				return ObservationTableCEXHandlers.MALER_PNUELI;
			}else if (optionValue.equals(ObservationTableCEXHandlers.SHAHBAZ.toString())) {
				return ObservationTableCEXHandlers.SHAHBAZ;
			}
		}
		return ObservationTableCEXHandlers.RIVEST_SCHAPIRE;
	}


	private static Options createOptions() {
		// create the Options
		Options options = new Options();
		options.addOption( SOT,  false, "Save observation table (OT)" );
		options.addOption( HELP, false, "Shows help" );
		options.addOption( CONFIG, true, "Configuration file");
		options.addOption( SUL,  true, "System Under Learning (SUL)" );
		options.addOption( OT,   true, "Load observation table (OT)" );
		options.addOption( OUT,  true, "Set output directory" );
		options.addOption( CLOS, true, "Set closing strategy."
				+ "\nOptions: {"+String.join(", ", closingStrategiesAvailable)+"}");
		options.addOption( EQ, 	 true, "Set equivalence query generator."
				+ "\nOptions: {"+String.join(", ", eqMethodsAvailable)+"}");
		options.addOption( CEXH, true, "Set counter example (CE) processing method."
				+ "\nOptions: {"+String.join(", ", cexHandlersAvailable)+"}");
		options.addOption( CACHE,false,"Use caching.");
		options.addOption( LEARN,true, "Model learning algorithm."
				+"\nOptions: {"+String.join(", ", learningMethodsAvailable)+"}");
		options.addOption( SEED, true, "Seed used by the random generator");
		options.addOption( INFO, true, "Add extra information as string");
		return options;
	}


	private static LearnLogger createLogfile(File out_dir, String filename) throws SecurityException, IOException {
		File filelog = new File(out_dir,filename);
		FileHandler fh = new FileHandler(filelog.getAbsolutePath());
		fh.setFormatter(new SimpleFormatter());
		LearnLogger logger;
		logger = LearnLogger.getLogger(SimpleProfiler.class);
//		logger = LearnLogger.getLogger(Experiment.class);		
		return logger;

	}
}

