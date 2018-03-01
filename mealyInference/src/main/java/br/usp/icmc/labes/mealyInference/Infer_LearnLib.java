/**
 * 
 */
package br.usp.icmc.labes.mealyInference;

import java.io.BufferedReader;
import java.io.File;
import java.io.FileOutputStream;
import java.io.FileReader;
import java.io.FileWriter;
import java.io.FilenameFilter;
import java.io.IOException;
import java.io.PrintStream;
import java.sql.Timestamp;
import java.text.SimpleDateFormat;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.Date;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Random;
import java.util.Set;
import java.util.logging.FileHandler;
import java.util.logging.Level;
import java.util.logging.LogRecord;
import java.util.logging.SimpleFormatter;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import org.apache.commons.cli.BasicParser;
import org.apache.commons.cli.CommandLine;
import org.apache.commons.cli.CommandLineParser;
import org.apache.commons.cli.DefaultParser;
import org.apache.commons.cli.HelpFormatter;
import org.apache.commons.cli.OptionBuilder;
import org.apache.commons.cli.Options;
import org.apache.commons.cli.ParseException;

import br.usp.icmc.labes.mealyInference.utils.MyObservationTable;
import br.usp.icmc.labes.mealyInference.utils.OTUtils;
import br.usp.icmc.labes.mealyInference.utils.Utils;
import de.learnlib.algorithms.lstargeneric.ce.ObservationTableCEXHandler;
import de.learnlib.algorithms.lstargeneric.ce.ObservationTableCEXHandlers;
import de.learnlib.algorithms.lstargeneric.closing.ClosingStrategies;
import de.learnlib.algorithms.lstargeneric.closing.ClosingStrategy;
import de.learnlib.algorithms.lstargeneric.mealy.ExtensibleLStarMealy;
import de.learnlib.algorithms.lstargeneric.mealy.ExtensibleLStarMealyBuilder;
import de.learnlib.api.EquivalenceOracle;
import de.learnlib.api.MembershipOracle;
import de.learnlib.api.SUL;
import de.learnlib.cache.mealy.MealyCaches;
import de.learnlib.eqtests.basic.WpMethodEQOracle.MealyWpMethodEQOracle;
import de.learnlib.eqtests.basic.mealy.RandomWalkEQOracle;
import de.learnlib.experiments.Experiment;
import de.learnlib.experiments.Experiment.MealyExperiment;
import de.learnlib.logging.LearnLogger;
import de.learnlib.oracles.ResetCounterSUL;
import de.learnlib.oracles.SULOracle;
import de.learnlib.oracles.SymbolCounterSUL;
import de.learnlib.simulator.sul.MealySimulatorSUL;
import de.learnlib.statistics.SimpleProfiler;
import de.learnlib.statistics.StatisticSUL;
import net.automatalib.automata.transout.MealyMachine;
import net.automatalib.automata.transout.impl.compact.CompactMealy;
import net.automatalib.util.graphs.dot.GraphDOT;
import net.automatalib.words.Alphabet;
import net.automatalib.words.Word;
import net.automatalib.words.WordBuilder;
import net.automatalib.words.impl.Alphabets;

/**
 * @author damasceno
 *
 */
public class Infer_LearnLib {

	private static final String SOT = "sot";
	private static final String SUL = "sul";
	private static final String HELP = "help";
	private static final String HELP_SHORT = "h";
	private static final String OT = "ot";
	private static final String CEXH = "cexh";
	private static final String CLOS = "clos";
	private static final String EQ = "eq";
	private static final String CACHE = "cache";
	private static final String SEED = "seed";
	private static final String OUT = "out";
	
	private static final SimpleDateFormat sdf = new SimpleDateFormat("yyyyMMddHHmmss");
	
	private static final String[] eqMethodsAvailable = {"rndWalk" , "wp"};
	private static final String[] closingStrategiesAvailable = {"CloseFirst" , "CloseShortest"};
	private static final String[] cexHandlersAvailable = {"ClassicLStar" , "MalerPnueli", "RivestSchapire", "Shahbaz", "Suffix1by1"};


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
				throw new IllegalArgumentException("must provide a single SUL");
			}

			if( line.hasOption( SEED ) ) {
				rnd_seed.setSeed(Long.valueOf(line.getOptionValue(SEED)));
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

			// set closing strategy
			ClosingStrategy strategy 			= getClosingStrategy(line.getOptionValue(CLOS));

			// set CE processing approach
			ObservationTableCEXHandler handler 	= getCEXHandler(line.getOptionValue(CEXH));

			// create log 
			LearnLogger logger = createLogfile(out_dir,sul.getName()
					+(line.hasOption(OT)?"_reused_"+obsTable.getName():"")
					+"."+sdf.format(timestamp)
					+".log");

			// load mealy machine
			CompactMealy<String, Word<String>> mealyss = Utils.getInstance().loadMealyMachine(sul);
			logger.logEvent("SUL name: "+sul.getName());
			logger.logEvent("SUL dir: "+sul.getAbsolutePath());
			logger.logEvent("Output dir: "+out_dir);

			// SUL simulator
			SUL<String,Word<String>> sulSim = new MealySimulatorSUL(mealyss, Utils.getInstance().OMEGA_SYMBOL);

			// membership oracle for counting queries wraps sul
			StatisticSUL<String, Word<String>>  mqSul_sym = new SymbolCounterSUL<>("MQ", sulSim);
			StatisticSUL<String, Word<String>>  mqSul_rst = new ResetCounterSUL <>("MQ", mqSul_sym);			
			MembershipOracle<String, Word<Word<String>>> mqOracle = new SULOracle<String, Word<String>>(mqSul_rst);

			// use caching to avoid duplicate queries
			if(line.hasOption(CACHE))  {
				mqOracle = MealyCaches.createTreeCache(mealyss.getInputAlphabet(), mqOracle);
			}
			logger.logEvent("Cache: "+(line.hasOption(CACHE)?"Y":"N"));

			// reuse OT
			MyObservationTable myot = new MyObservationTable();
			if(line.hasOption(OT)){
				myot = OTUtils.getInstance().readOT(obsTable,mealyss.getInputAlphabet());
				OTUtils.getInstance().revalidateOT2(myot, mqOracle,mealyss);
			}
			logger.logEvent("Reuse OT: "+(line.hasOption(OT)?line.getOptionValue(OT):"N/A"));


			// equivalence oracle for counting queries wraps sul
			StatisticSUL<String, Word<String>> eqSul_sym = new SymbolCounterSUL<>("EQ", sulSim);
			StatisticSUL<String, Word<String>> eqSul_rst = new ResetCounterSUL<>("EQ", eqSul_sym);
			MembershipOracle<String, Word<Word<String>>> sulEqOracle = new SULOracle<String, Word<String>>(eqSul_rst);
			
			EquivalenceOracle<MealyMachine<?, String, ?, Word<String>>, String, Word<Word<String>>> eqOracle = null;
			
			if(line.hasOption(EQ)){
				switch (line.getOptionValue(EQ)) {
				case "rndWalk":
					// create RandomWalkEQOracle
					double restartProbability = 0.05;
					int maxSteps = 10000;
					boolean resetStepCount = true;
					eqOracle = new RandomWalkEQOracle<String, Word<String>>(
							restartProbability,// reset SUL w/ this probability before a step 
							maxSteps, // max steps (overall)
							resetStepCount, // reset step count after counterexample 
							rnd_seed, // make results reproducible 
							eqSul_rst
							);
					logger.logEvent("EquivalenceOracle: RandomWalkEQOracle("+restartProbability+","+maxSteps+","+resetStepCount+")");
					break;
				case "wp":
					int maxDepth = 2;
					eqOracle = new MealyWpMethodEQOracle<>(maxDepth, sulEqOracle);
					logger.logEvent("EquivalenceOracle: MealyWpMethodEQOracle("+maxDepth+")");
				default:
					eqOracle = new MealyWpMethodEQOracle<>(2, sulEqOracle);
					logger.logEvent("EquivalenceOracle: MealyWpMethodEQOracle("+2+")");
					break;
				}
			}else{
				eqOracle = new MealyWpMethodEQOracle<>(2, sulEqOracle);
				logger.logEvent("EquivalenceOracle: MealyWpMethodEQOracle("+2+")");
			}

			///////////////////////////////////////////////
			// Run the experiment using MealyExperiment  //
			///////////////////////////////////////////////

			// Empty list of prefixes 
			List<Word<String>> initPrefixes = new ArrayList<Word<String>>();

			// Empty list of suffixes => minimal compliant setinitCes
			List<Word<String>> initSuffixes = new ArrayList<Word<String>>();

			initSuffixes.clear();
			initPrefixes.clear();

			if(line.hasOption(OT)){
				initSuffixes.addAll(myot.getSuffixes());
				initPrefixes.addAll(myot.getPrefixes());
			}else{
				initPrefixes.add(Word.epsilon());
			}


			// construct L* instance 
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

			// turn on time profiling
			experiment.setProfile(true);

			// enable logging of models
			experiment.setLogModels(true);

			// run experiment
			experiment.run();

			// profiling
			SimpleProfiler.logResults();

			// learning statistics
			logger.logStatistic(mqSul_rst.getStatisticalData());
			logger.logStatistic(mqSul_sym.getStatisticalData());
			logger.logStatistic(eqSul_rst.getStatisticalData());
			logger.logStatistic(eqSul_sym.getStatisticalData());

			if(learner.getHypothesisModel().getStates().size() != mealyss.getStates().size()){
				logger.log(new LogRecord(Level.INFO, "ERROR: Number of states does not match!"));
			}

			if(line.hasOption(SOT)){
				File sul_ot = new File(out_dir,sul.getName()+".ot");
				OTUtils.getInstance().writeOT(learner.getObservationTable(), sul_ot);	
			}
			
			File sul_model = new File(out_dir,sul.getName()+".sul");
			FileWriter fw = new FileWriter(sul_model);
			GraphDOT.write(mealyss, mealyss.getInputAlphabet(), fw);
			
			File hypothesis = new File(out_dir,sul.getName()+".infer");
			fw = new FileWriter(hypothesis);
			GraphDOT.write(experiment.getFinalHypothesis(), mealyss.getInputAlphabet(), fw);

		}
		catch( Exception exp ) {
			System.out.println( "Unexpected exception:" + exp.getMessage() );
			// automatically generate the help statement
			formatter.printHelp( "Infer_LearnLib", options );
		}

	}


	private static ClosingStrategy getClosingStrategy(String optionValue) {
		if(optionValue != null){
			if (optionValue.equals(ClosingStrategies.CLOSE_FIRST.toString())) {
				return ClosingStrategies.CLOSE_FIRST;
			}else if (optionValue.equals(ClosingStrategies.CLOSE_SHORTEST.toString())) {
				return ClosingStrategies.CLOSE_SHORTEST;
			}
		}
		return ClosingStrategies.CLOSE_FIRST;
	}


	private static ObservationTableCEXHandler getCEXHandler(String optionValue) {
		if(optionValue != null){
			if (optionValue.equals(ObservationTableCEXHandlers.RIVEST_SCHAPIRE.toString())) {
				return ObservationTableCEXHandlers.RIVEST_SCHAPIRE;

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
		options.addOption( SUL,  true, "System Under Learning (SUL)" );
		options.addOption( OT,   true, "Load observation table (OT)" );
		options.addOption( OUT,  true, "Set output directory" );
		options.addOption( CLOS, true, "Set closing strategy.\nOptions: {"+String.join(", ", closingStrategiesAvailable)+"}");
		options.addOption( EQ, 	 true, "Set equivalence query generator.\nOptions: {"+String.join(", ", eqMethodsAvailable)+"}");
		options.addOption( CEXH, true, "Set counter example (CE) processing method.\nOptions: {"+String.join(", ", closingStrategiesAvailable)+"}");
		options.addOption( CACHE,false,"Use caching.");
		options.addOption( SEED, true, "Seed used by the random generator");
		//		options.addOption( OptionBuilder.withLongOpt( "block-size" )
		//		                                .withDescription( "use SIZE-byte blocks" )
		//		                                .hasArg()
		//		                                .withArgName("SIZE")
		//		                                .create() );
		return options;
	}


	private static LearnLogger createLogfile(File out_dir, String filename) throws SecurityException, IOException {
		File filelog = new File(out_dir,filename);
		FileHandler fh = new FileHandler(filelog.getAbsolutePath());
		fh.setFormatter(new SimpleFormatter());
		LearnLogger logger; 
		logger = LearnLogger.getLogger(SimpleProfiler.class);	logger.setUseParentHandlers(false); logger.addHandler(fh);
		logger = LearnLogger.getLogger(Experiment.class);		logger.setUseParentHandlers(false); logger.addHandler(fh);
		return logger;

	}
}

