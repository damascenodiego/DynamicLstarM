/**
 * 
 */
package br.usp.icmc.labes.mealyInference;

import java.io.File;
import java.io.FileInputStream;
import java.io.FileNotFoundException;
import java.io.FileWriter;
import java.io.IOException;
import java.io.InputStream;
import java.sql.Timestamp;
import java.text.SimpleDateFormat;
import java.util.ArrayList;
import java.util.List;
import java.util.Properties;
import java.util.Random;
import java.util.logging.FileHandler;
import java.util.logging.SimpleFormatter;

import org.apache.commons.cli.BasicParser;
import org.apache.commons.cli.CommandLine;
import org.apache.commons.cli.CommandLineParser;
import org.apache.commons.cli.HelpFormatter;
import org.apache.commons.cli.Options;

import br.usp.icmc.labes.mealyInference.utils.IrfanEQOracle;
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
import de.learnlib.api.logging.LearnLogger;
import de.learnlib.api.oracle.EquivalenceOracle;
import de.learnlib.api.oracle.MembershipOracle;
import de.learnlib.api.query.DefaultQuery;
import de.learnlib.api.statistic.StatisticSUL;
import de.learnlib.datastructure.observationtable.ObservationTable;
import de.learnlib.datastructure.observationtable.writer.ObservationTableASCIIWriter;
import de.learnlib.driver.util.MealySimulatorSUL;
import de.learnlib.filter.cache.mealy.MealyCaches;
import de.learnlib.filter.cache.sul.SULCaches;
import de.learnlib.filter.statistic.Counter;
import de.learnlib.filter.statistic.sul.ResetCounterSUL;
import de.learnlib.filter.statistic.sul.SymbolCounterSUL;
import de.learnlib.oracle.equivalence.RandomWordsEQOracle;
import de.learnlib.oracle.equivalence.WpMethodEQOracle;
import de.learnlib.oracle.equivalence.mealy.RandomWalkEQOracle;
import de.learnlib.oracle.membership.SULOracle;
import de.learnlib.util.Experiment.MealyExperiment;
import de.learnlib.util.statistics.SimpleProfiler;
import net.automatalib.automata.transout.MealyMachine;
import net.automatalib.automata.transout.impl.compact.CompactMealy;
import net.automatalib.serialization.dot.GraphDOT;
import net.automatalib.util.automata.Automata;
import net.automatalib.words.Word;

/**
 * @author damasceno
 *
 */
public class Infer_LearnLib {

	public static final String MAX_STEPS_IS_MULT = "maxStepsIsMult";
	public  static final String RESET_STEP_COUNT = "resetStepCount";
	public static final String MAX_STEPS = "maxSteps";
	public static final String RESTART_PROBABILITY = "restartProbability";

	private static final String MAX_TESTS = "maxTests";
	private static final String MIN_LENGTH = "minLength";
	private static final String MAX_LENGTH = "maxLength";
	private static final String MAX_TESTS_IS_MULT = "maxTestsIsMult";
	private static final String MAX_LENGTH_IS_MULT = "maxLengthIsMult";
	private static final String MIN_LENGTH_IS_MULT = "minLengthIsMult";

	
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
	public static final String DEBUG = "debug";
	public static final String INFO = "info";
	
	public static final SimpleDateFormat sdf = new SimpleDateFormat("yyyyMMddHHmmss");
	
	public static final String[] eqMethodsAvailable = {"rndWalk" , "rndWords", "wp", "irfan"};
	public static final String[] closingStrategiesAvailable = {"CloseFirst" , "CloseShortest"};
	private static final String RIVEST_SCHAPIRE_ALLSUFFIXES = "RivestSchapireAllSuffixes";
	public static final String[] cexHandlersAvailable = {"ClassicLStar" , "MalerPnueli", "RivestSchapire", RIVEST_SCHAPIRE_ALLSUFFIXES, "Shahbaz", "Suffix1by1"};
	


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

			// create log 
			LearnLogger logger = LearnLogger.getLogger(Infer_LearnLib.class);

			// set closing strategy
			ClosingStrategy strategy 			= getClosingStrategy(line.getOptionValue(CLOS));

			// set CE processing approach
			ObservationTableCEXHandler handler 	= getCEXHandler(line.getOptionValue(CEXH));
			
			
			// load mealy machine
			CompactMealy<String, Word<String>> mealyss = Utils.getInstance().loadMealyMachine(sul);
			logger.logEvent("SUL name: "+sul.getName());
			logger.logEvent("SUL dir: "+sul.getAbsolutePath());
			logger.logEvent("Output dir: "+out_dir);
			if( line.hasOption( SEED ) ) {
				rnd_seed.setSeed(Long.valueOf(line.getOptionValue(SEED)));
				logger.logEvent("Seed: "+line.getOptionValue(SEED));
			}else{
				rnd_seed.setSeed(tstamp);
				logger.logEvent("Seed: "+Long.toString(tstamp));
			}
			

			Utils.getInstance();
			// SUL simulator
			SUL<String,Word<String>> sulSim = new MealySimulatorSUL<>(mealyss, Utils.OMEGA_SYMBOL);

			// membership oracle for counting queries wraps sul
			StatisticSUL<String, Word<String>>  tot_sym = new SymbolCounterSUL<>("Queries", sulSim);
			StatisticSUL<String, Word<String>>  tot_rst = new ResetCounterSUL <>("Queries", tot_sym);
			
			// SUL for counting queries wraps sul
			SUL<String, Word<String>> the_sul = tot_rst;
			
			// use caching to avoid duplicate queries
			if(line.hasOption(CACHE))  {
				the_sul = SULCaches.createTreeCache(mealyss.getInputAlphabet(), tot_rst);
			}
			
			MembershipOracle<String, Word<Word<String>>> mqOracle = new SULOracle<String, Word<String>>(the_sul);
			
			logger.logEvent("Cache: "+(line.hasOption(CACHE)?"Y":"N"));

			// reuse OT
			MyObservationTable myot = new MyObservationTable();
			if(line.hasOption(OT)){
				myot = OTUtils.getInstance().readOT(obsTable,mealyss.getInputAlphabet());
				ObservationTable<String, Word<Word<String>>> reval_ot = OTUtils.getInstance().revalidateOT2(myot, mqOracle,mealyss);
				new ObservationTableASCIIWriter<>().write(reval_ot, new File(out_dir,sul.getName()+".ot.reval"));
			}
			logger.logEvent("Reused OT: "+(line.hasOption(OT)?obsTable.getName():"N/A"));

			// learning statistics
			logger.logEvent("Reused queries [resets]: " +((Counter)(tot_rst.getStatisticalData())).getCount());
			logger.logEvent("Reused queries [symbols]: "+((Counter)(tot_sym.getStatisticalData())).getCount());
			
			logger.logEvent("ClosingStrategy: "+strategy.toString());
			logger.logEvent("ObservationTableCEXHandler: "+handler.toString());
			
			EquivalenceOracle<MealyMachine<?, String, ?, Word<String>>, String, Word<Word<String>>> eqOracle = null;
			
			if(line.hasOption(EQ)){
				switch (line.getOptionValue(EQ)) {
				case "rndWalk":
					// create RandomWalkEQOracle
					Properties rndWalk_prop = loadRandomWalkProperties();
					double restartProbability = Double.valueOf(rndWalk_prop.getProperty(RESTART_PROBABILITY, "0.05"));
					int maxSteps = Integer.valueOf(rndWalk_prop.getProperty(MAX_STEPS, "1000"));
					if(rndWalk_prop.containsKey(MAX_STEPS_IS_MULT)){
						maxSteps = mealyss.getStates().size()*Integer.valueOf(rndWalk_prop.getProperty(MAX_STEPS_IS_MULT));
					}
					
					boolean resetStepCount = Boolean.valueOf(rndWalk_prop.getProperty(RESET_STEP_COUNT, "true"));;
					eqOracle = new RandomWalkEQOracle<String, Word<String>>(
							the_sul, // sul
							restartProbability,// reset SUL w/ this probability before a step 
							maxSteps, // max steps (overall)
							resetStepCount, // reset step count after counterexample 
							rnd_seed // make results reproducible 
							);
					logger.logEvent("EquivalenceOracle: RandomWalkEQOracle("+restartProbability+","+maxSteps+","+resetStepCount+")");
					break;
				case "rndWords":
					// create RandomWordsEQOracle
					Properties rndWords_prop = loadRandomWordsProperties();
					int maxTests  = Integer.valueOf(rndWords_prop.getProperty(MAX_TESTS, "100"));
					if(rndWords_prop.containsKey(MAX_TESTS_IS_MULT)){
						maxTests = mealyss.getStates().size()*Integer.valueOf(rndWords_prop.getProperty(MAX_TESTS_IS_MULT));
					}
					
					int maxLength = Integer.valueOf(rndWords_prop.getProperty(MAX_LENGTH, "100"));
					if(rndWords_prop.containsKey(MAX_LENGTH_IS_MULT)){
						maxLength = mealyss.getStates().size()*Integer.valueOf(rndWords_prop.getProperty(MAX_LENGTH_IS_MULT));
					}
					
					int minLength = Integer.valueOf(rndWords_prop.getProperty(MIN_LENGTH, "100"));
					if(rndWords_prop.containsKey(MIN_LENGTH_IS_MULT)){
						minLength = mealyss.getStates().size()*Integer.valueOf(rndWords_prop.getProperty(MIN_LENGTH_IS_MULT));
					}
					
					eqOracle = new RandomWordsEQOracle<>(mqOracle, minLength, maxLength, maxTests,rnd_seed);
					logger.logEvent("EquivalenceOracle: RandomWordsEQOracle("+minLength+", "+maxLength+", "+maxTests+")");
					break;
				case "wp":
					int maxDepth = 2;
					eqOracle = new WpMethodEQOracle<>(mqOracle, maxDepth);
					logger.logEvent("EquivalenceOracle: MealyWpMethodEQOracle("+maxDepth+")");
					break;
				case "irfan":
					eqOracle = new IrfanEQOracle<>(the_sul, mealyss.getStates().size(),rnd_seed);
					logger.logEvent("EquivalenceOracle: IrfanEQOracle("+mealyss.getStates().size()+")");
					break;
				default:
					eqOracle = new WpMethodEQOracle<>(mqOracle, 0);
					logger.logEvent("EquivalenceOracle: MealyWpMethodEQOracle("+0+")");
					break;
				}
			}else{
				eqOracle = new WpMethodEQOracle<>(mqOracle, 2);
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
				for (String in : mealyss.getInputAlphabet()) {
					Word wrd = Word.epsilon();
					wrd=wrd.append(in);
					
					initSuffixes.add(wrd);
				}
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


			if(line.hasOption(DEBUG)){
				Counter rounds = new Counter("rounds", "#");
				rounds.increment();
				logger.logPhase("Starting round " + rounds.getCount());
				logger.logPhase("Learning");
				SimpleProfiler.start("Learning");
				learner.startLearning();
				SimpleProfiler.stop("Learning");
				
				File debug_dir = new File(out_dir,"debug/");
				debug_dir.mkdirs();
				boolean done = false;
				CompactMealy<String, Word<String>> hyp = learner.getHypothesisModel();

				// save first hypothesis (unique state w/self-loops)
				File sul_model = new File(debug_dir,sul.getName()+".hyp."+rounds.getCount()+".dot");
				FileWriter fw = new FileWriter(sul_model);
				GraphDOT.write(hyp, hyp.getInputAlphabet(), fw);
				//save first OT
				new ObservationTableASCIIWriter<>().write(learner.getObservationTable(), new File(debug_dir,sul.getName()+".hyp."+rounds.getCount()+".ot"));
				
				while (!done) {
					hyp = learner.getHypothesisModel();
					
					logger.logPhase("Searching for counterexample");
					SimpleProfiler.start("Searching for counterexample");
					DefaultQuery<String, Word<Word<String>>> ce = eqOracle.findCounterExample(hyp, hyp.getInputAlphabet());
					SimpleProfiler.stop("Searching for counterexample");
					if (ce == null) {
						done = true;
						continue;
					}
					
					logger.logCounterexample(ce.getInput().toString());
					
					// next round ...
					rounds.increment();
					logger.logPhase("Starting round " + rounds.getCount());
					logger.logPhase("Learning");
					SimpleProfiler.start("Learning");
					learner.refineHypothesis(ce);
					SimpleProfiler.stop("Learning");
					
					// save current round's hypothesis 
					sul_model = new File(debug_dir,sul.getName()+".hyp."+rounds.getCount()+".dot");
					fw = new FileWriter(sul_model);
					GraphDOT.write(hyp, hyp.getInputAlphabet(), fw);
					//save current round's OT
					new ObservationTableASCIIWriter<>().write(learner.getObservationTable(), new File(debug_dir,sul.getName()+".hyp."+rounds.getCount()+".ot"));
				}
				
				// save last round's hypothesis
				sul_model = new File(out_dir,sul.getName()+".hyp.dot");
				fw = new FileWriter(sul_model);
				GraphDOT.write(hyp, hyp.getInputAlphabet(), fw);
				// save last round's OT
				new ObservationTableASCIIWriter<>().write(learner.getObservationTable(), new File(debug_dir,sul.getName()+".hyp.ot"));
				
				// save sul as dot (i.e., mealyss)
				sul_model = new File(out_dir,sul.getName()+".sul.dot");
				fw = new FileWriter(sul_model);
				GraphDOT.write(mealyss, mealyss.getInputAlphabet(), fw);
				
				logger.logConfig("Rounds: "+rounds.getCount());				
			}else{
				// The experiment will execute the main loop of active learning
				MealyExperiment<String, Word<String>> experiment = new MealyExperiment<String, Word<String>> (learner, eqOracle, mealyss.getInputAlphabet());

				// turn on time profiling
				experiment.setProfile(true);

				// enable logging of models
				experiment.setLogModels(true);
				
				// run experiment
				experiment.run();
				
				logger.logConfig("Rounds: "+experiment.getRounds().getCount());
			}

			// learning statistics
			logger.logStatistic(tot_rst.getStatisticalData());
			logger.logStatistic(tot_sym.getStatisticalData());

			// profiling
			SimpleProfiler.logResults();

			
			if(learner.getHypothesisModel().getStates().size() != mealyss.getStates().size()){
				logger.logConfig("Number of states: NOK");
			}else{
				logger.logConfig("Number of states: OK");
			}
			
			if(line.hasOption(INFO))  {
				logger.logConfig("Info: "+line.getOptionValue(INFO));
			}else{
				logger.logConfig("Info: N/A");
			}

			if(line.hasOption(SOT)){
				File sul_ot = new File(out_dir,sul.getName()+".ot");
				OTUtils.getInstance().writeOT(learner.getObservationTable(), sul_ot);
				new ObservationTableASCIIWriter<>().write(learner.getObservationTable(), new File(out_dir,sul.getName()+".ot.final"));
			}
			
			logger.logConfig("OT suffixes: "+learner.getObservationTable().getSuffixes().toString());
			ArrayList<Word<String>> globalSuffixes = new ArrayList<>();
			Automata.characterizingSet(learner.getHypothesisModel(), learner.getHypothesisModel().getInputAlphabet(), globalSuffixes);
			logger.logConfig("Characterizing set: "+globalSuffixes.toString());
			

		}
		catch( Exception exp ) {
			System.out.println( "Unexpected exception:" + exp.getMessage() );
			// automatically generate the help statement
			formatter.printHelp( "Infer_LearnLib", options );
		}

	}


	private static Properties loadRandomWordsProperties() {
		Properties rndWords = new Properties();
		File rndWords_prop = new File("rndWords.properties");
		
		if(rndWords_prop.exists()){
			InputStream in;
			try {
				in = new FileInputStream(rndWords_prop);
				rndWords.load(in);
				in.close();
			} catch (Exception e) {
				e.printStackTrace();
			}
		}
		
		return rndWords;
	}


	private static Properties loadRandomWalkProperties() {
		Properties rndWalk = new Properties();
		File rndWalk_prop = new File("rndWalk.properties");
		
		if(rndWalk_prop.exists()){
			InputStream in;
			try {
				in = new FileInputStream(rndWalk_prop);
				rndWalk.load(in);
				in.close();
			} catch (Exception e) {
				e.printStackTrace();
			}
		}
		
		return rndWalk;
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
		options.addOption( SUL,  true, "System Under Learning (SUL)" );
		options.addOption( OT,   true, "Load observation table (OT)" );
		options.addOption( OUT,  true, "Set output directory" );
		options.addOption( CLOS, true, "Set closing strategy.\nOptions: {"+String.join(", ", closingStrategiesAvailable)+"}");
		options.addOption( EQ, 	 true, "Set equivalence query generator.\nOptions: {"+String.join(", ", eqMethodsAvailable)+"}");
		options.addOption( CEXH, true, "Set counter example (CE) processing method.\nOptions: {"+String.join(", ", cexHandlersAvailable)+"}");
		options.addOption( CACHE,false,"Use caching.");
		options.addOption( DEBUG,false,"Debugging inference.");
		options.addOption( SEED, true, "Seed used by the random generator");
		options.addOption( INFO, true, "Add extra information as string");
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
		logger = LearnLogger.getLogger(SimpleProfiler.class);
//		logger = LearnLogger.getLogger(Experiment.class);		
		return logger;

	}
}

