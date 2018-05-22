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
import de.learnlib.filter.cache.sul.SULCache;
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

	public static final String SOT = "sot";
	public static final String SUL = "sul";
	public static final String HELP = "help";
	public static final String HELP_SHORT = "h";
	public static final String OT = "ot";
	public static final String PROJ = "proj";
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

			// IncrementalMealyBuilder for caching EQs and MQs together
			IncrementalMealyBuilder<String,Word<String>> cbuilder = new IncrementalMealyTreeBuilder<>(mealyss.getInputAlphabet());
						
			// Counters for MQs 
			StatisticSUL<String, Word<String>>  mq_sym = new SymbolCounterSUL<>("MQ", sulSim);
			StatisticSUL<String, Word<String>>  mq_rst = new ResetCounterSUL <>("MQ", mq_sym);
			
			// SUL for counting queries wraps sul
			SUL<String, Word<String>> mq_sul = mq_rst;
			
			// use caching to avoid duplicate queries
			if(line.hasOption(CACHE))  {
				// SULs for associating the IncrementalMealyBuilder 'cbuilder' to MQs
				mq_sul = new SULCache<>(cbuilder, mq_rst);
			}
			
			MembershipOracle<String, Word<Word<String>>> mqOracle = new SULOracle<String, Word<String>>(mq_sul);
			
			logger.logEvent("Cache: "+(line.hasOption(CACHE)?"Y":"N"));

			// reuse OT
			MyObservationTable myot = new MyObservationTable();
			if(line.hasOption(OT)){
				logger.logEvent("Revalidating OT: Start readOT()");
				if(line.hasOption(PROJ)){
					myot = OTUtils.getInstance().readOT(obsTable,mealyss.getInputAlphabet(),true);
				}else{
					myot = OTUtils.getInstance().readOT(obsTable,mealyss.getInputAlphabet());	
				}
				logger.logEvent("Revalidating OT: End readOT()");
				
				logger.logEvent("Revalidating OT: Start revalidateOT2()");
				ObservationTable<String, Word<Word<String>>> reval_ot = OTUtils.getInstance().revalidateOT2(myot, mqOracle,mealyss);
				logger.logEvent("Revalidating OT: End revalidateOT2()");
				new ObservationTableASCIIWriter<>().write(reval_ot, new File(out_dir,sul.getName()+".ot.reval"));
			}
			logger.logEvent("Reused OT: "+(line.hasOption(OT)?obsTable.getName():"N/A"));

			// learning statistics
			logger.logEvent("Reused queries [resets]: " +((Counter)(mq_rst.getStatisticalData())).getCount());
			logger.logEvent("Reused queries [symbols]: "+((Counter)(mq_sym.getStatisticalData())).getCount());
			
			logger.logEvent("ClosingStrategy: "+strategy.toString());
			logger.logEvent("ObservationTableCEXHandler: "+handler.toString());
			
			// Counters for EQs
			StatisticSUL<String, Word<String>>  eq_sym = new SymbolCounterSUL<>("EQ", sulSim);
			StatisticSUL<String, Word<String>>  eq_rst = new ResetCounterSUL <>("EQ", eq_sym);
			
			// SUL for counting queries wraps sul
			SUL<String, Word<String>> eq_sul = eq_rst;

			// use caching to avoid duplicate queries
			if(line.hasOption(CACHE))  {
				// SULs for associating the IncrementalMealyBuilder 'cbuilder' to EQs
				eq_sul = new SULCache<>(cbuilder, eq_rst);
			}
			
			MembershipOracle<String,Word<Word<String>>> oracleForEQoracle = new SULOracle<>(eq_sul);
			
			EquivalenceOracle<MealyMachine<?, String, ?, Word<String>>, String, Word<Word<String>>> eqOracle = null;
			
			
			if(line.hasOption(EQ)){
				LearnLibProperties learn_props = LearnLibProperties.getInstance();
				switch (line.getOptionValue(EQ)) {
				case "rndWalk":
					// create RandomWalkEQOracle
					double restartProbability = learn_props.getRndWalk_restartProbability();
					int maxSteps = learn_props.getRndWalk_maxSteps();
					if(learn_props.hasProperty(LearnLibProperties.RND_WALK+LearnLibProperties.MAX_STEPS_IS_MULT)){
						maxSteps = mealyss.getStates().size()*learn_props.getRndWalk_maxStepsIsMult();
					}
					
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
					if(learn_props.hasProperty(LearnLibProperties.RND_WORDS+LearnLibProperties.MAX_TESTS_IS_MULT)){
						maxTests = mealyss.getStates().size()*learn_props.getRndWords_maxTestsIsMult();
					}
					
					int maxLength = learn_props.getRndWords_maxLength();
					if(learn_props.hasProperty(LearnLibProperties.MAX_LENGTH_IS_MULT)){
						maxLength = mealyss.getStates().size()*learn_props.getRndWords_maxLengthIsMult();
					}
					
					int minLength = learn_props.getRndWords_minLength();
					if(learn_props.hasProperty(LearnLibProperties.MIN_LENGTH_IS_MULT)){
						minLength = mealyss.getStates().size()*learn_props.getRndWords_minLengthIsMult();
					}
					
					eqOracle = new RandomWordsEQOracle<>(oracleForEQoracle, minLength, maxLength, maxTests,rnd_seed);
					logger.logEvent("EquivalenceOracle: RandomWordsEQOracle("+minLength+", "+maxLength+", "+maxTests+")");
					break;
				case "wp":
					int maxDepth = learn_props.getWp_maxDepth();
					eqOracle = new WpMethodEQOracle<>(oracleForEQoracle, maxDepth);
					logger.logEvent("EquivalenceOracle: MealyWpMethodEQOracle("+maxDepth+")");
					break;
				case "irfan":
					eqOracle = new IrfanEQOracle<>(eq_sul, mealyss.getStates().size(),rnd_seed);
					if(learn_props.hasProperty(LearnLibProperties.IRFAN+LearnLibProperties.MAX_TESTS_IS_MULT)){
						((IrfanEQOracle)eqOracle).set_maxResetsIsMult(learn_props.getIrfan_maxTestsIsMult());
					}else if(learn_props.hasProperty(LearnLibProperties.IRFAN+LearnLibProperties.MAX_TESTS)){
						((IrfanEQOracle)eqOracle).set_maxResets(learn_props.getIrfan_maxTests());
					}
					if(learn_props.hasProperty(LearnLibProperties.IRFAN+LearnLibProperties.MAX_LENGTH_IS_MULT)){
						((IrfanEQOracle)eqOracle).set_maxLengthIsMult(Integer.valueOf(learn_props.getIrfan_maxLengthIsMult()));
					}else if(learn_props.hasProperty(LearnLibProperties.IRFAN+LearnLibProperties.MAX_LENGTH)){
						((IrfanEQOracle)eqOracle).set_maxLength(learn_props.getIrfan_maxLength());
					}
					logger.logEvent("EquivalenceOracle: IrfanEQOracle("+mealyss.getStates().size()+","+((IrfanEQOracle)eqOracle).getMaxLengthCE()+","+((IrfanEQOracle)eqOracle).getMaxResets()+")");
					break;
				default:
					eqOracle = new WpMethodEQOracle<>(oracleForEQoracle, 0);
					logger.logEvent("EquivalenceOracle: MealyWpMethodEQOracle("+0+")");
					break;
				}
			}else{
				eqOracle = new WpMethodEQOracle<>(oracleForEQoracle, 2);
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
			logger.logStatistic(mq_rst.getStatisticalData());
			logger.logStatistic(mq_sym.getStatisticalData());
			logger.logStatistic(eq_rst.getStatisticalData());
			logger.logStatistic(eq_sym.getStatisticalData());

			// profiling
			SimpleProfiler.logResults();

			Word<String> sepWord = Automata.findSeparatingWord(mealyss, learner.getHypothesisModel(), mealyss.getInputAlphabet());			
			if(sepWord == null){
				logger.logConfig("Equivalent: OK");
			}else{
				logger.logConfig("Equivalent: NOK");
			}
			
			logger.logConfig("SUL total states: "+mealyss.getStates().size());
			logger.logConfig("SUL total inputs: "+mealyss.getInputAlphabet().size());
			
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
			System.err.println( "Unexpected Exception:" + exp.getMessage() );
			exp.printStackTrace();
			// automatically generate the help statement
			formatter.printHelp( "Infer_LearnLib", options );
		}

	}


	private static Properties loadIrfanEQProperties() {
		Properties props = new Properties();
		File rndWords_prop = new File("irfan.properties");
		
		if(rndWords_prop.exists()){
			InputStream in;
			try {
				in = new FileInputStream(rndWords_prop);
				props.load(in);
				in.close();
			} catch (Exception e) {
				e.printStackTrace();
			}
		}
		
		return props;
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
		options.addOption( PROJ, false, "Revalidate suffix set using projection. (Default: truncate at first invalid symbol)" );
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

