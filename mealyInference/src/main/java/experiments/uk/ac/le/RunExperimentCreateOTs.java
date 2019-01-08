package experiments.uk.ac.le;

import java.io.File;
import java.io.IOException;
import java.sql.Timestamp;
import java.text.SimpleDateFormat;
import java.util.ArrayList;
import java.util.Date;
import java.util.List;
import java.util.Random;

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
import de.learnlib.datastructure.observationtable.writer.ObservationTableASCIIWriter;
import de.learnlib.driver.util.MealySimulatorSUL;
import de.learnlib.filter.statistic.sul.ResetCounterSUL;
import de.learnlib.filter.statistic.sul.SymbolCounterSUL;
import de.learnlib.oracle.equivalence.WMethodEQOracle;
import de.learnlib.oracle.membership.SULOracle;
import de.learnlib.util.Experiment.MealyExperiment;
import net.automatalib.automata.transout.MealyMachine;
import net.automatalib.incremental.mealy.tree.IncrementalMealyTreeBuilder;
import net.automatalib.util.automata.Automata;
import net.automatalib.words.Alphabet;
import net.automatalib.words.Word;

public class RunExperimentCreateOTs {

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

	
	public static void main(String[] args) {
		// output directory
		String out_dir_string = "logDir/";
		log_dir = new File(out_dir_string );
		log_dir.mkdir();

		// random seed
		rnd_seed = new Random(tstamp);
		// timestamp
		timestamp = new Timestamp(tstamp);


		//Set this before the logger start.
		System.setProperty("logdir", out_dir_string);
		System.setProperty("logtstamp", sdf.format(timestamp).replaceAll("/", "_"));

		logger = LearnLogger.getLogger(RunExperimentCreateOTs.class);

		try {
//			list_of_list_of_suls.add(Experiments.NORDSEC16_CLI_load());
			list_of_list_of_suls.add(Experiments.NORDSEC16_SRV_load());
			list_of_list_of_suls.add(Experiments.QUIC_PROTOCOL_load());
			list_of_list_of_suls.add(Experiments.SSH_IMPLEM_load());
			list_of_list_of_suls.add(Experiments.EDENTIFIER2_IMPLEM_load());
//			list_of_list_of_suls.add(Experiments.TCP_CLI_IMPLEM_load());
//			list_of_list_of_suls.add(Experiments.TCP_SRV_IMPLEM_load());

			out_dir = new File(log_dir,sdf.format(new Date(tstamp))); out_dir.mkdirs();
			for (List<MealyPlusFile> list_of_suls : list_of_list_of_suls) {
				for (MealyPlusFile sul_i : list_of_suls) {
					logger.logEvent("Start creating OT: "+sul_i.getFile().getName());
					createInitialSetsFromFile(sul_i);
					logger.logEvent("End creating OT: "+sul_i.getFile().getName());
				}
			}
		}catch(Exception e) {
			e.printStackTrace();
		}
	}

	protected static void createInitialSetsFromFile(MealyPlusFile the_sul) throws IOException {
		File sul_ot = new File(log_dir,the_sul.getFile().getName()+".reuse");

		// Empty list of prefixes 
		ArrayList<Word<String>> initPrefixes = new ArrayList<Word<String>>();
		initPrefixes.add(Word.epsilon());
		// Empty list of suffixes => minimal compliant setinitCes
		ArrayList<Word<String>> initSuffixes = new ArrayList<Word<String>>();
		
		for (String e : the_sul.getMealyss().getInputAlphabet()) {
			Word<String>  w = Word.epsilon(); 
			w=w.append(e);
			initSuffixes.add(w);			
		}
//		initSuffixes.addAll(Automata.characterizingSet(the_sul.getMealyss(), the_sul.getMealyss().getInputAlphabet()));
		
		SUL<String,Word<String>> sulSim = new MealySimulatorSUL<>(the_sul.getMealyss(), Utils.OMEGA_SYMBOL);
		Alphabet<String> alphabet = the_sul.getMealyss().getInputAlphabet();

		// set closing strategy and CE processing approach
		ClosingStrategy<Object, Object> strategy 			= ClosingStrategies.CLOSE_FIRST;
		ObservationTableCEXHandler<Object, Object> handler 	= ObservationTableCEXHandlers.CLASSIC_LSTAR;

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
//		eqOracle1 = new RandomWMethodEQOracle<>(oracleForEQoracle1, 2, 50, 20000);
//		eqOracle1 = new RandomWalkEQOracle<>(sulSim, 0.5, 20000, new Random());
		eqOracle1 = new WMethodEQOracle<>(oracleForEQoracle1, 2);
//		eqOracle1 = new CompleteExplorationEQOracle(oracleForEQoracle1, the_sul.getMealyss().getStates().size());

		// The experiment will execute the main loop of active learning
		MealyExperiment<String, Word<String>> experiment1 = new MealyExperiment<String, Word<String>> (learner1, eqOracle1, alphabet);
		// turn on time profiling
		experiment1.setProfile(true);
		// enable logging of modelsOT
		experiment1.setLogModels(true);
		// run experiment
		experiment1.run();

		OTUtils.getInstance().writeOT(learner1.getObservationTable(), sul_ot);
		Word<String> sepWord = Automata.findSeparatingWord(the_sul.getMealyss(), learner1.getHypothesisModel(), the_sul.getMealyss().getInputAlphabet());			
		if(sepWord == null){
			logger.logConfig("Equivalent: OK");
			new ObservationTableASCIIWriter<>().write(learner1.getObservationTable(),new File(out_dir,the_sul.getFile().getName()+".ot"));
		}else{
			logger.logConfig("Equivalent: NOK");
			System.err.println("Equivalent: NOK");
			System.exit(1);
			new ObservationTableASCIIWriter<>().write(learner1.getObservationTable(),new File(out_dir,the_sul.getFile().getName()+".otERR"));
		}		
	}


}
