package br.usp.icmc.labes.mealyInference.utils;

import java.io.File;
import java.io.FileInputStream;
import java.io.InputStream;
import java.util.Properties;

import de.learnlib.algorithms.lstar.ce.ObservationTableCEXHandler;
import de.learnlib.algorithms.lstar.ce.ObservationTableCEXHandlers;
import de.learnlib.algorithms.lstar.closing.ClosingStrategies;
import de.learnlib.algorithms.lstar.closing.ClosingStrategy;

public class LearnLibProperties {
	
	public static final String MAX_STEPS 		 = "maxSteps";
	public static final String MAX_STEPS_IS_MULT = "maxStepsIsMult";
	public static final String RESET_STEPS_COUNT = "resetStepsCount";
	
	public static final String RESTART_PROBABILITY = "restartProbability";

	public static final String MAX_TESTS  			= "maxTests";
	public static final String MAX_TESTS_IS_MULT  	= "maxTestsIsMult";
	public static final String MIN_LENGTH 			= "minLength";
	public static final String MAX_LENGTH_IS_MULT 	= "maxLengthIsMult";
	public static final String MAX_LENGTH 			= "maxLength";
	public static final String MIN_LENGTH_IS_MULT 	= "minLengthIsMult";
	public static final String MAX_DEPTH 			= "maxDepth";
	
	public static final String REVAL_MODE 			= "reval_using";
	public static final String REVAL_OT 			= "OT";
	public static final String REVAL_LEARNER		= "Learner";
	public static final String REVAL_CEXH = "reval_cexh";
	public static final String REVAL_CLOS = "reval_clos";
	
	
	public static final String RND_WALK = "rndWalk_";
	public static final String RND_WORDS = "rndWords_";
	public static final String IRFAN 	 = "irfan_";
	public static final String WP 	 = "wp_";

	private Properties props;
	
	private static LearnLibProperties instance;

	private double rndWalk_restartProbability;
	private int rndWalk_maxSteps;
	private int rndWalk_maxStepsIsMult;
	private boolean rndWalk_resetStepCount;
	private boolean rndWords_resetStepsCount;
	private int rndWords_minLength;
	
	private String revalMode;

	private int rndWords_maxTests;
	private int rndWords_minLengthIsMult;
	private int rndWords_maxLengthIsMult;
	private int rndWords_maxTestsIsMult;
	private int rndWords_maxLength;
	private int irfan_maxLength;
	private int irfan_maxLengthIsMult;
	private int irfan_maxTests;
	private int irfan_maxTestsIsMult;
	private int wp_maxDepth;
	private ClosingStrategy revalClos;
	private ObservationTableCEXHandler revalCexh;
	
	
	
	
	
	private LearnLibProperties() { loadProperties(); }
	
	public static LearnLibProperties getInstance() {
		if(instance == null) instance = new LearnLibProperties();
		return instance;
	}
	
	public void loadProperties(){
		File f = new File(".learnlib");
		if(props!=null){
			props.clear();
		}else{
			props = new Properties();
		}
		
		if(f.exists()){
			InputStream in;
			try {
				in = new FileInputStream(f);
				props.load(in);
				in.close();
			} catch (Exception e) {
				e.printStackTrace();
			}
		}
		rndWalk_restartProbability 	=  Double.valueOf(props.getProperty(RND_WALK+RESTART_PROBABILITY, "0.05"));
		rndWalk_maxSteps 			= Integer.valueOf(props.getProperty(RND_WALK+MAX_STEPS, "100"));
		rndWalk_maxStepsIsMult 		= Integer.valueOf(props.getProperty(RND_WALK+MAX_STEPS_IS_MULT, "2"));
		rndWalk_resetStepCount 		= Boolean.valueOf(props.getProperty(RND_WALK+RESET_STEPS_COUNT, "true"));
		
		rndWords_resetStepsCount 	= Boolean.valueOf(props.getProperty(RND_WORDS+RESET_STEPS_COUNT, "true"));
		rndWords_minLength 			= Integer.valueOf(props.getProperty(RND_WORDS+MIN_LENGTH, "100"));
		rndWords_maxLength 			= Integer.valueOf(props.getProperty(RND_WORDS+MAX_LENGTH, "100"));
		rndWords_maxTests  			= Integer.valueOf(props.getProperty(RND_WORDS+MAX_TESTS, "100"));
		rndWords_minLengthIsMult 	= Integer.valueOf(props.getProperty(RND_WORDS+MIN_LENGTH_IS_MULT,"2"));
		rndWords_maxLengthIsMult 	= Integer.valueOf(props.getProperty(RND_WORDS+MAX_LENGTH_IS_MULT,"2"));
		rndWords_maxTestsIsMult 	= Integer.valueOf(props.getProperty(RND_WORDS+MAX_TESTS_IS_MULT,"2"));

		irfan_maxTestsIsMult 	= Integer.valueOf(props.getProperty(IRFAN+MAX_TESTS_IS_MULT,"2"));
		irfan_maxTests 			= Integer.valueOf(props.getProperty(IRFAN+MAX_TESTS,"100"));
		irfan_maxLengthIsMult 	= Integer.valueOf(props.getProperty(IRFAN+MAX_LENGTH_IS_MULT,"2"));
		irfan_maxLength 		= Integer.valueOf(props.getProperty(IRFAN+MAX_LENGTH,"100"));
		
		wp_maxDepth 			= Integer.valueOf(props.getProperty(WP+MAX_DEPTH,"2"));
		
		revalMode				= String.valueOf(props.getProperty(REVAL_MODE,REVAL_LEARNER));
		
		
		if(props.containsKey(REVAL_CEXH)){
			String key = props.getProperty(REVAL_CEXH);
			switch (key) {
			case "RIVEST_SCHAPIRE":
				revalCexh = ObservationTableCEXHandlers.RIVEST_SCHAPIRE;
				break;
			case "RIVEST_SCHAPIRE_ALLSUFFIXES":
				revalCexh = ObservationTableCEXHandlers.RIVEST_SCHAPIRE_ALLSUFFIXES;
				break;
			case "SUFFIX1BY1":
				revalCexh = ObservationTableCEXHandlers.SUFFIX1BY1;
				break;
			default:
				revalCexh = ObservationTableCEXHandlers.RIVEST_SCHAPIRE;
				break;
			}
		}else{
			revalCexh = ObservationTableCEXHandlers.RIVEST_SCHAPIRE;
		}
		
		if(props.containsKey(REVAL_CLOS)){
			String key = props.getProperty(REVAL_CLOS);
			switch (key) {
			case "CLOSE_FIRST":
				revalClos = ClosingStrategies.CLOSE_FIRST;
				break;
			case "CLOSE_SHORTEST":
				revalClos = ClosingStrategies.CLOSE_SHORTEST;
				break;
			case "CLOSE_LEX_MIN":
				revalClos = ClosingStrategies.CLOSE_LEX_MIN;
				break;
			default:
				revalClos = ClosingStrategies.CLOSE_FIRST;
				break;
			}
		}else{
			revalClos = ClosingStrategies.CLOSE_FIRST;
		}
		
	}
	
	public double getRndWalk_restartProbability() {
		return rndWalk_restartProbability;
	}
	
	public int getRndWalk_maxSteps() {
		return rndWalk_maxSteps;
	}
	
	public int getRndWalk_maxStepsIsMult() {
		return rndWalk_maxStepsIsMult;
	}
	
	public boolean getRndWalk_resetStepsCount() {
		return rndWalk_resetStepCount;
	}

	public boolean getRndWords_resetStepsCount() {
		return rndWords_resetStepsCount;
	}

	public int getRndWords_minLength() {
		return rndWords_minLength;
	}

	public int getRndWords_maxTests() {
		return rndWords_maxTests;
	}

	public int getRndWords_minLengthIsMult() {
		return rndWords_minLengthIsMult;
	}

	public int getRndWords_maxLengthIsMult() {
		return rndWords_maxLengthIsMult;
	}

	public int getRndWords_maxTestsIsMult() {
		return rndWords_maxTestsIsMult;
	}

	public int getRndWords_maxLength() {
		return rndWords_maxLength;
	}
	
	public int getIrfan_maxLength() {
		return irfan_maxLength;
	}

	public int getIrfan_maxLengthIsMult() {
		return irfan_maxLengthIsMult;
	}
	
	public int getIrfan_maxTests() {
		return irfan_maxTests;
	}
	
	public int getIrfan_maxTestsIsMult() {
		return irfan_maxTestsIsMult;
	}
	
	public int getWp_maxDepth() {
		return wp_maxDepth;
	}
	
	public String getRevalMode() {
		return revalMode;
	}
	
	public ObservationTableCEXHandler getRevalCexh() {
		return revalCexh;
	}
	
	public ClosingStrategy getRevalClos() {
		return revalClos;
	}
	
	public boolean hasProperty(String key){
		return props.containsKey(key);
	}

}
