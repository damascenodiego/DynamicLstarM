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
	public static final String RESET_STEPS_COUNT = "resetStepsCount";
	
	public static final String RESTART_PROBABILITY = "restartProbability";

	public static final String MAX_TESTS  			= "maxTests";
	public static final String BOUND  				= "bound";
	public static final String MAX_LENGTH 			= "maxLength";
	
	public static final String MIN_LENGTH 			= "minLength";
	public static final String RND_LENGTH 			= "rndLength";
	public static final String MAX_DEPTH 			= "maxDepth";
	
	public static final String REVAL_MODE 			= "reval_using";
	public static final String REVAL_OT 			= "OT";
	public static final String REVAL_LEARNER		= "Learner";

	public static final String PROJECTION = "projection";
	
	public static final String RND_WALK = "rndWalk_";
	public static final String RND_WORDS = "rndWords_";
	public static final String WP 	 = "wp_";
	public static final String W 	 = "w_";
	public static final String WEQ 	 = "weq_";

	private Properties props;
	
	private static LearnLibProperties instance;

	private int rndWalk_maxSteps;
	private int rndWords_minLength;
	private double rndWalk_restartProbability;
	private boolean rndWalk_resetStepCount;
	
	private String revalMode;

	private int rndWords_maxTests;
	private int rndWords_maxLength;
	
	private int weq_minLen;
	private int weq_rndLen;
	private int weq_bound;
	
	private int w_maxDepth;
	
	private boolean projection;
	
	private LearnLibProperties() { loadProperties(); }
	
	public static LearnLibProperties getInstance() {
		if(instance == null) instance = new LearnLibProperties();
		return instance;
	}
	
	
	public void loadProperties(){
		File f = new File(".learnlib");
		loadProperties(f);
	}
	public void loadProperties(File f){
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
		projection = Boolean.valueOf(props.getProperty(PROJECTION, "false"));
		
		rndWalk_restartProbability 	= Double .valueOf(props.getProperty(RND_WALK+RESTART_PROBABILITY, "0.05"));
		rndWalk_maxSteps 			= Integer.valueOf(props.getProperty(RND_WALK+MAX_STEPS, "100"));
		rndWalk_resetStepCount 		= Boolean.valueOf(props.getProperty(RND_WALK+RESET_STEPS_COUNT, "true"));
		
		rndWords_minLength 			= Integer.valueOf(props.getProperty(RND_WORDS+MIN_LENGTH, "100"));
		rndWords_maxLength 			= Integer.valueOf(props.getProperty(RND_WORDS+MAX_LENGTH, "100"));
		rndWords_maxTests  			= Integer.valueOf(props.getProperty(RND_WORDS+MAX_TESTS, "100"));

		weq_minLen 	= Integer.valueOf(props.getProperty(WEQ+MIN_LENGTH,"2"));
		weq_rndLen 	= Integer.valueOf(props.getProperty(WEQ+RND_LENGTH,"20"));
		weq_bound 	= Integer.valueOf(props.getProperty(WEQ+MAX_TESTS,"200000"));
		
		w_maxDepth 				= Integer.valueOf(props.getProperty(W+MAX_DEPTH,"2"));
		
		revalMode				= String.valueOf(props.getProperty(REVAL_MODE,REVAL_LEARNER));
		

	}
	
	public double getRndWalk_restartProbability() {
		return rndWalk_restartProbability;
	}
	
	public int getRndWalk_maxSteps() {
		return rndWalk_maxSteps;
	}
	
	public boolean getRndWalk_resetStepsCount() {
		return rndWalk_resetStepCount;
	}

	public int getRndWords_minLength() {
		return rndWords_minLength;
	}

	public int getRndWords_maxTests() {
		return rndWords_maxTests;
	}

	public int getRndWords_maxLength() {
		return rndWords_maxLength;
	}
	
	public int getW_maxDepth() {
		return w_maxDepth;
	}
	
	public String getRevalMode() {
		return revalMode;
	}

	public int getWeq_rndLen() {
		return weq_rndLen;
	}

	public int getWeq_bound() {
		return weq_bound;
	}

	public int getWeq_minLen() {
		return weq_minLen;
	}

	public void setProjection(boolean projection) {
		this.projection = projection;
	}
	
	public boolean getProjection() {
		return this.projection;
	}
	
}
