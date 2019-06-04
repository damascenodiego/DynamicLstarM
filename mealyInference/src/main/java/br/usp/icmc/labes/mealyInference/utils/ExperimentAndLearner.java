package br.usp.icmc.labes.mealyInference.utils;

import de.learnlib.algorithms.ttt.mealy.TTTLearnerMealy;
import de.learnlib.datastructure.observationtable.OTLearner.OTLearnerMealy;
import de.learnlib.util.Experiment.MealyExperiment;
import net.automatalib.words.Word;

public class ExperimentAndLearner {
	
	private OTLearnerMealy learner;
	private MealyExperiment experiment;
	private OTLearnerMealy learner_ttt;

	public ExperimentAndLearner(OTLearnerMealy learner, MealyExperiment experiment) {
		this.learner = learner;
		this.experiment = experiment;
	}
	
	public ExperimentAndLearner(TTTLearnerMealy tttlearner, MealyExperiment experiment) {
		this.learner_ttt = learner;
		this.experiment = experiment;
	}

	public MealyExperiment getExperiment() {
		return experiment;
	}
	
	public OTLearnerMealy getLearner() {
		return learner;
	}
	
	public OTLearnerMealy getLearner_TTT() {
		return learner_ttt;
	}
}
