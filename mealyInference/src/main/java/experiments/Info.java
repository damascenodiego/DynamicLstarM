package experiments;

public class Info {
	public static void main(String[] args) {
		System.err.println("Run one of the following commands:");
		
		System.out.println("java -cp runcomparison.jar experiments.br.usp.icmc.labes.ExperimentNordsec16CreateOTs");
		System.out.println("java -cp runcomparison.jar experiments.br.usp.icmc.labes.ExperimentNordsec16 <numberOfRepetitions>");

		
		System.out.println("java -cp runcomparison.jar experiments.uk.ac.le.RunExperimentCreateOTs");
		System.out.println("java -cp runcomparison.jar experiments.uk.ac.le.RunExperimentWMethod");
		System.out.println("java -cp runcomparison.jar experiments.uk.ac.le.RunExperimentRandomWMethod <numberOfRepetitions>");
		System.out.println("java -cp runcomparison.jar experiments.uk.ac.le.RunExperimentRandomWMethodQsize <numberOfRepetitions>");
		

		

		
	}
}
