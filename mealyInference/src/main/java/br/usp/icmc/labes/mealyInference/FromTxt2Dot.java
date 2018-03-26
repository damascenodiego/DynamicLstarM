package br.usp.icmc.labes.mealyInference;

import java.io.BufferedReader;
import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.io.InputStreamReader;

import br.usp.icmc.labes.mealyInference.utils.Utils;
import net.automatalib.automata.transout.impl.compact.CompactMealy;
import net.automatalib.serialization.dot.GraphDOT;
import net.automatalib.words.Word;

public class FromTxt2Dot {
	
	public static void main(String[] args) {
		try {
			// load mealy machine
			File fsm = new File("/home/damasceno/Dropbox/Apps/ShareLaTeX/PhD research diary/images/exp01/logback/log_experiments_mid_low/fsm/fsm_15_352.txt");
			CompactMealy<String, Word<String>> mealy = Utils.getInstance().loadMealyMachine(fsm);
			Utils.removeSelfLoops(mealy);			
			
			// save sul as dot (i.e., mealyss)
			File sul_model = new File(fsm.getParentFile(),fsm.getName()+".dot");
			FileWriter fw = new FileWriter(sul_model);
			GraphDOT.write(mealy, mealy.getInputAlphabet(), fw);
			
			String[] commands0 = {"dot","-T", "png", "-o", sul_model.getParentFile().getAbsolutePath()+"/"+fsm.getName()+".png", sul_model.getAbsolutePath()};
			System.out.println(String.join("\n",commands0));
			String result0 = getProcessOutput(commands0);
			System.out.println(result0);
		} catch (Exception e) {
			e.printStackTrace();
		}
	}
	
	public static String getProcessOutput(String[] commands) throws IOException, InterruptedException
    {
        ProcessBuilder processBuilder = new ProcessBuilder(commands);

        processBuilder.redirectErrorStream(true);

        Process process = processBuilder.start();
        StringBuilder processOutput = new StringBuilder();

        try (BufferedReader processOutputReader = new BufferedReader(
                new InputStreamReader(process.getInputStream()));)
        {
            String readLine;

            while ((readLine = processOutputReader.readLine()) != null)
            {
                processOutput.append(readLine + System.lineSeparator());
            }

            process.waitFor();
        }

        return processOutput.toString().trim();
    }

}
