package br.usp.icmc.labes.spl;

import java.io.BufferedReader;
import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileReader;

public class SPLConfigUtils {
	public static void main(String[] args) {

//		String[] args={"/home/damasceno/git/learnlib_tests/mealyInference/experiments_mid_low/fsm/configurations_fsm_15.txt",".5"};
		try {
			if(args.length!=2) {
				System.err.println("Required parameters:\t<configuration file path> <number of features>");
				return;
			}
			File file = new File(args[0]);
			if(!file.exists()) throw new FileNotFoundException("Not found:\t"+args[0]);
			if(!(args[1].matches("[0-1]?\\.[0-9]+") || args[1].matches("[0-9]+"))) throw new Exception("Invalid interger number:\t"+args[1]);
			
			BufferedReader br = new BufferedReader(new FileReader(file));
			
			Configurations config = new Configurations();
			String line = br.readLine();
			String brkn_ln[] = null;
			while (br.ready()) {
				line = br.readLine();
				brkn_ln = line.split("\t");
				if(brkn_ln.length != 2) continue;
				
				String a_conf = brkn_ln[0];
				brkn_ln = brkn_ln[1].split(" ");
				for (String a_feat : brkn_ln) {
					config.addConfiguration(a_conf,a_feat);
				}								
			}
			
//			System.out.println(config.toString());
//			System.out.println(config.featuresToString());
			if(args[1].matches("[0-1]?\\.[0-9]+")){
				System.out.println(config.selectRandomConfigsWithPercentFeatures(Double.valueOf(args[1])));
			}else if (args[1].matches("[0-9]+")){
				System.out.println(config.selectRandomConfigsWithNFeatures(Integer.valueOf(args[1])));
			}
			
			
		} catch (Exception e) {
			e.printStackTrace();
		}
		
	}
}
