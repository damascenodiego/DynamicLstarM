package br.usp.icmc.labes.mealyInference.utils;

import java.io.BufferedWriter;
import java.io.File;
import java.io.FileWriter;
import java.util.ArrayList;
import java.util.Collections;
import java.util.Comparator;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.SortedSet;
import java.util.TreeSet;

import org.apache.commons.cli.BasicParser;
import org.apache.commons.cli.CommandLine;
import org.apache.commons.cli.CommandLineParser;
import org.apache.commons.cli.HelpFormatter;
import org.apache.commons.cli.Options;

import net.automatalib.automata.transout.impl.compact.CompactMealy;
import net.automatalib.automata.transout.impl.compact.CompactMealyTransition;
import net.automatalib.commons.util.comparison.CmpUtil;
import net.automatalib.util.automata.Automata;
import net.automatalib.words.Alphabet;
import net.automatalib.words.Word;

public class BuildOT {

	private static final String SUL = "sul";
	private static final String HELP = "h";
	private static final String SUL_AS_KISS = "kiss";
	private static final String SUL_AS_DOT = "dot";
	//private static final String MK_OT = "ot";

	public static void main(String[] args) {

		// create the command line parser
		CommandLineParser parser = new BasicParser();
		// create the Options
		Options options = createOptions();
		// automatically generate the help statement
		HelpFormatter formatter = new HelpFormatter();

		try {
			// parse the command line arguments
			CommandLine line = parser.parse( options, args);
			
			if(!line.hasOption(SUL)) throw new Exception("The model of a SUL is required!");
			
			File f = new File(line.getOptionValue(SUL));
			
			CompactMealy<String, Word<String>> mealy = null;
			
			if(line.hasOption(SUL_AS_DOT)) {
				mealy = Utils.getInstance().loadMealyMachineFromDot(f);
			}else if(line.hasOption(SUL_AS_KISS)) {
				mealy = Utils.getInstance().loadMealyMachine(f);				
			}else {
				mealy = Utils.getInstance().loadMealyMachine(f);
			}
			
			Utils.getInstance().saveMealyMachineAsKiss(mealy, new File(f.getParent(),f.getName().replaceAll("\\.[(dot)(txt)(kiss)]$", "")+".kiss"));			
			Map<Integer, Word<String>> accessStringMap = new HashMap<>();
			Integer initState = mealy.getInitialState();
			accessStringMap.put(initState, Word.epsilon());
			
			dfs(mealy,initState,accessStringMap);
			
			List<Word<String>> accessString = new ArrayList<>(accessStringMap.values());
			Alphabet<String> abc = mealy.getInputAlphabet();
			Collections.sort(accessString, new Comparator<Word<String>>() {
	            @Override
	            public int compare(Word<String> o1, Word<String> o2) { return CmpUtil.lexCompare(o1, o2, abc ); }
	        });
			
			//System.out.println(accessString);
			
			BufferedWriter bw_ot = new BufferedWriter(new FileWriter(new File(f.getParent(),f.getName().replaceAll("\\.[(dot)(txt)(kiss)]$", "")+".ot")));

			for (int i = 1; i < accessString.size(); i++) {
				bw_ot.append(";");
				bw_ot.append(accessString.get(i).getSymbol(0));
				for (int j = 1; j < accessString.get(i).size(); j++) {
					bw_ot.append(",");
					bw_ot.append(accessString.get(i).getSymbol(j));
				}
			}
			bw_ot.append("\n");
			List<Word<String>> w_set = Automata.characterizingSet(mealy, mealy.getInputAlphabet());
			
			for (int i = 1; i < w_set.size(); i++) {
				bw_ot.append(";");
				bw_ot.append(w_set.get(i).getSymbol(0));
				for (int j = 1; j < w_set.get(i).size(); j++) {
					bw_ot.append(",");
					bw_ot.append(w_set.get(i).getSymbol(j));
				}
			}
			
			bw_ot.close();
			

		} catch (Exception e) {
			e.printStackTrace();
			formatter.printHelp("BuildOT", options);
		}
	}

	private static void dfs(CompactMealy<String, Word<String>> mealy, Integer si,
			Map<Integer, Word<String>> accessString) {
		for (String in : mealy.getInputAlphabet()) {
			CompactMealyTransition<Word<String>> tr = mealy.getTransition(si, in);
			if(accessString.containsKey(tr.getSuccId())) continue;
			accessString.put(tr.getSuccId(),accessString.get(si).append(in));
			dfs(mealy, tr.getSuccId(), accessString);			
		}		
	}

	private static Options createOptions() {
		/// create the Options
		Options options = new Options();
		options.addOption( SUL,  true, "System Under Learning (SUL)" );
		options.addOption( SUL_AS_DOT,   false, "SUL is formatted as dot file" );
		options.addOption( SUL_AS_KISS,  false, "SUL is formatted as kiss file" );
		options.addOption( HELP, false, "Shows help" );
		//options.addOption( MK_OT,   true, "Create observation table (OT)" );
		return options;
	}

}
