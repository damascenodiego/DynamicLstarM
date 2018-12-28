package uk.ac.le.experiment;

import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.io.InputStreamReader;
import java.io.OutputStreamWriter;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import br.usp.icmc.labes.mealyInference.utils.MyObservationTable;
import br.usp.icmc.labes.mealyInference.utils.OTUtils;
import br.usp.icmc.labes.mealyInference.utils.Utils;
import de.learnlib.algorithms.lstar.ce.ObservationTableCEXHandler;
import de.learnlib.algorithms.lstar.ce.ObservationTableCEXHandlers;
import de.learnlib.algorithms.lstar.closing.ClosingStrategies;
import de.learnlib.algorithms.lstar.closing.ClosingStrategy;
import de.learnlib.algorithms.lstar.mealy.ExtensibleLStarMealy;
import de.learnlib.api.SUL;
import de.learnlib.api.oracle.EquivalenceOracle;
import de.learnlib.api.oracle.MembershipOracle;
import de.learnlib.api.query.DefaultQuery;
import de.learnlib.api.statistic.StatisticSUL;
import de.learnlib.datastructure.observationtable.ObservationTable;
import de.learnlib.datastructure.observationtable.writer.ObservationTableASCIIWriter;
import de.learnlib.filter.cache.sul.SULCache;
import de.learnlib.filter.statistic.sul.ResetCounterSUL;
import de.learnlib.filter.statistic.sul.SymbolCounterSUL;
import de.learnlib.oracle.equivalence.RandomWMethodEQOracle;
import de.learnlib.oracle.membership.SULOracle;
import net.automatalib.automata.transout.MealyMachine;
import net.automatalib.automata.transout.impl.compact.CompactMealy;
import net.automatalib.automata.transout.impl.compact.CompactMealyTransition;
import net.automatalib.incremental.mealy.tree.IncrementalMealyTreeBuilder;
import net.automatalib.serialization.dot.GraphDOT;
import net.automatalib.util.automata.Automata;
import net.automatalib.words.Alphabet;
import net.automatalib.words.Word;
import net.automatalib.words.impl.Alphabets;

public class PassiveSatLearning {

	public static void main(String[] args) {
		
		String strOut;
		
		try {
			// set SUL path
			File sul = new File("./experiments_sat/ictss2017.fsm"); // FSM
			File io  = new File("./experiments_sat/ictss2017.io");	 // IO single trace
			File z3_file  = new File("./experiments_sat/ictss2017.sat");	 // IO single trace

			
			// load trace omega
			DefaultQuery<String, Word<String>> query = Utils.getInstance().loadMealyTrace(io);
			
			// load mealy machine
			CompactMealy<String, Word<String>> mealyIO = Utils.getInstance().buildOmegaMealyMachine(query);

			StringBuffer sbuff = new StringBuffer();
			
			int nBlocks = 3;
			sbuff.append("; set variables\n");
			for (Integer state : mealyIO.getStates()) {
				for (int blockID = 0; blockID < nBlocks; blockID++) {
					strOut = String.format("(declare-const v_%d_%d Bool)\n", state,blockID);
					sbuff.append(strOut);
				}
			}
			for (Integer statei : mealyIO.getStates()) {
				for (Integer statej : mealyIO.getStates()) {
					if(statei.equals(statej)) continue;
					strOut = String.format("(declare-const e_%d_%d Bool)\n", statei,statej);
					sbuff.append(strOut);
				}
			}

			sbuff.append("\n; set constraints that each state should be in **AT LEAST** in one block\n");
			for (Integer state : mealyIO.getStates()) {
				sbuff.append("(assert (or");
				for (int blockID = 0; blockID < nBlocks; blockID++) {
					strOut = String.format(" v_%d_%d", state,blockID);
					sbuff.append(strOut);					
				}
				sbuff.append("))\n");
			}

			sbuff.append("\n");
			sbuff.append("; set constraints that each state should be in **AT MOST** in one block\n");
			for (Integer state : mealyIO.getStates()) {
				sbuff.append("(assert (and");
				for (int blocki = 0; blocki < nBlocks; blocki++) {
					for (int blockj = blocki+1; blockj < nBlocks; blockj++) {
						if(blocki == blockj) continue;
						strOut = String.format(" (or (not v_%d_%d) (not v_%d_%d))", state,blocki, state,blockj);
						sbuff.append(strOut);
					}
				}
				sbuff.append("))\n");
			}

			sbuff.append("\n");
			sbuff.append("; set constraints to simplify learning\n");
			for (Integer statei : mealyIO.getStates()) {
				for (Integer statej : mealyIO.getStates()) {
					if(statei.equals(statej)) continue;
					for (String input : mealyIO.getInputAlphabet()) {
						CompactMealyTransition<Word<String>> trI = mealyIO.getTransition(statei, input);
						CompactMealyTransition<Word<String>> trJ = mealyIO.getTransition(statej, input);
						if(trI != null && trJ !=null) {
							if(trI.getOutput().equals(trJ.getOutput())) {
								strOut = String.format("(assert (=> e_%d_%d e_%d_%d))\n", statei,statej,trI.getSuccId(),trJ.getSuccId());
								sbuff.append(strOut);
							}else {
								strOut = String.format("(assert (= e_%d_%d false))\n", statei,statej);
								sbuff.append(strOut);
							}
						}
					}
				}
			}


			sbuff.append("\n");
			sbuff.append("; set relation between auxiliary variables");
			sbuff.append("\n");
			for (Integer statei : mealyIO.getStates()) {
				for (Integer statej : mealyIO.getStates()) {
					if(statei.equals(statej)) continue;
					for (int blocki = 0; blocki < nBlocks; blocki++) {
						strOut = String.format("(assert (=> (and e_%d_%d v_%d_%d) v_%d_%d))\n", statei,statej, statei,blocki,statej,blocki);
						sbuff.append(strOut);
						strOut = String.format("(assert (=> (and (not e_%d_%d) v_%d_%d) (not v_%d_%d)))\n", statei,statej, statei,blocki,statej,blocki);
						sbuff.append(strOut);
					}
				}
			}
//			Map<String,Set<String>> clausePart = new HashMap<>();
//			for (Integer statei : mealyIO.getStates()) {
//				for (Integer statej : mealyIO.getStates()) {
//					if(statei.equals(statej)) continue;
//					for (String input : mealyIO.getInputAlphabet()) {
//						CompactMealyTransition<Word<String>> trI = mealyIO.getTransition(statei, input);
//						CompactMealyTransition<Word<String>> trJ = mealyIO.getTransition(statej, input);
//						if(trI != null && trJ !=null) {
//							if(trI.getOutput().equals(trJ.getOutput())) {
//								StringBuffer sbuff_key = new StringBuffer();
//								StringBuffer sbuff_val = new StringBuffer();
//								sbuff_key.append(input+"/"+trI.getOutput()+" ");
//								sbuff_val.append(String.format("  (not  e_%d_%d)\n", statei,statej));
//								clausePart.putIfAbsent(sbuff_key.toString(), new HashSet<>());
//								clausePart.get(sbuff_key.toString()).add(sbuff_val.toString());
//							}
//						}
//					}
//				}
//			}
//			
//			for (String key : clausePart.keySet()) {
//				bw.write("(assert (or false \n");
//				for (String value : clausePart.get(key)) {
//					bw.write(value);(get-info :all-statistics)
//				}
//				bw.write(") )\n");
//			}

			

			sbuff.append("(check-sat)\n");
			sbuff.append("(get-model)\n");
			
//			File io_sat = new File(io.getParentFile(),io.getName()+".sat");
//			BufferedWriter bw = new BufferedWriter(new FileWriter(io_sat));
//			bw.write(sbuff.toString());
//			bw.close();
			
//			String outZ3 = callZ3(io_sat);
			String[] commands = {"./z3","-in"};
			String outZ3 = getProcessOutput(commands, sbuff.toString());
			//System.out.println(outZ3);
			
			CompactMealy<String, Word<String>> omegaConj = processz3Output(outZ3,mealyIO,nBlocks);
			
			File mealyIO_dot = new File(io.getParentFile(),io.getName()+".bkp.dot");
			GraphDOT.write(mealyIO, mealyIO.getInputAlphabet(), new FileWriter(mealyIO_dot));
			
			File omegaConj_dot = new File(io.getParentFile(),io.getName()+".conj.dot");
			GraphDOT.write(omegaConj, omegaConj.getInputAlphabet(), new FileWriter(omegaConj_dot));
			
			CompactMealy<String, Word<String>> mealySul = Utils.getInstance().loadMealyMachine(sul);
			File sul_dot = new File(io.getParentFile(),io.getName()+".sul.dot");
			GraphDOT.write(mealySul, mealySul.getInputAlphabet(), new FileWriter(sul_dot));

		} catch (Exception e) {
			e.printStackTrace();
		}
	}


	private static String parseUniq0(Integer s_A, Integer s_B, Set<String> uniqs) {
		StringBuilder sb = new StringBuilder();
		for (String string : uniqs) {
			if(s_A!=null && string.startsWith("Uniq_"+s_A)) {
				sb.append(string);
				sb.append(" ");
			}
			if(s_B!=null &&  string.endsWith("_"+s_B)) {
				sb.append(string);
				sb.append(" ");
			}
		}
		return sb.toString();
	}

	public static String callZ3(File z3File) throws IOException, InterruptedException {
		String[] commands = {"./z3",z3File.getAbsolutePath()};
		return getProcessOutput(commands);
	}

	public static CompactMealy<String, Word<String>> processz3Output(String outZ3, CompactMealy<String, Word<String>> omegaMachine, int nBlocks) {
		Alphabet<String> alphabet = Alphabets.fromCollection(omegaMachine.getInputAlphabet());
		CompactMealy<String, Word<String>> omegaConjecture = new CompactMealy<String, Word<String>>(alphabet);

		if(outZ3.startsWith("unsat")) {
			return omegaConjecture;
		}
		
		boolean[][] partitions = new boolean[omegaMachine.getStates().size()][];
		Pattern define_fun = Pattern.compile("\\(define-fun ([ve])_([0-9]+)_([0-9]+) \\(\\) Bool\\s+([a-z]+)\\)");
		Matcher matcher = define_fun.matcher(outZ3);
		while(matcher.find()) {
			//System.out.println(matcher.group(0));
			if(matcher.group(1).equalsIgnoreCase("v")) {
				int state = Integer.valueOf(matcher.group(2));
				int part = Integer.valueOf(matcher.group(3));
				boolean boolVal = Boolean.valueOf(matcher.group(4));
				if(partitions[state] == null) {
					partitions[state] = new boolean[nBlocks];
				}
				partitions[state][part] = boolVal;
			}
		}
//		System.out.println(Arrays.deepToString(partitions).replaceAll("\\], \\[", "\\]\n\\[").replaceAll("\\[\\[", "[").replaceAll("\\]\\]", "]"));

		Map<Integer,Integer> part2state = new HashMap<>();

		for (int i = 0; i < partitions.length; i++) {
			if(!part2state.containsKey(Arrays.hashCode(partitions[i]))) {
				part2state.put(Arrays.hashCode(partitions[i]), omegaConjecture.addState());
			}
		}


		Integer si = omegaConjecture.getState(0); 
		omegaConjecture.setInitialState(si);
		
		for (Integer stateId: omegaMachine.getStates()) {
			for (String inputIdx : omegaMachine.getInputAlphabet()) {
				CompactMealyTransition<Word<String>> transiton = omegaMachine.getTransition(stateId, inputIdx);
				if(transiton!=null && omegaConjecture.getTransition(part2state.get(Arrays.hashCode(partitions[stateId])), inputIdx) == null) {
					omegaConjecture.addTransition(part2state.get(Arrays.hashCode(partitions[stateId])), inputIdx, part2state.get(Arrays.hashCode(partitions[transiton.getSuccId()])), transiton.getOutput());
				}
			}
		}

		return omegaConjecture;
	}
	
	public static String getProcessOutput(String[] commands) throws IOException, InterruptedException {
		return getProcessOutput(commands, null);
	}
	public static String getProcessOutput(String[] commands, String inputToProcess) throws IOException, InterruptedException {
		ProcessBuilder processBuilder = new ProcessBuilder(commands);

		processBuilder.redirectErrorStream(true);

		Process process = processBuilder.start();

		StringBuilder processOutput = new StringBuilder();
		try {
			
			BufferedWriter processOutputWriter = new BufferedWriter(new OutputStreamWriter(process.getOutputStream()));
			if(inputToProcess!=null) {
				if(inputToProcess.length()>0) {
					processOutputWriter.write(inputToProcess);
					processOutputWriter.flush();
                    processOutputWriter.close();
				}
			}
			BufferedReader processOutputReader = new BufferedReader(new InputStreamReader(process.getInputStream()));
			String readLine;
			while ((readLine = processOutputReader.readLine()) != null) {
				processOutput.append(readLine + System.lineSeparator());
			}
			process.waitFor();
		}catch(Exception e){
			e.printStackTrace();
		}

		return processOutput.toString().trim();
	}
}
