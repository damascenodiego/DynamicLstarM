package br.usp.icmc.labes.mealyInference.utils;

import java.io.BufferedReader;
import java.io.File;
import java.io.FileReader;
import java.io.FileWriter;
import java.io.IOException;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.SortedMap;
import java.util.TreeMap;

import org.apache.commons.collections4.OrderedMapIterator;
import org.apache.commons.collections4.trie.PatriciaTrie;

import com.google.common.collect.Maps;

import br.usp.icmc.labes.mealyInference.Infer_LearnLib;
import de.learnlib.datastructure.observationtable.ObservationTable;
import de.learnlib.datastructure.observationtable.Row;
import de.learnlib.datastructure.observationtable.reader.SimpleObservationTable;
import de.learnlib.datastructure.observationtable.writer.ObservationTableASCIIWriter;
import de.learnlib.util.statistics.SimpleProfiler;
import de.learnlib.algorithms.lstar.ce.ObservationTableCEXHandlers;
import de.learnlib.algorithms.lstar.closing.ClosingStrategies;
import de.learnlib.algorithms.lstar.mealy.ExtensibleLStarMealy;
import de.learnlib.algorithms.lstar.mealy.ExtensibleLStarMealyBuilder;
import de.learnlib.api.logging.LearnLogger;
import de.learnlib.api.oracle.MembershipOracle;
import de.learnlib.api.query.Query;
import net.automatalib.automata.transout.impl.compact.CompactMealy;
import net.automatalib.words.Alphabet;
import net.automatalib.words.Word;

public class OTUtils {


	private static final String WORD_DELIMITER = ";";
	private static final String SYMBOL_DELIMITER = ",";

	private static OTUtils instance;

	private OTUtils() { }

	public static OTUtils getInstance() {

		if(instance==null) instance = new OTUtils();

		return instance;
	}

	public void writeOT(ObservationTable<String, Word<Word<String>>> observationTable, File fout) throws IOException{

		FileWriter fw = new FileWriter(fout);

		StringBuilder sb = new StringBuilder();

		// write short prefixes
		sb.delete(0, sb.length());
		for (Word<String> word : observationTable.getShortPrefixes()) {
			if(!word.isEmpty()){
				for (int i = 0; i < word.length(); i++) {
					sb.append(word.getSymbol(i).toString());
					if(i!=word.length()-1) sb.append(SYMBOL_DELIMITER);
				}
			}
			sb.append(WORD_DELIMITER);
		}
//		fw.write(sb.toString());
//
//		// write long prefixes
//		sb.delete(0, sb.length());
//		for (Word<String> word : observationTable.getLongPrefixes()) {
//			if(!word.isEmpty()){
//				for (int i = 0; i < word.length(); i++) {
//					sb.append(word.getSymbol(i).toString());
//					if(i!=word.length()-1) sb.append(SYMBOL_DELIMITER);
//				}
//			}
//			sb.append(WORD_DELIMITER);
//		}
		sb.deleteCharAt(sb.length()-1);
		sb.append('\n');
		fw.write(sb.toString());

		// write suffixes
		sb.delete(0, sb.length());
		for (Word<String> word : observationTable.getSuffixes()) {
			if(!word.isEmpty()){
				for (int i = 0; i < word.length(); i++) {
					sb.append(word.getSymbol(i).toString());
					if(i!=word.length()-1) sb.append(SYMBOL_DELIMITER);
				}
			}
			sb.append(WORD_DELIMITER);
		}
		sb.deleteCharAt(sb.length()-1);
		sb.append('\n');
		fw.write(sb.toString());
		fw.close();

	}
	
	public void writeOT(MyObservationTable observationTable, File fout) throws IOException{

		FileWriter fw = new FileWriter(fout);

		StringBuilder sb = new StringBuilder();

		// write prefixes
		sb.delete(0, sb.length());
		for (Word<String> word : observationTable.getPrefixes()) {
			if(!word.isEmpty()){
				for (int i = 0; i < word.length(); i++) {
					sb.append(word.getSymbol(i).toString());
					if(i!=word.length()-1) sb.append(SYMBOL_DELIMITER);
				}
			}
			sb.append(WORD_DELIMITER);
		}
		fw.write(sb.toString());

		// write suffixes
		sb.delete(0, sb.length());
		for (Word<String> word : observationTable.getSuffixes()) {
			if(!word.isEmpty()){
				for (int i = 0; i < word.length(); i++) {
					sb.append(word.getSymbol(i).toString());
					if(i!=word.length()-1) sb.append(SYMBOL_DELIMITER);
				}
			}
			sb.append(WORD_DELIMITER);
		}
		sb.deleteCharAt(sb.length()-1);
		sb.append('\n');
		fw.write(sb.toString());
		fw.close();

	}

	public MyObservationTable readOT(File fin, Alphabet<String> abc) throws IOException{
		Map<String, String>  nameToSymbol  = generateNameToSymbolMap(abc); 

		List<Word<String>> suf = new ArrayList<>();
		List<Word<String>> pref= new ArrayList<>();

		BufferedReader fr = new BufferedReader(new FileReader(fin));

		String line = fr.readLine();
		boolean add;

		if(!line.isEmpty()){
			String[] words = line.split(WORD_DELIMITER);
			for (String prefixWord : words) {
				String[] symbolNames = prefixWord.split(SYMBOL_DELIMITER);
				Word<String> word = Word.epsilon();
				add=true;
				if (!prefixWord.isEmpty()) {
					for (String symbolName : symbolNames) {
						if(!nameToSymbol.containsKey(symbolName)){
							add = false;
							break;							
						}
						word = word.append(nameToSymbol.get(symbolName));
					}
				}
				if(add) pref.add(word);
			}
		}

		line = fr.readLine();
		if(!line.isEmpty()){
			String[] words = line.split(WORD_DELIMITER);
			for (String suffixWord : words) {
				String[] symbolNames = suffixWord.split(SYMBOL_DELIMITER);
				Word<String> word = Word.epsilon();
				add = true;
				if (!suffixWord.isEmpty()) {
					for (String symbolName : symbolNames) {
						if(!nameToSymbol.containsKey(symbolName)){
							add = false;
							continue;							
						}
						word = word.append(nameToSymbol.get(symbolName));
					}
				}
				if(add) suf.add(word);
			}
		}
		fr.close();

		MyObservationTable my_ot = new MyObservationTable(pref, suf);

		return my_ot;
	}

	private Map<String, String> generateNameToSymbolMap(Alphabet<String> abc) {
		Map<String, String> nameToSymbol = Maps.newHashMapWithExpectedSize(abc.size());

		for (String symbol : abc) {
			String symbolName = symbol.toString();
			if (nameToSymbol.containsKey(symbolName)) {
				throw new IllegalArgumentException(
						"Symbol name '" + symbolName + "' is used more than once in alphabet");
			}
			else {
				nameToSymbol.put(symbolName, symbol);
			}
		}

		return nameToSymbol;
	}
	
	private Map<String, Word<String>> generateNameToWordMap(List<? extends Word<String>> list) {
		Map<String, Word<String>> nameToSymbol = new HashMap<String, Word<String>>(list.size());

		for (Word<String> word : list) {
			String symbolName = word.toString();
			if (nameToSymbol.containsKey(symbolName)) {
				throw new IllegalArgumentException(
						"Symbol name '" + symbolName + "' is used more than once in alphabet");
			}
			else {
				nameToSymbol.put(symbolName, word);
			}
		}

		return nameToSymbol;
	}

	public ObservationTable<String, Word<Word<String>>> revalidateOT2(MyObservationTable myot, MembershipOracle<String, Word<Word<String>>>  oracle, CompactMealy<String, Word<String>> mealyss){
		
		// create log 
		LearnLogger logger = LearnLogger.getLogger(OTUtils.class);
					
		// construct L* instance to update T by asking MQs
		ExtensibleLStarMealyBuilder<String, Word<String>> builder = new ExtensibleLStarMealyBuilder<String, Word<String>>();
		builder.setAlphabet(mealyss.getInputAlphabet());
		builder.setOracle(oracle);
		builder.setInitialPrefixes(myot.getPrefixes());
		builder.setInitialSuffixes(myot.getSuffixes());
		builder.setCexHandler(ObservationTableCEXHandlers.RIVEST_SCHAPIRE);
		builder.setClosingStrategy(ClosingStrategies.CLOSE_FIRST);

		ExtensibleLStarMealy<String, Word<String>> learner = builder.create();

		
		SimpleProfiler.start("Revalidating OT");
		learner.startLearning();
		SimpleProfiler.stop("Revalidating OT");
		//new ObservationTableASCIIWriter<>().write(learner.getObservationTable(), System.out);

		PatriciaTrie<Row<String>> trie = new PatriciaTrie<>();
		
		for (Row<String> row : learner.getObservationTable().getShortPrefixRows()) {
			if(row.getLabel().isEmpty()){
				trie.put(row.getLabel().toString(), row);
			}else{
				trie.put(Word.epsilon().toString()+row.getLabel().toString(), row);
			}
		}
		
		// well-formed cover set (key -> output | value -> row from updated OT)
		Map<String,Word<String>> wellFormedCover = new TreeMap<>();

		// experiment cover set (key -> suffix | value -> Col(suffix))
		Map<String,StringBuffer> col_suffs = new HashMap<>();
		for (int col_id = 0; col_id < learner.getObservationTable().getSuffixes().size(); col_id++) {
			col_suffs.put(learner.getObservationTable().getSuffix(col_id).toString(), new  StringBuffer(learner.getObservationTable().getAllRows().size()));
		}
		
		// supports: (i) removing redundant rows and extensions and (ii) finding the first representative columns
		Set<String> keySupport = new HashSet<>();
		
		// find well-formed cover
		String currKey = trie.firstKey();
		String prevKey = null;
		while(currKey != null){
			Row<String> row = trie.get(currKey);
			// state already covered?
			if(wellFormedCover.containsKey(row.toString())){
//				System.err.println(currKey+"\t"+row.getContents().toString());
				// get previous key to go to the next sub-tree
				prevKey = trie.previousKey(currKey);
				// removes (i) 'currKey' and its extensions (i.e., with currKey as prefix)
				keySupport.clear(); keySupport.addAll(trie.prefixMap(currKey).keySet());
				// prune sub-tree
				for (String  toRm : keySupport) {
					trie.remove(toRm);
					
				}
				currKey = prevKey;
			}else{
//				System.out.println(currKey+"\t"+row.getContents().toString());
				// new state covered
				wellFormedCover.put(row.toString(),row.getLabel());
				for (int col_id = 0; col_id < learner.getObservationTable().getSuffixes().size(); col_id++) {
					ObservationTable<String, Word<Word<String>>> sot = learner.getObservationTable();
					col_suffs.get(learner.getObservationTable().getSuffix(col_id).toString()).append(sot.rowContents(row).get(col_id).toString()); 
				}
			}
			currKey = trie.nextKey(currKey);
			
		}
		
		// find experiment cover
		Set<String> experimentCover = new HashSet<>();
		keySupport.clear();
		for (String key : col_suffs.keySet()) {
			if(keySupport.contains(col_suffs.get(key).toString())){
//				System.err.println(key+"\t"+col_suffs.get(key));
			}else{
//				System.out.println(key+"\t"+col_suffs.get(key));
				keySupport.add(col_suffs.get(key).toString());
				experimentCover.add(key);
			}
		}
			
//		System.out.println(trie.keySet());
//		System.out.println(experimentCover);
		
		myot.getPrefixes().clear();
		myot.getSuffixes().clear();
		
		myot.getPrefixes().add(Word.epsilon());
		for (String key : wellFormedCover.keySet()) {
			if(!wellFormedCover.get(key).isEmpty()){
				myot.getPrefixes().add(wellFormedCover.get(key));
			}
		}
		
		Map<String, Word<String>> symbolWord = generateNameToWordMap(learner.getObservationTable().getSuffixes());
		for (String key : experimentCover) {
			myot.getSuffixes().add(symbolWord.get(key));			
		}
		
//		System.out.println("END!!!");
		return learner.getObservationTable();
	}
	
	public void revalidateOT(MyObservationTable myot, MembershipOracle<String, Word<Word<String>>>  oracle){
		
		if(myot.getPrefixes().size()==0 || myot.getSuffixes().size()==0) return;
		
//		System.out.println(myot);
		
		PatriciaTrie<Word<String>> trie = new PatriciaTrie<>();
		
		for (Word<String> pref : myot.getPrefixes()) {
			if(pref.isEmpty()){
				trie.put(pref.toString(), pref);
			}else{
				trie.put(Word.epsilon().toString()+pref.toString(), pref);
			}
			
		}
		
		Set<String> observedOutputs = new HashSet<>();
		Set<String> keys2rm_set = new HashSet<>();
		Map<String,String[]> prefOutputs = new LinkedHashMap<>(); 

		String key = trie.firstKey();
		String prevKey;
		String currKey;
		StringBuilder sb = new StringBuilder(1);
		String[] outs;
		for (int i = 0; i>=0 && i < trie.size(); i++) {
			if(key==null) continue;
			Word<String> pref = trie.get(key);
			sb.delete(0, sb.length());
			outs = new String[myot.getSuffixes().size()];
			int sufId = 0;
			for (Word<String> suff : myot.getSuffixes()) {
				String answer = oracle.answerQuery(pref,suff).toString();
				sb.append(answer);
				outs[sufId] = answer;
				sufId++;
			}
			String sb_s = sb.toString();
			currKey = key;
			if(observedOutputs.contains(sb_s)){
				prevKey=trie.previousKey(key);
				keys2rm_set.addAll(trie.prefixMap(key).keySet());
				for (String key2rm : keys2rm_set) {
					trie.remove(key2rm);
					i--;
				}
				keys2rm_set.clear();
				key=prevKey;
			}else{
				prefOutputs.put(currKey, outs);
				observedOutputs.add(sb_s);
			}
			
			key=trie.nextKey(key);
		}
//		System.out.println(trie.toString());
		boolean[] suff2Add = new boolean[myot.getSuffixes().size()];
		for (int i = 0; i < suff2Add.length; i++)  suff2Add[i] = true;
		
		for (int i = 0; i < myot.getSuffixes().size(); i++) {
			sb.delete(0, sb.length());
			for (String k : prefOutputs.keySet()) {
				sb.append(prefOutputs.get(k)[i]);
			}
			String sb_s = sb.toString();
			if(keys2rm_set.contains(sb_s)){
				suff2Add[i] = false;
			}else{
				keys2rm_set.add(sb_s);	
			}
		}
		
		myot.getPrefixes().clear();
		for (String k : trie.keySet()) {
			myot.getPrefixes().add(trie.get(k));
		}
		
		for (int i = myot.getSuffixes().size()-1; i >0 ; i--) {
			if(!suff2Add[i]){
				myot.getSuffixes().remove(i);
			}
		}
		
//		System.out.println(myot);
	}

	public void revalidateOT(MyObservationTable myot, MembershipOracle<String, Word<Word<String>>> mqOracle,
			Alphabet<String> inputAlphabet) {
		
		Map<String, String>  nameToSymbol  = generateNameToSymbolMap(inputAlphabet);

		Map<String, Word<String>> ot_map = new  TreeMap<>();
		
		for (Word<String> word : myot.getPrefixes()) {
			boolean keep = true;
			for (int i = 0; i < word.size(); i++) {
				String symbol = word.getSymbol(i);				
				if(!nameToSymbol.containsKey(symbol)) {
					keep = false;
					break;
				}
			}
			if (keep) {
				ot_map.put(word.toString(),word);
			}
		}
		if(!ot_map.isEmpty()) myot.getPrefixes().clear();
		myot.getPrefixes().addAll(ot_map.values());
		ot_map.clear();
		
		for (Word<String> word : myot.getSuffixes()) {
			boolean keep = true;
			for (int i = 0; i < word.size(); i++) {
				String symbol = word.getSymbol(i);
				if(!nameToSymbol.containsKey(symbol)){
					keep = false;
					break;
				}
			}
			if (keep) {
				ot_map.put(word.toString(),word);
			}
		}
		if(!ot_map.isEmpty()) myot.getSuffixes().clear();
		myot.getSuffixes().addAll(ot_map.values());
		ot_map.clear();

		revalidateOT(myot, mqOracle);
		
	}




}