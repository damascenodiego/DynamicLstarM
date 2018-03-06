package br.usp.icmc.labes.mealyInference.utils;

import java.io.BufferedReader;
import java.io.File;
import java.io.FileReader;
import java.io.FileWriter;
import java.io.IOException;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.Collections;
import java.util.Comparator;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.SortedMap;
import java.util.TreeMap;
import java.util.TreeSet;

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
		Map<String,List<String>> col_suffs = new TreeMap<>();
		for (int col_id = 0; col_id < learner.getObservationTable().getSuffixes().size(); col_id++) {
			col_suffs.put(learner.getObservationTable().getSuffix(col_id).toString(), new  ArrayList<String>(learner.getObservationTable().getAllRows().size()));
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
					col_suffs.get(learner.getObservationTable().getSuffix(col_id).toString()).add(sot.rowContents(row).get(col_id).toString()); 
				}
			}
			currKey = trie.nextKey(currKey);
			
		}
		
		// find experiment cover
		Set<String> experimentCover = new HashSet<>();
		experimentCover = mkExperimentCover(col_suffs);
			
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

	private Set<String> mkExperimentCover(Map<String, List<String>> col_suffs) {
		Map<String, Map<String,Set<Integer>>> tmap = new TreeMap<>(); 
		
		int totRows = 0; 
		for (String key : col_suffs.keySet()) {
			List<String> col = col_suffs.get(key);
			tmap.putIfAbsent(key,new TreeMap<>());
			totRows = col.size();
			for (int row_id = 0; row_id < col.size(); row_id++) {
				tmap.get(key).putIfAbsent(col.get(row_id).toString(), new TreeSet<>());
				tmap.get(key).get(col.get(row_id).toString()).add(row_id);
			}
		}
		List<Set<String>> plist = powerSetAsList(tmap.keySet());
		if(plist.get(0).size()==0) plist.remove(0);
		
		for (Set<String> set_rows : plist) {
			Set<Integer> dist_row = new HashSet<>();
			for (String rows : set_rows) {
				Map<String, Set<Integer>> tmap_row = tmap.get(rows);
				for (String eq_rows_key : tmap_row.keySet()) {
					if(tmap_row.get(eq_rows_key).size()==1){
						dist_row.addAll(tmap_row.get(eq_rows_key));
					}
				}
			}
			if(dist_row.size() == totRows){
				return set_rows;
			}
			
		}
		return plist.get(plist.size()-1);
	}

	public static <T> Set<Set<T>> powerSet(Set<T> originalSet) {
	    Set<Set<T>> sets = new HashSet<Set<T>>();
	    if (originalSet.isEmpty()) {
	        sets.add(new HashSet<T>());
	        return sets;
	    }
	    List<T> list = new ArrayList<T>(originalSet);
	    T head = list.get(0);
	    Set<T> rest = new HashSet<T>(list.subList(1, list.size())); 
	    for (Set<T> set : powerSet(rest)) {
	        Set<T> newSet = new HashSet<T>();
	        newSet.add(head);
	        newSet.addAll(set);
	        sets.add(newSet);
	        sets.add(set);
	    }       
	    return sets;
	}  

	private <T> List<Set<T>> powerSetAsList(Set<T> originalSet){
		Set<Set<T>> pset = powerSet(originalSet);
		
		List<Set<T>> plist = new ArrayList<Set<T>>(pset);
		
		Collections.sort(plist, new Comparator<Set<T>>() {

			@Override
			public int compare(Set<T> o1, Set<T> o2) {
				return Integer.compare(o1.size(), o2.size());
			}
		});

		return plist;
	}

}