package br.usp.icmc.labes.mealyInference.utils;

import java.io.BufferedReader;
import java.io.File;
import java.io.FileReader;
import java.io.FileWriter;
import java.io.IOException;
import java.util.ArrayList;
import java.util.Collections;
import java.util.Comparator;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.TreeMap;
import java.util.TreeSet;

import org.apache.commons.collections4.trie.PatriciaTrie;

import com.google.common.collect.Maps;

import de.learnlib.datastructure.observationtable.GenericObservationTable;
import de.learnlib.datastructure.observationtable.ObservationTable;
import de.learnlib.datastructure.observationtable.Row;
import de.learnlib.util.statistics.SimpleProfiler;
import de.learnlib.api.oracle.MembershipOracle;
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

		Map<String,Word<String>> suf = new LinkedHashMap<>();
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
						if(nameToSymbol.containsKey(symbolName)) {
							word = word.append(nameToSymbol.get(symbolName));
						}
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
				if(add) suf.put(word.toString(),word);
			}
		}
		fr.close();

		MyObservationTable my_ot = new MyObservationTable(pref, suf.values());

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
		
		// revalidate observation table
		GenericObservationTable<String, Word< Word<String> > > gen_ot = new GenericObservationTable<>(mealyss.getInputAlphabet());
		
		SimpleProfiler.start("Learning");
		gen_ot.initialize(myot.getPrefixes(), myot.getSuffixes(), oracle);
		SimpleProfiler.stop("Learning");
		//new ObservationTableASCIIWriter<>().write(learner.getObservationTable(), System.out);

		PatriciaTrie<Row<String>> trie = new PatriciaTrie<>();
		
		for (Row<String> row : gen_ot.getShortPrefixRows()) {
			if(row.getLabel().isEmpty()){
				trie.put(row.getLabel().toString(), row);
			}else{
				trie.put(Word.epsilon().toString()+row.getLabel().toString(), row);
			}
		}
		
		// well-formed cover set (key -> output | value -> row from updated OT)
		Map<String,Word<String>> wellFormedCover = new TreeMap<>();

		// supports: (i) removing redundant rows and extensions and (ii) finding the first representative columns
		Set<String> keySupport = new HashSet<>();
		
		// find well-formed cover
		String currKey = trie.firstKey();
		String prevKey = null;
		while(currKey != null){
			Row<String> row = trie.get(currKey);
			// state already covered? 
			// check if the rowContent was already obtained 
			if(wellFormedCover.containsKey(gen_ot.rowContents(row).toString())){
				// get previous key to go to the next sub-tree
				prevKey = trie.previousKey(currKey);
				// removes (i) 'currKey' and its extensions (i.e., with currKey as prefix)
				keySupport.clear(); keySupport.addAll(trie.prefixMap(currKey).keySet());
				// prune sub-tree
				for (String  toRm : keySupport) {
					trie.remove(toRm);
					
				}
				// retake tree search from previous key
				currKey = prevKey;
			}else{
				// new state covered
				wellFormedCover.put(gen_ot.rowContents(row).toString(),row.getLabel());
			}
			// go to the next key
			currKey = trie.nextKey(currKey);
			
		}
		
		// find experiment cover
		Set<String> experimentCover = mkExperimentCover(gen_ot,wellFormedCover);
			
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
		
		Map<String, Word<String>> symbolWord = generateNameToWordMap(gen_ot.getSuffixes());
		for (String key : experimentCover) {
			myot.getSuffixes().add(symbolWord.get(key));			
		}
		
//		System.out.println("END!!!");
		return gen_ot;
	}

	private Set<String> mkExperimentCover(ObservationTable<String, Word<Word<String>>> observationTable,
			Map<String, Word<String>> wellFormedCover) {
 		Set<String> experimentCover = new HashSet<>();

 		// get the IDs of all suffixes columns
		Set<Integer> suffixes = new TreeSet<>();
		for (int i = 0; i < observationTable.getSuffixes().size(); i++)  suffixes.add(i);

		// generate powerset with all possible combinations
		// sorted from the smallest subset to the suffixes set itself
		List<Set<Integer>> plist = powerSetAsList(suffixes);
				
		// remove the empty subset
		if(plist.get(0).isEmpty()) plist.remove(0);
		
		// create StringBuffers to concatenate outputs
		List<StringBuffer> cols_concat = new ArrayList<>(wellFormedCover.size());
		for (int i = 0; i < wellFormedCover.size(); i++)  cols_concat.add(i, new StringBuffer());
		
		// for each combination of suffix
		for (Set<Integer> subset : plist) {
			// clear StringBuffers
			for (int i = 0; i < cols_concat.size(); i++)  cols_concat.get(i).delete(0, cols_concat.get(i).length());

			int row_id = 0;
			// for each row \in wellFormedCover 
			for (String row : wellFormedCover.keySet()) {
				Word<String> row_obj = wellFormedCover.get(row);
				// for each columnId \in subset
				for (int columnId : subset) {
					// concatenate all outputs  --> row \cdot cols[columnId]
					// (obs.: in cols_concat, row is referred to as row_id)
					cols_concat.get(row_id).append(observationTable.cellContents(observationTable.getRow(row_obj), columnId).toString());
				}
				row_id++; // go to the next row (SEE: wellFormedCover)
			}
			
			
			// count the number of distinct rows
			Set<String> allOutputs = new HashSet<>();
			for (StringBuffer out : cols_concat)  allOutputs.add(out.toString());

			
			if(		allOutputs.size() 		// if the *number of distinct rows* 
					==						// is equals to
					wellFormedCover.size()	// the size of the *well formed cover* subset
					){						// then subset is a representative experiment cover subset 
				for (Integer columnId : subset) {			
					experimentCover.add(observationTable.getSuffix(columnId).toString()); // save all suffixes
				}				
				break; // stop searching for an experiment cover set
			}
		}

		return experimentCover;
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