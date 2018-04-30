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
import java.util.SortedMap;

import org.apache.commons.collections4.trie.PatriciaTrie;

import com.google.common.collect.Maps;

import de.learnlib.datastructure.observationtable.ObservationTable;
import de.learnlib.datastructure.observationtable.Row;
import de.learnlib.util.statistics.SimpleProfiler;
import de.learnlib.algorithms.lstar.ce.ObservationTableCEXHandlers;
import de.learnlib.algorithms.lstar.closing.ClosingStrategies;
import de.learnlib.algorithms.lstar.mealy.ExtensibleLStarMealy;
import de.learnlib.algorithms.lstar.mealy.ExtensibleLStarMealyBuilder;
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
		return readOT(fin, abc, false);		
	}
	public MyObservationTable readOT(File fin, Alphabet<String> abc, boolean projection) throws IOException{
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
							if(projection) {
								continue; // ignore invalid symbols
							}else {
								break; // trunk suffix at first invalid symbol
							}
						}
						word = word.append(nameToSymbol.get(symbolName));
					}
				}
				if(add) suf.put(word.toString(),word);
			}
		}
		fr.close();

		// sort from the longest to the shortest sequence to remove redundant sequences 
		// (e.g., prefix of another seq)
		List<Word<String>> words = new ArrayList<>(suf.values());
		Collections.sort(words, new Comparator<Word<String>>() {
			@Override
			public int compare(Word<String> o1, Word<String> o2) {
				return Integer.compare(o2.size(),o1.size());
			}
		});

		// trie used to look for prefixes
		PatriciaTrie<Word<String>> trie = new PatriciaTrie<>();
		for (Word<String> word : words) {
			SortedMap<String, Word<String>> prefMap = trie.prefixMap(word.toString());
			if(!prefMap.isEmpty()) {
				continue; // skip if prefix of longer seq
			}else{
				trie.put(word.toString(), word); // otherwise keep
			}
		}
		
		// remove shorter sequences from suf object
		for (Word<String> word : words) {
			if(!trie.containsKey(word.toString())){
				suf.remove(word.toString());
			}
		}
		
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
		
		// Q: Why revalidate observation table using ExtensibleLStarMealy ?
		// A: The OT has to be *well-formed* and *long prefixes may reach new states* !!!
		ExtensibleLStarMealyBuilder<String, Word<String>> builder = new ExtensibleLStarMealyBuilder<String, Word<String>>();
		builder.setAlphabet(mealyss.getInputAlphabet());
		builder.setOracle(oracle);
		builder.setInitialPrefixes(myot.getPrefixes());
		builder.setInitialSuffixes(myot.getSuffixes());
		builder.setCexHandler(ObservationTableCEXHandlers.RIVEST_SCHAPIRE);
		builder.setClosingStrategy(ClosingStrategies.CLOSE_FIRST);
		ExtensibleLStarMealy<String, Word<String>> learner = builder.create();
		
		SimpleProfiler.start("Learning");
		learner.startLearning();
		SimpleProfiler.stop("Learning");
		//new ObservationTableASCIIWriter<>().write(learner.getObservationTable(), System.out);

		ObservationTable<String, Word<Word<String>>> gen_ot = learner.getObservationTable();
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
		Set<Word<String>> experimentCover = mkExperimentCover(gen_ot,wellFormedCover);
			
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
		for (Word<String> key : experimentCover) {
			myot.getSuffixes().add(symbolWord.get(key.toString()));			
		}
		
//		System.out.println("END!!!");
		return gen_ot;
	}

	private Set<Word<String>> mkExperimentCover(ObservationTable<String, Word<Word<String>>> observationTable, Map<String, Word<String>> wellFormedCoverSet) {

		// get rows from the OT at the wellFormerCoverSet
		Set<Row<String>> wellFormedCover = new HashSet<>();
		for (String key : wellFormedCoverSet.keySet()) {
			wellFormedCover.add(observationTable.getRow(wellFormedCoverSet.get(key)));
		}
		
		// find the subset of E that is the experiment cover set
		Set<Word<String>> experimentCover = ExperimentCover.getInstance().find(observationTable, wellFormedCover);

		return experimentCover;
	}

	public static class ExperimentCover{
		
		private static ExperimentCover instance;
		
		private ExperimentCover(){}
		
		public static ExperimentCover getInstance() {
			if(instance==null) {
				instance = new ExperimentCover();
			}
			return instance;
		}

		// find the experiment cover set using an approach similar to that for synchronizing trees
		Set<Word<String>> find(ObservationTable<String, Word<Word<String>>> observationTable, Set<Row<String>> wellFormedCover){
			
			// DistinguishableStates keeps the set of distinguished states and the suffixes used to that
			List<DistinguishableStates> toAnalyze = new ArrayList<>();
			
			// set of nodes found (used to find previously visited states)
			Set<Set<Set<Row<String>>>> nodesFound = new HashSet<>();

			// creates the first DistinguishableStates
			Set<Set<Row<String>>> diff_states = new HashSet<>();
			// all states undistinguished
			diff_states.add(wellFormedCover); 
			// no suffixes applied
			Set<Integer> eSubset = new HashSet<>();
			toAnalyze.add(new DistinguishableStates(observationTable, diff_states, eSubset));
			
			// current DistinguishableStates analyzed ( singleton is kept here )
			DistinguishableStates item = toAnalyze.get(0);
			
			// the DistinguishableStates with the 'best' subset of E 
			DistinguishableStates best = toAnalyze.get(0); 
			
			while (!toAnalyze.isEmpty()) {
				item = toAnalyze.remove(0);
				if(item.getDistinguishedStates().size()>best.getDistinguishedStates().size()) {
					// (i.e., distinguish the largest number of states)
					best = item;
				}
				if(item.isSingleton()) break; // if is singleton stops here!!! :)
				
				for (int sufIdx = 0; sufIdx < observationTable.getSuffixes().size(); sufIdx++){
					if(item.getESubset().contains(sufIdx)) {
						// suffix already applied at this item
						continue;
					}
					// new subset of states that may be distinguished by 'sufIdx' 
					diff_states = new HashSet<>(); eSubset = new HashSet<>();
					for (Set<Row<String>> prefixes : item.getDistinguishedStates()) {
						// maps the outputs to rows (used for keeping states equivalent given 'sufIdx') 
						Map<String,Set<Row<String>>> out2Rows = new TreeMap<>();
						// look 'sufIdx' for each prefix
						for (Row<String> pref : prefixes) {
							String outStr = observationTable.cellContents(pref, sufIdx).toString();
							// if outStr is new, then add sufIdx as an useful suffix
							if(out2Rows.putIfAbsent(outStr, new HashSet<>()) == null){
								eSubset.add(sufIdx);
							}
							out2Rows.get(outStr).add(pref);
						}
						// the subsets of states that are distinguished by 'sufIdx'
						diff_states.addAll(out2Rows.values());
					}
					// if diff_states was previously visited, then discard! :(
					if(nodesFound.contains(diff_states)) continue;
					nodesFound.add(diff_states); // otherwise keep it!
					// create a new DistinguishableStates 
					DistinguishableStates new_diststates = new DistinguishableStates(observationTable);
					new_diststates.setDistinguishedStates(diff_states);
					// add previously applied suffixes to eSubset (i.e., { eSubset \cup 'sufIdx'}  
					eSubset.addAll(item.getESubset());
					new_diststates.setESubset(eSubset);
					// add it to be analyzed later 
					toAnalyze.add(new_diststates);
				}
			}
			Set<Word<String>> out = new HashSet<>();
			if(item.isSingleton()){ // if item is singleton then return its suffixes
				for (Integer e_el : item.getESubset()) {
					out.add(observationTable.getSuffix(e_el));
				}
				
			}else{ // otherwise add the 'best' subset of E
				for (Integer e_el : best.getESubset()) {
					out.add(observationTable.getSuffix(e_el));
				}
			}
			return out;
		}
		
		public class DistinguishableStates{
			private ObservationTable<String, Word<Word<String>>> observationTable;
			private Set<Set<Row<String>>> distinguishedStates;
			private Set<Integer> eSubset;
			private boolean isSingleton;
			
			public DistinguishableStates(ObservationTable<String, Word<Word<String>>> ot, Set<Set<Row<String>>> states, Set<Integer> esubset) {
				this.observationTable = ot;
				this.distinguishedStates = states;
				this.eSubset = esubset;
				this.isSingleton = false;
				for (Set<Row<String>> set : this.distinguishedStates) {
					if(set.size()!=1){
						return;
					}
				}
				this.isSingleton = true;
			}
			
			public DistinguishableStates(ObservationTable<String, Word<Word<String>>> ot) {
				this.observationTable = ot;
			}
			
			public Set<Set<Row<String>>> getDistinguishedStates() {
				return distinguishedStates;
			}
			
			public Set<Integer> getESubset() {
				return eSubset;
			}
			
			public ObservationTable<String, Word<Word<String>>> getObservationTable() {
				return observationTable;
			}
			public boolean isSingleton() {
				return isSingleton;
			}
			
			public void setDistinguishedStates(Set<Set<Row<String>>> states) {
				this.distinguishedStates = states;
				for (Set<Row<String>> set : this.distinguishedStates) {
					if(set.size()!=1){
						return;
					}
				}
				this.isSingleton = true;
			}
			public void setESubset(Set<Integer> eSubset) {
				this.eSubset = eSubset;
			}
			@Override
			public boolean equals(Object obj) {
				if(obj !=null && obj instanceof DistinguishableStates){
					return this.distinguishedStates.equals(((DistinguishableStates) obj).distinguishedStates);
				}
				return false;
			}
			
			@Override
			public int hashCode() {
				StringBuffer sb = new StringBuffer(observationTable.toString().length());
				sb.append("{");
				for (Set<Row<String>> set : distinguishedStates) {
					sb.append("{");
					for (Row<String> row : set) {
						sb.append(row.getRowId());
						sb.append(",");
					}
					sb.append("}");
				}
				sb.append("}");
				return sb.toString().hashCode();
			}
			@Override
			public String toString() {
				StringBuffer sb = new StringBuffer(observationTable.toString().length());
				sb.append(observationTable.toString());
				sb.append('\n');
				sb.append("Distinguished states:\n");
				for (Set<Row<String>> set : distinguishedStates) {
					for (Row<String> row : set) {
						sb.append('\t');
						sb.append(row.getRowId());
					}
					sb.append('\n');
				}
				sb.append("Columns:");
				for (Integer intVal : eSubset) {
					sb.append('\t');
					sb.append(intVal);
				}
				sb.append('\n');
				return sb.toString();
			}
		}
		
	}
	
}