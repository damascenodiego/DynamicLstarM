package br.usp.icmc.labes.spl;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Random;
import java.util.Set;

import jdk.nashorn.internal.ir.annotations.Immutable;

public class Configurations {
	
	Map<String,Set<String>> configurations;
	Map<String,Set<String>> features;
	Map<Integer,Set<String>> totFeatToFeat;
	
	int maxFeatures;
	
	public Configurations() {
		configurations 	= new LinkedHashMap<>();
		features 		= new LinkedHashMap<>();
		maxFeatures = 0;
	}
	
	public void addConfiguration(String configId, Collection<String> features) {
		this.configurations.putIfAbsent(configId, new LinkedHashSet<>(features.size()));		
		for (String a_feat : features) {
			this.configurations.get(configId).add(a_feat);
			this.features.putIfAbsent(a_feat, new LinkedHashSet<>(features.size()));
			this.features.get(a_feat).add(configId);
		}
		if(maxFeatures<this.configurations.get(configId).size()){
			maxFeatures=this.configurations.get(configId).size();
		}
	}
	
	public void addConfiguration(String configId, String a_feat) {
		this.configurations.putIfAbsent(configId, new LinkedHashSet<>(features.size()));
		if(a_feat!=null){
			this.configurations.get(configId).add(a_feat);
			this.features.putIfAbsent(a_feat, new LinkedHashSet<>(features.size()));
			this.features.get(a_feat).add(configId);
		}
		if(maxFeatures<this.configurations.get(configId).size()){
			maxFeatures=this.configurations.get(configId).size();
		}
	}
	
	@Immutable
	public Map<String, Set<String>> getConfigurations() {
		return Collections.unmodifiableMap(this.configurations);
	}
	
	@Immutable
	public Map<String, Set<String>> getFeatures() {
		return Collections.unmodifiableMap(this.features);
	}
	
	public Set<String> getConfiguration(String configId){
		this.configurations.putIfAbsent(configId, new LinkedHashSet<>(features.size()));
		
		return this.configurations.get(configId);
	}
	
	public Set<String> getFeature(String featId){
		this.features.putIfAbsent(featId, new LinkedHashSet<>(features.size()));
		
		return this.features.get(featId);
	}
	
	public List<String> getConfigsWithNFeatures(int totFeat){
		List<String> lst = new ArrayList<>();
		for (String a_conf : this.configurations.keySet()) {
			if(this.configurations.get(a_conf).size()==totFeat){
				lst.add(a_conf);
			}
		}		
		return lst;
	}
	
	public void updateDatabase(){
		totFeatToFeat.clear();
		for (String a_conf : this.configurations.keySet()) {
			totFeatToFeat.putIfAbsent(this.configurations.get(a_conf).size(), new LinkedHashSet<>(features.size()));
			totFeatToFeat.get(this.configurations.get(a_conf).size()).add(a_conf);
		}
	}
	
	public String selectRandomConfigsWithNFeatures(int totFeat, Random rnd){
		List<String> confs = getConfigsWithNFeatures(totFeat);
		
		return confs.get(rnd.nextInt(confs.size()));
		
	}
	
	public String selectRandomConfigsWithNFeatures(int totFeat){
		Random rnd = new Random();
		return selectRandomConfigsWithNFeatures(totFeat,rnd);
		
	}
	
	public List<String> getConfigsWithPercentFeatures(double percentFeat){
		System.out.println(((int)(maxFeatures*percentFeat)));
		return getConfigsWithNFeatures(((int)(maxFeatures*percentFeat)));
	}
	
	public String selectRandomConfigsWithPercentFeatures(double percentFeat, Random rnd){
		System.out.println(((int)(maxFeatures*percentFeat)));
		return selectRandomConfigsWithNFeatures(((int)(maxFeatures*percentFeat)));
		
	}
	
	public String selectRandomConfigsWithPercentFeatures(double percentFeat){
		Random rnd = new Random();
		return selectRandomConfigsWithNFeatures(((int)(maxFeatures*percentFeat)),rnd);
		
	}
	
	
	
	@Override
	public String toString() {
		StringBuilder sb = new StringBuilder();
		for (String a_conf : this.configurations.keySet()) {
			sb.append(a_conf);
			sb.append(":\t");
			for (String a_feat : this.configurations.get(a_conf)) {
				sb.append(a_feat);
				sb.append(" ");
			}
			sb.append("\n");
			
		}
		return sb.toString();
	}
	
	public String featuresToString() {
		StringBuilder sb = new StringBuilder();
		for (String a_feat : this.features.keySet()) {
			sb.append(a_feat);
			sb.append(":\t");
			for (String a_conf : this.features.get(a_feat)) {
				sb.append(a_conf);
				sb.append(" ");
			}
			sb.append("\n");
			
		}
		return sb.toString();
	}
	
}
