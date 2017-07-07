package br.usp.icmc.fsm.common;

import java.util.ArrayList;

public class Node {
	private State state;
	String type;
	private ArrayList<Node> children = new ArrayList<Node>();
	//private ArrayList<String> labels = new ArrayList<String>();
	
	public Node(State st, String type) {
		state = st;
		this.type = type;
	}
	
	public String getType(){
		return type;
	}
	
	public void setType(String type){
		this.type = type;
	}
	
	public State getState() {
		return state;
	}
	
	public void addChild(Node n) {
		children.add(n);
		//labels.add(label);
	}
	
	public ArrayList<Node> getChildren() {
		return children;
	}
	
	public void remove(Node n){
		children.remove(n);
	}
	
	//public ArrayList<String> getLabels() {
	//	return labels;
	//}
}
