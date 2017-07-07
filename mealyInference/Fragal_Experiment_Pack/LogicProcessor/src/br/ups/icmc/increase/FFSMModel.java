package br.ups.icmc.increase;

import java.io.File;
import java.io.IOException;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.Iterator;
import java.util.Random;
import java.util.Set;

import sun.reflect.generics.tree.Tree;
import br.usp.icmc.ffsm.FFSM;
import br.usp.icmc.ffsm.FState;
import br.usp.icmc.ffsm.FTransition;
import br.usp.icmc.fsm.common.FileHandler;
import br.usp.icmc.fsm.common.FiniteStateMachine;
import br.usp.icmc.fsm.common.Node;
import br.usp.icmc.fsm.common.Ntree;
import br.usp.icmc.fsm.common.State;
import br.usp.icmc.fsm.common.Transition;
import br.usp.icmc.fsm.reader.FFSMModelReader;
import br.usp.icmc.fsm.reader.FsmModelReader;

public class FFSMModel {
	
	Ntree tree;
	ArrayList<State> s_found;
	Node current_node;
	String clause;
	int count;
	ArrayList<Integer> conf_count;
	HashMap<String, Integer> conf_map;
	
	public FFSMModel(){
		conf_map = new HashMap<String, Integer>();
	}
	
	public HashMap<String, Integer> getMap(){
		return conf_map;
	}
	
	public void gen_FFSM(String folder, int amount) throws IOException{
		
		for(int k=1; k<=amount; k++){
			String header = "s0@f0 -- a@f0 / 0 -> s0@f0\n";
					
			String clause = "";
			for(int i=1; i<=k; i++){
				clause = clause.concat("s0@f0 -- a"+i+"@f"+i+" / 0 -> s"+i+"@f"+i+"\n");			
			}
			String prop_aux = header.concat(clause);
			
			clause = "";
			for(int i=1; i<=k; i++){
				clause = clause.concat("s"+i+"@f"+i+" -- a@f"+i+" / 1 -> s0@f0\n");			
			}			
			prop_aux = prop_aux.concat(clause);
			
			clause = "";
			for(int i=1; i<=k; i++){
				clause = clause.concat("s"+i+"@f"+i+" -- b@f"+i+" / o"+i+" -> s"+i+"@f"+i+"\n");			
			}			
			prop_aux = prop_aux.concat(clause);
			
			
			String path = "./"+folder+"/ffsm"+k+".txt";
			FileHandler fh = new FileHandler();
			fh.print_file(prop_aux, path);
		}
		
	}
	
	public void gen_FFSM_best(String folder, int amount) throws IOException{
		
		for(int k=1; k<=amount; k++){
			String header = "s0@f0 -- a@f0 / 0 -> s0@f0\n";
					
			String clause = "";
			for(int i=1; i<=k; i++){
				clause = clause.concat("s"+(i-1)+"@f"+(i-1)+" -- a"+i+"@f"+i+" / 0 -> s"+i+"@f"+i+"\n");			
			}
			String prop_aux = header.concat(clause);
			
			clause = "";
			for(int i=1; i<=k; i++){
				clause = clause.concat("s"+i+"@f"+i+" -- a@f"+i+" / 1 -> s"+(i-1)+"@f"+(i-1)+"\n");			
			}			
			prop_aux = prop_aux.concat(clause);
			
			clause = "";
			for(int i=1; i<=k; i++){
				clause = clause.concat("s"+i+"@f"+i+" -- b@f"+i+" / o"+i+" -> s"+i+"@f"+i+"\n");			
			}			
			prop_aux = prop_aux.concat(clause);
			
			
			String path = "./"+folder+"/ffsm"+k+".txt";
			FileHandler fh = new FileHandler();
			fh.print_file(prop_aux, path);
		}
		
	}
	

	public void gen_FFSM_mid(String folder, int amount) throws IOException{
		
		for(int k=1; k<=amount; k++){
			String header = "s0@f0 -- a@f0 / 0 -> s0@f0\n";
					
			String clause = "";
			for(int i=1; i<=(k/2)+1; i++){
				clause = clause.concat("s0@f0 -- a"+i+"@f"+i+" / 0 -> s"+i+"@f"+i+"\n");			
			}
			String prop_aux = header.concat(clause);
			
			clause = "";
			for(int i=1; i<=(k/2)+1; i++){
				clause = clause.concat("s"+i+"@f"+i+" -- a@f"+i+" / 1 -> s0@f0\n");			
			}			
			prop_aux = prop_aux.concat(clause);
			
			clause = "";
			for(int i=1; i<=(k/2)+1; i++){
				clause = clause.concat("s"+i+"@f"+i+" -- b@f"+i+" / o"+i+" -> s"+i+"@f"+i+"\n");			
			}			
			prop_aux = prop_aux.concat(clause);
			
			
			clause = "";
			for(int i=(k/2)+2; i<=k; i++){
				clause = clause.concat("s"+(i-1)+"@f"+(i-1)+" -- a"+i+"@f"+i+" / 0 -> s"+i+"@f"+i+"\n");			
			}
			prop_aux = prop_aux.concat(clause);
			
			clause = "";
			for(int i=(k/2)+2; i<=k; i++){
				clause = clause.concat("s"+i+"@f"+i+" -- a@f"+i+" / 1 -> s"+(i-1)+"@f"+(i-1)+"\n");			
			}			
			prop_aux = prop_aux.concat(clause);
			
			clause = "";
			for(int i=(k/2)+2; i<=k; i++){
				clause = clause.concat("s"+i+"@f"+i+" -- b@f"+i+" / o"+i+" -> s"+i+"@f"+i+"\n");			
			}			
			prop_aux = prop_aux.concat(clause);
			
			
			String path = "./"+folder+"/ffsm"+k+".txt";
			FileHandler fh = new FileHandler();
			fh.print_file(prop_aux, path);
		}
		
	}
	
	public void gen_dot_FFSM(String ffsm_path, String dotpath) throws IOException, InterruptedException{
		FileHandler fh = new FileHandler();
				
		File file = new File(ffsm_path);
		FFSMModelReader reader = new FFSMModelReader(file);
		FFSM ffsm = reader.getFFSM();
		
		String clause = "";
		clause = clause.concat("digraph MefGraph{\n");
		clause = clause.concat("	node [fontsize=\"10\"]\n\n");
		clause = clause.concat("                  	rankdir=LR\n");
		for(FState f : ffsm.getFStates()){
			clause = clause.concat("	"+f.getStateName()+" [label=\""+f.getStateName()
					+"("+f.getCondition()+")"
					+"\"]\n");
		}
		for(FTransition t : ffsm.getFTransitions()){
			clause = clause.concat("	"+t.getSource().getStateName()+" -> "+t.getTarget().getStateName()
					+" [label=\""
					+t.getCInput().getIn()
					+"("+t.getCInput().getCond()+")/"
					+t.getOutput()
					+"\"]\n");
		}
		
		clause = clause.concat("}");
		
		fh.print_file(clause, dotpath); //dot -T pdf -o ffsm.pdf ffsm.dot
		String[] commands = {"dot","-T", "pdf", "-o", "./increase_random/dots/ffsm.pdf", "./increase_random/dots/ffsm.dot"};
		String result = fh.getProcessOutput(commands);
		
		String[] commands2 = {"gnome-open","./increase_random/dots/ffsm.pdf"};
		result = fh.getProcessOutput(commands2);			
	}
	
	public int get_configs_for_ffsm(String fsm_path)throws IOException, InterruptedException{
				
		File file = new File(fsm_path);
		FsmModelReader reader = new FsmModelReader(file, true);
		try {
			FiniteStateMachine fsm = reader.getFsm();
			s_found = new ArrayList<State>();
			s_found.add(fsm.getInitialState());
			
			tree = new Ntree();				
			tree.setRoot(new Node(fsm.getInitialState(), "and"));
			current_node = tree.getRoot();
			count = 0;
			
			rec_tree(fsm.getInitialState(), tree.getRoot());				
			//tree.print();
			//calculate number of configurations		
			int c = calc_config(tree.getRoot());			
			return c;
		} catch (Exception e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
		return 0;
	}
	
	public int get_configs_for_ffsm(String folder, int nfeatures)throws IOException, InterruptedException{
		
		FileHandler fh = new FileHandler();
		Random ran = new Random();
		int inputs = ran.nextInt(nfeatures) + 1;
		//int inputs = nfeatures;
		int states = nfeatures;
		int transitions = inputs*states;			
		String[] commands = {"./increase_random/fsm-gen-fsm","2", ""+inputs, ""+states, ""+transitions, "1"};
		String result = fh.getProcessOutput(commands);
		
		String path = "./"+folder+"/metafsm/fsm_xxx.txt";			
		fh.print_file(result, path);
		
		// create meta tree for FM			
		File file = new File(path);
		FsmModelReader reader = new FsmModelReader(file, true);
		try {
			FiniteStateMachine fsm = reader.getFsm();
			ArrayList<Transition> ts = fsm.getInitialState().getOut();
			s_found = new ArrayList<State>();
			s_found.add(fsm.getInitialState());
			
			tree = new Ntree();				
			tree.setRoot(new Node(fsm.getInitialState(), "and"));
			current_node = tree.getRoot();
			count = 0;
			
			rec_tree(fsm.getInitialState(), tree.getRoot());				
			//tree.print();
			//calculate number of configurations		
			int c = calc_config(tree.getRoot());	
			gen_random_FM(tree.getRoot(), folder, 1, nfeatures);
			return c;
		} catch (Exception e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
		return 0;
	}
	
	public int gen_random_FFSM_sample(String folder, int population, int sample, int nfeatures) 
			throws IOException, InterruptedException{
				
		ArrayList<HashMap<Ntree, Integer>> q1 = new ArrayList<HashMap<Ntree, Integer>>();
		ArrayList<HashMap<Ntree, Integer>> q2 = new ArrayList<HashMap<Ntree, Integer>>();
		ArrayList<HashMap<Ntree, Integer>> q3 = new ArrayList<HashMap<Ntree, Integer>>();
		ArrayList<HashMap<Ntree, Integer>> q4 = new ArrayList<HashMap<Ntree, Integer>>();
		ArrayList<HashMap<Ntree, Integer>> qall = new ArrayList<HashMap<Ntree, Integer>>();
		int min_sample = sample;
		
		// pick random trees from the population
		for(int k=1; k<=population; k++){						
			FileHandler fh = new FileHandler();			
			//./fsm-gen-fsm num-out num-in num-states num-trans randseed
			// random inputs=1 to n-1 
			// out=2
			// transitions inputs*states
			
			Random ran = new Random();
			int inputs = ran.nextInt(nfeatures) + 1;
			//int inputs = nfeatures;
			int states = nfeatures;
			int transitions = inputs*states;			
			String[] commands = {"./increase_random/fsm-gen-fsm","2", ""+inputs, ""+states, ""+transitions, ""+k};
			String result = fh.getProcessOutput(commands);
			
			String path = "./"+folder+"/metafsm/fsm_xxx.txt";			
			fh.print_file(result, path);
			
			// create meta tree for FM			
			File file = new File(path);
			FsmModelReader reader = new FsmModelReader(file, true);
			try {
				FiniteStateMachine fsm = reader.getFsm();
				ArrayList<Transition> ts = fsm.getInitialState().getOut();
				s_found = new ArrayList<State>();
				s_found.add(fsm.getInitialState());
				
				tree = new Ntree();				
				tree.setRoot(new Node(fsm.getInitialState(), "and"));
				current_node = tree.getRoot();
				count = 0;
				
				rec_tree(fsm.getInitialState(), tree.getRoot());				
				//tree.print();
				//calculate number of configurations		
				int c = calc_config(tree.getRoot());				
				
				//int max = (int) Math.pow(2, nfeatures);
				int min = 2;
				int count = 1;
				while(min < (nfeatures+1)){
					count++;
					min = (int) Math.pow(2, count);
				}
				
				int y1 = (int) Math.pow(2,(60*nfeatures)/100);
				int y2 = (int) Math.pow(2,(70*nfeatures)/100);
				int y3 = (int) Math.pow(2,(80*nfeatures)/100);
				int y4 = (int) Math.pow(2, nfeatures);
				//System.out.println("fsm_"+nfeatures+"_"+k+" Confs " + c);
				
				HashMap<Ntree, Integer> this_fsm = new HashMap<Ntree, Integer>();
				this_fsm.put(tree, c);
				if(c <= y1){
					if(q1.size() <= sample){
						//System.out.println("Added to 1");
						q1.add(this_fsm);
					}					
				}else if(c <= y2){
					if(q2.size() <= sample){
						//System.out.println("Added to 2");
						q2.add(this_fsm);
					}
				}else if(c <= y3){
					if(q3.size() <= sample){
						//System.out.println("Added to 3");
						q3.add(this_fsm);
					}
				}else if(c <= y4){
					if(q4.size() <= sample){
						//System.out.println("Added to 4");
						q4.add(this_fsm);
					}
				}else{
					System.out.println("Error!!! Invalid number of configurations");
				}
				
				//got enough?
				if(q1.size() == sample && q2.size() == sample &&
					 q3.size() == sample && q4.size() == sample){
					break;
				}
				
			} catch (Exception e) {
				// TODO Auto-generated catch block
				e.printStackTrace();
			}
		}
		
		// equilize samples		
		int s1 = q1.size();
		int s2 = q2.size();
		int s3 = q3.size();
		int s4 = q4.size();
		int min = sample;
		if(s1 < min){
			min = s1;
		}
		if(s2 < min){
			min = s2;
		}
		if(s3 < min){
			min = s3;
		}
		if(s4 < min){
			min = s4;
		}
		while(q1.size() > min){
			q1.remove(0);
		}
		while(q2.size() > min){
			q2.remove(0);
		}
		while(q3.size() > min){
			q3.remove(0);
		}
		while(q4.size() > min){
			q4.remove(0);
		}
		min_sample = min;
		
		//put all samples into one bowl
		for(int k=0; k<min_sample; k++){
			//qall.add(q1.get(k));
			qall.add(q2.get(k));
			qall.add(q3.get(k));
			//qall.add(q4.get(k));
		}

		if(min_sample < sample){
			System.out.println("Sample for "+nfeatures + " features is less than expected! "+min_sample
					+" "+q1.size()+" "+q2.size()+" "+q3.size()+" "+q4.size());
		}
		
		//work on samples (gen. FM and FFSMs)
		conf_map = new HashMap<String, Integer>();
		for(int k=1; k<=(min_sample*2); k++){
			for(Ntree tr : qall.get(k-1).keySet()){
				int confs = qall.get(k-1).get(tr);
				gen_random_FM(tr.getRoot(), folder, k, nfeatures);
				
				//gen FFSM
				String path_ffsm = "./"+folder+"/ffsms/ffsm_"+nfeatures+"_"+k+".txt";
				gen_FFSM_tree(tr.getRoot(), path_ffsm);
				
				//gen maximal fsm for the ffsm
				FsmModel gen = new FsmModel();
				String fsmpath = "./"+folder+"/fsm/fsm_"+nfeatures+"_"+k+".txt";
			    try {
			      gen.gen_FSM_tree(tr.getRoot(), fsmpath);
			    } catch (IOException e) {
			      e.printStackTrace();
			      throw new RuntimeException("Problems with creating the fsm model files");
			    }
				conf_map.put(fsmpath, confs);
			}
		}
		return (min_sample*2);
		
	}
	
	public void gen_random_FFSM(String folder, int amount, int nfeatures) 
			throws IOException, InterruptedException{
		
		conf_map = new HashMap<String, Integer>();
		
		for(int k=1; k<=amount; k++){						
			FileHandler fh = new FileHandler();			
			//./fsm-gen-fsm num-out num-in num-states num-trans randseed
			// random inputs=1 to n-1 
			// out=2
			// transitions inputs*states
			
			Random ran = new Random();
			int inputs = ran.nextInt(nfeatures) + 1;
			int states = nfeatures;
			int transitions = inputs*states;			
			String[] commands = {"./increase_random/fsm-gen-fsm","2", ""+inputs, ""+states, ""+transitions, ""+k};
			String result = fh.getProcessOutput(commands);
			
			String path = "./"+folder+"/metafsm/fsm_"+nfeatures+"_"+k+".txt";			
			fh.print_file(result, path);
			
			// create meta tree for FM			
			File file = new File(path);
			FsmModelReader reader = new FsmModelReader(file, true);
			try {
				FiniteStateMachine fsm = reader.getFsm();
				ArrayList<Transition> ts = fsm.getInitialState().getOut();
				s_found = new ArrayList<State>();
				s_found.add(fsm.getInitialState());
				
				tree = new Ntree();				
				tree.setRoot(new Node(fsm.getInitialState(), "and"));
				current_node = tree.getRoot();
				count = 0;
				
				rec_tree(fsm.getInitialState(), tree.getRoot());				
				//tree.print();
				//calculate number of configurations		
				int c = calc_config(tree.getRoot());
				//System.out.println("fsm_"+nfeatures+"_"+k+" Confs " + c);				

				gen_random_FM(tree.getRoot(), folder, k, nfeatures);
							
				//gen FFSM
				String path_ffsm = "./"+folder+"/ffsms/ffsm_"+nfeatures+"_"+k+".txt";
				gen_FFSM_tree(tree.getRoot(), path_ffsm);
				
				//gen maximal fsm for the ffsm
				FsmModel gen = new FsmModel();
				String fsmpath = "./"+folder+"/fsm/fsm_"+nfeatures+"_"+k+".txt";
			    try {
			      gen.gen_FSM_tree(tree.getRoot(), fsmpath);
			    } catch (IOException e) {
			      e.printStackTrace();
			      throw new RuntimeException("Problems with creating the fsm model files");
			    }
				conf_map.put(fsmpath, c);
				
			} catch (Exception e) {
				// TODO Auto-generated catch block
				e.printStackTrace();
			}
		}		
	}
	
	private int rec_find_conf(Node n, Node father){
		
		int sum = 1;
		if(n.getType().equals("and")){
			for(Node n1 : n.getChildren()){				
				sum = sum * rec_find_conf(n1, n);
			}
			if(father.getType().equals("alt")){
				return sum;
			}else{
				return sum+1;
			}
		}		
		if(n.getType().equals("or")){
			for(Node n1 : n.getChildren()){				
				sum = sum * rec_find_conf(n1, n);
			}
			if(father.getType().equals("alt")){
				return sum-1;
			}else{
				return sum;
			}
		}
		if(n.getType().equals("alt")){	
			for(Node n1 : n.getChildren()){
				sum = sum + rec_find_conf(n1, n);
			}
			if(father.getType().equals("alt")){
				return sum-1;
			}else{
				return sum;
			}			
		}		
		if(n.getType().equals("feature")){			
			if(father.getType().equals("feature")){
				if(n.getChildren().size() > 0){
					Node child = n.getChildren().get(0);
					return rec_find_conf(child, n)+1;
				}else return 2;
			}
			if(father.getType().equals("alt")){
				if(n.getChildren().size() > 0){
					Node child = n.getChildren().get(0);
					return rec_find_conf(child, n);
				}else return 1;				
			}if(father.getType().equals("and")){
				if(n.getChildren().size() > 0){
					Node child = n.getChildren().get(0);
					return rec_find_conf(child, n)+1;
				}else return 2;
			}
			if(father.getType().equals("or")){
				if(n.getChildren().size() > 0){
					Node child = n.getChildren().get(0);
					return rec_find_conf(child, n)+1;
				}else return 2;
			}
		}	
		return 0;
	}
	
	private int calc_config(Node n)
	{	
		int confs = 1;
		for(Node n1 : n.getChildren()){		
			int c = rec_find_conf(n1, n);
			confs = confs * c;
			//System.out.println(" root "+ n.getState().getLabel()+" child "
			//+ n1.getState().getLabel() + " confs "+c+" types "+n.getType()+" "+n1.getType());
		}
		return confs;
	}
	
	private void rec_genFFSM(Node n){		
		for(Node n1 : n.getChildren()){	
			String state1 = n.getState().getLabel();
			String state2 = n1.getState().getLabel();
			String input = state2;
			String output = state2;
			
			clause = clause.concat("s"+state1+"@f"+state1+" -- a"+input+"@f"+input+" / 0 -> s"+state2+"@f"+state2+"\n");
			clause = clause.concat("s"+state2+"@f"+state2+" -- a@f"+input+" / 1 -> s"+state1+"@f"+state1+"\n");	
			clause = clause.concat("s"+state2+"@f"+state2+" -- b@f"+input+" / o"+output+" -> s"+state2+"@f"+state2+"\n");
			rec_genFFSM(n1);			
		}
	}
	
	public void gen_FFSM_tree(Node root, String path_ffsm) throws IOException {
		
		String header = "s0@f0 -- a@f0 / 0 -> s0@f0\n";		
		clause = "";
		rec_genFFSM(root);
		
		String prop_aux = header.concat(clause);			
		
		FileHandler fh = new FileHandler();
		fh.print_file(prop_aux, path_ffsm);
	}
	
	public void gen_random_FM(Node root, String folder, int k, int nfeatures) throws IOException {
		//System.out.println("*****************");
		//System.out.println("Testing Tree");
		
		String header = "<?xml version=\"1.0\" encoding=\"UTF-8\" standalone=\"no\"?>\n";
		
		header = header.concat("	<featureModel chosenLayoutAlgorithm=\"4\">\n");
		header = header.concat("		<struct>\n");
		header = header.concat("			<and mandatory=\"true\" name=\"Root [f0]\">\n");
		
		clause = "";
		rec_genFM("			", root);
		//System.out.println("*****************");
		String bottom = "			</and>\n";
		bottom = bottom.concat("		</struct>\n");
		bottom = bottom.concat("		<constraints/>\n");
		bottom = bottom.concat("		<calculations Auto=\"true\" Constraints=\"true\" Features=\"true\" Redundant=\"true\" Tautology=\"true\"/>\n");
		bottom = bottom.concat("		<comments/>\n");
		bottom = bottom.concat("		<featureOrder userDefined=\"false\"/>\n");
		bottom = bottom.concat("	</featureModel>\n");
		
		String prop_aux = header.concat(clause);
		prop_aux = prop_aux.concat(bottom);		

		String path = "./"+folder+"/feature_models/example_"+nfeatures+"_"+k+".xml";
		FileHandler fh = new FileHandler();
		fh.print_file(prop_aux, path);
	}
	
	private void rec_genFM(String level, Node n)
	{
		//System.out.println(level + n.getState().getLabel() + "("+arclabel+")");
		//Iterator<String> number = n.getLabels().iterator();
		for(Node n1 : n.getChildren())
		{
			//print(level + "----", n1, arclabels.next());
			if(n1.getChildren().size() <= 0){
				clause = clause.concat(level + "	"+"<"+n1.getType()+" name=\"Optional [f"+n1.getState().getLabel()+"]\"/>\n");
			}else{
				clause = clause.concat(level + "	"+"<"+n1.getType()+" name=\"Optional [f"+n1.getState().getLabel()+"]\">\n");
				rec_genFM(level + "	", n1);
				clause = clause.concat(level + "	"+"</"+n1.getType()+">\n");				
			}
		}
	}
	
	public void rec_tree(State state, Node c_node){
		ArrayList<Transition> ts = state.getOut();	
		ArrayList<Node> st_cicle = new ArrayList<Node>();		
		//current_node = c_node;
		
		for(Transition t : ts){
			if(!s_found.contains(t.getOut())){				
				s_found.add(t.getOut());
				Node node = new Node(t.getOut(), "feature");
				//current_node.addChild(node);
				st_cicle.add(node);
				tree.addNode(c_node, node);
			}
		}
		if(st_cicle.size() > 1 && !c_node.equals(tree.getRoot())){
			String[] type = {"and", "or", "alt"};
			Random ran = new Random();
			int x = ran.nextInt(3);
			c_node.setType(type[x]);					
		}
		for(Node n : st_cicle){			
			rec_tree(n.getState(), n);
		}
	}
	
}
