package br.usp.icmc.fsm.logic;

import java.io.File;
import java.io.IOException;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.Map;

import javax.xml.parsers.DocumentBuilder;
import javax.xml.parsers.DocumentBuilderFactory;

import org.w3c.dom.Document;
import org.w3c.dom.NamedNodeMap;
import org.w3c.dom.Node;
import org.w3c.dom.NodeList;

import br.usp.icmc.ffsm.CommonPath;
import br.usp.icmc.ffsm.FFSM;
import br.usp.icmc.ffsm.FState;
import br.usp.icmc.ffsm.FTransition;
import br.usp.icmc.fsm.common.FileHandler;
import br.usp.icmc.fsm.reader.FFSMModelReader;

public class FFSMProperties 
{
	
	Map<FState,ArrayList<ArrayList<FTransition>>> path_map;
	Map<String,ArrayList<CommonPath>> seq_map;
	ArrayList<FTransition> no_loop_ft;
	ArrayList<FState> found_fc;
	ArrayList<FState> nfound_fc;
	String folder;
	
	FFSM ffsm;
	String prop;
	static String clause;
	static int features;
	static boolean optional;
	static ArrayList<String> all_ids;
	
	boolean islog, debug;
	static String log;
	
	public FFSMProperties(String folder, boolean islog, boolean debug){
		this.folder = folder;
		this.islog = islog;
		this.debug = debug;
		log = "";
	}
	
	public FFSMProperties(String folder){
		this.folder = folder;
	}
	
	public String getlog(){
		return log;
	}
	
	public boolean set_checkFFSM(String ffsm_path, String prop) throws IOException, InterruptedException{
		File file = new File(ffsm_path);
		FFSMModelReader reader = new FFSMModelReader(file);
		ffsm = reader.getFFSM();
		this.prop = prop;
				
		FState fs = check_conditional_state(ffsm.getFStates());
		if(fs != null){
			System.out.println("Invalid conditional state "+ fs + " on "+ ffsm_path);
			return false;
		}
		
		FTransition t = check_transition(ffsm.getFTransitions());
		if(t != null){
			System.out.println("Invalid transition "+ t + " on "+ ffsm_path);
			return false;
		}
		
		return true;
	}	
	
	public FState check_conditional_state(ArrayList<FState> l) 
			throws IOException, InterruptedException{
				
		String header = prop;		
		String clause = "";
		
		for(FState fs: l){
			clause = clause.concat("(push)\n");
			clause = clause.concat("(assert "+fs.getCondition()+")\n");		
			clause = clause.concat("(check-sat)\n");
			clause = clause.concat("(pop)\n");
		}
		
		String prop_aux = header.concat(clause);
		// print stm2 file and execute
		String fpath = "./"+folder+"/f_cds.smt2";
		FileHandler fh = new FileHandler();
		fh.print_file(prop_aux, fpath);
		
		//System.out.println(prop_aux);
		
		String[] commands = {"./ffsm/z3","./"+folder+"/f_cds.smt2"};
		String result = fh.getProcessOutput(commands);		
		String[] outs = result.split("\n");
		
		for(int i=0; i<outs.length; i++){
			if(outs[i].equals("unsat")){
				return l.get(i);
			}
		}
		// Ok there is no invalid conditional state
		return null;	
	}
		
	public FTransition check_transition(ArrayList<FTransition> l) 
			throws IOException, InterruptedException{
				
		String header = prop;
		String clause = "";
		
		for(FTransition ft: l){
			clause = clause.concat("(push)\n");
			clause = clause.concat("(assert (and "+ft.getSource().getCondition()
					+" "+ft.getCInput().getCond()+" "+ft.getTarget().getCondition()+"))\n");		
			clause = clause.concat("(check-sat)\n");
			clause = clause.concat("(pop)\n");
		}
		
		String prop_aux = header.concat(clause);
		// print stm2 file and execute
		String fpath = "./"+folder+"/f_cts.smt2";
		FileHandler fh = new FileHandler();
		fh.print_file(prop_aux, fpath);
				
		String[] commands = {"./ffsm/z3","./"+folder+"/f_cts.smt2"};
		String result = fh.getProcessOutput(commands);		
		String[] outs = result.split("\n");
						
		for(int i=0; i<outs.length; i++){
			if(outs[i].equals("unsat")){
				return l.get(i);
			}
		}
		// Ok there is no invalid conditional state
		return null;	
	}
	
	public String read_XML_FeatureModel(String featuremodel){
		try {
			File fXmlFile = new File(featuremodel);
			DocumentBuilderFactory dbFactory = DocumentBuilderFactory.newInstance();
			DocumentBuilder dBuilder = dbFactory.newDocumentBuilder();
			Document doc = dBuilder.parse(fXmlFile);
					
			doc.getDocumentElement().normalize();
			log = "";
	
			if(islog) log = log.concat("Root element :" + doc.getDocumentElement().getNodeName()+"\n");
			
			if (doc.hasChildNodes()) {	
				features = 0;
				clause = "";
				
				Node root = getRoot(doc.getChildNodes().item(0).getChildNodes()).item(0).getParentNode();
				//if(islog)printNote(root.getChildNodes());	
				
				all_ids = new ArrayList<String>();				
				createTree(root.getChildNodes(), "and", "root");				
						
				if(islog) log = log.concat("Features "+features+"\n");
				String aux_clause = "(define-sort Feature () Bool)\n";
				for(String id : all_ids){
					aux_clause = aux_clause.concat("(declare-const "+id+" Feature)\n");
				}				
				clause = clause.concat("))\n\n");
				
				String body = clause;
				clause = aux_clause;
				clause = clause.concat(body);
									
				if(islog) log = log.concat(clause+"\n");
			}			
			
	    } catch (Exception e) {
	    	e.printStackTrace();
	    }
		return clause;
	}
	
	public NodeList getRoot(NodeList nodeList){
		
		for (int count = 0; count < nodeList.getLength(); count++) {
			Node tempNode = nodeList.item(count);	
			// make sure it's element node.
			if (tempNode.getNodeType() == Node.ELEMENT_NODE) {
				if(tempNode.getNodeName().equals("struct")){					
					return tempNode.getChildNodes();
				}
			}
		}		
		return null;
	}
	
	private static ArrayList<String> createTree(NodeList nodeList, String parent_type, String parent_id) {
		ArrayList<String> ids = new ArrayList<String>();
	    
		for (int count = 0; count < nodeList.getLength(); count++) {
			Node tempNode = nodeList.item(count);			
			
			if (tempNode.getNodeType() == Node.ELEMENT_NODE) {	
				String id = handleNode(tempNode);
				ids.add(id);
				
				if((parent_type.equals("and") || parent_type.equals("feature")) && !parent_id.equals("root")){						
					if(optional){
						clause = clause.concat("   (=> "+id+" "+parent_id+")\n");
					}else{
						clause = clause.concat("   (= "+id+" "+parent_id+")\n");
					}
				}
				
				if(tempNode.getNodeName().equals("and")){					
					if(parent_id.equals("root")){
						clause = clause.concat("\n(assert "+id+")\n");
						clause = clause.concat("(assert (and\n");
					}
					createTree(tempNode.getChildNodes(), "and", id);
				}
				if(tempNode.getNodeName().equals("alt")){					
					
					ArrayList<String> child_ids = createTree(tempNode.getChildNodes(), "alt", id);
					ArrayList<String> child_ids2 = (ArrayList<String>) child_ids.clone();
					clause = clause.concat("   (= (or");
					for(String d1: child_ids){
						clause = clause.concat(" "+d1+" ");
					}
					clause = clause.concat(") "+id+")\n");
					for(String d1: child_ids){
						child_ids2.remove(d1);
						for(String d2: child_ids2){
							clause = clause.concat("   (not (and "+d1+" "+d2+"))\n");
						}
					}															
				}
				if(tempNode.getNodeName().equals("or")){
					ArrayList<String> child_ids = createTree(tempNode.getChildNodes(), "or", id);
					clause = clause.concat("   (= (or");
					for(String d1: child_ids){
						clause = clause.concat(" "+d1+" ");
					}					
					clause = clause.concat(") "+id+")\n");
				}
				if(tempNode.getNodeName().equals("feature")){
											
					createTree(tempNode.getChildNodes(), "feature", id);	
				}
							
			}	
		}
	    return ids;
	}
	
	private static ArrayList<String> createTree_old(NodeList nodeList, String parent_type, String parent_id) {
		ArrayList<String> ids = new ArrayList<String>();
	    for (int count = 0; count < nodeList.getLength(); count++) {
			Node tempNode = nodeList.item(count);
			
			if (tempNode.getNodeType() == Node.ELEMENT_NODE) {								
				if(tempNode.getNodeName().equals("and")){
					String id = handleNode(tempNode);
					ids.add(id);
					if(parent_id.equals("root")){
						clause = clause.concat("\n(assert "+id+")\n");
						clause = clause.concat("(assert (and\n");
					}					
					if(parent_id.equals("and") || parent_id.equals("feature")){
						if(optional){
							clause = clause.concat("   (=> "+id+" "+parent_id+")\n");
						}else{
							clause = clause.concat("   (= "+id+" "+parent_id+")\n");
						}						
					}
					if(parent_id.equals("alt") || parent_id.equals("or")){
						clause = clause.concat(" "+id+" ");
					}
					if(tempNode.getChildNodes() != null && tempNode.getChildNodes().getLength() > 0){
						createTree(tempNode.getChildNodes(), "and", id);
					}					
				}
				if(tempNode.getNodeName().equals("alt")){					
					String id = handleNode(tempNode);
					ids.add(id);
					if(parent_id.equals("and") || parent_id.equals("feature")){
						if(optional){
							clause = clause.concat("   (=> "+id+" "+parent_id+")\n");
						}else{
							clause = clause.concat("   (= "+id+" "+parent_id+")\n");
						}						
					}
					if(parent_id.equals("alt") || parent_id.equals("or")){
						clause = clause.concat(" "+id+" ");						
					}
					
					clause = clause.concat("   (= (or");
					ArrayList<String> child_ids = createTree(tempNode.getChildNodes(), "alt", id);
					ArrayList<String> child_ids2 = (ArrayList<String>) child_ids.clone();
					clause = clause.concat(") "+id+")\n");
					for(String d1: child_ids){
						child_ids2.remove(d1);
						for(String d2: child_ids2){
							clause = clause.concat("   (not (and "+d1+" "+d2+"))\n");
						}
					}
					
					if(tempNode.getChildNodes() != null && tempNode.getChildNodes().getLength() > 0){
						createTree(tempNode.getChildNodes(), "and", id);
					}
										
				}
				if(tempNode.getNodeName().equals("or")){					
					String id = handleNode(tempNode);
					ids.add(id);
					
					if(optional){
						clause = clause.concat("   (=> "+id+" "+parent_id+")\n");
					}else{
						clause = clause.concat("   (= "+id+" "+parent_id+")\n");
					}						
					
					clause = clause.concat("   (= (or");
					ArrayList<String> child_ids = createTree(tempNode.getChildNodes(), "or", id);					
					clause = clause.concat(") "+id+")\n");
				}
				if(tempNode.getNodeName().equals("feature")){
					String id = handleNode(tempNode);
					ids.add(id);				
					if(parent_id.equals("and") || parent_id.equals("feature")){
						if(optional){
							clause = clause.concat("   (=> "+id+" "+parent_id+")\n");
						}else{
							clause = clause.concat("   (= "+id+" "+parent_id+")\n");
						}
					}
					if(parent_id.equals("alt") || parent_id.equals("or")){
						clause = clause.concat(" "+id+" ");
					}										
					
					if(tempNode.getChildNodes() != null && tempNode.getChildNodes().getLength() > 0){
						createTree(tempNode.getChildNodes(), "feature", id);
					}				
				}
							
			}	
		}
	    return ids;
	}
	
	public static String handleNode(Node tempNode){
		features++;
		optional = true;
		NamedNodeMap nodeMap = tempNode.getAttributes();
		String feature_id = "";
		for (int i = 0; i < nodeMap.getLength(); i++) {	
			Node node = nodeMap.item(i);
			if(node.getNodeName().equals("name")){
				String aux = node.getNodeValue();
				feature_id = aux.substring(aux.lastIndexOf("[")+1,aux.lastIndexOf("]"));						 
			}
			if(node.getNodeName().equals("mandatory")){
				if(node.getNodeValue().equals("true")){
					optional = false;
				}
			}
		}			
		all_ids.add(feature_id);
		return feature_id;
	}
	
	private static void printNote(NodeList nodeList) {

	    for (int count = 0; count < nodeList.getLength(); count++) {
			Node tempNode = nodeList.item(count);	
			// make sure it's element node.
			if (tempNode.getNodeType() == Node.ELEMENT_NODE) {				
				// get node name and value				
				log = log.concat("\nNode Name =" + tempNode.getNodeName() + " [OPEN]"+"\n");				
				if (tempNode.hasAttributes()) {	
					// get attributes names and values
					NamedNodeMap nodeMap = tempNode.getAttributes();	
					for (int i = 0; i < nodeMap.getLength(); i++) {	
						Node node = nodeMap.item(i);							
						log = log.concat("attr name : " + node.getNodeName()+"\n");
						log = log.concat("attr value : " + node.getNodeValue()+"\n");
					}	
				}	
				if (tempNode.hasChildNodes()) {	
					// loop again if has child nodes
					printNote(tempNode.getChildNodes());	
				}					
				log = log.concat("Node Name =" + tempNode.getNodeName() + " [CLOSE]"+"\n");
			}	
		}
	}	
	
	public boolean is_deterministic(){
		
		boolean deterministic = true;
		try	{
			log = "";
			String clause = "";	
			
			deter:for(FState fst : ffsm.getFStates()){				
				ArrayList<FTransition> stx1 = (ArrayList<FTransition>) fst.getOut().clone();
				ArrayList<FTransition> stx2 = (ArrayList<FTransition>) fst.getOut().clone();				
				for(FTransition ft: stx1){					
					stx2.remove(ft);					
					for(FTransition ft2 : stx2){
						if(ft.getCInput().getIn().equals(ft2.getCInput().getIn())){
							if(islog) log = log.concat("Checking transitions "+ft+" and "+ft2+"\n");
							if(debug) System.out.println("Checking transitions "+ft+" and "+ft2);							
							clause = clause.concat("(push)\n");				
							clause = clause.concat("(assert (and \n");
							clause = clause.concat("    (and "+
									ft.getSource().getCondition()+" "+
									ft.getCInput().getCond()+" "+
									ft.getTarget().getCondition()+")\n");
							clause = clause.concat("    (and "+
									ft2.getSource().getCondition()+" "+
									ft2.getCInput().getCond()+" "+
									ft2.getTarget().getCondition()+")\n");
							clause = clause.concat("))\n");
							clause = clause.concat("(check-sat)\n");
							clause = clause.concat("(pop)\n");							
						}						
					}					
				}
			}
			if(!clause.equals("")){
				String prop_aux = prop.concat(clause);
				// print stm2 file and execute
				//String path = "./"+folder+"/f_deter_"+count+".smt2";
				String path = "./"+folder+"/f_deter.smt2";
				FileHandler fh = new FileHandler();
				fh.print_file(prop_aux, path);
				
				//String[] commands = {"./ffsm/z3","./"+folder+"/f_deter_"+count+".smt2"};
				String[] commands = {"./ffsm/z3","./"+folder+"/f_deter.smt2"};
				String result = fh.getProcessOutput(commands);							
				String[] outs = result.split("\n");
							
				for(int i=0; i<outs.length; i++){
					if(outs[i].equals("sat")){
						return false;
					}
				}
			}			
		}
		catch(Exception ex)		{
			ex.printStackTrace();
			return false;
		}
		return deterministic;
	}
	
	public boolean is_deterministic_old2(){
		
		boolean deterministic = true;
		try	{						
			int count = 0;
			log = "";
			
			deter:for(FState fst : ffsm.getFStates()){				
				ArrayList<FTransition> stx1 = (ArrayList<FTransition>) fst.getOut().clone();
				ArrayList<FTransition> stx2 = (ArrayList<FTransition>) fst.getOut().clone();				
				for(FTransition ft: stx1){					
					stx2.remove(ft);					
					for(FTransition ft2 : stx2){
						if(ft.getCInput().getIn().equals(ft2.getCInput().getIn())){
							if(islog) log = log.concat("Checking transitions "+ft+" and "+ft2+"\n");
							if(debug) System.out.println("Checking transitions "+ft+" and "+ft2);
							count++;
							String clause = "";							
							clause = clause.concat("(assert (and \n");
							clause = clause.concat("    (and "+
									ft.getSource().getCondition()+" "+
									ft.getCInput().getCond()+" "+
									ft.getTarget().getCondition()+")\n");
							clause = clause.concat("    (and "+
									ft2.getSource().getCondition()+" "+
									ft2.getCInput().getCond()+" "+
									ft2.getTarget().getCondition()+")\n");
							clause = clause.concat("))\n");
							clause = clause.concat("(check-sat)");
							String prop_aux = prop.concat(clause);
							// print stm2 file and execute
							//String path = "./"+folder+"/f_deter_"+count+".smt2";
							String path = "./"+folder+"/f_deter.smt2";
							FileHandler fh = new FileHandler();
							fh.print_file(prop_aux, path);
							
							//String[] commands = {"./ffsm/z3","./"+folder+"/f_deter_"+count+".smt2"};
							String[] commands = {"./ffsm/z3","./"+folder+"/f_deter.smt2"};
							String result = fh.getProcessOutput(commands);							
							String[] outs = result.split("\n");
							
							if(outs[0].equals("sat")){
								deterministic = false;
								break deter;								
							}else{
								if(islog) log = log.concat("OK"+"\n");
								if(debug) System.out.println("OK");
							}
						}						
					}					
				}
			}					
		}
		catch(Exception ex)		{
			ex.printStackTrace();
			return false;
		}
		return deterministic;
	}
	
	public boolean is_complete(){
		
		boolean complete = true;
		try	{								
			log = "";			
			String clause = "";
			
			for(FState fst : ffsm.getFStates()){					
				if(islog) log = log.concat("Conditional State "+fst+"\n");
				for(String in: ffsm.getInputAlphabet()){					
					if(islog) log = log.concat("		"+in+"\n");					
					
					clause = clause.concat("(push)\n");
					clause = clause.concat("(assert "+fst.getCondition()+")\n");
					clause = clause.concat("(assert (and \n");
					boolean in_found = false;
					for(FTransition ft: fst.getOut()){							
						if(ft.getCInput().getIn().equals(in)){
							in_found = true;
							clause = clause.concat("    (not (and "+									
									ft.getCInput().getCond()+" "+
									ft.getTarget().getCondition()+"))\n");
						}						
					}
					if(in_found){
						clause = clause.concat("))\n");
						clause = clause.concat("(check-sat)\n");
						clause = clause.concat("(pop)\n");										
					}else{
						if(islog) log = log.concat("Not OK"+"\n");
						//System.out.println("NOT OK");
						return false;						
					}
				}
			}
			if(!clause.equals("")){
				String prop_aux = prop.concat(clause);
				// print stm2 file and execute
				//String path = "./"+folder+"/f_comp_"+count+".smt2";
				String path = "./"+folder+"/f_comp.smt2";
				FileHandler fh = new FileHandler();
				fh.print_file(prop_aux, path);
				
				//String[] commands = {"./ffsm/z3","./"+folder+"/f_comp_"+count+".smt2"};
				String[] commands = {"./ffsm/z3","./"+folder+"/f_comp.smt2"};
				String result = fh.getProcessOutput(commands);						
				String[] outs = result.split("\n");
				
				for(int i=0; i<outs.length; i++){
					if(outs[i].equals("sat")){
						return false;
					}
				}
			}
		}
		catch(Exception ex)	{
			ex.printStackTrace();
			return false;			
		}		
		return complete;
	}
	
	public boolean is_complete_old2(){
		
		boolean complete = true;
		try	{								
			log = "";
			int count = 0;
			
			complete:for(FState fst : ffsm.getFStates()){					
				if(islog) log = log.concat("Conditional State "+fst+"\n");
				for(String in: ffsm.getInputAlphabet()){					
					if(islog) log = log.concat("		"+in+"\n");
					count++;
					String clause = "";
					clause = clause.concat("(assert "+fst.getCondition()+")\n");
					clause = clause.concat("(assert (and \n");
					boolean in_found = false;
					for(FTransition ft: fst.getOut()){							
						if(ft.getCInput().getIn().equals(in)){
							in_found = true;
							clause = clause.concat("    (not (and "+									
									ft.getCInput().getCond()+" "+
									ft.getTarget().getCondition()+"))\n");
						}						
					}
					if(in_found){
						clause = clause.concat("))\n");
						clause = clause.concat("(check-sat)");
						String prop_aux = prop.concat(clause);
						// print stm2 file and execute
						//String path = "./"+folder+"/f_comp_"+count+".smt2";
						String path = "./"+folder+"/f_comp.smt2";
						FileHandler fh = new FileHandler();
						fh.print_file(prop_aux, path);
						
						//String[] commands = {"./ffsm/z3","./"+folder+"/f_comp_"+count+".smt2"};
						String[] commands = {"./ffsm/z3","./"+folder+"/f_comp.smt2"};
						String result = fh.getProcessOutput(commands);						
						String[] outs = result.split("\n");
												
						if(outs[0].equals("sat")){
							complete = false; 
							break complete;							
						}					
					}else{
						if(islog) log = log.concat("Not OK"+"\n");
						complete = false;												 
						break complete;						
					}
				}
			}
		}
		catch(Exception ex)	{
			ex.printStackTrace();
			return false;			
		}		
		return complete;
	}
	
	public boolean is_initially_connected(){
		
		boolean init_con = true;
		try	{			
			log = "";
			if(islog) log = log.concat("Conditional States "+ffsm.getFStates()+"\n");		
			//if(islog) log = log.concat("Transitions "+ffsm.getFTransitions()+"\n");		
			if(islog) log = log.concat("Conditional Inputs "+ffsm.getInputAlphabet()+"\n");		
			if(islog) log = log.concat("Outputs "+ffsm.getOutputAlphabet()+"\n");
						
			//find paths
			find_all_paths();
			if(islog) print_paths(path_map);
			if(islog) log = log.concat("\n\nConditional States "+ffsm.getFStates()+"\n\n");
			
			//check valid paths
			boolean epath = check_valid_paths(prop);			
			if(islog) log = log.concat("\nRemoving invalid paths\n"+"\n");	
			if(islog) print_paths(path_map);			
			if(!epath){
				return false;
			}
			
			//check reachability of products
			boolean cpath = check_product_coverage(prop);
			if(!cpath){
				return false;
			}
			
		}
		catch(Exception ex)
		{
			ex.printStackTrace();
			return false;
		}				
		return init_con;
	}
	
	public boolean is_initially_connected_old2(){
		
		boolean init_con = true;
		try	{			
			log = "";
			if(islog) log = log.concat("Conditional States "+ffsm.getFStates()+"\n");		
			//if(islog) log = log.concat("Transitions "+ffsm.getFTransitions()+"\n");		
			if(islog) log = log.concat("Conditional Inputs "+ffsm.getInputAlphabet()+"\n");		
			if(islog) log = log.concat("Outputs "+ffsm.getOutputAlphabet()+"\n");
						
			//find paths
			find_all_paths();
			if(islog) print_paths(path_map);
			if(islog) log = log.concat("\n\nConditional States "+ffsm.getFStates()+"\n\n");
			
			//check valid paths
			boolean epath = check_valid_paths_old(prop);			
			if(islog) log = log.concat("\nRemoving invalid paths\n"+"\n");	
			if(islog) print_paths(path_map);			
			if(!epath){
				return false;
			}
			
			//check reachability of products
			boolean cpath = check_product_coverage_old(prop);
			if(!cpath){
				return false;
			}
			
		}
		catch(Exception ex)
		{
			ex.printStackTrace();
			return false;
		}				
		return init_con;
	}
	
	public boolean is_minimal_old2(){
		
		boolean minimal = true;
		try	{									
			log = "";
			if(islog) log = log.concat("Conditional States "+ffsm.getFStates()+"\n");		
			//if(islog) log = log.concat("Transitions "+ffsm.getFTransitions()+"\n");		
			if(islog) log = log.concat("Conditional Inputs "+ffsm.getInputAlphabet()+"\n");		
			if(islog) log = log.concat("Outputs "+ffsm.getOutputAlphabet()+"\n");
			
			//String[] outs = check_state_pairs();
			
			int count = 0;
			ArrayList<FState> fs_aux = (ArrayList<FState>) ffsm.getFStates().clone();
			for(FState fs1 : ffsm.getFStates()){
				fs_aux.remove(fs1);
				for(FState fs2 : fs_aux){
					//if(outs[count].equals("sat")){
					if(check_state_pair_old(prop, fs1, fs2)){
						boolean stilltrue = find_and_check_disting_seq_old(prop, fs1, fs2, ffsm.getNumberOfFStates());
						if(!stilltrue){
							return false;
						}
					}
					count++;
				}					
			}
		}
		catch(Exception ex)
		{
			ex.printStackTrace();
			return false;
		}		
		return minimal;
	}
	
	public boolean is_minimal(){
		
		boolean minimal = true;
		try	{									
			log = "";
			if(islog) log = log.concat("Conditional States "+ffsm.getFStates()+"\n");		
			//if(islog) log = log.concat("Transitions "+ffsm.getFTransitions()+"\n");		
			if(islog) log = log.concat("Conditional Inputs "+ffsm.getInputAlphabet()+"\n");		
			if(islog) log = log.concat("Outputs "+ffsm.getOutputAlphabet()+"\n");
			
			String[] outs = check_state_pairs();
			
			int count = 0;
			ArrayList<FState> fs_aux = (ArrayList<FState>) ffsm.getFStates().clone();
			for(FState fs1 : ffsm.getFStates()){
				fs_aux.remove(fs1);
				for(FState fs2 : fs_aux){
					if(outs[count].equals("sat")){
						boolean stilltrue = find_and_check_disting_seq(prop, fs1, fs2, ffsm.getNumberOfFStates());
						if(!stilltrue){
							return false;
						}
					}
					count++;
				}					
			}
		}
		catch(Exception ex)
		{
			ex.printStackTrace();
			return false;
		}		
		return minimal;
	}
	
	public boolean find_and_check_disting_seq(String header, FState fs1, FState fs2, int n) 
			throws IOException, InterruptedException{
							
		ArrayList<FTransition> current_out1 = fs1.getOut();
		ArrayList<FTransition> current_out2 = fs2.getOut();				
		seq_map = new HashMap<String,ArrayList<CommonPath>>();	
		boolean found_input = false;
						
		//process distinguish seq size 1
		String[] outs = check_common_pair(header, current_out1, current_out2, fs1, fs2);
		
		int count = 0;
		for(String in : ffsm.getInputAlphabet()){			
			seq_map.put(in, new ArrayList<CommonPath>());
			for(FTransition co1 : current_out1){
				for(FTransition co2 : current_out2){
					//check the same input
					if(co1.getCInput().getIn().equals(in) 
							&& co2.getCInput().getIn().equals(in)){	
						//Is there a product for both transitions?
						if(outs[count].equals("sat")){
							CommonPath cnew = new CommonPath(fs1, fs2, n);
							//They...
							//1-Can be distinguished? (identification)
							//2-Max size path is less than n-1?
							//3-Is there a valid path (products) for both transitions?
							if(cnew.addCommon(co1, co2)){
								seq_map.get(in).add(cnew);
								found_input = true;
							}
						}
						count++;
					}					
				}
			}	
		}	
		
		if(!found_input){			
			if(islog) log = log.concat("Could not find a input for "+ fs1 + " and "+fs2+"\n");
			if(debug) System.out.println("Could not find a input for "+ fs1 + " and "+fs2);
			return false;
		}
		
		//print
		if(islog || debug) print_common_pairs(fs1, fs2);	
		
		//check input		
		ArrayList<String> alp = new ArrayList<String>();
		for(String s : ffsm.getInputAlphabet()){
			alp.add(s);
		}			
		for(int i=1; i<=alp.size(); i++){			
			ArrayList<ArrayList<String>> inchecklist = find_inset(i,alp.size(),alp);			
			if(islog) log = log.concat("CHECKING"+"\n");
			if(debug) System.out.println("CHECKING");
			for(ArrayList<String> incheck : inchecklist){				
				if(islog) log = log.concat(incheck+"\n");
				if(debug) System.out.println(incheck);
				ArrayList<String> inputset = check_disting_old(header, fs1, fs2, seq_map, incheck);
				if(inputset != null){					
					if(islog) log = log.concat("\nState pair "+fs1+" and "+fs2+" OK for inputset "+inputset+"\n"+"\n");
					if(debug) System.out.println("\nState pair "+fs1+" and "+fs2+" OK for inputset "+inputset+"\n");
					return true;
				}
			}			
		}	
					
		
		//recursive call to n-1
		for(String in : ffsm.getInputAlphabet()){
			ArrayList<CommonPath> caux = (ArrayList<CommonPath>) seq_map.get(in).clone();
			for(CommonPath cp : caux){
				FState a1 = cp.get1().get(cp.get1().size()-1).getTarget();
				FState a2 = cp.get2().get(cp.get2().size()-1).getTarget();				
				//if both do not lead to the same state, and both are not self loops
				if(!a1.equals(a2) && !(fs1.equals(a1) && (fs2.equals(a2)))){
					seq_map.get(in).clear();					
					if(islog) log = log.concat(" WHAT? "+ fs1+" -> "+a1 + " "+fs2+" -> "+" "+a2+ " input "+in +"\n");
					if(debug) System.out.println(" WHAT? "+ fs1+" -> "+a1 + " "+fs2+" -> "+" "+a2+ " input "+in);
					boolean got = rec_common(header, a1, a2, cp, in);
					if(got){						
						if(islog) log = log.concat("GOT "+ fs1+" "+fs2 + " "+a1+" "+" "+a2+ " "+in+"\n");
						if(debug) System.out.println("GOT "+ fs1+" "+fs2 + " "+a1+" "+" "+a2+ " "+in);
						return true;
					}
				}				
			}
		}
				
		if(islog) log = log.concat("Could no find a seq. for "+ fs1 + " and "+fs2+"\n");
		if(debug) System.out.println("Could no find a seq. for "+ fs1 + " and "+fs2);
		//could not find a distinguishing sequence...
		return false;
	}
	
	public boolean find_and_check_disting_seq_old(String header, FState fs1, FState fs2, int n) 
			throws IOException, InterruptedException{
							
		ArrayList<FTransition> current_out1 = fs1.getOut();
		ArrayList<FTransition> current_out2 = fs2.getOut();				
		seq_map = new HashMap<String,ArrayList<CommonPath>>();	
		boolean found_input = false;
						
		//process distinguish seq size 1
		//String[] outs = check_common_pair(header, current_out1, current_out2, fs1, fs2);
		
		int count = 0;
		for(String in : ffsm.getInputAlphabet()){			
			seq_map.put(in, new ArrayList<CommonPath>());
			for(FTransition co1 : current_out1){
				for(FTransition co2 : current_out2){
					//check the same input
					if(co1.getCInput().getIn().equals(in) 
							&& co2.getCInput().getIn().equals(in)){	
						//Is there a product for both transitions?
						//if(outs[count].equals("sat")){
						if(check_common_pair_old(header, fs1, fs2, co1, co2)){
							CommonPath cnew = new CommonPath(fs1, fs2, n);
							//They...
							//1-Can be distinguished? (identification)
							//2-Max size path is less than n-1?
							//3-Is there a valid path (products) for both transitions?
							if(cnew.addCommon_old(header, co1, co2)){
								seq_map.get(in).add(cnew);
								found_input = true;
							}
						}
						count++;
					}					
				}
			}	
		}	
		
		if(!found_input){			
			if(islog) log = log.concat("Could not find a input for "+ fs1 + " and "+fs2+"\n");
			if(debug) System.out.println("Could not find a input for "+ fs1 + " and "+fs2);
			return false;
		}
		
		//print
		if(islog || debug) print_common_pairs(fs1, fs2);	
		
		//check input		
		ArrayList<String> alp = new ArrayList<String>();
		for(String s : ffsm.getInputAlphabet()){
			alp.add(s);
		}				
		for(int i=1; i<=alp.size(); i++){			
			ArrayList<ArrayList<String>> inchecklist = find_inset(i,alp.size(),alp);			
			if(islog) log = log.concat("CHECKING"+"\n");
			if(debug) System.out.println("CHECKING");
			for(ArrayList<String> incheck : inchecklist){				
				if(islog) log = log.concat(incheck+"\n");
				if(debug) System.out.println(incheck);
				ArrayList<String> inputset = check_disting_old(header, fs1, fs2, seq_map, incheck);
				if(inputset != null){					
					if(islog) log = log.concat("\nState pair "+fs1+" and "+fs2+" OK for inputset "+inputset+"\n"+"\n");
					if(debug) System.out.println("\nState pair "+fs1+" and "+fs2+" OK for inputset "+inputset+"\n");
					return true;
				}
			}			
		}				
		
		//recursive call to n-1
		for(String in : ffsm.getInputAlphabet()){
			ArrayList<CommonPath> caux = (ArrayList<CommonPath>) seq_map.get(in).clone();
			for(CommonPath cp : caux){
				FState a1 = cp.get1().get(cp.get1().size()-1).getTarget();
				FState a2 = cp.get2().get(cp.get2().size()-1).getTarget();				
				//if both do not lead to the same state, and both are not self loops
				if(!a1.equals(a2) && !(fs1.equals(a1) && (fs2.equals(a2)))){
					seq_map.get(in).clear();					
					if(islog) log = log.concat(" WHAT? "+ fs1+" -> "+a1 + " "+fs2+" -> "+" "+a2+ " input "+in +"\n");
					if(debug) System.out.println(" WHAT? "+ fs1+" -> "+a1 + " "+fs2+" -> "+" "+a2+ " input "+in);
					boolean got = rec_common_old(header, a1, a2, cp, in);
					if(got){						
						if(islog) log = log.concat("GOT "+ fs1+" "+fs2 + " "+a1+" "+" "+a2+ " "+in+"\n");
						if(debug) System.out.println("GOT "+ fs1+" "+fs2 + " "+a1+" "+" "+a2+ " "+in);
						return true;
					}
				}				
			}
		}
				
		if(islog) log = log.concat("Could no find a seq. for "+ fs1 + " and "+fs2+"\n");
		if(debug) System.out.println("Could no find a seq. for "+ fs1 + " and "+fs2);
		//could not find a distinguishing sequence...
		return false;
	}
	
	public ArrayList<ArrayList<String>> find_inset(int size, int max, ArrayList<String> alp){		
		ArrayList<ArrayList<String>> inchecklist = new ArrayList<ArrayList<String>>();
		for(int i=size; i<=max; i++){
			for(String in1 : alp){
				ArrayList<String> inset = new ArrayList<String>();
				inset.add(in1);
				if(inset.size() < i){	
					ArrayList<String> inset2 = (ArrayList<String>) inset.clone();
					for(String in2 : alp){						
						if(!in1.equals(in2)){							
							inset2.add(in2);
							if(inset2.size() >= i){
								inchecklist.add(inset2);
								inset2 = (ArrayList<String>) inset.clone();
							}
						}						
					}
				}else inchecklist.add(inset);				
			}
		}
		return inchecklist;
	}
	
	public boolean rec_common(String header, FState fs1, FState fs2, CommonPath cp, String lastinput) 
			throws IOException, InterruptedException{
		ArrayList<FTransition> current_out1 = fs1.getOut();
		ArrayList<FTransition> current_out2 = fs2.getOut();
		boolean found_input = false;
				
		if(islog) log = log.concat(" TEST0 " + fs1 + " " +fs2+"\n");
		if(debug) System.out.println(" TEST0 " + fs1 + " " +fs2+"\n");
		if(islog || debug) print_common_pairs(fs1, fs2);
		
		String[] outs = check_common_valid_pair(header, current_out1, current_out2, fs1, fs2, cp);
				
		int count = 0;
		for(String in : ffsm.getInputAlphabet()){			
			for(FTransition co1 : current_out1){
				for(FTransition co2 : current_out2){
					//check the same input
					if(co1.getCInput().getIn().equals(in) 
							&& co2.getCInput().getIn().equals(in)){	
						//Is there a product for both transitions?
						if(outs[count].equals("sat") && !cp.getDistinguish()){						
							CommonPath cnew = new CommonPath(cp.getS1(), cp.getS2(), cp.getN(), cp.get1(), cp.get2());							
							if(cnew.addCommon(co1, co2)){									
								seq_map.get(lastinput).add(cnew);
								found_input = true;								
							}
						}
						count++;
					}					
				}
			}	
		}	
		if(!found_input){			
			if(islog) log = log.concat("\nNo input available!"+"\n");
			if(debug) System.out.println("\nNo input available!");
			return false;
		}
		if(islog) log = log.concat(" TEST1 " + fs1 + " " +fs2+"\n");
		if(debug) System.out.println(" TEST1 " + fs1 + " " +fs2);
		if(islog || debug) print_common_pairs(fs1, fs2);	
			
		//check input				
		ArrayList<String> alp = new ArrayList<String>();
		for(String s : ffsm.getInputAlphabet()){
			alp.add(s);
		}
		for(int i=1; i<=alp.size(); i++){			
			ArrayList<ArrayList<String>> inchecklist = find_inset(i,alp.size(),alp);			
			if(islog) log = log.concat("CHECKING 2"+"\n");
			if(debug) System.out.println("CHECKING 2");
			for(ArrayList<String> incheck : inchecklist){				
				if(islog) log = log.concat(incheck+"\n");
				if(debug) System.out.println(incheck);
				ArrayList<String> inputset = check_disting_old(header, fs1, fs2, seq_map, incheck);
				if(inputset != null){					
					if(islog) log = log.concat("\nState pair "+fs1+" and "+fs2+" OK for inputset "+inputset+"\n"+"\n");
					if(debug) System.out.println("\nState pair "+fs1+" and "+fs2+" OK for inputset "+inputset+"\n");
					return true;
				}
			}			
		}	
		
		
		ArrayList<CommonPath> caux = seq_map.get(lastinput);
		for(CommonPath p : caux){
			FState a1 = p.get1().get(p.get1().size()-1).getTarget();
			FState a2 = p.get2().get(p.get2().size()-1).getTarget();
			String in = p.get1().get(p.get1().size()-1).getCInput().getIn();
			FState a11 = p.get1().get(p.get1().size()-1).getSource();
			FState a22 = p.get2().get(p.get2().size()-1).getSource();				
			if(!a1.equals(a2) && !(a11.equals(a1) && (a22.equals(a2)))){				
				if(islog) log = log.concat("\n States \n"+a1+" "+a2+" "+a11+" "+a22+ " "+in+"\n");
				if(islog) log = log.concat("\nGoing recursive\n"+in+"\n");
				if(debug) System.out.println("\n States \n"+a1+" "+a2+" "+a11+" "+a22+ " "+in+"\n");
				if(debug) System.out.println("\nGoing recursive\n"+in+"\n");
				boolean got = rec_common(header, a1, a2, p, in);
				if(got){
					return true;
				}
			}				
		}		
		
		return false;
	}
	
	public boolean rec_common_old(String header, FState fs1, FState fs2, CommonPath cp, String lastinput) 
			throws IOException, InterruptedException{
		ArrayList<FTransition> current_out1 = fs1.getOut();
		ArrayList<FTransition> current_out2 = fs2.getOut();
		boolean found_input = false;
				
		if(islog) log = log.concat(" TEST0 " + fs1 + " " +fs2+"\n");
		if(debug) System.out.println(" TEST0 " + fs1 + " " +fs2+"\n");
		if(islog || debug) print_common_pairs(fs1, fs2);
				
		for(String in : ffsm.getInputAlphabet()){			
			for(FTransition co1 : current_out1){
				for(FTransition co2 : current_out2){
					//check the same input
					if(co1.getCInput().getIn().equals(in) 
							&& co2.getCInput().getIn().equals(in)){	
						//Is there a product for both transitions?
						if(check_common_pair_old(header, fs1, fs2, co1, co2) && !cp.getDistinguish()){
							CommonPath cnew = new CommonPath(cp.getS1(), cp.getS2(), cp.getN(), cp.get1(), cp.get2());							
							if(cnew.addCommon_old(header, co1, co2)){									
								seq_map.get(lastinput).add(cnew);
								found_input = true;								
							}
						}
					}					
				}
			}	
		}	
		if(!found_input){			
			if(islog) log = log.concat("\nNo input available!"+"\n");
			if(debug) System.out.println("\nNo input available!");
			return false;
		}
		if(islog) log = log.concat(" TEST1 " + fs1 + " " +fs2+"\n");
		if(debug) System.out.println(" TEST1 " + fs1 + " " +fs2);
		if(islog || debug) print_common_pairs(fs1, fs2);	
			
		//check input				
		ArrayList<String> alp = new ArrayList<String>();
		for(String s : ffsm.getInputAlphabet()){
			alp.add(s);
		}	
		for(int i=1; i<=alp.size(); i++){			
			ArrayList<ArrayList<String>> inchecklist = find_inset(i,alp.size(),alp);			
			if(islog) log = log.concat("CHECKING 2"+"\n");
			if(debug) System.out.println("CHECKING 2");
			for(ArrayList<String> incheck : inchecklist){				
				if(islog) log = log.concat(incheck+"\n");
				if(debug) System.out.println(incheck);
				ArrayList<String> inputset = check_disting_old(header, fs1, fs2, seq_map, incheck);
				if(inputset != null){					
					if(islog) log = log.concat("\nState pair "+fs1+" and "+fs2+" OK for inputset "+inputset+"\n"+"\n");
					if(debug) System.out.println("\nState pair "+fs1+" and "+fs2+" OK for inputset "+inputset+"\n");
					return true;
				}
			}			
		}			 
		
		ArrayList<CommonPath> caux = seq_map.get(lastinput);
		for(CommonPath p : caux){
			FState a1 = p.get1().get(p.get1().size()-1).getTarget();
			FState a2 = p.get2().get(p.get2().size()-1).getTarget();
			String in = p.get1().get(p.get1().size()-1).getCInput().getIn();
			FState a11 = p.get1().get(p.get1().size()-1).getSource();
			FState a22 = p.get2().get(p.get2().size()-1).getSource();				
			if(!a1.equals(a2) && !(a11.equals(a1) && (a22.equals(a2)))){				
				if(islog) log = log.concat("\n States \n"+a1+" "+a2+" "+a11+" "+a22+ " "+in+"\n");
				if(islog) log = log.concat("\nGoing recursive\n"+in+"\n");
				if(debug) System.out.println("\n States \n"+a1+" "+a2+" "+a11+" "+a22+ " "+in+"\n");
				if(debug) System.out.println("\nGoing recursive\n"+in+"\n");
				boolean got = rec_common_old(header, a1, a2, p, in);
				if(got){
					return true;
				}
			}				
		}		
		
		return false;
	}
	
	public ArrayList<String> check_disting(String header, ArrayList<String> alp, FState fs1, FState fs2, 
			Map<String,ArrayList<CommonPath>> map) 
			throws IOException, InterruptedException{
				
		String clause = "";
		ArrayList<ArrayList<String>> inputsetlist = new ArrayList<ArrayList<String>>();
		
		for(int i=1; i<=alp.size(); i++){			
			ArrayList<ArrayList<String>> inchecklist = find_inset(i,alp.size(),alp);
			for(ArrayList<String> incheck : inchecklist){	
				if(islog) log = log.concat(incheck+"\n");
				if(debug) System.out.println(incheck);
				
				ArrayList<String> inputset = new ArrayList<String>();
				clause = clause.concat("(push)\n");
				clause = clause.concat("(assert (and "+fs1.getCondition()+" "+fs2.getCondition()+"))\n");
				clause = clause.concat("(assert (and \n");
				for(String in : incheck){			
					ArrayList<CommonPath> caux = map.get(in);
					for(CommonPath cp : caux){				
						if(cp.getDistinguish()){	
							String inaux = "";
							clause = clause.concat("    (not (and ");
							for(FTransition t : cp.get1()){
								inaux = inaux.concat(t.getCInput().getIn() + "+");
								clause = clause.concat(t.getCInput().getCond()+" "
										+t.getTarget().getCondition()+" ");
							}
							for(FTransition t : cp.get2()){
								clause = clause.concat(t.getCInput().getCond()+" "
										+t.getTarget().getCondition()+" ");
							}
							clause = clause.concat("))\n");	
							inputset.add(inaux);
						}				
					}
				}				
				clause = clause.concat("))\n");
				clause = clause.concat("(check-sat)\n");
				clause = clause.concat("(pop)\n");
				inputsetlist.add(inputset);				
			}
		}		
		if(!clause.equals("")){
			String prop_aux = header.concat(clause);
			// print stm2 file and execute
			String fpath = "./"+folder+"/f_dpair.smt2";
			FileHandler fh = new FileHandler();
			fh.print_file(prop_aux, fpath);
			
			String[] commands = {"./ffsm/z3","./"+folder+"/f_dpair.smt2"};
			String result = fh.getProcessOutput(commands);		
			String[] outs = result.split("\n");
			for(int i=0; i<inputsetlist.size(); i++){
				if(outs[i].equals("unsat")){			
					return inputsetlist.get(i);
				}
			}
		}		
		return null;
	}	
	
	public ArrayList<String> check_disting_old(String header, FState fs1, FState fs2, 
			Map<String,ArrayList<CommonPath>> map, ArrayList<String> inputcheck) 
			throws IOException, InterruptedException{
				
		String clause = "";
		ArrayList<String> inputset = new ArrayList<String>();
		clause = clause.concat("(assert (and "+fs1.getCondition()+" "+fs2.getCondition()+"))\n");
		clause = clause.concat("(assert (and \n");
		for(String in : inputcheck){			
			ArrayList<CommonPath> caux = map.get(in);
			for(CommonPath cp : caux){				
				if(cp.getDistinguish()){	
					String inaux = "";
					clause = clause.concat("    (not (and ");
					for(FTransition t : cp.get1()){
						inaux = inaux.concat(t.getCInput().getIn() + "+");
						clause = clause.concat(t.getCInput().getCond()+" "
								+t.getTarget().getCondition()+" ");
					}
					for(FTransition t : cp.get2()){
						clause = clause.concat(t.getCInput().getCond()+" "
								+t.getTarget().getCondition()+" ");
					}
					clause = clause.concat("))\n");	
					inputset.add(inaux);
				}				
			}
		}				
		clause = clause.concat("))\n");
		clause = clause.concat("(check-sat)");
		String prop_aux = header.concat(clause);
		// print stm2 file and execute
		String fpath = "./"+folder+"/f_dpair.smt2";
		FileHandler fh = new FileHandler();
		fh.print_file(prop_aux, fpath);
		
		String[] commands = {"./ffsm/z3","./"+folder+"/f_dpair.smt2"};
		String result = fh.getProcessOutput(commands);		
		String[] outs = result.split("\n");
						
		if(outs[0].equals("unsat")){			
			return inputset;						
		}else{
			return null;
		}		
	}	
	
	public String[] check_state_pairs() 
			throws IOException, InterruptedException{
				
		String clause = "";			
		ArrayList<FState> fs_aux = (ArrayList<FState>) ffsm.getFStates().clone();
		for(FState fs1 : ffsm.getFStates()){
			fs_aux.remove(fs1);
			for(FState fs2 : fs_aux){
				clause = clause.concat("(push)\n");
				clause = clause.concat("(assert (and "+fs1.getCondition()+" "+fs2.getCondition()+"))\n");		
				clause = clause.concat("(check-sat)\n");
				clause = clause.concat("(pop)\n");			
			}
		}	
		if(!clause.equals("")){
			String prop_aux = prop.concat(clause);
			// print stm2 file and execute
			String fpath = "./"+folder+"/f_cscpair.smt2";
			FileHandler fh = new FileHandler();
			fh.print_file(prop_aux, fpath);
			
			String[] commands = {"./ffsm/z3","./"+folder+"/f_cscpair.smt2"};
			String result = fh.getProcessOutput(commands);		
			String[] outs = result.split("\n");
			return outs;
		}
		return new String[0];
	}
	
	public boolean check_state_pair_old(String header, FState fs1, FState fs2) 
			throws IOException, InterruptedException{
				
		String clause = "";
		clause = clause.concat("(assert (and "+fs1.getCondition()+" "+fs2.getCondition()+"))\n");		
		clause = clause.concat("(check-sat)");
		String prop_aux = header.concat(clause);
		// print stm2 file and execute
		String fpath = "./"+folder+"/f_cscpair.smt2";
		FileHandler fh = new FileHandler();
		fh.print_file(prop_aux, fpath);
		
		String[] commands = {"./ffsm/z3","./"+folder+"/f_cscpair.smt2"};
		String result = fh.getProcessOutput(commands);		
		String[] outs = result.split("\n");
						
		if(outs[0].equals("sat")){			
			return true;						
		}else{
			return false;
		}		
	}
	
	
	public String[] check_common_pair(String header, ArrayList<FTransition> current_out1,
			ArrayList<FTransition> current_out2, FState fs1, FState fs2) 
			throws IOException, InterruptedException{
			
		String clause = "";
		for(String in : ffsm.getInputAlphabet()){
			for(FTransition co1 : current_out1){
				for(FTransition co2 : current_out2){
					//check the same input
					if(co1.getCInput().getIn().equals(in) 
							&& co2.getCInput().getIn().equals(in)){						
						clause = clause.concat("(push)\n");
						clause = clause.concat("(assert (and "+fs1.getCondition()+" "+fs2.getCondition()+"))\n");
						clause = clause.concat("(assert (and ");
						clause = clause.concat(co1.getCInput().getCond()+" "
									+co1.getTarget().getCondition()+" ");	
						clause = clause.concat(co2.getCInput().getCond()+" "
								+co2.getTarget().getCondition());
						clause = clause.concat("))\n");
						clause = clause.concat("(check-sat)\n");
						clause = clause.concat("(pop)\n");						
					}					
				}
			}	
		}	
		String prop_aux = header.concat(clause);
		// print stm2 file and execute
		String fpath = "./"+folder+"/f_ccpair.smt2";
		FileHandler fh = new FileHandler();
		fh.print_file(prop_aux, fpath);
		
		String[] commands = {"./ffsm/z3","./"+folder+"/f_ccpair.smt2"};
		String result = fh.getProcessOutput(commands);		
		String[] outs = result.split("\n");
			
		return outs;
	}
	
	public String[] check_common_valid_pair(String header, ArrayList<FTransition> current_out1,
			ArrayList<FTransition> current_out2, FState fs1, FState fs2, CommonPath cp) 
			throws IOException, InterruptedException{
			
		String clause = "";
		for(String in : ffsm.getInputAlphabet()){
			for(FTransition co1 : current_out1){
				for(FTransition co2 : current_out2){
					//check the same input
					if(co1.getCInput().getIn().equals(in) 
							&& co2.getCInput().getIn().equals(in)){						
						clause = clause.concat("(push)\n");
						clause = clause.concat("(assert (and "+fs1.getCondition()+" "+fs2.getCondition()+"))\n");
						clause = clause.concat("(assert (and ");
						for(FTransition t : cp.get1()){
							clause = clause.concat(t.getCInput().getCond()+" "
									+t.getTarget().getCondition()+" ");
						}
						for(FTransition t : cp.get2()){
							clause = clause.concat(t.getCInput().getCond()+" "
									+t.getTarget().getCondition()+" ");
						}
						clause = clause.concat(co1.getCInput().getCond()+" "
									+co1.getTarget().getCondition()+" ");	
						clause = clause.concat(co2.getCInput().getCond()+" "
								+co2.getTarget().getCondition());
						clause = clause.concat("))\n");
						clause = clause.concat("(check-sat)\n");
						clause = clause.concat("(pop)\n");						
					}					
				}
			}	
		}	
		String prop_aux = header.concat(clause);
		// print stm2 file and execute
		String fpath = "./"+folder+"/f_ccpairpath.smt2";
		FileHandler fh = new FileHandler();
		fh.print_file(prop_aux, fpath);
		
		String[] commands = {"./ffsm/z3","./"+folder+"/f_ccpairpath.smt2"};
		String result = fh.getProcessOutput(commands);		
		String[] outs = result.split("\n");
			
		return outs;
	}
	
	public boolean check_common_pair_old(String header, FState fs1, FState fs2,
			FTransition co1, FTransition co2) 
			throws IOException, InterruptedException{
				
		String clause = "";
		clause = clause.concat("(assert (and "+fs1.getCondition()+" "+fs2.getCondition()+"))\n");
		clause = clause.concat("(assert (and ");
		clause = clause.concat(co1.getCInput().getCond()+" "
					+co1.getTarget().getCondition()+" ");	
		clause = clause.concat(co2.getCInput().getCond()+" "
				+co2.getTarget().getCondition());
		clause = clause.concat("))\n");
		clause = clause.concat("(check-sat)");
		String prop_aux = header.concat(clause);
		// print stm2 file and execute
		String fpath = "./"+folder+"/f_ccpair.smt2";
		FileHandler fh = new FileHandler();
		fh.print_file(prop_aux, fpath);
		
		String[] commands = {"./ffsm/z3","./"+folder+"/f_ccpair.smt2"};
		String result = fh.getProcessOutput(commands);		
		String[] outs = result.split("\n");
						
		if(outs[0].equals("sat")){			
			return true;						
		}else{
			return false;
		}		
	}
	
	
	public boolean check_product_coverage(String header) throws IOException, InterruptedException{
		
		boolean init_con = true;
		String clause = "";
		
		for(FState s: path_map.keySet()){
			if(path_map.get(s) != null){
				clause = clause.concat("(push)\n");
				clause = clause.concat("(assert "+s.getCondition()+")\n");
				clause = clause.concat("(assert (and \n");
				for(ArrayList<FTransition> path : path_map.get(s)){
					clause = clause.concat("    (not (and ");
					for(FTransition t : path){
						clause = clause.concat(t.getSource().getCondition()+" "
								+t.getCInput().getCond()+" ");
					}
					clause = clause.concat("))\n");
				}
				clause = clause.concat("))\n");
				clause = clause.concat("(check-sat)\n");
				clause = clause.concat("(pop)\n");
			}			
		}
		if(!clause.equals("")){
			String prop_aux = header.concat(clause);
			// print stm2 file and execute
			String fpath = "./"+folder+"/f_cpath.smt2";
			FileHandler fh = new FileHandler();
			fh.print_file(prop_aux, fpath);
			
			String[] commands = {"./ffsm/z3","./"+folder+"/f_cpath.smt2"};
			String result = fh.getProcessOutput(commands);				
			String[] outs = result.split("\n");
			int count = 0;
			for(FState s: path_map.keySet()){
				if(path_map.get(s) != null){
					if(outs[count].equals("sat")){					
						if(islog) log = log.concat("Conditional state "+s +" cannot be reached by all products"+"\n");
						System.out.println("Conditional state "+s +" cannot be reached by all products"+"\n");
						return false;						
					}else{					
						if(islog) log = log.concat("Conditional state "+s +" OK"+"\n");
					}
					count++;
				}
			}
		}
		return init_con;
	}
	
	public boolean check_product_coverage_old(String header) throws IOException, InterruptedException{
		
		boolean init_con = true;
		for(FState s: path_map.keySet()){
			if(path_map.get(s) != null){
				String clause = "";
				clause = clause.concat("(assert "+s.getCondition()+")\n");
				clause = clause.concat("(assert (and \n");
				for(ArrayList<FTransition> path : path_map.get(s)){
					clause = clause.concat("    (not (and ");
					for(FTransition t : path){
						clause = clause.concat(t.getSource().getCondition()+" "
								+t.getCInput().getCond()+" ");
					}
					clause = clause.concat("))\n");
				}
				clause = clause.concat("))\n");
				clause = clause.concat("(check-sat)");
				String prop_aux = header.concat(clause);
				// print stm2 file and execute
				String fpath = "./"+folder+"/f_cpath.smt2";
				FileHandler fh = new FileHandler();
				fh.print_file(prop_aux, fpath);
				
				String[] commands = {"./ffsm/z3","./"+folder+"/f_cpath.smt2"};
				String result = fh.getProcessOutput(commands);				
				String[] outs = result.split("\n");
								
				if(outs[0].equals("sat")){					
					if(islog) log = log.concat("Conditional state "+s +" cannot be reached by all products"+"\n");
					System.out.println("Conditional state "+s +" cannot be reached by all products"+"\n");
					return false;						
				}else{					
					if(islog) log = log.concat("Conditional state "+s +" OK"+"\n");
				}
			}			
		}
		return init_con;
	}
	
	public boolean check_valid_paths(String header) throws IOException, InterruptedException{
		
		boolean init_con = true;
		String clause = "";
		
		for(FState s: path_map.keySet()){	
			if(path_map.get(s) != null){				
				for(ArrayList<FTransition> path : path_map.get(s)){					
					clause = clause.concat("(push)\n");
					clause = clause.concat("(assert "+s.getCondition()+")\n");
					clause = clause.concat("(assert (and ");
					for(FTransition t : path){
						clause = clause.concat(t.getSource().getCondition()+" "
								+t.getCInput().getCond()+" ");
					}
					clause = clause.concat("))\n");
					clause = clause.concat("(check-sat)\n");
					clause = clause.concat("(pop)\n");					
				}				
			}			
		}
		if(!clause.equals("")){
			String prop_aux = header.concat(clause);
			// print stm2 file and execute
			String fpath = "./"+folder+"/f_vpath.smt2";
			FileHandler fh = new FileHandler();
			fh.print_file(prop_aux, fpath);
			
			String[] commands = {"./ffsm/z3","./"+folder+"/f_vpath.smt2"};
			String result = fh.getProcessOutput(commands);					
			String[] outs = result.split("\n");
			int count = 0;
			for(FState s: path_map.keySet()){	
				if(path_map.get(s) != null){
					ArrayList<ArrayList<FTransition>> aux_paths = (ArrayList<ArrayList<FTransition>>) path_map.get(s).clone();
					for(ArrayList<FTransition> path : aux_paths){					
						if(outs[count].equals("unsat")){
							path_map.get(s).remove(path);								
						}
						count++;
					}
					if(path_map.get(s).size() < 1){
						return false;
					}
				}
			}
		}		
		return init_con;
	}
	
	public boolean check_valid_paths_old(String header) throws IOException, InterruptedException{
		
		boolean init_con = true;
		for(FState s: path_map.keySet()){	
			if(path_map.get(s) != null){
				ArrayList<ArrayList<FTransition>> aux_paths = (ArrayList<ArrayList<FTransition>>) path_map.get(s).clone();
				for(ArrayList<FTransition> path : aux_paths){
					String clause = "";
					clause = clause.concat("(assert "+s.getCondition()+")\n");
					clause = clause.concat("(assert (and ");
					for(FTransition t : path){
						clause = clause.concat(t.getSource().getCondition()+" "
								+t.getCInput().getCond()+" ");
					}
					clause = clause.concat("))\n");
					clause = clause.concat("(check-sat)");
					String prop_aux = header.concat(clause);
					// print stm2 file and execute
					String fpath = "./"+folder+"/f_vpath.smt2";
					FileHandler fh = new FileHandler();
					fh.print_file(prop_aux, fpath);
					
					String[] commands = {"./ffsm/z3","./"+folder+"/f_vpath.smt2"};
					String result = fh.getProcessOutput(commands);					
					String[] outs = result.split("\n");
									
					if(outs[0].equals("unsat")){
						path_map.get(s).remove(path);								
					}	
				}
				if(path_map.get(s).size() < 1){
					return false;
				}
			}			
		}		
		return init_con;
	}
	
	public void find_all_paths(){
		no_loop_ft = (ArrayList<FTransition>) ffsm.getFTransitions().clone();
		for(FTransition ft : ffsm.getFTransitions()){
			if(ft.getSource().equals(ft.getTarget())){
				no_loop_ft.remove(ft);
			}
		}
					
		FState current = ffsm.getFInitialState();
		ArrayList<FTransition> current_out = current.getOut();
					
		found_fc = new ArrayList<FState>();
		nfound_fc = (ArrayList<FState>) ffsm.getFStates().clone();		
		nfound_fc.remove(current);
		found_fc.add(current);
					
		path_map = new HashMap<FState,ArrayList<ArrayList<FTransition>>>();
		
		for(FState s : nfound_fc){
			path_map.put(s, new ArrayList<ArrayList<FTransition>>());
		}			
		//process initial c. state
		for(FTransition ct : current_out){
			if(no_loop_ft.contains(ct)){
				if(!found_fc.contains(ct.getTarget())){
					nfound_fc.remove(ct.getTarget());
					found_fc.add(ct.getTarget());
				}					
				ArrayList<FTransition> current_path = new ArrayList<FTransition>();
				current_path.add(ct);					
				ArrayList<ArrayList<FTransition>> c_paths = new ArrayList<ArrayList<FTransition>>();					
				c_paths.add(current_path);
				path_map.put(ct.getTarget(), c_paths);
			}				
		}						
		ArrayList<FState> found_aux = (ArrayList<FState>) found_fc.clone();
		for(FState cs : found_aux){
			if(!cs.equals(ffsm.getFInitialState())){
				rec_find_path(cs);
			}				
		}
	}
	
	public void rec_find_path(FState current){
		ArrayList<FTransition> current_out = current.getOut();		
		for(FTransition ct : current_out){
			if(no_loop_ft.contains(ct)){				
				ArrayList<ArrayList<FTransition>> c_paths = path_map.get(ct.getTarget());
				ArrayList<ArrayList<FTransition>> lc_paths = path_map.get(current);				
				prepath: for(ArrayList<FTransition> inc_path : lc_paths){					
					//if this c. state was found before
					for(FTransition c : inc_path){
						if(c.getTarget().equals(ct.getTarget())){
							continue prepath;
						}
					}
					ArrayList<FTransition> new_path = new ArrayList<FTransition>();
					FState last = inc_path.get(inc_path.size()-1).getSource();
					if(!last.equals(ct.getTarget()) && c_paths != null){						
						new_path.addAll(inc_path);
						new_path.add(ct);
						if(!c_paths.contains(new_path)){
							c_paths.add(new_path);							
						}						
					}					
				}				
				path_map.put(ct.getTarget(), c_paths);				
				if(!found_fc.contains(ct.getTarget())){
					nfound_fc.remove(ct.getTarget());
					found_fc.add(ct.getTarget());
					rec_find_path(ct.getTarget());
				}				
			}			
		}		
	}	
	
	public void print_paths(Map<FState,ArrayList<ArrayList<FTransition>>> path_map){
		if(islog) log = log.concat("\n Printing conditional state paths"+"\n");	
		if(debug) System.out.println("\n Printing conditional state paths");
		for(FState s: path_map.keySet()){			
			if(islog) log = log.concat("Conditional State "+s+"\n");
			if(debug) System.out.println("Conditional State "+s);
			int count = 0;
			if(path_map.get(s) != null){
				for(ArrayList<FTransition> path : path_map.get(s)){
					count++;
					if(islog) log = log.concat("Path "+count+": "+path+"\n");
					if(debug) System.out.println("Path "+count+": "+path);
				}
			}			
		}
	}
	
	public void print_common_pairs(FState fs1, FState fs2){				
		if(islog) log = log.concat("Conditional State pair "+ fs1 + " and " + fs2+"\n");	
		if(debug) System.out.println("Conditional State pair "+ fs1 + " and " + fs2);
		for(String in : ffsm.getInputAlphabet()){			
			if(islog) log = log.concat("  Input "+in+"\n");
			if(debug) System.out.println("  Input "+in);
			ArrayList<CommonPath> caux = seq_map.get(in);
			for(CommonPath cp : caux){				
				if(islog) log = log.concat("     Pair "+cp.get1()+ " "+ cp.get2()+"\n");
				if(debug) System.out.println("     Pair "+cp.get1()+ " "+ cp.get2());
			}
		}
	}
	
}
