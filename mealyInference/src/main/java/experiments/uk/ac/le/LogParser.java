package experiments.uk.ac.le;

import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.File;
import java.io.FileReader;
import java.io.FileWriter;
import java.util.Arrays;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import org.prop4j.And;
import org.prop4j.Literal;
import org.prop4j.Node;
import org.prop4j.NodeReader;
import org.prop4j.NodeWriter;
import org.prop4j.NodeWriter.Notation;

import de.ovgu.featureide.fm.core.base.IConstraint;
import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.base.IFeatureModelFactory;
import de.ovgu.featureide.fm.core.base.impl.FMFactoryManager;
import de.ovgu.featureide.fm.core.base.impl.FeatureModel;
import de.ovgu.featureide.fm.core.configuration.Configuration;
import de.ovgu.featureide.fm.core.io.IFeatureModelFormat;
import de.ovgu.featureide.fm.core.io.manager.FeatureModelManager;
import de.ovgu.featureide.fm.core.io.xml.XmlFeatureModelFormat;

public class LogParser {
	
	private static final String TIMESTAMP_PATTERN = "[\\d]+[\\d]+[\\d]+ [\\d]+:[\\d]+:[\\d]+ [\\w]+ [\\w]+\\s*|\\s*";
	
	static final Pattern patt_start = Pattern.compile(TIMESTAMP_PATTERN+"Start (\\w+) @([\\w\\.-]+)( w/([\\w\\.-]+))?");
	static final Pattern patt_sul = Pattern.compile(TIMESTAMP_PATTERN+"SUL name: (\\w+).dot");
	static final Pattern patt_seed = Pattern.compile(TIMESTAMP_PATTERN+"Seed: (\\d+)");
	static final Pattern patt_clos = Pattern.compile(TIMESTAMP_PATTERN+"ClosingStrategy: (.+)");
	static final Pattern patt_oth = Pattern.compile(TIMESTAMP_PATTERN+"ObservationTableCEXHandler: (.+)");
	static final Pattern patt_eqo = Pattern.compile(TIMESTAMP_PATTERN+"EquivalenceOracle: (.+)");
	static final Pattern patt_round = Pattern.compile(TIMESTAMP_PATTERN+"Rounds: (.+)");
	static final Pattern patt_mq_rst = Pattern.compile(TIMESTAMP_PATTERN+"MQ \\[resets\\]: (.+)");
	static final Pattern patt_mq_sym = Pattern.compile(TIMESTAMP_PATTERN+"MQ \\[symbols\\]: (.+)");
	static final Pattern patt_eq_rst = Pattern.compile(TIMESTAMP_PATTERN+"EQ \\[resets\\]: (.+)");
	static final Pattern patt_eq_sym = Pattern.compile(TIMESTAMP_PATTERN+"EQ \\[symbols\\]: (.+)");
	static final Pattern patt_lrn_time = Pattern.compile(TIMESTAMP_PATTERN+"Learning \\[ms\\]: (.+)");
	static final Pattern patt_cex_time = Pattern.compile(TIMESTAMP_PATTERN+"Searching for counterexample \\[ms\\]: (.+)");
	static final Pattern patt_equiv = Pattern.compile(TIMESTAMP_PATTERN+"Equivalent: (N?OK)");
	static final Pattern patt_end = Pattern.compile(TIMESTAMP_PATTERN+"End (\\w+) @");
	
	public static void main(String[] args) {
		try {
			File fr = new File("/home/cdnd1/remote_euler/"
//					+ ""
					+ "RunExperimentWMethod/logback_2019_01_07_17_57_13_817"
					+ ".log");
			File fw = new File(fr.getParentFile(),fr.getName().replaceAll(".log$", ".tab"));
			
			BufferedReader br = new BufferedReader(new FileReader(fr));
			BufferedWriter bw = new BufferedWriter(new FileWriter(fw));

			bw.write("Method\t");
			bw.write("SUL\t");
			bw.write("Reused\t");
			bw.write("CLOS\t");
			bw.write("CEXH\t");
//			bw.write("Seed\t");
			bw.write("Oracle\t");
			bw.write("Rounds\t");
			bw.write("MQ_Resets\t");
			bw.write("MQ_Symbols\t");
			bw.write("EQ_Resets\t");
			bw.write("EQ_Symbols\t");
			bw.write("LearningTime\t");
			bw.write("CEX_SearchTime\t");
			bw.write("Equivalent\n");
			
			Matcher matcher;
			while (br.ready()) {
				String line = br.readLine();
				if((matcher = patt_start.matcher(line)).find()) {
					bw.write(matcher.group(1));
					bw.write("\t");
					bw.write(matcher.group(2));
					bw.write("\t");
					if(matcher.group(4)!=null) {
						bw.write(matcher.group(4));
					}else {
						bw.write("-");
					}
				}else if((matcher = patt_clos.matcher(line)).find()) {
					bw.write("\t");
					bw.write(matcher.group(1));
				}else if((matcher = patt_oth.matcher(line)).find()) {
					bw.write("\t");
					bw.write(matcher.group(1));
//				}else if((matcher = patt_seed.matcher(line)).find()) {
//					bw.write("\t");
//					bw.write(matcher.group(1));
				}else if((matcher = patt_eqo.matcher(line)).find()) {
					bw.write("\t");
					bw.write(matcher.group(1));
				}else if((matcher = patt_round.matcher(line)).find()) {
					bw.write("\t");
					bw.write(matcher.group(1));
				}else if((matcher = patt_mq_rst.matcher(line)).find()) {
					bw.write("\t");
					bw.write(matcher.group(1));
				}else if((matcher = patt_mq_sym.matcher(line)).find()) {
					bw.write("\t");
					bw.write(matcher.group(1));
				}else if((matcher = patt_eq_rst.matcher(line)).find()) {
					bw.write("\t");
					bw.write(matcher.group(1));
				}else if((matcher = patt_eq_sym.matcher(line)).find()) {
					bw.write("\t");
					bw.write(matcher.group(1));
				}else if((matcher = patt_lrn_time.matcher(line)).find()) {
					bw.write("\t");
					bw.write(matcher.group(1));
				}else if((matcher = patt_cex_time.matcher(line)).find()) {
					bw.write("\t");
					bw.write(matcher.group(1));
				}else if((matcher = patt_equiv.matcher(line)).find()) {
					bw.write("\t");
					bw.write(matcher.group(1));
				}else if((matcher = patt_end.matcher(line)).find()) {
					bw.write("\n");
				}
					
			}
			br.close();
			bw.close();
		} catch (Exception e) {
			e.printStackTrace();
		}
		
		
	}
}
