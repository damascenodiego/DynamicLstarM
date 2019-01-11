package experiments.uk.ac.le;

import java.io.File;
import java.util.ArrayList;
import java.util.List;

import br.usp.icmc.labes.mealyInference.utils.Utils;
import net.automatalib.automata.transout.impl.compact.CompactMealy;
import net.automatalib.words.Word;

public class Experiments {

	public static final String[] NORDSEC16_CLI = {	
			//			"Benchmark/Nordsec16/client_097.dot", 
			//			"Benchmark/Nordsec16/client_097e.dot", 
			//			"Benchmark/Nordsec16/client_098f.dot", 
			"Benchmark/Nordsec16/client_098j.dot", 
			"Benchmark/Nordsec16/client_098l.dot", 
			"Benchmark/Nordsec16/client_098m.dot", 
			"Benchmark/Nordsec16/client_101.dot", 
			"Benchmark/Nordsec16/client_098za.dot", 
			"Benchmark/Nordsec16/client_100m.dot", 
			"Benchmark/Nordsec16/client_101h.dot", 
			"Benchmark/Nordsec16/client_102.dot", 
			"Benchmark/Nordsec16/client_110-pre1.dot",
	};
	
	public static final List<MealyPlusFile> NORDSEC16_CLI_load() throws Exception{
		List<MealyPlusFile> outList = new ArrayList<>();
		
		for (String string : NORDSEC16_CLI) {
			File file = new File(string);
			CompactMealy<String, Word<String>> mealy = Utils.getInstance().loadMealyMachineFromDot(file);
			outList.add(new MealyPlusFile(mealy, file));
		}
		
		return outList;
	}

	public static final String[] NORDSEC16_SRV = {	
			"Benchmark/Nordsec16/server_097.dot", 
			"Benchmark/Nordsec16/server_097c.dot", 
			"Benchmark/Nordsec16/server_097e.dot",
			"Benchmark/Nordsec16/server_098l.dot", 
			"Benchmark/Nordsec16/server_098m.dot", 
			"Benchmark/Nordsec16/server_100.dot", 
			"Benchmark/Nordsec16/server_098s.dot", 
			"Benchmark/Nordsec16/server_098u.dot", 
			"Benchmark/Nordsec16/server_101.dot", 
			"Benchmark/Nordsec16/server_098za.dot", 
			"Benchmark/Nordsec16/server_101k.dot", 
			"Benchmark/Nordsec16/server_102.dot",
			"Benchmark/Nordsec16/server_110pre1.dot"


	};
	
	public static final List<MealyPlusFile> NORDSEC16_SRV_load() throws Exception{
		List<MealyPlusFile> outList = new ArrayList<>();
		
		for (String string : NORDSEC16_SRV) {
			File file = new File(string);
			CompactMealy<String, Word<String>> mealy = Utils.getInstance().loadMealyMachineFromDot(file);
			outList.add(new MealyPlusFile(mealy, file));
		}
		
		return outList;
	}


	public static final String[] QUIC_PROTOCOL = {
			"Benchmark/QUICprotocol/QUICprotocolwith0RTT.dot",
			"Benchmark/QUICprotocol/QUICprotocolwithout0RTT.dot"
	};
	
	public static final List<MealyPlusFile> QUIC_PROTOCOL_load() throws Exception{
		List<MealyPlusFile> outList = new ArrayList<>();
		
		for (String string : QUIC_PROTOCOL) {
			File file = new File(string);
			CompactMealy<String, Word<String>> mealy = Utils.getInstance().loadMealyMachineFromDot(file);
			outList.add(new MealyPlusFile(mealy, file));
		}
		
		return outList;
	}

	public static final String[] SSH_IMPLEM = {
			"Benchmark/SSH/BitVise.dot.fixed",
			"Benchmark/SSH/DropBear.dot.fixed",
			"Benchmark/SSH/OpenSSH.dot.fixed",
	};
	
	public static final List<MealyPlusFile> SSH_IMPLEM_load() throws Exception{
		List<MealyPlusFile> outList = new ArrayList<>();
		
		for (String string : SSH_IMPLEM) {
			File file = new File(string);
			CompactMealy<String, Word<String>> mealy = Utils.getInstance().loadMealyMachineFromDot(file);
			outList.add(new MealyPlusFile(mealy, file));
		}
		
		return outList;
	}


	public static final String[] TCP_CLI_IMPLEM = {
			"Benchmark/TCP/TCP_FreeBSD_Client.dot.txt",
			"Benchmark/TCP/TCP_Linux_Client.dot.txt",
			"Benchmark/TCP/TCP_Windows8_Client.dot.txt",
	};
	
	public static final List<MealyPlusFile> TCP_CLI_IMPLEM_load() throws Exception{
		List<MealyPlusFile> outList = new ArrayList<>();
		
		for (String string : TCP_CLI_IMPLEM) {
			File file = new File(string);
			CompactMealy<String, Word<String>> mealy = Utils.getInstance().loadMealyMachine(file);
			outList.add(new MealyPlusFile(mealy, file));
		}

		return outList;
	}
	
	public static final String[] TCP_SRV_IMPLEM = {
			"Benchmark/TCP/TCP_FreeBSD_Server.dot.txt",
			"Benchmark/TCP/TCP_Linux_Server.dot.txt",
			"Benchmark/TCP/TCP_Windows8_Server.dot.txt",
	};
	
	public static final List<MealyPlusFile> TCP_SRV_IMPLEM_load() throws Exception{
		List<MealyPlusFile> outList = new ArrayList<>();
		
		for (String string : TCP_SRV_IMPLEM) {
			File file = new File(string);
			CompactMealy<String, Word<String>> mealy = Utils.getInstance().loadMealyMachine(file);
			outList.add(new MealyPlusFile(mealy, file));
		}
		
		return outList;
	}
	
	public static final String[] EDENTIFIER2_IMPLEM = {
			"Benchmark/Edentifier2/learnresult_new_Rand_500_10-15_MC_fix.dot",
			"Benchmark/Edentifier2/learnresult_old_500_10-15_fix.dot",
	};
	
	public static final List<MealyPlusFile> EDENTIFIER2_IMPLEM_load() throws Exception{
		List<MealyPlusFile> outList = new ArrayList<>();
		
		for (String string : EDENTIFIER2_IMPLEM) {
			File file = new File(string);
			CompactMealy<String, Word<String>> mealy = Utils.getInstance().loadMealyMachineFromDot(file);
			outList.add(new MealyPlusFile(mealy, file));
		}
		
		return outList;
	}
	
	
	public static final String[] XRAY_PHILIPS = {
			"Benchmark/Xray/learnresult1.dot",
			"Benchmark/Xray/learnresult2.dot",
			"Benchmark/Xray/learnresult3.dot",
			//"Benchmark/Xray/learnresult4.dot",
			//"Benchmark/Xray/learnresult5.dot",
			"Benchmark/Xray/learnresult6.dot",
	};

	
	
/*	
	public static final String[] TLS_IMPLEM = {
			"Benchmark/TLS/OpenSSL_1.0.2_client_regular.dot",
			"Benchmark/TLS/OpenSSL_1.0.1l_client_regular.dot",
			"Benchmark/TLS/OpenSSL_1.0.1j_client_regular.dot",
			"Benchmark/TLS/OpenSSL_1.0.1g_client_regular.dot",
			"Benchmark/TLS/NSS_3.17.4_client_regular.dot",
			"Benchmark/TLS/GnuTLS_3.3.12_client_regular.dot",
			"Benchmark/TLS/GnuTLS_3.3.8_client_regular.dot",

			"Benchmark/TLS/RSA_BSAFE_Java_6.1.1_server_regular.dot",
			"Benchmark/TLS/RSA_BSAFE_C_4.0.4_server_regular.dot",
			"Benchmark/TLS/OpenSSL_1.0.2_server_regular.dot",
			"Benchmark/TLS/OpenSSL_1.0.1l_server_regular.dot",
			"Benchmark/TLS/OpenSSL_1.0.1j_server_regular.dot",
			"Benchmark/TLS/OpenSSL_1.0.1g_server_regular.dot",
			"Benchmark/TLS/NSS_3.17.4_server_regular.dot",
			"Benchmark/TLS/miTLS_0.1.3_server_regular.dot",
			"Benchmark/TLS/GnuTLS_3.3.12_server_regular.dot",
			"Benchmark/TLS/GnuTLS_3.3.8_server_regular.dot",

			"Benchmark/TLS/GnuTLS_3.3.12_server_full.dot",
			"Benchmark/TLS/GnuTLS_3.3.8_server_full.dot",

			"Benchmark/TLS/GnuTLS_3.3.12_client_full.dot",
			"Benchmark/TLS/GnuTLS_3.3.8_client_full.dot",
			"Benchmark/TLS/OpenSSL_1.0.2_client_full.dot",
			"Benchmark/TLS/NSS_3.17.4_client_full.dot",
	};
*/
	
}
