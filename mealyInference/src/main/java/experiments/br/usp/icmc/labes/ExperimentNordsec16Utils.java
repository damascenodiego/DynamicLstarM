package experiments.br.usp.icmc.labes;

public class ExperimentNordsec16Utils {

	private static ExperimentNordsec16Utils instance = null;
	private ExperimentNordsec16Utils() {
		nordsec16_client_rlzdate();
		nordsec16_server_rlzdate();
//		nordsec16_client();
//		nordsec16_server();
//		verleg();
//		usenix15_gnuTLS_client();
//		usenix15_gnuTLS_server();
//		usenix15_openSSL_cli();
//		usenix15_openSSL_srv();
	}
	
	public static ExperimentNordsec16Utils getInstance() {
		
		if(instance==null){ instance = new ExperimentNordsec16Utils();}
		return instance;
	}
	private static String [] versions;
	private static String tab_filename; 

	public static String getTab_filename() {
		return tab_filename;
	}
	
	public static String[] getVersions() {
		return versions;
	}
	
	public void nordsec16_client_rlzdate() {
		String[] local_versions = {	
//				"BenchmarkNordsec16/client_097.dot", 
//				"BenchmarkNordsec16/client_097e.dot", 
//				"BenchmarkNordsec16/client_098f.dot", 
				"BenchmarkNordsec16/client_098j.dot", 
				"BenchmarkNordsec16/client_098l.dot", 
				"BenchmarkNordsec16/client_098m.dot", 
				"BenchmarkNordsec16/client_101.dot", 
				"BenchmarkNordsec16/client_098za.dot", 
				"BenchmarkNordsec16/client_100m.dot", 
				"BenchmarkNordsec16/client_101h.dot", 
				"BenchmarkNordsec16/client_102.dot", 
				"BenchmarkNordsec16/client_110-pre1.dot",
		};
		versions = local_versions;
		tab_filename = "nordsec16_client.tab";

	}

	public void nordsec16_server_rlzdate() {
		String[] local_versions = {

				"BenchmarkNordsec16/server_097.dot", 
				"BenchmarkNordsec16/server_097c.dot", 
				"BenchmarkNordsec16/server_097e.dot",
				"BenchmarkNordsec16/server_098l.dot", 
				"BenchmarkNordsec16/server_098m.dot", 
				"BenchmarkNordsec16/server_100.dot", 
				"BenchmarkNordsec16/server_098s.dot", 
				"BenchmarkNordsec16/server_098u.dot", 
				"BenchmarkNordsec16/server_101.dot", 
				"BenchmarkNordsec16/server_098za.dot", 
				"BenchmarkNordsec16/server_101k.dot", 
				"BenchmarkNordsec16/server_102.dot",
				"BenchmarkNordsec16/server_110pre1.dot"


		};

		versions = local_versions;
		tab_filename = "nordsec16_server.tab";


	}
	private void nordsec16_client() {
		String[] local_versions = {	
				"BenchmarkNordsec16/client_097.dot", 
				"BenchmarkNordsec16/client_097e.dot", 
				"BenchmarkNordsec16/client_098f.dot", 
				"BenchmarkNordsec16/client_098j.dot", 
				"BenchmarkNordsec16/client_098l.dot", 
				"BenchmarkNordsec16/client_098m.dot", 
				"BenchmarkNordsec16/client_098za.dot", 
				"BenchmarkNordsec16/client_100m.dot", 
				"BenchmarkNordsec16/client_101.dot", 
				"BenchmarkNordsec16/client_101h.dot", 
				"BenchmarkNordsec16/client_102.dot", 
				"BenchmarkNordsec16/client_110-pre1.dot",
		};
		versions = local_versions;
		tab_filename = "nordsec16_client.tab";

	}

	private void nordsec16_server() {
		String[] local_versions = {

				"BenchmarkNordsec16/server_097.dot", 
				"BenchmarkNordsec16/server_097c.dot", 
				"BenchmarkNordsec16/server_097e.dot",
				"BenchmarkNordsec16/server_098l.dot", 
				"BenchmarkNordsec16/server_098m.dot", 
				"BenchmarkNordsec16/server_098s.dot", 
				"BenchmarkNordsec16/server_098u.dot", 
				"BenchmarkNordsec16/server_098za.dot", 
				"BenchmarkNordsec16/server_100.dot", 
				"BenchmarkNordsec16/server_101.dot", 
				"BenchmarkNordsec16/server_101k.dot", 
				"BenchmarkNordsec16/server_102.dot",
				"BenchmarkNordsec16/server_110pre1.dot"


		};

		versions = local_versions;
		tab_filename = "nordsec16_server.tab";


	}

	private void verleg() {
		String[] local_versions = {
				"BenchmarkSSH/DropBear.dot",
				"BenchmarkSSH/BitVise.dot",			
				"BenchmarkSSH/OpenSSH.dot",
		};
		versions = local_versions;
		tab_filename = "verleg.tab";

	}

	private void usenix15_gnuTLS_server() {
		String[] local_versions =  {"BenchmarkTLS/GnuTLS_3.3.8_server_regular.dot", "BenchmarkTLS/GnuTLS_3.3.12_server_regular.dot",};
		versions = local_versions;
		tab_filename = "usenix15_gnuTLS_server.tab";
	}
	
	private void usenix15_gnuTLS_client() {
		String[] local_versions =  {"BenchmarkTLS/GnuTLS_3.3.8_client_regular.dot", "BenchmarkTLS/GnuTLS_3.3.12_client_regular.dot",};
		versions = local_versions;
		tab_filename = "usenix15_gnuTLS_client.tab";
	}

	private void usenix15_openSSL_cli() {
		String[] local_versions =  {"BenchmarkTLS/OpenSSL_1.0.1g_client_regular.dot", "BenchmarkTLS/OpenSSL_1.0.1j_client_regular.dot","BenchmarkTLS/OpenSSL_1.0.1l_client_regular.dot", "BenchmarkTLS/OpenSSL_1.0.2_client_regular.dot",};
		versions = local_versions;
		tab_filename = "usenix15_openSSL_cli.tab";
	}

	private void usenix15_openSSL_srv() {
		String[] local_versions =  {"BenchmarkTLS/OpenSSL_1.0.1g_server_regular.dot", "BenchmarkTLS/OpenSSL_1.0.1j_server_regular.dot","BenchmarkTLS/OpenSSL_1.0.1l_server_regular.dot", "BenchmarkTLS/OpenSSL_1.0.2_server_regular.dot",};
		versions = local_versions;
		tab_filename = "usenix15_openSSL_srv.tab";
	}
	
}