package br.usp.icmc.labes.examples.TLS;

public class ModelsFromRealSULs_utils {

	private static ModelsFromRealSULs_utils instance = null;
	private ModelsFromRealSULs_utils() {
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
	
	public static ModelsFromRealSULs_utils getInstance() {
		
		if(instance==null){ instance = new ModelsFromRealSULs_utils();}
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
//				"experiment_nordsec16/client_097.dot", 
//				"experiment_nordsec16/client_097e.dot", 
//				"experiment_nordsec16/client_098f.dot", 
				"experiment_nordsec16/client_098j.dot", 
				"experiment_nordsec16/client_098l.dot", 
				"experiment_nordsec16/client_098m.dot", 
				"experiment_nordsec16/client_101.dot", 
				"experiment_nordsec16/client_098za.dot", 
				"experiment_nordsec16/client_100m.dot", 
				"experiment_nordsec16/client_101h.dot", 
				"experiment_nordsec16/client_102.dot", 
				"experiment_nordsec16/client_110-pre1.dot",
		};
		versions = local_versions;
		tab_filename = "nordsec16_client.tab";

	}

	public void nordsec16_server_rlzdate() {
		String[] local_versions = {

				"experiment_nordsec16/server_097.dot", 
				"experiment_nordsec16/server_097c.dot", 
				"experiment_nordsec16/server_097e.dot",
				"experiment_nordsec16/server_098l.dot", 
				"experiment_nordsec16/server_098m.dot", 
				"experiment_nordsec16/server_100.dot", 
				"experiment_nordsec16/server_098s.dot", 
				"experiment_nordsec16/server_098u.dot", 
				"experiment_nordsec16/server_101.dot", 
				"experiment_nordsec16/server_098za.dot", 
				"experiment_nordsec16/server_101k.dot", 
				"experiment_nordsec16/server_102.dot",
				"experiment_nordsec16/server_110pre1.dot"


		};

		versions = local_versions;
		tab_filename = "nordsec16_server.tab";


	}
	private void nordsec16_client() {
		String[] local_versions = {	
				"experiment_nordsec16/client_097.dot", 
				"experiment_nordsec16/client_097e.dot", 
				"experiment_nordsec16/client_098f.dot", 
				"experiment_nordsec16/client_098j.dot", 
				"experiment_nordsec16/client_098l.dot", 
				"experiment_nordsec16/client_098m.dot", 
				"experiment_nordsec16/client_098za.dot", 
				"experiment_nordsec16/client_100m.dot", 
				"experiment_nordsec16/client_101.dot", 
				"experiment_nordsec16/client_101h.dot", 
				"experiment_nordsec16/client_102.dot", 
				"experiment_nordsec16/client_110-pre1.dot",
		};
		versions = local_versions;
		tab_filename = "nordsec16_client.tab";

	}

	private void nordsec16_server() {
		String[] local_versions = {

				"experiment_nordsec16/server_097.dot", 
				"experiment_nordsec16/server_097c.dot", 
				"experiment_nordsec16/server_097e.dot",
				"experiment_nordsec16/server_098l.dot", 
				"experiment_nordsec16/server_098m.dot", 
				"experiment_nordsec16/server_098s.dot", 
				"experiment_nordsec16/server_098u.dot", 
				"experiment_nordsec16/server_098za.dot", 
				"experiment_nordsec16/server_100.dot", 
				"experiment_nordsec16/server_101.dot", 
				"experiment_nordsec16/server_101k.dot", 
				"experiment_nordsec16/server_102.dot",
				"experiment_nordsec16/server_110pre1.dot"


		};

		versions = local_versions;
		tab_filename = "nordsec16_server.tab";


	}

	private void verleg() {
		String[] local_versions = {
				"experiment_verleg/Learning-SSH-Paper/models/DropBear.dot",
				"experiment_verleg/Learning-SSH-Paper/models/BitVise.dot",			
				"experiment_verleg/Learning-SSH-Paper/models/OpenSSH.dot",
		};
		versions = local_versions;
		tab_filename = "verleg.tab";

	}

	private void usenix15_gnuTLS_server() {
		String[] local_versions =  {"experiment_usenix15/GnuTLS_3.3.8_server_regular.dot", "experiment_usenix15/GnuTLS_3.3.12_server_regular.dot",};
		versions = local_versions;
		tab_filename = "usenix15_gnuTLS_server.tab";
	}
	
	private void usenix15_gnuTLS_client() {
		String[] local_versions =  {"experiment_usenix15/GnuTLS_3.3.8_client_regular.dot", "experiment_usenix15/GnuTLS_3.3.12_client_regular.dot",};
		versions = local_versions;
		tab_filename = "usenix15_gnuTLS_client.tab";
	}

	private void usenix15_openSSL_cli() {
		String[] local_versions =  {"experiment_usenix15/OpenSSL_1.0.1g_client_regular.dot", "experiment_usenix15/OpenSSL_1.0.1j_client_regular.dot","experiment_usenix15/OpenSSL_1.0.1l_client_regular.dot", "experiment_usenix15/OpenSSL_1.0.2_client_regular.dot",};
		versions = local_versions;
		tab_filename = "usenix15_openSSL_cli.tab";
	}

	private void usenix15_openSSL_srv() {
		String[] local_versions =  {"experiment_usenix15/OpenSSL_1.0.1g_server_regular.dot", "experiment_usenix15/OpenSSL_1.0.1j_server_regular.dot","experiment_usenix15/OpenSSL_1.0.1l_server_regular.dot", "experiment_usenix15/OpenSSL_1.0.2_server_regular.dot",};
		versions = local_versions;
		tab_filename = "usenix15_openSSL_srv.tab";
	}
	
}
