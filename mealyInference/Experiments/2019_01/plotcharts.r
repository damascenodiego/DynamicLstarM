source("./util.R")

out_format<-".png"; ggsave_dev<-"png"
out_format<-".pdf"; ggsave_dev<-cairo_pdf

logdir<-"/home/cdnd1/euler_remote/"
# logfname <- "mqtt"
# logfname <- "nordsec16_client"
# logfname <- "nordsec16_server"
## logfname <- "tcp"
## logfname <- "xray"

# the_EqOracles<-c("WMethodHypEQOracle", "WpMethodHypEQOracle")
# the_measurements<-c("EQ_Resets","MQ_Resets","Rounds","TQ_Resets")
the_EqOracles<-c("WpMethodHypEQOracle");the_measurements<-c("EQ_Resets","MQ_Resets","TQ_Resets")


logfname <- "ssh"
tab<-prepareTab(logdir,logfname)
tab<-tab[!(grepl("^L1",tab$Method)),]; tab<-tab[!(grepl("^TTT",tab$Method)),]
# tab<-tab[!(grepl("^DL.M_v1",tab$Method)),]; 
tab$Method<-gsub("^DL.M_v2",paste(sprintf('\u2202'),"L*M",sep = ""),tab$Method); 
tab$Method<-gsub("^DL.M_v1","DL*M+",tab$Method); 
tab$Method<-gsub("^DL.M_v0","DL*M",tab$Method); 
tab$Method<-factor(tab$Method,levels = c("∂L*M", "DL*M+", "DL*M", "Adp", "L*M", "L1","TTT"))
# plotCorrectness(logdir,tab,logfname, out_format,the_EqOracles)
# plotMetrics_face_grid(logdir,tab,logfname, out_format,the_EqOracles,the_measurements)
# plotMetrics_allTogether(logdir,tab,logfname, out_format,the_EqOracles,the_measurements)
# plotMetrics_plot_grid(logdir,tab,logfname, out_format,the_EqOracles,the_measurements)
sul_ot<-mk_sul_ot_ssh()
plotMetrics_specificAsBars  (logdir,tab,logfname, out_format,the_EqOracles,sul_ot,the_measurements)
plotMetrics_specificAllPairs(logdir,tab,logfname, out_format,the_EqOracles,sul_ot)

saveTabReusedPrefSuff(logdir,tab,logfname,the_EqOracles)
saveTab(logdir,tab,logfname)

logfname <- "mqtt"
tab<-prepareTab(logdir,logfname)
tab<-tab[!(grepl("^L1",tab$Method)),]; tab<-tab[!(grepl("^TTT",tab$Method)),]
# tab<-tab[!(grepl("^DL.M_v1",tab$Method)),]; 
tab$Method<-gsub("^DL.M_v2",paste(sprintf('\u2202'),"L*M",sep = ""),tab$Method); 
tab$Method<-gsub("^DL.M_v1","DL*M+",tab$Method); 
tab$Method<-gsub("^DL.M_v0","DL*M",tab$Method); 
tab$Method<-factor(tab$Method,levels = c("∂L*M", "DL*M+", "DL*M", "Adp", "L*M", "L1","TTT"))
# plotCorrectness(logdir,tab,logfname, out_format,the_EqOracles)
# plotMetrics_face_grid(logdir,tab,logfname, out_format,the_EqOracles,the_measurements)
# plotMetrics_allTogether(logdir,tab,logfname, out_format,the_EqOracles,the_measurements)
# plotMetrics_plot_grid(logdir,tab,logfname, out_format,the_EqOracles,the_measurements)
sul_ot<-mk_sul_ot_mqtt()
plotMetrics_specificAsBars  (logdir,tab,logfname, out_format,the_EqOracles,sul_ot,the_measurements)
plotMetrics_specificAllPairs(logdir,tab,logfname, out_format,the_EqOracles,sul_ot)
saveTabReusedPrefSuff(logdir,tab,logfname,the_EqOracles)

saveTab(logdir,tab,logfname)

logfname <- "nordsec16_client"
tab<-prepareTab(logdir,logfname)
tab<-tab[!(grepl("^L1",tab$Method)),]; tab<-tab[!(grepl("^TTT",tab$Method)),]
# tab<-tab[!(grepl("^DL.M_v1",tab$Method)),]; 
tab$Method<-gsub("^DL.M_v2",paste(sprintf('\u2202'),"L*M",sep = ""),tab$Method); 
tab$Method<-gsub("^DL.M_v1","DL*M+",tab$Method); 
tab$Method<-gsub("^DL.M_v0","DL*M",tab$Method); 
tab$Method<-factor(tab$Method,levels = c("∂L*M", "DL*M+", "DL*M", "Adp", "L*M", "L1","TTT"))
# plotCorrectness(logdir,tab,logfname, out_format,the_EqOracles)
# plotMetrics_face_grid(logdir,tab,logfname, out_format,the_EqOracles,the_measurements)
# plotMetrics_allTogether(logdir,tab,logfname, out_format,the_EqOracles,the_measurements)
# plotMetrics_plot_grid(logdir,tab,logfname, out_format,the_EqOracles,the_measurements)
sul_ot<-mk_sul_ot_cli()
plotMetrics_specificAsBars   (logdir,tab,logfname, out_format,the_EqOracles,sul_ot,the_measurements)
plotMetrics_specificFirstPrev(logdir,tab,logfname, out_format,the_EqOracles,sul_ot)
saveTabReusedPrefSuff(logdir,tab,logfname,the_EqOracles)
saveTab(logdir,tab,logfname,pairs=sul_ot)

logfname <- "nordsec16_server"
tab<-prepareTab(logdir,logfname)
tab<-tab[!(grepl("^L1",tab$Method)),]; tab<-tab[!(grepl("^TTT",tab$Method)),]
# tab<-tab[!(grepl("^DL.M_v1",tab$Method)),]; 
tab$Method<-gsub("^DL.M_v2",paste(sprintf('\u2202'),"L*M",sep = ""),tab$Method); 
tab$Method<-gsub("^DL.M_v1","DL*M+",tab$Method); 
tab$Method<-gsub("^DL.M_v0","DL*M",tab$Method); 
tab$Method<-factor(tab$Method,levels = c("∂L*M", "DL*M+", "DL*M", "Adp", "L*M", "L1","TTT"))
# plotCorrectness(logdir,tab,logfname, out_format,the_EqOracles)
# plotMetrics_face_grid(logdir,tab,logfname, out_format,the_EqOracles,the_measurements)
# plotMetrics_allTogether(logdir,tab,logfname, out_format,the_EqOracles,the_measurements)
# plotMetrics_plot_grid(logdir,tab,logfname, out_format,the_EqOracles,the_measurements)
sul_ot<-mk_sul_ot_srv()
plotMetrics_specificAsBars(logdir,tab,logfname, out_format,the_EqOracles,sul_ot,the_measurements)
plotMetrics_specificFirstPrev(logdir,tab,logfname, out_format,the_EqOracles,sul_ot)
saveTabReusedPrefSuff(logdir,tab,logfname,the_EqOracles)
saveTab(logdir,tab,logfname,pairs=sul_ot)
