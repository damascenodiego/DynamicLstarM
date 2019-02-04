source("./util.R")

out_format<-".png"; ggsave_dev<-"png"
# out_format<-".pdf"; ggsave_dev<-cairo_pdf

logdir<-"/home/diego/remote_euler/"

the_EqOracles<-c("WpMethodHypEQOracle");
the_measurements<-c("EQ_Resets","MQ_Resets","TQ_Resets")

logfname <- "nordsec16_server"
tab<-prepareTab(logdir,logfname)
tab<-tab[!(grepl("^L1",tab$Method)),]; tab<-tab[!(grepl("^TTT",tab$Method)),]
# tab<-tab[!(grepl("^DL.M_v1",tab$Method)),]; 
tab$Method<-gsub("^DL.M_v2",paste(sprintf('\u2202'),"L*M",sep = ""),tab$Method); 
tab$Method<-gsub("^DL.M_v1","DL*M+",tab$Method); 
tab$Method<-gsub("^DL.M_v0","DL*M",tab$Method); 
tab$Method<-factor(tab$Method,levels = c("∂L*M", "DL*M+", "DL*M", "Adp", "L*M", "L1","TTT"))

tab<-tab[!(tab$Seed=="null"),]
tab$MQ_Resets_Diff<-0
tab$EQ_Resets_Diff<-0
tab$MQ_Symbols_Diff<-0
tab$EQ_Symbols_Diff<-0
tab_lsm<-na.omit(tab[tab$Method=="L*M",])
for (sul in unique(tab_lsm$SUL)) {
  tab[tab$SUL==sul,"MQ_Resets_Diff"]<-tab[tab$SUL==sul,"MQ_Resets"]-unique(tab_lsm[tab_lsm$SUL==sul,"MQ_Resets"])
  tab[tab$SUL==sul,"EQ_Resets_Diff"]<-tab[tab$SUL==sul,"EQ_Resets"]-unique(tab_lsm[tab_lsm$SUL==sul,"EQ_Resets"])
  tab[tab$SUL==sul,"MQ_Symbols_Diff"]<-tab[tab$SUL==sul,"MQ_Symbols"]-unique(tab_lsm[tab_lsm$SUL==sul,"MQ_Symbols"])
  tab[tab$SUL==sul,"EQ_Symbols_Diff"]<-tab[tab$SUL==sul,"EQ_Symbols"]-unique(tab_lsm[tab_lsm$SUL==sul,"EQ_Symbols"])
}

metric_id<-"EQ_Resets_Diff"
p2 <- ggplot(data=tab[!(tab$Method=="L*M"),], aes_string(x="Method", y=metric_id)) +
  # geom_boxplot(outlier.colour="red", outlier.shape=8, outlier.size=4)
  geom_boxplot(outlier.shape=NA)
p2

control  <-tab[tab$Method=="∂L*M","EQ_Resets_Diff"]
treatment<-tab[tab$Method=="DL*M" ,"EQ_Resets_Diff"]
treatment<-tab[tab$Method=="DL*M+","EQ_Resets_Diff"]
treatment<-tab[tab$Method=="Adp","EQ_Resets_Diff"]

wilcox.test(control, treatment, conf.level = 0.95)

tab_summ <- summarySE(tab, measurevar=metric_id, groupvars=c("Method"))

metric_id<-"MQ_Resets_Diff"
p2 <- ggplot(data=tab[!(tab$Method=="L*M"),], aes_string(x="Method", y=metric_id)) +
  # geom_boxplot(outlier.colour="red", outlier.shape=8, outlier.size=4)
  geom_boxplot(outlier.shape=NA)+facet_grid( Method ~ Reuse)
p2

tab_summ <- summarySE(tab, measurevar=metric_id, groupvars=c("Method"))


tab_filename<-"releaseDatesSuls.tab"
versions_info <- read.table(tab_filename, sep="\t", header=TRUE)
versions_info$date<-as.Date(versions_info$date,format="%Y-%m-%d %H:%M:%S")
versions_info$version<-gsub("^server_","srv_",gsub("^client_","cli_",versions_info$version))
versions_info<-versions_info[order(versions_info$date),]
versions_info$qsize<-as.numeric(versions_info$qsize)

tab$DeltaT<-0
for (the_sul in unique(tab$SUL)) {
  for (the_ruz in unique(tab[tab$SUL==the_sul,"Reuse"])) {
    if(!(the_ruz=="null")){
      dateRuz<-versions_info[versions_info$version==the_ruz,"date"]
      dateSul<-versions_info[versions_info$version==the_sul,"date"]
      tab[(tab$SUL==the_sul)&(tab$Reuse==the_ruz),"DeltaT"]<-as.numeric(difftime(dateRuz, dateSul))
    }
  }
}

tab$DeltaQ<-0
for (the_sul in unique(tab$SUL)) {
  for (the_ruz in unique(tab[tab$SUL==the_sul,"Reuse"])) {
    if(!(the_ruz=="null")){
      dateRuz<-versions_info[versions_info$version==the_ruz,"qsize"]
      dateSul<-versions_info[versions_info$version==the_sul,"qsize"]
      tab[(tab$SUL==the_sul)&(tab$Reuse==the_ruz),"DeltaQ"]<-dateRuz-dateSul
    }
  }
}


for (the_method in c("∂L*M", "DL*M+", "DL*M", "Adp")) {
  my_x = "DeltaQ"; 
  # my_y = "EQ_Resets_Diff"; query_type<-"EQs"
  my_y = "MQ_Resets_Diff"; query_type<-"MQs"
  my_xlab = "Distance between release dates in days"; 
  my_ylab = paste("Difference between the number of",query_type)
  # tab_subset<-tab[tab$DeltaT>=0,]
  tab_subset<-tab
  # tab_subset<-tab_subset[tab$Method=="∂L*M",]
  # tab_subset<-tab_subset[tab$Method=="DL*M",]
  tab_subset<-tab_subset[tab$Method==the_method,]
  tab_subset<-na.omit(tab_subset)
  # ad.test(tab_subset[,my_y])
  ppp <-ggscatter(tab_subset,
                  x = my_x,
                  y = my_y,
                  # xlab = my_xlab,
                  # ylab = my_ylab,
                  title = paste("Method:",the_method),
                  add = "reg.line",
                  cor.method = "kendall",
                  conf.int = TRUE, # Add confidence interval
                  cor.coef = TRUE # Add correlation coefficient. see ?stat_cor
                  
  )
  print(ppp)  
}

