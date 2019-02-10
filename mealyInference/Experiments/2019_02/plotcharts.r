source("./util.R")

out_format<-".png"; ggsave_dev<-"png"
# out_format<-".pdf"; ggsave_dev<-cairo_pdf

logdir<-"/home/cdnd1/euler_rsync/Nordsec16_server/"

the_EqOracles<-"WpMethodHypEQOracle";
the_measurements<-c("EQ_Resets","MQ_Resets","TQ_Resets")

logfname <- "nordsec16_server"
tab<-prepareTab(logdir,logfname)
tab<-tab[!(grepl("^L1",tab$Method)),]; tab<-tab[!(grepl("^TTT",tab$Method)),]
# tab<-tab[!(grepl("^DL.M_v1",tab$Method)),]; 
tab$Method<-gsub("^DL.M_v2",paste(sprintf('\u2202'),"L*M",sep = ""),tab$Method); 
tab$Method<-gsub("^DL.M_v1","DL*M+",tab$Method); 
tab$Method<-gsub("^DL.M_v0","DL*M",tab$Method); 
tab$Method<-factor(tab$Method,levels = c("∂L*M", "DL*M+", "DL*M", "Adp", "L*M", "L1","TTT"))

tab_se<-summarySE(tab,measurevar ="MQ_Resets",groupvars = c("SUL","Reuse","Method"))

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
rm(tab_lsm,sul)

plotdir<-paste("./","plots","",logfname,the_EqOracles,"",sep = "/")
dir.create(file.path( plotdir), showWarnings = FALSE,recursive = TRUE)

{
  ###############################################################################################################
  sul_ot<-mk_sul_ot_srv()
  
  tab_sot<-tab[((tab$SUL %in% sul_ot$SUL) & tab$Reuse=="null"),]
  tab_sot<-rbind(tab_sot,tab[paste(tab$SUL,tab$Reuse) %in% paste(sul_ot$SUL,sul_ot$Reuse),])
  
  tab_sot <- tab_sot[grepl(paste("^",the_EqOracles,sep = ""),tab_sot$EqO),]
  tab_this <- tab_sot
  
  tab_melt <- melt(tab_this, id = c("SUL","Method","Reuse"), measure = c("EQ_Resets_Diff","MQ_Resets_Diff"))
  names(tab_melt)<-c("SUL","Method","Reuse","Type","Number")
  tab_melt$Type<-gsub("_Resets_Diff$","s_diff",tab_melt$Type)
  tab_melt$Type<-factor(tab_melt$Type,levels = c("MQs_diff","EQs_diff"))
  
  v0<-names(which.max(table(tab_melt$Reuse)))
  tab_melt[((!tab_melt$Reuse=="null")&(!tab_melt$Reuse==v0)),"Reuse"]<-"Reuse Prev"
  tab_melt[((!tab_melt$Reuse=="null")&(tab_melt$Reuse==v0)),"Reuse"]<-"Reuse First"
  
  tradf<-tab_melt[((tab_melt$Reuse=="null")),]
  tradf$Reuse<-"Reuse First"
  
  tradp<-tab_melt[((tab_melt$Reuse=="null")),]
  tradp$Reuse<-"Reuse Prev"
  tab_melt<-rbind(tab_melt,tradf,tradp)
  tab_melt<-tab_melt[((!tab_melt$Reuse=="null")),]
  tab_melt<-tab_melt[!(tab_melt$Method=="L*M"),]
  
  tab_melt_q_sum<-summarySE(tab_melt,measurevar = "Number",groupvars = c("Method","Reuse","Type"))
  
  ################################################################################################################
  qtype<-"EQs_diff"; y_label<-"Variation on the number of EQs\n(Reuse-based vs. Traditional Learning)"
  tab_melt_q<-tab_melt[tab_melt$Type==qtype,]
  tab_melt_q<-tab_melt_q[tab_melt_q$Reuse=="Reuse Prev",]
  plot1 <- ggplot(data=tab_melt_q, aes_string(x="Method", y="Number",fill="Method")) +
    # geom_boxplot(outlier.colour="red", outlier.shape=8, outlier.size=2)+
    stat_boxplot(geom ='errorbar')+
    geom_boxplot(outlier.shape=NA)+
    labs(title = paste("Learing w/previous version"), x = "", y = y_label) +
    theme_bw()+
    theme(
      legend.position="none",
      plot.title = element_text(hjust = 0.5, size=8),
      axis.title.y  = element_text(angle = 90, hjust = 0.5,vjust = 0.5, size=6),
      axis.text.x  = element_text(angle = 25, hjust = 1, size=6),
      axis.text.y  = element_text(angle = 0, hjust = 1, size=6),
    )+
    scale_fill_grey(start=0.8, end=0.5)+
    coord_cartesian(ylim=c(-0.1 ,0.1))
  
  tab_melt_q<-tab_melt[tab_melt$Type==qtype,]
  tab_melt_q<-tab_melt_q[tab_melt_q$Reuse=="Reuse First",]
  plot2 <- ggplot(data=tab_melt_q, aes_string(x="Method", y="Number",fill="Method")) +
    # geom_boxplot(outlier.colour="red", outlier.shape=8, outlier.size=2)+
    stat_boxplot(geom ='errorbar')+
    geom_boxplot(outlier.shape=NA)+
    labs(title = paste("Learing w/first version"), x = "", y = "") +
    theme_bw()+
    theme(
      plot.title = element_text(hjust = 0.5, size=8),
      axis.text.x  = element_text(angle = 25, hjust = 1, size=6),
      axis.text.y  = element_text(angle = 0, hjust = 1, size=6),
    )+
    scale_fill_grey(start=0.8, end=0.5)+
    coord_cartesian(ylim=c(-80 ,450))
  pgrid<-plot_grid(plot1,plot2,labels = "AUTO",nrow = 1,rel_widths = c(.75, 1))
  
  filename <- paste(plotdir,paste(qtype,logfname,"firstprev",sep = "_"),out_format,sep="")
  ggsave(device=ggsave_dev, filename, width = 5, height = 3.5, dpi=320)  # ssh plots
  
  ################################################################################################################
  qtype<-"MQs_diff"; y_label<-"Variation on the number of MQs\n(Reuse-based vs. Traditional Learning)"
  tab_melt_q<-tab_melt[tab_melt$Type==qtype,]
  tab_melt_q<-tab_melt_q[tab_melt_q$Reuse=="Reuse Prev",]
  plot1 <- ggplot(data=tab_melt_q, aes_string(x="Method", y="Number",fill="Method")) +
    # geom_boxplot(outlier.colour="red", outlier.shape=8, outlier.size=2)+
    stat_boxplot(geom ='errorbar')+
    geom_boxplot(outlier.shape=NA)+
    labs(title = paste("Learing w/previous version"), x = "", y = y_label) +
    theme_bw()+
    theme(
      legend.position="none",
      plot.title = element_text(hjust = 0.5, size=8),
      axis.title.y  = element_text(angle = 90, hjust = 0.5,vjust = 0.5, size=6),
      axis.text.x  = element_text(angle = 25, hjust = 1, size=6),
      axis.text.y  = element_text(angle = 0, hjust = 1, size=6),
    )+
    scale_fill_grey(start=0.8, end=0.5)+
      coord_cartesian(ylim=c(-300 ,100))
  
  tab_melt_q<-tab_melt[tab_melt$Type==qtype,]
  tab_melt_q<-tab_melt_q[tab_melt_q$Reuse=="Reuse First",]
  plot2 <- ggplot(data=tab_melt_q, aes_string(x="Method", y="Number",fill="Method")) +
    # geom_boxplot(outlier.colour="red", outlier.shape=8, outlier.size=2)+
    stat_boxplot(geom ='errorbar')+
    geom_boxplot(outlier.shape=NA)+
    labs(title = paste("Learing w/first version"), x = "", y = "") +
    theme_bw()+
    theme(
      plot.title = element_text(hjust = 0.5, size=8),
      axis.text.x  = element_text(angle = 25, hjust = 1, size=6),
      axis.text.y  = element_text(angle = 0, hjust = 1, size=6),
    )+
    scale_fill_grey(start=0.8, end=0.5)+
    coord_cartesian(ylim=c(-300 ,900))
  pgrid<-plot_grid(plot1,plot2,labels = "AUTO",nrow = 1,rel_widths = c(.75, 1))
  
  filename <- paste(plotdir,paste(qtype,logfname,"firstprev",sep = "_"),out_format,sep="")
  ggsave(device=ggsave_dev, filename, width = 5, height = 3.5, dpi=320)  # ssh plots
  
  #####################################################################################
  rm(pgrid,plot1,plot2,tab_melt,tab_melt_q,tab_melt_q_sum,tradf,tradp,tab_sot,tab_this,qtype,sul,the_ruz,the_sul,v0,y_label,plotdir2)
}


{
  ###############################################################################################################
  sul_ot<-mk_sul_ot_srv()
  
  tab_sot<-tab[((tab$SUL %in% sul_ot$SUL) & tab$Reuse=="null"),]
  tab_sot<-rbind(tab_sot,tab[paste(tab$SUL,tab$Reuse) %in% paste(sul_ot$SUL,sul_ot$Reuse),])
  
  tab_sot <- tab_sot[grepl(paste("^",the_EqOracles,sep = ""),tab_sot$EqO),]
  tab_this <- tab_sot
  
  tab_melt <- melt(tab_this, id = c("SUL","Method","Reuse"), measure = c("EQ_Resets","MQ_Resets"))
  names(tab_melt)<-c("SUL","Method","Reuse","Type","Number")
  tab_melt$Type<-gsub("_Resets$","s",tab_melt$Type)
  tab_melt$Type<-factor(tab_melt$Type,levels = c("MQs","EQs"))
  
  v0<-names(which.max(table(tab_melt$Reuse)))
  tab_melt[((!tab_melt$Reuse=="null")&(!tab_melt$Reuse==v0)),"Reuse"]<-"Reuse Prev"
  tab_melt[((!tab_melt$Reuse=="null")&(tab_melt$Reuse==v0)),"Reuse"]<-"Reuse First"
  
  tradf<-tab_melt[((tab_melt$Reuse=="null")),]
  tradf$Reuse<-"Reuse First"
  
  tradp<-tab_melt[((tab_melt$Reuse=="null")),]
  tradp$Reuse<-"Reuse Prev"
  tab_melt<-rbind(tab_melt,tradf,tradp)
  # tab_melt<-tab_melt[((!tab_melt$Reuse=="null")),]
  # tab_melt<-tab_melt[!(tab_melt$Method=="L*M"),]
  
  tab_melt_q_sum<-summarySE(tab_melt,measurevar = "Number",groupvars = c("Method","Reuse","Type"))
  
  ################################################################################################################
  qtype<-"EQs"; y_label<-"Number of EQs"
  tab_melt_q<-tab_melt[tab_melt$Type==qtype,]
  tab_melt_q<-tab_melt_q[tab_melt_q$Reuse=="Reuse Prev",]
  plot1 <- ggplot(data=tab_melt_q, aes_string(x="Method", y="Number",fill="Method")) +
    # geom_boxplot(outlier.colour="red", outlier.shape=8, outlier.size=2)+
    stat_boxplot(geom ='errorbar')+
    geom_boxplot(outlier.shape=NA)+
    labs(title = paste("Learing w/previous version"), x = "", y = y_label) +
    theme_bw()+
    theme(
      legend.position="none",
      plot.title = element_text(hjust = 0.5, size=8),
      axis.title.y  = element_text(angle = 90, hjust = 0.5,vjust = 0.5, size=6),
      axis.text.x  = element_text(angle = 25, hjust = 1, size=6),
      axis.text.y  = element_text(angle = 0, hjust = 1, size=6),
    )+
    scale_fill_grey(start=0.8, end=0.5)#+coord_cartesian(ylim=c(-5 ,5))
  
  tab_melt_q<-tab_melt[tab_melt$Type==qtype,]
  tab_melt_q<-tab_melt_q[tab_melt_q$Reuse=="Reuse First",]
  plot2 <- ggplot(data=tab_melt_q, aes_string(x="Method", y="Number",fill="Method")) +
    # geom_boxplot(outlier.colour="red", outlier.shape=8, outlier.size=2)+
    stat_boxplot(geom ='errorbar')+
    geom_boxplot(outlier.shape=NA)+
    labs(title = paste("Learing w/first version"), x = "", y = "") +
    theme_bw()+
    theme(
      plot.title = element_text(hjust = 0.5, size=8),
      axis.text.x  = element_text(angle = 25, hjust = 1, size=6),
      axis.text.y  = element_text(angle = 0, hjust = 1, size=6),
    )+
    scale_fill_grey(start=0.8, end=0.5)#+    coord_cartesian(ylim=c(-0 ,2000))
  pgrid<-plot_grid(plot1,plot2,labels = "AUTO",nrow = 1,rel_widths = c(.75, 1))
  
  filename <- paste(plotdir,paste(qtype,logfname,"firstprev",sep = "_"),out_format,sep="")
  ggsave(device=ggsave_dev, filename, width = 5, height = 3.5, dpi=320)  # ssh plots
  
  ################################################################################################################
  qtype<-"MQs"; y_label<-"Numbers of MQs\n(Reuse-based vs. Traditional Learning)"
  tab_melt_q<-tab_melt[tab_melt$Type==qtype,]
  tab_melt_q<-tab_melt_q[tab_melt_q$Reuse=="Reuse Prev",]
  plot1 <- ggplot(data=tab_melt_q, aes_string(x="Method", y="Number",fill="Method")) +
    # geom_boxplot(outlier.colour="red", outlier.shape=8, outlier.size=2)+
    stat_boxplot(geom ='errorbar')+
    geom_boxplot(outlier.shape=NA)+
    labs(title = paste("Learing w/previous version"), x = "", y = y_label) +
    theme_bw()+
    theme(
      legend.position="none",
      plot.title = element_text(hjust = 0.5, size=8),
      axis.title.y  = element_text(angle = 90, hjust = 0.5,vjust = 0.5, size=6),
      axis.text.x  = element_text(angle = 25, hjust = 1, size=6),
      axis.text.y  = element_text(angle = 0, hjust = 1, size=6),
    )+
    scale_fill_grey(start=0.8, end=0.5)#+coord_cartesian(ylim=c(-300 ,130))
  
  tab_melt_q<-tab_melt[tab_melt$Type==qtype,]
  tab_melt_q<-tab_melt_q[tab_melt_q$Reuse=="Reuse First",]
  plot2 <- ggplot(data=tab_melt_q, aes_string(x="Method", y="Number",fill="Method")) +
    # geom_boxplot(outlier.colour="red", outlier.shape=8, outlier.size=2)+
    stat_boxplot(geom ='errorbar')+
    geom_boxplot(outlier.shape=NA)+
    labs(title = paste("Learing w/first version"), x = "", y = "") +
    theme_bw()+
    theme(
      plot.title = element_text(hjust = 0.5, size=8),
      axis.text.x  = element_text(angle = 25, hjust = 1, size=6),
      axis.text.y  = element_text(angle = 0, hjust = 1, size=6),
    )+
    scale_fill_grey(start=0.8, end=0.5)#+coord_cartesian(ylim=c(-300 ,800))
  pgrid<-plot_grid(plot1,plot2,labels = "AUTO",nrow = 1,rel_widths = c(.75, 1))
  
  filename <- paste(plotdir,paste(qtype,logfname,"firstprev",sep = "_"),out_format,sep="")
  ggsave(device=ggsave_dev, filename, width = 5, height = 3.5, dpi=320)  # ssh plots
  
  #####################################################################################
  rm(pgrid,plot1,plot2,tab_melt,tab_melt_q,tab_melt_q_sum,tradf,tradp,tab_sot,tab_this,qtype,sul,the_ruz,the_sul,v0,y_label,plotdir2)
}

the_tab<-tab[!(tab$Method=="L*M"),]


# control  <-tab[tab$Method=="∂L*M","EQ_Resets_Diff"]
# treatment<-tab[tab$Method=="DL*M" ,"EQ_Resets_Diff"]
# treatment<-tab[tab$Method=="DL*M+","EQ_Resets_Diff"]
# treatment<-tab[tab$Method=="Adp","EQ_Resets_Diff"]
# wilcox.test(control, treatment, conf.level = 0.95)


{
  tab_filename<-"releaseDatesSuls.tab"
  versions_info <- read.table(tab_filename, sep="\t", header=TRUE)
  versions_info$date<-as.Date(versions_info$date,format="%Y-%m-%d %H:%M:%S")
  versions_info$version<-gsub("^server_","srv_",gsub("^client_","cli_",versions_info$version))
  versions_info<-versions_info[order(versions_info$date),]
  versions_info$qsize<-as.numeric(versions_info$qsize)
  
  {
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
    tab$DeltaT<-0
    for (the_sul in unique(tab$SUL)) {
      for (the_ruz in unique(tab[tab$SUL==the_sul,"Reuse"])) {
        if(!(the_ruz=="null")){
          dateRuz<-versions_info[versions_info$version==the_ruz,"date"]
          dateSul<-versions_info[versions_info$version==the_sul,"date"]
          tab[(tab$SUL==the_sul)&(tab$Reuse==the_ruz),"DeltaT"]<-as.numeric(difftime(dateSul, dateRuz))
        }
      }
    }
  }
  rm(dateRuz,dateSul,tab_filename)
}


for (corrMethod in c("pearson", "spearman")) {
  # for (my_x in c("DeltaQ", "DeltaT")) {
  for (my_x in c("DeltaQ")) {
    for (my_y in c("EQ_Resets_Diff", "MQ_Resets_Diff")) {
      query_type<-paste(gsub("_Resets_Diff$","",my_y),"s",sep = "")
      my_xlab = ""; 
      if(my_x=="DeltaQ"){
        my_xlab<-"Structural distance"
      }else if(my_x=="DeltaT"){
        my_xlab<-"Temporal distance"
      }
      my_ylab = paste("Difference between the number of",query_type)
      for (my_method in c("∂L*M", "DL*M+", "DL*M", "Adp")) {
        tab_subset<-tab[tab$Method==my_method,]
        tab_subset<-na.omit(tab_subset)
        # ad.test(tab_subset[,my_y])
        # ppp <-ggscatter(tab_subset[(tab_subset[,my_x]>0),],
        ppp <-ggscatter(tab_subset,
                        x = my_x,
                        y = my_y,
                        xlab = my_xlab,
                        ylab = my_ylab,
                        title = paste("Method:",my_method),
                        add = "reg.line",
                        cor.method = corrMethod,
                        conf.int = TRUE, # Add confidence interval
                        cor.coef = TRUE # Add correlation coefficient. see ?stat_cor
        )+theme(
            plot.title = element_text(hjust = 0.5, size=8),
            axis.text.x  = element_text(angle = 0,   hjust = 0.5, vjust = 0.5, size=6),
            axis.text.y  = element_text(angle = 0,   hjust = 0.5, vjust = 0.5, size=6),
            axis.title.x  = element_text(angle = 0,  hjust = 0.5, vjust = 0.5, size=6),
            axis.title.y  = element_text(angle = 90, hjust = 0.5, vjust = 0.5, size=6)
          )
        filename <- paste(plotdir,paste(logfname,my_x,my_y,my_method,"firstprev",corrMethod,sep = "_"),out_format,sep="")
        ggsave(device=ggsave_dev, filename, width = 6, height = 3.5, dpi=320)  # ssh plots
      }
    }
  }
  
  plot<-ggscatter(tab_subset,
                  y = "DeltaQ",
                  x = "DeltaT",
                  ylab = "Structural distance",
                  xlab = "Temporal distance",
                  title = "Correlation between structural and temporal distance",
                  add = "reg.line",
                  cor.method = corrMethod,
                  conf.int = TRUE, # Add confidence interval
                  cor.coef = TRUE # Add correlation coefficient. see ?stat_cor
  )+theme(
    plot.title = element_text(hjust = 0.5, size=8),
    axis.text.x  = element_text(angle = 0,   hjust = 0.5, vjust = 0.5, size=6),
    axis.text.y  = element_text(angle = 0,   hjust = 0.5, vjust = 0.5, size=6),
    axis.title.x  = element_text(angle = 0,  hjust = 0.5, vjust = 0.5, size=6),
    axis.title.y  = element_text(angle = 90, hjust = 0.5, vjust = 0.5, size=6),
  )
  filename <- paste(plotdir,paste(logfname,"structural_temporal_dist",corrMethod,sep = "_"),out_format,sep="")
  ggsave(device=ggsave_dev, filename, width = 6, height = 3.5, dpi=320)  # ssh plots
}

