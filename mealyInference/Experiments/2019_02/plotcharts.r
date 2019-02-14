source("./util.R")

# out_format<-".png"; ggsave_dev<-"png"
out_format<-".pdf"; ggsave_dev<-cairo_pdf

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

tab<-tab[!(tab$Seed=="null"),]
tab$MQ_Resets_Diff<-0
tab$EQ_Resets_Diff<-0
tab$MQ_Symbols_Diff<-0
tab$EQ_Symbols_Diff<-0
tab$TQ_Resets_Diff<-0
tab$TQ_Symbols_Diff<-0

tab_lsm<-na.omit(tab[tab$Method=="L*M",])
for (sul in unique(tab_lsm$SUL)) {
  tab[tab$SUL==sul,"MQ_Resets_Diff"]<-tab[tab$SUL==sul,"MQ_Resets"]-unique(tab_lsm[tab_lsm$SUL==sul,"MQ_Resets"])
  tab[tab$SUL==sul,"EQ_Resets_Diff"]<-tab[tab$SUL==sul,"EQ_Resets"]-unique(tab_lsm[tab_lsm$SUL==sul,"EQ_Resets"])
  tab[tab$SUL==sul,"MQ_Symbols_Diff"]<-tab[tab$SUL==sul,"MQ_Symbols"]-unique(tab_lsm[tab_lsm$SUL==sul,"MQ_Symbols"])
  tab[tab$SUL==sul,"EQ_Symbols_Diff"]<-tab[tab$SUL==sul,"EQ_Symbols"]-unique(tab_lsm[tab_lsm$SUL==sul,"EQ_Symbols"])
  tab[tab$SUL==sul,"TQ_Resets_Diff"] <-tab[tab$SUL==sul,"TQ_Resets_Diff"]+tab[tab$SUL==sul,"MQ_Resets_Diff"]
  tab[tab$SUL==sul,"TQ_Symbols_Diff"]<-tab[tab$SUL==sul,"TQ_Symbols_Diff"]+tab[tab$SUL==sul,"MQ_Symbols_Diff"]
}
rm(tab_lsm,sul)

plotdir<-paste("./","plots","",logfname,the_EqOracles,"",sep = "/")
dir.create(file.path( plotdir), showWarnings = FALSE,recursive = TRUE)

tab_se<-summarySE(tab,measurevar ="EQ_Resets",groupvars = c("SUL","Reuse","Method"))
tab_filename <- paste(plotdir,"EQ_summary.tab",sep="")
write.table(tab_se, file = tab_filename, sep = "\t",row.names = FALSE, col.names = TRUE)

tab_se<-summarySE(tab,measurevar ="MQ_Resets",groupvars = c("SUL","Reuse","Method"))
tab_filename <- paste(plotdir,"MQ_summary.tab",sep="")
write.table(tab_se, file = tab_filename, sep = "\t",row.names = FALSE, col.names = TRUE)

tab_se<-summarySE(tab,measurevar ="TQ_Resets",groupvars = c("SUL","Reuse","Method"))
tab_filename <- paste(plotdir,"TQ_summary.tab",sep="")
write.table(tab_se, file = tab_filename, sep = "\t",row.names = FALSE, col.names = TRUE)

#####

tab_se<-summarySE(tab,measurevar ="EQ_Resets_Diff",groupvars = c("SUL","Reuse","Method"))
tab_filename <- paste(plotdir,"EQ_Diff_summary.tab",sep="")
write.table(tab_se, file = tab_filename, sep = "\t",row.names = FALSE, col.names = TRUE)

tab_se<-summarySE(tab,measurevar ="MQ_Resets_Diff",groupvars = c("SUL","Reuse","Method"))
tab_filename <- paste(plotdir,"MQ_Diff_summary.tab",sep="")
write.table(tab_se, file = tab_filename, sep = "\t",row.names = FALSE, col.names = TRUE)

tab_se<-summarySE(tab,measurevar ="TQ_Resets_Diff",groupvars = c("SUL","Reuse","Method"))
tab_filename <- paste(plotdir,"TQ_Diff_summary.tab",sep="")
write.table(tab_se, file = tab_filename, sep = "\t",row.names = FALSE, col.names = TRUE)


# subtab<-summarySE(tab,measurevar = "Rounds",groupvars = c("SUL","Reuse","CloS","CExH","EqO","Method"))
subtab<-tab[((tab$Method=="L*M")),]
subtab<-subtab[,c("SUL","CloS","CExH","EqO","Method","Rounds","MQ_Resets","EQ_Resets","MQ_Symbols","EQ_Symbols","Correct")]
subtab<-unique(subtab)

tab_melt <- melt(subtab, id = c("SUL","Method"), measure = c("EQ_Resets","MQ_Resets"))
names(tab_melt)<-c("SUL","Method","Query","Total")
plot <- ggplot(data=tab_melt, aes_string(x="SUL", y="Total")) +
  geom_bar(stat = "identity", position = 'dodge',fill="#CBCBCB")+
  geom_text(aes_string(label="Total"),size=1.5,position = position_dodge(width = 1))+
  facet_wrap(. ~ Query,scales = "free")+
  theme_bw()+
  theme(
    plot.title = element_text(hjust = 0.5, size=8),
    axis.text.x  = element_text(angle = 25, hjust = 1, size=5),
    axis.text.y  = element_text(angle = 0, hjust = 1, size=5),
    axis.title.x = element_blank(),
    axis.title.y = element_text(angle = 90,  hjust = 0.5, size=5),
    strip.text.x = element_text(size = 4)
  )

filename <- paste(plotdir,"lstarm_queries",out_format,sep="")
ggsave(device=ggsave_dev, filename, width = 8, height = 1.5, dpi=320)  # ssh plots

################################
## calculate DeltaT and DeltaQ #
################################

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
  # rm(dateRuz,dateSul,tab_filename)
}

tab$DeltaT<-trunc(tab$DeltaT/(6*30))
# tab$DeltaT<-trunc(tab$DeltaT/7)

tab<-tab[(tab$DeltaT>=0),]

min(tab$DeltaT)
sul_lst  <- unique(tab$SUL)
ruz_lst  <- unique(tab$Reuse)
ruz_lst  <- ruz_lst [! (ruz_lst %in% c('null'))]
methods_lst<-c("∂L*M", "DL*M", "DL*M+", "Adp")

# compute some of the lower and upper whiskers
ylim1 = list()
ylim1[["EQ_Resets_Diff@∂L*M"]]  <-c(-30,5)
ylim1[["EQ_Resets_Diff@DL*M+"]] <-c(-175,25)
# ylim1[["EQ_Resets_Diff@DL*M"]]  <-c(-10,20)
# ylim1[["EQ_Resets_Diff@Adp"]]   <-c(-10,20)
# for (measure_id in c("EQ_Resets_Diff")) {
for (measure_id in c("TQ_Resets_Diff","EQ_Resets_Diff","MQ_Resets_Diff")) {
  bplots<-list()
  for (method_id in methods_lst){
    tab_m<-na.omit(tab[((tab$Method==method_id)),])
    # tab_m<-na.omit(tab[(!(tab$Method=="L*M")),])
    
    tab_melt <- melt(tab_m, id = c("SUL","Method","Reuse","DeltaQ","DeltaT"), measure = measure_id)
    names(tab_melt)<-c("SUL","Method","Reuse","DeltaQ","DeltaT","Type","Number")
    
    plot <- ggplot(data=tab_melt, aes_string(x="DeltaT", y="Number", group="DeltaT")) +
      # geom_boxplot(outlier.colour="red", outlier.shape=8, outlier.size=0.1)+
      geom_boxplot(outlier.shape=NA)+
      stat_boxplot(geom ='errorbar')+
      facet_wrap(. ~ Method,scales = "free", nrow = 1)+
      theme_bw()+
      labs(title = paste("Variation of numbers of queries vs. numbers of states"), x = "Δ number of states", y = gsub("_Resets_Diff","s",paste("Δ number of",measure_id))) +
      theme(
        legend.position="none",
        plot.title = element_blank(), #element_text(hjust = 0.5, size=8),
        axis.text.x  = element_text(angle = 25, hjust = 1,   size=5),
        axis.text.y  = element_text(angle = 0,  hjust = 1,   size=5),
        axis.title.x = element_blank(),
        axis.title.y = element_blank(),
        # axis.title.x = element_text(angle = 0,  hjust = 0.5, size=5),
        # axis.title.y = element_text(angle = 90, hjust = 0.5, size=5),
        strip.text.x = element_text(size = 4, margin = margin(0.05,0,0.05,0, "cm"))
      )
    if(paste(measure_id,method_id,sep = "@") %in% names(ylim1)){
      plot <- plot+ coord_cartesian(ylim = ylim1[[paste(measure_id,method_id,sep = "@")]])  
    }
    
    bplots[[method_id]]<-plot
  }
  bplots[[1]]<-bplots[[1]]+theme(axis.title.y = element_text(angle = 90, size=5))
  pgrid<-plot_grid(plotlist=bplots,labels = "AUTO", label_size = 4, nrow = 1)
  
  title <- ggdraw() + draw_label("Δ number of states", size = 5)
  pgridd<-plot_grid(pgrid,NULL,title, ncol=1, rel_heights=c(1, -0.1, 0.1)) # rel_heights values control title margins
  
  filename <- paste(plotdir,paste(measure_id,sep = "_"),out_format,sep="")
  ggsave(device=ggsave_dev, filename, width = 10, height = 1.7, dpi=320)  # ssh plots
}
  

  
effsiz_method_ctrl <- character()
effsiz_method_trtm <- character()
effsiz_metr <- character()
effsiz_wilc <- numeric()
effsiz_deltaq <- numeric()
effsiz_vd <- numeric()
effsiz_vd_mag <- character()

effsiz_tab <- data.frame(effsiz_method_ctrl,
                         effsiz_method_trtm,
                         effsiz_deltaq,
                         effsiz_metr,
                         effsiz_wilc,
                         effsiz_vd,effsiz_vd_mag)
names(effsiz_tab) <- c("Control","Treatment",
                       "DeltaT",
                       "Measure",
                       "Wilcox",
                       "VD", "VD magnitude" )
checked<-c()
for (method_ctrl in methods_lst) {
  for (method_trtm in methods_lst) {
    if(method_ctrl==method_trtm) next
    idx<-toString(sort(c(method_ctrl,method_trtm)))
    if(idx %in% checked) next;
    checked<-c(idx,checked)
    subtab <- (tab[((tab$Method==method_ctrl) | (tab$Method==method_trtm)),])
    for (dtq in unique(subtab$DeltaT)) {
      for (measure_id in c("TQ_Resets_Diff","EQ_Resets_Diff","MQ_Resets_Diff")) {
        #####################################################
        control   <- c(subtab[((subtab$DeltaT==dtq) & (subtab$Method==method_ctrl)),measure_id])
        treatment <- c(subtab[((subtab$DeltaT==dtq) & (subtab$Method==method_trtm)),measure_id])
        
        ################################
        # L*M vs Each adapive learning #
        ################################
        wilc<-(wilcox.test(control, treatment))
        d <- (c(treatment,control))
        f <- c(rep(c(method_trtm),each=length(treatment)) , rep(c(method_ctrl),each=length(control)))
        ## compute Vargha and Delaney
        effs_vd <- (VD.A(d,f))
        
        effsiz_tab <- rbind(effsiz_tab,data.frame(
          "Control"= method_ctrl,
          "Treatment"= method_trtm,
          "DeltaT" = dtq,
          "Measure"=measure_id,
          "Wilcox"=(wilc$p.value),
          "VD"=(effs_vd$estimate),
          "VD magnitude"=effs_vd$magnitude)
        )
        # dat<-data.frame(Method=f,Queries=d)
        # ggplot(dat, aes(x=Queries)) +
        #   # geom_histogram(binwidth=.5, colour="black", fill="white") +
        #   # # geom_vline(aes(xintercept=mean(Queries, na.rm=T)),   # Ignore NA values for mean
        #   # #            color="red", linetype="dashed", size=1)+
        #   # geom_density()+
        #   geom_histogram(aes(y=..density..),      # Histogram with density instead of count on y-axis
        #                  binwidth=.5,
        #                  colour="black", fill="white") +
        #   geom_density(alpha=.2, fill="#FF6666")+  # Overlay with transparent density plot
        #   facet_wrap(. ~ Method,scales = "free")
      }
    }
  }
}
  
tab_filename <- paste(plotdir,"effsize.tab",sep="")
write.table(effsiz_tab, file = tab_filename, sep = "\t",row.names = FALSE, col.names = TRUE)

effsiz_tab$Comparison<-paste(effsiz_tab$Control,"vs.",effsiz_tab$Treatment)

mu <- ddply(effsiz_tab, c("Control","Treatment","Measure"), summarise, grp.mean=mean(VD))
tab_filename <- paste(plotdir,"avg_effsize.tab",sep="")
write.table(mu, file = tab_filename, sep = "\t",row.names = FALSE, col.names = TRUE)


for (measure_id in c("TQ_Resets_Diff","EQ_Resets_Diff","MQ_Resets_Diff")) {
  subtab<-effsiz_tab[(effsiz_tab$Measure==measure_id),]
  mu <- ddply(subtab, c("Control","Treatment"), summarise, grp.mean=mean(VD))
  ggplot(subtab, aes(x=VD,fill=Comparison)) + 
    geom_histogram(aes(y=..density..), colour="black", fill="white", bins=9)+
    stat_density(alpha=.2, fill="darkgray") +
    # facet_grid(Treatment ~ Control,scales = "free")+
    facet_wrap(Control ~ Treatment ,scales = "free",nrow = 1)+
    theme_bw()+
    coord_cartesian(xlim = c(0,1))+
    labs(title = "", x = "Vargha-Delaney's Â", y = "Count") +
    theme(
      plot.title = element_blank(), 
      axis.text.x  = element_text(angle = 25, hjust = 1,   size=5),
      axis.text.y  = element_text(angle = 0,  hjust = 1,   size=5),
      axis.title.x = element_text(angle = 0,  hjust = 0.5, size=5),
      axis.title.y = element_text(angle = 90, hjust = 0.5, size=5),
      strip.text.x = element_text(size = 5, margin = margin(0.05,0,0.05,0, "cm"))
    )+
    geom_vline(data=mu,aes(xintercept=grp.mean),color="darkgray", linetype="dashed", size=0.75)
  filename <- paste(plotdir,paste("effsize_hist",measure_id,sep = "_"),out_format,sep="")
  # ggsave(device=ggsave_dev, filename, width = 10, height = 4, dpi=320)  # facet_grid
  ggsave(device=ggsave_dev, filename, width = 10, height = 2, dpi=320)  # facet_wrap
}

for (measure_id in c("TQ_Resets_Diff","EQ_Resets_Diff","MQ_Resets_Diff")) {
  subtab<-effsiz_tab[(effsiz_tab$Measure==measure_id),]
  ggplot(subtab, aes(x=DeltaT,y=VD,group=DeltaT)) + 
    geom_hline(aes(yintercept=0.147),color="red", linetype="dashed",   size=0.25)+
    geom_hline(aes(yintercept=0.853),color="red", linetype="dashed",   size=0.25)+
    geom_hline(aes(yintercept=0.330),color="blue", linetype="dashed", size=0.25)+
    geom_hline(aes(yintercept=0.670),color="blue", linetype="dashed", size=0.25)+
    geom_hline(aes(yintercept=0.474),color="gray", linetype="dashed",  size=0.25)+
    geom_hline(aes(yintercept=0.526),color="gray", linetype="dashed",  size=0.25)+
    geom_boxplot(outlier.shape=NA)+
    facet_wrap(Control ~ Treatment ,ncol = 1)+
    theme_bw()+
    coord_cartesian(ylim = c(0,1))+
    labs(title = "", x = "Vargha-Delaney's Â", y = "Count") +
    theme(
      plot.title = element_blank(), 
      axis.text.x  = element_text(angle = 25, hjust = 1,   size=5),
      axis.text.y  = element_text(angle = 0,  hjust = 1,   size=5),
      axis.title.x = element_text(angle = 0,  hjust = 0.5, size=5),
      axis.title.y = element_text(angle = 90, hjust = 0.5, size=5),
      strip.text.x = element_text(size = 5, margin = margin(0.05,0,0.05,0, "cm"))
    )
    
  filename <- paste(plotdir,paste("effsize_boxplot",measure_id,sep = "_"),out_format,sep="")
  # ggsave(device=ggsave_dev, filename, width = 10, height = 4, dpi=320)  # facet_grid
  ggsave(device=ggsave_dev, filename, width = 3, height = 10, dpi=320)  # facet_wrap
}
  

for (my_x in c("DeltaT")) {
  # for (corrMethod in c("pearson", "kendall", "spearman")) {
  for (corrMethod in c("pearson")) {
    for (my_y in c("EQ_Resets_Diff", "MQ_Resets_Diff")) {
      query_type<-paste(gsub("_Resets_Diff$","",my_y),"s",sep = "")
      my_xlab = ""; 
      if(my_x=="DeltaT"){
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
      
      
      # normal<-tab_subset[,my_y]
      # ggqqplot(normal)
      # shapiro.test(normal)
      # filename <- paste(plotdir,paste(logfname,my_x,my_y,my_method,"hist",sep = "_"),out_format,sep="")
      # ggsave(device=ggsave_dev, filename, width = 6, height = 3.5, dpi=320)  # ssh plots
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

