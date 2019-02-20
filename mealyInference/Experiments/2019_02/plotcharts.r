source("./util.R")

out_format<-".png"; ggsave_dev<-"png"
out_format<-".pdf"; ggsave_dev<-cairo_pdf

logdir<-"./"

the_EqOracles<-"WpMethodHypEQOracle";
methods_lst<-c("∂L*M", "Adp", "DL*M", "DL*M+")


logfname <- "nordsec16_server"
tab<-prepareTab(logdir,logfname)
tab<-tab[!(grepl("^L1",tab$Method)),]; tab<-tab[!(grepl("^TTT",tab$Method)),]
# tab<-tab[!(grepl("^DL.M_v1",tab$Method)),]; 
tab$Method<-gsub("^DL.M_v2",paste(sprintf('\u2202'),"L*M",sep = ""),tab$Method); 
tab$Method<-gsub("^DL.M_v1","DL*M+",tab$Method); 
tab$Method<-gsub("^DL.M_v0","DL*M",tab$Method); 
tab$Method<-factor(tab$Method,levels = c("∂L*M", "Adp", "DL*M+", "DL*M", "L*M", "L1","TTT"))

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

for (the_col in c("MQ_Resets_Diff","EQ_Resets_Diff")) {
  the_ctrl<-"∂L*M"
  control<-tab[(tab$Method==the_ctrl),   ]
  control<-control[,the_col]
  for (the_trmt in c("Adp","DL*M","DL*M+")) {
    treatment<-tab[(tab$Method==the_trmt),]
    treatment<-treatment[,the_col]
    wilc<-wilcox.test(control, treatment)
    print(paste(the_col,"@",the_ctrl,"vs.",the_trmt,":",wilc$p.value))
  }
}

for (theMethod in c("L*M",methods_lst)) {
  # subtab<-summarySE(tab,measurevar = "Rounds",groupvars = c("SUL","Reuse","CloS","CExH","EqO","Method"))
  subtab<-tab[((tab$Method==theMethod)),]
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
  
  filename <- paste(plotdir,theMethod,"_queries",out_format,sep="")
  ggsave(device=ggsave_dev, filename, width = 8, height = 1.5, dpi=320)  # ssh plots  
}


rm(subtab,tab_melt,plot,filename)

##########################################
## calculate Delta Time and Delta States #
##########################################

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
    tab$DeltaD<-0
    for (the_sul in unique(tab$SUL)) {
      for (the_ruz in unique(tab[tab$SUL==the_sul,"Reuse"])) {
        if(!(the_ruz=="null")){
          dateRuz<-versions_info[versions_info$version==the_ruz,"date"]
          dateSul<-versions_info[versions_info$version==the_sul,"date"]
          tab[(tab$SUL==the_sul)&(tab$Reuse==the_ruz),"DeltaD"]<-as.numeric(difftime(dateSul, dateRuz))
        }
      }
    }
  }
}
rm(dateRuz,dateSul,tab_filename,the_ruz,the_sul,versions_info)

tab$DeltaY<-trunc(tab$DeltaD/(12*30))
tab$DeltaM<-trunc(tab$DeltaD/(30))
tab$DeltaW<-trunc(tab$DeltaD/(7))

tab<-tab[(tab$DeltaD>=0),]

for (deltaType in c("DeltaD","DeltaY","DeltaW","DeltaM")) {
  my_xlab = ""; 
  if(deltaType=="DeltaD") my_xlab<-"Δ time (Days)"
  if(deltaType=="DeltaY") my_xlab<-"Δ time (Years)"
  if(deltaType=="DeltaM") my_xlab<-"Δ time (Months)"
  if(deltaType=="DeltaW") my_xlab<-"Δ time (Weeks)"

  plotdir_type<-paste(plotdir,deltaType,"/",sep = "/")
  dir.create(file.path(plotdir_type), showWarnings = FALSE,recursive = TRUE)
  
  tab_se<-summarySE(tab,measurevar ="EQ_Resets",groupvars = c("SUL","Reuse",deltaType,"Method"))
  tab_filename <- paste(plotdir_type,"EQ_summary.tab",sep="")
  write.table(tab_se, file = tab_filename, sep = "\t",row.names = FALSE, col.names = TRUE)
  
  tab_se<-summarySE(tab,measurevar ="MQ_Resets",groupvars = c("SUL","Reuse",deltaType,"Method"))
  tab_filename <- paste(plotdir_type,"MQ_summary.tab",sep="")
  write.table(tab_se, file = tab_filename, sep = "\t",row.names = FALSE, col.names = TRUE)
  
  # tab_se<-summarySE(tab,measurevar ="TQ_Resets",groupvars = c("SUL","Reuse",deltaType,"Method"))
  # tab_filename <- paste(plotdir_type,"TQ_summary.tab",sep="")
  # write.table(tab_se, file = tab_filename, sep = "\t",row.names = FALSE, col.names = TRUE)
  
  #####
  
  tab_se<-summarySE(tab,measurevar ="EQ_Resets_Diff",groupvars = c("SUL","Reuse",deltaType,"Method"))
  tab_filename <- paste(plotdir_type,"EQ_Diff_summary.tab",sep="")
  write.table(tab_se, file = tab_filename, sep = "\t",row.names = FALSE, col.names = TRUE)
  
  tab_se<-summarySE(tab,measurevar ="MQ_Resets_Diff",groupvars = c("SUL","Reuse",deltaType,"Method"))
  tab_filename <- paste(plotdir_type,"MQ_Diff_summary.tab",sep="")
  write.table(tab_se, file = tab_filename, sep = "\t",row.names = FALSE, col.names = TRUE)
  
  # tab_se<-summarySE(tab,measurevar ="TQ_Resets_Diff",groupvars = c("SUL","Reuse",deltaType,"Method"))
  # tab_filename <- paste(plotdir_type,"TQ_Diff_summary.tab",sep="")
  # write.table(tab_se, file = tab_filename, sep = "\t",row.names = FALSE, col.names = TRUE)
  
  rm(tab_se,tab_filename)
  
  # compute some of the lower and upper whiskers
  ylim1 = list()
  ylim1[["EQ_Resets_Diff@∂L*M"]]  <-c(-15,10);   ylim1[["EQ_Resets_Diff@Adp"]]   <-c(-15,10)
  ylim1[["EQ_Resets_Diff@DL*M+"]] <-c(-100,450); ylim1[["EQ_Resets_Diff@DL*M"]]  <-c(-100,450)
  ylim1[["MQ_Resets_Diff@∂L*M"]]  <-c(-150,85);   ylim1[["MQ_Resets_Diff@Adp"]]   <-c(-150,85)
  ylim1[["MQ_Resets_Diff@DL*M+"]] <-c(-100,800); ylim1[["MQ_Resets_Diff@DL*M"]]  <-c(-100,800)
  # for (measure_id in c("EQ_Resets_Diff")) {
  # for (measure_id in c("TQ_Resets_Diff","EQ_Resets_Diff","MQ_Resets_Diff")) {
  for (measure_id in c("EQ_Resets_Diff","MQ_Resets_Diff")) {
    bplots<-list()
    for (method_id in methods_lst){
      tab_m<-na.omit(tab[((tab$Method==method_id)),])
      # tab_m<-na.omit(tab[(!(tab$Method=="L*M")),])
  
      tab_melt <- melt(tab_m, id = c("SUL","Method","Reuse","DeltaQ",deltaType), measure = measure_id)
      names(tab_melt)<-c("SUL","Method","Reuse","DeltaQ",deltaType,"Type","Number")
  
      # tab_melt$Number<-log(tab_melt$Number)
      plot <- ggplot(data=tab_melt, aes_string(x=deltaType, y="Number", group=deltaType)) +
        geom_boxplot(outlier.colour="red", outlier.shape=8, outlier.size=0.1)+
        # geom_boxplot(outlier.shape=NA)+
        stat_boxplot(geom ='errorbar')+
        facet_wrap(. ~ Method,scales = "free", nrow = )+
        theme_bw()+
        labs(y = gsub("_Resets_Diff","s",paste("Δ number of",measure_id))) +
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
    # bplots[[1]]<-bplots[[1]]+theme(axis.title.y = element_text(angle = 90, size=5))
    pgrid<-plot_grid(plotlist=bplots,labels = "AUTO", label_size = 4, nrow = 2)
  
    x_title <- ggdraw() + draw_label(gsub("_Resets_Diff","s",paste("Δ number of",measure_id)), size = 5, angle = 90)
    pgrid<-plot_grid(x_title,pgrid,nrow = 1, rel_widths = c(0.025,1))
    
    y_title <- ggdraw() + draw_label(my_xlab, size = 5)
    pgridd<-plot_grid(pgrid,NULL,y_title, ncol=1, rel_heights=c(1, -0.08, 0.1)) # rel_heights values control title margins
  
    filename <- paste(plotdir_type,paste("plot",measure_id,sep = "_"),out_format,sep="")
    ggsave(device=ggsave_dev, filename, width = 4, height = 3, dpi=320)  # ssh plots
  }
  rm(bplots,pgrid,pgridd,plot,tab_m,tab_melt,x_title,y_title,ylim1,filename)

  effsiz_tab <- data.frame(character(),
                           character(),
                           character(),
                           numeric(),
                           numeric(),
                           numeric(),
                           character())
  names(effsiz_tab) <- c("Control","Treatment",
                         "Delta",
                         "Measure",
                         "Wilcox",
                         "VD", "VD magnitude" )
  checked<-c()
  
  for (method_ctrl in c("∂L*M")) {
    for (method_trtm in methods_lst) {
      if(method_ctrl==method_trtm) next
      idx<-toString(sort(c(method_ctrl,method_trtm)))
      if(idx %in% checked) next;
      checked<-c(idx,checked)
      subtab <- (tab[((tab$Method==method_ctrl) | (tab$Method==method_trtm)),])
      for (dtq in unique(subtab[,deltaType])) {
        for (measure_id in c("TQ_Resets_Diff","EQ_Resets_Diff","MQ_Resets_Diff")) {
          #####################################################
          control   <- c(subtab[((subtab[,deltaType]==dtq) & (subtab$Method==method_ctrl)),measure_id])
          treatment <- c(subtab[((subtab[,deltaType]==dtq) & (subtab$Method==method_trtm)),measure_id])
          
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
            "Delta" = dtq,
            "Measure"=measure_id,
            "Wilcox"=(wilc$p.value),
            "VD"=(effs_vd$estimate),
            "VD magnitude"=effs_vd$magnitude)
          )
        }
      }
    }
  }
  
  tab_filename <- paste(plotdir_type,"effsize.tab",sep="")
  write.table(effsiz_tab, file = tab_filename, sep = "\t",row.names = FALSE, col.names = TRUE)
  
  effsiz_tab$Comparison<-paste(effsiz_tab$Control,"vs.",effsiz_tab$Treatment)
  
  mu <- ddply(effsiz_tab, c("Control","Treatment","Measure"), summarise, grp.mean=mean(VD))
  tab_filename <- paste(plotdir_type,"avg_effsize.tab",sep="")
  write.table(mu, file = tab_filename, sep = "\t",row.names = FALSE, col.names = TRUE)
  
  
  # for (measure_id in c("TQ_Resets_Diff","EQ_Resets_Diff","MQ_Resets_Diff")) {
  for (measure_id in c("EQ_Resets_Diff","MQ_Resets_Diff")) {
    subtab<-effsiz_tab[(effsiz_tab$Measure==measure_id),]
    mu <- ddply(subtab, c("Control","Treatment"), summarise, grp.mean=mean(VD))
    
    dat_text <- data.frame(
      Control = mu$Control,
      Treatment = mu$Treatment,
      Comparison = paste(mu$Control,"vs.",mu$Treatment),
      Mean   = paste("μ =",round(mu$grp.mean,digits = 3))
    )
    
    ggplot(subtab, aes(x=VD,fill=Comparison)) + 
      geom_histogram(aes(y=..density..), colour="black", fill="white", bins=9)+
      # stat_density(alpha=.2, fill="darkgray") +
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
      )+ geom_text(
        data    = dat_text,
        mapping = aes(x = -Inf, y = -Inf, label = Mean),
        x   = .85,
        y   = 2,
        size = 2
      )+ 
      geom_vline(data=mu,aes(xintercept=grp.mean),color="darkgray", linetype="dashed", size=0.75)
    filename <- paste(plotdir_type,paste("effsize_hist",measure_id,sep = "_"),out_format,sep="")
    # ggsave(device=ggsave_dev, filename, width = 10, height = 4, dpi=320)  # facet_grid
    ggsave(device=ggsave_dev, filename, width = 6, height = 2, dpi=320)  # facet_wrap
  }
  
  # for (measure_id in c("TQ_Resets_Diff","EQ_Resets_Diff","MQ_Resets_Diff")) {
  for (measure_id in c("EQ_Resets_Diff","MQ_Resets_Diff")) {

    subtab<-effsiz_tab[(effsiz_tab$Measure==measure_id),]
    ggplot(subtab, aes(x=Delta,y=VD,group=Delta)) + 
      geom_hline(aes(yintercept=0.147),color="red",  alpha = 0.30, linetype="dashed",   size=0.25)+
      geom_hline(aes(yintercept=0.853),color="red",  alpha = 0.30, linetype="dashed",   size=0.25)+
      geom_hline(aes(yintercept=0.330),color="blue", alpha = 0.30, linetype="dashed", size=0.25)+
      geom_hline(aes(yintercept=0.670),color="blue", alpha = 0.30, linetype="dashed", size=0.25)+
      geom_hline(aes(yintercept=0.474),color="gray", alpha = 0.30, linetype="dashed",  size=0.25)+
      geom_hline(aes(yintercept=0.526),color="gray", alpha = 0.30, linetype="dashed",  size=0.25)+
      # geom_boxplot(outlier.shape=NA)+
      geom_boxplot(outlier.colour="red", outlier.shape=8, outlier.size=0.1)+
      facet_wrap(Control ~ Treatment ,ncol = 1)+
      theme_bw()+
      coord_cartesian(ylim = c(0,1))+
      labs(title = "", y = "Vargha-Delaney's Â", x = my_xlab) +
      theme(
        plot.title = element_blank(), 
        axis.text.x  = element_text(angle = 25, hjust = 1,   size=5),
        axis.text.y  = element_text(angle = 0,  hjust = 1,   size=5),
        axis.title.x = element_text(angle = 0,  hjust = 0.5, size=5),
        axis.title.y = element_text(angle = 90, hjust = 0.5, size=5),
        strip.text.x = element_text(size = 5, margin = margin(0.05,0,0.05,0, "cm"))
      )
    
    filename <- paste(plotdir_type,paste("effsize_boxplot",measure_id,sep = "_"),out_format,sep="")
    # ggsave(device=ggsave_dev, filename, width = 10, height = 4, dpi=320)  # facet_grid
    ggsave(device=ggsave_dev, filename, width = 3, height = 4, dpi=320)  # facet_wrap
  }
  
  
  my_x<- deltaType
  my_xlab = ""; 
  if(deltaType=="DeltaQ") my_xlab<-"Δ states"
  if(deltaType=="DeltaD") my_xlab<-"Δ time (Days)"
  if(deltaType=="DeltaY") my_xlab<-"Δ time (Years)"
  if(deltaType=="DeltaY") my_xlab<-"Δ time (Months)"
  # for (corrMethod in c("pearson", "kendall", "spearman")) {
  for (corrMethod in c("pearson")) {
    for (my_y in c("EQ_Resets_Diff", "MQ_Resets_Diff")) {
      query_type<-paste(gsub("_Resets_Diff$","",my_y),"s",sep = "")
      
      my_ylab = paste("Δ number of",query_type)
      for (my_method in c("∂L*M", "DL*M+", "DL*M", "Adp")) {
        tab_subset<-tab[tab$Method==my_method,]
        tab_subset<-na.omit(tab_subset)
        # ad.test(tab_subset[,my_y])
        # ppp <-ggscatter(tab_subset[(tab_subset[,my_x]>0),],
        ppp <-ggscatter(tab_subset,
                        x = deltaType,
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
        filename <- paste(plotdir_type,paste(logfname,my_x,my_y,my_method,"firstprev",corrMethod,sep = "_"),out_format,sep="")
        ggsave(device=ggsave_dev, filename, width = 6, height = 3.5, dpi=320)  # ssh plots
      }
    }
  }
  
  plot<-ggscatter(tab_subset,
                  y = "DeltaQ",
                  x = deltaType,
                  ylab = "Δ number of states",
                  xlab = my_xlab,
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
  filename <- paste(plotdir_type,paste(logfname,"structural_temporal_dist",corrMethod,sep = "_"),out_format,sep="")
  ggsave(device=ggsave_dev, filename, width = 6, height = 3.5, dpi=320)  # ssh plots
}

