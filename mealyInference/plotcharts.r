# source("./util.R")
list.of.packages <- c("ggplot2","reshape2","gtools","stringr","scales","effsize","SortableHTMLTables","RColorBrewer","ggpubr","nortest","cowplot","reshape")

new.packages <- list.of.packages[!(list.of.packages %in% installed.packages(lib.loc="/home/cdnd1/Rpackages/")[,"Package"])]
if(length(new.packages)) install.packages(new.packages,lib="/home/cdnd1/Rpackages/")
lapply(list.of.packages,require,character.only=TRUE, lib.loc="/home/cdnd1/Rpackages/")

# new.packages <- list.of.packages[!(list.of.packages %in% installed.packages()[,"Package"])]
# if(length(new.packages)) install.packages(new.packages, dependencies = TRUE)
# lapply(list.of.packages,require,character.only=TRUE)

;rm(new.packages,list.of.packages)


# args = commandArgs(trailingOnly=TRUE)
logdir<-"/home/cdnd1/euler_remote/"
logfname <- "ssh"
# logfname <- "mqtt"
# logfname <- "nordsec16"
# logfname <- "tcp"
## logfname <- "xray"


tab<-data.frame()
# for (logfname in logs) {
tab_filename<-paste(logdir,logfname,".tab",sep="")
tab <- rbind(tab,read.table(tab_filename, sep="|", header=TRUE))
# }

names(tab) <- c("SUL","Seed","Cache","CloS","CExH","EqO","Method","Reuse","Reused_Resets","Reused_Symbols","Rounds","MQ_Resets","MQ_Symbols","EQ_Resets","EQ_Symbols","L_ms","SCEx","Q_Size","I_Size","Correct","Info" )
tab$Info<-gsub("^N/A$","null",tab$Info)

tab$L_ms    <- as.numeric(tab$L_ms)
tab$Rounds  <- as.numeric(tab$Rounds)
tab$SCEx_ms <- as.numeric(tab$CExH)
tab$MQ_Resets  <- as.numeric(tab$MQ_Resets)
tab$MQ_Symbols <- as.numeric(tab$MQ_Symbols)
tab$EQ_Resets  <- as.numeric(tab$EQ_Resets)
tab$EQ_Symbols <- as.numeric(tab$EQ_Symbols)
tab$Correct    <- as.character(tab$Correct)
tab$Seed  <- as.character(tab$Seed)

tab$TQ_Resets  <- tab$MQ_Resets+tab$EQ_Resets
tab$TQ_Symbols  <- tab$MQ_Symbols+tab$EQ_Symbols


tab$SUL <- gsub('\\.[a-z]+$', '', gsub('\\.[a-z]+$', '', gsub('\\.[a-z]+$', '', tab$SUL)))
tab$Reuse <- gsub('\\.[a-z]+$', '', gsub('\\.[a-z]+$', '', gsub('\\.[a-z]+$', '', tab$Reuse)))
tab$EqO <- gsub('\\([^\\(]+\\)$', '', tab$EqO)

tab$Method<-factor(tab$Method,levels = c("TTT","DL*M_v2", "DL*M_v1", "Adaptive", "L*M", "L1"))

for (anEqO in unique(tab$EqO)) {
  # if(anEqO=="RandomWMethodHypEQOracle") next
  plotdir<-paste("","plots","",logfname,anEqO,"",sep = "/")
  dir.create(file.path(logdir, plotdir), showWarnings = FALSE,recursive = TRUE)
  
  tab_se <- tab[grep(paste("^",anEqO,sep = ""),tab$EqO),]
  tab_se<-tab_se[!(grepl("TTT",tab_se$Method)|grepl("L1",tab_se$Method)),]
  
  tab_ok <- tab_se
  tab_ok$CorrectType <- paste(tab_ok$SUL,tab_ok$Reuse,tab_ok$Method,tab_ok$Correct,sep = "|")
  tab_ok <- rle(sort(tab_ok$CorrectType))

  df_ok <- data.frame(Correct=tab_ok$values, Total=tab_ok$lengths)
  df_ok$Percent <-0
  df_ok<-transform(df_ok, FOO = colsplit(Correct, split = "\\|", names = c('SUL','Reuse','Method', 'Correct')))
  names(df_ok)<-c("SRMC","Total","Percent","SUL","Reuse","Method","Correct")
  df_ok$SRMC <- paste(df_ok$SUL,df_ok$Reuse,df_ok$Method,sep = "|")
  df_ok<-df_ok[,c(4,5,6,7,2,3,1)]

  for (variable in unique(df_ok$SRMC)) {
    df_ok[((df_ok$SRMC==variable)&(df_ok$Correct=="OK")),"Percent"]<-df_ok[((df_ok$SRMC==variable)&(df_ok$Correct=="OK")),"Total"]/sum(df_ok[((df_ok$SRMC==variable)),"Total"])
    df_ok[((df_ok$SRMC==variable)&(df_ok$Correct=="NOK")),"Percent"]<-df_ok[((df_ok$SRMC==variable)&(df_ok$Correct=="NOK")),"Total"]/sum(df_ok[((df_ok$SRMC==variable)),"Total"])
  }
  
  df_ok$SUL  <-gsub("^SUL_","",gsub('\\.[a-z]+$',"",df_ok$SUL))
  df_ok$Reuse<-gsub("^SUL_","",gsub('\\.[a-z]+$',"",df_ok$Reuse))
  
  # df_ok$Approach<-paste(df_ok$Method,"(",df_ok$SUL,",",df_ok$Reuse,")",sep = "");df_ok$Approach<-gsub("null\\)$",")",df_ok$Approach)
  df_ok$Approach<-paste(df_ok$Method,"(",df_ok$Reuse,")",sep = "");df_ok$Approach<-gsub("\\(null\\)$","",df_ok$Approach)
  
  tab_this <- df_ok
  tab_tmp<-data.frame()
  for (sul_id in unique(tab_this$SUL)) {
    for (tmp in unique(tab_this[(tab_this$SUL==sul_id),"Reuse"])) {
      if(grepl("^null",tmp)) next;
      new_rows<-tab_this[((tab_this$Reuse=="null")&(tab_this$SUL==sul_id)),]
      new_rows$Reuse<-gsub("^null",tmp,new_rows$Reuse)
      tab_tmp<-rbind(tab_tmp,new_rows)
    }
  }
  tab_this<-rbind(tab_this,tab_tmp)
  tab_this<-tab_this[!grepl("^null",tab_this$Reuse),]
  df_ok<-tab_this[!(grepl("L*M",tab_this$Method) & grepl("L1",tab_this$Method) & grepl("TTT",tab_this$Method)),]
  df_ok<-rbind(df_ok,unique(tab_this[(grepl("L*M",tab_this$Method) & grepl("L1",tab_this$Method) & grepl("TTT",tab_this$Method)),]))
  
  
  # bplots<-list()
  for(sul_id in unique(df_ok$SUL)){
    # reused_models<-levels(factor(unique(data[(data$Inferred==sul_id),"Reused"])))
    df_ok$PercentRnd<-round(df_ok$Percent,digits = 2)
    df_tmp<-df_ok[grepl(sul_id,df_ok$SUL),]
    p2 <- ggplot(df_tmp, aes(Reuse,Percent))+ 
      geom_bar(stat = "identity", aes(fill = Correct,group=Correct),position = 'dodge')+
      geom_text(aes(label=PercentRnd,group=Correct),size=2,position = position_dodge(width = 1))+
      facet_grid(. ~ Method, scales = "free", space = "free")+
      theme_bw()+
      scale_color_grey()+
      labs(title = paste("Equivalence Oracle: ",anEqO), x = "Reused OT", y = paste(" SUL: ",sul_id," (% correct Hyp.)",sep = "")) +
      theme(
        plot.title = element_text(hjust = 0.5, size=7),
        # legend.position="none",
        legend.title = element_text(hjust = 0.5, size=7),
        legend.text = element_text(hjust = 0.5, size=5),
        legend.box.background = element_rect(),
        axis.text.x = element_text(angle = 35, hjust = 1, size=7),
        axis.title.x=element_blank(),
        axis.title.y = element_text(angle = 90, size=7)
      )+
      scale_fill_manual(values = c("grey50", "grey90", "red"),
                         labels = c("OK", "NOK", "null"), 
                         drop = FALSE)
      
    filename <- paste(logdir,plotdir,paste("boxplot",sul_id,sep = "_"),".png",sep="")
    ggsave(filename, width = 10, height = 5)
    # bplots[[sul_id]]<-p2
  }
  # p2<-plot_grid(plotlist=bplots,ncol = 1)
  # p2<-plot_grid(p2,get_legend(bplots[[1]]+theme(legend.position = "right",legend.title=element_text(size=5),legend.text=element_text(size=5))),nrow = 1,rel_widths = c(8, 1))
  # filename <- paste(logdir,plotdir,paste("boxplot_",sul_id,sep = "_"),".pdf",sep="")
  # ggsave(filename, width = 30, height = 40)
  # next
  
  ;rm(df_ok,tab_this,tab_ok,df_tmp,new_rows,bplots,p2,plot,tmp)
  
  tab_se <- tab_se[grepl("OK",tab_se$Correct),]
  
  # tab_se<-tab_se[!(grepl("TTT",tab_se$Method)|grepl("L1",tab_se$Method)),]
  tab_se$SUL<-gsub("^SUL_","",tab_se$SUL)
  tab_se$Reuse<-gsub("^SUL_","",tab_se$Reuse)
  # for(metric_id in c("MQ_Resets","TQ_Resets","EQ_Resets")){
  for(metric_id in c("Rounds","TQ_Resets","MQ_Resets","EQ_Resets")){
    tab_this <- tab_se
    tab_tmp<-data.frame()
    for (sul_id in unique(tab_this$SUL)) {
      for (tmp in unique(tab_this[(tab_this$SUL==sul_id),"Reuse"])) {
        if(grepl("^null",tmp)) next;
        new_rows<-tab_this[((tab_this$Reuse=="null")&(tab_this$SUL==sul_id)),]
        new_rows$Reuse<-gsub("^null",tmp,new_rows$Reuse)
        tab_tmp<-rbind(tab_tmp,new_rows)
      }
    }
    tab_this<-rbind(tab_this,tab_tmp)
    tab_this<-tab_this[!grepl("^null",tab_this$Reuse),]
    ;rm(tab_tmp)
    
    for(id_sul in unique(tab_this$SUL)){
      tab_l<-tab_this[grepl(id_sul,tab_this$SUL),]
      title_lab <- paste(metric_id,"@",id_sul)
      plot <- ggplot(tab_l, aes_string(x="Method", y=metric_id,group="Method",fill="Method")) +
        geom_boxplot()+
        # coord_flip() +
        facet_grid(. ~ Reuse)+
        theme_bw() +
        scale_color_grey() + 
        labs(title = paste("SUL: ",id_sul," - ","EqOracle: ",anEqO), x = "Approach", y = paste(metric_id,sep = "")) +
        theme(
          plot.title = element_text(hjust = 0.5, size=7),
          # legend.position="bottom",
          legend.position="none",
          legend.title = element_text(hjust = 0.5, size=7),
          legend.text = element_text(hjust = 0.5, size=5),
          legend.box.background = element_rect(),
          axis.text.x = element_text(angle = 25, hjust = 1, size=7),
          axis.title.x = element_text(hjust = 0.5, size=7),
          axis.title.y = element_text(angle = 90, size=7),
          strip.text = element_text(hjust = 0.5, size=7)
        )+
        scale_fill_manual(values = c("grey70", "grey60", "grey50", "grey80", "grey90", "grey100"),
                          labels = c("DL*M_v2", "DL*M_v1", "Adaptive", "L*M", "L1", "TTT"), 
                          drop = FALSE)
      filename <- paste(logdir,plotdir,paste(metric_id,id_sul,sep = "_"),".png",sep="")
      ggsave(filename, width = 10, height = 3)
      ;rm(tab_l,plot,df_tmp)
    }
  }
  
  # effsiz_sul <- character()
  # effsiz_reuz <- character()
  # effsiz_metr <- character()
  # effsiz_wilc <- numeric()
  # effsiz_vd <- numeric()
  # effsiz_vd_mag <- character()
  # 
  # effsiz_tab <- data.frame(effsiz_sul,effsiz_reuz,effsiz_metr,effsiz_wilc,effsiz_vd,effsiz_vd_mag)
  # names(effsiz_tab) <- c("SUL","Reuse", "Metric","Wilcox","VD", "VD magnitude" )
  # 
  # reuse_ids_wona <-unique(tab_se$Reuse)
  # reuse_ids_wona <- setdiff(reuse_ids_wona,c("N/A"))
  # for(metric_id in c("EQ_Resets","MQ_Resets")){
  #   for(SUL_id in unique(tab_se$SUL)){
  #     for(reuse_id in reuse_ids_wona){
  #       # if(SUL_id==reuse_id) next
  #       # for(metric_id in c( "L_ms","Rounds","SCEx_ms","MQ_Resets","MQ_Symbols", "EQ_Resets","EQ_Symbols")){
  #       
  #       
  #       #####################################################
  #       # print(paste("SUL ",SUL_id, "Reval(",reuse_id,") | Metric: ",metric_id))
  #       control<-tab_se[(tab_se$SUL==SUL_id),]
  #       control<-control[(control$Reuse=="N/A"),]
  #       
  #       treatment<-tab_se[(tab_se$SUL==SUL_id),]
  #       treatment<-treatment[(treatment$Reuse==reuse_id),]
  #       
  #       control<-control[,metric_id]
  #       treatment<-treatment[,metric_id] 
  #       wilc<-(wilcox.test(control, treatment, paired=FALSE, alternative = "greater",conf.level = 0.95))
  #       
  #       ######################
  #       # L*M vs Dynamic L*M #
  #       ######################
  #       
  #       d <- (c(treatment,control))
  #       f <- c(rep(c("Treatment"),each=length(treatment)) , rep(c("Control"),each=length(control)))
  #       ## compute Cohen's d
  #       ## data and factor
  #       # effs_d <- print(cohen.d(d,f,paired = FALSE))
  #       ## compute Hedges' g
  #       # effs_g <- print(cohen.d(d,f,hedges=TRUE,paired = FALSE))
  #       ## compute Vargha and Delaney 
  #       effs_vd <- (VD.A(d,f))
  #       
  #       effsiz_tab <- rbind(effsiz_tab,data.frame(
  #         "SUL"=SUL_id,
  #         "Reuse"=reuse_id,
  #         "Metric"=metric_id,
  #         "Wilcox"=(as.numeric(wilc[3])),
  #         "VD"=(effs_vd$estimate),
  #         "VD magnitude"=effs_vd$magnitude
  #       ))
  #       
  #       
  #       x_d <- c(control,treatment)
  #       f_d <- c(rep(c("L*M"),each=length(control)), rep(c("Dynamic L*M"),each=length(treatment)))
  #       x_temp <- data.frame(Metric=x_d,Inference=f_d)
  #       data_temp  <- melt(x_temp,id.vars = "Inference")
  #       plot <- ggplot(data_temp, aes(x = value,fill=Inference)) + 
  #         geom_density(alpha=0.4) + 
  #         # scale_fill_grey(start = 0, end = .9) +
  #         ggtitle(label = paste("SUL ",SUL_id, "Reval(",reuse_id,") | Metric: ",metric_id),subtitle = paste("VD Â12 =",round(effs_vd$estimate,digits=3),"(magn. ",effs_vd$magnitude,")")) +
  #         theme_bw() + 
  #         theme(plot.title = element_text(hjust = 0.5),plot.subtitle = element_text(hjust = 0.5)) + 
  #         scale_x_continuous(name = metric_id) + 
  #         scale_y_continuous(name = "Density")
  #       # print(plot)
  #       filename <- paste(logdir,"/rndWalk/EffectSize","_",metric_id,"_",SUL_id,"_",reuse_id,".png",sep="");
  #       ggsave(filename, width = 8, height = 8)
  #       
  #     }
  #   }
  # }
  # 
  # rownames(effsiz_tab) <- NULL
  # 
  # effsiz_tab$VD<-round(effsiz_tab$VD,digits = 4)
  # effsiz_tab$Wilcox<-round(effsiz_tab$Wilcox,digits = 4)
  # 
  # filename <- paste(logdir,"/rndWalk/EffectSize.tab",sep="");
  # write.table(effsiz_tab,filename,sep="\t",row.names=FALSE, quote=FALSE,dec=",")
}

