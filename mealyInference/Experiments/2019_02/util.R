list.of.packages <- c("ggpubr","ggrepel","ggplot2","reshape2","gtools","stringr","scales","effsize","SortableHTMLTables","RColorBrewer","ggpubr","nortest","cowplot","reshape")

new.packages <- list.of.packages[!(list.of.packages %in% installed.packages(lib.loc="/home/cdnd1/Rpackages/")[,"Package"])]
if(length(new.packages)) install.packages(new.packages,lib="/home/cdnd1/Rpackages/")
lapply(list.of.packages,require,character.only=TRUE, lib.loc="/home/cdnd1/Rpackages/")

# new.packages <- list.of.packages[!(list.of.packages %in% installed.packages()[,"Package"])]
# if(length(new.packages)) install.packages(new.packages, dependencies = TRUE)
# lapply(list.of.packages,require,character.only=TRUE)

# devtools::install_github("wilkelab/cowplot")
# devtools::install_github("kassambara/ggpubr")
rm(new.packages,list.of.packages)


## Gives count, mean, standard deviation, standard error of the mean, and confidence interval (default 95%).
##   data: a data frame.
##   measurevar: the name of a column that contains the variable to be summariezed
##   groupvars: a vector containing names of columns that contain grouping variables
##   na.rm: a boolean that indicates whether to ignore NA's
##   conf.interval: the percent range of the confidence interval (default is 95%)
summarySE <- function(data=NULL, measurevar, groupvars=NULL, na.rm=FALSE,
                      conf.interval=.95, .drop=TRUE) {
  library(plyr)
  
  # New version of length which can handle NA's: if na.rm==T, don't count them
  length2 <- function (x, na.rm=FALSE) {
    if (na.rm) sum(!is.na(x))
    else       length(x)
  }
  
  # This does the summary. For each group's data frame, return a vector with
  # N, mean, and sd
  datac <- ddply(data, groupvars, .drop=.drop,
                 .fun = function(xx, col) {
                   c(N    = length2(xx[[col]], na.rm=na.rm),
                     mean = mean   (xx[[col]], na.rm=na.rm),
                     sd   = sd     (xx[[col]], na.rm=na.rm)
                   )
                 },
                 measurevar
  )
  
  # Rename the "mean" column    
  datac <- rename(datac, c("mean" = measurevar))
  
  datac$se <- datac$sd / sqrt(datac$N)  # Calculate standard error of the mean
  
  # Confidence interval multiplier for standard error
  # Calculate t-statistic for confidence interval: 
  # e.g., if conf.interval is .95, use .975 (above/below), and use df=N-1
  ciMult <- qt(conf.interval/2 + .5, datac$N-1)
  datac$ci <- datac$se * ciMult
  
  return(datac)
}

plotCorrectness<-function(logdir,tab,logfname, out_format,the_EqOracles){
  ###########################################################################################################
  # Plots showing percentual of correct inferences
  
  # tab$EqO<-gsub("null","WpMethodHypEQOracle",tab$EqO)
  # anEqO<-"WpMethodHypEQOracle"
  for (anEqO in the_EqOracles) {
    plotdir<-paste("","plots",logfname,anEqO,"boxplots","",sep = "/")
    dir.create(file.path(logdir, plotdir), showWarnings = FALSE,recursive = TRUE)
    
    tab_se <- tab[grepl(paste("^",anEqO,"$",sep = ""),tab$EqO),]
    
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
    
    
    df_ok$Approach<-paste(df_ok$Method,"(",df_ok$Reuse,")",sep = "");df_ok$Approach<-gsub("\\(null\\)$","",df_ok$Approach)
    
    tab_this <- df_ok
    tab_tmp<-data.frame()
    for (id_sul in unique(tab_this$SUL)) {
      for (tmp in unique(tab_this[(tab_this$SUL==id_sul),"Reuse"])) {
        if(grepl("^null",tmp)) next;
        new_rows<-tab_this[((tab_this$Reuse=="null")&(tab_this$SUL==id_sul)),]
        new_rows$Reuse<-gsub("^null",tmp,new_rows$Reuse)
        tab_tmp<-rbind(tab_tmp,new_rows)
      }
    }
    tab_this<-rbind(tab_this,tab_tmp)
    tab_this<-tab_this[!grepl("^null",tab_this$Reuse),]
    df_ok<-tab_this[!(grepl("^L*M",tab_this$Method) & grepl("^L1",tab_this$Method) & grepl("^TTT",tab_this$Method)),]
    df_ok<-rbind(df_ok,unique(tab_this[(grepl("^L*M",tab_this$Method) & grepl("^L1",tab_this$Method) & grepl("^TTT",tab_this$Method)),]))
    
    
    for(id_sul in unique(df_ok$SUL)){
      df_ok$PercentRnd<-round(df_ok$Percent,digits = 2)
      df_tmp<-df_ok[grepl(paste("^",id_sul,"$",sep = ""),df_ok$SUL),]
      p2 <- ggplot(df_tmp, aes(Reuse,Percent))+ 
        geom_bar(stat = "identity", aes(fill = Correct,group=Correct),position = 'dodge')+
        geom_text(aes(label=PercentRnd,group=Correct),size=2,position = position_dodge(width = 1))+
        facet_grid(. ~ Method, scales = "free", space = "free")+
        theme_bw()+
        scale_color_grey()+
        # labs(title = paste("Learning ",id_sul," using ",anEqO,sep = ""), x = "Method", y = "(% correct Hyp.)") +
        labs(title = paste("SUL: ",id_sul," | Equivalence Oracle: ",anEqO,sep = ""), x = "Method", y = "(% correct Hyp.)") +
        theme(
          plot.title = element_text(hjust = 0.5, size=7),
          # legend.position="none",
          legend.title = element_text(hjust = 0.5, size=7),
          legend.text = element_text(hjust = 0.5, size=5),
          legend.box.background = element_rect(),
          axis.text.x = element_text(angle = 35, hjust = 1, size=7),
          axis.title.x=element_blank(),
          axis.title.y = element_text(angle = 90, size=7)
        ) + scale_fill_manual(values = c("OK"="grey50", "NOK"="grey90", "null"="red"),drop = FALSE)
      
      filename <- paste(logdir,plotdir,paste("boxplot",id_sul,sep = "_"),out_format,sep="")
      ggsave(device=ggsave_dev, filename, width = 10, height = 5)
    }
    
    #rm(df_ok,tab_this,tab_ok,df_tmp,p2,tmp,tab_tmp,new_rows,tab_se,variable,plotdir,filename)
  }
}

plotMetrics_face_grid<-function(logdir,tab,logfname, out_format,the_EqOracles,the_measurements){
  ###########################################################################################################
  # Plots showing Metrics using facet_grid
  
  # tab$EqO<-gsub("null","WpMethodHypEQOracle",tab$EqO)
  # anEqO<-"WpMethodHypEQOracle"
  for (anEqO in the_EqOracles) {
    plotdir<-paste("","plots","",logfname,anEqO,"",sep = "/")
    dir.create(file.path(logdir, plotdir), showWarnings = FALSE,recursive = TRUE)
    
    tab_se <- tab[grepl(paste("^",anEqO,"$",sep = ""),tab$EqO),]
    
    for(metric_id in the_measurements){
      # for(metric_id in c("TQ_Resets")){
      tab_this <- tab_se
      tab_tmp<-data.frame()
      for (id_sul in unique(tab_this$SUL)) {
        for (tmp in unique(tab_this[(tab_this$SUL==id_sul),"Reuse"])) {
          if(grepl("^null",tmp)) next;
          new_rows<-tab_this[((tab_this$Reuse=="null")&(tab_this$SUL==id_sul)),]
          new_rows$Reuse<-gsub("^null",tmp,new_rows$Reuse)
          tab_tmp<-rbind(tab_tmp,new_rows)
        }
      }
      tab_this<-rbind(tab_this,tab_tmp)
      tab_this<-tab_this[!grepl("^null",tab_this$Reuse),]
      #rm(tab_tmp,tmp,new_rows)
      
      for(id_sul in unique(tab_this$SUL)){
        tab_l<-tab_this[(grepl(paste("^",id_sul,"$",sep = ""),tab_this$SUL)& grepl("^OK",tab_this$Correct)),]
        title_lab <- paste(metric_id,"@",id_sul)
        # tab_l$Method<-factor(tab_l$Method,levels = c("DL*M_v2", "DL*M_v1", "DL*M_v0", "Adp", "L*M", "L1","TTT"))
        # tab_l$Correct<-factor(tab_l$Correct,levels = c("OK","NOK"))
        if(nrow(tab_l)==0) next
        
        plot <- ggplot(tab_l, aes_string(x="Method", y=metric_id,group=1,fill="Method")) +
          stat_summary(fun.y=sum, geom="line",color="grey80")+
          geom_point(size = 0.5, aes(shape=Method),stat='summary', fun.y=sum) +
          # geom_text(aes_string(label=metric_id), hjust = 1.30, vjust = -0.05, size=1.0)+
          geom_text_repel(aes_string(label=metric_id), size=1.10)+
          facet_grid(. ~ Reuse)+
          theme_bw() +
          scale_color_grey() +
          # labs(title = paste("Learning ",id_sul," using ",anEqO), x = "Method", y = paste(metric_id,sep = "")) +
          labs(title = paste("SUL: ",id_sul," | Equivalence Oracle: ",anEqO,sep = ""), x = "Method", y = metric_id) +
          theme(
            plot.title = element_text(hjust = 0.5, size=5),
            legend.position="none",
            legend.title = element_text(hjust = 0.5, size=5),
            legend.text = element_text(hjust = 0.5, size=5),
            legend.box.background = element_rect(),
            axis.text.x = element_text(angle = 25, hjust = 1, size=5),
            axis.text.y = element_text(angle = 0, hjust = 1, size=5),
            axis.title.x = element_text(hjust = 0.5, size=5),
            axis.title.y = element_text(angle = 90, size=5),
            strip.text        = element_text(hjust = 0.5, size=5),
            # axis.title.x = element_blank(),
            # axis.title.y = element_blank()
          )+ scale_fill_manual(values = c( "DL*M_v2"  = "grey20",
                                           "DL*M_v1"  = "grey30",
                                           "DL*M_v0"  = "grey40",
                                           "Adp" = "grey50",
                                           "L*M"      = "grey60",
                                           "L1"       = "grey70",
                                           "TTT"      = "grey80"
          ))+ expand_limits(y = c(min(tab_l[,metric_id])*1, max(tab_l[,metric_id])*1))
        filename <- paste(logdir,plotdir,paste(metric_id,id_sul,sep = "_"),out_format,sep="")
        if(length(unique(tab_l$Reuse))==2)  ggsave(device=ggsave_dev, filename, width = 04, height = 1.75, dpi=320)  # ssh plots
        if(length(unique(tab_l$Reuse))==4)  ggsave(device=ggsave_dev, filename, width = 07, height = 2.75, dpi=320)  # mqtt plots
        if(length(unique(tab_l$Reuse))==6)  ggsave(device=ggsave_dev, filename, width = 07, height = 1.75, dpi=320)  # OpenSSL_client plots
        if(length(unique(tab_l$Reuse))==12) ggsave(device=ggsave_dev, filename, width = 16, height = 2.50, dpi=320)  # OpenSSL_server plots 
        #rm(plot,filename,title_lab,tmp)
      }
      #rm(tab_this,tab_l)
    }
    #rm(tab_se,plotdir,metric_id)
  }
}


plotMetrics_plot_grid<-function(logdir,tab,logfname, out_format,the_EqOracles,the_measurements){
  ###########################################################################################################
  # Plots showing Metrics using plot_grid for each Reuse
  
  # tab$EqO<-gsub("null","WpMethodHypEQOracle",tab$EqO)
  # anEqO<-"WpMethodHypEQOracle"
  for (anEqO in the_EqOracles) {
    plotdir<-paste("","plots","",logfname,anEqO,"",sep = "/")
    dir.create(file.path(logdir, plotdir), showWarnings = FALSE,recursive = TRUE)
    
    tab_se <- tab[grepl(paste("^",anEqO,"$",sep = ""),tab$EqO),]
    
    for(metric_id in the_measurements){
      # for(metric_id in c("TQ_Resets")){
      tab_this <- tab_se
      tab_tmp<-data.frame()
      for (id_sul in unique(tab_this$SUL)) {
        for (tmp in unique(tab_this[(tab_this$SUL==id_sul),"Reuse"])) {
          if(grepl("^null",tmp)) next;
          new_rows<-tab_this[((tab_this$Reuse=="null")&(tab_this$SUL==id_sul)),]
          new_rows$Reuse<-gsub("^null",tmp,new_rows$Reuse)
          tab_tmp<-rbind(tab_tmp,new_rows)
        }
      }
      tab_this<-rbind(tab_this,tab_tmp)
      tab_this<-tab_this[!grepl("^null",tab_this$Reuse),]
      #rm(tab_tmp,tmp,new_rows)
      
      for(id_sul in unique(tab_this$SUL)){
        tab_l<-tab_this[(grepl(paste("^",id_sul,"$",sep = ""),tab_this$SUL)& grepl("^OK",tab_this$Correct)),]
        title_lab <- paste(metric_id,"@",id_sul)
        # tab_l$Method<-factor(tab_l$Method,levels = c("DL*M_v2", "DL*M_v1", "DL*M_v0", "Adp", "L*M", "L1","TTT"))
        # tab_l$Correct<-factor(tab_l$Correct,levels = c("OK","NOK"))
        if(nrow(tab_l)==0) next
        
        bplots<-list()
        for(id_ruz in unique(tab_l$Reuse)){
          plot <- ggplot(tab_l[tab_l$Reuse==id_ruz,], aes_string(x="Method", y=metric_id,group=1,fill="Method")) +
            stat_summary(fun.y=sum, geom="line",color="grey80")+
            geom_point(size = 0.5, aes(shape=Method),stat='summary', fun.y=sum) +
            # geom_text(aes_string(label=metric_id), hjust = 1.30, vjust = -0.05, size=1.0)+
            geom_text_repel(aes_string(label=metric_id), size=1.10)+
            theme_bw() +
            scale_color_grey() +
            # labs(title = paste("Learning ",id_sul," using ",anEqO), x = "Method", y = paste(metric_id,sep = "")) +
            # labs(title = paste("Reusing ",id_ruz),                    x = "Method", y = paste(metric_id,sep = "")) +
            labs(title = paste("Reuse OT: ",id_ruz),                    x = "Method", y = paste(metric_id,sep = "")) +
            theme(
              plot.title = element_text(hjust = 0.5, size=5),
              legend.position="none",
              legend.title = element_text(hjust = 0.5, size=5),
              legend.text = element_text(hjust = 0.5, size=5),
              legend.box.background = element_rect(),
              axis.text.x = element_text(angle = 25, hjust = 1, size=5),
              axis.text.y = element_text(angle = 0, hjust = 1, size=5),
              # axis.title.x = element_text(hjust = 0.5, size=5),
              # axis.title.y = element_text(angle = 90, size=5),
              strip.text        = element_text(hjust = 0.5, size=5),
              axis.title.x = element_blank(),
              axis.title.y = element_blank(),
            )+ scale_fill_manual(values = c( "DL*M_v2"  = "grey20",
                                             "DL*M_v1"  = "grey30",
                                             "DL*M_v0"  = "grey40",
                                             "Adp" = "grey50",
                                             "L*M"      = "grey60",
                                             "L1"       = "grey70",
                                             "TTT"      = "grey80"
            ))
          # + expand_limits(y = c(min(tab_l[,metric_id])*1, max(tab_l[,metric_id])*1))
          bplots[[id_ruz]]<-plot
        }
        bplots[[1]]<-bplots[[1]]+theme(axis.title.y = element_text(angle = 90, size=5))
        pgrid<-plot_grid(plotlist=bplots,labels = LETTERS[1:length(bplots)], label_size = 5, nrow = 1)
        # pgrid2<-plot_grid(pgrid,
        #                   get_legend(bplots[[1]]+
        #                                theme(legend.position = "bottom",
        #                                      # legend.title=element_text(size=7),
        #                                      # legend.text=element_text(size=7),
        #                                      legend.justification = "center")
        #                   )
        #                   ,nrow = 2,rel_heights = c(10, 1))
        # now add the title
        # title <- ggdraw() + draw_label(paste("Learning ",id_sul," using ",anEqO), fontface='bold', size = 05)
        title <- ggdraw() + draw_label(paste("SUL: ",id_sul," | Equivalence oracle: ",anEqO, sep = ""), fontface='bold', size = 05)
        pgridd<-plot_grid(title, pgrid, ncol=1, rel_heights=c(0.1, 1)) # rel_heights values control title margins
        plotdir2<-paste(plotdir,"plot_grid","",sep = "/")
        dir.create(file.path(logdir, plotdir2), showWarnings = FALSE,recursive = TRUE)
        filename <- paste(logdir,plotdir2,paste(metric_id,id_sul,sep = "_"),out_format,sep="")
        if(length(unique(tab_l$Reuse))==2)  ggsave(device=ggsave_dev, filename, width = 04, height = 1.75, dpi=320)  # ssh plots
        if(length(unique(tab_l$Reuse))==4)  ggsave(device=ggsave_dev, filename, width = 07, height = 1.50, dpi=320)  # mqtt plots
        if(length(unique(tab_l$Reuse))==6)  ggsave(device=ggsave_dev, filename, width = 07, height = 1.75, dpi=320)  # OpenSSL_client plots
        if(length(unique(tab_l$Reuse))==12) ggsave(device=ggsave_dev, filename, width = 16, height = 1.50, dpi=320)  # OpenSSL_server plots 
        #rm(plot,filename,title_lab,tmp,plotdir2)
      }
      #rm(tab_this,tab_l)
    }
    #rm(tab_se,plotdir,metric_id)
  }
}

plotMetrics_allTogether<-function(logdir,tab,logfname, out_format,the_EqOracles,the_measurements){
  ###########################################################################################################
  # Plots showing Metrics using for all Reuse
  
  
  # tab$EqO<-gsub("null","WpMethodHypEQOracle",tab$EqO)
  # anEqO<-"WpMethodHypEQOracle"
  for (anEqO in the_EqOracles) {
    plotdir<-paste("","plots","",logfname,anEqO,"",sep = "/")
    dir.create(file.path(logdir, plotdir), showWarnings = FALSE,recursive = TRUE)
    
    tab_se <- tab[grepl(paste("^",anEqO,"$",sep = ""),tab$EqO),]
    
    tab_this <- tab_se
    tab_tmp<-data.frame()
    for (id_sul in unique(tab_this$SUL)) {
      for (tmp in unique(tab_this[(tab_this$SUL==id_sul),"Reuse"])) {
        if(grepl("^null",tmp)) next;
        new_rows<-tab_this[((tab_this$Reuse=="null")&(tab_this$SUL==id_sul)),]
        new_rows$Reuse<-gsub("^null",tmp,new_rows$Reuse)
        tab_tmp<-rbind(tab_tmp,new_rows)
      }
    }
    tab_this<-rbind(tab_this,tab_tmp)
    tab_this<-tab_this[!grepl("^null",tab_this$Reuse),]
    #rm(tab_tmp,tmp,new_rows)
    
    the_measures<-c("EQ_Resets","MQ_Resets","TQ_Resets")
    
    for(id_sul in unique(tab_this$SUL)){
      tab_l<-tab_this[(grepl(paste("^",id_sul,"$",sep = ""),tab_this$SUL)& grepl("^OK",tab_this$Correct)),]
      tab_melt <- melt(tab_l, id = c("SUL","Method","Reuse"), measure = the_measures)
      bplots<-list()
      for (mezur in the_measures) {
        p2 <- ggplot(tab_melt[tab_melt$variable==mezur,], aes(x=Method,y=value,colour = Reuse,group=Reuse))+ 
          # geom_text_repel(aes(label=value), size=3,segment.colour = "black")+
          geom_label_repel(aes(label=value), size=3)+
          geom_point(size = 0.5, aes(shape=Reuse))+ 
          geom_line()+
          theme(legend.position="none")+
          # labs(title = paste("Learning ",id_sul," using ",anEqO), x = "Method", y = mezur)
          labs(x = "Method", y = mezur)
        bplots[[mezur]]<-p2
      }
      pgrid<-plot_grid(plotlist=bplots,nrow = 1)
      pgrid2<-plot_grid(pgrid,
                        get_legend(bplots[[1]]+
                                     theme(legend.position = "bottom",
                                           # legend.title=element_text(size=7),
                                           # legend.text=element_text(size=7),
                                           legend.justification = "center")
                        )
                        ,nrow = 2,rel_heights = c(10, 1))
      filename <- paste(logdir,plotdir,paste("Queries",id_sul,sep = "_"),out_format,sep="")
      # ggsave(device=ggsave_dev, filename, width = 04, height = 1.75, dpi=320)  # ssh plots
      # ggsave(device=ggsave_dev, filename, width = 12, height = 2.5, dpi=320)  # ssh plots
      ggsave(                  filename, width = 12, height = 2.5, dpi=320)  # ssh plots
      #rm(tab_l,tab_melt,bplots,p2,pgrid,pgrid2)
    }
  }
  
}

prepareTab<-function(logdir,logfname,tab){
  tab_filename<-paste(logdir,logfname,".tab",sep="")
  tab <- read.table(tab_filename, sep="|", header=TRUE)
  
  names(tab) <- c("SUL","Seed","Cache","CloS","CExH","EqO","Method","Reuse","Reuse_Resets","Reuse_Symbols","Rounds","MQ_Resets","MQ_Symbols","EQ_Resets","EQ_Symbols","L_ms","SCEx","Q_Size","I_Size","Correct","Info","ReusedPref","ReusedSuf" )
  tab$Info<-gsub("^N/A$","null",tab$Info)
  
  tab$L_ms    <- as.numeric(tab$L_ms)
  tab$Rounds  <- as.numeric(tab$Rounds)
  tab$SCEx    <- as.numeric(tab$SCEx)
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
  
  tab$Method<-gsub("^Adaptive","Adp",tab$Method)
  tab$Method<-factor(tab$Method,levels = c("DL*M_v2", "DL*M_v1", "DL*M_v0", "Adp", "L*M", "L1","TTT"))
  tab$Correct<-factor(tab$Correct,levels = c("OK","NOK"))
  
  tab$SUL  <-gsub("^SUL_","",gsub('\\.[a-z]+$',"",gsub("^client_","cli_",gsub('^server_',"srv_",tab$SUL))))
  tab$Reuse<-gsub("^SUL_","",gsub('\\.[a-z]+$',"",gsub("^client_","cli_",gsub('^server_',"srv_",tab$Reuse))))
  
  return(tab)
}


plotMetrics_specificGroups<-function(logdir,tab,logfname, out_format,the_EqOracles,sul_ot,the_measurements){
  ###########################################################################################################
  # Plots showing Metrics for specific groups of SUL+Reuse OTs
  
  # tab$EqO<-gsub("null","WpMethodHypEQOracle",tab$EqO)
  # anEqO<-"WpMethodHypEQOracle"
  for (anEqO in the_EqOracles) {
    plotdir<-paste("","plots","",logfname,anEqO,"",sep = "/")
    dir.create(file.path(logdir, plotdir), showWarnings = FALSE,recursive = TRUE)
    
    tab_se <- tab[grepl(paste("^",anEqO,sep = ""),tab$EqO),]
    
    for(metric_id in the_measurements){
      # for(metric_id in c("TQ_Resets")){
      # metric_id<-("TQ_Resets")
      tab_this <- tab_se
      tab_tmp<-data.frame()
      for (id_sul in unique(tab_this$SUL)) {
        for (tmp in unique(tab_this[(tab_this$SUL==id_sul),"Reuse"])) {
          if(grepl("^null",tmp)) next;
          new_rows<-tab_this[((tab_this$Reuse=="null")&(tab_this$SUL==id_sul)),]
          new_rows$Reuse<-gsub("^null",tmp,new_rows$Reuse)
          tab_tmp<-rbind(tab_tmp,new_rows)
        }
      }
      tab_this<-rbind(tab_this,tab_tmp)
      tab_this<-tab_this[!grepl("^null",tab_this$Reuse),]
      #rm(tab_tmp,tmp,new_rows)
      
      for(id_sul in unique(sul_ot$SUL)){
        tab_l<-tab_this[(grepl(paste("^",id_sul,"$",sep = ""),tab_this$SUL)& grepl("^OK",tab_this$Correct)),]
        title_lab <- paste(metric_id,"@",id_sul)
        # tab_l$Method<-factor(tab_l$Method,levels = c("DL*M_v2", "DL*M_v1", "DL*M_v0", "Adp", "L*M", "L1","TTT"))
        # tab_l$Correct<-factor(tab_l$Correct,levels = c("OK","NOK"))
        if(nrow(tab_l)==0) next
        
        bplots<-list()
        for(id_ruz in unique(sul_ot[grepl(paste("^",id_sul,"$",sep = ""),sul_ot$SUL),"Reuse"])){
          plot <- ggplot(tab_l[tab_l$Reuse==id_ruz,], aes_string(x="Method", y=metric_id,group=1,fill="Method")) +
            stat_summary(fun.y=sum, geom="line",color="grey80")+
            geom_point(size = 0.5, aes(shape=Method),stat='summary', fun.y=sum) +
            # geom_text(aes_string(label=metric_id), hjust = 1.30, vjust = -0.05, size=1.0)+
            geom_text_repel(aes_string(label=metric_id), size=1.10)+
            theme_bw() +
            scale_color_grey() +
            # labs(title = paste("Learning ",id_sul," using ",anEqO), x = "Method", y = paste(metric_id,sep = "")) +
            # labs(title = paste("Reusing ",id_ruz),                    x = "Method", y = paste(metric_id,sep = "")) +
            labs(title = paste("Reuse OT: ",id_ruz),                    x = "Method", y = paste(metric_id,sep = "")) +
            theme(
              plot.title = element_text(hjust = 0.5, size=5),
              legend.position="none",
              legend.title = element_text(hjust = 0.5, size=5),
              legend.text = element_text(hjust = 0.5, size=5),
              legend.box.background = element_rect(),
              axis.text.x = element_text(angle = 25, hjust = 1, size=5),
              axis.text.y = element_text(angle = 0, hjust = 1, size=5),
              # axis.title.x = element_text(hjust = 0.5, size=5),
              # axis.title.y = element_text(angle = 90, size=5),
              strip.text        = element_text(hjust = 0.5, size=5),
              axis.title.x = element_blank(),
              axis.title.y = element_blank(),
            )+ scale_fill_manual(values = c( "DL*M_v2"  = "grey20",
                                             "DL*M_v1"  = "grey30",
                                             "DL*M_v0"  = "grey40",
                                             "Adp" = "grey50",
                                             "L*M"      = "grey60",
                                             "L1"       = "grey70",
                                             "TTT"      = "grey80"
            ))
          # + expand_limits(y = c(min(tab_l[,metric_id])*1, max(tab_l[,metric_id])*1))
          bplots[[id_ruz]]<-plot
        }
        bplots[[1]]<-bplots[[1]]+theme(axis.title.y = element_text(angle = 90, size=5))
        pgrid<-plot_grid(plotlist=bplots,labels = LETTERS[1:length(bplots)], label_size = 5, nrow = 1)
        title <- ggdraw() + draw_label(paste("SUL: ",id_sul," | Equivalence oracle: ",anEqO, sep = ""), fontface='bold', size = 05)
        pgridd<-plot_grid(title, pgrid, ncol=1, rel_heights=c(0.1, 1)) # rel_heights values control title margins
        plotdir2<-paste(plotdir,"specificGroups","",sep = "/")
        dir.create(file.path(logdir, plotdir2), showWarnings = FALSE,recursive = TRUE)
        filename <- paste(logdir,plotdir2,paste(metric_id,id_sul,sep = "_"),out_format,sep="")
        if(length(bplots)==2)  ggsave(device=ggsave_dev, filename, width = 04, height = 1.75, dpi=320)  # ssh plots
        if(length(bplots)==4)  ggsave(device=ggsave_dev, filename, width = 07, height = 1.50, dpi=320)  # mqtt plots
        if(length(bplots)==6)  ggsave(device=ggsave_dev, filename, width = 07, height = 1.75, dpi=320)  # OpenSSL_client plots
        if(length(bplots)==12) ggsave(device=ggsave_dev, filename, width = 16, height = 1.50, dpi=320)  # OpenSSL_server plots 
        #rm(plot,filename,title_lab,tmp,plotdir2)
      }
      #rm(tab_this,tab_l)
    }
    #rm(tab_se,plotdir,metric_id)
  }
}


plotMetrics_specificAsBars<-function(logdir,tab,logfname, out_format,the_EqOracles,sul_ot,the_measurements){
  ###########################################################################################################
  # Plots showing Metrics for specific groups of SUL+Reuse OTs
  
  # anEqO<-"WpMethodHypEQOracle"
  for (anEqO in the_EqOracles) {
    plotdir<-paste("","plots","",logfname,anEqO,"",sep = "/")
    dir.create(file.path(logdir, plotdir), showWarnings = FALSE,recursive = TRUE)
    
    tab_se <- tab[grepl(paste("^",anEqO,sep = ""),tab$EqO),]
    tab_this <- tab_se
    
    tab_melt <- melt(tab_this, id = c("SUL","Method","Reuse"), measure = the_measurements)
    names(tab_melt)<-c("SUL","Method","Reuse","Type","Number")
    tab_melt$Type<-gsub("_Resets$","s",tab_melt$Type)
    tab_melt$Type<-factor(tab_melt$Type,levels = c("MQs","EQs","TQs"))
    tab_melt<-tab_melt[tab_melt$Type!="TQs",]
    
    plotdir2<-paste(plotdir,"specificAsBars","",sep = "/")
    dir.create(file.path(logdir, plotdir2), showWarnings = FALSE,recursive = TRUE)
    
    for(id_sul in unique(sul_ot$SUL)){
      tab_l<-tab_melt[tab_melt$SUL==id_sul,]
      tab_tmp<-data.frame()
      for (tmp in unique(sul_ot[(sul_ot$SUL==id_sul),"Reuse"])) {
        tab_tmpp<-tab_l[((tab_l$Method%in%c("L*M","L1","TTT"))&(tab_l$SUL==id_sul)),]
        tab_tmpp$Reuse<-tmp
        tab_tmp<-rbind(tab_tmp,tab_tmpp)
        rm(tab_tmpp)
      }
      tab_l<-tab_l[!(tab_l$Reuse=="null"),]
      tab_l<-rbind(tab_tmp,tab_l);rm(tab_tmp)
      tab_l<-tab_l[tab_l$Reuse %in%sul_ot[(sul_ot$SUL==id_sul),"Reuse"],]
      if(nrow(tab_l)==0) next
      the_labels<-gsub("^0$","",as.character(tab_l$Number))
      plot <- ggplot(tab_l, aes_string(x="Method", y="Number",group="Method",fill="Type")) +
        geom_bar(stat="identity", position = "stack")+
        # geom_text_repel(aes_string(label="Number"), size=1.10, vjust =-0.250)+
        geom_text(        aes(label=the_labels), position  = "stack", vjust=-0.10, size=1.0)+
        theme_light() +
        facet_grid( ~ Reuse)+
        scale_color_grey() +
        labs(title = paste("SUL ",id_sul))+
        # # labs(title = paste("Reuse OT: ",id_ruz),                    x = "Method", y = paste(metric_id,sep = "")) +
        theme( 
          plot.title         = element_text(hjust = 0.5, size=5),
          # legend.position    = "top", 
          # legend.box         = "horizontal",
          # legend.position    = c(0.5, .0),
          legend.key.size    = unit(2, "mm"),
          legend.title       = element_text(hjust = 0.5, size=5),
          legend.text        = element_text(hjust = 0.5, size=5),
          legend.box.spacing = unit(-0.5, "mm"),
          legend.background  = element_blank(),
          axis.text.x  = element_text(angle = 25, hjust = 1, size=3),
          axis.text.y  = element_text(angle = 0, hjust = 1, size=5),
          axis.title.x = element_text(hjust = 0.5, size=5),
          axis.title.y = element_text(angle = 90, size=5),
          strip.text   = element_text(hjust = 0.5, size=5)
        )+ scale_fill_manual(name="Type",
                             values = c( "EQs"  = "grey50",
                                         "MQs"  = "grey80")
        )
      
      filename <- paste(logdir,plotdir2,paste(id_sul,sep = "_"),out_format,sep="")
      the_length<-length((unique(tab_l$Reuse))) 
      if(the_length==2) ggsave(device=ggsave_dev, filename, width = 2.75, height = 1.75, dpi=320)  # ssh plots
      if(the_length==4) ggsave(device=ggsave_dev, filename, width = 3.5, height = 1.75, dpi=320)  # ssh plots
    }
    
  }
}


plotMetrics_specificFirstPrev<-function(logdir,tab,logfname, out_format,the_EqOracles,pairs){
  ###########################################################################################################
  # Plots showing Metrics for specific groups of SUL+Reuse OTs
  
  # anEqO<-"WpMethodHypEQOracle"
  for (anEqO in the_EqOracles) {
    plotdir<-paste("","plots","",logfname,anEqO,"",sep = "/")
    dir.create(file.path(logdir, plotdir), showWarnings = FALSE,recursive = TRUE)
    
    tab_sot<-tab[((tab$SUL %in% pairs$SUL) & tab$Reuse=="null"),]
    tab_sot<-rbind(tab_sot,tab[paste(tab$SUL,tab$Reuse) %in% paste(pairs$SUL,pairs$Reuse),])
    
    tab_sot <- tab_sot[grepl(paste("^",anEqO,sep = ""),tab_sot$EqO),]
    tab_this <- tab_sot
    
    tab_melt <- melt(tab_this, id = c("SUL","Method","Reuse"), measure = c("EQ_Resets","MQ_Resets","TQ_Resets"))
    names(tab_melt)<-c("SUL","Method","Reuse","Type","Number")
    tab_melt$Type<-gsub("_Resets$","s",tab_melt$Type)
    tab_melt$Type<-factor(tab_melt$Type,levels = c("MQs","EQs","TQs"))
    tab_melt<-tab_melt[tab_melt$Type!="TQs",]
    
    plotdir2<-paste(plotdir,"specificAsBars","",sep = "/")
    dir.create(file.path(logdir, plotdir2), showWarnings = FALSE,recursive = TRUE)
    
    v0<-names(which.max(table(tab_melt$Reuse)))
    tab_melt[((!tab_melt$Reuse=="null")&(!tab_melt$Reuse==v0)),"Reuse"]<-"Prev"
    tab_melt[((!tab_melt$Reuse=="null")&(tab_melt$Reuse==v0)),"Reuse"]<-"First"
    
    tradf<-tab_melt[((tab_melt$Reuse=="null")),]
    tradf$Reuse<-"First"
    
    tradp<-tab_melt[((tab_melt$Reuse=="null")),]
    tradp$Reuse<-"Prev"
    tab_melt<-rbind(tab_melt,tradf,tradp)
    
    tab_melt<-tab_melt[((!tab_melt$Reuse=="null")),]
    
    the_labels<-gsub("^0$","",as.character(tab_melt$Number))
    plot <- ggplot(tab_melt, aes_string(x="Method", y="Number",fill="Type")) +
      geom_bar(stat="identity", position = "stack")+
      geom_text(        aes(label=the_labels), position  = "stack", vjust=0.10, size=3)+
      facet_grid(Reuse ~ SUL, scales="free")+
      theme_light() +
      # labs(title = paste(toupper(logfname)),                    x = "Learning Algorithm", y = "Number of Queries") +
      labs(x = "Learning Algorithm", y = "Number of Queries") +
      theme( 
        plot.title         = element_text(hjust = 0.5, size=10),
        axis.text.x  = element_text(angle = 25, hjust = 1, size=5)
      )+
      scale_color_grey()+ scale_fill_manual(name="Type",
                                            values = c( "EQs"  = "grey50",
                                                        "MQs"  = "grey80"))
    
    
    filename <- paste(logdir,plotdir2,paste(logfname,"firstprev",sep = "_"),out_format,sep="")
    # the_length<-length((unique(tab_l$Reuse))) 
    ggsave(device=ggsave_dev, filename, width = 18, height = 5.5, dpi=320)  # ssh plots
  }
}

mk_sul_ot_cli<-function(){
  sul_ot <- data.frame(matrix(ncol = 2, nrow = 0))
  sul_ot<-rbind(sul_ot,data.frame(SUL="cli_098m"  	, Reuse="cli_098j"  	))
  sul_ot<-rbind(sul_ot,data.frame(SUL="cli_098m"  	, Reuse="cli_098l"  	))
  sul_ot<-rbind(sul_ot,data.frame(SUL="cli_101"  		, Reuse="cli_098j"  	))
  sul_ot<-rbind(sul_ot,data.frame(SUL="cli_101"  		, Reuse="cli_098m"  	))
  sul_ot<-rbind(sul_ot,data.frame(SUL="cli_098za"  	, Reuse="cli_098j"  	))
  sul_ot<-rbind(sul_ot,data.frame(SUL="cli_098za"  	, Reuse="cli_101"  	))
  sul_ot<-rbind(sul_ot,data.frame(SUL="cli_100m"  	, Reuse="cli_098j"  	))
  sul_ot<-rbind(sul_ot,data.frame(SUL="cli_100m"  	, Reuse="cli_098za"  	))
  sul_ot<-rbind(sul_ot,data.frame(SUL="cli_101h"  	, Reuse="cli_098j"  	))
  sul_ot<-rbind(sul_ot,data.frame(SUL="cli_101h"  	, Reuse="cli_100m"  	))
  sul_ot<-rbind(sul_ot,data.frame(SUL="cli_102"  		, Reuse="cli_098j"  	))
  sul_ot<-rbind(sul_ot,data.frame(SUL="cli_102"  		, Reuse="cli_101h"  	))
  sul_ot<-rbind(sul_ot,data.frame(SUL="cli_110-pre1" 	, Reuse="cli_098j"  	))
  sul_ot<-rbind(sul_ot,data.frame(SUL="cli_110-pre1" 	, Reuse="cli_102"  	))
  return(sul_ot)
}

mk_sul_ot_srv<-function(){
  sul_ot <- data.frame(matrix(ncol = 2, nrow = 0))
  sul_ot<-rbind(sul_ot,data.frame(SUL="srv_097e"  	, Reuse="srv_097"  	))
  sul_ot<-rbind(sul_ot,data.frame(SUL="srv_097e"  	, Reuse="srv_097c"  	))
  sul_ot<-rbind(sul_ot,data.frame(SUL="srv_098l"  	, Reuse="srv_097"  	))
  sul_ot<-rbind(sul_ot,data.frame(SUL="srv_098l"  	, Reuse="srv_097e"  	))
  sul_ot<-rbind(sul_ot,data.frame(SUL="srv_098m"  	, Reuse="srv_097"  	))
  sul_ot<-rbind(sul_ot,data.frame(SUL="srv_098m"  	, Reuse="srv_098l"  	))
  sul_ot<-rbind(sul_ot,data.frame(SUL="srv_100"  		, Reuse="srv_097"  	))
  sul_ot<-rbind(sul_ot,data.frame(SUL="srv_100"  		, Reuse="srv_098m"  	))
  sul_ot<-rbind(sul_ot,data.frame(SUL="srv_098s"  	, Reuse="srv_097"  	))
  sul_ot<-rbind(sul_ot,data.frame(SUL="srv_098s"  	, Reuse="srv_100"  	))
  sul_ot<-rbind(sul_ot,data.frame(SUL="srv_098u"  	, Reuse="srv_097"  	))
  sul_ot<-rbind(sul_ot,data.frame(SUL="srv_098u"  	, Reuse="srv_098s"  	))
  sul_ot<-rbind(sul_ot,data.frame(SUL="srv_101"  		, Reuse="srv_097"  	))
  sul_ot<-rbind(sul_ot,data.frame(SUL="srv_101"  		, Reuse="srv_098u"  	))
  sul_ot<-rbind(sul_ot,data.frame(SUL="srv_098za"  	, Reuse="srv_097"  	))
  sul_ot<-rbind(sul_ot,data.frame(SUL="srv_098za"  	, Reuse="srv_101"  	))
  sul_ot<-rbind(sul_ot,data.frame(SUL="srv_101k"  	, Reuse="srv_097"  	))
  sul_ot<-rbind(sul_ot,data.frame(SUL="srv_101k"  	, Reuse="srv_098za"  	))
  sul_ot<-rbind(sul_ot,data.frame(SUL="srv_102"  		, Reuse="srv_097"  	))
  sul_ot<-rbind(sul_ot,data.frame(SUL="srv_102"  		, Reuse="srv_101k"  	))
  sul_ot<-rbind(sul_ot,data.frame(SUL="srv_110pre1" 	, Reuse="srv_097"  	))
  sul_ot<-rbind(sul_ot,data.frame(SUL="srv_110pre1" 	, Reuse="srv_102"  	))
  return(sul_ot)
}

mk_sul_ot_ssh<-function(){
  sul_ot <- data.frame(matrix(ncol = 2, nrow = 0))
  sul_ot<-rbind(sul_ot,data.frame(SUL="OpenSSH"  	, Reuse="DropBear"  	))
  sul_ot<-rbind(sul_ot,data.frame(SUL="OpenSSH"  	, Reuse="BitVise"  	))
  sul_ot<-rbind(sul_ot,data.frame(SUL="DropBear"  	, Reuse="OpenSSH"  	))
  sul_ot<-rbind(sul_ot,data.frame(SUL="DropBear"  	, Reuse="BitVise"  	))
  sul_ot<-rbind(sul_ot,data.frame(SUL="BitVise"  	, Reuse="DropBear"  	))
  sul_ot<-rbind(sul_ot,data.frame(SUL="BitVise"  	, Reuse="OpenSSH"  	))
  return(sul_ot)
}


mk_sul_ot_mqtt<-function(){
  sul_ot <- data.frame(matrix(ncol = 2, nrow = 0))
  sul_ot<-rbind(sul_ot,data.frame(SUL="ActiveMQ"  	, Reuse="emqtt"  	))
  sul_ot<-rbind(sul_ot,data.frame(SUL="ActiveMQ"  	, Reuse="hbmqtt"  	))
  sul_ot<-rbind(sul_ot,data.frame(SUL="ActiveMQ"  	, Reuse="mosquitto"  	))
  sul_ot<-rbind(sul_ot,data.frame(SUL="ActiveMQ"  	, Reuse="VerneMQ"  	))
  
  sul_ot<-rbind(sul_ot,data.frame(SUL="emqtt"  	, Reuse="ActiveMQ"  	))
  sul_ot<-rbind(sul_ot,data.frame(SUL="emqtt"  	, Reuse="hbmqtt"  	))
  sul_ot<-rbind(sul_ot,data.frame(SUL="emqtt"  	, Reuse="mosquitto"  	))
  sul_ot<-rbind(sul_ot,data.frame(SUL="emqtt"  	, Reuse="VerneMQ"  	))
  
  sul_ot<-rbind(sul_ot,data.frame(SUL="hbmqtt"  	, Reuse="ActiveMQ"  	))
  sul_ot<-rbind(sul_ot,data.frame(SUL="hbmqtt"  	, Reuse="emqtt"  	))
  sul_ot<-rbind(sul_ot,data.frame(SUL="hbmqtt"  	, Reuse="mosquitto"  	))
  sul_ot<-rbind(sul_ot,data.frame(SUL="hbmqtt"  	, Reuse="VerneMQ"  	))
  
  sul_ot<-rbind(sul_ot,data.frame(SUL="mosquitto"  	, Reuse="ActiveMQ"  	))
  sul_ot<-rbind(sul_ot,data.frame(SUL="mosquitto"  	, Reuse="emqtt"  	))
  sul_ot<-rbind(sul_ot,data.frame(SUL="mosquitto"  	, Reuse="hbmqtt"  	))
  sul_ot<-rbind(sul_ot,data.frame(SUL="mosquitto"  	, Reuse="VerneMQ"  	))
  
  sul_ot<-rbind(sul_ot,data.frame(SUL="VerneMQ"  	, Reuse="ActiveMQ"  	))
  sul_ot<-rbind(sul_ot,data.frame(SUL="VerneMQ"  	, Reuse="emqtt"  	))
  sul_ot<-rbind(sul_ot,data.frame(SUL="VerneMQ"  	, Reuse="hbmqtt"  	))
  sul_ot<-rbind(sul_ot,data.frame(SUL="VerneMQ"  	, Reuse="mosquitto"  	))
  
  return(sul_ot)
}

saveTabReusedPrefSuff<-function(logdir,tab,logfname,the_EqOracles){
  for (the_eqo in the_EqOracles) {
    reusedPrefSuf<-tab[,c("SUL","Reuse","EqO","Method","ReusedPref","ReusedSuf","MQ_Resets","EQ_Resets")]
    reusedPrefSuf<-reusedPrefSuf[!(reusedPrefSuf$ReusedPref=="null"),]
    reusedPrefSuf<-transform(reusedPrefSuf, Pref = colsplit(ReusedPref, split = "/", names = c('End','Ini')))
    reusedPrefSuf<-transform(reusedPrefSuf, Suff = colsplit(ReusedSuf, split = "/", names = c('End','Ini')))
    names(reusedPrefSuf)<-c("SUL","Reuse","Method","EqO","ReusedPref","ReusedSuf","MQs","EQs","PrefEnd","PrefIni","SuffEnd","SuffIni")
    reusedPrefSuf<-reusedPrefSuf[,c("SUL","Reuse","Method","EqO","MQs","EQs","PrefIni","SuffIni","PrefEnd","SuffEnd")]
    
    out_file<-paste(logdir,"/","plots","/",logfname,"/reusedPrefSuf_",the_eqo,"_",logfname,".csv",sep = "")
    write.csv(reusedPrefSuf, file = out_file)
    
    out_file<-paste(logdir,"/","plots","/",logfname,"/reusedPrefSuf_",the_eqo,"_",logfname,".tab",sep = "")
    write.table(reusedPrefSuf, file = out_file, sep = "\t",row.names = FALSE, col.names = TRUE)
  }
  
}

saveTab<-function(logdir,tab,logfname,pairs = NULL){
  tab_cpy<-transform(tab    , Pref = colsplit(ReusedPref, split = "/", names = c('End','Ini')))
  tab_cpy<-transform(tab_cpy, Suff = colsplit(ReusedSuf, split = "/", names = c('End','Ini')))
  
  the_measurements<-c("EqO","SUL","Method","Reuse","EQ_Resets","MQ_Resets","TQ_Resets","Rounds","Pref.Ini","Suff.Ini","Pref.End","Suff.End")
  tab_cpy<-tab_cpy[,the_measurements]
  
  names(tab_cpy)<-c( "EqO","SUL","Method","Reused","EQs"      ,"MQs"      ,"TQs"      ,"Rounds","PrefIni" ,"SuffIni" ,"PrefEnd" ,"SuffEnd")
  out_file<-paste(logdir,"/","plots","/",logfname,"/tabPaper_",logfname,".tab",sep = "")
  write.table(tab_cpy, file = out_file, sep = "\t",row.names = FALSE, col.names = TRUE)
  
  out_file<-paste(logdir,"/","plots","/",logfname,"/tabComplete_",logfname,".tab",sep = "")
  write.table(tab, file = out_file, sep = "\t",row.names = FALSE, col.names = TRUE)
  
  if(!is.null(pairs)){
    tab_sot<-tab[((tab$SUL %in% pairs$SUL) & tab$Reuse=="null"),]
    tab_sot<-rbind(tab_sot,tab[paste(tab$SUL,tab$Reuse) %in% paste(pairs$SUL,pairs$Reuse),])
    
    out_file<-paste(logdir,"/","plots","/",logfname,"/tab_sot_",logfname,".tab",sep = "")
    write.table(tab_sot, file = out_file, sep = "\t",row.names = FALSE, col.names = TRUE)
    
    tab_sot<-tab_cpy[((tab_cpy$SUL %in% pairs$SUL) & tab_cpy$Reuse=="null"),]
    tab_sot<-rbind(tab_sot,tab_cpy[paste(tab_cpy$SUL,tab_cpy$Reuse) %in% paste(pairs$SUL,pairs$Reuse),])
    
    out_file<-paste(logdir,"/","plots","/",logfname,"/tab_sot_Paper_",logfname,".tab",sep = "")
    write.table(tab_sot, file = out_file, sep = "\t",row.names = FALSE, col.names = TRUE)
  }
  
}