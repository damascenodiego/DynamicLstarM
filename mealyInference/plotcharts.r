list.of.packages <- c("ggplot2","reshape2","gtools","stringr","scales","effsize","SortableHTMLTables","RColorBrewer","ggpubr","nortest","cowplot","reshape")

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

# args = commandArgs(trailingOnly=TRUE)

logdir<-"/home/cdnd1/euler_remote/"
logs <- c("mqtt")

tab<-data.frame()
for (logfname in logs) {
  tab_filename<-paste(logdir,logfname,".tab",sep="")
  tab <- rbind(tab,read.table(tab_filename, sep="|", header=TRUE))
}

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


tab$SUL <- gsub('\\.[a-z]+$', '', gsub('\\.[a-z]+$', '', tab$SUL))
tab$Reuse <- gsub('\\.[a-z]+$', '', gsub('\\.[a-z]+$', '', tab$Reuse))
tab$EqO <- gsub('\\([^\\(]+\\)$', '', tab$EqO)

dir.create(file.path(logdir, "plots"), showWarnings = FALSE)
tab_se <- tab[grepl("OK",tab$Correct),]

# tab_se <- tab[grep("^RandomWMethodQsizeEQOracle",tab$EqO),]
# 
# tab_ok <- tab
# tab_ok$CorrectType <- paste(tab_ok$SUL,tab_ok$Method,tab_ok$Correct,sep = "|")
# tab_ok <- rle(sort(tab_ok$CorrectType))
# 
# df_ok <- data.frame(Correct=tab_ok$values, Total=tab_ok$lengths)
# df_ok$Percent <-0
# df_ok<-transform(df_ok, FOO = colsplit(Correct, split = "\\|", names = c('SUL','Method', 'Correct')))
# names(df_ok)<-c("SMC","Total","Percent","SUL","Method","Correct")
# df_ok$SMC <- paste(df_ok$SUL,df_ok$Method,sep = "|")
# df_ok<-df_ok[,c(4,5,6,2,3,1)]
# 
# for (variable in unique(df_ok$SMC)) {
#   print(df_ok[((df_ok$SMC==variable)&(df_ok$Correct=="OK")),"Percent"])
# }

tab_se<-tab_se[(grepl("^RandomWalkEQOracle",tab$EqO)),]
# tab_se<-tab[!(grepl("TTT",tab$Method)| grepl("L1",tab$Method)),]
tab_se<-tab_se[!(grepl("L1",tab_se$Method)),]
tab_se$SUL<-gsub("^SUL_","",tab_se$SUL)
tab_se$Reuse<-gsub("^SUL_","",tab_se$Reuse)
for(metric_id in c("MQ_Resets","TQ_Resets","EQ_Resets")){
#for(metric_id in c("L_ms","Rounds","MQ_Resets","EQ_Resets")){
  # tab_this <- summarySE(tab_se, measurevar=metric_id, groupvars=c("Method","SUL","Reuse"))
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
# }
# {
  
  for(id_sul in unique(tab_this$SUL)){
    tab_l<-tab_this[grepl(id_sul,tab_this$SUL),]
    title_lab <- paste(metric_id,"@",id_sul)
    # ymin_v=tab_l[,4]-tab_l[,6]; ymin_v[ymin_v<0]<-0; ymax_v=tab_l[,4]+tab_l[,6]; ymax_v[ymin_v<0]<-0
    plot <- ggplot(tab_l, aes_string(x="Method", y=metric_id,group="Method",fill="Method")) +
      geom_boxplot()+
      # coord_flip() +
      # geom_point(aes(shape=Method, color=Method))+
      facet_grid(. ~ Reuse)+
      theme_bw() +
      scale_color_grey() + 
      theme(
        plot.title = element_text(hjust = 0.5),
        # legend.position="none",
        legend.box.background = element_rect(),
        axis.text.x = element_text(angle = 35, hjust = 1)
      )
    # +coord_cartesian(ylim = c(0, max(ymax_v))) 
    # labs(title = title_lab, x = "SUL | Reuse")
    filename <- paste(logdir,"/plots/",paste(metric_id,id_sul,sep = "_"),".png",sep="")
    ggsave(filename, width = 20, height = 3)
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