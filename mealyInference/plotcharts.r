library(ggplot2)
library(reshape2)
library(gtools)
library(stringr)
library(scales)
library(effsize)

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

args = commandArgs(trailingOnly=TRUE)

# logdir<-"log_experiments_random20180319_235151_260397897"
logdir<-args
tab_filename<-paste(logdir,"/log4j/log.tab",sep="")

tab <- read.table(tab_filename, sep="|", header=TRUE)

tab$L_ms    <- as.numeric(tab$L_ms)
tab$Rounds  <- as.numeric(tab$Rounds)
tab$SCEx_ms <- as.numeric(tab$CExH)
tab$MQ_Resets  <- as.numeric(tab$MQ_Resets)
tab$MQ_Symbols <- as.numeric(tab$MQ_Symbols)
tab$EQ_Resets  <- as.numeric(tab$EQ_Resets)
tab$EQ_Symbols <- as.numeric(tab$EQ_Symbols)
tab$Correct    <- as.character(tab$Correct)

tab$SUL <- gsub('^fsm_', '', gsub('.txt$', '', tab$SUL))
tab$Reuse <- gsub('^fsm_', '', gsub('.txt.ot$', '', tab$Reuse))

id_sul   <- unique(tab$SUL)
id_reuse <- unique(tab$Reuse)
id_clos <- unique(tab$CloS)
id_cexh <- unique(tab$CExH)
id_eqo <- unique(tab$EqO)


dir.create(file.path(logdir, "rndWalk"), showWarnings = FALSE)

tab_se <- tab[grep("^RandomWalkEQOracle",tab$EqO),]

# tab_ok <- rle(sort(tab_se$Correct))
tab_ok <- tab[grep("^RandomWalkEQOracle",tab$EqO),]
tab_ok$CorrectType <- paste(gsub("^[0-9]+","Dynamic L*M",gsub('^N/A',"L*M",tab_ok$Reuse)),tab_ok$Correct)
tab_ok <- rle(sort(tab_ok$CorrectType))


df_ok <- data.frame(Correct=tab_ok$values, Total=tab_ok$lengths)
df_ok$Method<-"L*M"
df_ok[grep("^Dynamic L\\*M",df_ok$Correct),]$Method<-"Dynamic L*M"
df_ok$Correct <- gsub("^(Dynamic )?L\\*M ","",df_ok$Correct)
df_ok$Percent <-0
df_ok[df_ok$Method=="Dynamic L*M",]$Percent<-df_ok[df_ok$Method=="Dynamic L*M",]$Total/sum(df_ok[df_ok$Method=="Dynamic L*M",]$Total)
df_ok[df_ok$Method=="L*M",]$Percent<-df_ok[df_ok$Method=="L*M",]$Total/sum(df_ok[df_ok$Method=="L*M",]$Total)
df_ok$Percent <- 100*df_ok$Percent
p <- ggplot(df_ok, aes(x=Method, y=Percent,fill=Correct) ) + 
  geom_bar(stat="identity", position=position_dodge()) + 
  scale_fill_manual(values = c("OK" = "dark green", "NOK" = "red")) +
  scale_y_continuous(limits=c(0,100)) +
  labs(title = "Correct hypotheses", x = "Method", y = "Correct hypothese (in %)") +
  theme(plot.title = element_text(hjust = 0.5),plot.subtitle = element_text(hjust = 0.5)) + 
  geom_text(aes(label=paste(df_ok$Total," (",round(df_ok$Percent,digits = 3),"%)",sep="")), position=position_dodge(width=0.9), vjust=-0.25)
filename <- paste(logdir,"/rndWalk/correct.png",sep = "")
ggsave(filename, width = 8, height = 8)

# tab_se$SUL  <- gsub("^[^_]+_","P",tab_se$SUL)
# tab_se$Reuse  <- gsub("^[^_]+_","P",tab_se$Reuse)
tab_se$SUL_Reuse <- paste(tab_se$SUL,"+Rev(",tab_se$Reuse,")",sep = "")
tab_se$SUL_Reuse <- gsub("\\+Rev\\(N/A\\)$","",tab_se$SUL_Reuse)
tab_se <- tab_se[tab_se$Correct=="OK",]

tab_se$EqO <- gsub('.[0-9]+\\.[0-9]+,[0-9]+,[a-z]+)$', '', tab_se$EqO)
# plots separated for each SUL 
for(id in id_sul){
  # for(metric_id in c("L_ms","Rounds","SCEx_ms","MQ_Resets","MQ_Symbols","EQ_Resets","EQ_Symbols")){
  for(metric_id in c("L_ms","Rounds","MQ_Resets","EQ_Resets")){
    tab_this <- summarySE(tab_se[tab_se$SUL==id,], measurevar=metric_id, groupvars=c("SUL", "Cache", "Reuse","CloS","CExH","EqO","SUL_Reuse"))
    tab_this <- tab_this[!(tab_this$SUL==tab_this$Reuse),] # include OT revalidate for itself?
    title_lab <- paste(metric_id,"@",id
                       ,"(RandomWalkEQOracle)")
    tab_this$SUL_Reuse <- factor(tab_this$SUL_Reuse, levels=mixedsort(as.character(tab_this$SUL_Reuse)))
    plot <- ggplot(tab_this, aes_string(x="SUL_Reuse", y=metric_id)) +
      geom_errorbar(aes(ymin=tab_this[,9]-tab_this[,12], ymax=tab_this[,9]+tab_this[,12]),color="black", width=1) +
      # geom_bar(stat="identity", position = position_stack(reverse = TRUE)) +
      # coord_flip() +
      geom_point(aes(shape=Reuse, color=Reuse))+
      theme_bw() +
      theme(plot.title = element_text(hjust = 0.5),legend.box.background = element_rect(),axis.text.x = element_text(angle = 45, hjust = 1))+
      labs(title = title_lab, x = "SUL | Reuse")
    filename <- paste(logdir,"/rndWalk/",metric_id,"_",gsub("/","",id),".png",sep="");
    # filename <- paste(logdir,"/rndWalk/all_",metric_id,".png",sep="");
    ggsave(filename, width = 8, height = 8)
    
  }
}

# all SULs in one same plot
# for(metric_id in c("L_ms","Rounds","SCEx_ms","MQ_Resets","MQ_Symbols","EQ_Resets","EQ_Symbols")){
for(metric_id in c("L_ms","Rounds","MQ_Resets","EQ_Resets")){
# for(metric_id in c("EQ_Resets")){
  tab_this <- summarySE(tab_se, measurevar=metric_id, groupvars=c("SUL", "Cache", "Reuse","CloS","CExH","EqO","SUL_Reuse"))
  # tab_this <- tab_this[!(tab_this$SUL==tab_this$Reuse),]  # include OT revalidate for itself?
  title_lab <- paste(metric_id#,"@",id
                     ,"(RandomWalkEQOracle)")
  tab_this$SUL_Reuse <- factor(tab_this$SUL_Reuse, levels=mixedsort(as.character(tab_this$SUL_Reuse)))
  plot <- ggplot(tab_this, aes_string(x="SUL_Reuse", y=metric_id)) +
    geom_errorbar(aes(ymin=tab_this[,9]-tab_this[,12], ymax=tab_this[,9]+tab_this[,12]),color="black", width=1) +
    # geom_bar(stat="identity", position = position_stack(reverse = TRUE)) +
    # coord_flip() +
    geom_point(aes(shape=Reuse, color=Reuse))+
    theme_bw() +
    theme(plot.title = element_text(hjust = 0.5),legend.box.background = element_rect(),axis.text.x = element_text(angle = 45, hjust = 1))+
    labs(title = title_lab, x = "SUL | Reuse")
  print(plot)
  # filename <- paste(logdir,"/rndWalk/",metric_id,"_",gsub("/","",id),".png",sep="");
  filename <- paste(logdir,"/rndWalk/all_",metric_id,".png",sep="");
  ggsave(filename, width = 8, height = 8)
  
}

effsiz_sul <- character()
effsiz_reuz <- character()
effsiz_metr <- character()
effsiz_wilc <- numeric()
effsiz_vd <- numeric()
effsiz_vd_mag <- character()

effsiz_tab <- data.frame(effsiz_sul,effsiz_reuz,effsiz_metr,effsiz_wilc,effsiz_vd,effsiz_vd_mag)
names(effsiz_tab) <- c("SUL","Reuse", "Metric","Wilcox","VD", "VD magnitude" )

reuse_ids_wona <-unique(tab_se$Reuse)
reuse_ids_wona <- setdiff(reuse_ids_wona,c("N/A"))
for(metric_id in c("EQ_Resets","MQ_Resets")){
for(SUL_id in unique(tab_se$SUL)){
  for(reuse_id in reuse_ids_wona){
    # if(SUL_id==reuse_id) next
    # for(metric_id in c( "L_ms","Rounds","SCEx_ms","MQ_Resets","MQ_Symbols", "EQ_Resets","EQ_Symbols")){
    
      
      #####################################################
      # print(paste("SUL ",SUL_id, "Reval(",reuse_id,") | Metric: ",metric_id))
      control<-tab_se[(tab_se$SUL==SUL_id),]
      control<-control[(control$Reuse=="N/A"),]
      
      treatment<-tab_se[(tab_se$SUL==SUL_id),]
      treatment<-treatment[(treatment$Reuse==reuse_id),]
      
      control<-control[,metric_id]
      treatment<-treatment[,metric_id] 
      wilc<-(wilcox.test(control, treatment, paired=FALSE, alternative = "greater",conf.level = 0.95))
      
      ######################
      # L*M vs Dynamic L*M #
      ######################
      
      d <- (c(treatment,control))
      f <- c(rep(c("Treatment"),each=length(treatment)) , rep(c("Control"),each=length(control)))
      ## compute Cohen's d
      ## data and factor
      # effs_d <- print(cohen.d(d,f,paired = FALSE))
      ## compute Hedges' g
      # effs_g <- print(cohen.d(d,f,hedges=TRUE,paired = FALSE))
      ## compute Vargha and Delaney 
      effs_vd <- (VD.A(d,f))
      
      effsiz_tab <- rbind(effsiz_tab,data.frame(
        "SUL"=SUL_id,
        "Reuse"=reuse_id,
        "Metric"=metric_id,
        "Wilcox"=(as.numeric(wilc[3])),
        "VD"=(effs_vd$estimate),
        "VD magnitude"=effs_vd$magnitude
      ))
      
      
      x_d <- c(control,treatment)
      f_d <- c(rep(c("L*M"),each=length(control)), rep(c("Dynamic L*M"),each=length(treatment)))
      x_temp <- data.frame(Metric=x_d,Inference=f_d)
      data_temp  <- melt(x_temp,id.vars = "Inference")
      plot <- ggplot(data_temp, aes(x = value,fill=Inference)) + 
        geom_density(alpha=0.4) + 
        # scale_fill_grey(start = 0, end = .9) +
        ggtitle(label = paste("SUL ",SUL_id, "Reval(",reuse_id,") | Metric: ",metric_id),subtitle = paste("VD Â12 =",round(effs_vd$estimate,digits=3),"(magn. ",effs_vd$magnitude,")")) +
        theme_bw() + 
        theme(plot.title = element_text(hjust = 0.5),plot.subtitle = element_text(hjust = 0.5)) + 
        scale_x_continuous(name = metric_id) + 
        scale_y_continuous(name = "Density")
      # print(plot)
      filename <- paste(logdir,"/rndWalk/EffectSize","_",metric_id,"_",SUL_id,"_",reuse_id,".png",sep="");
      ggsave(filename, width = 8, height = 8)
      
    }
  }
}

rownames(effsiz_tab) <- NULL

effsiz_tab$VD<-round(effsiz_tab$VD,digits = 4)
effsiz_tab$Wilcox<-round(effsiz_tab$Wilcox,digits = 4)

filename <- paste(logdir,"/rndWalk/EffectSize.tab",sep="");
write.table(effsiz_tab,filename,sep="\t",row.names=FALSE, quote=FALSE,dec=",")