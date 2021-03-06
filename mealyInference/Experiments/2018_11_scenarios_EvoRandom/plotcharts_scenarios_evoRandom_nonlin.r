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

# logdir<-"./xxx"
logdir<-args
tab_filename<-paste(logdir,"/log.tab",sep="")

tab <- read.table(tab_filename, sep="|", header=TRUE)
tab$Info<-gsub("^.+Traditional$","",tab$Info)

tab$L_ms    <- as.numeric(tab$L_ms)
tab$Rounds  <- as.numeric(tab$Rounds)
tab$SCEx_ms <- as.numeric(tab$CExH)
tab$Reval_Resets  <- as.numeric(tab$Reval_Resets)
tab$Reval_Symbols <- as.numeric(tab$Reval_Symbols)
tab$MQ_Resets  <- as.numeric(tab$MQ_Resets)
tab$MQ_Symbols <- as.numeric(tab$MQ_Symbols)
tab$EQ_Resets  <- as.numeric(tab$EQ_Resets)
tab$EQ_Symbols <- as.numeric(tab$EQ_Symbols)
tab$Correct    <- as.character(tab$Correct)
tab$Total_Suffixes <- as.numeric(tab$Total_Suffixes)
tab$S_size <- as.numeric(tab$S_size)
tab$I_size <- as.numeric(tab$I_size)

tab$SUL <- gsub('^v_', '', gsub('.fsm$', '', tab$SUL))
tab$Reuse <- gsub('^v_', '', gsub('.fsm.ot$', '', tab$Reuse))

tab<-cbind(tab,str_split_fixed(tab$Info, " - ", 5))
names(tab)[names(tab)=="1"] <- "p_id"; tab$p_id<-gsub("^0+","",tab$p_id)
names(tab)[names(tab)=="2"] <- "s_id"; tab$s_id<-gsub("^0+","",tab$s_id)
names(tab)[names(tab)=="3"] <- "Version"   ;
names(tab)[names(tab)=="4"] <- "Reval"; tab$Reval<-gsub("^0+","",tab$Reval)
names(tab)[names(tab)=="5"] <- "ReuseApproach"; tab$ReuseApproach<-gsub("^0+","",tab$ReuseApproach)
tab$Version<-tab$SUL
tab$Version<-gsub("^0+$","_",tab$Version); tab$Version<-gsub("^0+","",tab$Version); tab$Version<-gsub("^_+","0",tab$Version)

tab$Version <-as.numeric(tab$Version)
tab$SUL <- tab$Version

dir.create(file.path(logdir, "IrfanEQOracle"), showWarnings = FALSE)

# tab<-tab[grep("^000$",tab$SUL,invert = TRUE),]
tab_ok <- tab[grep("^IrfanEQOracle",tab$EqO),]
tab_ok$CorrectType <- paste(gsub("^[0-9]+","Dynamic L*M",gsub('^N/A',"L*M",tab_ok$Reuse)),tab_ok$ReuseApproach,tab_ok$Correct)
tab_ok$Method <- paste(gsub("^[0-9]+","Dynamic L*M",gsub('^N/A',"L*M",tab_ok$Reuse)),tab_ok$ReuseApproach)
tab_ok <- rle(sort(tab_ok$CorrectType))


df_ok <- data.frame(Correct=tab_ok$values, Total=tab_ok$lengths)
df_ok$Method<-"L*M"

df_ok[grep("^Dynamic L\\*M First",df_ok$Correct),]$Method<-"Dynamic L*M First"
df_ok[grep("^Dynamic L\\*M Previous",df_ok$Correct),]$Method<-"Dynamic L*M Previous"

df_ok[grep("^Dynamic L\\*M First\\+proj",df_ok$Correct),]$Method<-"Dynamic L*M First+proj"
df_ok[grep("^Dynamic L\\*M Previous\\+proj",df_ok$Correct),]$Method<-"Dynamic L*M Previous+proj"


df_ok$Correct <- gsub("^(Dynamic )?L\\*M ([FirstPrevious\\+proj ]+)?","",df_ok$Correct)
df_ok$Percent <-0

df_ok[df_ok$Method=="Dynamic L*M First+proj",]$Percent<-df_ok[df_ok$Method=="Dynamic L*M First+proj",]$Total/sum(df_ok[df_ok$Method=="Dynamic L*M First+proj",]$Total)
df_ok[df_ok$Method=="Dynamic L*M Previous+proj",]$Percent<-df_ok[df_ok$Method=="Dynamic L*M Previous+proj",]$Total/sum(df_ok[df_ok$Method=="Dynamic L*M Previous+proj",]$Total)

df_ok[df_ok$Method=="Dynamic L*M First",]$Percent<-df_ok[df_ok$Method=="Dynamic L*M First",]$Total/sum(df_ok[df_ok$Method=="Dynamic L*M First",]$Total)
df_ok[df_ok$Method=="Dynamic L*M Previous",]$Percent<-df_ok[df_ok$Method=="Dynamic L*M Previous",]$Total/sum(df_ok[df_ok$Method=="Dynamic L*M Previous",]$Total)

df_ok[df_ok$Method=="L*M",]$Percent<-df_ok[df_ok$Method=="L*M",]$Total/sum(df_ok[df_ok$Method=="L*M",]$Total)
df_ok$Percent <- 100*df_ok$Percent
p <- ggplot(df_ok, aes(x=Method, y=Percent,fill=Correct) ) +
  geom_bar(stat="identity", position=position_dodge()) +
  scale_fill_manual(values = c("OK" = "dark green", "NOK" = "red")) +
  scale_y_continuous(limits=c(0,100)) +
  labs(title = "Correct hypotheses", x = "Method", y = "Correct hypothese (in %)") +
  theme(plot.title = element_text(hjust = 0.5),plot.subtitle = element_text(hjust = 0.5)) +
  geom_text(aes(label=paste(df_ok$Total," (",round(df_ok$Percent,digits = 3),"%)",sep="")), position=position_dodge(width=0.9), vjust=-0.25)
filename <- paste(logdir,"/IrfanEQOracle/correct.png",sep = "")
ggsave(filename, width = 8, height = 8)
rm(tab_ok,df_ok) #remove tab_ok and df_ok
# 
tab_se <- tab[grep("^IrfanEQOracle",tab$EqO),]
tab_se <- tab_se[tab_se$Correct=="OK",]
tab_se$EqO <- gsub('.[0-9,]+.$', '', tab_se$EqO)

tab_se <- tab_se[grep("^0+$",tab_se$SUL,invert = TRUE),]

tab_se$MQMinusRevalResets<-tab_se$MQ_Resets-tab_se$Reval_Resets
tab_se$MQMinusRevalSymbols<-tab_se$MQ_Symbols-tab_se$Reval_Symbols

tab_se$Total_Resets<-tab_se$MQ_Resets+tab_se$EQ_Resets
tab_se$Total_Symbols<-tab_se$MQ_Symbols+tab_se$EQ_Symbols

for(metric_id in c("L_ms","Rounds"
                   ,"Reval_Resets","MQ_Resets","EQ_Resets","Total_Resets","MQMinusRevalResets"
                   ,"Reval_Symbols","MQ_Symbols","EQ_Symbols","Total_Symbols","MQMinusRevalSymbols"
                   ,"Total_Suffixes"
                   )){
  # tab_this<-tab_se[tab_se$SUL==id,]
  # print(metric_id)
  tab_this<-(tab_se)
  tab_this$Reuse<-gsub("^[0-9-]+","REV",tab_this$Reuse)# tab_this$Reuse<-gsub("^N/A","",tab_this$Reuse)
  tab_this$Reuse<-paste(tab_this$Reuse,tab_this$ReuseApproach)

  tab_this$Version<-as.numeric(tab_this$Version)
  tab_this <- summarySE(tab_this, measurevar=metric_id, groupvars=c("Version", "Reuse"))
  title_lab <- paste(metric_id,"(IrfanEQOracle)")
  plot <- ggplot(tab_this, aes_string(x="Version", y=metric_id,colour="Reuse")) +
    geom_line()+
    geom_errorbar(aes(ymin=tab_this[,metric_id]-tab_this[,"ci"], ymax=tab_this[,metric_id]+tab_this[,"ci"]), width=1) +
    # geom_bar(stat="identity", position = position_stack(reverse = TRUE)) +
    # coord_flip() +
    geom_point(aes(shape=Reuse, color=Reuse))+
    theme_bw() +
    theme(plot.title = element_text(hjust = 0.5),legend.box.background = element_rect(),axis.text.x = element_text(angle = 45, hjust = 1))+
    ylim(0, max(tab_this[,metric_id]))+
    labs(title = title_lab, x = "Version")
  filename <- paste(logdir,"/IrfanEQOracle/",metric_id,".png",sep=""); # filename <- paste(logdir,"/IrfanEQOracle/all_",metric_id,".png",sep="");
  ggsave(filename, width = 8, height = 8)

}

for(metric_id in c("S_size","I_size")){
  tab_this <- summarySE(tab_se, measurevar=metric_id, groupvars=c("Version"))
  plot <- ggplot(tab_this, aes_string(x="Version", y=metric_id)) +
    geom_line()+
    geom_errorbar(aes(ymin=tab_this[,metric_id]-tab_this$ci, ymax=tab_this[,metric_id]+tab_this$ci),color="black", width=1) +
    theme_bw() +
    theme(plot.title = element_text(hjust = 0.5),legend.box.background = element_rect(),axis.text.x = element_text(angle = 45, hjust = 1))+
    labs(title = "SUL size")
  print(plot)
  filename <- paste(logdir,"/IrfanEQOracle","/model_",metric_id,".png",sep="");
  ggsave(filename, width = 8, height = 8)  
}

# # dir.create(file.path(logdir, "IrfanEQOracle/EffectSize/"), showWarnings = FALSE)
# # effsiz_version <- character()
# # effsiz_metr <- character()
# # effsiz_wilc <- numeric()
# # effsiz_vd <- numeric()
# # effsiz_vd_mag <- character()
# # 
# # effsiz_tab <- data.frame(effsiz_version,effsiz_metr,
# #                          effsiz_wilc,
# #                          effsiz_vd,effsiz_vd_mag)
# # names(effsiz_tab) <- c("Version","Metric","Wilcox","VD", "VD magnitude" )
# # 
# # for(metric_id in c("L_ms","Rounds","MQ_Resets","MQ_Symbols","EQ_Resets","EQ_Symbols")){
# #     for(ver in unique(tab_se$Version)){
# #       tab_this<-na.omit(tab_se)
# #       tab_this<-tab_this[tab_this$Version==ver,]
# #       tab_this$Reuse<-gsub("^[0-9-]+","REV",tab_this$Reuse)# tab_this$Reuse<-gsub("^N/A","",tab_this$Reuse)
# #       tab_this$Reuse<-paste(tab_this$Reuse,tab_this$ReuseApproach)
# # 
# #       #####################################################
# #       control<-tab_this[tab_this$Reuse=="N/A",metric_id]
# #       treatment<-tab_this[tab_this$Reuse=="REV",metric_id]
# # 
# #       wilc<-(wilcox.test(control, treatment, paired=FALSE, alternative = "greater",conf.level = 0.95))
# # 
# #       ######################
# #       # L*M vs Dynamic L*M #
# #       ######################
# # 
# #       d <- (c(treatment,control))
# #       f <- c(rep(c("Treatment"),each=length(treatment)) , rep(c("Control"),each=length(control)))
# #       ## compute Vargha and Delaney
# #       effs_vd <- (VD.A(d,f))
# # 
# #       effsiz_tab <- rbind(effsiz_tab,data.frame(
# #         "Version"=ver,
# #         "Metric"=metric_id,
# #         "Wilcox"=(as.numeric(wilc[3])),
# #         "VD"=(effs_vd$estimate),
# #         "VD magnitude"=effs_vd$magnitude
# # 
# #       ))
# #   }
# # }
# # rownames(effsiz_tab) <- NULL
# # effsiz_tab$VD<-round(effsiz_tab$VD,digits = 4)
# # effsiz_tab$Wilcox<-round(effsiz_tab$Wilcox,digits = 4)
# # filename <- paste(logdir,"/IrfanEQOracle/EffectSize.tab",sep="");
# # write.table(effsiz_tab,filename,sep="\t",row.names=FALSE, quote=FALSE,dec=",",append=FALSE)
