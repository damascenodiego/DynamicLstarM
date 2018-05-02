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

# logdir<-"./log_scenarios_random20180416_180612_609539375"
logdir<-args
tab_filename<-paste(logdir,"/log.tab",sep="")

tab <- read.table(tab_filename, sep="|", header=TRUE)

tab$L_ms    <- as.numeric(tab$L_ms)
tab$Rounds  <- as.numeric(tab$Rounds)
tab$SCEx_ms <- as.numeric(tab$CExH)
tab$MQ_Resets  <- as.numeric(tab$MQ_Resets)
tab$MQ_Symbols <- as.numeric(tab$MQ_Symbols)
tab$EQ_Resets  <- as.numeric(tab$EQ_Resets)
tab$EQ_Symbols <- as.numeric(tab$EQ_Symbols)
tab$Correct    <- as.character(tab$Correct)

tab$SUL <- gsub('^v_', '', gsub('.fsm$', '', tab$SUL))
tab$Reuse <- gsub('^v_', '', gsub('.fsm.ot$', '', tab$Reuse))
tab$SUL <- gsub("^[0-9]+_[0-9]+_",'',tab$SUL)
tab$Reuse <- gsub("^[0-9]+_[0-9]+_",'',tab$Reuse)

tab<-cbind(tab,str_split_fixed(tab$Info, " - ", 4))

tab[,"2"]<-gsub("^0+","",tab[,"2"])
tab$size<-as.numeric(tab[,"2"])

dir.create(file.path(logdir, "IrfanEQOracle"), showWarnings = FALSE)

tab_ok <- tab[grep("^IrfanEQOracle",tab$EqO),]
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
filename <- paste(logdir,"/IrfanEQOracle/correct.png",sep = "")
ggsave(filename, width = 8, height = 8)
rm(tab_ok,df_ok) #remove tab_ok and df_ok

tab_se <- tab[grep("^IrfanEQOracle",tab$EqO),]
tab_se <- tab_se[tab_se$Correct=="OK",]
tab_se$EqO <- gsub('.[0-9]+.$', '', tab_se$EqO)

# plots separated for each kind of sub-FSM 
for(metric_id in c("L_ms","Rounds","MQ_Resets","MQ_Symbols","EQ_Resets","EQ_Symbols")){
    # tab_this<-tab_se[tab_se$SUL==id,]
    tab_this<-na.omit(tab_se)
    tab_this$Reuse<-gsub("^[0-9-]+","REV",tab_this$Reuse)# tab_this$Reuse<-gsub("^N/A","",tab_this$Reuse)
    
    tab_this <- summarySE(tab_this, measurevar=metric_id, groupvars=c("size", "Reuse"))
    title_lab <- paste(metric_id,"(IrfanEQOracle)")
    plot <- ggplot(tab_this, aes_string(x="size", y=metric_id,colour="Reuse")) +
      geom_line()+
      geom_errorbar(aes(ymin=tab_this[,4]-tab_this[,7], ymax=tab_this[,4]+tab_this[,7]),color="black", width=1) +
      # geom_bar(stat="identity", position = position_stack(reverse = TRUE)) +
      # coord_flip() +
      geom_point(aes(shape=Reuse, color=Reuse))+
      theme_bw() +
      theme(plot.title = element_text(hjust = 0.5),legend.box.background = element_rect(),axis.text.x = element_text(angle = 45, hjust = 1))+
      labs(title = title_lab, x = "Size")
    filename <- paste(logdir,"/IrfanEQOracle/",metric_id,".png",sep=""); # filename <- paste(logdir,"/IrfanEQOracle/all_",metric_id,".png",sep="");
    ggsave(filename, width = 8, height = 8)
    
}


# dir.create(file.path(logdir, "IrfanEQOracle/EffectSize/"), showWarnings = FALSE)
# 
# effsiz_size <- character()
# effsiz_metr <- character()
# effsiz_wilc <- numeric()
# effsiz_d <- numeric()
# effsiz_d_mag <- character()
# effsiz_g <- numeric()
# effsiz_g_mag <- character()
# effsiz_vd <- numeric()
# effsiz_vd_mag <- character()
# 
# effsiz_tab <- data.frame(effsiz_size,effsiz_metr,
#                          effsiz_wilc,
#                          effsiz_d,effsiz_d_mag,
#                          effsiz_g,effsiz_g_mag,
#                          effsiz_vd,effsiz_vd_mag)
# names(effsiz_tab) <- c("Size","Metric","Wilcox","Cohen", "Cohen magnitude","Hedges", "Hedges magnitude","VD", "VD magnitude" )
# 
# 
# for(metric_id in c("L_ms","Rounds","MQ_Resets","MQ_Symbols","EQ_Resets","EQ_Symbols")){
#     for(size in unique(tab_se$size)){
#       tab_this<-na.omit(tab_se)
#       tab_this<-tab_this[tab_this$size==size,]
#       tab_this$Reuse<-gsub("^[0-9-]+","REV",tab_this$Reuse)# tab_this$Reuse<-gsub("^N/A","",tab_this$Reuse)
#       
#       #####################################################
#       control<-tab_this[tab_this$Reuse=="N/A",metric_id]
#       treatment<-tab_this[tab_this$Reuse=="REV",metric_id]
#       
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
#       effs_d <- (cohen.d(d,f,paired = FALSE))
#       ## compute Hedges' g
#       effs_g <- (cohen.d(d,f,hedges=TRUE,paired = FALSE))
#       ## compute Vargha and Delaney 
#       effs_vd <- (VD.A(d,f))
#       
#       effsiz_tab <- rbind(effsiz_tab,data.frame(
#         "Size"=size,
#         "Metric"=metric_id,
#         "Wilcox"=(as.numeric(wilc[3])),
#         "Cohen"=(effs_d$estimate),
#         "Cohen magnitude"=effs_d$magnitude,
#         "Hedges"=(effs_g$estimate),
#         "Hedges magnitude"=effs_g$magnitude,
#         "VD"=(effs_vd$estimate),
#         "VD magnitude"=effs_vd$magnitude
#         
#       ))
#   }
# }
# 
# rownames(effsiz_tab) <- NULL
# 
# effsiz_tab$VD<-round(effsiz_tab$VD,digits = 4)
# effsiz_tab$Wilcox<-round(effsiz_tab$Wilcox,digits = 4)
# 
# filename <- paste(logdir,"/IrfanEQOracle/EffectSize/EffectSize.tab",sep="");
# write.table(effsiz_tab,filename,sep="\t",row.names=FALSE, quote=FALSE,dec=",",append=FALSE)
# 
