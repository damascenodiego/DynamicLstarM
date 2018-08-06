list.of.packages <- c("ggplot2","reshape2","gtools","stringr","scales","effsize","SortableHTMLTables","RColorBrewer")

# new.packages <- list.of.packages[!(list.of.packages %in% installed.packages(lib.loc="/home/damascdn/Rpackages/")[,"Package"])]
# if(length(new.packages)) install.packages(new.packages,lib="/home/damascdn/Rpackages/")
# lapply(list.of.packages,require,character.only=TRUE, lib.loc="/home/damascdn/Rpackages/")

new.packages <- list.of.packages[!(list.of.packages %in% installed.packages()[,"Package"])]
if(length(new.packages)) install.packages(new.packages)
lapply(list.of.packages,require,character.only=TRUE)

# Multiple plot function
#
# ggplot objects can be passed in ..., or to plotlist (as a list of ggplot objects)
# - cols:   Number of columns in layout
# - layout: A matrix specifying the layout. If present, 'cols' is ignored.
#
# If the layout is something like matrix(c(1,2,3,3), nrow=2, byrow=TRUE),
# then plot 1 will go in the upper left, 2 will go in the upper right, and
# 3 will go all the way across the bottom.
#
multiplot <- function(..., plotlist=NULL, file, cols=1, layout=NULL) {
  library(grid)
  
  # Make a list from the ... arguments and plotlist
  plots <- c(list(...), plotlist)
  
  numPlots = length(plots)
  
  # If layout is NULL, then use 'cols' to determine layout
  if (is.null(layout)) {
    # Make the panel
    # ncol: Number of columns of plots
    # nrow: Number of rows needed, calculated from # of cols
    layout <- matrix(seq(1, cols * ceiling(numPlots/cols)),
                     ncol = cols, nrow = ceiling(numPlots/cols))
  }
  
  if (numPlots==1) {
    print(plots[[1]])
    
  } else {
    # Set up the page
    grid.newpage()
    pushViewport(viewport(layout = grid.layout(nrow(layout), ncol(layout))))
    
    # Make each plot, in the correct location
    for (i in 1:numPlots) {
      # Get the i,j matrix positions of the regions that contain this subplot
      matchidx <- as.data.frame(which(layout == i, arr.ind = TRUE))
      
      print(plots[[i]], vp = viewport(layout.pos.row = matchidx$row,
                                      layout.pos.col = matchidx$col))
    }
  }
}

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

# logdir<-args

# OpenSSL (server-side versions)
logdir<-"./"; fname<-"nordsec16_server"
list.of.suls.to.remove <- c(
  # "server_097",
  # "server_097c",
  # "server_097e",
  # "server_098l",
  # "server_098m",
  # "server_098s",
  # "server_098u",
  # "server_098za",
  # "server_100"  #remove
  # "server_101",
  # "server_101k",
  # "server_102",
  # "server_110pre1"
)

# ## OpenSSL (client-side versions)
# logdir<-"./"; fname<-"nordsec16_client"
# list.of.suls.to.remove <- c(
#   "client_097","client_097e","client_098f"
# #   "client_098j", "client_098l", "client_098m", "client_098za","client_101", "client_100m","client_101h","client_102","client_110-pre1"
# )

# logdir<-"./experiment_verleg/Learning-SSH-Paper/models/"; fname<-"verleg"
# logdir<-"./experiment_usenix15/"; fname<-"usenix15_gnuTLS_server"
# logdir<-"./experiment_usenix15/"; fname<-"usenix15_gnuTLS_client"
# logdir<-"./experiment_usenix15/"; fname<-"usenix15_openSSL_srv"
# logdir<-"./experiment_usenix15/"; fname<-"usenix15_openSSL_cli"

tab_filename<-paste(logdir,fname,".tab",sep="")

data <- read.table(tab_filename, sep="\t", header=TRUE)
reused_lst  <- levels(data$Reused)
reused_lst  <-reused_lst [! (reused_lst %in% c('N/A'))]
reused_lst  <- c(c("N/A"),reused_lst)
data$Reused <- factor(data$Reused, reused_lst)

data$Total_Resets<-data$EQ_Reset+data$MQ_Reset

for(model_name in unique(data$Inferred)){
  data[((data$Inferred==model_name)&(!(data$Reused=="N/A"))),"EQ_Reset_Percent"]<-data[((data$Inferred==model_name)&(!(data$Reused=="N/A"))),"EQ_Reset"]/data[((data$Inferred==model_name)&((data$Reused=="N/A"))),"EQ_Reset"]
  data[((data$Inferred==model_name)&(!(data$Reused=="N/A"))),"MQ_Reset_Percent"]<-data[((data$Inferred==model_name)&(!(data$Reused=="N/A"))),"MQ_Reset"]/data[((data$Inferred==model_name)&((data$Reused=="N/A"))),"MQ_Reset"]
  data[((data$Inferred==model_name)&(!(data$Reused=="N/A"))),"Total_Resets_Percent"]<-data[((data$Inferred==model_name)&(!(data$Reused=="N/A"))),"Total_Resets"]/data[((data$Inferred==model_name)&((data$Reused=="N/A"))),"Total_Resets"]
}
data[(data$Reused=="N/A"),"EQ_Reset_Percent"]<-1
data[(data$Reused=="N/A"),"MQ_Reset_Percent"]<-1
data[(data$Reused=="N/A"),"Total_Resets_Percent"]<-1


tab_ok <- data
tab_ok$Scenario<-"N/A"
tab_ok[grep("N/A",tab_ok$Reused,invert = TRUE),]$Scenario<-"Dynamic L*M"
tab_ok[grep("N/A",tab_ok$Reused,invert = FALSE),]$Scenario<-"L*M"
tab_ok$Merged <- paste(tab_ok$Scenario,tab_ok$Success,sep = "|")
tab_count<- rle(sort(tab_ok$Merged))


df_ok <- data.frame(Method=tab_count$values, Total=tab_count$lengths)
df_ok$Percent <- 0 
df_ok[df_ok$Method=="L*M|OK", ]$Percent <- df_ok[df_ok$Method=="L*M|OK", ]$Total/sum(df_ok[df_ok$Method=="L*M|OK",]$Total,df_ok[df_ok$Method=="L*M|NOK",]$Total)
df_ok[df_ok$Method=="L*M|NOK",]$Percent <- df_ok[df_ok$Method=="L*M|NOK",]$Total/sum(df_ok[df_ok$Method=="L*M|OK",]$Total,df_ok[df_ok$Method=="L*M|NOK",]$Total)
df_ok[df_ok$Method=="Dynamic L*M|OK", ]$Percent <- df_ok[df_ok$Method=="Dynamic L*M|OK", ]$Total/sum(df_ok[df_ok$Method=="Dynamic L*M|OK",]$Total,df_ok[df_ok$Method=="Dynamic L*M|NOK",]$Total)
df_ok[df_ok$Method=="Dynamic L*M|NOK",]$Percent <- df_ok[df_ok$Method=="Dynamic L*M|NOK",]$Total/sum(df_ok[df_ok$Method=="Dynamic L*M|OK",]$Total,df_ok[df_ok$Method=="Dynamic L*M|NOK",]$Total)
df_ok$Percent <- round(100*df_ok$Percent,digits = 2)

df_ok$Status<-"Failed"
df_ok[df_ok$Method=="L*M|OK", ]$Status<-"OK"
df_ok[df_ok$Method=="Dynamic L*M|OK", ]$Status<-"OK"
df_ok$Method<-gsub("\\|N?OK$","",df_ok$Method)
df_ok <- df_ok[,c(1,4,2,3)]

plotdir<- paste(logdir, "plots","/",fname,sep = "")
dir.create(file.path(plotdir), showWarnings = FALSE,recursive = TRUE)

p <- ggplot(df_ok, aes(x=Method, y=Percent) ) +
  geom_bar(aes(fill = Status),stat="identity") +
  scale_fill_manual(values = c("OK" = "light green", "Failed" = "red")) +
  scale_y_continuous(limits=c(0,100)) +
  labs(title = "Models correctly inferred (in %)", x = "Inference algorithm", y = "Percentage of correct hypotheses") +
  theme(
    plot.title = element_text(hjust = 0.5),
    plot.subtitle = element_text(hjust = 0.5),
    legend.position="right",
    axis.text.x = element_text(angle = 15, hjust = 1)
  )
  

filename <- paste(plotdir,"/accuracy.png",sep = "");ggsave(filename, width = 7, height = 6,dpi=320)

filename <- paste(plotdir,"/accuracy.tab",sep = "")
write.table(df_ok,filename,sep="\t",row.names=FALSE, quote=FALSE,dec=",",append=FALSE)

rm(tab_ok,df_ok) #remove tab_ok and df_ok


data <-data[(data$Success=="OK"),]

for(sulToRm in list.of.suls.to.remove){
  data <- data[(!((data$Inferred==sulToRm)|(data$Reused==sulToRm))),]
}

colourCount = length(unique(data$Inferred))
###
# coul = brewer.pal(4, "BuPu")  # Classic palette BuPu, with 4 colors
# coul = brewer.pal(12, "Set3") # My palette
coul = brewer.pal(12, "Paired") # My palette
getPalette = colorRampPalette(coul)
##

metric_id<-"EQ_Reset"
data_summ <- summarySE(data, measurevar=metric_id, groupvars=c("Inferred", "Reused"))
p2 <- ggplot(data=data_summ, aes(x=Inferred, y=EQ_Reset, fill = Reused)) +
  geom_bar(colour = "black", position='dodge', stat="identity", width=0.75) +
  geom_errorbar(aes(
    ymin=data_summ[,metric_id]-data_summ[,"ci"], ymax=data_summ[,metric_id]+data_summ[,"ci"]
  ), position = position_dodge(0.75),width = 0.2)+
  theme(plot.title = element_text(hjust = 0.5),legend.box.background = element_rect(),axis.text.x = element_text(angle = 45, hjust = 1))+
  labs(title = tab_filename)+
  scale_fill_manual(values = c("#A9A9A9",getPalette(colourCount)))
  # scale_fill_brewer(palette="Spectral")
  
filename <- paste(plotdir,"/EQ_Reset","_",fname,".png",sep="");ggsave(filename, width = 15, height = 5,dpi=320)

metric_id<-"MQ_Reset"
data_summ <- summarySE(data, measurevar=metric_id, groupvars=c("Inferred", "Reused"))
p2 <- ggplot(data=data_summ, aes(x=Inferred, y=MQ_Reset, fill = Reused)) +
  geom_bar(colour = "black", position='dodge', stat="identity", width=0.75) +
  geom_errorbar(aes(
    ymin=data_summ[,metric_id]-data_summ[,"ci"], ymax=data_summ[,metric_id]+data_summ[,"ci"]
  ), position = position_dodge(0.75),width = 0.2)+
  theme(plot.title = element_text(hjust = 0.5),legend.box.background = element_rect(),axis.text.x = element_text(angle = 45, hjust = 1))+
  labs(title = tab_filename)+
  scale_fill_manual(values = c("#A9A9A9",getPalette(colourCount)))
  # scale_fill_brewer(palette="Spectral")

filename <- paste(plotdir,"/MQ_resets","_",fname,".png",sep="");ggsave(filename, width = 15, height = 5,dpi=320)

metric_id<-"Rounds"
data_summ <- summarySE(data, measurevar=metric_id, groupvars=c("Inferred", "Reused"))
p2 <- ggplot(data=data_summ, aes(x=Inferred, y=Rounds, fill = Reused)) +
  geom_bar(colour = "black", position='dodge', stat="identity", width=0.75) +
  geom_errorbar(aes(
    ymin=data_summ[,metric_id]-data_summ[,"ci"], ymax=data_summ[,metric_id]+data_summ[,"ci"]
  ), position = position_dodge(0.75),width = 0.2)+
  theme(plot.title = element_text(hjust = 0.5),legend.box.background = element_rect(),axis.text.x = element_text(angle = 45, hjust = 1))+
  labs(title = tab_filename)+
  scale_fill_manual(values = c("#A9A9A9",getPalette(colourCount)))
# scale_fill_brewer(palette="Spectral")

filename <- paste(plotdir,"/Rounds","_",fname,".png",sep="");ggsave(filename, width = 15, height = 5,dpi=320)

metric_id<-"MQ_Reset_Reval"
data_summ <- summarySE(data, measurevar=metric_id, groupvars=c("Inferred", "Reused"))
data_summ<-data_summ[(!(data_summ$Reused=="N/A")),]
p2 <- ggplot(data=data_summ, aes(x=Inferred, y=MQ_Reset_Reval, fill = Reused)) +
  geom_bar(colour = "black", position='dodge', stat="identity", width=0.75) +
  geom_errorbar(aes(
    ymin=data_summ[,metric_id]-data_summ[,"ci"], ymax=data_summ[,metric_id]+data_summ[,"ci"]
  ), position = position_dodge(0.75),width = 0.2)+
  theme(plot.title = element_text(hjust = 0.5),legend.box.background = element_rect(),axis.text.x = element_text(angle = 45, hjust = 1))+
  labs(title = tab_filename)+
  scale_fill_manual(values = getPalette(colourCount))
# scale_fill_brewer(palette="Spectral")

filename <- paste(plotdir,"/MQ_Reset_Reval","_",fname,".png",sep="");ggsave(filename, width = 15, height = 5,dpi=320)



metric_id<-"Total_Resets"
data_summ <- summarySE(data, measurevar=metric_id, groupvars=c("Inferred", "Reused"))
data_summ<-data_summ[(!(data_summ$Reused=="N/A")),]
p2 <- ggplot(data=data_summ, aes(x=Inferred, y=Total_Resets, fill = Reused)) +
  geom_bar(colour = "black", position='dodge', stat="identity", width=0.75) +
  geom_errorbar(aes(
    ymin=data_summ[,metric_id]-data_summ[,"ci"], ymax=data_summ[,metric_id]+data_summ[,"ci"]
  ), position = position_dodge(0.75),width = 0.2)+
  theme(plot.title = element_text(hjust = 0.5),legend.box.background = element_rect(),axis.text.x = element_text(angle = 45, hjust = 1))+
  labs(title = tab_filename)+
  scale_fill_manual(values = getPalette(colourCount))
# scale_fill_brewer(palette="Spectral")

filename <- paste(plotdir,"/Total_Resets","_",fname,".png",sep="");ggsave(filename, width = 15, height = 5,dpi=320)


filename <- paste(plotdir,"/Prcnt_EQ_Reset_",fname,".tab",sep="");
metric_id<-"EQ_Reset"
data_summ <- summarySE(data, measurevar=metric_id, groupvars=c("Inferred", "Reused"))
sink(filename)
sul_lst<-levels(unique(data_summ$Inferred))
cat("SUL","L*M",sul_lst,"\n",sep="\t")
# cat("SUL","L*M",gsub("$",")",gsub("^","Dyn L*M(",sul_lst)),"\n",sep="\t")
for(sul in sul_lst){
  # if(sul %in% list.of.suls.to.remove) next;
  mylist<-c(sul)
  mylist<-c(mylist,round(data_summ[((data_summ$Inferred==sul)&(data_summ$Reused=="N/A")),]$EQ_Reset,digits = 2))
  for(ruz in sul_lst){
    # if(ruz %in% list.of.suls.to.remove) next;
    content_str<-paste(data_summ[((data_summ$Inferred==sul)&(data_summ$Reused==ruz)),]$EQ_Reset,"",sep="")
    if(content_str==""){
      mylist<-c(mylist,'-')
    }else{
      content_str<-paste(
        round(data_summ[((data_summ$Inferred==sul)&(data_summ$Reused==ruz)),]$EQ_Reset,digits = 2),
        " sd=",
        round(data_summ[((data_summ$Inferred==sul)&(data_summ$Reused==ruz)),]$sd,digits = 2),
        "=sd",
        " perc=",
        round(
          ((data_summ[((data_summ$Inferred==sul)&(data_summ$Reused==ruz)),]$sd/data_summ[((data_summ$Inferred==sul)&(data_summ$Reused=="N/A")),]$EQ_Reset)-1)*100
          ,digits = 2),
        "=perc",
        sep="")
      mylist<-c(mylist,content_str)
    }
    
  }
  cat(mylist,"\n",sep="\t")
}
sink()


filename <- paste(plotdir,"/Prcnt_MQ_Reset_",fname,".tab",sep="");
metric_id<-"MQ_Reset"
data_summ <- summarySE(data, measurevar=metric_id, groupvars=c("Inferred", "Reused"))
sink(filename)
sul_lst<-levels(unique(data_summ$Inferred))
cat("SUL","L*M",sul_lst,"\n",sep="\t")
# cat("SUL","L*M",gsub("$",")",gsub("^","Dyn L*M(",sul_lst)),"\n",sep="\t")
for(sul in sul_lst){
  # if(sul %in% list.of.suls.to.remove) next;
  mylist<-c(sul)
  mylist<-c(mylist,round(data_summ[((data_summ$Inferred==sul)&(data_summ$Reused=="N/A")),]$MQ_Reset,digits = 2))
  for(ruz in sul_lst){
    # if(ruz %in% list.of.suls.to.remove) next;
    content_str<-paste(data_summ[((data_summ$Inferred==sul)&(data_summ$Reused==ruz)),]$MQ_Reset,"",sep="")
    if(content_str==""){
      mylist<-c(mylist,'-')
    }else{
      content_str<-paste(
        round(data_summ[((data_summ$Inferred==sul)&(data_summ$Reused==ruz)),]$MQ_Reset,digits = 2),
        " sd=",
        round(data_summ[((data_summ$Inferred==sul)&(data_summ$Reused==ruz)),]$sd,digits = 2),
        "=sd",
        " perc=",
        round(
          ((data_summ[((data_summ$Inferred==sul)&(data_summ$Reused==ruz)),]$sd/data_summ[((data_summ$Inferred==sul)&(data_summ$Reused=="N/A")),]$MQ_Reset)-1)*100
          ,digits = 2),
        "=perc",
        sep="")
      mylist<-c(mylist,content_str)
    }
    
  }
  cat(mylist,"\n",sep="\t")
}
sink()

