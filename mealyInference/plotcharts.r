library(ggplot2)
library(reshape2)


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


tab <- read.table(paste("./",spl_name,"_output.txt",sep=""), sep="\t", header=TRUE)

spl_name <- "agm"
newdir <-paste('Experiment_',spl_name,"/",sep = "")
dir.create(newdir)


for(metric_name in c("mq_resets", "mq_symbol", "eq_resets", "eq_symbol", "learning", "search_ce")){
    tab_agg <- summarySE(tab, measurevar=metric_name, groupvars=c("scenario", "config"))
    
    colnames(tab_agg)[2] <- "Configuration"
    colnames(tab_agg)[4] <- "Metric"
    tab_agg$scenario<-gsub('^fsm_agm', 'AGM', tab_agg$scenario)
    tab_agg$Configuration <- gsub('^cache.rev$', 'Filter + Rev', tab_agg$Configuration)
    tab_agg$Configuration <- gsub('^cache$', 'Filter', tab_agg$Configuration)
    tab_agg$Configuration <- gsub('^none$', 'Default', tab_agg$Configuration)
    
    
    
    title_lab = paste(metric_name)
    x_lab="Scenario"
    y_lab=metric_name
    leg_lab="Configuration"
    
    plot <- ggplot(tab_agg, aes(x=scenario, y=Metric,group=Configuration,color=Configuration)) +
      geom_errorbar(aes(ymin=Metric-ci, ymax=Metric+ci),color="black", width=1) +
      geom_line() +
      geom_point(aes(shape=Configuration, color=Configuration))+
      scale_shape_manual(values=c(4,25,24))+
      theme_bw() +
      theme(plot.title = element_text(hjust = 0.5),legend.box.background = element_rect()) #+
      # labs(title = title_lab, x = x_lab, y = y_lab, color = leg_lab)
    
    filename <- paste(newdir,"/",metric_name,".png",sep="")
    ggsave(filename)
}

tab_errors <- read.table(paste("./",spl_name,"_noErrors.txt",sep=""), sep="\t", header=TRUE)

tab_agg <- summarySE(tab_errors, measurevar="totErrors", groupvars=c("scenario", "config"))

colnames(tab_agg)[2] <- "Configuration"
colnames(tab_agg)[4] <- "Errors"

  
tab_agg$scenario<-gsub('^fsm_agm', 'AGM', tab_agg$scenario)
tab_agg$Configuration <- gsub('^cache.rev$', 'Filter + Rev', tab_agg$Configuration)
tab_agg$Configuration <- gsub('^cache$', 'Filter', tab_agg$Configuration)
tab_agg$Configuration <- gsub('^none$', 'Default', tab_agg$Configuration)

title_lab = paste(metric_name," Avg no. of Errors")
x_lab="Scenario"
y_lab="Tot Errors (Avg)"
leg_lab="Configuration"

plot <- ggplot(tab_agg, aes(x=scenario, y=Errors,group=Configuration,color=Configuration)) +
  geom_errorbar(aes(ymin=Errors-ci, ymax=Errors+ci),color="black", width=1) +
  geom_line() +
  geom_point(aes(shape=Configuration, color=Configuration))+
  scale_shape_manual(values=c(4,25,24))+
  theme_bw() +
  theme(plot.title = element_text(hjust = 0.5),legend.box.background = element_rect()) +
  # scale_color_manual(values=c("#FF0000", "#00FF00" , "#0000FF"))+
  # scale_y_continuous(limits=c(0, 1.0)) +
  # scale_x_continuous(limits=c(0, 100),breaks=0:100*10) +
  labs(title = title_lab, x = x_lab, y = y_lab, color = leg_lab)

filename <- paste(newdir,"/totErrors.png",sep="")
ggsave(filename)

file.copy(paste("./",spl_name,"_output.txt",sep=""),newdir)
file.copy(paste("./",spl_name,"_noErrors.txt",sep=""),newdir)
file.remove(paste("./",spl_name,"_output.txt",sep=""))
file.remove(paste("./",spl_name,"_noErrors.txt",sep=""))
