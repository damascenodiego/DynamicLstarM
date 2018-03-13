library(ggplot2)
library(reshape2)
library(gtools)
library(stringr)
library(scales)

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

tab <- read.table("./log.tab", sep="|", header=TRUE)

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


tab_wp <- tab[grep("^MealyWpMethodEQOracle",tab$EqO),]
tab_wp$SUL_Reuse <- paste(tab_wp$SUL,"+Rev(",tab_wp$Reuse,")",sep = "")
tab_wp <- tab_wp[tab_wp$Correct=="OK",]
# for(id in id_sul){
  for(metric_name in c("L_ms","Rounds","SCEx_ms","MQ_Resets","MQ_Symbols","EQ_Resets","EQ_Symbols")){
    title_lab <- paste(metric_name#,"@",id
                       ,"(MealyWpMethodEQOracle)")
    tab_this <- tab_wp#[tab_wp$SUL==id,]
    plot <- ggplot(tab_this, aes_string(x="SUL_Reuse", y=metric_name)) +
      # geom_errorbar(aes(ymin=Metric-ci, ymax=Metric+ci),color="black", width=1) +
      geom_bar(stat="identity", position = position_stack(reverse = TRUE)) +
      coord_flip() +
      geom_point(aes(shape=Reuse, color=Reuse))+
      theme_bw() +
      theme(plot.title = element_text(hjust = 0.5),legend.box.background = element_rect())+
      labs(title = title_lab, x = "SUL | Reuse")
    # filename <- paste("./plots/wp/",metric_name,"_",gsub("/","",id),".pdf",sep=""); ggsave(filename)
    filename <- paste("./plots/wp/",metric_name,".pdf",sep=""); ggsave(filename, width = 8, height = 12)
    ggsave(filename)
    print(plot)
  }
# }

tab_ok <- rle(sort(tab_wp$Correct))
df_ok <- data.frame(Status=tab_ok$values, Total=tab_ok$lengths, Percent = as.numeric(100 * tab_ok$lengths / sum(tab_ok$lengths)))
p <- ggplot(df_ok, aes(Status, Total) ) + 
  geom_bar(stat="identity") + labs(title = "Correct hypotheses", x = "Status", y = "Total number") +
  geom_text(aes(label=paste(df_ok$Total," (",percent(df_ok$Percent/100),")",sep="")), vjust=0)
filename <- "./plots/wp/correct.pdf"
ggsave(filename, width = 8, height = 8)


tab_se <- tab[grep("^RandomWalkEQOracle",tab$EqO),]

tab_ok <- rle(sort(tab_se$Correct))
df_ok <- data.frame(Status=tab_ok$values, Total=tab_ok$lengths, Percent = as.numeric(100 * tab_ok$lengths / sum(tab_ok$lengths)))
p <- ggplot(df_ok, aes(Status, Total) ) + 
  geom_bar(stat="identity") + labs(title = "Correct hypotheses", x = "Status", y = "Total number") +
  geom_text(aes(label=paste(df_ok$Total," (",percent(df_ok$Percent/100),")",sep="")), vjust=0)
filename <- "./plots/rndWalk/correct.pdf"
ggsave(filename, width = 8, height = 8)


tab_se$SUL_Reuse <- paste(tab_se$SUL,"+Rev(",tab_se$Reuse,")",sep = "")
tab_se <- tab_se[tab_se$Correct=="OK",]
# for(id in id_sul){
  for(metric_name in c("L_ms","Rounds","SCEx_ms","MQ_Resets","MQ_Symbols","EQ_Resets","EQ_Symbols")){
    tab_this <- summarySE(tab_se#[tab_se$SUL==id,]
                          , measurevar=metric_name, groupvars=c("SUL", "Cache", "Reuse","CloS","CExH","EqO","SUL_Reuse"))
    title_lab <- paste(metric_name#,"@",id
                       ,"(RandomWalkEQOracle)")
    plot <- ggplot(tab_this, aes_string(x="SUL_Reuse", y=metric_name)) +
      geom_errorbar(aes(ymin=tab_this[,9]-tab_this[,12], ymax=tab_this[,9]+tab_this[,12]),color="black", width=1) +
      # geom_bar(stat="identity", position = position_stack(reverse = TRUE)) +
      coord_flip() +
      geom_point(aes(shape=Reuse, color=Reuse))+
      theme_bw() +
      theme(plot.title = element_text(hjust = 0.5),legend.box.background = element_rect())+
      labs(title = title_lab, x = "SUL | Reuse")
    # filename <- paste("./plots/rndWalk/",metric_name,"_",gsub("/","",id),".pdf",sep=""); ggsave(filename)
    filename <- paste("./plots/rndWalk/",metric_name,".pdf",sep=""); ggsave(filename, width = 8, height = 12)
    
  }
# }



