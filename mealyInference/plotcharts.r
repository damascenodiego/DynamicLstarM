library(ggplot2)
library(reshape2)

tab <- read.table("./Experiment_17_07_21_13_17_05/output.txt", sep="\t", header=TRUE)
tab<-tab[(tab$step<=70),]
#tab<-tab[!(tab$config=="none"),]

#tab<-tab[!(tab$config=="ce_cache_rev"),]
#tab<-tab[!(tab$config=="ce_rev"),]

#newdir <- paste("Experiment", format(Sys.time(),"%y_%m_%d_%H_%M_%S"), sep = "_")
#dir.create(newdir)

newdir <-'Experiment_17_07_21_13_17_05'

for(metric_name in c(
                      #"rounds", 
                      "mq_resets", "mq_symbol", "eq_resets", "eq_symbol", "learning", "search_ce"
                      #,"learning_ce" 
                    )){
  for(scenario_name in c("fsm", "fsm_best", "fsm_mid")){
  #for(scenario_name in unique(tab$scenario)){
    tab_agg <- aggregate(tab[[metric_name]], by=list(tab$scenario, tab$config, tab$step), 
                     function(x)mean(x, na.rm=TRUE))
    names(tab_agg) <- c("scenario", "config", "step", "average")
    
    tab_agg$config <- gsub('^ce$', 'CE', tab_agg$config)
    tab_agg$config <- gsub('^ce.cache$', 'CE + Filter', tab_agg$config)
    tab_agg$config <- gsub('^none$', 'Default', tab_agg$config)
    
    plot <- ggplot(subset(tab_agg, scenario %in% c(scenario_name)),
           aes(x = step, 
               y = average, 
               group=config, 
               color=config
               )) + geom_point() + geom_line() + geom_smooth(aes(x = step, y = average, group=config, color=config), method=lm, se=FALSE)
    plot <- plot + ggtitle(paste(metric_name, " for ",scenario_name,sep="")) + theme(plot.title = element_text(hjust = 0.5))
    plot <- plot + xlab("Number of features") + ylab(paste("Avg (",metric_name,")",sep=""))
    plot <- plot + scale_color_discrete(name="Configuration", breaks=c("Default","CE","CE + Filter")) 
    plot <- plot + theme_bw()
    plot <- plot + theme(legend.position = "bottom", legend.background = element_rect(color = "black", size = 0.2, linetype = "solid"), legend.direction = "horizontal")
    #plot <- plot + theme(legend.position = "right", legend.background = element_rect(color = "black", size = 0.2, linetype = "solid"), legend.direction = "vertical")
    
    #filename <- paste(newdir,"/",scenario_name,"_",metric_name,".png",sep="")
    filename <- paste(newdir,"/",metric_name,"_",scenario_name,".png",sep="")
    ggsave(filename)
  }
}

file.copy(list.files(".","output.txt", full.names = TRUE),"newdir")
file.copy(list.files(".",".+log", full.names = TRUE),"newdir")