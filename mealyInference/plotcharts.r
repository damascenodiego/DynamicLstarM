library(ggplot2)
library(reshape2)

tab <- read.table("./output.txt", sep="\t", header=TRUE)
tab<-tab[(tab$step<=70),]
#tab<-tab[!(tab$config=="none"),]

#tab<-tab[!(tab$config=="ce_cache_rev"),]
#tab<-tab[!(tab$config=="ce_rev"),]

newdir <- paste("Experiment", format(Sys.time(),"%y_%m_%d_%H_%M_%S"), sep = "_")
#newdir <-'Experiment_test/'
dir.create(newdir)


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
    tab_agg$config <- gsub('^cache$', 'Filter', tab_agg$config)
    tab_agg$config <- gsub('^none$', 'Default', tab_agg$config)
    
    plot <- ggplot(subset(tab_agg, scenario %in% c(scenario_name)),
           aes(x = step, 
               y = average, 
               group=config, 
               color=config
               )) + geom_point() + geom_line() + geom_smooth(aes(x = step, y = average, group=config, color=config), method=lm, se=FALSE)
    plot <- plot + ggtitle(paste(metric_name, " for ",scenario_name,sep="")) 
    plot <- plot + xlab("Number of features") + ylab(paste("Avg (",metric_name,")",sep=""))
    plot <- plot + scale_color_discrete(name="Configuration", breaks=c("Default","Filter","CE","CE + Filter")) 
    plot <- plot + theme_bw()
    plot <- plot + theme(plot.title = element_text(hjust = 0.5), legend.position = "bottom", legend.background = element_rect(color = "black", size = 0.2, linetype = "solid"), legend.direction = "horizontal")
    #plot <- plot + theme(legend.position = "right", legend.background = element_rect(color = "black", size = 0.2, linetype = "solid"), legend.direction = "vertical")
    
    #filename <- paste(newdir,"/",scenario_name,"_",metric_name,".png",sep="")
    filename <- paste(newdir,"/",metric_name,"_",scenario_name,".png",sep="")
    ggsave(filename)
  }
}

tab_errors <- read.table("./noErrors.txt", sep="\t", header=TRUE)
tab_errors<-tab_errors[(tab_errors$step<=70),]

for(scenario_name in unique(tab_errors$scenario)){
  tab_agg <- aggregate(tab_errors[["totErrors"]], by=list(tab_errors$scenario, tab_errors$config, tab_errors$step), 
                       function(x)sum(x, na.rm=TRUE))
  names(tab_agg) <- c("scenario", "config", "step", "totErrors")
  
  tab_agg$config <- gsub('^ce$', 'CE', tab_agg$config)
  tab_agg$config <- gsub('^ce.cache$', 'CE + Filter', tab_agg$config)
  tab_agg$config <- gsub('^cache$', 'Filter', tab_agg$config)
  tab_agg$config <- gsub('^none$', 'Default', tab_agg$config)
  
  plot <- ggplot(subset(tab_agg, scenario %in% c(scenario_name)),
                 aes(x = step, 
                     y = totErrors, 
                     group=config, 
                     color=config
                 )) + geom_point() + geom_line() + geom_smooth(aes(x = step, y = totErrors, group=config, color=config), method=lm, se=FALSE)
  plot <- plot + ggtitle(paste("Total of errors for ",scenario_name,sep="")) 
  plot <- plot + xlab("Number of features") + ylab("Total of Errors")
  plot <- plot + scale_color_discrete(name="Configuration", breaks=c("Default","Filter","CE","CE + Filter")) 
  plot <- plot + theme_bw()
  plot <- plot + theme(plot.title = element_text(hjust = 0.5), legend.position = "bottom", legend.background = element_rect(color = "black", size = 0.2, linetype = "solid"), legend.direction = "horizontal")
  #plot <- plot + theme(legend.position = "right", legend.background = element_rect(color = "black", size = 0.2, linetype = "solid"), legend.direction = "vertical")
  
  #filename <- paste(newdir,"/",scenario_name,"_",metric_name,".png",sep="")
  filename <- paste(newdir,"/","noErrors_",scenario_name,".png",sep="")
  ggsave(filename)
}
  
file.copy("noErrors.txt",newdir)
file.copy("output.txt",newdir)
file.copy("increase_random_fsm.log",newdir)
file.copy("increase_fsm_mid.log",newdir)
file.copy("increase_fsm_best.log",newdir)
file.copy("increase_fsm.log",newdir)



