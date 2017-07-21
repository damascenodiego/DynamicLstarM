library(ggplot2)
library(reshape2)

tab <- read.table("./output.txt", sep="\t", header=TRUE)
tab<-tab[(tab$step<=70),]

#tab<-tab[!(tab$config=="ce_cache_rev"),]
#tab<-tab[!(tab$config=="ce_rev"),]


for(metric_name in c(
                      #"rounds", 
                      "mq_resets", "mq_symbol", "eq_resets", "eq_symbol", "learning", "search_ce"
                      #,"learning_ce" 
                    )){
  #for(scenario_name in c("fsm", "fsm_best", "fsm_mid")){
  for(scenario_name in unique(tab$scenario)){
    tab_agg <- aggregate(tab[[metric_name]], by=list(tab$scenario, tab$config, tab$step), 
                     function(x)mean(x, na.rm=TRUE))
    names(tab_agg) <- c("Scenario", "Configuration", "step", "average")
    
    plot <- ggplot(subset(tab_agg, Scenario %in% c(scenario_name)),
           aes(x = step, 
               y = average, 
               group=Configuration, 
               color=Configuration
               )) + 
      geom_point()+geom_line()
    
    filename <- paste(metric_name,"_",scenario_name,".png",sep="")
    ggsave(filename)
  }
}