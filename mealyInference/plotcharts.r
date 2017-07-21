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
    names(tab_agg) <- c("scenario", "config", "step", "average")
    
    tab_agg$config <- gsub('^ce$', 'CE', tab_agg$config)
    tab_agg$config <- gsub('^ce.cache$', 'CE + Filter', tab_agg$config)
    tab_agg$config <- gsub('^none$', 'Default', tab_agg$config)
    
    plot <- ggplot(subset(tab_agg, scenario %in% c(scenario_name)),
           aes(x = step, 
               y = average, 
               group=config, 
               color=config
               )) + geom_point() + geom_line() 
    #plot <- plot + ggtitle(paste(metric_name, " to infer ",scenario_name,sep="")) + theme(plot.title = element_text(hjust = 0.5))
    plot <- plot + xlab("Number of features") + ylab(paste("Avg (",metric_name,")",sep=""))
    plot <- plot + scale_color_discrete(name="Configuration") 
    plot <- plot + theme_bw()
    plot <- plot + theme(legend.position = "bottom", legend.background = element_rect(color = "black", size = 0.2, linetype = "solid"), legend.direction = "horizontal")
    #plot <- plot + theme(legend.position = "right", legend.background = element_rect(color = "black", size = 0.2, linetype = "solid"), legend.direction = "vertical")
    
    
    filename <- paste(metric_name,"_",scenario_name,".png",sep="")
    ggsave(filename)
  }
}