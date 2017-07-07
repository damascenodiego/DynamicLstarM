rm(list=ls())

#Product = c(1,2,3,4,5,6,7,8,9,10,11,12,13,14,15)

#ffsm = c(567,389,285,448,659,779,917,1188,1270,1490,1206,1770,1609,1608,1792)
#fsm = c(8,10,11,207,11,23,45,92,306,501,1695,4026,8839,18922,38067)

Product = c(8,10,12,14,16,20,25,30,35,40,45,50,55,60,65,70)

ffsm = c(4630,8849,11205,9444,11973,18887,85021,124835,202250,330070,482869,725203,1008881,1344426,1760325,2131610)
fsm = c(1524,3952,18900,163010,990504,23102155,2390700465,74831257074,82741935033,211259618601,147661486668,192128758384,350055779527,332479684585,296591569237,336059447483)

#ffsm_best = c(4215,7063,12355,22142,105334,130965,219619,353873,520702,779515,1073709,1447125,1891641,2307943)
fsm_best = c(108,162,173,218,290,545,1621,2633,3829,5486,6622,7262,8169,11317,11462,12656)

#ffsm_mid = c(7978,9392,16228,89037,119795,207362,337395,500972,776861,1075784,1438131,1878687,2221902)
fsm_mid = c(789,2616,6478,24118,37944,94801,535234,4809151,44599327,276736533,3243250758,9819409682,110535597902,99999999999,99999999999,99999999999)


#pdf("~/myplot.pdf", width=5.05, height=3.8)
mar.default <- c(5,4,4,2) + 0.1
par(mar = mar.default + c(0, 1, 0, 0)) 

plot(Product, ffsm, type="o", main="Check properties FFSM vs FSM(Product by Product)",
     col="blue", xlab="", ylab="", 
     ylim=c(0, 2000000),  xaxt="n", yaxt="n")
lines(Product, fsm, col = "red", lty = 1, type="o", lwd=1, pch=2)
lines(Product, fsm_best, col = "black", lty = 1, type="o", lwd=1, pch=4)
lines(Product, fsm_mid, col = "orange", lty = 1, type="o", lwd=1, pch=5)
abline(h = 0, v = 8, col = "lightgray", lty = 3)
abline(v = 10, col = "lightgray", lty = 3)
abline(v = 12, col = "lightgray", lty = 3)
abline(v = 14, col = "lightgray", lty = 3)
abline(v = 16, col = "lightgray", lty = 3)
abline(v = 20, col = "lightgray", lty = 3)
abline(v = 25, col = "lightgray", lty = 3)
abline(v = 30, col = "lightgray", lty = 3)
abline(v = 35, col = "lightgray", lty = 3)
abline(v = 40, col = "lightgray", lty = 3)
abline(v = 45, col = "lightgray", lty = 3)
abline(v = 50, col = "lightgray", lty = 3)
abline(v = 55, col = "lightgray", lty = 3)
abline(v = 60, col = "lightgray", lty = 3)
abline(v = 65, col = "lightgray", lty = 3)
abline(v = 70, col = "lightgray", lty = 3)
abline(h = 500000, col = "lightgray", lty = 3)
abline(h = 1000000, col = "lightgray", lty = 3)
abline(h = 1500000, col = "lightgray", lty = 3)
abline(h = 2000000, col = "lightgray", lty = 3)
#abline(h = 500000, v = 8, col = "lightgray", lty = 3)

ex2 <- expression("FFSM", "FSM worst", "FSM best", "FSM middle")
legend("top", legend=ex2, lty=c(1,1,1,1), lwd=c(1,1,1,1), col=c("blue", "red","black","orange"), 
       adj = c(0, .6), cex=1, pch=c(1,2,4,5), bty="n")
axis(1, at=Product,labels=Product, col.axis="black", las=1, cex.axis=0.7)
axis(2, col.axis="black", las=2, cex.axis=0.7)

mtext("Number of features of an SPL", side = 1, line = 3, cex =1, font = 1)
mtext("Execution checking time(ms)", side = 2, line = 4, cex =1, font = 1)
