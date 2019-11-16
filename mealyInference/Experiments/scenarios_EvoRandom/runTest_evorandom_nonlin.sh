#!/bin/bash

function processLog {   
   if [ ! -f $logdir/log.tab ]; then
      echo "SUL|Cache|Reuse|CloS|CExH|EqO|L_ms|Rounds|SCEx_ms|Reval_Resets|Reval_Symbols|MQ_Resets|MQ_Symbols|EQ_Resets|EQ_Symbols|Correct|Info|Total_Suffixes|S_size|I_size" > $logdir/log.tab
   fi   
   for i in  ./$logdir/logback*.log; do
      line=`grep "|SUL name"  $i                                       | cut -d\|  -f2- | cut -d:  -f2- `
      line="${line}|"`grep "|Cache"  $i                               | cut -d\|  -f2- | cut -d:  -f2- `
      line="${line}|"`grep "|Reused OT:"  $i                          | cut -d\|  -f2- | cut -d:  -f2- `
      line="${line}|"`grep "|ClosingStrategy: CloseFirst" $i          | cut -d\|  -f2- | cut -d:  -f2- `
      line="${line}|"`grep "|ObservationTableCEXHandler:" $i          | cut -d\|  -f2- | cut -d:  -f2- `
      line="${line}|"`grep "|EquivalenceOracle:"  $i                  | cut -d\|  -f2- | cut -d:  -f2- `
      line="${line}|"`grep "|Learning \[ms\]:"  $i                    | cut -d\|  -f2- | cut -d:  -f2- `
      line="${line}|"`grep "|Rounds:"  $i                             | cut -d\|  -f2- | cut -d:  -f2- `
      line="${line}|"`grep "|Searching for counterexample \[ms\]" $i  | cut -d\|  -f2- | cut -d:  -f2- `
      line="${line}|"`grep "|Reused queries \[resets\]"  $i           | cut -d\|  -f2- | cut -d:  -f2- `
      line="${line}|"`grep "|Reused queries \[symbols\]" $i           | cut -d\|  -f2- | cut -d:  -f2- `
      line="${line}|"`grep "|MQ \[resets\]"  $i                  | cut -d\|  -f2- | cut -d:  -f2- `
      line="${line}|"`grep "|MQ \[symbols\]"  $i                  | cut -d\|  -f2- | cut -d:  -f2- `
      line="${line}|"`grep "|EQ \[resets\]"  $i                  | cut -d\|  -f2- | cut -d:  -f2- `
      line="${line}|"`grep "|EQ \[symbols\]"  $i                  | cut -d\|  -f2- | cut -d:  -f2- `
      line="${line}|"`grep "|Equivalent: " $i                   | cut -d\|  -f2- | cut -d:  -f2- `
      line="${line}|"`grep "|Info: " $i                         | cut -d\|  -f2- | cut -d:  -f2- `
      line="${line}|"`grep "|OT suffixes: " $i                  | cut -d\|  -f2- | awk -F"," '{print NF-1}'`
      line="${line}|"`grep "|SUL total states: " $i             | cut -d\|  -f2- | cut -d:  -f2- `
      line="${line}|"`grep "|SUL total inputs: " $i             | cut -d\|  -f2- | cut -d:  -f2- `
      echo $line | sed "s/|\ /|/g" >> $logdir/log.tab
   done
   Rscript ./plotcharts_scenarios_evoRandom_nonlin.r $logdir
   mv $logdir/logback*.log ./$logdir/log4j/
}

rm ./log4j/*.log

folder="evoRandom_s_0250_p_20_v_100"
logdir=$folder/log\_$(date +"%Y%m%d_%H%M%S_%N")

# s_all={"0010" "0025" "0050" "0075" "0100" "0250" "0500" "0750" "1000"}

# reps=30; s_val="0250"; p_tot="10"; v_tot="100";
reps=2; s_val="0250"; p_tot="2"; v_tot="50";

mkdir $logdir/
mkdir $logdir/log4j/

## now loop through the above array
for p_val in `seq -f "%03g" 1 $p_tot`; do
for reval in `seq 1 $reps`; do
   # for s_val in "${s_all[@]}"; do
      for v_val in `seq -f "%03g" 10 10 $v_tot`; do
         v_prev=`expr $v_val - 10`;v_prev=`seq -f "%03g" $v_prev $v_prev`
            sul=./$folder/s_$s_val/p_$p_val/v_000.fsm
         newsul=./$folder/s_$s_val/p_$p_val/v_$v_val.fsm
         prevsul=./$folder/s_$s_val/p_$p_val/v_$v_prev.fsm

         java -Xms512m -Xmx2048m  -jar ../Infer_LearnLib.jar -sul $sul             -sot   -cexh Suffix1by1 -clos CloseFirst -cache -eq irfan -info "NA"
         java -Xms512m -Xmx2048m  -jar ../Infer_LearnLib.jar -sul $prevsul         -sot   -cexh Suffix1by1 -clos CloseFirst -cache -eq irfan -info "NA"
         java -Xms512m -Xmx2048m  -jar ../Infer_LearnLib.jar -sul $newsul                 -cexh Suffix1by1 -clos CloseFirst -cache -eq irfan -info "NA"

         java -Xms512m -Xmx2048m  -jar ../Infer_LearnLib.jar -sul $newsul -ot $sul.ot     -cexh Suffix1by1 -clos CloseFirst -cache -eq irfan -info "$p_val - $s_val - $v_val - $reval - First+proj"  	-proj
         java -Xms512m -Xmx2048m  -jar ../Infer_LearnLib.jar -sul $newsul -ot $prevsul.ot -cexh Suffix1by1 -clos CloseFirst -cache -eq irfan -info "$p_val - $s_val - $v_val - $reval - Previous+proj"	-proj
         java -Xms512m -Xmx2048m  -jar ../Infer_LearnLib.jar -sul $newsul -ot $sul.ot     -cexh Suffix1by1 -clos CloseFirst -cache -eq irfan -info "$p_val - $s_val - $v_val - $reval - First"
         java -Xms512m -Xmx2048m  -jar ../Infer_LearnLib.jar -sul $newsul -ot $prevsul.ot -cexh Suffix1by1 -clos CloseFirst -cache -eq irfan -info "$p_val - $s_val - $v_val - $reval - Previous"
         
      done
   # done
   mv ./log4j/logback*.log $logdir/
   processLog &
done
done