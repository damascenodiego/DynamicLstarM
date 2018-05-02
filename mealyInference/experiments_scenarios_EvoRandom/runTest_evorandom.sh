#!/bin/bash

function processLog {   
   if [ ! -f $logdir/log.tab ]; then
      echo "SUL|Cache|Reuse|CloS|CExH|EqO|L_ms|Rounds|SCEx_ms|Reval_Resets|Reval_Symbols|MQ_Resets|MQ_Symbols|EQ_Resets|EQ_Symbols|Correct|Info" > $logdir/log.tab
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
      line="${line}|"`grep "|Info: " $i                               | cut -d\|  -f2- | cut -d:  -f2- `
      echo $line | sed "s/|\ /|/g" >> $logdir/log.tab
   done
   Rscript ./plotcharts_scenarios_evoRandom.r $logdir
   mv $logdir/logback*.log ./$logdir/log4j/
}

rm ./log4j/*.log

logdir=log_experiments_evorandom$(date +"%Y%m%d_%H%M%S_%N")

reps=5
s_ini="100"
s_end="500"
p_end="10";p_end=`expr $p_end - 1`;
v_end="5";v_end=`expr $v_end - 1`; v_end_minusone=`expr $v_end - 1`

mkdir $logdir/
mkdir $logdir/log4j/

## now loop through the above array
for p_val in `seq -f "%03g" 0 $p_end`; do
for v_val in `seq -f "%03g" 0 $v_end_minusone`; do
   for s_val in `seq -f "%04g" $s_ini $s_ini $s_end`; do
      for reval in `seq 1 $reps`; do
         sul=./evoRandom_s_$s_ini\_$s_end\_p_`expr $p_end + 1`\_v_`expr $v_end + 1`/s_$s_val/p_$p_val/v_$v_val.fsm
         v_next=`expr $v_val + 1`; v_next=`seq -f "%03g" $v_next $v_next`
         newsul=./evoRandom_s_$s_ini\_$s_end\_p_`expr $p_end + 1`\_v_`expr $v_end + 1`/s_$s_val/p_$p_val/v_$v_next.fsm
         
         java -jar ../Infer_LearnLib.jar -sul $sul           -sot  -cexh RivestSchapire -clos CloseFirst -cache -eq irfan -info "NA"
         java -jar ../Infer_LearnLib.jar -sul $newsul              -cexh RivestSchapire -clos CloseFirst -cache -eq irfan -info "$p_val - $s_val - $v_next - $reval"
         java -jar ../Infer_LearnLib.jar -sul $newsul -ot $sul.ot  -cexh RivestSchapire -clos CloseFirst -cache -eq irfan -info "$p_val - $s_val - $v_next - $reval"
      done
   done
   mv ./log4j/logback*.log $logdir/
   processLog &
done
done