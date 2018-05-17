#!/bin/bash

function processLog {   
   if [ ! -f $logdir/log.tab ]; then
      echo "SUL|Cache|Reuse|CloS|CExH|EqO|L_ms|Rounds|SCEx_ms|Reval_Resets|Reval_Symbols|MQ_Resets|MQ_Symbols|EQ_Resets|EQ_Symbols|Correct|Info|Total_Suffixes" > $logdir/log.tab
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
      line="${line}|"`grep "|OT suffixes: " $i                  | cut -d\|  -f2- | awk -F"," '{print NF-1}'`
      echo $line | sed "s/|\ /|/g" >> $logdir/log.tab
   done
   Rscript ./plotcharts_nordsec16.r $logdir
   mv $logdir/logback*.log ./$logdir/log4j/
}

# source constants.sh
reps=10
## declare an array variable
arr=("experiment_nordsec16/server_097c.dot.txt" "experiment_nordsec16/server_097e.dot.txt");

rm ./log4j/*.log
rm ./experiment_nordsec16/server_*.ot
rm ./experiment_nordsec16/server_*.sul
rm ./experiment_nordsec16/server_*.infer
rm ./experiment_nordsec16/server_*.final
rm ./experiment_nordsec16/server_*.reval

logdir=log_experiment_nordsec16$(date +"%Y%m%d_%H%M%S_%N")

mkdir $logdir/
mkdir $logdir/log4j/

## now loop through the above array
# for i in "${arr[@]}"; do
for i in "experiment_nordsec16/server_097.dot.txt"; do
   for a in `seq 1 $reps`; do
      java -jar ./Infer_LearnLib.jar -sul $i -sot -cexh RivestSchapire -clos CloseFirst -cache -eq wp
      for j in "${arr[@]}"; do
         for b in `seq 1 $reps`; do
            java -jar ./Infer_LearnLib.jar -sul $j      -cexh RivestSchapire -clos CloseFirst -cache -eq irfan
            java -jar ./Infer_LearnLib.jar -sul $j -ot $i.ot -cexh RivestSchapire -clos CloseFirst -cache -eq irfan
         done
      done
      mv ./log4j/logback*.log $logdir/
      processLog &
   done
done