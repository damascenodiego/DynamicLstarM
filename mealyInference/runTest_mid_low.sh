#!/bin/bash

source constants.sh

## declare an array variable
arr=("experiments_mid_low/fsm/fsm_15_2.txt" "experiments_mid_low/fsm/fsm_15_176.txt" "experiments_mid_low/fsm/fsm_15_352.txt"); 
arr_suls=("./SULs/2feat.txt" "./SULs/50Perc.txt" "./SULs/100Perc.txt")
mkdir -p ./SULs

rm ./log4j/*.log
rm ./SULs/*

logdir=log_experiments_mid_low$(date +"%Y%m%d_%H%M%S_%N")

## now loop through the above array
for a in `seq 1 $reps`; do
   arr[0]="experiments_mid_low/fsm/"`java -jar selectConfig.jar ./experiments_mid_low/fsm/configurations_fsm_15.txt 2`".txt"
   arr[1]="experiments_mid_low/fsm/"`java -jar selectConfig.jar ./experiments_mid_low/fsm/configurations_fsm_15.txt 176`".txt"
   arr[2]="experiments_mid_low/fsm/"`java -jar selectConfig.jar ./experiments_mid_low/fsm/configurations_fsm_15.txt 352`".txt"

   cp ${arr[0]} ./SULs/2feat.txt
   cp ${arr[1]} ./SULs/50Perc.txt
   cp ${arr[2]} ./SULs/100Perc.txt
   
   for i in "${arr_suls[@]}"; do
      echo java -jar ./Infer_LearnLib.jar -sul $i -sot -cexh RivestSchapire -clos CloseFirst -cache -eq rndWalk
      java -jar ./Infer_LearnLib.jar -sul $i -sot -cexh RivestSchapire -clos CloseFirst -cache -eq rndWalk
      for j in "${arr_suls[@]}"; do
         for b in `seq 1 $reps`; do
            java -jar ./Infer_LearnLib.jar -sul $j -ot $i.ot -cexh RivestSchapire -clos CloseFirst -cache -eq rndWalk
         done
      done
   done
done

echo "SUL|Cache|Reuse|CloS|CExH|EqO|L_ms|Rounds|SCEx_ms|MQ_Resets|MQ_Symbols|EQ_Resets|EQ_Symbols|Correct" > log4j/log.tab
for i in  ./log4j/logback*.log; do
   line=`grep "|SUL name"  $i                                       | cut -d\|  -f2- | cut -d:  -f2- `
   line="${line}|"`grep "|Cache"  $i                               | cut -d\|  -f2- | cut -d:  -f2- `
   line="${line}|"`grep "|Reused OT:"  $i                          | cut -d\|  -f2- | cut -d:  -f2- `
   line="${line}|"`grep "|ClosingStrategy: CloseFirst" $i          | cut -d\|  -f2- | cut -d:  -f2- `
   line="${line}|"`grep "|ObservationTableCEXHandler:" $i          | cut -d\|  -f2- | cut -d:  -f2- `
   line="${line}|"`grep "|EquivalenceOracle:"  $i                  | cut -d\|  -f2- | cut -d:  -f2- `
   line="${line}|"`grep "|Learning \[ms\]:"  $i                    | cut -d\|  -f2- | cut -d:  -f2- `
   line="${line}|"`grep "|Rounds:"  $i                             | cut -d\|  -f2- | cut -d:  -f2- `
   line="${line}|"`grep "|Searching for counterexample \[ms\]" $i  | cut -d\|  -f2- | cut -d:  -f2- `
   line="${line}|"`grep "|MQ \[resets\]"  $i                       | cut -d\|  -f2- | cut -d:  -f2- `
   line="${line}|"`grep "|MQ \[symbols\]" $i                       | cut -d\|  -f2- | cut -d:  -f2- `
   line="${line}|"`grep "|EQ \[resets\]"  $i                       | cut -d\|  -f2- | cut -d:  -f2- `
   line="${line}|"`grep "|EQ \[symbols\]" $i                       | cut -d\|  -f2- | cut -d:  -f2- `
   line="${line}|"`grep "|Number of states: " $i                   | cut -d\|  -f2- | cut -d:  -f2- `
   echo $line >> log4j/log.tab
done
sed -i "s/|\ /|/g" ./log4j/log.tab

mkdir $logdir/
mv ./log4j $logdir/