#!/bin/bash

source constants.sh

## declare an array variable
arr=("2.txt" "8.txt" "16.txt");
arr_suls=("./SULs/2.txt" "./SULs/8.txt" "./SULs/16.txt")
mkdir -p ./SULs

rm ./log4j/*.log
rm ./SULs/*

logdir=log_experiments_random$(date +"%Y%m%d_%H%M%S_%N")

random_confs=("experiments_random/fsm/configurations_fsm_15_1.txt"
"experiments_random/fsm/configurations_fsm_15_2.txt"
"experiments_random/fsm/configurations_fsm_15_3.txt"
"experiments_random/fsm/configurations_fsm_15_4.txt"
"experiments_random/fsm/configurations_fsm_15_5.txt"
"experiments_random/fsm/configurations_fsm_15_6.txt"
"experiments_random/fsm/configurations_fsm_15_7.txt"
"experiments_random/fsm/configurations_fsm_15_8.txt"
"experiments_random/fsm/configurations_fsm_15_9.txt"
"experiments_random/fsm/configurations_fsm_15_10.txt"
"experiments_random/fsm/configurations_fsm_15_11.txt"
"experiments_random/fsm/configurations_fsm_15_12.txt"
"experiments_random/fsm/configurations_fsm_15_13.txt"
"experiments_random/fsm/configurations_fsm_15_14.txt"
"experiments_random/fsm/configurations_fsm_15_15.txt"
"experiments_random/fsm/configurations_fsm_15_16.txt"
"experiments_random/fsm/configurations_fsm_15_17.txt"
"experiments_random/fsm/configurations_fsm_15_18.txt"
"experiments_random/fsm/configurations_fsm_15_19.txt"
"experiments_random/fsm/configurations_fsm_15_20.txt"
"experiments_random/fsm/configurations_fsm_15_21.txt"
"experiments_random/fsm/configurations_fsm_15_22.txt"
"experiments_random/fsm/configurations_fsm_15_23.txt"
"experiments_random/fsm/configurations_fsm_15_24.txt"
"experiments_random/fsm/configurations_fsm_15_25.txt"
"experiments_random/fsm/configurations_fsm_15_26.txt"
"experiments_random/fsm/configurations_fsm_15_27.txt"
"experiments_random/fsm/configurations_fsm_15_28.txt"
"experiments_random/fsm/configurations_fsm_15_29.txt"
"experiments_random/fsm/configurations_fsm_15_30.txt")

for conf in "${random_confs[@]}"; do
   ## now loop through the above array
   for a in `seq 1 $rnd_scens`; do
      arr[0]="experiments_random/fsm/"`java -jar selectConfig.jar ./$conf 2`".txt"
      arr[1]="experiments_random/fsm/"`java -jar selectConfig.jar ./$conf 0.5`".txt"
      arr[2]="experiments_random/fsm/"`java -jar selectConfig.jar ./$conf 1.0`".txt"

      cp ${arr[0]} ./SULs/2.txt
      cp ${arr[1]} ./SULs/8.txt
      cp ${arr[2]} ./SULs/16.txt
      
      for i in "${arr_suls[@]}"; do
         echo java -jar ./Infer_LearnLib.jar -sul $i -sot -cexh RivestSchapire -clos CloseFirst -cache -eq rndWalk
         java -jar ./Infer_LearnLib.jar -sul $i -sot -cexh RivestSchapire -clos CloseFirst -cache -eq rndWalk
         for j in "${arr_suls[@]}"; do
            for b in `seq 1 $num_revals`; do
               java -jar ./Infer_LearnLib.jar -sul $j -ot $i.ot -cexh RivestSchapire -clos CloseFirst -cache -eq rndWalk
            done
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

Rscript ./plotcharts.r $logdir