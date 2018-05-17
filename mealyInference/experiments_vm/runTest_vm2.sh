#!/bin/bash

# source constants.sh
rnd_scens=2;num_revals=2
## declare an array variable
arr=("");
arr_suls=("./SULs/5.txt" "./SULs/6.txt" "./SULs/7.txt" "./SULs/8.txt")
mkdir -p ./SULs

rm ./log4j/*.log
rm ./SULs/*

logdir=log_experiments_vm$(date +"%Y%m%d_%H%M%S_%N")

random_confs=("experiments_vm/fsm/configurations_fsm_vm.txt")

for conf in "${random_confs[@]}"; do
   ## now loop through the above array
   for a in `seq 1 $rnd_scens`; do
      arr[0]="experiments_vm/fsm/"`java -jar selectConfig.jar ./$conf 5`".txt"
      arr[1]="experiments_vm/fsm/"`java -jar selectConfig.jar ./$conf 6`".txt"
      arr[2]="experiments_vm/fsm/"`java -jar selectConfig.jar ./$conf 7`".txt"
      arr[3]="experiments_vm/fsm/"`java -jar selectConfig.jar ./$conf 8`".txt"
      

      cp ${arr[0]} ./SULs/5.txt
      cp ${arr[1]} ./SULs/6.txt
      cp ${arr[2]} ./SULs/7.txt
      cp ${arr[3]} ./SULs/8.txt
      
      
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