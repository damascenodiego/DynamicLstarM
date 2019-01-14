#!/bin/bash

# source constants.sh
reps=20;
## declare an array variable

arr=(
"experiments_vm/fsm/fsm_vm_1.txt"
"experiments_vm/fsm/fsm_vm_2.txt"
"experiments_vm/fsm/fsm_vm_3.txt"
"experiments_vm/fsm/fsm_vm_4.txt"
"experiments_vm/fsm/fsm_vm_5.txt"
"experiments_vm/fsm/fsm_vm_6.txt"
"experiments_vm/fsm/fsm_vm_7.txt"
"experiments_vm/fsm/fsm_vm_8.txt"
"experiments_vm/fsm/fsm_vm_9.txt"
"experiments_vm/fsm/fsm_vm_10.txt"
"experiments_vm/fsm/fsm_vm_11.txt"
"experiments_vm/fsm/fsm_vm_12.txt"
"experiments_vm/fsm/fsm_vm_13.txt"
"experiments_vm/fsm/fsm_vm_14.txt"
"experiments_vm/fsm/fsm_vm_15.txt"
"experiments_vm/fsm/fsm_vm_16.txt"
"experiments_vm/fsm/fsm_vm_17.txt"
"experiments_vm/fsm/fsm_vm_18.txt"
"experiments_vm/fsm/fsm_vm_19.txt"
"experiments_vm/fsm/fsm_vm_20.txt");

rm ./log4j/*.log
rm ./experiments_bcs2/fsm/fsm_*.ot
rm ./experiments_bcs2/fsm/fsm_*.sul
rm ./experiments_bcs2/fsm/fsm_*.infer
rm ./experiments_bcs2/fsm/fsm_*.final
rm ./experiments_bcs2/fsm/fsm_*.reval

logdir=log_experiments_bcs2$(date +"%Y%m%d_%H%M%S_%N")

## now loop through the above array
for i in "${arr[@]}"; do
   for a in `seq 1 $reps`; do
      java -jar ./Infer_LearnLib.jar -sul $i -sot -cexh RivestSchapire -clos CloseFirst -cache -eq irfan
      for j in "${arr[@]}"; do
         for b in `seq 1 $reps`; do
            java -jar ./Infer_LearnLib.jar -sul $j      -cexh RivestSchapire -clos CloseFirst -cache -eq irfan
            java -jar ./Infer_LearnLib.jar -sul $j -ot $i.ot -cexh RivestSchapire -clos CloseFirst -cache -eq irfan
         done
      done
   done
done

echo "SUL|Cache|Reuse|CloS|CExH|EqO|L_ms|Rounds|SCEx_ms|Reval_Resets|Reval_Symbols|Total_Resets|Total_Symbols|Correct|Info" > log4j/log.tab
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
   line="${line}|"`grep "|Reused queries \[resets\]"  $i           | cut -d\|  -f2- | cut -d:  -f2- `
   line="${line}|"`grep "|Reused queries \[symbols\]" $i           | cut -d\|  -f2- | cut -d:  -f2- `
   line="${line}|"`grep "|Queries \[resets\]"  $i                  | cut -d\|  -f2- | cut -d:  -f2- `
   line="${line}|"`grep "|Queries \[symbols\]" $i                  | cut -d\|  -f2- | cut -d:  -f2- `
   line="${line}|"`grep "|Number of states: " $i                   | cut -d\|  -f2- | cut -d:  -f2- `
   line="${line}|"`grep "|Info: " $i                               | cut -d\|  -f2- | cut -d:  -f2- `
   echo $line >> log4j/log.tab
done
sed -i "s/|\ /|/g" ./log4j/log.tab

mkdir $logdir/
mv ./log4j $logdir/
mv ./experiments_bcs2/fsm/fsm_*.ot  $logdir/
mv ./experiments_bcs2/fsm/fsm_*.sul  $logdir/
mv ./experiments_bcs2/fsm/fsm_*.infer  $logdir/
mv ./experiments_bcs2/fsm/fsm_*.final  $logdir/
mv ./experiments_bcs2/fsm/fsm_*.reval  $logdir/

Rscript ./plotcharts.r $logdir
