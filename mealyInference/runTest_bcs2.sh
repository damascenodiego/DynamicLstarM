#!/bin/bash

source constants.sh

## declare an array variable
arr=("experiments_bcs2/fsm/fsm_bcs2_1.txt" "experiments_bcs2/fsm/fsm_bcs2_2.txt" "experiments_bcs2/fsm/fsm_bcs2_3.txt" "experiments_bcs2/fsm/fsm_bcs2_4.txt" "experiments_bcs2/fsm/fsm_bcs2_5.txt" "experiments_bcs2/fsm/fsm_bcs2_6.txt");

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
      echo java -jar ./Infer_LearnLib.jar -sul $i -sot -cexh RivestSchapire -clos CloseFirst -cache -eq rndWalk
      java -jar ./Infer_LearnLib.jar -sul $i -sot -cexh RivestSchapire -clos CloseFirst -cache -eq rndWalk
      for j in "${arr[@]}"; do
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
mv ./experiments_bcs2/fsm/fsm_*.ot  $logdir/
mv ./experiments_bcs2/fsm/fsm_*.sul  $logdir/
mv ./experiments_bcs2/fsm/fsm_*.infer  $logdir/
mv ./experiments_bcs2/fsm/fsm_*.final  $logdir/
mv ./experiments_bcs2/fsm/fsm_*.reval  $logdir/

# for i in ./experiments_bcs2/fsm/fsm_bcs2_[0-9].txt; do
#    echo java -jar ./Infer_LearnLib.jar -sul $i -sot -cexh RivestSchapire -clos CloseFirst -cache -eq wp
#    java -jar ./Infer_LearnLib.jar -sul $i -sot -cexh RivestSchapire -clos CloseFirst -cache -eq wp
#    for j    in ./experiments_bcs2/fsm/fsm_bcs2_[0-9].txt; do
#       java -jar ./Infer_LearnLib.jar -sul $j -ot $i.ot -cexh RivestSchapire -clos CloseFirst -cache -eq wp
#    done
# done

