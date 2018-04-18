#!/bin/bash

# source constants.sh
num_revals=20

## declare an array variable
typeSUL=("rmInputs" "rmStates" "rmInputsStates");

rm ./log4j/*.log

logdir=log_scenarios_random_10_100_20_0.6_$(date +"%Y%m%d_%H%M%S_%N")


for sul_scen in experiments_scenarios_random_10_100_20_0.6/*; do
   sul_name=$(basename -- $sul_scen).fsm
   for type in "${typeSUL[@]}"; do
      for sub_sul in $sul_scen/$type/*.fsm; do
         for a in `seq 1 $num_revals`; do
            java -jar ./Infer_LearnLib.jar -sul $sub_sul                       -sot -cexh RivestSchapire -clos CloseFirst -cache -eq irfan -info "$type"
            java -jar ./Infer_LearnLib.jar -sul $sul_scen/$sul_name                 -cexh RivestSchapire -clos CloseFirst -cache -eq irfan -info "$type"
            java -jar ./Infer_LearnLib.jar -sul $sul_scen/$sul_name -ot $sub_sul.ot -cexh RivestSchapire -clos CloseFirst -cache -eq irfan -info "$type"
         done
      done
   done
done

echo "SUL|Cache|Reuse|CloS|CExH|EqO|L_ms|Rounds|SCEx_ms|Total_Resets|Total_Symbols|Correct|Info" > log4j/log.tab
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
   line="${line}|"`grep "|Queries \[resets\]"  $i                       | cut -d\|  -f2- | cut -d:  -f2- `
   line="${line}|"`grep "|Queries \[symbols\]" $i                       | cut -d\|  -f2- | cut -d:  -f2- `
   line="${line}|"`grep "|Number of states: " $i                   | cut -d\|  -f2- | cut -d:  -f2- `
   line="${line}|"`grep "|Info: " $i                   | cut -d\|  -f2- | cut -d:  -f2- `
   echo $line >> log4j/log.tab
done
sed -i "s/|\ /|/g" ./log4j/log.tab

mkdir $logdir/
mv ./log4j $logdir/

Rscript ./plotcharts_scenarios_random.r $logdir