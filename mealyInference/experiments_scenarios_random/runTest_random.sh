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
   Rscript ./plotcharts_scenarios_random.r $logdir
   mv $logdir/logback*.log ./$logdir/log4j/
}

rm ./log4j/*.log

logdir=log_experiments_random$(date +"%Y%m%d_%H%M%S_%N")

reps=5
# SULs parameters
t_inp=10; f_t_inp=`seq -f "%03g" $t_inp $t_inp`; 
t_out=2;  f_t_out=`seq -f "%03g" $t_out $t_out`;

# scenario parameters
s_min=20; f_s_min=`seq -f "%03g" $s_min $s_min`; 
s_max=100 f_s_max=`seq -f "%03g" $s_max $s_max`; 
t_rnd=5; t_rnd_max=`expr $t_rnd - 1`; f_t_rnd=`seq -f "%03g" $t_rnd $t_rnd`;
percents=( "075" "050" "025" );
typeSUL=("rmInputs" "rmStates" "rmInputsStates");

# ./experiments_scenarios_random_$f_s_min\_$f_s_max\_$f_t_rnd/model_$modelId/ex_$f_t_inp\_$f_t_out\_numStates/$typeSUL/i_$f_t_inp\_$f_t_out\_numStates\_r_$rndFsmID.fsm

mkdir $logdir/
mkdir $logdir/log4j/

## now loop through the above array
for model_id in `seq -f "%03g" 0 $t_rnd_max`; do 							# 5x
	for rnd_id in `seq -f "%03g" 0 $t_rnd_max`; do 							# 5x
		for reval in `seq 1 $reps`; do                                 # reps
         for percent in "${percents[@]}"; do 								# 3x
				for f_typeSUL in "${typeSUL[@]}"; do 							# 3x
					for f_numStates in `seq -f "%03g" $s_min $s_min $s_max`; do # 5x
						perc_dir=./experiments_scenarios_random_$f_s_min\_$f_s_max\_$f_t_rnd\_$percent
						sul_name=$perc_dir/model_$model_id/ex_$f_t_inp\_$f_t_out\_$f_numStates/sul.fsm
						subsul_name=$perc_dir/model_$model_id/ex_$f_t_inp\_$f_t_out\_$f_numStates/$f_typeSUL/subsul_$rnd_id.fsm
						# 
		            java -jar ../Infer_LearnLib.jar -sul $subsul_name             -sot -cexh RivestSchapire -clos CloseFirst -cache -eq irfan -info "$percent - $model_id - $f_numStates - $rnd_id - $f_typeSUL - $reval - NA"
		            java -jar ../Infer_LearnLib.jar -sul $sul_name                     -cexh RivestSchapire -clos CloseFirst -cache -eq irfan -info "$percent - $model_id - $f_numStates - $rnd_id - $f_typeSUL - $reval - NA"
		            java -jar ../Infer_LearnLib.jar -sul $sul_name -ot $subsul_name.ot -cexh RivestSchapire -clos CloseFirst -cache -eq irfan -info "$percent - $model_id - $f_numStates - $rnd_id - $f_typeSUL - $reval - Trunc"
		            java -jar ../Infer_LearnLib.jar -sul $sul_name -ot $subsul_name.ot -cexh RivestSchapire -clos CloseFirst -cache -eq irfan -info "$percent - $model_id - $f_numStates - $rnd_id - $f_typeSUL - $reval - Projection" -proj
					done
				done
			done
         mv ./log4j/logback*.log $logdir/;   # add mv log here!
         processLog &                  # add processLog here!
		done
	done
done