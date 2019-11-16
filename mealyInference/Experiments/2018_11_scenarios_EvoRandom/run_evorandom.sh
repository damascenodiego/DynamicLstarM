#!/bin/bash

if [[ $# -eq 0 ]] ; 
then
   runID=$(date +"%Y%m%d_%H%M%S_%N")
else
   runID=$1
fi

function processLog {   
   if [ ! -f $rundir/log.tab ]; then
      echo "SUL|Cache|Reuse|CloS|CExH|EqO|L_ms|Rounds|SCEx_ms|Reval_Resets|Reval_Symbols|MQ_Resets|MQ_Symbols|EQ_Resets|EQ_Symbols|Correct|Info|Total_Suffixes|S_size|I_size" > $rundir/log.tab
   fi   
   for i in  $tmpdir/*.log; do
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
      echo $line | sed "s/|\ /|/g" >> $rundir/log.tab
   done
   Rscript $experimentdir/plotcharts_scenarios_evoRandom.r $rundir &> /dev/null &
   mv $tmpdir/*.log $logdir
}



experimentdir=/home/damascdn/remote_euler/learnlib/

rundir=$experimentdir/experiment\_$runID
mkdir $rundir/

tmpdir=$rundir/tmp/
mkdir $tmpdir/

logdir=$rundir/logs/
mkdir $logdir/

otdir=$rundir/OTs/
mkdir $otdir/

s_val="0250";
p_tot="10";
v_tot="100";
reps=10;

cd $experimentdir

## now loop!
for p_val in `seq -f "%03g" 1 $p_tot`; do
for reval in `seq 1 $reps`; do
   # for s_val in "${s_all[@]}"; do
   for v_val in `seq -f "%03g" 10 10 $v_tot`; do
       v_prev=`expr $v_val - 10`;v_prev=`seq -f "%03g" $v_prev $v_prev`
          sul=$experimentdir/evoRandom_s_0250_p_20_v_100/s_$s_val/p_$p_val/v_000.fsm
       newsul=$experimentdir/evoRandom_s_0250_p_20_v_100/s_$s_val/p_$p_val/v_$v_val.fsm
      prevsul=$experimentdir/evoRandom_s_0250_p_20_v_100/s_$s_val/p_$p_val/v_$v_prev.fsm

      otdir_now=$otdir/s_$s_val/p_$p_val/v_$v_val/r_$reval/
      mkdir -p $otdir_now

      jvm_args="-Dlogdir=$tmpdir -Dlogname=log_$s_val""_$p_val""_$v_val""_$reval -Dlogback.configurationFile=$experimentdir/paramlog.xml -Xms512m -Xmx4096m"
      learnlib_params="-cexh Suffix1by1 -clos CloseFirst -cache -eq irfan -out $otdir_now"

      java $jvm_args -jar $experimentdir/Infer_LearnLib.jar -sul $sul             -sot   $learnlib_params -info "$sul - $s_val - $p_val - $v_val - $reval - Traditional"
      java $jvm_args -jar $experimentdir/Infer_LearnLib.jar -sul $prevsul         -sot   $learnlib_params -info "$prevsul - $s_val - $p_val - $v_val - $reval - Traditional"
      java $jvm_args -jar $experimentdir/Infer_LearnLib.jar -sul $newsul                 $learnlib_params -info "$newsul - $s_val - $p_val - $v_val - $reval - Traditional"
     
      java $jvm_args -jar $experimentdir/Infer_LearnLib.jar -sul $newsul -ot $otdir_now/v_000.fsm.ot     $learnlib_params -info "$newsul - $s_val - $p_val - $v_val - $reval - First"
      java $jvm_args -jar $experimentdir/Infer_LearnLib.jar -sul $newsul -ot $otdir_now/v_$v_prev.fsm.ot $learnlib_params -info "$newsul - $s_val - $p_val - $v_val - $reval - Previous"

      java $jvm_args -jar $experimentdir/Infer_LearnLib.jar -sul $newsul -ot $otdir_now/v_000.fsm.ot     $learnlib_params -info "$newsul - $s_val - $p_val - $v_val - $reval - First+proj"    -proj
      java $jvm_args -jar $experimentdir/Infer_LearnLib.jar -sul $newsul -ot $otdir_now/v_$v_prev.fsm.ot $learnlib_params -info "$newsul - $s_val - $p_val - $v_val - $reval - Previous+proj" -proj
      
   done
   # done
   processLog
done
done