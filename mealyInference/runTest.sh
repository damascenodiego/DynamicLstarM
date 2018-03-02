#!/bin/sh

rm ./log4j/*.log
rm ./experiments_*/fsm/fsm_*.ot
rm ./experiments_*/fsm/fsm_*.sul
rm ./experiments_*/fsm/fsm_*.infer
rm ./experiments_*/fsm/fsm_*.final
rm ./experiments_*/fsm/fsm_*.reval


for i in ./experiments_agm/fsm/fsm_agm_[0-9].txt; do
   java -jar ./Infer_LearnLib.jar -sul $i -sot -cexh RivestSchapire -clos CloseFirst -cache -eq wp
   for j in ./experiments_agm/fsm/fsm_agm_[0-9].txt; do
      java -jar ./Infer_LearnLib.jar -sul $j -ot $i.ot -cexh RivestSchapire -clos CloseFirst -cache -eq wp
   done
done


for a in seq 1 30; do
   for i in ./experiments_agm/fsm/fsm_agm_[0-9].txt; do
      java -jar ./Infer_LearnLib.jar -sul $i -sot -cexh RivestSchapire -clos CloseFirst -cache -eq rndWalk
      for b in seq 1 30; do
         for j in ./experiments_agm/fsm/fsm_agm_[0-9].txt; do
            java -jar ./Infer_LearnLib.jar -sul $j -ot $i.ot -cexh RivestSchapire -clos CloseFirst -cache -eq rndWalk
         done
      done
   done
done

# for i in ./experiments_bcs2/fsm/fsm_bcs2_[0-9].txt; do
#    java -jar ./Infer_LearnLib.jar -sul $i -sot -cexh RivestSchapire -clos CloseFirst -cache -eq wp
#    for j in ./experiments_bcs2/fsm/fsm_bcs2_[0-9].txt; do
#       java -jar ./Infer_LearnLib.jar -sul $j -ot $i.ot -cexh RivestSchapire -clos CloseFirst -cache -eq wp
#    done
# done


logdir=log_dir$(date +"%Y-%m-%d_%H-%M-%S")
mkdir $logdir/
echo "SUL | Cache | Reuse | CloS | CExH | EqO | L(ms) | SCEx(ms) | MQ(Resets) | MQ(Symbols) | EQ(Resets) | EQ(Symbols) | " |tee log4j/log.tab
for i in  ./log4j/*.log; do
   line="" 
   line+=`grep "|SUL name"  $i                    | cut -d\|  -f2- | cut -d:  -f2- `; line+=" | "
   line+=`grep "|Cache"  $i                       | cut -d\|  -f2- | cut -d:  -f2- `; line+=" | "
   line+=`grep "|Reused OT:"  $i                  | cut -d\|  -f2- | cut -d:  -f2- `; line+=" | "
   line+=`grep "|ClosingStrategy: CloseFirst" $i  | cut -d\|  -f2- | cut -d:  -f2- `; line+=" | "
   line+=`grep "|ObservationTableCEXHandler:" $i  | cut -d\|  -f2- | cut -d:  -f2- `; line+=" | "
   line+=`grep "|EquivalenceOracle:"  $i          | cut -d\|  -f2- | cut -d:  -f2- `; line+=" | "
   line+=`grep "|Learning \[ms\]:"  $i              | cut -d\|  -f2- | cut -d:  -f2- `; line+=" | "
   line+=`grep "|Searching for counterexample \[ms\]" $i | cut -d\|  -f2- | cut -d:  -f2- `; line+=" | "
   line+=`grep "|MQ \[resets\]"  $i               | cut -d\|  -f2- | cut -d:  -f2- `; line+=" | "
   line+=`grep "|MQ \[symbols\]" $i               | cut -d\|  -f2- | cut -d:  -f2- `; line+=" | "
   line+=`grep "|EQ \[resets\]"  $i               | cut -d\|  -f2- | cut -d:  -f2- `; line+=" | "
   line+=`grep "|EQ \[symbols\]" $i               | cut -d\|  -f2- | cut -d:  -f2- `
   echo $line |tee -a log4j/log.tab
   # grep "ERROR: " $i                       | cut -d\|  -f2- |tee -a $logdir/$logdir.log
done

# # logdir="log_dir2018-03-01_17-04-35"
# # rm $logdir.log
# # for i in  ./fsm_*.log; do 
# #    echo $i                                |tee -a $logdir.log
# #    grep "INFO: MQ \[resets\]"  $i    | cut -d:  -f2- |tee -a $logdir.log
# #    grep "INFO: MQ \[symbols\]" $i    | cut -d:  -f2- |tee -a $logdir.log
# #    grep "INFO: EQ \[resets\]"  $i    | cut -d:  -f2- |tee -a $logdir.log
# #    grep "INFO: EQ \[symbols\]" $i    | cut -d:  -f2- |tee -a $logdir.log
# #    grep "INFO: ERROR: " $i       | cut -d:  -f2- |tee -a $logdir.log
# # done


mv ./log4j $logdir/
mv ./experiments_*/fsm/fsm_*.ot  $logdir/
mv ./experiments_*/fsm/fsm_*.sul  $logdir/
mv ./experiments_*/fsm/fsm_*.infer  $logdir/
mv ./experiments_*/fsm/fsm_*.final  $logdir/
mv ./experiments_*/fsm/fsm_*.reval  $logdir/
