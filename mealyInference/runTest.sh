#!/bin/sh

rm ./log4j/*.log
rm ./experiments_*/fsm/fsm_*.ot
rm ./experiments_*/fsm/fsm_*.sul
rm ./experiments_*/fsm/fsm_*.infer
rm ./experiments_*/fsm/fsm_*.final
rm ./experiments_*/fsm/fsm_*.reval


for i in ./experiments_agm/fsm/fsm_agm_[0-9].txt; do
   java -jar ./Infer_LearnLib.jar -sul $i -sot -cexh RivestSchapire -clos CloseFirst -cache -eq wp
   for j    in ./experiments_agm/fsm/fsm_agm_[0-9].txt; do
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

echo "SUL\tCache\tReuse\tCloS\tCExH\tEqO\tL(ms)\tSCEx(ms)\tMQ(Resets)\tMQ(Symbols)\tEQ(Resets)\tEQ(Symbols)\t" |tee log4j/log.tab
for i in  ./log4j/*.log; do
   line=`grep "|SUL name"  $i                                       | cut -d\|  -f2- | cut -d:  -f2- `
   line="${line}\t"`grep "|Cache"  $i                               | cut -d\|  -f2- | cut -d:  -f2- `
   line="${line}\t"`grep "|Reused OT:"  $i                          | cut -d\|  -f2- | cut -d:  -f2- `
   line="${line}\t"`grep "|ClosingStrategy: CloseFirst" $i          | cut -d\|  -f2- | cut -d:  -f2- `
   line="${line}\t"`grep "|ObservationTableCEXHandler:" $i          | cut -d\|  -f2- | cut -d:  -f2- `
   line="${line}\t"`grep "|EquivalenceOracle:"  $i                  | cut -d\|  -f2- | cut -d:  -f2- `
   line="${line}\t"`grep "|Learning \[ms\]:"  $i                    | cut -d\|  -f2- | cut -d:  -f2- `
   line="${line}\t"`grep "|Rounds:"  $i                             | cut -d\|  -f2- | cut -d:  -f2- `
   line="${line}\t"`grep "|Searching for counterexample \[ms\]" $i  | cut -d\|  -f2- | cut -d:  -f2- `
   line="${line}\t"`grep "|MQ \[resets\]"  $i                       | cut -d\|  -f2- | cut -d:  -f2- `
   line="${line}\t"`grep "|MQ \[symbols\]" $i                       | cut -d\|  -f2- | cut -d:  -f2- `
   line="${line}\t"`grep "|EQ \[resets\]"  $i                       | cut -d\|  -f2- | cut -d:  -f2- `
   line="${line}\t"`grep "|EQ \[symbols\]" $i                       | cut -d\|  -f2- | cut -d:  -f2- `
   line="${line}\t"`grep "|Number of states: " $i                   | cut -d\|  -f2- | cut -d:  -f2- `
   echo $line |tee -a log4j/log.tab
done
sed -i "s/\t\ /\t/g" ./log4j/log.tab

mv ./log4j $logdir/
mv ./experiments_*/fsm/fsm_*.ot  $logdir/
mv ./experiments_*/fsm/fsm_*.sul  $logdir/
mv ./experiments_*/fsm/fsm_*.infer  $logdir/
mv ./experiments_*/fsm/fsm_*.final  $logdir/
mv ./experiments_*/fsm/fsm_*.reval  $logdir/

