#!/bin/sh

# rm ./experiments_*/fsm/fsm_*.log
# rm ./experiments_*/fsm/fsm_*.ot

for i in ./experiments_agm/fsm/fsm_agm_[0-9].txt ./experiments_bcs2/fsm/fsm_bcs2_[0-9].txt; do
	java -jar ./Infer_LearnLib.jar -sul $i -sot -cexh RivestSchapire -clos CloseFirst -cache -eq rndWalk
done

for i in ./experiments_agm/fsm/fsm_agm_[0-9].txt; do
	for j in ./experiments_agm/fsm/fsm_agm_[0-9].txt; do
		java -jar ./Infer_LearnLib.jar -sul $i -ot $j.ot -cexh RivestSchapire -clos CloseFirst -cache -eq rndWalk
	done
done

for i in ./experiments_bcs2/fsm/fsm_bcs2_[0-9].txt; do
	for j in ./experiments_bcs2/fsm/fsm_bcs2_[0-9].txt; do
		java -jar ./Infer_LearnLib.jar -sul $i -ot $j.ot -cexh RivestSchapire -clos CloseFirst -cache -eq rndWalk
	done
done


logdir=log_dir$(date +"%Y-%m-%d_%H-%M-%S")
mkdir $logdir/
for i in  ./experiments_*/fsm/fsm_*.log; do 
	echo $i  										|tee -a $logdir/$logdir.log
	grep "INFO: MQ \[resets\]"  $i 	| cut -d:  -f2- |tee -a $logdir/$logdir.log
	grep "INFO: MQ \[symbols\]" $i 	| cut -d:  -f2- |tee -a $logdir/$logdir.log
	grep "INFO: EQ \[resets\]"  $i 	| cut -d:  -f2- |tee -a $logdir/$logdir.log
	grep "INFO: EQ \[symbols\]" $i 	| cut -d:  -f2- |tee -a $logdir/$logdir.log
	grep "INFO: ERROR: " $i 		| cut -d:  -f2- |tee -a $logdir/$logdir.log
done

# logdir="log_dir2018-03-01_17-04-35"
# rm $logdir.log
# for i in  ./fsm_*.log; do 
# 	echo $i  										|tee -a $logdir.log
# 	grep "INFO: MQ \[resets\]"  $i 	| cut -d:  -f2- |tee -a $logdir.log
# 	grep "INFO: MQ \[symbols\]" $i 	| cut -d:  -f2- |tee -a $logdir.log
# 	grep "INFO: EQ \[resets\]"  $i 	| cut -d:  -f2- |tee -a $logdir.log
# 	grep "INFO: EQ \[symbols\]" $i 	| cut -d:  -f2- |tee -a $logdir.log
# 	grep "INFO: ERROR: " $i 		| cut -d:  -f2- |tee -a $logdir.log
# done


mv ./experiments_*/fsm/fsm_*.log $logdir/
mv ./experiments_*/fsm/fsm_*.ot  $logdir/