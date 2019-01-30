#!/bin/bash

#PBS -l ncpus=10
#PBS -l walltime=48:00:00
#PBS -m ae
#PBS -M damascenodiego@usp.br

# for i in `seq 1 10`; do qsub -N "fase_r$i" -v "var=10" ./fase19.sh ; done
# qsub -N "ssh_wwph" ./ssh.sh 
module load gcc/4.9.2 R/3.3.3 java-oracle/jdk1.8.0_65

my_dir=/home/damascdn/remote_euler/
cd $my_dir

runID=$(date +"%Y%m%d_%H%M%S_%N")

# for eqo in "wphyp" "whyp"; do
for eqo in "wphyp"; do
# for eqo in "rndWalk" "wrndhyp"; do
	for sul_fname in $my_dir/Benchmark/SSH/*.dot.fixed; do

		java -jar $my_dir/mylearn.jar -cache -cexh RivestSchapire -learn lstar -clos CloseFirst -eq $eqo -sul $sul_fname.kiss -out $my_dir/SSH/$runID/ &
		sleep 1s
		java -jar $my_dir/mylearn.jar -cache -cexh RivestSchapire -learn l1    -clos CloseFirst -eq $eqo -sul $sul_fname.kiss -out $my_dir/SSH/$runID/ &
		sleep 1s
		java -jar $my_dir/mylearn.jar -cache 					  -learn ttt 	  				-eq $eqo -sul $sul_fname.kiss -out $my_dir/SSH/$runID/ &
		sleep 1s
	done; wait


	for sul_i in $my_dir/Benchmark/SSH/*.dot.fixed; do
		for sul_j in $my_dir/Benchmark/SSH/*.dot.fixed; do
			if [[ $sul_i != $sul_j ]] ; 
			then
				java -jar $my_dir/mylearn.jar -cache -cexh RivestSchapire -learn adaptive  -clos CloseFirst -eq $eqo -sul $sul_i.kiss -ot $sul_j.ot -out $my_dir/SSH/$runID/ &
				sleep 1s
				java -jar $my_dir/mylearn.jar -cache -cexh RivestSchapire -learn dlstar_v0 -clos CloseFirst -eq $eqo -sul $sul_i.kiss -ot $sul_j.ot -out $my_dir/SSH/$runID/ &
				sleep 1s
				java -jar $my_dir/mylearn.jar -cache -cexh RivestSchapire -learn dlstar_v1 -clos CloseFirst -eq $eqo -sul $sul_i.kiss -ot $sul_j.ot -out $my_dir/SSH/$runID/ &
				sleep 1s
				java -jar $my_dir/mylearn.jar -cache -cexh RivestSchapire -learn dlstar_v2 -clos CloseFirst -eq $eqo -sul $sul_i.kiss -ot $sul_j.ot -out $my_dir/SSH/$runID/ &
				sleep 1s
			fi
		done; wait
	done 
 
done
# if [[ $var -eq 0 ]] ; 
# then
# 	var=1
# fi 
# echo "Number of repetitions set as $var" 
# for rep in `seq -f "%03g" 1 $var`; do
# 	for sul_fname in $my_dir/Benchmark/SSH/*.dot.fixed; do
# 		for eqo in "rndWalk" "wrndhyp"; do
# 			java -jar $my_dir/mylearn.jar -cache -cexh RivestSchapire -learn lstar -clos CloseFirst -eq $eqo -sul $sul_fname.kiss -out $my_dir/SSH/$runID/log_$rep
# 			java -jar $my_dir/mylearn.jar -cache -cexh RivestSchapire -learn l1    -clos CloseFirst -eq $eqo -sul $sul_fname.kiss -out $my_dir/SSH/$runID/log_$rep
# 			java -jar $my_dir/mylearn.jar -cache 					  -learn ttt 	  				-eq $eqo -sul $sul_fname.kiss -out $my_dir/SSH/$runID/log_$rep
# 		done
# 	done	
# 	for sul_i in $my_dir/Benchmark/SSH/*.dot.fixed; do
# 		for sul_j in $my_dir/Benchmark/SSH/*.dot.fixed; do
# 			if [[ $sul_i != $sul_j ]] ; 
# 			then
# 				for eqo in "rndWalk" "wrndhyp"; do
# 					java -jar $my_dir/mylearn.jar -cache -cexh RivestSchapire -learn adaptive  -clos CloseFirst -eq $eqo -sul $sul_i.kiss -ot $sul_j.ot -out $my_dir/SSH/$runID/log_$rep 
# 					java -jar $my_dir/mylearn.jar -cache -cexh RivestSchapire -learn dlstar_v1 -clos CloseFirst -eq $eqo -sul $sul_i.kiss -ot $sul_j.ot -out $my_dir/SSH/$runID/log_$rep
# 					java -jar $my_dir/mylearn.jar -cache -cexh RivestSchapire -learn dlstar_v2 -clos CloseFirst -eq $eqo -sul $sul_i.kiss -ot $sul_j.ot -out $my_dir/SSH/$runID/log_$rep
# 				done
# 			fi
# 		done
# 	done
# done