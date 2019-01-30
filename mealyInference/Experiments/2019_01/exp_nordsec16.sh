#!/bin/bash

#PBS -l ncpus=30
#PBS -l walltime=96:00:00
#PBS -m ae
#PBS -M damascenodiego@usp.br

# for i in `seq 1 10`; do qsub -N "fase_r$i" -v "var=10" ./fase19.sh ; done
# qsub -N "nrd_wwph" ./nordsec16.sh 
module load gcc/4.9.2 R/3.3.3 java-oracle/jdk1.8.0_65

my_dir=/home/damascdn/remote_euler/
cd $my_dir

runID=$(date +"%Y%m%d_%H%M%S_%N")
# for rep in `seq -f "%03g" 1 $var`; do for eqo in "rndWalk" "wrndhyp"; do
# for eqo in "wphyp" "whyp"; do
for eqo in "wphyp"; do
	for side in "client" "server"; do
	for sul_fname in $my_dir/Benchmark/Nordsec16/$side"_"*.dot; do

		java -jar $my_dir/mylearn.jar -cache -cexh RivestSchapire -learn lstar -clos CloseFirst -eq $eqo -sul $sul_fname.kiss -out $my_dir/Nordsec16"_"$side/$runID/ &
		sleep 1s
		java -jar $my_dir/mylearn.jar -cache -cexh RivestSchapire -learn l1    -clos CloseFirst -eq $eqo -sul $sul_fname.kiss -out $my_dir/Nordsec16"_"$side/$runID/ &
		sleep 1s
		java -jar $my_dir/mylearn.jar -cache 					  -learn ttt 					-eq $eqo -sul $sul_fname.kiss -out $my_dir/Nordsec16"_"$side/$runID/ &
		sleep 1s
	done; wait
	done
	for side in "client" "server"; do
	for sul_i in $my_dir/Benchmark/Nordsec16/$side"_"*.dot; do
		for sul_j in $my_dir/Benchmark/Nordsec16/$side"_"*.dot; do
			if [[ $sul_i != $sul_j ]] ; 
			then
				java -jar $my_dir/mylearn.jar -cache -cexh RivestSchapire -learn adaptive  -clos CloseFirst -eq $eqo -sul $sul_i.kiss -ot $sul_j.ot -out $my_dir/Nordsec16"_"$side/$runID/ &
				sleep 1s
				java -jar $my_dir/mylearn.jar -cache -cexh RivestSchapire -learn dlstar_v0 -clos CloseFirst -eq $eqo -sul $sul_i.kiss -ot $sul_j.ot -out $my_dir/Nordsec16"_"$side/$runID/ &
				sleep 1s
				java -jar $my_dir/mylearn.jar -cache -cexh RivestSchapire -learn dlstar_v1 -clos CloseFirst -eq $eqo -sul $sul_i.kiss -ot $sul_j.ot -out $my_dir/Nordsec16"_"$side/$runID/ &
				sleep 1s
				java -jar $my_dir/mylearn.jar -cache -cexh RivestSchapire -learn dlstar_v2 -clos CloseFirst -eq $eqo -sul $sul_i.kiss -ot $sul_j.ot -out $my_dir/Nordsec16"_"$side/$runID/ &
				sleep 1s
			fi
		done; wait
	done
	done
done 
#done