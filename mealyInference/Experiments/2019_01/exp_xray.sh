#!/bin/bash

#PBS -N mqtt_ln
#PBS -l ncpus=1
#PBS -l walltime=48:00:00
#PBS -m ae
#PBS -M damascenodiego@usp.br

# for i in `seq 1 10`; do qsub -N "fase_r$i" -v "var=10" ./fase19.sh ; done

module load gcc/4.9.2 R/3.3.3 java-oracle/jdk1.8.0_65

my_dir=/home/damascdn/remote_euler/
cd $my_dir

# java -cp runcomparison.jar experiments.br.usp.icmc.labes.ExperimentNordsec16CreateOTs


if [[ $var -eq 0 ]] ; 
then
	var=1
fi 
echo "Number of repetitions set as $var" 
runID=$(date +"%Y%m%d_%H%M%S_%N")

for rep in `seq -f "%03g" 1 $var`; do
	for sul_fname in $my_dir/Benchmark/Xray/learnresult*.dot; do
		for eqo in "weq" "rndWalk" "w" "wrnd"; do
			java -jar $my_dir/mylearn.jar -cache -cexh RivestSchapire -learn lstar -clos CloseFirst -eq $eqo -sul $sul_fname.kiss -out $my_dir/XRAY/$runID/log_$rep
			java -jar $my_dir/mylearn.jar -cache -cexh RivestSchapire -learn l1    -clos CloseFirst -eq $eqo -sul $sul_fname.kiss -out $my_dir/XRAY/$runID/log_$rep
			java -jar $my_dir/mylearn.jar -cache 					  -learn ttt 	  				-eq $eqo -sul $sul_fname.kiss -out $my_dir/XRAY/$runID/log_$rep
		done
	done	
	for sul_i in $my_dir/Benchmark/Xray/learnresult*.dot; do
		for sul_j in $my_dir/Benchmark/Xray/learnresult*.dot; do
			if [[ $sul_i != $sul_j ]] ; 
			then
				for eqo in "weq" "rndWalk" "w" "wrnd"; do
					java -jar $my_dir/mylearn.jar -cache -cexh RivestSchapire -learn adaptive  -clos CloseFirst -eq $eqo -sul $sul_i.kiss -ot $sul_j.ot -out $my_dir/XRAY/$runID/log_$rep 
					java -jar $my_dir/mylearn.jar -cache -cexh RivestSchapire -learn dlstar_v1 -clos CloseFirst -eq $eqo -sul $sul_i.kiss -ot $sul_j.ot -out $my_dir/XRAY/$runID/log_$rep
					java -jar $my_dir/mylearn.jar -cache -cexh RivestSchapire -learn dlstar_v2 -clos CloseFirst -eq $eqo -sul $sul_i.kiss -ot $sul_j.ot -out $my_dir/XRAY/$runID/log_$rep
				done
			fi
		done
	done
done
