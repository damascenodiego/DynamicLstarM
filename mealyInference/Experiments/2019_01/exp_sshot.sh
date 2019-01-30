#!/bin/bash

#PBS -N mqtt_ot
#PBS -l ncpus=1
#PBS -l walltime=96:00:00
#PBS -m ae
#PBS -M damascenodiego@usp.br

# for i in `seq 1 10`; do qsub -N "fase_r$i" -v "var=10" ./fase19.sh ; done

module load gcc/4.9.2 R/3.3.3 java-oracle/jdk1.8.0_65

my_dir=/home/damascdn/remote_euler/
cd $my_dir

for sul_fname in $my_dir/Benchmark/SSH/*.dot.fixed; do
	java -cp $my_dir/mylearn.jar br.usp.icmc.labes.mealyInference.utils.BuildOT -sul $sul_fname -dot
done
