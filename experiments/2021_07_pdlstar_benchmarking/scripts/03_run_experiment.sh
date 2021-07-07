#!/bin/bash

runID=$(date +"%Y%m%d_%H%M%S_%N")
totRep=100
eqo="wp"

cd ..
# create folder for the random OTs
mkdir -p ./results/
run_path=./results/run_$runID/
mkdir $run_path

# repeat the experiment "totRep" times
for (( repNum = 0; repNum < totRep; repNum++ )); do
    echo "Running experiment: Iteration $repNum"
    # and save the results in the folder "repNum"
    rep_path=$run_path/rep_$repNum/
    mkdir $rep_path
    # run the experments for each subject
    for SBJCT_DIR in ./subjects/*/;do
        subject_name=$(basename -- "$SBJCT_DIR")
        mkdir $rep_path/$subject_name
        subj_run_path=$rep_path/$subject_name/
        echo "Running experiment: Subject $subject_name"
        # for each version:
        for sul_i in $SBJCT_DIR/*.kiss; do
            # ...setup the SUL model   
            sul_basename=$(basename -- "$sul_i")
            sul_fname=$subj_run_path/$sul_basename".kiss"
            java -cp ./scripts/mylearn.jar br.usp.icmc.labes.mealyInference.utils.BuildOT -sul $sul_i -out $subj_run_path/ -mkot
            # and run traditional learning
            echo "Running experiment: Traditional learning $sul_basename"
            java -jar ./scripts/mylearn.jar -cache -cexh RivestSchapire -learn lstar -clos CloseFirst -eq $eqo -sul $sul_fname -out $subj_run_path/SUL_"${sul_basename%.*}"/lstar/
            java -jar ./scripts/mylearn.jar -cache -cexh RivestSchapire -learn l1    -clos CloseFirst -eq $eqo -sul $sul_fname -out $subj_run_path/SUL_"${sul_basename%.*}"/l1/
        done
        # for each reused version "sul_j":
        for sul_j in $SBJCT_DIR/*.kiss; do
            # ... create a random OT
            java -cp ./scripts/mylearn.jar br.usp.icmc.labes.mealyInference.utils.BuildOT -sul $sul_j -out $subj_run_path/ -mkot -rnd
            # and get the OT filename
            ot_basename=$(basename -- "$sul_j")
            ot_fname=$subj_run_path/$ot_basename".ot"
            # for each SUL version "sul_i":
            for sul_i in $SBJCT_DIR/*.kiss; do
                # get the SUL filename
                sul_basename=$(basename -- "$sul_i")
                sul_fname=$subj_run_path/$sul_basename".kiss"
                echo "Running experiment: Adaptive learning on $sul_basename by reusing $ot_basename"
                # and then run the adaptive algorithms
                java -jar ./scripts/mylearn.jar -cache -cexh RivestSchapire -learn adaptive  -clos CloseFirst -eq $eqo -sul $sul_fname -ot $ot_fname -out $subj_run_path/SUL_"${sul_basename%.*}"/adaptive/OT_"${ot_basename%.*}"/   -info "rep=$repNum" &
                # sleep 2s
                java -jar ./scripts/mylearn.jar -cache -cexh RivestSchapire -learn dlstar_v0 -clos CloseFirst -eq $eqo -sul $sul_fname -ot $ot_fname -out $subj_run_path/SUL_"${sul_basename%.*}"/dlstar_v0/OT_"${ot_basename%.*}"/  -info "rep=$repNum" &
                # sleep 2s
                java -jar ./scripts/mylearn.jar -cache -cexh RivestSchapire -learn dlstar_v1 -clos CloseFirst -eq $eqo -sul $sul_fname -ot $ot_fname -out $subj_run_path/SUL_"${sul_basename%.*}"/dlstar_v1/OT_"${ot_basename%.*}"/  -info "rep=$repNum" &
                # sleep 2s
                java -jar ./scripts/mylearn.jar -cache -cexh RivestSchapire -learn dlstar_v2 -clos CloseFirst -eq $eqo -sul $sul_fname -ot $ot_fname -out $subj_run_path/SUL_"${sul_basename%.*}"/dlstar_v2/OT_"${ot_basename%.*}"/  -info "rep=$repNum" &
                # sleep 2s
            done;
        done;
        # wait
    done
done