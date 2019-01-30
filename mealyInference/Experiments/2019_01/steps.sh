find $PWD/SSH/  -iname "*.log" | java -cp ./mylearn.jar br.usp.icmc.labes.mealyInference.utils.ProcessLogFiles > ./ssh.tab &
find $PWD/MQTT/  -iname "*.log" | java -cp ./mylearn.jar br.usp.icmc.labes.mealyInference.utils.ProcessLogFiles > ./mqtt.tab &
find $PWD/Nordsec16_client/  -iname "*.log" | java -cp ./mylearn.jar br.usp.icmc.labes.mealyInference.utils.ProcessLogFiles > ./nordsec16_client.tab &
find $PWD/Nordsec16_server/  -iname "*.log" | java -cp ./mylearn.jar br.usp.icmc.labes.mealyInference.utils.ProcessLogFiles > ./nordsec16_server.tab &


mkdir old
mv ./[STMNX]*  old
mv ./*.[oe]*  old
mv ./logs old
#mv ./*.tab old
rm -rf old &

./sshot.sh
./mqttot.sh
./fase19ot.sh

#for i in `seq 01 05`; do qsub -N "ssh$i" 	-v "var=6" ./ssh.sh  ; done
#for i in `seq 01 05`; do qsub -N "mqtt$i" 	-v "var=6" ./mqtt.sh  ; done
#for i in `seq 01 05`; do qsub -N "fase$i" 	-v "var=6" ./fase19.sh  ; done

#for i in `seq 01 05`; do qsub -N "tcp$i" 	-v "var=6" ./tcp.sh  ; done
#./tcpot.sh
# qsub -N "tcp_wwph" ./tcp.sh 
#find $PWD/TCP/  -iname "*.log" | java -cp ./mylearn.jar br.usp.icmc.labes.mealyInference.utils.ProcessLogFiles > ./tcp.tab &


qsub -N "wwph_ssh" ./exp_ssh.sh 
qsub -N "wwph_mqt" ./exp_mqtt.sh 
qsub -N "wwph_nrd" ./exp_nordsec16.sh 
