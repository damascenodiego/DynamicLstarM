

mkdir old
mv ./SSH  old
mv ./TCP  old
mv ./MQTT  old
mv ./Nordsec16 old
mv ./XRAY old
mv ./logs old

rm -rf old &

./sshot.sh
./tcpot.sh
./mqttot.sh
./fase19ot.sh

for i in `seq 01 05`; do qsub -N "ssh$i" 	-v "var=6" ./ssh.sh  ; done
for i in `seq 01 05`; do qsub -N "tcp$i" 	-v "var=6" ./tcp.sh  ; done
for i in `seq 01 05`; do qsub -N "mqtt$i" 	-v "var=6" ./mqtt.sh  ; done
for i in `seq 01 05`; do qsub -N "fase$i" 	-v "var=6" ./fase19.sh  ; done

find $PWD/SSH/  -iname "*.log" | java -cp ./mylearn.jar br.usp.icmc.labes.mealyInference.utils.ProcessLogFiles > ./ssh.tab &
find $PWD/TCP/  -iname "*.log" | java -cp ./mylearn.jar br.usp.icmc.labes.mealyInference.utils.ProcessLogFiles > ./tcp.tab &
find $PWD/MQTT/  -iname "*.log" | java -cp ./mylearn.jar br.usp.icmc.labes.mealyInference.utils.ProcessLogFiles > ./mqtt.tab &
find $PWD/Nordsec16/  -iname "*.log" | java -cp ./mylearn.jar br.usp.icmc.labes.mealyInference.utils.ProcessLogFiles > ./nordsec16.tab &