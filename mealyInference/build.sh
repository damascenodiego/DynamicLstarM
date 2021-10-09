#/bin/sh

# Source: https://maven.apache.org/guides/mini/guide-3rd-party-jars-local.html

mvn install:install-file -Dfile=lib/de.ovgu.featureide.lib.fm-v3.4.2.jar \
        -DgroupId='de.ovgu.featureide.lib' \
        -DartifactId='fm' \
        -Dversion='v3.4.2' \
        -Dpackaging=jar
mvn package

cp ./target/pdlstarm-0.0.1.jar ./pdlstarm.jar
cp ./target/pdlstarm-0.0.1.jar ../experiments/2021_07_pdlstar_benchmarking/scripts/pdlstarm.jar