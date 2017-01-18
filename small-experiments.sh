#!/bin/bash

if [ ! -s Tools/runsolver ]
then
	echo "Downloading runsolver"
	curl -L https://www.cril.univ-artois.fr/~roussel/runsolver/runsolver-3.3.5.tar.bz2 --output Tools/runsolver-3.3.5.tar.bz2
	mkdir -p Tools/runsolver-src
	tar -xf Tools/runsolver-3.3.5.tar.bz2 --directory Tools/runsolver-src
	echo "Building runsolver"
	make -C ./Tools/runsolver-src/runsolver/src
	mv Tools/runsolver-src/runsolver/src/runsolver Tools/
fi

file="syntcomp2016-tlsf-synthesis/Parameterized/simple_arbiter_2.tlsf"


echo "Executing Benchmark $file with input-symbolic encoding"
./Tools/runsolver -w /dev/null -W 300 ./bosy.sh $file --backend input-symbolic
echo "Executing Benchmark $file with state-symbolic encoding"
./Tools/runsolver -w /dev/null -W 300 ./bosy.sh $file --backend state-symbolic
echo "Executing Benchmark $file with fully symbolic encoding"
./Tools/runsolver -w /dev/null -W 300 ./bosy.sh $file --backend symbolic
echo "Executing Benchmark $file with explicit encoding"
./Tools/runsolver -w /dev/null -W 300 ./bosy.sh $file --backend explicit
echo "Executing Benchmark $file with SMT encoding"
./Tools/runsolver -w /dev/null -W 300 ./bosy.sh $file --backend smt


echo "Executing Benchmark $file with state-symbolic encoding, EPR solver vampire"
./Tools/runsolver -w /dev/null -W 240 ./bosy.sh $file --backend state-symbolic --solver vampire --strategy linear
echo "Executing Benchmark $file with fully symbolic encoding, EPR solver vampire"
./Tools/runsolver -w /dev/null -W 240 ./bosy.sh $file --backend symbolic --solver vampire --strategy linear

echo "Executing Benchmark $file with state-symbolic encoding, EPR solver e-prover"
#./Tools/runsolver -w /dev/null -W 360 ./bosy.sh $file --backend state-symbolic --solver eprover --strategy linear
echo "Executing Benchmark $file with fully symbolic encoding, EPR solver e-prover"
#./Tools/runsolver -w /dev/null -W 360 ./bosy.sh $file --backend symbolic --solver eprover



