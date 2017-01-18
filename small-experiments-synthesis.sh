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


echo "Executing Benchmark $file with explicit encoding, synthesis"
./Tools/runsolver -w /dev/null -W 120 ./bosy.sh $file --backend explicit --synthesize --target dot | xdot - 
echo "Executing Benchmark $file with input-symbolic encoding, synthesis"
./Tools/runsolver -w /dev/null -W 120 ./bosy.sh $file --backend input-symbolic --synthesize --target dot | xdot - 

echo "Executing Benchmark $file with explicit encoding, synthesis, size determination"
./Tools/runsolver -w /dev/null -W 120 ./bosy.sh $file --backend explicit --synthesize --target aiger | ./aigstat.py

echo "Executing Benchmark $file with input-symbolic encoding, synthesis, size determination"
./Tools/runsolver -w /dev/null -W 120 ./bosy.sh $file --backend input-symbolic --synthesize --target aiger | ./aigstat.py
