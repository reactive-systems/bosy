#!/bin/bash

PATH_TO_RUNSOLVER="Tools/runsolver"

if [ ! -s $PATH_TO_RUNSOLVER ]
then
	echo "Downloading runsolver"
	curl -L https://www.cril.univ-artois.fr/~roussel/runsolver/runsolver-3.3.5.tar.bz2 --output Tools/runsolver-3.3.5.tar.bz2
	mkdir -p Tools/runsolver-src
	tar -xf Tools/runsolver-3.3.5.tar.bz2 --directory Tools/runsolver-src
	echo "Building runsolver"
	make -C ./Tools/runsolver-src/runsolver/src
	mv Tools/runsolver-src/runsolver/src/runsolver .
fi

# find . -type f -name '*.tlsf' -print0 | while IFS= read -r -d '' file; do
# 	printf 'Executing Benchmark: %s\n' "$file"
# 	#timeout 3600s
# 	time ./Tools/syfco "$file" -f bosy | .build/debug/BoSy
# done
