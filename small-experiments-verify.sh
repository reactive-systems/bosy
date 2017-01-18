
#!/bin/bash

if [ ! -s Tools/NuSMV ]
then
	echo "Downloading NuSMV binary"
	curl -L http://nusmv.fbk.eu/distrib/NuSMV-2.6.0-linux64.tar.gz --output Tools/NuSMV-2.6.0-linux64.tar.gz
	tar -xf Tools/NuSMV-2.6.0-linux64.tar.gz --directory Tools/
	cp Tools/NuSMV-2.6.0-Linux/bin/NuSMV Tools/NuSMV
fi

file="syntcomp2016-tlsf-synthesis/Parameterized/simple_arbiter_2.tlsf"

echo "Executing Benchmark $file with input-symbolic encoding, synthesis, size determination"
./bosy.sh $file --backend input-symbolic --synthesize --target smv > /tmp/synthesized_result.smv 

./Tools/syfco -f smv $file | grep LTLSPEC  >> /tmp/synthesized_result.smv

echo "Verifying result"
./Tools/NuSMV /tmp/synthesized_result.smv
