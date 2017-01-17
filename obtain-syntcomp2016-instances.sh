#!/bin/bash

if  [ ! -s syntcomp2017-tlsf-synthesis-instances.tar ]
then
	curl http://syntcomp.cs.uni-saarland.de/syntcomp2016/experiment/7/download-instances -o syntcomp2016-tlsf-synthesis-instances.tar
	tar xf syntcomp2016-tlsf-synthesis-instances.tar --strip 1
	mv "SYNTCOMP2016 - TLSF" syntcomp2016-tlsf-synthesis
	find . -name *.lzma -exec unxz {} \;
fi

