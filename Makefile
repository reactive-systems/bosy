.PHONY: default debug release test tools required-tools optional-tools all clean distclean
.INTERMEDIATE: Tools/ltl3ba-1.1.3.tar.gz Tools/bloqqer-037-8660cb9-151127.tar.gz Tools/bloqqer-031-7a176af-110509.tar.gz Tools/cadet-bin.tar.gz Tools/caqe-bin.tar.gz Tools/cryptominisat-5.0.1.tar.gz Tools/cvc4-1.5.tar.gz Tools/depqbf-5.01.tar.gz Tools/spot-2.3.5.tar.gz Tools/z3-4.5.0.tar.gz Tools/rareqs-1.1.src.tgz Tools/picosat-965.tar.gz Tools/idq-1.0.tar.gz Tools/quabs-bin.tar.gz Tools/vampire.zip Tools/E.tgz Tools/NuSMV-2.6.0.tar.gz Tools/aiger-1.9.9.tar.gz
.SECONDARY: Tools/abc-hg/abc Tools/abc-hg Tools/bloqqer-031-7a176af-110509 Tools/bloqqer-031-7a176af-110509/bloqqer Tools/bloqqer-037-8660cb9-151127 Tools/bloqqer-037-8660cb9-151127/bloqqer Tools/ltl3ba Tools/ltl3ba-1.1.3 Tools/ltl3ba-1.1.3/ltl3ba Tools/cryptominisat-5.0.1 Tools/cryptominisat-5.0.1/build Tools/depqbf-version-5.01/depqbf Tools/depqbf-version-5.01 Tools/spot-2.3.5 Tools/cvc4-1.5 Tools/cvc4-1.5/builds/bin/cvc4 Tools/z3-4.5.0/build/z3 Tools/z3-4.5.0 Tools/rareqs-1.1 Tools/syfco-git Tools/syfco-git/syfco Tools/picosat-965 Tools/picosat Tools/idq-1.0 Tools/idq-1.0/idq Tools/NuSMV-2.6.0 Tools/NuSMV-2.6.0/NuSMV/build/bin/NuSMV Tools/NuSMV-2.6.0/NuSMV/build/bin/ltl2smv Tools/aiger-1.9.9 Tools/aiger-1.9.9/aigbmc Tools/aiger-1.9.9/smvtoaig Tools/aiger-ltl-model-checker Tools/aiger-ltl-model-checker/combine-aiger

default: release

debug: required-tools
	swift build

release: required-tools
	swift build --configuration release -Xcc -O3 -Xcc -DNDEBUG -Xswiftc -Ounchecked

all: tools release

test:
	swift test

clean:
	swift package clean
	
clean-source-tools:
	rm -rf Tools/aiger-1.9.9
	rm -rf Tools/abc-hg
	rm -rf Tools/ltl3ba-1.1.3
	rm -rf Tools/bloqqer-037-8660cb9-151127
	rm -rf Tools/bloqqer-031-7a176af-110509
	rm -rf Tools/cryptominisat-5.0.1
	rm -rf Tools/depqbf-version-5.01
	rm -rf Tools/spot-2.3.5
	rm -rf Tools/cvc4-1.5
	rm -rf Tools/z3-4.5.0
	rm -rf Tools/rareqs-1.1
	rm -rf Tools/syfco-git
	rm -rf Tools/picosat-965
	rm -rf Tools/picosat
	rm -rf Tools/idq-1.0
	rm -rf Tools/NuSMV-2.6.0
	rm -rf Tools/aiger-ltl-model-checker

distclean:
	swift package reset
	rm -rf Tools

tools: required-tools optional-tools

required-tools: \
	Tools/abc \
	Tools/bloqqer \
	Tools/bloqqer-031 \
	Tools/cryptominisat5 \
	Tools/ltl2tgba \
	Tools/ltl3ba \
	Tools/idq \
	Tools/quabscm \
	Tools/rareqs \
	Tools/syfco \
	Tools/z3

optional-tools: \
	Tools/aigbmc \
	Tools/smvtoaig \
	Tools/cadet \
	Tools/caqem \
	Tools/combine-aiger \
	Tools/cvc4 \
	Tools/depqbf \
	Tools/eprover \
	Tools/ltl2smv \
	Tools/NuSMV \
	Tools/picosat-solver \
	Tools/vampire \
	Tools/hqs

Tools/.f:
	mkdir -p Tools
	touch Tools/.f

# abc
Tools/abc: Tools/abc-hg/abc
	cp Tools/abc-hg/abc Tools/abc

Tools/abc-hg/abc: Tools/abc-hg
	make -C Tools/abc-hg

Tools/abc-hg: Tools/.f
	cd Tools ; hg clone https://bitbucket.org/alanmi/abc abc-hg

# aiger
Tools/smvtoaig: Tools/aiger-1.9.9/smvtoaig
	cp Tools/aiger-1.9.9/smvtoaig Tools/smvtoaig

Tools/aiger-1.9.9/smvtoaig: Tools/aiger-1.9.9
	cd Tools/aiger-1.9.9 ; ./configure.sh
	make -C Tools/aiger-1.9.9 smvtoaig

Tools/aigbmc: Tools/aiger-1.9.9/aigbmc
	cp Tools/aiger-1.9.9/aigbmc Tools/aigbmc

Tools/aiger-1.9.9/aigbmc: Tools/aiger-1.9.9 Tools/picosat/picosat.o
	cd Tools/aiger-1.9.9 ; ./configure.sh
	make -C Tools/aiger-1.9.9 aigbmc

Tools/aiger-1.9.9: Tools/aiger-1.9.9.tar.gz
	cd Tools ; tar xzf aiger-1.9.9.tar.gz

Tools/aiger-1.9.9.tar.gz: Tools/.f
	cd Tools ; curl -OL http://fmv.jku.at/aiger/aiger-1.9.9.tar.gz

# bloqqer
Tools/bloqqer: Tools/bloqqer-037-8660cb9-151127/bloqqer
	cp Tools/bloqqer-037-8660cb9-151127/bloqqer Tools/bloqqer

Tools/bloqqer-037-8660cb9-151127/bloqqer: Tools/bloqqer-037-8660cb9-151127
	cd Tools/bloqqer-037-8660cb9-151127 ; ./configure
	make -C Tools/bloqqer-037-8660cb9-151127

Tools/bloqqer-037-8660cb9-151127: Tools/bloqqer-037-8660cb9-151127.tar.gz
	cd Tools ; tar xzf bloqqer-037-8660cb9-151127.tar.gz

Tools/bloqqer-037-8660cb9-151127.tar.gz: Tools/.f
	cd Tools ; curl -OL http://fmv.jku.at/bloqqer/bloqqer-037-8660cb9-151127.tar.gz

Tools/bloqqer-031: Tools/bloqqer-031-7a176af-110509/bloqqer
	cp Tools/bloqqer-031-7a176af-110509/bloqqer Tools/bloqqer-031

Tools/bloqqer-031-7a176af-110509/bloqqer: Tools/bloqqer-031-7a176af-110509
	cd Tools/bloqqer-031-7a176af-110509 ; ./configure
	make -C Tools/bloqqer-031-7a176af-110509

Tools/bloqqer-031-7a176af-110509: Tools/bloqqer-031-7a176af-110509.tar.gz
	cd Tools ; tar xzf bloqqer-031-7a176af-110509.tar.gz

Tools/bloqqer-031-7a176af-110509.tar.gz: Tools/.f
	cd Tools ; curl -OL http://fmv.jku.at/bloqqer/bloqqer-031-7a176af-110509.tar.gz

# cadet
Tools/cadet: Tools/cadet-git/cadet
	cp Tools/cadet-git/cadet Tools/

Tools/cadet-git/cadet: Tools/cadet-git
	cd Tools/cadet-git ; ./configure
	make -C Tools/cadet-git

Tools/cadet-git: Tools/.f
	cd Tools ; git clone https://github.com/MarkusRabe/cadet.git cadet-git

# caqe
Tools/caqem: Tools/caqe-bin
	cp Tools/caqe-bin/caqem Tools/caqem

Tools/caqe-bin: Tools/caqe-bin.tar.gz
	cd Tools ; tar xzf caqe-bin.tar.gz

Tools/caqe-bin.tar.gz: Tools/.f
	cd Tools ; curl -OL -G -d dl=1 https://www.dropbox.com/s/8a0c61ua2w6glik/caqe-bin.tar.gz

# combine-aiger
Tools/combine-aiger: Tools/aiger-ltl-model-checker/combine-aiger
	cp Tools/aiger-ltl-model-checker/combine-aiger Tools/combine-aiger

Tools/aiger-ltl-model-checker/combine-aiger: Tools/aiger-ltl-model-checker
	make -C Tools/aiger-ltl-model-checker

Tools/aiger-ltl-model-checker:
	cd Tools ; git clone https://github.com/reactive-systems/aiger-ltl-model-checker.git

# cryptominisat
Tools/cryptominisat5: Tools/cryptominisat-5.0.1/build
	cp Tools/cryptominisat-5.0.1/build/cryptominisat5_simple Tools/cryptominisat5

Tools/cryptominisat-5.0.1/build: Tools/cryptominisat-5.0.1
	mkdir Tools/cryptominisat-5.0.1/build
	cd Tools/cryptominisat-5.0.1/build ; cmake -DCMAKE_BUILD_TYPE=Release -DSTATICCOMPILE=ON ..
	cd Tools/cryptominisat-5.0.1/build ; make -j4

Tools/cryptominisat-5.0.1: Tools/cryptominisat-5.0.1.tar.gz
	cd Tools ; tar xzf cryptominisat-5.0.1.tar.gz

Tools/cryptominisat-5.0.1.tar.gz: Tools/.f
	cd Tools ; curl -OL https://github.com/msoos/cryptominisat/archive/5.0.1.tar.gz
	mv Tools/5.0.1.tar.gz Tools/cryptominisat-5.0.1.tar.gz

# cvc4
Tools/cvc4: Tools/cvc4-1.5/builds/bin/cvc4
	cp Tools/cvc4-1.5/builds/bin/cvc4 Tools/cvc4

Tools/cvc4-1.5/builds/bin/cvc4: Tools/cvc4-1.5
	cd Tools/cvc4-1.5 ; ./configure --enable-static-binary MAC_STATIC_BINARY_MANUAL_OVERRIDE=1 #--best --enable-gpl
	make -j4 -C Tools/cvc4-1.5

Tools/cvc4-1.5: Tools/cvc4-1.5.tar.gz
	cd Tools ; tar xzf cvc4-1.5.tar.gz

Tools/cvc4-1.5.tar.gz: Tools/.f
	cd Tools ; curl -OL http://cvc4.cs.stanford.edu/downloads/builds/src/cvc4-1.5.tar.gz

# depqbf
Tools/depqbf: Tools/depqbf-version-5.01/depqbf
	cp Tools/depqbf-version-5.01/depqbf Tools/depqbf

Tools/depqbf-version-5.01/depqbf: Tools/depqbf-version-5.01
	make -C Tools/depqbf-version-5.01

Tools/depqbf-version-5.01: Tools/depqbf-5.01.tar.gz
	cd Tools ; tar xzf depqbf-5.01.tar.gz

Tools/depqbf-5.01.tar.gz: Tools/.f
	cd Tools ; curl -OL https://github.com/lonsing/depqbf/archive/version-5.01.tar.gz
	mv Tools/version-5.01.tar.gz Tools/depqbf-5.01.tar.gz

# eprover
Tools/eprover: Tools/E
	cd Tools/E ; ./configure
	make -C Tools/E
	cp Tools/E/PROVER/eprover Tools/

Tools/E: Tools/E.tgz
	cd Tools ; tar xzf E.tgz

Tools/E.tgz: Tools/.f
	cd Tools ; curl -OL http://wwwlehre.dhbw-stuttgart.de/~sschulz/WORK/E_DOWNLOAD/V_1.9.1/E.tgz

# vampire
Tools/vampire: Tools/Vampires
	cp Tools/Vampires/vampire_x86_64 Tools/vampire
Tools/Vampires: Tools/vampire.zip
	cd Tools ; unzip -D vampire.zip
Tools/vampire.zip: Tools/.f
	cd Tools ; curl -OL http://forsyte.at/wp-content/uploads/vampire.zip

# spot/ltl2tgba
Tools/ltl2tgba: Tools/spot-2.3.5
	cd Tools/spot-2.3.5; ./configure --disable-python --enable-static --disable-shared
	cd Tools/spot-2.3.5; make
	cp Tools/spot-2.3.5/bin/ltl2tgba Tools/

Tools/spot-2.3.5: Tools/spot-2.3.5.tar.gz
	cd Tools; tar xzf spot-2.3.5.tar.gz

Tools/spot-2.3.5.tar.gz: Tools/.f
	cd Tools; curl -OL http://www.lrde.epita.fr/dload/spot/spot-2.3.5.tar.gz

# ltl3ba
Tools/ltl3ba: Tools/ltl3ba-1.1.3/ltl3ba
	cp Tools/ltl3ba-1.1.3/ltl3ba Tools/ltl3ba

Tools/ltl3ba-1.1.3/ltl3ba: Tools/ltl3ba-1.1.3
	cd Tools ; make -C ltl3ba-1.1.3

Tools/ltl3ba-1.1.3: Tools/ltl3ba-1.1.3.tar.gz
	cd Tools ; tar xzf ltl3ba-1.1.3.tar.gz
	
Tools/ltl3ba-1.1.3.tar.gz: Tools/.f
	cd Tools ; curl -OL https://sourceforge.net/projects/ltl3ba/files/ltl3ba/1.1/ltl3ba-1.1.3.tar.gz

# idq
Tools/idq: Tools/idq-1.0/idq
	cp Tools/idq-1.0/idq Tools/idq

Tools/idq-1.0/idq: Tools/idq-1.0
	# patch makefile
	cd Tools/idq-1.0 ; sed -i -e 's/-static//g' makefile
	# build
	make -C Tools/idq-1.0

Tools/idq-1.0: Tools/idq-1.0.tar.gz
	cd Tools ; tar xzf idq-1.0.tar.gz

Tools/idq-1.0.tar.gz: Tools/.f
	cd Tools ; curl -OL http://fmv.jku.at/idq/idq-1.0.tar.gz

# hqs
Tools/hqs: Tools/hqs-bin/hqs
	cp Tools/hqs-bin/hqs Tools/hqs-linux
	cp Tools/hqs-bin/preprocess Tools/hqspre-linux

Tools/hqs-bin/hqs: Tools/hqs-bin.tar.gz
	cd Tools ; tar xzf hqs-bin.tar.gz

Tools/hqs-bin.tar.gz: Tools/.f
	cd Tools ; curl -OL -G -d dl=1 https://www.dropbox.com/s/cdesqq4ckh96x2i/hqs-bin.tar.gz

# NuSMV
Tools/NuSMV: Tools/NuSMV-2.6.0/NuSMV/build/bin/NuSMV
	cp Tools/NuSMV-2.6.0/NuSMV/build/bin/NuSMV Tools/NuSMV

Tools/NuSMV-2.6.0/NuSMV/build/bin/NuSMV: Tools/NuSMV-2.6.0
	cd Tools/NuSMV-2.6.0/NuSMV ; mkdir build
	cd Tools/NuSMV-2.6.0/NuSMV/build ; cmake .. && make

Tools/ltl2smv: Tools/NuSMV-2.6.0/NuSMV/build/bin/ltl2smv
	cp Tools/NuSMV-2.6.0/NuSMV/build/bin/ltl2smv Tools/ltl2smv

Tools/NuSMV-2.6.0/NuSMV/build/bin/ltl2smv: Tools/NuSMV-2.6.0
	cd Tools/NuSMV-2.6.0/NuSMV ; mkdir build
	cd Tools/NuSMV-2.6.0/NuSMV/build ; cmake .. && make

Tools/NuSMV-2.6.0: Tools/NuSMV-2.6.0.tar.gz
	cd Tools ; tar xzf NuSMV-2.6.0.tar.gz

Tools/NuSMV-2.6.0.tar.gz: Tools/.f
	cd Tools ; curl -OL http://nusmv.fbk.eu/distrib/NuSMV-2.6.0.tar.gz

# picosat
Tools/picosat-solver: Tools/picosat-965
	cd Tools/picosat-965 ; ./configure.sh
	make -C Tools/picosat-965 picosat
	cp Tools/picosat-965/picosat Tools/picosat-solver

Tools/picosat-965: Tools/picosat-965.tar.gz
	cd Tools ; tar xzf picosat-965.tar.gz

Tools/picosat: Tools/picosat-965
	cd Tools ; ln -sf picosat-965 picosat

Tools/picosat/picosat.o: Tools/picosat
	cd Tools/picosat ; ./configure.sh
	make -C Tools/picosat picosat.o

Tools/picosat-965.tar.gz: Tools/.f
	cd Tools ; curl -OL http://fmv.jku.at/picosat/picosat-965.tar.gz

# QuAbS
Tools/quabscm: Tools/quabs-bin
	cp Tools/quabs-bin/quabscm Tools/quabscm

Tools/quabs-bin: Tools/quabs-bin.tar.gz
	cd Tools ; tar xzf quabs-bin.tar.gz

Tools/quabs-bin.tar.gz: Tools/.f
	cd Tools ; curl -OL -G -d dl=1 https://www.dropbox.com/s/zfkfj3f4uns5de5/quabs-bin.tar.gz

# rareqs
Tools/rareqs: Tools/rareqs-1.1
	# apply patches
	patch -p1 --directory=Tools/rareqs-1.1 -i ../../rareqs.patch
	# build
	make -C Tools/rareqs-1.1
	cp Tools/rareqs-1.1/rareqs Tools/rareqs

Tools/rareqs-1.1: Tools/rareqs-1.1.src.tgz
	cd Tools ; tar xzf rareqs-1.1.src.tgz

Tools/rareqs-1.1.src.tgz: Tools/.f
	cd Tools ; curl -OL http://sat.inesc-id.pt/~mikolas/sw/areqs/rareqs-1.1.src.tgz

# syfco
Tools/syfco: Tools/syfco-git/syfco
	cp Tools/syfco-git/syfco Tools/syfco

Tools/syfco-git/syfco: Tools/syfco-git
	cd Tools/syfco-git ; stack setup
	cd Tools/syfco-git ; make

Tools/syfco-git: Tools/.f
	cd Tools ; git clone https://github.com/reactive-systems/syfco.git syfco-git

# z3
Tools/z3: Tools/z3-4.5.0/build/z3
	cp Tools/z3-4.5.0/build/z3 Tools/z3

Tools/z3-4.5.0/build/z3: Tools/z3-4.5.0
	cd Tools/z3-4.5.0 ; ./configure
	make -C Tools/z3-4.5.0/build

Tools/z3-4.5.0: Tools/z3-4.5.0.tar.gz
	cd Tools ; tar xzf z3-4.5.0.tar.gz
	cd Tools ; mv z3-z3-4.5.0 z3-4.5.0

Tools/z3-4.5.0.tar.gz: Tools/.f
	cd Tools ; curl -OL https://github.com/Z3Prover/z3/archive/z3-4.5.0.tar.gz

