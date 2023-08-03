#tool versions
aiger_version=1.9.9
bloqqer_version=037-8660cb9-151127
caqe_version=4.0.2
cms_version=5.8.0
cvc_major_ver=5
cvc_minor_ver=1.8
depqbf_version=6.03
eprover_version=V_2.5
spot_version=2.9.7
ltl3ba_version=1.1.3
idq_version=1.0
nuSMV_version=v1.2#prebuild file version
pico_version=965
rareqs_version=1.1
z3_version=4.8.10


.PHONY: default debug release test tools required-tools optional-tools all clean distclean
.INTERMEDIATE: Tools/ltl3ba-$(ltl3ba_version).tar.gz Tools/bloqqer-$(bloqqer_version).tar.gz Tools/bloqqer-031-7a176af-110509.tar.gz Tools/cadet-bin.tar.gz Tools/caqe-bin.tar.gz Tools/cryptominisat-$(cms_version).tar.gz Tools/cvc$(cvc_major_ver)-$(cvc_minor_ver).tar.gz Tools/depqbf-$(depqbf_version).tar.gz Tools/spot-$(spot_version).tar.gz Tools/z3-$(z3_version).tar.gz Tools/rareqs-$(rareqs_version).src.tgz Tools/picosat-$(pico_version).tar.gz Tools/idq-$(idq_version).tar.gz Tools/vampire.zip Tools/E.tgz  Tools/aiger-$(aiger_version).tar.gz
.SECONDARY: Tools/abc-hg/abc Tools/abc-hg Tools/bloqqer-031-7a176af-110509 Tools/bloqqer-031-7a176af-110509/bloqqer Tools/bloqqer-$(bloqqer_version) Tools/bloqqer-$(bloqqer_version)/bloqqer Tools/ltl3ba Tools/ltl3ba-$(ltl3ba_version) Tools/ltl3ba-$(ltl3ba_version)/ltl3ba Tools/cryptominisat-$(cms_version) Tools/cryptominisat-$(cms_version)/build Tools/depqbf-version-$(depqbf_version)/depqbf Tools/depqbf-version-$(depqbf_version) Tools/quabs-git Tools/spot-$(spot_version) Tools/cvc$(cvc_major_ver)-$(cvc_minor_ver) Tools/cvc$(cvc_major_ver)-$(cvc_minor_ver)/builds/bin/cvc4 Tools/z3-$(z3_version)/build/z3 Tools/z3-$(z3_version) Tools/rareqs-$(rareqs_version) Tools/syfco-git Tools/syfco-git/syfco Tools/picosat-$(pico_version) Tools/picosat Tools/idq-$(idq_version) Tools/idq-$(idq_version)/idq Tools/aiger-$(aiger_version) Tools/aiger-$(aiger_version)/aigbmc Tools/aiger-$(aiger_version)/smvtoaig Tools/aiger-ltl-model-checker Tools/aiger-ltl-model-checker/combine-aiger

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
	rm -rf Tools/aiger-$(aiger_version)
	rm -rf Tools/abc-hg
	rm -rf Tools/ltl3ba-$(ltl3ba_version)
	rm -rf Tools/bloqqer-$(bloqqer_version)
	rm -rf Tools/bloqqer-031-7a176af-110509
	rm -rf Tools/cryptominisat-$(cms_version)
	rm -rf Tools/depqbf-version-$(depqbf_version)
	rm -rf Tools/spot-$(spot_version)
	rm -rf Tools/cvc$(cvc_major_ver)-$(cvc_minor_ver)
	rm -rf Tools/z3-$(z3_version)
	rm -rf Tools/rareqs-$(rareqs_version)
	rm -rf Tools/quabs-git
	rm -rf Tools/syfco-git
	rm -rf Tools/picosat-$(pico_version)
	rm -rf Tools/picosat
	rm -rf Tools/idq-$(idq_version)
	rm -rf Tools/NuSMV-$(nuSMV_version)
	rm -rf Tools/aiger-ltl-model-checker

distclean:
	swift package reset
	rm -rf Tools

tools: required-tools optional-tools

required-tools: \
	Tools/abc \
	Tools/bloqqer \
	Tools/bloqqer-031 \
	Tools/cadet \
	Tools/cryptominisat5 \
	Tools/ltl2tgba \
	Tools/ltl3ba \
	Tools/idq \
	Tools/quabs \
	Tools/rareqs \
	Tools/syfco \
	Tools/z3

optional-tools: \
	Tools/aigbmc \
	Tools/smvtoaig \
	Tools/caqe \
	Tools/combine-aiger \
	Tools/cvc4 \
	Tools/depqbf \
	Tools/eprover \
	Tools/picosat-solver \
	Tools/vampire \
	Tools/hqs \
	Tools/NuSMV \
	Tools/ltl2smv

Tools/.f:
	mkdir -p Tools
	touch Tools/.f

# abc
Tools/abc: Tools/abc-hg/abc
	cp Tools/abc-hg/abc Tools/abc

Tools/abc-hg/abc: Tools/abc-hg
	make -C Tools/abc-hg

Tools/abc-hg: Tools/.f
	cd Tools ; git clone https://github.com/berkeley-abc/abc.git abc-hg

# aiger
Tools/smvtoaig: Tools/aiger-$(aiger_version)/smvtoaig
	cp Tools/aiger-$(aiger_version)/smvtoaig Tools/smvtoaig

Tools/aiger-$(aiger_version)/smvtoaig: Tools/aiger-$(aiger_version)
	cd Tools/aiger-$(aiger_version) ; ./configure.sh
	make -C Tools/aiger-$(aiger_version) smvtoaig

Tools/aigbmc: Tools/aiger-$(aiger_version)/aigbmc
	cp Tools/aiger-$(aiger_version)/aigbmc Tools/aigbmc

Tools/aiger-$(aiger_version)/aigbmc: Tools/aiger-$(aiger_version) Tools/picosat/picosat.o
	cd Tools/aiger-$(aiger_version) ; ./configure.sh
	make -C Tools/aiger-$(aiger_version) aigbmc

Tools/aiger-$(aiger_version): Tools/aiger-$(aiger_version).tar.gz
	cd Tools ; tar xzf aiger-$(aiger_version).tar.gz

Tools/aiger-$(aiger_version).tar.gz: Tools/.f
	cd Tools ; curl -OL http://fmv.jku.at/aiger/aiger-$(aiger_version).tar.gz

# bloqqer
Tools/bloqqer: Tools/bloqqer-$(bloqqer_version)/bloqqer
	cp Tools/bloqqer-$(bloqqer_version)/bloqqer Tools/bloqqer

Tools/bloqqer-$(bloqqer_version)/bloqqer: Tools/bloqqer-$(bloqqer_version)
	cd Tools/bloqqer-$(bloqqer_version) ; ./configure
	make -C Tools/bloqqer-$(bloqqer_version)

Tools/bloqqer-$(bloqqer_version): Tools/bloqqer-$(bloqqer_version).tar.gz
	cd Tools ; tar xzf bloqqer-$(bloqqer_version).tar.gz

Tools/bloqqer-$(bloqqer_version).tar.gz: Tools/.f
	cd Tools ; curl -OL http://fmv.jku.at/bloqqer/bloqqer-$(bloqqer_version).tar.gz

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
Tools/caqe: Tools/caqe-src/target/release/caqe
	cp Tools/caqe-$(caqe_version)/target/release/caqe Tools/caqe
Tools/caqe-src/target/release/caqe: Tools/caqe-src
	cd Tools/caqe-$(caqe_version) && cargo build --release

Tools/caqe-src: Tools/caqe-src.tar.gz
	cd Tools && tar xzf caqe-src.tar.gz

Tools/caqe-src.tar.gz:
	cd Tools && curl -L -G -o caqe-src.tar.gz https://github.com/ltentrup/caqe/archive/$(caqe_version).tar.gz


# combine-aiger
Tools/combine-aiger: Tools/aiger-ltl-model-checker/combine-aiger
	cp Tools/aiger-ltl-model-checker/combine-aiger Tools/combine-aiger

Tools/aiger-ltl-model-checker/combine-aiger: Tools/aiger-ltl-model-checker
	make -C Tools/aiger-ltl-model-checker

Tools/aiger-ltl-model-checker:
	cd Tools ; git clone https://github.com/reactive-systems/aiger-ltl-model-checker.git

# cryptominisat
Tools/cryptominisat5: Tools/cryptominisat-$(cms_version)/build
	cp Tools/cryptominisat-$(cms_version)/build/cryptominisat5_simple Tools/cryptominisat5

Tools/cryptominisat-$(cms_version)/build: Tools/cryptominisat-$(cms_version)
	mkdir Tools/cryptominisat-$(cms_version)/build
	cd Tools/cryptominisat-$(cms_version)/build ; cmake -DCMAKE_BUILD_TYPE=Release -DSTATICCOMPILE=ON -DENABLE_PYTHON_INTERFACE=OFF ..
	cd Tools/cryptominisat-$(cms_version)/build ; make -j4

Tools/cryptominisat-$(cms_version): Tools/cryptominisat-$(cms_version).tar.gz
	cd Tools ; tar xzf cryptominisat-$(cms_version).tar.gz

Tools/cryptominisat-$(cms_version).tar.gz: Tools/.f
	cd Tools ; curl -OL https://github.com/msoos/cryptominisat/archive/$(cms_version).tar.gz
	mv Tools/$(cms_version).tar.gz Tools/cryptominisat-$(cms_version).tar.gz

# cvc4
Tools/cvc4: Tools/cvc$(cvc_major_ver)-$(cvc_minor_ver)/builds/bin/cvc4
	cp Tools/cvc$(cvc_major_ver)-$(cvc_minor_ver)/build/bin/cvc4 Tools/cvc4

Tools/cvc$(cvc_major_ver)-$(cvc_minor_ver)/builds/bin/cvc4: Tools/cvc$(cvc_major_ver)-$(cvc_minor_ver)
	cd Tools/cvc$(cvc_major_ver)-$(cvc_minor_ver) ; ./contrib/get-antlr-3.4
	cd Tools/cvc$(cvc_major_ver)-$(cvc_minor_ver) ; ./configure.sh production --static --static-binary #--best --enable-gpl
	make -j4 -C Tools/cvc$(cvc_major_ver)-$(cvc_minor_ver)/build

Tools/cvc$(cvc_major_ver)-$(cvc_minor_ver): Tools/cvc$(cvc_major_ver)-$(cvc_minor_ver).tar.gz
	cd Tools ; tar xzf cvc$(cvc_major_ver)-$(cvc_minor_ver).tar.gz

Tools/cvc$(cvc_major_ver)-$(cvc_minor_ver).tar.gz: Tools/.f
	cd Tools ; curl -OL https://github.com/cvc5/cvc5/archive/refs/tags/$(cvc_minor_ver).tar.gz
	mv Tools/$(cvc_minor_ver).tar.gz Tools/cvc$(cvc_major_ver)-$(cvc_minor_ver).tar.gz

# depqbf
Tools/depqbf: Tools/depqbf-version-$(depqbf_version)/depqbf
	cp Tools/depqbf-version-$(depqbf_version)/depqbf Tools/depqbf

Tools/depqbf-version-$(depqbf_version)/depqbf: Tools/depqbf-version-$(depqbf_version)
	cd Tools/depqbf-version-$(depqbf_version); ./compile.sh

Tools/depqbf-version-$(depqbf_version): Tools/depqbf-$(depqbf_version).tar.gz
	cd Tools ; tar xzf depqbf-$(depqbf_version).tar.gz

Tools/depqbf-$(depqbf_version).tar.gz: Tools/.f
	cd Tools ; curl -OL https://github.com/lonsing/depqbf/archive/version-$(depqbf_version).tar.gz
	mv Tools/version-$(depqbf_version).tar.gz Tools/depqbf-$(depqbf_version).tar.gz

# eprover
Tools/eprover: Tools/E
	cd Tools/E ; ./configure
	make -C Tools/E
	cp Tools/E/PROVER/eprover Tools/

Tools/E: Tools/E.tgz
	cd Tools ; tar xzf E.tgz

Tools/E.tgz: Tools/.f
	cd Tools ; curl -OL http://wwwlehre.dhbw-stuttgart.de/~sschulz/WORK/E_DOWNLOAD/$(eprover_version)/E.tgz

# vampire
Tools/vampire: Tools/vampire.zip
	cd Tools ; unzip -d vampire vampire.zip
Tools/vampire.zip: Tools/.f
	cd Tools ; curl -L -o vampire.zip https://github.com/vprover/vampire/releases/download/v4.7/vampire4.7.zip

# spot/ltl2tgba
Tools/ltl2tgba: Tools/spot-$(spot_version)
	cd Tools/spot-$(spot_version); ./configure --disable-python --enable-static --disable-shared
	cd Tools/spot-$(spot_version); make
	cp Tools/spot-$(spot_version)/bin/ltl2tgba Tools/

Tools/spot-$(spot_version): Tools/spot-$(spot_version).tar.gz
	cd Tools; tar xzf spot-$(spot_version).tar.gz

Tools/spot-$(spot_version).tar.gz: Tools/.f
	cd Tools; curl -OL http://www.lrde.epita.fr/dload/spot/spot-$(spot_version).tar.gz

# ltl3ba
Tools/ltl3ba: Tools/ltl3ba-$(ltl3ba_version)/ltl3ba
	cp Tools/ltl3ba-$(ltl3ba_version)/ltl3ba Tools/ltl3ba

Tools/ltl3ba-$(ltl3ba_version)/ltl3ba: Tools/ltl3ba-$(ltl3ba_version)
	cd Tools ; make -C ltl3ba-$(ltl3ba_version)

Tools/ltl3ba-$(ltl3ba_version): Tools/ltl3ba-$(ltl3ba_version).tar.gz
	cd Tools ; tar xzf ltl3ba-$(ltl3ba_version).tar.gz
	
Tools/ltl3ba-$(ltl3ba_version).tar.gz: Tools/.f
	cd Tools ; curl -OL https://sourceforge.net/projects/ltl3ba/files/ltl3ba/1.1/ltl3ba-$(ltl3ba_version).tar.gz

# idq
Tools/idq: Tools/idq-$(idq_version)/idq
	cp Tools/idq-$(idq_version)/idq Tools/idq

Tools/idq-$(idq_version)/idq: Tools/idq-$(idq_version)
	# patch makefile
	cd Tools/idq-$(idq_version) ; sed -i -e 's/-static//g' makefile
	# build
	make -C Tools/idq-$(idq_version)

Tools/idq-$(idq_version): Tools/idq-$(idq_version).tar.gz
	cd Tools ; tar xzf idq-$(idq_version).tar.gz

Tools/idq-$(idq_version).tar.gz: Tools/.f
	cd Tools ; curl -OL http://fmv.jku.at/idq/idq-$(idq_version).tar.gz

# hqs
Tools/hqs: Tools/hqs-bin/hqs
	cp Tools/hqs-bin/hqs Tools/hqs-linux
	cp Tools/hqs-bin/preprocess Tools/hqspre-linux

Tools/hqs-bin/hqs: Tools/hqs-bin.tar.gz
	cd Tools ; tar xzf hqs-bin.tar.gz

Tools/hqs-bin.tar.gz: Tools/.f
	cd Tools ; curl -OL -G -d dl=1 https://www.dropbox.com/s/cdesqq4ckh96x2i/hqs-bin.tar.gz

# NuSMV
Tools/NuSMV: Tools/NuSMV-$(nuSMV_version)/dl
	mv Tools/NuSMVa_linux64 Tools/NuSMV
	chmod +x Tools/NuSMV

Tools/ltl2smv:
	cd Tools ; curl -OL https://github.com/hklarner/NuSMV-a/releases/download/v1.2/ltl2smv
	chmod +x Tools/ltl2smv

Tools/NuSMV-$(nuSMV_version)/dl: Tools/.f
	cd Tools ; curl -OL https://github.com/hklarner/NuSMV-a/releases/download/v1.2/NuSMVa_linux64

# picosat
Tools/picosat-solver: Tools/picosat-$(pico_version)
	cd Tools/picosat-$(pico_version) ; ./configure.sh
	make -C Tools/picosat-$(pico_version) picosat
	cp Tools/picosat-$(pico_version)/picosat Tools/picosat-solver

Tools/picosat-$(pico_version): Tools/picosat-$(pico_version).tar.gz
	cd Tools ; tar xzf picosat-$(pico_version).tar.gz

Tools/picosat: Tools/picosat-$(pico_version)
	cd Tools ; ln -sf picosat-$(pico_version) picosat

Tools/picosat/picosat.o: Tools/picosat
	cd Tools/picosat ; ./configure.sh
	make -C Tools/picosat picosat.o

Tools/picosat-$(pico_version).tar.gz: Tools/.f
	cd Tools ; curl -OL http://fmv.jku.at/picosat/picosat-$(pico_version).tar.gz

# QuAbS
Tools/quabs: Tools/quabs-git/release/quabs
	cp Tools/quabs-git/release/quabs Tools/quabs

Tools/quabs-git/release/quabs: Tools/quabs-git
	cd Tools/quabs-git; mkdir -p release
	cd Tools/quabs-git/release ; cmake -DCMAKE_BUILD_TYPE=Release .. && make

Tools/quabs-git: Tools/.f
	cd Tools ; git clone --recurse-submodules https://github.com/reactive-systems/quabs.git quabs-git

# rareqs
Tools/rareqs: Tools/rareqs-$(rareqs_version)
	# apply patches
	patch -p1 --directory=Tools/rareqs-$(rareqs_version) -i ../../rareqs.patch
	# build
	make -C Tools/rareqs-$(rareqs_version)
	cp Tools/rareqs-$(rareqs_version)/rareqs Tools/rareqs

Tools/rareqs-$(rareqs_version): Tools/rareqs-$(rareqs_version).src.tgz
	cd Tools ; tar xzf rareqs-$(rareqs_version).src.tgz

Tools/rareqs-$(rareqs_version).src.tgz: Tools/.f
	cd Tools ; curl -OL http://sat.inesc-id.pt/~mikolas/sw/areqs/rareqs-$(rareqs_version).src.tgz

# syfco
Tools/syfco: Tools/syfco-git/syfco
	cp Tools/syfco-git/syfco Tools/syfco

Tools/syfco-git/syfco: Tools/syfco-git
	cd Tools/syfco-git ; stack setup
	cd Tools/syfco-git ; make

Tools/syfco-git: Tools/.f
	cd Tools ; git clone https://github.com/reactive-systems/syfco.git syfco-git

# z3
Tools/z3: Tools/z3-$(z3_version)/build/z3
	cp Tools/z3-$(z3_version)/build/z3 Tools/z3

Tools/z3-$(z3_version)/build/z3: Tools/z3-$(z3_version)
	cd Tools/z3-$(z3_version) ; ./configure
	make -C Tools/z3-$(z3_version)/build

Tools/z3-$(z3_version): Tools/z3-$(z3_version).tar.gz
	cd Tools ; tar xzf z3-$(z3_version).tar.gz
	cd Tools ; mv z3-z3-$(z3_version) z3-$(z3_version)

Tools/z3-$(z3_version).tar.gz: Tools/.f
	cd Tools ; curl -OL https://github.com/Z3Prover/z3/archive/z3-$(z3_version).tar.gz
