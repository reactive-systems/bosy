.PHONY: default debug release test tools all clean distclean

default: debug

debug: tools
	swift build

release: tools
	swift build --configuration release

test:
	swift test

clean:
	swift build --clean

distclean:
	swift build --clean=dist
	rm -rf Tools

tools: \
	Tools/abc \
	Tools/bloqqer \
	Tools/eprover \
	Tools/ltl3ba \
	Tools/idq \
	Tools/picosat \
	Tools/rareqs \
	Tools/syfco \
	Tools/z3

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

# eprover
Tools/eprover: Tools/E
	cd Tools/E ; ./configure
	make -C Tools/E
	cp Tools/E/PROVER/eprover Tools/

Tools/E: tools/E.tgz
	cd Tools ; tar xzf E.tgz

tools/E.tgz: Tools/.f
	cd Tools ; curl -OL http://wwwlehre.dhbw-stuttgart.de/~sschulz/WORK/E_DOWNLOAD/V_1.9.1/E.tgz

# ltl3ba
Tools/ltl3ba: Tools/ltl3ba-1.1.3/ltl3ba
	cp Tools/ltl3ba-1.1.3/ltl3ba Tools/ltl3ba

Tools/ltl3ba-1.1.3/ltl3ba: Tools/ltl3ba-1.1.3
	cd Tools ; make -C ltl3ba-1.1.3

Tools/ltl3ba-1.1.3: Tools/ltl3ba-1.1.3.tar.gz
	cd Tools ; tar xvfz ltl3ba-1.1.3.tar.gz
	
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

# picosat
Tools/picosat: Tools/picosat-965
	cd Tools/picosat-965 ; ./configure.sh
	make -C Tools/picosat-965 picosat
	cp Tools/picosat-965/picosat Tools/picosat

Tools/picosat-965: Tools/picosat-965.tar.gz
	cd Tools ; tar xzf picosat-965.tar.gz

Tools/picosat-965.tar.gz: Tools/.f
	cd Tools ; curl -OL http://fmv.jku.at/picosat/picosat-965.tar.gz

# rareqs
Tools/rareqs: Tools/rareqs-1.1
	# apply patches
	cd Tools/rareqs-1.1/minisat/core ; sed -i -e 's/friend Lit mkLit(Var var, bool sign = false);/Lit mkLit(Var var, bool sign);/g' SolverTypes.h
	cd Tools/rareqs-1.1/minisat/core ; sed -i -e 's/inline  Lit  mkLit     (Var var, bool sign)/inline  Lit  mkLit     (Var var, bool sign = false)/g' SolverTypes.h
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
	make -C Tools/syfco-git

Tools/syfco-git: Tools/.f
	cd Tools ; git clone https://github.com/reactive-systems/syfco.git syfco-git

# z3
Tools/z3: Tools/z3-git
	cd Tools/z3-git ; ./configure
	make -C Tools/z3-git/build
	cp Tools/z3-git/build/z3 Tools/z3

Tools/z3-git: Tools/.f
	cd Tools ; git clone https://github.com/Z3Prover/z3.git z3-git

