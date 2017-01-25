# BoSy Artifact Evaluation

We provide an Ubuntu 16.04 LTS 64-bit VM with a single user `cav` and password `ae`. The machine runs best with 2 vCores and at least 4GB RAM. 


## Getting Started

The source code of BoSy is located under `~/Desktop/BoSy`.
All dependencies necessary to build BoSy are already installed, executing `make` produces the BoSy binary. 
The external solvers are located under `~/Desktop/BoSy/Tools` and have been built from sources or use binaries from their respective websites. `make required-tools` and `make optional-tools` will perform the necessary download and compile steps, which we have executed already. To save space, we have removed intermediate build files and sources for the solvers from the VM.


## Benchmarks

BoSy supports the SYNTCOMP TLSF benchmark format via the conversion tool `syfco`.
The SYNTCOMP benchmarks can be downloaded from the official website by calling the script `obtain-syntcomp2016-instances.sh`.
The helper script `bosy.sh` does the conversion, i.e., accepts TLSF inputs.
An example call is

    ./bosy.sh syntcomp2016-tlsf-synthesis/Parameterized/simple_arbiter_2.tlsf

and should terminate with `realizable`.
BoSy supports the following command line options:
   --synthesize		construct solution after realizability
   --statistics		display solving statistics
   --strategy linear|exponential
   --player both|system|environment
   --backend explicit|input-symbolic|state-symbolic|symbolic|smt
   --semantics mealy|moore
   --automaton-tool ltl3ba|spot
   --target aiger|dot|smv
   --solver picosat|cryptominisat|rareqs|depqbf|cadet|caqe|quabs|idq|eprover|vampire|z3|cvc4
   --qbf-certifier cadet|caqe|quabs

For example

    ./bosy.sh syntcomp2016-tlsf-synthesis/Parameterized/simple_arbiter_2.tlsf --synthesize --target smv

extracts an SMV implementation after determining realizability.


## Provided Scenarios

We provide 3 different scenarios that are provided in shell scripts:
* small-experiments.sh runs every possible backend on a small example specification
* small-experiments-synthesis.sh additionally synthesizes implementations and displays them
* small-experiments-verify.sh verifies a synthesized solution using the NuSMV model checker

Additionally, we provide a script to verify the results from the paper:
* load-balancer-experiments.sh executes multiple configurations of BoSy on the load_balancer_5.tlsf benchmark and reports run time and solution size. (warning: the run time is ca 1h 30min)

The scatter plot provided in the paper cannot be verified in the VM within reasonable time due to the need for a large timeout (1 h) per benchmark.
However, BoSy was already evaluated independently in the reactive synthesis competition and the results of the input-symbolic variant are available online at http://syntcomp.cs.uni-saarland.de/syntcomp2016/experiment/6.

## Guide to the source code

BoSy has been written in Swift 3.0. The following source files provide a good entry-point:
* `~/Desktop/BoSy/Sources/BoSy/main.swift` starts the searches for system and environment strategies and triggers automata translation.
* `~/Desktop/BoSy/Sources/BoSy/Automaton.swift` contains the code for the automata translation and for calling ltl3ba and spot.
* `~/Desktop/BoSy/Sources/BoSy/SolutionSearch.swift` contains the actual search. The function `hasSolution` calls `solve` for each encoding and increases the bound according to the search strategy.
* `~/Desktop/BoSy/Sources/BoSy/InputSymbolicEncoding.swift` contains the input-symbolic encoding to QBF.
* `~/Desktop/BoSy/Sources/BoSy/Solver.swift` contains any solver-specific code and the program calls and options for each solver.
* `~/Desktop/BoSy/Sources/BoSy/ExplicitStateSolution.swift` contains the representation of the synthesized solution and the output formats.
