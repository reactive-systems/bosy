# BoSy Artefact Evaluation

We provide an Ubuntu VM with a single user `cav` and password `ae`.


## Getting Started

The source code of BoSy is located under `~/Desktop/BoSy`.
All dependencies necessary to build BoSy are already installed, executing `make` produces the BoSy binary.


## Benchmarks

BoSy support the SYNTCOMP TLSF benchmark format by the conversion tool `syfco`.
The SYNTCOMP benchmarks can be downloaded by calling the script `obtain-syntcomp2016-instances.sh`
The helper script `bosy.sh` does the conversion, i.e., accepts TLSF inputs.
An example call is

    ./bosy.sh syntcomp2016-tlsf-synthesis/Parameterized/simple_arbiter_2.tlsf

and should terminate with `realizable`.
BoSy support the following command line options:
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

extracts an SMV implementation after determine realizability.


## Provided Scenarios

We provide 3 different scenarios that are encoded in shell scripts:
* small-experiments.sh runs every possible backend on a small example specification
* small-experiments-synthesis.sh additionally synthesizes implementations and displays them
* small-experiments-verify.sh verifies a synthesized solution using the NuSMV model checker

Additionally, we provide a script to verify the results from the paper:
* load-balancer-experiments.sh executes multiple configurations of BoSy on the load_balancer_5.tlsf benchmark and reports run time and solution size. (warning: the run time is ca 1h 30min)
