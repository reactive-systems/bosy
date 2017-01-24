#!/bin/bash


file="syntcomp2016-tlsf-synthesis/Parameterized/load_balancer_5.tlsf"

echo "Realizability results"

echo "Executing Benchmark $file with spot, explicit encoding, solver picosat"
time ./bosy.sh $file --player system --automaton-tool spot --backend explicit --solver picosat
echo "Executing Benchmark $file with spot, explicit encoding, solver cryptominisat"
time ./bosy.sh $file --player system --automaton-tool spot --backend explicit --solver cryptominisat

echo "Executing Benchmark $file with spot, input-symbolic encoding, solver rareqs"
time ./bosy.sh $file --player system --automaton-tool spot --backend input-symbolic --solver rareqs
echo "Executing Benchmark $file with spot, input-symbolic encoding, solver caqe"
time ./bosy.sh $file --player system --automaton-tool spot --backend input-symbolic --solver caqe

echo "Executing Benchmark $file with ltl3ba, explicit encoding, solver picosat"
time ./bosy.sh $file --player system --automaton-tool ltl3ba --backend explicit --solver picosat
echo "Executing Benchmark $file with ltl3ba, explicit encoding, solver cryptominisat"
time ./bosy.sh $file --player system --automaton-tool ltl3ba --backend explicit --solver cryptominisat

echo "Executing Benchmark $file with ltl3ba, input-symbolic encoding, solver rareqs"
time ./bosy.sh $file --player system --automaton-tool ltl3ba --backend input-symbolic --solver rareqs
echo "Executing Benchmark $file with ltl3ba, input-symbolic encoding, solver caqe"
time ./bosy.sh $file --player system --automaton-tool ltl3ba --backend input-symbolic --solver caqe

echo "Synthesis results"

echo "Executing Benchmark $file with spot, explicit encoding, solver picosat"
time ./bosy.sh $file --player system --automaton-tool spot --backend explicit --solver picosat --synthesize | ./aigstat.py
echo "Executing Benchmark $file with spot, explicit encoding, solver cryptominisat"
time ./bosy.sh $file --player system --automaton-tool spot --backend explicit --solver cryptominisat --synthesize | ./aigstat.py

echo "Executing Benchmark $file with spot, input-symbolic encoding, solver quabs"
time ./bosy.sh $file --player system --automaton-tool spot --backend input-symbolic --synthesize --qbf-certifier quabs | ./aigstat.py
echo "Executing Benchmark $file with spot, input-symbolic encoding, solver cadet"
time ./bosy.sh $file --player system --automaton-tool spot --backend input-symbolic --synthesize --qbf-certifier cadet | ./aigstat.py
echo "Executing Benchmark $file with spot, input-symbolic encoding, solver caqe"
time ./bosy.sh $file --player system --automaton-tool spot --backend input-symbolic --synthesize --qbf-certifier caqe | ./aigstat.py

echo "Executing Benchmark $file with ltl3ba, explicit encoding, solver picosat"
time ./bosy.sh $file --player system --automaton-tool ltl3ba --backend explicit --solver picosat --synthesize | ./aigstat.py
echo "Executing Benchmark $file with ltl3ba, explicit encoding, solver cryptominisat"
time ./bosy.sh $file --player system --automaton-tool ltl3ba --backend explicit --solver cryptominisat --synthesize | ./aigstat.py

echo "Executing Benchmark $file with ltl3ba, input-symbolic encoding, solver quabs"
time ./bosy.sh $file --player system --automaton-tool ltl3ba --backend input-symbolic --synthesize --qbf-certifier quabs | ./aigstat.py
echo "Executing Benchmark $file with ltl3ba, input-symbolic encoding, solver caqe"
time ./bosy.sh $file --player system --automaton-tool ltl3ba --backend input-symbolic --synthesize --qbf-certifier caqe | ./aigstat.py


