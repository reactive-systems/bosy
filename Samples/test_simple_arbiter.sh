#!/usr/bin/env bash

result=0

# test realizability
echo "checking realizability using input-symbolic (QBF) backend"
./bosy.sh Samples/simple_arbiter.bosy --backend input-symbolic
if [ "$?" -ne "0" ]; then
  result=1
fi

echo "checking realizability using explicit (SAT) backend"
./bosy.sh Samples/simple_arbiter.bosy --backend explicit
if [ "$?" -ne "0" ]; then
  result=1
fi

echo "checking realizability using SMT backend"
./bosy.sh Samples/simple_arbiter.bosy --backend smt
if [ "$?" -ne "0" ]; then
  result=1
fi

# test synthesis
echo "synthesizing using input-symbolic (QBF) backend"
./bosy.sh Samples/simple_arbiter.bosy --backend input-symbolic --synthesize
if [ "$?" -ne "0" ]; then
  result=1
fi

echo "synthesizing using explicit (SAT) backend"
./bosy.sh Samples/simple_arbiter.bosy --backend explicit --synthesize
if [ "$?" -ne "0" ]; then
  result=1
fi

echo "synthesizing using SMT backend"
./bosy.sh Samples/simple_arbiter.bosy --backend smt --synthesize
if [ "$?" -ne "0" ]; then
  result=1
fi

if [ "$result" -ne "0" ]; then
  echo ""
  echo "failed"
fi
exit $result