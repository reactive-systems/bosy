#!/usr/bin/env bash

result=0

# test realizability
echo "checking realizability using input-symbolic (QBF) backend"
./bosy.sh Samples/simple_arbiter.bosy --backend input-symbolic 2>&1 | grep "result: realizable"
if [ "$?" -ne "0" ]; then
  echo "failed"
  result=1
fi

echo "checking realizability using explicit (SAT) backend"
./bosy.sh Samples/simple_arbiter.bosy --backend explicit 2>&1 | grep "result: realizable"
if [ "$?" -ne "0" ]; then
  echo "failed"
  result=1
fi

echo "checking realizability using SMT backend"
./bosy.sh Samples/simple_arbiter.bosy --backend smt 2>&1 | grep "result: realizable"
if [ "$?" -ne "0" ]; then
  echo "failed"
  result=1
fi

# test synthesis
echo "synthesizing using input-symbolic (QBF) backend"
./bosy.sh Samples/simple_arbiter.bosy --backend input-symbolic --synthesize 2>&1 | grep "result: realizable"
if [ "$?" -ne "0" ]; then
  echo "failed"
  result=1
fi

echo "synthesizing using explicit (SAT) backend"
./bosy.sh Samples/simple_arbiter.bosy --backend explicit --synthesize 2>&1 | grep "result: realizable"
if [ "$?" -ne "0" ]; then
  echo "failed"
  result=1
fi

echo "synthesizing using SMT backend"
./bosy.sh Samples/simple_arbiter.bosy --backend smt --synthesize 2>&1 | grep "result: realizable"
if [ "$?" -ne "0" ]; then
  echo "failed"
  result=1
fi

if [ "$result" -ne "0" ]; then
  echo ""
  echo "failed"
fi
exit $result