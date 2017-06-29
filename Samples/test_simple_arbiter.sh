#!/usr/bin/env bash

# test realizability
./bosy.sh Samples/simple_arbiter.bosy --backend input-symbolic 2>&1 | grep "result: realizable" || exit 1
./bosy.sh Samples/simple_arbiter.bosy --backend explicit  2>&1 | grep "result: realizable" || exit 1
./bosy.sh Samples/simple_arbiter.bosy --backend smt  2>&1 | grep "result: realizable" || exit 1

# test synthesis
./bosy.sh Samples/simple_arbiter.bosy --backend input-symbolic --synthesize  2>&1 | grep "result: realizable" || exit 1
./bosy.sh Samples/simple_arbiter.bosy --backend explicit --synthesize  2>&1 | grep "result: realizable" || exit 1
./bosy.sh Samples/simple_arbiter.bosy --backend smt --synthesize 2>&1 | grep "result: realizable" || exit 1
