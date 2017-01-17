#!/usr/bin/env bash

tlsf_input=$1

if [ ! -f "$tlsf_input" ]; then
  echo "$0 <instance.tlsf>"
  exit 1
fi

./Tools/syfco --format bosy $1 | .build/release/BoSy ${@:2}
killall abc bloqqer eprover idq ltl2tgba ltl3ba spot picosat quabsl rareqs syfco z3 vampire &> /dev/null
