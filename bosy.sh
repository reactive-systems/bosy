#!/usr/bin/env bash

file_input=$1

if [ ! -f "$file_input" ]; then
  echo "$0 <instance>"
  exit 1
fi

if [ ${file_input: -5} == ".tlsf" ]; then
	./Tools/syfco --format bosy $file_input | .build/release/BoSy ${@:2}
else
	.build/release/BoSy ${@:2} $file_input
fi

exit_code=$?

killall abc bloqqer eprover idq ltl2tgba ltl3ba spot picosat quabscm rareqs syfco z3 vampire &> /dev/null

exit $?
