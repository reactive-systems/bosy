#!/usr/bin/env bash

swift run -c release BoSy ${@:1}

exit_code=$?

# Terminate all tools that may have been started by BoSy
for f in Tools/*; do
    if [ ! -f $f ]; then
        continue
    fi
    tool=$(basename $f)
    killall $tool &> /dev/null
done

exit $?
