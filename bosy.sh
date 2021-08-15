#!/usr/bin/env bash

function run_original() { #the original behavior. encapsulated into function for readability
    if $2; then
        swift run -c release BoSy --help
        return $?
    fi

    swift run -c release BoSy "$1"
    exit_code=$?

    # Terminate all tools that may have been started by BoSy
    for f in Tools/*; do
        if [ ! -f "$f" ]; then
            continue
        fi
        tool=$(basename "$f")
        killall "$tool" &>/dev/null
    done
    return $exit_code
}

# helper functions
# returns 2 if the default set of tools can't be found, 1 if default tools are complete but additional ones are not compiled,
# and 0 if everything is compiled and ready to use
function check_tools() { #check state of the current build, determines what build commands need to be run
    echo "Checking tool state... "
    # spell-checker:disable
    tools=("abc" "bloqqer" "bloqqer-031" "cadet" "cryptominisat5" "ltl2tgba" "ltl3ba" "idq" "quabs" "rareqs" "syfco" "z3")
    tools_full=("aigbmc" "smvtoaig" "caqe" "combine-aiger" "cvc4" "depqbf" "eprover" "picosat-solver" "vampire" "hqs-linux" "hqspre-linux" "ltl2smv" "NuSMV")
    # spell-checker:enable
    if [ ! -d "./Tools" ]; then
        return 2
    fi
    ret_code=0
    for tool in "${tools[@]}"; do #check standard tools
        if [ ! -f "./Tools/$tool" ] || [ ! -x "./Tools/$tool" ]; then
            ret_code=2
            break 1
        fi
    done
    if [ $ret_code -ne 0 ]; then
        echo "No complete set of default tools found. Rebuilding if requested"
        return $ret_code
    fi
    echo "Complete set of default tools found! Checking for additional tools... "
    for tool in "${tools_full[@]}"; do #check full tool set
        if [ ! -f "./Tools/$tool" ] || [ ! -x "./Tools/$tool" ]; then
            echo "Additional tools not complete. Build them in you want to use them"
            return 1
        fi
    done
    echo "All tools found. Noting to do here."
}

function build_tools() { # $1 fresh-minimal, $2 fresh-full, $3 tool_state
    if $1 && [ "$3" -eq 2 ]; then
        echo "building default tool-set"
        make 2>tool_build_errors.log | tee tool_build.log
    fi
    if $2 && { [ "$3" -eq 1 ] || [ "$3" -eq 2 ]; }; then
        echo "building additional tool-set"
        make all 2>tool_build_errors.log | tee tool_build.log
    fi
    return $?
}

function build_swift_on_demand() {
    if ! $1; then                                                      # no rebuild of already built binary
        if [ -d "./.build" ] || [ ! -f "./.build/release/BoSy" ]; then # build bc no binary present
            swift build --configuration release -Xcc -O3 -Xcc -DNDEBUG -Xswiftc -Ounchecked
            return $?
        fi
    elif ! $2; then
        swift build --configuration release -Xcc -O3 -Xcc -DNDEBUG -Xswiftc -Ounchecked
        return $?
    fi
}

function print_help() {
    echo "
        Usage:
        $(basename "$0") [options] [bosy-options]

        Options:
            --help: shows this help text and exits
            --use-existing: use old version of the script, rebuilding the swift code on every run.
            --fresh: just rebuild the swift code before running (fast).
            --fresh-minimal: rebuild swift-code + default tools (needed for auto-configured bosy run, time intensive)
            --fresh-full:  rebuild swift + build all tools from scratch (VERY time intensive).
                Note: Most thorough fresh* option set will take precedence

        For bosy specific options see $(basename "$0") --tool-help
    "
}

if [ "$#" -eq 0 ]; then
    print_help
    exit 0
fi

args=("${@:1}")

use_existing=false
fresh_minimal=false
fresh=false
fresh_full=false
print_help_flag=false
tool_help=false

for i in "${!args[@]}"; do
    val=${args[$i]}
    case "$val" in
    "--use-existing")
        use_existing=true
        unset "args[$i]"
        ;;
    "--fresh-minimal")
        fresh_minimal=true
        unset "args[$i]"
        ;;
    "--fresh")
        fresh=true
        unset "args[key]"
        ;;
    "--fresh-full")
        fresh_full=true
        unset "args[$i]"
        ;;
    "--help")
        print_help_flag=true
        break
        ;;
    "--tool-help")
        tool_help=true
        unset "args[$i]"
        break
        ;;
    esac
done

if $print_help_flag; then
    print_help
    exit 0
fi

echo "'Args passed to bosy: ${args[*]}'"

if $use_existing; then
    echo "Running in with original script behavior"
    run_original "${args[@]}" "$tool_help"
    exit $?
fi

build_swift_on_demand $fresh_full || $fresh_minimal || $fresh $fresh_minimal || $fresh_full

check_tools
tool_state=$?

if [ "$tool_state" -eq 2 ] && ! $fresh_minimal && ! $fresh_full; then
    echo "Error: None or not all of the required tools present! Please use at least the --fresh-minimal flag or build them manually"
    exit 1
fi

if $fresh_full && [ "$tool_state" -eq 2 ]; then
    fresh_minimal=true
fi

build_tools $fresh_minimal $fresh_full $tool_state

if $tool_help; then
    .build/release/BoSy --help
else
    .build/release/BoSy "${args[@]}"
fi
exit_code=$?

# Terminate all tools that may have been started by BoSy
for f in Tools/*; do
    if [ ! -f "$f" ]; then
        continue
    fi
    tool=$(basename "$f")
    killall "$tool" &>/dev/null
done

exit $exit_code
