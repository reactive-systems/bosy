#!/usr/bin/env bash

#TODO --use-existing, --fresh-minimal, --fresh, --fresh-full, tool var,

tools=("abc" "bloqqer" "bloqqer-031" "cadet" "cryptominisat5" "ltl2tgba" "ltl3ba" "idq" "quabs" "rareqs" "syfco" "z3")
tools_full=("agibmc" "smvtoaig" "caqe" "combine-aiger" "cvc4" "depqbf" "eprover" "picosat-solver" "vampire" "hqs-linux" "hqspre-linux" "ltl2smv" "NuSMV")

function run_original() {
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
function check_tools() {
    if [ ! -d "./Tools" ]; then
        return 3
    fi
    ret_code=0
    for tool in "${!tools[@]}"; do
        if [ ! -f "./Tools/$tool" ] || [ ! -x "./Tools/$tool" ]; then
            ret_code=3
            break 1
        fi
    done
    if [ $ret_code -ne 0 ]; then
        return $ret_code
    fi
    for tool in "${!tools_full[@]}"; do
        if [ ! -f "./Tools/$tool" ] || [ ! -x "./Tools/$tool" ]; then
            return 0
        fi
    done
}

function build_tools() {
    if [ "$1" ]; then
        make all 2>tool_build_errors.log | tee tool_build.log
    else
        make 2>tool_build_errors.log | tee tool_build.log
    fi
    return $?
}

function build_swift_on_demand() {
    if [ ! "$1" ]; then                                              #no rebuild of already built binary
        if [ -d "./.build" ] || [ ! -f "./.build/debug/BoSy" ]; then # build bc no binary present
            swift build
            return $?
        fi
    elif [ ! "$2" ]; then
        swift build
        return $?
    fi
}

function print_help() {
    echo "
        Usage:
        $(basename "$0") [options] [bosy-options]

        Options:
            --use-existing: use old version of the script, rebuilding the swift code on every run.
            --fresh: just rebuild the swift code before running (fast).
            --fresh-minimal: rebuild swift-code + default tools (needed for auto-configured bosy run, time intensive)
            --fresh-full:  rebuild swift + build all tools from scratch (VERY time intensive).
                Note: Most thorough fresh* option set will take precedence

        For bosy tool specific options see $(basename "$0") tool --tool-help
    "
}

args=@

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
        fresh_full=full
        unset "args[$i]"
        ;;
    "--help")
        print_help_flag=true
        break
        ;;
    esac
done

if [ "$print_help_flag" ]; then
    print_help
    exit 0
fi

if [ "$use_existing" ]; then
    run_original "${args[@]}"
    exit $?
fi

build_swift_on_demand [ $fresh_full -o $fresh_minimal -o $fresh ] [ $fresh_minimal -o $fresh_full]

build_tools [ $fresh_full -o $fresh_minimal ]

#dev not: @ contains args, :1 cuts script name

exit $?
