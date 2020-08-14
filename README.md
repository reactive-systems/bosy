# BoSy

BoSy is a reactive synthesis tool based on constraint-solving.


## Awards

* First and second place in sequential LTL synthesis track (SYNTCOMP 2016)
* Second and third place in sequential LTL realizability track (SYNTCOMP 2016)
* First place (quality ranking) in sequential LTL synthesis track (SYNTCOMP 2017)
* Third place in sequential LTL realizability track (SYNTCOMP 2017)

## Online Interface

BoSy can be tried without installation directly in your browser in our [online interface](https://www.react.uni-saarland.de/tools/online/BoSy/).

## Installation

BoSy is tested on macOS and Ubuntu.

* Requires [Swift compiler](https://swift.org/download)
* `make` builds the minimal configuration:
	*  downloads and builds required dependencies (in directory `Tools`)
	*  builds the BoSy binary
* Optional dependencies are built with `make all`

> One may need to install additional dependencies for building the tools that BoSy depends on. Check the make output and the respective tool description for more information.

### System Package Dependencies

The following packages need to be installed in order to build BoSy with all dependencies.

For CAQE, you also need Rust installed.

#### Ubuntu 16.04

```bash
apt-get install bison build-essential clang cmake curl flex gcc git libantlr3c-dev libbdd-dev libboost-program-options-dev libicu-dev libreadline-dev mercurial unzip vim-common wget zlib1g-dev libsqlite3-dev
# Haskell stack
curl -sSL https://get.haskellstack.org/ | sh
```

#### macOS

```
xcode-select --install
brew tap brewsci/science
brew install libbuddy haskell-stack cmake
```


## Usage

BoSy uses a JSON based input file format (SYNTCOMP TLSF support via a [transformation tool](https://github.com/reactive-systems/syfco)).

Consider the following arbiter specification for two clients.
Every request from a client (signal `r_0`/`r_1`) must be eventually granted (signal `g_0`/`g_1`) by the arbiter with the restriction that `g_0` and `g_1` may not be set simultaneously.

```json
{
	"semantics": "mealy",
	"inputs":  ["r_0", "r_1"],
	"outputs": ["g_0", "g_1"],
	"assumptions": [],
	"guarantees": [
		"G ((!g_0) || (!g_1))",
		"G (r_0 -> (F g_0))",
		"G (r_1 -> (F g_1))"
	]
}
```

The command `./bosy.sh [--synthesize] arbiter.json` checks the specification for realizability.
If the option `--synthesize` is given, a solution is extracted after realizability check.
Check `./bosy.sh --help` for more options.


## Synthesis from HyperLTL Specifications

`BoSyHyper` (a separate binary) supports synthesis of reactive systems from specifications given in HyperLTL.


### Example

The following system keeps a `secret` until the `publish` signal arrives.

```json
{
    "semantics": "moore",
    "inputs": ["decision", "value", "publish"],
    "outputs": ["internal", "result"],
    "assumptions": [],
    "guarantees": [
        "!internal",
        "(G (decision -> (value <-> X internal)))",
        "(G (!decision -> (internal <-> X internal)))",
        "(G ( publish -> X(internal <-> result)))"
    ],
    "hyper": [
        "forall pi1 pi2. ( (publish[pi1] || publish[pi2]) R (result[pi1] <-> result[pi2]) )"
    ]
}
```

```bash
$ swift run -c release BoSyHyper Samples/HyperLTL/SecretDecision.bosy
info: Linear automaton contains 4 states
info: Hyper automaton contains 1 states
info: build encoding for bound 1
info: build encoding for bound 2
info: build encoding for bound 3
realizable
```
