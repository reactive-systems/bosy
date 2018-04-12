#!/usr/bin/env bash

slow=$1
if [ -z "$1" ]; then
    printf "Note: Only run fast experiments, start script with --slow to run all\n\n"
fi

swift build -c release

# define colors for better readability
RED='\033[0;31m'
BLUE='\033[0;34m'
NC='\033[0m' # No Color


printf "\n${RED}Symmetric Mutex${NC}\n"

# Symmetric arbiter (moore)
printf "\n* ${BLUE}Symmetric Mutex (moore,non-sym)${NC}\n"
time swift run -c release BoSy --player system Samples/HyperLTL/bakery_sym_unrealizable_moore.bosy

printf "\n* ${BLUE}Symmetric Mutex (moore,sym)${NC}\n"
time swift run -c release BoSyHyper --environment Samples/HyperLTL/bakery_sym_unrealizable_moore.bosy

printf "\n* ${BLUE}Symmetric Mutex (moore,tie)${NC}\n"
time swift run -c release BoSyHyper Samples/HyperLTL/bakery_tie_realizable_moore.bosy


# Symmetric arbiter (mealy)
printf "\n* ${BLUE}Symmetric Mutex (mealy,non-sym)${NC}\n"
time swift run -c release BoSy --player system Samples/HyperLTL/bakery_sym_unrealizable.bosy

printf "\n* ${BLUE}Symmetric Mutex (mealy,sym)${NC}\n"
time swift run -c release BoSyHyper --environment Samples/HyperLTL/bakery_sym_unrealizable.bosy

printf "\n* ${BLUE}Symmetric Mutex (mealy,tie)${NC}\n"
time swift run -c release BoSyHyper Samples/HyperLTL/bakery_tie_realizable.bosy


# Full arbiter (moore)
printf "\n* ${BLUE}Symmetric Mutex (moore,full-non-sym)${NC}\n"
time swift run -c release BoSy --player system Samples/HyperLTL/bakery_full_sym_unrealizable_moore.bosy

printf "\n* ${BLUE}Symmetric Mutex (moore,full-sym)${NC}\n"
time swift run -c release BoSyHyper --environment Samples/HyperLTL/bakery_full_sym_unrealizable_moore.bosy

printf "\n* ${BLUE}Symmetric Mutex (moore,tie)${NC}\n"
if [[ -n "$slow" ]]; then
    time swift run -c release BoSyHyper Samples/HyperLTL/bakery_full_tie_realizable_moore.bosy  # slow ~1h
else
    echo "omitted, re-run with --slow"
fi

# Full arbiter (mealy)
printf "\n* ${BLUE}Symmetric Mutex (mealy,full-non-sym)${NC}\n"
time swift run -c release BoSy --player system Samples/HyperLTL/bakery_full_sym_unrealizable.bosy

printf "\n* ${BLUE}Symmetric Mutex (mealy,full-sym)${NC}\n"
time swift run -c release BoSyHyper --environment Samples/HyperLTL/bakery_full_sym_unrealizable.bosy

printf "\n* ${BLUE}Symmetric Mutex (mealy,tie)${NC}\n"
time swift run -c release BoSyHyper Samples/HyperLTL/bakery_full_tie_realizable.bosy


printf "\n\n${RED}Encoder/Decoder${NC}\n"

# Encoder/Decoder (moore)
printf "\n* ${BLUE}Encoder/Decoder (moore,1-2-hamming-2)${NC}\n"
time swift run -c release BoSyHyper Samples/HyperLTL/encoder_1_2_hamming_2_moore.bosy

printf "\n* ${BLUE}Encoder/Decoder (moore,1-2-fault-tolerant)${NC}\n"
time swift run -c release BoSyHyper --environment Samples/HyperLTL/encoder_1_2_unrealizable_moore.bosy

printf "\n* ${BLUE}Encoder/Decoder (moore,1-3-fault-tolerant)${NC}\n"
time swift run -c release BoSyHyper Samples/HyperLTL/encoder_1_3_realizable_moore.bosy

#time swift run -c release BoSyHyper --environment Samples/HyperLTL/encoder_2_2_hamming_2_moore.bosy

printf "\n* ${BLUE}Encoder/Decoder (moore,2-3-hamming-2)${NC}\n"
if [[ -n "$slow" ]]; then
    time swift run -c release BoSyHyper Samples/HyperLTL/encoder_2_3_hamming_2_moore.bosy --min-bound 16 # slow ~4h
else
    echo "omitted, re-run with --slow"
fi


# Encoder/Decoder (mealy)
printf "\n* ${BLUE}Encoder/Decoder (mealy,1-2-hamming-2)${NC}\n"
time swift run -c release BoSy --player system Samples/HyperLTL/encoder_1_2_hamming_2.bosy

#time swift run -c release BoSyHyper --environment --paths 3 Samples/HyperLTL/encoder_1_2_unrealizable.bosy # does not work due to encoding

printf "\n* ${BLUE}Encoder/Decoder (mealy,1-3-fault-tolerant)${NC}\n"
time swift run -c release BoSyHyper Samples/HyperLTL/encoder_1_3_realizable.bosy

printf "\n* ${BLUE}Encoder/Decoder (mealy,2-3-hamming-2)${NC}\n"
time swift run -c release BoSyHyper Samples/HyperLTL/encoder_2_3_hamming_2.bosy

printf "\n* ${BLUE}Encoder/Decoder (mealy,2-3-hamming-3)${NC}\n"
time swift run -c release BoSyHyper --environment --paths 3 Samples/HyperLTL/encoder_2_2_hamming_2.bosy



# CAP Theorem

printf "\n\n${RED}CAP Theorem${NC}\n"

printf "\n* ${BLUE}CAP Theorem (moore,cap-2-linear)${NC}\n"
time swift run -c release BoSy --player system Samples/HyperLTL/cap_2_moore.bosy

printf "\n* ${BLUE}CAP Theorem (mealy,cap-2-linear)${NC}\n"
time swift run -c release BoSy --player system Samples/HyperLTL/cap_2.bosy

printf "\n* ${BLUE}CAP Theorem (moore,cap-2)${NC}\n"
if [[ -n "$slow" ]]; then
    time swift run -c release BoSyHyper --environment Samples/HyperLTL/cap_2_moore.bosy # slow ~30min
else
    echo "omitted, re-run with --slow"
fi

#time swift run -c release BoSyHyper --environment Samples/HyperLTL/cap_2.bosy # does not work due to encoding

printf "\n* ${BLUE}CAP Theorem (mealy,ca-2)${NC}\n"
time swift run -c release BoSyHyper Samples/HyperLTL/ca_2.bosy

printf "\n* ${BLUE}CAP Theorem (mealy,ca-3)${NC}\n"
time swift run -c release BoSyHyper Samples/HyperLTL/ca_3.bosy

printf "\n* ${BLUE}CAP Theorem (mealy,cp-2)${NC}\n"
time swift run -c release BoSyHyper Samples/HyperLTL/cp_2.bosy

printf "\n* ${BLUE}CAP Theorem (moore,cp-2)${NC}\n"
time swift run -c release BoSyHyper Samples/HyperLTL/cp_2_moore.bosy

printf "\n* ${BLUE}CAP Theorem (mealy,cp-3)${NC}\n"
time swift run -c release BoSyHyper Samples/HyperLTL/cp_3.bosy

printf "\n* ${BLUE}CAP Theorem (moore,cp-3)${NC}\n"
time swift run -c release BoSyHyper Samples/HyperLTL/cp_3_moore.bosy

printf "\n* ${BLUE}CAP Theorem (mealy,ap-2)${NC}\n"
time swift run -c release BoSyHyper Samples/HyperLTL/ap_2.bosy

printf "\n* ${BLUE}CAP Theorem (mealy,ap-3)${NC}\n"
time swift run -c release BoSyHyper Samples/HyperLTL/ap_3.bosy


printf "\n\n${RED}Bus protocol${NC}\n"

# bus protocol (moore)

printf "\n* ${BLUE}Bus protocol (moore,ni1)${NC}\n"
time swift run -c release BoSyHyper --environment Samples/HyperLTL/bus_master_unrealizable.bosy

printf "\n* ${BLUE}Bus protocol (moore,ni2)${NC}\n"
time swift run -c release BoSyHyper Samples/HyperLTL/bus_master_forget.bosy

# bus protocol (mealy)

printf "\n* ${BLUE}Bus protocol (mealy,ni1)${NC}\n"
time swift run -c release BoSyHyper --environment Samples/HyperLTL/bus_master_unrealizable_mealy.bosy

printf "\n* ${BLUE}Bus protocol (mealy,ni2)${NC}\n"
time swift run -c release BoSyHyper Samples/HyperLTL/bus_master_forget_mealy.bosy


printf "\n\n${RED}Dining Cryptographers${NC}\n"

# dining cryptographers
time swift run -c release BoSyHyper Samples/HyperLTL/dining-cryptographers.bosy
