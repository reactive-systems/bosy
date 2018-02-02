#!/usr/bin/env bash

swift build -c release

set -x #echo on

# Simple arbiter (moore)
time swift run -c release BoSy --player system Samples/HyperLTL/bakery_sym_unrealizable_moore.bosy

time swift run -c release BoSyHyper --environment Samples/HyperLTL/bakery_sym_unrealizable_moore.bosy

time swift run -c release BoSyHyper Samples/HyperLTL/bakery_tie_realizable_moore.bosy

# Simple arbiter (mealy)
time swift run -c release BoSy --player system Samples/HyperLTL/bakery_sym_unrealizable.bosy

time swift run -c release BoSyHyper --environment Samples/HyperLTL/bakery_sym_unrealizable.bosy

time swift run -c release BoSyHyper Samples/HyperLTL/bakery_tie_realizable.bosy


# Full arbiter (moore)
time swift run -c release BoSy --player system Samples/HyperLTL/bakery_full_sym_unrealizable_moore.bosy

time swift run -c release BoSyHyper --environment Samples/HyperLTL/bakery_full_sym_unrealizable_moore.bosy

time swift run -c release BoSyHyper Samples/HyperLTL/bakery_full_tie_realizable_moore.bosy  # slow ~1h

# Full arbiter (mealy)
time swift run -c release BoSy --player system Samples/HyperLTL/bakery_full_sym_unrealizable.bosy

time swift run -c release BoSyHyper --environment Samples/HyperLTL/bakery_full_sym_unrealizable.bosy

time swift run -c release BoSyHyper Samples/HyperLTL/bakery_full_tie_realizable.bosy


# Secret decision (moore)
time swift run -c release BoSy --player system Samples/HyperLTL/SecretDecision.bosy

time swift run -c release BoSyHyper Samples/HyperLTL/SecretDecision.bosy

time swift run -c release BoSyHyper Samples/HyperLTL/SecretDecisionForget.bosy

# Secret decision (mealy)
time swift run -c release BoSy --player system Samples/HyperLTL/SecretDecision_Mealy.bosy

time swift run -c release BoSyHyper Samples/HyperLTL/SecretDecision_Mealy.bosy

time swift run -c release BoSyHyper Samples/HyperLTL/SecretDecisionForget_Mealy.bosy


# Encoder/Decoder (moore)
time swift run -c release BoSy --player system Samples/HyperLTL/encoder_1_2_hamming_2_moore.bosy

time swift run -c release BoSyHyper --environment Samples/HyperLTL/encoder_1_2_unrealizable_moore.bosy

time swift run -c release BoSyHyper Samples/HyperLTL/encoder_1_3_realizable_moore.bosy

#time swift run -c release BoSyHyper --environment Samples/HyperLTL/encoder_2_2_hamming_2_moore.bosy

time swift run -c release BoSyHyper Samples/HyperLTL/encoder_2_3_hamming_2_moore.bosy --min-bound 16 # slow ~4h


# Encoder/Decoder (mealy)
time swift run -c release BoSy --player system Samples/HyperLTL/encoder_1_2_hamming_2.bosy

#time swift run -c release BoSyHyper --environment --paths 3 Samples/HyperLTL/encoder_1_2_unrealizable.bosy # does not work due to encoding

time swift run -c release BoSyHyper Samples/HyperLTL/encoder_1_3_realizable.bosy

time swift run -c release BoSyHyper --environment --paths 3 Samples/HyperLTL/encoder_2_2_hamming_2.bosy

time swift run -c release BoSyHyper Samples/HyperLTL/encoder_2_3_hamming_2.bosy


# CAP Theorem

time swift run -c release BoSy --player system Samples/HyperLTL/cap_2_moore.bosy

time swift run -c release BoSy --player system Samples/HyperLTL/cap_2.bosy

time swift run -c release BoSyHyper --environment Samples/HyperLTL/cap_2_moore.bosy # slow ~30min

time swift run -c release BoSyHyper --environment Samples/HyperLTL/cap_2.bosy # does not work due to encoding

time swift run -c release BoSyHyper Samples/HyperLTL/ca_2.bosy

time swift run -c release BoSyHyper Samples/HyperLTL/ca_3.bosy

time swift run -c release BoSyHyper Samples/HyperLTL/cp_2.bosy

time swift run -c release BoSyHyper Samples/HyperLTL/cp_2_moore.bosy

time swift run -c release BoSyHyper Samples/HyperLTL/cp_3.bosy

time swift run -c release BoSyHyper Samples/HyperLTL/cp_3_moore.bosy

time swift run -c release BoSyHyper Samples/HyperLTL/ap_2.bosy

time swift run -c release BoSyHyper Samples/HyperLTL/ap_3.bosy


# bus protocol (moore)

time swift run -c release BoSyHyper --environment Samples/HyperLTL/bus_master_unrealizable.bosy

time swift run -c release BoSyHyper Samples/HyperLTL/bus_master_forget.bosy

# bus protocol (mealy)

time swift run -c release BoSyHyper --environment Samples/HyperLTL/bus_master_unrealizable_mealy.bosy

time swift run -c release BoSyHyper Samples/HyperLTL/bus_master_forget_mealy.bosy


# dining cryptographers
time swift run -c release BoSyHyper Samples/HyperLTL/dining-cryptographers.bosy
