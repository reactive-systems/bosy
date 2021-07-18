# Solver-encoding compatibility matrix
The following table outlines the current compatibility between solvers and encodings. For those not in the table, see below.

 | x             | picosat | cryptominisat | rareqs | caqe+cadet | caqe+quabs | hqs | vampire | z3  |
 | ------------- | ------- | ------------- | ------ | ---------- | ---------- | --- | ------- | --- |
 | aiger         | ✅       | ✅             | ✅      | ✅          | ✅          | ❌   | ❌       | ✅   |
 | dot           | ✅       | ✅             | ✅      | ✅          | ✅          | ❌   | ❌       | ✅   |
 | dot-topograpy | ✅       | ✅             | ✅      | ✅          | ✅          | ❌   | ❌       | ❌   |
 | smv           | ✅       | ✅             | ✅      | ❌          | ✅          | ❌   | ❌       | ✅   |
 | verilog       | ✅       | ✅             | ✅      | ✅          | ✅          | ❌   | ❌       | ✅   |

 ##### Solver that are not inthe list:
 - cadet, quabs: work only for certifying
 - dcaque: has no binary since a few versions
 - epover, cvc4, idq: currently errors on input