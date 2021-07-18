# Solver-encoding compatibility matrix
The following table outlines the current compatibility between solvers and encodings. For those not in the table, see below.

 | x              | picosat | cryptominisat | rareqs  | caqe+cadet | caqe+quabs | hqs      | vampire  | z3       |
 | -------------- | ------- | ------------- | ------- | ---------- | ---------- | -------- | -------- | -------- |
 | aiger          | &#9989; | &#9989;       | &#9989; | &#9989;    | &#9989;    | &#10060; | &#10060; | &#9989;  |
 | dot            | &#9989; | &#9989;       | &#9989; | &#9989;    | &#9989;    | &#10060; | &#10060; | &#9989;  |
 | dot-topography | &#9989; | &#9989;       | &#9989; | &#9989;    | &#9989;    | &#10060; | &#10060; | &#10060; |
 | smv            | &#9989; | &#9989;       | &#9989; | &#10060;   | &#9989;    | &#10060; | &#10060; | &#9989;  |
 | verilog        | &#9989; | &#9989;       | &#9989; | &#9989;    | &#9989;    | &#10060; | &#10060; | &#9989;  |
<!-- &#9989; = check mark, &#10060; = X -->
 ##### Solver that are not in the list:
 - cadet, quabs: work only for certifying
 - dcaque: has no binary since a few versions
 - eprover, cvc4, idq: currently errors on input