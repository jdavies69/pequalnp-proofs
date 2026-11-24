# A 2,554-state search for the first OR on Petersen inputs 0 and 6

Lean's compiled evaluator verified every state in a six-level search for a nine-input circuit with at most 15 gates. Its first gate computes the OR of inputs 0 and 6. The search needs 2,554 states. Its larger predecessor needed 19,248.

The smaller search uses finite witnesses for 17,684 distinct states that it excludes based on the number of available signals. The witnesses cover possible assignments of input polarities to a formula and possible choices of which signals belong to a reusable subformula. The verifier computes each witness against the actual truth tables. A hash lookup supplies a candidate witness list.

The pinned Lean kernel verified the general exclusion rules, the implication from checked rows to the exact L-meta-2504 statement, and the first and last singleton layers. The full six-level replay used Lean’s compiled evaluator. Independent kernel proofs for all 2,554 states are pending.

From a clone of this branch with pinned Lean and Mathlib, run `sh notes/petersen-adaptive/check.sh`. It builds the proof modules, reports the axiom dependencies and replays every row. The expected counts in order are 1, 66, 1,100, 1,316, 70 and 1. The supporting modules are in the adjacent petersen-orientation and petersen-2504 directories. The original finite circuit verifier and vertex-deletion bounds were developed by loris-olsem for upstream L-meta-1667.
