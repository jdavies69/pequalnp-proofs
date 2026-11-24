# Three assignments that exclude an optimal Petersen circuit

This certificate considers a nine-input Petersen graph circuit with only one additional gate that reads the distinguished input. Setting that input to false leaves an eight-variable edge function with an exact circuit minimum of 13 gates. A normalized circuit attaining the minimum must use every remaining gate to create a fresh, nonconstant truth table. A finite search tracks whether any of these truth tables leaves a set of 63 values.

The upper cofactor needs to agree with the target on the local eight-bit assignments 1, 8 and 52. The first two must give true and the last must give false. Exhaustive Lean proofs show that no circuit staying inside the 63 lower-cofactor values can match those three outputs, even when it may independently use the distinguished reader on any wire with the same lower-cofactor value.

Lean's compiled evaluator passed all 1,736 states of the search. The pinned kernel verified the implication from those table checks to the exact L-meta-2504 statement. Independent kernel checks of the individual table blocks are in progress.

Run `sh notes/petersen-reader-invariant/check.sh` from a clone of this branch with the pinned Lean toolchain and its Mathlib cache. EvaluateAll prints the budget, row count and any failed row indices. An empty list means every row at that budget passed.

The search builds on the finite circuit verifier and induced-subgraph bounds in upstream L-meta-1667, the eight-input bound in L-meta-2036, and the circuit normalization in L-meta-2502. The signed-formula and shared-subformula witnesses are adapted from the parallel L-meta-2161 proof effort. The source files use project modules available in this fork.
