# A first-OR lower bound for the Petersen graph with one vertex deleted

The proposed bound says that a fan-in-two AND, OR, NOT circuit computing the nine-input edge function needs at least 16 gates if its first gate computes the OR of inputs 0 and 6. The second theorem specializes the bound to the single-reader condition in the desk's L-meta-2504 assignment.

The forest contains 19,248 states. Lean’s compiled evaluator passed the original verifier on every state. Independent proof terms for the individual segments and the two concluding theorems are included. Full kernel verification across those segments is in progress.

From a clone of this branch with its pinned Lean toolchain and Mathlib installed, run the following command.

```sh
sh notes/petersen-2504/check-certificate.sh
```

The script first builds the upstream verifier, checks the data and the circuit argument, then checks every segment and assembles the final theorems. The last two lines report their axiom dependencies. The checker uses Python 3 to compile each segment in smaller units and bound peak memory. Allow time for the segment checks.

The verifier for finite circuit searches, the vertex-deletion bounds and the original nine-input chart come from loris-olsem’s merged proof of L-meta-1667 in upstream PR 4332. This certificate supplies the new forest for the OR of inputs 0 and 6, the first-gate argument and the specialization to L-meta-2504.
