# Petersen circuit branches excluded by topology

The pinned Lean kernel checks that two specific sets of eleven available truth tables cannot compute the nine-input Petersen-minus-one edge function within eleven more AND, OR or NOT gates.

In the example in `TopologyExample.lean`, the prefix computes OR(0,6), OR(1,0), AND(3,2), and OR(5,1), in that order. The available wires are the seven original inputs numbered 2 through 8 and all four gate outputs. Six witnesses cover all 2,048 possible choices of input signs for a read-once formula. Ten more witnesses exclude every choice of which available signals belong to a shared subformula. Counting the binary gates shows these two families exhaust the eleven-gate possibilities for this branch. Other choices of live wires after the same prefix can give different branches.

`OrientationCut.lean`, `ModuleCertificate.lean`, and `TightCertificate.lean` state the general exclusion rules. `AdaptiveForest.lean` shows how a certified exclusion can be used while verifying a finite circuit search. The remaining modules supply the read-once, shared-subformula, and finite-pattern arguments developed for the parallel L-meta-2161 proof by jdavies69. The underlying circuit search and its nine-input graph come from loris-olsem's merged L-meta-1667 proof.

From a clone of this branch with pinned Lean and Mathlib, run `sh notes/petersen-orientation/check.sh`. The examples establish individual branches of the L-meta-2504 search.
