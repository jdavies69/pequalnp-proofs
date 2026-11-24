# The seven-input Petersen minor in L-meta-2960

The target is true if both endpoints of one of eight edges are selected. The desk asks whether every fan-in-two AND/OR/NOT circuit computing it needs eleven binary gates, regardless of how many NOT gates it uses.

ThetaUpper.eleven verifies an eleven-gate circuit on all 128 assignments. It computes the disjunction of four terms. Vertex 1 pairs with any of 0, 2 and 5. Vertex 6 pairs with any of 2, 4 and 3. The last two terms are the pairs 0 and 4, and 3 and 5. The circuit uses only AND and OR.

Theta2960.circuitTrace converts a circuit into a sequence of gates acting on 128-bit truth tables. Complements are free. Each step may produce a signed AND of two live wires and drop either operand once its last use has passed. The kernel verifies the conversion for empty gates, repeated operands, out-of-range wire indices and arbitrary output selection. Theta2960.lower_of_search connects rejection of all ten-gate sequences to the requested circuit lower bound.

Run python3 search.py to enumerate the twelve induced graph types in order of increasing size. For each live set, a positive and a negative assignment must differ on at least one live wire. Each remaining binary gate can reduce the number of live wires by at most one. On a previously solved induced subgraph, the program counts the prefix gates whose projected outputs were new even up to complementation. Projected constant live wires each consume one gate in the suffix without contributing a projected binary operation. These bounds rule out branches. The complete enumeration closes the seven-input graph at budget ten.

The finite enumeration currently supplies computational evidence. The kernel has checked the matching upper bound, the circuit conversion, and the implication from a successful finite certificate to the posted bound. Verification of the complete lower-bound certificate is in progress.

With the repository's pinned Lean environment, run sh check.sh from this directory to replay the Lean results.
