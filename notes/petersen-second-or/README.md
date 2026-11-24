# The second OR after AND(x₀,x₃)

The question in L-meta-1869 is whether 13 more gates can compute the edge predicate of the Petersen graph minus one vertex. The suffix receives nine inputs, their fixed AND(x₀,x₃), and the output of a second OR. Operand 10 of that OR reads the default false value. This permits empty and singleton ORs, repeated operands, and either operand being the fixed AND.

[PetersenSecondORSearch.lean](../PetersenSecondORSearch.lean) proves that a successful suffix needs at least eight non-NOT gates and can have at most five NOT gates. It then constructs, from any successful suffix, a sequence of live wire sets on 414 pairs of assignments with opposite answers. The end of the file proves that ruling out all such sequences implies the exact positive twin L-meta-1868. The finite exclusion is an explicit hypothesis of that theorem.

The C++ program enumerates the wire sets. A state retains only wires needed by later gates. A binary operation can drop or retain each operand, and a NOT can drop or retain its operand. With no NOT remaining each positive/negative pair must be separated in the forward direction by some available wire. While NOT remains, either direction suffices. Neither condition excludes a needed state, as established in Lean by the separation and live-size lemmas. The C++ implementation and its reported negative answers are outside the Lean kernel.

From this directory run the following commands with a C++17 compiler and Python 3.

```sh
c++ -std=c++17 -O3 search.cpp -o search
python3 run.py 2 > local.csv
diff results.csv local.csv
```

The optional number selects the worker count. The 66 unordered operand pairs and 14 NOT counts give 924 cases. The checked-in run reports 1,148 eligible starting states across cases, 155,858,783 state visits, and zero witnesses. A second C++ implementation gave identical starting counts, visits, and verdicts in all 924 cases. The test signatures and live-wire formalization derive from [jmwalsh96’s checked certificate for L-meta-1672](https://github.com/brilliant-hq/pequalnp-proofs/pull/4290). The 414 pairs were evaluated against the graph in Lean.

## Kernel-checked cases

[PetersenSecondORCases.lean](../PetersenSecondORCases.lean) proves that an unrestricted circuit for this nine-vertex function needs at least 15 gates. The proof inserts a spare fixed first AND and applies the project's checked L-meta-1672. This also gives a 14-gate lower bound on the suffix in each of the following cases:

- Every suffix using only AND and OR, for every legal second OR. Monotonicity lets the circuit discard the nonedge AND.
- Every suffix with arbitrary AND, OR and NOT gates when the second OR is redundant. There are 23 such unordered operand pairs. The OR repeats one of its operands, reads the default false value, or is absorbed by one of the two inputs of the first AND.

Four symmetries of the graph preserve the fixed AND. For the 43 remaining unordered operand pairs, the Lean file verifies that relabeling the circuit reduces the problem to 16 representatives. Any remaining counterexample must have exactly 13 suffix gates, including between one and five NOT gates. The theorem `PetersenCases.exactBound` derives the desk's complete L-meta-1868 statement assuming those representative cases are impossible. Their formal exclusion remains open here.

To check this companion, use the project's pinned checkout containing [the merged L-meta-1672 theorem](https://github.com/brilliant-hq/pequalnp-proofs/pull/4290). From the checkout's `lean` directory, build `lake build PEqualNP.Outside.L_meta_1672` and then run `lake env lean /path/to/PetersenSecondORCases.lean`.
