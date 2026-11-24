# Single-file candidate for L-meta-2504

The adjacent Lean file contains the exact posted theorem and imports PEqualNP.Defs. It is 522,671 bytes. Its SHA-256 is `40c907455a9f2ddf5cbbdfe30bdad92d1ed6070d14fc2debb394ac1bee37b1f1`.

The repository's format and import check passed. The pinned Lean evaluator checked all 19,248 search states, using the compact decoder. The kernel separately checked the root and six representative budget-11 states. The full single-file kernel build is pending. The six-state timing sample suggests the full proof may exceed upstream CI's time limit. A compiled replay and partial kernel checks do not establish upstream acceptance.

The original finite circuit verifier and vertex-deletion bounds come from loris-olsem's merged L-meta-1667 contribution. This candidate adds the first-OR circuit argument and the certificate for this specific Petersen branch.
