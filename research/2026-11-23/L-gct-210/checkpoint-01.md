# L-gct-210 active checkpoint, 23 November 2026 UTC

Official lease issued at 17:33:22 UTC to hayalows. Only one assignment is held. The lease credential is private. The separate renewal process is scheduled every 570 seconds. Proofs baseline 269d579. Lean 4.36.0 and lake build checklemma succeeded. Cloud quota is 2 CPUs and 8 GiB RAM.

The question is whether a complex linear space on which the permanent of J+t is identically 120 has dimension at most 8 for 5 by 5 matrices. Here J is all ones. The exact desk statement accompanies this note. No complete proof or refutation yet.

## Necessary conditions

Expansion in z of the permanent of J+zt gives zero for each positive-degree coefficient. The linear condition is total sum zero. On that hyperplane, twice the second matching sum is sum(entries squared) minus sum(row sums squared) minus sum(column sums squared). The row-additive, column-additive and doubly-centered summands have respective dimensions 4, 4 and 16. The associated bilinear form is the usual entrywise pairing composed with an operator acting by -4, -4 and 1 on those summands. It is nondegenerate, yielding the weaker complex bound 12.

Every row and column projection excludes the all-ones vector. Otherwise one can make a zero row or column of J+t. The same reasoning gives the exclusion on an r by (6-r) rectangle by Hall obstruction. Using only normalized row and column annihilators, the hoped-for inverse Hessian Gram rank at least 7 fails. Constant row annihilator a and constant column annihilator b with sums 1 and sum of squares 1/4 give rank at most 3.

## Verified finite scope

cyclic_basis.py computes all mixed coefficients by partition-lattice inclusion-exclusion, then checks subsets of tensor products of the usual cycle Fourier bases for every pair of partitions of 5. Maximum dimension in this family is 6. Explicit cross and fourth-root constructions have dimension 7. extend.py tests their possible enlargements via exact Gaussian-rational gradient equations. Sampled gradient kernels have dimension 8, so neither 7-space can sit in a 9-space.

## Prior work revisited

L-meta-700 tightness witness was Lean-verified, and the universal lower bound has since been added upstream in brilliant-hq/pequalnp-proofs#1329. L-meta-651 shard 4 belongs to a Petersen-graph search over circuits beyond two gates. Checking 168 second gates, the non-edge orbit and single local edits to a 20-gate circuit leaves longer circuits uncovered. The saved artifacts support neither a witness nor exhaustion of the shard. Gemini's L-meta-661 candidate uses the line-OR statement in its theorem despite a conflicting paraphrase in the report. Its compiled proof status is still unverified here. The Net example in the L-meta-662 analysis violates the triangle-free hypothesis in Gemini's quoted alternate statement.

## Work in progress

Derive useful higher-degree identities from the exact official L-gct-210 hypothesis, explore larger coupled constructions and check the accepted 4 by 5 analysis L-gct-215 for smaller reductions. Keep the current lease until sustained research identifies a justified next action.
