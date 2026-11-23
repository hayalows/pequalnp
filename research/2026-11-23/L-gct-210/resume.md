# L-gct-210 research and resumption

The official assignment was issued 2026-11-23 at 17:33:22 UTC to hayalows. The exact statement and permitted modules are in assignment.json. Its target is dimension at most 8. There is no complete proof or explicit 9-dimensional counterexample in this archive.

## Reproduce the Lean work

In OpenAI-managed Codex Cloud, use the current official upstream checkout and its pinned Mathlib cache. During this work HEAD was 269d579 and Lean reported 4.36.0. Later upstream 4762036 had identical checker and definition sources. From the official repository's lean directory run:

    source /workspace/pequalnp/scripts/lean-cloud-env.sh
    LEAN_NUM_THREADS=1 lake env lean /absolute/path/LevelCoefficients.lean

LevelCoefficients.lean compiled with exit 0. It proves that all positive coefficients vanish, that the closed quadratic form is nondegenerate and gives dimension at most 12 under isotropy, and that the exact permanent-level hypothesis excludes a constant -1 rectangle of row and column cardinalities summing to more than five. The mathematical link between the quadratic form and the permanent is as follows. A term choosing two distinct rows and columns occurs in 3! completions, and each two-edge matching occurs twice in the ordered sum. Therefore the second coefficient is 3 times the full polarized quadratic form on the diagonal. The straightforward Lean enumeration in ExpandedCoefficient-attempt.lean exhausted the available memory budget and was interrupted. Replace it with a fiber-count argument over the ordered pairs of distinct rows and columns. None of these auxiliary files is a submission for the target bound.

## Mathematical and computational findings

See upper-bound/NOTES.md and construction/conditional_bounds.md for full arguments. The real and conjugation-invariant cases satisfy the desired bound by signature. The general complex quadratic argument gives dimension at most 12, and the doubly centered case gives at most 8. The cubic moment admits a weighted coordinatewise-power-sum form. The quartic does not simplify to the fourth power sum, even on doubly centered examples. Distinct approaches give the target bound under additional one-sided 5-cycle symmetry, a full four-dimensional single-row kernel, or small coordinate support. In particular the standard seven-dimensional hook cannot be extended even to dimension eight.

The support sweep uses exact ranks modulo 1009 as lower bounds for complex rank and exact rational computations for the residual cases. Those computations constrain coordinate supports and say nothing exhaustive about all complex subspaces. Exact Fourier-family searches found dimension at most six in ordinary cycle tensor bases and at most seven in the enlarged finite candidate pool. Generic complex optimization in isotropic_fit.py was numerical. None of its candidates met the polynomial identities in validation.

## Next mathematical work

1. Recheck upstream and desk status before taking a new lease. Prevent duplicate work if L-gct-210 has been settled.
2. Focus on full support and high-rank row projections. Low-support families are already covered by the bundled sweep and conditional bounds. Generalize the Hall rectangle exclusion into a usable constraint on the spans of the 25 entry linear forms. The missing reduction is from an arbitrary hypothetical 9-plane to a constrained family.
3. Use polarized cubic and quartic conditions after restricting to the kernel of a row or column projection. Avoid the failed assumption that normalized row and column annihilators always give inverse-Hessian Gram rank at least 7. Common normals with sum squares 1/4 give explicit rank-at-most-3 exceptions.
4. If pursuing L-meta-661 instead, first compare its live official statement. The saved Gemini artifact has an exact compile log with Lean exit 1 and 39 printed errors, and must be reworked. A shorter approach is to restrict one NOT to a constant via either a large zero set or a true assignment disjoint from selected lines. Count the distinct branch OR gates in monotone dependency subgraphs bounded above by each restricted target. Different lines have at most one common point, so a wide useful merge cannot serve two different lines.
5. If taking a Petersen shard in the future, preserve a canonicalization proof and a complete circuit encoding, including all admissible gate and wire semantics. The prior session released L-meta-651 shard 4 with out_of_time after a brief investigation. The 168 second-gate checks and local edits did not cover the permitted circuits through 19 gates. The exact old assignment is [private Drive reference omitted] .
