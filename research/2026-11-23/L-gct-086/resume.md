# L-gct-086 research and resumption, 23 November 2026 UTC

An ordinary desk request, without a hard flag, assigned L-gct-086 at 17:53:30 UTC. The exact statement is in assignment.json. It asks for a uniform constant C such that a complex linear subspace of n-by-n matrices on which permanent(J+t) is identically n! has dimension at most C*n. This is the all-ones level-space statement, rather than the matrix-subspace paraphrase in Gemini's earlier note. No proof or superlinear counterexample to the exact assignment is in this checkpoint.

## Lean-verified results

Use the official upstream Lean checkout with Lean 4.36.0. From its lean directory, run:

    source /workspace/pequalnp/scripts/lean-cloud-env.sh
    LEAN_NUM_THREADS=1 lake env lean /absolute/path/LevelHall.lean
    LEAN_NUM_THREADS=1 lake env lean /absolute/path/ProductRotation.lean

Both files exit 0. LevelHall.lean uses the exact project permanent and proves that the line polynomial on each level direction is constant, that no direction can equal -1 on an oversized row-by-column rectangle, and that no fixed Taylor order yields the desired linear upper bound. In the last result, n=r*m with m≥2, and a primitive mth root z acts on a direction by rotating every block of m rows. Each of the r profiles is a freely chosen sum-zero column vector. The dimension is r*(n−1), all row and column sums are zero, and row-permutation invariance kills each coefficient of positive degree below m. This family is an obstruction to a truncated proof. A rank-one direction with a primitive-root profile of length m on both axes has nonzero degree-m coefficient.

ProductRotation.lean gives the rigorous bound dim V < m if a sum of m products ∏j(1+s_i*v_j), with s_i nonzero and arbitrary scalar weights, is a fixed nonzero constant on V. Starting from a finite-dimensional affine slice, choose a coordinate that varies on its direction space, set one factor to zero, and continue in a codimension-one slice. Repeated full row-root blocks pair with arbitrary column profiles in this way: when a row profile has the full root multiset repeated floor(n/m) times and zeros elsewhere, its elementary symmetric sums are nonzero in every allowable degree divisible by m. A genuinely level rank-one product with that fixed row profile therefore makes the root-averaged column product constant, and the column dimension is <m.

## Mathematical evidence and limitations

- L-gct-092 reduces the general problem to doubly centered spaces at a cost of 2n in dimension. L-gct-080 supplies examples of dimension 2n−3. L-gct-084, 088, 089 and 099 give exact coefficient formulas useful for constructing and checking candidates.
- Quadratic signature gives at most 2n−2 for conjugation-invariant spaces, but arbitrary complex isotropic spaces are larger. Large doubly centered truncated examples show that even obtaining a fixed number of additional moments cannot close that gap.
- Root-block construction: a disjoint row and column partition has a primitive root profile in each block. Each edge of a bipartite block graph carries an independent rank-one parameter. A positive coefficient survives exactly when there is nonzero integer transport supported on the graph with every row and column block either unused or filled to its capacity. Once a participating block is used, primitive-root summation forces all its slots to be used for these profiles. Contributions for the same transportation monomial have the same root product and positive integer multiplicities, so there is no cancellation. Complete-grid, Ferrers, comparable-divisibility, and uniform-weight subclasses have linear bounds. Uniform weights use a transportation tree formed by interval overlap and degree peeling. No extrapolation from weighted finite experiments to a general graph theorem.
- The Fourier support calculation gives linear bounds for column-separated models and for prime-power row/column Fourier families. For prime-power n, the row-cycle-invariant space bound uses exact nonvanishing of zero-weight Fourier coefficients and Rado's independent transversal theorem. Without invariance, a reduction mod p loses the needed constraint: the group algebra has large nilpotent ideals.
- The apolar squarefree algebra encodes all matching products, but multiplication followed by projection to degree n−1 loses high primitive components. No lower-growth estimate adequate to force dim L=O(n) is established.

## Resume

1. Recheck official status before claiming a new lease. Compile the two supporting files and reproduce the finite graphs only for the scope recorded in their logs.
2. The best open near-term research direction is to understand arbitrary, potentially correlated Fourier components. The proof for genuine row-cycle invariance cannot be applied to an arbitrary L. A proof of invariance under degeneration would have to preserve all the matching equations, not just their lowest weight pieces.
3. The block family has an exact transport criterion. A general weighted core theorem would rule out the whole construction family. Conversely, a sequence of transport-free block graphs with superlinear edges would provide an explicit route to an actual refutation. Test any candidates in both the transport model and the polynomial before formalizing.
4. For the general upper bound, an effective estimate on the growth of gradients or squarefree-product spans through linearly many orders could use the verified low-order obstruction to choose which orders matter. Hall exclusions alone permit dimension of order n² and cannot establish the desired result.

A further linear subclass follows by combining the exact support argument with Scherk's unique-sum inequality. Take arbitrary primitive-root row blocks of lengths m_i and one full prime-power cyclic Fourier basis on the n columns. Within row block i, take independent tensor directions whose column frequencies lie in A_i. Nonzero row coefficients require exactly m_i uses of every active row block. The column coefficient on such a monomial is nonzero exactly when the total weight is zero, by the prime-power Fourier calculation. Thus a level space forbids nonempty zero-sum transversals across the sets m_i A_i of m_i-fold sums. In particular no such set contains zero. Adding an abstention zero to each set gives a unique representation of zero in the sumset. Iterating Scherk gives sum_i |m_i A_i|≤n−1. Translating A_i by (m_i−1) copies of a fixed element injects it into m_i A_i, so the dimension sum_i |A_i| is at most n−1. This is independent of whether the row block sizes are comparable.

Lease closed by the desk with missing_lemma at 2026-11-23T18:13:30Z after 20 minutes of work. Both renewals returned 200.
