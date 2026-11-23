# L-lib-123 research and resumption, 23 November 2026 UTC

The desk assigned L-lib-123 to hayalows on an ordinary request at 18:13:44 UTC. The exact assignment is in assignment.json. It asks for natural p and q such that 1 ≤ p < q and FP3 p q. For every language decidable on the pinned FinTM2 model in O(2^(q n)) steps, FP3 requires an exact-length three-block existential, universal, existential verifier with block lengths K·2^(p n)+K and a predicate linear-time on its full encoded pair input. The constant K and predicate can depend on the language. The genuine fixed power saving remains unresolved.

## Lean evidence

Run in the official Lean 4.36.0 checkout:

    source /workspace/pequalnp/scripts/lean-cloud-env.sh
    lake build +PEqualNP.Library.Evasion.MBudget +PEqualNP.Library.Evasion.MTrans
    LEAN_NUM_THREADS=1 lake env lean /absolute/path/VerifierAccounting.lean
    LEAN_NUM_THREADS=1 lake env lean /absolute/path/Butterfly.lean

The supporting files compile with exit 0. VerifierAccounting.lean proves the exact ∃∀∃ unfolding, monotonicity in the source exponent, and FP3 p q for q ≤ p with p≥1. The latter uses the checked budget wrapper to reject inputs with inadequate witness length and permits a constant-time-per-symbol transducer. Simply ignoring the entire witness and running the source machine would break the global linear bound on malformed pairs. The file also proves that no fixed polynomial factor in the input length covers the exponential gap between p and q. This does not prove FP3 for any p < q. The file uses internal helper modules for private research. The official assignment permits only Mathlib and PEqualNP.Defs.

Butterfly.lean formally counts surviving paths for the directed butterfly. At stage i the low i bits have been replaced with the target bits. Exactly 2^k source-target pairs pass through each vertex, and each cut leaves some target with at least 2^k minus the cut size surviving sources. The page layout is justified below and is separately verified by exhaustive checks for k=1,…,8 in butterfly_layout.py. That finite check is limited to these parameters.

construction/InternalAlphabet.lean checks that reachable symbols at each stack of a fixed FinTM2 lie in uniformly finite sets despite the type allowing infinite alphabet domains for internal stacks. The input alphabet and control are finite, and each push symbol lies in the finite image of a callback from finite control, drawn from fixed finite statement trees. This rules out a hidden arbitrary-data oracle through work-stack types. ExactAlt.lean checks the combined verifier input length.

upper/Checkpoint.lean and upper/DAGCertificates.lean formalize the soundness and completeness of abstract checkpoint and directed-cone certificates. They do not construct a sublinear-time verifier for arbitrary machines.

## Routes tested

Two-block checkpointing for a deterministic time T and space S machine gives certificates of scale roughly sqrt(TS) times overhead, by balancing the cost of checkpoint descriptions and local replay. This gives a fixed saving when S has a fixed power saving relative to T. Full-space runs have no savings by this accounting. A deterministic square-root-space simulation does not preserve the original T time in general. Williams's tree evaluation depends on deep paths and can have very large time overhead. See https://arxiv.org/abs/2502.17779 and its discussion of alternating time in §5.

A directed segregator would yield a promising ∃∀∃ simulation of a block-respecting run: guess coarse movement metadata and values on cut vertices, universally select a vertex, and existentially certify its truncated ancestor cone. Topological induction checks all global commitments. To give a fixed saving, both cut size and maximum cone size would need to be a fixed power below the number of blocks, with efficient metadata handling. General constant-page forward graphs do not have this property.

For the butterfly, order incoming copies of a layer by their binary words in increasing order and outgoing copies in decreasing order. The relay edges within a layer are nested and share one page across disjoint layers. Identity transition edges, and bit-flip edges restricted to source bit zero or one, are monotone in natural word order. They therefore each form a nested page between consecutive outgoing and incoming copies. These intervals are disjoint between transition bands. One can reduce four pages to three by inserting a merge/fork layer of words with the replaced bit deleted. The two monotone restrictions for deletion and insertion use two cross-layer pages. Each merge copy has path load at most twice the width w=2^k, and all word copies have load w. A cut below w/4 leaves some target with at least w/2 reachable sources in an O(k w)-vertex graph. This defeats any universal fixed power bound on both cut and cones for this graph class. It is not a lower bound for deciding a language by another representation. Related context: Paul, Pippenger, Szemerédi, Trotter, https://scholarship.claremont.edu/hmc_fac_pub/1043/ and page-layout expanders https://arxiv.org/abs/1501.05020 .

A long-query relativized diagonalization gives a clean barrier: for p<q, one oracle language can ask an oracle bit at length between 2^(p n) and 2^(q n). Any fixed candidate verifier at exponent p makes only shorter queries at sufficiently large n. Diagonalize at fresh query lengths against the countable verifier list. This applies in the written-query model and does not refute unrelativized FP3.

## Resume

1. Recheck exact upstream and desk status. Neither q≤p nor any abstract oracle counterexample is a proof of the official statement.
2. Continue only with a mechanism that uses the content of the deterministic computation. A universal directed graph-cut theorem from page count alone is false. A narrower theorem on the block graphs of a specific efficient oblivious simulator would need a new structural argument.
3. A second concrete target is short, verifiably correct Boolean circuits for random access to the deterministic trace. A first witness committing to a short enough trace circuit would let the universal block challenge any local transition and let the short verifier evaluate it. Short machine description is insufficient to establish small trace circuits. All claims about speedups must account for worst-case sequential access and malformed verifier inputs.
4. Prefer a genuinely small finite project assignment if the desk makes one available. Three consecutive ordinary requests in this session assigned hard research problems. Claiming again without evidence of a tractable step risks holding another hard lease without a credible short route.

Desk release: 2026-11-23T18:33:44Z 200 missing_lemma. Renewal log included.
