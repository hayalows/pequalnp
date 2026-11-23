# P vs NP research, 23 November 2026

This archive contains working notes, supporting Lean proofs, experiments, compiler output, and reproducible scripts from the Codex Cloud research session. The official statements are preserved in the assignment files. The supporting results do not establish any of the three assigned conjectures. There was no submission to the official project.

| Work | Result |
| --- | --- |
| [L-gct-210](L-gct-210/resume.md) | Lean checked coefficient vanishing, the zero-rectangle obstruction, and a bound under quadratic isotropy. The unrestricted complex dimension bound of 8 remains unproved. |
| [L-gct-086](L-gct-086/resume.md) | Lean checked a fixed-Taylor-order obstruction and supporting dimension lemmas. The unrestricted linear bound remains unproved. |
| [L-lib-123](L-lib-123/resume.md) | Lean checked the verifier accounting for the no-saving case and a butterfly path-count obstruction. The required strict speedup remains unproved. |
| [L-meta-661](L-meta-661/resume.md) | The private continuation checked incidence and DAG gate-count lemmas. The link to the exact circuit evaluator still needs a complete Lean proof. Gemini's draft compilation diagnostics are preserved in the L-gct-210 directory. |

The three official research windows lasted twenty minutes each. All six renewals succeeded, and the desk confirmed each lease release with `missing_lemma`. The assignment snapshots and lease logs omit credentials. The session scripts are preserved for operational context and assume the original cloud workspace layout.

Earlier evidence reviewed in the session is included for continuity.

- [L-meta-651](L-meta-651) contains the Petersen graph shard 4 scripts and results. The second-gate checks and local edits covered only a small part of the search through 19 gates.
- [L-meta-700](L-meta-700) contains the verified bowtie circuit witness of weight 10. The universal bound later merged separately. [Upstream proof](https://github.com/brilliant-hq/pequalnp-proofs/pull/1329)
- [L-meta-662](L-meta-662) contains the separate Net graph Boolean calculations. Their relationship to the exact official theorem was unresolved in the reviewed material.

The original verification used Lean 4.36.0 with the official repository's pinned dependencies. Each research directory records its verification scope and reproduction commands. Consult the notes before running an incomplete attempt or a script that acquires a lease.
