# Formalization gates and exact claim boundaries

No Lean executable, Lake command, kernel audit or CI run is authorized or performed here. All new Lean-like files use `.lean.txt`, are outside `src/`, and are absent from Lake and Palomar manifests.

| Gate | Mathematical obligation | Present status |
| --- | --- | --- |
| T0 | TOB-QMC weak consistency for any prescribed subexponential shrinking alpha | Complete proposed proof bodies copied structurally from existing proofs, with `rejects_of_log` substituted; **uncompiled** |
| T1 | Explicit alpha=chiSqOneTail(log m) TOB-QMC corollaries | Proposed complete compositions using existing tail-limit lemmas; **uncompiled** |
| G0 | Deterministic score-gap lemma for approximate optimizers | Elementary `linarith` proof draft; **uncompiled** |
| G1 | WQC population bad-tree gap, candidate-space availability and normalized regret | Handproof from finite tree class and existing population/refinement results |
| G2 | Hoeffding coordinate bound and finite-sample guide bound | Elementary handproof; no Lean probability proof yet |
| S0 | Multinomial LIL or a sufficient pathwise empirical-rate lemma | New analytic formalization required |
| S1 | Actual cut/T3 Gaussian-cone tail lower bound on regular null paths | Rectangle-event handproof outline; **highest-priority analytic review gate** |
| S2 | T1 tail sandwich and star/T1 pathwise null/alternative statistics | Handproof; exact Lean limit/tail interfaces to be supplied |
| S3 | Uniform good-test event over every guide/coarsening, then deterministic reconstruction | Finite-universe handproof; no independence between stages |
| E0 | ECToBlob Bon strong convergence to `limitTree` on arbitrary guides | Composition of S2/S3 and the existing deterministic framework; **not kernel verified** |
| E1 | Binary Assumption-1 laws exclude all centroids, allowing fixed beta | Existing no-trivial-four-blob lemma plus star converse; composition not checked |
| F0 | Method-of-types inequality for composite trinomial null | Full elementary handproof; separate calibration variant |
| F1 | Summable null/alternative errors and late-error bound | Full union-bound/Borel-Cantelli handproof |

## Priority

Review T0/T1 and G0 first: these are low-risk source-level compositions. Then S0/S2 and E0/E1 provide the clearest path to a stronger ECToBlob theorem. S1 must be established before claiming the same pathwise result for TOB-QMC's actual T3/cut p-values. F0/F1 offer an independent conservative route, but change calibration and must not be mixed up with the original algorithms.

## Uncompiled means uncompiled

Absence of `sorry` in a draft does not mean Lean has accepted its imports, implicit arguments, elaboration, universe levels or proof terms. The existing repository audit does not cover these files. Nothing is recorded as kernel-closed in this PR.

## Non-claims

- No alteration of the original paper's theorem or an archived Challenge/Solution statement.
- No blanket general-network extension of sparse TOB-QMC contraction. Level 1 and adequate quartet coverage remain where required.
- No new result for Cauchy, CBC or BBC strong consistency without their own endpoint/tail analysis.
- No claim that constant alpha presets are statistically consistent.
- No claim that finite approximation ratios imply vanishing WQC regret.
- No user-tuning requirement is added to QWC; shared hypotheses are mathematical conditions, not new runtime parameters.
- No independence assumption across quartets or between the same-data guide and contraction stages.
- No robustness to arbitrary fixed-fraction adversarial replacement is asserted by these iid probability results.

## Source map

All paths refer to the original commit `a1102a1e6150db9bd2f119f12757ea0abb0354d6`:

- `src/TOBQMC/Consistency.lean`, `ConsistencyT3.lean`: original end-to-end weak consistency proof structure.
- `src/TINNiK/Basic.lean`, `T3.lean`: rejection under prescribed subexponential levels and existing explicit schedule results.
- `src/TOBQMC/WQC.lean`, `Astral.lean`: almost-sure guide refinement and candidate-space saturation.
- `src/ECToBlob/Framework.lean`: `AdequateTests`, `RunBy.ectoblobBy_eq`, `tendsto_ectoblobBy_limitTree`, `theorem8_2_levels`.
- `src/ECToBlob/Remark84.lean`: binary-network coarsening target and `not_hasTrivialFourBlob_of_isBinary`.
- `src/Basic/Testing/Defs.lean`: actual statistic and Gaussian-tail definitions.
- `src/ECToBlob/Section5.lean`: generic independent-inheritance NMSC Assumption-1 specialization.

The proofs should remain paper-owned, with genuinely shared statistical/finite-score lemmas factored into Basic only after their interfaces are reviewed.
