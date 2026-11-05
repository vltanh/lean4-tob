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
| S1 | Actual cut/T3 Gaussian-cone tail lower bound for arbitrary small polynomial exponents | Optional sharper-schedule project; the **T3 lower bound is already formalized** as `half_chiSqOneTail_le_t3PValue` |
| O1 | Identify the original star/T1/T3 LRT statistics with 2m times the KL projection onto their exact closed nulls | New typed bridge needed |
| O2 | Multinomial method-of-types uniform bound `(m+1)^2 exp(-t/2)` for those statistics, including support boundaries | Full elementary handproof; not kernel-checked |
| O3 | Use the pre-existing `log_chiSqOneTail_ge` and T1/T3 tail sandwich to certify the **actual** p-value schedule `alpha_m=(m+1)^(-100)` | Explicit handproof of null error `(m+1)^(-2)`; no Gaussian-cone geometry needed |
| O4 | Alternative Hoeffding/Pinsker bound and Bonferroni uniformity over all data-dependent states | Full handproof, not Lean checked |
| O5 | Borel--Cantelli and reconstruction: strong TOB-QMC-T3 and ECToBlob-Bon results, fixed beta for binary networks | New finite-universe and reconstruction composition required |
| O6 | Formalize dyadic Hoeffding--Doob maximal concentration and a.s. empirical `O(sqrt(log log m/m))` for each quartet coordinate | Elementary handproof in `OriginalPValuesStrong.md` §10; uncompiled |
| O7 | KL local-quadratic bound on the positive population support, then original-test `-log p=O(log log m)` and full polynomial schedule window | Composition with checked tail bounds; uncompiled |
| S2 | T1 tail sandwich and star/T1 pathwise null/alternative statistics | Handproof; exact Lean limit/tail interfaces to be supplied |
| S3 | Uniform good-test event over every guide/coarsening, then deterministic reconstruction | Finite-universe handproof; no independence between stages |
| E0 | ECToBlob Bon strong convergence to `limitTree` on arbitrary guides | Composition of S2/S3 and the existing deterministic framework; **not kernel verified** |
| E1 | Binary Assumption-1 laws exclude all centroids, allowing fixed beta | Existing no-trivial-four-blob lemma plus star converse; composition not checked |
| F0 | Method-of-types inequality for composite trinomial null | Full elementary handproof; separate calibration variant |
| F1 | Summable null/alternative errors and late-error bound | Full union-bound/Borel-Cantelli handproof |

## Priority

**Updated priority:** first close the low-risk T0/T1/G0 compositions. Then close **O1--O5** for the actual T1/T3/LRT-star p-values; pre-existing bounds remove the former T3 Gaussian-cone blocker for the conservative polynomial schedule. Only afterwards pursue the sharper, optional S0/S1 schedule window. The separate F0/F1 calibration changes the tests and must not be confused with the new original-test result.

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


## BBC and Cauchy endpoint gate update

**O8:** Prove the deterministic BBC sandwich `min(P) <= BBC(P) <= min(1,2|P|min(P))` under nonempty values in [0,1]. Then Bon's strong theorem extends to BBC with an alternative factor 2. **O9:** formalize the strict-null discordant-tie lazy-random-walk recurrence and `t1PValue=1`; this obstructs blanket scalar strong rejection for pure Cauchy/CBC. Neither new gate is checked in Lean. See [CombinationStrong.md](CombinationStrong.md).


## New combined finite-sample pipeline proof gates

**B0 (not kernel-closed):** Establish the full finite oriented-test universe
J<=7*choose(n,4), and give an explicit finite bound H_n on the **product**
of nested Bon/BBC correction multipliers. A bound based only on the final
layer cardinality is insufficient for multi-stage composition.

**B1 (not kernel-closed):** Compose original T1/T3/LRT-star tail sandwiches,
method-of-types KL bound, and the conservative alpha_m=(m+1)^(-100) to obtain
simultaneous false-null probability <=J/(m+1)^2.

**B2 (not kernel-closed):** Prove the minimum positive off-null distance
and the single-coordinate Hoeffding event: on d_m<delta_*/6, every
alternative p-value <=exp(-m*delta_*^2/8).

**B3 (not kernel-closed):** Compose the same d_m event with the WQC bad-tree
gap and normalized guide regret, then the TOB-QMC T3 and ECToBlob Bon/BBC
deterministic reconstruction theorems. State all model/cover/selection
conditions explicitly. See [PipelineBounds.md](PipelineBounds.md), (B5).

**B4 (not kernel-closed):** Sum the finite-m error bound over m>=M,
including candidate-availability and regret failures, to prove the
(B6) tail-of-time bound. Mere convergence in probability of the guide
is not sufficient; use a.s. eventual validity or summable failures.

The companion [HANDOFF.md](HANDOFF.md) separates these new handproofs from
existing Lean-checked tail/reference lemmas and identifies the lowest-risk
first formalization gate.
