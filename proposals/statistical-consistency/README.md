# Stronger statistical consistency: proposal and handproofs

**Status: source-only proposal, 2026-11-02. No Lean, Lake, CI, kernel audit or compilation has been run for these additions.** Nothing in `src/`, the paper statements, Palomar records, dependency versions or workflow configuration is changed. Existing formalized results are distinguished from the new, uncompiled compositions below. This proposal is based on repository commit `a1102a1e6150db9bd2f119f12757ea0abb0354d6`.

## Results proposed

| ID | Strengthening | Status of this addition |
| --- | --- | --- |
| T-levels | Replace TOB-QMC's existential level sequence by **every prescribed** positive alpha_m tending to zero with -log(alpha_m)=o(m), including one network-independent explicit sequence | Handproof by composition of existing lemmas; complete proposed Lean proof bodies in an uncompiled `.lean.txt` draft |
| T-strong | TOB-QMC's cut/T3 reconstruction becomes **eventually exactly correct almost surely** for levels in a stronger log-log separation window | New pathwise handproof, with analytic/formalization gates identified |
| E-strong | ECToBlob with **Bonferroni combination** becomes eventually correct almost surely, uniformly over same-data guides/coarsening paths under its identification hypotheses | New pathwise handproof; no claim for Cauchy/CBC/BBC |
| E-fixed-beta | For **binary networks under Assumption 1**, the star level beta may stay fixed in (0,1); only alpha needs to shrink | New composition; genuine star-centroid cases are explicitly excluded |
| G-regret | Guide optimization need not be exact: **o(m) raw WQC regret** relative to an available population-optimal tree suffices, with a quantitative score-margin bound | Elementary handproof and uncompiled deterministic Lean lemma |
| C-types | A separate **finite-sample-valid conservative calibration** gives explicit null-error and alternative-detection bounds, hence summable failures | Full elementary method-of-types handproof; a proposed calibration variant, NOT a theorem about current default p-values |

Read [TOB-QMC](TOBQMC.md), [ECToBlob](ECToBlob.md), [guide optimization](GuideRegret.md), [finite-sample calibration](FiniteSample.md), and [proof gates](FORMALIZATION.md).

## What is already in this repository

- `TINNiK.theorem4_explicit` and `TINNiK.theorem4T3_explicit` already supply an explicit level based on the chi-square-one upper tail at log(m). We do **not** claim to have discovered that schedule.
- `TINNiK.rejects_of_log`, `TINNiK.t3Rejects_of_log`, `TINNiK.tests_correct`, and `TINNiK.tests_correct_t3_of_t3Detectable` supply the analytic ingredients for T-levels.
- `TOBQMC.theorem1_optimal` and `TOBQMC.astral_refines_treeOfBlobs` already give almost-sure guide refinement for the specified exact objectives/search spaces. The new result is relaxation to vanishing normalized optimization regret, not a retrospective certificate for arbitrary software.
- `ECToBlob.theorem8_2_levels` already permits subexponentially decreasing positive levels. The new proposal strengthens convergence mode and treats data-dependent guides and fixed beta in the no-centroid binary setting.
- `ECToBlob.Coarsening.limitTree` and the binary-network arbitrary-guide intersection result already exist. Here we propose their **pathwise** counterpart; the underlying structural target is not new.

## Main distinctions

All limits are for **fixed taxa and a fixed identifiable data-generating law**. The number of loci is m; n denotes taxa. The sampling unit is the locus. Quartets within a locus need not be independent.

For reference, convergence in probability is

    P(output_m = target) -> 1.

Strong consistency here means

    P(exists M, for every m >= M, output_m = target) = 1.

The latter does not follow merely from the former, nor merely from an asymptotically uniform p-value. The new proofs require pathwise control of null fluctuations and alternative separation.

No new result is claimed to establish better finite-sample accuracy, unconditional anomalous-network identifiability, robustness to arbitrary persistent gene-tree bias, growing-taxon consistency, or floating-point soundness. In particular the finite-sample calibration is deliberately conservative and is not recommended as a production default without experiments.

## Paper ownership and QWC

TOB-QMC results are kept in the TOB-QMC proposal, ECToBlob results in the ECToBlob proposal. Shared statistical lemmas are separated. There is no new build dependency on QWC. A companion QWC theory update can cite these results for guide refinement and robustness while retaining its own evidence-model proofs in its repository.

## Reading order / finite gates

1. Check the explicit-level proof bodies against the existing API; they contain no `sorry`, but **have not been elaborated**.
2. Formalize the elementary deterministic guide-gap lemma, then its probability and asymptotic consequences.
3. Establish uniform pathwise scalar-test tail bounds; this is the real missing analytic gate for T-strong/E-strong.
4. Feed simultaneous correct-test events into the existing deterministic reconstruction theorems.
5. Prove the exact method-of-types error bound before implementing a certified-calibration variant.

Compilation and CI remain deliberately deferred. These files must not be added to a build/audit target as though already verified.
