# TOB-QMC: prescribed schedules and almost-sure eventual recovery

**Status: new handproof-level compositions and uncompiled proof source.** Sources are pinned to commit `a1102a1e6150db9bd2f119f12757ea0abb0354d6`. No change is proposed to the statements of the original paper or its archived proof routes.

## 1. T-levels: from existence to an explicit family of schedules

Under exactly the model/guide/cover hypotheses of `TOBQMC.consistency`, replace its existential alpha by a supplied sequence satisfying

    alpha_m > 0,
    alpha_m -> 0,
    log(alpha_m)/m -> 0.

Then the same consistency-in-probability conclusion follows for any fixed beta > 0. For conventional test levels one can take beta in (0,1). For the T3 variant use the hypotheses of `TOBQMC.consistencyT3_of_offModel`: a binary level-1 NMSC network, standard metric/inheritance assumptions, T-quartet nonanomaly and every non-treelike quartet CF outside the T3 model. Exact WQC and a valid disjoint cover remain the guide/detection assumptions in this direct wrapper.

**Handproof:** In the existing proof, replace the call to `TINNiK.exists_levels` by `TINNiK.rejects_of_log`. Use `TINNiK.tests_correct` with the supplied convergence of alpha. The remainder is the existing WQC guide-refinement event plus `TOBQMC.theorem2`. For T3, replace `exists_levels_t3` by `t3Rejects_of_log` and use `tests_correct_t3_of_t3Detectable`. All of these ingredients already exist; see the proposed proof bodies in `drafts/TOBQMCExplicitLevels.lean.txt`.

One explicit choice is

    alpha_m = Pr(chi-square_1 > log m),  m >= 1.

The harmless value at m=0 can be defined by the existing Lean function. Another family is alpha_m=(m+1)^(-a) for any fixed a>0. The first choice uses the exact same analytic lemmas already present in `TINNiK.theorem4_explicit` and `theorem4T3_explicit`. The novelty here is the **TOB-QMC composition**, not the schedule itself.

The raw quartet search may be data-dependent, provided it retains the required disjoint cover and only adds valid 2+2 quartets around each candidate split. A finite randomized budget that does not guarantee such a cover is not automatically covered. The search variants in `BipartitionSearch.lean`, `BipartitionSearchT3.lean` and `Implementation.lean` should get analogous schedule wrappers after the basic wrapper is reviewed.

## 2. Strong consistency with the original T3 p-value: a simpler proof

The stronger, **preferred** argument is now
[OriginalPValuesStrong.md](OriginalPValuesStrong.md). The existing
`half_chiSqOneTail_le_t3PValue` gives a **uniform** lower
bound for every selected quartet orientation, and
`t3PValue_le_chiSqTwoTail` gives the alternative upper bound.
Use `alpha_m=(m+1)^(-100)` and any fixed
`beta in (0,1)`. A multinomial method-of-types bound yields
the **finite-sample null-error bound**
`P(false reject of one true T3 null) <= (m+1)^(-2)`,
hence only finitely many null errors almost surely. The
off-T3 alternative has an exponentially summable missed-rejection
bound whenever the positive KL separation exceeds the explicit
threshold. Combine this with the already proved a.s. WQC/ASTRAL
guide refinement and deterministic level-1 reconstruction.

**New stronger possibility:** since the T3 p-value sandwich is
uniform over every selected orientation, TOB-QMC's
**blob/non-blob contraction classification** does not
asymptotically need a maximum-likelihood orientation selector,
merely a valid quartet orientation. This is *not* a claim for
TINNiK's separate inferred quartet-tree output, which does
need a correct orientation.

This is a handproof until the LRT/KL bridge, method-of-types
bound, Borel--Cantelli coupling and reconstruction
composition are kernel-checked. The exponent 100 is a
conservative mathematical witness, not a recommended finite-m
operational setting. This does NOT prove the corresponding
cut-test strong result; its reference tail needs separate
analysis.

## 3. Every polynomial level: pathwise T3 theorem

[OriginalPValuesStrong.md §10](OriginalPValuesStrong.md#10-stronger-schedules-every-fixed-polynomial-exponent-without-a-new-gaussian-cone-estimate) derives the stronger schedule window from a dyadic Hoeffding--Doob maximal inequality and the **existing** T3 tail sandwich. In particular, every fixed `alpha_m=(m+1)^(-a)`, `a>0`, is sufficient for the proposed almost-sure TOB-QMC-T3 theorem. No new Gaussian-cone lower bound is needed; the remaining gate is the dyadic maximal lemma and its likelihood/statistic bridge.

### Pathwise strong consistency (not a corollary of weak convergence alone)

Assume fixed n, iid complete binary gene trees, the T3 level-1 hypotheses above, and positive quartet coordinates. In particular a truly tree-like quartet has a unique matching resolution and is off the centroid. Let alpha_m eventually lie in (0,1), and put h_m=-log(alpha_m). A sufficient stronger schedule condition is

    h_m / log log(m+e^e) -> infinity,
    h_m / m -> 0.

Keep any fixed beta in (0,1). Then the mathematical TOB-QMC T3 estimator with an eventually refining guide and a sufficient disjoint cover is eventually correct almost surely. Exact WQC or the specified exact ASTRAL dynamic program supplies guide refinement under its own model assumptions. The almost-sure claim also permits a data-dependent valid cover and additional searched quartets.

Polynomial schedules alpha_m=(m+1)^(-a), a>0, and the chi-square-one tail at log m satisfy the window. A decreasing sequence with only h_m->infinity and h_m=o(m) is sufficient for the existing weak argument but is **not automatically sufficient for this strong argument**; the lower separation from log-log fluctuations matters.

### Scalar pathwise lemma needed

For each fixed regular tree-like quartet, the correct branch of the likelihood-ratio statistic is O(log log m) almost surely, by the multinomial law of the iterated logarithm and a local quadratic expansion. For every fixed non-tree-like quartet off T3, its minimum likelihood-ratio statistic divided by m converges to a strictly positive KL projection gap.

The p-values in this repository are parameter-dependent Gaussian-cone tails, not simply a chi-square-one tail. One must therefore justify the following bounds for the **actual definitions**:

    null:       -log p_m = O(log log m) a.s.;
    alternative: p_m <= exp(-c m) eventually a.s., for some c>0.

**Update:** The earlier proposed Gaussian-rectangle argument is unnecessary for T3, because `half_chiSqOneTail_le_t3PValue` is already formalized and uniform over nuisance parameters. The dyadic maximal rate makes its null statistic O(log log m); the existing bound then gives `-log p_T3=O(log log m)`. Off model, the chi-square-two upper bound and positive statistic-growth gap give exponential decay. Fixed beta works because all quartet CFs are off the star centroid under the stated detectability hypotheses. The cut-test reference tail still requires separate work.

This geometric argument is the **new analytic proof gate**; the manuscript does not replace it by an assertion of asymptotic uniformity. It must be made precise for the exact cut/T3 tail definitions and the selected ML topology before a kernel-level theorem is claimed. An unqualified CDF convergence theorem at fixed thresholds is not enough for shrinking alpha_m.

### Reconstruction proof

Intersect these pathwise events over the finite oriented quartet universe before selecting a same-data guide or search path. For large m, every true-edge quartet is accepted by the appropriate tree test and every necessary false-edge witness is rejected, simultaneously; star classification is correct as well. The deterministic disjoint-cover theorem then contracts exactly the false refinement edges. Intersect with the guide's almost-sure refinement event. No independent guide sample is required.

## 4. Limits and boundary cases

- A fixed positive alpha does not in general give vanishing false-rejection risk at regular true cuts. Strong consistency is **not claimed for the shipped constant-alpha preset**.
- The T3 null is a union of the three oriented T1 half-segments. Pairwise-distinct CFs are sufficient but unnecessarily strong for its alternatives; keep the existing off-T3 hypothesis.
- The cut-model version needs its own detectability condition. Do not identify the equal-discordant full line, oriented T1 half-segment and T3 union.
- No universally good finite-sample choice follows from the schedule theorem. Every fixed exponent a>0 is asymptotically sufficient but can behave differently at 100–500 loci.
- The algorithm may use a near-optimal guide under the score-margin result in `GuideRegret.md`; this requires **vanishing normalized regret**, not merely an optimizer's name or a fixed approximation ratio.

## 5. Existing APIs used

- `src/TOBQMC/Consistency.lean`: `consistency`, `tendsto_optimaRefine`.
- `src/TOBQMC/ConsistencyT3.lean`: `t3Detectable_of_level1`, `tobqmcT3`, `consistencyT3_of_offModel`.
- `src/TINNiK/Basic.lean`: `rejects_of_log`, `tests_correct`, `theorem4_explicit`.
- `src/TINNiK/T3.lean`: `t3Rejects_of_log`, `tests_correct_t3_of_t3Detectable`, `theorem4T3_explicit`.
- `src/TOBQMC/Astral.lean`: `astral_refines_treeOfBlobs` and the candidate-superset variants.

The uncompiled wrappers target weak consistency, where the imported lemmas suffice. The stronger pathwise theorem is deliberately recorded separately from those wrapper bodies.
