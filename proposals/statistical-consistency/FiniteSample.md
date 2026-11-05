# An optional finite-sample-valid calibration via multinomial types

**Status: complete elementary handproof at the mathematical level, not Lean checked.** This section proposes a DIFFERENT conservative test calibration. It does not claim that existing nominal chi-square p-values or QWC integrated-null Bayes factors already satisfy these finite-sample bounds. No runtime default is changed.

## Relation to the new ORIGINAL-p-value result

[OriginalPValuesStrong.md](OriginalPValuesStrong.md) uses
this same method-of-types *statistic bound* to establish
an explicit, very conservative shrinking-level guarantee
for the **already implemented T1/T3/LRT-star p-values**,
via **already formalized** upper/lower chi-square-tail
sandwich inequalities. That result keeps the original
p-value definitions; the `p_type` proposed here is
a *different, optional* finite-sample calibrated p-value.
Do not conflate the two or imply that the original
p-values are exactly super-uniform at every finite sample.

## 1. Uniform bound for a composite quartet null

Let Y_1,...,Y_m be iid observations with values in three quartet resolutions, m>=1. Let p be their distribution, hat p the empirical frequencies, and K a nonempty closed subset of the probability simplex. Examples include the centroid, an oriented matching-cut segment, or the union of the three matching-cut segments. Use extended KL with the usual zero-coordinate conventions. Define

    Lambda_m = 2m inf_{z in K} KL(hat p || z).

If p belongs to K, then for every t>=0,

    P_p(Lambda_m >= t) <= min(1, (m+1)^2 exp(-t/2)).                 (F1)

**Proof.** For any attainable type h, its multinomial coefficient is at most exp(m H(h)). This follows by evaluating the probability of that type under h itself: a probability is at most one. Hence P_p(hat p=h) <= exp[-m KL(h||p)]. There are choose(m+2,2) <= (m+1)^2 possible types. Since p is one of the null candidates, Lambda_m <= 2m KL(hat p||p). Summing the type bound over the event proves (F1), including boundary p where unattainable types have probability zero.

Consequently

    p_type = min(1, (m+1)^2 exp(-Lambda_m/2))

is a valid finite-sample p-value uniformly over this composite null. This is an exact probabilistic bound, not an appeal to an asymptotic reference chi-square law. Computing the KL projection at the centroid/T1/T3 models uses the already familiar quartet likelihood geometry.

## 2. A fixed, no-user-tuning sequence with summable null error

Suppose at most J distinct oriented/null-model comparisons may be used, with J fixed by the taxa and list of models. For example, all three oriented T1 comparisons plus one star comparison per quartet give J=4*choose(n,4). If T3 union comparisons are added, include them in J as well.

Reject a null when

    Lambda_m > tau_m,
    tau_m = 2 log[J (m+1)^4].                                      (F2)

This is equivalent to using p_type < 1/[J(m+1)^2]. By (F1) and a union bound,

    P(any true-null comparison rejected at m) <= 1/(m+1)^2.        (F3)

No independence across comparisons is needed. The sum over m is finite, so Borel-Cantelli gives **only finitely many true-null rejections almost surely**. For every M>=1, the probability of any true-null error at a sample size m>=M is at most 1/M, by summing (F3). This late-error bound is explicit. It is not a claim that the overall probability of any error from the first locus is 0.05.

The constants here are predetermined design choices. They may be conservative; no finite-sample accuracy optimality is implied.

## 3. Explicit alternative separation

For a fixed off-model p, put delta=inf_{z in K} ||p-z||_1>0. If ||hat p-p||_1<delta/2, then Pinsker and the triangle inequality give

    Lambda_m >= m*delta^2/4.

Coordinatewise Hoeffding gives

    P(||hat p-p||_1 >= delta/2) <= 6 exp(-m*delta^2/18).

Therefore, whenever m*delta^2/4 > tau_m,

    P(off-model comparison is not rejected) <= 6 exp(-m*delta^2/18). (F4)

For at most J off-model comparisons with minimum gap delta_*>0, combine (F3) and (F4): after the explicit separation condition is met,

    P(any local comparison is incorrect)
      <= 1/(m+1)^2 + 6J exp(-m*delta_*^2/18).                      (F5)

These errors are summable, so every comparison is simultaneously correct for all sufficiently large m almost surely. For M beyond the separation onset, a late-error bound is

    1/M + 6J exp(-M*delta_*^2/18) / (1-exp(-delta_*^2/18)).

The gap delta_* is for analysis; the schedule itself does not use it.

## 4. Safe use with Bonferroni-combined reconstruction

The local bound is not by itself a statement about every software pipeline. To feed calibrated p_type values into Bonferroni edge/tree tests at a_m=1/[J(m+1)^2], account for the largest combination-size factor K_max. A true-null family remains accepted if each true-null p_type >= a_m. A family with an alternative is rejected when an alternative p_type < a_m/K_max.

Thus replace the alternative separation requirement by

    m*delta_*^2/4 > tau_m + 2 log K_max.                           (F6)

For a single layer combining at most J distinct comparisons, K_max<=J. If an implementation nests corrections, use its actual bounded amplification factor, not silently J. Since n is fixed, K_max is constant and (F6) still eventually holds. The same union bounds apply.

An ECToBlob-style calibration variant may use p_type for star and T1 tests with Bonferroni combination. Its topology conclusion then follows from the existing deterministic reconstruction theorem whenever the graph-identifiability and guide assumptions hold. TOB-QMC may use the calibrated T3/cut tests with its sufficient cover, but correct ML topology selection and guide refinement must also be accounted for.

For a full pipeline, add the guide-failure probability and any required ML-topology-selection failure probability to (F5). Strict positive population topology gaps give ordinary exponential ML-selection error bounds. Do not omit these terms from a claimed end-to-end finite-sample theorem.

## 5. Why this is an optional proposal, not a silent upgrade of existing guarantees

The schedule changes the calibration and potentially power. Its purpose is to obtain a demonstrable finite-sample guarantee and a simple strong-consistency route. Current TOB-QMC/ECToBlob p-values have their own boundary-aware reference laws, and QWC uses an integrated-null likelihood ratio; neither can simply inherit (F1) by changing a label.

The implementation and accuracy comparison of this variant are outside this source-only PR. The existing scalar statistics, deterministic topology lemmas and count model could be reused, but a corresponding typed API would need to be written and verified.
