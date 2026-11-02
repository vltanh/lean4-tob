# ECToBlob: strong consistency, same-data guides, and fixed beta for binary networks

**Status: new handproof-level extension. No Lean compilation.** The original corrected Theorem 8.2 and its generic/level variants remain untouched. This proposal initially restricts p-value combination to **Bonferroni**, avoiding unproved tail-cancellation arguments for Cauchy-based corrections.

## 1. Existing result versus proposed result

`ECToBlob.theorem8_2_levels` already gives convergence in probability for any positive alpha_m,beta_m tending to zero with log(alpha_m)/m and log(beta_m)/m tending to zero. It permits a fixed supplied ToB refinement and every algorithm option, with its additional positivity hypothesis for Cauchy/CBC.

The proposed strengthening has three components:

1. Upgrade to **eventual exact output almost surely** for a suitable schedule window.
2. Make the scalar-test event uniform over **all possible guide trees and coarsenings** at fixed n, allowing guide estimation and contraction to reuse the same loci.
3. For binary networks satisfying Assumption 1, keep **beta fixed in (0,1)**: there are no genuine star-null quartets, so the star test eventually rejects everywhere.

Items 1 and 3 are not claims about the package's fixed alpha=0.05 finite-sample preset.

## 2. A simpler strong theorem for the ACTUAL Bonferroni/LRT tests

See [OriginalPValuesStrong.md](OriginalPValuesStrong.md)
for the complete direct argument. The existing
`chiSqOneTail_le_t1Tail` and `t1Tail_le_chiSqTwoTail`
bound the original T1 p-value; `starPValue .lrt`
is exactly an exponential chi-square-two tail. A method-of-types
argument then gives the finite-sample false-null bound
`(m+1)^(-2)` for each constituent with the explicit,
network-independent sequence

```text
alpha_m = (m+1)^(-100)
beta_m  = (m+1)^(-100)
```

In contrast to the earlier regular-point argument, **this
approach also permits zero population quartet coordinates**
for the LRT-star/T1 tests, provided the corresponding KL
projection and finite-support boundary cases are formalized.
The same Bonferroni, finite-universe and deterministic
`limitTree` arguments cover arbitrary data-dependent
binary guide sequences and all fixed-taxon network levels.
For binary networks satisfying Assumption 1, fixed beta
is also available, as in Section 3.

The actual-p-value composition is **not Lean checked**;
it needs typed LRT/KL bridges, type-count probabilities and
Borel--Cantelli. It is intentionally limited to
`starTest=.lrt` and `testCo=.bon`, not the
Pearson/Cauchy/CBC/BBC alternatives.

## 3. Every polynomial level: Bonferroni/LRT-star/T1 theorem

[OriginalPValuesStrong.md §10](OriginalPValuesStrong.md#10-stronger-schedules-every-fixed-polynomial-exponent-without-a-new-gaussian-cone-estimate) establishes the broader handproof window by dyadic maximal concentration and the **existing** T1 tail sandwich. It covers every fixed positive polynomial exponent and the original paper's chi-square-tail schedule; the extra work is formalizing the maximal inequality and likelihood/KL bridge, not inventing a new Gaussian-cone lower bound.

### Pathwise Bonferroni argument for arbitrary Assumption-1 laws

Fix a phylogenetic network N, a finite labelled taxon set, and an iid law on complete binary gene trees. Assume both directions of ECToBlob Assumption 1 at this law. For this new analytic argument additionally assume all quartet CF coordinates are positive; finiteness gives a uniform eta>0 lower bound. This positivity restriction is stated explicitly rather than silently assuming the whole generality of the existing weak theorem.

Use the LRT or Pearson star test as defined in the repository, the defined T1 test, and Bonferroni combination. Let h_alpha(m)=-log alpha_m and h_beta(m)=-log beta_m satisfy, eventually,

    0 < alpha_m,beta_m < 1,
    log log(m+e^e) = o(h_alpha(m)),
    log log(m+e^e) = o(h_beta(m)),
    h_alpha(m), h_beta(m) = o(m).

For any possibly same-data sequence of binary guides T_m, the proposed pathwise conclusion is

    P(exists M, for every m>=M,
      ECToBlob_m(T_m) = limitTree(N,T_m)) = 1.

The target is the repository's existing `ECToBlob.Coarsening.limitTree`, not automatically intersection with the ToB for an arbitrary nonbinary network. If the guides eventually refine the true ToB, `limitTree` equals it and this gives strong exact recovery. For binary N under the assumptions below, the target is precisely `Splits(T_m) intersect Splits(ToB(N))`.

A fully explicit pair is alpha_m=beta_m=(m+1)^(-2). The paper's alpha based on chi-square-one at log m and beta=m^(-1/2), apart from harmless initial values, also satisfy the stronger window. The constant 2 is a fixed demonstration, not an optimal finite-sample recommendation.

### Scalar proof

For a true star-null p=(1/3,1/3,1/3), the LRT and Pearson statistics are O(log log m) almost surely; their chi-square-two upper tails are therefore at least exp(-C log log m) eventually. A non-star quartet has statistic m*c+o(m), c>0, so its star p-value decays exponentially.

For oriented T1, let Lambda_m be the likelihood-ratio statistic and mu_m the fitted mean in `t1Tail`. The actual definition has

    Pr(chi-square_1 > t) <= t1Tail(mu,t) <= Pr(chi-square_2 > t),  mu>=0.

The lower bound holds because the defining random variable is Z^2 plus a nonnegative term. For the upper bound, couple Zbar=mu+Z0: when mu>=0 its negative part is no larger in magnitude than the negative part of Z0, so Z^2 + (Zbar_-)^2 <= Z^2+Z0^2. The fitted T1 parameter ensures mu_m>=0.

At any positive-coordinate p on the closed T1 segment, the saturated-versus-null likelihood gap is at most the saturated-versus-true-p gap. A multinomial LIL plus the local KL expansion bounds it by O(log log m), including the centroid. Thus -log p_T1=O(log log m). At p outside the closed T1 segment, the constrained KL gap is positive and Lambda_m/m converges to a positive constant; the upper tail bound gives exponential decay.

The schedule window separates both regimes pathwise. This step is stronger than invoking asymptotic uniformity at a fixed threshold.

### Combining and adaptive contraction

For K p-values with K bounded by the finite oriented quartet universe,

    p_Bon = min(1, K * min_i p_i).

If all constituents satisfy their null, p_Bon is at least their minimum, which is eventually above the selected level. If any constituent is off-null, p_Bon is at most K times an exponentially small p-value, eventually below that level. No independence across quartets is needed.

There are finitely many guide topologies, coarsenings, edge-quartet sets and tree-quartet sets for fixed taxa. Intersect the scalar probability-one events first, then obtain one almost-surely finite sample index at which **every** required test on **every** candidate state is correct. Instantiate the existing deterministic `RunBy.ectoblobBy_eq` / `IsLimit.outputBy_eq` argument. The bi/quad/mul choices and early/late stopping rule do not affect this eventual conclusion when their corresponding deterministic predicates hold.

This is a handproof of the finite-universe argument and the analytic bounds. Its translation into the exact Lean definitions, measurable events and statistic expansions remains an explicit formalization task.

## 4. E-fixed-beta: binary networks do not need a vanishing star level

Assume in addition that N is binary. The repository proves

    not_hasTrivialFourBlob_of_isBinary.

The star converse of Assumption 1 then excludes the centroid for **every** quartet. Therefore each star statistic has a strictly positive linear growth rate and each star p-value tends to zero exponentially, simultaneously over all quartets and possible guides. For every fixed beta in (0,1), every nonempty combined star test is eventually below beta. The initial star-contraction phase eventually contracts **no edges**.

The remaining T1 phase still has the correct arbitrary-guide coarsening target. Hence the E-strong theorem holds with **fixed beta**, provided alpha satisfies its strong schedule window. This includes beta=0.8 or beta=0.95 mathematically; their finite-sample behaviour is not guaranteed by this argument.

**This does not extend to general nonbinary networks with true centroid quartets.** For such quartets, a fixed beta cannot be substituted into the above pathwise star-null argument. The earlier statement that ECToBlob always needs both levels to shrink was too broad: that is sufficient for the general theorem, not necessary in the binary no-centroid setting.

The positivity assumption in Section 2 is automatic for standard finite-parameter NMSC laws with the repository's positive-probability gene-tree property, but not for every abstract CF law permitted by its original theorem.

## 5. End-to-end guide composition

Intersect the uniform reconstruction event with an eventually-refining-guide event. This can be supplied by the exact ASTRAL/WQC theorem, or by the vanishing-regret criterion in `GuideRegret.md`, under their own assumptions. The proof uses the same loci for both stages; independence between stages is not assumed.

For a generic strictly quartet-nonanomalous **binary** network under independent inheritance (rho=0), the existing Proposition 5.1 and binary no-trivial-four-blob result supply the needed identification law. Together with exact ASTRAL refinement this gives the proposed strong end-to-end ECToBlob-Bon result, with an explicit alpha and **fixed beta**. This is a new composition, not an existing audited theorem.

## 6. Deliberate exclusions

The strong theorem here is not asserted for Cauchy/CBC/BBC, because extreme p-values and endpoint cancellations need a separate almost-sure analysis. The original weak theorems for those combinations retain their existing scope. No claim is made for fixed alpha at all sample sizes, arbitrary anomalous quartets, arbitrary persistent estimation bias, dependent observations without an appropriate pathwise frequency bound, or floating-point execution of the R package.
