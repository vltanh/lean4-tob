# Finite-sample pipeline bounds for the ORIGINAL T3/T1/LRT-star tests

**Status: new integrated mathematical handproof. No kernel compilation or CI.** This document composes the [original-p-value scalar concentration](OriginalPValuesStrong.md) with [approximate WQC guide score gaps](GuideRegret.md) and the **existing** deterministic reconstruction theorems. It strengthens the previous separate asymptotic conclusions into one auditable finite-sample inequality, without claiming that the current software defaults use this conservative schedule.

## 1. Model, fixed levels, and total correction amplification

Let \(X\) be a fixed set of \(n\ge4\) taxa and \(Q=\binom n4\). Draw \(m\ge1\) **iid complete binary gene trees** from a fixed distribution \(P\). Each oriented quartet coordinate is a Bernoulli variable across loci, with population probability \(p_s\) and empirical probability \(\hat p_s\). Define the *one event used by both stages*
\[
d_m=\max_{\text{all }3Q\text{ oriented quartet coordinates}}
    |\hat p_s-p_s| .
\]

Consider the original model tests with their exact definitions in \`src/Basic/Testing/Defs.lean\`, \`src/External/MitchellAllmanRhodes2019/T3Test.lean\`:
- T3 likelihood-ratio test using its original fitted-nuisance p-value, for any of the three orientations;
- T1 likelihood-ratio test using its original p-value, for any of the three orientations;
- **LRT star** test \(\exp(-T_\star/2)\) (not the Pearson option).

There are at most \(J=7Q\) distinct scalar tests in this **union** (three T3, three T1 and one star for each quartet). A given inference pipeline uses a subset. Let \(\mathcal K\) be their closed population null models, respectively the T3 union, oriented T1 half-segment and centroid.

Use the **predeclared, network-independent** level
\[
\boxed{\alpha_m=(m+1)^{-100}.}
\]
For general ECToBlob star tests take \(\beta_m=\alpha_m\). For the TOB-QMC T3 model or **binary ECToBlob with no centroid under Assumption 1**, a fixed \(\beta\in(0,1)\) is possible, under the separately stated population classification premises.

Allow combinations by **Bonferroni or BBC**. Each finite combination of \(k\ge1\) children satisfies
\[
\min_i p_i\le {\rm combine}(p_1,\ldots,p_k)
      \le c\,k\min_i p_i,\qquad
c=1\ (\mathrm{Bon}),\quad c=2\ (\mathrm{BBC}).
\]
Nested combinations multiply the factors along a selection chain. Define \(H_n\ge1\) to be a **deterministic upper bound on this total product across every possible stage/guide/coarsening with \(n\) taxa**. This replaces an incorrect shortcut of using only the size of the last family when combinations are nested. Finiteness of all candidate states at fixed \(n\) guarantees such an \(H_n\) exists. For a single Bonferroni layer with at most \(K_{\max}\) children, take \(H_n=K_{\max}\); for BBC use \(2K_{\max}\).

**We do not assume independence between quartets or between guide estimation and contraction.**

## 2. A simultaneous finite-sample null bound for the actual p-values

The original T3 p-value obeys the already formalized inequality
\[
\tfrac12\,\chi^2_1\text{-tail}(10T_3)
\le p_{\rm T3}
\le e^{-T_3/2}.
\]
The original T1 p-value obeys
\[
\chi^2_1\text{-tail}(T_1)
\le p_{\rm T1}
\le e^{-T_1/2}.
\]
The LRT star p-value equals \(e^{-T_\star/2}\). The existing \`log_chiSqOneTail_ge\` tail bound implies, with the deliberately conservative choice 100, that for **every** one of these scalar tests, at a genuine population null,
\[
\{p_{\rm scalar}< (m+1)^{-100}\}
\subseteq\{T_{\mathcal K}>8\log(m+1)\}.
\tag{B1}
\]
The likelihood-ratio/KL identity is
\[
T_{\mathcal K}=2m\inf_{z\in\mathcal K}
                {\rm KL}(\hat p_q\|z).
\]
Under a true null, a multinomial method-of-types bound gives, for every \(m\ge1\),
\[
\Pr(T_{\mathcal K}>t)\le(m+1)^2e^{-t/2}.
\]
Hence
\[
\Pr(\text{some true-null scalar comparison falsely rejected at }m)
\le\frac{J}{(m+1)^2}.
\tag{B2}
\]
This holds across the **entire test universe**, irrespective of any subsequent same-data guide, choice of orientation or chosen combination. Unlike a claim of exact superuniformity for the original p-values, this is a conservative finite-sample proof route. Its type-count and typed LRT/KL bridge are still **handproof-level obligations**, not currently kernel checked.

## 3. A single concentration event controls every alternative AND the guide

Let \(\delta_*>0\) be the smallest positive \(L^1\) distance
\[
\delta_*=\min_{\substack{\text{required off-null}\\
                  \text{scalar comparison }(q,\mathcal K)}}
 \inf_{z\in\mathcal K}\|p_q-z\|_1 .
\]
There are finitely many comparisons; if none are off-null, omit the alternative separation condition. On the event \(d_m<\delta_*/6\), each quartet has \(L^1\) empirical error less than \(\delta_*/2\), so Pinsker yields
\[
T_{\mathcal K}
=2m\inf_{z\in\mathcal K}{\rm KL}(\hat p_q\|z)
\ge m\delta_*^2/4
\]
at **every** required alternative. Their original p-values are all at most \(e^{-m\delta_*^2/8}\). Consequently, if
\[
\boxed{\frac{m\delta_*^2}{8}>
       100\log(m+1)+\log H_n,}
\tag{B3}
\]
every required alternative is rejected **even after all allowed nested Bon/BBC combinations**. For a fixed-beta star phase, also require \(m\delta_*^2/8>\log(H_n/\beta)\) if that phase combines p-values. If beta is \(\alpha_m\), B3 covers it.

Now consider WQC guide selection, with empirical score normalized by \(mQ\). Assume the population WQC objective has gap \(\Delta>0\) separating its optimum from every binary tree that does **not** refine the true ToB. Let the guide search space contain a population-optimal tree except with probability \(a_m\). Let the guide's normalized empirical optimization regret be at most a fixed \(r<\Delta\) except with probability \(b_m\). These events may depend on the same loci.

The deterministic score-margin lemma in [GuideRegret.md](GuideRegret.md) says \(2d_m+r<\Delta\) forces guide refinement. Therefore put
\[
x=\min\{\delta_*/6,\;(\Delta-r)/4\}>0.
\]
On \(d_m<x\), both the guide and **all alternatives** are correct when B3 holds. The common-coordinate Hoeffding bound gives
\[
\Pr(d_m\ge x)\le 6Qe^{-2mx^2}.
\tag{B4}
\]
The dimension here is **\(3Q\) Bernoulli coordinates**, not \(3Q\) independent samples. The correlations between quartets at the same locus are irrelevant to this union bound.

## 4. Combined finite-sample end-to-end risk theorem

Assume the relevant **deterministic reconstruction theorem** has the following property: whenever the guide refines the ToB and every scalar test along every allowed contraction/search state makes its population-null/alternative decision correctly, the pipeline returns exactly the true ToB. Use:
- **TOB-QMC-T3**, under its binary level-1, T-quartet-nonanomalous, off-T3 alternative, valid witness cover and selection requirements;
- **ECToBlob with LRT star, T1 and Bon/BBC**, under both directions of Assumption 1 at the actual law, and its specified valid combination/coarsening semantics.

This theorem does **not** automatically apply to TOB-QMC's other cut-test p-value or ECToBlob's Pearson star test, Cauchy/CBC, or an undocumented search mode. The current deterministic theorems/implementation hypotheses must be matched precisely in the eventual Lean statement.

When B3 (and the fixed-beta alternative condition, if relevant) holds, the **mathematical** pipeline has
\[
\boxed{\Pr(\widehat B_m\ne\mathrm{ToB}(N))
  \ \le\ \min\left\{1,\;
   a_m+b_m+\frac{J}{(m+1)^2}+6Qe^{-2mx^2}\right\}.}
\tag{B5}
\]
This is simply the union of (i) unavailable population-optimal candidate, (ii) excessive guide regret, (iii) *some* true-null test falsely rejected, and (iv) the **single** coordinate-error event handling all off-null tests and guide score errors. No sample splitting or test/guide independence is used.

If a **known-good fixed guide** is supplied, set \(a_m=b_m=0\) and use \(x=\delta_*/6\); there is no need to assume a population WQC gap. If a guide is arbitrary and may be wrong, the same local test event yields **correct coarsening to \`limitTree N T_m\`**, rather than exact ToB, for the ECToBlob deterministic arbitrary-guide framework. It is incorrect to report full ToB recovery when genuine guide splits are missing.

### Exact constrained ASTRAL specialization

If the allowed search space includes every input gene-tree bipartition and the optimizer is exact, set \(b_m=0\). Choose one fixed population-optimal binary tree \(T^*\). Under the NMSC positive gene-tree-probability hypothesis, let \(\pi_s>0\) denote the probability that one input gene tree contains split \(s\in\mathrm{Splits}_{\rm int}(T^*)\). By an elementary missing-split union bound,
\[
a_m\le\sum_{s\in\mathrm{Splits}_{\rm int}(T^*)}
             (1-\pi_s)^m
    \le\sum_s e^{-m\pi_s}.
\]
Thus B5 is an **explicit, network-parameter-dependent finite-sample upper bound** for exact ASTRAL plus either eligible contraction algorithm, without assuming the guide is magically correct. The \(\Delta,\delta_*,\pi_s\) quantities are **analysis constants**, not tuning inputs.

## 5. Tail-of-time bound and almost-sure consistency

Suppose \(r,\Delta,\delta_*,H_n\) are fixed, B3 holds for all \(m\ge M\), and \(\sum_{m\ge1}(a_m+b_m)<\infty\). Summing B5 without the cap gives
\[
\boxed{
\Pr\left(\exists m\ge M:\widehat B_m\ne\mathrm{ToB}(N)\right)
\le
\sum_{m\ge M}(a_m+b_m)
+\frac{J}{M}
+\frac{6Qe^{-2Mx^2}}{1-e^{-2x^2}} .
}
\tag{B6}
\]
The right-hand side tends to zero as \(M\to\infty\), so Borel--Cantelli gives eventual exact recovery **almost surely**:
\[
\Pr(\exists M\;\forall m\ge M:\widehat B_m=\mathrm{ToB}(N))=1.
\]

The **strong consistency and finite-sample bounds are at the handproof level** until the scalar method-of-types theorem, LRT/KL identities, combinator sandwich, deterministic reconstruction bridges and candidate-space event are formalized. A merely \(o(m)\) regret bound **in probability** is not enough for the almost-sure form without an eventual pathwise/summability property.

## 6. Why this is stronger, and the remaining limitations

- B5 uses the **original p-values**, not an alternative method-of-types-calibrated p-value. The schedule is unusually conservative, not empirically optimal.
- B5 combines guide misspecification and quartet-test errors in **one matched-data bound**; it does not treat guide and contraction data as independent.
- B6 is an **any-future-time** error bound, not just \(\Pr(\widehat B_m\ne B)\to0\).
- This does not prove that a particular practical heuristic has small regret, or that the current constant-alpha TOB-QMC/ECToBlob defaults are asymptotically consistent.
- The result assumes fixed taxa, a fixed identifiable distribution, iid complete binary gene trees, a **positive alternative separation** and an exact-or-certified guide optimizer.
- No fixed-fraction adversarial gene-tree corruption, systematic estimation bias, increasing-taxon regime, native numerical correctness or Cauchy/CBC almost-sure theorem is established.

## 7. New Lean gates

The hard dependencies are (a) typed \(T=2m\,{\rm KL}\) for the three original test null models, (b) the finite-support method-of-types bound and Borel--Cantelli, (c) the **Bon/BBC nested-factor** lemma and (d) the exact deterministic reconstruction API for every tested option. The score-margin lemma and universal tail comparisons have proposed Lean proofs or already checked source lemmas. See [the updated ledger](FORMALIZATION.md).

**No Lean compilation, CI or kernel audit was run for this proposal.**
