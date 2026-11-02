# Strong consistency for the ORIGINAL quartet p-values: explicit conservative levels

**New handproof-level strengthening (2026-11-02). Not compiled, reviewed, or Lean-verified.**
This note supersedes the claim in the earlier proposal that the parameter-dependent Gaussian-cone T3 lower tail needs a new, hard geometric estimate. An **already formalized uniform lower bound** makes that step unnecessary. The missing work is instead the finite-sample method-of-types bound, its exact Lean bridge to the LRT definitions, and finite-universe/reconstruction composition.

This concerns **the original T1, T3 and LRT-star p-values defined in the repository**, not the different method-of-types p-value proposed in [FiniteSample.md](FiniteSample.md).

## 1. Already formalized inequalities

For every nonnegative quartet count vector and any choice of one of its three resolutions \(s\):

1. **T3** ([\`External/MitchellAllmanRhodes2019/T3Test.lean\`](../../src/External/MitchellAllmanRhodes2019/T3Test.lean)):
   \[
   \frac12\,\mathrm{chiSqOneTail}(10\,T_3)
   \ \le p_3(s)\ \le\ \exp(-T_3/2),
   \quad T_3=\mathrm{t3Stat}(c,q).
   \]
   The lower bound is \`half_chiSqOneTail_le_t3PValue\` (line ~725), the upper \`t3PValue_le_chiSqTwoTail\`. **Both hold for every fitted orientation**, including orientations not selected by maximum likelihood; the fitted T1 parameter automatically lies in \([0,1]\).
2. **T1** ([\`Basic/Testing/Tails.lean\`](../../src/Basic/Testing/Tails.lean)):
   \[
   \mathrm{chiSqOneTail}(T_1)
   \le p_1(s)\le\exp(-T_1/2),
   \quad T_1=\mathrm{t1Stat}(c,s),
   \]
   because \`chiSqOneTail_le_t1Tail\`, \`t1Tail_le_chiSqTwoTail\`, and nonnegativity of the fitted nuisance mean. The lower bound is independent of the fitted nuisance value.
3. **LRT star:** \(p_\star=\exp(-T_\star/2)\), exactly, with \(T_\star=\mathrm{starStat}\). This argument does **not** cover the Pearson star option without additional work.
4. **A lower bound for chi-square-one tails** is already formalized as
   \[
   \log\mathrm{chiSqOneTail}(t)\ge
      -C-t,\qquad C=1+\log\sqrt{2\pi},\qquad t\ge0.
   \]
   See \`log_chiSqOneTail_ge\` in \`Basic/Testing/Tails.lean\` (line ~626). The bound is very conservative but uniform.

These bounds are much stronger for this purpose than convergence of null p-values in distribution: they prevent the p-value from collapsing unexpectedly at any sample size or fitted nuisance parameter.

## 2. Exact multinomial likelihood-ratio identity

For any finite 3-category sample with empirical CFs \(\hat p_m\), let \(K\) be one of the following *closed* null subsets of the 2-simplex:

- the centroid \(\{(1/3,1/3,1/3)\}\) (star);
- one oriented T1 half-segment \(\mathcal C_s=\{(\theta,(1-\theta)/2,(1-\theta)/2):1/3\le\theta\le1\}\);
- the T3 union \(\bigcup_s\mathcal C_s\).

For the original LRT statistics \`starStat\`, \`t1Stat\` and \`t3Stat\`, respectively,
\[
T_K(m)=2m\,\inf_{z\in K}\mathrm{KL}(\hat p_m\|z).
\]
The T3 statistic is explicitly the minimum of the three T1 statistics. These identities follow from maximizing the saturated multinomial log-likelihood and the corresponding constrained likelihood; they still need typed Lean statements for the actual \`QuartetTree\` definitions. At empirical zero coordinates use \(0\log0=0\). The KL divergence is extended-valued if needed at an incompatible boundary; the constrained MLE exists because each \(K\) is compact.

If the population CF \(p\in K\), then
\[
T_K(m)\le2m\,\mathrm{KL}(\hat p_m\|p).
\]

## 3. Distribution-free finite-sample null control by types

For \(m\ge1\) iid categorical draws from *any* population \(p\) in the null \(K\), including distributions with zero coordinates, the standard type inequality is
\[
\Pr_p(\hat p_m=h)\le e^{-m\mathrm{KL}(h\|p)}
\]
for every attainable empirical type \(h\). There are \(\binom{m+2}{2}\le(m+1)^2\) types. Hence for all \(t\ge0\),
\[
\boxed{\Pr_p(T_K(m)>t)\le(m+1)^2e^{-t/2}.}\tag{O1}
\]

Crucially, this is a **finite-sample bound on the actual likelihood-ratio statistic**, even though the p-value uses an asymptotic Gaussian-cone reference law. It does *not* assert that the original p-value is exactly super-uniform at finite \(m\).

## 4. A universal, deliberately conservative ORIGINAL-p-value schedule

Put \(L_m=\log(m+1)\), \(\alpha_m=(m+1)^{-100}\), and
\[
t_m=8L_m.
\]

For \(T_3\le t_m\), the already checked T3 lower-tail inequality gives
\[
\log p_3(s)\ge
-\log2-C-10T_3
\ge-(\log2+C)-80L_m>-100L_m=\log\alpha_m
\]
for every \(m\ge1\) (using the elementary constant inequality \(\log2+C<20\log2\)). Hence, for **every fitted orientation** \(s\),
\[
\{p_3(s)<\alpha_m\}\subseteq\{T_3>t_m\}.
\]
For T1 the same implication follows with \(-C-T_1\), and for the LRT star test with \(-T_\star/2\). Consequently **under each respective true null**
\[
\boxed{
\Pr(p_{\mathrm{T1}}<\alpha_m),\
\Pr(p_{\mathrm{T3}}<\alpha_m),\
\Pr(p_{\mathrm{star,LRT}}<\alpha_m)
\ \le (m+1)^{-2}.}\tag{O2}
\]

For T3 the bound is even **uniform over the data-chosen fitted topology** because the event on the right depends only on \(T_3\), not on \(s\). If several different oriented T1 nulls are tested adaptively, take a union bound over their finite universe.

With \(J\) fixed possible comparisons, at a particular \(m\),
\[
\Pr(\hbox{some true null falsely rejected})\le J(m+1)^{-2}.
\]
The series over \(m\) converges, so Borel--Cantelli shows that *eventually every true-null comparison is accepted almost surely*, even if the guide, quartet search, model orientation and contraction trajectory depend on the same data. No within-locus quartet independence is assumed.

**Statistical cost:** exponent 100 is chosen for a short, provable bound, **not** for good accuracy at 100--500 loci. A better finite-sample schedule may require sharper tail inequalities and an empirical power comparison.

## 5. Explicit off-null power bound for the original p-values

Let \(p\notin K\) and \(\delta=\inf_{z\in K}\|p-z\|_1>0\). If \(\|\hat p_m-p\|_1<\delta/2\), Pinsker's inequality yields
\[
T_K(m)=2m\inf_{z\in K}\mathrm{KL}(\hat p_m\|z)
\ge m\delta^2/4.
\]
Three coordinatewise Hoeffding inequalities give
\[
\Pr(\|\hat p_m-p\|_1\ge\delta/2)\le6e^{-m\delta^2/18}.
\]

Every one of the original p-values above has an upper bound \(e^{-T_K/2}\). Hence, whenever
\[
m\delta^2/8>100\log(m+1)+\log K_{\max},
\]
where \(K_{\max}\ge1\) bounds the multiplicity of a relevant Bonferroni combination,
\[
\boxed{\Pr(p_{\mathrm{off-null}}\ge\alpha_m/K_{\max})
   \le6e^{-m\delta^2/18}.}\tag{O3}
\]
The same bound holds for LRT-star p-values. This shows that every off-model constituent is eventually rejected with an **exponentially summable** probability of failure.

The gap \(\delta\) is an unknown **analysis constant**, not a parameter required by the schedule. For fixed taxa, minima over the finitely many nonnull quartet/model comparisons are positive.

## 6. TOB-QMC-T3: an explicit almost-sure theorem target

Fix a binary level-1 NMSC network and iid complete binary gene trees. Assume the exact hypotheses of \`TOBQMC.consistencyT3_of_offModel\` (standard metric assumptions, T-quartet nonanomaly, every non-treelike quartet off the T3 null, and sufficient disjoint quartet covers). Let \(\alpha_m=(m+1)^{-100}\), and let \(\beta\in(0,1)\) be any fixed star level.

Then the proposed **stronger conclusion** for the mathematical TOB-QMC-T3 algorithm is
\[
\boxed{\Pr(\exists M\;\forall m\ge M:\ \widehat B_m=\mathrm{ToB}(N))=1.}\tag{O4}
\]

Proof: the T3 detectability conditions put all true treelike quartet distributions on the T3 null, all non-treelike ones off it, and exclude any centroid. For every quartet the LRT-star p-value is thus exponentially small almost surely, so the fixed \(\beta\) eventually lets the T3 test act. Apply O2/O3 simultaneously to all T3 p-values and all quartet orientations, and intersect the event with the already formalized almost-sure WQC or ASTRAL refinement event. The deterministic TOB-QMC Theorem 2 then contracts exactly the extra refinement edges. Borel--Cantelli upgrades *all local tests at once* to eventual pathwise correctness.

**Additional strengthening:** no ML requirement on the selected T3 orientation is needed for the **blob/non-blob classification** used by the TOB-QMC contraction step: the uniform T3 p-value sandwich holds for every resolution. Only require a valid selected resolution of each quartet, not a maximum-likelihood one. This claim concerns TOB-QMC's use of the \`testedB\` predicate, not the separate \`testedT\` output of TINNiK.

This does **not** extend TOB-QMC's sparse contraction guarantee to arbitrary-level or arbitrary incorrect guides. All quartets on a species tree are T3-treelike even if a guide displays the wrong split; the orientation-free T3 oracle cannot discover that guide error.

## 7. ECToBlob-Bon: an original-test almost-sure theorem target

Fix a network of **arbitrary level**, including nonbinary networks, and an iid complete binary gene-tree law satisfying both directions of the appropriate ECToBlob Assumption 1. Use **LRT star**, **T1** tests, and **Bonferroni** correction, with
\[
\alpha_m=\beta_m=(m+1)^{-100}.
\]
There is **no need here to assume positive population quartet coordinates**: the type bound treats zero coordinates by their actual support, and the original universal T1 tail inequalities hold for all nonnegative count vectors. (Formalizing the boundary continuity and extended KL projection is an explicit task.)

Intersect the simultaneous true-null/nonnull events from O2/O3 over the complete finite quartet/resolution universe. At fixed taxa all possible guide/coarsening states and their Bonferroni combination sets belong to a finite universe with a uniform \(K_{\max}\). The original deterministic ECToBlob reconstruction theorem then gives, for **any** possibly data-dependent sequence of binary guides \(T_m\):
\[
\boxed{
\Pr(\exists M\;\forall m\ge M:\
\mathrm{ECToBlob}_{\mathrm{Bon,LRT}}(T_m,G_{1:m})
=\mathrm{limitTree}(N,T_m))=1.
}\tag{O5}
\]
Whenever the guides eventually refine ToB, the limit tree is the true ToB. For binary networks with the hypotheses of the existing arbitrary-guide coarsening theorem, the limit is the intersection of the guide with the true ToB.

For binary Assumption-1 networks, the existing no-trivial-four-blob result and the star converse rule out all true star-null quartets. **Then any fixed \(\beta\in(0,1)\)** can replace \(\beta_m\), with the shrinking \(\alpha_m\) unchanged. This must not be generalized to nonbinary networks containing a genuine centroid.

The Bonferroni combined p-value is \(\min(1,K\min_i p_i)\) for nonempty families. On a true null its false-rejection event implies that some true-null constituent has p<\(\alpha_m\); on an alternative it is enough that one off-model constituent has p<\(\alpha_m/K_{\max}\). This uses **no** independence of quartet tests.

## 8. Explicit tail-of-time and end-to-end error control

For \(J\) possible scalar tests, let \(\delta_*>0\) be the minimum \(L^1\) gap across the finitely many required nonnull tests. For sufficiently large \(m\), after the explicit O3 separation condition,
\[
\Pr(\hbox{at least one scalar test wrong at }m)
\le \frac{J}{(m+1)^2}
      +6J e^{-m\delta_*^2/18}.
\]
The probability of *any* such failure at some \(m\ge M\), for \(M\) beyond the separation onset, is at most
\[
\boxed{\frac{J}{M}+ \frac{6J e^{-M\delta_*^2/18}}
                                    {1-e^{-\delta_*^2/18}}.}\tag{O6}
\]
Add the guide's error probability to obtain a finite-m end-to-end bound. For **tail-of-time** end-to-end control, a summable guide-error bound or an eventual a.s. guide result is needed; do not silently substitute a weak guide theorem.

## 9. What is proved already, and what remains

**Already kernel-checked in the existing repository:**

- \`half_chiSqOneTail_le_t3PValue\`, \`t3PValue_le_chiSqTwoTail\`;
- \`chiSqOneTail_le_t1Tail\`, \`t1Tail_le_chiSqTwoTail\`, \`log_chiSqOneTail_ge\`;
- the T1/T3/star **definitions**, the exact T3 null as the union of three T1 half-segments;
- TOB-QMC's deterministic level-1 contraction and exact WQC/ASTRAL almost-sure guide-refinement results;
- ECToBlob's deterministic coarsening \`limitTree\` and the binary no-trivial-four-blob result.

**New and NOT YET kernel-checked:** O1--O6, the finite-sample type-count and LRT/KL bridges, Borel--Cantelli/infinite-sample coupling, simultaneous same-data guide composition, and removal of the ML-orientation hypothesis from the T3 contraction pipeline. This source-only PR deliberately does not add \`src/\` declarations or modify the kernel-audited theorem inventory.

**Limits:** these are strong **fixed-taxon** results, not uniform in taxon number or vanishing alternatives. The original p-values at a fixed 0.05 significance level are not automatically consistent. Strong theorem status is handproof until the explicit gates in \`FORMALIZATION.md\` are closed.


## 10. Stronger schedules: every fixed polynomial exponent, without a new Gaussian-cone estimate

The exponent-100 theorem above has a simple finite-sample bound. To reach an **arbitrary fixed polynomial exponent**, use a dyadic maximal Hoeffding argument, **not** a new Gaussian-cone calculation. This is a further handproof-level result; the probability and count-statistic bridges have not yet been formalized.

### Dyadic maximal concentration

Let \(Y_i\in[0,1]\) be iid with mean \(p\), and \(S_k=\sum_{i=1}^k(Y_i-p)\). Hoeffding's exponential moment bound and Doob's maximal inequality applied to the nonnegative submartingale \(\exp(\lambda S_k)\) yield
\[
\Pr\left(\max_{k\le N}|S_k|\ge t\right)\le2\exp(-2t^2/N).
\]
For each sign, use \(\mathbb E e^{\lambda S_N}\le e^{N\lambda^2/8}\) and minimize at \(\lambda=4t/N\).

Take \(N=2^{j+1}\) and \(t_j=2\sqrt{2^j\log(j+1)}\). Then the maximum-error event has probability at most \(2(j+1)^{-4}\), which is summable. Borel--Cantelli implies that eventually, on each dyadic block \(2^j\le m<2^{j+1}\),
\[
\left|\frac{S_m}{m}\right|
\le2\sqrt{\frac{\log(j+1)}{2^j}}
=O\!\left(\sqrt{\frac{\log\log m}{m}}\right)
\quad\text{almost surely}.
\]
Apply this to the finitely many quartet/resolution indicator variables. Only independence **across loci** is used.

### Null-statistic and original-p-value bounds

For a true null \(p\in K\), the original statistic satisfies
\[
T_K(m)\le2m\,\mathrm{KL}(\hat p_m\|p).
\]
On the positive support of \(p\), KL is locally quadratic. Coordinates with \(p_i=0\) are identically zero almost surely, so they can be omitted. The dyadic rate gives
\[
T_K(m)=O(\log\log m)\quad\text{almost surely}.
\]

The existing T3/T1 chi-square-tail **lower bounds**, and the exact star-LRT formula, therefore imply
\[
-\log p_{\mathrm{original}}(m)=O(\log\log m)
\quad\text{at every true null, almost surely}.
\]
This is uniform over the finite oriented quartet universe and does not require selecting the fitted T3 topology independently.

For every off-model \(p\notin K\), the strong law and continuity of the constrained KL projection give \(T_K(m)/m\to2I_K(p)>0\), and the original **upper** tail bounds give
\[
-\log p_{\mathrm{original}}(m)\ge m I_K(p)+o(m).
\]
Thus every predetermined positive level with
\[
\boxed{
\log\log m=o(-\log\alpha_m),\qquad
-\log\alpha_m=o(m)
}
\]
separates all true and false quartet nulls **eventually almost surely**. The analogous condition on \(\beta_m\) applies to true star-null quartets in nonbinary ECToBlob. In particular,
\[
\alpha_m=(m+1)^{-a},\quad \beta_m=(m+1)^{-b},\qquad a,b>0
\]
are sufficient; TOB-QMC-T3 and binary ECToBlob can instead keep any fixed \(\beta\in(0,1)\). The pre-existing ECToBlob schedules \(\alpha_m=\Pr(\chi_1^2>\log m)\) and \(\beta_m=m^{-1/2}\) also meet this window.

**Upgrade to O4/O5:** the same strong-consistency theorem targets hold for this entire schedule window, conditional on formalizing the dyadic maximal lemma and the LRT/KL bridge. The window is sufficient, not necessary. It does not imply good finite-sample accuracy for every exponent.

### Verification status

The older alleged T3 Gaussian-cone lower-tail gap is **already closed in the underlying repository** by \`half_chiSqOneTail_le_t3PValue\`. The missing kernel work is the maximal concentration lemma, local quadratic KL bound, typed likelihood-ratio identity, Borel--Cantelli coupling and reconstruction. None is marked complete in this PR.
