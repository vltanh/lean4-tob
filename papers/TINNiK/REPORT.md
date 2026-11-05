# Audit of TINNiK and its formalization

Paper: E. S. Allman, H. Baños, J. D. Mitchell, J. A. Rhodes, *TINNiK: inference of the tree of blobs of a species
network under the coalescent model*, [Algorithms Mol. Biol. 19 (2024), 23](https://doi.org/10.1186/s13015-024-00266-2).
No author TeX source exists for it. The audit was made against the publisher's XML (PMC11539473), which includes TeX for
the equations but is not the authors' original TeX source. "Line N", or "TINNiK's text, line N", is a line of the plain
text of that XML, one line per paragraph, as [`docs/CONFIGURATION.md`](../../docs/CONFIGURATION.md) defines it. Section
and result numbers are the paper's.

This paper is one of four formalized in this repository ([`../../README.md`](../../README.md)). The findings are numbered
across the collection, and this report keeps those numbers: E29–E33, E40 and E75 on the paper, E82 on Mitchell et al. 2019, a
source it uses, and E34 for the typos.

Status of the formalization:

- **Unconditional.** No result of the literature is assumed.
- **Proved, by the paper's arguments** except for the departures of Section 7: every numbered result of TINNiK, that is
  Propositions 5 and 6, the estimates of Appendix C, and Theorem 4, with the paper's levels
  ([`TINNiK.theorem4`](../../src/TINNiK/Basic.lean#L629)). The maximum likelihood estimate of Appendix C.1 has no
  maximum on the open cut model at some counts (E31), and is read on the closed simplex.
- **Also proved, from what the paper says in passing:** the T3 option ([`TINNiK.theorem4T3`](../../src/TINNiK/T3.lean#L469)),
  the algorithm with missing taxa ([`TINNiK.theorem4_missing`](../../src/TINNiK/MissingTaxa.lean#L473)), neighbor
  joining in Step 4 ([`TINNiK.theorem4_nj`](../../src/TINNiK/NJ.lean#L35)), the counts behind its running times
  ([`src/TINNiK/Counts.lean`](../../src/TINNiK/Counts.lean)), the index of a set of four taxa in lex order of line 162
  ([`src/TINNiK/LexIndex.lean`](../../src/TINNiK/LexIndex.lean)), and the consistency of the outline of an algorithm in
  Section 5 of Allman et al. 2023, which TINNiK develops ([`TINNiK.outline_cut_consistent`](../../src/TINNiK/AllmanOutline.lean#L70)).
  [`TINNiK.theorem4_explicit`](../../src/TINNiK/Basic.lean#L657) also proves Theorem 4 for one sequence of levels,
  independent of the network and the parameters.
- **Proved cited results**: TINNiK's Theorem 1 (CF-detectability), Theorem 2 (the B-quartet inference rule) and the
  combinatorial part of its Theorem 3, which come from Allman et al. 2023, in [`src/AllmanEtAl2023/`](../../src/AllmanEtAl2023),
  which also proves that paper's own statements ([its folder](../AllmanEtAl2023/README.md)); Rhodes 2020, Theorem 2;
  Mitchell et al. 2019, Theorem 3.1 for the cut model, and Propositions 4.1, 4.2, 5.1, 5.2; that neighbor joining is
  exact on tree metrics (Saitou, Nei 1987; Studier, Keppler 1988) and Buneman's four-point theorem, in the library
  [`lean4-phylogenetics`](https://github.com/vltanh/lean4-phylogenetics); and that the Lemma of Studier and Keppler fails
  at a polytomy. Section 2 says which of these sources were read.
- **Statements**: one correction, E31, agreed with the user who requested this formalization. The library's statements
  leave out hypotheses that the proofs do not use (Section 5); [`src/MainResults/TINNiK.lean`](../../src/MainResults/TINNiK.lean)
  keeps the paper's.
- `lake build` passes with no warnings, and there is no `sorry`, `axiom`, `native_decide` or `implemented_by` in
  [`src/`](../../src). [`scripts/Audit.lean`](../../scripts/Audit.lean) checks every declaration of the project and of
  the library [`lean4-phylogenetics`](https://github.com/vltanh/lean4-phylogenetics), including private and generated
  ones, against the standard axioms [`propext`](https://leanprover-community.github.io/mathlib4_docs/Init/Core.html#propext),
  [`Classical.choice`](https://leanprover-community.github.io/mathlib4_docs/Init/Prelude.html#Classical.choice),
  [`Quot.sound`](https://leanprover-community.github.io/mathlib4_docs/Init/Prelude.html#Quot.sound).
- [`src/MainResults/TINNiK.lean`](../../src/MainResults/TINNiK.lean) states eight main theorems, of the paper and of
  the two sources Mitchell et al. 2019 and Studier, Keppler 1988, and proves them from the libraries.
  `scripts/check_kernels.sh papers/TINNiK/palomar/comparator.json` checks them under Lean's kernel, NanoDa (through
  Comparator's normal mode) and con-ron, and all three accept them. There is no separate Challenge: Comparator runs on
  that module as both challenge and solution, so it compares no separate statement file with a proof.
- **Proofs.** They follow the paper's, except the departures in Section 7. Two proofs of the paper's results depart from
  it: Theorem 4 under the alternative, which repairs a gap (E33), and Proposition 5, by the central limit theorem, since
  Lean lacks van der Vaart's Theorem 16.7. Of the cited results, neighbor joining repairs a gap, and Mitchell et al.'s
  Propositions 4.1 and 5.1 go by the central limit theorem too. Buneman's four-point theorem and the T3 theorems have no
  printed argument to follow. [`docs/route_differences.tsv`](../../docs/route_differences.tsv) records every difference
  of route.
- No person has reviewed the proofs. Independent agents reviewed the statements and compared the proofs with the paper
  ([`docs/CREDITS.md`](../../docs/CREDITS.md)).

## 1. Summary

- **Errors.** TINNiK has a misprint in the count of quartets sharing three taxa (E29), and its cut model is an open set
  on which the MLE need not exist at some counts with a zero (E31); neither affects a result. The typos are in E34.
- **Gaps.** E30, E32, E33, E40. All are repaired, and none changes a statement. E75 says what line 202's
  "straightforward" generalization to missing taxa needs: each set of four taxa on more and more gene trees. Nothing
  there is an error.
- **Missing hypotheses.** None found (Section 4).
- **Redundant hypotheses.** Section 5: `0 ≤ δ` in Theorem 4; the star test, which the consistency claim does not need,
  though the proof at step 2a uses it; and for the output of the T3 option, no anomalous quartets on the subsets that
  the tree of blobs does not resolve. Of a cited result: `φ ∈ (0, 1]` in Mitchell et al.'s Proposition 4.2.
- **Use of cited results.** TINNiK's Theorem 2 is applied beyond its printed hypothesis (b) (E30); the stronger rule it
  needs holds by the same proof. Its Theorem 1, Rhodes 2020's Theorem 2 and Mitchell et al.'s Theorem 3.1 are used
  correctly; Theorem 1 also excludes the centroid, so the separate analyticity argument is unnecessary (Section 11).
  Among results only cited, Studier and Keppler's Lemma fails at polytomies, a failure of wording if the letter means
  binary trees, and their theorem holds (Section 2). Mitchell et al.'s Appendix C has a misprint in one display, and its
  Proposition 5.2 holds as printed (E82).

## 2. Results from prior work and how the paper uses them

Allman et al. 2023 is another paper of this collection, formalized by its own proofs in
[`src/AllmanEtAl2023/`](../../src/AllmanEtAl2023), with [its own folder](../AllmanEtAl2023/README.md) and
[report](../AllmanEtAl2023/REPORT.md). TINNiK restates three of its results as its Theorems 1, 2 and 3. The rows below on
it are the forms TINNiK uses.

### Proved in `src/External/`, and in `src/AllmanEtAl2023/`

| Result | Where the paper uses it | Source | Theorem |
| --- | --- | --- | --- |
| The B-quartet inference rule (TINNiK's Theorem 2; its Theorem 3, combinatorial part, is [`AllmanEtAl2023.closure_complete`](../../src/AllmanEtAl2023/Basic.lean#L724)) | TINNiK Theorem 4 | Allman et al. 2023, Theorems 2, 3 | [`AllmanEtAl2023.rule_core`](../../src/AllmanEtAl2023/Basic.lean#L614), [`AllmanEtAl2023.closure_sound`](../../src/AllmanEtAl2023/Basic.lean#L732), [`AllmanEtAl2023.closure_complete`](../../src/AllmanEtAl2023/Basic.lean#L724); as printed, [`AllmanEtAl2023.theorem2`](../../src/AllmanEtAl2023/Theorem2.lean#L36), [`AllmanEtAl2023.theorem3`](../../src/AllmanEtAl2023/Theorem3.lean#L510) |
| CF-detectability of 4-blobs for generic parameters (TINNiK's Theorem 1) | TINNiK Theorem 4 | Allman et al. 2023, Theorem 1 and Corollary 1 | [`AllmanEtAl2023.cfDetectable_generic`](../../src/AllmanEtAl2023/CFDetectable.lean#L24); as printed, [`AllmanEtAl2023.corollary1`](../../src/AllmanEtAl2023/Corollary1.lean#L67), [`AllmanEtAl2023.theorem1`](../../src/AllmanEtAl2023/Theorem1.lean#L28) |
| Lemma 3 of the source, at any degree | TINNiK Theorem 4, through the closure | Allman et al. 2023 | [`AllmanEtAl2023.lemma3_resolves`](../../src/AllmanEtAl2023/Basic.lean#L240); as printed, [`AllmanEtAl2023.lemma3`](../../src/AllmanEtAl2023/Lemma3.lean#L35) |
| The quartet distance is a tree metric with the same topology | TINNiK Theorem 4 | Rhodes 2020 | [`External.Rhodes2020.theorem2`](../../src/External/Rhodes2020/Theorem2.lean#L776) |
| Limit law of the likelihood ratio at a cut model | TINNiK Prop. 5 | Mitchell et al. 2019 | [`External.MitchellAllmanRhodes2019.cutModel_theorem31`](../../src/External/MitchellAllmanRhodes2019/CutModel.lean#L181), for this model |
| Limit laws and densities of the T3 and T1 tests at the singularity | The T3 option | Mitchell et al. 2019, Propositions 4.1, 4.2, 5.1, 5.2 | [`External.MitchellAllmanRhodes2019.proposition4_1`](../../src/External/MitchellAllmanRhodes2019/T3Limit.lean#L481), [`External.MitchellAllmanRhodes2019.proposition4_2`](../../src/External/MitchellAllmanRhodes2019/T3Density.lean#L839), [`External.MitchellAllmanRhodes2019.proposition5_1`](../../src/External/MitchellAllmanRhodes2019/T1Limit.lean#L1092), [`External.MitchellAllmanRhodes2019.proposition5_2`](../../src/External/MitchellAllmanRhodes2019/T1Limit.lean#L1079), for the trinomial |

The rows on Mitchell et al. prove the source's conclusions for the model used. The limit laws are proved by the central
limit theorem, in place of van der Vaart's Theorem 16.7 (Section 7); the densities of Propositions 4.2 and 5.2 follow the
source's Appendices B and C ([`src/External/MitchellAllmanRhodes2019/README.md`](../../src/External/MitchellAllmanRhodes2019/README.md)).

### What was read

| Source | Cited by | Read? |
| --- | --- | --- |
| Allman et al. 2023 | TINNiK, Theorems 1–3 and the proof of Theorem 4 | Read: the PMC author manuscript NIHMS1884071 ([PMC10062380](https://pmc.ncbi.nlm.nih.gov/articles/PMC10062380/)) and the [arXiv TeX](https://arxiv.org/abs/2205.03466). Its audit is in [its report](../AllmanEtAl2023/REPORT.md) |
| Rhodes 2020 | TINNiK | Read, in PMC7650847. The plain text of that page lacks the displayed equations, which are in the page's XML |
| Studier, Keppler 1988 | TINNiK's Step 4, through neighbor joining | Read: the journal's PDF, a scan of 3 pages, in the Internet Archive's copy, since the publisher refused the download |
| Saitou, Nei 1987 | TINNiK's Step 4 | Not read. The algorithm is taken in Studier and Keppler's formulation |
| Buneman 1971, 1974 | Through the quartet distance of TINNiK's Theorem 4 | Not read in full. The proof of the four-point theorem here isn't Buneman's: it is by induction on the number of nodes, joining neighbours |
| Mitchell et al. 2019 | TINNiK | Read: the arXiv TeX and PDF (1806.08458v1), not the journal's text |
| NANUQ (Allman et al. 2019) | TINNiK | Read: arXiv v1 and the PMC text. The references behind its Proposition 9, which prints no proof, weren't read |

TINNiK's introduction also sets its algorithm against level-1 methods, which no proof uses (Section 10).

### Assumed

Nothing from the literature: the formalization is unconditional.

### Standard facts used without citation

| Fact | Where | In the formalization |
| --- | --- | --- |
| Central limit theorem, in dimension 2 by Cramér–Wold | TINNiK Prop. 5, star and T1 limits | Mathlib's `tendstoInDistribution_inv_sqrt_mul_sum_sub`; [`Phylogenetics.Trinomial.tendstoInDistribution_normalizedSums`](../../src/Basic/Testing/Trinomial/CLT.lean#L110) |
| Wilks-type limits: χ²₂ for the star test, the T1 mixture | TINNiK §"Algorithms" | Proved directly for the trinomial: [`Phylogenetics.Trinomial.tendsto_star_lrt`](../../src/Basic/Testing/Trinomial/Tests.lean#L369), [`Phylogenetics.Trinomial.tendsto_t1`](../../src/Basic/Testing/Trinomial/Tests.lean#L418) |
| Absorption of Kingman's coalescent; Tavaré's formula | The NMSC's definition | The library `Phylogenetics`, [`Phylogenetics/Coalescent/`](https://github.com/vltanh/lean4-phylogenetics/tree/f1a3592dee6e3f7d5e7a68a0695ac457de23d2de/Phylogenetics/Coalescent) |
| Neighbor joining and other exact tree builders recover a tree from its metric | TINNiK Theorem 4 | The theorem is stated for any [`Phylogenetics.IsExactBuilder`](https://github.com/vltanh/lean4-phylogenetics/blob/f1a3592dee6e3f7d5e7a68a0695ac457de23d2de/Phylogenetics/Tree/Metric.lean#L51). [`Phylogenetics.NJ.isExactBuilder_nj`](https://github.com/vltanh/lean4-phylogenetics/blob/f1a3592dee6e3f7d5e7a68a0695ac457de23d2de/Phylogenetics/Tree/NeighborJoining.lean#L1964) proves neighbor joining is one, for every tie-break; [`TINNiK.theorem4_nj`](../../src/TINNiK/NJ.lean#L35) is the result. [`External.Rhodes2020.exists_isExactBuilder`](../../src/External/Rhodes2020/Theorem2.lean#L889) gives another |

### Gaps in the proofs of cited results

Proving the cited results by their sources' arguments exposed one gap. Studier and Keppler's theorem holds, and their
Lemma fails at polytomies, if it isn't meant for binary trees only. Section 3 has the later point on a cited work (E82)
and the typos of the sources (E34).

- **Studier and Keppler 1988, neighbor joining (a failure of wording, if the letter means binary trees).** Assuming "a tree in which all branches are positive", page 730 attributes to Saitou and Nei the Lemma "If i and j are neighbors, then S_ij is the strictly least element in its row and column", with the proof "Each summand in formula (5a) is positive". It fails at a polytomy: on a 4-star with unit weights all `S_ij` are equal ([`External.StudierKeppler1988.not_lemmaAsPrinted`](../../src/External/StudierKeppler1988/Lemma.lean#L95)). The letter never defines "neighbors", read here as a cherry of a resolution, and its Figure 1 is binary. If it means binary trees, the star is outside its scope. Their theorem holds, with polytomies too: [`Phylogenetics.NJ.exists_QC_lt_of_not_nbr`](https://github.com/vltanh/lean4-phylogenetics/blob/f1a3592dee6e3f7d5e7a68a0695ac457de23d2de/Phylogenetics/Tree/NeighborJoining.lean#L785), by a different comparison (Section 7).

### Does the paper use each cited result correctly?

| Cited result | Where | Verdict |
| --- | --- | --- |
| Allman et al. Theorem 1 | TINNiK Theorem 4 | Correct; it also excludes the centroid, since strictly cut and non-cut CFs have two different entries, so the separate analyticity argument is unnecessary (Section 11) |
| Allman et al. Theorem 2 | TINNiK Theorem 4 | Applied loosely: E30 |
| Rhodes 2020 Theorem 2 | TINNiK Theorem 4 | Correct. Pendant edges have weight at least 2 as well |
| Mitchell et al. Theorem 3.1 | TINNiK Prop. 5 | Correct for fixed φ; the "not too close to the boundary" remark is not needed (E32) |

## 3. Errors and gaps in the paper

**E29. B-inference, Step 3(a)(i).** The number of quartets sharing exactly three taxa with a fixed one is `4(N-4)`, not `4(N-1)`. The order is unchanged. Lean: [`TINNiK.card_sharing_three`](../../src/TINNiK/Basic.lean#L39).

**E30. Theorem 2 of the source, as applied.** Hypothesis (b) says that a `t` is a B-quartet "on the induced 4-taxon network", but the Inference Rule also has to fire from a `t` inferred as a B-quartet of the full network, which may be treelike when induced.
This needs a stronger rule than the printed one. It holds by the same proof, because the separating cut edge also resolves `t` on `N`. Lean: [`AllmanEtAl2023.rule_core`](../../src/AllmanEtAl2023/Basic.lean#L614), from which [`AllmanEtAl2023.theorem2`](../../src/AllmanEtAl2023/Theorem2.lean#L36) and [`AllmanEtAl2023.closure_sound`](../../src/AllmanEtAl2023/Basic.lean#L732) follow.

**E31. Appendix C.1.** A maximum need not exist on the open cut model: at the counts `(1,0,0)`, and at any `(n,0,0)` with `n > 0`, the supremum `1` isn't attained ([`TINNiK.not_exists_generatingCutModel_maximizer`](../../src/TINNiK/Statistics/OpenCutModel.lean#L108)). Not every count with a zero fails: at `(4,1,0)` an interior maximizer wins, by a computation by hand, noted in the docstring and not in Lean. Lean estimates on the closed simplex, with strictly positive generating parameters, as agreed with the user. [`TINNiK.cutLineMLE_maximizes`](../../src/TINNiK/Statistics/AppendixC.lean#L72).

**E32. Propositions 5 and 6, proofs.** "Assuming `θ₀` is not too close to the boundary … dependent on the sample size" is informal and not needed for fixed `φ₀`. The result holds as stated. In Proposition 6, differentiating under the integral has no justification given: it holds for `x > 0`, by domination on a neighbourhood of `x`, and fails at `x = 0`, where the derivative of the integrand vanishes and `G₁` has a positive right derivative. This does no harm, since `{0}` is null. The density `g = 2 Σ d/dx Gᵢ` also needs `Gᵢ(x) → 0` as `x → 0` ([`ProbabilityTheory.measure_polarStrip_eq_lintegral_of_hasDerivAt`](../../src/Basic/ForMathlib/Probability/GaussianPlane.lean#L739)). Every display of the proposition checks out.

**E33. Theorem 4, proof.** Under the alternative, "the test distribution converges to the `χ²₁`" gives no comparison at cutoffs `m d/2` growing with `m`, and "without loss of generality" the MLE on the vertical line hides that the fitted line is random and `d` depends on it. Repairs: the test distribution is pointwise at most that of `Z²`, and the least limit over the three lines gives one `d` ([`Phylogenetics.QuartetTests.cutTest_alternative`](../../src/Basic/Testing/Tails.lean#L683), [`Phylogenetics.QuartetTests.cutTail_le_chiSqOneTail`](../../src/Basic/Testing/Tails.lean#L147)). Under the null, the paper's argument works and Lean follows it, with two corrections to "`μ₀` goes to `∞` and the distribution converges to the `χ²₁`". First, it should be `|μ₀| → ∞`, as Appendix C.3 writes it, since anomalous strictly cut CFs have `μ₀ → -∞`; the two signs behave alike, since `z̄ ↦ -z̄` swaps the last two terms of `Λ_n`. Second, the limit is governed by `cos α₀ |μ₀|`, the distance from `(0, μ₀)` to the other two lines, and `|μ₀|` alone is not enough: `α₀ → π/2` as `φ₀ → 3/2`, and at fixed `n` there `|μ₀| → ∞` while `cos α₀ μ₀ → -√n`, so the law tends to that of `min(Z², (Z-√n)², (Z+√n)²)`. This does no harm at a positive CF, where `φ̂ → φ₀ < 3/2`. Lean proves the limit uniformly in the argument and the parameter ([`Phylogenetics.Trinomial.abs_cutTail_sub_chiSqOneTail_lt`](../../src/Basic/Testing/Trinomial/Tests.lean#L168)), which is what the plug-in needs ([`Phylogenetics.Trinomial.eventually_abs_cutTail_estimate_sub_lt`](../../src/Basic/Testing/Trinomial/Tests.lean#L286)); so the p-value is asymptotically uniform ([`Phylogenetics.QuartetTests.cutPValue_asymptoticallyUniform`](../../src/Basic/Testing/Limits.lean#L423)) and `P(p < α_m) → 0` for any `α_m → 0` ([`Phylogenetics.QuartetTests.cutTest_null`](../../src/Basic/Testing/Limits.lean#L452)). With no 4-blob among the induced networks, "the maximum of the `α'_m`" is over an empty family; any sequence tending to `0` serves, and Lean adds `P(χ²₁ > m)` ([`TINNiK.exists_levels`](../../src/TINNiK/Basic.lean#L582)). The centroid step evaluates at hybridization parameters `0` or `1`, on the boundary of the parameter space, so "analyticity" must hold across it: the CFs are analytic on all the coordinates ([`AllmanEtAl2023.isGenericNull_of_analyticOnNhd`](../../src/AllmanEtAl2023/GenericCF.lean#L166)). The result holds.

### Remarks, discussion, and smaller points

These came from formalizing what the paper says in passing.

**E40. TINNiK: B-quartet inference, "this pair will be compared again later".** That sentence alone does not cover a third B-quartet of the rule appearing after the pair's comparison. The sentence before it supplies the comparison ("any time a new one is discovered it is compared to all quartets that share three taxa with it"), and the other of the pair is among its [`TINNiK.otherSets`](../../src/TINNiK/Counts.lean#L58), so the algorithm is right. Lean: [`TINNiK.mem_bQuartetInference_iff`](../../src/TINNiK/Counts.lean#L683) proves its output is the closure [`BInferred`](../../src/Basic/Defs.lean#L126).

**E75. TINNiK lines 198 and 202: what the generalization to missing taxa needs (nothing here is an error).** Line 198: "The TINNiK algorithm can also be applied when gene trees have missing taxa, provided each subset of 4 taxa occurs on at least one gene tree, so the qcCF is not the zero vector", which is right, and says what the algorithm needs to run. Line 202 restricts the discussion of consistency to gene trees on the full taxon set, "since generalizing from this is straightforward". That generalization needs each set of four taxa on more and more gene trees ([`TINNiK.Covers`](../../src/TINNiK/MissingTaxa.lean#L97)). On a set on one gene tree, which resolves it, the star p-value is `1/3`, and at `β ≤ 1/3` it is judged a B-quartet however many gene trees there are ([`TINNiK.mem_testedB_of_coverCount_eq_one`](../../src/TINNiK/MissingTaxa.lean#L68)); a set on no tree is judged one at any `β ≤ 1` ([`TINNiK.mem_testedB_of_coverCount_eq_zero`](../../src/TINNiK/MissingTaxa.lean#L54)). With that condition the generalization goes as "straightforward" suggests: [`TINNiK.theorem4_missing`](../../src/TINNiK/MissingTaxa.lean#L473), [`TINNiK.theorem4T3_missing`](../../src/TINNiK/MissingTaxa.lean#L490), and NANUQ's [`External.AllmanBanosRhodes2019.theorem36_missing`](../../src/External/AllmanBanosRhodes2019/MissingTaxa.lean#L196).

### Points on cited works

This is about a source that TINNiK cites, and it affects no result of the paper. Section 2 has the earlier point on
Studier and Keppler 1988.

**E82. Mitchell et al. 2019, Appendix C (a misprint, and a loose word).** In the first display for model T1, the second line of `d/dx G₁` repeats that of `G₂`; it should be `(1/2π) e^{-x²/2} √(2π) ½(1 + erf(μ₀/√2))`. And the appendix calls `x` the distance to the mean, where it is the distance to the half-line. Proposition 5.2 holds as printed: [`External.MitchellAllmanRhodes2019.proposition5_2`](../../src/External/MitchellAllmanRhodes2019/T1Limit.lean#L1079).

### Typos

**E34.**

- TINNiK, Appendix C: `Λ̃_n` for Proposition 5's `Λ_n`.
- Mitchell et al. 2019: "Proposition 16.7" for van der Vaart's Theorem 16.7, in one place.
- Rhodes 2020, the display before (2), and (2), (3): the sums over `C_v^i` run to `k` or `k(v)`, though there are `k - 2` blocks; (2) prints `v on p` for `P`.

## 4. Missing hypotheses

The audit found no statement of TINNiK that is false without a condition it leaves implicit. The one correction of a
statement, E31, is to the maximum likelihood estimate of Appendix C.1, which is read on the closed simplex (Section 6).
`4 ≤ |X|` is implicit in Theorem 4 and explicit in Lean (Section 6). E75 records the condition that the generalization
to missing taxa needs, for a result that the paper calls straightforward and does not state.

## 5. Redundant hypotheses

The Lean statements leave these out, except where the last column says otherwise and in [`src/MainResults/TINNiK.lean`](../../src/MainResults/TINNiK.lean), which keeps the paper's hypotheses.

| Result | Hypothesis that is not needed | Why | Lean |
| --- | --- | --- | --- |
| TINNiK Theorem 4 | `0 ≤ δ` | The filter uses only `δ < 2` | [`TINNiK.theorem4_of_rejects`](../../src/TINNiK/Basic.lean#L542) drops it; [`TINNiK.theorem4`](../../src/TINNiK/Basic.lean#L629) keeps `0 ≤ δ`, unused |
| TINNiK Theorem 4 | The star test: "any `β > 0`" includes `β > 1`, where it has no effect | At `β > 1` no p-value reaches the level, so TINNiK with `δ = 0` is the outline of Allman et al.'s Section 5 with the cut test alone, and the theorem still holds. So the consistency claim doesn't need the star test, though the proof at step 2a uses it | [`TINNiK.outline_cut_eq_tinnik`](../../src/TINNiK/AllmanOutline.lean#L45), [`TINNiK.outline_cut_consistent`](../../src/TINNiK/AllmanOutline.lean#L70) |
| TINNiK, T3 option | No anomalous quartets on subsets the tree of blobs doesn't resolve | Needed for correctness on every subset ([`TINNiK.tendsto_mem_testedBT3_of_anomalous`](../../src/TINNiK/T3.lean#L513)). For the output, T-quartet nonanomaly and CF-detectability suffice: a rejected subset of the third class is a true B-quartet, and the closure doesn't change | [`TINNiK.theorem4T3_of_tQuartet`](../../src/TINNiK/T3.lean#L713) |
| Mitchell et al. Proposition 4.2 | `φ ∈ (0, 1]` | The printed density is the density for all `φ < 3/2` | [`External.MitchellAllmanRhodes2019.proposition4_2`](../../src/External/MitchellAllmanRhodes2019/T3Density.lean#L839) |

## 6. How the formalization reads the paper

### Readings specific to this paper

- **TINNiK Theorem 4**: [`TINNiK.theorem4`](../../src/TINNiK/Basic.lean#L629) uses the paper's levels ([`TINNiK.exists_levels`](../../src/TINNiK/Basic.lean#L582)), which depend on unknown limits. [`TINNiK.theorem4_explicit`](../../src/TINNiK/Basic.lean#L657) also proves it for one sequence `α_m = P(χ²₁ > log m)`, independent of the network and parameters, as ECToBlob's Remark 8.3 suggests. [`ECToBlob.remark83_tinnik`](../../src/ECToBlob/Remark83.lean#L235) makes `β` explicit too.
- **`4 ≤ |X|`** in [`TINNiK.theorem4`](../../src/TINNiK/Basic.lean#L629) is explicit in Lean and implicit in the paper: at `|X| = 2` the quartet distance is 0, and [`IsExactBuilder`](https://github.com/vltanh/lean4-phylogenetics/blob/f1a3592dee6e3f7d5e7a68a0695ac457de23d2de/Phylogenetics/Tree/Metric.lean#L51) says nothing about that input.

### Readings shared with TOB-QMC and ECToBlob

TOB-QMC and ECToBlob, which build on TINNiK, share these readings.

- **Networks** are directed multigraphs with named arcs ([`Phylogenetics.RootedNetwork`](https://github.com/vltanh/lean4-phylogenetics/blob/f1a3592dee6e3f7d5e7a68a0695ac457de23d2de/Phylogenetics/Network/Defs.lean#L30)), rooted, with parallel arcs allowed. The paper's semi-directed networks are handled through the rooted networks they come from.
- **Unrooted trees** are families of sides of splits ([`Phylogenetics.IsUnrootedTree`](https://github.com/vltanh/lean4-phylogenetics/blob/f1a3592dee6e3f7d5e7a68a0695ac457de23d2de/Phylogenetics/Tree/Defs.lean#L49): [`unroot`](https://github.com/vltanh/lean4-phylogenetics/blob/f1a3592dee6e3f7d5e7a68a0695ac457de23d2de/Phylogenetics/Hierarchy/Defs.lean#L43) of a hierarchy). The tree of blobs `T_B(N)` is the family of nonempty proper sides of cut edges ([`Phylogenetics.treeOfBlobs`](https://github.com/vltanh/lean4-phylogenetics/blob/f1a3592dee6e3f7d5e7a68a0695ac457de23d2de/Phylogenetics/Network/Quartets.lean#L40)).
  Bridges to the graphs: [`Phylogenetics.RootedNetwork.blobTree`](https://github.com/vltanh/lean4-phylogenetics/blob/f1a3592dee6e3f7d5e7a68a0695ac457de23d2de/Phylogenetics/Network/TreeOfBlobs.lean#L127) is the graph with blobs contracted; [`Phylogenetics.RootedNetwork.mem_treeOfBlobs_iff_blobTree`](https://github.com/vltanh/lean4-phylogenetics/blob/f1a3592dee6e3f7d5e7a68a0695ac457de23d2de/Phylogenetics/Network/TreeOfBlobs.lean#L213) says the two agree on splits, and [`Phylogenetics.RootedNetwork.blobTree_isTree`](https://github.com/vltanh/lean4-phylogenetics/blob/f1a3592dee6e3f7d5e7a68a0695ac457de23d2de/Phylogenetics/Network/TreeOfBlobs.lean#L134) that it is a tree. The root of `blobTree` is not deleted. Allman et al.'s [`AllmanEtAl2023.Trd`](../../src/AllmanEtAl2023/BlobDefinitions.lean#L422) is the reduced graph, and [`AllmanEtAl2023.Bridges.splits_Trd`](../../src/AllmanEtAl2023/Bridges.lean#L353) says its splits are this family.
- **Induced networks**: `HasCutSplitOn Y A` says that one arc of the subgraph of ancestors of `Y` is the only arc of it crossing a vertex set that meets `Y` in `A`; [`Phylogenetics.RootedNetwork.hasCutSplitOn_iff_separates`](https://github.com/vltanh/lean4-phylogenetics/blob/f1a3592dee6e3f7d5e7a68a0695ac457de23d2de/Phylogenetics/Network/Cuts.lean#L253) gives the domination form, and [`Phylogenetics.RootedNetwork.hasCutSplitOn_iff_inducedNetwork_hasCutSplit`](https://github.com/vltanh/lean4-phylogenetics/blob/f1a3592dee6e3f7d5e7a68a0695ac457de23d2de/Phylogenetics/Network/Induced.lean#L857) proves it equal to the cut splits of the graph `inducedNetwork` (LSA restriction, then suppression). The papers later than Allman et al. 2023, TINNiK among them, use this network, whose CFs are those of `N` on four taxa ([`Phylogenetics.NMSC.nmscCF_inducedNetwork`](https://github.com/vltanh/lean4-phylogenetics/blob/f1a3592dee6e3f7d5e7a68a0695ac457de23d2de/Phylogenetics/NMSC/Induced.lean#L76)). Allman et al.'s own results use their Definition 6, [`AllmanEtAl2023.induced`](../../src/AllmanEtAl2023/InducedNetwork.lean#L296), which keeps what lies above the LSA; the two have the same cut-edge splits ([`AllmanEtAl2023.Bridges.induced_hasCutSplit_iff`](../../src/AllmanEtAl2023/Bridges.lean#L210)).
- **Quartet trees** are unordered pairs of cherries; [`Phylogenetics.Displays`](https://github.com/vltanh/lean4-phylogenetics/blob/f1a3592dee6e3f7d5e7a68a0695ac457de23d2de/Phylogenetics/Tree/Defs.lean#L84).
- **The NMSC** on arbitrary networks is an order-free sum over histories ([`Phylogenetics.geneTreeDist`](https://github.com/vltanh/lean4-phylogenetics/blob/f1a3592dee6e3f7d5e7a68a0695ac457de23d2de/Phylogenetics/NMSC/Defs.lean#L94)), the product over vertices and arcs of the joint law of the forests at the bottom and top of each arc. One lineage per taxon. `ρ` is the inheritance correlation of TOB-QMC's supplement, in closed form as an exchangeable Pólya law ([`Phylogenetics.allocationWeight`](https://github.com/vltanh/lean4-phylogenetics/blob/f1a3592dee6e3f7d5e7a68a0695ac457de23d2de/Phylogenetics/NMSC/Defs.lean#L54), proved equal to the urn in [`Phylogenetics.allocationWeight_eq_urn`](https://github.com/vltanh/lean4-phylogenetics/blob/f1a3592dee6e3f7d5e7a68a0695ac457de23d2de/Phylogenetics/NMSC/Inheritance.lean#L232)). [`Phylogenetics.sum_geneTreeDist`](https://github.com/vltanh/lean4-phylogenetics/blob/f1a3592dee6e3f7d5e7a68a0695ac457de23d2de/Phylogenetics/NMSC/Basic.lean#L51) and [`Phylogenetics.geneTreeDist_support`](https://github.com/vltanh/lean4-phylogenetics/blob/f1a3592dee6e3f7d5e7a68a0695ac457de23d2de/Phylogenetics/NMSC/Basic.lean#L64) validate it: a law on binary rooted trees. TINNiK's Theorem 4 is stated at `ρ = 0`, independent inheritance.
- **Sampling**: `Phylogenetics.iidProb dist n Ev` is the finite sum over samples, proved equal to the product measure ([`Phylogenetics.iidProb_eq_pi`](../../src/Basic/Testing/IID.lean#L264)).
- **Test statistics** follow the implementation (MSCquartets, Mitchell et al.). The T1 p-value uses the plug-in `min(1, φ̂)` at all counts; small-count procedures of software are not modelled. Star: likelihood ratio by default, Pearson as `StarTest.pearson`.
- **Parameters**: `MetricData` has lengths on all arcs and hybridization parameters; `IsMetric` requires positivity on tree edges, and `γ` strictly between 0 and 1 where a reticulation has two parents.
- **The T3 test**: [`Phylogenetics.t3Stat`](../../src/External/MitchellAllmanRhodes2019/T3Test.lean#L56) is the minimum over topologies of [`t1Stat`](../../src/Basic/Testing/Defs.lean#L63), and [`Phylogenetics.t3Var`](../../src/External/MitchellAllmanRhodes2019/T3Test.lean#L63) the random variable of Mitchell et al.'s Proposition T3approx, whose squared distance to the three half-lines is [`Phylogenetics.QuartetTests.t3Var_eq_min_sqDistHalfLine`](../../src/External/MitchellAllmanRhodes2019/T3Test.lean#L172) (a step they leave as "it can be shown"); at `Z = 0` their formula gives 0, harmless since `Z = 0` has probability zero. The sources differ at the centroid: Mitchell et al.'s null includes it, TINNiK's Fig. 2 caption excludes it, and its anomalous condition `q ≥ 1/3` counts it as anomalous. Lean follows each: [`Phylogenetics.IsT3Null`](../../src/External/MitchellAllmanRhodes2019/T3Test.lean#L51) follows Mitchell et al., `TINNiK.NoAnomalousQuartets` TINNiK. TINNiK's Theorem 4 says "using the cut test", so [`TINNiK.theorem4T3`](../../src/TINNiK/T3.lean#L469) has no printed proof to follow, and takes the structure of the proof for the cut test.
- **Counts of operations** are counts of what the paper's claims are about, tied to the definitions by `Finset.card` of what a step enumerates or by an instrumented run ([`Phylogenetics.NJ.ops_run`](https://github.com/vltanh/lean4-phylogenetics/blob/f1a3592dee6e3f7d5e7a68a0695ac457de23d2de/Phylogenetics/Tree/NeighborJoining.lean#L1976), [`TINNiK.count_bQuartetInference`](../../src/TINNiK/Counts.lean#L710)). There is no machine model, so these aren't running times. [`TINNiK.tinnikOperations_le`](../../src/TINNiK/Counts.lean#L848) takes the cost of Step 4, `nj ≤ c N³`, as a hypothesis, and the library counts neighbor joining's steps ([`Phylogenetics.NJ.njOps_le`](https://github.com/vltanh/lean4-phylogenetics/blob/f1a3592dee6e3f7d5e7a68a0695ac457de23d2de/Phylogenetics/Tree/NeighborJoining.lean#L1999)).
- **Missing taxa.** TINNiK states no model. Here gene trees are independent draws from the NMSC, each with taxa `on m i` fixed in advance. A gene tree on a subset is the restriction of a full gene tree ([`Phylogenetics.partialCount_restrict`](../../src/Basic/Testing/MissingTaxa.lean#L69)), by sampling consistency. Each set of four taxa is on more and more gene trees ([`TINNiK.Covers`](../../src/TINNiK/MissingTaxa.lean#L97)), which is what the generalization that line 202 calls straightforward needs (E75).

### Corrections of statements

E31: the maximum likelihood estimate of Appendix C.1 is taken on the closed simplex, with the generating parameter in the
open simplex, as agreed with the user who requested this formalization
([`src/TINNiK/Statistics/Definitions.lean`](../../src/TINNiK/Statistics/Definitions.lean)).

## 7. Departures from the paper's proofs

The last column but one says why, and says so plainly when a departure isn't forced. Mechanics and representation with the same content aren't listed: paths as sets of arcs, for instance, and a concrete value for "sufficiently long".

| Result | The paper's argument | The formalization's | Why | E-item |
| --- | --- | --- | --- | --- |
| TINNiK Proposition 5 | From Mitchell et al. Theorem 3.1 (van der Vaart 16.7) | Direct CLT for this model; projections and minimum as the paper | Lean lacks differentiability in quadratic mean, local asymptotic normality, MLE consistency | — |
| TINNiK Theorem 4 | Under the alternative, the test law's limit `χ²₁` | A pointwise upper bound by `Z²`, and the least limit over the three lines. The centroid step follows the paper ([`TINNiK.isGenericNull_centroid`](../../src/TINNiK/Basic.lean#L411)), though CF-detectability already gives it (Section 11). The null follows the paper, with E33's corrections | Gap: the limit gives no comparison at growing cutoffs, and the fitted line is random | E33 |
| TINNiK Theorem 4, what it reaches | Cites Theorem 1 of Allman et al., and the inference rule | [`AllmanEtAl2023.cfDetectable_generic`](../../src/AllmanEtAl2023/CFDetectable.lean#L24), [`AllmanEtAl2023.closure_sound`](../../src/AllmanEtAl2023/Basic.lean#L732), [`AllmanEtAl2023.closure_complete`](../../src/AllmanEtAl2023/Basic.lean#L724), which reach that paper's claims on induced networks, three taxa and its Lemma 2. Proposition 6 isn't used: it is the density of a law that [`cutTail`](../../src/Basic/Testing/Defs.lean#L125) defines directly | Not a departure: the proof the paper cites, one level down | — |
| Neighbor joining (Studier, Keppler 1988) | A Lemma on rows of `S`, and a contradiction from two nodes | `Q = -∑ w_S g_S` over edges, and a side with at most `n/2` clusters, whose neighbours beat the pair ([`Phylogenetics.NJ.exists_QC_lt_of_not_nbr`](https://github.com/vltanh/lean4-phylogenetics/blob/f1a3592dee6e3f7d5e7a68a0695ac457de23d2de/Phylogenetics/Tree/NeighborJoining.lean#L785)) | Gap: their Lemma fails at polytomies, which is a matter of wording if the letter means binary trees | Section 2 |
| Mitchell et al. Propositions 4.1, 5.1 (cited) | Read off its Theorem 3.1, and so van der Vaart's Theorem 16.7 | The central limit theorem for the trinomial ([`Phylogenetics.QuartetTests.t3Stat_limitLaw`](../../src/External/MitchellAllmanRhodes2019/T3Limit.lean#L622), [`Phylogenetics.QuartetTests.t1Stat_limitLaw`](../../src/External/MitchellAllmanRhodes2019/T1Limit.lean#L1150)) | Lean lacks that theorem, as for TINNiK's Proposition 5 | — |

The proof of Buneman's four-point theorem ([`Phylogenetics.FourPoint.exists_tree_of_isFourPoint`](https://github.com/vltanh/lean4-phylogenetics/blob/f1a3592dee6e3f7d5e7a68a0695ac457de23d2de/Phylogenetics/Tree/FourPoint.lean#L802), by induction on a pair maximizing the Gromov product) wasn't compared with the published one, which wasn't read in full. The T3 theorems have no printed proof. TINNiK's estimation on the closed simplex ([`src/TINNiK/Statistics/Definitions.lean`](../../src/TINNiK/Statistics/Definitions.lean)) is a correction of statement, E31.

## 8. What each result depends on

<!-- Generated from scripts/Audit.lean -->

| Result | Lean | Results from prior work used |
| --- | --- | --- |
| TINNiK C.1, line MLE | [`TINNiK.cutLineMLE_maximizes`](../../src/TINNiK/Statistics/AppendixC.lean#L72) | – |
| TINNiK C.1, line log-likelihood | [`TINNiK.lineMaxLogLikelihood_eq`](../../src/TINNiK/Statistics/AppendixC.lean#L180) | – |
| TINNiK C.1, full log-likelihood | [`TINNiK.fullMaxLogLikelihood_eq`](../../src/TINNiK/Statistics/AppendixC.lean#L205) | – |
| TINNiK Proposition 5 | [`TINNiK.proposition5`](../../src/TINNiK/Statistics/AppendixC.lean#L343) | [`External.MitchellAllmanRhodes2019.cutModel_theorem31`](../../src/External/MitchellAllmanRhodes2019/CutModel.lean#L181) |
| TINNiK Proposition 6 | [`TINNiK.proposition6`](../../src/TINNiK/Statistics/Proposition6.lean#L951) | – |
| TINNiK Theorem 4, at given parameters | [`TINNiK.theorem4_of_rejects`](../../src/TINNiK/Basic.lean#L542) | [`AllmanEtAl2023.CFDetectable`](../../src/AllmanEtAl2023/CFDetectable.lean), [`AllmanEtAl2023.closure_complete`](../../src/AllmanEtAl2023/Basic.lean#L724), [`AllmanEtAl2023.closure_sound`](../../src/AllmanEtAl2023/Basic.lean#L732), [`External.Rhodes2020.theorem2`](../../src/External/Rhodes2020/Theorem2.lean#L776), [`External.Rhodes2020.quartetWeight_ge_two`](../../src/External/Rhodes2020/Theorem2.lean#L868) |
| TINNiK Theorem 4, one sequence of levels | [`TINNiK.theorem4_explicit`](../../src/TINNiK/Basic.lean#L657) | [`AllmanEtAl2023.CFDetectable`](../../src/AllmanEtAl2023/CFDetectable.lean), [`AllmanEtAl2023.closure_complete`](../../src/AllmanEtAl2023/Basic.lean#L724), [`AllmanEtAl2023.closure_sound`](../../src/AllmanEtAl2023/Basic.lean#L732), [`External.Rhodes2020.theorem2`](../../src/External/Rhodes2020/Theorem2.lean#L776), [`External.Rhodes2020.quartetWeight_ge_two`](../../src/External/Rhodes2020/Theorem2.lean#L868) |
| TINNiK Theorem 4 | [`TINNiK.theorem4`](../../src/TINNiK/Basic.lean#L629) | [`AllmanEtAl2023.cfDetectable_generic`](../../src/AllmanEtAl2023/CFDetectable.lean#L24), [`AllmanEtAl2023.CFDetectable`](../../src/AllmanEtAl2023/CFDetectable.lean), [`AllmanEtAl2023.closure_complete`](../../src/AllmanEtAl2023/Basic.lean#L724), [`AllmanEtAl2023.closure_sound`](../../src/AllmanEtAl2023/Basic.lean#L732), [`External.Rhodes2020.theorem2`](../../src/External/Rhodes2020/Theorem2.lean#L776), [`External.Rhodes2020.quartetWeight_ge_two`](../../src/External/Rhodes2020/Theorem2.lean#L868) |
| TINNiK Theorem 4, T3 option | [`TINNiK.theorem4T3`](../../src/TINNiK/T3.lean#L469) | [`AllmanEtAl2023.cfDetectable_generic`](../../src/AllmanEtAl2023/CFDetectable.lean#L24), [`AllmanEtAl2023.CFDetectable`](../../src/AllmanEtAl2023/CFDetectable.lean), [`AllmanEtAl2023.closure_complete`](../../src/AllmanEtAl2023/Basic.lean#L724), [`AllmanEtAl2023.closure_sound`](../../src/AllmanEtAl2023/Basic.lean#L732), [`External.Rhodes2020.theorem2`](../../src/External/Rhodes2020/Theorem2.lean#L776), [`External.Rhodes2020.quartetWeight_ge_two`](../../src/External/Rhodes2020/Theorem2.lean#L868) |
| TINNiK Theorem 4, neighbor joining | [`TINNiK.theorem4_nj`](../../src/TINNiK/NJ.lean#L35) | [`AllmanEtAl2023.cfDetectable_generic`](../../src/AllmanEtAl2023/CFDetectable.lean#L24), [`AllmanEtAl2023.CFDetectable`](../../src/AllmanEtAl2023/CFDetectable.lean), [`AllmanEtAl2023.closure_complete`](../../src/AllmanEtAl2023/Basic.lean#L724), [`AllmanEtAl2023.closure_sound`](../../src/AllmanEtAl2023/Basic.lean#L732), [`External.Rhodes2020.theorem2`](../../src/External/Rhodes2020/Theorem2.lean#L776), [`External.Rhodes2020.quartetWeight_ge_two`](../../src/External/Rhodes2020/Theorem2.lean#L868), [`Phylogenetics.NJ.isExactBuilder_nj`](https://github.com/vltanh/lean4-phylogenetics/blob/f1a3592dee6e3f7d5e7a68a0695ac457de23d2de/Phylogenetics/Tree/NeighborJoining.lean#L1964) |
| Allman et al. 2023, Like NANUQ, it can be shown to provide a statistically consistent estimate of the network features it seeks ... | [`TINNiK.outline_cut_consistent`](../../src/TINNiK/AllmanOutline.lean#L70) | [`AllmanEtAl2023.cfDetectable_generic`](../../src/AllmanEtAl2023/CFDetectable.lean#L24), [`AllmanEtAl2023.CFDetectable`](../../src/AllmanEtAl2023/CFDetectable.lean), [`AllmanEtAl2023.closure_complete`](../../src/AllmanEtAl2023/Basic.lean#L724), [`AllmanEtAl2023.closure_sound`](../../src/AllmanEtAl2023/Basic.lean#L732), [`External.Rhodes2020.theorem2`](../../src/External/Rhodes2020/Theorem2.lean#L776), [`External.Rhodes2020.quartetWeight_ge_two`](../../src/External/Rhodes2020/Theorem2.lean#L868) |
| TINNiK, Theorem 4 with missing taxa at given parameters | [`TINNiK.theorem4_missing_of_rejects`](../../src/TINNiK/MissingTaxa.lean#L442) | [`AllmanEtAl2023.CFDetectable`](../../src/AllmanEtAl2023/CFDetectable.lean), [`AllmanEtAl2023.closure_complete`](../../src/AllmanEtAl2023/Basic.lean#L724), [`AllmanEtAl2023.closure_sound`](../../src/AllmanEtAl2023/Basic.lean#L732), [`External.Rhodes2020.theorem2`](../../src/External/Rhodes2020/Theorem2.lean#L776), [`External.Rhodes2020.quartetWeight_ge_two`](../../src/External/Rhodes2020/Theorem2.lean#L868) |
| TINNiK, Theorem 4 with missing taxa at parameters with CF-detectability | [`TINNiK.theorem4_missing_of_cfDetectable`](../../src/TINNiK/MissingTaxa.lean#L456) | [`AllmanEtAl2023.CFDetectable`](../../src/AllmanEtAl2023/CFDetectable.lean), [`AllmanEtAl2023.closure_complete`](../../src/AllmanEtAl2023/Basic.lean#L724), [`AllmanEtAl2023.closure_sound`](../../src/AllmanEtAl2023/Basic.lean#L732), [`External.Rhodes2020.theorem2`](../../src/External/Rhodes2020/Theorem2.lean#L776), [`External.Rhodes2020.quartetWeight_ge_two`](../../src/External/Rhodes2020/Theorem2.lean#L868) |
| TINNiK, Theorem 4 with missing taxa | [`TINNiK.theorem4_missing`](../../src/TINNiK/MissingTaxa.lean#L473) | [`AllmanEtAl2023.cfDetectable_generic`](../../src/AllmanEtAl2023/CFDetectable.lean#L24), [`AllmanEtAl2023.CFDetectable`](../../src/AllmanEtAl2023/CFDetectable.lean), [`AllmanEtAl2023.closure_complete`](../../src/AllmanEtAl2023/Basic.lean#L724), [`AllmanEtAl2023.closure_sound`](../../src/AllmanEtAl2023/Basic.lean#L732), [`External.Rhodes2020.theorem2`](../../src/External/Rhodes2020/Theorem2.lean#L776), [`External.Rhodes2020.quartetWeight_ge_two`](../../src/External/Rhodes2020/Theorem2.lean#L868) |
| TINNiK, The T3 option with missing taxa | [`TINNiK.theorem4T3_missing`](../../src/TINNiK/MissingTaxa.lean#L490) | [`AllmanEtAl2023.closure_complete`](../../src/AllmanEtAl2023/Basic.lean#L724), [`AllmanEtAl2023.closure_sound`](../../src/AllmanEtAl2023/Basic.lean#L732), [`External.Rhodes2020.theorem2`](../../src/External/Rhodes2020/Theorem2.lean#L776), [`External.Rhodes2020.quartetWeight_ge_two`](../../src/External/Rhodes2020/Theorem2.lean#L868) |
| TINNiK, no maximum on the open cut model | [`TINNiK.not_exists_generatingCutModel_maximizer`](../../src/TINNiK/Statistics/OpenCutModel.lean#L108) | – |
| Mitchell et al. 2019, The density tends to that of χ²₁ (tendsto_t3Density_atTop) | [`Phylogenetics.QuartetTests.tendsto_t3Density_atTop`](../../src/External/MitchellAllmanRhodes2019/T3Density.lean#L753) | – |
| Mitchell et al. 2019, The density at the singularity | [`Phylogenetics.QuartetTests.t3Density_one`](../../src/External/MitchellAllmanRhodes2019/T3Density.lean#L709) | – |
| Mitchell et al. 2019, Proposition 4.2 (t3Var_density) | [`Phylogenetics.QuartetTests.t3Var_density`](../../src/External/MitchellAllmanRhodes2019/T3Density.lean#L604) | – |
| Mitchell et al. 2019, t3Tail_eq_integral | [`Phylogenetics.QuartetTests.t3Tail_eq_integral`](../../src/External/MitchellAllmanRhodes2019/T3Density.lean#L614) | – |
| Mitchell et al. 2019, The density is continuous in φ₀ | [`Phylogenetics.QuartetTests.continuousOn_t3Density`](../../src/External/MitchellAllmanRhodes2019/T3Density.lean#L791) | – |
| Mitchell et al. 2019, Proposition 4.2 (proposition4_2) | [`External.MitchellAllmanRhodes2019.proposition4_2`](../../src/External/MitchellAllmanRhodes2019/T3Density.lean#L839) | – |
| Mitchell et al. 2019, The p-value with the true parameter at the singularity is asymptotically uniform | [`Phylogenetics.QuartetTests.t3Tail_t3Stat_asymptoticallyUniform`](../../src/External/MitchellAllmanRhodes2019/T3Limit.lean#L707) | – |
| Mitchell et al. 2019, tendstoInDistribution_t3Stat | [`Phylogenetics.QuartetTests.tendstoInDistribution_t3Stat`](../../src/External/MitchellAllmanRhodes2019/T3Limit.lean#L738) | – |
| Mitchell et al. 2019, t3Stat_limitLaw_density | [`Phylogenetics.QuartetTests.t3Stat_limitLaw_density`](../../src/External/MitchellAllmanRhodes2019/T3Limit.lean#L663) | – |
| Mitchell et al. 2019, Proposition 4.1 | [`External.MitchellAllmanRhodes2019.proposition4_1`](../../src/External/MitchellAllmanRhodes2019/T3Limit.lean#L481) | – |
| Mitchell et al. 2019, t3Stat is the likelihood ratio statistic | [`Phylogenetics.QuartetTests.t3Stat_eq_likelihoodRatio`](../../src/External/MitchellAllmanRhodes2019/T3Limit.lean#L582) | – |
| Mitchell et al. 2019, Off the singularity, the limit law of the T3 statistic is χ²₁ | [`Phylogenetics.QuartetTests.t3Stat_limitLaw_of_isT1Strict`](../../src/External/MitchellAllmanRhodes2019/T3Limit.lean#L638) | – |
| Mitchell et al. 2019, The limit law of the T3 statistic at the singularity | [`Phylogenetics.QuartetTests.t3Stat_limitLaw`](../../src/External/MitchellAllmanRhodes2019/T3Limit.lean#L622) | – |
| Mitchell et al. 2019, This distribution is not a χ² | [`Phylogenetics.QuartetTests.map_t3Var_one_ne_chiSqLaw`](../../src/External/MitchellAllmanRhodes2019/T3Limit.lean#L857) | – |
| Mitchell et al. 2019, The T3 statistic is the likelihood ratio statistic of the source | [`Phylogenetics.Trinomial.t3S_eq_likelihoodRatio`](../../src/External/MitchellAllmanRhodes2019/T3Limit.lean#L195) | – |
| Mitchell et al. 2019, The T1 statistic is the likelihood ratio statistic of the source | [`Phylogenetics.Trinomial.t1S_eq_likelihoodRatio`](../../src/External/MitchellAllmanRhodes2019/T1Limit.lean#L697) | – |
| Mitchell et al. 2019, The limit law of the T1 statistic at the boundary point | [`Phylogenetics.QuartetTests.t1Stat_limitLaw`](../../src/External/MitchellAllmanRhodes2019/T1Limit.lean#L1150) | – |
| Mitchell et al. 2019, The T1 test distribution at μ₀ = 0 is ½ χ²₁ + ½ χ²₂ | [`Phylogenetics.QuartetTests.t1Tail_zero`](../../src/External/MitchellAllmanRhodes2019/T1Limit.lean#L563) | – |
| Mitchell et al. 2019, Off the boundary, the limit law of the T1 statistic is χ²₁ | [`Phylogenetics.QuartetTests.t1Stat_limitLaw_of_isT1Strict`](../../src/External/MitchellAllmanRhodes2019/T1Limit.lean#L1162) | – |
| Mitchell et al. 2019, Proposition 5.2 (t1Var_density) | [`Phylogenetics.QuartetTests.t1Var_density`](../../src/External/MitchellAllmanRhodes2019/T1Limit.lean#L438) | – |
| Mitchell et al. 2019, tendstoInDistribution_t1Stat | [`Phylogenetics.QuartetTests.tendstoInDistribution_t1Stat`](../../src/External/MitchellAllmanRhodes2019/T1Limit.lean#L1213) | – |
| Mitchell et al. 2019, tendsto_struveM₀_atTop | [`Phylogenetics.QuartetTests.tendsto_struveM₀_atTop`](../../src/External/MitchellAllmanRhodes2019/T1Limit.lean#L87) | – |
| Mitchell et al. 2019, Proposition 5.1 | [`External.MitchellAllmanRhodes2019.proposition5_1`](../../src/External/MitchellAllmanRhodes2019/T1Limit.lean#L1092) | – |
| Mitchell et al. 2019, t1Stat_limitLaw_density | [`Phylogenetics.QuartetTests.t1Stat_limitLaw_density`](../../src/External/MitchellAllmanRhodes2019/T1Limit.lean#L1185) | – |
| Mitchell et al. 2019, The density at μ₀ = 0 | [`Phylogenetics.QuartetTests.t1Density_zero`](../../src/External/MitchellAllmanRhodes2019/T1Limit.lean#L545) | – |
| Mitchell et al. 2019, Proposition 5.2 (proposition5_2) | [`External.MitchellAllmanRhodes2019.proposition5_2`](../../src/External/MitchellAllmanRhodes2019/T1Limit.lean#L1079) | – |
| Mitchell et al. 2019, With the true parameter, the T1 p-value at the boundary point is asymptotically uniform | [`Phylogenetics.QuartetTests.t1Tail_t1Stat_asymptoticallyUniform`](../../src/External/MitchellAllmanRhodes2019/T1Limit.lean#L1225) | – |
| Mitchell et al. 2019, The density tends to that of χ²₁ (tendsto_t1Density_atTop) | [`Phylogenetics.QuartetTests.tendsto_t1Density_atTop`](../../src/External/MitchellAllmanRhodes2019/T1Limit.lean#L648) | – |
| Mitchell et al. 2019, With the fitted parameter, the T1 p-value at the boundary point is not asymptotically uniform | [`Phylogenetics.QuartetTests.t1PValue_centroid_not_asymptoticallyUniform`](../../src/External/MitchellAllmanRhodes2019/T1Limit.lean#L1241) | – |
| Studier, Keppler 1988, the Lemma fails at a polytomy | [`External.StudierKeppler1988.not_lemmaAsPrinted`](../../src/External/StudierKeppler1988/Lemma.lean#L95) | – |

The route check (`python3 scripts/route_check.py check docs/paper_routes.tsv --accept docs/route_differences.tsv`)
confirms that every proof uses the results that the paper's proof cites, except the differences recorded in
[`docs/route_differences.tsv`](../../docs/route_differences.tsv), each with its reason. It merges all the declarations
that share a label, so `tinnik:theorem4`, for instance, is the union of [`TINNiK.theorem4`](../../src/TINNiK/Basic.lean#L629),
[`TINNiK.theorem4_of_rejects`](../../src/TINNiK/Basic.lean#L542) and [`TINNiK.theorem4_nj`](../../src/TINNiK/NJ.lean#L35).
TINNiK has no author TeX source, so its rows of [`docs/paper_routes.tsv`](../../docs/paper_routes.tsv) are written by hand.

## 9. Not formalized

**Empirical claims.**

- The simulations, the data analyses and measured running times, and TINNiK's report in Appendix C.3 that at the singularity both tests "perform very conservatively for small significance levels". Asymptotic running times are proved as counts of operations, with no machine model (Section 6).

**Results of cited sources that no proof here uses** are left out, and aren't listed. Mitchell et al.'s Theorem 3.1 is a
general theorem on regular models, which rests on van der Vaart's Theorem 16.7; only its conclusion for the cut model is
proved (Section 2).

**Statements that are false.** Each row is a statement, read as the row says, with the theorem that shows it fails. What's formalized is the failure, and the true form where there is one (Sections 3 and 4). Loose sentences, and proof steps that fail with the result standing, are in Section 3 and not here.

| Statement | Item | Counterexample |
| --- | --- | --- |
| TINNiK Appendix C.1, the MLE on the open cut model, at counts such as `(1, 0, 0)` | E31 | [`TINNiK.not_exists_generatingCutModel_maximizer`](../../src/TINNiK/Statistics/OpenCutModel.lean#L108) |
| Studier, Keppler 1988, the Lemma, at a polytomy. If the letter means binary trees, a failure of wording | Section 2 | [`External.StudierKeppler1988.not_lemmaAsPrinted`](../../src/External/StudierKeppler1988/Lemma.lean#L95) |

## 10. The paper in the literature

The search was made on 2026-10-31, for TINNiK together with [TOB-QMC](../TOBQMC/README.md) and
[ECToBlob](../ECToBlob/README.md), which build on it, in OpenAlex (works citing TINNiK, TOB-QMC, ECToBlob, Allman et al.
2023, Ané et al. 2024, Huber et al. 2025, "Beyond level-1", Rhodes et al. 2025, Xu and Ané 2023, NANUQ+, and the WABI
paper of Dai and Molloy; keyword searches), Crossref (title searches; its `updates` filter for corrections), Europe PMC
and PubMed, the bioRxiv API (versions, journal links), the arXiv API, GitHub's search API, the Archive of Formal Proofs,
and web search. We kept every correction or counterexample found, and otherwise the works that state or claim a result
about the tree of blobs, about which four-taxon information decides it, or about a method that starts from a tree of
blobs with a stated guarantee. Empirical studies, reviews and work on other problems were screened by abstract and left
out. Each statement below comes from the cited work's abstract or numbered statements, and we say where only the
abstract was read. Citation indexes lag, so recent citing work may be missing. A preprint's results are reported as
claimed. This section keeps the works that concern TINNiK; the reports of TOB-QMC and ECToBlob have the others.

### Before the paper

- Solís-Lemus, Ané, [PLoS Genet. 12 (2016)](https://doi.org/10.1371/journal.pgen.1005896) (SNaQ, pseudolikelihood on quartets); Baños, [Bull. Math. Biol. 81 (2019)](https://doi.org/10.1007/s11538-018-0485-4) ([arXiv 2017-11-28](https://arxiv.org/abs/1711.10545); read for its Proposition 7): "every cycle of size at least 4 and every hybrid node in a cycle of size at least 5" of a level-1 network are identifiable from gene tree quartets; Allman, Baños, Rhodes, [NANUQ, Algorithms Mol. Biol. 14 (2019)](https://doi.org/10.1186/s13015-019-0159-2) ([arXiv 2019-05-16](https://arxiv.org/abs/1905.07050)): level-1 inference from quartet hypothesis tests and a quartet intertaxon distance. TINNiK's introduction sets its algorithm against these level-1 methods.
- Allman, Baños, Mitchell, Rhodes, [J. Math. Biol. 86 (2023), 10](https://doi.org/10.1007/s00285-022-01838-9) ([arXiv 2022-05-06](https://arxiv.org/abs/2205.03466)): "most features of the unrooted tree of blobs" are determined by the distribution of gene quartet topologies, with no assumption on the level, through a B-quartet inference rule. It names a difficulty that TINNiK meets: a B-quartet of the network can have a cut-edge split on its induced 4-taxon network, "the main obstacle" (compare E30). It is formalized in this collection: [its folder](../AllmanEtAl2023/README.md).

What the paper adds. TINNiK ([bioRxiv 2024-04-24](https://doi.org/10.1101/2024.04.20.590418)) turns the sketch of Allman et al. 2023 into an algorithm with a consistency theorem (Theorem 4) and writes "We know of no other proposed algorithm for tree of blobs inference from biological data"; ECToBlob and TOB-QMC both describe it as the first. We found no earlier proof of TINNiK's Theorem 4. Section 2 lists the cited results the proofs use, including Mitchell et al. 2019 and Rhodes 2020.

### Concurrent work

- Huber, van Iersel, Jones, Moulton, Veenema-Nipius, [Bull. Math. Biol. 87 (2025), 136](https://doi.org/10.1007/s11538-025-01510-5) ([arXiv 2024-08-23](https://arxiv.org/abs/2408.12997)). Theorem 5.1, for binary semi-directed networks, which "does not put any restriction on the level": a nontrivial `A|B` is a cut-edge split exactly when `a₁a₂|b₁b₂` is a cut-edge split of the quarnet for all `a₁, a₂ ∈ A`, `b₁, b₂ ∈ B`. Corollary 5.6: the quarnets determine the blob tree.
- Frohn, Holtgrefe, van Iersel, Jones, Kelk, [J. Comput. Syst. Sci. 152 (2025), 103655](https://doi.org/10.1016/j.jcss.2025.103655) ([arXiv 2024-09-09](https://arxiv.org/abs/2409.06034)). Lemma 1 sharpens Huber et al.'s theorem by fixing `a₁` and `b₁`. Theorem 5 reconstructs the tree of blobs of a binary network of any level in `O(n³)` time from `O(n³)` quarnet-splits, and Proposition 6 gives a lower bound of `Ω(n log n + ℓn)` quarnet-splits at level `ℓ`.

Huber et al. and Frohn et al. work from exact quarnet information, with no statistical model. Both appeared after the TINNiK preprint and do not build on its algorithm.

### Since the paper

We found no erratum, retraction or published counterexample to a statement of TINNiK: Crossref's `updates` filter returned nothing for TINNiK or for Allman et al. 2023, and Europe PMC lists no correction for either. Among the works cited in this section, the only correction we found is that to Holtgrefe et al. 2025, for an omitted figure. The errors recorded in Section 3 are this audit's own.

Versions of the paper:

- TINNiK: no later version found. It is implemented, with ECToBlob and NANUQ+, in MSCquartets 3.3 (Rhodes, Allman, Ané, Baños, Mitchell, Wicke, [Bioinformatics, 2026-10-20](https://doi.org/10.1093/bioinformatics/btag775); [EcoEvoRxiv 2026-06-09](https://doi.org/10.32942/x24d5w); abstract only).

Work building on TINNiK:

- TOB-QMC (Dai, Han, Molloy; first public version [bioRxiv v1, 2025-11-06](https://doi.org/10.1101/2025.11.05.686850); published as [Genome Research, doi 10.1101/gr.282203.126](https://doi.org/10.1101/gr.282203.126)) and ECToBlob (Rhodes, Allman, Ané, Baños; [bioRxiv v1, 2026-05-31](https://doi.org/10.64898/2026.05.28.728501)), both formalized in this collection ([TOB-QMC](../TOBQMC/README.md), [ECToBlob](../ECToBlob/README.md)). They describe TINNiK as the first algorithm for the problem, and add a different outline: an optimum of the quartet criterion refines the tree of blobs, and edges are then contracted by quartet tests. TOB-QMC applies TINNiK's tests (ECToBlob compares with the T3 option) to `O(n)` four-taxon subsets around an edge and keeps the smallest p-value, with guarantees at level 1 (its Corollary 1, Theorem 2). TOB-QMC cites the statement of TINNiK's Theorem 4 for the correctness of the tests on all four-taxon subsets, which is a step of its proof, [`TINNiK.tests_correct`](../../src/TINNiK/Basic.lean#L506) (E21, in [TOB-QMC's report](../TOBQMC/REPORT.md)).
- Allman, Baños, Rhodes, Wicke, NANUQ⁺, [Algorithms Mol. Biol. 20 (2025), 14](https://doi.org/10.1186/s13015-025-00274-w) ([bioRxiv 2024-11-03](https://doi.org/10.1101/2024.10.30.621146); abstract only): given a tree of blobs from TINNiK, resolves its multifurcations to level-1 structure.
- Kolbow, Kong, Solís-Lemus, InPhyNet, [bioRxiv 2025-05-07](https://doi.org/10.1101/2025.05.05.652278) (preprint; abstract only): merges independently inferred level-1 networks and claims that a statistically consistent pipeline can be built with it. TOB-QMC says its guarantee comes from partitioning taxa by the tree of blobs.
- Allman, Ané, Baños, Rhodes, "Beyond level-1", [Bull. Math. Biol. 87 (2025), 166](https://doi.org/10.1007/s11538-025-01545-8) ([arXiv 2025-04-29](https://arxiv.org/abs/2504.21116)): identifiability of classes of galled tree-child networks of any level, by first identifying the tree of blobs. Its Proposition 5.1 states tree of blobs identifiability for binary networks with generic parameters under the displayed tree model and both independent and common inheritance, by "straightforward modifications" of Allman et al. 2023. Nevins, Claudio, Nguyen, SEQUoIA, [SIAM Undergrad. Res. Online 19 (2026)](https://doi.org/10.1137/26S1843342), turn that result into an algorithm using the NANUQ⁺ and TINNiK functions.
- Holtgrefe, Allman, Baños, van Iersel, Moulton, Rhodes, Wicke, [Bull. Math. Biol. 87 (2025), 168](https://doi.org/10.1007/s11538-025-01549-4) ([arXiv 2025-07-23](https://arxiv.org/abs/2507.17308); [correction, 88 (2026), 26](https://doi.org/10.1007/s11538-025-01564-5): a production error omitted Fig. 12b, results unaffected): features of outer-labeled planar galled level-2 networks distinguishable from displayed quartets, and circular decomposability of an inter-taxon quartet distance (Theorem 4.7). Its outline for an inference method starts from TINNiK's tree of blobs.
- Dai, Molloy, *Is level-1 blob reconstruction under the network multispecies coalescent easy?*, [WABI 2026, LIPIcs 390, 1:1–1:24](https://doi.org/10.4230/LIPIcs.WABI.2026.1) (published 2026-08-27, revised 2026-09-28; [bioRxiv v1 2026-06-10, v2 2026-09-21](https://doi.org/10.64898/2026.06.06.730607)). "Blob reconstruction" here means the inside of a level-1 blob, with the tree of blobs given as input. For binary semi-directed level-1 networks, NetCS finds the hybrid block and circular order of each blob of degree at least 5 (Lemma 1, Theorems 1–3). Its proofs use TOB-QMC's Theorem 2, and cite TINNiK's Theorem 4 for correctness of the tests on all 4-taxon subsets, the same reading as E21.

Other related work:

- Frohn, Holtgrefe, van Iersel, Jones, Kelk, [Ann. Comb. (2026)](https://doi.org/10.1007/s00026-026-00830-0) ([arXiv 2025-11-27](https://arxiv.org/abs/2511.22736); abstract only): sequence length sufficient to reconstruct binary level-1 networks under the CFN model. This is a finite-sample result on sequences at level 1. We found no such bound for TINNiK's tests.
- TOB-QMC's contraction step asks only whether the network induced on four taxa has a 4-blob, on the four-taxon subsets around an edge of a refinement, and TOB-QMC proves that this suffices at level 1 (its Corollary 1, Theorem 2). Allman et al. 2023 and TINNiK work at any level and use resolved topologies with the inference rule, since "the induced network on a B-quartet may or may not have a 4-blob, and can even be a tree". They do not ask about four-taxon sets around an edge of a refinement.

### Formalizations

We found no other formalization of TINNiK or of Allman et al. 2023, in any system. Searches covered GitHub (repository and code search, by language), the [Archive of Formal Proofs](https://www.isa-afp.org/) sitemap, OpenAlex and web search; they see public work only.

- [vltanh/lean4-phylogenetics](https://github.com/vltanh/lean4-phylogenetics) (Lean 4, public, Apache-2.0, created 2026-10-10, by the user who requested this formalization): the multispecies coalescent, Kingman's coalescent on forests with Tavaré's formula, rooted metric level-1 networks and their network coalescent, and the concordance factors of a cycle (Baños 2019). This project imports it, pinned at commit `f1a3592`, for its definitions and general results, among them neighbor joining and the four-point theorem (Section 2). Before that, it adapted the library's hierarchy kernel and Kingman modules from commit `06f684e` ([`docs/ADAPTED_SOURCES.md`](../../docs/ADAPTED_SOURCES.md), [`docs/COALESCENT_SOURCES.md`](../../docs/COALESCENT_SOURCES.md)). Its term-based level-1 network coalescent isn't used, and the network coalescent on arbitrary networks, first written for this project, has moved there.
- [vltanh/lean4-camus](https://github.com/vltanh/lean4-camus) (Lean 4, public, created 2026-10-10, same owner): the CAMUS dynamic program for level-1 networks (Willson, Warnow, [Bioinformatics 2026](https://doi.org/10.1093/bioinformatics/btag245)) and the statistical steps of that paper. Surveyed for this project ([`docs/CONFIGURATION.md`](../../docs/CONFIGURATION.md)), not imported.
- [vltanh/lean4-adr11](https://github.com/vltanh/lean4-adr11) (Lean 4, public, created 2026-10-04, same owner): Allman, Degnan, Rhodes 2011, identifying the rooted species tree from unrooted gene trees under the multispecies coalescent. Not used here.
- [SauersML/Descent](https://github.com/SauersML/Descent) (Lean 4, public, created 2026-08-05): "A Lean 4 formalization of genetic theory", with coalescent modules (`Descent/Coalescent/`); a code search of it for "multispecies" returns nothing. Not used here.
- Coq/Rocq, Isabelle, Agda: GitHub's language-filtered repository searches for "phylogenetic", "phylogeny" and "coalescent" returned nothing. No entry name in the [Archive of Formal Proofs](https://www.isa-afp.org/) sitemap contains "phylogen" or "coalesc"; we did not search the entries' contents.

## 11. What's next

### Open directions

- **Other inheritance.** Theorem 4 is proved under the NMSC with independent inheritance, `ρ = 0`, and the CF-detectability it uses, [`AllmanEtAl2023.cfDetectable_generic`](../../src/AllmanEtAl2023/CFDetectable.lean#L24), covers only `ρ = 0`. For binary networks at generic parameters, "Beyond level-1" (Proposition 5.1, Section 10) extends the arguments of Allman et al. 2023 to common inheritance, `ρ = 1`, for tree of blobs identifiability, and leaves other `ρ` aside. [`Phylogenetics.geneTreeDist`](https://github.com/vltanh/lean4-phylogenetics/blob/f1a3592dee6e3f7d5e7a68a0695ac457de23d2de/Phylogenetics/NMSC/Defs.lean#L94) includes `ρ`. What is needed first is the generic clause of CF-detectability at that `ρ`: a nonvanishing witness for each 4-taxon network.

### Simpler proofs

Each of these is, or was in an earlier version, the argument of a formal proof, so it is checked in Lean. We found none of them published, in the search of Section 10.

- **TINNiK's Theorem 4: the centroid.** The paper proves `CF ≠ (1/3,1/3,1/3)` for generic parameters by a separate analyticity argument. It follows from CF-detectability: strictly cut and non-cut CFs each have two different entries. This removes that paragraph of the proof, and also the need for a separate generic set. The formal proof of Theorem 4 takes the paper's step; [`TINNiK.tests_correct`](../../src/TINNiK/Basic.lean#L506) takes the shortcut, [`TINNiK.noCentroidCF_of_cfDetectable`](../../src/TINNiK/Basic.lean#L352).
- **TINNiK Proposition 6.** Computing the strip probabilities in rotated Cartesian coordinates, with Fubini in place of differentiating under the integral, and taking `G₄, G₅` as reflections of `G₃, G₂` at `-μ`, gives the same `d/dx Gᵢ` and needs no domination argument. An earlier version of the formal proof did this (in the repository's history); the formal proof now follows the paper.
- **The T3 test at the singularity.** Non-collapse needs no limit law: the T3 statistic is at most the T1 statistic, which is tight on the null, and the p-value is at least `½ χ²₁(10 t)`, since `sin² α₀ ≥ 1/10` on `[0,1]`.
- **Wilks-type limits for a trinomial.** The paper uses these limits; for a trinomial there is an elementary proof. One estimate, `|(1+v) log(1+v) - v - v²/2| ≤ 4|v|³` for `|v| ≤ 1/2` ([`Real.abs_entropyExcess_sub_le`](../../src/Basic/ForMathlib/Analysis/SpecialFunctions/EntropyExcess.lean#L50)), gives each likelihood ratio statistic as a sum of such terms, so each is uniformly close on bounded sets to a continuous function of the whitened frequencies, and an extended continuous mapping theorem, proved from the portmanteau theorem on open sets (`Phylogenetics.Trinomial.tendstoInDistribution_of_closeOnBalls`), finishes. This does not use van der Vaart's Theorem 16.7. At the centroid, Pearson's statistic is exactly `Z₁² + Z₂²` ([`Phylogenetics.Trinomial.pearsonS_centroid`](../../src/Basic/Testing/Trinomial/Whiten.lean#L425)).
- **Neighbor joining.** The side with at most `n/2` clusters is shorter than Studier and Keppler's two-node contradiction, and it covers polytomies.
- **Rhodes Theorem 2.** `{x,y,u,v} ∈ Q` holds exactly when no side contains `u, v` and avoids `x, y`, so count such pairs directly and split them by node, with no case split on the shape of the quartet.

### The formalization

- **Non-binary networks.** [`TINNiK.theorem4`](../../src/TINNiK/Basic.lean#L629) takes binary networks. [`AllmanEtAl2023.exists_reduction_of_blobDegree`](../../src/AllmanEtAl2023/Reduction.lean#L951) should allow blob vertices of degree at most 3 and no trivial 4-blob on any 4-set; a trivial 4-blob has the centroid CF at every parameter, so some such condition is needed.
- **Other inheritance.** [`AllmanEtAl2023.corollary1`](../../src/AllmanEtAl2023/Corollary1.lean#L67) is at `ρ = 0`. [`Phylogenetics.NMSC.one_sub_exp_le_nmscCF`](https://github.com/vltanh/lean4-phylogenetics/blob/f1a3592dee6e3f7d5e7a68a0695ac457de23d2de/Phylogenetics/NMSC/Witness.lean#L687) and the analytic parametrization hold for all `ρ`, and the mixture does too, so the same proof may reach the generic clause at other `ρ`: see the open direction above.
- **What [`src/Basic/`](../../src/Basic) holds for this paper.** [`src/Basic/README.md`](../../src/Basic/README.md) lists each module with its possible home. TINNiK uses `Defs` (the algorithm and its standing assumptions) and `Testing/*` (the hypothesis tests, their tails and limit laws), which stay in this project; `TreeCounts`, which could go to the library `Phylogenetics`; and, through these, `ForMathlib/*`, which could go to Mathlib.
- **Contributions to other libraries.** [`src/Basic/ForMathlib/`](../../src/Basic/ForMathlib) holds what could move to Mathlib, and TINNiK uses: the error function ([`src/Basic/ForMathlib/Analysis/SpecialFunctions/Erf.lean`](../../src/Basic/ForMathlib/Analysis/SpecialFunctions/Erf.lean)), the second-order expansion of `x log x` ([`src/Basic/ForMathlib/Analysis/SpecialFunctions/EntropyExcess.lean`](../../src/Basic/ForMathlib/Analysis/SpecialFunctions/EntropyExcess.lean)), the maximum of a multinomial likelihood ([`src/Basic/ForMathlib/Analysis/SpecialFunctions/GibbsInequality.lean`](../../src/Basic/ForMathlib/Analysis/SpecialFunctions/GibbsInequality.lean); Mathlib has Gibbs' inequality for `klDiv`), zero sets of analytic functions ([`src/Basic/ForMathlib/Analysis/AnalyticZeroSet.lean`](../../src/Basic/ForMathlib/Analysis/AnalyticZeroSet.lean)), strip probabilities and the orthonormal change of coordinates for two independent unit normals ([`src/Basic/ForMathlib/Probability/GaussianPlane.lean`](../../src/Basic/ForMathlib/Probability/GaussianPlane.lean); Mathlib has rotation invariance as `stdGaussian_map`), the `χ²₂` tail and Gaussian interval bounds ([`src/Basic/ForMathlib/Probability/GaussianTail.lean`](../../src/Basic/ForMathlib/Probability/GaussianTail.lean)), and an extended continuous mapping theorem ([`src/Basic/ForMathlib/Probability/Transfer.lean`](../../src/Basic/ForMathlib/Probability/Transfer.lean)). What is general to phylogenetics is already in the library [`lean4-phylogenetics`](https://github.com/vltanh/lean4-phylogenetics), which keeps what is standard to the field; [`src/Basic/README.md`](../../src/Basic/README.md) says what here could still go there.
- **Reuse of [`src/External/`](../../src/External).** The quartet metrization of Rhodes is stated for arbitrary unrooted trees, in [`src/External/Rhodes2020/`](../../src/External/Rhodes2020). [`src/External/MitchellAllmanRhodes2019/`](../../src/External/MitchellAllmanRhodes2019) has the limit law of the likelihood ratio at a cut model, and the limit laws and densities of the T3 and T1 tests for the trinomial. The rule and Lemma 3 of Allman et al., which TINNiK uses, are stated for arbitrary rooted networks, in [`src/AllmanEtAl2023/`](../../src/AllmanEtAl2023). These are for other formalizations citing the same sources.
