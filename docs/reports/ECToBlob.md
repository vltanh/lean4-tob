# Audit of ECToBlob

- **ECToBlob**: J. A. Rhodes, E. S. Allman, C. Ané, H. Baños, *Statistical inference of the Tree of Blobs of a
  phylogenetic network from quartet concordance factors*,
  [bioRxiv 10.64898/2026.05.28.728501 v1](https://www.biorxiv.org/content/10.64898/2026.05.28.728501v1).

This is the part of [the audit](../REPORT.md) about ECToBlob. [The audit](../REPORT.md) has what the five papers have in common: the summary and the status of the formalization, the results from prior work that they cite (Section 2), the readings that ECToBlob, TOB-QMC and TINNiK share (Section 6), the literature (Section 10) and what's next (Section 11). The sections here keep its numbers, and the findings are numbered across the five papers: here E1–E17, E35–E38, E41, E68.

## 3. Errors and gaps in the paper

**E1. Remark 3.2.** "Any multifurcation in a potential maximizer can be arbitrarily resolved to increase the MQS score" is
loose when some probabilities vanish: an arbitrary resolution need not increase the score. Some resolution with positive
probability does, since the three probabilities on a quartet sum to 1. [`ECToBlob.remark3_2`](../../src/ECToBlob/Section3.lean#L569) proves the remark.

**E2. Equation (3.3) is false as printed.** Summing over representative tuples counts a quartet once for each choice of
representatives of the other blocks, so a quartet in distinct blocks is overcounted by the product of the sizes of the
unused blocks. With blocks of sizes `(2,1,1,1,1)` and all cross-block CFs `1/3`, the left side is `3` and the right side `10/3` on a binary `T`; a multifurcating species tree with one positive-length cherry realizes these CFs, at all valid parameters under the NMSC ([`ECToBlob.Equation33Counterexample.not_equation33Printed`](../../src/ECToBlob/Equation33Counterexample.lean#L239)). This refutes
the identity, not Theorem 3.1. Repair, along the paper's route: weight each local term by the product of its four block sizes,
divide by `∏ᵢ |Xᵢ|`, and use the weighted local objective for the splicing. Lean: [`ECToBlob.equation3_3`](../../src/ECToBlob/Section3.lean#L86), [`ECToBlob.localWeight`](../../src/ECToBlob/Section3.lean#L187),
[`ECToBlob.theorem3_1`](../../src/ECToBlob/Section3.lean#L488). The identity also needs the `Xᵢ` to cover `X`, as the paper's do. The side claims at lines 497–500 and 504–507, and lines 501–504 (a splice of maximizers maximizes `f_m`), are false for the printed, unweighted `f̃_m`: with block sizes `(4,1,1,1,1)` and abstract weights, the maximizers of `f_m` and of the unweighted `f̃_m` can differ (not shown realized by a network). All hold for the weighted objective. Lines 461–463 also use, unstated, that the quartets a tree displays determine its splits ([`Phylogenetics.subset_of_forall_displays`](https://github.com/vltanh/lean4-phylogenetics/blob/9948de9b3cba330596424efd2dca9617be2efb0c/Phylogenetics/Tree/Splits.lean#L748)), and lines 504–507 that a side of a maximizer outside `T_B` refines one multifurcation ([`Phylogenetics.exists_mem_multifurcations_isBlockUnion`](https://github.com/vltanh/lean4-phylogenetics/blob/9948de9b3cba330596424efd2dca9617be2efb0c/Phylogenetics/Tree/Detach.lean#L230)).

**E3. Corollary 3.6, proof.** "The probability that `f̂` and `f` have different sets of optima → 0" is false when `f` has
ties: `f(a)=f(b)=0`, `fₙ(a)=1/(n+1)`, `fₙ(b)=0` converges uniformly with different argmax sets for every `n`, and ties do
occur here. The result holds: the empirical optima lie among the expected ones, by the gap to non-maximizers, which is what
the corollary says. Lean: [`ECToBlob.corollary3_6`](../../src/ECToBlob/Section3.lean#L1483).

**E4. Theorem 4.1, proof.** "The minimality of `|E|` implies that the funnel of `a₁` can only attach to `G̃₃` on the
`ã₂`-side" is elliptical: it needs the comparability of the sets `E(z, …)` of cut edges for different replacements. Going from
one funnel to all of them at once needs that funnels on opposite sides of an edge share no node, which is true and unstated. The "two
3-blobs" and "chain of 2-blobs" remarks are used only in part: the chain on `G̃₃` gives the comparability ([`ECToBlob.quartetCuts_subset_or_subset`](../../src/ECToBlob/Section4Funnels.lean#L1204)), and funnels on opposite sides share no node ([`ECToBlob.Induces.attach_funnels`](../../src/ECToBlob/Section4Funnels.lean#L301)).
Also unstated: that the `ã₂`-side is the component off the arc of `E` nearest `ã₂`, and that `b̃₁`, `b̃₂` lie in one component of `G̃₃ \ E`. The result holds.

**E5. Proposition 5.1.** Its proof rests on an adaptation of Allman et al.'s Theorem 1 stated by "checking the argument", and on atoms at hybrid length 0 that the source's measure doesn't have. The sketch is filled in here, and the claim holds, including on the face where all hybrid lengths vanish ([`ECToBlob.adaptedAllmanTheorem1`](../../src/ECToBlob/Section5.lean#L151), [`ECToBlob.proposition5_1`](../../src/ECToBlob/Section5.lean#L184)). The two other facts are proved for every network: [`Phylogenetics.NMSC.cut_alternatives`](https://github.com/vltanh/lean4-phylogenetics/blob/9948de9b3cba330596424efd2dca9617be2efb0c/Phylogenetics/NMSC/Exchangeability.lean#L550), [`Phylogenetics.NMSC.trivial_uniform`](https://github.com/vltanh/lean4-phylogenetics/blob/9948de9b3cba330596424efd2dca9617be2efb0c/Phylogenetics/NMSC/Exchangeability.lean#L771).

**E6. Lemma 6.1, proof.** `Bon(P) = km` omits the clipping at one in the paper's definition: `{3/4, 3/4}` gives `Bon = 1`, not
`3/2`. The inequality needed still holds. Lean: [`ECToBlob.bonP_le_mul`](../../src/ECToBlob/Section6.lean#L144).

**E7. §6 and Lemma 6.1: Cauchy endpoints.** The Cauchy combination is undefined at `p = 0`, an allowed input by `P ⊂ [0,1)`, and CBC
can feed `Bon = 1` into it. Lean's total tangent is not a reading of the undefined expression, so the Lean definitions
extend `f` continuously at the endpoints. Simultaneous inputs `0` and `1` have no continuous extension, but this case does not
occur on the lemma's domain: `Bon = 1` forces all inputs positive. Lean: [`Phylogenetics.cauchyP`](../../src/Basic/Testing/Combining.lean#L40), [`ECToBlob.cauchyP_pair_le_max`](../../src/ECToBlob/Section6.lean#L182). E11 and the value of CBC in E15 rest on this choice.

**E8. Lemma 6.1, part 1: the domain of the bound.** The lemma gives no domain for `B`, and evaluates it only at `(min P, max P)`, so `η ≤ D`. There the printed `B_{Cauchy,k}(η, D)`, with `f` extended at `0` as in E7, has all the claimed properties, and this is all that Theorem 8.2 uses. Off that domain it does not: it is not non-decreasing in `k` when `η > D` (at `η = 0.9`, `D = 0.1` it is `0.9` at `k = 1` and `0.5` at `k = 2`), and it fails `∼ kη` at `D = 0`. Lean states the lemma on `0 ≤ η ≤ D < 1` with the printed bound ([`ECToBlob.lemma6_1_part1`](../../src/ECToBlob/Section6.lean#L539), [`ECToBlob.cauchyBound`](../../src/ECToBlob/Section6.lean#L274)).

**E9. Algorithm 7.1, Step 10.** The late rule needs a convention when no iteration is rejected. Lean chooses the first iteration, which agrees
with the rule's intent ([`Phylogenetics.selectedIteration`](../../src/Basic/Defs.lean#L105)).

**E10. Theorem 8.2: missing genericity.** The theorem quantifies over any model meeting Assumption 1, whose converse clauses
hold only generically, while the proof invokes "our assumption of generic numerical parameters". For the literal general model
the statement is false: a one-parameter family of laws on a rooted 4-cycle network (Section 4) coincides at one parameter with the law of a
resolved tree, and no levels `α_n`, `β_n` of ECToBlob's algorithm can serve both ([`ECToBlob.Theorem82Literal.not_theorem8_2_literal`](../../src/ECToBlob/Theorem82Literal.lean#L227)). This is not a counterexample under the NMSC. Lean quantifies over
parameters meeting both clauses: [`ECToBlob.theorem8_2`](../../src/ECToBlob/Section8.lean#L714), and [`ECToBlob.theorem8_2_generic`](../../src/ECToBlob/Section8.lean#L751) for the generic form. Corrected as the user
agreed, 2026-10-27.

**E11. Theorem 8.2: boundary laws.** Assumption 1 allows both alternatives of a quartet with a cut-edge split to have probability zero, since (5.2) is a condition on `p₁ > p₂ = p₃` with no positivity, though the source's T1 null is `p₁ ≥ p₂ = p₃ > 0`. Counts on such a quartet are `(n,0,0)` almost surely, so its T1 statistic is `0` and its p-value is exactly `1` for every `n` ([`Phylogenetics.QuartetTests.t1PValue_degenerate`](../../src/Basic/Testing/Limits.lean#L339)). The proof does not cover this: Lemma 6.1 assumes `P ⊂ [0,1)`, and "individual p-values `≤ 1-δ`" fails. The printed Cauchy formula is undefined at `p = 1`, so what the theorem says here depends on how `f` is extended. With Lean's continuous extension (E7), `Cauchy` of positive p-values containing `1` is `1`, and the theorem fails for Cauchy and CBC, as follows. With a finite value of `f(1)`, as in the authors' R code (`tan((0.5-1)π)` is finite in floating point), Lemma 6.1 holds at `D = 1`, the printed proof goes through, and the output on the example below is correct.

Counterexample: the rooted 5-sunlet with arcs `r→v_b, r→v_c, v_b→v_a, v_c→v_d, v_a→h, v_d→h, h→e, v_a→a, v_b→b, v_c→c, v_d→d`, whose tree of blobs is the five-leaf star, under the Displayed Tree model with weights `γ` on `((a,e),b,(c,d))` and `1-γ` on `((a,b),c,(d,e))`. On `abcd`, the
network has the cut split `ab|cd` and the CF is `(1,0,0)`; the other four quartets have CFs `(γ, 1-γ, 0)` up to order, and no cut split or trivial 4-blob. Both directions of Assumption 1 hold, for all `γ ∈ (0,1)`. Take `T₀` with cherries `ab`, `cd`, a resolution of the star. The star test keeps `T₀`, since these CFs are not uniform; `T₀` displays `ab|cd`, so its overall
Cauchy p-value is `1 ≥ α_n`; so for all `α, β` both selection rules return `T₀`, which is not the star. Bon and BBC are not affected, since clipping loses the `1`. A mixture with weights `δ, 1-δ` of a point mass at `T₀` and the uniform law on all 15 binary trees shows that `-log β_n = o(n)` for any
sequence working on trees, so the failure does not depend on the choice of sequences. An independent reader recomputed the law, the network's predicates and Assumption 1, and simulated the Lean definitions on this example and on a second law with the same CF on `abcd` at `n = 500, 5000, 50000`: Cauchy and CBC returned `T₀` in every replicate, and Bon and BBC returned the star at `n ≥ 5000`. The same failure is proved in Lean, on another network, with the cut edge `de|abc` and a 4-cycle: [`FinNetwork.Binary.counterexample`](../../src/ECToBlob/DisplayedTreeExample.lean#L286) at the displayed tree model and all valid parameters, and [`BinaryLaw.not_theorem8_2_without_hpos`](../../src/ECToBlob/BinaryLawExample.lean#L707), that no sequences `α_n`, `β_n` serve all laws of binary gene trees meeting both directions of Assumption 1.

The NMSC has positive CFs ([`Phylogenetics.nmscCF_pos`](https://github.com/vltanh/lean4-phylogenetics/blob/9948de9b3cba330596424efd2dca9617be2efb0c/Phylogenetics/NMSC/Basic.lean#L96)), so the paper's main model loses nothing. Lean adds the hypothesis `hpos` to [`ECToBlob.theorem8_2`](../../src/ECToBlob/Section8.lean#L714), for these two variants only and on T1-strict quartets only. So `hpos` is what Lean's extension needs; a finite `f(1)` would need no such hypothesis. The user agreed to this correction on 2026-10-31.

**E12. Theorem 8.2, proof: the witness may be a trivial 4-blob.** "By Corollaries 4.2 and 4.3, `S^a(e)` is empty exactly when `e` is a cut-edge" fails for non-binary
networks: the quartet that those corollaries find may have a trivial 4-blob, on which the T1 null hypothesis holds (`CF = (1/3,1/3,1/3)` is on every T1 null).
So those corollaries do not show that a false edge has a T1-rejecting quartet. The statement holds. Repair: an edge surviving Step 3 has a quartet with no trivial 4-blob in its
multipartition, and from it [`ECToBlob.falseEdge_witness`](../../src/ECToBlob/FalseEdge.lean#L807) produces a quartet in the multipartition of `T₀` with neither a cut-edge split on the wanted bipartition nor a
trivial 4-blob, for all three quartet types at every stage. The formal proof starts from the paper's witness ([`ECToBlob.Deterministic.exists_not_inducedCutSplit_edgeQuartets`](../../src/ECToBlob/Deterministic.lean#L352)); the trivial 4-blob is the case that needs the repair ([`ECToBlob.Deterministic.Run.exists_not_t1Null_of_witness`](../../src/ECToBlob/Deterministic.lean#L375)). Logically Corollary 4.2 is then redundant (Section 11).

**E13. Theorem 8.2, proof: T1 at the centroid (a gap, and a loose sentence behind it).** "Arguing as for the star test" is not enough. Line 1017 excepts the centroid from the `χ²₁` limit, and the next sentence, lines 1018–1020, says "if the expected quartet CFs satisfy the null hypothesis, then the p-value from each individual 4-taxon set has a uniform distribution on [0, 1], asymptotically as the number of genes increases". At the centroid that fails: the fitted T1 p-value is not asymptotically uniform ([`Phylogenetics.QuartetTests.t1PValue_centroid_not_asymptoticallyUniform`](../../src/External/MitchellAllmanRhodes2019/T1Limit.lean#L1241)), though the p-value with the true parameter is ([`Phylogenetics.QuartetTests.t1Tail_t1Stat_asymptoticallyUniform`](../../src/External/MitchellAllmanRhodes2019/T1Limit.lean#L1225)). So Lemma 8.1 does not apply there. Repaired by tightness ([`Phylogenetics.QuartetTests.t1PValue_centroid_tight`](../../src/Basic/Testing/Limits.lean#L377)) and a union bound.
line 1017 notes this), so Lemma 8.1 does not apply there. Repaired by tightness ([`Phylogenetics.QuartetTests.t1PValue_centroid_tight`](../../src/Basic/Testing/Limits.lean#L377)) and a union bound.

**E14. Theorem 8.2, proof: the threshold.** `B(η_n, 1-δ) ∼ β_n` does not give `< β_n`. Repaired with a constant: `η_n = c₀ · level` ([`ECToBlob.Deterministic.exists_combineBounds`](../../src/ECToBlob/Deterministic.lean#L636)). Only
`b_n = o(n)` is used, not `b_n ∼ log n`, and the asymptotic of `α_n` is unused. "An individual p-value is below `η_n` exactly when the test statistic is above `b_n`" holds for the star test, whose test law is fixed, and "the T1 tests are handled similarly" does not carry it over:
the T1 law depends on an estimated `μ`. Lean bounds the T1 p-value by the `χ²₂` tail at the statistic: with `Z̄ = Z̄₀ + μ`, for `μ ≥ 0` the extra term `½(1 - sgn Z̄)Z̄²` is at most `Z̄₀²`, so the variable is at most `Z² + Z̄₀²` ([`Phylogenetics.QuartetTests.t1Tail_le_chiSqTwoTail`](../../src/Basic/Testing/Tails.lean#L81)).

**E15. Theorem 8.2, proof: bounds on the combined p-values.** "In `(α_n, 1-δ)`" is false on the upper side for Bon, BBC and CBC, even with positive alternatives: `Bon({3/4, 3/4}) = 1`, and then `BBC` is `1`, and so is `CBC` under the extension of E7. Individual p-values `≤ 1-δ` is false when alternatives vanish (E11). Only the
lower bounds are needed, and the upper individual bounds only for Cauchy and CBC. Lean uses [`ECToBlob.minP_le_combineP`](../../src/ECToBlob/Section6.lean#L234) and [`ECToBlob.combineP_le_two_mul`](../../src/ECToBlob/Section6.lean#L249) for Bon and BBC, and Lemma 6.1 for Cauchy and CBC.

**E16. Theorem 8.2, proof: intermediate trees.** The bounds `ε/(2s)` are per edge, but for type `mul` an edge's quartets depend on the random current tree `T_k`, so the union must
run over all states the algorithm could visit. Likewise "our prior choice of `M`" does not cover the sets that the overall `p_k` uses. The formal proof keeps the paper's test-by-test bounds with one test for each pair of a subset `T ⊆ T₀` and an edge of `T`, and one overall test for each `T`, and their number `K` replaces `s` ([`ECToBlob.eventually_t1_all`](../../src/ECToBlob/Section8.lean#L558)).

**E17. Theorem 8.2, proof: Step 3.** "`T_{k₁}` is obtained from `T₀` by contracting precisely those edges that resolve multifurcations" is false as written: on a 4-cycle, `ab|cd` resolves a multifurcation of the tree of blobs and survives Step 3, since its quartet is not uniform. The formal
proof shows what is needed: `T_B` is kept and each kept edge has a non-uniform quartet ([`ECToBlob.Deterministic.Run.treeOfBlobs_subset_afterStar`](../../src/ECToBlob/Deterministic.lean#L264), [`ECToBlob.Deterministic.Run.exists_not_uniform`](../../src/ECToBlob/Deterministic.lean#L281)).

### Remarks, discussion, and smaller points

These came from formalizing what the papers say in passing.

**E35. ECToBlob Remark 8.4: fails on a non-binary network.** The remark says the argument "indicates" that with `T₀` not a resolution the output keeps the cut edges of `T₀` and contracts the others, with no restriction on the network. For binary networks this holds ([`ECToBlob.Coarsening.remark8_4`](../../src/ECToBlob/Remark84.lean#L1560), with `hpos` of Theorem 8.2 for Cauchy and CBC), and on many non-binary pairs too ([`ECToBlob.Coarsening.remark8_4_of_noTrivial`](../../src/ECToBlob/Remark84.lean#L1529)). It fails on the tree `((0,1),2,3,4)` with one internal edge, with `T₀` the binary tree with cherries `02`, `34` and middle taxon `1`, the false edge `34|012` stays, since `34|01` is a cut split and `34|02`, `34|12` are trivial 4-blobs, all on the T1 null, and `34|01` is not uniform, so neither test contracts it ([`ECToBlob.Coarsening.Counterexample.not_remark8_4`](../../src/ECToBlob/Remark84.lean#L2306), for all options, at the sequences of Theorem 8.2, for a law on nine gene trees meeting Assumption 1 in the form of [`ECToBlob.theorem8_2`](../../src/ECToBlob/Section8.lean#L714); and [`ECToBlob.Coarsening.Counterexample.not_remark8_4_nmsc`](../../src/ECToBlob/Remark84.lean#L2358) for the NMSC itself, at every valid `θ` and `ρ ∈ [0,1]`). The limit on any network and any `T₀` is [`ECToBlob.Coarsening.limitTree`](../../src/ECToBlob/Remark84.lean#L780), and [`ECToBlob.Coarsening.limitTree_eq_inter_iff`](../../src/ECToBlob/Remark84.lean#L1148) is the exact criterion for the remark on a pair `(N, T₀)`. The cut edges of `T₀` stay in all cases, and every edge of the limit is compatible with the tree of blobs. The remark's wording is hedged ("indicates", "should").

**E36. ECToBlob Remark 3.3 and Proposition 5.1: "no anomalous quartets" must be strict.** Lines 402–404 cite Ané et al. for: the NMSC satisfies (3.1) when the network has no anomalous quartets and cut edges have positive lengths. The remark quotes no definition, and the paper's own use is strict (line 722). Their Definition 2 gives only `1/3 ≤ p_ab|cd`. At a `3₂`-cycle with hybrid arcs of length 0, arcs `s₁, s₂` on the other side of the cycle, whose sum is their `s₀`, and cut edge `t = log(1 + (1-ρ)γ(1-γ)(1-e^{-(s₁+s₂)}))`, all three CFs equal `1/3`: nothing is anomalous in that sense, (3.1) fails, and all three binary trees tie, so the conclusion of Theorem 3.1 fails too ([`ECToBlob.Remark33Counterexample.remark3_3_strict`](../../src/ECToBlob/Remark33Counterexample.lean#L683), for any `0 ≤ ρ < 1`). The parameters with a tie form a null set. Under TINNiK's definition, or TOB-QMC's, the claim holds. Lean's [`IsTQuartetNonanomalous`](../../src/Basic/Defs.lean#L254) and [`NoAnomalousQuartets`](../../src/Basic/Defs.lean#L190) are strict.

**E37. ECToBlob Theorem 8.2: "any model" and the displayed tree model (a step that fails; the conclusion depends on the variant).** With the convention of lines 289–293 that a star contributes `(1/3, 1/3, 1/3)`, a trivial 4-blob under the displayed tree model gives counts `(n/3, n/3, n/3)` on every sample and p-values exactly `1` ([`ECToBlob.pValues_of_hasTrivialFourBlob`](../../src/ECToBlob/Remark33.lean#L719)). So line 1065, "each individual p-value is uniformly distributed as n → ∞", is false there ([`ECToBlob.not_asymptoticallyUniform_starPValue`](../../src/ECToBlob/Remark33.lean#L732)), and Lemma 8.1 doesn't apply. [`ECToBlob.theorem8_2`](../../src/ECToBlob/Section8.lean#L714) takes binary gene trees, so it doesn't reach this model on non-binary networks. For Bon and BBC the conclusion holds on every network, binary or not, since the repaired proof uses only the lower bound on p-values: [`DisplayedTree.theorem8_2_displayed`](../../src/ECToBlob/DisplayedTree.lean#L410), with the converse of Assumption 1 as a hypothesis at the parameters, as in Theorem 8.2. For Cauchy and CBC it fails, through E11, and so under Lean's extension of the Cauchy transform at `p = 1` (E7): if an internal edge of the tree of blobs survives Step 3, the output is the tree after Step 3 at every level `α ≤ 1` ([`DisplayedTree.ectoblob_eq_afterStar`](../../src/ECToBlob/DisplayedTree.lean#L577)), with counterexamples on a binary network on five taxa ([`FinNetwork.Binary.counterexample`](../../src/ECToBlob/DisplayedTreeExample.lean#L286)) and on a non-binary one on six, with a trivial 4-blob and a polytomy ([`FinNetwork.NonBinary.counterexample`](../../src/ECToBlob/DisplayedTreeExample.lean#L564)).

**E38. ECToBlob §10: "the T1 test has greater power".** The null of T1 is nested in that of T3 ([`Phylogenetics.QuartetTests.isT3Null_of_isT1Null`](../../src/External/MitchellAllmanRhodes2019/T3Test.lean#L1230)), and the T3 statistic is at most the T1 statistic ([`Phylogenetics.QuartetTests.t3Stat_le_t1Stat`](../../src/External/MitchellAllmanRhodes2019/T3Test.lean#L538)). The p-values compare the other way at the maximum likelihood topology, since there the statistics agree and the T3 reference law is lower: [`Phylogenetics.QuartetTests.t3PValue_lt_t1PValue`](../../src/External/MitchellAllmanRhodes2019/T3Test.lean#L1253), and [`Phylogenetics.QuartetTests.exists_t3PValue_lt_t1PValue`](../../src/External/MitchellAllmanRhodes2019/T3Test.lean#L1262) at counts `(3,2,1)`. At a fixed level, if T1 rejects `s` and T3 doesn't, then `s` isn't the maximum likelihood topology. The sentence holds in the sense that at a CF on another half-line T1 rejects and T3 doesn't ([`Phylogenetics.QuartetTests.t1_rejects_where_t3_cannot`](../../src/External/MitchellAllmanRhodes2019/T3Test.lean#L1299)).

**E41. ECToBlob §3 and §7: what the observations need.**

- Lines 363–369 say that for `γ`s near 0 and 1, MQS infers displayed trees, on a set of positive measure, and that ties occur between. All three hold for the NMSC at every `ρ` ([`ECToBlob.Section3Observations.not_isNull_selectsDisplayed`](../../src/ECToBlob/Section3Observations.lean#L788), [`ECToBlob.Section3Observations.exists_tie_of_displayedTrees`](../../src/ECToBlob/Section3Observations.lean#L941), and [`ECToBlob.Section3Observations.fourCycle_not_isNull`](../../src/ECToBlob/Section3Observations.lean#L1114), [`ECToBlob.Section3Observations.fourCycle_exists_tie`](../../src/ECToBlob/Section3Observations.lean#L1104) on a 4-cycle). "Select a displayed tree" needs that tree binary: optimal trees are binary, so otherwise the statement is about its resolutions. "Sufficiently close" needs positive length on each internal edge of the displayed tree, which holds on binary networks and when all lengths are positive; it fails on `N₁` of Figure 1 with both hybrid arcs of length 0, where all CFs are `1/3` ([`ECToBlob.Section3Observations.isMQSOptimal_treeAC_of_length_zero`](../../src/ECToBlob/Section3Observations.lean#L1235)).
- Lines 922–935 on time. "The `k`th edge contracted might be incident to as many as `4 + k` other internal edges" holds as an upper bound ([`ECToBlob.Counts.card_incidentSides_le`](../../src/ECToBlob/Counts.lean#L410)) when `k` counts all edges contracted so far, Step 3's included, and the `4 + k` includes pendant edges; a step may contract several tied edges. It is not attained for `k > (s - 8)/2`. The printed sum `∑_{k=0}^{s-3}` has one term too many. And the `O(s⁵)` for `bi` and `quad` assumes p-values are stored: as written the algorithm recomputes at each step, which is `O(s⁶)` for every type. Storing them is sound ([`ECToBlob.Counts.edgeT1P_eq_of_qType_ne_mul`](../../src/ECToBlob/Counts.lean#L496)). The bounds are [`ECToBlob.Counts.ectoblobOperations_le`](../../src/ECToBlob/Counts.lean#L828), [`ECToBlob.Counts.ectoblobOperationsMul_le`](../../src/ECToBlob/Counts.lean#L849), [`ECToBlob.Counts.ectoblobOperationsRecomputing_le`](../../src/ECToBlob/Counts.lean#L869).

**E68. ECToBlob line 1422: "any valid test" (a loose sentence).** "The input star test p-values could come from any valid test of a multifurcation, and the input T1 test p-values from any test that the 4-taxon subnetwork has the desired edge split." The sentence says "could", and proving it shows what that takes. Validity isn't all that Theorem 8.2's proof uses: the tests need power at the levels `α_n`, `β_n`, and for Cauchy and CBC the null p-values must stay away from `1`. [`Framework.AdequateTests`](../../src/ECToBlob/Framework.lean#L252) lists what the proof needs, and [`Framework.consistency_ectoblobBy`](../../src/ECToBlob/Framework.lean#L327) is the conclusion for any tests meeting it. The passage after it, lines 1424–1432 on sum-of-pairs distances, is [`SumOfPairs.consistency_sumOfPairs`](../../src/ECToBlob/SumOfPairs.lean#L665), for the tests built there, with Bon and BBC.

### Typos

**E34.**

- ECToBlob, proof of Corollary 4.3: `∪_{j′≠i} B_{j′}` should be `∪_{j′≠j} B_{j′}`.
- ECToBlob, §7: "Theorem 3.6" for Corollary 3.6; §10: "Theorem 4.2 and Theorem 4.3" for Corollaries.

## 4. Missing hypotheses

| Where | Missing hypothesis | Counterexample without it | In the formalization |
| --- | --- | --- | --- |
| ECToBlob Theorem 8.2 (E10), agreed | Parameters outside the exceptional sets of Assumption 1's converse | A rooted 4-cycle network with arcs `s→r, s→d, r→u, r→v, u→h, v→h, u→a, v→b, h→c`, whose tree of blobs is a star, with the model `(1/2, 1/4+h(t), 1/4-h(t))`, `h(t) = (t-1)/(8(1+(t-1)²))`, with `t` the length of the arc `s→r`: at `t = 1` its law equals that of a resolved tree `ab\|cd`, which has the same `T₀`, so no levels `α_n`, `β_n` of ECToBlob's algorithm serve both ([`ECToBlob.Theorem82Literal.not_theorem8_2_literal`](../../src/ECToBlob/Theorem82Literal.lean#L227)) | [`ECToBlob.Assumption1Forward`](../../src/Basic/Defs.lean#L213), [`ECToBlob.Assumption1Converse`](../../src/Basic/Defs.lean#L219) hold at the given law; [`ECToBlob.theorem8_2_generic`](../../src/ECToBlob/Section8.lean#L751) |
| ECToBlob Theorem 8.2 (E11), agreed | For Cauchy and CBC only: positive alternatives on T1-strict quartets | The 5-sunlet of E11, under the continuous extension of `f` at `p = 1`; see E11 | `hpos` in [`ECToBlob.theorem8_2`](../../src/ECToBlob/Section8.lean#L714) |
| ECToBlob (3.3) (E2) | Block-size weights; the blocks cover `X` (they do in the paper) | E2; for the cover, `X = {a,b,c,d}`, `P = {{a}}`, `s = ab\|cd`, `w` the indicator of `s` | [`ECToBlob.equation3_3`](../../src/ECToBlob/Section3.lean#L86) |
| ECToBlob Theorem 8.2, "any model" (E37) | For Cauchy and CBC, under Lean's extension at `p = 1`: positive alternatives, which the displayed tree model lacks. The formal [`ECToBlob.theorem8_2`](../../src/ECToBlob/Section8.lean#L714) is on binary gene trees, a narrowing | [`FinNetwork.Binary.counterexample`](../../src/ECToBlob/DisplayedTreeExample.lean#L286), [`FinNetwork.NonBinary.counterexample`](../../src/ECToBlob/DisplayedTreeExample.lean#L564) | [`ECToBlob.theorem8_2`](../../src/ECToBlob/Section8.lean#L714); for Bon and BBC on the displayed tree model on any network, [`DisplayedTree.theorem8_2_displayed`](../../src/ECToBlob/DisplayedTree.lean#L410) |
| ECToBlob Remark 8.4 (E35) | Binary network, or [`ECToBlob.Coarsening.limitTree_eq_inter_iff`](../../src/ECToBlob/Remark84.lean#L1148) | E35 | [`ECToBlob.Coarsening.remark8_4`](../../src/ECToBlob/Remark84.lean#L1560) |
| ECToBlob Remark 3.3 (E36) | The strict reading of "no anomalous quartets" | E36 | [`ECToBlob.remark3_3_nmsc`](../../src/ECToBlob/Remark33.lean#L294) |

## 5. Redundant hypotheses

The Lean statements leave these out, except where the last column says otherwise and in [`src/MainResults/ECToBlob.lean`](../../src/MainResults/ECToBlob.lean), which keeps the paper's hypotheses.

| Result | Hypothesis that is not needed | Why | Lean |
| --- | --- | --- | --- |
| ECToBlob Theorem 4.1 | `A₁ ∩ A₂ = ∅`, `B₁ ∩ B₂ = ∅` | Only `A ∩ B = ∅` and the cover are used | [`ECToBlob.theorem4_1`](../../src/ECToBlob/Section4.lean#L55) |
| ECToBlob Proposition 5.1, forward clauses | Degree 2 or 3 in blobs | Exchangeability holds on every network | [`ECToBlob.proposition5_1`](../../src/ECToBlob/Section5.lean#L184), where the condition enters only through the generic clause |
| ECToBlob (3.3) | Nonempty blocks | | [`ECToBlob.equation3_3`](../../src/ECToBlob/Section3.lean#L86) |
| ECToBlob Remark 3.3, common inheritance | The standing conditions on parameters other than the cut arc's length | The bound holds at boundary parameters: each displayed tree gives it | [`Phylogenetics.RootedNetwork.one_sub_exp_le_sub_nmscCF_rho_one`](https://github.com/vltanh/lean4-phylogenetics/blob/9948de9b3cba330596424efd2dca9617be2efb0c/Phylogenetics/NMSC/DisplayedTreeModel.lean#L1231), [`ECToBlob.remark3_3_common`](../../src/ECToBlob/Remark33.lean#L302) |
| ECToBlob Remark 3.3, displayed tree model | Positive lengths on cut edges | The model is topological | [`ECToBlob.remark3_3_displayed`](../../src/ECToBlob/Remark33.lean#L519) |

## 6. How the formalization reads the paper

### Readings specific to this paper

- **Gene trees in ECToBlob's Theorem 8.2** are binary ([`ECToBlob.BinaryGeneTree`](../../src/Basic/Defs.lean#L224)), which is what the proof and the NMSC give; ECToBlob's unrooted topological gene trees need not be. So the theorem covers the NMSC at any `ρ`, and, for Bon and BBC, the Displayed Tree model when all displayed trees are binary: on a cut split that model's CF is `(1,0,0)`, so the hypothesis `hpos` fails for Cauchy and CBC. The Displayed Tree model on any network, whose gene trees need not be binary, is [`DisplayedTree.theorem8_2_displayed`](../../src/ECToBlob/DisplayedTree.lean#L410), for Bon and BBC (E37).
- **[`CutExchangeable`](https://github.com/vltanh/lean4-phylogenetics/blob/9948de9b3cba330596424efd2dca9617be2efb0c/Phylogenetics/Network/Quartets.lean#L67)** is the form in which ECToBlob's Theorem 3.1 uses its condition 2; [`ECToBlob.pendantChainInvariant_cutExchangeable`](../../src/ECToBlob/Section3.lean#L1363) derives it from the literal form, and [`ECToBlob.pendantChainInvariant_nmscCF`](../../src/ECToBlob/Remark33.lean#L1395), [`ECToBlob.pendantChainInvariant_displayedCF`](../../src/ECToBlob/Remark33.lean#L1436) prove the literal form for the models of Remark 3.3.
- **ECToBlob's Lemma 6.1** gives no domain for its bound. Lean states it on `0 ≤ η ≤ D < 1`, the values `(min P, max P)` reach, with the printed bound (E8).
- **Lemma 8.1** of ECToBlob is proved for functions of iid finite samples, with `δ` chosen first. This is the form its use needs, and is stronger in the order of quantifiers.
- **ECToBlob's §10, sentence by sentence.** "May increase power" (line 1411) and "might" (line 1433) claim nothing. That quartets are used for several edges is [`InPassing.exists_quartet_of_two_edges`](../../src/ECToBlob/InPassing.lean#L303). Lines 1419–1423 are E68. Combining edge p-values under CBC fails on one law meeting Assumption 1 ([`BinaryLaw.OnBinary.not_consistency_edge_combination_cbc`](../../src/ECToBlob/BinaryLawExample.lean#L1106)); on the general NMSC it isn't treated. On sum-of-pairs distances, the analogue of Assumption 1 is a hypothesis ([`SumOfPairs.SPForward`](../../src/ECToBlob/SumOfPairs.lean#L401), [`SumOfPairs.SPConverse`](../../src/ECToBlob/SumOfPairs.lean#L406)), the forward direction is [`SumOfPairs.spForward_averageDist`](../../src/ECToBlob/SumOfPairs.lean#L923) for the displayed tree model, on any network, and the converse is [`SumOfPairs.Instance.spConverse_averageDist`](../../src/ECToBlob/SumOfPairs.lean#L1136) on one binary network. On Log-det distances, a single Markov model on a tree is additive ([`LogDet.logDetDist_path`](../../src/ECToBlob/LogDet.lean#L165)) and a mixture need not be ([`LogDet.not_logDet_additive_mixture`](../../src/ECToBlob/LogDet.lean#L243)). "May be non-uniform" at lines 1435–1440 is [`InPassing.tendsto_prob_le_given_gt`](../../src/ECToBlob/InPassing.lean#L319), for a selection chosen for the purpose; the selection by MQS isn't treated. Post-selection p-values are future work there, and nothing is stated.
- **Remark 3.4.** Legried et al.'s model is [`External.LegriedEtAl2021.SpeciesTree`](../../src/External/LegriedEtAl2021/Model.lean#L41), a rooted binary species tree with a law on each edge of what one copy becomes, and gene trees as the addresses of their leaves in each species. The birth-death law isn't defined here, so the results hold for every such law, which their proofs allow. [`External.LegriedEtAl2021.displays_treeOfBlobs_iff`](../../src/External/LegriedEtAl2021/Bridge.lean#L556) and [`External.LegriedEtAl2021.displays_pickTree_iff`](../../src/External/LegriedEtAl2021/Bridge.lean#L408) connect it with the library's trees and networks, and [`Remark34.remark3_4_displays`](../../src/ECToBlob/Remark34.lean#L52) is (3.1) as the hypothesis of Theorem 3.1. The question the remark leaves open, on networks, has no model in any source, so [`Remark34.OpenQuestion`](../../src/ECToBlob/Remark34.lean#L100) has the model as a parameter.
- **The displayed tree model** of ECToBlob is [`Phylogenetics.RootedNetwork.displayedSides`](https://github.com/vltanh/lean4-phylogenetics/blob/9948de9b3cba330596424efd2dca9617be2efb0c/Phylogenetics/NMSC/DisplayedTreeModel.lean#L183) with [`ECToBlob.displayedTreeDist`](../../src/ECToBlob/Remark33.lean#L406). Remark 3.2's "no impact on the score" holds for the raw probabilities of resolved topologies ([`ECToBlob.remark3_2_no_impact`](../../src/ECToBlob/Remark33.lean#L606)), and under the convention of lines 289–293 each new quartet adds `1/3` ([`ECToBlob.quartetScore_displayedCF_of_resolution`](../../src/ECToBlob/Remark33.lean#L619)), the reason for the remark's last sentence, [`ECToBlob.isBinaryTree_of_displayedCF_maximizer`](../../src/ECToBlob/Remark33.lean#L541).

## 7. Departures from the paper's proofs

The last column but one says why, and says so plainly when a departure isn't forced. Mechanics and representation with the same content aren't listed: paths as sets of arcs, for instance, and a concrete value for "sufficiently long".

| Result | The paper's argument | The formalization's | Why | E-item |
| --- | --- | --- | --- | --- |
| ECToBlob Theorem 3.1 | Local objective `f̃_m`; (3.3) | Weighted by the block sizes; the claims on all maximizers hold in that form ([`ECToBlob.innerSum_le_of_isBlockAttachment`](../../src/ECToBlob/Section3.lean#L219), [`ECToBlob.quartetScore_le_pullTree_of_starPart_maximizer`](../../src/ECToBlob/Section3.lean#L287), [`ECToBlob.exists_splice_of_maximizer`](../../src/ECToBlob/Section3.lean#L517)) | Gap: (3.3) is false, and so is the side claim at lines 497–500 for the unweighted objective | E2 |
| ECToBlob Remark 3.2 | "Arbitrarily resolved" increases the score | One chosen split of positive weight | Gap: a resolution of weight zero doesn't increase it | E1 |
| ECToBlob Corollary 3.6 | Equal sets of optima | Containment, by the gap to non-maximizers | Gap | E3 |
| ECToBlob Theorem 4.1 | The induced subnetwork has two 3-blobs, joined by chains of 2-blobs and cut edges | The same on `G̃₄`, without suppression, with degree counted by cut edges with a taxon beyond them ([`ECToBlob.IsTwoBlobs.exists_three_cuts`](../../src/ECToBlob/Section4Funnels.lean#L1007), [`ECToBlob.IsTwoBlobs.exists_two_blob`](../../src/ECToBlob/Section4Funnels.lean#L1109)) | Not forced. On `G̃₄` the arc from the root to the LSA can be a third cut edge | E4 |
| ECToBlob Proposition 5.1 | Quarnet by quarnet, "checking the argument" of Allman et al. | On `N` directly, for each 4-set, with the witness on the face where hybrid lengths are 0; "no anomalous quartets" read strictly | The first isn't forced: it avoids pushing this measure, with its atoms, through the map of parameters. The second is forced | E5, E36 |
| ECToBlob Theorem 8.2 | Per-edge bounds, Lemma 8.1 per edge, Corollaries 4.2, 4.3; `B ∼ β_n`; T1 threshold "exactly when"; Step 3 "precisely"; bounds `(α_n, 1-δ)` | The same structure. Repairs: one test per pair (`T ⊆ T₀`, edge of `T`) and `K` tests; [`falseEdge_witness`](../../src/ECToBlob/FalseEdge.lean#L807) in the trivial 4-blob case; a constant `c₀`; tightness at the centroid; the `χ²₂` bound for T1; a weaker Step 3 claim; only the lower bounds; degenerate nulls apart; `2k · min` for Bon and BBC. The statement is on binary gene trees, a narrowing and not a repair (E37). `quad` on a non-binary `T₀` uses the multipartition, and the late rule fixes a value when no `p_k < α` (E9); these fill what the paper leaves undefined | Gaps, except the count: `K` counts sides of edges, and shares of the failure probability differ, which is immaterial and not forced | E10–E17, E37 |
| ECToBlob Theorem 8.2, displayed tree model | Line 1065, uniform p-values, and Lemma 8.1 | Each null p-value is `1` on every sample of positive probability, which gives the lower bound Bon and BBC use ([`DisplayedTree.theorem8_2_displayed`](../../src/ECToBlob/DisplayedTree.lean#L410)) | Forced: line 1065 is false under this model | E37 |

## 8. What each result depends on

<!-- Generated from scripts/Audit.lean -->

| Result | Lean | Results from prior work used |
| --- | --- | --- |
| ECToBlob Lemma 3.5 | [`ECToBlob.lemma3_5`](../../src/ECToBlob/Section3.lean#L34) | – |
| ECToBlob (3.2) | [`ECToBlob.equation3_2`](../../src/ECToBlob/Section3.lean#L52) | – |
| ECToBlob (3.3), repaired | [`ECToBlob.equation3_3`](../../src/ECToBlob/Section3.lean#L86) | – |
| ECToBlob Theorem 3.1 | [`ECToBlob.theorem3_1`](../../src/ECToBlob/Section3.lean#L488) | – |
| ECToBlob Remark 3.2 | [`ECToBlob.remark3_2`](../../src/ECToBlob/Section3.lean#L569) | – |
| ECToBlob Corollary 3.6 | [`ECToBlob.corollary3_6`](../../src/ECToBlob/Section3.lean#L1483) | – |
| ECToBlob Theorem 4.1 | [`ECToBlob.theorem4_1`](../../src/ECToBlob/Section4.lean#L55) | – |
| ECToBlob Corollary 4.2 | [`ECToBlob.corollary4_2`](../../src/ECToBlob/Section4.lean#L172) | – |
| ECToBlob Corollary 4.3 | [`ECToBlob.corollary4_3`](../../src/ECToBlob/Section4.lean#L204) | – |
| ECToBlob Proposition 5.1 | [`ECToBlob.proposition5_1`](../../src/ECToBlob/Section5.lean#L184) | [`ECToBlob.adaptedAllmanTheorem1`](../../src/ECToBlob/Section5.lean#L151) |
| ECToBlob Lemma 6.1, part 1 | [`ECToBlob.lemma6_1_part1`](../../src/ECToBlob/Section6.lean#L539) | – |
| ECToBlob Lemma 6.1, part 2 | [`ECToBlob.lemma6_1_part2`](../../src/ECToBlob/Section6.lean#L576) | – |
| ECToBlob Lemma 8.1 | [`ECToBlob.lemma8_1`](../../src/ECToBlob/Lemma81.lean#L18) | – |
| ECToBlob Theorem 8.2 | [`ECToBlob.theorem8_2`](../../src/ECToBlob/Section8.lean#L714) | – |
| ECToBlob Remark 3.3, NMSC | [`ECToBlob.remark3_3_nmsc`](../../src/ECToBlob/Remark33.lean#L294) | – |
| ECToBlob Remark 3.3, common inheritance | [`ECToBlob.remark3_3_common`](../../src/ECToBlob/Remark33.lean#L302) | – |
| ECToBlob Remark 3.3, displayed tree model | [`ECToBlob.remark3_3_displayed`](../../src/ECToBlob/Remark33.lean#L519) | – |
| ECToBlob Remark 3.3, the counterexample to its non-strict reading | [`ECToBlob.Remark33Counterexample.remark3_3_strict`](../../src/ECToBlob/Remark33Counterexample.lean#L683) | – |
| ECToBlob Remark 5.2 | [`ECToBlob.Remark52.remark5_2`](../../src/ECToBlob/Remark52.lean#L1082) | – |
| ECToBlob Remark 8.3, NANUQ | [`ECToBlob.remark83_nanuq`](../../src/ECToBlob/Remark83.lean#L102) | – |
| ECToBlob Remark 8.3, TINNiK | [`ECToBlob.remark83_tinnik`](../../src/ECToBlob/Remark83.lean#L235) | [`AllmanEtAl2023.CFDetectable`](../../src/AllmanEtAl2023/CFDetectable.lean), [`AllmanEtAl2023.closure_complete`](../../src/AllmanEtAl2023/Basic.lean#L724), [`AllmanEtAl2023.closure_sound`](../../src/AllmanEtAl2023/Basic.lean#L732), [`External.Rhodes2020.theorem2`](../../src/External/Rhodes2020/Theorem2.lean#L776), [`External.Rhodes2020.quartetWeight_ge_two`](../../src/External/Rhodes2020/Theorem2.lean#L868) |
| ECToBlob Remark 8.4, binary networks | [`ECToBlob.Coarsening.remark8_4`](../../src/ECToBlob/Remark84.lean#L1560) | – |
| ECToBlob Remark 8.4, the counterexample | [`ECToBlob.Coarsening.Counterexample.not_remark8_4`](../../src/ECToBlob/Remark84.lean#L2306) | – |
| ECToBlob Remark 8.4, the counterexample under the NMSC | [`ECToBlob.Coarsening.Counterexample.not_remark8_4_nmsc`](../../src/ECToBlob/Remark84.lean#L2358) | – |
| ECToBlob §3, MQS at a displayed tree, positive measure | [`ECToBlob.Section3Observations.not_isNull_selectsDisplayed`](../../src/ECToBlob/Section3Observations.lean#L788) | – |
| ECToBlob §3, ties | [`ECToBlob.Section3Observations.exists_tie_of_displayedTrees`](../../src/ECToBlob/Section3Observations.lean#L941) | – |
| ECToBlob §10, the line test | [`ECToBlob.Remarks.consistency_line_nmsc`](../../src/ECToBlob/Remarks.lean#L566) | [`ECToBlob.adaptedAllmanTheorem1`](../../src/ECToBlob/Section5.lean#L151) |
| ECToBlob §10, a random T₀ | [`ECToBlob.Remarks.consistency_random_tree`](../../src/ECToBlob/Remarks.lean#L637) | – |
| ECToBlob §10, data splitting | [`ECToBlob.Remarks.consistency_data_splitting`](../../src/ECToBlob/Remarks.lean#L718) | – |
| ECToBlob §10, combining edge p-values | [`ECToBlob.Remarks.consistency_edge_combination`](../../src/ECToBlob/Remarks.lean#L978) | – |
| Rhodes et al. 2025, The analogue of Assumption 1 in the forward direction, for the displayed tree model, on any network | [`ECToBlob.SumOfPairs.spForward_averageDist`](../../src/ECToBlob/SumOfPairs.lean#L923) | – |
| Hoeffding 1963, Hoeffding's inequality | [`ECToBlob.SumOfPairs.iidProb_mean_ge_le`](../../src/ECToBlob/SumOfPairs.lean#L87) | – |
| ECToBlob, Lines 215-216, the other way | [`ECToBlob.Biconnected.blobSetoid_of_isBiconnectedSet`](../../src/ECToBlob/Biconnected.lean#L307) | – |
| ECToBlob, Lines 215-216, one way | [`ECToBlob.Biconnected.isBiconnectedSet_blob`](../../src/ECToBlob/Biconnected.lean#L265) | – |
| ECToBlob, Lines 217-218 | [`ECToBlob.Biconnected.blobSetoid_of_two_biconnected`](../../src/ECToBlob/Biconnected.lean#L338) | – |
| ECToBlob, Lines 1419-1423: the conclusion of Theorem 8.2 for any adequate tests | [`ECToBlob.Framework.consistency_ectoblobBy`](../../src/ECToBlob/Framework.lean#L327) | – |
| ECToBlob, The choice of the BIC (lines 1160-1163) | [`ECToBlob.Framework.theorem8_2_bic`](../../src/ECToBlob/Framework.lean#L464) | – |
| ECToBlob, Theorem 8.2 at other levels (lines 1159-1167) | [`ECToBlob.Framework.theorem8_2_levels`](../../src/ECToBlob/Framework.lean#L440) | – |
| ECToBlob, Under the displayed tree model, Cauchy and CBC return the tree after Step 3 | [`ECToBlob.DisplayedTree.ectoblob_eq_afterStar`](../../src/ECToBlob/DisplayedTree.lean#L577) | – |
| ECToBlob, Theorem 8.2 | [`ECToBlob.DisplayedTree.theorem8_2_displayed`](../../src/ECToBlob/DisplayedTree.lean#L410) | – |
| ECToBlob, Cauchy and CBC on the displayed tree model: a false edge that Step 3 keeps stays | [`ECToBlob.DisplayedTree.tendsto_ectoblob_displayed_zero`](../../src/ECToBlob/DisplayedTree.lean#L622) | – |
| ECToBlob, The counterexample on a non-binary network | [`ECToBlob.FinNetwork.NonBinary.counterexample`](../../src/ECToBlob/DisplayedTreeExample.lean#L564) | – |
| ECToBlob, The counterexample on a binary network | [`ECToBlob.FinNetwork.Binary.counterexample`](../../src/ECToBlob/DisplayedTreeExample.lean#L286) | – |
| ECToBlob, E11 of the report: Theorem 8.2 without its hypothesis on the alternatives is false for Cauchy and CBC, at all ... | [`ECToBlob.BinaryLaw.not_theorem8_2_without_hpos`](../../src/ECToBlob/BinaryLawExample.lean#L707) | – |
| ECToBlob, Lines 1164-1167: we also need o(n) cutoff values | [`ECToBlob.BinaryLaw.OnFour.tendsto_log_beta_of_consistent`](../../src/ECToBlob/BinaryLawExample.lean#L622) | – |
| ECToBlob §10: combining the edge p-values under CBC fails | [`ECToBlob.BinaryLaw.OnBinary.not_consistency_edge_combination_cbc`](../../src/ECToBlob/BinaryLawExample.lean#L1106) | – |
| ECToBlob, Lines 1419-1432: the framework on distances | [`ECToBlob.SumOfPairs.consistency_sumOfPairs`](../../src/ECToBlob/SumOfPairs.lean#L665) | – |
| ECToBlob, The tree of blobs is identifiable from average pairwise distances | [`ECToBlob.SumOfPairs.treeOfBlobs_eq_of_eq`](../../src/ECToBlob/SumOfPairs.lean#L525) | – |
| ECToBlob, The framework on average distances, for the displayed tree model | [`ECToBlob.SumOfPairs.consistency_averageDist`](../../src/ECToBlob/SumOfPairs.lean#L1057) | – |
| ECToBlob, Line 882 (multipartitionQuartets_anti) | [`ECToBlob.InPassing.multipartitionQuartets_anti`](../../src/ECToBlob/InPassing.lean#L1314) | – |
| ECToBlob, Lines 892-893: the combined p-value assessing all edges remaining in T_ki need not monotonically increase ... | [`ECToBlob.InPassing.exists_treeTestP_decreasing`](../../src/ECToBlob/InPassing.lean#L1034) | – |
| ECToBlob, Lines 673-679 | [`ECToBlob.InPassing.Sunlet.not_corollary4_3_with_taxa`](../../src/ECToBlob/InPassing.lean#L286) | – |
| ECToBlob, Line 882 (multipartitionQuartets_subset_bipartitionQuartets) | [`ECToBlob.InPassing.multipartitionQuartets_subset_bipartitionQuartets`](../../src/ECToBlob/InPassing.lean#L1325) | – |
| ECToBlob, Lines 1164-1165: any valid choice needs β_n → 0 | [`ECToBlob.InPassing.tendsto_beta_of_consistent`](../../src/ECToBlob/InPassing.lean#L856) | – |
| ECToBlob, Lines 760-761 | [`ECToBlob.InPassing.tendsto_starS_sub_pearsonS`](../../src/ECToBlob/InPassing.lean#L1262) | – |
| ECToBlob, tendsto_prob_le_given_gt | [`ECToBlob.InPassing.tendsto_prob_le_given_gt`](../../src/ECToBlob/InPassing.lean#L319) | – |
| ECToBlob, The statement of line 728 | [`ECToBlob.InPassing.Assumption1ForAllRho`](../../src/ECToBlob/InPassing.lean#L229) | – |
| ECToBlob, If the sequence of combined p-values is monotone, then both methods agree | [`ECToBlob.InPassing.selected_early_eq_late_of_monotone`](../../src/ECToBlob/InPassing.lean#L171) | – |
| ECToBlob, Lines 293-306 | [`ECToBlob.InPassing.tendsto_inferred`](../../src/ECToBlob/InPassing.lean#L493) | – |
| ECToBlob, Lines 1164-1165: any valid choice needs α_n → 0, in order to fail to reject a true null consistently | [`ECToBlob.InPassing.tendsto_alpha_of_consistent`](../../src/ECToBlob/InPassing.lean#L780) | – |
| ECToBlob, Lines 523-526 | [`ECToBlob.InPassing.exists_oscillating_optimum`](../../src/ECToBlob/InPassing.lean#L656) | – |
| ECToBlob, tendsto_altBon_div | [`ECToBlob.InPassing.tendsto_altBon_div`](../../src/ECToBlob/InPassing.lean#L43) | – |
| ECToBlob, cauchyP_pair | [`ECToBlob.InPassing.cauchyP_pair`](../../src/ECToBlob/InPassing.lean#L75) | – |
| ECToBlob, exists_quartet_of_two_edges | [`ECToBlob.InPassing.exists_quartet_of_two_edges`](../../src/ECToBlob/InPassing.lean#L303) | – |
| ECToBlob, Otherwise, the early method tree is more resolved than the late one | [`ECToBlob.InPassing.selectedIteration_early_le_late`](../../src/ECToBlob/InPassing.lean#L142) | – |
| ECToBlob, exists_early_selected | [`ECToBlob.InPassing.exists_early_selected`](../../src/ECToBlob/InPassing.lean#L119) | – |
| ECToBlob, Lines 1164-1167, both levels: we also need o(n) cutoff values | [`ECToBlob.BinaryLaw.tendsto_log_levels_of_valid`](../../src/ECToBlob/LevelCutoffs.lean#L462) | – |
| ECToBlob, Lines 1164-1167: we also need o(n) cutoff values, for α_n | [`ECToBlob.BinaryLaw.OnBlob.tendsto_log_alpha_of_consistent`](../../src/ECToBlob/LevelCutoffs.lean#L377) | – |
| ECToBlob, A mixture is not additive | [`ECToBlob.LogDet.not_logDet_additive_mixture`](../../src/ECToBlob/LogDet.lean#L243) | – |
| ECToBlob, Tree additivity | [`ECToBlob.LogDet.logDetDist_path`](../../src/ECToBlob/LogDet.lean#L165) | – |
| ECToBlob, A gene family that follows one species tree picked at random | [`ECToBlob.Remark34.remark3_4_mixture`](../../src/ECToBlob/Remark34.lean#L80) | – |
| ECToBlob, Remark 3.4, multiple alleles | [`ECToBlob.Remark34.remark3_4_multi`](../../src/ECToBlob/Remark34.lean#L68) | [`External.LegriedEtAl2021.eq7`](../../src/External/LegriedEtAl2021/Theorem1.lean#L896) |
| ECToBlob, The open question of Remark 3.4 | [`ECToBlob.Remark34.OpenQuestion`](../../src/ECToBlob/Remark34.lean#L100) | – |
| ECToBlob, Remark 3.4, one gene copy | [`ECToBlob.Remark34.remark3_4_single`](../../src/ECToBlob/Remark34.lean#L41) | [`External.LegriedEtAl2021.eq5`](../../src/External/LegriedEtAl2021/Theorem1.lean#L868) |
| ECToBlob, Remark 3.4, on the network of the species tree | [`ECToBlob.Remark34.remark3_4_displays`](../../src/ECToBlob/Remark34.lean#L52) | [`External.LegriedEtAl2021.eq5`](../../src/External/LegriedEtAl2021/Theorem1.lean#L868) |
| ECToBlob, equation (3.3) as printed is false | [`ECToBlob.Equation33Counterexample.not_equation33Printed`](../../src/ECToBlob/Equation33Counterexample.lean#L239) | – |
| ECToBlob, Theorem 8.2 on the literal general model is false | [`ECToBlob.Theorem82Literal.not_theorem8_2_literal`](../../src/ECToBlob/Theorem82Literal.lean#L227) | – |

## 9. Not formalized

**Empirical claims.**

- ECToBlob, TOB-QMC, TINNiK: the simulations, the data analyses and measured running times, ECToBlob's evidence at lines 907–910 that combined p-values aren't monotone, and TINNiK's report in Appendix C.3 that at the singularity both tests "perform very conservatively for small significance levels". Asymptotic running times are proved as counts of operations, with no machine model (Section 6).

**Statements that are false.** Each row is a statement, read as the row says, with the theorem that shows it fails. What's formalized is the failure, and the true form where there is one (Sections 3 and 4). Loose sentences, and proof steps that fail with the result standing, are in Section 3 and not here: among them E13, E64, E68–E74.

| Statement | Item | Counterexample |
| --- | --- | --- |
| ECToBlob (3.3) | E2 | [`ECToBlob.Equation33Counterexample.not_equation33Printed`](../../src/ECToBlob/Equation33Counterexample.lean#L239) |
| ECToBlob Theorem 8.2 on the literal general model, for ECToBlob's levels | E10 | [`ECToBlob.Theorem82Literal.not_theorem8_2_literal`](../../src/ECToBlob/Theorem82Literal.lean#L227) |
| ECToBlob Theorem 8.2, for Cauchy and CBC with no hypothesis on the alternatives, under Lean's continuous extension of a formula undefined at `p = 1` | E11 | [`BinaryLaw.not_theorem8_2_without_hpos`](../../src/ECToBlob/BinaryLawExample.lean#L707), [`FinNetwork.Binary.counterexample`](../../src/ECToBlob/DisplayedTreeExample.lean#L286) |
| ECToBlob Remark 3.3, under the non-strict definition it cites | E36 | [`ECToBlob.Remark33Counterexample.remark3_3_strict`](../../src/ECToBlob/Remark33Counterexample.lean#L683) |
| ECToBlob Remark 8.4, what it says the argument "indicates", on a non-binary network | E35 | [`ECToBlob.Coarsening.Counterexample.not_remark8_4`](../../src/ECToBlob/Remark84.lean#L2306), [`ECToBlob.Coarsening.Counterexample.not_remark8_4_nmsc`](../../src/ECToBlob/Remark84.lean#L2358) |
| ECToBlob line 1065 under the displayed tree model | E37 | [`ECToBlob.not_asymptoticallyUniform_starPValue`](../../src/ECToBlob/Remark33.lean#L732) |
