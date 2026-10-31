# Audit of the papers and the formalization

Papers, with the versions audited:

- **ECToBlob**: J. A. Rhodes, E. S. Allman, C. Ané, H. Baños, *Statistical inference of the Tree of Blobs of a
  phylogenetic network from quartet concordance factors*,
  [bioRxiv 10.64898/2026.05.28.728501 v1](https://www.biorxiv.org/content/10.64898/2026.05.28.728501v1).
- **TOB-QMC**: J. Dai, Y. Han, E. K. Molloy, *Quartet-based species tree methods enable fast and consistent tree of
  blobs reconstruction under the network multispecies coalescent*,
  [bioRxiv 10.1101/2025.11.05.686850 v5](https://www.biorxiv.org/content/10.1101/2025.11.05.686850v5), with its supplement
  (internally dated February 26, 2026; its link to v5 is unconfirmed, and its numbering differs from v5's in places).
- **TINNiK**: E. S. Allman, H. Baños, J. D. Mitchell, J. A. Rhodes, *TINNiK: inference of the tree of blobs of a species
  network under the coalescent model*, [Algorithms Mol. Biol. 19 (2024), 23](https://doi.org/10.1186/s13015-024-00266-2).

No author TeX was available. The audit was made against PDF text and publisher XML (which embeds TeX for TINNiK's
equations), so line numbers below refer to these sources: for TOB-QMC, the line numbers printed in the preprint; for
ECToBlob, lines of a text extraction, given only as a locator; the labels of the route check (`ecto:…`,
`tob2025:…`, `tinnik:…`) are this project's. Section, result and equation numbers are the papers'.

Status of the formalization:

- **Proved, by the papers' arguments** except for the departures of Section 7: every numbered result of ECToBlob
  (Theorems 3.1, 4.1, 8.2; Lemmas 3.5, 6.1, 8.1; Corollaries 3.6, 4.2, 4.3; equations (3.2), (3.3); Remark 3.2), of TOB-QMC
  (Lemmas 2, 3, 4; equations (1)–(4); Theorems 1, 2; Corollary 1; the ASTRAL corollary; the correctness of 3-fix-1-alter; the
  consistency claim of §4.3; supplement Lemma 4) and of TINNiK (Propositions 5, 6; Appendix C; Theorem 4).
- **Proved cited results**: Allman et al. 2023 Theorem 2 and Lemma 3; Rhodes 2020 Theorem 2; Huber et al. 2025 Theorem 5.1,
  forward direction; Ané et al. 2024 exchangeability; Mitchell et al. 2019 Theorem 3.1 for this model.
- **Conditional** on one result of the literature: `External.AllmanEtAl2023.Corollary1` (TINNiK's Theorem 1: 4-blobs are
  CF-detectable for generic parameters), a hypothesis of `TINNiK.theorem4`, and on the form that ECToBlob's
  Proposition 5.1 adapts it to, `ECToBlob.AdaptedAllmanTheorem1`, a hypothesis of `ECToBlob.proposition5_1`. Everything else is unconditional, including ECToBlob's Theorem 8.2 and
  TOB-QMC's consistency claim, which take the papers' own assumptions. Section 2 gives what Lean lacks for the two.
- **Statements**: the corrections are listed in Section 4 and at the end of Section 6. One of them, E11, still awaits the agreement
  of the user who requested this formalization.
- `lake build` passes; the only `sorry`s are the statements of `Challenge.lean`, by design. There is no `axiom`, `native_decide`
  or `implemented_by`. `scripts/Audit.lean` checks every declaration of the libraries, including private and generated
  ones, against the standard axioms `propext`, `Classical.choice`, `Quot.sound`.
- `Challenge.lean` states the main results; `Solution.lean` proves them word for word; Comparator accepts the pair under
  Lean's kernel and NanoDa.
- No person has reviewed the proofs. Independent agents reviewed the statements and compared the proofs with the papers
  (`CREDITS.md`).

## 1. Summary

- **Errors.** ECToBlob's (3.3) overcounts (E2). The claims of TOB-QMC's supplement that its Lemma 7 and Theorem 1 hold at
  arbitrary level are false at level 2 (E25), its Lemma 2's converse is false (E23), and so is its claim that positive edge
  lengths exclude the centroid (E28). TINNiK's count of the quartets sharing three taxa is wrong (E29), and a maximum
  likelihood estimate need not exist on its open cut model (E31).
- **Gaps.** The proof of ECToBlob's Theorem 8.2 has the most serious ones: the quartet witnessing a false edge may have a
  trivial 4-blob, where the T1 null holds (E12); this needed a new 1,100-line argument, `ECToBlob.falseEdge_witness`, and
  changes no statement. Others: E3, E4, E6–E8, E13–E17 (ECToBlob); E18–E22 (TOB-QMC); E30, E32, E33 (TINNiK). All are repaired,
  and none changes a statement.
- **Missing hypotheses.** ECToBlob's Theorem 8.2 needs generic parameters for the literal general model (E10, agreed) and,
  for its Cauchy and CBC variants, positive alternatives (E11, not yet agreed). Section 4.
- **Redundant hypotheses.** Section 5. The most notable: the disjointness of `A₁, A₂` and of `B₁, B₂` in Theorem 4.1 of
  ECToBlob; all the refinement hypotheses in TOB-QMC's Lemma 4; `0 ≤ δ` in TINNiK's Theorem 4.
- **Use of cited results.** TINNiK's Theorem 2 is applied beyond its printed hypothesis (b) (E30), TOB-QMC cites the statement
  of TINNiK's Theorem 4 for what is a step of its proof (E21), and ECToBlob's Proposition 5.1 adapts a theorem with "checking
  the argument" (Section 2).

## 2. Results from prior work and how the papers use them

### Proved in `External/`

| Result | Where the papers use it | Source | Theorem in `External/` |
| --- | --- | --- | --- |
| Theorem 5.1, forward: a cut edge's split induces cut-edge splits on quartets | TOB-QMC Lemma 2 | Huber et al. 2025 | `External.HuberEtAl2025.theorem5_1_forward` |
| Taxa on one side of a cut edge are exchangeable for quartets with the other taxa on the other side | ECToBlob Prop. 5.1, TOB-QMC Lemma 3 | Ané et al. 2024 | `External.AneEtAl2024.exchangeability` |
| The B-quartet inference rule (TINNiK's Theorem 2) | TINNiK Theorem 4 | Allman et al. 2023 | `External.AllmanEtAl2023.theorem2`, `External.AllmanEtAl2023.closure_sound`, `External.AllmanEtAl2023.closure_complete` |
| Lemma 3 of the source | TINNiK Theorem 4, through the rule | Allman et al. 2023 | `External.AllmanEtAl2023.lemma3` |
| The quartet distance is a tree metric with the same topology (TINNiK's Theorem 3) | TINNiK Theorem 4 | Rhodes 2020 | `External.Rhodes2020.theorem2` |
| Limit law of the likelihood ratio at a cut model | TINNiK Prop. 5 | Mitchell et al. 2019 | `External.MitchellAllmanRhodes2019.cutModel_theorem31`, for this model |

The row on Mitchell et al. proves the source's conclusion for the model used, by the central limit theorem, not from van der Vaart's Theorem 16.7
(Section 7). The Lean form of exchangeability is on arbitrary networks with inheritance correlation.

### Assumed (a conditional formalization)

| Result | Where the papers use it | Source | Hypothesis in the formalization | What Lean lacks | Plan |
| --- | --- | --- | --- | --- | --- |
| For a binary network, parameters at which some 4-taxon induced network fails CF-detectability form a null set | TINNiK Theorem 4 | Allman et al. 2023, Theorem 1 and Corollary 1 (TINNiK's Theorem 1) | `External.AllmanEtAl2023.Corollary1` | The analytic parametrization of quartet CFs on networks; zero sets of nonzero analytic functions on products of intervals as null sets; the reduction of general networks to a list of 4-taxon cases, with a nonzero witness in each | Large but feasible: Section 11. The user decides |
| For ECToBlob's restricted parameters, an induced network with neither a cut edge nor a trivial 4-blob has three distinct probabilities generically | ECToBlob Prop. 5.1 | Adaptation of the previous row ("checking the argument") | `ECToBlob.AdaptedAllmanTheorem1` (`generic_distinct`) | As above, with parameters on nodes of degree 2 or 3 of non-binary networks | As above |

Both statements are about one network and name their parameter set, so neither can hold vacuously: `Corollary1` says that a
specific set is contained in a null set. `ECToBlob.proposition5_1` is the paper's reduction, and is conditional on this hypothesis.
Assumption 1 of ECToBlob is the paper's own hypothesis of Theorem 8.2, not a cited result, and appears as `ECToBlob.Assumption1Forward`
and `ECToBlob.Assumption1Converse`.

### Standard facts used without citation

| Fact | Where | In the formalization |
| --- | --- | --- |
| Central limit theorem, in dimension 2 by Cramér–Wold | TINNiK Prop. 5, star and T1 limits | Mathlib's `tendstoInDistribution_inv_sqrt_mul_sum_sub`; `Phylogenetics.Trinomial.tendstoInDistribution_normalizedSums` |
| Wilks-type limits: χ²₂ for the star test, the T1 mixture | ECToBlob §6, §8; TINNiK §"hypothesis tests" | Proved directly for the trinomial: `Phylogenetics.Trinomial.tendsto_star_lrt`, `Phylogenetics.Trinomial.tendsto_t1` |
| Strong law of large numbers | TOB-QMC Theorem 1 | Mathlib's `strong_law_ae_real` |
| Weak law for empirical frequencies | ECToBlob Cor. 3.6, Theorem 8.2 | `Phylogenetics.QuartetTests.tendsto_iidProb_freq` |
| Absorption of Kingman's coalescent; Tavaré's formula | The NMSC's definition | `Basic/Phylogenetics/Coalescent/`, adapted from `lean4-phylogenetics` |
| Compatible splits have a common tree | TOB-QMC Lemma 3 ("compatibility supertree"), ECToBlob §3 | `Phylogenetics.splice_isUnrootedTree` |
| Neighbor joining and other exact tree builders recover a tree from its metric | TINNiK Theorem 4 | The theorem is stated for any `Phylogenetics.IsExactBuilder`; `External.Rhodes2020.exists_isExactBuilder` shows one exists. Neighbor joining itself is not formalized (Section 9) |

### Does each paper use each cited result correctly?

| Cited result | Where | Verdict |
| --- | --- | --- |
| Huber et al. Theorem 5.1 | TOB-QMC Lemma 2 | Correct. The source treats binary semi-directed networks; the forward direction needs neither |
| Ané et al. exchangeability | TOB-QMC Lemma 3, ECToBlob §3, §5 | Correct |
| Allman et al. Theorem 1 | TINNiK Theorem 4 | Correct, and its use against the centroid is unnecessary (Section 11) |
| Allman et al. Theorem 2 | TINNiK Theorem 4 | Applied loosely: E30 |
| Rhodes 2020 Theorem 2 | TINNiK Theorem 4 | Correct. Pendant edges have weight at least 2 as well |
| Mitchell et al. Theorem 3.1 | TINNiK Prop. 5 | Correct for fixed φ; the "not too close to the boundary" remark is not needed (E32) |
| TINNiK Theorem 4 | TOB-QMC §4.3 | Applied loosely: E21 |
| Allman et al. Theorem 1, adapted | ECToBlob Prop. 5.1 | Plausible but not checked here. The adaptation is stated by "checking the argument", and is assumed |

## 3. Errors and gaps in the papers

### ECToBlob

**E1. Remark 3.2.** "Any multifurcation in a potential maximizer can be arbitrarily resolved to increase the MQS score" is
loose when some probabilities vanish: an arbitrary resolution need not increase the score. Some resolution with positive
probability does, since the three probabilities on a quartet sum to 1. `ECToBlob.remark3_2` proves the remark.

**E2. Equation (3.3) is false as printed.** Summing over representative tuples counts a quartet once for each choice of
representatives of the other blocks, so a quartet in distinct blocks is overcounted by the product of the sizes of the
unused blocks. With blocks of sizes `(2,1,1,1,1)` and all cross-block CFs `1/3`, the left side is `3` and the right side `10/3`
(`scripts/SourceChecks.lean`); a multifurcating species tree with one positive-length cherry realizes these CFs. This refutes
the identity, not Theorem 3.1. Repair, along the paper's route: weight each local term by the product of its four block sizes,
divide by `∏ᵢ |Xᵢ|`, and use the weighted local objective for the splicing. Lean: `ECToBlob.equation3_3`, `ECToBlob.localWeight`,
`ECToBlob.theorem3_1`. The identity also needs the `Xᵢ` to cover `X`, as the paper's do.

**E3. Corollary 3.6, proof.** "The probability that `f̂` and `f` have different sets of optima → 0" is false when `f` has
ties: `f(a)=f(b)=0`, `fₙ(a)=1/(n+1)`, `fₙ(b)=0` converges uniformly with different argmax sets for every `n`, and ties do
occur here. The result holds: the empirical optima lie among the expected ones, by the gap to non-maximizers, which is what
the corollary says. Lean: `ECToBlob.corollary3_6`.

**E4. Theorem 4.1, proof.** "The minimality of `|E|` implies that the funnel of `a₁` can only attach to `G̃₃` on the
`ã₂`-side" is elliptical: it needs the comparability of the sets `E(z, …)` of cut edges for different replacements. Going from
one funnel to all of them at once needs that funnels on opposite sides of an edge share no node, which is true and unstated. The "two
3-blobs" and "chain of 2-blobs" remarks are not used. The formal proof supplies comparability (`ECToBlob.quartetCutArc_comparable`), and its
per-taxon domination takes care of the funnels. The result holds.

**E5. Proposition 5.1.** Its proof rests on an adaptation of Allman et al.'s Theorem 1 stated by "checking the argument". This is not
an error, but the formalization cannot confirm it, and takes the generic clause as a hypothesis under the proposition's own degree condition (Section 2). The
paper's two other facts are proved for every network: `Phylogenetics.NMSC.cut_alternatives`, `Phylogenetics.NMSC.trivial_uniform`.

**E6. Lemma 6.1, proof.** `Bon(P) = km` omits the clipping at one in the paper's definition: `{3/4, 3/4}` gives `Bon = 1`, not
`3/2`. The inequality needed still holds. Lean: `Phylogenetics.QuartetTests.bonP_le_mul` (name in the library: `bonP_le_mul`).

**E7. §6 and Lemma 6.1: Cauchy endpoints.** The Cauchy combination is undefined at `p = 0`, an allowed input by `P ⊂ [0,1)`, and CBC
can feed `Bon = 1` into it. Lean's total tangent is not a reading of the undefined expression, so the Lean definitions
extend `f` continuously at the endpoints. Simultaneous inputs `0` and `1` have no continuous extension, but this case does not
occur on the lemma's domain: `Bon = 1` forces all inputs positive. Lean: `Phylogenetics.cauchyP`, `ECToBlob.cauchyP_pair_le_max`.

**E8. Lemma 6.1, part 1: the bound.** The printed `B_{Cauchy,k}(η, D)` has all the claimed properties on `0 < η ≤ D < 1`, the only region `(min P, max P)` reaches when `min P > 0`, which is where the paper uses it.
The lemma's statement also covers other points, and there it fails: it is claimed non-decreasing in `k`, and is not when `η > D` (at `η = 0.9`, `D = 0.1` it is `0.9` at `k = 1` and `0.5` at `k = 2`), and it fails `∼ kη` at `D = 0`,
where `f(0) = +∞` makes it `0` for `k ≥ 2`. No bound agreeing with the printed one for `η ≤ D` can have both properties at `D = 0`, as `ECToBlob/Section6.lean` shows. The lemma holds, by another bound: `ECToBlob.cauchyBound` uses
the anchor `max(D, η, 1/2)`, and equals the printed bound for `η ≤ D`, `D ≥ 1/2` (Section 7). The theorem's use is unaffected.

**E9. Algorithm 7.1, Step 10.** The late rule needs a convention when no iteration is rejected. Lean chooses the first iteration, which agrees
with the rule's intent (`Phylogenetics.selectedIteration`).

**E10. Theorem 8.2: missing genericity.** The theorem quantifies over any model meeting Assumption 1, whose converse clauses
hold only generically, while the proof invokes "our assumption of generic numerical parameters". For the literal general model
the statement is false: a one-parameter family of laws on a rooted 4-cycle network (Section 4) coincides at one parameter with the law of a
resolved tree, and no sequence of tests can converge to both. This is not a counterexample under the NMSC. Lean quantifies over
parameters meeting both clauses: `ECToBlob.theorem8_2`, and `ECToBlob.theorem8_2_generic` for the generic form. Corrected as the user
agreed, 2026-10-27.

**E11. Theorem 8.2: boundary laws.** For the Cauchy and CBC variants the statement fails when both alternatives of a quartet with a cut-edge
split have probability zero. Assumption 1 allows this, since (5.2) is a condition on `p₁ > p₂ = p₃` with no positivity, though the source's T1 null is `p₁ ≥ p₂ = p₃ > 0`. Counts on such a quartet are `(n,0,0)`
almost surely, so its T1 statistic is `0` and its p-value is exactly `1` for every `n` (`Phylogenetics.QuartetTests.t1PValue_degenerate`), and `Cauchy` of any multiset of positive p-values containing `1` is `1`. Lemma 6.1 assumes `P ⊂ [0,1)`, and the proof's "individual p-values `≤ 1-δ`"
excludes this case without saying so.

Counterexample: the rooted 5-sunlet with arcs `r→v_b, r→v_c, v_b→v_a, v_c→v_d, v_a→h, v_d→h, h→e, v_a→a, v_b→b, v_c→c, v_d→d`, whose tree of blobs is the five-leaf star, under the Displayed Tree model with weights `γ` on `((a,e),b,(c,d))` and `1-γ` on `((a,b),c,(d,e))`. On `abcd`, the
network has the cut split `ab|cd` and the CF is `(1,0,0)`; the other four quartets have CFs `(γ, 1-γ, 0)` up to order, and no cut split or trivial 4-blob. Both directions of Assumption 1 hold, for all `γ ∈ (0,1)`. Take `T₀` with cherries `ab`, `cd`, a resolution of the star. The star test keeps `T₀`, since these CFs are not uniform; `T₀` displays `ab|cd`, so its overall
Cauchy p-value is `1 ≥ α_n`; so for all `α, β` both selection rules return `T₀`, which is not the star. Bon and BBC are not affected, since clipping loses the `1`. A mixture with weights `δ, 1-δ` of a point mass at `T₀` and the uniform law on all 15 binary trees shows that `-log β_n = o(n)` for any
sequence working on trees, so the failure does not depend on the choice of sequences. An independent reader recomputed the law, the network's predicates and Assumption 1, and simulated the Lean definitions on both examples at `n = 500, 5000, 50000`: Cauchy and CBC returned `T₀` in every replicate, and Bon and BBC returned the star at `n ≥ 5000`.

The NMSC has positive CFs (`Phylogenetics.nmscCF_pos`), so the paper's main model loses nothing. Lean adds the hypothesis `hpos` to `ECToBlob.theorem8_2`, for these two variants only and on T1-strict quartets only. MSCquartets-style software differs at this point: `tan((0.5-1)π)` is finite in floating point. **The user has not yet agreed to this correction.**

**E12. Theorem 8.2, proof: the witness may be a trivial 4-blob.** "By Corollaries 4.2 and 4.3, `S^a(e)` is empty exactly when `e` is a cut-edge" fails for non-binary
networks: the quartet that those corollaries find may have a trivial 4-blob, on which the T1 null hypothesis holds (`CF = (1/3,1/3,1/3)` is on every T1 null).
So those corollaries do not show that a false edge has a T1-rejecting quartet. The statement holds. Repair: an edge surviving Step 3 has a quartet with no trivial 4-blob in its
multipartition, and from it `ECToBlob.falseEdge_witness` produces a quartet in the multipartition of `T₀` with neither a cut-edge split on the wanted bipartition nor a
trivial 4-blob, for all three quartet types at every stage. Hence also Corollary 4.2 is not used (Section 7).

**E13. Theorem 8.2, proof: T1 at the centroid.** "Arguing as for the star test" is not enough: T1 p-values are not asymptotically uniform at the centroid (the paper's own
line 1017 notes this), so Lemma 8.1 does not apply there. Repaired by tightness (`Phylogenetics.QuartetTests.t1PValue_centroid_tight`) and a union bound.

**E14. Theorem 8.2, proof: the threshold.** `B(η_n, 1-δ) ∼ β_n` does not give `< β_n`. Repaired with a constant: `η_n = c₀ · level` (`ECToBlob.exists_combineBounds`). Only
`b_n = o(n)` is used, not `b_n ∼ log n`, and the asymptotic of `α_n` is unused. "An individual p-value is below `η_n` exactly when the test statistic is above `b_n`" holds for the star test, whose test law is fixed, and "the T1 tests are handled similarly" does not carry it over:
the T1 law depends on an estimated `μ`. Lean bounds the T1 p-value by the `χ²₂` tail at the statistic (`Phylogenetics.QuartetTests.t1Tail_le_chiSqTwoTail`).

**E15. Theorem 8.2, proof: bounds on the combined p-values.** "In `(α_n, 1-δ)`" is false on the upper side for Bon, BBC and CBC, even with positive alternatives: `Bon({3/4, 3/4}) = 1`, and then `BBC` and `CBC` are `1`. Individual p-values `≤ 1-δ` is false when alternatives vanish (E11). Only the
lower bounds are needed, and the upper individual bounds only for Cauchy and CBC. Lean uses `ECToBlob.minP_le_combineP` and `ECToBlob.combineP_le_two_mul` for Bon and BBC, and Lemma 6.1 for Cauchy and CBC.

**E16. Theorem 8.2, proof: intermediate trees.** The bounds `ε/(2s)` are per edge, but for type `mul` an edge's quartets depend on the random current tree `T_k`, so the union must
run over all states the algorithm could visit. Likewise "our prior choice of `M`" does not cover the sets that the overall `p_k` uses. The formal proof uses one event per quartet (`ECToBlob.Deterministic.Run`), and then a deterministic argument.

**E17. Theorem 8.2, proof: Step 3.** "`T_{k₁}` is obtained from `T₀` by contracting precisely those edges that resolve multifurcations" is false as written: on a 4-cycle, `ab|cd` resolves a multifurcation of the tree of blobs and survives Step 3, since its quartet is not uniform. The formal
proof shows what is needed: `T_B` is kept and each kept edge has a non-uniform quartet (`ECToBlob.Deterministic.Run.treeOfBlobs_subset_afterStar`, `ECToBlob.Deterministic.Run.exists_not_uniform`).

### TOB-QMC, main text (v5)

**E18. Lemma 3, proof.** The result holds; the steps below are repaired in `TOBQMC.lemma3_of_properties`, `TOBQMC.lemma3`, and in the proof of exchangeability.

- Lines 449–451: "uniquely maximized by `T_N`" is wrong: every refinement of `T_N` ties (`Phylogenetics.quartetPart_of_displays`); (2) only compares with non-refinements. The strictness of (2) needs that a non-refinement differs from `T_N` on some T-quartet, so that displayed quartets determine splits (`Phylogenetics.subset_of_forall_displays`).
- Lines 467–471: "only after the four sampled lineages enter this blob can they coalesce" is false for the block containing the root: the three other lineages can coalesce inside the blob and then leave upward. The conclusion holds for a different reason: a pair that coalesces first decides the quartet whichever taxon is above, and if all three leave uncoalesced the three quartet trees are equally likely. `Phylogenetics.NMSC.exchangeability` treats both cases.
- Lines 472–486: framed as a contradiction, but it is a direct transformation of any maximizer. The reasons (i), (ii) justify `QS^v(new) = QS^v - QS^{v(b)} + QS^{v(a)}`, not the printed equality with `QS^v(T*)`; quartets without `b`
  are unaffected, and those with `b` read as the same with `a`, because `b` is now sister to `a`. These last facts are unstated, and the case `QS^{v(a)} > QS^{v(b)}` cannot occur at a maximizer.
- Line 485, "Repeating": needs three unstated facts: detaching `b` leaves the partial scores of the block's other taxa unchanged, so `a` stays best; the block side grows step by step; and earlier block sides
  survive later operations (`TOBQMC.vertexTaxonPart_detachReattach_of_ne`, `Phylogenetics.insert_mem_detachReattach`, `Phylogenetics.mem_detachReattach_of_not_mem`). Also, `a` must be chosen afresh for each block, on the current tree.
- Lines 489–492: needs an unresolved quartet to be resolvable by a compatible refinement (`Phylogenetics.exists_refinement_displays`).
- Lines 492–495: property (2) is what forces every remaining side to be a union of blocks (`TOBQMC.displays_filter_isBlockUnion`), which is not noted.
- Lines 497–498: compatibility of the local trees at different vertices is asserted (`Phylogenetics.IsVertexPartition.compatible_of_ne`), and that the result is binary needs a proof (`Phylogenetics.isBinaryTree_of_forall_displays`).

**E19. Lemma 4, proof of ⇒ (lines 551–556).** It does not treat two or more taxa below `v_h`. They lie in one block, a fact stated only in the proof of Corollary 1, so distinct blocks exclude this case.
Lean: `TOBQMC.Level1.blockWalk_of_below_reticulation`. The result holds.

**E20. Corollary 1, proof (lines 563, 568).** "Each side contains at least two blocks (otherwise `B_N` is not binary)" gives the wrong reason: a side with one block is a cut side, so the edge would be in the tree of blobs. Binary `B` is not needed. "By the setting" also needs `e ∉ T_N`, for the same reason (`TOBQMC.Level1.exists_not_isTreelike`). The result holds.

**E21. Consistency (lines 597–600).** The paper cites TINNiK's Theorem 4 as stating that the tests are correct on all four-taxon subsets. Its statement is about the algorithm's output, and this fact is a step of its proof,
for generic parameters at `ρ = 0`. It also fails under v5's assumptions: at parameters where a treelike subset has the centroid CF (E28), the test answers wrongly there. The claim holds anyway, under v5's own assumptions:
the argument needs correct answers on the non-treelike subsets (6a) and on the subsets the tree of blobs resolves (nonanomaly and exchangeability), and a treelike subset around a false positive is harmless. The step from
Theorem 1's almost-sure "for all large `k`" to probability tending to one is unstated. Lean: `TOBQMC.consistency`, `TINNiK.tendsto_testedB`, `TINNiK.tendsto_not_testedB`, `TOBQMC.tendsto_optimaRefine`.

**E22. Margin (lines 503–505, and supplement Lemma 4, Eq. (1)).** "`π` is the minimum absolute difference between the qCFs of T-quartets" can be zero: the species tree CF `(1/2,1/4,1/4)` has equal alternatives. Then the condition
"absolute error `< 0`" is impossible. Repair: use the positive differences between the displayed quartet and each alternative, minimized over T-quartets, with the same radius. Lean: `TOBQMC.Margin`, `TOBQMC.exists_margin`.

### TOB-QMC, supplement

**E23. Lemma 2: false converse.** A treelike induced quartet can restrict a star on the full tree of blobs: the network with arcs `s→e, s→r, r→u, u→v, v→h, r→w, w→h, u→a, v→b, w→c, h→d` has
a five-leaf star as tree of blobs, while its restriction to `{e,a,b,c}` displays `ab|ce` (`scripts/SunletCheck.lean`). The proof of the converse in fact reproves the contrapositive of the forward direction. Main v5 keeps only the forward direction, as does Lean (`TOBQMC.lemma2`). Agreed with the user.

**E24. Lemma 4, proof.** Strict coordinate errors are weakened to non-strict bounds, after which strict positivity is claimed at the boundary radius; keeping them strict repairs this at the same radius. Equations (6)–(7) must cancel agreeing quartet
terms before identifying the sums. The final display has `2|Y_tree|δ` for `2|Y_star|δ`. `B*` is "some tree that maximizes `QS_E`", and then `QS_E^star(B*) ≥ QS_E^star(T)` is taken from Lemma 5, which gives this for the constructed tree; it holds for any maximizer, since the constructed tree attains both maxima, but that needs saying. Lean: `TOBQMC.supplementLemma4`.

**E25. Lemma 7 and Theorem 1 at arbitrary level: false.** The supplement's claims extend to networks of arbitrary level that a disjoint cover finds a non-treelike quartet around every false edge. On the binary level-2 network with arcs `(0,2),(1,3),(1,4),(3,6),(2,8),(6,9),(6,10),(9,12),(2,13),(13,7),(3,14),(14,5),(13,14),(0,15),(15,1),(9,16),(16,11),(15,16)`,
leaves `4,5,7,8,10,11,12`, the 3-fix-1-alter cover with blocks `{10},{7},{4,5,8},{11,12}` and anchors `10,7,8,12` has every quartet treelike, though the edge is false. Main v5 restricts Theorem 2 to level 1, so this is consistent with it. This concerns covers, not an oracle on all quartets around an edge (Section 10).

**E26. Lemma 8: missing hypothesis.** A trivial blob need not contain a reticulation: the singleton blob at the parent of `a, b` in `((a,b),(c,d))`. The intended statement requires a nontrivial blob, as agreed with the user. Only used through level-1 arguments in Lean: `TOBQMC.Level1.exists_reticulation_or_forall_isBridge`.

**E27. §1.2.** The initial `α = ρ/(1-ρ)` conflicts with the later `ρ = 1/(α+1)` and the stated endpoints; the consistent form is `α = (1-ρ)/ρ`. Lean: `Phylogenetics.concentration_relation`, `Phylogenetics.urnStep_eq_concentration`.

**E28. "We can safely assume" no centroid (supplement line 300).** Positive tree edge lengths do not exclude `P = (1/3,1/3,1/3)`: the `3₂`-cycle at `t = t₁ = t₂ = 0.02`, `γ = 1/2`, `t₃ ≈ 0.12830`, `ρ = 0` has the centroid CF, as TINNiK itself says in its discussion before Theorem 4. It affects only the statement of E21's test step.

### TINNiK

**E29. B-inference, Step 3(a)(i).** The number of quartets sharing exactly three taxa with a fixed one is `4(N-4)`, not `4(N-1)`. The order is unchanged. Lean: `TINNiK.card_sharing_three`.

**E30. Theorem 2 of the source, as applied.** Hypothesis (b) says that a `t` is a B-quartet "on the induced 4-taxon network", but the Inference Rule also has to fire from a `t` inferred as a B-quartet of the full network, which may be treelike when induced.
This needs a stronger rule than the printed one. It holds by the same proof, because the separating cut edge also resolves `t` on `N`. Lean: `External.AllmanEtAl2023.rule_core`, from which `External.AllmanEtAl2023.theorem2` and `External.AllmanEtAl2023.closure_sound` follow.

**E31. Appendix C.1.** A maximum need not exist on the open cut model: counts `(1,0,0)` have supremum not attained (`scripts/BoundaryCheck.lean`). Lean estimates on the closed simplex, with strictly positive generating parameters, as agreed with the user. `TINNiK.cutLineMLE_maximizes`.

**E32. Proposition 5, proof.** "Assuming `θ₀` is not too close to the boundary … dependent on the sample size" is informal and not needed for fixed `φ₀`. The result holds as stated.

**E33. Theorem 4, proof.** "The test distribution converges to `χ²₁`" gives no comparison at levels `α_m → 0`, nor at cutoffs `m d/2` growing with `m`. The same sentence says that `μ₀ → ∞`, where anomalous strictly cut CFs have `μ₀ → -∞`. "Without loss of generality the MLE is on the vertical line" hides that
the fitted line is random and `d` depends on it. The result holds. Repairs: under the alternative, the test distribution is pointwise at most that of `Z²`, and the least limit over the three lines gives one `d` (`Phylogenetics.QuartetTests.cutTest_alternative`, `Phylogenetics.QuartetTests.cutTail_le_chiSqOneTail`); under the null, a uniform lower bound on the test law replaces the limit (`Phylogenetics.QuartetTests.cutTest_null`).

### Typos

**E34.**

- ECToBlob, proof of Corollary 4.3: `∪_{j′≠i} B_{j′}` should be `∪_{j′≠j} B_{j′}`.
- ECToBlob, §7: "Theorem 3.6" for Corollary 3.6; §10: "Theorem 4.2 and Theorem 4.3" for Corollaries.
- TOB-QMC, line 449: `QS^tree(T|N)` for `QS^tree(T_N)`. Lines 455, 459: `Pᵢ ≠ Pⱼ ≠ Pₛ ≠ Pₜ` must mean pairwise distinct. Line 462: `∪∪ Y` gives taxa, not 4-subsets: should be the union of `f_cover(P)`.
- TOB-QMC, line 535: `Z|Y` for `Z|W`.
- TINNiK, Appendix C: `Λ̃_n` for Proposition 5's `Λ_n`.
- Allman et al. 2023, proof of Lemma 3: "`N \ {e0}`" for `N′`, "`Kbc`" for `K_cd` (possibly an artifact of the text extraction).
- Mitchell et al. 2019: "Proposition 16.7" for van der Vaart's Theorem 16.7, in one place.

## 4. Missing hypotheses

| Where | Missing hypothesis | Counterexample without it | In the formalization |
| --- | --- | --- | --- |
| ECToBlob Theorem 8.2 (E10), agreed | Parameters outside the exceptional sets of Assumption 1's converse | A rooted 4-cycle network with arcs `s→r, s→d, r→u, r→v, u→h, v→h, u→a, v→b, h→c`, whose tree of blobs is a star, with the model `(1/2, 1/4+h(t), 1/4-h(t))`, `h(t) = (t-1)/(8(1+(t-1)²))`, for one edge length `t`: at `t = 1` its law equals that of a resolved tree `ab\|cd`, which has the same `T₀`, so no test sequence can be consistent for both (`scripts/IndistinguishabilityCheck.lean` for the algebra) | `ECToBlob.Assumption1Forward`, `ECToBlob.Assumption1Converse` hold at the given law; `ECToBlob.theorem8_2_generic` |
| ECToBlob Theorem 8.2 (E11), **not yet agreed** | For Cauchy and CBC only: positive alternatives on T1-strict quartets | The 5-sunlet of E11 | `hpos` in `ECToBlob.theorem8_2` |
| ECToBlob (3.3) (E2) | Block-size weights; the blocks cover `X` (they do in the paper) | E2; for the cover, `X = {a,b,c,d}`, `P = {{a}}`, `s = ab\|cd`, `w` the indicator of `s` | `ECToBlob.equation3_3` |
| TOB-QMC supplement Lemma 8 (E26), agreed | Nontrivial blob | E26 | Not stated as such: used through `TOBQMC.Level1.exists_reticulation_or_forall_isBridge` |

## 5. Redundant hypotheses

The Lean statements leave these out, except in `Challenge.lean`, which keeps the papers' hypotheses.

| Result | Hypothesis that is not needed | Why | Lean |
| --- | --- | --- | --- |
| ECToBlob Theorem 4.1 | `A₁ ∩ A₂ = ∅`, `B₁ ∩ B₂ = ∅` | Only `A ∩ B = ∅` and the cover are used | `ECToBlob.theorem4_1` |
| ECToBlob Proposition 5.1, forward clauses | Degree 2 or 3 in blobs; binary | Exchangeability holds on every network | `ECToBlob.proposition5_1`, where the condition enters only through the assumed clause |
| ECToBlob (3.3) | Nonempty blocks | | `ECToBlob.equation3_3` |
| TOB-QMC Lemma 4 | That `B` is a tree, refines `T_N`, that `A` is an internal side and is not in `T_N` | Only `RefinesBlob` is used | `TOBQMC.lemma4` |
| TOB-QMC Corollary 1, Theorem 2 | `B` binary | | `TOBQMC.corollary1`, `TOBQMC.theorem2` |
| TINNiK Theorem 4 | `0 ≤ δ` | The filter uses only `δ < 2`. Also, "binary" is needed only for the hypothesis `Corollary1` to hold | `TINNiK.theorem4_of_rejects`, `TINNiK.theorem4` |
| Allman et al. Theorem 2 | Binary network | | `External.AllmanEtAl2023.theorem2` |
| Huber et al. Theorem 5.1, forward | Binary | | `External.HuberEtAl2025.theorem5_1_forward` |

## 6. How the formalization reads the papers

- **Networks** are directed multigraphs with named arcs (`Phylogenetics.RootedNetwork`), rooted, with parallel arcs allowed. The papers' semi-directed networks are handled through the rooted networks they come from; TOB-QMC's `N⁻` is `N` with a root.
- **Unrooted trees** are families of sides of splits (`Phylogenetics.IsUnrootedTree`: `unroot` of a hierarchy). The tree of blobs `T_B(N)` is the family of nonempty proper sides of cut edges (`Phylogenetics.treeOfBlobs`).
  Bridges to the graphs: `Phylogenetics.RootedNetwork.blobTree` is the graph with blobs contracted; `Phylogenetics.RootedNetwork.mem_treeOfBlobs_iff_blobTree` says the two agree on splits, and `Phylogenetics.RootedNetwork.blobTree_isTree` that it is a tree. The root of `blobTree` is not deleted, so a fully reduced `T_rd` does not exist as one graph; the split family it has is settled.
- **Induced networks**: `HasCutSplitOn Y A` is stated through domination in the subgraph of ancestors of `Y`. `Phylogenetics.RootedNetwork.hasCutSplitOn_iff_inducedNetwork_hasCutSplit` proves it equal to the cut splits of the graph `inducedNetwork` (LSA restriction, then suppression).
- **Quartet trees** are unordered pairs of cherries; `Phylogenetics.Displays`.
- **The NMSC** on arbitrary networks is an order-free sum over histories (`Phylogenetics.geneTreeDist`), the product over vertices and arcs of the joint law of the forests at the bottom and top of each arc. One lineage per taxon. `ρ` is the inheritance correlation of TOB-QMC's supplement, in closed form as an exchangeable Pólya law (`Phylogenetics.allocationWeight`, proved equal to the urn in `Phylogenetics.allocationWeight_eq_urn`). `Phylogenetics.sum_geneTreeDist` and `Phylogenetics.geneTreeDist_support` validate it: a law on binary rooted trees.
- **Sampling**: `Phylogenetics.iidProb dist n Ev` is the finite sum over samples, proved equal to the product measure (`Phylogenetics.iidProb_eq_pi`). TOB-QMC's almost-sure statement uses any probability space (`TOBQMC.IsGeneTreeSample`).
- **Test statistics** follow the implementation (MSCquartets, Mitchell et al.). The T1 p-value uses the plug-in `min(1, φ̂)` at all counts; small-count procedures of software are not modelled. Star: likelihood ratio by default, Pearson as `StarTest.pearson`.
- **Gene trees in ECToBlob's Theorem 8.2** are binary (`ECToBlob.BinaryGeneTree`), which is what the proof and the NMSC give; ECToBlob's unrooted topological gene trees need not be. The theorem still covers all three models of §5.
- **TOB-QMC's disjoint cover around an edge of a non-binary tree** (Definition 2) is read with the multipartition at the edge (`Phylogenetics.multipartitionQuartets`), since Theorem 2 is stated there.
- **`CutExchangeable`** is the form in which ECToBlob's Theorem 3.1 uses its condition 2; `ECToBlob.pendantChainInvariant_cutExchangeable` derives it from the literal form.
- **Parameters**: `MetricData` has lengths on all arcs and hybridization parameters; `IsMetric` requires positivity on tree edges, and `γ` strictly between 0 and 1 where a reticulation has two parents.
- **Assumption 6a** of TOB-QMC is the hypothesis `hBlob` of `TOBQMC.consistency`.
- **TINNiK Theorem 4**: `TINNiK.theorem4` uses the paper's levels (`TINNiK.exists_levels`), which depend on unknown limits. `TINNiK.theorem4_explicit` also proves it for one sequence `α_m = P(χ²₁ > log m)`, independent of the network and parameters, as ECToBlob's Remark 8.3 suggests.
- **Lemma 8.1** of ECToBlob is proved for functions of iid finite samples, with `δ` chosen first. This is the form its use needs, and is stronger in the order of quantifiers.

Corrections of statements, listed here for reference: E2 (3.3); E10 and E11, Theorem 8.2; E23, E26, supplement results; E31, TINNiK's MLE.

## 7. Departures from the papers' proofs

| Result | The paper's argument | The formalization's | Why it is necessary | E-item |
| --- | --- | --- | --- | --- |
| ECToBlob Theorem 3.1 | Local objective `f̃_m`; (3.3) | Weighted by the block sizes. The paper's side claims on the form of all maximizers (lines 497–500, 504–507) are not formalized: the statement doesn't ask for them | Gap: (3.3) is false | E2 |
| ECToBlob Corollary 3.6 | Equal sets of optima | Containment, by the gap to non-maximizers | Gap | E3 |
| ECToBlob Lemma 6.1, part 1 | Cauchy bound anchored at `D` | Anchored at `max(D, η, 1/2)`, zero for `η ≤ 0` | Gap: the statement includes `D = 0` and `η > D` | E8 |
| ECToBlob Proposition 5.1 | Adapts Allman et al.'s Theorem 1 | The generic clause is a named hypothesis; the other two facts are proved | Lean lacks the analytic parametrization | E5 |
| ECToBlob Theorem 8.2 | Per-edge bounds; witness from Corollaries 4.2, 4.3; Lemma 8.1 per edge; `B ∼ β_n`; T1 threshold "exactly when"; Step 3 "precisely"; bounds `(α_n, 1-δ)` | Per-quartet events; `falseEdge_witness`, without Corollary 4.2; Lemma 8.1 once, jointly; a constant `c₀`; tightness at the centroid; the `χ²₂` bound for T1; a weaker Step 3 claim; only the lower bounds, and degenerate nulls separately | Gaps. Each of these steps fails or does not cover the case | E11–E17 |
| TOB-QMC Lemma 3 | Contradiction (lines 472–486); the tree on one taxon per block is binary, a refinement's gain "amplified after reattaching" (lines 489–492) | Direct transformation; the maximizer resolves every 4-taxon set in distinct blocks, on all of `X`. No restriction or reattachment | Gap, for the first; representation, for the second: trees are split families on `X`, and "binary after restriction" translates to the claim on 4-sets | E18 |
| TOB-QMC Lemma 4 | ⇐: exhibits the suppressed semi-directed `N\|Y` by wedge paths. ⇒, distinct blocks: one wedge path per pair, and the split read off their order | ⇐: no arc of the rooted induced subgraph separates two taxa from two others. ⇒: descends from the top of the blob to an arc with exactly two taxa below | Representation: treelikeness is a statement on the rooted induced subgraph, and wedge paths have no counterpart | E19 |
| TOB-QMC consistency | Cites correctness on all subsets | Only the subsets that matter | Gap: false at some parameters allowed by the printed assumptions | E21 |
| TOB-QMC supplement Lemma 4 | Margin from all three differences; strictness dropped, then claimed | Margin against the displayed quartet; strict bounds | Gap | E22, E24 |
| TINNiK Proposition 5 | From Mitchell et al. Theorem 3.1 (van der Vaart 16.7) | Direct CLT for this model; projections and minimum as the paper | Lean lacks differentiability in quadratic mean, local asymptotic normality, MLE consistency | — |
| TINNiK Proposition 6 | Polar coordinates, differentiating under the integral; a second rotated figure for `G₄, G₅` | Rotated Cartesian coordinates and Fubini; `R₄, R₅, R₆` by reflection | Not forced, and listed for completeness: this is how the integrals are computed, a matter of mechanics. Mathlib has polar coordinates. The six strips, the intermediate `d/dx Gᵢ`, `G = 2 Σ Gᵢ` and the formula are the paper's | — |
| TINNiK Theorem 4 | Centroid excluded by analyticity of the NMSC parametrization; the test law's limit `χ²₁` | From CF-detectability directly; a pointwise upper bound by `Z²` under the alternative, and a uniform lower bound under the null | Lean lacks the parametrization (a simpler argument exists: Section 11). The limit gives no comparison at moving levels: a gap | E33 |
| Allman et al. Lemma 3 (cited) | A cycle through `A, K_ab, e₀, K_cd` | Domination, comparing arcs by `order_of_isBelow_of_dominates` | Representation: components have no direct counterpart; result cited | — |
| Rhodes 2020 Theorem 2 (cited) | Sum over nodes on the `x`–`y` path | Double count over path edges | Representation: trees are split families | — |

`docs/route_differences.tsv` lists the changes in the cited results, each with its reason.

## 8. What each result depends on

<!-- Generated from scripts/Audit.lean -->

AUDIT_TABLE

The route check (`scripts/route_check.py check docs/paper_routes.tsv --accept docs/route_differences.tsv`) confirms that every proof uses the results that the paper's proof cites, except the differences recorded in `docs/route_differences.tsv`, each with its reason.

## 9. Not formalized

- Simulations, data analyses and running-time claims of all three papers (ECToBlob §9; TOB-QMC §2.3–2.4 and the `O(n²)` counts; TINNiK's complexity discussion, apart from E29).
- Neighbor joining: TINNiK's Theorem 4 is proved for any exact builder (`Phylogenetics.IsExactBuilder`), and such a builder exists; that NJ is one is standard (Atteson 1999), and is not formalized.
- The T3 test option of TOB-QMC (assumption 6b), and TOB-QMC's treelikeness oracle with the T3 test.
- That TREE-QMC's or ASTRAL's heuristic finds an optimum: `TOBQMC.astral_corollary` assumes the search space fills up with gene tree bipartitions as in the paper; `TOBQMC.consistency` takes any exact solver.
- ECToBlob's side claims in the proof of Theorem 3.1 on the form of all maximizers (lines 497–500, 504–507); Remark 8.3 as a theorem for NANUQ (its TINNiK part is `TINNiK.theorem4_explicit`); Remark 8.4 (coarsening); §10's discussions.
- TOB-QMC's Lemma 1 (cited, used in no proof) and its supplement's Lemma 8 (not needed for the level-1 arguments, which use `TOBQMC.Level1.exists_reticulation_or_forall_isBridge`).
- TOB-QMC's supplement Lemma 7 and Theorem 1 at arbitrary level, which are false (E25); at level 1 they are Lemma 4 and Theorem 2.
- Allman et al. 2023's Theorem 1 and Corollary 1 (assumed).

## 10. The papers in the literature

The search was made on 2026-10-31 in OpenAlex (works citing TINNiK, TOB-QMC, ECToBlob, Allman et al. 2023, Ané et al. 2024, Huber et al. 2025, "Beyond level-1", Rhodes et al. 2025, Xu and Ané 2023, NANUQ+, and the WABI paper of Dai and Molloy; keyword searches), Crossref (title searches; its `updates` filter for corrections), Europe PMC and PubMed, the bioRxiv API (versions, journal links), the arXiv API, GitHub's search API, the Archive of Formal Proofs, and web search. We kept every correction or counterexample found, and otherwise the works that state or claim a result about the tree of blobs, about which four-taxon information decides it, or about a method that starts from a tree of blobs with a stated guarantee. Empirical studies, reviews and work on other problems were screened by abstract and left out. Each statement below comes from the cited work's abstract or numbered statements, and we say where only the abstract was read. We could not read the full text of the Genome Research version of TOB-QMC (subscription), of BROOQS, DIMPLE and Justison et al. (bioRxiv answered HTTP 429), or of Rasschaert's preprint (SSRN answered HTTP 403). Citation indexes lag: OpenAlex lists one work citing ECToBlob and two citing TOB-QMC, so recent citing work may be missing. A preprint's results are reported as claimed.

### Before the paper

- Gusfield, Bansal, Bafna, Song, [J. Comput. Biol. 14 (2007)](https://doi.org/10.1089/cmb.2006.0137): a decomposition theorem for phylogenetic networks that exposes "a maximal embedded tree structure" (abstract only). TOB-QMC cites it for the tree of blobs.
- Solís-Lemus, Ané, [PLoS Genet. 12 (2016)](https://doi.org/10.1371/journal.pgen.1005896) (SNaQ, pseudolikelihood on quartets); Baños, [Bull. Math. Biol. 81 (2019)](https://doi.org/10.1007/s11538-018-0485-4) ([arXiv 2017-11-28](https://arxiv.org/abs/1711.10545)): "every cycle of size at least 4 and every hybrid node in a cycle of size at least 5" of a level-1 network are identifiable from gene tree quartets; Allman, Baños, Rhodes, [NANUQ, Algorithms Mol. Biol. 14 (2019)](https://doi.org/10.1186/s13015-019-0159-2) ([arXiv 2019-05-16](https://arxiv.org/abs/1905.07050)): level-1 inference from quartet hypothesis tests and a quartet intertaxon distance. TINNiK's introduction sets its algorithm against these level-1 methods.
- Allman, Baños, Mitchell, Rhodes, [J. Math. Biol. 86 (2023), 10](https://doi.org/10.1007/s00285-022-01838-9) ([arXiv 2022-05-06](https://arxiv.org/abs/2205.03466)): "most features of the unrooted tree of blobs" are determined by the distribution of gene quartet topologies, with no assumption on the level, through a B-quartet inference rule. It names the difficulty the three papers meet in different ways: a B-quartet of the network can have a cut-edge split on its induced 4-taxon network, "the main obstacle". Section 2 gives what is proved and what is assumed from it.
- Xu, Ané, [J. Math. Biol. 86 (2023), 12](https://doi.org/10.1007/s00285-022-01847-8) ([arXiv 2021-10-22](https://arxiv.org/abs/2110.11814)): the "distance split tree" built from average pairwise distances refines the tree of blobs, and at level 1 equals the tree of blobs refined to separate polytomies from blobs (Theorem 10). Its Conjecture 9 is taken up by a preprint under Since the paper. ECToBlob's §10 suggests applying its framework to distances.
- Solís-Lemus, Yang, Ané, [Syst. Biol. 65 (2016)](https://doi.org/10.1093/sysbio/syw030): species tree methods can be inconsistent under gene flow. Dinh, Baños, [Mol. Biol. Evol. 42 (2025), msaf049](https://doi.org/10.1093/molbev/msaf049) (published 2025-03-07): under the NMSC, "including nonanomalous scenarios", ASTRAL can produce a tree "that does not correspond to any topology displayed by the true underlying network". TOB-QMC and ECToBlob cite these as the reason a statement about quartet optima on networks is needed.
- Ané, Fogg, Allman, Baños, Rhodes, [J. Math. Biol. 88 (2024), 29](https://doi.org/10.1007/s00285-024-02050-7) ([bioRxiv 2023-08-21](https://doi.org/10.1101/2023.08.18.553582)): under common inheritance "4-taxon networks are never anomalous"; under independent and correlated inheritance simulations find "truly anomalous networks are rare" and many networks close to the anomaly zone. Source of the no-anomaly hypotheses of TOB-QMC and ECToBlob, and of the exchangeability of Section 2.
- Rhodes, Baños, Xu, Ané, [Adv. Appl. Math. 163 (2025), 102804](https://doi.org/10.1016/j.aam.2024.102804) ([arXiv 2024-02-18](https://arxiv.org/abs/2402.11693)): circular orders of outer-labeled planar blobs are identified from 4-taxon subnetworks. Its Corollary 6.6 gives the tree of blobs under the displayed tree model, common inheritance, and independent inheritance with no anomalous quartets. Its Lemma A.1 classifies 4-taxon networks, and ECToBlob says its Theorem 4.1 extends part of that lemma to more taxa.
- Huber, van Iersel, Jones, Moulton, Veenema-Nipius, [Bull. Math. Biol. 87 (2025), 136](https://doi.org/10.1007/s11538-025-01510-5) ([arXiv 2024-08-23](https://arxiv.org/abs/2408.12997)). Theorem 5.1, for binary semi-directed networks with "no restriction on the level": a nontrivial `A|B` is a cut-edge split exactly when `a₁a₂|b₁b₂` is a cut-edge split of the quarnet for all `a₁, a₂ ∈ A`, `b₁, b₂ ∈ B`. Corollary 5.6: the quarnets determine the blob tree. TOB-QMC's Lemma 2 is the forward direction, as TOB-QMC says.
- Frohn, Holtgrefe, van Iersel, Jones, Kelk, [J. Comput. Syst. Sci. 152 (2025), 103655](https://doi.org/10.1016/j.jcss.2025.103655) ([arXiv 2024-09-09](https://arxiv.org/abs/2409.06034)). Lemma 1 sharpens Huber et al.'s theorem by fixing `a₁` and `b₁`. Theorem 5 reconstructs the tree of blobs of a network of any level in `O(n³)` time from `O(n³)` quarnet-splits, and Proposition 6 gives a lower bound of `Ω(n log n + ℓn)` quarnet-splits at level `ℓ`. For binary networks ECToBlob's Corollary 4.2 is this Lemma 1, as ECToBlob says: it "follows from Lemma 1 of [17], which depends on results in [22]. Our proof is considerably briefer and we relax the binary condition". ECToBlob's Theorem 4.1 goes further in two ways: the network need not be binary, and the partitions `A₁, A₂` and `B₁, B₂` are arbitrary.

Huber et al. and Frohn et al. work from exact quarnet information, with no statistical model. Both appeared after the TINNiK preprint and do not build on its algorithm.

What the papers add. TINNiK ([bioRxiv 2024-04-24](https://doi.org/10.1101/2024.04.20.590418)) turns the sketch of Allman et al. 2023 into an algorithm with a consistency theorem (Theorem 4) and writes "We know of no other proposed algorithm for tree of blobs inference from biological data"; ECToBlob and TOB-QMC both describe it as the first. TOB-QMC and ECToBlob add a different outline: an optimum of the quartet criterion refines the tree of blobs, and edges are then contracted by quartet tests. We found no earlier statement of that refinement result, and no earlier proof of TINNiK's Theorem 4. Section 2 lists the cited results the proofs use, including Mitchell et al. 2019 and Rhodes 2020.

### Concurrent work

- TOB-QMC and ECToBlob. First public versions: TOB-QMC [bioRxiv v1, 2025-11-06](https://doi.org/10.1101/2025.11.05.686850), under the title "Fast and accurate tree of blobs reconstruction under the network multispecies coalescent"; ECToBlob [bioRxiv v1, 2026-05-31](https://doi.org/10.64898/2026.05.28.728501). ECToBlob's statement: "When this work was well underway, we learned a different group was independently pursuing the same outline for tree of blobs inference", with its research dated to a residence at ICERM in Fall 2024, and thanks to Dai, Han and Molloy "for sharing their pre-publication work". TOB-QMC v5 does not mention ECToBlob; it thanks Ané, Allman, Baños and Rhodes for feedback.
  - Same result: an optimum of the quartet criterion refines the tree of blobs. TOB-QMC's Theorem 1 assumes the binary NMSC model and T-quartet-nonanomalous networks. ECToBlob's Theorem 3.1 and Corollary 3.6 assume only two conditions on the gene tree distribution, which its Remark 3.3 says hold for the NMSC with no anomalous quartets, for common inheritance and for the displayed tree model.
  - Same question by another method: the contraction step. TOB-QMC applies TINNiK's tests (ECToBlob compares with the T3 option) to `O(n)` four-taxon subsets around an edge and keeps the smallest p-value, with guarantees at level 1 (its Corollary 1, Theorem 2). ECToBlob applies the T1 test to the bipartition, quadripartition or multipartition sets of an edge, combines p-values under dependence, and contracts one step at a time; its Theorem 4.1 and Theorem 8.2 hold at any level. ECToBlob's §10 gives the authors' comparison of the two.
- Holtgrefe, Huber, van Iersel, Jones, Martin, Moulton, Squirrel, [Mol. Biol. Evol. 42 (2025), msaf067](https://doi.org/10.1093/molbev/msaf067) ([bioRxiv 2024-11-03](https://doi.org/10.1101/2024.11.01.621567); abstract only): level-1 networks from quarnets or alignments, "combinatorially consistent" on full triangle-free quarnet sets. TOB-QMC says it was released during its study and "creates candidate TOBs, through edge contractions, which is similar to TOB-QMC", from sequence data and with no statistical guarantee under the NMSC.
- Englander, Frohn, Gross, Holtgrefe, van Iersel, Jones, Sullivant, [bioRxiv 2025-04-24](https://doi.org/10.1101/2025.04.18.649493) (v4, 2026-07-04; preprint, no journal link in the bioRxiv API; abstract only): claims that under the Jukes-Cantor and Kimura 2-parameter models any two binary semi-directed networks displaying different quartets are distinguishable, so that the tree of blobs is identifiable at any level. Same question on sequence data. ECToBlob cites it.

### Since the paper

We found no erratum, retraction or published counterexample to a statement of the three papers: Crossref's `updates` filter returned nothing for TINNiK, the Genome Research paper, or the cited papers we checked (Allman et al. 2023, Ané et al. 2024, Huber et al., Frohn et al., "Beyond level-1", NANUQ+, Rhodes et al., Xu and Ané, Dinh and Baños); Europe PMC lists no correction for TINNiK, Allman et al. 2023, Ané et al. 2024, Huber et al., "Beyond level-1" or NANUQ+, and PubMed lists none for the Genome Research paper. The errors recorded in Section 3 are this audit's own.

Versions of the papers:

- TOB-QMC: bioRxiv v2 (2025-12-09) changed the title; v3 (2026-02-26), v4 (2026-04-06), and v5 (2026-05-15), the version audited. The supplement's internal date, February 26, 2026, is v3's posting date. Published as [Genome Research, doi 10.1101/gr.282203.126](https://doi.org/10.1101/gr.282203.126), accepted 2026-08-20, online 2026-08-28, [ahead of print on PubMed](https://pubmed.ncbi.nlm.nih.gov/42665444/). Its abstract keeps the restriction ("statistically consistent TOB reconstruction when the underlying network is level-1"). We have not read its text or supplement, so we cannot say how its statements differ from v5.
- ECToBlob: the bioRxiv API lists v1 only and no journal link. Crossref's [listing of the SIAM Journal on Life Sciences](https://api.crossref.org/journals/3066-7410/works) (25 works, to 2026-10-14) does not contain it. No version newer than the one audited was found.
- TINNiK: no later version found. It is implemented, with ECToBlob and NANUQ+, in MSCquartets 3.3 (Rhodes, Allman, Ané, Baños, Mitchell, Wicke, [Bioinformatics, 2026-10-20](https://doi.org/10.1093/bioinformatics/btag775); [EcoEvoRxiv 2026-06-09](https://doi.org/10.32942/x24d5w); abstract only).

Work building on TINNiK:

- Allman, Baños, Rhodes, Wicke, NANUQ⁺, [Algorithms Mol. Biol. 20 (2025), 14](https://doi.org/10.1186/s13015-025-00274-w) ([bioRxiv 2024-11-03](https://doi.org/10.1101/2024.10.30.621146); abstract only): given a tree of blobs from TINNiK, resolves its multifurcations to level-1 structure.
- Kolbow, Kong, Solís-Lemus, InPhyNet, [bioRxiv 2025-05-07](https://doi.org/10.1101/2025.05.05.652278) (preprint; abstract only): merges independently inferred level-1 networks and claims that a statistically consistent pipeline can be built with it. TOB-QMC says its guarantee comes from partitioning taxa by the tree of blobs.
- Allman, Ané, Baños, Rhodes, "Beyond level-1", [Bull. Math. Biol. 87 (2025), 166](https://doi.org/10.1007/s11538-025-01545-8) ([arXiv 2025-04-29](https://arxiv.org/abs/2504.21116)): identifiability of classes of galled tree-child networks of any level, by first identifying the tree of blobs. Its Proposition 5.1 states tree of blobs identifiability for binary networks with generic parameters under the displayed tree model and both independent and common inheritance, by "straightforward modifications" of Allman et al. 2023. ECToBlob's §5 leaves the analogue of its Assumption 1 under common or correlated inheritance as something it "strongly suspects". Nevins, Claudio, Nguyen, SEQUoIA, [SIAM Undergrad. Res. Online 19 (2026)](https://doi.org/10.1137/26S1843342), turn that result into an algorithm using the NANUQ⁺ and TINNiK functions.
- Holtgrefe, Allman, Baños, van Iersel, Moulton, Rhodes, Wicke, [Bull. Math. Biol. (2025)](https://doi.org/10.1007/s11538-025-01549-4) ([arXiv 2025-07-23](https://arxiv.org/abs/2507.17308)): features of outer-labeled planar galled level-2 networks distinguishable from displayed quartets, and circular decomposability of an inter-taxon quartet distance (Theorem 4.7). Its outline for an inference method starts from TINNiK's tree of blobs.
- Frohn, Holtgrefe, van Iersel, Jones, Kelk, [Ann. Comb. (2026)](https://doi.org/10.1007/s00026-026-00830-0) ([arXiv 2025-11-27](https://arxiv.org/abs/2511.22736); abstract only): sequence length sufficient to reconstruct binary level-1 networks under the CFN model. This is a finite-sample result on sequences at level 1. We found no such bound for the tests of the three papers.

Work building on TOB-QMC:

- Dai, Molloy, *Is level-1 blob reconstruction under the network multispecies coalescent easy?*, [WABI 2026, LIPIcs 390, 1:1–1:24](https://doi.org/10.4230/LIPIcs.WABI.2026.1) (published 2026-08-27, revised 2026-09-28; [bioRxiv v1 2026-06-10, v2 2026-09-21](https://doi.org/10.64898/2026.06.06.730607)). "Blob reconstruction" here means the inside of a level-1 blob, with the tree of blobs given as input. For binary semi-directed level-1 networks, NetCS finds the hybrid block and circular order of each blob of degree at least 5 (Lemma 1, Theorems 1–3); Corollary 1 states statistical consistency with `O(n log(n) k)` time and `O(n log n)` quarnet queries in its fast mode, matching Frohn et al.'s lower bound. Every statement assumes level 1, and the paper says nothing about treelikeness tests beyond level 1. Its proofs use TOB-QMC's Theorem 2 and the result it numbers Lemma 5 (v5's Lemma 4), and cite TINNiK's Theorem 4 for correctness of the tests on all 4-taxon subsets, the same reading recorded here as E21. The revised version's notice says the trees of blobs estimated in its experiment 3 "did not satisfy the properties of the protocol", that "a minor bug in the TOB reconstruction code" did not explain this, and that after a rerun the trees were "much more accurate" with overall conclusions unchanged. The notice does not say whether the bug touched TOB-QMC's own experiments, which are outside this formalization (Section 9). The theorems of TOB-QMC are not affected.
- Guang, Sapoval, Yan, Kessler, Nakhleh, DIMPLE, [bioRxiv 2026-10-18](https://doi.org/10.64898/2026.10.12.758494) (preprint; abstract only): divide-and-conquer inference "without an explicit restriction on network level", using a tree of blobs. No theorem is claimed in the abstract.
- Arasti, Mirarab, BROOQS, [bioRxiv 2026-09-04, v3 2026-10-26](https://doi.org/10.64898/2026.08.31.748319) (preprint; abstract only): resolves a tree of blobs into a level-1 network; claims a proof of consistency under the NMSC for blobs of size 5 to 15 in its PQ-tree variant, and conjectures it for its spectral variant.
- Justison et al., [bioRxiv 2026-09-04](https://doi.org/10.64898/2026.09.01.748505) (preprint; abstract only): reports by simulation that SNaQ on non-level-1 networks "frequently recovers a tree of blobs compatible with the true network".

Other related work:

- Holtgrefe, Huber, van Iersel, Moulton, [arXiv 2026-10-06](https://arxiv.org/abs/2610.07855) (preprint): claims level-3 semi-directed networks are encoded by their quinnets and that one known counterexample is the only obstruction for quarnets; restates Huber et al.'s Corollary 5.6.
- Cummings, Curiel, Currie, Kagy, Ranasinghe, Rhodes, [arXiv 2026-08-04](https://arxiv.org/abs/2608.03544) (preprint): claims features of level-1 networks identifiable from quintet concordance factors and not from quartets; its Proposition 4.1 claims a limit that holds for `m`-tet concordance factors of every `m`.
- Brits, Holtgrefe, van Iersel, Martin, [arXiv 2026-07-14, v3 2026-08-25](https://arxiv.org/abs/2607.12919) (preprint; abstract and statements scanned): claims that under Jukes-Cantor no network and tree induce the same leaf-pattern distribution unless the network is a tree with 2-blobs.
- Rasschaert, [SSRN 7292396 (2026)](https://doi.org/10.2139/ssrn.7292396) (preprint, DOI registered 2026-08-16; abstract read through Crossref, text not read). Claims a six-taxon binary level-5 counterexample to Xu and Ané's Conjecture 9: a distance split tree with an internal split that "no average-distance-equivalent metric semidirected network of any level" realizes by a cut edge. This is a claimed counterexample to a conjecture, not to a result of the three papers.

Treelikeness beyond level 1. TOB-QMC's oracle asks only whether the network induced on four taxa has a 4-blob. No work we read proves or refutes that this suffices at higher level, on all four-taxon subsets around an edge.

- TOB-QMC v5 proves it at level 1 (Corollary 1, Theorem 2), and from level-2 simulations suggests "a practical heuristic for higher-level networks". Its supplement of February 26, 2026 claims it for disjoint covers at any level (its Lemma 7, Theorem 1); that claim is false at level 2 (E25).
- ECToBlob's §10: "we know of no proof of a stronger result that would justify using the T3 test. Thus the formal justification for TOB-QMC is currently limited to level-1 networks [13, Theorem 2], although simulations suggest it may perform well beyond that case."
- Huber et al.'s Theorem 5.1, Frohn et al.'s Lemma 1 and ECToBlob's Theorem 4.1 hold at any level, but they ask whether a named split `a₁a₂|b₁b₂` is a cut-edge split of the quarnet, which is more than treelikeness: Frohn et al.'s count of a quarnet-split includes identifying "the specific split".
- Allman et al. 2023 and TINNiK work at any level and use resolved topologies with the inference rule, since "the induced network on a B-quartet may or may not have a 4-blob, and can even be a tree". They do not ask about four-taxon sets around an edge of a refinement.
- Dai and Molloy's WABI paper, "Beyond level-1", Holtgrefe et al. and the other works above do not address the question.

### Formalizations

We found no other formalization of any of the three papers, of Allman et al. 2023, or of Huber et al. 2025, in any system. Searches covered GitHub (repository and code search, by language) and web search; they see public work only.

- [vltanh/lean4-phylogenetics](https://github.com/vltanh/lean4-phylogenetics) (Lean 4, public, Apache-2.0, created 2026-10-10, by the user who requested this formalization): the multispecies coalescent, Kingman's coalescent on forests with Tavaré's formula, rooted metric level-1 networks and their network coalescent, and the concordance factors of a cycle (Baños 2019). This project adapted its hierarchy kernel and Kingman modules from commit `06f684e` (`docs/ADAPTED_SOURCES.md`, `docs/COALESCENT_SOURCES.md`). Its level-1 network datatype was not used, and the network coalescent on arbitrary networks in `Basic/Phylogenetics/NMSC/` is new.
- [vltanh/lean4-camus](https://github.com/vltanh/lean4-camus) (Lean 4, public, created 2026-10-10, same owner): the CAMUS dynamic program for level-1 networks (Willson, Warnow, [Bioinformatics 2026](https://doi.org/10.1093/bioinformatics/btag245)) and the statistical steps of that paper. Surveyed for this project (`docs/CONFIGURATION.md`), not imported.
- [vltanh/lean4-adr11](https://github.com/vltanh/lean4-adr11) (Lean 4, public, created 2026-10-04, same owner): Allman, Degnan, Rhodes 2011, identifying the rooted species tree from unrooted gene trees under the multispecies coalescent. Not used here.
- [SauersML/Descent](https://github.com/SauersML/Descent) (Lean 4, public, created 2026-08-05): "A Lean 4 formalization of genetic theory", with coalescent modules (`Descent/Coalescent/`); a code search of it for "multispecies" returns nothing. Not used here.
- Poindexter, [Zenodo 2026-08-04](https://doi.org/10.5281/zenodo.21802297) (preprint; abstract only), claims a Lean 4 proof of confluence of a saturation procedure for rooted triples. [Paureel/rooted-forest-frontier](https://github.com/Paureel/rooted-forest-frontier) (created 2026-10-16) concerns rooted maximum agreement forests of two trees, and its README says its argument "is not an end-to-end machine-checked runtime theorem". Neither treats networks or the coalescent.
- Coq/Rocq, Isabelle, Agda: GitHub's language-filtered repository searches for "phylogenetic", "phylogeny" and "coalescent" returned nothing. Code search found only incidental uses, of which the closest is [CharlesCNorton/sciuridae-verified](https://github.com/CharlesCNorton/sciuridae-verified), a Rocq formalization of squirrel taxonomy. No entry name in the [Archive of Formal Proofs](https://www.isa-afp.org/) sitemap contains "phylogen" or "coalesc"; we did not search the entries' contents.

## 11. What's next

Plans for follow-up papers are kept in `NEXT.md`, which is not published.

### Open directions

- **Treelikeness beyond level 1.** ECToBlob's §10 says of the T3 test: "we know of no proof of a stronger result that would justify using the T3 test", and that the formal justification for TOB-QMC stops at level 1; Section 10 finds no published work that settles this. The question: for a network of any level and a refinement `B` of its tree of blobs, does every edge of `B` not in the tree of blobs have a non-treelike 4-taxon set among those around it? The papers' arguments stop short of it: Theorem 4.1's hypothesis names the split `a₁a₂|b₁b₂`, and an induced network may resolve another way, while TOB-QMC's Lemma 4 depends on a blob having a single reticulation. A disjoint cover is not enough at level 2 (E25). A related question: how many treelikeness queries around an edge are needed at level `k`.
- **Assumption 1 under correlated inheritance.** ECToBlob "strongly suspects" Assumption 1 for common or correlated inheritance, and `Corollary1` here covers only `ρ = 0`. `Phylogenetics.geneTreeDist` includes `ρ`, and the forward clauses are proved for all `ρ` (`Phylogenetics.cut_alternatives`, `Phylogenetics.trivial_uniform`). What is needed is the generic clause: a nonvanishing witness for each 4-taxon network, for each `ρ`.
- **Rates.** All consistency statements here are asymptotic, with no rate. The proof of Theorem 8.2 runs on one event per quartet, so a non-asymptotic statement would follow from a concentration bound on each test, with constants depending on the distance of the CF from the null. What stands in the way is the non-regularity at the centroid and the boundary (E11, E13).
- **Theorem 8.2 for Cauchy and CBC on the boundary.** E11 shows these two variants need positive alternatives on null quartets. The T1 test's own null excludes the boundary in Mitchell et al., while (5.2) does not. A test that behaves at `(1,0,0)`, or a statement of the assumption that excludes it, would remove the hypothesis.
- **Remark 8.4 (coarsening).** The same proof should give: if `T₀` is not a resolution, the output has no false edges and lacks only the cut edges missing from `T₀`. `ECToBlob.Deterministic` isolates the argument; its hypotheses on `T₀` would need weakening where it uses `T_B ⊆ T₀`.
- **The T3 test and the no-anomaly assumption.** ECToBlob's discussion asks how the cut test can act as an analog of T3 when no-anomaly is not assumed. `TOBQMC.consistency` uses TINNiK's cut test for this; with no T-quartet nonanomaly, Theorem 1 itself fails, and what remains to study is the output of the method when `B` isn't a refinement.

### Simpler proofs

Each of these is the argument of the formal proof, so it is checked in Lean. We found none of them published, in the search of Section 10.

- **ECToBlob Theorem 4.1, in domination language.** An arc `e` induces the split `a₁a₂|b₁b₂` on a quartet exactly when `e` dominates `a₁, a₂` (every root path to them uses `e`) and `b₁, b₂` are not below it, or the reverse (`Phylogenetics.RootedNetwork.hasCutSplitOn_iff_separates`). Then a cut edge of a quartet is a statement about each taxon separately, and the paper's chain of 2-blobs and funnel argument becomes a case split on two orderings of arcs (`ECToBlob.TripleCutArc.up_or_up`). It needs no vertex sets and no laminarity. It saves the discussion of `G̃₃, G̃₄`, Figure 2 and the "two 3-blobs" remark.
- **Allman et al. Lemma 3, likewise.** Since `e₀` isn't a cut on `Y`, some taxon `α` is below `e₀` and not dominated by it, and an arc resolving `{a,b,c,α}` on `Y \ {d}` compares with `e₀` by `External.AllmanEtAl2023.order_of_isBelow_of_dominates`. Components and the cycle through `A, K_ab, e₀, K_cd` do not appear.
- **TINNiK's Theorem 4: the centroid.** The paper proves `CF ≠ (1/3,1/3,1/3)` for generic parameters by a separate analyticity argument. It follows from CF-detectability: strictly cut and non-cut CFs each have two different entries. This removes that paragraph of the proof, and also the need for a separate generic set.
- **Rhodes 2020 Theorem 2.** Double-count over the edges of the `x`–`y` path instead of summing over nodes (`External.Rhodes2020.sum_sidePairs`). Each pair of taxa other than `y` counts at exactly one edge, unless it is a pair `uv` with `uv|xy` displayed. This replaces the source's two node equations.
- **Binary trees.** A tree is binary exactly when it resolves every 4-set (`Phylogenetics.isBinaryTree_of_forall_displays`, `Phylogenetics.IsBinaryTree.exists_displays`). In TOB-QMC's Lemma 3 this replaces the degree argument of the "second observation".
- **The T1 tail.** `P(T > t) ≤ P(χ²₂ > t)`: with `Z̄ = Z̄₀ + μ`, for `μ ≥ 0` the extra term `½(1 - sgn Z̄)Z̄²` is at most `Z̄₀²`, so the variable is at most `Z² + Z̄₀²` (`Phylogenetics.QuartetTests.t1Tail_le_chiSqTwoTail`). No comparison of densities is needed.
- **Wilks-type limits for a trinomial.** One estimate, `|(1+v) log(1+v) - v - v²/2| ≤ 4|v|³` for `|v| ≤ 1/2` (`Real.abs_entropyExcess_sub_le`), gives every statistic as a sum of such terms, so each is uniformly close on bounded sets to a continuous function of the whitened frequencies, and the portmanteau theorem on open sets finishes. This avoids the general machinery of van der Vaart's Theorem 16.7, tightness and Slutsky. At the centroid, Pearson's statistic is exactly `Z₁² + Z₂²` (`Phylogenetics.Trinomial.pearsonS_centroid`).
- **Bridges at level 1.** An arc is a bridge exactly when no other arc enters the descendants of its target (`TOBQMC.Level1.isBridge_iff_reaches`). Most facts on blobs in TOB-QMC's Lemma 4 and Corollary 1 follow in a few lines.
- **The B-quartet rule.** 32 boolean cases on `{a,b,c,d,e} ∩ A` show that a split resolving one of three 4-sets either resolves `{a,b,c,d}` or `{b,c,d,e}`, or separates `a, e` from `b, c, d` (`External.AllmanEtAl2023.rule_core`).

### The formalization

- **The assumed results.** Proving `External.AllmanEtAl2023.Corollary1` and the generic clause of `ECToBlob.AdaptedAllmanTheorem1` would make the whole formalization unconditional. It is large but feasible, in layers: (1) quartet CFs as explicit analytic functions of lengths and `γ`, from `Phylogenetics.geneTreeDist` by summing histories; (2) the zero set of a nonzero real-analytic function on a product of intervals is null; (3) reducing a 4-taxon network to the source's finite list of cases, by the source's graph surgery at boundary parameters, with a nonzero witness per case. Estimated at 3,000–6,000 lines. Whether to spend that effort is the user's decision.
- **Generality to reach.** Non-binary gene trees in Theorem 8.2 (Section 6); `T3`; TOB-QMC's level-`k` bounds.
- **Contributions to other libraries.** `Basic/` holds what could move to Mathlib: the error function (`Basic/Analysis/SpecialFunctions/Erf.lean`), rotation invariance and strip probabilities of the standard Gaussian on the plane (`Basic/Probability/GaussianPlane.lean`), `χ²` tails for 1 and 2 degrees of freedom (`Basic/Probability/GaussianTail.lean`), an extended continuous mapping theorem (`Basic/Probability/Trinomial/Transfer.lean`), and Gibbs' inequality (`Basic/Analysis/SpecialFunctions/GibbsInequality.lean`). It also holds what could go to a phylogenetics library: `Basic/Phylogenetics/` (networks, cut edges by domination, split families and tree metrics, Kingman's coalescent, and the NMSC on arbitrary networks). All of it depends on Mathlib only.
- **Reuse of `External/`.** The rule of Allman et al., the quartet metrization of Rhodes, and exchangeability under the NMSC are stated for arbitrary networks, for other formalizations citing the same sources.
