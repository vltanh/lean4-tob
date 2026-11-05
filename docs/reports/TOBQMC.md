# Audit of TOB-QMC

- **TOB-QMC**: J. Dai, Y. Han, E. K. Molloy, *Quartet-based species tree methods enable fast and consistent tree of
  blobs reconstruction under the network multispecies coalescent*,
  [bioRxiv 10.1101/2025.11.05.686850 v5](https://www.biorxiv.org/content/10.1101/2025.11.05.686850v5), with its supplement
  (internally dated February 26, 2026; its link to v5 is unconfirmed, and its numbering differs from v5's in places).

This is the part of [the audit](../REPORT.md) about TOB-QMC. [The audit](../REPORT.md) has what the five papers have in common: the summary and the status of the formalization, the results from prior work that they cite (Section 2), the readings that ECToBlob, TOB-QMC and TINNiK share (Section 6), the literature (Section 10) and what's next (Section 11). The sections here keep its numbers, and the findings are numbered across the five papers: here E18–E28, E39, E69–E74, E83.

## 3. Errors and gaps in the paper

### Main text (v5)

**E18. Lemma 3, proof.** The result holds; the steps below are repaired in [`TOBQMC.lemma3_of_properties`](../../src/TOBQMC/WQC.lean#L619), [`TOBQMC.lemma3`](../../src/TOBQMC/WQC.lean#L678), and in the proof of exchangeability.

- Lines 449–451: "uniquely maximized by `T_N`" is wrong: every refinement of `T_N` ties ([`Phylogenetics.quartetPart_of_displays`](https://github.com/vltanh/lean4-phylogenetics/blob/9948de9b3cba330596424efd2dca9617be2efb0c/Phylogenetics/Tree/Detach.lean#L587)); (2) only compares with non-refinements. The strictness of (2) needs that a non-refinement differs from `T_N` on some T-quartet, so that displayed quartets determine splits ([`Phylogenetics.subset_of_forall_displays`](https://github.com/vltanh/lean4-phylogenetics/blob/9948de9b3cba330596424efd2dca9617be2efb0c/Phylogenetics/Tree/Splits.lean#L748)).
- Lines 467–471: "only after the four sampled lineages enter this blob can they coalesce" is false for the block containing the root: the three other lineages can coalesce inside the blob and then leave upward. The conclusion holds for a different reason: a pair that coalesces first decides the quartet whichever taxon is above, and if all three leave uncoalesced the three quartet trees are equally likely. [`Phylogenetics.NMSC.exchangeability`](https://github.com/vltanh/lean4-phylogenetics/blob/9948de9b3cba330596424efd2dca9617be2efb0c/Phylogenetics/NMSC/Exchangeability.lean#L412) treats both cases.
- Lines 472–486: the reasons (i), (ii) justify `QS^v(new) = QS^v - QS^{v(b)} + QS^{v(a)}`, not the printed equality with `QS^v(T*)`; quartets without `b` are unaffected, and those with `b` read as the same with `a`, because `b` is now sister to `a`. These last facts are unstated, and the case `QS^{v(a)} > QS^{v(b)}` cannot occur at a maximizer.
- Line 485, "Repeating": needs three unstated facts: detaching `b` leaves the partial scores of the block's other taxa unchanged, so `a` stays best; the block side grows step by step; and earlier block sides
  survive later operations ([`TOBQMC.vertexTaxonPart_detachReattach_of_ne`](../../src/TOBQMC/WQC.lean#L331), [`Phylogenetics.insert_mem_detachReattach`](https://github.com/vltanh/lean4-phylogenetics/blob/9948de9b3cba330596424efd2dca9617be2efb0c/Phylogenetics/Tree/Detach.lean#L536), [`Phylogenetics.mem_detachReattach_of_not_mem`](https://github.com/vltanh/lean4-phylogenetics/blob/9948de9b3cba330596424efd2dca9617be2efb0c/Phylogenetics/Tree/Detach.lean#L549)). Also, `a` must be chosen afresh for each block, on the current tree.
- Lines 489–492: the reattached tree is a tree only because of property (2), since a side of the refined tree is either a lift or lies inside a block, which is unstated ([`Phylogenetics.reattach_isUnrootedTree`](https://github.com/vltanh/lean4-phylogenetics/blob/9948de9b3cba330596424efd2dca9617be2efb0c/Phylogenetics/Tree/Splice.lean#L723)). That a refinement gains needs that displayed quartets determine splits. "Amplified" has no single factor: the gain on `X` is the sum over representative tuples of the gains, divided by `∏|B|` ([`TOBQMC.prod_card_mul_vertexPart_sub`](../../src/TOBQMC/WQC.lean#L493)).
- Lines 492–495: property (2) is what forces every remaining side to be a union of blocks ([`TOBQMC.displays_filter_isBlockUnion`](../../src/TOBQMC/WQC.lean#L578)), which is not noted.
- Lines 497–498: compatibility of the local trees at different vertices is asserted ([`Phylogenetics.IsVertexPartition.compatible_of_ne`](https://github.com/vltanh/lean4-phylogenetics/blob/9948de9b3cba330596424efd2dca9617be2efb0c/Phylogenetics/Tree/Splice.lean#L78)), and that the result is binary needs a proof ([`Phylogenetics.isBinaryTree_of_forall_displays`](https://github.com/vltanh/lean4-phylogenetics/blob/9948de9b3cba330596424efd2dca9617be2efb0c/Phylogenetics/Tree/Detach.lean#L177)).

**E19. Lemma 4, proof.** Of ⇒ (lines 551–556): It does not treat two or more taxa below `v_h`. They lie in one block, a fact stated only in the proof of Corollary 1, so distinct blocks exclude this case. Of ⇐ (line 546): it stops at "these conditions are sufficient" without saying why the cycle with its attachments has no 2|2 cut edge. A cut edge isn't on the cycle, so two taxa on its far side would attach through it, contradicting distinct blocks ([`TOBQMC.Level1.not_hasWedgeCutSplit`](../../src/Basic/Wedge.lean#L1845)).
Lean: [`TOBQMC.Level1.blockWalk_of_below_reticulation`](../../src/Basic/Level1Blobs.lean#L903). The result holds.

**E20. Corollary 1, proof (lines 567–568), and Theorem 2, proof (lines 583–584).** "(otherwise `B_N` is not binary)" gives the wrong reason for each side having at least two blocks: a side with one block is a cut side, so the edge would be in the tree of blobs. Binary `B` is not needed. In Theorem 2, "By the setting" each block lies in a single block of the quadripartition also needs `e ∉ T_N`, for the same reason ([`TOBQMC.Level1.exists_not_isTreelike`](../../src/TOBQMC/Level1.lean#L457)). That an edge of `B_N` not in `T_N` refines one vertex of `T_N`, from a non-trivial blob (lines 530–531, 563–564), is also taken "by the setting": a lowest bridge with taxa of both sides below it gives the vertex, and a trivial blob has too few children for four blocks ([`TOBQMC.exists_blob_of_false_positive`](../../src/TOBQMC/Level1.lean#L329)). The result holds.

**E21. Consistency (lines 597–600).** The paper cites TINNiK's Theorem 4 as stating that the tests are correct on all four-taxon subsets. Its statement is about the algorithm's output, and this fact is a step of its proof, for generic parameters at `ρ = 0`, so it doesn't apply as cited under v5's assumptions. The fact does hold under them, for reasons the paper does not give: non-treelike subsets by 6a; subsets the tree of blobs resolves by nonanomaly and exchangeability; and for a treelike subset the tree of blobs does not resolve, a highest separating arc is not a bridge, and its source is a fork where the rest of the process is symmetric, so the split's CF is strictly largest ([`TOBQMC.Level1.nmscCF_lt_of_not_displays`](../../src/Basic/Level1CF.lean#L172), from [`Phylogenetics.NMSC.nmscCF_lt_of_fork`](https://github.com/vltanh/lean4-phylogenetics/blob/9948de9b3cba330596424efd2dca9617be2efb0c/Phylogenetics/NMSC/TreeCF.lean#L451)). Such a subset need not induce a tree: a reticulation above the fork can stay in its induced subgraph, with three lineages through it. So at level 1, T-quartet nonanomaly implies condition 6b, and [`TOBQMC.Level1.cfDetectable`](../../src/TOBQMC/Level1CF.lean#L54) gives CF-detectability under v5's assumptions. The step from Theorem 1's almost-sure "for all large `k`" to probability tending to one is unstated. Lean: [`TOBQMC.consistency`](../../src/TOBQMC/Consistency.lean#L131), [`TINNiK.tests_correct`](../../src/TINNiK/Basic.lean#L506), and the private [`tendsto_optimaRefine`](../../src/TOBQMC/Consistency.lean#L78) of [`src/TOBQMC/Consistency.lean`](../../src/TOBQMC/Consistency.lean).

**E22. Margin (lines 503–505, and supplement Lemma 4, Eq. (1)).** "`π` is the minimum absolute difference between the qCFs of T-quartets" is always zero: by exchangeability every T-quartet has equal alternatives, so `π(Y) = 0`, and the supplement's "`π_min > 0`" is false for every network whose tree of blobs is not a star. The condition "absolute error `< 0`" is impossible, so Lemma 4 as printed is vacuous. Lean: [`TOBQMC.not_printedPiMin_pos`](../../src/TOBQMC/SupplementLemma4Margin.lean#L65), [`TOBQMC.not_exists_printedError_lt`](../../src/TOBQMC/SupplementLemma4Margin.lean#L73). Repair: use the positive differences between the displayed quartet and each alternative, minimized over T-quartets, with the same radius. Lean: [`TOBQMC.Margin`](../../src/TOBQMC/WQC.lean#L691), [`TOBQMC.exists_margin`](../../src/TOBQMC/WQC.lean#L857).

### Supplement

**E23. Lemma 2: false converse, with `N|Y` the induced subnetwork.** The supplement defines `N|Y` as the induced subnetwork (lines 129–134). With that, a treelike induced quartet can restrict a star on the full tree of blobs: the network with arcs `s→e, s→r, r→u, u→v, v→h, r→w, w→h, u→a, v→b, w→c, h→d`, up to the names of its vertices, has
a five-leaf star as tree of blobs, while its restriction to `{e,a,b,c}` displays `ab|ce` ([`TOBQMC.SupplementLemma2.not_lemma2Converse`](../../src/TOBQMC/SupplementLemma2.lean#L165)). The printed proof of the converse, though, glosses "`N|Y` is a 4-blob" as "there exists a blob `B` in `N` such that each taxon ... is separated from the other three taxa in `Y` by a cut edge incident to `B`". Under that gloss these sets are 4-blobs and the converse doesn't fail. So the statement is false as the supplement's definition reads, and its proof suggests that the gloss may be what was meant. Main v5 keeps only the forward direction, as does Lean ([`TOBQMC.lemma2`](../../src/TOBQMC/Level1.lean#L33)). Agreed with the user.

**E24. Lemma 4, proof.** Strict coordinate errors are weakened to non-strict bounds, after which strict positivity is claimed at the boundary radius; keeping them strict repairs this at the same radius. Equations (6)–(7) must cancel agreeing quartet
terms before identifying the sums. The final display has `2|Y_tree|δ` for `2|Y_star|δ`. `B*` is "some tree that maximizes `QS_E`", and then `QS_E^star(B*) ≥ QS_E^star(T)` is taken from Lemma 5, which gives this for the constructed tree; it holds for any maximizer, since the constructed tree attains both maxima, but that needs saying. Lean: [`TOBQMC.supplementLemma4`](../../src/TOBQMC/WQC.lean#L707).

**E25. Lemma 7 and Theorem 1 at arbitrary level: false.** The supplement's claims extend to networks of arbitrary level that a disjoint cover finds a non-treelike quartet around every false edge. On the binary level-2 network with arcs `(0,2),(1,3),(1,4),(3,6),(2,8),(6,9),(6,10),(9,12),(2,13),(13,7),(3,14),(14,5),(13,14),(0,15),(15,1),(9,16),(16,11),(15,16)`,
leaves `4,5,7,8,10,11,12`, the 3-fix-1-alter cover with blocks `{10},{7},{4,5,8},{11,12}` and anchors `10,7,8,12` has every quartet treelike, though the edge is false. Lean: [`TOBQMC.LevelTwo.not_supplementLemma7`](../../src/TOBQMC/SupplementLevelTwo.lean#L588), on two sets that meet both conditions of Lemma 7 and are treelike; [`TOBQMC.LevelTwo.not_supplementTheorem1`](../../src/TOBQMC/SupplementLevelTwo.lean#L721), at `ρ = 1`, with "relaxed nonanomalous" read as condition 1 of Definition 1 and T-quartet nonanomaly, both of which hold there; [`TOBQMC.LevelTwo.tendsto_tobqmcT3_eq_treeOfBlobs_rho_one`](../../src/TOBQMC/SupplementLevelTwo.lean#L679) with the T3 option; and [`TOBQMC.LevelTwo.forGenericParams_tendsto_tobqmc_eq_treeOfBlobs`](../../src/TOBQMC/SupplementLevelTwo.lean#L664) at `ρ = 0` for generic parameters, where 6a holds too. So the statistical form covers `ρ = 1` and generic parameters at `ρ = 0`, and other `ρ` aren't proved. The oracle form needs no parameters: [`TOBQMC.LevelTwo.not_theorem2_without_level_one`](../../src/TOBQMC/SupplementLevelTwo.lean#L612). The printed proof of Lemma 7 connects its subgraph by undirected paths, while the induced subnetwork keeps only the arcs ancestral to the set. Main v5 restricts Theorem 2 to level 1, so this is consistent with it. This concerns covers, not an oracle on all quartets around an edge (Section 10).

**E26. Lemma 8: missing hypothesis.** A trivial blob need not contain a reticulation: the singleton blob at the parent of `a, b` in `((a,b),(c,d))`. The intended statement requires a nontrivial blob, as agreed with the user. Only used through level-1 arguments in Lean: [`TOBQMC.Level1.exists_reticulation_or_forall_isBridge`](../../src/Basic/Level1Blobs.lean#L354).

**E27. §1.2.** The initial `α = ρ/(1-ρ)` conflicts with the later `ρ = 1/(α+1)` and the stated endpoints; the consistent form is `α = (1-ρ)/ρ`. Lean: `Phylogenetics.concentration_relation`, [`Phylogenetics.urnStep_eq_concentration`](https://github.com/vltanh/lean4-phylogenetics/blob/9948de9b3cba330596424efd2dca9617be2efb0c/Phylogenetics/NMSC/Inheritance.lean#L103).

**E28. "We can safely assume" no centroid (supplement line 300).** Positive tree edge lengths do not exclude `P = (1/3,1/3,1/3)`: the `3₂`-cycle at `t = t₁ = t₂ = 0.02`, `γ = 1/2`, `t₃ ≈ 0.12830`, `ρ = 0` has the centroid CF, as TINNiK itself says in its discussion before Theorem 4. This does not affect v5, whose Definition 1 has strict inequalities and so excludes it on T-quartets. It matters in the supplement, whose Definition 1 is non-strict and relies on this sentence to exclude the centroid: there a true edge with such a quartet would be contracted by the star test.

### Remarks, discussion, and smaller points

These came from formalizing what the papers say in passing.

**E39. TOB-QMC: scaling claims and Algorithm 2.** The result still holds under each of these.

- Lines 603–604 on binary lifting: E69.
- Algorithm 2 (supplement lines 654–676): the tuple `(a₁,a₂,b₁,b₂)` is never reassigned from `q_min` on a repeat, so each pass rebuilds the same `N` and the repeat is vacuous; at `n = 4` the set `N` is empty, so line 10 has no minimizer and line 4 never exits; the test at line 5 isn't counted in `i`; and `i` overshoots the limit by up to `2(n-4)`. Lean: [`TOBQMC.SearchOut.counts`](../../src/TOBQMC/BipartitionSearch.lean#L559), with at most `(n-3) + 2·limit + 2(n-4)` subsets per edge ([`TOBQMC.card_threeFixOneAlter_union_testedSets_le`](../../src/TOBQMC/BipartitionSearch.lean#L578)).
- Lines 130–132 have "fast and default ... `2n²` and `n²/4`, respectively", swapped against the supplement (lines 851–855).
- Supplement Lemma 8's proof, beyond E26: "reticulation nodes in `v`" should be `B`; "binary" isn't used; the two disjoint paths degenerate at `u₀ = r'`; "`u₀` is an ancestor of `u₁`" holds only for a particular reticulation on the cycle.

**E69. TOB-QMC lines 603–604: binary lifting (a wrong name; the total stands).** "The well-known binary lifting algorithm to retrieve the LCA of any pair of leaves in a gene tree in O(1) time." Binary lifting takes `O(log n)` per query: moving a vertex up by `2^J - 1` takes at least `J` jumps ([`Phylogenetics.LCA.length_ge_of_sum_two_pow`](../../src/Basic/LCA.lean#L397)), which gives `O(n² k log n)` for the printed tests ([`TOBQMC.threeFixOneAlterLifting_le`](../../src/TOBQMC/RunningTime.lean#L94)). The printed `O(1)` query and `O(n log(n) k)` precomputation are those of an Euler tour with a sparse table ([`Phylogenetics.LCA.isRangeMin_rangeQuery`](../../src/Basic/LCA.lean#L89)), and with it the printed total holds ([`TOBQMC.threeFixOneAlterReads_le`](../../src/TOBQMC/RunningTime.lean#L57)).

**E70. TOB-QMC line 570: "Ω(n⁴) per edge and thus Ω(n⁵) in total" (a loose sentence: a worst case).** An edge with a cherry on one side has `C(n - 2, 2)` subsets around it ([`TOBQMC.card_bipartitionQuartets_of_two`](../../src/TOBQMC/RunningTime.lean#L556)). Over the edges of a caterpillar the total is `C(n + 1, 5)` ([`TOBQMC.sum_card_bipartitionQuartets_of_caterpillar`](../../src/TOBQMC/RunningTime.lean#L593)), and on a balanced tree it is at most `n⁴` ([`TOBQMC.balanced_total_le`](../../src/TOBQMC/RunningTime.lean#L625)). The last is a sum over the side sizes of a balanced tree, with no tree in the statement. A worst case is enough for the paper's point, that brute force "is no better than TINNiK".

**E71. TOB-QMC lines 171–172: "setting β = 1 ensures the null of the star test is always rejected" (a loose sentence).** It fails exactly on three equal counts, where the p-value is `1` ([`TOBQMC.starPValue_eq_one_of_forall_eq`](../../src/TOBQMC/Implementation.lean#L564)), and it holds on all others ([`TOBQMC.starPValue_lt_one`](../../src/TOBQMC/Implementation.lean#L579)).

**E72. TOB-QMC lines 618–622: "does not exceed" (a loose sentence).** "The time complexity of detecting FPs O(n³k + n log(n)k) does not exceed the time complexity of seeking a TOB refinement (note that TREE-QMC has time complexity O(n³k) with some assumptions and ASTRAL-III has time complexity O(n^1.726 k^1.726 D)...)". It holds for TREE-QMC, which is what the supplement says at its line 677 ([`TOBQMC.searchReads_le_cube`](../../src/TOBQMC/RunningTime.lean#L79)). As a comparison of bounds it doesn't extend to the ASTRAL-III bound beside it: at `k = 1` and `D` of order `n`, that bound is below `n³` ([`TOBQMC.rpow_mul_lt_cube`](../../src/TOBQMC/RunningTime.lean#L543)).

**E73. TOB-QMC supplement lines 642–647 (an error in an example; the conclusion stands).** With `|A| = |C| = 1` and `|B| = |D| = (n-2)/2`, the printed probability of one taxon from each block is `4(n-2)²/(n-1)⁴`, from picking a taxon with probabilities `2/(n-1)` and `(n-2)/(n-1)`, which don't belong to a sampling. Around the bipartition, the fraction of subsets with one taxon from each block is exactly `16/n²` ([`TOBQMC.card_around_of_blocks`](../../src/TOBQMC/RunningTime.lean#L724)). The order `1/n²`, which is what the remark uses, is right.

**E74. TOB-QMC line 281: "TINNiK is deterministic" (a loose sentence, with no mathematical content).** TINNiK's step 2c says that in case of a tie one chooses uniformly at random. Lean's [`TINNiK.theorem4`](../../src/TINNiK/Basic.lean#L629) holds for every selection ([`IsMLSelection`](../../src/Basic/Defs.lean#L145)), which is what makes the tie harmless.

### Points on the sources that only this paper uses

These are about the sources that the five papers cite, and none affects a result of the five papers. Section 2 has the earlier points on them.

**E83. Zhang et al. 2018 (ASTRAL-III), Eq. 7 (a dropped constant).** Their Eq. 3 has `½ QI(T, M)`, and Eq. 7 restates it with no `½`. The constant has no effect on the order. Lean's count is [`TOBQMC.astralOperations_le`](../../src/TOBQMC/RunningTime.lean#L400).

### Typos

**E34.**

- TOB-QMC, line 449: `QS^tree(T|N)` for `QS^tree(T_N)`. Lines 455, 459: `Pᵢ ≠ Pⱼ ≠ Pₛ ≠ Pₜ` must mean pairwise distinct. Line 462: `∪∪ Y` gives taxa, not 4-subsets: should be the union of `f_cover(P)`.
- TOB-QMC, line 535: `Z|Y` for `Z|W`.

## 4. Missing hypotheses

| Where | Missing hypothesis | Counterexample without it | In the formalization |
| --- | --- | --- | --- |
| TOB-QMC supplement Lemma 8 (E26), agreed | Nontrivial blob | E26; [`TOBQMC.not_two_le_indegree_of_sameBlob_leaf`](../../src/TOBQMC/SupplementLemma8.lean#L112) | [`TOBQMC.supplement_lemma8`](../../src/TOBQMC/SupplementLemma8.lean#L91), with `v ≠ w` in the blob of `v` |

## 5. Redundant hypotheses

The Lean statements leave these out, except where the last column says otherwise and in [`src/MainResults/TOBQMC.lean`](../../src/MainResults/TOBQMC.lean), which keeps the paper's hypotheses.

| Result | Hypothesis that is not needed | Why | Lean |
| --- | --- | --- | --- |
| TOB-QMC Lemma 4 | That `B` is a tree, refines `T_N`, that `A` is an internal side and is not in `T_N` | Only [`RefinesBlob`](../../src/TOBQMC/Level1.lean#L40) is used | [`TOBQMC.lemma4`](../../src/TOBQMC/Level1.lean#L382) |
| TOB-QMC Corollary 1 | `B` binary (line 558) | Theorem 2 prints no "binary"; [`TOBQMC.theorem2`](../../src/TOBQMC/Level1.lean#L534) reads the quadripartition as the multipartition (Section 6) | [`TOBQMC.corollary1`](../../src/TOBQMC/Level1.lean#L413) keeps it and uses only [`IsUnrootedTree`](https://github.com/vltanh/lean4-phylogenetics/blob/9948de9b3cba330596424efd2dca9617be2efb0c/Phylogenetics/Tree/Defs.lean#L49) |
| TOB-QMC, T3 option | 6a in full; off the T3 model suffices | The T3 test also detects a 4-blob with a cut CF having `q > 1/3`, which the cut test misses; being off the T3 model is enough | [`TOBQMC.consistencyT3_of_offModel`](../../src/TOBQMC/ConsistencyT3.lean#L93) |
| TOB-QMC, T3 option | 6b, given condition 4, at level 1 | At level 1 the two are equivalent; on any network 6b implies condition 4 | [`TOBQMC.noAnomalousQuartets_iff_tQuartetNonanomalous`](../../src/TOBQMC/ConsistencyT3.lean#L71) |

## 6. How the formalization reads the paper

### Readings specific to this paper

- **TOB-QMC's disjoint cover around an edge of a non-binary tree** (Definition 2) is read with the multipartition at the edge ([`Phylogenetics.multipartitionQuartets`](https://github.com/vltanh/lean4-phylogenetics/blob/9948de9b3cba330596424efd2dca9617be2efb0c/Phylogenetics/Tree/Defs.lean#L107)), since Theorem 2 is stated there.
- **Assumption 6a** of TOB-QMC is the hypothesis `hBlob` of [`TOBQMC.consistency`](../../src/TOBQMC/Consistency.lean#L131).
- **TOB-QMC's restriction `N⁻|Y`**: Lemma 4 is proved on `wedgeArcs Y`, the union of the wedge paths of `N` between taxa of `Y`, which lies below the LSA ([`Phylogenetics.RootedNetwork.wedgeArcs_subset_belowArcs`](../../src/Basic/Wedge.lean#L775)). Its cut edges with both sides nonempty are those of `HasCutSplitOn` ([`Phylogenetics.RootedNetwork.hasWedgeCutSplit_iff_hasCutSplitOn`](../../src/Basic/Wedge.lean#L901)). Parallel arcs and degree-two blobs are not suppressed: in a binary network this changes no split of a cut edge, which is not formalized. "Contains a 4-blob" is read as "no cut edge with a `2|2` split", the paper's equivalence at lines 379–382.
- **TOB-QMC's combined search**: [`TOBQMC.tobqmcSearch`](../../src/TOBQMC/BipartitionSearch.lean#L726) reads the tests as [`TOBQMC.tobqmc`](../../src/Basic/Defs.lean#L266) does. This is with the cut test ([`TOBQMC.consistency_search`](../../src/TOBQMC/BipartitionSearch.lean#L796)) and with T3 ([`TOBQMC.consistencyT3_search_of_noAnomalous`](../../src/TOBQMC/BipartitionSearchT3.lean#L202)). The implementation at lines 133–137, which runs the star test on the minimizer only, is [`TOBQMC.tobqmcImplementation`](../../src/TOBQMC/Implementation.lean#L82), with the second `pmin` at line 137 read as the star p-value on the minimizer, as the sentence before it says. [`TOBQMC.consistency_implementation`](../../src/TOBQMC/Implementation.lean#L197) is its consistency, for any selection of subsets containing a disjoint cover, possibly depending on the data, and such covers exist ([`TOBQMC.exists_isDisjointCover`](../../src/TOBQMC/Implementation.lean#L389)). It contracts fewer edges than [`tobqmc`](../../src/Basic/Defs.lean#L266) ([`TOBQMC.tobqmc_subset_implementation`](../../src/TOBQMC/Implementation.lean#L113)).

## 7. Departures from the paper's proofs

The last column but one says why, and says so plainly when a departure isn't forced. Mechanics and representation with the same content aren't listed: paths as sets of arcs, for instance, and a concrete value for "sufficiently long".

| Result | The paper's argument | The formalization's | Why | E-item |
| --- | --- | --- | --- | --- |
| TOB-QMC Lemma 1 (cited there, from Ané et al.; v5 prints no proof) | Their proof, from "two 3-blobs" (Allman et al.'s Lemma 1) to a cut edge | [`IsTreelike`](https://github.com/vltanh/lean4-phylogenetics/blob/9948de9b3cba330596424efd2dca9617be2efb0c/Phylogenetics/Network/Quartets.lean#L49) says this directly | Not forced | — |
| TOB-QMC Lemma 4 | Attachments distinct, then suppressed `N⁻\|Y`, "thus" a 4-blob | On the subnetwork `wedgeArcs Y` without suppression; a 2\|2 cut edge would make two taxa attach through it | The "thus" is a gap. Skipping suppression isn't forced | E19 |
| TOB-QMC Corollary 1 | "Each side has two blocks" from `B` binary; the blob "by the setting" | From the edge not being in `T_N`; the blob is proved ([`TOBQMC.exists_blob_of_false_positive`](../../src/TOBQMC/Level1.lean#L329)) | Gap: the printed reason is wrong | E20 |
| TOB-QMC supplement Lemma 4 | Margin from all three differences; strictness dropped, then claimed; `B*` a maximizer | Margin against the displayed quartet; strict bounds; `B*` the tree of Lemma 3, through a hypothesis | Gap for the first two. The hypothesis isn't forced | E22, E24 |
| TOB-QMC supplement Lemma 8 | Two disjoint paths from the blob root, a sequence of reticulations | A lowest reticulation, by a sink of the blob below `u` ([`TOBQMC.exists_reticulation_below`](../../src/TOBQMC/SupplementLemma8.lean#L43)) | Not forced in the sense of the rule, though the printed route has gaps and needs Menger's theorem, which the library lacks | E26, E39 |
| TOB-QMC consistency | Theorem 1, Theorem 2, and TINNiK's Theorem 4 for correct tests on all four-taxon subsets | The same combination, with the levels of TINNiK's proof. Correctness is the proof step [`TINNiK.tests_correct`](../../src/TINNiK/Basic.lean#L506), at parameters where [`TOBQMC.Level1.cfDetectable`](../../src/TOBQMC/Level1CF.lean#L54) holds; on subsets treelike but not resolved by the tree of blobs this needs the new [`Phylogenetics.NMSC.nmscCF_lt_of_fork`](https://github.com/vltanh/lean4-phylogenetics/blob/9948de9b3cba330596424efd2dca9617be2efb0c/Phylogenetics/NMSC/TreeCF.lean#L451) | Gap: the cited statement concerns the output at generic parameters and `ρ = 0`, and the paper does not treat the third class | E21 |
| Blobs in linear time (TOB-QMC supplement line 206) | Contract the blobs and suppress the vertices of degree two | The family of sides, as discovery-time intervals ([`Phylogenetics.BridgeDFS.mem_treeOfBlobs_iff`](../../src/Basic/BridgeDFS.lean#L1222)) | Representation: [`treeOfBlobs`](https://github.com/vltanh/lean4-phylogenetics/blob/9948de9b3cba330596424efd2dca9617be2efb0c/Phylogenetics/Network/Quartets.lean#L40) is a family of sides | — |
| TOB-QMC Theorem 2 | "Following the proof of Corollary 1" | The steps of that proof, Lemmas 2 and 4, and not the corollary's statement, which concerns all subsets around an edge and says nothing on a cover | Not a departure from the argument: the route check records it | — |

## 8. What each result depends on

<!-- Generated from scripts/Audit.lean -->

| Result | Lean | Results from prior work used |
| --- | --- | --- |
| TOB-QMC Lemma 2 | [`TOBQMC.lemma2`](../../src/TOBQMC/Level1.lean#L33) | [`External.HuberEtAl2025.theorem5_1_forward`](../../src/External/HuberEtAl2025/Theorem51.lean#L25) |
| TOB-QMC (1) | [`TOBQMC.equation1`](../../src/TOBQMC/WQC.lean#L78) | – |
| TOB-QMC (2) | [`TOBQMC.equation2`](../../src/TOBQMC/WQC.lean#L119) | – |
| TOB-QMC (3) | [`TOBQMC.equation3`](../../src/TOBQMC/WQC.lean#L154) | – |
| TOB-QMC Lemma 3, its proof's form | [`TOBQMC.lemma3_of_properties`](../../src/TOBQMC/WQC.lean#L619) | – |
| TOB-QMC Lemma 3 | [`TOBQMC.lemma3`](../../src/TOBQMC/WQC.lean#L678) | [`External.AneEtAl2024.exchangeability`](../../src/External/AneEtAl2024/Exchangeability.lean#L28) |
| TOB-QMC Supplement Lemma 4 | [`TOBQMC.supplementLemma4`](../../src/TOBQMC/WQC.lean#L707) | – |
| TOB-QMC Theorem 1 | [`TOBQMC.theorem1`](../../src/TOBQMC/WQC.lean#L989) | [`External.AneEtAl2024.exchangeability`](../../src/External/AneEtAl2024/Exchangeability.lean#L28) |
| TOB-QMC Theorem 1, optima | [`TOBQMC.theorem1_optimal`](../../src/TOBQMC/WQC.lean#L1029) | [`External.AneEtAl2024.exchangeability`](../../src/External/AneEtAl2024/Exchangeability.lean#L28) |
| TOB-QMC ASTRAL corollary | [`TOBQMC.astral_corollary`](../../src/TOBQMC/WQC.lean#L1064) | [`External.AneEtAl2024.exchangeability`](../../src/External/AneEtAl2024/Exchangeability.lean#L28) |
| TOB-QMC Lemma 4 | [`TOBQMC.lemma4`](../../src/TOBQMC/Level1.lean#L382) | [`External.HuberEtAl2025.theorem5_1_forward`](../../src/External/HuberEtAl2025/Theorem51.lean#L25) |
| TOB-QMC Corollary 1 | [`TOBQMC.corollary1`](../../src/TOBQMC/Level1.lean#L413) | [`External.HuberEtAl2025.theorem5_1_forward`](../../src/External/HuberEtAl2025/Theorem51.lean#L25) |
| TOB-QMC Theorem 2 | [`TOBQMC.theorem2`](../../src/TOBQMC/Level1.lean#L534) | [`External.HuberEtAl2025.theorem5_1_forward`](../../src/External/HuberEtAl2025/Theorem51.lean#L25) |
| TOB-QMC 3f1a | [`TOBQMC.threeFixOneAlter_correct`](../../src/TOBQMC/Level1.lean#L784) | [`External.HuberEtAl2025.theorem5_1_forward`](../../src/External/HuberEtAl2025/Theorem51.lean#L25) |
| TOB-QMC consistency | [`TOBQMC.consistency`](../../src/TOBQMC/Consistency.lean#L131) | [`AllmanEtAl2023.CFDetectable`](../../src/AllmanEtAl2023/CFDetectable.lean), [`External.AneEtAl2024.exchangeability`](../../src/External/AneEtAl2024/Exchangeability.lean#L28), [`External.HuberEtAl2025.theorem5_1_forward`](../../src/External/HuberEtAl2025/Theorem51.lean#L25) |
| TOB-QMC Lemma 1 | [`TOBQMC.lemma1`](../../src/TOBQMC/Lemma1.lean#L554) | – |
| TOB-QMC supplement Lemma 8 | [`TOBQMC.supplement_lemma8`](../../src/TOBQMC/SupplementLemma8.lean#L91) | – |
| TOB-QMC, the bipartition search with 3f1a | [`TOBQMC.consistency_search`](../../src/TOBQMC/BipartitionSearch.lean#L796) | [`AllmanEtAl2023.CFDetectable`](../../src/AllmanEtAl2023/CFDetectable.lean), [`External.AneEtAl2024.exchangeability`](../../src/External/AneEtAl2024/Exchangeability.lean#L28), [`External.HuberEtAl2025.theorem5_1_forward`](../../src/External/HuberEtAl2025/Theorem51.lean#L25) |
| TOB-QMC consistency, T3 option | [`TOBQMC.consistencyT3_of_noAnomalous`](../../src/TOBQMC/ConsistencyT3.lean#L160) | [`External.AneEtAl2024.exchangeability`](../../src/External/AneEtAl2024/Exchangeability.lean#L28), [`External.HuberEtAl2025.theorem5_1_forward`](../../src/External/HuberEtAl2025/Theorem51.lean#L25) |
| TOB-QMC ASTRAL's output | [`TOBQMC.astral_refines_treeOfBlobs`](../../src/TOBQMC/Astral.lean#L159) | [`External.AneEtAl2024.exchangeability`](../../src/External/AneEtAl2024/Exchangeability.lean#L28), [`Phylogenetics.IsTraceback.isAstralOptimal`](https://github.com/vltanh/lean4-phylogenetics/blob/9948de9b3cba330596424efd2dca9617be2efb0c/Phylogenetics/Tree/AstralDP.lean#L1103) |
| ASTRAL-III, Theorem 1 of Zhang et al. 2018 | [`TOBQMC.astralOperations_le`](../../src/TOBQMC/RunningTime.lean#L400) | [`External.KaneTao2017.theorem1`](../../src/External/KaneTao2017/PartitioningClusters.lean#L974) |
| ASTRAL-III, Lemma 1 of Zhang et al. 2018 | [`TOBQMC.qi_eq_qiFast`](../../src/TOBQMC/RunningTime.lean#L285) | – |
| TREE-QMC, Theorem 3 of Han and Molloy 2023 | [`TOBQMC.treeQMCWork_le`](../../src/TOBQMC/RunningTime.lean#L129) | – |
| TOB-QMC, A TOB refinement need not be a display tree of the network | [`TOBQMC.DisplayedRefinement.refinement_not_displayed`](../../src/TOBQMC/DisplayedRefinement.lean#L40) | – |
| TOB-QMC, The implementation at embedded lines 133-137 | [`TOBQMC.tobqmcImplementation`](../../src/TOBQMC/Implementation.lean#L82) | – |
| TOB-QMC, The claim of TOB-QMC for its implementation | [`TOBQMC.consistency_implementation`](../../src/TOBQMC/Implementation.lean#L197) | [`AllmanEtAl2023.CFDetectable`](../../src/AllmanEtAl2023/CFDetectable.lean), [`External.AneEtAl2024.exchangeability`](../../src/External/AneEtAl2024/Exchangeability.lean#L28), [`External.HuberEtAl2025.theorem5_1_forward`](../../src/External/HuberEtAl2025/Theorem51.lean#L25) |
| TOB-QMC, The claim of TOB-QMC for its implementation, with the T3 test | [`TOBQMC.consistencyT3_implementation`](../../src/TOBQMC/Implementation.lean#L256) | [`External.AneEtAl2024.exchangeability`](../../src/External/AneEtAl2024/Exchangeability.lean#L28), [`External.HuberEtAl2025.theorem5_1_forward`](../../src/External/HuberEtAl2025/Theorem51.lean#L25) |
| TOB-QMC supplement, the margin of Lemma 4 as printed vanishes | [`TOBQMC.not_printedPiMin_pos`](../../src/TOBQMC/SupplementLemma4Margin.lean#L65) | – |
| TOB-QMC supplement, Lemma 4 as printed has no instance | [`TOBQMC.not_exists_printedError_lt`](../../src/TOBQMC/SupplementLemma4Margin.lean#L73) | – |
| TOB-QMC supplement, the converse of Lemma 2 is false, with the induced subnetwork | [`TOBQMC.SupplementLemma2.not_lemma2Converse`](../../src/TOBQMC/SupplementLemma2.lean#L165) | – |
| TOB-QMC supplement, Lemma 7 is false at level 2 | [`TOBQMC.LevelTwo.not_supplementLemma7`](../../src/TOBQMC/SupplementLevelTwo.lean#L588) | – |
| TOB-QMC supplement, Theorem 1 is false at level 2 | [`TOBQMC.LevelTwo.not_supplementTheorem1`](../../src/TOBQMC/SupplementLevelTwo.lean#L721) | – |
| TOB-QMC, Theorem 2 needs level 1 | [`TOBQMC.LevelTwo.not_theorem2_without_level_one`](../../src/TOBQMC/SupplementLevelTwo.lean#L612) | – |
| TOB-QMC supplement, level 2, the T3 option at rho = 1 | [`TOBQMC.LevelTwo.tendsto_tobqmcT3_eq_treeOfBlobs_rho_one`](../../src/TOBQMC/SupplementLevelTwo.lean#L679) | – |
| TOB-QMC supplement, level 2, generic parameters at rho = 0 | [`TOBQMC.LevelTwo.forGenericParams_tendsto_tobqmc_eq_treeOfBlobs`](../../src/TOBQMC/SupplementLevelTwo.lean#L664) | [`AllmanEtAl2023.cfDetectable_generic`](../../src/AllmanEtAl2023/CFDetectable.lean#L24), [`AllmanEtAl2023.CFDetectable`](../../src/AllmanEtAl2023/CFDetectable.lean) |

## 9. Not formalized

**Empirical claims.**

- ECToBlob, TOB-QMC, TINNiK: the simulations, the data analyses and measured running times, ECToBlob's evidence at lines 907–910 that combined p-values aren't monotone, and TINNiK's report in Appendix C.3 that at the singularity both tests "perform very conservatively for small significance levels". Asymptotic running times are proved as counts of operations, with no machine model (Section 6).

**Statements that are false.** Each row is a statement, read as the row says, with the theorem that shows it fails. What's formalized is the failure, and the true form where there is one (Sections 3 and 4). Loose sentences, and proof steps that fail with the result standing, are in Section 3 and not here: among them E13, E64, E68–E74.

| Statement | Item | Counterexample |
| --- | --- | --- |
| TOB-QMC supplement Lemma 2, converse, with `N\|Y` the induced subnetwork, as the supplement defines it. Under the printed proof's gloss, a blob of `N`, it doesn't fail | E23 | [`TOBQMC.SupplementLemma2.not_lemma2Converse`](../../src/TOBQMC/SupplementLemma2.lean#L165) |
| TOB-QMC supplement Lemma 4, the margin as printed | E22 | [`TOBQMC.not_printedPiMin_pos`](../../src/TOBQMC/SupplementLemma4Margin.lean#L65), [`TOBQMC.not_exists_printedError_lt`](../../src/TOBQMC/SupplementLemma4Margin.lean#L73) |
| TOB-QMC supplement Lemma 7 and Theorem 1 at arbitrary level | E25 | [`TOBQMC.LevelTwo.not_supplementLemma7`](../../src/TOBQMC/SupplementLevelTwo.lean#L588); [`TOBQMC.LevelTwo.not_supplementTheorem1`](../../src/TOBQMC/SupplementLevelTwo.lean#L721), at `ρ = 1`, and generically at `ρ = 0` |
| TOB-QMC supplement Lemma 8 on a trivial blob | E26 | [`TOBQMC.not_two_le_indegree_of_sameBlob_leaf`](../../src/TOBQMC/SupplementLemma8.lean#L112) |
| TOB-QMC supplement line 300, on the centroid | E28 | [`External.AllmanBanosRhodes2019.ThreeTwo.centroid_N₃`](../../src/External/AllmanBanosRhodes2019/ThreeTwoCycle.lean#L1024) |
