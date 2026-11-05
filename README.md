# The tree of blobs of a phylogenetic network, in Lean

A Lean 4 formalization of five papers on the tree of blobs, what remains of a phylogenetic network when its reticulate parts are contracted:

- **Gusfield, Bansal, Bafna, Song 2007**: the decomposition theory behind the idea, on networks that derive a set of binary sequences.
- **Allman, Baños, Mitchell, Rhodes 2023**: the tree of blobs is identifiable from gene quartet distributions under the network multispecies coalescent.
- **TINNiK** (Allman, Baños, Mitchell, Rhodes 2024), **TOB-QMC** (Dai, Han, Molloy 2026) and **ECToBlob** (Rhodes, Allman, Ané, Baños 2026): methods that infer it from 4-taxon concordance factors, and recover it with probability tending to one as the number of gene trees grows.

**Status.** The formalization is complete for the numbered results, and no result of the literature is assumed: there is no `sorry` or `axiom`, and the audit finds only Lean's standard axioms. Every numbered result is proved as printed, or proved in a corrected form with the correction documented. One theorem is conditional, and says so in its statement: Theorem 10 of Gusfield et al., with `R(M + S)` read by the definition at its line 385, is refuted for multiple crossovers given a finite computation that Lean's kernel hasn't completed. The paper's own use of that symbol suggests a slip for `R_S(M)`, and with that Theorem 10 is proved. No person has reviewed the proofs. Independent agents reviewed the statements and compared the proofs with the papers, and the results of that audit are in [`docs/REPORT.md`](docs/REPORT.md).

## What is proved

- The numbered results of all five papers, listed at the head of [`docs/REPORT.md`](docs/REPORT.md), by the papers' arguments except for the departures listed in [its Section 7](docs/REPORT.md#7-departures-from-the-papers-proofs). Its Section 8 has what each depends on. These are excepted, as the audit finds them false: TOB-QMC's supplement Lemma 7 and Theorem 1 at arbitrary level, its Lemma 2's converse, Theorem 4 of Gusfield et al. as printed, and its Theorem 10 if `R(M + S)` is read by the definition at line 385, where the paper's own use suggests a slip. The true forms are proved.
- The results they cite, in [`src/External/`](src/External), each with a README that says whether its source was read: Rhodes 2020 (Theorem 2), Huber et al. 2025 (Theorem 5.1), Ané et al. 2024 (exchangeability, Proposition 12, a rule of its Section 3.3), Mitchell et al. 2019 (Theorem 3.1 for this model, the limit laws and densities of T3 and T1), NANUQ 2019 (Proposition 9; Theorem 36, corrected), Legried et al. 2021 (Theorem 1 on quartets), Dinh and Baños 2025 (Theorem 1), Kane and Tao 2017 (the bound of Theorem 1), Gusfield 1991 (the Perfect Phylogeny Theorem), Semple and Steel 2003 (the Splits Equivalence Theorem), Gusfield et al. 2004 (one cycle, reduced galled trees, optimality, an algorithm with its correctness and count), Myers and Griffiths 2003 (the haplotype bound, the integer program, Algorithms 1 and 3), Hudson and Kaplan 1985 (the bound and its algorithm), Song and Hein 2005 (the bound by ordered SPR, and that the minimum over trees is `R¹`). Results of these sources that no proof here uses are left out.
- What the papers say in passing, where it's mathematics and true. [Section 9 of the report](docs/REPORT.md#9-not-formalized) lists what remains: empirical claims, statements that are wrong, each with its counterexample, and what stays open.
- `lake build` passes with no warnings, and there is no `native_decide` or `implemented_by`. [`scripts/Audit.lean`](scripts/Audit.lean) checks all 26,537 declarations of the project and of the library it uses, including private and generated ones, against [`propext`](https://leanprover-community.github.io/mathlib4_docs/Init/Core.html#propext), [`Classical.choice`](https://leanprover-community.github.io/mathlib4_docs/Init/Prelude.html#Classical.choice), [`Quot.sound`](https://leanprover-community.github.io/mathlib4_docs/Init/Prelude.html#Quot.sound). [`scripts/check_kernels.sh`](scripts/check_kernels.sh) checks the main theorems under three kernels: Lean's, NanoDa and con-ron.

## The main results

The modules of [`src/MainResults/`](src/MainResults), one per paper with the sources it cites, state and prove 90 theorems, in the namespace `TreeOfBlobs`, each with a docstring in plain terms; [`src/MainResults.lean`](src/MainResults.lean) imports the five. One is conditional, as it says: [`TreeOfBlobs.gusfield_theorem10Printed_multiple_false_of_search`](src/MainResults/Gusfield2007.lean#L219). The names [`TreeOfBlobs.theorem1`](src/MainResults/TOBQMC.lean#L59), [`TreeOfBlobs.theorem2`](src/MainResults/TOBQMC.lean#L85), [`TreeOfBlobs.theorem4`](src/MainResults/TINNiK.lean#L49) are TOB-QMC's and TINNiK's; those of the other papers and of the sources have prefixes.

### ECToBlob

- [`TreeOfBlobs.theorem3_1`](src/MainResults/ECToBlob.lean#L72) (3.1): every tree maximizing the Maximum Quartet Support objective resolves the tree of blobs, for quartet probabilities with strict dominance across cut edges and exchangeability across them.
- [`TreeOfBlobs.theorem4_1`](src/MainResults/ECToBlob.lean#L82) (4.1): if `a₁a₂|b₁b₂` is a cut-edge split of every induced 4-taxon network for `aᵢ ∈ Aᵢ`, `bᵢ ∈ Bᵢ`, then `A₁ ∪ A₂ | B₁ ∪ B₂` is a cut-edge split of the network.
- [`TreeOfBlobs.theorem8_2`](src/MainResults/ECToBlob.lean#L101) (8.2, corrected): there are test levels `α_n, β_n`, independent of the network, such that every variant of the algorithm, from any resolution of the tree of blobs, returns the tree of blobs with probability tending to one.

### TOB-QMC

- [`TreeOfBlobs.theorem1`](src/MainResults/TOBQMC.lean#L59), [`TreeOfBlobs.theorem1_optimal`](src/MainResults/TOBQMC.lean#L71) (1): optimal solutions of Weighted Quartet Consensus refine the tree of blobs, almost surely for all large numbers of gene trees.
- [`TreeOfBlobs.theorem2`](src/MainResults/TOBQMC.lean#L85) (2): on a binary level-1 network, an oracle for treelikeness on a disjoint cover around each edge of a refinement finds the edges to contract.
- [`TreeOfBlobs.consistency`](src/MainResults/TOBQMC.lean#L96) (§4.3): the resulting method is consistent for level-1 networks, under the paper's assumptions.

### TINNiK

- [`TreeOfBlobs.theorem4`](src/MainResults/TINNiK.lean#L49) (4): for generic parameters there are levels `α_m → 0` such that the algorithm is consistent, for any `β > 0` and exact tree builder.

### Allman et al. 2023

- [`TreeOfBlobs.allman_lemma1`](src/MainResults/AllmanEtAl2023.lean#L55): on four taxa, the semidirected network has one 4-blob, a B-quartet, or two 3-blobs, a T-quartet, and otherwise only 2-blobs.
- [`TreeOfBlobs.allman_theorem1`](src/MainResults/AllmanEtAl2023.lean#L76): on four taxa, for generic parameters, the tree of blobs has the topology `ab|cd` exactly when the concordance factor is strictly `(ab|cd)`-cut, and is unresolved exactly when it is non-cut. [`TreeOfBlobs.allman_corollary1`](src/MainResults/AllmanEtAl2023.lean#L86) reads the topology of each induced 4-taxon network of a larger one from its concordance factor.
- [`TreeOfBlobs.allman_proposition1`](src/MainResults/AllmanEtAl2023.lean#L93), [`TreeOfBlobs.allman_proposition1_converse`](src/MainResults/AllmanEtAl2023.lean#L101): the concordance factors on such a network with topology `ab|cd` are exactly the triples `(p, q, q)`, for all `p + 2q = 1`.
- [`TreeOfBlobs.allman_theorem2`](src/MainResults/AllmanEtAl2023.lean#L120), [`TreeOfBlobs.allman_theorem3`](src/MainResults/AllmanEtAl2023.lean#L130): the B-quartet Inference Rule, and with it all B-quartets can be identified from the concordance factors.
- [`TreeOfBlobs.allman_theorem4`](src/MainResults/AllmanEtAl2023.lean#L137): for generic parameters, one function, chosen before the network, recovers the reduced unrooted tree of blobs from the gene quartet distribution.
- [`TreeOfBlobs.allman_lemma2_needs_connected`](src/MainResults/AllmanEtAl2023.lean#L111): Lemma 2 needs a word that it lacks (see below).

### Gusfield et al. 2007

- [`TreeOfBlobs.gusfield_theorem1`](src/MainResults/Gusfield2007.lean#L57), [`TreeOfBlobs.gusfield_theorem3`](src/MainResults/Gusfield2007.lean#L64): every `M` has a network whose blobs correspond to the non-trivial components of its incompatibility graph, and with an ancestral sequence there is one with exactly the sum of the components' minima of recombination nodes.
- [`TreeOfBlobs.gusfield_lemma4`](src/MainResults/Gusfield2007.lean#L74): the edges of a component in `T̄` form a star.
- [`TreeOfBlobs.gusfield_theorem4_entry`](src/MainResults/Gusfield2007.lean#L85), [`TreeOfBlobs.gusfield_theorem4_iff`](src/MainResults/Gusfield2007.lean#L93), [`TreeOfBlobs.gusfield_exists_realization`](src/MainResults/Gusfield2007.lean#L102): the true forms of Theorem 4, and that their hypotheses can be met. [`TreeOfBlobs.gusfield_theorem4_false_top`](src/MainResults/Gusfield2007.lean#L112), [`TreeOfBlobs.gusfield_theorem4_false_siteFree`](src/MainResults/Gusfield2007.lean#L118): Theorem 4 as printed is false.
- [`TreeOfBlobs.gusfield_theorem5`](src/MainResults/Gusfield2007.lean#L125), [`TreeOfBlobs.gusfield_theorem6`](src/MainResults/Gusfield2007.lean#L132), [`TreeOfBlobs.gusfield_theorem7`](src/MainResults/Gusfield2007.lean#L139), [`TreeOfBlobs.gusfield_theorem8`](src/MainResults/Gusfield2007.lean#L148), [`TreeOfBlobs.gusfield_theorem9`](src/MainResults/Gusfield2007.lean#L154), [`TreeOfBlobs.gusfield_corollary2`](src/MainResults/Gusfield2007.lean#L174), [`TreeOfBlobs.gusfield_corollary3`](src/MainResults/Gusfield2007.lean#L180): the sufficient conditions for decomposability.
- [`TreeOfBlobs.gusfield_theorem10`](src/MainResults/Gusfield2007.lean#L162): Theorem 10, with the rooted count, in each crossover model. [`TreeOfBlobs.gusfield_theorem10_unrooted`](src/MainResults/Gusfield2007.lean#L205): the form without an ancestral sequence, which isn't in the paper.
- [`TreeOfBlobs.gusfield_theorem10Printed_single_false`](src/MainResults/Gusfield2007.lean#L211): Theorem 10 with `R(M + S)` read by the definition at line 385 is false for single crossovers, on 14 rows and 8 sites. [`TreeOfBlobs.gusfield_theorem10Printed_multiple_false_of_search`](src/MainResults/Gusfield2007.lean#L219): **conditional**. With that reading, for multiple crossovers, on 74 rows and 34 sites, it is false given [`Gusfield2007.printedMSearch`](src/Gusfield2007/Theorem10PrintedMultiple.lean#L269), a finite computation that the kernel hasn't completed. The paper's own use of the symbol, at lines 525 and 560, suggests a slip for `R_S(M)`, which is [`TreeOfBlobs.gusfield_theorem10`](src/MainResults/Gusfield2007.lean#L162).
- [`TreeOfBlobs.gusfield_unrootedConjecture_single_false`](src/MainResults/Gusfield2007.lean#L188), [`TreeOfBlobs.gusfield_unrootedConjecture_multiple_false`](src/MainResults/Gusfield2007.lean#L193), [`TreeOfBlobs.gusfield_rootedConjecture_single_false`](src/MainResults/Gusfield2007.lean#L198), [`TreeOfBlobs.gusfield_rootedConjecture_multiple_false`](src/MainResults/Gusfield2007.lean#L201): the four Full-Decomposition Optimality Conjectures are false.
- [`TreeOfBlobs.gusfield_theorem11`](src/MainResults/Gusfield2007.lean#L168): for any `d`, a matrix with `F¹(M) - R¹(M) ≥ d`. [`TreeOfBlobs.gusfield_Md_R_eq`](src/MainResults/Gusfield2007.lean#L244): `R¹(M_d) = 3d`.
- [`TreeOfBlobs.gusfield_exists_isEfficientAtEntry`](src/MainResults/Gusfield2007.lean#L226): line 329, with the entry node counted. [`TreeOfBlobs.gusfield_treeness_merged_false`](src/MainResults/Gusfield2007.lean#L235): the treeness inequality fails for a blob that merges two components. [`TreeOfBlobs.gusfield_conjecture22_false`](src/MainResults/Gusfield2007.lean#L247): the conjecture of Huson and Klöpper is false, as Klöpper's thesis states it.

### What the papers say in passing

- [`TreeOfBlobs.ectoblob_theorem8_2_displayed`](src/MainResults/ECToBlob.lean#L126), [`TreeOfBlobs.ectoblob_displayed_counterexample`](src/MainResults/ECToBlob.lean#L140): under the displayed tree model, Theorem 8.2 holds for Bon and BBC on every network, and fails for Cauchy and CBC under Lean's extension at `p = 1`. [`TreeOfBlobs.ectoblob_not_theorem8_2_without_hpos`](src/MainResults/ECToBlob.lean#L161): without its hypothesis on the alternatives, it fails for those two at all sequences.
- [`TreeOfBlobs.ectoblob_not_consistency_edge_combination_cbc`](src/MainResults/ECToBlob.lean#L176), [`TreeOfBlobs.ectoblob_consistency_sumOfPairs`](src/MainResults/ECToBlob.lean#L201), [`TreeOfBlobs.ectoblob_remark3_4_displays`](src/MainResults/ECToBlob.lean#L194): from ECToBlob's §10 and Remark 3.4.
- [`TreeOfBlobs.tobqmc_consistency_implementation`](src/MainResults/TOBQMC.lean#L122), [`TreeOfBlobs.tobqmc_refinement_not_displayed`](src/MainResults/TOBQMC.lean#L145): TOB-QMC's implementation, and that a refinement of the tree of blobs need not be displayed.
- [`TreeOfBlobs.tinnik_theorem4_missing`](src/MainResults/TINNiK.lean#L69): TINNiK with missing taxa.
- [`TreeOfBlobs.tobqmc_not_supplementLemma7`](src/MainResults/TOBQMC.lean#L167), [`TreeOfBlobs.tobqmc_not_supplementTheorem1`](src/MainResults/TOBQMC.lean#L170), [`TreeOfBlobs.tobqmc_not_theorem2_without_level_one`](src/MainResults/TOBQMC.lean#L173), [`TreeOfBlobs.tobqmc_tendsto_tobqmcT3_rho_one`](src/MainResults/TOBQMC.lean#L176), [`TreeOfBlobs.tobqmc_forGenericParams_tendsto`](src/MainResults/TOBQMC.lean#L185): the claims of TOB-QMC's supplement at arbitrary level are false at level 2. [`TreeOfBlobs.tobqmc_not_lemma2Converse`](src/MainResults/TOBQMC.lean#L164), [`TreeOfBlobs.tobqmc_not_printedPiMin_pos`](src/MainResults/TOBQMC.lean#L151), [`TreeOfBlobs.tobqmc_not_exists_printedError_lt`](src/MainResults/TOBQMC.lean#L157): its Lemma 2's converse, and the margin of its Lemma 4.
- [`TreeOfBlobs.ectoblob_not_equation33Printed`](src/MainResults/ECToBlob.lean#L215), [`TreeOfBlobs.ectoblob_not_theorem8_2_literal`](src/MainResults/ECToBlob.lean#L218): ECToBlob's (3.3) as printed, and its Theorem 8.2 on the literal general model. [`TreeOfBlobs.tinnik_not_exists_generatingCutModel_maximizer`](src/MainResults/TINNiK.lean#L81): no maximum on TINNiK's open cut model at some counts.
- [`TreeOfBlobs.allman_blobDistance_not_identifiable`](src/MainResults/AllmanEtAl2023.lean#L152), [`TreeOfBlobs.allman_banos_range`](src/MainResults/AllmanEtAl2023.lean#L162), [`TreeOfBlobs.allman_outline_consistent`](src/MainResults/AllmanEtAl2023.lean#L172): from Allman et al. 2023, the distance between blobs for every `k ≥ 1`, Baños's range on `𝒩(1)⁺`, and the outline of an algorithm in its Section 5.

### The sources

- Gusfield et al. 2004: [`TreeOfBlobs.galled_exists_isCycle_of_conflict`](src/MainResults/Gusfield2007.lean#L258), [`TreeOfBlobs.galled_theorem2_2`](src/MainResults/Gusfield2007.lean#L264), [`TreeOfBlobs.galled_theorem8_3`](src/MainResults/Gusfield2007.lean#L272), [`TreeOfBlobs.galled_line381`](src/MainResults/Gusfield2007.lean#L278), [`TreeOfBlobs.galled_galledBuild_correct`](src/MainResults/Gusfield2007.lean#L286), [`TreeOfBlobs.galled_galledBuildOps_le`](src/MainResults/Gusfield2007.lean#L295).
- Myers and Griffiths 2003, Hudson and Kaplan 1985, Song and Hein 2005: [`TreeOfBlobs.myersGriffiths_algorithm1_isOptimalValue`](src/MainResults/Gusfield2007.lean#L308), [`TreeOfBlobs.myersGriffiths_Rh_le_R`](src/MainResults/Gusfield2007.lean#L313), [`TreeOfBlobs.hudsonKaplan_isOptimalValue`](src/MainResults/Gusfield2007.lean#L318), [`TreeOfBlobs.songHein_exists_orderedLength_eq_R`](src/MainResults/Gusfield2007.lean#L324).
- NANUQ: [`TreeOfBlobs.nanuq_proposition9_source`](src/MainResults/ECToBlob.lean#L241), [`TreeOfBlobs.nanuq_theorem36_missing`](src/MainResults/ECToBlob.lean#L263). Mitchell et al. 2019: [`TreeOfBlobs.mitchell_proposition4_1`](src/MainResults/TINNiK.lean#L97), [`TreeOfBlobs.mitchell_proposition4_2`](src/MainResults/TINNiK.lean#L108), [`TreeOfBlobs.mitchell_proposition5_1`](src/MainResults/TINNiK.lean#L116), [`TreeOfBlobs.mitchell_proposition5_2`](src/MainResults/TINNiK.lean#L127).
- [`TreeOfBlobs.ane_proposition12`](src/MainResults/TOBQMC.lean#L204), [`TreeOfBlobs.huber_theorem5_1`](src/MainResults/TOBQMC.lean#L209), [`TreeOfBlobs.dinhBanos_theorem1`](src/MainResults/TOBQMC.lean#L216), [`TreeOfBlobs.kaneTao_theorem1`](src/MainResults/TOBQMC.lean#L223), [`TreeOfBlobs.legried_theorem1`](src/MainResults/ECToBlob.lean#L280), [`TreeOfBlobs.studierKeppler_not_lemmaAsPrinted`](src/MainResults/TINNiK.lean#L134).

## Results of the audit

The numbers refer to the audit: [its Section 3](docs/REPORT.md#3-errors-and-gaps-in-the-papers) says which report has each, and the report gives it with its location, the paper's sentence, a Lean counterexample and the repair.

- **Gusfield et al. 2007.** Theorem 4 is false as printed, since the definition of "efficient" omits the node where a blob is entered (E42), and since site-free arcs are allowed (E43); it holds with both repaired, up to two conventions (E44). The first repair is in print, in Gusfield's 2014 book, in a stricter form, which we read only in snippets (E42); the Lean adds the exact characterization, the failure under the printed definition, and the check in the kernel. Theorem 10 is false if `R(M + S)` is read by the definition at line 385: for single crossovers by a counterexample in Lean, and for multiple crossovers given one search that the kernel hasn't completed. Lines 525 and 560 use that symbol for a network with ancestral sequence `S`, which suggests a slip for `R_S(M)`, and with that it is true and proved, with no hypothesis on the columns (E51). Line 373 on the most tree-like network (E45, E67), line 554 on galled networks (E49), line 560 on visible nodes (E50), the step at line 403 on one `M` (E48) and line 180's wording of "reduced" (E47) are false as printed. Theorem 1 and the refutations aren't affected. All of this was read in the PMC manuscript and an author's copy with its symbols, where the misprints are too. The journal's typeset text wasn't reachable.
- **Allman et al. 2023.** No numbered result fails, reading a subnetwork as connected; read literally, Lemma 2 does, and its proof and all its uses assume the word (E55). A side remark in the proof of Proposition 1 fails for some `ε` (E57), the remark on edge lengths between trivial blobs means internal edges (E64), and the proofs have gaps that are filled here (E56, E58–E62). Some misprints are in the PMC manuscript only (E57, E63, E66).
- **ECToBlob.** (3.3) overcounts (E2). Remark 8.4 fails on a non-binary network (E35). Remark 3.3 needs "no anomalous quartets" read strictly (E36). Theorem 8.2 needs parameters meeting Assumption 1 (E10), and, for its Cauchy and CBC variants, positive alternatives on null quartets (E11), both agreed with the person who asked for this formalization; the second doesn't affect the NMSC. The largest gap is in its proof: the witness of a false edge may have a trivial 4-blob, which needed a new argument (E12). Under the displayed tree model, line 1065 is false, and Theorem 8.2 holds for Bon and BBC and fails for Cauchy and CBC (E37). At the centroid, the sentence on uniform T1 p-values is false (E13). Line 1422 asks too little of the tests (E68).
- **TOB-QMC.** The supplement's Lemma 7 and Theorem 1 are false at level 2, by an explicit network (E25). Its Lemma 2's converse is false with `N|Y` the induced subnetwork, as it defines it, and holds under the gloss in its proof (E23), and positive lengths don't exclude the centroid (E28). The margin of its Lemma 4 is vacuous as printed (E22). Some sentences on running times and levels are loose: binary lifting isn't `O(1)` per query, though the total stands (E69), and E70–E74.
- **TINNiK.** The count `4(N-1)` should be `4(N-4)` (E29), and the MLE need not exist on the open cut model (E31). Its use of its Theorem 2 needs a stronger rule, which the same proof gives (E30).
- **Among results only cited.** NANUQ's Theorem 36 is false as printed, at the distance, and Studier and Keppler's Lemma fails at polytomies, a failure of wording if the letter means binary trees; both are in the report's Section 2. One direction of Corollary 2.1 of Gusfield et al. 2004 is false (E76). The rest are gaps and misprints, each of which leaves the result standing (E77–E84), and one point we didn't check (E85).
- **Proofs.** They follow the sources' arguments, except the departures in [the report's Section 7](docs/REPORT.md#7-departures-from-the-papers-proofs), each with what the paper does, what Lean does and why. Some repair a gap or an error; some have no printed argument to follow, such as Allman et al.'s Lemma 1 and the modification at Gusfield et al.'s line 329; a few weren't forced, and say so. [`docs/route_differences.tsv`](docs/route_differences.tsv) records every difference of route. Two sources of proved results weren't read: Gusfield 1991 and Semple and Steel 2003, whose proofs here are standard arguments. Huson and Klöpper 2007 wasn't read either: its conjecture comes from Klöpper's thesis of 2008, and its definitions from its errata and a later paper.

## Status of what's open

Stated in Lean and not settled here: Gusfield et al.'s line 425 ([`Gusfield2007.MinDecomposableOfForallS`](src/Gusfield2007/Conjectures.lean#L118)), which is neither proved nor refuted, and Theorem 10 for multiple crossovers with `R(M + S)` read by the definition at line 385, refuted only given [`Gusfield2007.printedMSearch`](src/Gusfield2007/Theorem10PrintedMultiple.lean#L269). Two separate programs by the same author, not in the repository, and Lean's `#eval` support that hypothesis; the kernel hasn't completed it, and none of those is a proof.

## Credits

- Requested and supervised by The-Anh Vu-Le, who chose the papers, agreed to the corrections of ECToBlob's and TOB-QMC's statements, and decided the library's boundary and the project's layout. **No person has reviewed the proofs.**
- Source audit and first foundations by Codex; statements, proofs, audit and documents by Claude (Opus 5.5) in Claude Code, with sub-agents, following the [formalize-math-paper](https://github.com/vltanh/formalize-math-paper) procedure.
- Made on 2026-10-27 and from 2026-10-31 to 2026-11-01. [`docs/CREDITS.md`](docs/CREDITS.md) has the details.

## Related work

From [the report's Section 10](docs/REPORT.md#10-the-papers-in-the-literature).

- No formalization of these papers was found other than this one. This project imports the public [lean4-phylogenetics](https://github.com/vltanh/lean4-phylogenetics).
- Gusfield's book *ReCombinatorics* (2014), read only in snippets, restates Theorem 4 of Gusfield et al. 2007 with the entry node counted, for "canonical" ARGs. Huson et al. 2009 credit Yun Song with an example of the refutation of the conjectures, in a form on clusters, and van Iersel et al. 2010 and Kelk et al. 2012 state it. Dress et al. 2011 relate the blocks of the Buneman graph to the components of the incompatibility graph.
- History: Gusfield et al. 2007 decomposed networks along incompatible characters. Allman et al. 2023 showed tree of blobs identifiability from quartets, with no bound on the level, and TINNiK made it an algorithm with a consistency theorem. Huber et al. 2025 and Frohn et al. 2025 give the exact-quarnet form that ECToBlob's Theorem 4.1 extends. ECToBlob's Corollary 4.2 is, for binary networks, Lemma 1 of Frohn et al., as ECToBlob says.
- Concurrent: TOB-QMC and ECToBlob prove the same result that an optimum of the quartet criterion refines the tree of blobs, and ECToBlob calls the two works independent.
- Since: Dai and Molloy (WABI 2026) reconstruct level-1 blobs from a tree of blobs, using TOB-QMC's Theorem 2. Allman et al. 2024 settle metric identifiability at level 1. We found no erratum to any of the five papers, and no other work stating the errors recorded here, apart from the book's repair above.

## What's next

The natural next steps are to extend the generic results beyond `ρ = 0`, to settle whether treelikeness of the quartets around an edge decides its membership in the tree of blobs beyond level 1, which ECToBlob's §10 raises, and to ask how much full decomposition costs, which Gusfield et al.'s line 666 leaves open. [The report's Section 11](docs/REPORT.md#11-whats-next) has these and the simpler arguments that the formalization found.

## Building

```sh
lake exe cache get
lake build
lake build Phylogenetics                                                         # the audit reads the whole library
lake env lean -DautoImplicit=false -DmaxSynthPendingDepth=3 scripts/Audit.lean   # axioms and dependencies
python3 scripts/route_check.py check docs/paper_routes.tsv --accept docs/route_differences.tsv
python3 scripts/check_layers.py                                                  # imports between units
scripts/check_kernels.sh                                                         # Lean's kernel, NanoDa, con-ron
```

- Toolchain: Lean and Mathlib `v4.36.0-rc1` ([`lean-toolchain`](lean-toolchain), [`lake-manifest.json`](lake-manifest.json)).
- The library [lean4-phylogenetics](https://github.com/vltanh/lean4-phylogenetics) is required by commit, `9948de9`, in [`lakefile.toml`](lakefile.toml). It holds the definitions and general results of phylogenetics that this project uses.
- [`scripts/check_kernels.sh`](scripts/check_kernels.sh) uses `lake comparator`, `leanexport` and `con-ron`, under `lake env`. By default it checks each paper's entry in [`palomar/`](palomar), from its `comparator.json`; given configurations, it checks those. The five entries took about 16 minutes on the last run. An earlier run, of all 90 theorems at once, measured 12.4 GB in its largest process.
- After adding a module, run `python3 scripts/gen_audit.py`; a new folder also needs a unit in [`scripts/layers.toml`](scripts/layers.toml). After moving declarations, run `python3 scripts/linkify_docs.py` to update the documents' links.
- [`docs/CONFIGURATION.md`](docs/CONFIGURATION.md) records the versions, decisions and what "line N" means for each paper. [`docs/ADAPTED_SOURCES.md`](docs/ADAPTED_SOURCES.md) and [`docs/COALESCENT_SOURCES.md`](docs/COALESCENT_SOURCES.md) record adapted code.

## Layout

| Folder | Content |
| --- | --- |
| [`src/MainResults/`](src/MainResults) | The 90 main theorems, in one module per paper, with those of the sources it cites; [`src/MainResults.lean`](src/MainResults.lean) imports the five |
| [`src/ECToBlob/`](src/ECToBlob) | ECToBlob: Sections 3–8, Remarks, §10, the displayed tree model, the framework on other tests |
| [`src/TOBQMC/`](src/TOBQMC) | TOB-QMC: quartet consensus, Lemma 4 at level 1, consistency, the bipartition search, the implementation, running times, the supplement's lemmas |
| [`src/TINNiK/`](src/TINNiK) | TINNiK: Theorem 4, the T3 option, neighbor joining, missing taxa, the outline of Allman et al., counts, the test's statistics |
| [`src/AllmanEtAl2023/`](src/AllmanEtAl2023) | Allman et al. 2023, on the paper's own objects, and the forms for the later papers. [Its README](src/AllmanEtAl2023/README.md) lists results, modules and remaining departures |
| [`src/Gusfield2007/`](src/Gusfield2007) | Gusfield et al. 2007, on sequence-labelled networks. It reaches only Mathlib and its own sources in [`src/External/`](src/External). [Its README](src/Gusfield2007/README.md) lists the modules |
| [`src/External/`](src/External) | The results that the papers cite, one folder per source, each with a README |
| [`src/Basic/`](src/Basic) | What the papers share beyond the library: the algorithms and standing assumptions, the hypothesis tests, blobs of level-1 networks, networks given by tables, analysis for Mathlib. It imports no paper. [Its README](src/Basic/README.md) has the modules |
| [`docs/`](docs) | [`REPORT.md`](docs/REPORT.md), the audit, with one report per paper in [`docs/reports/`](docs/reports); [`CREDITS.md`](docs/CREDITS.md), the configuration, the routes of the proofs |
| [`scripts/`](scripts) | The audit, the route check, the kernels, generated-file and link checks |
| [`palomar/`](palomar) | One entry per paper for a possible Palomar submission, which isn't planned: its metadata and the configuration of its kernel check |

### Units and their imports

[`scripts/layers.toml`](scripts/layers.toml) divides the code into units, each of which could be its own Lake package: [`Basic`](src/Basic), each paper with the sources that only it uses, and each source that several papers use. It lists the units that each unit may import, and [`scripts/check_layers.py`](scripts/check_layers.py) checks every import against it, and that the units form no cycle. CI runs it.

- [`Basic`](src/Basic) imports no paper. Of the sources, only NANUQ imports more than [`Basic`](src/Basic).
- Allman et al. 2023, then TINNiK, then NANUQ (Allman, Baños, Rhodes 2019), whose formalization uses the language of the two later papers and TINNiK's T3 test.
- TOB-QMC imports TINNiK, Ané et al. 2024, Huber et al. 2025, Kane, Tao 2017 and the T3 test of Mitchell et al. 2019. ECToBlob imports TINNiK, NANUQ, Legried et al. 2021 and the T3 test. The two were written independently, and neither imports the other: what both use is in [`Basic`](src/Basic).
- Gusfield et al. 2007 forms one unit with the five sources that only it uses. They are stated on its networks, [`Gusfield2007.Network`](src/Gusfield2007/Defs.lean#L129), and its proofs use them. The unit imports only Mathlib and Semple, Steel 2003.

`python3 scripts/check_layers.py --graph` prints the units, lowest first, with what each imports.

## GitHub configuration

[`.github/workflows/lean_action_ci.yml`](.github/workflows/lean_action_ci.yml) builds the project and the whole library, runs the audit, the route check and the check of imports between units, and checks that the generated files, the documents' links and the Markdown tables are current. It needs no settings. The three kernels aren't in CI, so run them by hand.

## License

Apache-2.0: [LICENSE](LICENSE). Code adapted from [lean4-phylogenetics](https://github.com/vltanh/lean4-phylogenetics) (Apache-2.0) keeps its notice in each file's header.
