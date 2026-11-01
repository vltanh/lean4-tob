# The tree of blobs of a phylogenetic network, in Lean

A Lean 4 formalization of five papers on the tree of blobs, what remains of a phylogenetic network when its reticulate parts are contracted:

- **Gusfield, Bansal, Bafna, Song 2007**: the decomposition theory behind the idea, on networks that derive a set of binary sequences.
- **Allman, Baños, Mitchell, Rhodes 2023**: the tree of blobs is identifiable from gene quartet distributions under the network multispecies coalescent.
- **TINNiK** (Allman, Baños, Mitchell, Rhodes 2024), **TOB-QMC** (Dai, Han, Molloy 2026) and **ECToBlob** (Rhodes, Allman, Ané, Baños 2026): methods that infer it from 4-taxon concordance factors, and recover it with probability tending to one as the number of gene trees grows.

**Status.** The formalization is complete for the numbered results and unconditional: no result of the literature is assumed, there is no `sorry` or `axiom`, and the audit finds only Lean's standard axioms. Every numbered result is proved as printed, or proved in a corrected form with the printed one refuted or left open and the correction documented. No person has reviewed the proofs. Independent agents reviewed the statements and compared the proofs with the papers, and the results of that audit are in [`docs/REPORT.md`](docs/REPORT.md).

## What is proved

- The numbered results of all five papers, listed at the head of [`docs/REPORT.md`](docs/REPORT.md), by the papers' arguments except for the departures listed in [its Section 7](docs/REPORT.md#7-departures-from-the-papers-proofs). Its Section 8 has what each depends on. These are excepted, as the audit finds them false: TOB-QMC's supplement Lemma 7 and Theorem 1 at arbitrary level, its Lemma 2's converse, and Theorem 4 of Gusfield et al. as printed, whose true forms are proved.
- The results they cite, in [`src/External/`](src/External), each with a README that says whether its source was read: Rhodes 2020 (Theorem 2), Huber et al. 2025 (Theorem 5.1, forward), Ané et al. 2024 (exchangeability), Mitchell et al. 2019 (Theorem 3.1, for this model), NANUQ 2019 (Proposition 9; Theorem 36, corrected), Gusfield 1991 (the Perfect Phylogeny Theorem), Semple and Steel 2003 (the Splits Equivalence Theorem), Gusfield et al. 2004 (one blob; reduced galled trees), Myers and Griffiths 2003 (the haplotype bound), Hudson and Kaplan 1985 (the lower bound), Song and Hein 2005 (the bound by ordered SPR).
- What the papers say in passing, where it's mathematics and true. [Section 9 of the report](docs/REPORT.md#9-not-formalized) lists what remains, and what stays open.
- `lake build` passes with no warnings, and there is no `native_decide` or `implemented_by`. [`scripts/Audit.lean`](scripts/Audit.lean) checks all 19,669 declarations of the project and of the library it uses, including private and generated ones, against [`propext`](https://leanprover-community.github.io/mathlib4_docs/Init/Core.html#propext), [`Classical.choice`](https://leanprover-community.github.io/mathlib4_docs/Init/Prelude.html#Classical.choice), [`Quot.sound`](https://leanprover-community.github.io/mathlib4_docs/Init/Prelude.html#Quot.sound). [`scripts/check_kernels.sh`](scripts/check_kernels.sh) checks the main theorems under three kernels: Lean's, NanoDa and con-ron.

## The main results

[`src/MainResults.lean`](src/MainResults.lean) states and proves 39 theorems, in the namespace `TreeOfBlobs`, each with a docstring in plain terms. The names [`TreeOfBlobs.theorem1`](src/MainResults.lean#L113), [`TreeOfBlobs.theorem2`](src/MainResults.lean#L139), [`TreeOfBlobs.theorem4`](src/MainResults.lean#L169) are TOB-QMC's and TINNiK's; those of the two other papers have prefixes.

### ECToBlob

- [`TreeOfBlobs.theorem3_1`](src/MainResults.lean#L65) (3.1): every tree maximizing the Maximum Quartet Support objective resolves the tree of blobs, for quartet probabilities with strict dominance across cut edges and exchangeability across them.
- [`TreeOfBlobs.theorem4_1`](src/MainResults.lean#L75) (4.1): if `a₁a₂|b₁b₂` is a cut-edge split of every induced 4-taxon network for `aᵢ ∈ Aᵢ`, `bᵢ ∈ Bᵢ`, then `A₁ ∪ A₂ | B₁ ∪ B₂` is a cut-edge split of the network.
- [`TreeOfBlobs.theorem8_2`](src/MainResults.lean#L94) (8.2, corrected): there are test levels `α_n, β_n`, independent of the network, such that every variant of the algorithm, from any resolution of the tree of blobs, returns the tree of blobs with probability tending to one.

### TOB-QMC

- [`TreeOfBlobs.theorem1`](src/MainResults.lean#L113), [`TreeOfBlobs.theorem1_optimal`](src/MainResults.lean#L125) (1): optimal solutions of Weighted Quartet Consensus refine the tree of blobs, almost surely for all large numbers of gene trees.
- [`TreeOfBlobs.theorem2`](src/MainResults.lean#L139) (2): on a binary level-1 network, an oracle for treelikeness on a disjoint cover around each edge of a refinement finds the edges to contract.
- [`TreeOfBlobs.consistency`](src/MainResults.lean#L150) (§4.3): the resulting method is consistent for level-1 networks, under the paper's assumptions.

### TINNiK

- [`TreeOfBlobs.theorem4`](src/MainResults.lean#L169) (4): for generic parameters there are levels `α_m → 0` such that the algorithm is consistent, for any `β > 0` and exact tree builder.

### Allman et al. 2023

- [`TreeOfBlobs.allman_lemma1`](src/MainResults.lean#L193): on four taxa, the semidirected network has one 4-blob, a B-quartet, or two 3-blobs, a T-quartet, and otherwise only 2-blobs.
- [`TreeOfBlobs.allman_theorem1`](src/MainResults.lean#L214): on four taxa, for generic parameters, the tree of blobs has the topology `ab|cd` exactly when the concordance factor is strictly `(ab|cd)`-cut, and is unresolved exactly when it is non-cut. [`TreeOfBlobs.allman_corollary1`](src/MainResults.lean#L224) reads the topology of each induced 4-taxon network of a larger one from its concordance factor.
- [`TreeOfBlobs.allman_proposition1`](src/MainResults.lean#L231), [`TreeOfBlobs.allman_proposition1_converse`](src/MainResults.lean#L239): the concordance factors on such a network with topology `ab|cd` are exactly the triples `(p, q, q)`, for all `p + 2q = 1`.
- [`TreeOfBlobs.allman_theorem2`](src/MainResults.lean#L258), [`TreeOfBlobs.allman_theorem3`](src/MainResults.lean#L268): the B-quartet Inference Rule, and with it all B-quartets can be identified from the concordance factors.
- [`TreeOfBlobs.allman_theorem4`](src/MainResults.lean#L275): for generic parameters, one function, chosen before the network, recovers the reduced unrooted tree of blobs from the gene quartet distribution.
- [`TreeOfBlobs.allman_lemma2_needs_connected`](src/MainResults.lean#L249): Lemma 2 needs a word that it lacks (see below).

### Gusfield et al. 2007

- [`TreeOfBlobs.gusfield_theorem1`](src/MainResults.lean#L291), [`TreeOfBlobs.gusfield_theorem3`](src/MainResults.lean#L298): every `M` has a network whose blobs correspond to the non-trivial components of its incompatibility graph, and with an ancestral sequence there is one with exactly the sum of the components' minima of recombination nodes.
- [`TreeOfBlobs.gusfield_lemma4`](src/MainResults.lean#L308): the edges of a component in `T̄` form a star.
- [`TreeOfBlobs.gusfield_theorem4_entry`](src/MainResults.lean#L319), [`TreeOfBlobs.gusfield_theorem4_iff`](src/MainResults.lean#L327), [`TreeOfBlobs.gusfield_exists_realization`](src/MainResults.lean#L336): the true forms of Theorem 4, and that their hypotheses can be met. [`TreeOfBlobs.gusfield_theorem4_false_top`](src/MainResults.lean#L346), [`TreeOfBlobs.gusfield_theorem4_false_siteFree`](src/MainResults.lean#L352): Theorem 4 as printed is false.
- [`TreeOfBlobs.gusfield_theorem5`](src/MainResults.lean#L359), [`TreeOfBlobs.gusfield_theorem6`](src/MainResults.lean#L366), [`TreeOfBlobs.gusfield_theorem7`](src/MainResults.lean#L373), [`TreeOfBlobs.gusfield_theorem8`](src/MainResults.lean#L382), [`TreeOfBlobs.gusfield_theorem9`](src/MainResults.lean#L388), [`TreeOfBlobs.gusfield_corollary2`](src/MainResults.lean#L417), [`TreeOfBlobs.gusfield_corollary3`](src/MainResults.lean#L423): the sufficient conditions for decomposability.
- [`TreeOfBlobs.gusfield_theorem10`](src/MainResults.lean#L398), [`TreeOfBlobs.gusfield_theorem10_multiple`](src/MainResults.lean#L405): Theorem 10, with the rooted count.
- [`TreeOfBlobs.gusfield_unrootedConjecture_single_false`](src/MainResults.lean#L431), [`TreeOfBlobs.gusfield_unrootedConjecture_multiple_false`](src/MainResults.lean#L436), [`TreeOfBlobs.gusfield_rootedConjecture_single_false`](src/MainResults.lean#L441), [`TreeOfBlobs.gusfield_rootedConjecture_multiple_false`](src/MainResults.lean#L444): the four Full-Decomposition Optimality Conjectures are false.
- [`TreeOfBlobs.gusfield_theorem11`](src/MainResults.lean#L411): for any `d`, a matrix with `F¹(M) - R¹(M) ≥ d`.

## Results of the audit

The numbers refer to [`docs/REPORT.md`](docs/REPORT.md), which gives each with its location, the paper's sentence, a Lean counterexample and the repair.

- **Gusfield et al. 2007.** Theorem 4 is false as printed, since the definition of "efficient" omits the node where a blob is entered (E42), and since site-free arcs are allowed (E43); it holds with both repaired, up to two conventions (E44). The first repair is in print, in Gusfield's 2014 book, in a stricter form, which we read only in snippets (E42); the Lean adds the exact characterization, the failure under the printed definition, and the check in the kernel. Line 373 on the most tree-like network (E45), line 554 on galled networks (E49), line 560 on visible nodes (E50), the step at line 403 on one `M` (E48) and line 180's wording of "reduced" (E47) are false as printed. Theorem 10 has a notation slip, and with the printed count it stays open (E51). Theorem 1 and the refutations aren't affected. All of this was read in the PMC manuscript and an author's copy with its symbols, where the misprints are too. The journal's typeset text wasn't reachable.
- **Allman et al. 2023.** No numbered result fails, reading a subnetwork as connected; read literally, Lemma 2 does, and its proof and all its uses assume the word (E55). A side remark in the proof of Proposition 1 fails for some `ε` (E57), the remark on edge lengths between trivial blobs means internal edges (E64), and the proofs have gaps that are filled here (E56, E58–E62). Some misprints are in the PMC manuscript only (E57, E63, E66).
- **ECToBlob.** (3.3) overcounts (E2). Remark 8.4 fails on a non-binary network (E35). Remark 3.3 needs "no anomalous quartets" read strictly (E36). Theorem 8.2 needs parameters meeting Assumption 1 (E10), and, for its Cauchy and CBC variants, positive alternatives on null quartets (E11), both agreed with the user; the second doesn't affect the NMSC. The largest gap is in its proof: the witness of a false edge may have a trivial 4-blob, which needed a new argument (E12).
- **TOB-QMC.** The supplement's Lemma 7 and Theorem 1 are false at level 2, by an explicit network (E25). Its Lemma 2's converse is false (E23), and positive lengths don't exclude the centroid (E28). The margin of its Lemma 4 is vacuous as printed (E22).
- **TINNiK.** The count `4(N-1)` should be `4(N-4)` (E29), and the MLE need not exist on the open cut model (E31). Its use of its Theorem 2 needs a stronger rule, which the same proof gives (E30).
- **Among results only cited.** NANUQ's Theorem 36 is false as printed, at the distance, and Studier and Keppler's Lemma, as we read it in a scan, fails at polytomies. Theirs and the others' gaps are in the report's Section 2.
- **Proofs.** They follow the sources' arguments, except the departures in [the report's Section 7](docs/REPORT.md#7-departures-from-the-papers-proofs), each with what the paper does, what Lean does and why. Some repair a gap or an error; some have no printed argument to follow, such as Allman et al.'s Lemma 1 and the modification at Gusfield et al.'s line 329; a few weren't forced, and say so. [`docs/route_differences.tsv`](docs/route_differences.tsv) records every difference of route. Four sources of proved results weren't read: Gusfield 1991, Semple and Steel 2003 and Song and Hein 2005, whose proofs here are standard arguments, and Baños 2019, whose claim has our own proof. Huson and Klöpper 2007 wasn't read either, and its definitions come from its errata and a later paper.

## Status of what's open

Stated in Lean and neither proved nor refuted: Gusfield et al.'s line 425 ([`Gusfield2007.MinDecomposableOfForallS`](src/Gusfield2007/Conjectures.lean#L118)), Theorem 10 with the printed count ([`Gusfield2007.Theorem10Printed`](src/Gusfield2007/SufficientConditions.lean#L562)), and whether distinct columns are needed in Theorem 10 for single crossovers. Theorem 8.2 of ECToBlob stays on binary gene trees, so it doesn't cover the displayed tree model on non-binary networks (E37).

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
scripts/check_kernels.sh                                                         # Lean's kernel, NanoDa, con-ron
```

- Toolchain: Lean and Mathlib `v4.36.0-rc1` ([`lean-toolchain`](lean-toolchain), [`lake-manifest.json`](lake-manifest.json)).
- The library [lean4-phylogenetics](https://github.com/vltanh/lean4-phylogenetics) is required by commit, `9948de9`, in [`lakefile.toml`](lakefile.toml). It holds the definitions and general results of phylogenetics that this project uses.
- [`scripts/check_kernels.sh`](scripts/check_kernels.sh) uses `lake comparator`, `leanexport` and `con-ron`, under `lake env`, and takes some minutes. Its configuration is [`palomar/comparator.json`](palomar/comparator.json).
- After adding a module, run `python3 scripts/gen_audit.py`. After moving declarations, run `python3 scripts/linkify_docs.py` to update the documents' links.
- `scripts/*Check.lean` check by themselves some counterexamples of the audit.
- [`docs/CONFIGURATION.md`](docs/CONFIGURATION.md) records the versions, decisions and what "line N" means for each paper. [`docs/ADAPTED_SOURCES.md`](docs/ADAPTED_SOURCES.md) and [`docs/COALESCENT_SOURCES.md`](docs/COALESCENT_SOURCES.md) record adapted code.

## Layout

| Folder | Content |
| --- | --- |
| [`src/MainResults.lean`](src/MainResults.lean) | The 39 main theorems |
| [`src/ECToBlob/`](src/ECToBlob) | ECToBlob: Sections 3–8, Remarks, §10 |
| [`src/TOBQMC/`](src/TOBQMC) | TOB-QMC: quartet consensus, level-1 blobs, consistency, the bipartition search, the supplement's lemmas |
| [`src/TINNiK/`](src/TINNiK) | TINNiK: Theorem 4, the T3 option, neighbor joining, counts, the test's statistics |
| [`src/AllmanEtAl2023/`](src/AllmanEtAl2023) | Allman et al. 2023, on the paper's own objects, and the forms for the later papers. [Its README](src/AllmanEtAl2023/README.md) lists results, modules and remaining departures |
| [`src/Gusfield2007/`](src/Gusfield2007) | Gusfield et al. 2007, on sequence-labelled networks. It imports Mathlib only. [Its README](src/Gusfield2007/README.md) lists the modules |
| [`src/External/`](src/External) | The results that the papers cite, one folder per source, each with a README |
| [`src/Basic/`](src/Basic) | What the papers share beyond the library: the algorithms and standing assumptions, the hypothesis tests, analysis for Mathlib. [Its README](src/Basic/README.md) has the modules |
| [`docs/`](docs) | [`REPORT.md`](docs/REPORT.md), [`CREDITS.md`](docs/CREDITS.md), the configuration, the routes of the proofs |
| [`scripts/`](scripts) | The audit, the route check, the kernels, generated-file and link checks, standalone checks of counterexamples |
| [`palomar/`](palomar) | Files for a possible Palomar submission, which isn't planned, and the configuration of the kernel check |

[`src/External/`](src/External) and the papers' libraries import each other at the level of modules, with no cycle: the bounds on Gusfield et al.'s networks in [`src/External/`](src/External) are stated on [`Gusfield2007.Network`](src/Gusfield2007/Defs.lean#L129), and [`src/Gusfield2007/`](src/Gusfield2007) uses them. So the libraries are a way of organizing the code rather than layers.

## GitHub configuration

[`.github/workflows/lean_action_ci.yml`](.github/workflows/lean_action_ci.yml) builds the project and the whole library, runs the audit and the route check, and checks that the generated files, the documents' links and the Markdown tables are current. It needs no settings. The three kernels aren't in CI, so run them by hand.

## License

Apache-2.0: [LICENSE](LICENSE). Code adapted from [lean4-phylogenetics](https://github.com/vltanh/lean4-phylogenetics) (Apache-2.0) keeps its notice in each file's header.
