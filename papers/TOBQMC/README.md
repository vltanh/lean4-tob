# TOB-QMC: quartet-based tree of blobs reconstruction, in Lean

[![CI](https://github.com/vltanh/lean4-tob/actions/workflows/lean_action_ci.yml/badge.svg)](https://github.com/vltanh/lean4-tob/actions/workflows/lean_action_ci.yml)

A Lean 4 formalization of J. Dai, Y. Han, E. K. Molloy, *Quartet-based species tree methods enable fast and consistent tree of blobs reconstruction under the network multispecies coalescent*, [bioRxiv 10.1101/2025.11.05.686850 v5](https://www.biorxiv.org/content/10.1101/2025.11.05.686850v5), with its supplement. The tree of blobs of a phylogenetic network is what remains of it when its reticulate parts are contracted. The paper shows that quartet-based species tree methods give a refinement of the tree of blobs under the network multispecies coalescent: almost surely, once there are enough gene trees, every optimal solution of Weighted Quartet Consensus refines it (Theorem 1). An oracle for treelikeness, applied to a disjoint cover of four-taxon subsets around each edge of the refinement, a linear number of them, then finds the edges to contract on a binary level-1 network (Theorem 2). With TINNiK's hypothesis tests as the oracle, the method, TOB-QMC, returns the tree of blobs with probability tending to one (§4.3). The formalization proves these and every other numbered result of the paper, and assumes no result of the literature.

This paper is part of the collection of four papers on the tree of blobs described in [`../../README.md`](../../README.md), formalized in one repository.

## What is proved

- Every numbered result of the paper, as printed or in a corrected form: Lemmas 1, 2, 3, 4; equations (1)–(3); Theorems 1, 2; Corollary 1; the ASTRAL corollary; the correctness of 3-fix-1-alter; the consistency claim of §4.3; supplement Lemmas 4, 8. The proofs follow the paper's arguments, except the departures listed in [Section 7 of the report](REPORT.md#7-departures-from-the-papers-proofs), and its Section 8 has what each result depends on.
- Three claims of the supplement are false, and their failure is proved: its Lemma 7 and Theorem 1 at level 2 (E25), its Lemma 2's converse with `N|Y` the induced subnetwork (E23), and the margin of its Lemma 4 as printed (E22). Main v5 states Theorem 2 at level 1 and keeps only the forward direction of Lemma 2.
- What the paper says in passing: the T3 option, the bipartition search combined with 3-fix-1-alter, the implementation that applies the star test to the minimizer only, that a refinement of the tree of blobs need not be a display tree, ASTRAL's dynamic program, exact on its search space, and the counts of operations behind the running-time claims. [Section 9 of the report](REPORT.md#9-not-formalized) lists what remains: empirical claims, and statements that are false.
- The results it cites, in [`src/External/`](../../src/External), each with a README that says whether its source was read: Huber et al. 2025 (Theorem 5.1, both directions), Ané et al. 2024 (exchangeability, Proposition 12, a rule of its Section 3.3), Dinh and Baños 2025 (Theorem 1, Corollary 2), Kane and Tao 2017 (the bound of Theorem 1) and Mitchell et al. 2019 (the limit laws and densities of the T3 and T1 tests, behind the T3 option). The counts of ASTRAL-III and TREE-QMC are in [`src/TOBQMC/RunningTime.lean`](../../src/TOBQMC/RunningTime.lean). What it uses of Allman et al. 2023 and of TINNiK is in their own units, whose papers have their own folders: [Allman et al. 2023](../AllmanEtAl2023/README.md), [TINNiK](../TINNiK/README.md).
- No result of the literature is assumed. `lake build` passes with no warnings, and there is no `sorry`, `axiom`, `native_decide` or `implemented_by`. [`scripts/Audit.lean`](../../scripts/Audit.lean) checks every declaration of the project and of the library it uses, including private and generated ones, against [`propext`](https://leanprover-community.github.io/mathlib4_docs/Init/Core.html#propext), [`Classical.choice`](https://leanprover-community.github.io/mathlib4_docs/Init/Prelude.html#Classical.choice) and [`Quot.sound`](https://leanprover-community.github.io/mathlib4_docs/Init/Prelude.html#Quot.sound). Run it from the repository root (see Building).
- No person has reviewed the proofs. Independent agents reviewed the statements and compared the proofs with the paper. [`REPORT.md`](REPORT.md) is the audit.

## The main results

[`src/MainResults/TOBQMC.lean`](../../src/MainResults/TOBQMC.lean) states and proves these theorems, in the namespace `TreeOfBlobs`, each with a docstring in plain terms. They keep the paper's hypotheses, including those that the proofs do not use.

### The paper

- [`TreeOfBlobs.theorem1`](../../src/MainResults/TOBQMC.lean#L59) (Theorem 1): for a network under the standard assumptions that is T-quartet-nonanomalous, independent gene trees from the NMSC, a binary tree `T` that does not refine the tree of blobs and `ε > 0`, there are a binary refinement `B` of the tree of blobs and `K` such that, with probability at least `1 - ε`, the quartet score of `B` on the first `k` gene trees exceeds that of `T` for all `k ≥ K`.
- [`TreeOfBlobs.theorem1_optimal`](../../src/MainResults/TOBQMC.lean#L71) (Theorem 1, "put simply"): almost surely, for all large `k`, every optimal solution of Weighted Quartet Consensus on the first `k` gene trees refines the tree of blobs.
- [`TreeOfBlobs.theorem2`](../../src/MainResults/TOBQMC.lean#L85) (Theorem 2): on a binary level-1 network, for any refinement `B` of the tree of blobs, applying the oracle for treelikeness to a disjoint cover of four-taxon subsets around each edge of `B`, and contracting the edges where it answers non-treelike on one of them, returns the tree of blobs.
- [`TreeOfBlobs.consistency`](../../src/MainResults/TOBQMC.lean#L96) (§4.3): for a binary level-1 network under the standard assumptions, T-quartet-nonanomalous, whose non-treelike 4-taxon sets have distinct concordance factors (assumption 6a), there are levels `α_k → 0` such that, for any `β > 0`, any selection of maximum likelihood topologies, any solver of Weighted Quartet Consensus and any disjoint covers, the method on `k` gene trees returns the tree of blobs with probability tending to one. The tests are TINNiK's star and cut tests.

### What the paper says in passing

- [`TreeOfBlobs.tobqmc_consistency_implementation`](../../src/MainResults/TOBQMC.lean#L122): the same holds for the implementation, which tests a selection of four-taxon subsets around each edge that contains a disjoint cover, possibly depending on the data, and applies the star test to the minimizer only.
- [`TreeOfBlobs.tobqmc_refinement_not_displayed`](../../src/MainResults/TOBQMC.lean#L145): a binary tree that refines the tree of blobs of a binary level-1 network, and that no parent choice displays.

### The supplement's claims that fail

- [`TreeOfBlobs.tobqmc_not_printedPiMin_pos`](../../src/MainResults/TOBQMC.lean#L151), [`TreeOfBlobs.tobqmc_not_exists_printedError_lt`](../../src/MainResults/TOBQMC.lean#L157) (E22): on a network whose tree of blobs is not a star, the margin `π_min` of supplement Lemma 4 is not positive, and no weights meet the printed hypothesis of that lemma.
- [`TreeOfBlobs.tobqmc_not_lemma2Converse`](../../src/MainResults/TOBQMC.lean#L164) (E23): the converse of supplement Lemma 2 is false with `N|Y` the induced subnetwork, as the supplement defines it. A binary level-1 network has a star as its tree of blobs, while the network induced on four taxa is treelike.
- [`TreeOfBlobs.tobqmc_not_supplementLemma7`](../../src/MainResults/TOBQMC.lean#L167) (E25): on a binary level-2 network, a set of four taxa around a false edge meets both conditions of supplement Lemma 7, and it is treelike.
- [`TreeOfBlobs.tobqmc_not_supplementTheorem1`](../../src/MainResults/TOBQMC.lean#L170) (E25): supplement Theorem 1 is false for a binary network of arbitrary level, by a counterexample at `ρ = 1`.
- [`TreeOfBlobs.tobqmc_not_theorem2_without_level_one`](../../src/MainResults/TOBQMC.lean#L173) (E25): with the hypothesis on the level left out, the oracle on the four-taxon subsets of a disjoint cover keeps a false edge.
- [`TreeOfBlobs.tobqmc_tendsto_tobqmcT3_rho_one`](../../src/MainResults/TOBQMC.lean#L176) (E25): on that level-2 network at `ρ = 1`, the method with the T3 option returns the tree of blobs with probability tending to zero, at all levels.
- [`TreeOfBlobs.tobqmc_forGenericParams_tendsto`](../../src/MainResults/TOBQMC.lean#L185) (E25): on the same network at `ρ = 0`, for generic parameters, all the assumptions of [`TreeOfBlobs.consistency`](../../src/MainResults/TOBQMC.lean#L96) but the level hold, and the method returns the tree of blobs with probability tending to zero.

### The sources it cites

- [`TreeOfBlobs.ane_proposition12`](../../src/MainResults/TOBQMC.lean#L204) (Ané et al. 2024, Proposition 12): under the common inheritance model with `ρ = 1`, a network with weak parameters is not anomalous on any four taxa. The source states it for a 4-taxon binary metric network.
- [`TreeOfBlobs.huber_theorem5_1`](../../src/MainResults/TOBQMC.lean#L209) (Huber et al. 2025, Theorem 5.1): a split `A|B` is the split of a cut edge exactly when it is trivial, or `a₁a₂|b₁b₂` is the split of a cut edge of the network induced on these taxa for all distinct `a₁, a₂ ∈ A` and `b₁, b₂ ∈ B`. The paper's Lemma 2 is the forward direction.
- [`TreeOfBlobs.dinhBanos_theorem1`](../../src/MainResults/TOBQMC.lean#L216) (Dinh, Baños 2025, Theorem 1): under the source's conditions (6) and (7), a tree that the network does not display has a higher expected ASTRAL score than both displayed trees.
- [`TreeOfBlobs.kaneTao_theorem1`](../../src/MainResults/TOBQMC.lean#L223) (Kane, Tao 2017, Theorem 1): for a finite collection `X` of finite sets, the number of triples `(A₁, A₂, A)` in `X` with `A` the disjoint union of `A₁` and `A₂` is at most `|X|^(3/p)`, with `p = log₃(27/4)`. This is the bound behind the exponent `1.726` of ASTRAL-III's running time.

## Palomar

No submission to [Palomar](https://github.com/mathlib-initiative) is planned. The files in [`palomar/`](palomar) are kept in case that changes, and the Comparator configuration is useful on its own.

- [`palomar/comparator.json`](palomar/comparator.json) runs Comparator on the main theorems above, with [`src/MainResults/TOBQMC.lean`](../../src/MainResults/TOBQMC.lean) as both the challenge and the solution. From the repository root, after `lake build`:

  ```sh
  scripts/check_kernels.sh papers/TOBQMC/palomar/comparator.json
  ```

  This checks the closure of each theorem under Lean's kernel, NanoDa and con-ron, and rejects `sorryAx`. It does not compare a separate statement file with a proof, which is what Palomar's Challenge and Solution are for. `lake comparator`, `leanexport` and `con-ron` come from the toolchain under `lake env`.
- [`palomar/formalization.yaml`](palomar/formalization.yaml) is the entry's metadata, valid against the schema it names: the paper, the sources it cites, the statements aligned to the `TreeOfBlobs.*` theorems of the module, and its fidelity section, which lists every divergence from the paper.

A submission would still need:

1. A Challenge that imports only Mathlib, with the definitions that its statements use in a block of its own, and the bridges from them to the library's definitions. The last such file, written for three papers of the collection together, is in the git history at `f838ea4`, with the scripts that kept its block equal to the library's and generated the Solution.
2. A Solution that restates those theorems and proves them from the libraries, and a `comparator.json` that names the two modules.
3. These files at the root of the repository that holds the paper, with `formalization.yaml` pointing at the new modules.

## Results of the audit

The numbers are those of [`REPORT.md`](REPORT.md), which gives each finding with its location, the paper's sentence, a Lean counterexample where there is one, and the repair. They are numbered across the papers of the collection.

- **Errors.** The supplement's Lemma 7 and Theorem 1 are false at level 2, by an explicit network (E25). Its Lemma 2's converse is false with `N|Y` the induced subnetwork, as it defines it, and holds under the gloss in its proof (E23). Its claim that positive edge lengths exclude the centroid is false (E28). The margin of its Lemma 4 is vacuous as printed (E22). None of these affects a result of main v5, which states Theorem 2 at level 1, keeps only the forward direction of Lemma 2 and excludes the centroid on T-quartets; supplement Lemma 4 holds with a repaired margin.
- **Gaps.** E18–E22, E24, E39, all repaired. Only E22 changes a statement. In E21, the consistency claim needs the tests to be correct on treelike subsets that the tree of blobs does not resolve; the paper does not treat these, and they are proved here.
- **Missing hypotheses.** Supplement Lemma 8 needs a nontrivial blob (E26, agreed with the user).
- **Redundant hypotheses.** All the refinement hypotheses of Lemma 4 except [`TOBQMC.RefinesBlob`](../../src/TOBQMC/Level1.lean#L40); `B` binary in Corollary 1; for the T3 option, 6a in full and 6b given condition 4.
- **Use of cited results.** The paper cites the statement of TINNiK's Theorem 4 for what is a step of its proof (E21), and its description of ASTRAL's search space is exact for ASTRAL-I's default only. Huber et al.'s Theorem 5.1 and Ané et al.'s exchangeability are used correctly.
- **Loose sentences and misprints.** Binary lifting isn't `O(1)` per query, though the total stands (E69), and E70–E74, most on running times, none affecting a result. A formula for `α` in §1.2 conflicts with the later one (E27). ASTRAL-III drops a constant (E83). Typos (E34).
- **Proofs.** They follow the paper's arguments, except the departures in [Section 7 of the report](REPORT.md#7-departures-from-the-papers-proofs), each with what the paper does, what Lean does and why. Some repair a gap or an error: Lemma 4 (E19), Corollary 1 (E20), the consistency claim (E21) and supplement Lemma 4 (E22, E24). A few aren't forced, and say so: Lemma 1, the suppression skipped in Lemma 4, supplement Lemma 8, and three proofs of cited results. [`docs/route_differences.tsv`](../../docs/route_differences.tsv) records every difference of route.

## Credits

- Requested and supervised by The-Anh Vu-Le, who chose the paper and its version, agreed to the corrections of its statements, and decided the library's boundary and the project's layout. **No person has reviewed the proofs.**
- Source audit and first foundations by Codex; statements, proofs, audit and documents by Claude (Opus 5.5) in Claude Code, with sub-agents, following the [formalize-math-paper](https://github.com/vltanh/formalize-math-paper) procedure.
- Made on 2026-10-27 and from 2026-10-31 to 2026-11-01, with the other papers of the collection; Claude's rounds used 85 sub-agents for the whole collection, at most 11 at once. [`docs/CREDITS.md`](../../docs/CREDITS.md) has the details.

## Related work

From [Section 10 of the report](REPORT.md#10-the-paper-in-the-literature).

- History: Gusfield et al. 2007's decomposition theory is the source of the tree of blobs. Allman et al. 2023 showed that the tree of blobs is identifiable from gene quartet distributions with no assumption on the level, and TINNiK made that an algorithm with a consistency theorem; TOB-QMC uses its tests. Huber et al. 2025 characterize cut-edge splits by quarnets, and TOB-QMC's Lemma 2 is the forward direction.
- Concurrent: ECToBlob (first version 2026-05-31; TOB-QMC's was 2025-11-06) proves the same result, that an optimum of the quartet criterion refines the tree of blobs, and contracts edges by another test. Its authors say that the two groups pursued the outline independently.
- Since: the paper appeared in Genome Research in 2026, whose text we could not read. Dai and Molloy (WABI 2026) reconstruct level-1 blobs from a tree of blobs, using TOB-QMC's Theorem 2 and its Lemma 4. We found no erratum, and no work that settles treelikeness beyond level 1.
- Formalizations: no other formalization of the paper was found. The project imports the public [lean4-phylogenetics](https://github.com/vltanh/lean4-phylogenetics).

## What's next

An open question is whether, beyond level 1, every false edge of a refinement of the tree of blobs has a non-treelike four-taxon set around it: the formal justification of TOB-QMC stops at level 1, and the supplement's claim for disjoint covers fails at level 2 (E25). That failure is proved at `ρ = 1` and for generic parameters at `ρ = 0`, and other values of `ρ` remain. [Section 11 of the report](REPORT.md#11-whats-next) has these and the simpler arguments that the formalization found.

## Building

From the repository root:

```sh
lake exe cache get
lake build
lake build MainResults.TOBQMC                                                    # this paper's main theorems
lake build Phylogenetics                                                         # the audit reads the whole library
lake env lean -DautoImplicit=false -DmaxSynthPendingDepth=3 scripts/Audit.lean   # axioms and dependencies
python3 scripts/route_check.py check docs/paper_routes.tsv --accept docs/route_differences.tsv
python3 scripts/check_layers.py                                                  # imports between units
scripts/check_kernels.sh papers/TOBQMC/palomar/comparator.json                   # Lean's kernel, NanoDa, con-ron
```

- Toolchain: Lean and Mathlib `v4.36.0-rc1` ([`lean-toolchain`](../../lean-toolchain), [`lake-manifest.json`](../../lake-manifest.json)). The library [lean4-phylogenetics](https://github.com/vltanh/lean4-phylogenetics) is required by commit, `f1a3592`, in [`lakefile.toml`](../../lakefile.toml).
- After adding a module, run `python3 scripts/gen_audit.py`; a new folder also needs a unit in [`scripts/layers.toml`](../../scripts/layers.toml). After moving declarations, run `python3 scripts/linkify_docs.py` to update the documents' links.
- [`.github/workflows/lean_action_ci.yml`](../../.github/workflows/lean_action_ci.yml) builds the project and the whole library, runs the audit, the route check and the check of imports between units, and checks that the generated files, the documents' links and the Markdown tables are current. The kernels aren't in CI, so run them by hand.
- [`docs/CONFIGURATION.md`](../../docs/CONFIGURATION.md) records the versions, the decisions and what "line N" means for the paper.

## Layout

The paper's code is the unit [`TOBQMC`](../../src/TOBQMC) of [`scripts/layers.toml`](../../scripts/layers.toml), which lists what it may import: [`Basic`](../../src/Basic), Allman et al. 2023, TINNiK, and the sources Ané et al. 2024, Huber et al. 2025, Kane, Tao 2017, Dinh, Baños 2025 and Mitchell et al. 2019. [`scripts/check_layers.py`](../../scripts/check_layers.py) checks every import against it. ECToBlob, written independently at the same time, isn't among them.

### [`src/TOBQMC/`](../../src/TOBQMC)

| Module | Content |
| --- | --- |
| [`Lemma1`](../../src/TOBQMC/Lemma1.lean) | Lemma 1: displayed quartet trees and 4-blobs |
| [`WQC`](../../src/TOBQMC/WQC.lean) | §4.1–4.2: quartet-based species tree methods give a refinement of the tree of blobs (Definition 1, equations (1)–(4), Lemma 3, supplement Lemma 4, Theorem 1, the ASTRAL corollary) |
| [`Astral`](../../src/TOBQMC/Astral.lean) | §4.2: the tree that ASTRAL's dynamic program returns refines the tree of blobs |
| [`Level1`](../../src/TOBQMC/Level1.lean) | §4.3: false positives in a refinement, with a linear number of tests, for level-1 networks (Lemma 2, Lemma 4, Corollary 1, Theorem 2, 3-fix-1-alter) |
| [`Level1CF`](../../src/TOBQMC/Level1CF.lean) | §4.3: concordance factors of induced cut-edge splits at level 1 |
| [`Consistency`](../../src/TOBQMC/Consistency.lean) | §4.3: statistical consistency for level-1 networks |
| [`ConsistencyT3`](../../src/TOBQMC/ConsistencyT3.lean) | §4.3: statistical consistency with the T3 option |
| [`BipartitionSearch`](../../src/TOBQMC/BipartitionSearch.lean) | §4.3: the bipartition search (Algorithm 2) combined with 3-fix-1-alter |
| [`BipartitionSearchT3`](../../src/TOBQMC/BipartitionSearchT3.lean) | §4.3: the bipartition search combined with 3-fix-1-alter, with the T3 option |
| [`Implementation`](../../src/TOBQMC/Implementation.lean) | The implementation of the tests, with the star test on the minimizer only |
| [`DisplayedRefinement`](../../src/TOBQMC/DisplayedRefinement.lean) | A refinement of the tree of blobs need not be a display tree |
| [`Counts`](../../src/TOBQMC/Counts.lean) | Operation counts |
| [`RunningTime`](../../src/TOBQMC/RunningTime.lean) | The running times, with what they rest on |
| [`SupplementLemma2`](../../src/TOBQMC/SupplementLemma2.lean) | Supplement, Lemma 2: the converse is false |
| [`SupplementLemma4Margin`](../../src/TOBQMC/SupplementLemma4Margin.lean) | Supplement, Lemma 4: the margin as printed vanishes |
| [`SupplementLemma8`](../../src/TOBQMC/SupplementLemma8.lean) | Supplement, Lemma 8: a reticulation at the boundary of a blob |
| [`SupplementLevelTwo`](../../src/TOBQMC/SupplementLevelTwo.lean) | Supplement, Lemma 7 and Theorem 1: false at level 2 |
| [`LevelOneDigraph`](../../src/TOBQMC/LevelOneDigraph.lean) | The two definitions of a level-1 network agree on binary networks |

[`src/MainResults/TOBQMC.lean`](../../src/MainResults/TOBQMC.lean) has the main theorems, and belongs to the same unit.

### The sources in [`src/External/`](../../src/External)

| Folder | Content |
| --- | --- |
| [`AneEtAl2024`](../../src/External/AneEtAl2024) | Ané et al. 2024: exchangeability under the NMSC, Proposition 12, rule 2 of Section 3.3 |
| [`HuberEtAl2025`](../../src/External/HuberEtAl2025) | Huber et al. 2025, Theorem 5.1 |
| [`DinhBanos2025`](../../src/External/DinhBanos2025) | Dinh, Baños 2025, Theorem 1 and Corollary 2 |
| [`KaneTao2017`](../../src/External/KaneTao2017) | Kane, Tao 2017: a bound on partitioning clusters |
| [`MitchellAllmanRhodes2019`](../../src/External/MitchellAllmanRhodes2019) | Mitchell, Allman, Rhodes 2019: hypothesis testing near singularities and boundaries. This paper uses the T3 test, `T3Test.lean` |

### The units it builds on

- [`src/AllmanEtAl2023/`](../../src/AllmanEtAl2023) and [`src/TINNiK/`](../../src/TINNiK): the papers of the collection that TOB-QMC builds on, with their own folders, [`../AllmanEtAl2023/`](../AllmanEtAl2023/README.md) and [`../TINNiK/`](../TINNiK/README.md). This paper uses Allman et al.'s reduction and CF-detectability, and TINNiK's tests and T3 option.
- [`src/Basic/`](../../src/Basic), what the papers share beyond the library ([its README](../../src/Basic/README.md)). This paper uses `Defs` (the algorithm and the standing assumptions), `Testing/*` (the hypothesis tests on quartet counts), `LocalObjective`, `RhoOne`, `LCA`, `BridgeDFS`, `InducedSplits`, `TreeCounts`, `UnitMetric`, `FinNetwork`, and the facts on blobs of level-1 networks: `Level1Blobs`, `Wedge` and `Level1Blocks`, which Lemma 4 uses, and `Level1CF`, the strictly largest concordance factor of E21.
- The library [lean4-phylogenetics](https://github.com/vltanh/lean4-phylogenetics): networks, trees, quartets, the coalescent and the network multispecies coalescent.

## License

Apache-2.0: [LICENSE](../../LICENSE). Code adapted from [lean4-phylogenetics](https://github.com/vltanh/lean4-phylogenetics) (Apache-2.0) keeps its notice in each file's header.
