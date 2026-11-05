# The tree of blobs of a phylogenetic network, in Lean

[![CI](https://github.com/vltanh/lean4-tob/actions/workflows/lean_action_ci.yml/badge.svg)](https://github.com/vltanh/lean4-tob/actions/workflows/lean_action_ci.yml)

Lean 4 formalizations of four papers that serve one problem: inferring the tree of blobs of a phylogenetic network. Each paper has a folder of its own in [`papers/`](papers), with a front page, an audit of the paper against the formalization, and the files of a Palomar entry. [`docs/REPORT.md`](docs/REPORT.md) is an overview of the field and its literature.

## The problem

A phylogenetic network on a set of taxa is a finite directed acyclic graph with a root that reaches every vertex, whose sinks are the taxa. Its reticulations, the vertices with more than one parent, stand for hybridization, gene flow or recombination. A blob is a maximal connected subgraph without cut edges. Contracting every blob to a vertex gives a tree, and suppressing its vertices of degree two gives the tree of blobs. Its splits are the splits of the taxa by the cut edges of the network. The tree of blobs shows the parts of the history that are tree-like and the places where reticulation happened, and leaves out what happened inside each blob. The level of a blob is its number of reticulation edges minus its number of reticulation vertices. Earlier methods that infer a whole network from quartets, such as SNaQ and NANUQ, assume level 1.

The data are gene trees, one per locus. Under the network multispecies coalescent (NMSC), each gene tree forms by coalescence inside the network, and the concordance factor of four taxa is the distribution of the three unrooted gene tree topologies on them. Allman, Baños, Mitchell and Rhodes (2023) proved that the quartet concordance factors determine the reduced unrooted tree of blobs, for generic parameters, with no bound on the level. The methods that followed estimate the concordance factors from a sample of gene trees, decide by hypothesis tests on sets of four taxa which splits are cut edges, and are consistent: they return the tree of blobs with probability tending to one as the number of gene trees grows. Later methods for the inside of the blobs, such as NANUQ⁺ and the level-1 blob reconstruction of Dai and Molloy, take the tree of blobs as input.

The idea of a blob is older, and combinatorial. Gusfield, Bansal, Bafna and Song, *A decomposition theory for phylogenetic networks and incompatible characters*, [J. Comput. Biol. 14 (2007), 1247–1272](https://doi.org/10.1089/cmb.2006.0137), studied networks with recombination that derive a given set of binary sequences. Their Decomposition Theorem gives such a network whose blobs correspond to the non-trivial connected components of the incompatibility graph of the sites, and so exposes "a maximal embedded tree structure". They then ask whether a network with the fewest recombination nodes can always be taken fully decomposed, give sufficient conditions, and show that in general it can't. Allman et al. 2023 and TOB-QMC cite the paper for the tree of blobs, and no proof here uses it. It is formalized separately, in [lean4-gusfield2007](https://github.com/vltanh/lean4-gusfield2007), whose [report](https://github.com/vltanh/lean4-gusfield2007/blob/main/REPORT.md) is its audit.

## The papers

In the order of their first versions. The last line of each section links to the paper's front page, its audit and its Palomar entry.

### Allman, Baños, Mitchell, Rhodes 2023: identifiability

E. S. Allman, H. Baños, J. D. Mitchell, J. A. Rhodes, *The tree of blobs of a species network: identifiability under the coalescent*, [J. Math. Biol. 86 (2023), 10](https://doi.org/10.1007/s00285-022-01838-9).

- **The paper.** On four taxa, for generic parameters, the concordance factor determines the tree of blobs of the induced 4-taxon network: it has the topology `ab|cd` exactly when the concordance factor is strictly `(ab|cd)`-cut, and it is unresolved exactly when the concordance factor is non-cut (Theorem 1, Corollary 1: the CF-detectability of 4-blobs). A set of four taxa can be unresolved in the tree of blobs of the whole network, a B-quartet, while its induced network has a cut edge, which the paper calls "the main obstacle". The B-quartet Inference Rule (Theorems 2 and 3) identifies all B-quartets from the concordance factors, and for generic parameters one function, chosen before the network, then recovers the reduced unrooted tree of blobs from the gene quartet distribution (Theorem 4).
- **The formalization.** Every numbered result, on the paper's own objects, with the remarks, the outline of an algorithm in its Section 5 and the examples of its Figures 1, 2, 3 and 9. Lemma 2 needs its subnetwork to be connected, as all its uses are. The forms that the three later papers use are stated on subgraphs of a fixed network, in the same part.
- [Front page](papers/AllmanEtAl2023/README.md) · [Audit](papers/AllmanEtAl2023/REPORT.md) · [Palomar entry](papers/AllmanEtAl2023/palomar)

### TINNiK (Allman, Baños, Mitchell, Rhodes 2024): an algorithm

E. S. Allman, H. Baños, J. D. Mitchell, J. A. Rhodes, *TINNiK: inference of the tree of blobs of a species network under the coalescent model*, [Algorithms Mol. Biol. 19 (2024), 23](https://doi.org/10.1186/s13015-024-00266-2).

- **The paper.** An algorithm from the identifiability result. It judges a set of four taxa a B-quartet when the star test does not reject at level `β` or the cut test rejects at level `α`, with the T3 test as an option; these tests build on Mitchell, Allman, Rhodes 2019. It closes the judged sets under the B-quartet Inference Rule, and builds a tree from a quartet distance (Rhodes 2020) by neighbor joining. Theorem 4: for generic parameters on a binary network there are levels `α_m → 0` such that, for any `β > 0` and any exact tree builder, the algorithm on `m` gene trees returns the tree of blobs with probability tending to one.
- **The formalization.** Theorem 4, with the paper's levels and with the T3 test; the maximum likelihood estimates of its Appendix C.1, read on the closed simplex; Propositions 5 and 6, the limit law of the cut test and its density; neighbor joining in its Step 4; the algorithm with missing taxa; and the counts behind its running times.
- [Front page](papers/TINNiK/README.md) · [Audit](papers/TINNiK/REPORT.md) · [Palomar entry](papers/TINNiK/palomar)

### TOB-QMC (Dai, Han, Molloy 2026): quartet consensus, then contraction

J. Dai, Y. Han, E. K. Molloy, *Quartet-based species tree methods enable fast and consistent tree of blobs reconstruction under the network multispecies coalescent*, [bioRxiv 10.1101/2025.11.05.686850 v5](https://www.biorxiv.org/content/10.1101/2025.11.05.686850v5), with its supplement. Published in [Genome Research](https://doi.org/10.1101/gr.282203.126), whose text we could not read.

- **The paper.** Under the binary NMSC, on networks whose T-quartets are not anomalous, every optimal solution of Weighted Quartet Consensus refines the tree of blobs, almost surely for all large numbers of gene trees (Theorem 1), so quartet-based species tree methods such as TREE-QMC and ASTRAL give a refinement. On a binary level-1 network, an oracle for treelikeness on a disjoint cover of quartets around each edge of a refinement finds the edges to contract (Theorem 2). With TINNiK's tests on these quartets, a linear number per edge, the method is consistent for level-1 networks (§4.3).
- **The formalization.** Every numbered result; the consistency claim of §4.3; the claims of the supplement at level 1, and their failure at level 2; the T3 option; the implementation; ASTRAL's dynamic program, exact on its search space; and the counts behind the running times.
- [Front page](papers/TOBQMC/README.md) · [Audit](papers/TOBQMC/REPORT.md) · [Palomar entry](papers/TOBQMC/palomar)

### ECToBlob (Rhodes, Allman, Ané, Baños 2026): the same outline, at any level

J. A. Rhodes, E. S. Allman, C. Ané, H. Baños, *Statistical inference of the Tree of Blobs of a phylogenetic network from quartet concordance factors*, [bioRxiv 10.64898/2026.05.28.728501 v1](https://www.biorxiv.org/content/10.64898/2026.05.28.728501v1).

- **The paper.** Every tree maximizing the Maximum Quartet Support objective resolves the tree of blobs, for quartet probabilities with strict dominance across cut edges and exchangeability across them (Theorem 3.1). If `a₁a₂|b₁b₂` is a cut-edge split of the induced 4-taxon network for all `aᵢ ∈ Aᵢ`, `bᵢ ∈ Bᵢ`, then `A₁ ∪ A₂ | B₁ ∪ B₂` is a cut-edge split of the network (Theorem 4.1). The algorithm applies the T1 test to the bipartition, quadripartition or multipartition sets of quartets of an edge, combines the p-values under dependence, and contracts one step at a time. There are test levels, independent of the network, such that every variant of the algorithm, from any resolution of the tree of blobs, returns the tree of blobs with probability tending to one (Theorem 8.2). Remark 8.3 adapts the argument to strengthen the consistency results of NANUQ and TINNiK.
- **The formalization.** Every numbered result. Theorem 8.2 is proved under two corrections agreed with the maintainer: parameters meeting both directions of Assumption 1, and, for two of its variants, positive alternatives on quartets strictly in the T1 null. Also proved: what the paper says in passing, among it Remark 8.3, Remark 8.4 for binary networks with a counterexample on a non-binary one, and statements of its §10.
- [Front page](papers/ECToBlob/README.md) · [Audit](papers/ECToBlob/REPORT.md) · [Palomar entry](papers/ECToBlob/palomar)

## How the papers build on each other

- TINNiK turns Allman et al. 2023 into an algorithm. Its Theorem 4 rests on the CF-detectability of 4-blobs and on the B-quartet Inference Rule, which TINNiK numbers Theorems 1 and 2.
- TOB-QMC and ECToBlob follow one outline, concurrently and independently: an optimum of a quartet criterion refines the tree of blobs, and tests on quartets around each edge remove the false edges. Both cite Allman et al. 2023 and TINNiK. TOB-QMC applies TINNiK's tests with the levels of the proof of its Theorem 4. ECToBlob adapts Theorem 1 of Allman et al. 2023 for its Proposition 5.1. Neither formalization imports the other: what both use is in [`src/Basic/`](src/Basic).
- NANUQ (Allman, Baños, Rhodes 2019), a method for level-1 networks, is a cited source here. Its formalization uses the language of Allman et al. 2023 and TINNiK's T3 test, and ECToBlob's Remark 8.3 strengthens its consistency result, as it does TINNiK's.

The cited sources are proved in [`src/External/`](src/External), one folder per source, each with a README that says whether its source was read. Results of these sources that no proof here uses are left out.

| Source | What is proved | Cited by | Folder |
| --- | --- | --- | --- |
| Mitchell, Allman, Rhodes 2019 | Theorem 3.1 for the trinomial cut model; the limit laws and densities of the T3 and T1 tests (Propositions 4.1, 4.2, 5.1, 5.2) | TINNiK, TOB-QMC, ECToBlob | [`MitchellAllmanRhodes2019`](src/External/MitchellAllmanRhodes2019) |
| Rhodes 2020 | Theorem 2: the quartet distance is a tree metric with the same topology | TINNiK, Allman et al. 2023 | [`Rhodes2020`](src/External/Rhodes2020) |
| Allman, Baños, Rhodes 2019 (NANUQ) | Proposition 9; Theorem 36, corrected | ECToBlob, TINNiK, Allman et al. 2023 | [`AllmanBanosRhodes2019`](src/External/AllmanBanosRhodes2019) |
| Ané et al. 2024 | Exchangeability across a cut edge; Proposition 12; rule 2 of its Section 3.3 | TOB-QMC, ECToBlob | [`AneEtAl2024`](src/External/AneEtAl2024) |
| Huber et al. 2025 | Theorem 5.1, both directions | TOB-QMC | [`HuberEtAl2025`](src/External/HuberEtAl2025) |
| Dinh, Baños 2025 | Theorem 1 and Corollary 2 | TOB-QMC, ECToBlob | [`DinhBanos2025`](src/External/DinhBanos2025) |
| Kane, Tao 2017 | The bound of Theorem 1 | TOB-QMC, through ASTRAL-III | [`KaneTao2017`](src/External/KaneTao2017) |
| Legried et al. 2021 | Theorem 1 on quartets | ECToBlob | [`LegriedEtAl2021`](src/External/LegriedEtAl2021) |
| Studier, Keppler 1988 | Their Lemma fails at a polytomy; their theorem holds with polytomies, in the library | TINNiK | [`StudierKeppler1988`](src/External/StudierKeppler1988) |

Allman et al. 2023 is both a paper of the collection and a source of the three later papers. The standard definitions and results of phylogenetics, among them networks, trees and their splits, the network multispecies coalescent, Kingman's coalescent with Tavaré's formula, neighbor joining and ASTRAL's dynamic program, are in the library [lean4-phylogenetics](https://github.com/vltanh/lean4-phylogenetics), which this project imports. So is the Splits Equivalence Theorem of Semple, Steel 2003, whose uniqueness half Allman et al. 2023 uses ([`Phylogenetics.SplitsEquivalence.xTree_unique`](https://github.com/vltanh/lean4-phylogenetics/blob/f1a3592dee6e3f7d5e7a68a0695ac457de23d2de/Phylogenetics/Tree/SplitsEquivalence.lean#L604)).

## Status

- Every numbered result of the four papers is proved, as printed or in a corrected form that the paper's report records. The proofs follow the papers' arguments, except the departures listed in Section 7 of each report, each with its reason. No result of the literature is assumed. Statements that the audit finds false are refuted in Lean, and their true forms are proved.
- `lake build` passes with no warnings, and there is no `sorry`, `axiom`, `native_decide` or `implemented_by` in [`src/`](src). [`scripts/Audit.lean`](scripts/Audit.lean) checks every declaration of the project and of the library it uses, including private and generated ones, against Lean's three standard axioms, [`propext`](https://leanprover-community.github.io/mathlib4_docs/Init/Core.html#propext), [`Classical.choice`](https://leanprover-community.github.io/mathlib4_docs/Init/Prelude.html#Classical.choice) and [`Quot.sound`](https://leanprover-community.github.io/mathlib4_docs/Init/Prelude.html#Quot.sound).
- The main theorems are in [`src/MainResults/`](src/MainResults), one module per paper, in the namespace `TreeOfBlobs`, each with a docstring in plain terms. [`scripts/check_kernels.sh`](scripts/check_kernels.sh) checks the main theorems of each paper's Palomar entry under three kernels: Lean's and NanoDa, through Comparator, and con-ron.
- The route check ([`scripts/route_check.py`](scripts/route_check.py)) confirms that every proof uses the results that the paper's proof cites, except the differences recorded, each with its reason, in [`docs/route_differences.tsv`](docs/route_differences.tsv).
- No person has reviewed the proofs. Independent agents reviewed the statements against the papers, compared the proofs with the papers' and checked the audit's findings.

## The field

[`docs/REPORT.md`](docs/REPORT.md) is an overview of the research direction: the problem and its history, the four papers and how their results and methods relate, the literature before, alongside and since them, with the dates of the searches, the open directions that span the papers, and where the audit stands, with an index saying which report has each finding E1–E85.

## Credits

- Requested and supervised by The-Anh Vu-Le, who chose the papers, agreed to the corrections of the statements of ECToBlob, TOB-QMC and TINNiK, and decided the library's boundary and the project's layout. **No person has reviewed the proofs.**
- Source audit and first foundations by Codex; statements, proofs, audit and documents by Claude (Opus 5.5) in Claude Code, with sub-agents, following the [formalize-math-paper](https://github.com/vltanh/formalize-math-paper) procedure.
- Made on 2026-10-27 and from 2026-10-31 to 2026-11-01, and arranged as a collection of papers on 2026-11-04, when Gusfield et al. 2007 moved to [lean4-gusfield2007](https://github.com/vltanh/lean4-gusfield2007) ([`docs/CONFIGURATION.md`](docs/CONFIGURATION.md)). [`docs/CREDITS.md`](docs/CREDITS.md) has the details.

## Building

```sh
lake exe cache get
lake build
lake build Phylogenetics                                                         # the audit reads the whole library
lake env lean -DautoImplicit=false -DmaxSynthPendingDepth=3 scripts/Audit.lean   # axioms and dependencies
python3 scripts/route_check.py check docs/paper_routes.tsv --accept docs/route_differences.tsv
python3 scripts/check_layers.py                                                  # imports between units
scripts/check_kernels.sh                                                         # Lean's kernel, NanoDa, con-ron, every entry
scripts/check_kernels.sh papers/TINNiK/palomar/comparator.json                   # one entry
```

- Toolchain: Lean and Mathlib `v4.36.0-rc1` ([`lean-toolchain`](lean-toolchain), [`lake-manifest.json`](lake-manifest.json)).
- The library [lean4-phylogenetics](https://github.com/vltanh/lean4-phylogenetics) is required by commit, `f1a3592`, in [`lakefile.toml`](lakefile.toml).
- [`scripts/check_kernels.sh`](scripts/check_kernels.sh) uses `lake comparator`, `leanexport` and `con-ron`, under `lake env`. By default it checks each entry in `papers/*/palomar/comparator.json`; given configurations, it checks those. The last run, on 2026-11-04, took about 18 minutes for the four entries; an earlier run, of all the main theorems at once, measured 12.4 GB in its largest process.
- After adding a module, run `python3 scripts/gen_audit.py`; a new folder also needs a unit in [`scripts/layers.toml`](scripts/layers.toml). After moving declarations, run `python3 scripts/linkify_docs.py` to update the documents' links. `python3 scripts/check_md_tables.py README.md docs/*.md papers/*/*.md` checks the Markdown tables.
- [`docs/CONFIGURATION.md`](docs/CONFIGURATION.md) records the versions, the decisions and what "line N" means for each paper. [`docs/ADAPTED_SOURCES.md`](docs/ADAPTED_SOURCES.md) and [`docs/COALESCENT_SOURCES.md`](docs/COALESCENT_SOURCES.md) record adapted code.

## Layout

| Folder | Content |
| --- | --- |
| [`papers/`](papers) | One folder per paper, [`ECToBlob`](papers/ECToBlob), [`TOBQMC`](papers/TOBQMC), [`TINNiK`](papers/TINNiK), [`AllmanEtAl2023`](papers/AllmanEtAl2023), as the root of a repository of its own would be: [`README.md`](README.md), the front page; `REPORT.md`, the audit; `palomar/`, with `formalization.yaml` and `comparator.json`, for a Palomar submission, which isn't planned |
| [`src/MainResults/`](src/MainResults) | The main theorems, one module per paper, with those of the sources it cites; [`src/MainResults.lean`](src/MainResults.lean) imports the four |
| [`src/Basic/`](src/Basic) | What the papers share beyond the library: the algorithms and standing assumptions, the hypothesis tests, blobs of level-1 networks, networks given by tables, analysis for Mathlib. It imports no paper. [Its README](src/Basic/README.md) has the modules |
| [`src/AllmanEtAl2023/`](src/AllmanEtAl2023) | Allman et al. 2023, on the paper's own objects, and the forms for the later papers. [Its README](src/AllmanEtAl2023/README.md) lists results and modules |
| [`src/TINNiK/`](src/TINNiK) | TINNiK: Theorem 4, the T3 option, neighbor joining, missing taxa, the outline of Allman et al., counts, the test's statistics |
| [`src/TOBQMC/`](src/TOBQMC) | TOB-QMC: quartet consensus, Lemma 4 at level 1, consistency, the bipartition search, the implementation, running times, the supplement's lemmas |
| [`src/ECToBlob/`](src/ECToBlob) | ECToBlob: Sections 3 to 8, Remarks, §10, the displayed tree model, the framework on other tests |
| [`src/External/`](src/External) | The results that the papers cite, one folder per source, each with a README |
| [`docs/`](docs) | [`REPORT.md`](docs/REPORT.md), the overview of the field; [`CREDITS.md`](docs/CREDITS.md); [`CONFIGURATION.md`](docs/CONFIGURATION.md); the records of adapted code; the routes of the proofs, [`paper_routes.tsv`](docs/paper_routes.tsv) and [`route_differences.tsv`](docs/route_differences.tsv); [`sources.json`](docs/sources.json), the hashes of the texts read |
| [`scripts/`](scripts) | The audit, the route check, the check of the units, the kernels, and the checks of generated files, links and tables |

Each folder of [`src/`](src) is a Lean library of the same name, declared in [`lakefile.toml`](lakefile.toml).

### Units and their imports

[`scripts/layers.toml`](scripts/layers.toml) divides the code into units, each of which could be its own Lake package: [`Basic`](src/Basic), each paper with its main results and the sources that only it uses, and each source that several papers use. It lists the units that each unit may import, and [`scripts/check_layers.py`](scripts/check_layers.py) checks every import against it, and that the units form no cycle. CI runs it.

- [`Basic`](src/Basic) imports no paper. Of the sources, only NANUQ imports more than [`Basic`](src/Basic).
- Allman et al. 2023, then TINNiK, then NANUQ (Allman, Baños, Rhodes 2019), whose formalization uses the language of the two later papers and TINNiK's T3 test, then ECToBlob.
- TOB-QMC imports TINNiK, Ané et al. 2024, Huber et al. 2025, Kane, Tao 2017, Dinh, Baños 2025 and the T3 test of Mitchell et al. 2019. ECToBlob imports TINNiK, NANUQ, Legried et al. 2021 and the T3 test. The two were written independently, and neither imports the other: what both use is in [`Basic`](src/Basic).
- [`MainResults.lean`](src/MainResults.lean) imports the four papers, and nothing imports it.

`python3 scripts/check_layers.py --graph` prints the units, lowest first, with what each imports.

## GitHub configuration

[`.github/workflows/lean_action_ci.yml`](.github/workflows/lean_action_ci.yml) builds the project and the whole library, runs the audit, the route check and the check of imports between units, and checks that the generated files, the documents' links and the Markdown tables are current. It needs no settings. The three kernels aren't in CI, so run them by hand.

## License

Apache-2.0: [LICENSE](LICENSE). Code adapted from [lean4-phylogenetics](https://github.com/vltanh/lean4-phylogenetics) (Apache-2.0) keeps its notice in each file's header.
