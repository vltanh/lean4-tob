# Allman et al. 2023: the tree of blobs of a species network, identifiability, in Lean

[![CI](https://github.com/vltanh/lean4-tob/actions/workflows/lean_action_ci.yml/badge.svg)](https://github.com/vltanh/lean4-tob/actions/workflows/lean_action_ci.yml)

A Lean 4 formalization of E. S. Allman, H. Baños, J. D. Mitchell, J. A. Rhodes, *The tree of blobs of a species network: identifiability under the coalescent*, [J. Math. Biol. 86 (2023), 10](https://doi.org/10.1007/s00285-022-01838-9), read in the PMC author manuscript and the [arXiv TeX](https://arxiv.org/abs/2205.03466). The tree of blobs of a phylogenetic network is what remains when its reticulate parts, the blobs, are contracted. The paper proves that under the network multispecies coalescent, for generic parameters, the reduced unrooted tree of blobs of a binary species network is identifiable from the distribution of gene quartet topologies, with no assumption on the level of the network. On four taxa, the concordance factor detects a 4-blob (Theorem 1). On more taxa, the B-quartet Inference Rule (Theorem 2) finds all B-quartets from the concordance factors (Theorem 3), and from these the tree is recovered (Theorem 4). The formalization is unconditional: no result of the literature is assumed, and there is no `sorry` or `axiom`. No person has reviewed the proofs.

This paper is part of the collection of four formalizations described in [`../../README.md`](../../README.md). Its audit is [`REPORT.md`](REPORT.md).

## What is proved

- Every numbered result of the paper, on its own objects: Lemmas 1, 2, 3; Theorems 1, 2, 3, 4; Corollaries 1, 2; Proposition 1 and its converse. The proofs follow the paper's, except the departures listed in [the report's Section 7](REPORT.md#7-departures-from-the-papers-proofs). Lemma 2 is proved for a connected subnetwork, which its proof and all its uses assume (E55).
- What the paper says in passing, where it is mathematics and true: the remarks listed in the [README of `src/AllmanEtAl2023/`](../../src/AllmanEtAl2023/README.md), including the outline of an algorithm in Section 5 and the examples of Figures 1, 2, 3 and 9. [Section 9 of the report](REPORT.md#9-not-formalized) lists what remains: two statements that are false, each with its counterexample, and Baños's bound on all level-1 networks, which nothing uses.
- The cited results that the proofs use: the Splits Equivalence Theorem (Semple, Steel 2003), in the library lean4-phylogenetics ([`Phylogenetics.SplitsEquivalence.xTree_unique`](https://github.com/vltanh/lean4-phylogenetics/blob/f1a3592dee6e3f7d5e7a68a0695ac457de23d2de/Phylogenetics/Tree/SplitsEquivalence.lean#L604), the uniqueness half); Theorem 2 of Rhodes 2020, in [`src/External/Rhodes2020/`](../../src/External/Rhodes2020); and what the paper quotes from Baños 2019, Sayyari and Mirarab 2016 and Semple and Steel 2005 ([the report's Section 2](REPORT.md#2-results-from-prior-work-and-how-the-paper-uses-them)). Nothing is assumed.
- The forms of the results that TINNiK, TOB-QMC and ECToBlob use, stated on subgraphs of a fixed network and by domination.
- `lake build` passes with no warnings, and there is no `sorry`, `axiom`, `native_decide` or `implemented_by`. [`scripts/Audit.lean`](../../scripts/Audit.lean) checks every declaration of the project and of the library it uses, including private and generated ones, against [`propext`](https://leanprover-community.github.io/mathlib4_docs/Init/Core.html#propext), [`Classical.choice`](https://leanprover-community.github.io/mathlib4_docs/Init/Prelude.html#Classical.choice) and [`Quot.sound`](https://leanprover-community.github.io/mathlib4_docs/Init/Prelude.html#Quot.sound). [Building](#building) says how to run it.

## The main results

[`src/MainResults/AllmanEtAl2023.lean`](../../src/MainResults/AllmanEtAl2023.lean) states 12 theorems in the namespace `TreeOfBlobs`, each with a docstring in plain terms, and keeps the paper's hypotheses. They are on the paper's own objects: [`IsBinaryNetwork`](../../src/AllmanEtAl2023/Definitions.lean#L61), its Definition 1; `Trd`, the reduced unrooted tree of blobs; [`cfTriple`](../../src/AllmanEtAl2023/Concordance.lean#L66), the concordance factor `CF_abcd`; and `ForGenericParams N P`, "for generic numerical parameters", `P` outside a null set.

- [`TreeOfBlobs.allman_lemma1`](../../src/MainResults/AllmanEtAl2023.lean#L55) (Lemma 1): on four taxa, the semidirected network has either exactly one 4-blob, with an unresolved reduced tree of blobs and the taxa a B-quartet, or exactly two 3-blobs, with a resolved tree and a T-quartet. Its other blobs without a taxon are 2-blobs.
- [`TreeOfBlobs.allman_theorem1`](../../src/MainResults/AllmanEtAl2023.lean#L76) (Theorem 1, CF-detectability of 4-blobs): on four taxa, for generic parameters, the reduced tree of blobs has the topology `ab|cd` exactly when the concordance factor is strictly `(ab|cd)`-cut, and is unresolved exactly when it is non-cut.
- [`TreeOfBlobs.allman_corollary1`](../../src/MainResults/AllmanEtAl2023.lean#L86) (Corollary 1): on a network on any number of taxa, for generic parameters, [`readTopology`](../../src/AllmanEtAl2023/Concordance.lean#L293), a function of the concordance factor alone, reads the topology of the reduced tree of blobs of each induced 4-taxon network.
- [`TreeOfBlobs.allman_proposition1`](../../src/MainResults/AllmanEtAl2023.lean#L93), [`TreeOfBlobs.allman_proposition1_converse`](../../src/MainResults/AllmanEtAl2023.lean#L101) (Proposition 1 and its converse): for all parameters, the concordance factor of a 4-taxon network whose reduced tree of blobs is `ab|cd` is a triple `(p, q, q)` with `0 < p, q < 1` and `p + 2q = 1`, and every such triple arises on such a network.
- [`TreeOfBlobs.allman_lemma2_needs_connected`](../../src/MainResults/AllmanEtAl2023.lean#L111) (Lemma 2 needs a word that it lacks): without a connected subnetwork, the hypotheses of Lemma 2 hold and no blob of the network is determined by `S`. The paper's proof and all its uses assume the word (E55).
- [`TreeOfBlobs.allman_theorem2`](../../src/MainResults/AllmanEtAl2023.lean#L120) (Theorem 2, the B-quartet Inference Rule): if `{a, b, c, d}` and `{b, c, d, e}` are B-quartets, and one of `{a, b, c, e}`, `{a, b, d, e}`, `{a, c, d, e}` is, on its induced network, a T-quartet with `a, e` separated, or a B-quartet, then all three are B-quartets.
- [`TreeOfBlobs.allman_theorem3`](../../src/MainResults/AllmanEtAl2023.lean#L130) (Theorem 3): for generic parameters, the sets that CF-detectability and the Inference Rule give from the concordance factors, [`CFInferred`](../../src/AllmanEtAl2023/Concordance.lean#L319), are exactly the B-quartets.
- [`TreeOfBlobs.allman_theorem4`](../../src/MainResults/AllmanEtAl2023.lean#L137) (Theorem 4): one function `F`, chosen before the network, recovers the reduced unrooted tree of blobs from the distribution of gene quartet topologies, for generic parameters on every binary network.
- [`TreeOfBlobs.allman_blobDistance_not_identifiable`](../../src/MainResults/AllmanEtAl2023.lean#L152) (Section 5, the distance between blobs isn't identifiable): on the network `𝒩(k)⁺` of Proposition 1, for every `k ≥ 1`, whose reduced tree of blobs is `ab|cd`, with stem of length `ε₀ > 0`, a nondegenerate segment of concordance factors arises at `ε₀` and at every `ε′` near it, with other lengths `M`.
- [`TreeOfBlobs.allman_banos_range`](../../src/MainResults/AllmanEtAl2023.lean#L162) (before Proposition 1, Baños's range): `𝒩(1)⁺` is level-1, its reduced tree of blobs is `ab|cd`, and over all parameters the first entry of its concordance factor takes exactly the values in `(1/6, 1)`. Baños's further bound on all level-1 networks isn't proved.
- [`TreeOfBlobs.allman_outline_consistent`](../../src/MainResults/AllmanEtAl2023.lean#L172) (Section 5, the outline of an algorithm): for any test that is right on each set of four taxa with probability tending to one, and an exact tree builder, the steps of the outline return the tree of blobs on `m` independent gene trees with probability tending to one.

## Palomar

No submission to Palomar is planned. The files in [`palomar/`](palomar) are kept in case that changes, and the Comparator configuration is useful on its own.

- [`palomar/comparator.json`](palomar/comparator.json) runs Comparator on the 12 main theorems, with [`MainResults.AllmanEtAl2023`](../../src/MainResults/AllmanEtAl2023.lean) as both the challenge and the solution module, permitting only [`propext`](https://leanprover-community.github.io/mathlib4_docs/Init/Core.html#propext), [`Quot.sound`](https://leanprover-community.github.io/mathlib4_docs/Init/Prelude.html#Quot.sound) and [`Classical.choice`](https://leanprover-community.github.io/mathlib4_docs/Init/Prelude.html#Classical.choice), with NanoDa enabled.
- [`palomar/formalization.yaml`](palomar/formalization.yaml) is the entry's metadata, valid against the schema it names: the paper, the sources it cites, the statements aligned to the `TreeOfBlobs.*` theorems, and its fidelity section, which lists every divergence from the paper. [`REPORT.md`](REPORT.md) has the details.

From the repository root, after `lake build`:

```sh
scripts/check_kernels.sh papers/AllmanEtAl2023/palomar/comparator.json
```

This checks the closure of each theorem under Lean's kernel and NanoDa, through `lake comparator`, and under con-ron, and rejects `sorryAx`. It does not compare a separate statement file with a proof, which is what Palomar's Challenge and Solution are for. `lake comparator`, `leanexport` and `con-ron` come from the toolchain under `lake env`.

A submission would still need:

1. A Challenge that imports only Mathlib, with the definitions that its statements use in a block of its own, and the bridges from them to the library's definitions.
2. A Solution that restates those theorems and proves them from the libraries, and a `comparator.json` that names the two modules.
3. These files at the root of the repository that holds the paper, with `formalization.yaml` pointing at the new modules.

## Audit summary

[Section 3 of the report](REPORT.md#3-errors-and-gaps-in-the-paper) gives each item with its location, the paper's sentence, a Lean counterexample where there is one, and the repair.

- **Errors.** No numbered result fails, reading a subnetwork as connected. Read literally, Lemma 2 does, and its proof and all its uses assume the word (E55). A side remark in the proof of Proposition 1 fails for some `ε` (E57).
- **Missing hypotheses.** Lemma 2 needs `M` connected (E55). The remark on edge lengths between trivial blobs holds for internal edges (E64).
- **Gaps.** The proofs have gaps that are filled here (E56, E58–E62). None changes a statement.
- **Smaller points.** Some misprints are in the PMC manuscript only (E57, E63, E66), and "`k` or `M` varied" is loose (E65).
- **Redundant hypotheses.** Among others, the binary hypothesis in Theorem 2, Lemma 3 and the combinatorial part of Theorem 3 ([Section 5](REPORT.md#5-redundant-hypotheses)).
- **Use of cited results.** Baños 2019, Semple and Steel 2005 and Rhodes 2020 are used correctly. Baños 2019 has a misprint in the proof of its Proposition 7 (E81).
- **Proofs.** They follow the paper's arguments, except the departures in [the report's Section 7](REPORT.md#7-departures-from-the-papers-proofs), each with what the paper does, what Lean does and why. Statement (b) of Theorem 1 also removes a stem, which the paper's step needs (E58). Statement (a) of Theorem 1, Theorem 2 and Baños's claim depart where it isn't forced, and say so. Lemma 1, the remark on the distance between blobs, the outline of Section 5 and other remarks have no printed argument to follow. [`docs/route_differences.tsv`](../../docs/route_differences.tsv) records every difference of route.

## Credits

- Requested and supervised by The-Anh Vu-Le, who chose the papers, decided the library's boundary and the project's layout, and published the repository. **No person has reviewed the proofs.** Independent agents reviewed the statements and compared the proofs with the paper.
- Codex made the source audit and first foundations of the collection, on 2026-10-27. Claude (Opus 5.5) in Claude Code, with sub-agents, wrote the statements, proofs, audit and documents, following the [formalize-math-paper](https://github.com/vltanh/formalize-math-paper) procedure.
- Made from 2026-10-31 to 2026-11-01, with the rest of the collection: first the results that TINNiK cites, then the paper as a primary one, from the evening of 2026-10-31. The collection used 85 sub-agents in all, to commit `282215c`. [`docs/CREDITS.md`](../../docs/CREDITS.md) has the details.

## Related work

From [the report's Section 10](REPORT.md#10-the-paper-in-the-literature).

- No other formalization of this paper was found. This project imports the public [lean4-phylogenetics](https://github.com/vltanh/lean4-phylogenetics). [lean4-adr11](https://github.com/vltanh/lean4-adr11), by the same owner, formalizes Allman, Degnan, Rhodes 2011, which the paper cites, and isn't used here.
- Before: the paper's own account cites level-1 work (SNaQ, Baños 2019, NANUQ) and takes the tree of blobs from Gusfield et al. 2007, which is formalized separately, in [lean4-gusfield2007](https://github.com/vltanh/lean4-gusfield2007).
- Since: TINNiK (2024) made the outline of Section 5 an algorithm with a consistency theorem, and TOB-QMC and ECToBlob build on the paper's results; all three are in this collection. "Beyond level-1" (2025) extends tree of blobs identifiability to common inheritance and the displayed tree model. Huber et al. 2025 and Frohn et al. 2025 give the tree of blobs from exact quarnets. Allman et al. 2024 settle the identifiability of edge lengths at level 1.
- We found no erratum, correction or counterexample to the paper, and no later work that restates Lemma 2.

## What's next

The natural next steps are to extend the generic results beyond independent inheritance, `ρ = 0`, where "Beyond level-1" has reached `ρ = 1` for binary networks, and to ask which lengths of cut edges are identifiable above level 1, which line 252 leaves to future work. [The report's Section 11](REPORT.md#11-whats-next) has these and the simpler arguments that the formalization found.

## Building

From the repository root:

```sh
lake exe cache get
lake build
lake build MainResults.AllmanEtAl2023                                            # this paper's main theorems
lake build Phylogenetics                                                         # the audit reads the whole library
lake env lean -DautoImplicit=false -DmaxSynthPendingDepth=3 scripts/Audit.lean   # axioms and dependencies
python3 scripts/route_check.py check docs/paper_routes.tsv --accept docs/route_differences.tsv
python3 scripts/check_layers.py                                                  # imports between units
scripts/check_kernels.sh papers/AllmanEtAl2023/palomar/comparator.json           # Lean's kernel, NanoDa, con-ron
```

- The audit, the route check and the check of imports cover the whole collection, this paper included.
- Toolchain: Lean and Mathlib `v4.36.0-rc1` ([`lean-toolchain`](../../lean-toolchain), [`lake-manifest.json`](../../lake-manifest.json)). The library lean4-phylogenetics is required by commit, `f1a3592`, in [`lakefile.toml`](../../lakefile.toml).
- After adding a module, run `python3 scripts/gen_audit.py`. After moving declarations, run `python3 scripts/linkify_docs.py` to update the documents' links.
- [`docs/CONFIGURATION.md`](../../docs/CONFIGURATION.md) records the versions, the decisions and what "line N" means.

## Layout

- [`src/AllmanEtAl2023/`](../../src/AllmanEtAl2023), in the namespace [`AllmanEtAl2023`](../../src/AllmanEtAl2023). [Its README](../../src/AllmanEtAl2023/README.md) lists the results, every module and the departures that remain. Its modules fall into these groups:
  - the paper's definitions, on its objects (`Definitions`, `InducedNetwork`, `BlobDefinitions`, `Concordance`, `NetworkNk`);
  - the language of subgraphs of a fixed network and cuts by domination, where Lemma 2, the cycle of Lemma 3 and the rule live and which the later papers use (`SubgraphBlobs`, `CutOrder`, `CycleLemma`, `Reduction`, [`Basic`](../../src/Basic)), with bridges to it from the paper's objects (`Bridges`, `InducedTransfer`, `BlobsPass`) and trees and `T_rd` on four taxa (`TreeSuppression`, `TrdTree`, `TreeIso`, `TrdFour`);
  - Theorem 1: statement (a) and the concordance factors through Definition 6, then statement (b) with the deleted networks, the 2-blob step and generic parameters (`Theorem1a`, `Theorem1b` and the modules they use);
  - the numbered results and the claims their proofs use (`Theorem1` to `Theorem4`, `Lemma1` to `Lemma3`, `Corollary1`, `Corollary2`, `Proposition1`, `Lemma2Counterexample`, `Claims`);
  - what the paper says in passing, with its figures (`InPassing`, `BlobDistance`, `Figures` and others); the outline of Section 5 (`Algorithm`); and [`CFDetectable`](../../src/AllmanEtAl2023/Basic.lean#L55), for the later papers.
- [`src/MainResults/AllmanEtAl2023.lean`](../../src/MainResults/AllmanEtAl2023.lean): the 12 main theorems.
- The sources in [`src/External/`](../../src/External), each with a README: [`Rhodes2020/`](../../src/External/Rhodes2020), the quartet metrization (Theorem 2), for the outline of Section 5. The Splits Equivalence Theorem, for [`AllmanEtAl2023.theorem4_iso`](../../src/AllmanEtAl2023/Theorem4.lean#L134), is in the library, in [`Phylogenetics.Tree.SplitsEquivalence`](https://github.com/vltanh/lean4-phylogenetics/blob/f1a3592dee6e3f7d5e7a68a0695ac457de23d2de/Phylogenetics/Tree/SplitsEquivalence.lean).
- From [`src/Basic/`](../../src/Basic), whose [README](../../src/Basic/README.md) lists its modules: [`Basic.Defs`](../../src/Basic/Defs.lean) (with [`Basic.Testing.Defs`](../../src/Basic/Testing/Defs.lean) and [`Basic.Testing.Combining`](../../src/Basic/Testing/Combining.lean), which it imports), [`Basic.Testing.IID`](../../src/Basic/Testing/IID.lean), [`Basic.General`](../../src/Basic/General.lean), [`Basic.NMSCChain`](../../src/Basic/NMSCChain.lean) and [`Basic.ForMathlib.Analysis.AnalyticZeroSet`](../../src/Basic/ForMathlib/Analysis/AnalyticZeroSet.lean).
- The library [lean4-phylogenetics](https://github.com/vltanh/lean4-phylogenetics), for networks, trees, quartets, the coalescent and the network multispecies coalescent.
- [`scripts/layers.toml`](../../scripts/layers.toml) lists what this unit may import: [`Basic`](../../src/Basic) and `Rhodes2020`, besides Mathlib and the library. [`scripts/check_layers.py`](../../scripts/check_layers.py) checks every import against it.
- [`palomar/`](palomar), the files for a possible Palomar entry, and [`REPORT.md`](REPORT.md), the audit.

## License

Apache-2.0: [`LICENSE`](../../LICENSE).
