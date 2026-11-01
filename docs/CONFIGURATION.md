# Formalization configuration

Recorded 2026-10-27 (America/Chicago).

## Sources of record

- ECToBlob: Rhodes, Allman, Ané and Baños, *Statistical inference of the Tree of Blobs of a phylogenetic network from quartet concordance factors*, [bioRxiv v1](https://www.biorxiv.org/content/10.64898/2026.05.28.728501v1). The bioRxiv API lists v1 dated 2026-05-31. The author's publications page lists the work as to appear in SIAM Journal on Life Sciences; no replacement version has been selected.
- TOB-QMC: Dai, Han and Molloy, *Quartet-based species tree methods enable fast and consistent tree of blobs reconstruction under the network multispecies coalescent*, [bioRxiv v5](https://www.biorxiv.org/content/10.1101/2025.11.05.686850v5), posted 2026-05-15. A later [Genome Research publication](https://doi.org/10.1101/gr.282203.126) exists. The user first selected the journal, then explicitly authorized bioRxiv fallback if the journal could not be retrieved. Publisher and Europe PMC access checks established that only the journal abstract was available, so the fallback applies. No equivalence of the journal and preprint proofs is claimed.
- TINNiK: Allman, Baños, Mitchell and Rhodes, *TINNiK: inference of the tree of blobs of a species network under the coalescent model*, [Algorithms for Molecular Biology 19, 23 (2024)](https://doi.org/10.1186/s13015-024-00266-2).

Downloads and working inventories are kept under ignored `notes/`; they are not distributed with the library. The TINNiK publisher XML includes TeX equations, but is not the authors' original TeX source.

No author TeX source exists for any of the three papers, so `docs/paper_routes.tsv` is written by hand from these sources.

The user supplied `ectob_supp.pdf` (6 pages) and `tob-qmc_supp.pdf` (43 pages) from Downloads on 2026-10-27. Both have been read and hashed. The ECToBlob supplement contains simulation appendices A/B. The TOB-QMC supplement is internally dated February 26, 2026 and uses some result numbers that differ from main v5. Its precise version linkage is unconfirmed; the internal date alone does not establish that a later supplement exists. Its mathematical claims are inventoried separately with a provisional crosswalk to the main text.

## Repository and toolchain

- New local repository; branch `formalize/tree-of-blobs`. No draft existed. The first rounds of work were made with Codex; `CREDITS.md` has the rounds.
- Lean and Mathlib `v4.36.0-rc1`, Mathlib commit `625d8914199bc567cca9b91f90e8e5afafa5ae51`.
- Lean `v4.36.0-rc2` was released on 2026-10-27, but the corresponding Mathlib release tag returned 404 during setup. Thus rc1 is the newest verified matched pair.
- Palomar's current minimum is `v4.35.0-rc2`; the selected toolchain exceeds it.
- Mathlib and Verso rc1 share `plausible` and `Cli`; both revisions match.
- The initial dependency cache was copied into this checkout from an existing local checkout at the same pinned release. No symlinks or shared mutable build directory are used.
- Compilation is enabled. Sub-agents check files against private snapshots of the build outputs; only the main session runs `lake build`.
- Libraries: `Basic` (the definitions specific to the three papers, and general results on their way to the library), `External`, and one library for each paper. They import the library `Phylogenetics` (see below). Each is a directory with no root module: the globs in `lakefile.toml` reach its modules, also those that nothing imports. Additional proof dependencies will be pinned only after checking their scope and statements.

## Scope and provenance

The requested target is all mathematical results of the three papers, their cited proof dependencies, and source/statement/proof-route audits. Empirical performance claims must be distinguished from mathematical theorems. No result is counted as formalized merely because an abstract implication or a placeholder module builds.

Cited results that are out of reach may become explicit hypotheses named after their sources, as the invoked skill permits. Results proved in these papers may not be replaced with such hypotheses.

The public `lean4-phylogenetics` and `lean4-camus` projects were surveyed for prior work and reusable foundations. A tree-only hierarchy kernel from the former was adapted with explicit provenance in [ADAPTED_SOURCES.md](ADAPTED_SOURCES.md). Selected network-independent finite Kingman modules were subsequently extracted; [COALESCENT_SOURCES.md](COALESCENT_SOURCES.md) records their scope and incomplete absorption/PMF work. The level-1 network syntax and NMSC modules were not imported; they cannot stand for arbitrary networks. CAMUS has not been incorporated.

Default license: Apache-2.0. Local Git identity: The-Anh Vu-Le. Public authorship and maintainership remain to be confirmed before publication. AI systems are credited as tools, not human authors.

No push, remote repository creation, publication, Palomar preflight, submission, or registration is authorized. Local work and milestone commits are authorized by the invoked skill.

## The library `Phylogenetics`

On 2026-10-31 the user asked this project to import the library [`lean4-phylogenetics`](https://github.com/vltanh/lean4-phylogenetics), which holds definitions and general results, in place of its own general layer. What the papers prove stays here: `src/Basic/Defs.lean` has the algorithms and the standing assumptions, `src/Basic/Testing/` and `src/Basic/ForMathlib/` have the hypothesis tests and the analysis behind them, the papers' libraries have their results, and `src/External/` has what they cite from other papers. `src/Basic/General.lean` has general results that can move to the library.

The library is required by commit, from GitHub (`lakefile.toml`). `lake build` builds only the modules of the library that this project imports; the audit reads all of them, so it also needs `lake build Phylogenetics`.

## Palomar

On 2026-10-31 the user decided that Palomar is not a target. `src/MainResults.lean` states and proves the main theorems, by hand, and imports the libraries of the three papers and what they use, not the statement libraries that still hold `sorry`; it replaces `Challenge.lean` and `Solution.lean`, and `scripts/gen_solution.py` and `scripts/sync_challenge_defs.py` are gone. This gives up Palomar's rule that the Challenge imports only Mathlib, deliberately: the user may not submit, and does not care about the limit on its length, and the copy of the definitions was about 800 lines that had to be kept equal to the library's.

[`palomar/`](../palomar) keeps `comparator.json` and `formalization.yaml`, and says what a submission would still need. Comparator runs on `MainResults` as both challenge and solution, so it checks the main theorems under Lean's kernel and NanoDa, and rejects `sorryAx`; it no longer compares a separate statement file with a proof. `scripts/check_kernels.sh` runs it and con-ron, Palomar's three kernels.

## Authorized corrections

The user explicitly approved using the closed probability simplex for TINNiK maximum-likelihood estimation while keeping the generating distribution strictly positive. The open-domain counterexample and correction are checked in `scripts/BoundaryCheck.lean`. On 2026-10-27 the user also explicitly approved restricting ECToBlob Theorem 8.2 to generic numerical parameters, outside the exceptional sets in both converse clauses of Assumption 1 for every induced quartet. This is a correction to the printed theorem, justified by E10 in REPORT.md, not an inferred standing hypothesis. The model-level generic claim and the pointwise parameter restriction are kept separate in Lean (`ECToBlob.theorem8_2_generic` and `ECToBlob.theorem8_2`).

The user also approved retaining only the valid forward implication of supplied TOB-QMC supplement Lemma 2: a resolved quartet on the full tree of blobs implies that its induced subnetwork is treelike. The false converse is documented with a five-taxon sunlet counterexample (E23). The main v5 already distinguishes these two kinds of quartet.

The user approved requiring a nontrivial blob in supplied TOB-QMC supplement Lemma 8 (E26). A singleton internal blob in a binary tree refutes the unrestricted statement. This correction uses the standard network convention that sinks are labelled leaves, explicit in main v5.

## Correction agreed on 2026-10-31

The user agreed to the correction E11 of REPORT.md: the Cauchy transform is extended continuously at `p = 1`, where the printed formula is undefined, and the Cauchy and CBC variants of ECToBlob's Theorem 8.2 carry the hypothesis of positive alternatives on T1-strict quartets, on the strength of a counterexample that an independent reader checked. A finite value of the transform at `p = 1`, as in the authors' R code, was the alternative, and was not chosen.

## Readings

The tests are read as implemented in the sources: gene trees are binary in Theorem 8.2, which covers the NMSC and the Displayed Tree model when all displayed trees are binary, and the small-count procedures of MSCquartets are not modelled.

## Publishing

The repository is public. The user first asked, on 2026-10-31, for everything to be pushed to a private repository, and has since made it public. The formalization is on branch `formalize/tree-of-blobs`; the working notes, `NEXT.md` and `notes/`, are ignored by git and are not in the repository. No Palomar preflight, submission or registration is authorized.
