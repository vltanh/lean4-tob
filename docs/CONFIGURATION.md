# Formalization configuration

Recorded 2026-10-27, and brought up to date on 2026-11-01 (America/Chicago).

## Sources of record

- ECToBlob: Rhodes, Allman, Ané and Baños, *Statistical inference of the Tree of Blobs of a phylogenetic network from quartet concordance factors*, [bioRxiv v1](https://www.biorxiv.org/content/10.64898/2026.05.28.728501v1). The bioRxiv API lists v1 dated 2026-05-31. The author's publications page lists the work as to appear in SIAM Journal on Life Sciences; no replacement version has been selected.
- TOB-QMC: Dai, Han and Molloy, *Quartet-based species tree methods enable fast and consistent tree of blobs reconstruction under the network multispecies coalescent*, [bioRxiv v5](https://www.biorxiv.org/content/10.1101/2025.11.05.686850v5), posted 2026-05-15. A later [Genome Research publication](https://doi.org/10.1101/gr.282203.126) exists. The user first selected the journal, then explicitly authorized bioRxiv fallback if the journal could not be retrieved. Publisher and Europe PMC access checks established that only the journal abstract was available, so the fallback applies. No equivalence of the journal and preprint proofs is claimed.
- TINNiK: Allman, Baños, Mitchell and Rhodes, *TINNiK: inference of the tree of blobs of a species network under the coalescent model*, [Algorithms for Molecular Biology 19, 23 (2024)](https://doi.org/10.1186/s13015-024-00266-2).
- Allman et al. 2023: Allman, Baños, Mitchell and Rhodes, *The tree of blobs of a species network: identifiability under the coalescent*, [J. Math. Biol. 86, 10 (2023)](https://doi.org/10.1007/s00285-022-01838-9), read in the PMC author manuscript NIHMS1884071 (PMC10062380) and the arXiv TeX.
- Gusfield et al. 2007: Gusfield, Bansal, Bafna and Song, *A decomposition theory for phylogenetic networks and incompatible characters*, [J. Comput. Biol. 14, 1247-1272 (2007)](https://doi.org/10.1089/cmb.2006.0137), read in the PMC author manuscript (PMC2581772), and, for the symbols that its plain text loses, in an [author's copy](https://people.eecs.berkeley.edu/~yss/Pub/decomposition.pdf) on Yun Song's page, made from a DVI file on 2008-01-19, with the same words apart from moved floats, footnotes and hyphenation. That copy isn't the journal's typeset text.

Downloads, working inventories and notes are private, and aren't in this repository. [`sources.json`](sources.json) has the hashes of the texts that the line numbers refer to, and of the later sources that were read. The TINNiK publisher XML includes TeX equations, but is not the authors' original TeX source. The journal's text of Allman et al. 2023 and of Gusfield et al. 2007 wasn't reachable, so the findings on them are about the authors' versions: [`REPORT.md`](REPORT.md) marks those that may not apply to the journal's text.

No author TeX source exists for ECToBlob, TOB-QMC, TINNiK or Gusfield et al. 2007, so their rows of `docs/paper_routes.tsv` are written by hand from these sources. Those of Allman et al. 2023 are checked against `route_check.py extract` on the arXiv TeX.

### Line numbers in the docstrings

The docstrings locate a passage by the lines of a text of the paper. The texts aren't distributed, so a line number is a locator only. Those of ECToBlob and of TOB-QMC's supplement can be reproduced with the command below, and those of TOB-QMC's main text are in its PDF.

| Paper | "Line" means |
| --- | --- |
| ECToBlob | a line of `pdftotext -layout` run on the bioRxiv v1 PDF (hash in `docs/sources.json`): "the paper's text, lines 588-627" |
| TOB-QMC | a line number printed in the margin of the bioRxiv v5 PDF: "embedded lines 384-385", "v5, line 421". In the supplement, a line of `pdftotext -layout`: "the supplement's text, lines 560-575" |
| TINNiK | a line of the plain text of the publisher's XML (PMC11539473), one line per paragraph: "TINNiK's text, line 194" |
| Allman et al. 2023 | a line of the plain text of the PMC page (PMC10062380), one line per paragraph: "the PMC text, line 149" |
| Gusfield et al. 2007 | a line of the plain text of the PMC page (PMC2581772), one line per paragraph: "line 342". The misprints in symbols were read in the author's copy above |
| NANUQ | a line of the plain text of arXiv v1 |
| Legried et al. 2021 | a line of `pdftotext -layout` run on the copy on NSF PAR (hash in `docs/sources.json`) |

The other sources are located by page, section or equation.

The user supplied `ectob_supp.pdf` (6 pages) and `tob-qmc_supp.pdf` (43 pages) from Downloads on 2026-10-27. Both have been read and hashed. The ECToBlob supplement contains simulation appendices A/B. The TOB-QMC supplement is internally dated February 26, 2026 and uses some result numbers that differ from main v5. Its precise version linkage is unconfirmed; the internal date alone does not establish that a later supplement exists. Its mathematical claims are inventoried separately with a provisional crosswalk to the main text.

## Repository and toolchain

- Public repository [`vltanh/lean4-tob`](https://github.com/vltanh/lean4-tob); branch `main`, named `formalize/tree-of-blobs` until 2026-11-04. No draft existed. The first rounds of work were made with Codex; `CREDITS.md` has the rounds.
- Layout: the Lean code is in `src/`, with `srcDir` in `lakefile.toml`, and the documents other than the `README` in `docs/`. The files for a possible Palomar submission are in `palomar/`, and the checks in `scripts/`.
- Lean and Mathlib `v4.36.0-rc1`, Mathlib commit `625d8914199bc567cca9b91f90e8e5afafa5ae51`.
- Lean `v4.36.0-rc2` was released on 2026-10-27, but the corresponding Mathlib release tag returned 404 during setup. Thus rc1 is the newest verified matched pair.
- Palomar's current minimum is `v4.35.0-rc2`; the selected toolchain exceeds it.
- Mathlib and Verso rc1 share `plausible` and `Cli`; both revisions match.
- The initial dependency cache was copied into this checkout from an existing local checkout at the same pinned release. No symlinks or shared mutable build directory are used.
- Compilation is enabled. Sub-agents check files against private snapshots of the build outputs; only the main session runs `lake build`.
- Libraries: `Basic` (the definitions specific to the first three papers, and general results on their way to the library), `External`, and one library for each paper. They import the library `Phylogenetics` (see below). Each is a directory with no root module: the globs in `lakefile.toml` reach its modules, also those that nothing imports. Additional proof dependencies will be pinned only after checking their scope and statements.

## Scope and provenance

The requested target is all mathematical results of the five papers, their cited proof dependencies, and source/statement/proof-route audits. Empirical performance claims must be distinguished from mathematical theorems. No result is counted as formalized merely because an abstract implication or a placeholder module builds.

Cited results that are out of reach may become explicit hypotheses named after their sources, as the invoked skill permits. Results proved in these papers may not be replaced with such hypotheses. None has been needed: no result is assumed.

The public `lean4-phylogenetics` and `lean4-camus` projects were surveyed for prior work and reusable foundations. A tree-only hierarchy kernel from the former was adapted with explicit provenance in [ADAPTED_SOURCES.md](ADAPTED_SOURCES.md). Selected network-independent finite Kingman modules were subsequently extracted; [COALESCENT_SOURCES.md](COALESCENT_SOURCES.md) records their scope and incomplete absorption/PMF work. That survey's level-1 network syntax and NMSC modules weren't used, since they can't stand for arbitrary networks. The project now imports that library for what it holds (below), and the network coalescent on arbitrary networks, first written here, has moved there. CAMUS has not been incorporated.

License: Apache-2.0. Git identity: The-Anh Vu-Le. AI systems are credited as tools, not human authors.

## The library `Phylogenetics`

On 2026-10-31 the user asked this project to import the library [`lean4-phylogenetics`](https://github.com/vltanh/lean4-phylogenetics), which holds definitions and general results, in place of its own general layer. What the papers prove stays here: `src/Basic/Defs.lean` has the algorithms and the standing assumptions, `src/Basic/Testing/` and `src/Basic/ForMathlib/` have the hypothesis tests and the analysis behind them, the papers' libraries have their results, and `src/External/` has what they cite from other papers. `src/Basic/General.lean` has general results that can move to the library.

The library is required by commit, `9948de9`, from GitHub (`lakefile.toml`). `lake build` builds only the modules of the library that this project imports; the audit reads all of them, so it also needs `lake build Phylogenetics`.

## Palomar

On 2026-10-31 the user decided that Palomar is not a target. `src/MainResults.lean` states and proves the main theorems, by hand, and imports the libraries of the five papers and what they use; it replaces `Challenge.lean` and `Solution.lean`, and `scripts/gen_solution.py` and `scripts/sync_challenge_defs.py` are gone. This gives up Palomar's rule that the Challenge imports only Mathlib, deliberately: the user may not submit, and does not care about the limit on its length, and the copy of the definitions was about 800 lines that had to be kept equal to the library's.

[`palomar/`](../palomar) keeps the files for a possible submission, and says what it would still need. Since 2026-11-04 it has one entry per paper, `palomar/<Paper>/`, with its `comparator.json` and `formalization.yaml`, and the main theorems are in one module per paper, `src/MainResults/<Paper>.lean`. Comparator runs on that module as both challenge and solution, so it checks the main theorems under Lean's kernel and NanoDa, and rejects `sorryAx`; it no longer compares a separate statement file with a proof. `scripts/check_kernels.sh` runs it and con-ron, Palomar's three kernels.

## Decisions of 2026-11-04

The user asked whether each paper should be its own package or repository, pulled in by git submodules, and then said "maybe that's not smart because they can share things!". Agreed ("yes to all"): one repository for now, organized so that each paper could become its own package. [`scripts/layers.toml`](../scripts/layers.toml) lists the units, a paper with its main results and the sources that only it uses, a source that several papers use, or `Basic`, and what each may import, and [`scripts/check_layers.py`](../scripts/check_layers.py) checks it in CI; what two papers share moved to `src/Basic/`. The audit has one report per paper, in [`reports/`](reports). Then the user asked for one Palomar entry per paper: `palomar/<Paper>/`, on `src/MainResults/<Paper>.lean`. If a paper ever moves to a repository of its own, Lake requires it by git and commit, not a submodule.

## Authorized corrections

The user explicitly approved using the closed probability simplex for TINNiK maximum-likelihood estimation while keeping the generating distribution strictly positive. The open-domain counterexample is `TINNiK.not_exists_generatingCutModel_maximizer`, in `src/TINNiK/Statistics/OpenCutModel.lean`. On 2026-10-27 the user also explicitly approved restricting ECToBlob Theorem 8.2 to generic numerical parameters, outside the exceptional sets in both converse clauses of Assumption 1 for every induced quartet. This is a correction to the printed theorem, justified by E10 in [`reports/ECToBlob.md`](reports/ECToBlob.md), not an inferred standing hypothesis. The model-level generic claim and the pointwise parameter restriction are kept separate in Lean (`ECToBlob.theorem8_2_generic` and `ECToBlob.theorem8_2`).

The user also approved retaining only the valid forward implication of supplied TOB-QMC supplement Lemma 2: a resolved quartet on the full tree of blobs implies that its induced subnetwork is treelike. The false converse is documented with a five-taxon sunlet counterexample (E23). The main v5 already distinguishes these two kinds of quartet.

The user approved requiring a nontrivial blob in supplied TOB-QMC supplement Lemma 8 (E26). A singleton internal blob in a binary tree refutes the unrestricted statement. This correction uses the standard network convention that sinks are labelled leaves, explicit in main v5.

## Correction agreed on 2026-10-31

The user agreed to the correction E11 of [`reports/ECToBlob.md`](reports/ECToBlob.md): the Cauchy transform is extended continuously at `p = 1`, where the printed formula is undefined, and the Cauchy and CBC variants of ECToBlob's Theorem 8.2 carry the hypothesis of positive alternatives on T1-strict quartets, on the strength of a counterexample that an independent reader checked. A finite value of the transform at `p = 1`, as in the authors' R code, was the alternative, and was not chosen.

## Decisions of 2026-11-01

Of Section 9 of [`REPORT.md`](REPORT.md), the user said: "leave only empirical and wrong stuff"; of cited results, "if they are cited but unused then we can just leave them out"; and "anything private should just go to the private notes".

The main session of the formalization chose the rest: each false statement is listed with its counterexample in Lean, with a list of what stays open, and the results left out aren't listed. One theorem, [`TreeOfBlobs.gusfield_theorem10Printed_multiple_false_of_search`](../src/MainResults.lean), has a finite computation as a visible hypothesis, which Lean's kernel hasn't completed. Two separate programs by the same author, not in the repository, and `#eval` support it, and it's labelled conditional wherever it's stated. No other theorem depends on it.

## Readings

The readings of each paper are in Section 6 of its report in [`reports/`](reports), and those that ECToBlob, TOB-QMC and TINNiK share in Section 6 of [`REPORT.md`](REPORT.md). The tests are read as implemented in the sources: gene trees are binary in Theorem 8.2, which covers the NMSC and the Displayed Tree model when all displayed trees are binary, and the small-count procedures of MSCquartets are not modelled.

## Publishing

The repository is public. The user first asked, on 2026-10-31, for everything to be pushed to a private repository, and then made it public. The formalization is on branch `main` (`formalize/tree-of-blobs` until 2026-11-04, when the user asked to clean it up as `main`); the working notes are not in the repository. A push needs the user's go-ahead. No Palomar preflight, submission or registration is authorized.
