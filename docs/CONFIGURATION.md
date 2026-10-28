# Formalization configuration

Recorded 2026-10-27 (America/Chicago).

## Sources of record

- ECToBlob: Rhodes, Allman, Ané and Baños, *Statistical inference of the Tree of Blobs of a phylogenetic network from quartet concordance factors*, [bioRxiv v1](https://www.biorxiv.org/content/10.64898/2026.05.28.728501v1). The bioRxiv API lists v1 dated 2026-05-31. The author's publications page lists the work as to appear in SIAM Journal on Life Sciences; no replacement version has been selected.
- TOB-QMC: Dai, Han and Molloy, *Quartet-based species tree methods enable fast and consistent tree of blobs reconstruction under the network multispecies coalescent*, [bioRxiv v5](https://www.biorxiv.org/content/10.1101/2025.11.05.686850v5), posted 2026-05-15. A later [Genome Research publication](https://doi.org/10.1101/gr.282203.126) exists. The user first selected the journal, then explicitly authorized bioRxiv fallback if the journal could not be retrieved. Publisher and Europe PMC access checks established that only the journal abstract was available, so the fallback applies. No equivalence of the journal and preprint proofs is claimed.
- TINNiK: Allman, Baños, Mitchell and Rhodes, *TINNiK: inference of the tree of blobs of a species network under the coalescent model*, [Algorithms for Molecular Biology 19, 23 (2024)](https://doi.org/10.1186/s13015-024-00266-2).

Downloads and working inventories are kept under ignored `notes/`; they are not distributed with the library. The TINNiK publisher XML includes TeX equations, but is not the authors' original TeX source.

The user supplied `ectob_supp.pdf` (6 pages) and `tob-qmc_supp.pdf` (43 pages) from Downloads on 2026-10-27. Both have been read and hashed. The ECToBlob supplement contains simulation appendices A/B. The TOB-QMC supplement is internally dated February 26, 2026 and uses some result numbers that differ from main v5. Its precise version linkage is unconfirmed; the internal date alone does not establish that a later supplement exists. Its mathematical claims are inventoried separately with a provisional crosswalk to the main text.

## Repository and toolchain

- New local repository; branch `formalize/tree-of-blobs`. No draft existed.
- Lean and Mathlib `v4.36.0-rc1`, Mathlib commit `625d8914199bc567cca9b91f90e8e5afafa5ae51`.
- Lean `v4.36.0-rc2` was released on 2026-10-27, but the corresponding Mathlib release tag returned 404 during setup. Thus rc1 is the newest verified matched pair.
- Palomar's current minimum is `v4.35.0-rc2`; the selected toolchain exceeds it.
- Mathlib and Verso rc1 share `plausible` and `Cli`; both revisions match.
- The initial dependency cache was copied into this checkout from an existing local checkout at the same pinned release. No symlinks or shared mutable build directory are used.
- Compilation is enabled. Only the root agent runs Lake builds.
- Libraries: `Basic`, `External`, and one library for each paper. Additional proof dependencies will be pinned only after checking their scope and statements.

## Scope and provenance

The requested target is all mathematical results of the three papers, their cited proof dependencies, source/statement/proof-route audits, and local Palomar packaging. Empirical performance claims must be distinguished from mathematical theorems. No result is counted as formalized merely because an abstract implication or a placeholder module builds.

Cited results that are out of reach may become explicit hypotheses named after their sources, as the invoked skill permits. Results proved in these papers may not be replaced with such hypotheses.

The public `lean4-phylogenetics` and `lean4-camus` projects were surveyed for prior work and reusable foundations. A tree-only hierarchy kernel from the former was adapted with explicit provenance in [ADAPTED_SOURCES.md](ADAPTED_SOURCES.md). Its level-1 network definitions and coalescent modules were not imported; they cannot stand for arbitrary networks. CAMUS has not been incorporated.

Default license: Apache-2.0. Local Git identity: The-Anh Vu-Le. Public authorship and maintainership remain to be confirmed before publication. AI systems are credited as tools, not human authors.

No push, remote repository creation, publication, Palomar preflight, submission, or registration is authorized. Local work and milestone commits are authorized by the invoked skill.

## Authorized corrections

The user explicitly approved using the closed probability simplex for TINNiK maximum-likelihood estimation while keeping the generating distribution strictly positive. The open-domain counterexample and correction are checked in `scripts/BoundaryCheck.lean`. On 2026-10-27 the user also explicitly approved restricting ECToBlob Theorem 8.2 to generic numerical parameters, outside the exceptional sets in both converse clauses of Assumption 1 for every induced quartet. This is a correction to the printed theorem, justified by E7 in REPORT.md, not an inferred standing hypothesis. The model-level generic claim and the pointwise parameter restriction must be kept separate in Lean.

The user also approved retaining only the valid forward implication of supplied TOB-QMC supplement Lemma 2: a resolved quartet on the full tree of blobs implies that its induced subnetwork is treelike. The false converse is documented with a five-taxon sunlet counterexample (E11). The main v5 already distinguishes these two kinds of quartet.
