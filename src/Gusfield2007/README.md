# Gusfield, Bansal, Bafna, Song 2007: a decomposition theory for phylogenetic networks and incompatible characters

Source: D. Gusfield, V. Bansal, V. Bafna, Y. S. Song, J. Comput. Biol. 14 (2007), 1247--1272. Read in the PMC author manuscript (PMC2581772). The journal's text wasn't reachable, so symbol-level readings rest on the manuscript alone.

"Line 342" in the docstrings means line 342 of the plain text of the PMC page, one line per paragraph. Symbols rendered as images are missing from that text.

The routes of the proofs are in `docs/paper_routes.tsv`, and their differences from the paper's in `docs/route_differences.tsv`.

The modules import Mathlib only, not the library `Phylogenetics`. The cited results are in `External/{SempleSteel2003, Gusfield1991, GusfieldEtAl2004, MyersGriffiths2003, HudsonKaplan1985, SongHein2005}`, and each of those READMEs says whether its source was read.

## Theorem 4

Theorem 4 is false with the printed definition of "efficient", because that definition omits the entry node of a blob (`theorem4_false_top`, `theorem4_false_small`). It is true with the entry node counted, up to two conventions and site-free arcs: `theorem4_entry` says that, for a fully decomposed network, `T′` is `T̄` exactly when the network has `Network.IsEfficientAtEntry`, `Network.RegularArcs` and `Network.DegreeCond`.

- The two conventions are a root of degree two and a recombination leaf (`theorem4Printed_false_rootDegreeTwo`, `theorem4Printed_false_recombLeaf`). Site-free arcs are an error of their own, since line 97 allows them (`theorem4_false_siteFree`).
- With the printed definition, `theorem4`, `theorem4_splits` and `theorem4_iff` state exactly what is needed.
- The hypotheses can be met, for every `M` with at least three rows (`exists_realization`).
- Not proved: that the modification of line 329 for `IsEfficientAtEntry` keeps the number of recombinations (`exists_isEfficientAtEntry` is existence only), and a root at an arbitrary node of `T̄` in line 299 (only the neighbour of a row is covered).

Section 4.2's characterization is false too (`mostTreeLikePrinted_false`); `treeness_le_and_eq_iff` is the true form. The head of `Uniqueness.lean` has the whole account.

## Modules

| Module | Contents |
| --- | --- |
| `Defs` | the definitions the statements mention, and the readings of the paper |
| `Basic` | `G_S(M) = G(M + S)`, arcs, paths and reachability, embeddings, isomorphisms, recombinants, `R` and `R_S` under renaming |
| `Blobs` | line 139, the two paths lemma, `T′` is a tree, making blobs node-disjoint (line 135) |
| `NetworkOps` | where a label comes from, the four-gamete test, trimming to the rows, moving a recombination node, `PreNet` |
| `BlobFacts` | sites off a blob, tree arcs, tops and exits of a blob, sides of a tree arc in `T′` |
| `Surgery` | the restriction to a component, and Lemma 5 |
| `Structure` | Section 3.1: Lemmas 1, 2, Theorem 2, Corollary 1 |
| `TreeFacts`, `TreeCuts`, `TreeContract` | sides of edges of a tree, cut functions, a perfect phylogeny with every internal edge labelled |
| `SuperCharacters` | Sections 3.2, 3.3: Lemmas 3, 4, existence and uniqueness of `T̄` |
| `DecompNet`, `InflateNet`, `GlueNet`, `TBarFrame` | removing arcs and leaves, a new leaf, the network that replaces a central node, gluing, `T̄` as a frame |
| `Decomposition` | Sections 2.3, 3.4, 3.5: Theorems 1, 3 and the converses |
| `Hub` | the modification of line 330, and turning an arc out of the root round |
| `ExplicitNetworks`, `FiniteNets`, `CounterexampleNets` | networks from lists of numbers, checked by the kernel; the networks of Sections 3.7 and 4.2 |
| `Uniqueness` | Sections 3.7, 4.2: Theorem 4, line 329, treeness |
| `Realizability` | the hypotheses of Theorem 4 can be met |
| `Conjectures` | Section 5.1: the conjectures, the computation of `F` and `F_S` |
| `Histories`, `Parsimony` | the labels of a network generated one at a time (`Gen`); mutation trees as networks, re-rooting (Section 4.1) |
| `SufficientConditions` | Section 5.2: Theorems 5 to 10, Corollaries 2, 3 |
| `GalledNetworks` | line 554: non-degenerate galled networks |
| `Examples`, `Components`, `LabelSearch` | the matrices of the figures, bookkeeping, a verified search for lower bounds on `R` |
| `Figure1`, `Figure5`, `Figure6`, `Figure8`, `EvenRows`, `MdMatrix`, `Mosaic` | the numbers of the figures, Footnote 2, `M_d` |
| `TimeOrdered`, `Figure10` | Section 5.3.3: time-ordered trees and ordered SPR, Figure 10, `R¹(M_d) ≤ 3d` |
| `Counterexamples` | Sections 5.1, 5.3: the conjectures are false, Theorem 11 |
