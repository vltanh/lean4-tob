# Gusfield, Bansal, Bafna, Song 2007: a decomposition theory for phylogenetic networks and incompatible characters

Source: D. Gusfield, V. Bansal, V. Bafna, Y. S. Song, J. Comput. Biol. 14 (2007), 1247--1272. Read in the PMC author manuscript (PMC2581772), and, for the symbols its plain text loses, in an author's copy with the same words, on Yun Song's page: <https://people.eecs.berkeley.edu/~yss/Pub/decomposition.pdf>. The journal's typeset text wasn't reachable, so nothing here was checked against it.

"Line 342" in the docstrings means line 342 of the plain text of the PMC page, one line per paragraph. Symbols rendered as images are missing from that text.

The routes of the proofs are in `docs/paper_routes.tsv`, and their differences from the paper's in `docs/route_differences.tsv`.

The modules import Mathlib only, not the library `Phylogenetics`. The cited results are in `External/{SempleSteel2003, Gusfield1991, GusfieldEtAl2004, MyersGriffiths2003, HudsonKaplan1985, SongHein2005}`, and each of those READMEs says whether its source was read.

## Theorem 4

Theorem 4 is false with the printed definition of "efficient", because that definition omits the entry node of a blob (`theorem4_false_top`, `theorem4_false_small`). It is true with the entry node counted, up to two conventions and site-free arcs. That repair is in print and isn't ours: Gusfield, *ReCombinatorics* (MIT Press, 2014), Section 7.3.5, counts an external node "without regard to edge direction", and states the theorem for its canonical networks, a stricter class, as Theorem 7.3.3; we read the book only in snippets (`docs/REPORT.md`, E42). What this adds is the characterization in both directions, the failure under the printed definition and the check in the kernel: `theorem4_entry` says that, for a fully decomposed network, `T′` is `T̄` exactly when the network has `Network.IsEfficientAtEntry`, `Network.RegularArcs` and `Network.DegreeCond`.

- The two conventions are a root of degree two and a recombination leaf (`theorem4Printed_false_rootDegreeTwo`, `theorem4Printed_false_recombLeaf`). Site-free arcs are a case line 97 allows and the statement must exclude, so the theorem fails as printed on them (`theorem4_false_siteFree`).
- With the printed definition, `theorem4`, `theorem4_splits` and `theorem4_iff` state exactly what is needed.
- The hypotheses can be met, for every `M` with at least three rows (`exists_realization`).
- Line 329 for `IsEfficientAtEntry` keeps the number of recombinations (`exists_isEfficientAtEntry_of_fullyDecomposed`, `exists_isEfficientAtEntry_of_any`, in `EntryNet`). Line 299 holds with the root at any node of `T̄` that isn't a row (`exists_network_rooted_at`, in `RootedFrame`); with the root at a row, the network derives the other rows (`exists_network_rooted_at_row`), since a network deriving all the rows can't have its root at a row with `T′ = T̄` (`root_not_mem_range`).

Section 4.2's characterization is false too (`mostTreeLikePrinted_false`); `treeness_le_and_eq_iff` is the true form, and `MergedTreeness` has the blobs it leaves out, where the inequality can fail (`treeness_merged_false`). The head of `Uniqueness.lean` has the whole account.

## Theorem 10

`theorem10` is the statement with the rooted count `R_S(M)`, which is what the paper's proof is about, in each crossover model and with no hypothesis on the columns. The sentence at line 560 is false with identical columns (`visibleOfTightPrinted_false`), so the proof uses the pair of labels on two sites with different columns; `sMinDecomposable_of_haplotype_tight` is the paper's proof, when the columns are distinct. Theorem 10 as printed, with the unrooted count `R(M + S)`, is `Theorem10Printed`. It is false for single crossovers (`theorem10Printed_single_false`). For multiple crossovers `theorem10Printed_multiple_false_of_search` has a counterexample, given one computation, `printedMSearch`, which is a visible hypothesis of that theorem: the kernel hasn't completed it.

## What stays open

Line 425, `MinDecomposableOfForallS`. `minDecomposable_iff_exists_root` reduces it to the roots, and `minDecomposableOfForallS_of_haplotypeBound_eq` is the case `H(M) = R(M)`.

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
| `SameCycles` | two networks with the same recombination cycles, for the surgeries that follow |
| `Hub` | the modification of line 330, and turning an arc out of the root round |
| `ExplicitNetworks`, `FiniteNets`, `CounterexampleNets` | networks from lists of numbers, checked by the kernel; the networks of Sections 3.7 and 4.2 |
| `Uniqueness` | Sections 3.7, 4.2: Theorem 4, line 329, treeness |
| `Realizability` | the hypotheses of Theorem 4 can be met |
| `EntryNet`, `RootedFrame`, `MergedTreeness` | line 329 for `IsEfficientAtEntry` with no more recombinations, line 299 with the root at any node, the treeness inequality for blobs that merge components |
| `Conjectures` | Section 5.1: the conjectures, the computation of `F` and `F_S` |
| `Histories`, `Parsimony` | the labels of a network generated one at a time (`Gen`); mutation trees as networks, re-rooting (Section 4.1) |
| `SufficientConditions` | Section 5.2: Theorems 5 to 10, Corollaries 2, 3 |
| `OpenStatements`, `OpenSearch`, `Theorem10PrintedMultiple` | Theorem 10 as printed and without an ancestral sequence; line 425 |
| `GalledNetworks` | line 554: non-degenerate galled networks |
| `HusonKloepper` | line 590: Conjecture 1 of Huson and Klöpper, read from Conjecture 2.2 of Klöpper's thesis; reticulate networks and the bridge to `R`; the refutation by Figure 8 |
| `Examples`, `Components`, `LabelSearch` | the matrices of the figures, bookkeeping, a verified search for lower bounds on `R` |
| `Figure1`, `Figure5`, `Figure6`, `Figure8`, `EvenRows`, `MdMatrix`, `Mosaic` | the numbers of the figures, Footnote 2, `M_d` |
| `TimeOrdered`, `Figure10`, `MdLower` | Section 5.3.3: time-ordered trees and ordered SPR, Figure 10, `R¹(M_d) ≤ 3d`, and `R¹(M_d) = 3d` |
| `Counterexamples` | Sections 5.1, 5.3: the conjectures are false, Theorem 11 |
