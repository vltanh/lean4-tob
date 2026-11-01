# Gusfield, Eddhu, Langley 2004: sites of one component lie on one blob, and reduced galled trees

Source: D. Gusfield, S. Eddhu, C. Langley, *Optimal, efficient reconstruction of phylogenetic networks with constrained
recombination*, J. Bioinformatics and Computational Biology 2 (2004), 173--213, as cited by Gusfield et al. 2007, lines 180,
182 to 185, 375 and 381 (the line numbers are explained in `src/Gusfield2007/README.md`). Read in the authors' copy, not the journal's text.

## `SameBlob.lean`: one blob

The citation: "all sites from the same non-trivial connected component of G(M) must appear on the same blob". The source doesn't mention blobs. In the proof of its Theorem 2.2, it proves "a general fact":
two sites in conflict in any phylogenetic network are together on some recombination cycle. It removes the other sites, contracts edges, deletes one arc into each recombination node, and applies the
Perfect Phylogeny Theorem.

`exists_isBlob_of_incompatible` is for any set of rows that label nodes of the network, which gives `M`, `M + S` and the set `L` of all node labels at once. It follows the source's case behind the deletion, without changing the network:

- If every recombination node is a copy of a parent on `{i, j}`, which is where an arc can be deleted, then only three pairs occur (`Gusfield2007.Network.exists_breaksAt_of_incompatible`), as in a perfect phylogeny.
- Otherwise a node breaks `{i, j}`, and its parents differ at both sites. Tracing the states up gives a cycle through the arc of each site and both arcs into the node (`exists_isCycle_of_label_ne`). The two cycles share an arc.

What differs from the source: no contraction or deletion is done. The source's unproved claim, that an arc can be deleted so that the leaves keep their labels, isn't needed. Its stronger conclusion, one cycle, isn't proved: Gusfield et
al. 2007 cite only one blob.

## `GalledTree.lean`: reduced galled trees are fully decomposed

Gusfield et al. 2007, line 180: "every reduced galled-tree for M must be fully-decomposed". `IsGall`, `IsGalledTree` and `IsReducedGalledTree` are Definitions 1.3, 1.4 and 2.2 of the source, and what they need is all in the source. The conflict
graph is a parameter of `IsReducedGalledTree`: `conflictGraph` of the ancestral sequence is the source's graph, and `incompatGraph` is the unrooted reading of 2007.

`IsReducedGalledTree.isFullyDecomposedFor_conflictGraph` and `isFullyDecomposedFor_incompatGraph` follow the source's steps: Lemma 2.1 (`label_tgt_of_notMem`), Lemma 2.3 (`lemma2_3`), Theorem 2.4 (`theorem2_4`), Theorem 2.5 (`theorem2_5`). Differences:

- The source's Theorem 2.2 and Lemma 2.3 are for one root and single crossovers, and go through the arrays W1, W2, W3 by cases. Here the root and the crossover model are arbitrary, so "the recombination point" has no meaning. In its place, each site gets a kind and a
  threshold on a line through the nodes of the gall (`exists_threshold`), which covers the three arrays at once. For a single crossover, the kind says which side of the recombination point a site is on.
- `lemma2_3` concludes that the sites are in one connected component. The source's exchange, "`i` conflicts with `j'` or `i'` conflicts with `j`", is `Straddles.cross`, for the sites ordered by kind.
- The unrooted form isn't in the source, which points to its reference [19], not read. The same proof covers it, since `G_S(M) = G(M + S)`.

Not formalized: the source's count of recombinations (Theorem 2.7, Section 8), which line 381 of 2007 uses for optimality.

**The wording of line 180.** 2007 says a galled tree is reduced "if every recombination cycle contains some incompatible sites". The source also asks for "no unconflicted sites". With the printed wording the claim fails: `line180_printed_false`, with the rows `000`, `101`, `010`, `110`.

`Gusfield2007.converse` and `Gusfield2007.converse_rooted` are derived from `SameBlob.lean`. Both modules import Gusfield2007 modules, because the statements are about those networks.
