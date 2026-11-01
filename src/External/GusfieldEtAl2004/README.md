# Gusfield, Eddhu, Langley 2004: sites of one component lie on one cycle, and reduced galled trees

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

What differs from the source: no contraction or deletion is done. The source's unproved claim, that an arc can be deleted so that the leaves keep their labels, isn't needed.

The source's conclusion, one cycle, is `exists_isCycle_of_conflict`, and `exists_isCycle_of_incompatible` in the unrooted form: true in any network, for any rows that label nodes, with any number of crossovers, and no counterexample exists. Here too the proof departs from the source, whose deletion can't be done at a node that takes one site from each parent when these differ at both sites. It traces states up, and has two cases:

- The arc of `i` is below that of `j`, or is the same arc (`exists_isCycle_of_below`). A node with the other state at `i` and the root's at `j` is needed, and at the first such node `j` comes back, from a parent with the root's state. The path through the arc of `j` and the arc of `i` to the other parent has the other state at `j` throughout, so the path with the root's state can't meet it below the arc of `j`.
- Neither arc is below the other (`exists_isCycle_of_cross`). At the first node with the other state at both sites, the two states come from different parents, and the two paths through the two arcs meet only above them.

## `GalledTree.lean`: reduced galled trees are fully decomposed

Gusfield et al. 2007, line 180: "every reduced galled-tree for M must be fully-decomposed". `IsGall`, `IsGalledTree` and `IsReducedGalledTree` are Definitions 1.3, 1.4 and 2.2 of the source, and what they need is all in the source. The conflict
graph is a parameter of `IsReducedGalledTree`: `conflictGraph` of the ancestral sequence is the source's graph, and `incompatGraph` is the unrooted reading of 2007.

`IsReducedGalledTree.isFullyDecomposedFor_conflictGraph` and `isFullyDecomposedFor_incompatGraph` follow the source's steps: Lemma 2.1 (`label_tgt_of_notMem`), Lemma 2.3 (`lemma2_3`), Theorem 2.4 (`theorem2_4`), Theorem 2.5 (`theorem2_5`). Differences:

- The source's Theorem 2.2 and Lemma 2.3 are for one root and single crossovers, and go through the arrays W1, W2, W3 by cases. Here the root and the crossover model are arbitrary, so "the recombination point" has no meaning. In its place, each site gets a kind and a
  threshold on a line through the nodes of the gall (`exists_threshold`), which covers the three arrays at once. For a single crossover, the kind says which side of the recombination point a site is on.
- `lemma2_3` concludes that the sites are in one connected component. The source's exchange, "`i` conflicts with `j'` or `i'` conflicts with `j`", is `Straddles.cross`, for the sites ordered by kind.
- The unrooted form isn't in the source, which points to its reference [19], not read. The same proof covers it, since `G_S(M) = G(M + S)`.

**Corollary 2.1 of the source** is false as stated, in one direction: `corollary2_1_printed_false`, a node of a gall with no edge off it has a label that isn't a row. Its proof shows the other direction, and that is what's used here (`exists_mem_label_eq`).

**The wording of line 180.** 2007 says a galled tree is reduced "if every recombination cycle contains some incompatible sites". The source also asks for "no unconflicted sites". With the printed wording the claim fails: `line180_printed_false`, with the rows `000`, `101`, `010`, `110`.

`Gusfield2007.converse` and `Gusfield2007.converse_rooted` are derived from `SameBlob.lean`. Both modules import Gusfield2007 modules, because the statements are about those networks.

## `Elimination.lean`: Theorem 8.1

The Elimination Algorithm of Section 8 of the source, `Elim`, and `B`, `minRemovals`. A deleted column stays in the rows with the ancestral state (`liveRow_bridge` is the bridge to `M(D)`), and identical rows are one element of the `Finset`, so a sequence deletion has no step of its own. A removal is allowed only when no column can be deleted, as in the source.

`theorem8_1` is `B ≤ R` for any crossovers. The source gives no proof of it beyond naming two inductions. Its reference, Myers and Griffiths 2003, p. 380, was read: there it is the bound `R_s` with known types, proved by taking the first event back in time. `exists_elim_nodeRows` is that argument on a network, with the nodes of a set `A` as the sample: a lowest node of `A` is a recombination node (removed), or the target of an arc with a site (a column with one `1`), or has its parent's row.

## `Optimality.lean`: Theorems 2.6, 2.7, Section 8, line 381

- `theorem2_6`, and `theorem2_7_moreover`, `theorem2_7_moreover_incompatGraph`, the second sentence of Theorem 2.7: the non-trivial components correspond to the galls with conflicted sites.
- `lemma8_1`, `lemma8_5`, `lemma8_6` and `theorem8_2`: a removal changes one component at most, so an execution has a removal for each. `theorem8_3`: `B = R_S = k`, also for multiple crossovers.
- `reducedGalledTree_recombCount_eq_RS` and `reducedGalledTree_recombCount_eq_R` connect these with `RS` and `R` of `Gusfield2007`. `line381_rooted` and `line381` are the statement of line 381: S-min decomposable and min decomposable.

Differences from the source (at the head of the file):

- The source carries a reduced galled tree through the execution, with surgery at each step (Lemmas 8.2 to 8.6). Here one galled tree stays fixed, and the matrices are its node labels on the columns left (`RowsOn`). The source's Lemma 8.6 uses Corollary 5.1 after a removal, whose proof needs distinct columns, and a removal doesn't keep them: on the rows `100, 110, 001, 111`, a reduced galled tree with one gall, removing `100` makes the columns 1 and 2 identical.
- The source's proof of Lemma 8.5 says a removed edge `(u, v)` on a gall has `v` the recombination node, since otherwise `v` is a branching node. A node on a gall needn't be branching, when an edge has no site. The claim about the graph holds (`lemma8_5`).
- Lemmas 8.3 and 8.4 are about two leaves with one label. `Derives` is a bijection, and identical rows are one, so they have no counterpart: the graph doesn't change.
- The unrooted forms aren't in the source. The same proof gives them, since a column with one `1` relative to any sequence is in no incompatibility, and the proof of `lemma8_5` handles the row with the root's pair. Line 381 of 2007 also cites Gusfield 2005, not read.

## `ReducedExists.lean`: Corollary 5.1, Theorem 2.7

`exists_isReducedGalledTree` is Corollary 5.1, `corollary5_1_min` its minimum, `theorem2_7` the first sentence of Theorem 2.7, `RS_eq_card_cent` the value of `R_S`, `sMinDecomposable_of_isGalledTree` line 381 for any galled tree with that ancestral sequence. The hypothesis is the source's that each column has a `1`.

Departure from the source: it moves unconflicted sites off the galls one at a time (Lemma 5.1, Theorem 5.1), a case analysis using distinct columns, which line 180 of 2007 doesn't assume. Here each non-trivial component gets a network from its gall (`gallNet`, `exists_gall_piece`), and the construction of Theorem 1 of 2007 glues them (`exists_reduced_of_pieces`). `isGalledTree_of_isFullyDecomposedFor` shows that the result is a galled tree, by counting recombination nodes. Theorem 5.1 for a network that isn't a galled tree isn't formalized: 2007 doesn't use it.

The proof of Theorem 2.7 in the source replaces a gall by a perfect phylogeny of "the sequences labeling the nodes on `Q`". Those can conflict when no row shows it: a gall whose only leaf is below the recombination node.

## `ReducedUnrooted.lean`: line 180 of 2007, unrooted

`exists_isReducedGalledTree_incompatGraph` is line 180 for `G(M)`, `minDecomposable_of_isGalledTree` line 381 for any galled tree, `R_eq_card_cent` the value of `R`. Not in the source, which leaves this case to a "future paper"; Gusfield 2005 wasn't read. The new root is a row off the recombination nodes of the galls with incompatibilities (`exists_leaf_avoiding`), and a gall is rooted at another node by turning arcs (`exists_turned`).

## `Theorem2_2.lean`: W1, W2, W3 and the recombination point

Departure from the source: the algorithm doesn't call this theorem. The source reads the recombination point from the bipartition of Lemma 3.1, which rests on Theorem 2.2, and `Algorithm.lean` tries the points instead, and checks that the chains give the recombination node.

`theorem2_2` is Theorem 2.2 of the source as printed, for single crossovers, both directions, by its proof: the three pairs are at nodes of the gall, and the other placements lack one. The recombination point is a lower set (`IsRecombPoint`), and a node of the gall is the end of the start of a side.

## `GallFromChains.lean`, `Algorithm.lean`: the decision, computed

`IsArrangement.exists_network` is Theorem 3.2 of the source read backwards: two chains of rows, disjoint in their sites, covering them, whose ends recombine to `s`, make a network with one recombination node.

`galledDecide S M` is a computable function (it runs under `#eval`) that returns the answer and the number of operations: the conflict graph (`conflictOps`, `edgesOps`), its components (`labOf`), and the Site-Arrangement Algorithm on each non-trivial one (`candidate`, `compTest`).

- `galledDecide_iff`: it says `true` exactly when `M` has a galled tree with ancestral sequence `S` and single crossovers. Hypotheses: there are rows, and each column has a `1`, the source's standing assumptions.
- `exists_reduced_of_decide`: when it says `true`, a reduced galled tree exists. `Build.lean` returns one.
- `galledDecide_ops_le`: at most `51 (n + m + 1)⁵` operations. This isn't the source's `O(nm + n³)`: the function compares all pairs of rows where the source cites an `O(n |C|)` perfect phylogeny test. The bound is in `n` and `m`, so `m ≤ 2n`, which the source cites from Wang et al. 2001, isn't needed and isn't proved.

It says `true` on the rows of the source's Figure 2 and `false` on those of its Figure 4, as the source says. Differences from the source: the recombination point is tried rather than read from the bipartition of Lemma 3.1, and the decision doesn't need Sections 4 and 6.

## `Build.lean`: the reduced galled tree, computed

`galledBuild S M` is a computable function (it runs under `#eval`). It returns `none` exactly when there is no galled tree (`galledBuild_isSome_iff`), and otherwise a table of nodes, parents and labels, and the node below each site's arc. `galledBuild_correct` says that the table is that of `gNet`, a network that derives `M`, with ancestral sequence `S`, single crossovers, and is a reduced galled tree. On the rows of the source's Figure 2 it returns two galls: the first in the arrangement of the source's Figure 9, with recombination node `10010`, which is another arrangement of the gall of its Figures 2 and 6, and the second below the node `00100` of the first, as in Figure 2. On the rows of Figure 4 it returns `none`.

The rule: the rows below a node are its cluster, one node for each sequence of each component, and a node is below another when its cluster is inside the other's. `trichotomy`, from Theorem 2 of 2007, makes the clusters nested or disjoint. The chains inside a gall are the arrangement.

Departure from the source: Sections 4 and 6 connect the galls by comparing numbers of `1`s, and place the unconflicted sites by walks with cases, and Section 7 checks the result at the end. Here that one rule gives all the parents outside the galls, and the proof makes the check unnecessary. The recombination point is tried rather than read from the bipartition of Lemma 3.1.

## `BuildCount.lean`: the count of the algorithm

`galledBuildOps S M` is `galledBuild` with its operations counted: it returns the same value (`galledBuildOps_fst`), and it counts at most `233 (n + m + 1)⁶` operations (`galledBuildOps_le`, line 180 of 2007), for the decision, the arrangements, the table and the nodes of the sites. An operation is a read of an entry, a comparison of two states or labels, or a write of a label. There is no machine model: the steps that a library function makes (`dedup`, `argmax`) are charged by a stated formula.

This isn't the source's `O(nm + n³)`, which uses a linear perfect phylogeny test and `m ≤ 2n` from Wang et al. 2001. The function compares all the pairs of rows and all the candidate parents of each node, and the bound is in `n` and `m`, so that fact isn't needed and isn't proved.

## `Counts.lean`: the source's steps at the source's costs

No machine model. `galledTreeOperations` adds the source's steps at its costs, with the polynomial bound `galledTreeOperations_le`. Those steps aren't the ones of `Build.lean`.

## Not formalized

- **Theorem 5.1 for a network that isn't a galled tree.** It is in the source's scope: "Let `N` be a phylogenetic network deriving `M` with a gall that contains both unconflicted and conflicted sites". Neither 2007 nor the algorithm uses that case. Its proof moves sites and arcs of the network, a case analysis on distinct columns with no all-zero column, which `ReducedExists.lean` replaces for galled trees by gluing. It applies Theorem 2.2, which the source states for galled trees, to a general network, so a proof would first need the form of Theorem 2.2 for a gall of any network.
- Lemma 5.1, a step of that proof, and Theorem 2.8, on a gall of any network.
- Theorem 2.3, which the source leaves to the reader, and Theorem 3.1 on bi-convex graphs, from its reference [8], not read.
- Lemma 3.1 and Lemma 3.2 on the bipartition, which the algorithm here doesn't read, and Theorem 3.3 on all the arrangements.
- The counts of arrangements (Theorems 3.4, 3.5, Corollary 4.1), the constant-time comparison of galls (Theorem 4.1), and the uniqueness of the digraph (Theorem 4.2).
- Lemmas 8.3 and 8.4, which track a network through the Elimination Algorithm, where `Optimality.lean` works on a fixed network instead.
- The duplicate columns of Theorem 9.1, and the back mutations of Theorem 11.1.
