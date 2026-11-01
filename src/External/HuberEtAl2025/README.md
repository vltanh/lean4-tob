# Huber et al. 2025, Theorem 5.1

Source: K. T. Huber, L. van Iersel, M. Jones, V. Moulton, L. Veenema-Nipius, *When are quarnets
sufficient to reconstruct semi-directed phylogenetic networks?*, Bull. Math. Biol. 87 (2025), 136,
<https://doi.org/10.1007/s11538-025-01510-5>.

TOB-QMC cites the forward direction as its Lemma 2. It says that a cut-edge split `A|B` of a binary
semi-directed network restricts to a cut-edge split `a₁a₂|b₁b₂` of the network restricted to any four
pairwise distinct `a₁, a₂ ∈ A`, `b₁, b₂ ∈ B`. `theorem5_1_forward` proves it for rooted networks, of
any degrees, from the domination description of cut edges in `Phylogenetics/Network/Cuts.lean` of the library.

The converse, `theorem5_1_converse`, and the whole statement, `theorem5_1`, are proved too, again on rooted networks of any degrees.

**Departure from the paper.** The source proves the converse for binary semi-directed networks, by induction on the non-trivial cut-edge splits. The base case, a simple network, takes its Lemmas 5.2 to 5.5: a split with an excellent cycle on each side, two of which overlap, and an analysis of what suppression leaves in the network induced on four taxa. Here the proof is through domination, in about a hundred lines.

The arcs that dominate a taxon form a chain, and domination goes up it: if `e` is above `e'`, both dominating `x`, then `e` dominates all that `e'` dominates (`dominates_of_above`). So the arcs dominating a set of taxa are the common ancestors in the dominator tree. Two consequences:

1. Given `a₀ ∈ A` and another taxon in `A`, there is `a' ∈ A` with `a' ≠ a₀` whose common dominators with `a₀` are those of all of `A` (`exists_pair_dominators`).
2. If each arc dominating `A` has a taxon of `B` below it, then one taxon `b` of `B` is below them all, since it is below the lowest (`exists_isBelow_all`).

By `hasCutSplitOn_iff_separates`, `A|B` is not a cut-edge split exactly when each arc dominating one side has a taxon of the other below it. So there is such a `b` for `A`, and such an `a` for `B`. Take `a'` for `a` and `b'` for `b`. An arc giving the cut-edge split `aa'|bb'` would dominate `a, a'`, so all of `A`, with `b` below it, or dominate `b, b'`, so all of `B`, with `a` below it. Neither is allowed.
