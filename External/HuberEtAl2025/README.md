# Huber et al. 2025, Theorem 5.1 (forward direction)

Source: K. T. Huber, L. van Iersel, M. Jones, V. Moulton, L. Veenema-Nipius, *When are quarnets
sufficient to reconstruct semi-directed phylogenetic networks?*, Bull. Math. Biol. 87 (2025), 136,
<https://doi.org/10.1007/s11538-025-01510-5>.

TOB-QMC cites the forward direction as its Lemma 2. It says that a cut-edge split `A|B` of a binary
semi-directed network restricts to a cut-edge split `a₁a₂|b₁b₂` of the network restricted to any four
pairwise distinct `a₁, a₂ ∈ A`, `b₁, b₂ ∈ B`. `theorem5_1_forward` proves it for rooted networks, of
any degrees, from the domination description of cut edges in `Basic/Phylogenetics/NetworkCuts.lean`.
