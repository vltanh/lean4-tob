# Legried, Molloy, Warnow, Roch 2021: quartets under gene duplication and loss

Source: B. Legried, E. K. Molloy, T. Warnow, S. Roch, *Polynomial-time statistical estimation of species trees under gene duplication
and loss*, J. Comput. Biol. 28 (2021), <https://doi.org/10.1089/cmb.2020.0424>. Read in its conference version with the same title, in
the copy on NSF PAR of the bioRxiv text 10.1101/821439; the journal's text was not read. Equation numbers below are those of that
version.

Cited by ECToBlob's Remark 3.4 as [24]: under duplication and loss, without incomplete lineage sorting, (3.1) holds on a species tree,
for one gene copy per individual or for all gene copies as multiple alleles.

## The model (`Model.lean`)

Their Section 3.1 is a birth-death process on each edge, and bifurcation of each copy at a speciation, with one copy at the root and fixed
rates, "although our proofs do not use these assumptions". `SpeciesTree` carries, on each edge, the law `K : PMF Shape` of what one copy
at the top becomes at the bottom: the addresses of its copies, an antichain. `geneLaw T` is the law of a gene tree, as the addresses of its
leaves in each species. Copies at the top of an edge evolve independently, which is what the proofs use. The birth-death law on shapes
itself isn't defined here, so that the results hold for every such law and not only for that one.

A topology of four leaves is `Pat`, defined by clusters: some vertex has two of them below it and not the other two.

## The bridges (`Bridge.lean`)

- Topologies are exclusive (`not_pat_of_pat`) and, on leaves none above another, exhaustive (`pat_trichotomy`). In a gene tree a leaf in one
  species is never above a leaf in another (`not_prefix_of_geneLaw`), so the three probabilities of topologies sum to one (`sum_probTopology`).
- One copy in each species gives an unrooted tree on the species, in the sense of the library: `pickTree`, `isUnrootedTree_pickTree`. It
  displays `quartetTree a b c d` exactly when `Pat` holds: `displays_pickTree_iff`.
- A species tree on all the species has clusters that are a hierarchy (`isHierarchy_clustersF`), and `speciesNetwork` is the library's network
  of it. Its tree of blobs is the unrooted species tree (`treeOfBlobs_speciesNetwork`), and displays `quartetTree A B C D` exactly when
  `SpeciesTree.IsQuartet` holds: `displays_treeOfBlobs_iff`.
- `quartetP` is the probability on `QuartetTree`, well defined by `probTopology_congr`. `quartetP_lt` is (3.1) in the form of the hypothesis of
  ECToBlob's Theorem 3.1, and `sum_treesOn_quartetP` the sum to one.

## The results (`Theorem1.lean`)

- `eq5`: their (5) in the proof of Theorem 1, for one copy picked uniformly in each species, given that all four have a copy.
- `eq7`: their (7) in the proof of Theorem 3, for all copies, as the expected number of choices with each topology. Its hypothesis that
  this expectation is finite is left implicit in the source; it holds for a birth-death process.
- `theorem1`: Theorem 1, identifiability, on quartets: two species trees with the same probabilities of topologies display the same
  quartets. That a tree is determined by its quartets, which they cite, isn't restated.
- `quartet_dom`: both (5) and (7), for any weight of a species on its number of copies.
- `exch_U` (`Correlation.lean`): their Lemma 1 and Lemma 2 at once.
- `mixture_dom`: not in the source, for a gene family that first picks a species tree. See `ECToBlob.Remark34`.
- `present_pos`, `numChoices_pos`: the positivity that the statements need, when a copy can go through each edge unchanged.

Not formalized: their Theorems 2 and 3 on the consistency of ASTRAL-one and ASTRAL-multi, which ECToBlob's remark doesn't cite.

## The proof

It follows theirs: the classification of tuples of ancestral copies at the most recent common ancestor `R` (`bal_class_ab`, `bal_class_ac`,
`cat_class_ab`, `cat_class_ac`; their (3), (4), (9), (10)); exchangeability for the terms with all copies distinct (`sum_distinct_swap`);
the positive correlation of Lemmas 1 and 2 (`step_le`); the counting (`bal_algebra`, `cat_algebra`).

Departures from the source:

- `claim_of_sep`, `catClaim_of_trip` and `exch_U` go down the tree one edge at a time, for a forest of copies at the top of an edge, where
  the source fixes `R` and conditions on the number of copies there, and in Lemma 1 on the numbers at the ancestor of `A`, `B`. The
  intermediate edges have laws of their own, so this is the same conditioning, in steps. A single step would need the composite law on
  shapes of a path of edges.
- The function `h(x, y)`, and its minimum on `x, y ≥ 1 / I`, is replaced by the display in their proof of Theorem 3, before division by the
  total, and a comparison term by term. This covers both (5) and (7), in `ℝ≥0∞`, where `0 / 0` needs no case.
- Lemma 1 and Lemma 2 are one statement, `exch_U`, for any weight `φ`: their proof of Lemma 2 factors the conditional expectation as
  `(N_j α)(N_k β)`, which isn't available for `φ n = 1 / n`, where the same independence gives a product over the two species.
