# Allman, Baños, Rhodes 2019: NANUQ

Source: E. S. Allman, H. Baños, J. A. Rhodes, *NANUQ: a method for inferring species networks from gene trees under the
coalescent model*, Algorithms Mol. Biol. 14 (2019), 24, <https://doi.org/10.1186/s13015-019-0159-2> (read in arXiv
v1, <https://arxiv.org/abs/1905.07050>, and in the published text, Europe PMC PMC6896299; the passages quoted agree).

ECToBlob's Remark 8.3 says that the argument of its Theorem 8.2 strengthens the source's consistency result.
`src/ECToBlob/Remark83.lean` proves that, from the results here.

## What is formalized (`NANUQ.lean`)

* Step 2 of the algorithm: `classify`, with the star test and the T3 test at levels `β`, `α`. Its printed statistics are
  `starStat` and `t3Stat` (`starStat_eq_printed`, `t3Stat_eq_printed`).
* Step 3, the network quartet distance of Definition 22 with the source's extension to star trees: `rho`,
  `nanuqDistance`. It is not TINNiK's distance: they differ at `x ≠ y` by the number of 4-cycles with `x, y` adjacent
  (`quartetDistance_sub_nanuqDistance`), and agree without 4-cycles (`nanuqDistance_eq_quartetDistance`). On a tree it is
  the tree metric of Rhodes 2020 (`nanuqDistance_treeClass`, the source's Theorem 17).
* Theorem 36, down to the distance, which is what its proof shows: `theorem36_of_proposition9`, with
  `theorem36_output_of_proposition9` for the steps after it, and `theorem36_generic_of_proposition9`. The proof is the
  source's: the star test by linear growth of the statistic, the second test by non-collapse under the null, and by linear
  growth off it, with a level per set of four taxa.

## What is formalized (`Placement.lean`, `Proposition9.lean`)

* Proposition 9, parts 1 and 3, on binary level-1 networks, at any `0 ≤ ρ ≤ 1`: `proposition9`. The source takes it from
  its references and prints no proof, so the proof is new. It uses the facts on blobs of level-1 networks in
  [`src/Basic/`](../../Basic) (`Level1Blobs`, `Wedge`, `Level1Blocks`), two cases of TOB-QMC's Lemma 4 among them, and
  Theorem 5.1 of Huber et al. 2025. It places lineages at vertices (`Placement.placeInj`) and
  moves them up by the Markov property; it has no formula in the branch lengths. `Proposition9.lean` has the argument.
* Proposition 9, part 2: `proposition9_part2`, in `Proposition9Part2.lean`, with the bound `CF_AB|CD ≥ 1/6`. Two lineages at
  a reticulation take one parent with probability at least `1/2`, and from there the masses are tree-like. "May or may not
  be tree-like": `ThreeTwo.isT1Strict_N₃`, `ThreeTwo.exists_not_isT3Null_N₃`.
* The structure of a `4₁`-cycle: `exists_cycle_of_not_isTreelike`, `not_isTreelike_iff`, and `exists_two_displayed` for the
  two quartet trees the grove displays.
* Theorem 36 with Proposition 9 proved: `theorem36`, `theorem36_output`, `theorem36_generic`. Also `t3Detectable`.

## What is formalized (`MissingTaxa.lean`, `Counts.lean`)

* Gene trees on subsets of the taxa, as the source's input says: the counts of Step 1 are `Phylogenetics.quartetCountOn`, and `theorem36_missing`, `theorem36_generic_missing` are the theorem when each set of four taxa is on more and more gene trees (`TINNiK.Covers`). The
  source does not state this.
* The running time: `nanuqOperations_le`, `O(n⁴ m)`, with Steps 4 and 5 as costs bounded as the source says.

## What is a hypothesis

`theorem36` has two: `ThreeTwoTreelike`, the hypothesis as printed, and `TINNiK.NoCentroidCF`, the correction below.
`theorem36_generic` has only the first.

`theorem36_output` also has the hypothesis that the steps after the distance return the wanted object on the theoretical
distance. That is what the source's Theorem 34, Corollary 24 and its references [6, 7] say.

## The source's definitions (`Quartet.lean`, `QuartetSemidirected.lean`, `QuartetContract.lean`, `QuartetCycle.lean`, `QuartetForm.lean`, `QuartetClass.lean`)

The source reads the types of cycle and `Q̃` on `N⁻` and `N_c⁻`. These are defined as printed, on a binary level-1 network:

* Definition 5: `trekArcs`, the edges in simple treks of `N⁻`. `trekArcs_eq_wedgeArcs`: these are TOB-QMC's `wedgeArcs`, for every
  network, since a simple semidirected trek is a directed one.
* `m_k`-cycles (line 399): `HasCycleType`, with `cycleSize` the number of vertices of the cycle of degree other than two in the graph of
  the kept edges.
* `Q̃` (Definition 20): `tildeGraph`, the contraction of the 2- and 3-cycles, and `qTilde`, with `suppressDegreeTwo`. `HasQuartetTopology`
  and `HasFourCycleTopology` are the literal tree and the literal 4-cycle.
* `ρ_xy` (Definition 20), `d_{Q,N⁻}` (Definition 22): `rhoTilde`, `sourceDistance`.

The bridges, all proved: `hasThreeTwoCycle_iff`; `hasCycleType_four_one_iff`; `networkClass_eq_tree_iff`, `networkClass_eq_cycle_iff`;
`qTilde_tree_or_cycle`; `rho_networkClass_eq`; `networkDistance_eq_sourceDistance`. No difference was found. `proposition9_source` states
Proposition 9 in these terms.

The representation: `Quartet.lean` keeps `LSA(X)`, which Definition 4 suppresses. It is a vertex of degree two, which Definition 5 suppresses
(`keptDegree_lsa_le`). `QuartetSemidirected.lean` reads Definition 5 on `AllmanEtAl2023.semidirected`, which carries the suppression out, and
proves that the readings agree: an edge is kept exactly when its arc is (`mem_sTrekEdges_iff`), the edge merging the two arcs at `LSA(X)` is kept
exactly when the arc it replaces is (`mem_sTrekEdges_merged_iff`), the kept edges are the kept arcs other than that one (`image_sTrekEdges`),
and each vertex of `N⁻` has the same degree in both graphs of kept edges (`sKeptDegree_eq`). `cycleSize`, `qTilde` and what follows them are
built from the kept arcs of `N`, and are not defined a second time on `N⁻`. Cycles are the blobs of the kept cycles, as the source says of a level-1 network (line 1381), and the contracted graph is
proved to be a tree or a graph with one cycle, so that no other cycle is left.

## What is left out

NeighborNet and the Circular Network algorithm (Steps 4, 5), which are not
characterized here. Splits graphs, and all the source's results about them and about split systems: Theorems 15, 23, 34,
Corollaries 16, 24, 31, 35, Lemmas 19, 21, 25-28, 32, 33, Proposition 30. Proposition 10 is checked on the printed formula (`figure5_lt`) and on
one network (`ThreeTwo.isT1Strict_N₃`), and is not stated for all level-1 networks. The data analyses. The running time is counted in `Counts.lean`, with NeighborNet and the Circular Network algorithm as parameters, not on a machine.

## Two errors in the proof of Theorem 36

1. "we choose `α_m` to be the minimum of the `α'_m`". A level rejects when the p-value is below it, so the level must be
   at least each `α'_m`: the maximum. At the minimum the test need not reject: `not_rejects_at_minimum`, for two sets of
   four taxa whose limits of the statistic have `40 d₁ < d₂`. The theorem is not affected: `exists_levels`.
2. "Since the network is binary, the true multinomial parameter values are `CF = (p₁, p₂, p₃)` with `p_i ≠ 1/3` or `0`".
   The hypothesis of the theorem, that induced `3₂`-cycles are tree-like, allows the centroid, which Definition 8 calls
   tree-like, and a binary network reaches it. `ThreeTwoCycle.lean` computes the concordance factors of a binary level-1
   network with a `3₂`-cycle from the definition of the NMSC (`ThreeTwo.nmscCF_N₃_abcd`), which gives the source's formula,
   and they are `(1/3, 1/3, 1/3)` at positive branch lengths (`ThreeTwo.centroid_N₃`). There the star test rejects with
   probability tending to `β` only, and the distance does not agree with the theoretical one with probability tending to
   one, for any levels: `ThreeTwo.not_theorem36AsPrinted_N₃`. The theorem needs `TINNiK.NoCentroidCF`, which holds off a
   null set of parameters (`TINNiK.isGenericNull_centroid`), and under the condition of the source's Proposition 10
   (`figure5_lt` on the printed formula; `ThreeTwo.theorem36_N₃` on this network).

The proof also uses, without saying so, that the maximum likelihood topologies are the true ones with probability tending
to one: `tendsto_maxCount_t3`, `tendsto_minCount`. The source's `α'_m = P(W_m > md/2)` is not a number, since the law `W_m`
depends on an estimate from the data; the proof here takes the bound `P(χ²₂ > md/2)` (`tendsto_t3PValue_lt_level`).
