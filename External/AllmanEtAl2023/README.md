# Allman, Baños, Mitchell, Rhodes 2023: identifiability of the tree of blobs

Source: E. S. Allman, H. Baños, J. D. Mitchell, J. A. Rhodes, *The tree of blobs of a species network:
identifiability under the coalescent*, J. Math. Biol. 86 (2023), 10,
<https://doi.org/10.1007/s00285-022-01838-9> (read in PMC10062380).

TINNiK states the source's Theorems 1, 2 and 3 as its Theorems 1, 2 and 3.

| Source | Lean | Status |
| --- | --- | --- |
| Definitions 7, 8, 12 (blobs, determined blobs, B-quartets) | `SameBlobIn`, `Determines` | `isBlob_restrict`: maximal connected subgraphs without cut edges; `not_resolves_iff_exists_determines`, `isBQuartet_iff_not_resolves`: the descriptions used in the file |
| Lemma 2 | `lemma2` | proved, as in the source; the subnetwork is taken connected |
| Corollary 2 | `corollary2` | proved from Lemma 2, for subgraphs induced on sets of taxa |
| Theorem 2 (inference rule) | `theorem2` | proved, for networks of any degrees. `rule_core` is the stronger form the closure needs (hypothesis (b) on the network, not the induced 4-taxon network) |
| Lemma 3 | `lemma3_blob`, in the source's language; `lemma3` | proved, along the source's cycle |
| Theorem 3 (combinatorial part) | `closure_complete`, `closure_sound` | proved, with the source's three steps (`closure_aux`) |
| Theorem 1 (CF-detectability, generic parameters) | `theorem1`, on four taxa; statements (a), (b) of its proof: `isGenericNull_not_isStrictlyCut`, `isGenericNull_not_isNonCut` | proved, for binary networks |
| Corollary 1 | `corollary1` | proved, for binary networks |

Files: `SubgraphBlobs.lean` has blobs of a set of arcs, Lemma 2, cycles. `CycleLemma.lean` has the proof of Lemma 3.
`CutOrder.lean` has cuts by domination. `Basic.lean` has Theorems 2 and 3, and the translation between the languages.

The proof of Lemma 3 follows the source: the paths `P₁` to `P₄` in its order, the cycle `C`, and the initial segment of `P₁`.
It fills the source's gap on why `P₁` meets `C` (`CutEdgeData.Paths.exists_meet`). The steps the source leaves implicit are
listed at the head of `CycleLemma.lean`.

Theorem 1 is in `Theorem1.lean`, on a network with four taxa, with the graph side of (b) in `Reduction.lean`, and Corollary 1 in
`Corollary1.lean`, through each induced 4-taxon network. The proof follows the source: exchangeability and long arcs give (a);
(b) reduces a 4-blob by boundary parameters to a mixture of two networks with different quartet trees (`exists_reduction`),
generic parameters make their CFs differ, and then `γ` is chosen (`exists_isNonCut_of_reduction`); the concordance factors are
entire in the coordinates (`Phylogenetics.analyticOnNhd_nmscCF_coordMetric`); and a nonzero real-analytic function has a null
zero set (`AnalyticOnNhd.prod_pi_volume_setOf_eq_zero`). Corollary 1 uses the map of parameters
(`Phylogenetics.RootedNetwork.isGenericNull_inducedMetric`) and the identity of CFs (`Phylogenetics.NMSC.nmscCF_inducedNetwork`).

Departures, recorded in the docstrings, and not forced except the second: no 2-blob step and no Lemma 1 (`exists_reduction_aux`);
line 149's order, where the source gives no reason (`IsLowPair.exists_splitOffAt`); one argument across the rooted forms
(`isGenericNull_not_isStrictlyCut`); deleted networks in the coordinates of `N` (`measure_nmscCF_eq_offMetric`); and an induced
network cut at the LSA, where the source's Definition 6 keeps what's above it (`corollary1`).

`exists_reduction_of_blobDegree` is the variant for networks whose blob vertices have degree at most 3, with tree arcs
as cut arcs. It gives the adaptation of Theorem 1 in ECToBlob's Proposition 5.1, `ECToBlob.adaptedAllmanTheorem1`, for
ECToBlob's measure, which has atoms at hybrid length `0`.
