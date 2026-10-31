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
| Theorem 1 (CF-detectability, generic parameters) | `theorem1`; statements (a), (b) of its proof: `isGenericNull_not_isStrictlyCut`, `isGenericNull_not_isNonCut` | proved, for binary networks |
| Corollary 1 | `corollary1` | proved, for binary networks |

Files: `SubgraphBlobs.lean` has blobs of a set of arcs, Lemma 2, cycles. `CycleLemma.lean` has the proof of Lemma 3.
`CutOrder.lean` has cuts by domination. `Basic.lean` has Theorems 2 and 3, and the translation between the languages.

Departures from the source's proof of Lemma 3: the paths are walks in sets of arcs; the cycle `C` is a minimal set of
arcs of `M` joining the ends of `e₀`, which is the source's "removing edges to eliminate any self-intersections"; and
the path from `α` to `C` is one within `A` from an arc of `C` in `A`, in place of the initial segment of `P₁`. The steps the
source leaves implicit are listed at the head of `CycleLemma.lean`.

Theorem 1 and Corollary 1 are in `Theorem1.lean`, and the graph side of (b) in `Reduction.lean`. The proof follows the
source: exchangeability and long arcs give (a); (b) reduces a 4-blob by boundary parameters to a mixture of two
networks with different quartet trees (`exists_reduction`, `nmscCF_ne_of_reduction`); the concordance factors are
entire in the coordinates (`Phylogenetics.analyticOnNhd_nmscCF_coordMetric`); and a nonzero real-analytic function has
a null zero set (`AnalyticOnNhd.prod_pi_volume_setOf_eq_zero`).

Departures from the source's proofs of Theorem 1 and Corollary 1, recorded in the docstrings: the step removing 2-blobs
is not needed (`exists_reduction_aux`), and Corollary 1 is proved on the network itself, with no comparison of the
parameter spaces of a network and its induced 4-taxon networks.

`exists_reduction_of_blobDegree` is the variant for networks whose blob vertices have degree at most 3, with tree arcs
as cut arcs. It gives the adaptation of Theorem 1 in ECToBlob's Proposition 5.1, `ECToBlob.adaptedAllmanTheorem1`, for
ECToBlob's measure, which has atoms at hybrid length `0`.
