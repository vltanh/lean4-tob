# Allman, Baños, Mitchell, Rhodes 2023: identifiability of the tree of blobs

Source: E. S. Allman, H. Baños, J. D. Mitchell, J. A. Rhodes, *The tree of blobs of a species network:
identifiability under the coalescent*, J. Math. Biol. 86 (2023), 10,
<https://doi.org/10.1007/s00285-022-01838-9> (read in PMC10062380).

TINNiK states the source's Theorems 1, 2 and 3 as its Theorems 1, 2 and 3.

| Source | Lean | Status |
| --- | --- | --- |
| Theorem 2 (inference rule) | `theorem2` | proved, for networks of any degrees |
| Lemma 3, Theorem 3 (combinatorial part) | `closure_complete`, `closure_sound` | proved |
| Theorem 1, Corollary 1 (CF-detectability, generic parameters) | `Corollary1` | **assumed** |

What Lean lacks for Corollary 1: the source argues that the NMSC concordance factors are analytic in
the numerical parameters; exchangeability and long edges give (a), and (b) reduces a 4-blob by
boundary parameters to a mixture of two networks with different quartet trees. It needs the analytic
parametrization on the boundary, network surgery at parameter value 0, and that a nonzero real-analytic
function has a null zero set. Building this on `Phylogenetics.geneTreeDist` is a large but feasible
effort. `TINNiK.theorem4` takes `Corollary1` as a named hypothesis.
