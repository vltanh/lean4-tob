# Kane, Tao 2017: a bound on partitioning clusters

Source: D. Kane, T. Tao, *A bound on partitioning clusters*, Electron. J. Combin. 24 (2017), P2.31, <https://doi.org/10.37236/6797>, read in its arXiv TeX (1702.00912v2).

Used by ASTRAL-III (Zhang, Rabiee, Sayyari, Mirarab 2018, read in Europe PMC, PMC5998893) for the `1.726` of its running time, which TOB-QMC quotes.

## What is formalized (`PartitioningClusters.lean`)

* Theorem 1, the bound: `theorem1`, `card_triples_le` (for three families, the source's second remark), `card_triples_le_rpow` (the exponent `1.726`, by `three_div_p_le`).
* The inequality (abc): `elementary_inequality`.

## Departures from the source's proof

* Induction on one element at a time, on sets, in place of tensorizing a convolution inequality for functions in blocks of coordinates. The source then applies that to indicator functions, so no function is needed here.
* **(abc).** The source proves it by compactness and critical points, with a small unspecified `ε`, and numerically: a root `u = 10.70297...`, at which the function has the value `0.040307...`. Here it is derived from `sum_psi_nonneg` by Gibbs' inequality. The latter is
  `ψ(a) + ψ(b) + ψ(c) ≥ 0` on the simplex, `ψ(t) = (p-1) t log t - (1-t) log(1-t)`, equivalently `p H(π) ≤ ∑ h(π_i)`. The function `ψ` is convex on `[0, (p-1)/p]`, which reduces the case of the two smaller entries there to the line `g(ε) = ψ(1-2ε) + 2ψ(ε)`. There the second derivative has the sign of
  `(p-2) + (3-p) ε`, so `g` is concave then convex, with `g(0) = 0` and a double zero at `1/3`: no number is needed. Numerical bounds on `log 2`, `log 3` are used only when the second entry is past `(p-1)/p`, where the sum is above `0.02`.

## What is left out

That the exponent cannot be improved. Neither TOB-QMC nor ASTRAL-III uses it. Its Theorem 3 on additive energy and the extension to `k` parts. The reduction to finite sets: sets here are `Finset α`.
