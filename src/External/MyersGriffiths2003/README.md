# Myers, Griffiths 2003: the haplotype bound

Source: S. R. Myers, R. C. Griffiths, *Bounds on the minimum number of recombination events in a sample history*, Genetics
163 (2003), 375--394, as stated in Gusfield et al. 2007, line 559 of `notes/sources/gusfield2007/pmc.txt`: `H(M)` is "the
number of rows of M, minus the number of distinct columns of M, minus one". Not read for this statement.

`Bound.lean` states with `sorry`:

- the bound, `haplotypeBound_le_R`, for any crossover model; the paper says the source's proof for single crossover also
  gives it for multiple crossover (line 559);
- the equality case that Gusfield et al. draw from its proof at lines 560 to 564, in a true form, `allVisible_of_eq`: with
  **distinct columns** in `M + S`, a network reaching the bound has every node visible.

The hypothesis of distinct columns is an addition. The printed sentence is false without it: see
`Gusfield2007.visibleOfTightPrinted_false`. The proof: the labels of `N` are the root's, or new at an arc carrying a site, or
new at a recombination node, so `|L| ≤ 1 + m + R(N)`. So `|M + S| ≤ |L| ≤ |M + S|` when `R(N) = H(M + S)`.

This module imports `Gusfield2007.Defs`, which imports Mathlib only, because the statement is about those networks.
