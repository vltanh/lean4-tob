# Myers, Griffiths 2003: the haplotype bound

Source: S. R. Myers, R. C. Griffiths, *Bounds on the minimum number of recombination events in a sample history*, Genetics
163 (2003), 375--394. Read: the journal's PDF, p. 379, equation (4). Gusfield et al. 2007 state it at line 559 (the line numbers are explained in `src/Gusfield2007/README.md`): `H(M)` is "the
number of rows of M, minus the number of distinct columns of M, minus one".

`Bound.lean` proves, by the argument of the source:

- `haplotypeBound_le_R`, the bound, for any crossover model. "Each recombination or mutation event in the ancestry creates at most one new type of the H that must be created altogether", the ancestor is one more, and the bound "may be applied to any subset of sites": here one site for each
  distinct column, which is the form Gusfield et al. give. The source counts `S` segregating sites, and the distinct columns come from this choice of subset. The source treats single crossovers; line 559 of Gusfield et al. says the same proof gives multiple crossovers, and it does: the argument (`Gusfield2007.Network.exists_source`) doesn't look at the crossovers.
- `haplotypeBound_addRow_le_RS`, line 559 of Gusfield et al.: `H(M + S) <= R_S(M)`, the case of a known ancestor. The source adds the all-zero type to the sample for this, and so does `M + S`.
- `allVisible_of_eq`, the equality case that Gusfield et al. draw from the proof at lines 560 to 564, in a true form: with **distinct columns** in `M + S`, a network reaching the bound has every node visible.

The hypothesis of distinct columns is an addition. The printed sentence is false without it: see `Gusfield2007.visibleOfTightPrinted_false`. The proof: the labels of `N` are the root's, or new at an arc carrying a site, or
new at a recombination node, so `|L| <= 1 + m + R(N)`. So `|M + S| <= |L| <= |M + S|` when `R(N) = H(M + S)`.

This module imports `Gusfield2007.Decomposition` for `recombSet_nonempty` and `rootedRecombSet_nonempty`, which say that the minimum `R`, `R_S` is over a nonempty set: without them `sInf` could be `0` by default.

The PMC page has only a PDF of this article, which blocks scripted downloads. The copy was obtained from the Internet Archive's copy of `genetics.org`, and it's 20 pages, as published.
