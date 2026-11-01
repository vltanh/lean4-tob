# Hudson, Kaplan 1985: the lower bound on the number of recombinations

Source: R. Hudson, N. Kaplan, *Statistical properties of the number of recombination events in the history of a sample of
DNA sequences*, Genetics 111 (1985), 147--164. Read: the journal's PDF (a scan with an OCR layer), p. 148 for the four-gamete test, pp. 152-153 and Appendix 2 for `R_M`.

Gusfield et al. 2007 use it at line 594 (the line numbers are explained in `src/Gusfield2007/README.md`), to get `R¹(M(C_k)) >= 2` for Figure 6, and at
line 643 for `M_d`.

`Bound.lean` proves `card_le_R`: pairwise non-overlapping intervals between incompatible sites each need a crossover, so their number is a lower bound on `R¹(M)`. This is the source's argument, in two steps:

- `Gusfield2007.Network.exists_breaksAt_of_incompatible`, in `Gusfield2007/NetworkOps.lean`, the four-gamete test: at most one mutation occurs at each site, so "the only way for all four gametic types to be in the sample is for at least one recombination event to have occurred in the history of the sample between the two sites";
- "to each interval we must assign at least one recombination event" (Appendix 2): a crossover separates at most one of a set of non-overlapping intervals.

The source's algorithm for `R_M`, which finds a largest set of such intervals, isn't formalized: Gusfield et al. use only the bound. The intervals of the source are open, so that they "are disjoint" when they share an endpoint at most, which is the hypothesis here.

This module imports `Gusfield2007.Decomposition` for `recombSet_nonempty`, which says that the minimum `R¹` is over a nonempty set.

The PMC page has only a PDF of this article, which blocks scripted downloads. The copy was obtained from the Internet Archive's copy of `genetics.org`.
