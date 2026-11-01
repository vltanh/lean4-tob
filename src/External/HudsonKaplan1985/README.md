# Hudson, Kaplan 1985: the lower bound on the number of recombinations

Source: R. Hudson, N. Kaplan, *Statistical properties of the number of recombination events in the history of a sample of
DNA sequences*, Genetics 111 (1985), 147--164. Read: the journal's PDF (a scan with an OCR layer), p. 148 for the four-gamete test, pp. 152-153 and Appendix 2 for `R_M`.

Gusfield et al. 2007 use it at line 594 (the line numbers are explained in `src/Gusfield2007/README.md`), to get `R¹(M(C_k)) >= 2` for Figure 6, and at
line 643 for `M_d`.

`Bound.lean` proves `card_le_R`: pairwise non-overlapping intervals between incompatible sites each need a crossover, so their number is a lower bound on `R¹(M)`. This is the source's argument, in two steps:

- `Gusfield2007.Network.exists_breaksAt_of_incompatible`, in `Gusfield2007/NetworkOps.lean`, the four-gamete test: at most one mutation occurs at each site, so "the only way for all four gametic types to be in the sample is for at least one recombination event to have occurred in the history of the sample between the two sites";
- "to each interval we must assign at least one recombination event" (Appendix 2): a crossover separates at most one of a set of non-overlapping intervals.

The intervals of the source are open, so that they "are disjoint" when they share an endpoint at most, which is the hypothesis here.

`Algorithm.lean` has the source's algorithm for `R_M` (Appendix 2, p. 162), which Gusfield et al. don't use, as a computable function of the matrix `D` (`hudsonKaplan`), with no networks in it. It's written as Appendix 2 describes it: the list with starting points not decreasing, the deletion of "those that completely contain other intervals", and the rounds "let `(i₂, j₂)` be the first interval with `i₂ ≥ j₁` such that `(i₂, j₂)` is not disjoint from all of the remaining intervals and delete all intervals whose first component is `< j₂` and `> i₂`". What's proved:

- `finalList_disjoint`: "at this point all of the intervals are disjoint". The argument is by the state of the list after each round, as the source doesn't give one.
- `hudsonKaplan_isOptimalValue`: "`R_M` equals the final number of intervals on the list". `R_M` (p. 152) is "the minimum number of recombination events in the history of the sample which is consistent with the structure of `D`", read as the minimum of `Σ r_l` with at least one event in each interval with `d(i, j) = 1`, as Myers and Griffiths 2003, p. 378, read it. The source's "to each interval we must assign at least one recombination event. Hence" gives one inequality. The other needs that the final list's events serve the deleted intervals too, which it doesn't say: `exists_pierce`, an event just before the right end point of each final interval.
- `card_le_hudsonKaplan`: no disjoint family of the first list is larger. The source doesn't say this, but it follows.
- `hudsonKaplan_eq_algorithm1`, `rStarVec_ne_zero_iff`: the two claims of Myers and Griffiths 2003, pp. 378-379, on this algorithm.
- `figure1`, `hudsonKaplan_comp_le`: the eight cases of the source's Figure 1, and "increasing `S` cannot decrease `R_M`".

`AlgorithmBound.lean` has `rM`, the value on a sample of sequences, and `rM_le_R`, by `card_le_R`. So `R_M` is a lower bound on `R¹`, by the source's argument, and it can be computed: `decide` evaluates it, as in `MyersGriffiths2003.exampleSample_values`.

`Bound.lean` imports `Gusfield2007.Decomposition` for `recombSet_nonempty`, which says that the minimum `R¹` is over a nonempty set. `Algorithm.lean` imports only `External.MyersGriffiths2003.Algorithm1`, for the program.

The PMC page has only a PDF of this article, which blocks scripted downloads. The copy was obtained from the Internet Archive's copy of `genetics.org`.
