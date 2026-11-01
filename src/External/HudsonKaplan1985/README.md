# Hudson, Kaplan 1985: the lower bound on the number of recombinations

Source: R. Hudson, N. Kaplan, *Statistical properties of the number of recombination events in the history of a sample of
DNA sequences*, Genetics 111 (1985), 147--164. Not read for this statement.

Gusfield et al. 2007 use it at line 594 of `notes/sources/gusfield2007/pmc.txt`, to get `R¹(M(C_k)) ≥ 2` for Figure 6, and at
line 643 for `M_d`.

`Bound.lean` states it with `sorry`: pairwise non-overlapping intervals between incompatible sites each need a crossover, so
their number is a lower bound on `R¹(M)`. This module imports `Gusfield2007.Defs`, which imports Mathlib only, because the
statement is about those networks.
