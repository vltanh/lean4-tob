# Song, Hein 2005: an upper bound on `R¹` from a sequence of trees

Source: Y. S. Song, J. Hein, *Constructing minimal ancestral recombination graphs*, J. Comput. Biol. 12 (2005), 147--169, as stated in Gusfield et al. 2007, line 654 of
`notes/sources/gusfield2007/pmc.txt`: "For any n by m matrix M, if P = T_1, T_2, ..., T_m is a sequence of time-ordered leaf-labeled trees in which T_i is compatible with site i in M,
for all i = 1, ..., m, then R¹(M) ≤ L(P)." Not read for this statement.

Gusfield et al. 2007 use it at line 656, to prove `R¹(M_d) ≤ 3d` in Theorem 11.

`Bound.lean` states it with `sorry`, with `L(P)` in `ℕ∞`, because `d_oSPR` is infinite between trees that no sequence of ordered-SPR operations connects. It imports
`Gusfield2007.TimeOrdered`, for the definitions, and `Gusfield2007.Defs`.

The time-ordered trees of the source may be binary; the paper doesn't say, and its Figure 10 has binary trees. The statement here has no such hypothesis. Check this against the source.
