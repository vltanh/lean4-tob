# Myers, Griffiths 2003: the haplotype bound

Source: S. R. Myers, R. C. Griffiths, *Bounds on the minimum number of recombination events in a sample history*, Genetics
163 (2003), 375--394. Read: the journal's PDF, pp. 376-379 for the bounds and Appendix A for the proof of Algorithm 1. Gusfield et al. 2007 state the haplotype bound at line 559 (the line numbers are explained in `src/Gusfield2007/README.md`): `H(M)` is "the
number of rows of M, minus the number of distinct columns of M, minus one".

`Bound.lean` proves, by the argument of the source:

- `haplotypeBound_le_R`, the bound, for any crossover model. "Each recombination or mutation event in the ancestry creates at most one new type of the H that must be created altogether", the ancestor is one more, and the bound "may be applied to any subset of sites": here one site for each
  distinct column, which is the form Gusfield et al. give. The source counts `S` segregating sites, and the distinct columns come from this choice of subset. The source treats single crossovers; line 559 of Gusfield et al. says the same proof gives multiple crossovers, and it does: the argument (`Gusfield2007.Network.exists_source`) doesn't look at the crossovers.
- `haplotypeBound_addRow_le_RS`, line 559 of Gusfield et al.: `H(M + S) <= R_S(M)`, the case of a known ancestor. The source adds the all-zero type to the sample for this, and so does `M + S`.
- `allVisible_of_eq`, the equality case that Gusfield et al. draw from the proof at lines 560 to 564, in a true form: with **distinct columns** in `M + S`, a network reaching the bound has every node visible.

The hypothesis of distinct columns is an addition. The printed sentence is false without it: see `Gusfield2007.visibleOfTightPrinted_false`. The proof: the labels of `N` are the root's, or new at an arc carrying a site, or
new at a recombination node, so `|L| <= 1 + m + R(N)`. So `|M + S| <= |L| <= |M + S|` when `R(N) = H(M + S)`.

`Bound.lean` imports `Gusfield2007.Decomposition` for `recombSet_nonempty` and `rootedRecombSet_nonempty`, which say that the minimum `R`, `R_S` is over a nonempty set: without them `sInf` could be `0` by default.

`Algorithm1.lean` has the integer program and Algorithm 1 (pp. 377-378, Appendix A), which Gusfield et al. don't use, with no networks in it, and in the source's order: the system (2) (`Feasible`), the vector of Proposition 6 (`rStarVec`), Lemma 7 (`lemma7`), Corollary 8 (`corollary8`), the matrix of Algorithm 1 (`algorithm1`, a computable function) and its proof (`algorithm1_isOptimalValue`), the solution from the top row (`rStarVec_eq_sub`), "as far to the right along the sequence as possible" (`sum_rStarVec_le_of_feasible`), the other from the last column (`isOptimalValue_column`), and the bounds of a best chain, "satisfied in all optimal solutions" (`sum_eq_of_chainSum_eq`). The source's example is `example_values`. In Appendix A, p. 393, "`r_p` or `r_q`" has to be `r_p` or `r_{q-1}`: `B_pq` has no term in `r_q`. The argument holds with it (`exists_feasible_extend`).

`Composite.lean` has what it says about `R¹`, by the source's argument: an event falls between two consecutive sites, so that the events of a network satisfy the system when `B_ij` bounds the events in the region (`exists_feasible`). The value of Algorithm 1 is then a lower bound (`algorithm1_le_R`), and on `R¹_S` for the local bounds of `M + S` (`algorithm1_le_RS`), which is the case of known types. The local bounds (`IsLocalBounds`) can be:

- `R¹` of the region (`isLocalBounds_region`). This needs `NoConstantColumn`, since a network has an arc for each site, and the source's sites are segregating.
- The four-gamete test (`isLocalBounds_fourGamete`), which gives `R_m`, and it's Hudson and Kaplan's `R_M` (`Rm_eq_rM`), as the source says on p. 378.
- The haplotype bound (4) on subsets of the region with its end points (`isLocalBounds_haplotypeBounds`), which gives `R_h`, with `R_m ≤ R_h` (`Rm_le_Rh`), and `R_h ≤ R¹` (`Rh_le_R`). The source's parameters, which limit the subsets to save time, aren't modelled: they can only lower the bound. The example's `R_m = 2`, `R_h = 3` and matrices come out of its sample in `exampleSample_values`.

`Gusfield2007.Gen.split` is the case of two regions of the system, with any two sets of sites. `add_R_le_R` is that case for intervals, with single crossovers on both sides.

`SampleHistory.lean` has **Algorithm 3** (`historyBound`, a computable function), for unknown and known types, with `R_s` (`Rs`, `RsKnown`), the bounds `Rs_le_R`, `RsKnown_le_RS`, and `R_h ≤ R_s` (`Rh_le_Rs`, `Rh_addRow_le_RsKnown`). The proof of the bound is the source's induction, on a set of nodes of a network closed under parents in place of "following the ancestors" in a history: see its docstring for the one difference, that it needs only one inequality of Proposition 2. The source's "obviously increasing in the number of segregating sites" takes some work, because the algorithm removes sites in a fixed order: `historyBound_steps`, `historyBound_rowsAt_le`. "Noninformative" is read as at most one row in the state, rather than exactly one, so that a site that stops being segregating can go.

`Proposition2.lean` has **Proposition 2** (`proposition2`, `proposition2_rooted`), for removing a noninformative site, by the source's two constructions. Coalescing is the identity, since `R` is a function of the set of rows. It has the example's "four is the true minimum" (`exampleSample_RS`), on a history found by a search: the source doesn't give one. The example is with known types. With unknown types `R_s` is 3 there (`exampleSample_Rs`), which the source doesn't state.

`Implementation.lean` has **Lemma 4** (`typeCount_erase_le`, `typeCount_le_erase_add_one`) and **Corollary 5** (`corollary5`), by the source's arguments.

`Constraints.lean` has the remark on p. 378 on adding constraints: `r_k = 0` (`isLeast_of_eq_zero`, `ne_zero_of_pos`), and recombination only between a few sites (`isLeast_of_merging`, `exists_ne_zero_of_merging`). "Remove the term in `r_k` from each constraint" merges two sites, and the bound of a new pair of sites is the largest of the old pairs it comes from, which the source doesn't spell out.

The rest of the source is empirical: the simulations and the LPL data.

The PMC page has only a PDF of this article, which blocks scripted downloads. The copy was obtained from the Internet Archive's copy of `genetics.org`, and it's 20 pages, as published.
