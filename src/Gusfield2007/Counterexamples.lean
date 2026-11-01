module

public import Gusfield2007.Conjectures
public import Gusfield2007.TimeOrdered
public import External.HudsonKaplan1985.Bound
public import External.SongHein2005.Bound

/-!
# Gusfield et al. 2007, Sections 5.1 and 5.3: the Full-Decomposition Optimality Conjectures are false

The examples of Figures 5, 6 to 7, 8 to 9, and Theorem 11. Sites are numbered from 0 here and from 1 in the paper. The numbers have been checked by an exhaustive backward search on histories, outside Lean. The search agrees with the paper on all of them.
-/

@[expose] public section

open scoped Classical

namespace Gusfield2007

/-! ### Figure 5 -/

/-- The incompatible pairs of Figure 5, as printed at line 404: `(1, 3), (1, 4), (2, 3), (2, 4), (5, 7), (5, 8), (6, 7), (6, 8)`. -/
theorem fig5_incompatible (i j : Fin 8) :
    Incompatible fig5 i j ↔ (i.val + 1, j.val + 1) ∈ [(1, 3), (1, 4), (2, 3), (2, 4), (5, 7), (5, 8), (6, 7), (6, 8)] ∨
      (j.val + 1, i.val + 1) ∈ [(1, 3), (1, 4), (2, 3), (2, 4), (5, 7), (5, 8), (6, 7), (6, 8)] := by
  unfold Incompatible
  revert i j
  decide

/-- The two components of Figure 5: "component `C₁` containing the first four sites of `M`, and component `C₂` containing the last four sites" (line 404). -/
theorem fig5_reachable (i j : Fin 8) : (incompatGraph fig5).Reachable i j ↔ (i ∈ fig5C₁ ↔ j ∈ fig5C₁) := by
  sorry

/-- **Lines 404 to 410** (`g:fig5`). "We can establish, using the program beagle, that `R¹(M(C₁)) = R¹(M(C₂)) = 1`, but `R¹(M) = 3`." So the unrooted conjecture isn't equivalent
to `R¹(M) = Σ_C R¹(M(C))`. -/
theorem fig5_counts :
    R .single (restrictRows fig5C₁ fig5) = 1 ∧ R .single (restrictRows fig5C₂ fig5) = 1 ∧ R .single fig5 = 3 := by
  sorry

/-- **Line 410**, the caption of Figure 5 (`g:fig5_caption`). "Example showing that `R(M) > Σ_{C ∈ G(M)} R(M(C))`": the text at line 404 is about `R¹`, and the caption about `R`. It holds for `R`
too: `R(M(C₁)) = R(M(C₂)) = 1` and `R(M) = 3`, by an exhaustive search (not the paper's). -/
theorem fig5_counts_multiple :
    R .multiple (restrictRows fig5C₁ fig5) = 1 ∧ R .multiple (restrictRows fig5C₂ fig5) = 1 ∧ R .multiple fig5 = 3 := by
  sorry

/-! ### Figures 6 and 7 -/

/-- The incompatibility graph of Figure 6: the edges `2-3`, `3-5`, `1-4`, `4-6` of the paper's numbering. -/
theorem fig6_incompatible (i j : Fin 6) :
    Incompatible fig6 i j ↔ (i.val + 1, j.val + 1) ∈ [(2, 3), (3, 5), (1, 4), (4, 6)] ∨
      (j.val + 1, i.val + 1) ∈ [(2, 3), (3, 5), (1, 4), (4, 6)] := by
  unfold Incompatible
  revert i j
  decide

/-- The two components of Figure 6. -/
theorem fig6_reachable (i j : Fin 6) : (incompatGraph fig6).Reachable i j ↔ (i ∈ fig6C₁ ↔ j ∈ fig6C₁) := by
  sorry

/-- Line 607: "every pair of columns already contains the binary pair 0,0, so if we add the ancestral sequence `S = 000000` to `M`, no additional incompatible pairs would be created and so
`G_S(M) = G(M)`". -/
theorem fig6_conflictGraph : conflictGraph (fun _ => false) fig6 = incompatGraph fig6 := by
  ext i j
  change Conflict (fun _ => false) fig6 i j ↔ Incompatible fig6 i j
  unfold Conflict Incompatible
  revert i j
  decide

/-- Line 594: "`R¹(M(C₁)) ≥ 2` and `R¹(M(C₂)) ≥ 2`", by the Hudson-Kaplan bound. -/
theorem fig6_two_le_R : 2 ≤ R .single (restrictRows fig6C₁ fig6) ∧ 2 ≤ R .single (restrictRows fig6C₂ fig6) := by
  sorry

/-- Figure 7: a network for the matrix of Figure 6, with ancestral sequence `000000`, using three single crossovers. -/
theorem figure7 : ∃ (a b : ℕ) (N : Network (Fin 6) (Fin a) (Fin b)), N.Obeys .single ∧ N.Derives fig6 ∧
    N.ancestral = (fun _ => false) ∧ N.recombCount = 3 := by
  sorry

/-- **Section 5.3.1** (`g:single_false`). "Certainly then, `F¹(M) ≥ 4`. However, `R¹(M) ≤ 3` (as shown in Figure 7), so `F¹(M) > R¹(M)`, showing that the single-crossover case of the Unrooted
Full-Decomposition Optimality Conjecture is false" (line 594). -/
theorem unrootedConjecture_single_false :
    4 ≤ F .single fig6 ∧ R .single fig6 ≤ 3 ∧ ¬ UnrootedConjecture .single := by
  sorry

/-- Line 608: the same example refutes the rooted single-crossover conjecture, with `S = 000000`. -/
theorem rootedConjecture_single_false : ¬ RootedConjecture .single := by
  sorry

/-! ### Figures 8 and 9 -/

/-- The incompatible pairs of Figure 8, not printed in the paper ("not shown", line 612), by computation. -/
theorem fig8_incompatible (i j : Fin 10) :
    Incompatible fig8 i j ↔ (i.val + 1, j.val + 1) ∈ [(1, 2), (1, 4), (1, 5), (2, 3), (2, 4), (2, 5), (3, 4), (3, 5), (6, 7), (6, 9),
        (6, 10), (7, 8), (7, 9), (7, 10), (8, 9), (8, 10)] ∨
      (j.val + 1, i.val + 1) ∈ [(1, 2), (1, 4), (1, 5), (2, 3), (2, 4), (2, 5), (3, 4), (3, 5), (6, 7), (6, 9),
        (6, 10), (7, 8), (7, 9), (7, 10), (8, 9), (8, 10)] := by
  unfold Incompatible
  revert i j
  decide

/-- The two components of Figure 8: "one component contains sites 1 through 5, and the other contains sites 6 through 10" (line 618). -/
theorem fig8_reachable (i j : Fin 10) : (incompatGraph fig8).Reachable i j ↔ (i ∈ fig8C₁ ↔ j ∈ fig8C₁) := by
  sorry

/-- Line 612: "Any phylogenetic network for `M(C₁)` that uses multiple-crossover recombinations, requires at least two recombination nodes", verified in the paper by the program multicross.pl.
Similarly for `M(C₂)`. -/
theorem fig8_two_le_R :
    2 ≤ R .multiple (restrictRows fig8C₁ fig8) ∧ 2 ≤ R .multiple (restrictRows fig8C₂ fig8) := by
  sorry

/-- Figure 9: a network with all-zero ancestral sequence for the matrix of Figure 8, with three recombination nodes. -/
theorem figure9 : ∃ (a b : ℕ) (N : Network (Fin 10) (Fin a) (Fin b)), N.Obeys .multiple ∧ N.Derives fig8 ∧
    N.ancestral = (fun _ => false) ∧ N.recombCount = 3 := by
  sorry

/-- **Section 5.3.2** (`g:multiple_false`). "For the sequences `M` given in Figure 8, `F(M) ≥ 4`. Figure 9 shows a phylogenetic network that generates `M` with only three recombination
nodes, using multiple-crossover recombination. Hence, the unrooted, multiple-crossover version of the Full-Decomposition Optimality Conjecture is false" (line 612). -/
theorem unrootedConjecture_multiple_false :
    4 ≤ F .multiple fig8 ∧ R .multiple fig8 ≤ 3 ∧ ¬ UnrootedConjecture .multiple := by
  sorry

/-- Line 590: the rooted multiple-crossover conjecture is false too, with `S = 0` a row of Figure 8. -/
theorem rootedConjecture_multiple_false : ¬ RootedConjecture .multiple := by
  sorry

/-- **Line 403** (`g:rooted_implies_unrooted_conj`). "Note that the rooted conjectures imply the original unrooted conjectures." As an implication between the conjectures, it holds because the rooted
ones are false: `rootedConjecture_single_false`, `rootedConjecture_multiple_false`. Departure from the paper: its argument has a gap on one `M`, see `minDecomposable_of_sMinDecomposable`. -/
theorem rootedConjecture_imp_unrootedConjecture {c : Crossover} (hc : c = .single ∨ c = .multiple)
    (h : RootedConjecture c) : UnrootedConjecture c := by
  rcases hc with rfl | rfl
  · exact absurd h rootedConjecture_single_false
  · exact absurd h rootedConjecture_multiple_false

/-! ### Theorem 11 -/

/-- Line 638: "`M_d` contains `d` repetitions of `uxyvxu`", where `x = 011000`, `y = 110000`, `u = 000011`, `v = 000110`. The rows of `M_d` are six. So the printed "6 by 6d" is rows by
columns, and `x, y, u, v` are columns. -/
theorem Md_column (d : ℕ) (j : Fin (6 * d)) (t : Fin 6) :
    (ofBits (fig6Table.getD t.val []) : Fin 6 → Bool) ⟨j.val % 6, Nat.mod_lt _ (by decide)⟩ =
      ((ofBits ([[0, 0, 0, 0, 1, 1], [0, 1, 1, 0, 0, 0], [1, 1, 0, 0, 0, 0], [0, 0, 0, 1, 1, 0], [0, 1, 1, 0, 0, 0], [0, 0, 0, 0, 1, 1]].getD (j.val % 6) [])) : Fin 6 → Bool) t := by
  generalize_proofs hlt
  generalize j.val % 6 = n at hlt
  have key : ∀ (n' : Fin 6) (t : Fin 6), (ofBits (fig6Table.getD t.val []) : Fin 6 → Bool) n' =
      ((ofBits ([[0, 0, 0, 0, 1, 1], [0, 1, 1, 0, 0, 0], [1, 1, 0, 0, 0, 0], [0, 0, 0, 1, 1, 0], [0, 1, 1, 0, 0, 0], [0, 0, 0, 0, 1, 1]].getD n'.val [])) : Fin 6 → Bool) t := by
    decide
  exact key ⟨n, hlt⟩ t

/-- The two components of `G(M_d)` (line 641): "the first only containing columns of type `x` or `y`, and the second only containing columns of type `u` or `v`". -/
theorem Md_reachable {d : ℕ} (i j : Fin (6 * d)) : (incompatGraph (Md d)).Reachable i j ↔ (i ∈ MdC₁ d ↔ j ∈ MdC₁ d) := by
  sorry

/-- Line 643: "`R¹(M_d(C₁)) = R¹(M_d(C₂)) = 2d`". The paper needs `≥` only, and leaves it as "straightforward". By the Hudson-Kaplan bound for `≥`. -/
theorem Md_R_component (d : ℕ) :
    R .single (restrictRows (MdC₁ d) (Md d)) = 2 * d ∧ R .single (restrictRows (MdC₂ d) (Md d)) = 2 * d := by
  sorry

/-- Figure 10 (line 656): the trees `T_ux`, `T_y`, `T_v` on the rows of Figure 6, by the heights of their nodes. `T_ux` is compatible with the columns `u`, `x`, and `T_y` with `y`, and `T_v` with `v`,
and `d_oSPR(T_ux, T_y) = d_oSPR(T_y, T_v) = d_oSPR(T_v, T_ux) = 1`. -/
theorem figure10 : ∃ Tux Ty Tv : TimeOrderedTree fig6,
    Tux.CompatibleWith (fun r => r.1 0) ∧ Tux.CompatibleWith (fun r => r.1 1) ∧
      Ty.CompatibleWith (fun r => r.1 2) ∧ Tv.CompatibleWith (fun r => r.1 3) ∧
      Tux.doSPR Ty = 1 ∧ Ty.doSPR Tv = 1 ∧ Tv.doSPR Tux = 1 := by
  sorry

/-- Line 656: "`L(P_d) = 3d ≥ R¹(M_d)`". -/
theorem Md_R_le (d : ℕ) : R .single (Md d) ≤ 3 * d := by
  sorry

/-- **Theorem 11** (`g:thm11`). "For any positive integer `d`, there exists a set of sequences `M` such that `F¹(M) − R¹(M) ≥ d`" (line 631). The difference is written as a sum, so that the truncation on `ℕ`
plays no part. -/
theorem theorem11 (d : ℕ) (hd : 0 < d) :
    ∃ (m : ℕ) (M : Finset (Fin m → Bool)), M.Nonempty ∧ NoConstantColumn M ∧ R .single M + d ≤ F .single M := by
  sorry

end Gusfield2007
