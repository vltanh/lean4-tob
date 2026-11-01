module

public import Gusfield2007.Conjectures
public import Gusfield2007.SufficientConditions
public import Gusfield2007.TimeOrdered
public import Gusfield2007.Figure1
public import Gusfield2007.Figure5
public import Gusfield2007.Figure6
public import Gusfield2007.Figure8
public import Gusfield2007.EvenRows
public import Gusfield2007.MdMatrix
public import Gusfield2007.Figure10
public import External.HudsonKaplan1985.Bound
public import External.SongHein2005.Bound

/-!
# Gusfield et al. 2007, Sections 5.1 and 5.3: the Full-Decomposition Optimality Conjectures are false

The examples of Figures 5, 6 to 7, 8 to 9, and Theorem 11. Sites are numbered from 0 here and from 1 in the paper.

The paper obtains the numbers of Figures 5 and 8 from the programs beagle and multicross.pl (lines 404, 612), and gives pen-and-paper arguments for Figure 6 and Theorem 11 (lines 594, 643, 656). Here, what has a pen-and-paper argument
follows it, by the Hudson-Kaplan bound and the fact of Song and Hein. Upper bounds are explicit networks, checked by the kernel. The other lower bounds are by the verified search of `Gusfield2007.LabelSearch`, which is checked by the kernel
in a few seconds, and by the composite bound `Gen.split`. A smaller counterexample to the multiple-crossover conjecture, not in the paper, is at the end of the section on Figures 8 and 9. The numbers agree with an independent exhaustive backward search on histories, outside Lean.
-/

@[expose] public section

open scoped Classical

namespace Gusfield2007

/-! ### What the arguments have in common -/

section Common

variable {ι : Type} [LinearOrder ι] [Finite ι]

/-- **Line 635** (`g:F_ge_sum`), for two components. -/
theorem add_R_le_F (c : Crossover) {M : Finset (ι → Bool)} (hM : M.Nonempty) (hC : NoConstantColumn M) {A : Set ι}
    (hA : ∀ i j, (incompatGraph M).Reachable i j ↔ (i ∈ A ↔ j ∈ A)) {a b : ι} (ha : a ∈ A) (hb : b ∉ A) :
    R c (restrictRows A M) + R c (restrictRows Aᶜ M) ≤ F c M := by
  have h := sum_R_le_F c M hM hC
  have e := finsum_connectedComponent_eq_add hA ha hb fun C => R c (restrictRows C M)
  exact e ▸ h

/-- A fully decomposed network from Theorem 3, for two components, when `S` doesn't change the graph (for example, `S` is a row). -/
theorem F_le_add_RS (c : Crossover) {M : Finset (ι → Bool)} {S : ι → Bool} (hM : M.Nonempty) (hC : NoConstantColumn M)
    (hG : conflictGraph S M = incompatGraph M) {A : Set ι} (hA : ∀ i j, (incompatGraph M).Reachable i j ↔ (i ∈ A ↔ j ∈ A)) {a b : ι} (ha : a ∈ A) (hb : b ∉ A) :
    F c M ≤ RS c (A.domRestrict S) (restrictRows A M) + RS c (Aᶜ.domRestrict S) (restrictRows Aᶜ M) := by
  obtain ⟨n, n', N, h₁, h₂, -, h₄, h₅⟩ := theorem3 c M S hM hC
  rw [hG] at h₄ h₅
  have e := finsum_connectedComponent_eq_add hA ha hb fun C => RS c (C.domRestrict S) (restrictRows C M)
  have hle : F c M ≤ N.recombCount := Nat.sInf_le ⟨n, n', N, h₁, h₂, h₄, rfl⟩
  rw [h₅] at hle
  exact e ▸ hle

omit [Finite ι] in
/-- `F(M) > R(M)` says that `M` isn't min decomposable. -/
theorem not_minDecomposable_of_lt {c : Crossover} {M : Finset (ι → Bool)} (h : R c M < F c M) : ¬ MinDecomposable c M := by
  rintro ⟨n, n', N, h₁, h₂, h₃, h₄⟩
  have hle : F c M ≤ N.recombCount := Nat.sInf_le ⟨n, n', N, h₁, h₂, h₃, rfl⟩
  omega

omit [Finite ι] in
/-- `F(M) > R_S(M)`, with `G_S(M) = G(M)`, says that `M` isn't S-min decomposable. -/
theorem not_sMinDecomposable_of_lt {c : Crossover} {M : Finset (ι → Bool)} {S : ι → Bool} (hG : conflictGraph S M = incompatGraph M) (h : RS c S M < F c M) :
    ¬ SMinDecomposable c S M := by
  rintro ⟨n, n', N, h₁, h₂, -, h₄, h₅⟩
  rw [hG] at h₄
  have hle : F c M ≤ N.recombCount := Nat.sInf_le ⟨n, n', N, h₁, h₂, h₄, rfl⟩
  omega

end Common

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
  refine reachable_iff_of_adj _ (fun i j hij => ?_) (a := 0) (b := 4) (fun i hi => reachable_of_two_steps ?_) (fun i hi => reachable_of_two_steps ?_) i j
  · change Incompatible fig5 i j at hij
    rw [fig5_incompatible] at hij
    change i.val < 4 ↔ j.val < 4
    revert hij
    revert i j
    decide
  · change i.val < 4 at hi
    change i = 0 ∨ Incompatible fig5 i 0 ∨ ∃ k, Incompatible fig5 i k ∧ Incompatible fig5 k 0
    unfold Incompatible
    revert hi
    revert i
    decide +kernel
  · change ¬ i.val < 4 at hi
    change i = 4 ∨ Incompatible fig5 i 4 ∨ ∃ k, Incompatible fig5 i k ∧ Incompatible fig5 k 4
    unfold Incompatible
    revert hi
    revert i
    decide +kernel

/-- **Lines 404 to 410** (`g:fig5`). "We can establish, using the program beagle, that `R¹(M(C₁)) = R¹(M(C₂)) = 1`, but `R¹(M) = 3`." So the unrooted conjecture isn't equivalent
to `R¹(M) = Σ_C R¹(M(C))`. -/
theorem fig5_counts :
    R .single (restrictRows fig5C₁ fig5) = 1 ∧ R .single (restrictRows fig5C₂ fig5) = 1 ∧ R .single fig5 = 3 :=
  ⟨fig5_R₁ (Or.inl rfl), fig5_R₂ (Or.inl rfl), fig5_R (Or.inl rfl)⟩

/-- **Line 410**, the caption of Figure 5 (`g:fig5_caption`). "Example showing that `R(M) > Σ_{C ∈ G(M)} R(M(C))`": the text at line 404 is about `R¹`, and the caption about `R`. It holds for `R`
too: `R(M(C₁)) = R(M(C₂)) = 1` and `R(M) = 3`, by the verified search (not the paper's). -/
theorem fig5_counts_multiple :
    R .multiple (restrictRows fig5C₁ fig5) = 1 ∧ R .multiple (restrictRows fig5C₂ fig5) = 1 ∧ R .multiple fig5 = 3 :=
  ⟨fig5_R₁ (Or.inr rfl), fig5_R₂ (Or.inr rfl), fig5_R (Or.inr rfl)⟩

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
  refine reachable_iff_of_adj _ (fun i j hij => ?_) (a := 2) (b := 3) (fun i hi => reachable_of_two_steps ?_) (fun i hi => reachable_of_two_steps ?_) i j
  · change Incompatible fig6 i j at hij
    rw [fig6_incompatible] at hij
    change (i = 1 ∨ i = 2 ∨ i = 4) ↔ (j = 1 ∨ j = 2 ∨ j = 4)
    revert hij
    revert i j
    decide
  · change i = 1 ∨ i = 2 ∨ i = 4 at hi
    change i = 2 ∨ Incompatible fig6 i 2 ∨ ∃ k, Incompatible fig6 i k ∧ Incompatible fig6 k 2
    unfold Incompatible
    revert hi
    revert i
    decide +kernel
  · change ¬ (i = 1 ∨ i = 2 ∨ i = 4) at hi
    change i = 3 ∨ Incompatible fig6 i 3 ∨ ∃ k, Incompatible fig6 i k ∧ Incompatible fig6 k 3
    unfold Incompatible
    revert hi
    revert i
    decide +kernel

theorem fig6C₁_compl : fig6C₁ᶜ = fig6C₂ := Set.ext fun i => by
  change ¬ (i = 1 ∨ i = 2 ∨ i = 4) ↔ (i = 0 ∨ i = 3 ∨ i = 5)
  revert i
  decide

theorem fig6C₁_zero : (0 : Fin 6) ∉ fig6C₁ := by
  change ¬ ((0 : Fin 6) = 1 ∨ (0 : Fin 6) = 2 ∨ (0 : Fin 6) = 4)
  decide

theorem fig6_nonempty : fig6.Nonempty := ⟨ofBits [0, 0, 1, 0, 0, 0], by decide +kernel⟩

theorem fig6_noConstantColumn : NoConstantColumn fig6 := by
  unfold NoConstantColumn
  decide +kernel

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
  rw [R_restrictRows fig6Sites₁ fig6Sites₁_strictMono fig6Sites₁_range, R_restrictRows fig6Sites₂ fig6Sites₂_strictMono fig6Sites₂_range]
  exact ⟨fig6Comp_two_le fig6Inc₁, fig6Comp_two_le fig6Inc₂⟩

/-- Figure 7: a network for the matrix of Figure 6, with ancestral sequence `000000`, using three single crossovers. -/
theorem figure7 : ∃ (a b : ℕ) (N : Network (Fin 6) (Fin a) (Fin b)), N.Obeys .single ∧ N.Derives fig6 ∧
    N.ancestral = (fun _ => false) ∧ N.recombCount = 3 :=
  ⟨16, 18, NetSpec.toNetwork figure7Spec_valid, NetSpec.obeys_single_toNetwork _ figure7Spec_single, NetSpec.derives_toNetwork _ figure7Spec_derives,
    figure7Spec_root, (NetSpec.recombCount_toNetwork _).trans figure7Spec_recombs⟩

/-- `F¹(M) ≥ 4` (line 594): "Certainly then". -/
theorem fig6_four_le_F : 4 ≤ F .single fig6 := by
  have h := add_R_le_F .single fig6_nonempty fig6_noConstantColumn (A := fig6C₁) fig6_reachable (a := 1) (b := 0) (Or.inl rfl) fig6C₁_zero
  rw [fig6C₁_compl] at h
  have h₂ := fig6_two_le_R
  omega

/-- `F¹(M) = 4`, by Theorem 3, with `S = 000000`. -/
theorem fig6_F_single : F .single fig6 = 4 := by
  have h := F_le_add_RS .single fig6_nonempty fig6_noConstantColumn fig6_conflictGraph (A := fig6C₁) fig6_reachable (a := 1) (b := 0) (Or.inl rfl) fig6C₁_zero
  rw [fig6C₁_compl] at h
  have h₁ := fig6_RS_single₁
  have h₂ := fig6_RS_single₂
  have h₃ := fig6_four_le_F
  omega

/-- `F(M) = 2`, by Theorem 3, with `S = 000000`. -/
theorem fig6_F_multiple : F .multiple fig6 = 2 := by
  have h := F_le_add_RS .multiple fig6_nonempty fig6_noConstantColumn fig6_conflictGraph (A := fig6C₁) fig6_reachable (a := 1) (b := 0) (Or.inl rfl) fig6C₁_zero
  have h' := add_R_le_F .multiple fig6_nonempty fig6_noConstantColumn (A := fig6C₁) fig6_reachable (a := 1) (b := 0) (Or.inl rfl) fig6C₁_zero
  rw [fig6C₁_compl] at h h'
  have h₁ := fig6_RS_multiple₁
  have h₂ := fig6_RS_multiple₂
  rw [fig6_R_multiple₁, fig6_R_multiple₂] at h'
  omega

/-- **Section 5.3.1** (`g:single_false`). "Certainly then, `F¹(M) ≥ 4`. However, `R¹(M) ≤ 3` (as shown in Figure 7), so `F¹(M) > R¹(M)`, showing that the single-crossover case of the Unrooted
Full-Decomposition Optimality Conjecture is false" (line 594). -/
theorem unrootedConjecture_single_false :
    4 ≤ F .single fig6 ∧ R .single fig6 ≤ 3 ∧ ¬ UnrootedConjecture .single := by
  have hR : R .single fig6 ≤ 3 := by
    obtain ⟨a, b, N, h₁, h₂, -, h₄⟩ := figure7
    exact h₄ ▸ Nat.sInf_le ⟨a, b, N, h₁, h₂, rfl⟩
  refine ⟨fig6_four_le_F, hR, fun h => ?_⟩
  have h₄ := fig6_four_le_F
  exact not_minDecomposable_of_lt (by omega) (h 6 fig6 fig6_nonempty fig6_noConstantColumn)

/-- **Line 608** (`g:rooted_single_false`). The same example refutes the rooted single-crossover conjecture, with `S = 000000`. -/
theorem rootedConjecture_single_false : ¬ RootedConjecture .single := by
  intro h
  have hRS : RS .single (fun _ => false) fig6 ≤ 3 := by
    obtain ⟨a, b, N, h₁, h₂, h₃, h₄⟩ := figure7
    exact h₄ ▸ Nat.sInf_le ⟨a, b, N, h₁, h₂, h₃, rfl⟩
  have h₄ := fig6_four_le_F
  exact not_sMinDecomposable_of_lt fig6_conflictGraph (by omega) (h 6 fig6 _ fig6_nonempty fig6_noConstantColumn)

/-- Line 607's `G_S(M)`, for `S = 001100`: it's connected. The pair of sites `3, 4` of the paper now conflicts. -/
theorem fig6Root_reachable (i j : Fin 6) : (conflictGraph fig6Root fig6).Reachable i j := by
  have key : ∀ i : Fin 6, (conflictGraph fig6Root fig6).Reachable i 2 := fun i => by
    have h₃₂ : (conflictGraph fig6Root fig6).Adj 3 2 := by
      change Conflict fig6Root fig6 3 2
      unfold Conflict
      decide +kernel
    have h : ∀ k : Fin 6, k = 2 ∨ k = 3 ∨ Conflict fig6Root fig6 k 2 ∨ Conflict fig6Root fig6 k 3 := by
      unfold Conflict
      decide +kernel
    rcases h i with rfl | rfl | h | h
    · exact SimpleGraph.Reachable.refl _
    · exact h₃₂.reachable
    · exact SimpleGraph.Adj.reachable (G := conflictGraph fig6Root fig6) h
    · exact (SimpleGraph.Adj.reachable (G := conflictGraph fig6Root fig6) h).trans h₃₂.reachable
  exact (key i).trans (key j).symm

/-- Line 403: the hypothesis `hG` of `minDecomposable_of_sMinDecomposable` is necessary. This example isn't in the paper: with `S = 001100`, the
topology of Figure 7 gives `R¹_S(M) = 3 = R¹(M)`, and `G_S(M)` is connected, so that `M` is S-min-1 decomposable by Theorem 5, yet `F¹(M) = 4`, so that `M` isn't min-1 decomposable. So the sentence of line 403, "by letting `S` be the
ancestral sequence that appears in the optimal phylogenetic network", doesn't prove the implication on one `M`. -/
theorem fig6_hG_necessary :
    RS .single fig6Root fig6 = R .single fig6 ∧ (∀ i j, (conflictGraph fig6Root fig6).Reachable i j) ∧ SMinDecomposable .single fig6Root fig6 ∧
      F .single fig6 = 4 ∧ ¬ MinDecomposable .single fig6 := by
  have hval := figure7RerootedSpec_valid
  have hrow : ∀ r ∈ fig6, r ∈ (NetSpec.toNetwork hval).labelSet := fun r hr => by
    obtain ⟨v, -, rfl⟩ := (NetSpec.derives_toNetwork hval figure7RerootedSpec_derives).surjOn hr
    exact Network.label_mem_labelSet _ v
  have hconn : ∀ i j, (conflictGraph fig6Root (NetSpec.toNetwork hval).labelSet).Reachable i j := fun i j =>
    (fig6Root_reachable i j).mono fun a b hab x y hxy => by
      obtain ⟨r, hr, h₁, h₂⟩ := hab x y hxy
      exact ⟨r, hrow r hr, h₁, h₂⟩
  refine ⟨fig6_RS_rerooted.trans fig6_R_single.symm, fig6Root_reachable, ?_, fig6_F_single, ?_⟩
  · refine theorem5 fig6_noConstantColumn (NetSpec.toNetwork hval) ⟨NetSpec.obeys_single_toNetwork _ figure7RerootedSpec_single, NetSpec.derives_toNetwork _ figure7RerootedSpec_derives, figure7RerootedSpec_root, ?_⟩ ?_
    · rw [NetSpec.recombCount_toNetwork, figure7RerootedSpec_recombs, fig6_RS_rerooted]
    · rw [card_connectedComponent_eq_one hconn, card_connectedComponent_eq_one fig6Root_reachable]
  · exact not_minDecomposable_of_lt (by rw [fig6_R_single, fig6_F_single]; omega)

/-! ### Line 608 -/

/-- **Line 608** (`g:line608_incompatible`). "Note also, that the first recombination creates the sequence `100010`; when it is added to `M`, sites 1 and 5 become incompatible, changing the number of connected components in `G_S(M)` as required by Theorem 9."

Here `S = 000000`. The first conjunct is the vertex `5` of Figure 7. Then sites 1 and 5 of the paper, `0` and `4` here, are compatible in `M`, and incompatible once `100010` is added. `G_S(M)` has two components; with `100010`, and with all the labels `L` of Figure 7, it has one. Theorem 9 requires this: if `L` respected `G_S(M)`, there would be a fully decomposed network with three recombination nodes, and `F¹(M) = 4`. -/
theorem fig6_line608_incompatible :
    (figure7Spec.IsRec 5 ∧ figure7Spec.label 5 = fig6Recomb) ∧
      (¬ Incompatible fig6 0 4 ∧ Incompatible (addRow fig6 fig6Recomb) 0 4) ∧
      Nat.card (conflictGraph (fun _ => false) fig6).ConnectedComponent = 2 ∧
      Nat.card (conflictGraph (fun _ => false) (addRow fig6 fig6Recomb)).ConnectedComponent = 1 ∧
      Nat.card (conflictGraph (fun _ => false) (NetSpec.toNetwork figure7Spec_valid).labelSet).ConnectedComponent = 1 ∧
      ¬ Respects (NetSpec.toNetwork figure7Spec_valid).labelSet (fun _ => false) fig6 := by
  have hinc : Incompatible (addRow fig6 fig6Recomb) 0 4 := fun a b => by
    have key : ∀ a b : Bool, (fig6Recomb 0 = a ∧ fig6Recomb 4 = b) ∨ ∃ r ∈ fig6, r 0 = a ∧ r 4 = b := by decide +kernel
    rcases key a b with h | ⟨r, hr, h⟩
    · exact ⟨_, mem_addRow.2 (Or.inl rfl), h⟩
    · exact ⟨r, mem_addRow.2 (Or.inr hr), h⟩
  -- With `100010`, the two components of `G_S(M)` are joined.
  have hconnect : ∀ L : Finset (Fin 6 → Bool), fig6 ⊆ L → Incompatible L 0 4 → ∀ i j, (conflictGraph (fun _ => false) L).Reachable i j := fun L hL hL₀ i j => by
    have hle : conflictGraph (fun _ => false) fig6 ≤ conflictGraph (fun _ => false) L := fun a b hab x y hxy => by
      obtain ⟨r, hr, h₁, h₂⟩ := hab x y hxy
      exact ⟨r, hL hr, h₁, h₂⟩
    have hadd : (conflictGraph (fun _ => false) L).Adj 0 4 := fun x y _ => hL₀ x y
    have hbase : ∀ u v, (u ∈ fig6C₁ ↔ v ∈ fig6C₁) → (conflictGraph (fun _ => false) L).Reachable u v := fun u v huv => by
      have h₀ : (conflictGraph (fun _ => false) fig6).Reachable u v := by
        rw [fig6_conflictGraph]
        exact (fig6_reachable u v).2 huv
      exact h₀.mono hle
    have hfour : (4 : Fin 6) ∈ fig6C₁ := Or.inr (Or.inr rfl)
    have key : ∀ i, (conflictGraph (fun _ => false) L).Reachable i 4 := fun i => by
      by_cases hi : i ∈ fig6C₁
      · exact hbase i 4 ⟨fun _ => hfour, fun _ => hi⟩
      · exact (hbase i 0 ⟨fun h => absurd h hi, fun h => absurd h fig6C₁_zero⟩).trans hadd.reachable
    exact (key i).trans (key j).symm
  have hval := figure7Spec_valid
  have hrow : fig6 ⊆ (NetSpec.toNetwork hval).labelSet := fun r hr => by
    obtain ⟨v, -, rfl⟩ := (NetSpec.derives_toNetwork hval figure7Spec_derives).surjOn hr
    exact Network.label_mem_labelSet _ v
  have hlab : (fig6Recomb : Fin 6 → Bool) ∈ (NetSpec.toNetwork hval).labelSet := figure7Spec_first_recomb.2.1 ▸ Network.label_mem_labelSet (NetSpec.toNetwork hval) 5
  refine ⟨⟨figure7Spec_first_recomb.1, figure7Spec_first_recomb.2.1⟩, ⟨by unfold Incompatible; decide +kernel, hinc⟩, ?_, card_connectedComponent_eq_one (hconnect _ (fun r hr => mem_addRow.2 (Or.inr hr)) hinc), ?_, ?_⟩
  · rw [fig6_conflictGraph]
    exact card_connectedComponent_eq_two fig6_reachable (a := 1) (b := 0) (Or.inl rfl) fig6C₁_zero
  · refine card_connectedComponent_eq_one (hconnect _ hrow fun x y => ?_)
    obtain ⟨r, hr, h₁, h₂⟩ := hinc x y
    rcases mem_addRow.1 hr with rfl | hr
    · exact ⟨_, hlab, h₁, h₂⟩
    · exact ⟨r, hrow hr, h₁, h₂⟩
  · intro hresp
    obtain ⟨a, b, N', h₁, h₂, -, h₄, h₅⟩ := theorem9 fig6_noConstantColumn (NetSpec.toNetwork hval) (NetSpec.obeys_single_toNetwork _ figure7Spec_single)
      (NetSpec.derives_toNetwork _ figure7Spec_derives) figure7Spec_root hresp
    rw [fig6_conflictGraph] at h₄
    rw [NetSpec.recombCount_toNetwork, figure7Spec_recombs] at h₅
    have hF : F .single fig6 ≤ N'.recombCount := Nat.sInf_le ⟨a, b, N', h₁, h₂, h₄, rfl⟩
    have := fig6_four_le_F
    omega

/-- **Line 608** (`g:line608_thm8`). "This counterexample is also consistent with Theorems 8 and 10, since the sites of the two components are not spatially disjoint". Here `S = 000000`, and Theorem 8 is the second conjunct: its hypothesis fails, and so does its conclusion. Neither component is an interval: `C₁` is the sites 2, 3, 5 of the paper, and `C₂` the sites 1, 4, 6. -/
theorem fig6_line608_theorem8 :
    ¬ SMinDecomposable .single (fun _ => false) fig6 ∧ (SpatiallyDisjoint (fun _ => false) fig6 → SMinDecomposable .single (fun _ => false) fig6) ∧
      ¬ SpatiallyDisjoint (fun _ => false) fig6 ∧ ¬ fig6C₁.OrdConnected ∧ ¬ fig6C₂.OrdConnected := by
  have hC₁ : ¬ fig6C₁.OrdConnected := fun h => by
    have h₃ : (3 : Fin 6) ∈ fig6C₁ := h.out (x := 2) (y := 4) (Or.inr (Or.inl rfl)) (Or.inr (Or.inr rfl)) ⟨by decide, by decide⟩
    change (3 : Fin 6) = 1 ∨ (3 : Fin 6) = 2 ∨ (3 : Fin 6) = 4 at h₃
    revert h₃
    decide
  have hC₂ : ¬ fig6C₂.OrdConnected := fun h => by
    have h₁ : (1 : Fin 6) ∈ fig6C₂ := h.out (x := 0) (y := 3) (Or.inl rfl) (Or.inr (Or.inl rfl)) ⟨by decide, by decide⟩
    change (1 : Fin 6) = 0 ∨ (1 : Fin 6) = 3 ∨ (1 : Fin 6) = 5 at h₁
    revert h₁
    decide
  have hRS : RS .single (fun _ => false) fig6 < F .single fig6 := by
    rw [fig6_RS_zero]
    have := fig6_four_le_F
    omega
  refine ⟨not_sMinDecomposable_of_lt fig6_conflictGraph hRS, theorem8 fig6_nonempty fig6_noConstantColumn, fun h => hC₁ ?_, hC₁, hC₂⟩
  have hsupp : ((conflictGraph (fun _ => false) fig6).connectedComponentMk 1).supp = fig6C₁ := by
    ext i
    rw [SimpleGraph.ConnectedComponent.mem_supp_iff, SimpleGraph.ConnectedComponent.eq, fig6_conflictGraph, fig6_reachable]
    exact ⟨fun h' => h'.2 (Or.inl rfl), fun h' => ⟨fun _ => Or.inl rfl, fun _ => h'⟩⟩
  rw [← hsupp]
  exact h _

/-- **Line 608** (`g:line608_thm10`). "and also the haplotype of one is not tight". The sentence is unclear in the PMC text, which is all we can read, and its likely meaning is "the haplotype bound of one component". Here is each reading, with `S = 000000`.

- The whole matrix: `H(M + S) = 2`, against `R¹_S(M) = R¹(M + S) = 3`. So the hypothesis of Theorem 10 fails, and Theorem 10 as printed holds here because of that.
- Each component, the two being the same matrix: `H(M(C_k) + S(C_k)) = 1`, against `R¹_{S(C_k)}(M(C_k)) = R¹(M(C_k)) = 2`.

For multiple crossovers the bounds are tight on components, since `R(M(C_k)) = 1`; the sentence is about the single-crossover case. -/
theorem fig6_line608_theorem10 :
    (haplotypeBound (addRow fig6 fun _ => false) = 2 ∧ RS .single (fun _ => false) fig6 = 3 ∧ R .single (addRow fig6 fun _ => false) = 3 ∧ Theorem10Printed .single fig6 fun _ => false) ∧
      (haplotypeBound (addRow (restrictRows fig6C₁ fig6) (fig6C₁.domRestrict fun _ => false)) = 1 ∧ RS .single (fig6C₁.domRestrict fun _ => false) (restrictRows fig6C₁ fig6) = 2 ∧ R .single (restrictRows fig6C₁ fig6) = 2) ∧
      (haplotypeBound (addRow (restrictRows fig6C₂ fig6) (fig6C₂.domRestrict fun _ => false)) = 1 ∧ RS .single (fig6C₂.domRestrict fun _ => false) (restrictRows fig6C₂ fig6) = 2 ∧ R .single (restrictRows fig6C₂ fig6) = 2) := by
  have hne₁ : (restrictRows fig6C₁ fig6).Nonempty := ⟨_, fig6_root_mem₁⟩
  have hne₂ : (restrictRows fig6C₂ fig6).Nonempty := ⟨_, fig6_root_mem₂⟩
  have hRS₁ := R_le_RS .single (fig6C₁.domRestrict fun _ => false) hne₁
  have hRS₂ := R_le_RS .single (fig6C₂.domRestrict fun _ => false) hne₂
  rw [fig6_R_single₁] at hRS₁
  rw [fig6_R_single₂] at hRS₂
  refine ⟨⟨fig6_haplotypeBound_addRow, fig6_RS_zero, fig6WithRoot_R, fun h => ?_⟩, ⟨?_, le_antisymm fig6_RS_single₁ hRS₁, fig6_R_single₁⟩, ⟨?_, le_antisymm fig6_RS_single₂ hRS₂, fig6_R_single₂⟩⟩
  · rw [fig6_haplotypeBound_addRow, fig6WithRoot_R] at h
    exact absurd h (by decide)
  · rw [addRow_eq_of_mem fig6_root_mem₁]
    exact fig6_haplotypeBound₁
  · rw [addRow_eq_of_mem fig6_root_mem₂]
    exact fig6_haplotypeBound₂

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
  refine reachable_iff_of_adj _ (fun i j hij => ?_) (a := 0) (b := 5) (fun i hi => reachable_of_two_steps ?_) (fun i hi => reachable_of_two_steps ?_) i j
  · change Incompatible fig8 i j at hij
    rw [fig8_incompatible] at hij
    change i.val < 5 ↔ j.val < 5
    revert hij
    revert i j
    decide +kernel
  · change i.val < 5 at hi
    change i = 0 ∨ Incompatible fig8 i 0 ∨ ∃ k, Incompatible fig8 i k ∧ Incompatible fig8 k 0
    unfold Incompatible
    revert hi
    revert i
    decide +kernel
  · change ¬ i.val < 5 at hi
    change i = 5 ∨ Incompatible fig8 i 5 ∨ ∃ k, Incompatible fig8 i k ∧ Incompatible fig8 k 5
    unfold Incompatible
    revert hi
    revert i
    decide +kernel

theorem fig8C₁_compl : fig8C₁ᶜ = fig8C₂ := Set.ext fun i => by
  change ¬ i.val < 5 ↔ 5 ≤ i.val
  omega

theorem fig8C₁_zero : (0 : Fin 10) ∈ fig8C₁ := by
  change (0 : Fin 10).val < 5
  decide

theorem fig8C₁_five : (5 : Fin 10) ∉ fig8C₁ := by
  change ¬ (5 : Fin 10).val < 5
  decide

theorem fig8_nonempty : fig8.Nonempty := ⟨ofBits [0, 0, 0, 0, 0, 0, 0, 0, 0, 0], by decide +kernel⟩

theorem fig8_noConstantColumn : NoConstantColumn fig8 := by
  unfold NoConstantColumn
  decide +kernel

theorem fig8_zero_mem : (fun _ => false : Fin 10 → Bool) ∈ fig8 := by decide +kernel

/-- Line 612: "Any phylogenetic network for `M(C₁)` that uses multiple-crossover recombinations, requires at least two recombination nodes", verified in the paper by the program multicross.pl.
Similarly for `M(C₂)`. Here by the verified search `fig8Comp_check`. -/
theorem fig8_two_le_R :
    2 ≤ R .multiple (restrictRows fig8C₁ fig8) ∧ 2 ≤ R .multiple (restrictRows fig8C₂ fig8) :=
  ⟨fig8_R_multiple₁.ge, fig8_R_multiple₂.ge⟩

/-- Figure 9: a network with all-zero ancestral sequence for the matrix of Figure 8, with three recombination nodes. -/
theorem figure9 : ∃ (a b : ℕ) (N : Network (Fin 10) (Fin a) (Fin b)), N.Obeys .multiple ∧ N.Derives fig8 ∧
    N.ancestral = (fun _ => false) ∧ N.recombCount = 3 :=
  ⟨28, 30, NetSpec.toNetwork figure9Spec_valid, trivial, NetSpec.derives_toNetwork _ figure9Spec_derives, figure9Spec_root,
    (NetSpec.recombCount_toNetwork _).trans figure9Spec_recombs⟩

/-- `F(M) ≥ 4` (line 612). -/
theorem fig8_four_le_F : 4 ≤ F .multiple fig8 := by
  have h := add_R_le_F .multiple fig8_nonempty fig8_noConstantColumn (A := fig8C₁) fig8_reachable (a := 0) (b := 5) fig8C₁_zero fig8C₁_five
  rw [fig8C₁_compl] at h
  have h₂ := fig8_two_le_R
  omega

/-- `F(M) = 4`, by Theorem 3, with `S = 0`. -/
theorem fig8_F_multiple : F .multiple fig8 = 4 := by
  have h := F_le_add_RS .multiple fig8_nonempty fig8_noConstantColumn (conflictGraph_eq_of_mem fig8_zero_mem) (A := fig8C₁) fig8_reachable (a := 0) (b := 5) fig8C₁_zero fig8C₁_five
  rw [fig8C₁_compl] at h
  have h₁ := fig8_RS_multiple₁
  have h₂ := fig8_RS_multiple₂
  have h₃ := fig8_four_le_F
  omega

/-- `F¹(M) = 6`, by Theorem 3, with `S = 0`. So `M` of Figure 8 is min-1 decomposable: `R¹(M) = 6`. It's a counterexample for multiple crossovers only. Not in the paper. -/
theorem fig8_F_single : F .single fig8 = 6 := by
  have h := F_le_add_RS .single fig8_nonempty fig8_noConstantColumn (conflictGraph_eq_of_mem fig8_zero_mem) (A := fig8C₁) fig8_reachable (a := 0) (b := 5) fig8C₁_zero fig8C₁_five
  have h' := add_R_le_F .single fig8_nonempty fig8_noConstantColumn (A := fig8C₁) fig8_reachable (a := 0) (b := 5) fig8C₁_zero fig8C₁_five
  rw [fig8C₁_compl] at h h'
  have h₁ := fig8_RS_single₁
  have h₂ := fig8_RS_single₂
  rw [fig8_R_single₁, fig8_R_single₂] at h'
  omega

/-- **Section 5.3.2** (`g:multiple_false`). "For the sequences `M` given in Figure 8, `F(M) ≥ 4`. Figure 9 shows a phylogenetic network that generates `M` with only three recombination
nodes, using multiple-crossover recombination. Hence, the unrooted, multiple-crossover version of the Full-Decomposition Optimality Conjecture is false" (line 612). -/
theorem unrootedConjecture_multiple_false :
    4 ≤ F .multiple fig8 ∧ R .multiple fig8 ≤ 3 ∧ ¬ UnrootedConjecture .multiple := by
  have hR : R .multiple fig8 ≤ 3 := by
    obtain ⟨a, b, N, h₁, h₂, -, h₄⟩ := figure9
    exact h₄ ▸ Nat.sInf_le ⟨a, b, N, h₁, h₂, rfl⟩
  refine ⟨fig8_four_le_F, hR, fun h => ?_⟩
  have h₄ := fig8_four_le_F
  exact not_minDecomposable_of_lt (by omega) (h 10 fig8 fig8_nonempty fig8_noConstantColumn)

/-- **Line 590** (`g:rooted_multiple_false`). The rooted multiple-crossover conjecture is false too, with `S = 0` a row of Figure 8. -/
theorem rootedConjecture_multiple_false : ¬ RootedConjecture .multiple := by
  intro h
  have hRS : RS .multiple (fun _ => false) fig8 ≤ 3 := by
    obtain ⟨a, b, N, h₁, h₂, h₃, h₄⟩ := figure9
    exact h₄ ▸ Nat.sInf_le ⟨a, b, N, h₁, h₂, h₃, rfl⟩
  have h₄ := fig8_four_le_F
  exact not_sMinDecomposable_of_lt (conflictGraph_eq_of_mem fig8_zero_mem) (by omega) (h 10 fig8 _ fig8_nonempty fig8_noConstantColumn)

/-! ### A smaller counterexample, not in the paper -/

theorem even_reachable (i j : Fin 6) : (incompatGraph evenRows).Reachable i j ↔ (i ∈ evenC₁ ↔ j ∈ evenC₁) := by
  refine reachable_iff_of_adj _ (fun i j hij => ?_) (a := 0) (b := 3) (fun i hi => reachable_of_two_steps ?_) (fun i hi => reachable_of_two_steps ?_) i j
  · change Incompatible evenRows i j at hij
    change i.val < 3 ↔ j.val < 3
    unfold Incompatible at hij
    revert hij
    revert i j
    decide +kernel
  · change i.val < 3 at hi
    change i = 0 ∨ Incompatible evenRows i 0 ∨ ∃ k, Incompatible evenRows i k ∧ Incompatible evenRows k 0
    unfold Incompatible
    revert hi
    revert i
    decide +kernel
  · change ¬ i.val < 3 at hi
    change i = 3 ∨ Incompatible evenRows i 3 ∨ ∃ k, Incompatible evenRows i k ∧ Incompatible evenRows k 3
    unfold Incompatible
    revert hi
    revert i
    decide +kernel

theorem evenC₁_compl : evenC₁ᶜ = evenC₂ := Set.ext fun i => by
  change ¬ i.val < 3 ↔ 3 ≤ i.val
  omega

theorem evenC₁_zero : (0 : Fin 6) ∈ evenC₁ := by
  change (0 : Fin 6).val < 3
  decide

theorem evenC₁_three : (3 : Fin 6) ∉ evenC₁ := by
  change ¬ (3 : Fin 6).val < 3
  decide

theorem even_nonempty : evenRows.Nonempty := ⟨ofBits [0, 0, 0, 0, 0, 0], by decide +kernel⟩

theorem even_noConstantColumn : NoConstantColumn evenRows := by
  unfold NoConstantColumn
  decide +kernel

theorem even_zero_mem : (fun _ => false : Fin 6 → Bool) ∈ evenRows := by decide +kernel

/-- `F(M) = 4` for `evenRows`. -/
theorem even_F : F .multiple evenRows = 4 := by
  have h := F_le_add_RS .multiple even_nonempty even_noConstantColumn (conflictGraph_eq_of_mem even_zero_mem) (A := evenC₁) even_reachable (a := 0) (b := 3) evenC₁_zero evenC₁_three
  have h' := add_R_le_F .multiple even_nonempty even_noConstantColumn (A := evenC₁) even_reachable (a := 0) (b := 3) evenC₁_zero evenC₁_three
  rw [evenC₁_compl] at h h'
  have h₁ := even_RS₁
  have h₂ := even_RS₂
  rw [even_R₁, even_R₂] at h'
  omega

/-- A smaller refutation of the unrooted multiple-crossover conjecture than Figure 8. **It isn't in the paper**; a search for this formalization found it, and it isn't claimed to be new (see `evenRows`). `F(M) = 4` and `R(M) = 3`, with 7
rows and 6 sites, against Figure 8's 13 and 10. -/
theorem even_unrootedConjecture_false : F .multiple evenRows = 4 ∧ R .multiple evenRows = 3 ∧ ¬ UnrootedConjecture .multiple :=
  ⟨even_F, even_R, fun h => not_minDecomposable_of_lt (by rw [even_F, even_R]; omega) (h 6 evenRows even_nonempty even_noConstantColumn)⟩

/-- A smaller refutation of the rooted multiple-crossover conjecture than Figure 8, with `S = 000000`, a row. It isn't in the paper. -/
theorem even_rootedConjecture_false : ¬ RootedConjecture .multiple := fun h => by
  have hRS : RS .multiple (fun _ => false) evenRows ≤ 3 := by
    have := NetSpec.RS_le (c := .multiple) evenNet_valid evenNet_derives trivial evenNet_root
    rwa [evenNet_recombs] at this
  exact not_sMinDecomposable_of_lt (conflictGraph_eq_of_mem even_zero_mem) (by rw [even_F]; omega) (h 6 evenRows _ even_nonempty even_noConstantColumn)

/-- **Line 403** (`g:rooted_implies_unrooted_conj`). "Note that the rooted conjectures imply the original unrooted conjectures." As an implication between the conjectures, it holds because the rooted
ones are false: `rootedConjecture_single_false`, `rootedConjecture_multiple_false`. Departure from the paper: its argument, "by letting `S` be the ancestral sequence that appears in the optimal phylogenetic network", is false as a step on one `M`: `fig6_hG_necessary`. See also `minDecomposable_of_sMinDecomposable`. -/
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

/-- Line 643: "`R¹(M_d(C₁)) = R¹(M_d(C₂)) = 2d`". The paper needs `≥` only, and leaves it as "straightforward". By the Hudson-Kaplan bound for `≥`, and the network of `Gusfield2007.Mosaic` for `≤`. -/
theorem Md_R_component (d : ℕ) :
    R .single (restrictRows (MdC₁ d) (Md d)) = 2 * d ∧ R .single (restrictRows (MdC₂ d) (Md d)) = 2 * d := by
  rw [compSet₁, compSet₂]
  exact ⟨R_comp_eq compData₁, R_comp_eq compData₂⟩

/-- **Theorem 11** (`g:thm11`). "For any positive integer `d`, there exists a set of sequences `M` such that `F¹(M) − R¹(M) ≥ d`" (line 631). The difference is written as a sum, so that the truncation on `ℕ`
plays no part. -/
theorem theorem11 (d : ℕ) (hd : 0 < d) :
    ∃ (m : ℕ) (M : Finset (Fin m → Bool)), M.Nonempty ∧ NoConstantColumn M ∧ R .single M + d ≤ F .single M := by
  refine ⟨6 * d, Md d, Md_nonempty, Md_noConstantColumn, ?_⟩
  have h := add_R_le_F .single Md_nonempty Md_noConstantColumn (A := MdC₁ d) Md_reachable (a := firstSite hd 1) (b := firstSite hd 0)
    (Or.inl (congrArg Fin.val (mod6_firstSite hd 1)))
    (fun h' => by
      have hm := congrArg Fin.val (mod6_firstSite hd 0)
      change (firstSite hd 0).val % 6 = 0 at hm
      change (firstSite hd 0).val % 6 = 1 ∨ (firstSite hd 0).val % 6 = 2 ∨ (firstSite hd 0).val % 6 = 4 at h'
      omega)
  rw [MdC₁_compl] at h
  obtain ⟨h₁, h₂⟩ := Md_R_component d
  have h₃ := Md_R_le d
  omega

end Gusfield2007
