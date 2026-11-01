module

public import External.SongHein2005.Bound

/-!
# Gusfield et al. 2007, Figure 10 and `R¹(M_d) ≤ 3d`

The three trees of Figure 10, on the rows of Figure 6, with times from the heights of the figure, the three ordered-SPR operations between them, and "`L(P_d) = 3d ≥ R¹(M_d)`" (line 656). The rows are numbered from 0 here and from 1 in the figure.
-/

@[expose] public noncomputable section

namespace Gusfield2007

namespace TimeOrderedTree

variable {X Y : Type*} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]

/-- A tree with its leaves renamed. -/
def mapEquiv (T : TimeOrderedTree X) (e : X ≃ Y) : TimeOrderedTree Y where
  clusters := T.clusters.map (Equiv.finsetCongr e).toEmbedding
  isHierarchy := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [Finset.mem_map_equiv, Equiv.finsetCongr_symm, Equiv.finsetCongr_apply, Finset.map_univ_equiv]
      exact T.isHierarchy.1
    · intro y
      rw [Finset.mem_map_equiv, Equiv.finsetCongr_symm, Equiv.finsetCongr_apply, Finset.map_singleton]
      exact T.isHierarchy.2.1 (e.symm y)
    · intro A hA
      rw [Finset.mem_map_equiv] at hA
      have := T.isHierarchy.2.2.1 _ hA
      rwa [Equiv.finsetCongr_symm, Equiv.finsetCongr_apply, Finset.map_nonempty] at this
    · intro A hA B hB
      rw [Finset.mem_map_equiv] at hA hB
      rcases T.isHierarchy.2.2.2 _ hA _ hB with h | h | h
      · left
        simpa [Equiv.finsetCongr_symm] using h
      · right; left
        simpa [Equiv.finsetCongr_symm] using h
      · right; right
        simpa [Equiv.finsetCongr_symm] using h
  time D := T.time ((Equiv.finsetCongr e).symm D)
  time_lt A hA B hB hc hAB := by
    rw [Finset.mem_map_equiv] at hA hB
    refine T.time_lt _ hA _ hB (by simpa [Equiv.finsetCongr_symm] using hc) ?_
    simpa [Equiv.finsetCongr_symm] using hAB

variable {T T' : TimeOrderedTree X} {e : X ≃ Y}

theorem mem_clusters_mapEquiv {D : Finset Y} : D ∈ (T.mapEquiv e).clusters ↔ (Equiv.finsetCongr e).symm D ∈ T.clusters :=
  Finset.mem_map_equiv

omit [Fintype X] [Fintype Y] in
theorem symm_sdiff (e : X ≃ Y) (A B : Finset Y) : (Equiv.finsetCongr e).symm (A \ B) = (Equiv.finsetCongr e).symm A \ (Equiv.finsetCongr e).symm B := by
  simp [Equiv.finsetCongr_symm, Equiv.finsetCongr_apply, Finset.map_sdiff]

omit [Fintype X] [Fintype Y] in
theorem symm_union (e : X ≃ Y) (A B : Finset Y) : (Equiv.finsetCongr e).symm (A ∪ B) = (Equiv.finsetCongr e).symm A ∪ (Equiv.finsetCongr e).symm B := by
  simp [Equiv.finsetCongr_symm, Equiv.finsetCongr_apply, Finset.map_union]

omit [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y] in
theorem symm_subset (e : X ≃ Y) (A B : Finset Y) : (Equiv.finsetCongr e).symm A ⊆ (Equiv.finsetCongr e).symm B ↔ A ⊆ B := by
  simp [Equiv.finsetCongr_symm, Equiv.finsetCongr_apply]

omit [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y] in
theorem symm_card (e : X ≃ Y) (A : Finset Y) : ((Equiv.finsetCongr e).symm A).card = A.card := by
  simp [Equiv.finsetCongr_symm, Equiv.finsetCongr_apply]

theorem mem_prunedClusters_mapEquiv {A G : Finset Y} :
    G ∈ (T.mapEquiv e).prunedClusters A ↔ (Equiv.finsetCongr e).symm G ∈ T.prunedClusters ((Equiv.finsetCongr e).symm A) := by
  simp only [prunedClusters, Finset.mem_image, Finset.mem_filter]
  constructor
  · rintro ⟨B, ⟨hB, hBA⟩, rfl⟩
    exact ⟨_, ⟨mem_clusters_mapEquiv.1 hB, by rwa [symm_subset]⟩, (symm_sdiff e B A).symm⟩
  · rintro ⟨B, ⟨hB, hBA⟩, h⟩
    have hsym : (Equiv.finsetCongr e).symm (Equiv.finsetCongr e B) = B := Equiv.symm_apply_apply _ _
    refine ⟨Equiv.finsetCongr e B, ⟨mem_clusters_mapEquiv.2 (by rwa [hsym]), fun h' => hBA ?_⟩, ?_⟩
    · have := (symm_subset e _ _).2 h'
      rwa [hsym] at this
    · apply (Equiv.finsetCongr e).symm.injective
      rw [symm_sdiff, ← h, hsym]

theorem prunedTime_mapEquiv (A D : Finset Y) :
    (T.mapEquiv e).prunedTime A D = T.prunedTime ((Equiv.finsetCongr e).symm A) ((Equiv.finsetCongr e).symm D) := by
  unfold prunedTime
  by_cases h : (Equiv.finsetCongr e).symm D ∈ T.clusters
  · rw [ite_eq_left (mem_clusters_mapEquiv.2 h), ite_eq_left h]
    rfl
  · rw [ite_eq_right fun h' => h (mem_clusters_mapEquiv.1 h'), ite_eq_right h]
    change T.time _ = _
    rw [symm_union]

/-- An ordered-SPR operation with the leaves renamed. -/
theorem IsOrderedSPR.mapEquiv (h : T.IsOrderedSPR T') : (T.mapEquiv e).IsOrderedSPR (T'.mapEquiv e) := by
  obtain ⟨A, hA, hA', hne, hsub, htime, hpr, hprt⟩ := h
  have hsym : (Equiv.finsetCongr e).symm (Equiv.finsetCongr e A) = A := Equiv.symm_apply_apply _ _
  refine ⟨Equiv.finsetCongr e A, mem_clusters_mapEquiv.2 (by rwa [hsym]), mem_clusters_mapEquiv.2 (by rwa [hsym]), ?_, ?_, ?_, ?_, ?_⟩
  · intro h'
    apply hne
    rw [← hsym, h', Equiv.finsetCongr_symm, Equiv.finsetCongr_apply, Finset.map_univ_equiv]
  · intro B hB
    rw [mem_clusters_mapEquiv, mem_clusters_mapEquiv]
    refine hsub _ ?_
    rw [← hsym]
    exact (symm_subset e _ _).2 hB
  · intro B hB hBT hc
    refine htime _ ?_ (mem_clusters_mapEquiv.1 hBT) (by rwa [symm_card])
    rw [← hsym]
    exact (symm_subset e _ _).2 hB
  · ext G
    rw [mem_prunedClusters_mapEquiv, mem_prunedClusters_mapEquiv, hsym, hpr]
  · intro D hD hc
    rw [prunedTime_mapEquiv, prunedTime_mapEquiv, hsym]
    refine hprt _ ?_ (by rwa [symm_card])
    rw [← hsym]
    exact mem_prunedClusters_mapEquiv.1 hD

/-- Compatibility with a column, with the leaves renamed. -/
theorem CompatibleWith.mapEquiv {a : X → Bool} (h : T.CompatibleWith a) : (T.mapEquiv e).CompatibleWith (a ∘ e.symm) := by
  obtain ⟨C, hC, hne, hC'⟩ := h
  have hsym : (Equiv.finsetCongr e).symm (Equiv.finsetCongr e C) = C := Equiv.symm_apply_apply _ _
  refine ⟨Equiv.finsetCongr e C, mem_clusters_mapEquiv.2 (by rwa [hsym]), ?_, ?_⟩
  · intro h'
    apply hne
    rw [← hsym, h', Equiv.finsetCongr_symm, Equiv.finsetCongr_apply, Finset.map_univ_equiv]
  · have key : ∀ b : Bool, C = Finset.univ.filter (a · = b) → Equiv.finsetCongr e C = Finset.univ.filter ((a ∘ e.symm) · = b) := by
      rintro b rfl
      ext y
      simp [Equiv.finsetCongr_apply, Finset.mem_map_equiv]
    rcases hC' with h' | h'
    · exact Or.inl (key _ h')
    · exact Or.inr (key _ h')

/-- A tree is at distance zero from itself. -/
theorem same_refl (T : TimeOrderedTree X) : T.Same T := ⟨rfl, fun _ _ _ => rfl⟩

theorem doSPR_self_le (T : TimeOrderedTree X) : T.doSPR T ≤ 0 :=
  sInf_le ⟨0, same_refl T, rfl⟩

theorem doSPR_le_one (h : T.IsOrderedSPR T') : T.doSPR T' ≤ 1 :=
  sInf_le ⟨1, ⟨T', h, same_refl T'⟩, rfl⟩

/-- Trees with different clusters are at distance at least one, so at distance one if an operation connects them. -/
theorem doSPR_eq_one (h : T.IsOrderedSPR T') (hne : T.clusters ≠ T'.clusters) : T.doSPR T' = 1 := by
  refine le_antisymm (doSPR_le_one h) (le_sInf ?_)
  rintro _ ⟨k, hk, rfl⟩
  cases k with
  | zero => exact absurd hk.1 hne
  | succ k =>
    have : (1 : ℕ∞) ≤ ((k + 1 : ℕ) : ℕ∞) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le k)
    exact this

end TimeOrderedTree

namespace Figure10

/-- The heights of the nodes of Figure 10, from the top. -/
def height (D : Finset (Fin 6)) : ℕ :=
  if D = {0, 1, 2} ∨ D = {0, 1} ∨ D = {0, 1, 2, 5} then 35
  else if D = {3, 4, 5} ∨ D = {2, 3, 4, 5} ∨ D = {3, 4} then 55
  else if D = {4, 5} ∨ D = {2, 4, 5} then 92
  else if D = {1, 2} ∨ D = {1, 2, 5} then 115
  else if D = {2, 5} then 140
  else 10

/-- The leaves, and the root. -/
def common : Finset (Finset (Fin 6)) := {Finset.univ, {0}, {1}, {2}, {3}, {4}, {5}}

/-- A tree on the rows of Figure 6 with the times of Figure 10, when it's a hierarchy. -/
def mkTree (cl : Finset (Finset (Fin 6))) (h₁ : Finset.univ ∈ cl ∧ (∀ x : Fin 6, {x} ∈ cl) ∧ (∀ A ∈ cl, A.Nonempty) ∧ ∀ A ∈ cl, ∀ B ∈ cl, A ⊆ B ∨ B ⊆ A ∨ Disjoint A B)
    (h₂ : ∀ A ∈ cl, ∀ B ∈ cl, 2 ≤ A.card → A ⊂ B → height B < height A) : TimeOrderedTree (Fin 6) where
  clusters := cl
  isHierarchy := h₁
  time D := (height D : ℝ)
  time_lt A hA B hB hc hAB := Nat.cast_lt.2 (h₂ A hA B hB hc hAB)

/-- The tree `T_ux` of Figure 10. -/
def Tux : TimeOrderedTree (Fin 6) := mkTree ({{0, 1, 2}, {1, 2}, {3, 4, 5}, {4, 5}} ∪ common) (by decide +kernel) (by decide +kernel)

/-- The tree `T_y` of Figure 10. -/
def Ty : TimeOrderedTree (Fin 6) := mkTree ({{0, 1}, {2, 3, 4, 5}, {2, 4, 5}, {2, 5}} ∪ common) (by decide +kernel) (by decide +kernel)

/-- The tree `T_v` of Figure 10. -/
def Tv : TimeOrderedTree (Fin 6) := mkTree ({{0, 1, 2, 5}, {1, 2, 5}, {2, 5}, {3, 4}} ∪ common) (by decide +kernel) (by decide +kernel)

/-- An ordered-SPR operation between trees of this kind can be checked by computation, the times being natural numbers. -/
theorem isOrderedSPR_of_decide {cl cl' : Finset (Finset (Fin 6))} {h₁ h₂ h₁' h₂'} (A : Finset (Fin 6)) (hA : A ∈ cl ∧ A ∈ cl' ∧ A ≠ Finset.univ)
    (hsub : ∀ B ∈ A.powerset, B ∈ cl ↔ B ∈ cl')
    (hpr : (cl.filter fun B => ¬ B ⊆ A).image (· \ A) = (cl'.filter fun B => ¬ B ⊆ A).image (· \ A))
    (hprt : ∀ D ∈ (cl.filter fun B => ¬ B ⊆ A).image (· \ A), 2 ≤ D.card → (if D ∈ cl then height D else height (D ∪ A)) = if D ∈ cl' then height D else height (D ∪ A)) :
    (mkTree cl h₁ h₂).IsOrderedSPR (mkTree cl' h₁' h₂') := by
  refine ⟨A, hA.1, hA.2.1, hA.2.2, fun B hB => hsub B (Finset.mem_powerset.2 hB), fun _ _ _ _ => rfl, hpr, fun D hD hc => ?_⟩
  have := hprt D hD hc
  unfold TimeOrderedTree.prunedTime
  change (if D ∈ cl then (height D : ℝ) else (height (D ∪ A) : ℝ)) = if D ∈ cl' then (height D : ℝ) else (height (D ∪ A) : ℝ)
  split_ifs at this ⊢ <;> exact_mod_cast this

theorem spr_ux_y : Tux.IsOrderedSPR Ty := isOrderedSPR_of_decide {2} (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem spr_y_v : Ty.IsOrderedSPR Tv := isOrderedSPR_of_decide {2, 5} (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem spr_v_ux : Tv.IsOrderedSPR Tux := isOrderedSPR_of_decide {5} (by decide) (by decide) (by decide +kernel) (by decide +kernel)

/-- A row of Figure 6. -/
def rowOf (t : Fin 6) : Fin 6 → Bool := ofBits (fig6Table.getD t.val [])

theorem compat_of_decide {T : TimeOrderedTree (Fin 6)} {a : Fin 6 → Bool} (C : Finset (Fin 6))
    (h : C ∈ T.clusters ∧ C ≠ Finset.univ ∧ C = Finset.univ.filter (a · = true)) : T.CompatibleWith a :=
  ⟨C, h.1, h.2.1, Or.inl h.2.2⟩

theorem compat_ux_u : Tux.CompatibleWith fun t => rowOf t 0 := compat_of_decide {4, 5} (by decide +kernel)
theorem compat_ux_x : Tux.CompatibleWith fun t => rowOf t 1 := compat_of_decide {1, 2} (by decide +kernel)
theorem compat_y_y : Ty.CompatibleWith fun t => rowOf t 2 := compat_of_decide {0, 1} (by decide +kernel)
theorem compat_v_v : Tv.CompatibleWith fun t => rowOf t 3 := compat_of_decide {3, 4} (by decide +kernel)
theorem compat_ux_x' : Tux.CompatibleWith fun t => rowOf t 4 := compat_of_decide {1, 2} (by decide +kernel)
theorem compat_ux_u' : Tux.CompatibleWith fun t => rowOf t 5 := compat_of_decide {4, 5} (by decide +kernel)

theorem clusters_ux_ne_y : Tux.clusters ≠ Ty.clusters := by decide +kernel
theorem clusters_y_ne_v : Ty.clusters ≠ Tv.clusters := by decide +kernel
theorem clusters_v_ne_ux : Tv.clusters ≠ Tux.clusters := by decide +kernel

section Rename

variable {X : Type*} [Fintype X] [DecidableEq X] {e : Fin 6 ≃ X}

theorem clusters_mapEquiv_ne {T T' : TimeOrderedTree (Fin 6)} (h : T.clusters ≠ T'.clusters) : (T.mapEquiv e).clusters ≠ (T'.mapEquiv e).clusters := fun h' =>
  h (Finset.map_injective _ h')

/-- **Figure 10** (line 656), on any set of six named rows: the trees `T_ux`, `T_y`, `T_v`, compatible with the columns, with `d_oSPR(T_ux, T_y) = d_oSPR(T_y, T_v) = d_oSPR(T_v, T_ux) = 1`. -/
theorem exists_trees (e : Fin 6 ≃ X) : ∃ Tux' Ty' Tv' : TimeOrderedTree X,
    Tux'.CompatibleWith ((fun t => rowOf t 0) ∘ e.symm) ∧ Tux'.CompatibleWith ((fun t => rowOf t 1) ∘ e.symm) ∧
      Ty'.CompatibleWith ((fun t => rowOf t 2) ∘ e.symm) ∧ Tv'.CompatibleWith ((fun t => rowOf t 3) ∘ e.symm) ∧
      Tux'.doSPR Ty' = 1 ∧ Ty'.doSPR Tv' = 1 ∧ Tv'.doSPR Tux' = 1 :=
  ⟨Tux.mapEquiv e, Ty.mapEquiv e, Tv.mapEquiv e, compat_ux_u.mapEquiv, compat_ux_x.mapEquiv, compat_y_y.mapEquiv, compat_v_v.mapEquiv,
    TimeOrderedTree.doSPR_eq_one spr_ux_y.mapEquiv (clusters_mapEquiv_ne clusters_ux_ne_y),
    TimeOrderedTree.doSPR_eq_one spr_y_v.mapEquiv (clusters_mapEquiv_ne clusters_y_ne_v),
    TimeOrderedTree.doSPR_eq_one spr_v_ux.mapEquiv (clusters_mapEquiv_ne clusters_v_ne_ux)⟩

end Rename

theorem rowOf_injective : Function.Injective rowOf := by decide +kernel

theorem exists_ne_rowOf : ∀ a b : Fin 6, a ≠ b → ∃ s, rowOf a s ≠ rowOf b s := by decide +kernel

theorem mem_fig6 (t : Fin 6) : rowOf t ∈ fig6 := Finset.mem_image.2 ⟨t, by simp, rfl⟩

/-- The rows of Figure 6, named. -/
def eFig6 : Fin 6 ≃ fig6 :=
  Equiv.ofBijective (fun t => ⟨rowOf t, mem_fig6 t⟩) ⟨fun _ _ h => rowOf_injective (congrArg Subtype.val h), fun r => by
    obtain ⟨t, -, ht⟩ := Finset.mem_image.1 r.2
    exact ⟨t, Subtype.ext ht⟩⟩

theorem eFig6_symm (r : fig6) (s : Fin 6) : r.1 s = rowOf (eFig6.symm r) s :=
  congrFun (congrArg Subtype.val (eFig6.apply_symm_apply r)).symm s

/-- **Figure 10** (`g:figure10`, line 656): the trees `T_ux`, `T_y`, `T_v` on the rows of Figure 6, by the heights of their nodes. `T_ux` is compatible with the columns `u`, `x`, and `T_y` with `y`, and `T_v` with `v`,
and `d_oSPR(T_ux, T_y) = d_oSPR(T_y, T_v) = d_oSPR(T_v, T_ux) = 1`. -/
theorem _root_.Gusfield2007.figure10 {i₁ : Fintype fig6} {i₂ : DecidableEq fig6} : ∃ Tux' Ty' Tv' : @TimeOrderedTree fig6 i₁ i₂,
    Tux'.CompatibleWith (fun r => r.1 0) ∧ Tux'.CompatibleWith (fun r => r.1 1) ∧
      Ty'.CompatibleWith (fun r => r.1 2) ∧ Tv'.CompatibleWith (fun r => r.1 3) ∧
      Tux'.doSPR Ty' = 1 ∧ Ty'.doSPR Tv' = 1 ∧ Tv'.doSPR Tux' = 1 := by
  have hfun : ∀ s : Fin 6, (fun r : fig6 => r.1 s) = (fun t => rowOf t s) ∘ eFig6.symm := fun s => funext fun r => eFig6_symm r s
  simp only [hfun]
  exact exists_trees eFig6

/-! ### `M_d` -/

section Md

/-- The rows of `M_d`. -/
def rowMd (d : ℕ) (t : Fin 6) : Fin (6 * d) → Bool := fun j => rowOf t ⟨j.val % 6, Nat.mod_lt _ (by decide)⟩

theorem mem_Md (d : ℕ) (t : Fin 6) : rowMd d t ∈ Md d := Finset.mem_image.2 ⟨t, by simp, rfl⟩

/-- The rows of `M_d`, named, when `d` isn't zero. -/
def eMd {d : ℕ} (hd : 0 < d) : Fin 6 ≃ Md d :=
  Equiv.ofBijective (fun t => ⟨rowMd d t, mem_Md d t⟩) ⟨fun a b h => by
    by_contra hne
    obtain ⟨s, hs⟩ := exists_ne_rowOf a b hne
    have hlt : s.val < 6 * d := Nat.lt_of_lt_of_le s.2 (Nat.le_mul_of_pos_right 6 hd)
    have := congrFun (congrArg Subtype.val h) ⟨s.val, hlt⟩
    have hs' : (⟨s.val % 6, Nat.mod_lt _ (by decide)⟩ : Fin 6) = s := Fin.ext (Nat.mod_eq_of_lt s.2)
    change rowOf a ⟨s.val % 6, _⟩ = rowOf b ⟨s.val % 6, _⟩ at this
    rw [hs'] at this
    exact hs this, fun r => by
    obtain ⟨t, -, ht⟩ := Finset.mem_image.1 r.2
    exact ⟨t, Subtype.ext ht⟩⟩

theorem eMd_symm {d : ℕ} (hd : 0 < d) (r : Md d) (j : Fin (6 * d)) : r.1 j = rowOf ((eMd hd).symm r) ⟨j.val % 6, Nat.mod_lt _ (by decide)⟩ :=
  congrFun (congrArg Subtype.val ((eMd hd).apply_symm_apply r)).symm j

/-- The tree for a column of type `s` of `uxyvxu`: the sequence `P₁ = T_ux T_ux T_y T_v T_ux T_ux` of line 656. -/
def treeAt (n : ℕ) : TimeOrderedTree (Fin 6) := if n = 2 then Ty else if n = 3 then Tv else Tux

theorem compat_treeAt (s : Fin 6) : (treeAt s.val).CompatibleWith fun t => rowOf t s := by
  fin_cases s
  · exact compat_ux_u
  · exact compat_ux_x
  · exact compat_y_y
  · exact compat_v_v
  · exact compat_ux_x'
  · exact compat_ux_u'

/-- The cost between a column and the next: `T_ux` to `T_y`, `T_y` to `T_v`, `T_v` to `T_ux`. -/
def stepCost (j : ℕ) : ℕ := if j % 6 = 1 ∨ j % 6 = 2 ∨ j % 6 = 3 then 1 else 0

theorem sum_stepCost (d : ℕ) : (Finset.range (6 * d)).sum stepCost = 3 * d := by
  induction d with
  | zero => simp
  | succ d ih =>
    have hc : ∀ r, r < 6 → stepCost (6 * d + r) = stepCost r := by
      intro r _
      unfold stepCost
      rw [Nat.mul_add_mod]
    rw [show 6 * (d + 1) = 6 * d + 5 + 1 by ring, Finset.sum_range_succ, show 6 * d + 5 = 6 * d + 4 + 1 by ring, Finset.sum_range_succ, show 6 * d + 4 = 6 * d + 3 + 1 by ring,
      Finset.sum_range_succ, show 6 * d + 3 = 6 * d + 2 + 1 by ring, Finset.sum_range_succ, show 6 * d + 2 = 6 * d + 1 + 1 by ring, Finset.sum_range_succ,
      show 6 * d + 1 = 6 * d + 0 + 1 by ring, Finset.sum_range_succ, show 6 * d + 0 = 6 * d by ring, ih]
    rw [show 6 * d + 0 + 1 + 1 + 1 + 1 + 1 = 6 * d + 5 by ring, show 6 * d + 0 + 1 + 1 + 1 + 1 = 6 * d + 4 by ring, show 6 * d + 0 + 1 + 1 + 1 = 6 * d + 3 by ring, show 6 * d + 0 + 1 + 1 = 6 * d + 2 by ring, show 6 * d + 0 + 1 = 6 * d + 1 by ring]
    rw [hc 5 (by omega), hc 4 (by omega), hc 3 (by omega), hc 2 (by omega), hc 1 (by omega)]
    have h₀ : stepCost (6 * d) = stepCost 0 := by simpa using hc 0 (by omega)
    rw [h₀]
    simp only [stepCost]
    norm_num
    ring

variable {X : Type*} [Fintype X] [DecidableEq X]

theorem doSPR_treeAt_le (e : Fin 6 ≃ X) (j : ℕ) : ((treeAt (j % 6)).mapEquiv e).doSPR ((treeAt ((j + 1) % 6)).mapEquiv e) ≤ (stepCost j : ℕ∞) := by
  have h : j % 6 = 0 ∨ j % 6 = 1 ∨ j % 6 = 2 ∨ j % 6 = 3 ∨ j % 6 = 4 ∨ j % 6 = 5 := by omega
  rcases h with h | h | h | h | h | h
  · have h' : (j + 1) % 6 = 1 := by omega
    simp only [h, h', treeAt, stepCost]
    simpa using TimeOrderedTree.doSPR_self_le _
  · have h' : (j + 1) % 6 = 2 := by omega
    simp only [h, h', treeAt, stepCost]
    simpa using TimeOrderedTree.doSPR_le_one spr_ux_y.mapEquiv
  · have h' : (j + 1) % 6 = 3 := by omega
    simp only [h, h', treeAt, stepCost]
    simpa using TimeOrderedTree.doSPR_le_one spr_y_v.mapEquiv
  · have h' : (j + 1) % 6 = 4 := by omega
    simp only [h, h', treeAt, stepCost]
    simpa using TimeOrderedTree.doSPR_le_one spr_v_ux.mapEquiv
  · have h' : (j + 1) % 6 = 5 := by omega
    simp only [h, h', treeAt, stepCost]
    simpa using TimeOrderedTree.doSPR_self_le _
  · have h' : (j + 1) % 6 = 0 := by omega
    simp only [h, h', treeAt, stepCost]
    simpa using TimeOrderedTree.doSPR_self_le _

/-- `L(P)` for a sequence of trees, bounded step by step. -/
theorem sprLength_ofFn_le {m : ℕ} (P : Fin m → TimeOrderedTree X) (c : ℕ → ℕ)
    (h : ∀ j (hj : j + 1 < m), (P ⟨j, by omega⟩).doSPR (P ⟨j + 1, hj⟩) ≤ (c j : ℕ∞)) :
    sprLength (List.ofFn P) ≤ (((Finset.range (m - 1)).sum c : ℕ) : ℕ∞) := by
  set L := List.ofFn P with hL
  have hlen : L.length = m := List.length_ofFn
  have hdrop : ∀ (j : ℕ) (hj : j < m), L.drop j = P ⟨j, hj⟩ :: L.drop (j + 1) := by
    intro j hj
    have hget : L[j]'(by rw [hlen]; exact hj) = P ⟨j, hj⟩ := by simp [hL]
    rw [List.drop_eq_getElem_cons (by rw [hlen]; exact hj), hget]
  have key : ∀ k n, n + k + 1 = m → sprLength (L.drop n) ≤ (((Finset.range k).sum fun i => c (n + i) : ℕ) : ℕ∞) := by
    intro k
    induction k with
    | zero =>
      intro n hn
      have hn' : n < m := by omega
      rw [hdrop n hn', List.drop_eq_nil_of_le (by omega)]
      simp [sprLength]
    | succ k ih =>
      intro n hn
      have h₁ : n < m := by omega
      have h₂ : n + 1 < m := by omega
      rw [hdrop n h₁, hdrop (n + 1) h₂]
      change (P ⟨n, h₁⟩).doSPR (P ⟨n + 1, h₂⟩) + sprLength (P ⟨n + 1, h₂⟩ :: L.drop (n + 1 + 1)) ≤ _
      rw [← hdrop (n + 1) h₂, Finset.sum_range_succ']
      have h₃ := ih (n + 1) (by omega)
      have h₄ := h n h₂
      simp only [Nat.add_zero, Nat.cast_add]
      rw [add_comm]
      refine add_le_add ?_ h₄
      convert h₃ using 3
      congr 1
      omega
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm
    have hnil : L = [] := List.eq_nil_of_length_eq_zero hlen
    rw [hnil]
    simp [sprLength]
  · have := key (m - 1) 0 (by omega)
    simpa using this

end Md

/-- **Line 656** (`g:Md_R_le`). "`L(P_d) = 3d ≥ R¹(M_d)`", by the fact of Song and Hein and the three trees of Figure 10. -/
theorem _root_.Gusfield2007.Md_R_le (d : ℕ) : R .single (Md d) ≤ 3 * d := by
  have hM : (Md d).Nonempty := ⟨_, mem_Md d 0⟩
  rcases Nat.eq_zero_or_pos d with hd | hd
  · subst hd
    let P : Fin (6 * 0) → TimeOrderedTree (Md 0) := fun i => i.elim0
    have h₁ := SongHein2005.R_le_sprLength (Md 0) hM P (fun i => i.elim0)
    have h₂ := sprLength_ofFn_le P stepCost (fun j hj => absurd hj (by omega))
    have h₃ : (R .single (Md 0) : ℕ∞) ≤ 0 := h₁.trans (by simpa using h₂)
    simpa using h₃
  · let P : Fin (6 * d) → TimeOrderedTree (Md d) := fun j => (treeAt (j.val % 6)).mapEquiv (eMd hd)
    have hP : ∀ j, (P j).CompatibleWith fun r => r.1 j := by
      intro j
      have hc := compat_treeAt ⟨j.val % 6, Nat.mod_lt _ (by decide)⟩
      have := TimeOrderedTree.CompatibleWith.mapEquiv (e := eMd hd) hc
      have hfun : (fun r : Md d => r.1 j) = (fun t => rowOf t ⟨j.val % 6, Nat.mod_lt _ (by decide)⟩) ∘ (eMd hd).symm := funext fun r => eMd_symm hd r j
      rw [hfun]
      exact this
    have h₁ := SongHein2005.R_le_sprLength (Md d) hM P hP
    have h₂ := sprLength_ofFn_le P stepCost (fun j _ => doSPR_treeAt_le (eMd hd) j)
    have h₃ : (Finset.range (6 * d - 1)).sum stepCost ≤ 3 * d := by
      rw [← sum_stepCost d]
      exact Finset.sum_le_sum_of_subset (Finset.range_mono (by omega))
    have h₄ : (R .single (Md d) : ℕ∞) ≤ ((3 * d : ℕ) : ℕ∞) := h₁.trans (h₂.trans (by exact_mod_cast h₃))
    exact_mod_cast h₄

end Figure10

end Gusfield2007
