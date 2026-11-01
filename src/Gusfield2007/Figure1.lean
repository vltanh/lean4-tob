module

public import Gusfield2007.Components
public import Gusfield2007.SuperCharacters

/-!
# Gusfield et al. 2007, Footnote 2: `T̄` isn't a perfect phylogeny on one site per component

The matrix of Figure 1, its two components, the tree `T` made from sites 1 and 2, and what `T̄` does with those sites.
-/

@[expose] public section

open scoped Classical

namespace Gusfield2007

theorem fig1_incompatible_side (i j : Fin 5) (h : Incompatible fig1 i j) : i ∈ fig1C ↔ j ∈ fig1C := by
  unfold Incompatible at h
  change (i = 0 ∨ i = 2 ∨ i = 3) ↔ (j = 0 ∨ j = 2 ∨ j = 3)
  revert h
  revert i j
  decide +kernel

/-- The two components of Figure 3: `C`, with the sites 1, 3, 4 of the paper, and `C′`, with the sites 2, 5. -/
theorem fig1_reachable (i j : Fin 5) : (incompatGraph fig1).Reachable i j ↔ (i ∈ fig1C ↔ j ∈ fig1C) := by
  refine reachable_iff_of_adj _ (fun i j hij => fig1_incompatible_side i j hij) (a := 0) (b := 1) (fun i hi => reachable_of_two_steps ?_) (fun i hi => reachable_of_two_steps ?_) i j
  · change i = 0 ∨ i = 2 ∨ i = 3 at hi
    change i = 0 ∨ Incompatible fig1 i 0 ∨ ∃ k, Incompatible fig1 i k ∧ Incompatible fig1 k 0
    unfold Incompatible
    revert hi
    revert i
    decide +kernel
  · change ¬ (i = 0 ∨ i = 2 ∨ i = 3) at hi
    change i = 1 ∨ Incompatible fig1 i 1 ∨ ∃ k, Incompatible fig1 i k ∧ Incompatible fig1 k 1
    unfold Incompatible
    revert hi
    revert i
    decide +kernel

theorem fig1_nonempty : fig1.Nonempty := ⟨ofBits [0, 0, 0, 1, 0], by decide +kernel⟩

theorem fig1_noConstantColumn : NoConstantColumn fig1 := by
  unfold NoConstantColumn
  decide +kernel

/-! ### The tree `T` from sites 1 and 2 -/

/-- The parent of a node of `T`: `0` has the state `00` on the two sites, `1` has `10`, `2` has `01`, and `3, ..., 9` are the leaves `a, ..., g`. -/
def fig1TPar (v : Fin 10) : Fin 10 := Fin.ofNat 10 ([0, 0, 0, 0, 1, 0, 1, 2, 2, 0].getD v 0)

/-- The tree `T` created from sites 1 and 2 of Figure 1. -/
def fig1T : SimpleGraph (Fin 10) where
  Adj u v := (u ≠ 0 ∧ fig1TPar u = v) ∨ (v ≠ 0 ∧ fig1TPar v = u)
  symm := ⟨fun _ _ h => h.symm⟩
  loopless := ⟨by decide⟩

instance : DecidableRel fig1T.Adj := fun _ _ => inferInstanceAs (Decidable (_ ∨ _))

/-- The leaf of a row. -/
def fig1Phi (r : fig1) : Fin 10 :=
  if r.1 = ofBits [0, 0, 0, 1, 0] then 3 else if r.1 = ofBits [1, 0, 0, 1, 0] then 4 else if r.1 = ofBits [0, 0, 1, 0, 0] then 5
  else if r.1 = ofBits [1, 0, 1, 0, 0] then 6 else if r.1 = ofBits [0, 1, 1, 0, 0] then 7 else if r.1 = ofBits [0, 1, 1, 0, 1] then 8 else 9

/-- The two columns of `T`: sites 1 and 2 of the paper. -/
def fig1A (r : fig1) (k : Fin 2) : Bool := r.1 (Fin.castLE (by decide) k)

/-- The edge of each of the two sites. -/
def fig1Edge (k : Fin 2) : Sym2 (Fin 10) := if k = 0 then s(0, 1) else s(0, 2)

/-- The state of a site at a node of `T`. -/
def fig1State (k : Fin 2) (v : Fin 10) : Bool :=
  if k = 0 then v = 1 ∨ v = 4 ∨ v = 6 else v = 2 ∨ v = 7 ∨ v = 8

theorem fig1T_isTree : fig1T.IsTree := by
  rw [SimpleGraph.isTree_iff_connected_and_card]
  refine ⟨⟨fun i j => ?_⟩, ?_⟩
  · have key : ∀ i, fig1T.Reachable i 0 := fun i => reachable_of_two_steps (by revert i; decide +kernel)
    exact (key i).trans (key j).symm
  · rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
    decide +kernel

theorem fig1T_perfect : IsPerfectPhylogeny fig1T fig1Phi fig1A fig1Edge where
  isTree := fig1T_isTree
  label_injective := by decide +kernel
  mem_range_iff v := by
    rw [Set.ncard_le_one_iff_subsingleton]
    have key : ∀ v, (∃ r, fig1Phi r = v) ↔ ∀ a b, fig1T.Adj v a → fig1T.Adj v b → a = b := by decide +kernel
    exact (key v).trans ⟨fun h a ha b hb => h a b ha hb, fun h a b ha hb => h ha hb⟩
  edge_mem k := by
    revert k
    decide +kernel
  split k x y := by
    have hphi : ∀ (k : Fin 2) (x : fig1), fig1A x k = fig1State k (fig1Phi x) := by decide +kernel
    rw [hphi, hphi]
    constructor
    · intro h
      have hrep : ∀ (k : Fin 2) (v : Fin 10), (let rep : Fin 10 := if fig1State k v then (if k = 0 then 1 else 2) else 0
          v = rep ∨ (fig1T.Adj v rep ∧ s(v, rep) ≠ fig1Edge k) ∨ ∃ w, (fig1T.Adj v w ∧ s(v, w) ≠ fig1Edge k) ∧ (fig1T.Adj w rep ∧ s(w, rep) ≠ fig1Edge k)) := by
        decide +kernel
      have hreach : ∀ v : Fin 10, (fig1T.deleteEdges {fig1Edge k}).Reachable v (if fig1State k v then (if k = 0 then 1 else 2) else 0) := fun v => by
        refine reachable_of_two_steps ?_
        simp only [SimpleGraph.deleteEdges_adj, Set.mem_singleton_iff]
        exact hrep k v
      have hx := hreach (fig1Phi x)
      have hy := hreach (fig1Phi y)
      rw [h] at hx
      exact hx.trans hy.symm
    · intro h
      have hadj : ∀ (k : Fin 2) (u v : Fin 10), fig1T.Adj u v → s(u, v) ≠ fig1Edge k → fig1State k u = fig1State k v := by decide +kernel
      unfold SameSide at h
      rw [SimpleGraph.reachable_iff_reflTransGen] at h
      generalize fig1Phi y = w at h ⊢
      induction h with
      | refl => rfl
      | tail _ huv ih =>
        rw [SimpleGraph.deleteEdges_adj, Set.mem_singleton_iff] at huv
        exact ih.trans (hadj k _ _ huv.1 huv.2)

/-! ### `T̄` -/

/-- In any graph, if `p`, `q` are on one side of `e₃` and on different sides of `e₁`, then `e₁` is on the side of `p`. -/
theorem sameSide_of_separated {W : Type*} {T : SimpleGraph W} {e₁ e₃ : Sym2 W} {v p q : W} (hv : v ∈ e₁) (h₃ : SameSide T e₃ p q) (h₁ : ¬ SameSide T e₁ p q) :
    SameSide T e₃ p v := by
  by_contra hnot
  refine h₁ ?_
  clear h₁
  unfold SameSide at *
  rw [SimpleGraph.reachable_iff_reflTransGen] at h₃
  have key : (T.deleteEdges {e₃}).Reachable p q ∧ (T.deleteEdges {e₁}).Reachable p q := by
    induction h₃ with
    | refl => exact ⟨SimpleGraph.Reachable.refl _, SimpleGraph.Reachable.refl _⟩
    | @tail w w' _ hadj ih =>
      obtain ⟨ih₃, ih₁⟩ := ih
      have hw' := ih₃.trans (SimpleGraph.Adj.reachable hadj)
      rw [SimpleGraph.deleteEdges_adj] at hadj
      refine ⟨hw', ih₁.trans (SimpleGraph.Adj.reachable ?_)⟩
      rw [SimpleGraph.deleteEdges_adj]
      refine ⟨hadj.1, fun he => ?_⟩
      have hv' : v ∈ s(w, w') := by
        rw [Set.mem_singleton_iff.1 he]
        exact hv
      rcases Sym2.mem_iff.1 hv' with rfl | rfl
      · exact hnot ih₃
      · exact hnot hw'
  exact key.2

/-- The row `c`. -/
def fig1RowC : Fin 5 → Bool := ofBits [0, 0, 1, 0, 0]

/-- The row `a`. -/
def fig1RowA : Fin 5 → Bool := ofBits [0, 0, 0, 1, 0]

theorem fig1RowC_mem : fig1RowC ∈ fig1 := by decide +kernel

theorem fig1RowA_mem : fig1RowA ∈ fig1 := by decide +kernel

/-- The character of `B` for the super-character `010` of `C`, the one of the rows `c, e, f, g`. -/
def fig1Char : SuperChar fig1 :=
  ⟨(incompatGraph fig1).connectedComponentMk 0, ⟨_, mem_restrictRows.2 ⟨fig1RowC, fig1RowC_mem, rfl⟩⟩⟩

theorem fig1Char_supp (i : Fin 5) : i ∈ fig1Char.1.supp ↔ i = 0 ∨ i = 2 ∨ i = 3 := by
  change i ∈ ((incompatGraph fig1).connectedComponentMk 0).supp ↔ _
  rw [SimpleGraph.ConnectedComponent.mem_supp_iff, SimpleGraph.ConnectedComponent.eq, fig1_reachable]
  have h₀ : (0 : Fin 5) ∈ fig1C := Or.inl rfl
  exact ⟨fun h => h.2 h₀, fun h => ⟨fun _ => h₀, fun _ => h⟩⟩

theorem charValue_fig1Char (r : Fin 5 → Bool) : charValue fig1Char r = true ↔ r 0 = false ∧ r 2 = true ∧ r 3 = false := by
  have h₀ : (0 : Fin 5) ∈ fig1Char.1.supp := (fig1Char_supp 0).2 (Or.inl rfl)
  have h₂ : (2 : Fin 5) ∈ fig1Char.1.supp := (fig1Char_supp 2).2 (Or.inr (Or.inl rfl))
  have h₃ : (3 : Fin 5) ∈ fig1Char.1.supp := (fig1Char_supp 3).2 (Or.inr (Or.inr rfl))
  refine (charValue_mk_iff (c := fig1Char.1) (S := fig1Char.2)).trans ?_
  constructor
  · intro h
    exact ⟨congrFun h ⟨0, h₀⟩, congrFun h ⟨2, h₂⟩, congrFun h ⟨3, h₃⟩⟩
  · rintro ⟨h0, h2, h3⟩
    funext ⟨i, hi⟩
    rcases (fig1Char_supp i).1 hi with rfl | rfl | rfl
    · exact h0
    · exact h2
    · exact h3

/-- **Footnote 2** (`g:footnote2`). "It may seem that `T̄` can be obtained by simply building a perfect phylogeny `T` using one site from each connected component of `G(M)`. However, this is wrong, because the edge structure of `T` may be very different from that of `T̄`. For example, in the tree `T`
created from sites 1 and 2 in Figure 1, the two edges labeled with those sites are adjacent, while they are not adjacent in `T̄`."

Sites 1 and 2 are in different components. `fig1T` is a perfect phylogeny for them, with all its internal edges labelled, and its two edges share the node `0`. `T̄` exists, and its edges carry super-characters rather than sites, so "the edges labeled with those sites" needs a reading. Here it is: the edges of
the super-characters in which the site has the state `1`, the state that labels the edge in `T`, with the root `00000` of Figure 1. No such edge for site 1 shares a node with one for site 2. The proof doesn't use uniqueness of `T̄`: the character `010` of `C` separates the rows beyond the first edge from the rows beyond the second. -/
theorem footnote2 :
    ¬ (incompatGraph fig1).Reachable 0 1 ∧
      (IsPerfectPhylogeny fig1T fig1Phi fig1A fig1Edge ∧ (∀ u v, fig1T.Adj u v → u ∉ Set.range fig1Phi → v ∉ Set.range fig1Phi → ∃ k, fig1Edge k = s(u, v)) ∧ ∃ v, v ∈ fig1Edge 0 ∧ v ∈ fig1Edge 1) ∧
      (∃ (n : ℕ) (T : SimpleGraph (Fin n)) (φ : fig1 → Fin n) (edge : SuperChar fig1 → Sym2 (Fin n)), IsTBar fig1 T φ edge) ∧
      ∀ {W : Type} {T : SimpleGraph W} {φ : fig1 → W} {edge : SuperChar fig1 → Sym2 W}, IsTBar fig1 T φ edge → ∀ k k' : SuperChar fig1,
        (∃ hi : (0 : Fin 5) ∈ k.1.supp, k.2.1 ⟨0, hi⟩ = true) → (∃ hi : (1 : Fin 5) ∈ k'.1.supp, k'.2.1 ⟨1, hi⟩ = true) → ∀ v ∈ edge k, v ∉ edge k' := by
  refine ⟨fun h => ?_, ⟨fig1T_perfect, ?_, 0, ?_, ?_⟩, exists_isTBar fig1 fig1_nonempty fig1_noConstantColumn, ?_⟩
  · have h₀ : (0 : Fin 5) ∈ fig1C := Or.inl rfl
    have h₁ : (1 : Fin 5) ∈ fig1C := ((fig1_reachable 0 1).1 h).1 h₀
    change (1 : Fin 5) = 0 ∨ (1 : Fin 5) = 2 ∨ (1 : Fin 5) = 3 at h₁
    revert h₁
    decide
  · have key : ∀ u v, fig1T.Adj u v → (¬ ∃ r, fig1Phi r = u) → (¬ ∃ r, fig1Phi r = v) → ∃ k, fig1Edge k = s(u, v) := by decide +kernel
    exact key
  · decide +kernel
  · decide +kernel
  · intro W T φ edge hT k k' hk hk' v hv hv'
    obtain ⟨c, S, hS⟩ := k
    obtain ⟨c', S', hS'⟩ := k'
    obtain ⟨hi, hval⟩ := hk
    obtain ⟨hi', hval'⟩ := hk'
    obtain ⟨r₀, hr₀, rfl⟩ := mem_restrictRows.1 hS
    obtain ⟨r₁, hr₁, rfl⟩ := mem_restrictRows.1 hS'
    have hr₀' : r₀ 0 = true := hval
    have hr₁' : r₁ 1 = true := hval'
    have hrows : ∀ r ∈ fig1, r 1 = true → r 0 = false ∧ r 2 = true ∧ r 3 = false := by decide +kernel
    let x : fig1 := ⟨r₀, hr₀⟩
    let y : fig1 := ⟨r₁, hr₁⟩
    let a : fig1 := ⟨fig1RowA, fig1RowA_mem⟩
    let c₀ : fig1 := ⟨fig1RowC, fig1RowC_mem⟩
    have hcx : charValue fig1Char x.1 = false := by
      rw [← Bool.not_eq_true, charValue_fig1Char]
      rintro ⟨h, -⟩
      rw [show x.1 0 = true from hr₀'] at h
      exact absurd h (by decide)
    have hca : charValue fig1Char a.1 = false := by
      rw [← Bool.not_eq_true, charValue_fig1Char]
      rintro ⟨-, h, -⟩
      exact absurd h (by decide +kernel)
    have hcy : charValue fig1Char y.1 = true := (charValue_fig1Char _).2 (hrows r₁ hr₁ hr₁')
    have hcc : charValue fig1Char c₀.1 = true := (charValue_fig1Char _).2 (by decide +kernel)
    -- The rows on the two sides of the two edges.
    have hkx : charValue (⟨c, _, hS⟩ : SuperChar fig1) x.1 = true := charValue_mk_iff.2 rfl
    have hka : charValue (⟨c, _, hS⟩ : SuperChar fig1) a.1 = false := by
      rw [← Bool.not_eq_true, charValue_mk_iff]
      intro h
      have h' : fig1RowA 0 = r₀ 0 := congrFun h ⟨0, hi⟩
      rw [hr₀'] at h'
      exact absurd h' (by decide +kernel)
    have hky : charValue (⟨c', _, hS'⟩ : SuperChar fig1) y.1 = true := charValue_mk_iff.2 rfl
    have hkc : charValue (⟨c', _, hS'⟩ : SuperChar fig1) c₀.1 = false := by
      rw [← Bool.not_eq_true, charValue_mk_iff]
      intro h
      have h' : fig1RowC 1 = r₁ 1 := congrFun h ⟨1, hi'⟩
      rw [hr₁'] at h'
      exact absurd h' (by decide +kernel)
    have s₁ : SameSide T (edge fig1Char) (φ x) (φ a) := (hT.split fig1Char x a).1 (hcx.trans hca.symm)
    have s₂ : SameSide T (edge fig1Char) (φ y) (φ c₀) := (hT.split fig1Char y c₀).1 (hcy.trans hcc.symm)
    have n₁ : ¬ SameSide T (edge ⟨c, _, hS⟩) (φ x) (φ a) := fun h => by
      have := (hT.split ⟨c, _, hS⟩ x a).2 h
      change charValue (⟨c, _, hS⟩ : SuperChar fig1) x.1 = charValue (⟨c, _, hS⟩ : SuperChar fig1) a.1 at this
      rw [hkx, hka] at this
      exact absurd this (by decide)
    have n₂ : ¬ SameSide T (edge ⟨c', _, hS'⟩) (φ y) (φ c₀) := fun h => by
      have := (hT.split ⟨c', _, hS'⟩ y c₀).2 h
      change charValue (⟨c', _, hS'⟩ : SuperChar fig1) y.1 = charValue (⟨c', _, hS'⟩ : SuperChar fig1) c₀.1 at this
      rw [hky, hkc] at this
      exact absurd this (by decide)
    have r₁' := sameSide_of_separated hv s₁ n₁
    have r₂' := sameSide_of_separated hv' s₂ n₂
    have hxy : SameSide T (edge fig1Char) (φ x) (φ y) := SimpleGraph.Reachable.trans r₁' (SimpleGraph.Reachable.symm r₂')
    have := (hT.split fig1Char x y).2 hxy
    change charValue fig1Char x.1 = charValue fig1Char y.1 at this
    rw [hcx, hcy] at this
    exact absurd this (by decide)

end Gusfield2007
