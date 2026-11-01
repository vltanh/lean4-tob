module

public import External.GusfieldEtAl2004.ReducedUnrooted

/-!
# Theorem 2.2 of Gusfield, Eddhu, Langley 2004: the arrays W1, W2, W3 and the recombination point

See the `README.md` of this directory. `GalledTree.lean` has the coordinates (`exists_threshold`), which cover the three arrays at once for any crossovers. This module states the theorem as the source does, for single crossovers. The proof is the source's: the three pairs are at nodes of the gall, and the placements
that don't give them are excluded one by one.

A node of the gall is given by the start `c` of a side: `P = c ++ d`, with `d` not empty so that the node isn't the recombination node. "A branching node below `i`" has the arc of `i` on `c`, and "a branching node between `j` and `i`" has the arc of `j` on `c` and not that of `i`.

Departure from the source: `Algorithm.lean` doesn't call this theorem. The source reads the recombination point from the bipartition of Lemma 3.1, which rests on Theorem 2.2, and `Algorithm.lean` tries the points instead, and checks that the chains give the recombination node.
-/

@[expose] public noncomputable section

open scoped Classical

namespace GusfieldEtAl2004

open Gusfield2007 Gusfield2007.Network

variable {ι V E : Type*} {N : Network ι V E} {w x : V} {p q : List E}

/-- **Definition 2.6** of the source: a branching node of a recombination cycle has an edge to a node not on the cycle. -/
def IsBranching (N : Network ι V E) (Q : Set E) (v : V) : Prop := ∃ g, N.src g = v ∧ N.tgt g ∉ N.blobVerts Q

/-- A branching node of the cycle on the side `P`, other than the recombination node, below the arc of `i`. -/
def BranchBelow (N : Network ι V E) (w : V) (Q : Set E) (P : List E) (i : ι) : Prop :=
  ∃ c d v, P = c ++ d ∧ d ≠ [] ∧ N.IsPath w v c ∧ N.site i ∈ c ∧ IsBranching N Q v

/-- A branching node of the cycle on the side `P` between the arc of `j`, above, and that of `i`. -/
def BranchBetween (N : Network ι V E) (w : V) (Q : Set E) (P : List E) (j i : ι) : Prop :=
  ∃ c d v, P = c ++ d ∧ d ≠ [] ∧ N.IsPath w v c ∧ N.site j ∈ c ∧ N.site i ∉ c ∧ IsBranching N Q v

/-- `L₀` is a recombination point of the recombination node of the cycle: a prefix from the side `p`, the `P`-side, and the rest from the side `q`, the `S`-side. -/
def IsRecombPoint [LinearOrder ι] (N : Network ι V E) (x : V) (p q : List E) (L₀ : LowerSet ι) : Prop :=
  ∃ a b, a ∈ p ∧ b ∈ q ∧ N.tgt a = x ∧ N.tgt b = x ∧ ∀ s, N.label x s = if s ∈ L₀ then N.label (N.src a) s else N.label (N.src b) s

/-- The array **W1** of the source: `i` on the `P`-side, `j` on the `S`-side, and a branching node below each. -/
def W1 (N : Network ι V E) (w : V) (p q : List E) (i j : ι) : Prop :=
  N.site i ∈ p ∧ N.site j ∈ q ∧ BranchBelow N w {e | e ∈ p ∨ e ∈ q} p i ∧ BranchBelow N w {e | e ∈ p ∨ e ∈ q} q j

/-- The array **W2** of the source: both on the `P`-side, `j` above `i`, a branching node between them and a branching node below `i`. -/
def W2 (N : Network ι V E) (w : V) (p q : List E) (i j : ι) : Prop :=
  N.site i ∈ p ∧ N.site j ∈ p ∧ BranchBetween N w {e | e ∈ p ∨ e ∈ q} p j i ∧ BranchBelow N w {e | e ∈ p ∨ e ∈ q} p i

/-- The array **W3** of the source: both on the `S`-side, `i` above `j`, a branching node between them and a branching node below `j`. -/
def W3 (N : Network ι V E) (w : V) (p q : List E) (i j : ι) : Prop :=
  N.site i ∈ q ∧ N.site j ∈ q ∧ BranchBetween N w {e | e ∈ p ∨ e ∈ q} q i j ∧ BranchBelow N w {e | e ∈ p ∨ e ∈ q} q j

variable [Finite V] {M : Finset (ι → Bool)}

/-- A branching node gives a row with its states on the gall (Lemma 2.1 of the source). -/
theorem row_of_branching (hG : IsGalledTree N) (hc : N.IsCycleOn w x p q) (hD : N.Derives M) {v : V} (hv : v ∈ N.blobVerts {e | e ∈ p ∨ e ∈ q}) (hb : IsBranching N {e | e ∈ p ∨ e ∈ q} v) :
    ∃ r ∈ M, ∀ s, N.site s ∈ {e | e ∈ p ∨ e ∈ q} → r s = N.label v s := by
  obtain ⟨g, rfl, hg⟩ := hb
  obtain ⟨y, hy, hgy⟩ := N.exists_isLeaf_reach (N.tgt g)
  have hoff : ∀ u ∈ N.blobVerts {e | e ∈ p ∨ e ∈ q}, ¬ N.Reach (N.tgt g) u := by
    intro u hu hr
    exact not_reach_tgt_src g ((reach_coalescent_of_reach_mem hG hc hg hu hr).trans (coalescent_reach_of_mem hc hv))
  refine ⟨N.label y, Finset.mem_coe.1 (hD.mapsTo hy), fun s hs => ?_⟩
  rw [label_of_reach_off hG hc hgy hoff hs, label_tgt_of_notMem hG hc hg hs]

/-- A row with a pair other than those of the root and of the recombination node at two sites of a gall is at a branching node of a side. -/
theorem branching_of_row (hG : IsGalledTree N) (hc : N.IsCycleOn w x p q) (hD : N.Derives M) {r : ι → Bool} (hr : r ∈ M) {i j : ι} (hi : N.site i ∈ {e | e ∈ p ∨ e ∈ q}) (hj : N.site j ∈ {e | e ∈ p ∨ e ∈ q})
    (hne : r i ≠ N.label x i ∨ r j ≠ N.label x j) (hf : r i ≠ N.label N.root i ∨ r j ≠ N.label N.root j) :
    ∃ v ∈ N.blobVerts {e | e ∈ p ∨ e ∈ q}, v ≠ x ∧ IsBranching N {e | e ∈ p ∨ e ∈ q} v ∧ ∀ s, N.site s ∈ {e | e ∈ p ∨ e ∈ q} → r s = N.label v s := by
  obtain ⟨y, hy, rfl⟩ := hD.surjOn hr
  have hreach : N.Reach w y := by
    rcases hf with h | h
    · exact (cycle_reach_src hc hi).trans ((reach_src_tgt _).trans (N.reach_of_label_ne h))
    · exact (cycle_reach_src hc hj).trans ((reach_src_tgt _).trans (N.reach_of_label_ne h))
  obtain ⟨l, hl⟩ := hreach.exists_isPath
  obtain ⟨b, p₁, p₂, -, -, hp₂, hb, hf'⟩ := hl.exists_last (fun v => v ∈ N.blobVerts {e | e ∈ p ∨ e ∈ q}) (coalescent_mem hc)
  have hbx : b ≠ x := by
    rintro rfl
    rcases hne with h | h
    · exact h (label_of_reach hG hc hp₂.reach hi)
    · exact h (label_of_reach hG hc hp₂.reach hj)
  cases p₂ with
  | nil =>
    exfalso
    have hby : b = y := hp₂
    rcases Relation.ReflTransGen.cases_head (cycle_reach_of_mem hc hb) with h | ⟨z, ⟨e, he, -⟩, -⟩
    · exact hbx h
    · exact hy e (he.trans hby)
  | cons f p₃ => exact ⟨b, hb, hbx, ⟨f, hp₂.1, hf' f (by simp)⟩, fun s hs => label_along hG hc hs hp₂ hf'⟩

/-- A node of a gall other than the recombination node is at the end of the start of a side, and the states there are read off that start. -/
theorem side_of_mem (hG : IsGalledTree N) (hc : N.IsCycleOn w x p q) {v : V} (hv : v ∈ N.blobVerts {e | e ∈ p ∨ e ∈ q}) (hvx : v ≠ x) :
    (∃ c d, p = c ++ d ∧ d ≠ [] ∧ N.IsPath w v c ∧ ∀ s, N.site s ∈ {e | e ∈ p ∨ e ∈ q} → (N.label v s ≠ N.label N.root s ↔ N.site s ∈ c)) ∨
      ∃ c d, q = c ++ d ∧ d ≠ [] ∧ N.IsPath w v c ∧ ∀ s, N.site s ∈ {e | e ∈ p ∨ e ∈ q} → (N.label v s ≠ N.label N.root s ↔ N.site s ∈ c) := by
  rcases cycle_mem_cases hc hv with h | ⟨c, d, h₁, h₂, h₃⟩ | ⟨c, d, h₁, h₂, h₃⟩
  · exact absurd h hvx
  · exact Or.inl ⟨c, d, h₁, h₂, h₃, fun s hs => label_cut hG hc h₁ h₂ h₃ hs⟩
  · exact Or.inr ⟨c, d, h₁, h₂, h₃, fun s hs => label_cut hG hc.symm h₁ h₂ h₃ (Or.symm hs)⟩

/-- The states of a parent of the recombination node are read off its side. -/
theorem parent_ne_iff (hG : IsGalledTree N) (hc : N.IsCycleOn w x p q) {a : E} (ha : a ∈ p) (hax : N.tgt a = x) {s : ι} (hs : N.site s ∈ {e | e ∈ p ∨ e ∈ q}) :
    N.label (N.src a) s ≠ N.label N.root s ↔ N.site s ∈ p := by
  obtain ⟨P₀, a', hP₀, hpath, hlast⟩ := hc.2.1.exists_last_arc hc.ne_nil
  obtain rfl : a' = a := path_eq_of_tgt_eq hc.2.1 (by rw [hP₀]; simp) ha (hlast.trans hax.symm)
  rw [label_cut hG hc hP₀ (by simp) hpath hs]
  obtain ⟨a₂, b₂, ha₂, hb₂, hab₂, hax₂, hbx₂⟩ := cycle_last_arcs hc
  obtain rfl : a₂ = a' := path_eq_of_tgt_eq hc.2.1 ha₂ ha (hax₂.trans hax.symm)
  have hsa : N.site s ≠ a₂ := site_ne_of_tgt_eq hab₂ (hax₂.trans hbx₂.symm) s
  constructor
  · intro h
    rw [hP₀]
    exact List.mem_append_left _ h
  · intro h
    rw [hP₀] at h
    rcases List.mem_append.1 h with h' | h'
    · exact h'
    · exact absurd (List.mem_singleton.1 h') hsa

section Point

variable [LinearOrder ι]

/-- **Theorem 2.2** (`ext:thm2_2`) of the source. "Let `T` be a galled-tree for matrix `M`. Two sites `i` and `j > i` in `M` conflict if and only if the following conditions hold: a) `i` and `j` are together on the same gall (call it `Q`) in `T`, with recombination node `x`, and `i < r_x ≤ j`. b) Sites `i` and `j` are arrayed on `Q` in one of the following three ways": W1, W2, W3.

Here `r_x` is the lower set `L₀` of `IsRecombPoint`, of which `i < r_x ≤ j` says that it has `i` and not `j`, the `P`-side is `p` and the `S`-side is `q`. The ancestral sequence is any, in place of all `0`. The proof is the source's. -/
theorem theorem2_2 (hG : IsGalledTree N) (hc₁ : N.Obeys .single) (hD : N.Derives M) {i j : ι} (hij : i < j) :
    Conflict N.ancestral M i j ↔ ∃ w x p q L₀, N.IsCycleOn w x p q ∧ IsRecombPoint N x p q L₀ ∧ i ∈ L₀ ∧ j ∉ L₀ ∧ (W1 N w p q i j ∨ W2 N w p q i j ∨ W3 N w p q i j) := by
  have hne : ∀ b : Bool, (!b) ≠ b := by decide
  have hroot : ∀ s, N.ancestral s = N.label N.root s := fun _ => rfl
  constructor
  · intro hcon
    have hL : ∀ r ∈ addRow M N.ancestral, ∃ v, N.label v = r := labels_addRow hD
    have hinc : Incompatible (addRow M N.ancestral) i j := (conflict_iff_incompatible_addRow _ _ _ _).1 hcon
    obtain ⟨Q, ⟨w, x, p₀, q₀, hc₀, rfl⟩, hsi₀, hsj₀⟩ := exists_isCycle_of_incompatible N hL hinc
    obtain ⟨e, f, hef, he, hf, L₀, hL₀⟩ := hc₁ x hc₀.1
    -- the sides, with `e` on the first
    obtain ⟨p, q, hc, hQ, hep, hfq⟩ : ∃ p q, N.IsCycleOn w x p q ∧ {g | g ∈ p ∨ g ∈ q} = {g | g ∈ p₀ ∨ g ∈ q₀} ∧ e ∈ p ∧ f ∈ q := by
      obtain ⟨a, b, ha, hb, hab, hax, hbx⟩ := cycle_last_arcs hc₀
      rcases eq_or_eq_of_tgt hab (hax.trans hbx.symm) (he.trans hax.symm) with rfl | rfl
      · rcases eq_or_eq_of_tgt hab (hax.trans hbx.symm) (hf.trans hax.symm) with rfl | rfl
        · exact absurd rfl hef
        · exact ⟨p₀, q₀, hc₀, rfl, ha, hb⟩
      · rcases eq_or_eq_of_tgt hab (hax.trans hbx.symm) (hf.trans hax.symm) with rfl | rfl
        · exact ⟨q₀, p₀, hc₀.symm, by ext g; exact or_comm, hb, ha⟩
        · exact absurd rfl hef
    have hsi : N.site i ∈ {g | g ∈ p ∨ g ∈ q} := hQ ▸ hsi₀
    have hsj : N.site j ∈ {g | g ∈ p ∨ g ∈ q} := hQ ▸ hsj₀
    -- `i` and `j` come from different parents
    obtain ⟨hiL, hjL⟩ : i ∈ L₀ ∧ j ∉ L₀ := by
      by_cases hiL : i ∈ L₀ <;> by_cases hjL : j ∈ L₀
      · exfalso
        rcases parent_pair_ne hG hc hL hsi hsj hinc (Or.inl hep) he with h | h
        · exact h (by rw [hL₀ i, ite_eq_left hiL])
        · exact h (by rw [hL₀ j, ite_eq_left hjL])
      · exact ⟨hiL, hjL⟩
      · exact absurd (L₀.lower hij.le hjL) hiL
      · exfalso
        rcases parent_pair_ne hG hc hL hsi hsj hinc (Or.inr hfq) hf with h | h
        · exact h (by rw [hL₀ i, ite_eq_right hiL])
        · exact h (by rw [hL₀ j, ite_eq_right hjL])
    refine ⟨w, x, p, q, L₀, hc, ⟨e, f, hep, hfq, he, hf, hL₀⟩, hiL, hjL, ?_⟩
    -- the states at the recombination node
    have hxi : N.label x i ≠ N.ancestral i ↔ N.site i ∈ p := by
      rw [hL₀ i, ite_eq_left hiL, hroot]
      exact parent_ne_iff hG hc hep he hsi
    have hxj : N.label x j ≠ N.ancestral j ↔ N.site j ∈ q := by
      rw [hL₀ j, ite_eq_right hjL, hroot]
      exact parent_ne_iff hG hc.symm hfq hf (Or.symm hsj)
    have hpq : ∀ {g}, g ∈ p → g ∉ q := fun hg => hc.notMem hg
    -- each of the three rows is at a node on a side
    have hrow : ∀ a b : Bool, (a ≠ N.ancestral i ∨ b ≠ N.ancestral j) → (a ≠ N.label x i ∨ b ≠ N.label x j) → ∃ (P : List E) (c d : List E) (v : V), (P = p ∨ P = q) ∧ P = c ++ d ∧ d ≠ [] ∧ N.IsPath w v c ∧ IsBranching N {g | g ∈ p ∨ g ∈ q} v ∧
        (N.site i ∈ c ↔ a ≠ N.ancestral i) ∧ (N.site j ∈ c ↔ b ≠ N.ancestral j) := by
      intro a b hab hax
      obtain ⟨r, hr, h₁, h₂⟩ := hcon a b hab
      obtain ⟨v, hv, hvx, hbr, hrv⟩ := branching_of_row hG hc hD hr hsi hsj (by rw [h₁, h₂]; exact hax) (by rw [h₁, h₂]; exact hab)
      have hri : ∀ c : List E, (∀ s, N.site s ∈ {g | g ∈ p ∨ g ∈ q} → (N.label v s ≠ N.label N.root s ↔ N.site s ∈ c)) → (N.site i ∈ c ↔ a ≠ N.ancestral i) ∧ (N.site j ∈ c ↔ b ≠ N.ancestral j) := by
        intro c hcs
        constructor
        · rw [← hcs i hsi, ← hrv i hsi, h₁]
          rfl
        · rw [← hcs j hsj, ← hrv j hsj, h₂]
          rfl
      rcases side_of_mem hG hc hv hvx with ⟨c, d, h₃, h₄, h₅, h₆⟩ | ⟨c, d, h₃, h₄, h₅, h₆⟩
      · exact ⟨p, c, d, v, Or.inl rfl, h₃, h₄, h₅, hbr, hri c h₆⟩
      · exact ⟨q, c, d, v, Or.inr rfl, h₃, h₄, h₅, hbr, hri c h₆⟩
    have hmemc : ∀ {P c d : List E} {g : E}, P = c ++ d → g ∈ c → g ∈ P := fun h hg => h ▸ List.mem_append_left _ hg
    -- the placement
    rcases hsi with hip | hiq <;> rcases hsj with hjp | hjq
    · -- both on the `P`-side: W2
      have hjq : N.site j ∉ q := hpq hjp
      have hxj' : N.label x j = N.ancestral j := by
        by_contra h
        exact hjq (hxj.1 h)
      have hxi' : N.label x i ≠ N.ancestral i := hxi.2 hip
      obtain ⟨P₁, c₁, d₁, v₁, hP₁, h₁, h₂, h₃, h₄, h₅, h₆⟩ := hrow (N.ancestral i) (!N.ancestral j) (Or.inr (hne _)) (Or.inr (by rw [hxj']; exact hne _))
      obtain ⟨P₂, c₂, d₂, v₂, hP₂, h₁', h₂', h₃', h₄', h₅', -⟩ := hrow (!N.ancestral i) (!N.ancestral j) (Or.inr (hne _)) (Or.inr (by rw [hxj']; exact hne _))
      have hjc₁ := h₆.2 (hne _)
      obtain rfl : P₁ = p := by
        rcases hP₁ with h | rfl
        · exact h
        · exact absurd (hmemc h₁ hjc₁) hjq
      have hic₂ := h₅'.2 (hne _)
      obtain rfl : P₂ = P₁ := by
        rcases hP₂ with h | rfl
        · exact h
        · exact absurd (hmemc h₁' hic₂) (hpq hip)
      refine Or.inr (Or.inl ⟨hip, hjp, ⟨c₁, d₁, v₁, h₁, h₂, h₃, hjc₁, fun h => ?_, h₄⟩, ⟨c₂, d₂, v₂, h₁', h₂', h₃', hic₂, h₄'⟩⟩)
      exact (h₅.1 h) rfl
    · -- `i` on the `P`-side, `j` on the `S`-side: W1
      have hxi' : N.label x i ≠ N.ancestral i := hxi.2 hip
      have hxj' : N.label x j ≠ N.ancestral j := hxj.2 hjq
      have hbool : ∀ {u v : Bool}, u ≠ v → v ≠ u := fun h h' => h h'.symm
      obtain ⟨P₁, c₁, d₁, v₁, hP₁, h₁, h₂, h₃, h₄, h₅, -⟩ := hrow (!N.ancestral i) (N.ancestral j) (Or.inl (hne _)) (Or.inr (hbool hxj'))
      obtain ⟨P₂, c₂, d₂, v₂, hP₂, h₁', h₂', h₃', h₄', -, h₆'⟩ := hrow (N.ancestral i) (!N.ancestral j) (Or.inr (hne _)) (Or.inl (hbool hxi'))
      have hic₁ := h₅.2 (hne _)
      have hjc₂ := h₆'.2 (hne _)
      obtain rfl : P₁ = p := by
        rcases hP₁ with h | rfl
        · exact h
        · exact absurd (hmemc h₁ hic₁) (hpq hip)
      obtain rfl : P₂ = q := by
        rcases hP₂ with rfl | h
        · exact absurd hjq (hpq (hmemc h₁' hjc₂))
        · exact h
      exact Or.inl ⟨hip, hjq, ⟨c₁, d₁, v₁, h₁, h₂, h₃, hic₁, h₄⟩, ⟨c₂, d₂, v₂, h₁', h₂', h₃', hjc₂, h₄'⟩⟩
    · -- `i` on the `S`-side, `j` on the `P`-side: the pair at the recombination node is the root's, and the pair `1, 1` is missing
      exfalso
      have hxi' : N.label x i = N.ancestral i := by
        by_contra h
        exact hpq (hxi.1 h) hiq
      obtain ⟨P₁, c₁, d₁, v₁, hP₁, h₁, -, -, -, h₅, h₆⟩ := hrow (!N.ancestral i) (!N.ancestral j) (Or.inl (hne _)) (Or.inl (by rw [hxi']; exact hne _))
      have hic := h₅.2 (hne _)
      have hjc := h₆.2 (hne _)
      rcases hP₁ with rfl | rfl
      · exact hpq (hmemc h₁ hic) hiq
      · exact hpq hjp (hmemc h₁ hjc)
    · -- both on the `S`-side: W3
      have hxi' : N.label x i = N.ancestral i := by
        by_contra h
        exact hc.symm.notMem hiq (hxi.1 h)
      obtain ⟨P₁, c₁, d₁, v₁, hP₁, h₁, h₂, h₃, h₄, h₅, h₆⟩ := hrow (!N.ancestral i) (N.ancestral j) (Or.inl (hne _)) (Or.inl (by rw [hxi']; exact hne _))
      obtain ⟨P₂, c₂, d₂, v₂, hP₂, h₁', h₂', h₃', h₄', -, h₆'⟩ := hrow (!N.ancestral i) (!N.ancestral j) (Or.inl (hne _)) (Or.inl (by rw [hxi']; exact hne _))
      have hic₁ := h₅.2 (hne _)
      have hjc₂ := h₆'.2 (hne _)
      obtain rfl : P₁ = q := by
        rcases hP₁ with rfl | h
        · exact absurd hiq (hpq (hmemc h₁ hic₁))
        · exact h
      obtain rfl : P₂ = P₁ := by
        rcases hP₂ with rfl | h
        · exact absurd hjq (hpq (hmemc h₁' hjc₂))
        · exact h
      refine Or.inr (Or.inr ⟨hiq, hjq, ⟨c₁, d₁, v₁, h₁, h₂, h₃, hic₁, fun h => ?_, h₄⟩, ⟨c₂, d₂, v₂, h₁', h₂', h₃', hjc₂, h₄'⟩⟩)
      exact (h₆.1 h) rfl
  · -- the sufficient direction: each pair is at a node, and so at a row
    rintro ⟨w, x, p, q, L₀, hc, ⟨a, b, ha, hb, hax, hbx, hL₀⟩, hiL, hjL, hW⟩
    have hend : ∀ {l : List E} {u v v' : V}, N.IsPath u v l → N.IsPath u v' l → v = v' := by
      intro l
      induction l with
      | nil => exact fun h h' => (show _ = _ from h).symm.trans h'
      | cons e l ih => exact fun h h' => ih h.2 h'.2
    have hrowAt : ∀ {P P' : List E}, N.IsCycleOn w x P P' → {g | g ∈ P ∨ g ∈ P'} = {g | g ∈ p ∨ g ∈ q} → ∀ {c d : List E} {v : V}, P = c ++ d → d ≠ [] → N.IsPath w v c → IsBranching N {g | g ∈ p ∨ g ∈ q} v →
        ∃ r ∈ M, ∀ s, N.site s ∈ {g | g ∈ p ∨ g ∈ q} → (r s ≠ N.ancestral s ↔ N.site s ∈ c) := by
      intro P P' hcP hset c d v hP hd hv hbr
      have hvm : v ∈ N.blobVerts {g | g ∈ P ∨ g ∈ P'} := by
        cases d with
        | nil => exact absurd rfl hd
        | cons g d' =>
          have hpath := hcP.2.1
          rw [hP, isPath_append] at hpath
          obtain ⟨y, h₁, h₂⟩ := hpath
          exact Or.inl ⟨g, Or.inl (by rw [hP]; simp), h₂.1.trans (hend h₁ hv)⟩
      have hvm' : v ∈ N.blobVerts {g | g ∈ p ∨ g ∈ q} := hset ▸ hvm
      obtain ⟨r, hr, hrv⟩ := row_of_branching hG hc hD hvm' hbr
      refine ⟨r, hr, fun s hs => ?_⟩
      rw [hrv s hs, hroot]
      exact label_cut hG hcP hP hd hv (hset ▸ hs)
    have hset' : {g | g ∈ q ∨ g ∈ p} = {g | g ∈ p ∨ g ∈ q} := by
      ext g
      exact or_comm
    obtain ⟨yx, hyx, hxy⟩ := N.exists_isLeaf_reach x
    have hrowx : ∀ s, N.site s ∈ {g | g ∈ p ∨ g ∈ q} → N.label yx s = N.label x s := fun s hs => label_of_reach hG hc hxy hs
    have hyxM : N.label yx ∈ M := Finset.mem_coe.1 (hD.mapsTo hyx)
    have hpq : ∀ {g}, g ∈ p → g ∉ q := fun hg => hc.notMem hg
    have hrows : ∀ {r₁₁ r₁₀ r₀₁ : ι → Bool}, r₁₁ ∈ M → r₁₀ ∈ M → r₀₁ ∈ M → r₁₁ i ≠ N.ancestral i → r₁₁ j ≠ N.ancestral j → r₁₀ i ≠ N.ancestral i → r₁₀ j = N.ancestral j → r₀₁ i = N.ancestral i → r₀₁ j ≠ N.ancestral j → Conflict N.ancestral M i j := by
      intro r₁₁ r₁₀ r₀₁ h₁ h₂ h₃ h₄ h₅ h₆ h₇ h₈ h₉ a₁ b₁ hab
      have hcases : ∀ {u v : Bool}, u ≠ v → u = !v := by decide
      by_cases ha₁ : a₁ = N.ancestral i <;> by_cases hb₁ : b₁ = N.ancestral j
      · exact absurd ha₁ (by rcases hab with h | h; exact h; exact absurd hb₁ h)
      · have hb₂ : b₁ = !N.ancestral j := hcases hb₁
        exact ⟨r₀₁, h₃, h₈.trans ha₁.symm, by rw [hb₂]; exact hcases h₉⟩
      · have ha₂ : a₁ = !N.ancestral i := hcases ha₁
        exact ⟨r₁₀, h₂, by rw [ha₂]; exact hcases h₆, h₇.trans hb₁.symm⟩
      · have ha₂ : a₁ = !N.ancestral i := hcases ha₁
        have hb₂ : b₁ = !N.ancestral j := hcases hb₁
        exact ⟨r₁₁, h₁, by rw [ha₂]; exact hcases h₄, by rw [hb₂]; exact hcases h₅⟩
    have hnot : ∀ {P : Prop} {u v : Bool}, (u ≠ v ↔ P) → ¬ P → u = v := fun h hn => by
      by_contra hne'
      exact hn (h.1 hne')
    have hprefix : ∀ {P c d c' d' : List E}, P = c ++ d → P = c' ++ d' → c <+: c' ∨ c' <+: c := fun h h' => List.prefix_or_prefix_of_prefix ⟨_, h.symm⟩ ⟨_, h'.symm⟩
    -- the states at the recombination node
    have hxi : ∀ (hs : N.site i ∈ {g | g ∈ p ∨ g ∈ q}), N.label x i ≠ N.ancestral i ↔ N.site i ∈ p := fun hs => by
      rw [hL₀ i, ite_eq_left hiL, hroot]
      exact parent_ne_iff hG hc ha hax hs
    have hxj : ∀ (hs : N.site j ∈ {g | g ∈ p ∨ g ∈ q}), N.label x j ≠ N.ancestral j ↔ N.site j ∈ q := fun hs => by
      rw [hL₀ j, ite_eq_right hjL, hroot]
      exact parent_ne_iff hG hc.symm hb hbx (Or.symm hs)
    rcases hW with ⟨hip, hjq, ⟨c₁, d₁, v₁, h₁, h₂, h₃, h₄, h₅⟩, ⟨c₂, d₂, v₂, h₁', h₂', h₃', h₄', h₅'⟩⟩ | ⟨hip, hjp, ⟨c₁, d₁, v₁, h₁, h₂, h₃, h₄, h₄n, h₅⟩, ⟨c₂, d₂, v₂, h₁', h₂', h₃', h₄', h₅'⟩⟩ |
      ⟨hiq, hjq, ⟨c₁, d₁, v₁, h₁, h₂, h₃, h₄, h₄n, h₅⟩, ⟨c₂, d₂, v₂, h₁', h₂', h₃', h₄', h₅'⟩⟩
    · -- W1
      have hsi : N.site i ∈ {g | g ∈ p ∨ g ∈ q} := Or.inl hip
      have hsj : N.site j ∈ {g | g ∈ p ∨ g ∈ q} := Or.inr hjq
      obtain ⟨r₁, hr₁, hr₁s⟩ := hrowAt hc rfl h₁ h₂ h₃ h₅
      obtain ⟨r₂, hr₂, hr₂s⟩ := hrowAt hc.symm hset' h₁' h₂' h₃' h₅'
      refine hrows hyxM hr₁ hr₂ (by rw [hrowx i hsi]; exact (hxi hsi).2 hip) (by rw [hrowx j hsj]; exact (hxj hsj).2 hjq) ((hr₁s i hsi).2 h₄) (hnot (hr₁s j hsj) fun h => hpq (h₁ ▸ List.mem_append_left _ h) hjq) (hnot (hr₂s i hsi) fun h => hpq hip (h₁' ▸ List.mem_append_left _ h)) ((hr₂s j hsj).2 h₄')
    · -- W2
      have hsi : N.site i ∈ {g | g ∈ p ∨ g ∈ q} := Or.inl hip
      have hsj : N.site j ∈ {g | g ∈ p ∨ g ∈ q} := Or.inl hjp
      obtain ⟨r₁, hr₁, hr₁s⟩ := hrowAt hc rfl h₁ h₂ h₃ h₅
      obtain ⟨r₂, hr₂, hr₂s⟩ := hrowAt hc rfl h₁' h₂' h₃' h₅'
      have hjc₂ : N.site j ∈ c₂ := by
        rcases hprefix h₁ h₁' with h | h
        · exact h.subset h₄
        · exact absurd (h.subset h₄') h₄n
      refine hrows hr₂ (by rw [← Finset.mem_coe]; exact Finset.mem_coe.2 hyxM) hr₁ ((hr₂s i hsi).2 h₄') ((hr₂s j hsj).2 hjc₂) (by rw [hrowx i hsi]; exact (hxi hsi).2 hip) (by rw [hrowx j hsj]; exact hnot (hxj hsj) (hpq hjp)) (hnot (hr₁s i hsi) h₄n) ((hr₁s j hsj).2 h₄)
    · -- W3
      have hsi : N.site i ∈ {g | g ∈ p ∨ g ∈ q} := Or.inr hiq
      have hsj : N.site j ∈ {g | g ∈ p ∨ g ∈ q} := Or.inr hjq
      obtain ⟨r₁, hr₁, hr₁s⟩ := hrowAt hc.symm hset' h₁ h₂ h₃ h₅
      obtain ⟨r₂, hr₂, hr₂s⟩ := hrowAt hc.symm hset' h₁' h₂' h₃' h₅'
      have hic₂ : N.site i ∈ c₂ := by
        rcases hprefix h₁ h₁' with h | h
        · exact h.subset h₄
        · exact absurd (h.subset h₄') h₄n
      refine hrows hr₂ hr₁ hyxM ((hr₂s i hsi).2 hic₂) ((hr₂s j hsj).2 h₄') ((hr₁s i hsi).2 h₄) (hnot (hr₁s j hsj) h₄n) (by rw [hrowx i hsi]; exact hnot (hxi hsi) fun h => hpq h hiq) (by rw [hrowx j hsj]; exact (hxj hsj).2 hjq)

end Point

end GusfieldEtAl2004
