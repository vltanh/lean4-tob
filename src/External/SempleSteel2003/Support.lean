module

public import Mathlib.Combinatorics.SimpleGraph.Acyclic
public import Mathlib.Combinatorics.SimpleGraph.DeleteEdges
public import Mathlib.Combinatorics.SimpleGraph.Maps
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Data.Set.Card
public import Mathlib.Order.Atoms

/-!
# Trees: the two sides of an edge, and the tree of a laminar family

Used by the Splits Equivalence Theorem (`SplitsEquivalence.lean`) and the Perfect Phylogeny Theorem
(`External/Gusfield1991/PerfectPhylogeny.lean`). Mathlib only.

* The two sides of an edge of a tree: `not_reachable_deleteEdges`, `reachable_deleteEdges_or`, `exists_far_sides`.
* The graph of a laminar family `𝓛` of nonempty subsets of `X`: its nodes are the members and `X`, its edges the covering pairs.
  It's a tree (`lamGraph_isTree`), whose edge below `a` has `a` on one side and the rest on the other (`lam_reachable_deleteEdges_iff`).
-/

@[expose] public section

open scoped Classical

namespace SempleSteel2003

section Tree

variable {W : Type*} {T : SimpleGraph W} {a b y z : W}

/-- An edge of an acyclic graph is a bridge. -/
theorem not_reachable_deleteEdges (hT : T.IsAcyclic) (h : T.Adj a b) : ¬ (T.deleteEdges {s(a, b)}).Reachable a b :=
  SimpleGraph.isBridge_iff.1 (SimpleGraph.isAcyclic_iff_forall_adj_isBridge.1 hT h)

theorem deleteEdges_adj_of_ne {e : Sym2 W} (h : T.Adj y z) (he : s(y, z) ≠ e) : (T.deleteEdges {e}).Adj y z := by
  rw [SimpleGraph.deleteEdges_adj]
  exact ⟨h, fun h' => he h'⟩

/-- Each node of a connected graph is reached from one end of an edge, without the edge. -/
theorem reachable_deleteEdges_or (hT : T.Connected) (a b w : W) :
    (T.deleteEdges {s(a, b)}).Reachable a w ∨ (T.deleteEdges {s(a, b)}).Reachable b w := by
  have hw := hT.preconnected a w
  rw [SimpleGraph.reachable_iff_reflTransGen] at hw
  induction hw with
  | refl => exact Or.inl (.refl _)
  | @tail y z _ hyz ih =>
    by_cases he : s(y, z) = s(a, b)
    · rcases Sym2.eq_iff.1 he with ⟨-, rfl⟩ | ⟨-, rfl⟩
      · exact Or.inr (.refl _)
      · exact Or.inl (.refl _)
    · have hadj := (deleteEdges_adj_of_ne hyz he).reachable
      exact ih.imp (fun h => h.trans hadj) (fun h => h.trans hadj)

/-- If `c` is an end of `e`, and isn't reached from `n` in `T - f`, then what is reached from `n` in `T - f` is reached in `T - e`:
the walks don't touch `c`. -/
theorem reachable_deleteEdges_of_not_reachable {e f : Sym2 W} {n c : W} (hc : c ∈ e)
    (hcn : ¬ (T.deleteEdges {f}).Reachable n c) (h : (T.deleteEdges {f}).Reachable n y) :
    (T.deleteEdges {e}).Reachable n y := by
  have hy := h
  rw [SimpleGraph.reachable_iff_reflTransGen] at hy
  induction hy with
  | refl => exact .refl _
  | @tail y z hr hyz ih =>
    have hry : (T.deleteEdges {f}).Reachable n y := (SimpleGraph.reachable_iff_reflTransGen _ _).2 hr
    have hrz : (T.deleteEdges {f}).Reachable n z := hry.trans hyz.reachable
    have hadj : T.Adj y z := (SimpleGraph.deleteEdges_adj.1 hyz).1
    refine (ih hry).trans (deleteEdges_adj_of_ne hadj fun he => ?_).reachable
    rw [← he, Sym2.mem_iff] at hc
    rcases hc with rfl | rfl
    · exact hcn hry
    · exact hcn hrz

/-- From a node, there is a neighbour towards any other node. -/
theorem exists_adj_reachable_deleteEdges (hT : T.Connected) {w a : W} (hne : w ≠ a) :
    ∃ n, T.Adj w n ∧ (T.deleteEdges {s(w, n)}).Reachable n a := by
  obtain ⟨p⟩ := hT.preconnected w a
  have hp := p.toPath.2
  generalize (p.toPath : T.Walk w a) = q at hp
  cases q with
  | nil => exact absurd rfl hne
  | @cons _ n _ h q =>
    refine ⟨n, h, SimpleGraph.reachable_deleteEdges_iff_exists_walk.2 ⟨q, fun he => ?_⟩⟩
    rw [SimpleGraph.Walk.cons_isPath_iff] at hp
    exact hp.2 (q.fst_mem_support_of_mem_edges he)

/-- Two edges of a tree have sides, one each, with no node in common: the sides pointing away from each other. For one edge,
these are its two sides. -/
theorem exists_far_sides (hT : T.IsTree) {a b c d : W} (hab : T.Adj a b) (hcd : T.Adj c d) :
    ∃ u v t t', s(a, b) = s(u, v) ∧ T.Adj u v ∧ s(c, d) = s(t, t') ∧ T.Adj t t' ∧
      ∀ y, ¬ ((T.deleteEdges {s(a, b)}).Reachable u y ∧ (T.deleteEdges {s(c, d)}).Reachable t y) := by
  -- the end of `ab` on the side away from `c`
  have h₁ : ∃ u v, s(a, b) = s(u, v) ∧ T.Adj u v ∧ (T.deleteEdges {s(a, b)}).Reachable v c := by
    rcases reachable_deleteEdges_or hT.1 a b c with h | h
    · exact ⟨b, a, Sym2.eq_swap, hab.symm, h⟩
    · exact ⟨a, b, rfl, hab, h⟩
  obtain ⟨u, v, hee, huv, hvc⟩ := h₁
  have huc : ¬ (T.deleteEdges {s(a, b)}).Reachable u c := fun h => by
    have := not_reachable_deleteEdges hT.2 huv
    rw [← hee] at this
    exact this (h.trans hvc.symm)
  -- the end of `cd` on the side away from `u`
  have h₂ : ∃ t t', s(c, d) = s(t, t') ∧ T.Adj t t' ∧ (T.deleteEdges {s(c, d)}).Reachable t' u := by
    rcases reachable_deleteEdges_or hT.1 c d u with h | h
    · exact ⟨d, c, Sym2.eq_swap, hcd.symm, h⟩
    · exact ⟨c, d, rfl, hcd, h⟩
  obtain ⟨t, t', hff, htt, htu⟩ := h₂
  have htu' : ¬ (T.deleteEdges {s(c, d)}).Reachable t u := fun h => by
    have := not_reachable_deleteEdges hT.2 htt
    rw [← hff] at this
    exact this (h.trans htu.symm)
  refine ⟨u, v, t, t', hee, huv, hff, htt, fun y ⟨h₃, h₄⟩ => ?_⟩
  have h₅ : (T.deleteEdges {s(c, d)}).Reachable u y :=
    reachable_deleteEdges_of_not_reachable (by simp) huc h₃
  exact htu' (h₄.trans h₅.symm)

/-- An isomorphism carries `T - e` to `T' - e'`. -/
theorem reachable_deleteEdges_iso {W' : Type*} {T' : SimpleGraph W'} (f : T ≃g T') (e : Sym2 W) (u v : W) :
    (T'.deleteEdges {e.map f}).Reachable (f u) (f v) ↔ (T.deleteEdges {e}).Reachable u v := by
  let g : T.deleteEdges {e} ≃g T'.deleteEdges {e.map f} :=
    { toEquiv := f.toEquiv
      map_rel_iff' := by
        intro x y
        have h₁ : T'.Adj (f.toEquiv x) (f.toEquiv y) ↔ T.Adj x y := f.map_rel_iff'
        have h₂ : s(f.toEquiv x, f.toEquiv y) = e.map f ↔ s(x, y) = e := by
          rw [← Sym2.map_mk]
          exact (Sym2.map.injective f.injective).eq_iff
        simp only [SimpleGraph.deleteEdges_adj, h₁, Set.mem_singleton_iff, h₂] }
  exact SimpleGraph.Iso.reachable_iff (φ := g)

/-- An isomorphism keeps the number of neighbours. -/
theorem ncard_neighborSet_iso {W' : Type*} {T' : SimpleGraph W'} (f : T ≃g T') (v : W) :
    (T'.neighborSet (f v)).ncard = (T.neighborSet v).ncard := by
  have himg : T'.neighborSet (f v) = f '' T.neighborSet v := by
    ext w
    simp only [SimpleGraph.mem_neighborSet, Set.mem_image]
    constructor
    · intro h
      refine ⟨f.symm w, ?_, by simp⟩
      rw [← f.map_adj_iff]
      simpa using h
    · rintro ⟨w', h, rfl⟩
      exact f.map_adj_iff.2 h
  rw [himg, Set.ncard_image_of_injective _ f.injective]

/-- A graph on a finite type is isomorphic to one on `Fin n`. -/
theorem exists_iso_fin [Finite W] (T : SimpleGraph W) : ∃ (n : ℕ) (T' : SimpleGraph (Fin n)), Nonempty (T ≃g T') := by
  obtain ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin W
  exact ⟨n, T.map e.toEmbedding, ⟨SimpleGraph.Iso.map e T⟩⟩

end Tree

section Laminar

variable {X : Type*}

/-- A laminar family of nonempty sets: two members are disjoint or nested. -/
structure IsLaminar (L : Set (Set X)) : Prop where
  nonempty : ∀ A ∈ L, A.Nonempty
  comparable : ∀ A ∈ L, ∀ B ∈ L, Disjoint A B ∨ A ⊆ B ∨ B ⊆ A

/-- The nodes of the graph of a laminar family: its members, and `X`. -/
abbrev LamNode (L : Set (Set X)) : Type _ := {A : Set X // A ∈ L ∨ A = Set.univ}

/-- The node `X`. -/
def lamRoot (L : Set (Set X)) : LamNode L := ⟨Set.univ, Or.inr rfl⟩

/-- The graph of a laminar family: the covering pairs of the order by inclusion. -/
def lamGraph (L : Set (Set X)) : SimpleGraph (LamNode L) := SimpleGraph.fromRel fun a b => a ⋖ b

variable {L : Set (Set X)}

theorem lamGraph_adj {a b : LamNode L} : (lamGraph L).Adj a b ↔ a ⋖ b ∨ b ⋖ a := by
  rw [lamGraph, SimpleGraph.fromRel_adj]
  constructor
  · exact fun h => h.2
  · rintro (h | h)
    · exact ⟨h.lt.ne, Or.inl h⟩
    · exact ⟨h.lt.ne', Or.inr h⟩

theorem le_lamRoot (v : LamNode L) : v ≤ lamRoot L := Subtype.coe_le_coe.1 (Set.subset_univ _)

theorem mem_of_le {a b : LamNode L} (h : a ≤ b) {x : X} (hx : x ∈ a.1) : x ∈ b.1 := Subtype.coe_le_coe.2 h hx

/-- Two nodes with a common element are nested. -/
theorem IsLaminar.le_or_le (hL : IsLaminar L) {a b : LamNode L} {x : X} (ha : x ∈ a.1) (hb : x ∈ b.1) : a ≤ b ∨ b ≤ a := by
  rcases a with ⟨a, ha' | rfl⟩ <;> rcases b with ⟨b, hb' | rfl⟩
  · rcases hL.comparable a ha' b hb' with h | h | h
    · exact absurd hb (Set.disjoint_left.1 h ha)
    · exact Or.inl h
    · exact Or.inr h
  · exact Or.inl (Set.subset_univ _)
  · exact Or.inr (Set.subset_univ _)
  · exact Or.inl le_rfl

variable [Nonempty X]

theorem IsLaminar.node_nonempty (hL : IsLaminar L) (v : LamNode L) : v.1.Nonempty := by
  rcases v with ⟨v, hv | rfl⟩
  · exact hL.nonempty v hv
  · exact Set.univ_nonempty

/-- Two nodes above a common node are nested. -/
theorem IsLaminar.le_or_le_of_le (hL : IsLaminar L) {v a b : LamNode L} (ha : v ≤ a) (hb : v ≤ b) : a ≤ b ∨ b ≤ a := by
  obtain ⟨x, hx⟩ := hL.node_nonempty v
  exact hL.le_or_le (ha hx) (hb hx)

/-- A node has at most one node covering it. -/
theorem IsLaminar.covBy_unique (hL : IsLaminar L) {a b c : LamNode L} (hb : a ⋖ b) (hc : a ⋖ c) : b = c := by
  rcases hL.le_or_le_of_le hb.le hc.le with h | h
  · rcases h.eq_or_lt with h | h
    · exact h
    · exact absurd h (hc.2 hb.lt)
  · rcases h.eq_or_lt with h | h
    · exact h.symm
    · exact absurd h (hb.2 hc.lt)

/-- The only edge from below `a` to outside is the edge above `a`. -/
theorem IsLaminar.eq_of_covBy_of_le (hL : IsLaminar L) {a v w : LamNode L} (hv : v ≤ a) (hw : v ⋖ w) (hn : ¬ w ≤ a) : v = a := by
  rcases hL.le_or_le_of_le hv hw.le with h | h
  · rcases hv.eq_or_lt with h' | h'
    · exact h'
    · have h₂ : a < w := lt_of_le_of_ne h fun h₃ => hn (h₃ ▸ le_rfl)
      exact absurd h₂ (hw.2 h')
  · exact absurd h hn

variable [Finite X]

omit [Nonempty X] in
/-- A node other than `X` has a node covering it. -/
theorem exists_covBy_of_ne_root {a : LamNode L} (ha : a ≠ lamRoot L) : ∃ b, a ⋖ b := by
  obtain ⟨b, hb, -⟩ := exists_covBy_le_of_lt (lt_of_le_of_ne (le_lamRoot a) ha)
  exact ⟨b, hb⟩

omit [Nonempty X] in
theorem lam_reachable_deleteEdges_of_le {a b u : LamNode L} (hab : a ⋖ b) (hu : u ≤ a) :
    ((lamGraph L).deleteEdges {s(a, b)}).Reachable u a := by
  induction u using WellFoundedGT.induction with
  | _ u ih =>
    rcases hu.eq_or_lt with rfl | hlt
    · exact .refl _
    · obtain ⟨c, huc, hca⟩ := exists_covBy_le_of_lt hlt
      have hadj : ((lamGraph L).deleteEdges {s(a, b)}).Adj u c := by
        refine deleteEdges_adj_of_ne (lamGraph_adj.2 (Or.inl huc)) fun he => ?_
        rcases Sym2.eq_iff.1 he with ⟨h₁, -⟩ | ⟨h₁, -⟩
        · exact hlt.ne h₁
        · exact absurd (h₁ ▸ hlt) hab.lt.not_gt
      exact hadj.reachable.trans (ih c huc.lt hca)

omit [Nonempty X] in
theorem lam_reachable_deleteEdges_of_not_le {a b u : LamNode L} (hu : ¬ u ≤ a) :
    ((lamGraph L).deleteEdges {s(a, b)}).Reachable u (lamRoot L) := by
  induction u using WellFoundedGT.induction with
  | _ u ih =>
    rcases (le_lamRoot u).eq_or_lt with rfl | hlt
    · exact .refl _
    · obtain ⟨c, huc, -⟩ := exists_covBy_le_of_lt hlt
      have hc : ¬ c ≤ a := fun h => hu (huc.le.trans h)
      have hadj : ((lamGraph L).deleteEdges {s(a, b)}).Adj u c := by
        refine deleteEdges_adj_of_ne (lamGraph_adj.2 (Or.inl huc)) fun he => ?_
        rcases Sym2.eq_iff.1 he with ⟨h₁, -⟩ | ⟨-, h₂⟩
        · exact hu (h₁ ▸ le_rfl)
        · exact hc (h₂ ▸ le_rfl)
      exact hadj.reachable.trans (ih c huc.lt hc)

/-- **The split of an edge** of the graph of a laminar family: the edge above `a` has below it exactly what is below `a`. -/
theorem lam_reachable_deleteEdges_iff (hL : IsLaminar L) {a b u v : LamNode L} (hab : a ⋖ b) :
    ((lamGraph L).deleteEdges {s(a, b)}).Reachable u v ↔ (u ≤ a ↔ v ≤ a) := by
  constructor
  · intro h
    rw [SimpleGraph.reachable_iff_reflTransGen] at h
    induction h with
    | refl => exact Iff.rfl
    | @tail y z _ hyz ih =>
      refine ih.trans ?_
      obtain ⟨hadj, hne⟩ := SimpleGraph.deleteEdges_adj.1 hyz
      have key : ∀ {p q : LamNode L}, p ⋖ q → s(p, q) ≠ s(a, b) → p ≤ a → q ≤ a := by
        intro p q hpq hs hp
        by_contra hq
        obtain rfl := hL.eq_of_covBy_of_le hp hpq hq
        obtain rfl := hL.covBy_unique hpq hab
        exact hs rfl
      rcases lamGraph_adj.1 hadj with h | h
      · exact ⟨key h hne, fun hz => h.le.trans hz⟩
      · exact ⟨fun hy => h.le.trans hy, key h (by rwa [Sym2.eq_swap])⟩
  · intro h
    by_cases hu : u ≤ a
    · exact (lam_reachable_deleteEdges_of_le hab hu).trans (lam_reachable_deleteEdges_of_le hab (h.1 hu)).symm
    · have hv : ¬ v ≤ a := fun hv => hu (h.2 hv)
      exact (lam_reachable_deleteEdges_of_not_le hu).trans (lam_reachable_deleteEdges_of_not_le hv).symm

/-- **The graph of a laminar family is a tree.** -/
theorem lamGraph_isTree (hL : IsLaminar L) : (lamGraph L).IsTree := by
  have hroot : ∀ u : LamNode L, (lamGraph L).Reachable u (lamRoot L) := by
    intro u
    induction u using WellFoundedGT.induction with
    | _ u ih =>
      rcases (le_lamRoot u).eq_or_lt with rfl | hlt
      · exact .refl _
      · obtain ⟨c, huc, -⟩ := exists_covBy_le_of_lt hlt
        exact (lamGraph_adj.2 (Or.inl huc)).reachable.trans (ih c huc.lt)
  have : Nonempty (LamNode L) := ⟨lamRoot L⟩
  refine ⟨SimpleGraph.Connected.mk fun u v => (hroot u).trans (hroot v).symm, ?_⟩
  rw [SimpleGraph.isAcyclic_iff_forall_adj_isBridge]
  intro a b h
  rw [SimpleGraph.isBridge_iff]
  rcases lamGraph_adj.1 h with h | h
  · intro hr
    exact h.lt.not_ge ((lam_reachable_deleteEdges_iff hL h).1 hr |>.1 le_rfl)
  · rw [Sym2.eq_swap]
    intro hr
    exact h.lt.not_ge ((lam_reachable_deleteEdges_iff hL h).1 hr |>.2 le_rfl)

omit [Nonempty X] in
/-- The least node containing `x`. -/
theorem IsLaminar.exists_least (hL : IsLaminar L) (x : X) : ∃ v : LamNode L, x ∈ v.1 ∧ ∀ w : LamNode L, x ∈ w.1 → v ≤ w := by
  obtain ⟨v, hv⟩ := Set.Finite.exists_minimal (Set.toFinite {v : LamNode L | x ∈ v.1}) ⟨lamRoot L, Set.mem_univ x⟩
  refine ⟨v, hv.1, fun w hw => ?_⟩
  rcases hL.le_or_le hv.1 hw with h | h
  · exact h
  · exact hv.2 hw h

/-- The label of `x`: the least node containing it. -/
noncomputable def IsLaminar.label (hL : IsLaminar L) (x : X) : LamNode L := (hL.exists_least x).choose

omit [Nonempty X] in
theorem IsLaminar.mem_label (hL : IsLaminar L) (x : X) : x ∈ (hL.label x).1 := (hL.exists_least x).choose_spec.1

omit [Nonempty X] in
theorem IsLaminar.label_le_iff (hL : IsLaminar L) {x : X} {v : LamNode L} : hL.label x ≤ v ↔ x ∈ v.1 :=
  ⟨fun h => mem_of_le h (hL.mem_label x), (hL.exists_least x).choose_spec.2 v⟩

end Laminar

end SempleSteel2003
