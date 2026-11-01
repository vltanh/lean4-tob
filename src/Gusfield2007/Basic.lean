module

public import Gusfield2007.Defs
public import Mathlib.Data.Fintype.Card

/-!
# Gusfield et al. 2007: basic facts

The fact `G_S(M) = G(M + S)`, reachability from the root, and independence of the types of vertices and arcs.
-/

@[expose] public section

open scoped Classical

namespace Gusfield2007

universe u v w

section Graphs

variable {ι : Type*}

theorem mem_addRow {M : Finset (ι → Bool)} {S r : ι → Bool} : r ∈ addRow M S ↔ r = S ∨ r ∈ M :=
  Finset.mem_insert

theorem addRow_eq_of_mem {M : Finset (ι → Bool)} {S : ι → Bool} (h : S ∈ M) : addRow M S = M :=
  Finset.insert_eq_of_mem h

theorem mem_restrictRows {C : Set ι} {M : Finset (ι → Bool)} {S : C → Bool} :
    S ∈ restrictRows C M ↔ ∃ r ∈ M, C.domRestrict r = S :=
  Finset.mem_image

/-- Adding a row keeps the standing assumption. -/
theorem NoConstantColumn.addRow {M : Finset (ι → Bool)} (h : NoConstantColumn M) (S : ι → Bool) :
    NoConstantColumn (addRow M S) := fun i => by
  obtain ⟨r, hr, r', hr', hne⟩ := h i
  exact ⟨r, mem_addRow.2 (Or.inr hr), r', mem_addRow.2 (Or.inr hr'), hne⟩

/-- Restricting to a set of sites keeps the standing assumption: the columns of `M(C)` are columns of `M`. -/
theorem NoConstantColumn.restrictRows {M : Finset (ι → Bool)} (h : NoConstantColumn M) (C : Set ι) :
    NoConstantColumn (restrictRows C M) := fun i => by
  obtain ⟨r, hr, r', hr', hne⟩ := h i
  exact ⟨C.domRestrict r, mem_restrictRows.2 ⟨r, hr, rfl⟩, C.domRestrict r', mem_restrictRows.2 ⟨r', hr', rfl⟩, hne⟩

/-- "Two columns conflict relative to `S` if and only if they are incompatible in `M + S`" (line 152). -/
theorem conflict_iff_incompatible_addRow (S : ι → Bool) (M : Finset (ι → Bool)) (i j : ι) :
    Conflict S M i j ↔ Incompatible (addRow M S) i j := by
  constructor
  · intro h a b
    by_cases hab : a = S i ∧ b = S j
    · exact ⟨S, mem_addRow.2 (Or.inl rfl), hab.1.symm, hab.2.symm⟩
    · obtain ⟨r, hr, h₁, h₂⟩ := h a b (by tauto)
      exact ⟨r, mem_addRow.2 (Or.inr hr), h₁, h₂⟩
  · intro h a b hab
    obtain ⟨r, hr, h₁, h₂⟩ := h a b
    rcases mem_addRow.1 hr with rfl | hr
    · rcases hab with hab | hab
      · exact absurd h₁.symm hab
      · exact absurd h₂.symm hab
    · exact ⟨r, hr, h₁, h₂⟩

/-- **Lines 152, 160** (`g:gs_eq`). "`G_S(M) = G(M)` if `S ∈ M`, and so `G_S(M) = G(M + S)`". -/
theorem conflictGraph_eq_incompatGraph_addRow (S : ι → Bool) (M : Finset (ι → Bool)) :
    conflictGraph S M = incompatGraph (addRow M S) := by
  ext i j
  exact conflict_iff_incompatible_addRow S M i j

/-- The other half of `g:gs_eq`: `G_S(M) = G(M)` if `S ∈ M` (line 160). -/
theorem conflictGraph_eq_of_mem {S : ι → Bool} {M : Finset (ι → Bool)} (hS : S ∈ M) :
    conflictGraph S M = incompatGraph M := by
  rw [conflictGraph_eq_incompatGraph_addRow, addRow, Finset.insert_eq_of_mem hS]

end Graphs

namespace Network

variable {ι : Type u} {V : Type v} {E : Type w} (N : Network ι V E)

/-- Every node is reachable from the root: "exactly one node (the root) with no incoming edges" (line 94), and `N` is
finite and acyclic. -/
theorem reach_root [Finite V] (v : V) : N.Reach N.root v := by
  have : IsTrans V (Relation.TransGen N.Arc) := ⟨fun _ _ _ => Relation.TransGen.trans⟩
  have : Std.Irrefl (Relation.TransGen N.Arc) := ⟨N.acyclic⟩
  induction v using (Finite.wellFounded_of_trans_of_irrefl (Relation.TransGen N.Arc)).induction with
  | _ v ih =>
    by_cases hv : ∀ e, N.tgt e ≠ v
    · rw [(N.root_iff v).1 hv]
      exact Relation.ReflTransGen.refl
    · push Not at hv
      obtain ⟨e, he⟩ := hv
      have ha : N.Arc (N.src e) v := ⟨e, rfl, he⟩
      exact (ih _ (Relation.TransGen.single ha)).tail ha

/-- Transport a network along bijections of its vertices and arcs. -/
def map {V' : Type*} {E' : Type*} (eV : V ≃ V') (eE : E ≃ E') : Network ι V' E' where
  src e := eV (N.src (eE.symm e))
  tgt e := eV (N.tgt (eE.symm e))
  root := eV N.root
  site i := eE (N.site i)
  label v := N.label (eV.symm v)
  simple e f h₁ h₂ := eE.symm.injective (N.simple _ _ (eV.injective h₁) (eV.injective h₂))
  acyclic v h := by
    have key : ∀ {a b}, Relation.TransGen (fun a b => ∃ e, eV (N.src (eE.symm e)) = a ∧ eV (N.tgt (eE.symm e)) = b) a b →
        Relation.TransGen (fun a b => ∃ e, N.src e = a ∧ N.tgt e = b) (eV.symm a) (eV.symm b) := by
      intro a b h
      refine Relation.TransGen.lift eV.symm ?_ _ _ h
      rintro a b ⟨e, rfl, rfl⟩
      exact ⟨eE.symm e, by simp, by simp⟩
    exact N.acyclic _ (key h)
  root_iff v := by
    have := N.root_iff (eV.symm v)
    constructor
    · intro h
      have h' : ∀ e, N.tgt e ≠ eV.symm v := fun e he => h (eE e) (by simp [he])
      rw [← this.1 h']; simp
    · rintro rfl e he
      exact ((N.root_iff N.root).2 rfl) (eE.symm e) (eV.injective he)
  inDegree_le_two e f g h₁ h₂ := by
    rcases N.inDegree_le_two _ _ _ (eV.injective h₁) (eV.injective h₂) with h | h | h <;>
      simp [eE.symm.injective.eq_iff] at h <;> simp [h]
  site_not_recomb i f h := by
    have := N.site_not_recomb i (eE.symm f) (eV.injective (by simpa using h))
    simp [← this]
  label_tree e he i := by
    have h' : ∀ f, N.tgt f = N.tgt (eE.symm e) → f = eE.symm e := fun f hf => by
      have := he (eE f) (by simp [hf])
      simp [← this]
    simpa [Equiv.eq_symm_apply] using N.label_tree (eE.symm e) h' i
  label_recomb e f hef h i := by
    simpa using N.label_recomb (eE.symm e) (eE.symm f) (by simpa using hef) (eV.injective h) i

/-- `N` is isomorphic to its transport. -/
theorem isIso_map {V' : Type*} {E' : Type*} (eV : V ≃ V') (eE : E ≃ E') : N.IsIso (N.map eV eE) eV eE where
  src e := by simp [map]
  tgt e := by simp [map]
  root := rfl
  site _ := rfl
  label v := by simp [map]

/-- Vertices and arcs can be taken to be `Fin a` and `Fin b`: the bridge for the minima `R`, `RS`, `F`, `FS`. -/
theorem exists_fin_iso [Finite V] [Finite E] :
    ∃ (a b : ℕ) (N' : Network ι (Fin a) (Fin b)) (eV : V ≃ Fin a) (eE : E ≃ Fin b), N.IsIso N' eV eE := by
  obtain ⟨a, ⟨eV⟩⟩ := Finite.exists_equiv_fin V
  obtain ⟨b, ⟨eE⟩⟩ := Finite.exists_equiv_fin E
  exact ⟨a, b, N.map eV eE, eV, eE, N.isIso_map eV eE⟩

/-- Isomorphic networks have the same number of recombination nodes, and obey the same crossover models, and
derive the same rows, and have the same ancestral sequence, and are fully decomposed for the same graphs. -/
theorem IsIso.invariants {N : Network ι V E} {V' E' : Type*} {N' : Network ι V' E'} {eV : V ≃ V'} {eE : E ≃ E'} (h : N.IsIso N' eV eE)
    [LinearOrder ι] :
    N'.recombCount = N.recombCount ∧ (∀ c, N'.Obeys c ↔ N.Obeys c) ∧
      (∀ M, N'.Derives M ↔ N.Derives M) ∧ N'.ancestral = N.ancestral ∧
      (∀ G, N'.IsFullyDecomposedFor G ↔ N.IsFullyDecomposedFor G) := by
  sorry

/-- A rank function that increases along arcs shows a graph is acyclic. -/
theorem acyclic_of_rank {src tgt : E → V} (f : V → ℕ) (h : ∀ e, f (src e) < f (tgt e)) (v : V) :
    ¬ Relation.TransGen (fun a b => ∃ e, src e = a ∧ tgt e = b) v v := by
  have key : ∀ {a b}, Relation.TransGen (fun a b => ∃ e, src e = a ∧ tgt e = b) a b → f a < f b := by
    intro a b hab
    induction hab with
    | single hb =>
      obtain ⟨e, rfl, rfl⟩ := hb
      exact h e
    | tail _ hb ih =>
      obtain ⟨e, rfl, rfl⟩ := hb
      exact ih.trans (h e)
  exact fun hv => lt_irrefl _ (key hv)

section Tree

variable {N}

/-- With at most one arc into each node, there is no recombination node. -/
theorem not_isRecomb_of_tgt_injective (h : Function.Injective N.tgt) (x : V) : ¬ N.IsRecomb x := by
  rintro ⟨e, f, hef, rfl, hf⟩
  exact hef (h hf.symm)

/-- With at most one arc into each node, there is no recombination cycle. -/
theorem not_isCycle_of_tgt_injective (h : Function.Injective N.tgt) (Q : Set E) : ¬ N.IsCycle Q := by
  rintro ⟨w, x, p, q, hc, -⟩
  exact not_isRecomb_of_tgt_injective h x hc.1

/-- With at most one arc into each node, there is no blob. -/
theorem not_isBlob_of_tgt_injective (h : Function.Injective N.tgt) (B : Set E) : ¬ N.IsBlob B := by
  rintro ⟨Q, hQ, -⟩
  exact not_isCycle_of_tgt_injective h Q hQ

/-- With at most one arc into each node, every arc is a tree arc. -/
theorem isTreeArc_of_tgt_injective (h : Function.Injective N.tgt) (e : E) : N.IsTreeArc e := by
  rintro ⟨Q, hQ, -⟩
  exact not_isCycle_of_tgt_injective h Q hQ

/-- With at most one arc into each node, the blobbed tree has the nodes of `N`. -/
theorem toBlobNode_injective_of_tgt_injective (h : Function.Injective N.tgt) : Function.Injective N.toBlobNode := by
  intro u v huv
  have hr : Relation.EqvGen (fun u v => ∃ e, N.OnCycle e ∧ N.src e = u ∧ N.tgt e = v) u v := Quotient.exact huv
  clear huv
  induction hr with
  | rel _ _ hab =>
    obtain ⟨e, he, -, -⟩ := hab
    exact absurd he (isTreeArc_of_tgt_injective h e)
  | refl => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-- With at most one arc into each node, `N` is fully decomposed for any graph. -/
theorem isFullyDecomposedFor_of_tgt_injective (h : Function.Injective N.tgt) (G : SimpleGraph ι) :
    N.IsFullyDecomposedFor G where
  blob_component B hB := absurd hB (not_isBlob_of_tgt_injective h B)
  isolated_treeArc _ _ := isTreeArc_of_tgt_injective h _
  nodeDisjoint B _ hB := absurd hB (not_isBlob_of_tgt_injective h B)

/-- With at most one arc into each node, `N` is efficient. -/
theorem isEfficient_of_tgt_injective (h : Function.Injective N.tgt) : N.IsEfficient where
  label_inj B _ _ _ hB := absurd hB (not_isBlob_of_tgt_injective h B)
  exit_unique B _ _ hB := absurd hB (not_isBlob_of_tgt_injective h B)

/-- With at most one arc into each node, `N` obeys all crossover models. -/
theorem obeys_of_tgt_injective [LinearOrder ι] (h : Function.Injective N.tgt) (c : Crossover) : N.Obeys c := by
  cases c
  · exact fun x hx => absurd hx (not_isRecomb_of_tgt_injective h x)
  · exact trivial
  · exact fun x hx => absurd hx (not_isRecomb_of_tgt_injective h x)

/-- With at most one arc into each node, there are no recombination nodes to count. -/
theorem recombCount_eq_zero_of_tgt_injective (h : Function.Injective N.tgt) : N.recombCount = 0 := by
  have : IsEmpty {x // N.IsRecomb x} := ⟨fun x => not_isRecomb_of_tgt_injective h x.1 x.2⟩
  simp [recombCount]

end Tree

end Network

section Counts

variable {ι : Type u} [LinearOrder ι] {V : Type v} {E : Type w} [Finite V] [Finite E] (N : Network ι V E)

/-- A network deriving `M` bounds `R c M`, whatever its types of vertices and arcs. -/
theorem R_le_recombCount {c : Crossover} {M : Finset (ι → Bool)} (hc : N.Obeys c) (hM : N.Derives M) :
    R c M ≤ N.recombCount := by
  obtain ⟨a, b, N', eV, eE, h⟩ := N.exists_fin_iso
  obtain ⟨h₁, h₂, h₃, -, -⟩ := h.invariants
  exact Nat.sInf_le ⟨a, b, N', (h₂ c).2 hc, (h₃ M).2 hM, h₁⟩

/-- A network deriving `M` with ancestral sequence `S` bounds `RS c S M`. -/
theorem RS_le_recombCount {c : Crossover} {S : ι → Bool} {M : Finset (ι → Bool)} (hc : N.Obeys c)
    (hM : N.Derives M) (hS : N.ancestral = S) : RS c S M ≤ N.recombCount := by
  obtain ⟨a, b, N', eV, eE, h⟩ := N.exists_fin_iso
  obtain ⟨h₁, h₂, h₃, h₄, -⟩ := h.invariants
  exact Nat.sInf_le ⟨a, b, N', (h₂ c).2 hc, (h₃ M).2 hM, h₄.trans hS, h₁⟩

/-- Renaming the sites by an isomorphism of orders changes nothing, in particular from a component `↥C` to `Fin |C|`. -/
theorem R_map_orderIso {ι' : Type u} [LinearOrder ι'] (e : ι ≃o ι') (c : Crossover) (M : Finset (ι → Bool)) :
    R c (M.image fun r => r ∘ e.symm) = R c M := by
  sorry

/-- Renaming the sites by an isomorphism of orders changes nothing, with an ancestral sequence. -/
theorem RS_map_orderIso {ι' : Type u} [LinearOrder ι'] (e : ι ≃o ι') (c : Crossover) (S : ι → Bool)
    (M : Finset (ι → Bool)) : RS c (S ∘ e.symm) (M.image fun r => r ∘ e.symm) = RS c S M := by
  sorry

end Counts

end Gusfield2007
