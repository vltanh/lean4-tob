module

public import Gusfield2007.Defs
public import Mathlib.Data.Fintype.Card

/-!
# Gusfield et al. 2007: basic facts

The fact `G_S(M) = G(M + S)`; arcs, directed paths, reachability, and induction along the arcs; embeddings of one network in another (`Network.Emb`), and isomorphisms, with the independence of the types of vertices and arcs that they give; recombinants (`Recombinant`).
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

/-- No constant column: each column has a row off any given state. -/
theorem NoConstantColumn.exists_ne {M : Finset (ι → Bool)} (h : NoConstantColumn M) (S : ι → Bool) (i : ι) : ∃ r ∈ M, r i ≠ S i := by
  obtain ⟨r, hr, r', hr', hne⟩ := h i
  by_cases h₁ : r i = S i
  · exact ⟨r', hr', fun h₂ => hne (h₁.trans h₂.symm)⟩
  · exact ⟨r, hr, h₁⟩

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

/-- A function that increases along a relation increases along its paths. -/
theorem lt_of_transGen {α β : Type*} [Preorder β] {r : α → α → Prop} (f : α → β) (h : ∀ a b, r a b → f a < f b) {a b : α} (hab : Relation.TransGen r a b) : f a < f b := by
  induction hab with
  | single hb => exact h _ _ hb
  | tail _ hb ih => exact ih.trans (h _ _ hb)

/-- A relation along which a function increases is acyclic. -/
theorem acyclic_of_strict {α β : Type*} [Preorder β] {r : α → α → Prop} (f : α → β) (h : ∀ a b, r a b → f a < f b) (x : α) : ¬ Relation.TransGen r x x :=
  fun hx => lt_irrefl _ (lt_of_transGen f h hx)

/-- A node reached from another, other than it, has a neighbour. -/
theorem exists_adj_of_reachable {G : SimpleGraph ι} {i j : ι} (h : G.Reachable i j) (hij : i ≠ j) : ∃ k, G.Adj i k := by
  obtain ⟨p⟩ := h
  cases p with
  | nil => exact absurd rfl hij
  | @cons _ k _ hk _ => exact ⟨k, hk⟩

/-- A strictly increasing rank exists on a finite acyclic relation. -/
theorem exists_rank {α : Type*} [Finite α] (r : α → α → Prop) (hr : ∀ a, ¬ Relation.TransGen r a a) :
    ∃ f : α → ℕ, ∀ a b, r a b → f a < f b := by
  refine ⟨fun b => {u | Relation.TransGen r u b}.ncard, fun a b hab => Set.ncard_lt_ncard ?_ (Set.toFinite _)⟩
  refine ⟨fun u hu => Relation.TransGen.tail hu hab, fun h => ?_⟩
  exact hr a (h (Relation.TransGen.single hab))

end Graphs

namespace Network

variable {ι : Type u} {V : Type v} {E : Type w} (N : Network ι V E)

/-- The labels of the nodes are in `labelSet`. -/
theorem label_mem_labelSet [Fintype V] (v : V) : N.label v ∈ N.labelSet :=
  Finset.mem_image_of_mem _ (Finset.mem_univ _)

/-! ### Arcs, directed paths, and what's above and below a node -/

section Reach

variable {N}

theorem arc_src_tgt (e : E) : N.Arc (N.src e) (N.tgt e) := ⟨e, rfl, rfl⟩

/-- An arc lengthens a path. -/
theorem reach_src_tgt (e : E) : N.Reach (N.src e) (N.tgt e) := Relation.ReflTransGen.single (arc_src_tgt e)

/-- There's no directed path from the target of an arc back to its source. -/
theorem not_reach_tgt_src (e : E) : ¬ N.Reach (N.tgt e) (N.src e) := fun h =>
  N.acyclic _ (Relation.TransGen.head' (arc_src_tgt e) h)

theorem src_ne_tgt (e : E) : N.src e ≠ N.tgt e := fun h =>
  not_reach_tgt_src (N := N) e (h ▸ .refl)

/-- Two nodes that reach each other are equal. -/
theorem Reach.antisymm {u v : V} (h₁ : N.Reach u v) (h₂ : N.Reach v u) : u = v := by
  rcases Relation.ReflTransGen.cases_tail h₁ with h | ⟨y, hy, e, rfl, rfl⟩
  · exact h.symm
  · exact absurd (h₂.trans hy) (not_reach_tgt_src e)

/-- The root isn't a recombination node. -/
theorem not_isRecomb_root : ¬ N.IsRecomb N.root := by
  rintro ⟨e, -, -, he, -⟩
  exact (N.root_iff N.root).2 rfl e he

/-- Nothing but the root reaches the root. -/
theorem eq_root_of_reach {a : V} (h : N.Reach a N.root) : a = N.root := by
  rcases Relation.ReflTransGen.cases_tail h with h | ⟨y, -, e, -, he⟩
  · exact h.symm
  · exact absurd he ((N.root_iff N.root).2 rfl e)

theorem IsPath.reach {u v : V} {p : List E} (h : N.IsPath u v p) : N.Reach u v := by
  induction p generalizing u with
  | nil => cases h; exact .refl
  | cons e p ih => exact Relation.ReflTransGen.head ⟨e, h.1, rfl⟩ (ih h.2)

theorem Reach.exists_isPath {u v : V} (h : N.Reach u v) : ∃ p, N.IsPath u v p := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact ⟨[], rfl⟩
  | head ha _ ih =>
    obtain ⟨e, rfl, rfl⟩ := ha
    obtain ⟨p, hp⟩ := ih
    exact ⟨e :: p, rfl, hp⟩

theorem IsPath.append {u v w : V} {p q : List E} (hp : N.IsPath u v p) (hq : N.IsPath v w q) : N.IsPath u w (p ++ q) := by
  induction p generalizing u with
  | nil => cases hp; exact hq
  | cons e p ih => exact ⟨hp.1, ih hp.2⟩

theorem IsPath.reach_src_of_mem {u v : V} {p : List E} {e : E} (h : N.IsPath u v p) (he : e ∈ p) : N.Reach u (N.src e) := by
  induction p generalizing u with
  | nil => exact absurd he (by simp)
  | cons f p ih =>
    obtain ⟨rfl, h₂⟩ := h
    rcases List.mem_cons.1 he with rfl | he
    · exact Relation.ReflTransGen.refl
    · exact Relation.ReflTransGen.head (arc_src_tgt f) (ih h₂ he)

theorem IsPath.reach_tgt_of_mem {u v : V} {p : List E} {e : E} (h : N.IsPath u v p) (he : e ∈ p) : N.Reach (N.tgt e) v := by
  induction p generalizing u with
  | nil => exact absurd he (by simp)
  | cons f p ih =>
    obtain ⟨-, h₂⟩ := h
    rcases List.mem_cons.1 he with rfl | he
    · exact h₂.reach
    · exact ih h₂ he

/-- Along a path, a property preserved by each arc passes from the start to the end. -/
theorem IsPath.rec_of_forall {P : V → Prop} : ∀ {p : List E} {u v : V}, N.IsPath u v p →
    (∀ e ∈ p, P (N.src e) → P (N.tgt e)) → P u → P v
  | [], _, _, h, _, hu => h ▸ hu
  | _ :: _, _, _, h, ha, hu => by
    obtain ⟨rfl, h₂⟩ := h
    exact IsPath.rec_of_forall h₂ (fun e he => ha e (List.mem_cons_of_mem _ he)) (ha _ List.mem_cons_self hu)

variable (N) [Finite V]

/-- The relation "strictly above" on the nodes is well founded. -/
theorem wellFounded_transGen : WellFounded (Relation.TransGen N.Arc) := by
  have : IsTrans V (Relation.TransGen N.Arc) := ⟨fun _ _ _ => Relation.TransGen.trans⟩
  have : Std.Irrefl (Relation.TransGen N.Arc) := ⟨N.acyclic⟩
  exact Finite.wellFounded_of_trans_of_irrefl _

/-- The relation "strictly below" on the nodes is well founded. -/
theorem wellFounded_transGen_swap : WellFounded (fun a b => Relation.TransGen N.Arc b a) := by
  have : IsTrans V (fun a b => Relation.TransGen N.Arc b a) := ⟨fun _ _ _ h h' => Relation.TransGen.trans h' h⟩
  have : Std.Irrefl (fun a b => Relation.TransGen N.Arc b a) := ⟨N.acyclic⟩
  exact Finite.wellFounded_of_trans_of_irrefl _

/-- Induction along the arcs: a finite network is acyclic. -/
theorem arc_induction {P : V → Prop} (h : ∀ v, (∀ e, N.tgt e = v → P (N.src e)) → P v) (v : V) : P v := by
  induction v using N.wellFounded_transGen.induction with
  | _ v ih => exact h v fun e he => ih _ (Relation.TransGen.single ⟨e, rfl, he⟩)

/-- A rank that increases along the arcs. -/
theorem exists_rank : ∃ ρ : V → ℕ, ∀ e, ρ (N.src e) < ρ (N.tgt e) := by
  obtain ⟨f, hf⟩ := _root_.Gusfield2007.exists_rank N.Arc N.acyclic
  exact ⟨f, fun e => hf _ _ (arc_src_tgt e)⟩

/-- Every node is reachable from the root: "exactly one node (the root) with no incoming edges" (line 94), and `N` is
finite and acyclic. -/
theorem reach_root (v : V) : N.Reach N.root v := by
  induction v using N.arc_induction with
  | _ v ih =>
    by_cases hv : ∀ e, N.tgt e ≠ v
    · rw [(N.root_iff v).1 hv]
      exact Relation.ReflTransGen.refl
    · push Not at hv
      obtain ⟨e, he⟩ := hv
      exact (ih e he).tail ⟨e, rfl, he⟩

/-- Every node has a leaf below it. -/
theorem exists_isLeaf_reach (v : V) : ∃ l, N.IsLeaf l ∧ N.Reach v l := by
  induction v using N.wellFounded_transGen_swap.induction with
  | _ v ih =>
    by_cases hv : N.IsLeaf v
    · exact ⟨v, hv, Relation.ReflTransGen.refl⟩
    · unfold IsLeaf at hv
      push Not at hv
      obtain ⟨e, rfl⟩ := hv
      obtain ⟨l, hl, hr⟩ := ih (N.tgt e) (Relation.TransGen.single (arc_src_tgt e))
      exact ⟨l, hl, Relation.ReflTransGen.head (arc_src_tgt e) hr⟩

end Reach

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

/-- The arcs of a recombination cycle under a map of arcs. -/
theorem image_setOf_mem_or_mem {α β : Type*} (g : α → β) (p q : List α) :
    g '' {e | e ∈ p ∨ e ∈ q} = {a | a ∈ p.map g ∨ a ∈ q.map g} := by
  ext a
  simp only [Set.mem_image, Set.mem_ofPred_eq, List.mem_map]
  constructor
  · rintro ⟨e, he | he, rfl⟩
    · exact Or.inl ⟨e, he, rfl⟩
    · exact Or.inr ⟨e, he, rfl⟩
  · rintro (⟨e, he, rfl⟩ | ⟨e, he, rfl⟩)
    · exact ⟨e, Or.inl he, rfl⟩
    · exact ⟨e, Or.inr he, rfl⟩

/-! ### Embeddings -/

section Emb

variable {κ : Type*} {V' : Type*} {E' : Type*}

/-- `N` sits in `N'` through the injections `f` on nodes and `g` on arcs. The sites play no role. -/
structure Emb (N : Network κ V E) (N' : Network ι V' E') (f : V → V') (g : E → E') : Prop where
  f_inj : Function.Injective f
  g_inj : Function.Injective g
  src : ∀ e, N'.src (g e) = f (N.src e)
  tgt : ∀ e, N'.tgt (g e) = f (N.tgt e)

variable {N : Network κ V E} {N' : Network ι V' E'} {f : V → V'} {g : E → E'}

theorem Emb.isPath (h : Emb N N' f g) : ∀ {p : List E} {u v : V}, N.IsPath u v p → N'.IsPath (f u) (f v) (p.map g)
  | [], _, _, hp => congrArg f hp
  | _ :: _, _, _, ⟨h₁, h₂⟩ => ⟨(h.src _).trans (congrArg f h₁), (h.tgt _) ▸ h.isPath h₂⟩

theorem Emb.isPath_back (h : Emb N N' f g) : ∀ {p' : List E'} {u : V} {v' : V'}, N'.IsPath (f u) v' p' →
    (∀ a ∈ p', a ∈ Set.range g) → ∃ v p, v' = f v ∧ p' = p.map g ∧ N.IsPath u v p
  | [], u, _, hp, _ => ⟨u, [], Eq.symm hp, rfl, rfl⟩
  | a :: p', u, v', ⟨h₁, h₂⟩, hall => by
    obtain ⟨e, rfl⟩ := hall a (by simp)
    have hsrc : N.src e = u := h.f_inj ((h.src e).symm.trans h₁)
    rw [h.tgt] at h₂
    obtain ⟨v, p, hv, hp, hpath⟩ := h.isPath_back h₂ fun b hb => hall b (by simp [hb])
    exact ⟨v, e :: p, hv, by simp [hp], hsrc, hpath⟩

theorem Emb.isCycleOn (h : Emb N N' f g) {w x : V} {p q : List E} (hc : N.IsCycleOn w x p q) :
    N'.IsCycleOn (f w) (f x) (p.map g) (q.map g) := by
  obtain ⟨⟨e₁, e₂, hne, h₁, h₂⟩, hp, hq, hpq, hd⟩ := hc
  refine ⟨⟨g e₁, g e₂, h.g_inj.ne hne, by rw [h.tgt, h₁], by rw [h.tgt, h₂]⟩, h.isPath hp, h.isPath hq,
    fun heq => hpq (List.map_injective_iff.2 h.g_inj heq), ?_⟩
  intro a ha b hb hab
  obtain ⟨a', ha', rfl⟩ := List.mem_map.1 ha
  obtain ⟨b', hb', rfl⟩ := List.mem_map.1 hb
  rw [h.tgt, h.tgt] at hab
  rw [h.tgt, hd a' ha' b' hb' (h.f_inj hab)]

theorem Emb.isCycle_image (h : Emb N N' f g) {Q : Set E} (hQ : N.IsCycle Q) : N'.IsCycle (g '' Q) := by
  obtain ⟨w, x, p, q, hc, rfl⟩ := hQ
  exact ⟨f w, f x, p.map g, q.map g, h.isCycleOn hc, image_setOf_mem_or_mem g p q⟩

/-- A cycle of `N'` with all its arcs in `N` is a cycle of `N`. -/
theorem Emb.cycle_back (h : Emb N N' f g) (hrec : ∀ x, N'.IsRecomb (f x) → N.IsRecomb x) {Q' : Set E'} (hQ' : N'.IsCycle Q')
    (hall : Q' ⊆ Set.range g) : ∃ Q, N.IsCycle Q ∧ Q' = g '' Q := by
  obtain ⟨w', x', p', q', ⟨hrecx, hp', hq', hpq, hd⟩, rfl⟩ := hQ'
  have hp₁ : ∀ a ∈ p', a ∈ Set.range g := fun a ha => hall (Or.inl ha)
  have hq₁ : ∀ a ∈ q', a ∈ Set.range g := fun a ha => hall (Or.inr ha)
  -- The start of the cycle is in `N`.
  obtain ⟨w, rfl⟩ : w' ∈ Set.range f := by
    cases p' with
    | cons a t =>
      obtain ⟨e, rfl⟩ := hp₁ a (by simp)
      exact ⟨N.src e, by rw [← hp'.1, h.src]⟩
    | nil =>
      cases q' with
      | cons a t =>
        obtain ⟨e, rfl⟩ := hq₁ a (by simp)
        exact ⟨N.src e, by rw [← hq'.1, h.src]⟩
      | nil => exact absurd rfl hpq
  obtain ⟨x, p, rfl, rfl, hp⟩ := h.isPath_back hp' hp₁
  obtain ⟨x₂, q, hx₂, rfl, hq⟩ := h.isPath_back hq' hq₁
  obtain rfl : x = x₂ := h.f_inj hx₂
  refine ⟨_, ⟨w, x, p, q, ⟨hrec x hrecx, hp, hq, fun heq => hpq (by rw [heq]), ?_⟩, rfl⟩, ?_⟩
  · intro a ha b hb hab
    apply h.f_inj
    rw [← h.tgt]
    refine hd (g a) (List.mem_map_of_mem ha) (g b) (List.mem_map_of_mem hb) ?_
    rw [h.tgt, h.tgt, hab]
  · exact (image_setOf_mem_or_mem g p q).symm

/-- The blob of a cycle of `N`, in `N'`, when each cycle of `N'` with an arc in `N` is a cycle of `N`. -/
theorem Emb.class_image (h : Emb N N' f g)
    (hback : ∀ Q', N'.IsCycle Q' → (∃ e ∈ Q', e ∈ Set.range g) → ∃ Q, N.IsCycle Q ∧ Q' = g '' Q) {Q₀ : Set E}
    (hQ₀ : N.IsCycle Q₀) (Q' : Set E') :
    Relation.ReflTransGen N'.ShareArc (g '' Q₀) Q' ↔ ∃ Q, Relation.ReflTransGen N.ShareArc Q₀ Q ∧ Q' = g '' Q := by
  constructor
  · intro hr
    induction hr with
    | refl => exact ⟨Q₀, Relation.ReflTransGen.refl, rfl⟩
    | @tail b c _ hbc ih =>
      obtain ⟨Q, hQ, rfl⟩ := ih
      obtain ⟨-, hc, a, ⟨e, he, rfl⟩, hac⟩ := hbc
      obtain ⟨Q₂, hQ₂, rfl⟩ := hback c hc ⟨g e, hac, e, rfl⟩
      refine ⟨Q₂, hQ.tail ⟨?_, hQ₂, ?_⟩, rfl⟩
      · cases hQ with
        | refl => exact hQ₀
        | tail _ h' => exact h'.2.1
      · obtain ⟨e', he', heq⟩ := hac
        exact ⟨e, he, h.g_inj heq ▸ he'⟩
  · rintro ⟨Q, hQ, rfl⟩
    induction hQ with
    | refl => exact Relation.ReflTransGen.refl
    | @tail b c _ hbc ih =>
      refine ih.tail ⟨h.isCycle_image hbc.1, h.isCycle_image hbc.2.1, ?_⟩
      obtain ⟨e, he₁, he₂⟩ := hbc.2.2
      exact ⟨g e, ⟨e, he₁, rfl⟩, ⟨e, he₂, rfl⟩⟩

theorem Emb.blob_image (h : Emb N N' f g)
    (hback : ∀ Q', N'.IsCycle Q' → (∃ e ∈ Q', e ∈ Set.range g) → ∃ Q, N.IsCycle Q ∧ Q' = g '' Q) {Q₀ : Set E}
    (hQ₀ : N.IsCycle Q₀) :
    ⋃₀ {Q' | Relation.ReflTransGen N'.ShareArc (g '' Q₀) Q'} = g '' ⋃₀ {Q | Relation.ReflTransGen N.ShareArc Q₀ Q} := by
  ext a
  constructor
  · rintro ⟨Q', hQ', ha⟩
    obtain ⟨Q, hQ, rfl⟩ := (h.class_image hback hQ₀ Q').1 hQ'
    obtain ⟨e, he, rfl⟩ := ha
    exact ⟨e, ⟨Q, hQ, he⟩, rfl⟩
  · rintro ⟨e, ⟨Q, hQ, he⟩, rfl⟩
    exact ⟨g '' Q, (h.class_image hback hQ₀ _).2 ⟨Q, hQ, rfl⟩, ⟨e, he, rfl⟩⟩

end Emb

namespace IsIso

variable {N} {V' : Type*} {E' : Type*} {N' : Network ι V' E'} {eV : V ≃ V'} {eE : E ≃ E'}

/-- The inverse of an isomorphism. -/
theorem symm (h : N.IsIso N' eV eE) : N'.IsIso N eV.symm eE.symm where
  src e := by rw [Equiv.eq_symm_apply, ← h.src]; simp
  tgt e := by rw [Equiv.eq_symm_apply, ← h.tgt]; simp
  root := by rw [Equiv.eq_symm_apply, h.root]
  site i := by rw [Equiv.eq_symm_apply, h.site]
  label v := by rw [← h.label]; simp

theorem isRecomb_of (h : N.IsIso N' eV eE) {x : V} (hx : N.IsRecomb x) : N'.IsRecomb (eV x) := by
  obtain ⟨e, e', hne, rfl, he'⟩ := hx
  exact ⟨eE e, eE e', eE.injective.ne hne, h.tgt e, by rw [h.tgt, he']⟩

theorem isRecomb (h : N.IsIso N' eV eE) (x : V) : N'.IsRecomb (eV x) ↔ N.IsRecomb x := by
  refine ⟨fun hx => ?_, h.isRecomb_of⟩
  simpa using h.symm.isRecomb_of hx

theorem isLeaf (h : N.IsIso N' eV eE) (v : V) : N'.IsLeaf (eV v) ↔ N.IsLeaf v := by
  constructor
  · intro hv e he
    exact hv (eE e) (by rw [h.src, he])
  · intro hv e he
    have := h.symm.src e
    rw [he] at this
    exact hv _ (by simpa using this)

theorem toEmb (h : N.IsIso N' eV eE) : Emb N N' eV eE := ⟨eV.injective, eE.injective, h.src, h.tgt⟩

theorem isCycle_image (h : N.IsIso N' eV eE) {Q : Set E} (hQ : N.IsCycle Q) : N'.IsCycle (eE '' Q) :=
  h.toEmb.isCycle_image hQ

theorem onCycle (h : N.IsIso N' eV eE) (e : E) : N'.OnCycle (eE e) ↔ N.OnCycle e := by
  constructor
  · rintro ⟨Q, hQ, heQ⟩
    refine ⟨eE.symm '' Q, h.symm.isCycle_image hQ, ⟨eE e, heQ, by simp⟩⟩
  · rintro ⟨Q, hQ, heQ⟩
    exact ⟨eE '' Q, h.isCycle_image hQ, e, heQ, rfl⟩

theorem isTreeArc (h : N.IsIso N' eV eE) (e : E) : N'.IsTreeArc (eE e) ↔ N.IsTreeArc e :=
  not_congr (h.onCycle e)

theorem shareArc_image (h : N.IsIso N' eV eE) {Q Q' : Set E} (hs : N.ShareArc Q Q') :
    N'.ShareArc (eE '' Q) (eE '' Q') := by
  obtain ⟨h₁, h₂, e, he, he'⟩ := hs
  exact ⟨h.isCycle_image h₁, h.isCycle_image h₂, eE e, ⟨e, he, rfl⟩, ⟨e, he', rfl⟩⟩

theorem reflTransGen_shareArc_image (h : N.IsIso N' eV eE) {Q Q' : Set E}
    (hs : Relation.ReflTransGen N.ShareArc Q Q') : Relation.ReflTransGen N'.ShareArc (eE '' Q) (eE '' Q') := by
  induction hs with
  | refl => exact .refl
  | tail _ hb ih => exact ih.tail (h.shareArc_image hb)

theorem isBlob_image (h : N.IsIso N' eV eE) {B : Set E} (hB : N.IsBlob B) : N'.IsBlob (eE '' B) := by
  obtain ⟨Q, hQ, rfl⟩ := hB
  refine ⟨eE '' Q, h.isCycle_image hQ, ?_⟩
  ext f
  constructor
  · rintro ⟨e, ⟨P, hP, heP⟩, rfl⟩
    exact ⟨eE '' P, h.reflTransGen_shareArc_image hP, e, heP, rfl⟩
  · rintro ⟨P', hP', hf⟩
    have := h.symm.reflTransGen_shareArc_image hP'
    have himg : eE.symm '' (eE '' Q) = Q := by simp [Set.image_image]
    rw [himg] at this
    exact ⟨eE.symm f, ⟨_, this, f, hf, rfl⟩, by simp⟩

/-- A blob of the image is the image of a blob. -/
theorem exists_eq_image_of_isBlob (h : N.IsIso N' eV eE) {B' : Set E'} (hB : N'.IsBlob B') :
    ∃ B, N.IsBlob B ∧ B' = eE '' B :=
  ⟨eE.symm '' B', h.symm.isBlob_image hB, by simp [Set.image_image]⟩

theorem blobVerts_image (h : N.IsIso N' eV eE) (B : Set E) :
    N'.blobVerts (eE '' B) = eV '' N.blobVerts B := by
  ext y
  simp only [blobVerts, Set.mem_union, Set.mem_image]
  constructor
  · rintro (⟨_, ⟨e, he, rfl⟩, rfl⟩ | ⟨_, ⟨e, he, rfl⟩, rfl⟩)
    · exact ⟨N.src e, Or.inl ⟨e, he, rfl⟩, (h.src e).symm⟩
    · exact ⟨N.tgt e, Or.inr ⟨e, he, rfl⟩, (h.tgt e).symm⟩
  · rintro ⟨_, ⟨e, he, rfl⟩ | ⟨e, he, rfl⟩, rfl⟩
    · exact Or.inl ⟨eE e, ⟨e, he, rfl⟩, h.src e⟩
    · exact Or.inr ⟨eE e, ⟨e, he, rfl⟩, h.tgt e⟩

theorem blobsNodeDisjoint_of (h : N.IsIso N' eV eE) (hd : N'.BlobsNodeDisjoint) : N.BlobsNodeDisjoint := by
  intro B B' hB hB' hne
  have := hd _ _ (h.isBlob_image hB) (h.isBlob_image hB') (eE.injective.image_injective.ne hne)
  rw [h.blobVerts_image, h.blobVerts_image] at this
  exact (Set.disjoint_image_iff eV.injective).1 this

theorem blobsNodeDisjoint (h : N.IsIso N' eV eE) : N'.BlobsNodeDisjoint ↔ N.BlobsNodeDisjoint :=
  ⟨h.blobsNodeDisjoint_of, h.symm.blobsNodeDisjoint_of⟩

/-- Sites on a common blob stay so. -/
theorem exists_isBlob_sites (h : N.IsIso N' eV eE) (i j : ι) :
    (∃ B, N'.IsBlob B ∧ N'.site i ∈ B ∧ N'.site j ∈ B) ↔ ∃ B, N.IsBlob B ∧ N.site i ∈ B ∧ N.site j ∈ B := by
  constructor
  · rintro ⟨B', hB', hi, hj⟩
    obtain ⟨B, hB, rfl⟩ := h.exists_eq_image_of_isBlob hB'
    rw [h.site, eE.injective.mem_set_image] at hi hj
    exact ⟨B, hB, hi, hj⟩
  · rintro ⟨B, hB, hi, hj⟩
    exact ⟨eE '' B, h.isBlob_image hB, by rw [h.site]; exact ⟨_, hi, rfl⟩, by rw [h.site]; exact ⟨_, hj, rfl⟩⟩

theorem derives_of (h : N.IsIso N' eV eE) {M : Finset (ι → Bool)} (hd : N.Derives M) : N'.Derives M := by
  refine ⟨fun v hv => ?_, fun u hu v hv huv => ?_, fun r hr => ?_⟩
  · have hv' : N.IsLeaf (eV.symm v) := (h.isLeaf _).1 (by simpa using hv)
    have := hd.mapsTo hv'
    rwa [← h.label, eV.apply_symm_apply] at this
  · have hu' : N.IsLeaf (eV.symm u) := (h.isLeaf _).1 (by simpa using hu)
    have hv' : N.IsLeaf (eV.symm v) := (h.isLeaf _).1 (by simpa using hv)
    have := hd.injOn hu' hv' (by rw [← h.label, ← h.label]; simpa using huv)
    simpa using this
  · obtain ⟨v, hv, rfl⟩ := hd.surjOn hr
    exact ⟨eV v, (h.isLeaf v).2 hv, h.label v⟩

theorem derives (h : N.IsIso N' eV eE) (M : Finset (ι → Bool)) : N'.Derives M ↔ N.Derives M :=
  ⟨h.symm.derives_of, h.derives_of⟩

theorem obeys_of [LinearOrder ι] (h : N.IsIso N' eV eE) {c : Crossover} (hd : N.Obeys c) : N'.Obeys c := by
  cases c with
  | single =>
    intro x hx
    obtain ⟨e, e', hne, he, he', L, hL⟩ := hd (eV.symm x) ((h.isRecomb _).1 (by simpa using hx))
    refine ⟨eE e, eE e', eE.injective.ne hne, by rw [h.tgt, he]; simp, by rw [h.tgt, he']; simp, L, fun i => ?_⟩
    have := hL i
    rw [← h.label, eV.apply_symm_apply] at this
    rw [this, h.src, h.src, h.label, h.label]
  | multiple => trivial
  | pointwise =>
    intro x hx
    obtain ⟨e, e', hne, he, he', j, hj⟩ := hd (eV.symm x) ((h.isRecomb _).1 (by simpa using hx))
    refine ⟨eE e, eE e', eE.injective.ne hne, by rw [h.tgt, he]; simp, by rw [h.tgt, he']; simp, j, fun i => ?_⟩
    have := hj i
    rw [← h.label, eV.apply_symm_apply] at this
    rw [this, h.src, h.src, h.label, h.label]

theorem obeys [LinearOrder ι] (h : N.IsIso N' eV eE) (c : Crossover) : N'.Obeys c ↔ N.Obeys c :=
  ⟨h.symm.obeys_of, h.obeys_of⟩

theorem isFullyDecomposedFor_of (h : N.IsIso N' eV eE) {G : SimpleGraph ι} (hd : N.IsFullyDecomposedFor G) :
    N'.IsFullyDecomposedFor G := by
  refine ⟨fun B hB => ?_, fun i hi => ?_, h.blobsNodeDisjoint.2 hd.nodeDisjoint⟩
  · obtain ⟨B₁, hB₁, rfl⟩ := h.exists_eq_image_of_isBlob hB
    obtain ⟨c, hc, hcs⟩ := hd.blob_component B₁ hB₁
    refine ⟨c, hc, fun i => ?_⟩
    rw [h.site, eE.injective.mem_set_image, hcs]
  · rw [h.site, h.isTreeArc]
    exact hd.isolated_treeArc i hi

theorem isFullyDecomposedFor (h : N.IsIso N' eV eE) (G : SimpleGraph ι) :
    N'.IsFullyDecomposedFor G ↔ N.IsFullyDecomposedFor G :=
  ⟨h.symm.isFullyDecomposedFor_of, h.isFullyDecomposedFor_of⟩

/-- Isomorphic networks have the same number of recombination nodes, and obey the same crossover models, and
derive the same rows, and have the same ancestral sequence, and are fully decomposed for the same graphs. -/
theorem invariants (h : N.IsIso N' eV eE) [LinearOrder ι] :
    N'.recombCount = N.recombCount ∧ (∀ c, N'.Obeys c ↔ N.Obeys c) ∧
      (∀ M, N'.Derives M ↔ N.Derives M) ∧ N'.ancestral = N.ancestral ∧
      (∀ G, N'.IsFullyDecomposedFor G ↔ N.IsFullyDecomposedFor G) := by
  refine ⟨?_, h.obeys, h.derives, ?_, h.isFullyDecomposedFor⟩
  · refine (Nat.card_congr (eV.subtypeEquiv fun x => (h.isRecomb x).symm)).symm
  · unfold ancestral
    rw [h.root, h.label]

end IsIso

/-- A rank function that increases along arcs shows a graph is acyclic. -/
theorem acyclic_of_rank {src tgt : E → V} (f : V → ℕ) (h : ∀ e, f (src e) < f (tgt e)) (v : V) :
    ¬ Relation.TransGen (fun a b => ∃ e, src e = a ∧ tgt e = b) v v :=
  acyclic_of_strict f (by rintro a b ⟨e, rfl, rfl⟩; exact h e) v

section Tree

variable {N}

/-- With no recombination node, at most one arc goes into each node. -/
theorem tgt_injective_of_no_recomb (h : ∀ x, ¬ N.IsRecomb x) : Function.Injective N.tgt := fun e f hef => by
  by_contra hne
  exact h _ ⟨e, f, hne, rfl, hef.symm⟩

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

section Recombinant

/-- `h` is obtained from `a` and `b` as the crossover model allows, `a` being the parent called `e` in `Network.Obeys`, and `b` the parent called `f`. Multiple crossovers
only ask that each state comes from a parent, which every network has at a recombination node (`Network.label_recomb`). -/
def Recombinant {ι : Type u} [LinearOrder ι] : Crossover → (ι → Bool) → (ι → Bool) → (ι → Bool) → Prop
  | .single, a, b, h => ∃ L : LowerSet ι, ∀ i, h i = if i ∈ L then a i else b i
  | .multiple, a, b, h => ∀ i, h i = a i ∨ h i = b i
  | .pointwise, a, b, h => ∃ j, ∀ i, h i = if i = j then b i else a i

/-- Multiple crossovers are no constraint. -/
theorem Recombinant.multiple {ι : Type u} [LinearOrder ι] {c : Crossover} {a b h : ι → Bool} (hr : Recombinant c a b h) : Recombinant .multiple a b h := by
  cases c with
  | single =>
    obtain ⟨L, hL⟩ := hr
    intro i
    rw [hL i]
    split_ifs <;> simp
  | multiple => exact hr
  | pointwise =>
    obtain ⟨j, hj⟩ := hr
    intro i
    rw [hj i]
    split_ifs <;> simp

/-- `Obeys` for all three models at once. -/
theorem Network.obeys_iff {ι : Type u} {V : Type v} {E : Type w} (N : Network ι V E) [LinearOrder ι] (c : Crossover) :
    N.Obeys c ↔ ∀ x, N.IsRecomb x → ∃ e f, e ≠ f ∧ N.tgt e = x ∧ N.tgt f = x ∧
      Recombinant c (N.label (N.src e)) (N.label (N.src f)) (N.label x) := by
  cases c
  · rfl
  · refine ⟨fun _ x hx => ?_, fun _ => trivial⟩
    obtain ⟨e, f, hef, he, hf⟩ := hx
    refine ⟨e, f, hef, he, hf, fun i => ?_⟩
    have := N.label_recomb e f hef (he.trans hf.symm) i
    rwa [he] at this
  · rfl

end Recombinant

section Rename

variable {ι : Type u} [LinearOrder ι] {V : Type v} {E : Type w} (N : Network ι V E)

/-- Rename the sites of a network along an isomorphism of orders. -/
def Network.renameSites {ι' : Type*} [LinearOrder ι'] (e : ι ≃o ι') : Network ι' V E where
  src := N.src
  tgt := N.tgt
  root := N.root
  site i := N.site (e.symm i)
  label v := N.label v ∘ e.symm
  simple := N.simple
  acyclic := N.acyclic
  root_iff := N.root_iff
  inDegree_le_two := N.inDegree_le_two
  site_not_recomb i f := N.site_not_recomb (e.symm i) f
  label_tree f hf i := by simpa using N.label_tree f hf (e.symm i)
  label_recomb f g hfg h i := N.label_recomb f g hfg h (e.symm i)

theorem Network.renameSites_recombCount {ι' : Type*} [LinearOrder ι'] (e : ι ≃o ι') :
    (N.renameSites e).recombCount = N.recombCount := rfl

theorem Network.renameSites_ancestral {ι' : Type*} [LinearOrder ι'] (e : ι ≃o ι') :
    (N.renameSites e).ancestral = N.ancestral ∘ e.symm := rfl

theorem Network.renameSites_obeys {ι' : Type*} [LinearOrder ι'] (e : ι ≃o ι') {c : Crossover} (h : N.Obeys c) :
    (N.renameSites e).Obeys c := by
  cases c with
  | single =>
    intro x hx
    obtain ⟨f, g, hne, hf, hg, L, hL⟩ := h x hx
    refine ⟨f, g, hne, hf, hg, LowerSet.map e L, fun i => ?_⟩
    have := hL (e.symm i)
    simpa [Network.renameSites, LowerSet.mem_map] using this
  | multiple => trivial
  | pointwise =>
    intro x hx
    obtain ⟨f, g, hne, hf, hg, j, hj⟩ := h x hx
    refine ⟨f, g, hne, hf, hg, e j, fun i => ?_⟩
    have := hj (e.symm i)
    simpa [Network.renameSites, OrderIso.symm_apply_eq] using this

theorem Network.renameSites_derives {ι' : Type*} [LinearOrder ι'] (e : ι ≃o ι') {M : Finset (ι → Bool)} (h : N.Derives M) :
    (N.renameSites e).Derives (M.image fun r => r ∘ e.symm) := by
  have hinj : Function.Injective fun r : ι → Bool => r ∘ e.symm := e.symm.surjective.injective_comp_right
  have hb : Set.BijOn (fun r : ι → Bool => r ∘ e.symm) (M : Set (ι → Bool))
      ((M.image fun r => r ∘ e.symm : Finset (ι' → Bool)) : Set (ι' → Bool)) := by
    rw [Finset.coe_image]
    exact hinj.injOn.bijOn_image
  exact hb.comp h

theorem comp_symm_comp {ι' : Type*} [LinearOrder ι'] (e : ι ≃o ι') (r : ι → Bool) : (r ∘ e.symm) ∘ e = r :=
  funext fun i => by simp

/-- `(M.image (· ∘ e.symm)).image (· ∘ e) = M`. -/
theorem image_comp_symm_image {ι' : Type*} [LinearOrder ι'] (e : ι ≃o ι') (M : Finset (ι → Bool)) :
    (M.image fun r => r ∘ e.symm).image (fun r => r ∘ e) = M := by
  ext r
  simp only [Finset.mem_image]
  constructor
  · rintro ⟨_, ⟨a, ha, rfl⟩, rfl⟩
    rwa [comp_symm_comp]
  · exact fun hr => ⟨r ∘ e.symm, ⟨r, hr, rfl⟩, comp_symm_comp e r⟩

end Rename

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

theorem R_map_orderIso_le {ι' : Type u} [LinearOrder ι'] (e : ι ≃o ι') (c : Crossover) (M : Finset (ι → Bool)) :
    {k | ∃ (a b : ℕ) (N : Network ι (Fin a) (Fin b)), N.Obeys c ∧ N.Derives M ∧ N.recombCount = k} ⊆
      {k | ∃ (a b : ℕ) (N : Network ι' (Fin a) (Fin b)), N.Obeys c ∧ N.Derives (M.image fun r => r ∘ e.symm) ∧
        N.recombCount = k} := by
  rintro k ⟨a, b, N, h₁, h₂, h₃⟩
  exact ⟨a, b, N.renameSites e, N.renameSites_obeys e h₁, N.renameSites_derives e h₂,
    (N.renameSites_recombCount e).trans h₃⟩

/-- Renaming the sites by an isomorphism of orders changes nothing, in particular from a component `↥C` to `Fin |C|`. -/
theorem R_map_orderIso {ι' : Type u} [LinearOrder ι'] (e : ι ≃o ι') (c : Crossover) (M : Finset (ι → Bool)) :
    R c (M.image fun r => r ∘ e.symm) = R c M := by
  unfold R
  congr 1
  refine Set.Subset.antisymm ?_ (R_map_orderIso_le e c M)
  have := R_map_orderIso_le e.symm c (M.image fun r => r ∘ e.symm)
  rwa [OrderIso.symm_symm, image_comp_symm_image] at this

theorem RS_map_orderIso_le {ι' : Type u} [LinearOrder ι'] (e : ι ≃o ι') (c : Crossover) (S : ι → Bool)
    (M : Finset (ι → Bool)) :
    {k | ∃ (a b : ℕ) (N : Network ι (Fin a) (Fin b)), N.Obeys c ∧ N.Derives M ∧ N.ancestral = S ∧ N.recombCount = k} ⊆
      {k | ∃ (a b : ℕ) (N : Network ι' (Fin a) (Fin b)), N.Obeys c ∧ N.Derives (M.image fun r => r ∘ e.symm) ∧
        N.ancestral = S ∘ e.symm ∧ N.recombCount = k} := by
  rintro k ⟨a, b, N, h₁, h₂, h₃, h₄⟩
  exact ⟨a, b, N.renameSites e, N.renameSites_obeys e h₁, N.renameSites_derives e h₂,
    (N.renameSites_ancestral e).trans (by rw [h₃]), (N.renameSites_recombCount e).trans h₄⟩

/-- Renaming the sites by an isomorphism of orders changes nothing, with an ancestral sequence. -/
theorem RS_map_orderIso {ι' : Type u} [LinearOrder ι'] (e : ι ≃o ι') (c : Crossover) (S : ι → Bool)
    (M : Finset (ι → Bool)) : RS c (S ∘ e.symm) (M.image fun r => r ∘ e.symm) = RS c S M := by
  unfold RS
  congr 1
  refine Set.Subset.antisymm ?_ (RS_map_orderIso_le e c S M)
  have := RS_map_orderIso_le e.symm c (S ∘ e.symm) (M.image fun r => r ∘ e.symm)
  rwa [OrderIso.symm_symm, image_comp_symm_image, comp_symm_comp] at this

end Counts

end Gusfield2007
