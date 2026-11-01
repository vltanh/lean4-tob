module

public import Gusfield2007.Blobs
public import Mathlib.Data.Fintype.Option
public import Mathlib.SetTheory.Cardinal.Finite

/-!
# Gusfield et al. 2007: operations on a network for the proofs of Sections 3.4 and 3.5

* `Decomp.prune`: removing arcs and leaves, and what's left without a path to a remaining leaf;
* `Decomp.addLeaf`: a new leaf with the label of a node, below that node;
* `Decomp.exists_copy_of_siteFree`: a blob with no site has a recombination node with the label of its two parents. So a network with
  the fewest recombination nodes has no such blob, the fact behind the proof note at Theorem 3.

These are helpers, in their own namespace, for `Gusfield2007.Decomposition`.
-/

@[expose] public section

open scoped Classical

namespace Gusfield2007

namespace Decomp

universe u v w

variable {ι : Type*} {V : Type*} {E : Type*} (N : Network ι V E)

/-! ### Removing arcs and leaves -/

section Prune

variable (A : E → Prop) (L : V → Prop)

/-- A path through the arcs in `A`. -/
def RA (u v : V) : Prop := Relation.ReflTransGen (fun a b => ∃ e, A e ∧ N.src e = a ∧ N.tgt e = b) u v

/-- A node with a path through the arcs in `A` to a leaf in `L`. -/
def Kept (v : V) : Prop := ∃ l, L l ∧ RA N A v l

/-- When arcs out of `A` and leaves out of `L` can be removed: each node other than the root keeps an arc in; a node losing an arc has the
label of the parent it keeps; `L` is made of leaves, and for each site a leaf in `L` has its state changed. -/
structure PruneHyp : Prop where
  in_arc : ∀ v, v ≠ N.root → ∃ e, A e ∧ N.tgt e = v
  drop : ∀ e f, A e → ¬ A f → N.tgt e = N.tgt f → ∀ i, N.label (N.tgt e) i = N.label (N.src e) i
  leaf : ∀ l, L l → N.IsLeaf l
  col : ∀ i, ∃ l, L l ∧ N.label l i ≠ N.label N.root i
  nonempty : ∃ l, L l

variable {N A L} (h : PruneHyp N A L)

include h in
theorem PruneHyp.ra_root [Finite V] (v : V) : RA N A N.root v := by
  refine N.arc_induction (P := fun v => RA N A N.root v) (fun v ih => ?_) v
  by_cases hv : v = N.root
  · rw [hv]
    exact Relation.ReflTransGen.refl
  · obtain ⟨e, he, rfl⟩ := h.in_arc v hv
    exact (ih e rfl).tail ⟨e, he, rfl, rfl⟩

include h in
theorem PruneHyp.A_site (i : ι) : A (N.site i) := by
  have hne : N.tgt (N.site i) ≠ N.root := fun heq => (N.root_iff _).2 heq (N.site i) rfl
  obtain ⟨e, he, ht⟩ := h.in_arc _ hne
  rwa [← N.site_not_recomb i e ht]

include h in
/-- A node with a site's state changed is below that site's arc, through the arcs in `A`. -/
theorem PruneHyp.ra_site [Finite V] {i : ι} (v : V) (hv : N.label v i ≠ N.label N.root i) : RA N A (N.tgt (N.site i)) v := by
  revert hv
  refine N.arc_induction (P := fun v => N.label v i ≠ N.label N.root i → RA N A (N.tgt (N.site i)) v) (fun v ih hv => ?_) v
  have hne : v ≠ N.root := by
    rintro rfl
    exact hv rfl
  obtain ⟨e, he, rfl⟩ := h.in_arc v hne
  have hA : ∀ {a}, A a → N.tgt a = N.tgt e → N.label (N.src a) i ≠ N.label N.root i → RA N A (N.tgt (N.site i)) (N.tgt e) :=
    fun {a} ha hat hl => (ih a hat hl).tail ⟨a, ha, rfl, hat⟩
  by_cases hdrop : ∃ f, ¬ A f ∧ N.tgt f = N.tgt e
  · obtain ⟨f, hf, hft⟩ := hdrop
    have hl := h.drop e f he hf hft.symm i
    exact hA he rfl (hl ▸ hv)
  · push Not at hdrop
    by_cases hu : ∀ f, N.tgt f = N.tgt e → f = e
    · have hl := N.label_tree e hu i
      by_cases hs : N.site i = e
      · rw [hs]
        exact Relation.ReflTransGen.refl
      · simp only [hs, ↓reduceIte] at hl
        exact hA he rfl (hl ▸ hv)
    · push Not at hu
      obtain ⟨f, hft, hfe⟩ := hu
      have hfA : A f := by
        by_contra hcon
        exact hdrop f hcon hft
      rcases N.label_recomb e f (Ne.symm hfe) hft.symm i with hl | hl
      · exact hA he rfl (hl ▸ hv)
      · exact hA hfA hft (by rw [← hl]; exact hv)

theorem Kept.src {e : E} (he : A e) (hk : Kept N A L (N.tgt e)) : Kept N A L (N.src e) := by
  obtain ⟨l, hl, hr⟩ := hk
  exact ⟨l, hl, Relation.ReflTransGen.head ⟨e, he, rfl, rfl⟩ hr⟩

include h in
theorem PruneHyp.kept_root [Finite V] : Kept N A L N.root := by
  obtain ⟨l, hl⟩ := h.nonempty
  exact ⟨l, hl, h.ra_root l⟩

include h in
theorem PruneHyp.kept_site [Finite V] (i : ι) : Kept N A L (N.tgt (N.site i)) := by
  obtain ⟨l, hl, hne⟩ := h.col i
  exact ⟨l, hl, h.ra_site l hne⟩

/-- The network with the arcs out of `A`, and all that doesn't reach `L`, removed. -/
noncomputable def prune [Finite V] : Network ι {v // Kept N A L v} {e // A e ∧ Kept N A L (N.tgt e)} where
  src e := ⟨N.src e.1, Kept.src e.2.1 e.2.2⟩
  tgt e := ⟨N.tgt e.1, e.2.2⟩
  root := ⟨N.root, h.kept_root⟩
  site i := ⟨N.site i, h.A_site i, h.kept_site i⟩
  label v := N.label v.1
  simple e f h₁ h₂ := Subtype.ext (N.simple _ _ (congrArg Subtype.val h₁) (congrArg Subtype.val h₂))
  acyclic v hv := by
    refine N.acyclic v.1 (Relation.TransGen.lift (p := fun a b => ∃ e, _ = a ∧ _ = b) Subtype.val ?_ _ _ hv)
    rintro a b ⟨e, rfl, rfl⟩
    exact ⟨e.1, rfl, rfl⟩
  root_iff v := by
    constructor
    · intro hv
      apply Subtype.ext
      by_contra hne
      obtain ⟨e, he, ht⟩ := h.in_arc v.1 hne
      exact hv ⟨e, he, ht ▸ v.2⟩ (Subtype.ext ht)
    · rintro rfl e he
      exact (N.root_iff N.root).2 rfl e.1 (congrArg Subtype.val he)
  inDegree_le_two e f g h₁ h₂ := by
    rcases N.inDegree_le_two e.1 f.1 g.1 (congrArg Subtype.val h₁) (congrArg Subtype.val h₂) with h' | h' | h'
    · exact Or.inl (Subtype.ext h')
    · exact Or.inr (Or.inl (Subtype.ext h'))
    · exact Or.inr (Or.inr (Subtype.ext h'))
  site_not_recomb i f hf := Subtype.ext (N.site_not_recomb i f.1 (congrArg Subtype.val hf))
  label_tree e he i := by
    have hiff : (⟨N.site i, h.A_site i, h.kept_site i⟩ : {e // A e ∧ Kept N A L (N.tgt e)}) = e ↔ N.site i = e.1 := Subtype.ext_iff
    by_cases hu : ∀ f, N.tgt f = N.tgt e.1 → f = e.1
    · have := N.label_tree e.1 hu i
      simp only [hiff]
      exact this
    · push Not at hu
      obtain ⟨f, hft, hfe⟩ := hu
      have hfA : ¬ A f := fun hA => by
        have := he ⟨f, hA, by rw [hft]; exact e.2.2⟩ (Subtype.ext hft)
        exact hfe (congrArg Subtype.val this)
      have hl := h.drop e.1 f e.2.1 hfA hft.symm i
      have hs : N.site i ≠ e.1 := fun hs => hfe (by
        rw [← hs] at hft
        rw [N.site_not_recomb i f hft, hs])
      simp only [hiff, hs, ↓reduceIte]
      exact hl
  label_recomb e f hne ht i :=
    N.label_recomb e.1 f.1 (fun h' => hne (Subtype.ext h')) (congrArg Subtype.val ht) i

theorem prune_isLeaf [Finite V] (v : {v // Kept N A L v}) : (prune h).IsLeaf v ↔ L v.1 := by
  constructor
  · intro hv
    obtain ⟨l, hl, hr⟩ := v.2
    cases Relation.ReflTransGen.cases_head hr with
    | inl heq => rwa [heq]
    | inr hex =>
      obtain ⟨c, ⟨e, he, h₁, rfl⟩, hc⟩ := hex
      exact absurd (Subtype.ext h₁) (hv ⟨e, he, ⟨l, hl, hc⟩⟩)
  · intro hL e he
    exact h.leaf _ hL e.1 (congrArg Subtype.val he)

theorem prune_derives [Finite V] {M : Finset (ι → Bool)} (hM : Set.BijOn N.label {v | L v} (M : Set (ι → Bool))) :
    (prune h).Derives M := by
  refine ⟨fun v hv => hM.mapsTo ((prune_isLeaf h v).1 hv), fun a ha b hb hab => ?_, fun r hr => ?_⟩
  · exact Subtype.ext (hM.injOn ((prune_isLeaf h a).1 ha) ((prune_isLeaf h b).1 hb) hab)
  · obtain ⟨l, hl, rfl⟩ := hM.surjOn hr
    exact ⟨⟨l, l, hl, Relation.ReflTransGen.refl⟩, (prune_isLeaf h _).2 hl, rfl⟩

theorem isRecomb_of_prune [Finite V] {x : {v // Kept N A L v}} (hx : (prune h).IsRecomb x) : N.IsRecomb x.1 := by
  obtain ⟨e, f, hne, rfl, hf⟩ := hx
  exact ⟨e.1, f.1, fun h' => hne (Subtype.ext h'), rfl, congrArg Subtype.val hf⟩

theorem prune_obeys [LinearOrder ι] [Finite V] {c : Crossover} (hc : N.Obeys c) : (prune h).Obeys c := by
  -- The two arcs into a recombination node of the pruned network are all the arcs into it.
  have hkey : ∀ {x : {v // Kept N A L v}}, (prune h).IsRecomb x → ∀ e, N.tgt e = x.1 → ∃ e' : {e // A e ∧ Kept N A L (N.tgt e)},
      e'.1 = e ∧ (prune h).tgt e' = x := by
    rintro x ⟨e₁, e₂, hne, h₁, h₂⟩ e he
    have h₁' : N.tgt e₁.1 = x.1 := congrArg Subtype.val h₁
    have h₂' : N.tgt e₂.1 = x.1 := congrArg Subtype.val h₂
    rcases N.inDegree_le_two e e₁.1 e₂.1 (he.trans h₁'.symm) (h₁'.trans h₂'.symm) with h' | h' | h'
    · exact ⟨e₁, h'.symm, h₁⟩
    · exact ⟨e₂, h'.symm, h₂⟩
    · exact absurd (Subtype.ext h') hne
  cases c with
  | single =>
    intro x hx
    obtain ⟨e, f, hne, he, hf, Ls, hl⟩ := hc x.1 (isRecomb_of_prune h hx)
    obtain ⟨e', rfl, he'⟩ := hkey hx e he
    obtain ⟨f', rfl, hf'⟩ := hkey hx f hf
    exact ⟨e', f', fun h' => hne (congrArg Subtype.val h'), he', hf', Ls, hl⟩
  | multiple => trivial
  | pointwise =>
    intro x hx
    obtain ⟨e, f, hne, he, hf, j, hl⟩ := hc x.1 (isRecomb_of_prune h hx)
    obtain ⟨e', rfl, he'⟩ := hkey hx e he
    obtain ⟨f', rfl, hf'⟩ := hkey hx f hf
    exact ⟨e', f', fun h' => hne (congrArg Subtype.val h'), he', hf', j, hl⟩

theorem prune_recombCount_le [Finite V] : (prune h).recombCount ≤ N.recombCount :=
  Nat.card_le_card_of_injective (fun x : {x // (prune h).IsRecomb x} => (⟨x.1.1, isRecomb_of_prune h x.2⟩ : {x // N.IsRecomb x}))
    fun _ _ hab => Subtype.ext (Subtype.ext (congrArg (fun z : {x // N.IsRecomb x} => z.1) hab))

/-- Removing an arc into a recombination node removes that recombination node. -/
theorem prune_recombCount_lt [Finite V] {f : E} (hf : ¬ A f) (hx : N.IsRecomb (N.tgt f)) :
    (prune h).recombCount < N.recombCount := by
  have hinj : Function.Injective (fun x : {x // (prune h).IsRecomb x} => (⟨x.1.1, isRecomb_of_prune h x.2⟩ : {x // N.IsRecomb x})) :=
    fun _ _ hab => Subtype.ext (Subtype.ext (congrArg (fun z : {x // N.IsRecomb x} => z.1) hab))
  have hnot : (⟨N.tgt f, hx⟩ : {x // N.IsRecomb x}) ∉ Set.range (fun x : {x // (prune h).IsRecomb x} =>
      (⟨x.1.1, isRecomb_of_prune h x.2⟩ : {x // N.IsRecomb x})) := by
    rintro ⟨x, hxf⟩
    have hxv : x.1.1 = N.tgt f := congrArg (fun z : {x // N.IsRecomb x} => z.1) hxf
    obtain ⟨e₁, e₂, hne, h₁, h₂⟩ := x.2
    have h₁' : N.tgt e₁.1 = N.tgt f := (congrArg Subtype.val h₁).trans hxv
    have h₂' : N.tgt e₂.1 = N.tgt f := (congrArg Subtype.val h₂).trans hxv
    rcases N.inDegree_le_two f e₁.1 e₂.1 h₁'.symm (h₁'.trans h₂'.symm) with h' | h' | h'
    · exact hf (h' ▸ e₁.2.1)
    · exact hf (h' ▸ e₂.2.1)
    · exact hne (Subtype.ext h')
  rw [Network.recombCount, Network.recombCount, Nat.card_congr (Equiv.ofInjective _ hinj)]
  exact Finite.card_subtype_lt hnot

end Prune

/-! ### A new leaf -/

section AddLeaf

/-- `N` with a new leaf below `v`, with the label of `v`, and an arc with no site to it. -/
noncomputable def addLeaf (v : V) : Network ι (Option V) (Option E) where
  src e := match e with
    | none => some v
    | some e => some (N.src e)
  tgt e := match e with
    | none => none
    | some e => some (N.tgt e)
  root := some N.root
  site i := some (N.site i)
  label x := match x with
    | none => N.label v
    | some x => N.label x
  simple e f h₁ h₂ := by
    cases e with
    | none => cases f with
      | none => rfl
      | some f => simp at h₂
    | some e => cases f with
      | none => simp at h₂
      | some f =>
        simp only [Option.some.injEq] at h₁ h₂
        rw [N.simple e f h₁ h₂]
  acyclic x hx := by
    have key : ∀ {a b}, Relation.TransGen (fun a b => ∃ e, (match e with
        | none => some v
        | some e => some (N.src e)) = a ∧ (match e with
        | none => none
        | some e => some (N.tgt e)) = b) a b →
        ∀ y, b = some y → ∃ z, a = some z ∧ Relation.TransGen N.Arc z y := by
      intro a b hab
      induction hab using Relation.TransGen.head_induction_on with
      | single hb =>
        rintro y rfl
        obtain ⟨e, h₁, h₂⟩ := hb
        cases e with
        | none => simp at h₂
        | some e =>
          simp only [Option.some.injEq] at h₂
          exact ⟨N.src e, h₁.symm, Relation.TransGen.single ⟨e, rfl, h₂⟩⟩
      | head hb _ ih =>
        rintro y rfl
        obtain ⟨z, rfl, hz⟩ := ih y rfl
        obtain ⟨e, h₁, h₂⟩ := hb
        cases e with
        | none => simp at h₂
        | some e =>
          simp only [Option.some.injEq] at h₂
          exact ⟨N.src e, h₁.symm, Relation.TransGen.head ⟨e, rfl, h₂⟩ hz⟩
    cases x with
    | none =>
      obtain ⟨c', ⟨f, h₄, h₅⟩, -⟩ := Relation.TransGen.head'_iff.1 hx
      cases f <;> simp at h₄
    | some y =>
      obtain ⟨z, hz, hzy⟩ := key hx y rfl
      obtain rfl : y = z := Option.some.inj hz
      exact N.acyclic y hzy
  root_iff x := by
    cases x with
    | none =>
      constructor
      · intro h
        exact absurd rfl (h none)
      · intro h
        simp at h
    | some y =>
      constructor
      · intro h
        have : ∀ e, N.tgt e ≠ y := fun e he => h (some e) (by simp [he])
        rw [(N.root_iff y).1 this]
      · intro h e he
        simp only [Option.some.injEq] at h
        cases e with
        | none => simp at he
        | some e =>
          simp only [Option.some.injEq] at he
          exact (N.root_iff y).2 h e he
  inDegree_le_two e f g h₁ h₂ := by
    cases e with
    | none =>
      cases f with
      | none => exact Or.inl rfl
      | some f => simp at h₁
    | some e =>
      cases f with
      | none => simp at h₁
      | some f =>
        cases g with
        | none => simp at h₂
        | some g =>
          simp only [Option.some.injEq] at h₁ h₂ ⊢
          exact N.inDegree_le_two e f g h₁ h₂
  site_not_recomb i f hf := by
    cases f with
    | none => simp at hf
    | some f =>
      simp only [Option.some.injEq] at hf ⊢
      exact N.site_not_recomb i f hf
  label_tree e he i := by
    cases e with
    | none => simp
    | some e =>
      have hu : ∀ f, N.tgt f = N.tgt e → f = e := fun f hf =>
        Option.some.inj (he (some f) (by simp [hf]))
      have := N.label_tree e hu i
      simpa using this
  label_recomb e f hne ht i := by
    cases e with
    | none =>
      cases f with
      | none => exact absurd rfl hne
      | some f => simp at ht
    | some e =>
      cases f with
      | none => simp at ht
      | some f =>
        simp only [Option.some.injEq] at ht
        exact N.label_recomb e f (fun h => hne (by rw [h])) ht i

variable {N} {v : V}

theorem addLeaf_emb : Network.Emb N (addLeaf N v) some some where
  f_inj := Option.some_injective _
  g_inj := Option.some_injective _
  src _ := rfl
  tgt _ := rfl

theorem isRecomb_addLeaf {x : Option V} : (addLeaf N v).IsRecomb x ↔ ∃ y, x = some y ∧ N.IsRecomb y := by
  constructor
  · rintro ⟨e, f, hne, rfl, hf⟩
    cases e with
    | none =>
      cases f with
      | none => exact absurd rfl hne
      | some f => simp [addLeaf] at hf
    | some e =>
      cases f with
      | none => simp [addLeaf] at hf
      | some f =>
        simp only [addLeaf, Option.some.injEq] at hf
        exact ⟨N.tgt e, rfl, e, f, fun h => hne (by rw [h]), rfl, hf⟩
  · rintro ⟨y, rfl, e, f, hne, rfl, hf⟩
    exact ⟨some e, some f, by simpa using hne, rfl, by simp [addLeaf, hf]⟩

theorem addLeaf_recombCount : (addLeaf N v).recombCount = N.recombCount := by
  have hbij : Function.Bijective (fun y : {x // N.IsRecomb x} =>
      (⟨some y.1, isRecomb_addLeaf.2 ⟨y.1, rfl, y.2⟩⟩ : {x // (addLeaf N v).IsRecomb x})) := by
    constructor
    · intro a b hab
      exact Subtype.ext (Option.some.inj (congrArg (fun z : {x // (addLeaf N v).IsRecomb x} => z.1) hab))
    · rintro ⟨x, hx⟩
      obtain ⟨y, rfl, hy⟩ := isRecomb_addLeaf.1 hx
      exact ⟨⟨y, hy⟩, rfl⟩
  exact (Nat.card_congr (Equiv.ofBijective _ hbij)).symm

theorem addLeaf_ancestral : (addLeaf N v).ancestral = N.ancestral := rfl

theorem addLeaf_obeys [LinearOrder ι] {c : Crossover} (hc : N.Obeys c) : (addLeaf N v).Obeys c := by
  cases c with
  | single =>
    intro x hx
    obtain ⟨y, rfl, hy⟩ := isRecomb_addLeaf.1 hx
    obtain ⟨e, f, hne, rfl, hf, Ls, hl⟩ := hc y hy
    exact ⟨some e, some f, by simpa using hne, rfl, by simp [addLeaf, hf], Ls, hl⟩
  | multiple => trivial
  | pointwise =>
    intro x hx
    obtain ⟨y, rfl, hy⟩ := isRecomb_addLeaf.1 hx
    obtain ⟨e, f, hne, rfl, hf, j, hl⟩ := hc y hy
    exact ⟨some e, some f, by simpa using hne, rfl, by simp [addLeaf, hf], j, hl⟩

/-- The leaves are the old ones, and the new one, when `v` wasn't a leaf. -/
theorem addLeaf_derives {M : Finset (ι → Bool)} (hN : N.Derives M) (hv : ¬ N.IsLeaf v) (hl : N.label v ∉ M) :
    (addLeaf N v).Derives (insert (N.label v) M) := by
  have hleaf : ∀ x : Option V, (addLeaf N v).IsLeaf x ↔ x = none ∨ ∃ y, x = some y ∧ N.IsLeaf y := by
    intro x
    constructor
    · intro hx
      cases x with
      | none => exact Or.inl rfl
      | some y =>
        refine Or.inr ⟨y, rfl, fun e he => hx (some e) (by simp [addLeaf, he])⟩
    · rintro (rfl | ⟨y, rfl, hy⟩) e he
      · cases e <;> simp [addLeaf] at he
      · cases e with
        | none =>
          simp only [addLeaf, Option.some.injEq] at he
          exact hv (he ▸ hy)
        | some e =>
          simp only [addLeaf, Option.some.injEq] at he
          exact hy e he
  refine ⟨fun x hx => ?_, fun a ha b hb hab => ?_, fun r hr => ?_⟩
  · rcases (hleaf x).1 hx with rfl | ⟨y, rfl, hy⟩
    · simp [addLeaf]
    · exact Finset.mem_coe.2 (Finset.mem_insert_of_mem (Finset.mem_coe.1 (hN.mapsTo hy)))
  · rcases (hleaf a).1 ha with rfl | ⟨y, rfl, hy⟩ <;> rcases (hleaf b).1 hb with rfl | ⟨y', rfl, hy'⟩
    · rfl
    · exact absurd (Finset.mem_coe.1 (hN.mapsTo hy')) (by rw [show N.label y' = N.label v from hab.symm]; exact hl)
    · exact absurd (Finset.mem_coe.1 (hN.mapsTo hy)) (by rw [show N.label y = N.label v from hab]; exact hl)
    · rw [hN.injOn hy hy' hab]
  · rcases Finset.mem_insert.1 (Finset.mem_coe.1 hr) with rfl | hr
    · exact ⟨none, (hleaf _).2 (Or.inl rfl), rfl⟩
    · obtain ⟨y, hy, rfl⟩ := hN.surjOn (Finset.mem_coe.2 hr)
      exact ⟨some y, (hleaf _).2 (Or.inr ⟨y, rfl, hy⟩), rfl⟩

/-- A cycle of `addLeaf N v` is a cycle of `N`: the new arc ends at a leaf that's not a recombination node. -/
theorem addLeaf_cycle_back {Q' : Set (Option E)} (hQ' : (addLeaf N v).IsCycle Q') : ∃ Q, N.IsCycle Q ∧ Q' = some '' Q := by
  refine (addLeaf_emb (N := N) (v := v)).cycle_back (fun x hx => ?_) hQ' ?_
  · obtain ⟨y, hy, hr⟩ := isRecomb_addLeaf.1 hx
    rwa [Option.some.inj hy]
  · obtain ⟨w, x, p, q, ⟨hrec, hp, hq, -, -⟩, rfl⟩ := hQ'
    have hxs : x ≠ none := by
      rintro rfl
      obtain ⟨y, hy, -⟩ := isRecomb_addLeaf.1 hrec
      simp at hy
    have key : ∀ {l : List (Option E)} {u : Option V}, (addLeaf N v).IsPath u x l → ∀ a ∈ l, a ∈ Set.range some := by
      intro l
      induction l with
      | nil => simp
      | cons b t ih =>
        rintro u ⟨-, h₂⟩ a ha
        rcases List.mem_cons.1 ha with rfl | ha
        · cases a with
          | some e => exact ⟨e, rfl⟩
          | none =>
            exfalso
            cases t with
            | nil => exact hxs (Eq.symm h₂)
            | cons c t' =>
              obtain ⟨h₃, -⟩ := h₂
              cases c <;> simp [addLeaf] at h₃
        · exact ih h₂ a ha
    rintro a (ha | ha)
    · exact key hp a ha
    · exact key hq a ha

theorem addLeaf_fullyDecomposed {G : SimpleGraph ι} (hN : N.IsFullyDecomposedFor G) :
    (addLeaf N v).IsFullyDecomposedFor G := by
  have hE := addLeaf_emb (N := N) (v := v)
  have hback : ∀ Q', (addLeaf N v).IsCycle Q' → (∃ e ∈ Q', e ∈ Set.range some) → ∃ Q, N.IsCycle Q ∧ Q' = some '' Q :=
    fun Q' hQ' _ => addLeaf_cycle_back hQ'
  have hblob : ∀ {B'}, (addLeaf N v).IsBlob B' → ∃ B, N.IsBlob B ∧ B' = some '' B := by
    rintro B' ⟨Q', hQ', rfl⟩
    obtain ⟨Q, hQ, rfl⟩ := addLeaf_cycle_back hQ'
    exact ⟨_, ⟨Q, hQ, rfl⟩, hE.blob_image hback hQ⟩
  have hverts : ∀ B : Set E, (addLeaf N v).blobVerts (some '' B) = some '' N.blobVerts B := by
    intro B
    ext x
    constructor
    · rintro (⟨a, ⟨e, he, rfl⟩, rfl⟩ | ⟨a, ⟨e, he, rfl⟩, rfl⟩)
      · exact ⟨N.src e, Or.inl ⟨e, he, rfl⟩, rfl⟩
      · exact ⟨N.tgt e, Or.inr ⟨e, he, rfl⟩, rfl⟩
    · rintro ⟨y, ⟨e, he, rfl⟩ | ⟨e, he, rfl⟩, rfl⟩
      · exact Or.inl ⟨some e, ⟨e, he, rfl⟩, rfl⟩
      · exact Or.inr ⟨some e, ⟨e, he, rfl⟩, rfl⟩
  refine ⟨fun B' hB' => ?_, fun i hi => ?_, fun B₁ B₂ h₁ h₂ hne => ?_⟩
  · obtain ⟨B, hB, rfl⟩ := hblob hB'
    obtain ⟨c, hc, hs⟩ := hN.blob_component B hB
    refine ⟨c, hc, fun i => ?_⟩
    rw [← hs i]
    change some (N.site i) ∈ some '' B ↔ _
    simp
  · rintro ⟨Q', hQ', hmem⟩
    obtain ⟨Q, hQ, rfl⟩ := addLeaf_cycle_back hQ'
    obtain ⟨e, he, heq⟩ := hmem
    obtain rfl : e = N.site i := Option.some.inj heq
    exact hN.isolated_treeArc i hi ⟨Q, hQ, he⟩
  · obtain ⟨B, hB, rfl⟩ := hblob h₁
    obtain ⟨B', hB', rfl⟩ := hblob h₂
    have hd := hN.nodeDisjoint B B' hB hB' (fun heq => hne (by rw [heq]))
    rw [hverts, hverts]
    exact (Set.disjoint_image_iff (Option.some_injective _)).2 hd

end AddLeaf

/-! ### A blob with no site -/

/-- A blob with no site has a recombination node with the label of both its parents: take a recombination node of a cycle of the blob with
nothing above it in the blob; the two paths of the cycle have no recombination node inside, nor site, and so keep the label of their start. -/
theorem exists_copy_of_siteFree [Finite V] {B : Set E} (hB : N.IsBlob B) (hs : ∀ i, N.site i ∉ B) :
    ∃ e f, e ≠ f ∧ N.tgt e = N.tgt f ∧ (∀ i, N.label (N.tgt e) i = N.label (N.src e) i) ∧
      ∀ i, N.label (N.tgt e) i = N.label (N.src f) i := by
  obtain ⟨Q₀, hQ₀, rfl⟩ := hB
  obtain ⟨ρ, hρ⟩ := N.exists_rank
  -- A cycle of the class with lowest recombination node.
  let P : ℕ → Prop := fun n => ∃ Q w x p q, Relation.ReflTransGen N.ShareArc Q₀ Q ∧ N.IsCycleOn w x p q ∧
    Q = {e | e ∈ p ∨ e ∈ q} ∧ ρ x = n
  have hP : ∃ n, P n := by
    obtain ⟨w, x, p, q, hc, hQ⟩ := hQ₀
    exact ⟨_, Q₀, w, x, p, q, Relation.ReflTransGen.refl, hc, hQ, rfl⟩
  obtain ⟨Q, w, x, p, q, hQ, hc, rfl, hρx⟩ := Nat.find_spec hP
  have hmin : ∀ {n}, P n → Nat.find hP ≤ n := fun {n} hn => Nat.find_min' hP hn
  obtain ⟨hrec, hp, hq, hpq, hd⟩ := id hc
  have hcyc : N.IsCycle {e | e ∈ p ∨ e ∈ q} := ⟨w, x, p, q, hc, rfl⟩
  -- A node inside a path of the cycle isn't a recombination node.
  have hint : ∀ {a}, (a ∈ p ∨ a ∈ q) → N.tgt a ≠ x → ∀ g, N.tgt g = N.tgt a → g = a := by
    intro a ha hax g hg
    by_contra hga
    obtain ⟨w', p', q', -, -, hc'⟩ := Network.exists_isCycleOn_of_tgt_eq (Ne.symm hga) hg.symm
    have hQ' : Relation.ReflTransGen N.ShareArc Q₀ {e | e ∈ p' ++ [a] ∨ e ∈ q' ++ [g]} :=
      hQ.tail ⟨hcyc, ⟨w', _, _, _, hc', rfl⟩, ⟨a, ha, Or.inl (by simp)⟩⟩
    have hle := hmin (n := ρ (N.tgt a)) ⟨_, w', _, _, _, hQ', hc', rfl, rfl⟩
    have hreach : N.Reach (N.tgt a) x := by
      rcases ha with ha | ha
      · exact hp.reach_tgt_of_mem ha
      · exact hq.reach_tgt_of_mem ha
    obtain hrefl | ⟨c, hc₁, hc₂⟩ := Relation.ReflTransGen.cases_head hreach
    · exact hax hrefl
    · have := lt_of_transGen (r := N.Arc) ρ (by rintro a b ⟨e, rfl, rfl⟩; exact hρ e) (Relation.TransGen.head' hc₁ hc₂)
      omega
  -- The arcs of a path of the cycle keep the label of the start.
  have hkeep : ∀ {l : List E} {u : V}, N.IsPath u x l → (∀ a ∈ l, a ∈ p ∨ a ∈ q) → N.label u = N.label w →
      ∀ a ∈ l, N.label (N.src a) = N.label w := by
    intro l
    induction l with
    | nil => simp
    | cons b t ih =>
      rintro u ⟨h₁, h₂⟩ hall hu a ha
      have hb : N.label (N.src b) = N.label w := by rw [h₁, hu]
      rcases List.mem_cons.1 ha with rfl | ha
      · exact hb
      · refine ih h₂ (fun c hc' => hall c (by simp [hc'])) ?_ a ha
        have hbx : N.tgt b ≠ x := by
          intro heq
          rw [heq] at h₂
          obtain ⟨c, hc', -⟩ : ∃ c, c ∈ t ∧ True := by
            cases t with
            | nil => simp at ha
            | cons c t' => exact ⟨c, by simp, trivial⟩
          exact Network.not_reach_tgt_src c ((h₂.reach_tgt_of_mem hc').trans (h₂.reach_src_of_mem hc'))
        have huniq := hint (hall b (by simp)) hbx
        funext i
        have hl := N.label_tree b huniq i
        have hsb : N.site i ≠ b := by
          intro heq
          apply hs i
          refine ⟨_, hQ, ?_⟩
          rw [heq]
          exact hall b (by simp)
        simp only [hsb, ↓reduceIte] at hl
        rw [hl, hb]
  have hkeepp := hkeep hp (fun a ha => Or.inl ha) rfl
  have hkeepq := hkeep hq (fun a ha => Or.inr ha) rfl
  -- The last arcs of the two paths.
  have hlast : ∀ {l : List E} {u : V}, N.IsPath u x l → l ≠ [] → ∃ l' e, l = l' ++ [e] ∧ N.IsPath u (N.src e) l' ∧ N.tgt e = x := by
    intro l
    induction l with
    | nil => simp
    | cons b t ih =>
      rintro u ⟨h₁, h₂⟩ -
      by_cases ht : t = []
      · subst ht
        exact ⟨[], b, rfl, h₁.symm, h₂⟩
      · obtain ⟨l', e, rfl, h₃, h₄⟩ := ih h₂ ht
        exact ⟨b :: l', e, rfl, ⟨h₁, h₃⟩, h₄⟩
  have hnil : ∀ {l l' : List E}, N.IsPath w x l → N.IsPath w x l' → l ≠ l' → l ≠ [] := by
    rintro l l' h₁ h₂ hne rfl
    have hwx : w = x := h₁
    subst hwx
    cases l' with
    | nil => exact hne rfl
    | cons b t =>
      obtain ⟨h₃, h₄⟩ := h₂
      exact Network.not_reach_tgt_src b (h₄.reach |>.trans (h₃ ▸ Relation.ReflTransGen.refl))
  obtain ⟨p₁, e, rfl, hp₁, hex⟩ := hlast hp (hnil hp hq hpq)
  obtain ⟨q₁, f, rfl, hq₁, hfx⟩ := hlast hq (hnil hq hp (Ne.symm hpq))
  have hef : e ≠ f := by
    rintro rfl
    cases p₁ with
    | nil =>
      cases q₁ with
      | nil => exact hpq rfl
      | cons b t =>
        have hwe : w = N.src e := hp₁
        obtain ⟨h₃, h₄⟩ := hq₁
        rw [← hwe] at h₄
        have h₅ := h₄.reach
        rw [← h₃] at h₅
        exact Network.not_reach_tgt_src b h₅
    | cons b t =>
      cases q₁ with
      | nil =>
        have hwe : w = N.src e := hq₁
        obtain ⟨h₃, h₄⟩ := hp₁
        rw [← hwe] at h₄
        have h₅ := h₄.reach
        rw [← h₃] at h₅
        exact Network.not_reach_tgt_src b h₅
      | cons b' t' =>
        -- The arc before `e` on each path has a target in common.
        have hl₁ : ∀ {l : List E} {u : V} {c}, N.IsPath u (N.src e) (c :: l) → ∃ a ∈ c :: l, N.tgt a = N.src e := by
          intro l
          induction l with
          | nil =>
            rintro u c ⟨-, h₂⟩
            exact ⟨c, by simp, h₂⟩
          | cons d l ih =>
            rintro u c ⟨-, h₂⟩
            obtain ⟨a, ha, hat⟩ := ih h₂
            exact ⟨a, List.mem_cons_of_mem _ ha, hat⟩
        obtain ⟨a, ha, hat⟩ := hl₁ hp₁
        obtain ⟨a', ha', hat'⟩ := hl₁ hq₁
        have hz := hd a (List.mem_append_left _ ha) a' (List.mem_append_left _ ha') (hat.trans hat'.symm)
        rw [hat] at hz
        exact Network.src_ne_tgt e (hz.trans hex.symm)
  have hl₁ := hkeepp e (by simp)
  have hl₂ := hkeepq f (by simp)
  refine ⟨e, f, hef, hex.trans hfx.symm, fun i => ?_, fun i => ?_⟩
  · rcases N.label_recomb e f hef (hex.trans hfx.symm) i with h' | h'
    · exact h'
    · rw [h', hl₁, hl₂]
  · rcases N.label_recomb e f hef (hex.trans hfx.symm) i with h' | h'
    · rw [h', hl₁, hl₂]
    · exact h'

end Decomp

end Gusfield2007
