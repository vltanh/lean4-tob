module

public import Gusfield2007.TreeFacts

/-!
# Gusfield et al. 2007: the sides of an edge of a tree

Tools for the proofs on `T̄` in Sections 3.2 and 3.3. A *cut function* of an edge `e` of a tree is a map from the nodes to
`Bool` that changes across `e` and across no other edge. It says on which side of `e` a node lies, in the terms the paper uses for
its "1-side" and "0-side" (line 271). The fact behind most steps of the paper's proof of Lemma 4 is `IsCut.not_fourth`: two distinct
edges have compatible splits.
-/

@[expose] public section

open scoped Classical

namespace Gusfield2007

variable {W : Type*} {T : SimpleGraph W} {e f g h : Sym2 W} {s t : W → Bool}

/-- `s` is a cut function of the edge `e` of `T`: it changes across `e`, and across no other edge. -/
def IsCut (T : SimpleGraph W) (e : Sym2 W) (s : W → Bool) : Prop :=
  ∀ ⦃u v⦄, T.Adj u v → (s u ≠ s v ↔ s(u, v) = e)

/-- A set closed under adjacency in a connected graph is everything. -/
theorem forall_of_adj_closed (hT : T.Preconnected) {P : W → Prop} (hP : ∀ ⦃u v⦄, T.Adj u v → P u → P v) {w : W}
    (hw : P w) (x : W) : P x := by
  obtain ⟨p⟩ := hT w x
  induction p with
  | nil => exact hw
  | cons h _ ih => exact ih (hP h hw)

theorem IsCut.eq_of_ne (hs : IsCut T e s) {u v : W} (huv : T.Adj u v) (h : s(u, v) ≠ e) : s u = s v := by
  by_contra hne
  exact h ((hs huv).1 hne)

theorem IsCut.ne_of_eq (hs : IsCut T e s) {u v : W} (huv : T.Adj u v) (h : s(u, v) = e) : s u ≠ s v :=
  (hs huv).2 h

theorem IsCut.ne_self {a b : W} (hs : IsCut T s(a, b) s) (hab : T.Adj a b) : s a ≠ s b :=
  hs.ne_of_eq hab rfl

/-- Two nodes on one side of `e` have the same value. -/
theorem IsCut.eq_of_sameSide (hs : IsCut T e s) {u v : W} (h : SameSide T e u v) : s u = s v := by
  obtain ⟨p⟩ := h
  induction p with
  | nil => rfl
  | cons h _ ih =>
    rw [SimpleGraph.deleteEdges_adj] at h
    rw [← ih]
    exact hs.eq_of_ne h.1 (by simpa using h.2)

/-- Two nodes with the same value are on one side of `e`, in a connected graph. -/
theorem IsCut.sameSide_of_eq (hT : T.Preconnected) {a b : W} (hs : IsCut T s(a, b) s) (hab : T.Adj a b) {u v : W}
    (h : s u = s v) : SameSide T s(a, b) u v := by
  have : Nonempty W := ⟨a⟩
  have key : ∀ x, SameSide T s(a, b) a x ∨ SameSide T s(a, b) b x := SempleSteel2003.reachable_deleteEdges_or ⟨hT⟩ a b
  have hne := hs.ne_self hab
  rcases key u with hu | hu <;> rcases key v with hv | hv
  · exact (SimpleGraph.Reachable.symm hu).trans hv
  · exact absurd ((hs.eq_of_sameSide hu).trans (h.trans (hs.eq_of_sameSide hv).symm)) hne
  · exact absurd ((hs.eq_of_sameSide hv).trans (h.symm.trans (hs.eq_of_sameSide hu).symm)) hne
  · exact (SimpleGraph.Reachable.symm hu).trans hv

/-- On a cut function of an edge of a connected graph, the two sides of the edge are the two values. -/
theorem IsCut.sameSide_iff (hT : T.Preconnected) (he : e ∈ T.edgeSet) (hs : IsCut T e s) {u v : W} : SameSide T e u v ↔ s u = s v := by
  induction e with
  | h a b => exact ⟨hs.eq_of_sameSide, hs.sameSide_of_eq hT he⟩

/-- Every edge of a tree has a cut function. -/
theorem exists_isCut (hT : T.IsTree) (he : e ∈ T.edgeSet) : ∃ s, IsCut T e s := by
  induction e with
  | h a b =>
    have hab : T.Adj a b := he
    have hbr : ¬ SameSide T s(a, b) a b := SempleSteel2003.not_reachable_deleteEdges hT.isAcyclic hab
    refine ⟨fun x => decide (SameSide T s(a, b) a x), fun u v huv => ?_⟩
    constructor
    · intro hne
      by_contra hcon
      apply hne
      have hadj : (T.deleteEdges {s(a, b)}).Adj u v := by
        rw [SimpleGraph.deleteEdges_adj]
        exact ⟨huv, by simpa using hcon⟩
      have hiff : SameSide T s(a, b) a u ↔ SameSide T s(a, b) a v :=
        ⟨fun h => SimpleGraph.Reachable.trans h hadj.reachable,
          fun h => SimpleGraph.Reachable.trans h hadj.symm.reachable⟩
      simp [hiff]
    · intro heq
      rcases Sym2.eq_iff.1 heq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · have : SameSide T s(u, v) u u := SimpleGraph.Reachable.refl u
        simp [this, hbr]
      · have : SameSide T s(v, u) v v := SimpleGraph.Reachable.refl v
        simp [this, hbr]

/-- Compatibility of the splits of two edges: one of the four corners of two distinct edges is empty. -/
theorem IsCut.not_fourth (hT : T.Preconnected) (hs : IsCut T e s) (ht : IsCut T f t) (he : e ∈ T.edgeSet)
    (hf : f ∈ T.edgeSet) (hef : e ≠ f) {a b : Bool} {x y z w : W} (hx : s x = a ∧ t x = b) (hy : s y = a ∧ t y = !b)
    (hz : s z = !a ∧ t z = b) : ¬ (s w = !a ∧ t w = !b) := by
  intro hw
  induction e with
  | h e₁ e₂ =>
  induction f with
  | h f₁ f₂ =>
  have he' : T.Adj e₁ e₂ := he
  have hf' : T.Adj f₁ f₂ := hf
  have hsf : s f₁ = s f₂ := hs.eq_of_ne hf' (Ne.symm hef)
  have hte : t e₁ = t e₂ := ht.eq_of_ne he' hef
  -- The corner of the far ends is closed under adjacency, and so is everything.
  have hne := hs.ne_self he'
  have hne' := ht.ne_self hf'
  have hall : ∀ α β : Bool, α ≠ s f₁ → β ≠ t e₁ → ∀ v, ¬ (s v = α ∧ t v = β) := by
    intro α β hα hβ v hv
    have hclosed : ∀ x, s x = α ∧ t x = β := by
      refine forall_of_adj_closed hT (P := fun x => s x = α ∧ t x = β) ?_ hv
      rintro u v huv ⟨hu₁, hu₂⟩
      have h₁ : s(u, v) ≠ s(e₁, e₂) := by
        intro heq
        rcases Sym2.eq_iff.1 heq with ⟨rfl, -⟩ | ⟨rfl, -⟩
        · exact hβ hu₂.symm
        · exact hβ (hu₂.symm.trans hte.symm)
      have h₂ : s(u, v) ≠ s(f₁, f₂) := by
        intro heq
        rcases Sym2.eq_iff.1 heq with ⟨rfl, -⟩ | ⟨rfl, -⟩
        · exact hα hu₁.symm
        · exact hα (hu₁.symm.trans hsf.symm)
      exact ⟨(hs.eq_of_ne huv h₁).symm.trans hu₁, (ht.eq_of_ne huv h₂).symm.trans hu₂⟩
    exact hα (hclosed f₁).1.symm
  -- One of the four corners is the far one, and it is occupied.
  rcases hx with ⟨hx₁, hx₂⟩
  rcases hy with ⟨hy₁, hy₂⟩
  rcases hz with ⟨hz₁, hz₂⟩
  rcases hw with ⟨hw₁, hw₂⟩
  have hfar : ∀ v, ¬ (s v = !s f₁ ∧ t v = !t e₁) := fun v => hall _ _ (by simp) (by simp) v
  cases ha : a <;> cases hb : b <;> cases h₁ : s f₁ <;> cases h₂ : t e₁ <;> subst ha hb <;>
    simp only [Bool.not_false, Bool.not_true, h₁, h₂] at hx₁ hx₂ hy₁ hy₂ hz₁ hz₂ hw₁ hw₂ hfar <;>
    first
      | exact hfar x ⟨hx₁, hx₂⟩
      | exact hfar y ⟨hy₁, hy₂⟩
      | exact hfar z ⟨hz₁, hz₂⟩
      | exact hfar w ⟨hw₁, hw₂⟩

/-- Two cut functions of one edge are equal or opposite. -/
theorem IsCut.eq_or_eq_not (hT : T.IsTree) (he : e ∈ T.edgeSet) (hs : IsCut T e s) (ht : IsCut T e t) :
    (∀ x, s x = t x) ∨ ∀ x, s x = !t x := by
  induction e with
  | h a b =>
  have hab : T.Adj a b := he
  by_cases h : s a = t a
  · left
    intro x
    by_cases hx : s a = s x
    · have := hs.sameSide_of_eq hT.connected.preconnected hab hx
      rw [← hx, ← ht.eq_of_sameSide this, h]
    · have h₁ : s x = s b := by
        have := hs.ne_self hab
        cases h₂ : s a <;> cases h₃ : s x <;> cases h₄ : s b <;> simp_all
      have := hs.sameSide_of_eq hT.connected.preconnected hab h₁
      rw [h₁, ht.eq_of_sameSide this]
      have h₂ := hs.ne_self hab
      have h₃ := ht.ne_self hab
      cases h₄ : s a <;> cases h₅ : s b <;> cases h₆ : t a <;> cases h₇ : t b <;> simp_all
  · right
    intro x
    by_cases hx : s a = s x
    · have := hs.sameSide_of_eq hT.connected.preconnected hab hx
      rw [← hx, ← ht.eq_of_sameSide this]
      cases h₄ : s a <;> cases h₆ : t a <;> simp_all
    · have h₁ : s x = s b := by
        have := hs.ne_self hab
        cases h₂ : s a <;> cases h₃ : s x <;> cases h₄ : s b <;> simp_all
      have := hs.sameSide_of_eq hT.connected.preconnected hab h₁
      rw [h₁, ht.eq_of_sameSide this]
      have h₂ := hs.ne_self hab
      have h₃ := ht.ne_self hab
      cases h₄ : s a <;> cases h₅ : s b <;> cases h₆ : t a <;> cases h₇ : t b <;> simp_all

/-- For two distinct nodes of a tree, there's a neighbour of the first across whose edge the second lies, and it's closer
to the second. -/
theorem exists_adj_separating (hT : T.IsTree) {a b : W} (hab : a ≠ b) :
    ∃ w, T.Adj a w ∧ ¬ SameSide T s(a, w) a b ∧ SameSide T s(a, w) w b ∧ T.dist w b < T.dist a b := by
  obtain ⟨p, hp⟩ := hT.connected.exists_walk_length_eq_dist a b
  have hpath : p.IsPath := p.isPath_of_length_eq_dist hp
  cases p with
  | nil => exact absurd rfl hab
  | @cons _ w _ hadj q =>
    have ha : a ∉ q.support := (SimpleGraph.Walk.cons_isPath_iff _ _).1 hpath |>.2
    have hq : s(a, w) ∉ q.edges := fun hmem => ha (q.fst_mem_support_of_mem_edges hmem)
    have hw : SameSide T s(a, w) w b :=
      SimpleGraph.reachable_deleteEdges_iff_exists_walk.2 ⟨q, hq⟩
    refine ⟨w, hadj, fun hsame => ?_, hw, ?_⟩
    · exact SempleSteel2003.not_reachable_deleteEdges hT.isAcyclic hadj (hsame.trans hw.symm)
    · have h₁ : T.dist w b ≤ q.length := SimpleGraph.dist_le q
      rw [SimpleGraph.Walk.length_cons] at hp
      omega

/-- Line 295: "every pair of edges [...] must be incident with each other. But in a tree, that is only possible if all those edges share exactly one endpoint, and so form a star around a
single center". The only other way for edges to be pairwise incident is a triangle, and a tree has none. -/
theorem exists_common_of_pairwise_incident (hT : T.IsTree) {F : Set (Sym2 W)} (hF : F ⊆ T.edgeSet) (hne : F.Nonempty)
    (hpair : ∀ e ∈ F, ∀ f ∈ F, ∃ v, v ∈ e ∧ v ∈ f) : ∃ v, ∀ e ∈ F, v ∈ e := by
  obtain ⟨e₀, he₀⟩ := hne
  induction e₀ with
  | h a b =>
  by_cases ha : ∀ e ∈ F, a ∈ e
  · exact ⟨a, ha⟩
  push Not at ha
  obtain ⟨e₁, he₁, hae₁⟩ := ha
  refine ⟨b, fun e he => ?_⟩
  by_contra hbe
  have hab : T.Adj a b := hF he₀
  -- The edge `e₁` joins `b` and a node `c`.
  obtain ⟨v₁, hv₁, hv₁'⟩ := hpair _ he₀ _ he₁
  have hbe₁ : b ∈ e₁ := by
    rcases Sym2.mem_iff.1 hv₁ with rfl | rfl
    · exact absurd hv₁' hae₁
    · exact hv₁'
  obtain ⟨c, rfl⟩ := hbe₁
  have hac : a ≠ c := fun heq => hae₁ (by rw [heq]; simp)
  have hbc : T.Adj b c := hF he₁
  -- The edge `e` contains `a`, since it's incident with `s(a, b)`, and `c`, since it's incident with `s(b, c)`.
  obtain ⟨v₂, hv₂, hv₂'⟩ := hpair _ he₀ _ he
  have hae : a ∈ e := by
    rcases Sym2.mem_iff.1 hv₂ with rfl | rfl
    · exact hv₂'
    · exact absurd hv₂' hbe
  obtain ⟨d, rfl⟩ := hae
  obtain ⟨v₃, hv₃, hv₃'⟩ := hpair _ he₁ _ he
  have hcd : c = d := by
    rcases Sym2.mem_iff.1 hv₃ with rfl | rfl
    · exact absurd hv₃' hbe
    · rcases Sym2.mem_iff.1 hv₃' with h' | h'
      · exact absurd h'.symm hac
      · exact h'
  subst hcd
  have hac' : T.Adj a c := hF he
  -- That's a triangle.
  obtain ⟨s, hs⟩ := exists_isCut hT (show s(a, b) ∈ T.edgeSet from hab)
  have h₁ : s b = s c := hs.eq_of_ne hbc fun heq => by
    rcases Sym2.eq_iff.1 heq with ⟨h', -⟩ | ⟨-, h'⟩
    · exact T.ne_of_adj hab h'.symm
    · exact hac h'.symm
  have h₂ : s a = s c := hs.eq_of_ne hac' fun heq => by
    rcases Sym2.eq_iff.1 heq with ⟨-, h'⟩ | ⟨h', -⟩
    · exact T.ne_of_adj hbc h'.symm
    · exact T.ne_of_adj hab h'
  exact hs.ne_self hab (h₂.trans h₁.symm)

section Rows

variable {X : Type*} {φ : X → W}

/-- Two maps to `Bool` with one partition. -/
theorem split_iff_of_iff {f g : X → Bool} {c d : Bool} (h : ∀ x, f x = c ↔ g x = d) (x y : X) : f x = f y ↔ g x = g y := by
  have hx := h x
  have hy := h y
  revert hx hy
  cases f x <;> cases f y <;> cases g x <;> cases g y <;> cases c <;> cases d <;> simp

theorem bool_iff_of_not_both {a b : Bool} (h₁ : ¬ (a = true ∧ b = true)) (h₂ : a = false → b ≠ false) :
    a = true ↔ b = false := by
  revert h₁ h₂
  cases a <;> cases b <;> simp

/-- Each side of an edge of a tree with its leaves labelled has a label (the paper's "a leaf reachable", line 285). -/
theorem exists_row_side [Finite W] (hT : T.IsTree) (hφ : ∀ v, (T.neighborSet v).ncard ≤ 1 → v ∈ Set.range φ) {a b : W}
    (hab : T.Adj a b) {s : W → Bool} (hs : IsCut T s(a, b) s) : ∃ x, s (φ x) = s a := by
  induction hn : {w | s w = s a}.ncard using Nat.strong_induction_on generalizing a b s with
  | _ n ih =>
    by_cases hdeg : (T.neighborSet a).ncard ≤ 1
    · obtain ⟨x, hx⟩ := hφ a hdeg
      exact ⟨x, by rw [hx]⟩
    · obtain ⟨u, hu, hub⟩ : ∃ u ∈ T.neighborSet a, u ≠ b := by
        by_contra hcon
        push Not at hcon
        apply hdeg
        have : T.neighborSet a ⊆ {b} := fun u hu => hcon u hu
        calc (T.neighborSet a).ncard ≤ ({b} : Set W).ncard := Set.ncard_le_ncard this (Set.toFinite _)
          _ = 1 := Set.ncard_singleton b
      have hau : T.Adj a u := hu
      have hne : s(a, u) ≠ s(a, b) := by
        intro heq
        rcases Sym2.eq_iff.1 heq with ⟨-, h⟩ | ⟨h₁, h₂⟩
        · exact hub h
        · exact T.ne_of_adj hab h₁
      obtain ⟨t, ht⟩ := exists_isCut hT (show s(a, u) ∈ T.edgeSet from hau)
      have ht' : IsCut T s(u, a) t := by rwa [Sym2.eq_swap]
      have hsu : s a = s u := hs.eq_of_ne hau hne
      have hta : t a = t b := ht.eq_of_ne hab (Ne.symm hne)
      have htne : t a ≠ t u := ht.ne_self hau
      have hab' : s a ≠ s b := hs.ne_self hab
      have hsub : {w | t w = t u} ⊂ {w | s w = s a} := by
        refine ⟨fun w hw => ?_, fun hcon => htne (hcon (a := a) rfl)⟩
        by_contra hw'
        have hw₁ : s w = !s a := by
          change ¬ (s w = s a) at hw'
          cases h₁ : s w <;> cases h₂ : s a <;> simp_all
        have hu₁ : t u = !t a := by
          cases h₁ : t u <;> cases h₂ : t a <;> simp_all
        have hb₁ : s b = !s a := by
          cases h₁ : s b <;> cases h₂ : s a <;> simp_all
        exact IsCut.not_fourth hT.connected.preconnected hs ht hab hau (Ne.symm hne)
          (x := a) (y := u) (z := b) (w := w) ⟨rfl, rfl⟩ ⟨hsu.symm, hu₁⟩ ⟨hb₁, hta.symm⟩
          ⟨hw₁, by rw [show t w = t u from hw, hu₁]⟩
      have hlt : {w | t w = t u}.ncard < n := hn ▸ Set.ncard_lt_ncard hsub (Set.toFinite _)
      obtain ⟨x, hx⟩ := ih _ hlt hau.symm ht' rfl
      refine ⟨x, ?_⟩
      by_contra hcon
      have hw₁ : s (φ x) = !s a := by
        cases h₁ : s (φ x) <;> cases h₂ : s a <;> simp_all
      have hu₁ : t u = !t a := by
        cases h₁ : t u <;> cases h₂ : t a <;> simp_all
      have hb₁ : s b = !s a := by
        cases h₁ : s b <;> cases h₂ : s a <;> simp_all
      exact IsCut.not_fourth hT.connected.preconnected hs ht hab hau (Ne.symm hne)
        (x := a) (y := u) (z := b) (w := φ x) ⟨rfl, rfl⟩ ⟨hsu.symm, hu₁⟩ ⟨hb₁, hta.symm⟩
        ⟨hw₁, by rw [hx, hu₁]⟩

end Rows

end Gusfield2007
