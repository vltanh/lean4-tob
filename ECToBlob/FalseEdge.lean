module

public import Basic.Phylogenetics.TreeSplits
public import ECToBlob.Section4

/-!
# ECToBlob §8: a false edge has a witness that is neither a cut split nor a trivial 4-blob

In its proof of Theorem 8.2 the paper says that the set `S^a(e)` of 4-taxon sets at an edge `e` of a
resolution `T₀` on which the T1 null fails is empty exactly when `e` is a cut edge, "by Corollaries
4.2 and 4.3". The corollaries give, at a false edge, a quartet that is not a cut-edge split of its
induced network; but this quartet may have a trivial 4-blob, on which the T1 null holds at the
centroid. This is a gap of the paper for non-binary networks. `falseEdge_witness` repairs it: at a
false edge whose quartets are not all trivial 4-blobs, some quartet of the multipartition is
neither.

The proof, by contradiction, moves from a quartet `ab|cd` with a trivial 4-blob to an adjacent
quartet `ab|cd'` with a cut split. Let `v` be the hub of the first and `e` its bridge towards `c`.
Then `e` separates `c, d'` from `a, b, d`. If `e` dominated all the taxa below it, then `e` would
give a cut side of the network, so a split of `T₀`, grouping `c, d'`: impossible, as they lie in
distinct blocks. So some `w` is below `e` without being dominated by `e`; then `w` is below `v` but
dominated by no arc leaving `v` (`IsStray`), and such a `w` makes the quartet of `w` and three taxa
of `ab|cd` neither a cut split nor a trivial 4-blob (`not_rdom_of_isStray`, `not_isHub_of_isStray`).

All of this is written in the language of domination of `Basic/Phylogenetics/NetworkCuts.lean`.

Corollary 4.3 enters through `FalseEdge.exists_cut_witness`. The witness lies in the multipartition
of `T₀`, the smallest of the sets of quartets that the algorithm can use at an edge, so it serves
all three quartet types and the overall p-values. The proof of Theorem 8.2 calls on
`falseEdge_witness` only in the case that is the gap, when the witness of Corollary 4.2 or 4.3 has a
trivial 4-blob (`Deterministic.Run.exists_not_t1Null_of_witness`).

API: `ECToBlob.falseEdge_witness`, `FalseEdge.exists_cut_witness`,
`FalseEdge.exists_mem_multipartitionQuartets`.
-/

@[expose] public noncomputable section

open Phylogenetics Phylogenetics.RootedNetwork Finset
open scoped Classical

namespace ECToBlob.FalseEdge

variable {V E X : Type*} {N : RootedNetwork V E X}

/-! ### Paths and domination -/

theorem reaches_of_avoiding {e : E} {u w : V} (h : N.AvoidingReach e u w) :
    N.graph.Reaches u w := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hf ih =>
    obtain ⟨f, _, hs, ht⟩ := hf
    exact ih.tail ⟨f, hs, ht⟩

/-- A path either avoids the arc `g` or passes through it. -/
theorem reaches_split (g : E) {u w : V} (h : N.graph.Reaches u w) :
    N.AvoidingReach g u w ∨
      (N.graph.Reaches u (N.graph.source g) ∧ N.graph.Reaches (N.graph.target g) w) := by
  induction h with
  | refl => exact Or.inl Relation.ReflTransGen.refl
  | tail _ hf ih =>
    obtain ⟨f, hs, ht⟩ := hf
    rcases ih with ih | ⟨h1, h2⟩
    · by_cases hfg : f = g
      · subst hfg
        right
        refine ⟨?_, ?_⟩
        · rw [hs]; exact reaches_of_avoiding ih
        · rw [ht]; exact Relation.ReflTransGen.refl
      · exact Or.inl (ih.tail ⟨f, hfg, hs, ht⟩)
    · exact Or.inr ⟨h1, h2.tail ⟨f, hs, ht⟩⟩

/-- A path avoiding `e` either avoids `g`, or passes through `g` while avoiding `e`. -/
theorem avoiding_split (e g : E) {u w : V} (h : N.AvoidingReach e u w) :
    N.AvoidingReach g u w ∨
      (N.AvoidingReach e u (N.graph.source g) ∧ N.AvoidingReach e (N.graph.target g) w) := by
  induction h with
  | refl => exact Or.inl Relation.ReflTransGen.refl
  | tail hp hf ih =>
    obtain ⟨f, hfe, hs, ht⟩ := hf
    rcases ih with ih | ⟨h1, h2⟩
    · by_cases hfg : f = g
      · subst hfg
        right
        refine ⟨?_, ?_⟩
        · rw [hs]; exact hp
        · rw [ht]; exact Relation.ReflTransGen.refl
      · exact Or.inl (ih.tail ⟨f, hfg, hs, ht⟩)
    · exact Or.inr ⟨h1, h2.tail ⟨f, hfe, hs, ht⟩⟩

theorem not_reaches_target_source (hN : N.IsPhylogenetic) (e : E) :
    ¬ N.graph.Reaches (N.graph.target e) (N.graph.source e) := fun h =>
  hN.acyclic (N.graph.source e) (Relation.TransGen.head' ⟨e, rfl, rfl⟩ h)

theorem reaches_arc (e : E) : N.graph.Reaches (N.graph.source e) (N.graph.target e) :=
  Relation.ReflTransGen.single ⟨e, rfl, rfl⟩

theorem isBelow_of_dominates (hN : N.IsPhylogenetic) {e : E} {x : X} (h : N.Dominates e x) :
    N.IsBelow e x := by
  rcases reaches_split e (hN.root_reaches (N.leaf x)) with h' | h'
  · exact absurd h' h
  · exact h'.2

/-- Two arcs dominating a taxon are comparable. -/
theorem dominates_comparable (hN : N.IsPhylogenetic) {e g : E} {x : X} (he : N.Dominates e x)
    (hg : N.Dominates g x) :
    e = g ∨ N.graph.Reaches (N.graph.target e) (N.graph.source g) ∨
      N.graph.Reaches (N.graph.target g) (N.graph.source e) := by
  rcases reaches_split g (hN.root_reaches (N.graph.source e)) with h1 | ⟨_, h1⟩
  · rcases reaches_split g (isBelow_of_dominates hN he) with h2 | ⟨h2, _⟩
    · by_cases heg : e = g
      · exact Or.inl heg
      · exact absurd ((h1.tail ⟨e, heg, rfl, rfl⟩).trans h2) hg
    · exact Or.inr (Or.inl h2)
  · exact Or.inr (Or.inr h1)

/-- An arc above `g` that dominates a taxon below `g` also dominates whatever `g` dominates. -/
theorem dominates_of_above (hN : N.IsPhylogenetic) {e g : E} {x y : X}
    (hab : N.graph.Reaches (N.graph.target e) (N.graph.source g)) (he : N.Dominates e x)
    (hgx : N.Dominates g x) (hgy : N.Dominates g y) : N.Dominates e y := by
  intro h
  have heg : g ≠ e := by
    rintro rfl
    exact not_reaches_target_source hN g hab
  rcases avoiding_split e g h with h' | ⟨h1, _⟩
  · exact hgy h'
  · rcases reaches_split e (isBelow_of_dominates hN hgx) with h2 | ⟨h2, _⟩
    · exact he ((h1.tail ⟨g, heg, rfl, rfl⟩).trans h2)
    · exact not_reaches_target_source hN e
        (hab.trans ((reaches_arc g).trans h2))

/-- A path from a vertex satisfying `P` to one that does not contains an arc leaving `P`. -/
theorem exists_exit_reaches (P : V → Prop) {u : V} {x : X}
    (h : N.graph.Reaches u (N.leaf x)) (hu : P u) (hx : ¬ P (N.leaf x)) :
    ∃ f, N.graph.Reaches (N.graph.target f) (N.leaf x) ∧ P (N.graph.source f) ∧
      ¬ P (N.graph.target f) := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact absurd hu hx
  | head hab hbc ih =>
    obtain ⟨f, hs, ht⟩ := hab
    by_cases hb : P (N.graph.target f)
    · rw [ht] at hb
      exact ih hb
    · refine ⟨f, ?_, ?_, hb⟩
      · rw [ht]; exact hbc
      · rw [hs]; exact hu

/-- The same for a path avoiding `e`. -/
theorem exists_exit_avoiding (P : V → Prop) {e : E} {u : V} {x : X}
    (h : N.AvoidingReach e u (N.leaf x)) (hu : P u) (hx : ¬ P (N.leaf x)) :
    ∃ f, f ≠ e ∧ N.graph.Reaches (N.graph.target f) (N.leaf x) ∧ P (N.graph.source f) ∧
      ¬ P (N.graph.target f) := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact absurd hu hx
  | head hab hbc ih =>
    obtain ⟨f, hfe, hs, ht⟩ := hab
    by_cases hb : P (N.graph.target f)
    · rw [ht] at hb
      exact ih hb
    · refine ⟨f, hfe, ?_, ?_, hb⟩
      · rw [ht]; exact reaches_of_avoiding hbc
      · rw [hs]; exact hu

/-! ### Hubs -/

/-- The bridge `e` leaves the hub `v` towards the taxon `x` of `q`. -/
def Leaves (N : RootedNetwork V E X) (q : Finset X) (v : V) (x : X) (e : E) : Prop :=
  N.graph.source e = v ∧ N.Dominates e x ∧ ∀ y ∈ q, y ≠ x → ¬ N.IsBelow e y

/-- The bridge `e` enters the hub `v` from the taxon `x` of `q`: the root is on the side of `x`. -/
def Enters (N : RootedNetwork V E X) (q : Finset X) (v : V) (x : X) (e : E) : Prop :=
  N.graph.target e = v ∧ (∀ y ∈ q, y ≠ x → N.Dominates e y) ∧ ¬ N.IsBelow e x

/-- The vertex `v` is the hub of a star on `q`, in the language of domination. -/
def IsHub (N : RootedNetwork V E X) (q : Finset X) (v : V) : Prop :=
  ∀ x ∈ q, ∃ e, Leaves N q v x e ∨ Enters N q v x e

/-- A trivial 4-blob has a hub. -/
theorem exists_isHub (hN : N.IsPhylogenetic) {q : Finset X} (hq : 1 < q.card)
    (h : HasTrivialFourBlob N q) : ∃ v, IsHub N q v := by
  obtain ⟨v, hv⟩ := h
  refine ⟨v, fun x hx => ?_⟩
  obtain ⟨e, he, S, hcross, hS, hvS, hinc⟩ := hv x hx
  refine ⟨e, ?_⟩
  obtain ⟨y₀, hy₀, hy₀x⟩ := Finset.exists_mem_ne hq x
  have hanc : ∀ {f z}, z ∈ q → N.graph.Reaches (N.graph.target f) (N.leaf z) →
      f ∈ N.ancestralArcs (q : Set X) := fun {f z} hz hr => ⟨z, by simpa using hz, hr⟩
  have hce : N.graph.Crosses e S := (hcross e he).2 rfl
  have hlx : N.leaf x ∈ S := (hS x hx).2 rfl
  have hly : ∀ y ∈ q, y ≠ x → N.leaf y ∉ S := fun y hy hne hin => hne ((hS y hy).1 hin)
  rcases hinc with hs | ht
  · -- the bridge leaves `v`
    have htS : N.graph.target e ∈ S := by
      rcases hce with ⟨h1, _⟩ | ⟨h1, _⟩
      · exact absurd (hs ▸ h1) hvS
      · exact h1
    have hroot : N.root ∉ S := by
      intro hr
      obtain ⟨f, hf, h1, h2⟩ := exists_exit_reaches (· ∈ S) (hN.root_reaches (N.leaf y₀)) hr
        (hly y₀ hy₀ hy₀x)
      have : f = e := (hcross f (hanc hy₀ hf)).1 (Or.inl ⟨h1, h2⟩)
      subst this
      exact hvS (hs ▸ h1)
    left
    refine ⟨hs, ?_, ?_⟩
    · intro h
      obtain ⟨f, hfe, hf, h1, h2⟩ := exists_exit_avoiding (· ∉ S) h hroot (not_not.2 hlx)
      exact hfe ((hcross f (hanc hx hf)).1 (Or.inr ⟨not_not.1 h2, h1⟩))
    · intro y hy hne hb
      obtain ⟨f, hf, h1, h2⟩ := exists_exit_reaches (· ∈ S) hb htS (hly y hy hne)
      have : f = e := (hcross f (hanc hy hf)).1 (Or.inl ⟨h1, h2⟩)
      subst this
      exact hvS (hs ▸ h1)
  · -- the bridge enters `v`
    have hroot : N.root ∈ S := by
      by_contra hr
      obtain ⟨f, hf, h1, h2⟩ := exists_exit_reaches (· ∉ S) (hN.root_reaches (N.leaf x)) hr
        (not_not.2 hlx)
      have : f = e := (hcross f (hanc hx hf)).1 (Or.inr ⟨not_not.1 h2, h1⟩)
      subst this
      exact h2 (ht ▸ hvS)
    right
    refine ⟨ht, ?_, ?_⟩
    · intro y hy hne h
      obtain ⟨f, hfe, hf, h1, h2⟩ := exists_exit_avoiding (· ∈ S) h hroot (hly y hy hne)
      exact hfe ((hcross f (hanc hy hf)).1 (Or.inl ⟨h1, h2⟩))
    · intro hb
      obtain ⟨f, hf, h1, h2⟩ := exists_exit_reaches (· ∉ S) hb (ht ▸ hvS) (not_not.2 hlx)
      have : f = e := (hcross f (hanc hx hf)).1 (Or.inr ⟨not_not.1 h2, h1⟩)
      subst this
      exact h2 (ht ▸ hvS)

/-- At most one bridge of a hub enters it. -/
theorem not_two_enters (hN : N.IsPhylogenetic) {q : Finset X} {v : V} {x y z : X} {e f : E}
    (hx : x ∈ q) (hz : z ∈ q) (hxy : x ≠ y) (hzx : z ≠ x) (hzy : z ≠ y)
    (he : Enters N q v x e) (hf : Enters N q v y f) : False := by
  rcases dominates_comparable hN (he.2.1 z hz hzx) (hf.2.1 z hz hzy) with h | h | h
  · subst h
    exact he.2.2 (isBelow_of_dominates hN (hf.2.1 x hx hxy))
  · refine not_reaches_target_source hN f ?_
    rw [hf.1, ← he.1]
    exact h
  · refine not_reaches_target_source hN e ?_
    rw [he.1, ← hf.1]
    exact h

/-- Of two taxa of a hub with a third one, one has a bridge leaving the hub. -/
theorem exists_leaves (hN : N.IsPhylogenetic) {q : Finset X} {v : V} (hv : IsHub N q v)
    {t₁ t₂ t₃ : X} (h₁ : t₁ ∈ q) (h₂ : t₂ ∈ q) (h₃ : t₃ ∈ q) (h₁₂ : t₁ ≠ t₂) (h₁₃ : t₁ ≠ t₃)
    (h₂₃ : t₂ ≠ t₃) :
    (∃ e, Leaves N q v t₁ e) ∨ ∃ e, Leaves N q v t₂ e := by
  obtain ⟨e₁, he₁⟩ := hv t₁ h₁
  obtain ⟨e₂, he₂⟩ := hv t₂ h₂
  rcases he₁ with he₁ | he₁
  · exact Or.inl ⟨e₁, he₁⟩
  rcases he₂ with he₂ | he₂
  · exact Or.inr ⟨e₂, he₂⟩
  exact (not_two_enters hN h₁ h₃ h₁₂ h₁₃.symm h₂₃.symm he₁ he₂).elim

theorem Leaves.isBelow_of_reaches (hN : N.IsPhylogenetic) {q : Finset X} {v : V} {x : X} {e g : E}
    (he : Leaves N q v x e) (hg : N.graph.Reaches (N.graph.target g) v) : N.IsBelow g x :=
  hg.trans ((he.1 ▸ reaches_arc e).trans (isBelow_of_dominates hN he.2.1))

/-- An arc dominating two taxa of a hub with a third one is above the hub. -/
theorem reaches_hub_of_dominates (hN : N.IsPhylogenetic) {q : Finset X} {v : V} (hv : IsHub N q v)
    {t₁ t₂ t₃ : X} (h₁ : t₁ ∈ q) (h₂ : t₂ ∈ q) (h₃ : t₃ ∈ q) (h₁₂ : t₁ ≠ t₂) (h₁₃ : t₁ ≠ t₃)
    (h₂₃ : t₂ ≠ t₃) {g : E} (hg₁ : N.Dominates g t₁) (hg₂ : N.Dominates g t₂) :
    N.graph.Reaches (N.graph.target g) v := by
  have key : ∀ {x y : X} {f : E}, y ∈ q → y ≠ x → Leaves N q v x f → N.Dominates g x →
      N.Dominates g y → N.graph.Reaches (N.graph.target g) v := by
    intro x y f hy hyx hf hgx hgy
    rcases dominates_comparable hN hf.2.1 hgx with h | h | h
    · subst h
      exact absurd (isBelow_of_dominates hN hgy) (hf.2.2 y hy hyx)
    · exact absurd (h.trans ((reaches_arc g).trans (isBelow_of_dominates hN hgy)))
        (hf.2.2 y hy hyx)
    · rw [← hf.1]; exact h
  rcases exists_leaves hN hv h₁ h₂ h₃ h₁₂ h₁₃ h₂₃ with ⟨f, hf⟩ | ⟨f, hf⟩
  · exact key h₂ h₁₂.symm hf hg₁ hg₂
  · exact key h₁ h₁₂ hf hg₂ hg₁

/-- An arc with two taxa of a hub with a third one not below it is not above the hub. -/
theorem not_reaches_hub (hN : N.IsPhylogenetic) {q : Finset X} {v : V} (hv : IsHub N q v)
    {t₁ t₂ t₃ : X} (h₁ : t₁ ∈ q) (h₂ : t₂ ∈ q) (h₃ : t₃ ∈ q) (h₁₂ : t₁ ≠ t₂) (h₁₃ : t₁ ≠ t₃)
    (h₂₃ : t₂ ≠ t₃) {g : E} (hg₁ : ¬ N.IsBelow g t₁) (hg₂ : ¬ N.IsBelow g t₂) :
    ¬ N.graph.Reaches (N.graph.target g) v := by
  intro h
  rcases exists_leaves hN hv h₁ h₂ h₃ h₁₂ h₁₃ h₂₃ with ⟨f, hf⟩ | ⟨f, hf⟩
  · exact hg₁ (hf.isBelow_of_reaches hN h)
  · exact hg₂ (hf.isBelow_of_reaches hN h)

/-- An arc dominating a taxon below `v`, and not above `v`, is below `v`. -/
theorem reaches_source_of_dominates (hN : N.IsPhylogenetic) {v : V} {w : X} {g : E}
    (hng : ¬ N.graph.Reaches (N.graph.target g) v) (hvw : N.graph.Reaches v (N.leaf w))
    (hg : N.Dominates g w) : N.graph.Reaches v (N.graph.source g) := by
  rcases reaches_split g (hN.root_reaches v) with h1 | ⟨_, h1⟩
  · rcases reaches_split g hvw with h2 | ⟨h2, _⟩
    · exact absurd (h1.trans h2) hg
    · exact h2
  · exact absurd h1 hng

/-- Of three taxa of a hub, two have a bridge leaving the hub. -/
theorem two_leaves (hN : N.IsPhylogenetic) {q : Finset X} {v : V} (hv : IsHub N q v)
    {t₁ t₂ t₃ : X} (h₁ : t₁ ∈ q) (h₂ : t₂ ∈ q) (h₃ : t₃ ∈ q) (h₁₂ : t₁ ≠ t₂) (h₁₃ : t₁ ≠ t₃)
    (h₂₃ : t₂ ≠ t₃) :
    ((∃ e, Leaves N q v t₁ e) ∧ ∃ e, Leaves N q v t₂ e) ∨
      ((∃ e, Leaves N q v t₁ e) ∧ ∃ e, Leaves N q v t₃ e) ∨
      ((∃ e, Leaves N q v t₂ e) ∧ ∃ e, Leaves N q v t₃ e) := by
  rcases exists_leaves hN hv h₁ h₂ h₃ h₁₂ h₁₃ h₂₃ with l₁ | l₂
  · rcases exists_leaves hN hv h₂ h₃ h₁ h₂₃ h₁₂.symm h₁₃.symm with l₂ | l₃
    · exact Or.inl ⟨l₁, l₂⟩
    · exact Or.inr (Or.inl ⟨l₁, l₃⟩)
  · rcases exists_leaves hN hv h₁ h₃ h₂ h₁₃ h₁₂ h₂₃.symm with l₁ | l₃
    · exact Or.inl ⟨l₁, l₂⟩
    · exact Or.inr (Or.inr ⟨l₂, l₃⟩)

/-- The hub of three taxa is unique. -/
theorem isHub_unique (hN : N.IsPhylogenetic) {q q' : Finset X} {u v : V} (hv : IsHub N q v)
    (hu : IsHub N q' u) {t₁ t₂ t₃ : X} (h₁ : t₁ ∈ q) (h₂ : t₂ ∈ q) (h₃ : t₃ ∈ q) (h₁' : t₁ ∈ q')
    (h₂' : t₂ ∈ q') (h₃' : t₃ ∈ q') (h₁₂ : t₁ ≠ t₂) (h₁₃ : t₁ ≠ t₃) (h₂₃ : t₂ ≠ t₃) : u = v := by
  have key : ∀ {i j k : X} {e f e' f' : E}, j ∈ q → k ∈ q' → j ≠ i → k ≠ i → Leaves N q v i e →
      Leaves N q' u i f → Leaves N q v k e' → Leaves N q' u j f' → u = v := by
    intro i j k e f e' f' hj hk hji hki he hf he' hf'
    rcases dominates_comparable hN he.2.1 hf.2.1 with h | h | h
    · subst h
      exact hf.1.symm.trans he.1
    · exact absurd (hf'.isBelow_of_reaches hN (by rw [← hf.1]; exact h)) (he.2.2 j hj hji)
    · exact absurd (he'.isBelow_of_reaches hN (by rw [← he.1]; exact h)) (hf.2.2 k hk hki)
  rcases two_leaves hN hv h₁ h₂ h₃ h₁₂ h₁₃ h₂₃ with
    ⟨⟨e₁, he₁⟩, ⟨e₂, he₂⟩⟩ | ⟨⟨e₁, he₁⟩, ⟨e₃, he₃⟩⟩ | ⟨⟨e₂, he₂⟩, ⟨e₃, he₃⟩⟩ <;>
  rcases two_leaves hN hu h₁' h₂' h₃' h₁₂ h₁₃ h₂₃ with
    ⟨⟨f₁, hf₁⟩, ⟨f₂, hf₂⟩⟩ | ⟨⟨f₁, hf₁⟩, ⟨f₃, hf₃⟩⟩ | ⟨⟨f₂, hf₂⟩, ⟨f₃, hf₃⟩⟩
  · exact key h₂ h₂' h₁₂.symm h₁₂.symm he₁ hf₁ he₂ hf₂
  · exact key h₃ h₂' h₁₃.symm h₁₂.symm he₁ hf₁ he₂ hf₃
  · exact key h₃ h₁' h₂₃.symm h₁₂ he₂ hf₂ he₁ hf₃
  · exact key h₂ h₃' h₁₂.symm h₁₃.symm he₁ hf₁ he₃ hf₂
  · exact key h₃ h₃' h₁₃.symm h₁₃.symm he₁ hf₁ he₃ hf₃
  · exact key h₂ h₁' h₂₃ h₁₃ he₃ hf₃ he₁ hf₂
  · exact key h₁ h₃' h₁₂ h₂₃.symm he₂ hf₂ he₃ hf₁
  · exact key h₁ h₂' h₁₃ h₂₃ he₃ hf₃ he₂ hf₁
  · exact key h₃ h₃' h₂₃.symm h₂₃.symm he₂ hf₂ he₃ hf₃

/-! ### A taxon stray from a hub -/

/-- The taxon `w` is below `v`, but no arc leaving `v` dominates it: a second path from the root
reaches it. -/
def IsStray (N : RootedNetwork V E X) (v : V) (w : X) : Prop :=
  N.graph.Reaches v (N.leaf w) ∧ ∀ f, N.graph.source f = v → ¬ N.Dominates f w

/-- `x₁x₂|x₃x₄` is a cut split of the network induced on the four taxa, in the language of
domination: `hasCutSplitOn_iff_separates`. -/
def RDom (N : RootedNetwork V E X) (x₁ x₂ x₃ x₄ : X) : Prop :=
  ∃ g, (N.Dominates g x₁ ∧ N.Dominates g x₂ ∧ ¬ N.IsBelow g x₃ ∧ ¬ N.IsBelow g x₄) ∨
    (N.Dominates g x₃ ∧ N.Dominates g x₄ ∧ ¬ N.IsBelow g x₁ ∧ ¬ N.IsBelow g x₂)

theorem RDom.swap {x₁ x₂ x₃ x₄ : X} (h : RDom N x₁ x₂ x₃ x₄) : RDom N x₁ x₂ x₄ x₃ := by
  obtain ⟨g, ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩⟩ := h
  · exact ⟨g, Or.inl ⟨h1, h2, h4, h3⟩⟩
  · exact ⟨g, Or.inr ⟨h2, h1, h3, h4⟩⟩

theorem RDom.symm {x₁ x₂ x₃ x₄ : X} (h : RDom N x₁ x₂ x₃ x₄) : RDom N x₃ x₄ x₁ x₂ := by
  obtain ⟨g, h | h⟩ := h
  · exact ⟨g, Or.inr h⟩
  · exact ⟨g, Or.inl h⟩

/-- A stray taxon gives no cut split with three taxa of the hub. -/
theorem not_rdom_of_isStray (hN : N.IsPhylogenetic) {q : Finset X} {v : V} (hv : IsHub N q v)
    {t₁ t₂ t₃ w : X} (h₁ : t₁ ∈ q) (h₂ : t₂ ∈ q) (h₃ : t₃ ∈ q) (h₁₂ : t₁ ≠ t₂) (h₁₃ : t₁ ≠ t₃)
    (h₂₃ : t₂ ≠ t₃) (hw : IsStray N v w) : ¬ RDom N t₁ t₂ t₃ w := by
  rintro ⟨g, ⟨g₁, g₂, _, g₄⟩ | ⟨g₃, g₄, g₁, g₂⟩⟩
  · exact g₄ ((reaches_hub_of_dominates hN hv h₁ h₂ h₃ h₁₂ h₁₃ h₂₃ g₁ g₂).trans hw.1)
  · have hng := not_reaches_hub hN hv h₁ h₂ h₃ h₁₂ h₁₃ h₂₃ g₁ g₂
    have hvg := reaches_source_of_dominates hN hng hw.1 g₄
    obtain ⟨f, hf | hf⟩ := hv t₃ h₃
    · rcases dominates_comparable hN hf.2.1 g₃ with h | h | h
      · subst h
        exact hw.2 f hf.1 g₄
      · exact hw.2 f hf.1 (dominates_of_above hN h hf.2.1 g₃ g₄)
      · exact hng (hf.1 ▸ h)
    · refine hf.2.2 ?_
      show N.graph.Reaches _ _
      rw [hf.1]
      exact hvg.trans ((reaches_arc g).trans (isBelow_of_dominates hN g₃))

/-- A stray taxon gives no trivial 4-blob with three taxa of the hub. -/
theorem not_isHub_of_isStray (hN : N.IsPhylogenetic) {q q' : Finset X} {u v : V} (hv : IsHub N q v)
    (hu : IsHub N q' u) {t₁ t₂ t₃ w : X} (h₁ : t₁ ∈ q) (h₂ : t₂ ∈ q) (h₃ : t₃ ∈ q) (h₁' : t₁ ∈ q')
    (h₂' : t₂ ∈ q') (h₃' : t₃ ∈ q') (hw' : w ∈ q') (h₁₂ : t₁ ≠ t₂) (h₁₃ : t₁ ≠ t₃)
    (h₂₃ : t₂ ≠ t₃) (hw : IsStray N v w) : False := by
  have huv := isHub_unique hN hv hu h₁ h₂ h₃ h₁' h₂' h₃' h₁₂ h₁₃ h₂₃
  subst huv
  obtain ⟨f, hf | hf⟩ := hu w hw'
  · exact hw.2 f hf.1 hf.2.1
  · refine hf.2.2 ?_
    show N.graph.Reaches _ _
    rw [hf.1]
    exact hw.1

/-- A taxon below, but not dominated by, a bridge leaving the hub is stray. -/
theorem isStray_of_leaves (hN : N.IsPhylogenetic) {q : Finset X} {v : V} {c w : X} {e : E}
    (he : Leaves N q v c e) (hb : N.IsBelow e w) (hd : ¬ N.Dominates e w) : IsStray N v w := by
  refine ⟨(he.1 ▸ reaches_arc e).trans hb, fun f hf hfw => ?_⟩
  have hef : e ≠ f := by
    rintro rfl
    exact hd hfw
  have h1 : N.AvoidingReach f N.root v := by
    rcases reaches_split f (hN.root_reaches v) with h | ⟨_, h⟩
    · exact h
    · exact absurd (hf ▸ h) (not_reaches_target_source hN f)
  rcases reaches_split f hb with h2 | ⟨h2, _⟩
  · have : N.AvoidingReach f N.root (N.graph.target e) := h1.tail ⟨e, hef, he.1, rfl⟩
    exact hfw (this.trans h2)
  · refine not_reaches_target_source hN e ?_
    rw [he.1, ← hf]
    exact h2

/-- A taxon below, but not dominated by, the bridge entering the hub is stray. -/
theorem isStray_of_enters (hN : N.IsPhylogenetic) {q : Finset X} {v : V} (hv : IsHub N q v)
    {c y z w : X} {e : E} (hy : y ∈ q) (hz : z ∈ q) (hyc : y ≠ c) (hzc : z ≠ c) (hzy : z ≠ y)
    (he : Enters N q v c e) (hb : N.IsBelow e w) (hd : ¬ N.Dominates e w) : IsStray N v w := by
  have hvw : N.graph.Reaches v (N.leaf w) := by
    rw [← he.1]; exact hb
  refine ⟨hvw, fun f hf hfw => ?_⟩
  simp only [Dominates, not_not] at hd
  rcases avoiding_split e f hd with h | ⟨h1, _⟩
  · exact hfw h
  · rw [hf] at h1
    obtain ⟨g, hg | hg⟩ := hv y hy
    · have hvy : N.graph.Reaches v (N.leaf y) :=
        (hg.1 ▸ reaches_arc g).trans (isBelow_of_dominates hN hg.2.1)
      rcases reaches_split e hvy with h2 | ⟨h2, _⟩
      · exact he.2.1 y hy hyc (h1.trans h2)
      · refine not_reaches_target_source hN e ?_
        rw [he.1]
        exact h2
    · exact not_two_enters hN hy hz hyc.symm.symm hzy hzc hg he

/-! ### Blocks of the multipartition -/

section Trees

variable [Fintype X] [DecidableEq X]

/-- The taxa `x`, `y` of the side `P` of an edge of `T` are in distinct blocks at that edge. -/
def Sep (T : Finset (Finset X)) (P : Finset X) (x y : X) : Prop :=
  x ≠ y ∧ ¬ ∃ C ∈ T, C ⊂ P ∧ x ∈ C ∧ y ∈ C

omit [Fintype X] [DecidableEq X] in
theorem Sep.symm {T : Finset (Finset X)} {P : Finset X} {x y : X} (h : Sep T P x y) :
    Sep T P y x :=
  ⟨h.1.symm, fun ⟨C, hC, hCP, hy, hx⟩ => h.2 ⟨C, hC, hCP, hx, hy⟩⟩

/-- Being in one block is transitive, so at each `z` one of the taxa in distinct blocks is in
another block than `z`. -/
theorem Sep.or {T : Finset (Finset X)} (hT : IsSplitFamily T) {P : Finset X} (hP : P ≠ univ)
    {x y : X} (h : Sep T P x y) (z : X) : Sep T P z x ∨ Sep T P z y := by
  by_contra hcon
  rw [not_or] at hcon
  have key : ∀ {t : X}, ¬ Sep T P z t → z = t ∨ ∃ C ∈ T, C ⊂ P ∧ z ∈ C ∧ t ∈ C := by
    intro t ht
    by_cases hzt : z = t
    · exact Or.inl hzt
    · right
      by_contra hne
      exact ht ⟨hzt, hne⟩
  rcases key hcon.1 with rfl | ⟨C₁, hC₁, hC₁P, hz₁, hx₁⟩
  · rcases key hcon.2 with rfl | ⟨C₂, hC₂, hC₂P, hz₂, hy₂⟩
    · exact h.1 rfl
    · exact h.2 ⟨C₂, hC₂, hC₂P, hz₂, hy₂⟩
  · rcases key hcon.2 with rfl | ⟨C₂, hC₂, hC₂P, hz₂, hy₂⟩
    · exact h.2 ⟨C₁, hC₁, hC₁P, hx₁, hz₁⟩
    · rcases hT.compatible C₁ hC₁ C₂ hC₂ with hs | hs | hs | hs
      · exact h.2 ⟨C₂, hC₂, hC₂P, hs hx₁, hy₂⟩
      · exact h.2 ⟨C₁, hC₁, hC₁P, hx₁, hs hy₂⟩
      · exact Finset.disjoint_left.1 hs hz₁ hz₂
      · apply hP
        rw [eq_univ_iff_forall]
        intro t
        have : t ∈ C₁ ∪ C₂ := hs ▸ mem_univ t
        rcases mem_union.1 this with ht | ht
        · exact hC₁P.1 ht
        · exact hC₂P.1 ht

/-- A side with at least two taxa has at least two blocks. -/
theorem exists_sep {T : Finset (Finset X)} (hT : IsSplitFamily T) {P : Finset X} (hP : P ≠ univ)
    (hcard : 2 ≤ P.card) : ∃ x ∈ P, ∃ y ∈ P, Sep T P x y := by
  obtain ⟨x₀, hx₀⟩ : P.Nonempty := Finset.card_pos.1 (by omega)
  have hne : (T.filter (· ⊂ P)).Nonempty := by
    refine ⟨{x₀}, mem_filter.2 ⟨hT.singleton_mem x₀, ?_⟩⟩
    rw [Finset.ssubset_iff_subset_ne]
    refine ⟨singleton_subset_iff.2 hx₀, ?_⟩
    rintro rfl
    simp at hcard
  obtain ⟨C, hC, hmax⟩ := Finset.exists_max_image _ Finset.card hne
  obtain ⟨hCT, hCP⟩ := mem_filter.1 hC
  obtain ⟨y, hyP, hyC⟩ := Finset.exists_of_ssubset hCP
  obtain ⟨x, hx⟩ := hT.nonempty C hCT
  refine ⟨x, hCP.1 hx, y, hyP, ?_, ?_⟩
  · rintro rfl
    exact hyC hx
  · rintro ⟨C', hC', hC'P, hxC', hyC'⟩
    rcases hT.compatible C hCT C' hC' with hs | hs | hs | hs
    · have hss : C ⊂ C' := by
        rw [Finset.ssubset_iff_subset_ne]
        refine ⟨hs, ?_⟩
        rintro rfl
        exact hyC hyC'
      have := hmax C' (mem_filter.2 ⟨hC', hC'P⟩)
      have := Finset.card_lt_card hss
      omega
    · exact hyC (hs hyC')
    · exact Finset.disjoint_left.1 hs hx hxC'
    · apply hP
      rw [eq_univ_iff_forall]
      intro t
      have : t ∈ C ∪ C' := hs ▸ mem_univ t
      rcases mem_union.1 this with ht | ht
      · exact hCP.1 ht
      · exact hC'P.1 ht

/-- The block of `x` at the side `P`. -/
def blockOf (T : Finset (Finset X)) (P : Finset X) (x : X) : Finset X :=
  P.filter fun y => ¬ Sep T P x y

/-- The blocks at the side `P`. -/
def blocks (T : Finset (Finset X)) (P : Finset X) : Finset (Finset X) :=
  P.image (blockOf T P)

/-- The blocks at the side `P`, enumerated. -/
def blockFn (T : Finset (Finset X)) (P : Finset X) : Fin (blocks T P).card → Finset X :=
  fun i => ((blocks T P).equivFin.symm i).1

omit [Fintype X] in
theorem blockFn_spec (T : Finset (Finset X)) (P : Finset X) (i : Fin (blocks T P).card) :
    ∃ x ∈ P, blockFn T P i = blockOf T P x := by
  obtain ⟨x, hx, h⟩ := mem_image.1 ((blocks T P).equivFin.symm i).2
  exact ⟨x, hx, h.symm⟩

omit [Fintype X] [DecidableEq X] in
theorem mem_blockOf_self (T : Finset (Finset X)) {P : Finset X} {x : X} (hx : x ∈ P) :
    x ∈ blockOf T P x :=
  mem_filter.2 ⟨hx, fun h => h.1 rfl⟩

theorem blockOf_eq {T : Finset (Finset X)} (hT : IsSplitFamily T) {P : Finset X} (hP : P ≠ univ)
    {x y : X} (h : ¬ Sep T P x y) : blockOf T P x = blockOf T P y := by
  have h' : ¬ Sep T P y x := fun hs => h hs.symm
  ext z
  simp only [blockOf, mem_filter, and_congr_right_iff]
  intro _
  constructor
  · intro hxz hyz
    rcases hyz.or hT hP x with hs | hs
    · exact h hs
    · exact hxz hs
  · intro hyz hxz
    rcases hxz.or hT hP y with hs | hs
    · exact h' hs
    · exact hyz hs

theorem two_le_card_blocks {T : Finset (Finset X)} (hT : IsSplitFamily T) {P : Finset X}
    (hP : P ≠ univ) (hcard : 2 ≤ P.card) : 2 ≤ (blocks T P).card := by
  obtain ⟨x, hx, y, hy, hxy⟩ := exists_sep hT hP hcard
  have hne : blockOf T P x ≠ blockOf T P y := by
    intro heq
    have : x ∈ blockOf T P y := heq ▸ mem_blockOf_self T hx
    exact (mem_filter.1 this).2 hxy.symm
  exact Finset.one_lt_card.2 ⟨_, mem_image_of_mem _ hx, _, mem_image_of_mem _ hy, hne⟩

omit [Fintype X] in
theorem blockFn_nonempty {T : Finset (Finset X)} {P : Finset X} (i : Fin (blocks T P).card) :
    (blockFn T P i).Nonempty := by
  obtain ⟨x, hx, h⟩ := blockFn_spec T P i
  exact ⟨x, h ▸ mem_blockOf_self T hx⟩

theorem blockFn_disjoint {T : Finset (Finset X)} (hT : IsSplitFamily T) {P : Finset X}
    (hP : P ≠ univ) (i i' : Fin (blocks T P).card) (hii : i ≠ i') :
    Disjoint (blockFn T P i) (blockFn T P i') := by
  obtain ⟨x, _, hxi⟩ := blockFn_spec T P i
  obtain ⟨x', _, hxi'⟩ := blockFn_spec T P i'
  rw [Finset.disjoint_left]
  intro z hz hz'
  rw [hxi] at hz
  rw [hxi'] at hz'
  have h1 := (mem_filter.1 hz).2
  have h2 := (mem_filter.1 hz').2
  have hsep : ¬ Sep T P x x' := by
    intro hs
    rcases hs.or hT hP z with h | h
    · exact h1 h.symm
    · exact h2 h.symm
  apply hii
  apply (blocks T P).equivFin.symm.injective
  apply Subtype.ext
  change blockFn T P i = blockFn T P i'
  rw [hxi, hxi', blockOf_eq hT hP hsep]

omit [Fintype X] in
theorem biUnion_blockFn (T : Finset (Finset X)) (P : Finset X) :
    Finset.univ.biUnion (blockFn T P) = P := by
  ext z
  simp only [mem_biUnion, mem_univ, true_and]
  constructor
  · rintro ⟨i, hi⟩
    obtain ⟨x, _, hxi⟩ := blockFn_spec T P i
    rw [hxi] at hi
    exact (mem_filter.1 hi).1
  · intro hz
    refine ⟨(blocks T P).equivFin ⟨blockOf T P z, mem_image_of_mem _ hz⟩, ?_⟩
    simp only [blockFn, Equiv.symm_apply_apply]
    exact mem_blockOf_self T hz

/-- **The use of Corollary 4.3.** At an edge of `T` that is not a cut edge, some quartet with taxa
in distinct blocks is not a cut-edge split. -/
theorem exists_cut_witness (hN : N.IsPhylogenetic) {T : Finset (Finset X)} (hT : IsSplitFamily T)
    {A : Finset X} (hA : 2 ≤ A.card) (hA' : 2 ≤ Aᶜ.card) (hcut : ¬ N.HasCutSplit (A : Set X)) :
    ∃ a₁ ∈ A, ∃ a₂ ∈ A, ∃ b₁ ∈ Aᶜ, ∃ b₂ ∈ Aᶜ, Sep T A a₁ a₂ ∧ Sep T Aᶜ b₁ b₂ ∧
      ¬ N.HasCutSplitOn (({a₁, a₂, b₁, b₂} : Finset X) : Set X)
        (({a₁, a₂} : Finset X) : Set X) := by
  have hAu : A ≠ univ := by
    rintro rfl
    simp at hA'
  have hAu' : Aᶜ ≠ univ := by
    intro h
    have : A = ∅ := by simpa using congrArg compl h
    subst this
    simp at hA
  have hna := two_le_card_blocks hT hAu hA
  have hnb := two_le_card_blocks hT hAu' hA'
  rcases corollary4_3 hN A hna hnb (blockFn T A) (blockFn T Aᶜ) blockFn_nonempty blockFn_nonempty
    (blockFn_disjoint hT hAu) (blockFn_disjoint hT hAu') (biUnion_blockFn T A)
    (biUnion_blockFn T Aᶜ) with h | h
  · exact absurd h hcut
  · obtain ⟨a₁, ha₁, a₂, ha₂, b₁, hb₁, b₂, hb₂, hbad⟩ :=
      h ⟨0, by omega⟩ ⟨0, by omega⟩
    obtain ⟨x, hx, hxi⟩ := blockFn_spec T A ⟨0, by omega⟩
    obtain ⟨y, hy, hyi⟩ := blockFn_spec T Aᶜ ⟨0, by omega⟩
    rw [hxi] at ha₁ ha₂
    rw [hyi] at hb₁ hb₂
    have hsepA : Sep T A a₁ a₂ := by
      obtain ⟨ha₂A, ha₂x⟩ := mem_sdiff.1 ha₂
      have hs : Sep T A x a₂ := by
        by_contra hs
        exact ha₂x (mem_filter.2 ⟨ha₂A, hs⟩)
      rcases hs.or hT hAu a₁ with h' | h'
      · exact absurd h'.symm (mem_filter.1 ha₁).2
      · exact h'
    have hsepB : Sep T Aᶜ b₁ b₂ := by
      obtain ⟨hb₂A, hb₂x⟩ := mem_sdiff.1 hb₂
      have hs : Sep T Aᶜ y b₂ := by
        by_contra hs
        exact hb₂x (mem_filter.2 ⟨hb₂A, hs⟩)
      rcases hs.or hT hAu' b₁ with h' | h'
      · exact absurd h'.symm (mem_filter.1 hb₁).2
      · exact h'
    exact ⟨a₁, (mem_filter.1 ha₁).1, a₂, (mem_sdiff.1 ha₂).1, b₁, (mem_filter.1 hb₁).1, b₂,
      (mem_sdiff.1 hb₂).1, hsepA, hsepB, hbad⟩

/-! ### Quartet trees as four taxa -/

omit [Fintype X] in
theorem card_four_of_ne {a b c d : X} (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c)
    (hbd : b ≠ d) (hcd : c ≠ d) : ({a, b, c, d} : Finset X).card = 4 := by
  simp [hab, hac, had, hbc, hbd, hcd]

omit [Fintype X] in
theorem ne_of_card_four {a b c d : X} (h : ({a, b, c, d} : Finset X).card = 4) :
    a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d := by
  have h3 : ∀ u v w : X, ({u, v, w} : Finset X).card ≤ 3 := fun _ _ _ => Finset.card_le_three
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rintro rfl
  · have e : ({a, a, c, d} : Finset X) = {a, c, d} := by ext; simp
    rw [e] at h
    have := h3 a c d
    omega
  · have e : ({a, b, a, d} : Finset X) = {a, b, d} := by ext; simp; tauto
    rw [e] at h
    have := h3 a b d
    omega
  · have e : ({a, b, c, a} : Finset X) = {a, b, c} := by ext; simp; tauto
    rw [e] at h
    have := h3 a b c
    omega
  · have e : ({a, b, b, d} : Finset X) = {a, b, d} := by ext; simp
    rw [e] at h
    have := h3 a b d
    omega
  · have e : ({a, b, c, b} : Finset X) = {a, b, c} := by ext; simp; tauto
    rw [e] at h
    have := h3 a b c
    omega
  · have e : ({a, b, c, c} : Finset X) = {a, b, c} := by ext; simp
    rw [e] at h
    have := h3 a b c
    omega

omit [Fintype X] in
theorem insert_pair_comm (a b c d : X) : ({c, d, a, b} : Finset X) = {a, b, c, d} := by
  ext z
  simp only [mem_insert, mem_singleton]
  tauto

omit [Fintype X] in
theorem insert_insert_pair_comm (a b c d : X) : ({a, b, d, c} : Finset X) = {a, b, c, d} := by
  ext z
  simp only [mem_insert, mem_singleton]
  tauto

omit [Fintype X] in
theorem pair_insert_comm (a b c d : X) : ({b, a, c, d} : Finset X) = {a, b, c, d} := by
  ext z
  simp only [mem_insert, mem_singleton]
  tauto

omit [Fintype X] in
theorem taxa_quartetTree {a b c d : X} (h : ({a, b, c, d} : Finset X).card = 4) :
    (quartetTree a b c d h).taxa = {a, b, c, d} := by
  ext z
  simp [QuartetTree.taxa, quartetTree]
  tauto

omit [Fintype X] in
theorem inter_four {A : Finset X} {a b c d : X} (ha : a ∈ A) (hb : b ∈ A) (hc : c ∉ A)
    (hd : d ∉ A) :
    A ∩ {a, b, c, d} = {a, b} := by
  ext z
  simp only [mem_inter, mem_insert, mem_singleton]
  constructor
  · rintro ⟨hz, rfl | rfl | rfl | rfl⟩
    · exact Or.inl rfl
    · exact Or.inr rfl
    · exact absurd hz hc
    · exact absurd hz hd
  · rintro (rfl | rfl)
    · exact ⟨ha, Or.inl rfl⟩
    · exact ⟨hb, Or.inr (Or.inl rfl)⟩

/-- A quartet with taxa in distinct blocks at the edge is in the multipartition of the edge. -/
theorem quartetTree_mem {T : Finset (Finset X)} {A : Finset X} {a b c d : X}
    (h : ({a, b, c, d} : Finset X).card = 4) (ha : a ∈ A) (hb : b ∈ A) (hc : c ∉ A) (hd : d ∉ A)
    (hab : Sep T A a b) (hcd : Sep T Aᶜ c d) :
    quartetTree a b c d h ∈ multipartitionQuartets T A := by
  have h₁ : A ∩ (quartetTree a b c d h).taxa = {a, b} := by
    rw [taxa_quartetTree, inter_four ha hb hc hd]
  have h₂ : Aᶜ ∩ (quartetTree a b c d h).taxa = {c, d} := by
    rw [taxa_quartetTree, ← insert_pair_comm a b c d,
      inter_four (mem_compl.2 hc) (mem_compl.2 hd) (fun h' => mem_compl.1 h' ha)
        (fun h' => mem_compl.1 h' hb)]
  simp only [multipartitionQuartets, bipartitionQuartets, mem_filter, mem_univ, true_and]
  refine ⟨?_, ?_, ?_⟩
  · rw [h₁]
    simp [quartetTree]
  · rw [h₁]
    rintro ⟨C, hC, hCA, hsub⟩
    exact hab.2 ⟨C, hC, hCA, hsub (by simp), hsub (by simp)⟩
  · rw [h₂]
    rintro ⟨C, hC, hCA, hsub⟩
    exact hcd.2 ⟨C, hC, hCA, hsub (by simp), hsub (by simp)⟩

/-- Every quartet of the multipartition has this form. -/
theorem exists_tuple {T : Finset (Finset X)} {A : Finset X} {s : QuartetTree X}
    (hs : s ∈ multipartitionQuartets T A) :
    ∃ (a b c d : X) (h : ({a, b, c, d} : Finset X).card = 4), s = quartetTree a b c d h ∧ a ∈ A ∧
      b ∈ A ∧ c ∉ A ∧ d ∉ A ∧ Sep T A a b ∧ Sep T Aᶜ c d := by
  obtain ⟨hcard, h2, hdisj⟩ := s.2
  obtain ⟨B, C, hBC, hsv⟩ := Finset.card_eq_two.1 hcard
  have hB : B ∈ s.val := by simp [hsv]
  have hC : C ∈ s.val := by simp [hsv]
  obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.1 (h2 B hB)
  obtain ⟨c, d, hcd, rfl⟩ := Finset.card_eq_two.1 (h2 C hC)
  have hdj := Finset.disjoint_left.1 (hdisj _ hB _ hC hBC)
  have hac : a ≠ c := fun h => hdj (a := a) (by simp) (by simp [h])
  have had : a ≠ d := fun h => hdj (a := a) (by simp) (by simp [h])
  have hbc : b ≠ c := fun h => hdj (a := b) (by simp) (by simp [h])
  have hbd : b ≠ d := fun h => hdj (a := b) (by simp) (by simp [h])
  have hc4 := card_four_of_ne hab hac had hbc hbd hcd
  have htaxa : s.taxa = {a, b, c, d} := by
    ext z
    simp [QuartetTree.taxa, hsv]
    tauto
  simp only [multipartitionQuartets, bipartitionQuartets, mem_filter, mem_univ, true_and] at hs
  obtain ⟨hmem, hn₁, hn₂⟩ := hs
  rw [hsv, mem_insert, mem_singleton] at hmem
  have hmemA : ∀ {y : X}, y ∈ s.taxa → (y ∈ A ∩ s.taxa ↔ y ∈ A) := fun hy => by simp [hy]
  have hta : a ∈ s.taxa := by simp [htaxa]
  have htb : b ∈ s.taxa := by simp [htaxa]
  have htc : c ∈ s.taxa := by simp [htaxa]
  have htd : d ∈ s.taxa := by simp [htaxa]
  have sep : ∀ {P : Finset X} {x y : X}, x ≠ y → x ∈ P ∩ s.taxa → y ∈ P ∩ s.taxa →
      P ∩ s.taxa = {x, y} → (¬ ∃ C ∈ T, C ⊂ P ∧ P ∩ s.taxa ⊆ C) → Sep T P x y := by
    intro P x y hxy _ _ hP hn
    refine ⟨hxy, ?_⟩
    rintro ⟨C, hC, hCP, hx, hy⟩
    refine hn ⟨C, hC, hCP, ?_⟩
    rw [hP]
    intro z hz
    rcases mem_insert.1 hz with rfl | hz
    · exact hx
    · rw [mem_singleton.1 hz]
      exact hy
  rcases hmem with hA | hA
  · have ha : a ∈ A := ((hmemA hta).1 (by simp [hA]))
    have hb : b ∈ A := ((hmemA htb).1 (by simp [hA]))
    have hc : c ∉ A := fun h => by
      have : c ∈ A ∩ s.taxa := mem_inter.2 ⟨h, htc⟩
      rw [hA] at this
      simp [hac.symm, hbc.symm] at this
    have hd : d ∉ A := fun h => by
      have : d ∈ A ∩ s.taxa := mem_inter.2 ⟨h, htd⟩
      rw [hA] at this
      simp [had.symm, hbd.symm] at this
    have hAc : Aᶜ ∩ s.taxa = {c, d} := by
      rw [htaxa, ← insert_pair_comm a b c d,
        inter_four (mem_compl.2 hc) (mem_compl.2 hd) (fun h' => mem_compl.1 h' ha)
          (fun h' => mem_compl.1 h' hb)]
    refine ⟨a, b, c, d, hc4, Subtype.ext hsv, ha, hb, hc, hd, ?_, ?_⟩
    · exact sep hab (by simp [hA]) (by simp [hA]) hA hn₁
    · exact sep hcd (by simp [hAc]) (by simp [hAc]) hAc hn₂
  · have ha : c ∈ A := ((hmemA htc).1 (by simp [hA]))
    have hb : d ∈ A := ((hmemA htd).1 (by simp [hA]))
    have hc : a ∉ A := fun h => by
      have : a ∈ A ∩ s.taxa := mem_inter.2 ⟨h, hta⟩
      rw [hA] at this
      simp [hac, had] at this
    have hd : b ∉ A := fun h => by
      have : b ∈ A ∩ s.taxa := mem_inter.2 ⟨h, htb⟩
      rw [hA] at this
      simp [hbc, hbd] at this
    have hAc : Aᶜ ∩ s.taxa = {a, b} := by
      rw [htaxa, inter_four (mem_compl.2 hc) (mem_compl.2 hd) (fun h' => mem_compl.1 h' ha)
          (fun h' => mem_compl.1 h' hb)]
    have hc4' := card_four_of_ne hcd hac.symm hbc.symm had.symm hbd.symm hab
    refine ⟨c, d, a, b, hc4', Subtype.ext ?_, ha, hb, hc, hd, ?_, ?_⟩
    · rw [hsv]
      simp [quartetTree, Finset.pair_comm]
    · exact sep hcd (by simp [hA]) (by simp [hA]) hA hn₁
    · exact sep hab (by simp [hAc]) (by simp [hAc]) hAc hn₂

omit [Fintype X] in
/-- A cut split of an induced network, read from a quartet tree. -/
theorem hasCutSplitOn_of_inducedCutSplit {a b c d : X} (h : ({a, b, c, d} : Finset X).card = 4)
    (hi : InducedCutSplit N (quartetTree a b c d h)) :
    N.HasCutSplitOn (({a, b, c, d} : Finset X) : Set X) (({a, b} : Finset X) : Set X) := by
  obtain ⟨B, hB, hcut⟩ := hi
  rw [taxa_quartetTree] at hcut
  simp only [quartetTree, mem_insert, mem_singleton] at hB
  rcases hB with rfl | rfl
  · exact hcut
  · obtain ⟨_, hac, had, hbc, hbd, _⟩ := ne_of_card_four h
    refine (hasCutSplitOn_congr ?_).1 ((hasCutSplitOn_compl _ _).2 hcut)
    ext z
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_inter_iff, Set.mem_compl_iff,
      Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨rfl | rfl | rfl | rfl, hn⟩
      · exact ⟨Or.inl rfl, Or.inl rfl⟩
      · exact ⟨Or.inr (Or.inl rfl), Or.inr rfl⟩
      · exact absurd (Or.inl rfl) hn
      · exact absurd (Or.inr rfl) hn
    · rintro ⟨hz, rfl | rfl⟩
      · exact ⟨hz, by simp [hac, had]⟩
      · exact ⟨hz, by simp [hbc, hbd]⟩

omit [Fintype X] in
/-- A cut split of an induced network in the language of domination. -/
theorem rdom_of_hasCutSplitOn (hN : N.IsPhylogenetic) {a b c d : X} (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d)
    (h : N.HasCutSplitOn (({a, b, c, d} : Finset X) : Set X) (({a, b} : Finset X) : Set X)) :
    RDom N a b c d := by
  rw [hasCutSplitOn_iff_separates hN] at h
  obtain ⟨g, ⟨_, h⟩ | ⟨_, h⟩⟩ := h
  · exact ⟨g, Or.inl ⟨h.1 a (by simp), h.1 b (by simp), h.2 c (by simp [hac.symm, hbc.symm]),
      h.2 d (by simp [had.symm, hbd.symm])⟩⟩
  · exact ⟨g, Or.inr ⟨h.1 c (by simp [hac.symm, hbc.symm]), h.1 d (by simp [had.symm, hbd.symm]),
      h.2 a (by simp), h.2 b (by simp)⟩⟩

/-! ### The heart of the repair -/

omit [DecidableEq X] in
/-- A cut side from an arc dominating all the taxa below it. -/
theorem hasCutSplit_below (hN : N.IsPhylogenetic) {e : E} (h : ∀ x, N.IsBelow e x → N.Dominates e x)
    {x₀ : X} (hx₀ : N.IsBelow e x₀) :
    N.HasCutSplit ((univ.filter fun x => N.IsBelow e x : Finset X) : Set X) := by
  rw [hasCutSplit_iff_hasCutSplitOn_univ hN, hasCutSplitOn_iff_separates hN]
  refine ⟨e, Or.inl ⟨⟨x₀, by simp [hx₀]⟩, ?_, ?_⟩⟩
  · rintro x ⟨_, hx⟩
    exact h x (by simpa using hx)
  · rintro x ⟨_, hx⟩ hb
    exact hx (by simpa using hb)

/-- A stray taxon contradicts the quartets of the edge all being cut splits or trivial 4-blobs. -/
theorem false_of_isStray (hN : N.IsPhylogenetic) {T : Finset (Finset X)} (hT : IsSplitFamily T)
    {P : Finset X} (hP : P ≠ univ) (hP' : Pᶜ ≠ univ)
    (hall : ∀ x₁ x₂ x₃ x₄, x₁ ∉ P → x₂ ∉ P → x₃ ∈ P → x₄ ∈ P → Sep T Pᶜ x₁ x₂ → Sep T P x₃ x₄ →
      HasTrivialFourBlob N {x₁, x₂, x₃, x₄} ∨ RDom N x₁ x₂ x₃ x₄)
    {a b c d w : X} {v : V} (ha : a ∉ P) (hb : b ∉ P) (hc : c ∈ P) (hd : d ∈ P)
    (hab : Sep T Pᶜ a b) (hcd : Sep T P c d) (hv : IsHub N {a, b, c, d} v)
    (hwa : w ≠ a) (hwb : w ≠ b) (hwc : w ≠ c) (hwd : w ≠ d) (hw : IsStray N v w) : False := by
  have hac : a ≠ c := fun h => ha (h ▸ hc)
  have had : a ≠ d := fun h => ha (h ▸ hd)
  have hbc : b ≠ c := fun h => hb (h ▸ hc)
  have hbd : b ≠ d := fun h => hb (h ▸ hd)
  have ma : a ∈ ({a, b, c, d} : Finset X) := by simp
  have mb : b ∈ ({a, b, c, d} : Finset X) := by simp
  have mc : c ∈ ({a, b, c, d} : Finset X) := by simp
  have md : d ∈ ({a, b, c, d} : Finset X) := by simp
  -- the quartet of `w` and three taxa `t₁ t₂ | t₃ w`, with a cut split or a trivial 4-blob
  have finish : ∀ {t₁ t₂ t₃ : X} {q' : Finset X}, t₁ ∈ ({a, b, c, d} : Finset X) →
      t₂ ∈ ({a, b, c, d} : Finset X) → t₃ ∈ ({a, b, c, d} : Finset X) → t₁ ≠ t₂ → t₁ ≠ t₃ →
      t₂ ≠ t₃ → t₁ ∈ q' → t₂ ∈ q' → t₃ ∈ q' → w ∈ q' → 1 < q'.card →
      HasTrivialFourBlob N q' ∨ RDom N t₁ t₂ t₃ w → False := by
    intro t₁ t₂ t₃ q' h₁ h₂ h₃ h₁₂ h₁₃ h₂₃ h₁' h₂' h₃' hw' hq' hor
    rcases hor with htr | hr
    · obtain ⟨u, hu⟩ := exists_isHub hN hq' htr
      exact not_isHub_of_isStray hN hv hu h₁ h₂ h₃ h₁' h₂' h₃' hw' h₁₂ h₁₃ h₂₃ hw
    · exact not_rdom_of_isStray hN hv h₁ h₂ h₃ h₁₂ h₁₃ h₂₃ hw hr
  by_cases hwP : w ∈ P
  · rcases hcd.or hT hP w with hs | hs
    · have hq : 1 < ({a, b, w, c} : Finset X).card := by
        rw [card_four_of_ne hab.1 hwa.symm hac hwb.symm hbc hwc]; omega
      exact finish ma mb mc hab.1 hac hbc (by simp) (by simp) (by simp) (by simp) hq
        ((hall a b w c ha hb hwP hc hab hs).imp id RDom.swap)
    · have hq : 1 < ({a, b, w, d} : Finset X).card := by
        rw [card_four_of_ne hab.1 hwa.symm had hwb.symm hbd hwd]; omega
      exact finish ma mb md hab.1 had hbd (by simp) (by simp) (by simp) (by simp) hq
        ((hall a b w d ha hb hwP hd hab hs).imp id RDom.swap)
  · rcases hab.or hT hP' w with hs | hs
    · have hq : 1 < ({w, a, c, d} : Finset X).card := by
        rw [card_four_of_ne hwa hwc hwd hac had hcd.1]; omega
      exact finish mc md ma hcd.1 hac.symm had.symm (by simp) (by simp) (by simp) (by simp) hq
        ((hall w a c d hwP ha hc hd hs hcd).imp id (fun h => h.symm.swap))
    · have hq : 1 < ({w, b, c, d} : Finset X).card := by
        rw [card_four_of_ne hwb hwc hwd hbc hbd hcd.1]; omega
      exact finish mc md mb hcd.1 hbc.symm hbd.symm (by simp) (by simp) (by simp) (by simp) hq
        ((hall w b c d hwP hb hc hd hs hcd).imp id (fun h => h.symm.swap))

/-- Two adjacent quartets, one with a trivial 4-blob and one with a cut split, are impossible. -/
theorem false_of_adjacent (hN : N.IsPhylogenetic) {T : Finset (Finset X)}
    (hsub : treeOfBlobs N ⊆ T) (hT : IsSplitFamily T) {P : Finset X} (hPT : P ∈ T)
    (hall : ∀ x₁ x₂ x₃ x₄, x₁ ∉ P → x₂ ∉ P → x₃ ∈ P → x₄ ∈ P → Sep T Pᶜ x₁ x₂ → Sep T P x₃ x₄ →
      HasTrivialFourBlob N {x₁, x₂, x₃, x₄} ∨ RDom N x₁ x₂ x₃ x₄)
    {a b c d d' : X} (ha : a ∉ P) (hb : b ∉ P) (hc : c ∈ P) (hd : d ∈ P) (hd' : d' ∈ P)
    (hab : Sep T Pᶜ a b) (hcd : Sep T P c d) (hcd' : Sep T P c d')
    (htr : HasTrivialFourBlob N {a, b, c, d}) (hr : RDom N a b c d') : False := by
  have hP : P ≠ univ := by
    rintro rfl
    exact ha (mem_univ a)
  have hP' : Pᶜ ≠ univ := by
    intro h
    exact (mem_compl.1 (h ▸ mem_univ c)) hc
  have hac : a ≠ c := fun h => ha (h ▸ hc)
  have had : a ≠ d := fun h => ha (h ▸ hd)
  have hbc : b ≠ c := fun h => hb (h ▸ hc)
  have hbd : b ≠ d := fun h => hb (h ▸ hd)
  have hcard := card_four_of_ne hab.1 hac had hbc hbd hcd.1
  have ma : a ∈ ({a, b, c, d} : Finset X) := by simp
  have mb : b ∈ ({a, b, c, d} : Finset X) := by simp
  have mc : c ∈ ({a, b, c, d} : Finset X) := by simp
  have md : d ∈ ({a, b, c, d} : Finset X) := by simp
  obtain ⟨v, hv⟩ := exists_isHub hN (by omega) htr
  -- a side of `T` containing `c, d'`, but not `a, d`, is impossible
  have noZ : ∀ Z ∈ T, c ∈ Z → d' ∈ Z → a ∉ Z → d ∉ Z → False := by
    intro Z hZ hcZ hd'Z haZ hdZ
    rcases hT.compatible Z hZ P hPT with h | h | h | h
    · exact hcd'.2 ⟨Z, hZ, Finset.ssubset_def.2 ⟨h, fun hPZ => hdZ (hPZ hd)⟩, hcZ, hd'Z⟩
    · exact hdZ (h hd)
    · exact Finset.disjoint_left.1 h hcZ hc
    · have : a ∈ Z ∪ P := h ▸ mem_univ a
      rcases mem_union.1 this with h' | h'
      · exact haZ h'
      · exact ha h'
  obtain ⟨e, he | he⟩ := hv c mc
  · -- the bridge towards `c` leaves the hub, and dominates `d'`
    have hed' : N.Dominates e d' := by
      obtain ⟨g, ⟨g₁, g₂, g₃, _⟩ | ⟨g₁, g₂, g₃, g₄⟩⟩ := hr
      · exact absurd (he.isBelow_of_reaches hN
          (reaches_hub_of_dominates hN hv ma mb mc hab.1 hac hbc g₁ g₂)) g₃
      · rcases dominates_comparable hN he.2.1 g₁ with h | h | h
        · subst h
          exact g₂
        · exact dominates_of_above hN h he.2.1 g₁ g₂
        · exact absurd (he.1 ▸ h) (not_reaches_hub hN hv ma mb mc hab.1 hac hbc g₃ g₄)
    by_cases hall' : ∀ x, N.IsBelow e x → N.Dominates e x
    · have hcb := isBelow_of_dominates hN he.2.1
      refine noZ (univ.filter fun x => N.IsBelow e x) (hsub ?_) (by simp [hcb])
        (by simp [isBelow_of_dominates hN hed']) (by simp [he.2.2 a ma hac])
        (by simp [he.2.2 d md hcd.1.symm])
      exact mem_filter.2 ⟨mem_univ _, ⟨c, by simp [hcb]⟩, ⟨a, by simp [he.2.2 a ma hac]⟩,
        hasCutSplit_below hN hall' hcb⟩
    · push Not at hall'
      obtain ⟨w, hwb, hwd⟩ := hall'
      have hne : ∀ y ∈ ({a, b, c, d} : Finset X), w ≠ y := by
        rintro _ hy rfl
        by_cases hyc : w = c
        · subst hyc
          exact hwd he.2.1
        · exact he.2.2 w hy hyc hwb
      exact false_of_isStray hN hT hP hP' hall ha hb hc hd hab hcd hv (hne a ma) (hne b mb)
        (hne c mc) (hne d md) (isStray_of_leaves hN he hwb hwd)
  · -- the bridge towards `c` enters the hub, and `d'` is not below it
    have hvd' : N.graph.target e = v := he.1
    have hed' : ¬ N.IsBelow e d' := by
      intro hb'
      have hvb : N.graph.Reaches v (N.leaf d') := by
        rw [← hvd']; exact hb'
      obtain ⟨g, ⟨g₁, g₂, _, g₄⟩ | ⟨g₁, g₂, g₃, g₄⟩⟩ := hr
      · exact g₄ ((reaches_hub_of_dominates hN hv ma mb mc hab.1 hac hbc g₁ g₂).trans hvb)
      · have hng := not_reaches_hub hN hv ma mb mc hab.1 hac hbc g₃ g₄
        have hvg := reaches_source_of_dominates hN hng hvb g₂
        refine he.2.2 ?_
        show N.graph.Reaches _ _
        rw [hvd']
        exact hvg.trans ((reaches_arc g).trans (isBelow_of_dominates hN g₁))
    by_cases hall' : ∀ x, N.IsBelow e x → N.Dominates e x
    · have hab' := isBelow_of_dominates hN (he.2.1 a ma hac)
      have hdb' := isBelow_of_dominates hN (he.2.1 d md hcd.1.symm)
      have hmem : (univ.filter fun x => N.IsBelow e x) ∈ T := hsub (mem_filter.2 ⟨mem_univ _,
        ⟨a, by simp [hab']⟩, ⟨c, by simp [he.2.2]⟩, hasCutSplit_below hN hall' hab'⟩)
      refine noZ _ (hT.compl_mem _ hmem) (by simp [he.2.2]) (by simp [hed']) (by simp [hab'])
        (by simp [hdb'])
    · push Not at hall'
      obtain ⟨w, hwb, hwd⟩ := hall'
      have hne : ∀ y ∈ ({a, b, c, d} : Finset X), w ≠ y := by
        rintro _ hy rfl
        by_cases hyc : w = c
        · subst hyc
          exact he.2.2 hwb
        · exact hwd (he.2.1 w hy hyc)
      exact false_of_isStray hN hT hP hP' hall ha hb hc hd hab hcd hv (hne a ma) (hne b mb)
        (hne c mc) (hne d md)
        (isStray_of_enters hN hv ma mb hac hbc.symm.symm hab.1.symm he hwb hwd)

/-- Connecting pairs in distinct blocks by replacing one taxon at a time: a property of pairs that
holds at one pair and not at another changes at one replacement. -/
theorem exists_step {T : Finset (Finset X)} (hT : IsSplitFamily T) {P : Finset X} (hP : P ≠ univ)
    (τ : X → X → Prop) (hτ : ∀ x y, τ x y → τ y x) {c d c' d' : X} (hc : c ∈ P) (hd : d ∈ P)
    (hc' : c' ∈ P) (hd' : d' ∈ P) (h : Sep T P c d) (h' : Sep T P c' d') (ht : τ c d)
    (hnt : ¬ τ c' d') :
    ∃ x ∈ P, ∃ y ∈ P, ∃ y' ∈ P, Sep T P x y ∧ Sep T P x y' ∧ τ x y ∧ ¬ τ x y' := by
  rcases h'.or hT hP c with hs | hs
  · by_cases h1 : τ c c'
    · exact ⟨c', hc', c, hc, d', hd', hs.symm, h', hτ _ _ h1, hnt⟩
    · exact ⟨c, hc, d, hd, c', hc', h, hs, ht, h1⟩
  · by_cases h1 : τ c d'
    · exact ⟨d', hd', c, hc, c', hc', hs.symm, h'.symm, hτ _ _ h1, fun h2 => hnt (hτ _ _ h2)⟩
    · exact ⟨c, hc, d, hd, d', hd', h, hs, ht, h1⟩

/-- The multipartition of an internal edge of a tree has a quartet. -/
theorem exists_mem_multipartitionQuartets {T : Finset (Finset X)} (hT : IsSplitFamily T)
    {A : Finset X} (hA : 2 ≤ A.card) (hA' : 2 ≤ Aᶜ.card) :
    ∃ s, s ∈ multipartitionQuartets T A := by
  have hAu : A ≠ univ := by
    rintro rfl
    simp at hA'
  have hAu' : Aᶜ ≠ univ := by
    intro h
    have : A = ∅ := by simpa using congrArg compl h
    subst this
    simp at hA
  obtain ⟨a, ha, b, hb, hab⟩ := exists_sep hT hAu hA
  obtain ⟨c, hc, d, hd, hcd⟩ := exists_sep hT hAu' hA'
  have hc' := mem_compl.1 hc
  have hd' := mem_compl.1 hd
  have h₁₃ : a ≠ c := fun h => hc' (h ▸ ha)
  have h₁₄ : a ≠ d := fun h => hd' (h ▸ ha)
  have h₂₃ : b ≠ c := fun h => hc' (h ▸ hb)
  have h₂₄ : b ≠ d := fun h => hd' (h ▸ hb)
  exact ⟨_, quartetTree_mem (card_four_of_ne hab.1 h₁₃ h₁₄ h₂₃ h₂₄ hcd.1) ha hb hc' hd' hab hcd⟩

end Trees

end ECToBlob.FalseEdge

namespace ECToBlob

open ECToBlob.FalseEdge

variable {V E X : Type*} [Fintype X] [DecidableEq X] {N : RootedNetwork V E X}

/-- **The repair of the proof of Theorem 8.2 (the trivial 4-blob gap).** At an edge of a resolution
of the tree of blobs that is not a cut edge, if the quartets of its multipartition are not all
trivial 4-blobs, then some quartet of the multipartition is neither a cut-edge split of its induced
network nor a trivial 4-blob. The paper's proof takes such a quartet from Corollaries 4.2 and 4.3,
whose witness may have a trivial 4-blob, at which the T1 null hypothesis holds. -/
theorem falseEdge_witness (hN : N.IsPhylogenetic) {T₀ : Finset (Finset X)}
    (hT₀ : IsResolutionOf T₀ (treeOfBlobs N)) {A : Finset X} (hA : A ∈ internalSides T₀)
    (hAT : A ∉ treeOfBlobs N)
    (hns : ∃ s ∈ multipartitionQuartets T₀ A, ¬ HasTrivialFourBlob N s.taxa) :
    ∃ s ∈ multipartitionQuartets T₀ A, ¬ InducedCutSplit N s ∧ ¬ HasTrivialFourBlob N s.taxa := by
  by_contra hcon
  push Not at hcon
  obtain ⟨hAT₀, hA₂, hA₂'⟩ := mem_filter.1 hA
  have hX : 2 ≤ Fintype.card X := hA₂.trans (Finset.card_le_univ A)
  have hT : IsSplitFamily T₀ := (isUnrootedTree_iff hX T₀).1 hT₀.1
  have hA₁ : A.Nonempty := Finset.card_pos.1 (by omega)
  have hA₁' : Aᶜ.Nonempty := Finset.card_pos.1 (by omega)
  have hnotcut : ¬ N.HasCutSplit (A : Set X) := fun h =>
    hAT (mem_filter.2 ⟨mem_univ _, hA₁, hA₁', h⟩)
  have hAu : A ≠ univ := by
    rintro rfl
    simp at hA₂'
  have hAu' : Aᶜ ≠ univ := by
    intro h
    have : A = ∅ := by simpa using congrArg compl h
    subst this
    simp at hA₂
  -- every quartet of the multipartition is a trivial 4-blob or a cut split
  have hall₀ : ∀ x₁ x₂ x₃ x₄, x₁ ∈ A → x₂ ∈ A → x₃ ∉ A → x₄ ∉ A → Sep T₀ A x₁ x₂ → Sep T₀ Aᶜ x₃ x₄ →
      HasTrivialFourBlob N {x₁, x₂, x₃, x₄} ∨ RDom N x₁ x₂ x₃ x₄ := by
    intro x₁ x₂ x₃ x₄ h₁ h₂ h₃ h₄ h₁₂ h₃₄
    have h₁₃ : x₁ ≠ x₃ := fun h => h₃ (h ▸ h₁)
    have h₁₄ : x₁ ≠ x₄ := fun h => h₄ (h ▸ h₁)
    have h₂₃ : x₂ ≠ x₃ := fun h => h₃ (h ▸ h₂)
    have h₂₄ : x₂ ≠ x₄ := fun h => h₄ (h ▸ h₂)
    have hc := card_four_of_ne h₁₂.1 h₁₃ h₁₄ h₂₃ h₂₄ h₃₄.1
    have hm := quartetTree_mem hc h₁ h₂ h₃ h₄ h₁₂ h₃₄
    by_cases hr : InducedCutSplit N (quartetTree x₁ x₂ x₃ x₄ hc)
    · exact Or.inr (rdom_of_hasCutSplitOn hN h₁₃ h₁₄ h₂₃ h₂₄
        (hasCutSplitOn_of_inducedCutSplit hc hr))
    · have := hcon _ hm hr
      rw [taxa_quartetTree] at this
      exact Or.inl this
  have hallA : ∀ x₁ x₂ x₃ x₄, x₁ ∉ A → x₂ ∉ A → x₃ ∈ A → x₄ ∈ A → Sep T₀ Aᶜ x₁ x₂ → Sep T₀ A x₃ x₄ →
      HasTrivialFourBlob N {x₁, x₂, x₃, x₄} ∨ RDom N x₁ x₂ x₃ x₄ := by
    intro x₁ x₂ x₃ x₄ h₁ h₂ h₃ h₄ h₁₂ h₃₄
    rcases hall₀ x₃ x₄ x₁ x₂ h₃ h₄ h₁ h₂ h₃₄ h₁₂ with h | h
    · rw [insert_pair_comm] at h
      exact Or.inl h
    · exact Or.inr h.symm
  have hallB : ∀ x₁ x₂ x₃ x₄, x₁ ∉ Aᶜ → x₂ ∉ Aᶜ → x₃ ∈ Aᶜ → x₄ ∈ Aᶜ → Sep T₀ Aᶜᶜ x₁ x₂ →
      Sep T₀ Aᶜ x₃ x₄ → HasTrivialFourBlob N {x₁, x₂, x₃, x₄} ∨ RDom N x₁ x₂ x₃ x₄ := by
    intro x₁ x₂ x₃ x₄ h₁ h₂ h₃ h₄ h₁₂ h₃₄
    rw [compl_compl] at h₁₂
    exact hall₀ x₁ x₂ x₃ x₄ (by simpa using h₁) (by simpa using h₂) (mem_compl.1 h₃)
      (mem_compl.1 h₄) h₁₂ h₃₄
  -- a quartet that is a trivial 4-blob, from Corollary 4.3
  obtain ⟨a₀, ha₀, b₀, hb₀, c₀, hc₀, d₀, hd₀, hab₀, hcd₀, hbad⟩ :=
    exists_cut_witness hN hT hA₂ hA₂' hnotcut
  have htr₀ : HasTrivialFourBlob N {a₀, b₀, c₀, d₀} := by
    have hc₀' := mem_compl.1 hc₀
    have hd₀' := mem_compl.1 hd₀
    have h₁₃ : a₀ ≠ c₀ := fun h => hc₀' (h ▸ ha₀)
    have h₁₄ : a₀ ≠ d₀ := fun h => hd₀' (h ▸ ha₀)
    have h₂₃ : b₀ ≠ c₀ := fun h => hc₀' (h ▸ hb₀)
    have h₂₄ : b₀ ≠ d₀ := fun h => hd₀' (h ▸ hb₀)
    have hc := card_four_of_ne hab₀.1 h₁₃ h₁₄ h₂₃ h₂₄ hcd₀.1
    have := hcon _ (quartetTree_mem hc ha₀ hb₀ hc₀' hd₀' hab₀ hcd₀)
      (fun hr => hbad (hasCutSplitOn_of_inducedCutSplit hc hr))
    rwa [taxa_quartetTree] at this
  -- a quartet that is not, by hypothesis
  obtain ⟨s, hs, hns⟩ := hns
  obtain ⟨a₁, b₁, c₁, d₁, hc₁, rfl, ha₁, hb₁, hc₁', hd₁', hab₁, hcd₁⟩ := exists_tuple hs
  rw [taxa_quartetTree] at hns
  have hsub := hT₀.2
  have hc₀' := mem_compl.1 hc₀
  have hd₀' := mem_compl.1 hd₀
  by_cases hmid : HasTrivialFourBlob N {a₁, b₁, c₀, d₀}
  · -- replacing taxa on the side `Aᶜ`
    obtain ⟨x, hx, y, hy, y', hy', hxy, hxy', hτ, hnτ⟩ := exists_step hT hAu'
      (fun x y => HasTrivialFourBlob N {a₁, b₁, x, y})
      (fun x y h => by rwa [insert_insert_pair_comm] at h) hc₀ hd₀ (mem_compl.2 hc₁')
      (mem_compl.2 hd₁') hcd₀ hcd₁ hmid hns
    have hr :=
      (hall₀ a₁ b₁ x y' ha₁ hb₁ (mem_compl.1 hx) (mem_compl.1 hy') hab₁ hxy').resolve_left hnτ
    exact false_of_adjacent hN hsub hT (hT.compl_mem A hAT₀) hallB (by simpa using ha₁)
      (by simpa using hb₁) hx hy hy' (by rwa [compl_compl]) hxy hxy' hτ hr
  · -- replacing taxa on the side `A`
    obtain ⟨x, hx, y, hy, y', hy', hxy, hxy', hτ, hnτ⟩ := exists_step hT hAu
      (fun x y => HasTrivialFourBlob N {x, y, c₀, d₀})
      (fun x y h => by rwa [pair_insert_comm] at h) ha₀ hb₀ ha₁ hb₁ hab₀ hab₁ htr₀ hmid
    have hr := (hall₀ x y' c₀ d₀ hx hy' hc₀' hd₀' hxy' hcd₀).resolve_left hnτ
    refine false_of_adjacent hN hsub hT hAT₀ hallA hc₀' hd₀' hx hy hy' hcd₀ hxy hxy' ?_ hr.symm
    rw [insert_pair_comm]
    exact hτ

end ECToBlob
