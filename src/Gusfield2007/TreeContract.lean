module

public import Gusfield2007.TreeCuts

/-!
# Gusfield et al. 2007: a perfect phylogeny with every internal edge labelled

The Perfect Phylogeny Theorem gives a tree whose edges can be unlabelled, and which can have nodes of degree two. `T̄` (line 264,
line 289, line 271) has neither. This file contracts the edges that aren't needed: it keeps one edge for each split of a
character and for each split of a single leaf, and contracts all the others (`IsPerfectPhylogeny.exists_normal`).
-/

@[expose] public section

open scoped Classical

namespace Gusfield2007

universe u v w

variable {W : Type u} {X : Type v} {κ : Type w}

/-- Two maps that separate `x` from everything else have the same fibres. -/
theorem split_eq_of_single {f g : X → Bool} {x : X} (hf : ∀ z, f z = f x ↔ z = x) (hg : ∀ z, g z = g x ↔ z = x)
    (a b : X) : f a = f b ↔ g a = g b := by
  have nb : ∀ {α β γ : Bool}, α ≠ γ → β ≠ γ → α = β := by decide
  by_cases ha : a = x <;> by_cases hb : b = x
  · simp [ha, hb]
  · subst ha
    exact ⟨fun h => absurd h.symm (mt (hf b).1 hb), fun h => absurd h.symm (mt (hg b).1 hb)⟩
  · subst hb
    exact ⟨fun h => absurd h (mt (hf a).1 ha), fun h => absurd h (mt (hg a).1 ha)⟩
  · exact ⟨fun _ => nb (mt (hg a).1 ha) (mt (hg b).1 hb), fun _ => nb (mt (hf a).1 ha) (mt (hf b).1 hb)⟩

/-- What the contraction provides, on a tree `T` with labels `φ` and edges `edge`. Each side of an edge has a label; distinct
edges have distinct splits; the split of each label from the others is the split of an edge; and each edge is labelled by a
character, or has such a split. -/
structure KeptSplits (T : SimpleGraph W) (φ : X → W) (edge : κ → Sym2 W) : Prop where
  isTree : T.IsTree
  row_side : ∀ ⦃a b⦄, T.Adj a b → ∀ c, IsCut T s(a, b) c → ∃ x, c (φ x) = c a
  split_inj : ∀ ⦃e f⦄, e ∈ T.edgeSet → f ∈ T.edgeSet → ∀ c c', IsCut T e c → IsCut T f c' →
    (∀ x y, c (φ x) = c (φ y) ↔ c' (φ x) = c' (φ y)) → e = f
  single : ∀ x y, x ≠ y → ∃ e ∈ T.edgeSet, ∃ c, IsCut T e c ∧ ∀ z, c (φ z) = c (φ x) ↔ z = x
  labelled_or_single : ∀ ⦃a b⦄, T.Adj a b →
    (∃ k, edge k = s(a, b)) ∨ ∃ x, ∀ c, IsCut T s(a, b) c → ∀ z, c (φ z) = c (φ x) ↔ z = x

namespace KeptSplits

variable {T : SimpleGraph W} {φ : X → W} {edge : κ → Sym2 W} (h : KeptSplits T φ edge)

include h

theorem injective : Function.Injective φ := by
  intro x y hxy
  by_contra hne
  obtain ⟨e, -, c, -, hz⟩ := h.single x y hne
  exact hne ((hz y).1 (by rw [hxy])).symm

theorem degree_aux {x : X} {u : W} (hu : T.Adj (φ x) u) {p : Sym2 W} (hp : p ∈ T.edgeSet) {c' : W → Bool}
    (hc' : IsCut T p c') (hz : ∀ z, c' (φ z) = c' (φ x) ↔ z = x) (hne : s(φ x, u) ≠ p) : False := by
  have hconn := h.isTree.connected.preconnected
  have nb : ∀ {α β : Bool}, α ≠ β → β = !α := by decide
  obtain ⟨c, hc⟩ := exists_isCut h.isTree (show s(φ x, u) ∈ T.edgeSet from hu)
  have hcne := hc.ne_self hu
  obtain ⟨y, hy⟩ := h.row_side hu.symm c (by rwa [Sym2.eq_swap])
  have hyx : y ≠ x := by
    rintro rfl
    exact hcne hy
  have hex : ∃ z, z ≠ x ∧ c (φ z) = c (φ x) := by
    by_contra hcon
    push Not at hcon
    refine hne (h.split_inj hu hp c c' hc hc' ?_)
    refine split_eq_of_single (x := x) (f := c ∘ φ) (g := c' ∘ φ) (fun z => ?_) hz
    refine ⟨fun hzx => ?_, fun hzx => by rw [hzx]⟩
    by_contra hzne
    exact hcon z hzne hzx
  obtain ⟨z, hzx, hzc⟩ := hex
  have ht : c' (φ x) = c' u := hc'.eq_of_ne hu hne
  exact IsCut.not_fourth hconn hc hc' hu hp hne (a := c (φ x)) (b := c' (φ x)) (x := φ x) (y := φ z) (z := u) (w := φ y)
    ⟨rfl, rfl⟩ ⟨hzc, nb (Ne.symm (mt (hz z).1 hzx))⟩ ⟨nb hcne, ht.symm⟩
    ⟨by rw [hy, nb hcne], nb (Ne.symm (mt (hz y).1 hyx))⟩

theorem degree_le_one [Finite W] (x : X) : (T.neighborSet (φ x)).ncard ≤ 1 := by
  by_contra hd
  obtain ⟨u, u', hu, hu', hne⟩ := (Set.one_lt_ncard_iff (Set.toFinite _)).1 (not_le.1 hd)
  have hu₁ : T.Adj (φ x) u := hu
  have hu₂ : T.Adj (φ x) u' := hu'
  obtain ⟨c, hc⟩ := exists_isCut h.isTree (show s(φ x, u) ∈ T.edgeSet from hu₁)
  obtain ⟨y, hy⟩ := h.row_side hu₁.symm c (by rwa [Sym2.eq_swap])
  have hyx : x ≠ y := by
    rintro rfl
    exact hc.ne_self hu₁ hy
  obtain ⟨p, hp, c', hc', hz⟩ := h.single x y hyx
  by_cases hpu : s(φ x, u) = p
  · refine h.degree_aux hu₂ hp hc' hz fun heq => hne ?_
    rcases Sym2.eq_iff.1 (hpu.trans heq.symm) with ⟨-, h'⟩ | ⟨h₁, -⟩
    · exact h'
    · exact absurd h₁ (T.ne_of_adj hu₂)
  · exact h.degree_aux hu₁ hp hc' hz hpu

theorem mem_range_of_degree [Finite W] [Nonempty X] {v : W} (hd : (T.neighborSet v).ncard ≤ 1) : v ∈ Set.range φ := by
  obtain ⟨x₀⟩ := ‹Nonempty X›
  by_cases hv : v = φ x₀
  · exact ⟨x₀, hv.symm⟩
  obtain ⟨w, hw, -⟩ := exists_adj_separating h.isTree hv
  have huniq : ∀ c, T.Adj v c → c = w := fun c hc =>
    (Set.ncard_le_one_iff (Set.toFinite _)).1 hd hc hw
  obtain ⟨c, hc⟩ := exists_isCut h.isTree (show s(v, w) ∈ T.edgeSet from hw)
  obtain ⟨x, hx⟩ := h.row_side hw c hc
  have hsame : SameSide T s(v, w) v (φ x) := hc.sameSide_of_eq h.isTree.connected.preconnected hw hx.symm
  exact ⟨x, sameSide_pendant huniq hsame⟩

theorem degree_ne_two [Finite W] [Nonempty X] (v : W) : (T.neighborSet v).ncard ≠ 2 := by
  intro hd
  have hconn := h.isTree.connected.preconnected
  have nb : ∀ {α β : Bool}, α ≠ β → β = !α := by decide
  obtain ⟨a, b, hab, hnb⟩ := Set.ncard_eq_two.1 hd
  have ha : T.Adj v a := by
    change a ∈ T.neighborSet v
    rw [hnb]; simp
  have hb : T.Adj v b := by
    change b ∈ T.neighborSet v
    rw [hnb]; simp
  have hnbr : ∀ {u}, T.Adj v u → u = a ∨ u = b := by
    intro u hu
    have : u ∈ T.neighborSet v := hu
    rw [hnb] at this
    simpa using this
  have hne : s(v, a) ≠ s(v, b) := by
    intro heq
    rcases Sym2.eq_iff.1 heq with ⟨-, h'⟩ | ⟨h₁, -⟩
    · exact hab h'
    · exact T.ne_of_adj hb h₁
  obtain ⟨c₁, hc₁⟩ := exists_isCut h.isTree (show s(v, a) ∈ T.edgeSet from ha)
  obtain ⟨c₂, hc₂⟩ := exists_isCut h.isTree (show s(v, b) ∈ T.edgeSet from hb)
  have h₁ : c₁ v ≠ c₁ a := hc₁.ne_self ha
  have h₂ : c₂ v ≠ c₂ b := hc₂.ne_self hb
  have h₃ : c₂ v = c₂ a := hc₂.eq_of_ne ha hne
  have h₄ : c₁ v = c₁ b := hc₁.eq_of_ne hb (Ne.symm hne)
  -- The node `v` is alone in its corner.
  have hZ : ∀ w, w ≠ v → ¬ (c₁ w = c₁ v ∧ c₂ w = c₂ v) := by
    intro w hw hz
    have hall := forall_of_adj_closed hconn (P := fun x => x ≠ v ∧ c₁ x = c₁ v ∧ c₂ x = c₂ v) (w := w) ?_ ⟨hw, hz⟩ v
    · exact hall.1 rfl
    · rintro x y hxy ⟨hx, hx₁, hx₂⟩
      have hyv : y ≠ v := by
        rintro rfl
        rcases hnbr hxy.symm with rfl | rfl
        · exact h₁ hx₁.symm
        · exact h₂ hx₂.symm
      have he₁ : s(x, y) ≠ s(v, a) := by
        intro heq
        rcases Sym2.eq_iff.1 heq with ⟨h', -⟩ | ⟨-, h'⟩
        · exact hx h'
        · exact hyv h'
      have he₂ : s(x, y) ≠ s(v, b) := by
        intro heq
        rcases Sym2.eq_iff.1 heq with ⟨h', -⟩ | ⟨-, h'⟩
        · exact hx h'
        · exact hyv h'
      exact ⟨hyv, (hc₁.eq_of_ne hxy he₁).symm.trans hx₁, (hc₂.eq_of_ne hxy he₂).symm.trans hx₂⟩
  -- The far corner is empty.
  have hZ' : ∀ w, ¬ (c₁ w = !c₁ v ∧ c₂ w = !c₂ v) := fun w =>
    IsCut.not_fourth hconn hc₁ hc₂ ha hb hne (x := v) (y := b) (z := a) ⟨rfl, rfl⟩ ⟨h₄.symm, nb h₂⟩ ⟨nb h₁, h₃.symm⟩
  -- So the rows give the two edges one split.
  have hrow : ∀ z, c₁ (φ z) = c₁ v ↔ c₂ (φ z) = !c₂ v := by
    intro z
    have hzv : φ z ≠ v := by
      intro heq
      have h' := h.degree_le_one z
      rw [heq, hd] at h'
      omega
    have h₅ := hZ _ hzv
    have h₆ := hZ' (φ z)
    cases h₇ : c₁ (φ z) <;> cases h₈ : c₂ (φ z) <;> cases h₉ : c₁ v <;> cases h₁₀ : c₂ v <;> simp_all
  refine hne (h.split_inj ha hb c₁ c₂ hc₁ hc₂ fun x y => ?_)
  have hx := hrow x
  have hy := hrow y
  cases h₇ : c₁ (φ x) <;> cases h₈ : c₂ (φ x) <;> cases h₉ : c₁ (φ y) <;> cases h₁₀ : c₂ (φ y) <;>
    cases h₁₁ : c₁ v <;> cases h₁₂ : c₂ v <;> simp_all

theorem not_single_of_not_range [Finite W] [Nonempty X] {a b : W} (hab : T.Adj a b) (ha : a ∉ Set.range φ) {c : W → Bool}
    (hc : IsCut T s(a, b) c) {x : X} (hx : c a = c (φ x)) (hz : ∀ z, c (φ z) = c (φ x) ↔ z = x) : False := by
  have hconn := h.isTree.connected.preconnected
  have nb : ∀ {α β : Bool}, α ≠ β → β = !α := by decide
  have hdeg : ¬ (T.neighborSet a).ncard ≤ 1 := fun hd => ha (h.mem_range_of_degree hd)
  obtain ⟨u, u', hu, hu', hne⟩ := (Set.one_lt_ncard_iff (Set.toFinite _)).1 (not_le.1 hdeg)
  obtain ⟨w, hw, hwb⟩ : ∃ w, T.Adj a w ∧ w ≠ b := by
    by_cases hub : u = b
    · exact ⟨u', hu', fun h' => hne (hub.trans h'.symm)⟩
    · exact ⟨u, hu, hub⟩
  have hne' : s(a, w) ≠ s(a, b) := by
    intro heq
    rcases Sym2.eq_iff.1 heq with ⟨-, h'⟩ | ⟨h₁, -⟩
    · exact hwb h'
    · exact T.ne_of_adj hab h₁
  obtain ⟨c', hc'⟩ := exists_isCut h.isTree (show s(a, w) ∈ T.edgeSet from hw)
  have h₁ : c a ≠ c b := hc.ne_self hab
  have h₂ : c' a ≠ c' w := hc'.ne_self hw
  have h₃ : c a = c w := hc.eq_of_ne hw hne'
  have h₄ : c' a = c' b := hc'.eq_of_ne hab (Ne.symm hne')
  have hfar : ∀ p, ¬ (c p = !c a ∧ c' p = !c' a) := fun p =>
    IsCut.not_fourth hconn hc hc' hab hw (Ne.symm hne') (x := a) (y := w) (z := b) ⟨rfl, rfl⟩ ⟨h₃.symm, nb h₂⟩
      ⟨nb h₁, h₄.symm⟩
  obtain ⟨y, hy⟩ := h.row_side hw.symm c' (by rwa [Sym2.eq_swap])
  have hyx : y = x := by
    refine (hz y).1 ?_
    rw [← hx]
    by_contra hcon
    exact hfar (φ y) ⟨nb (Ne.symm hcon), by rw [hy, nb h₂]⟩
  have hz' : ∀ z, c' (φ z) = c' (φ x) ↔ z = x := by
    intro z
    refine ⟨fun hzx => ?_, fun hzx => by rw [hzx]⟩
    by_contra hzne
    have h₅ : c (φ z) = !c a := by
      rw [hx]
      exact nb (Ne.symm (mt (hz z).1 hzne))
    rw [← hyx, hy, nb h₂] at hzx
    exact hfar (φ z) ⟨h₅, hzx⟩
  have := h.split_inj hab hw c c' hc hc' (split_eq_of_single (f := c ∘ φ) (g := c' ∘ φ) hz hz')
  exact hne' this.symm

theorem labelled [Finite W] [Nonempty X] {a b : W} (hab : T.Adj a b) (ha : a ∉ Set.range φ) (hb : b ∉ Set.range φ) :
    ∃ k, edge k = s(a, b) := by
  rcases h.labelled_or_single hab with hk | ⟨x, hx⟩
  · exact hk
  · exfalso
    obtain ⟨c, hc⟩ := exists_isCut h.isTree (show s(a, b) ∈ T.edgeSet from hab)
    by_cases hca : c a = c (φ x)
    · exact h.not_single_of_not_range hab ha hc hca (hx c hc)
    · have hne := hc.ne_self hab
      have hcb : c b = c (φ x) := by
        cases h₁ : c a <;> cases h₂ : c b <;> cases h₃ : c (φ x) <;> simp_all
      exact h.not_single_of_not_range hab.symm hb (by rwa [Sym2.eq_swap]) hcb (hx c hc)

end KeptSplits

section Contract

variable (T : SimpleGraph W) (K : Set (Sym2 W))

/-- The relation of the two ends of an edge to contract. -/
def ContractRel (u v : W) : Prop := T.Adj u v ∧ s(u, v) ∉ K

/-- The tree `T` with the edges not in `K` contracted. -/
def contractGraph : SimpleGraph (Quot (ContractRel T K)) :=
  SimpleGraph.fromRel fun x y => ∃ u v, T.Adj u v ∧ s(u, v) ∈ K ∧ Quot.mk _ u = x ∧ Quot.mk _ v = y

variable {T K}

theorem contractGraph_adj_exists {x y : Quot (ContractRel T K)} (h : (contractGraph T K).Adj x y) :
    ∃ u v, T.Adj u v ∧ s(u, v) ∈ K ∧ Quot.mk _ u = x ∧ Quot.mk _ v = y := by
  obtain ⟨-, ⟨u, v, h₁, h₂, h₃, h₄⟩ | ⟨u, v, h₁, h₂, h₃, h₄⟩⟩ := (SimpleGraph.fromRel_adj _ _ _).1 h
  · exact ⟨u, v, h₁, h₂, h₃, h₄⟩
  · exact ⟨v, u, h₁.symm, by rwa [Sym2.eq_swap], h₄, h₃⟩

/-- A cut function of a kept edge passes to the contraction. -/
theorem IsCut.contract {g : Sym2 W} (hg : g ∈ K) (hge : g ∈ T.edgeSet) {s : W → Bool} (hs : IsCut T g s) :
    ∃ s' : Quot (ContractRel T K) → Bool, (∀ u, s' (Quot.mk _ u) = s u) ∧
      IsCut (contractGraph T K) (Sym2.map (Quot.mk _) g) s' := by
  have hL : ∀ u v, ContractRel T K u v → s u = s v := fun u v h => hs.eq_of_ne h.1 fun heq => h.2 (heq ▸ hg)
  refine ⟨Quot.lift s hL, fun _ => rfl, ?_⟩
  intro x y hxy
  obtain ⟨u, v, huv, huvK, rfl, rfl⟩ := contractGraph_adj_exists hxy
  induction g with
  | h g₁ g₂ =>
  have hg' : T.Adj g₁ g₂ := hge
  change s u ≠ s v ↔ s(Quot.mk _ u, Quot.mk _ v) = s(Quot.mk _ g₁, Quot.mk _ g₂)
  constructor
  · intro hne
    rcases Sym2.eq_iff.1 ((hs huv).1 hne) with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rfl
    · exact Sym2.eq_swap
  · intro heq
    have hne := hs.ne_self hg'
    rcases Sym2.eq_iff.1 heq with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
    · have hu : s u = s g₁ := congrArg (Quot.lift s hL) h₁
      have hv : s v = s g₂ := congrArg (Quot.lift s hL) h₂
      rw [hu, hv]
      exact hne
    · have hu : s u = s g₂ := congrArg (Quot.lift s hL) h₁
      have hv : s v = s g₁ := congrArg (Quot.lift s hL) h₂
      rw [hu, hv]
      exact hne.symm

theorem contractGraph_isTree (hT : T.IsTree) (hK : K ⊆ T.edgeSet) : (contractGraph T K).IsTree := by
  have : Nonempty (Quot (ContractRel T K)) := ⟨Quot.mk _ (Classical.choice hT.connected.nonempty)⟩
  have hconn : (contractGraph T K).Connected := by
    refine (SimpleGraph.connected_iff _).2 ⟨?_, this⟩
    intro x y
    induction x using Quot.ind with
    | mk u =>
    induction y using Quot.ind with
    | mk v =>
    refine forall_of_adj_closed hT.connected.preconnected
      (P := fun z => (contractGraph T K).Reachable (Quot.mk _ u) (Quot.mk _ z)) ?_ (SimpleGraph.Reachable.refl _) v
    intro a b hab ha
    by_cases hK' : s(a, b) ∈ K
    · by_cases heq : Quot.mk (ContractRel T K) a = Quot.mk _ b
      · rwa [← heq]
      · have hadj : (contractGraph T K).Adj (Quot.mk _ a) (Quot.mk _ b) :=
          (SimpleGraph.fromRel_adj _ _ _).2 ⟨heq, Or.inl ⟨a, b, hab, hK', rfl, rfl⟩⟩
        exact ha.trans hadj.reachable
    · have heq : Quot.mk (ContractRel T K) a = Quot.mk _ b := Quot.sound ⟨hab, hK'⟩
      rwa [← heq]
  refine ⟨hconn, SimpleGraph.isAcyclic_iff_forall_adj_isBridge.2 ?_⟩
  intro x y hxy
  obtain ⟨u, v, huv, huvK, rfl, rfl⟩ := contractGraph_adj_exists hxy
  rw [SimpleGraph.isBridge_iff]
  intro hreach
  obtain ⟨s, hs⟩ := exists_isCut hT (hK huvK)
  obtain ⟨s', hs₁, hs₂⟩ := hs.contract huvK (hK huvK)
  have h₁ := hs₂.eq_of_sameSide hreach
  rw [hs₁, hs₁] at h₁
  exact hs.ne_self huv h₁

end Contract

/-- A perfect phylogeny can be taken to have all its internal edges labelled and no node of degree two: the tree `T̄` of lines
264, 271 and 289. The Perfect Phylogeny Theorem doesn't provide this, and the paper takes it for granted. -/
theorem IsPerfectPhylogeny.exists_normal {T : SimpleGraph W} {φ : X → W} {A : X → κ → Bool} {edge : κ → Sym2 W}
    [Finite W] [Nonempty X] (h : IsPerfectPhylogeny T φ A edge) :
    ∃ (W' : Type u) (_ : Finite W') (T' : SimpleGraph W') (φ' : X → W') (edge' : κ → Sym2 W'),
      IsPerfectPhylogeny T' φ' A edge' ∧
      (∀ u v, T'.Adj u v → u ∉ Set.range φ' → v ∉ Set.range φ' → ∃ k, edge' k = s(u, v)) ∧
      ∀ v, (T'.neighborSet v).ncard ≠ 2 := by
  have hT := h.isTree
  have hconnT := hT.connected.preconnected
  have hφ : ∀ v, (T.neighborSet v).ncard ≤ 1 → v ∈ Set.range φ := fun v => (h.mem_range_iff v).2
  let sp : Sym2 W → X → X → Prop := fun g x y => SameSide T g (φ x) (φ y)
  let Good : Set (Sym2 W) := {g | g ∈ T.edgeSet ∧ ((∃ k, sp g = sp (edge k)) ∨ ∃ x, ∀ y z, sp g y z ↔ (y = x ↔ z = x))}
  obtain ⟨K, hKG, hK⟩ := Set.exists_subset_bijOn Good sp
  have hKe : K ⊆ T.edgeSet := fun g hg => (hKG hg).1
  have hK3 : ∀ g ∈ Good, ∃ g' ∈ K, sp g' = sp g := fun g hg => hK.surjOn ⟨g, hg, rfl⟩
  have hrep : ∀ k, ∃ g ∈ K, sp g = sp (edge k) := fun k => hK3 _ ⟨h.edge_mem k, Or.inl ⟨k, rfl⟩⟩
  choose rep hrepK hrepsp using hrep
  let π : W → Quot (ContractRel T K) := Quot.mk _
  have hT' := contractGraph_isTree hT hKe
  have hconn' := hT'.connected.preconnected
  -- The sides of a kept edge are the same before and after.
  have hmem : ∀ g ∈ K, Sym2.map π g ∈ (contractGraph T K).edgeSet := by
    intro g hg
    obtain ⟨s, hs⟩ := exists_isCut hT (hKe hg)
    obtain ⟨s', -, hs'⟩ := hs.contract hg (hKe hg)
    have hge := hKe hg
    obtain ⟨s'', hs''₁, hs''⟩ := hs.contract hg hge
    induction g with
    | h a b =>
    have hab : T.Adj a b := hge
    have hne : π a ≠ π b := by
      intro heq
      apply hs.ne_self hab
      rw [← hs''₁ a, ← hs''₁ b]
      exact congrArg s'' heq
    change (contractGraph T K).Adj (π a) (π b)
    exact (SimpleGraph.fromRel_adj _ _ _).2 ⟨hne, Or.inl ⟨a, b, hab, hg, rfl, rfl⟩⟩
  have hside : ∀ g ∈ K, ∀ s, IsCut T g s → ∀ c, IsCut (contractGraph T K) (Sym2.map π g) c →
      ∀ u v, c (π u) = c (π v) ↔ s u = s v := by
    intro g hg s hs c hc u v
    obtain ⟨s', hs₁, hs₂⟩ := hs.contract hg (hKe hg)
    rw [← IsCut.sameSide_iff hconn' (hmem g hg) hc, IsCut.sameSide_iff hconn' (hmem g hg) hs₂, hs₁, hs₁]
  have hsp : ∀ g ∈ K, ∀ c, IsCut (contractGraph T K) (Sym2.map π g) c → ∀ x y, c (π (φ x)) = c (π (φ y)) ↔ sp g x y := by
    intro g hg c hc x y
    obtain ⟨s, hs⟩ := exists_isCut hT (hKe hg)
    rw [hside g hg s hs c hc]
    exact (IsCut.sameSide_iff hconnT (hKe hg) hs).symm
  have hadj : ∀ {a b}, (contractGraph T K).Adj a b → ∃ u v, T.Adj u v ∧ s(u, v) ∈ K ∧ π u = a ∧ π v = b :=
    fun h' => contractGraph_adj_exists h'
  have hkept : KeptSplits (contractGraph T K) (π ∘ φ) (fun k => Sym2.map π (rep k)) := by
    refine ⟨hT', ?_, ?_, ?_, ?_⟩
    · intro a b hab c hc
      obtain ⟨u, v, huv, huvK, rfl, rfl⟩ := hadj hab
      obtain ⟨s, hs⟩ := exists_isCut hT (hKe huvK)
      obtain ⟨x, hx⟩ := exists_row_side hT hφ huv hs
      exact ⟨x, (hside _ huvK s hs c hc _ _).2 hx⟩
    · intro e f he hf c c' hc hc' hsplit
      induction e with
      | h e₁ e₂ =>
      induction f with
      | h f₁ f₂ =>
      obtain ⟨u, v, huv, huvK, rfl, rfl⟩ := hadj he
      obtain ⟨u', v', huv', huvK', rfl, rfl⟩ := hadj hf
      have heq : s(u, v) = s(u', v') := hK.injOn huvK huvK' <| by
        funext x y
        exact propext (((hsp _ huvK c hc x y).symm.trans (hsplit x y)).trans (hsp _ huvK' c' hc' x y))
      change Sym2.map π s(u, v) = Sym2.map π s(u', v')
      rw [heq]
    · intro x y hxy
      have hne : φ x ≠ φ y := fun h' => hxy (h.label_injective h')
      obtain ⟨w, hw, -⟩ := exists_adj_separating hT hne
      have huniq : ∀ c, T.Adj (φ x) c → c = w := fun c hc =>
        (Set.ncard_le_one_iff (Set.toFinite _)).1 ((h.mem_range_iff _).1 ⟨x, rfl⟩) hc hw
      obtain ⟨s, hs⟩ := exists_isCut hT (show s(φ x, w) ∈ T.edgeSet from hw)
      have hs₁ : ∀ z, s (φ z) = s (φ x) ↔ z = x := by
        intro z
        refine ⟨fun hz => ?_, fun hz => by rw [hz]⟩
        exact h.label_injective (sameSide_pendant huniq (hs.sameSide_of_eq hconnT hw hz.symm))
      have hgood : s(φ x, w) ∈ Good := by
        refine ⟨hw, Or.inr ⟨x, fun y z => ?_⟩⟩
        change SameSide T s(φ x, w) (φ y) (φ z) ↔ _
        rw [hs.sameSide_iff hconnT hw]
        exact split_eq_of_single (f := s ∘ φ) (g := fun t => decide (t = x)) hs₁ (by simp) y z |>.trans (by
          by_cases h₁ : y = x <;> by_cases h₂ : z = x <;> simp [h₁, h₂])
      obtain ⟨g, hg, hgsp⟩ := hK3 _ hgood
      obtain ⟨c', hc'₁, hc'⟩ := (Classical.choose_spec (exists_isCut hT (hKe hg))).contract hg (hKe hg)
      refine ⟨_, hmem g hg, c', hc', fun z => ?_⟩
      change c' (π (φ z)) = c' (π (φ x)) ↔ z = x
      rw [hsp g hg c' hc' z x, hgsp]
      change SameSide T s(φ x, w) (φ z) (φ x) ↔ z = x
      rw [hs.sameSide_iff hconnT hw]
      exact hs₁ z
    · intro a b hab
      obtain ⟨u, v, huv, huvK, rfl, rfl⟩ := hadj hab
      rcases (hKG huvK).2 with ⟨k, hk⟩ | ⟨x, hx⟩
      · left
        refine ⟨k, ?_⟩
        have : rep k = s(u, v) := hK.injOn (hrepK k) huvK ((hrepsp k).trans hk.symm)
        change Sym2.map π (rep k) = Sym2.map π s(u, v)
        rw [this]
      · right
        refine ⟨x, fun c hc z => ?_⟩
        change c (π (φ z)) = c (π (φ x)) ↔ z = x
        rw [hsp _ huvK c hc z x, hx]
        simp
  have : Finite (Quot (ContractRel T K)) := Finite.of_surjective _ Quot.mk_surjective
  refine ⟨Quot (ContractRel T K), this, contractGraph T K, π ∘ φ, fun k => Sym2.map π (rep k), ⟨hT', hkept.injective,
    fun v => ⟨?_, hkept.mem_range_of_degree⟩, fun k => hmem _ (hrepK k), fun k x y => ?_⟩,
    fun u v huv hu hv => hkept.labelled huv hu hv, hkept.degree_ne_two⟩
  · rintro ⟨x, rfl⟩
    exact hkept.degree_le_one x
  · obtain ⟨c, hc⟩ := exists_isCut hT' (hmem _ (hrepK k))
    change A x k = A y k ↔ SameSide _ _ (π (φ x)) (π (φ y))
    rw [IsCut.sameSide_iff hconn' (hmem _ (hrepK k)) hc, hsp _ (hrepK k) c hc, hrepsp, h.split]

/-- A perfect phylogeny, with its two properties of `T̄`, on any finite type transports to some `Fin n`. -/
theorem IsPerfectPhylogeny.exists_fin {T : SimpleGraph W} {φ : X → W} {A : X → κ → Bool} {edge : κ → Sym2 W} [Finite W]
    (h : IsPerfectPhylogeny T φ A edge)
    (h₁ : ∀ u v, T.Adj u v → u ∉ Set.range φ → v ∉ Set.range φ → ∃ k, edge k = s(u, v))
    (h₂ : ∀ v, (T.neighborSet v).ncard ≠ 2) :
    ∃ (n : ℕ) (T' : SimpleGraph (Fin n)) (φ' : X → Fin n) (edge' : κ → Sym2 (Fin n)), IsPerfectPhylogeny T' φ' A edge' ∧
      (∀ u v, T'.Adj u v → u ∉ Set.range φ' → v ∉ Set.range φ' → ∃ k, edge' k = s(u, v)) ∧
      ∀ v, (T'.neighborSet v).ncard ≠ 2 := by
  obtain ⟨n, ⟨f⟩⟩ := Finite.exists_equiv_fin W
  let T' : SimpleGraph (Fin n) := T.comap f.symm
  have hiso : T' ≃g T := SimpleGraph.Iso.comap f.symm T
  have hT' : T'.IsTree := hiso.isTree_iff.2 h.isTree
  have hconn := hT'.connected.preconnected
  have hnbr : ∀ v, T'.neighborSet (f v) = f '' T.neighborSet v := by
    intro v
    ext u
    constructor
    · intro hu
      refine ⟨f.symm u, ?_, by simp⟩
      have : T.Adj (f.symm (f v)) (f.symm u) := hu
      simpa using this
    · rintro ⟨w, hw, rfl⟩
      have : T.Adj v w := hw
      change T.Adj (f.symm (f v)) (f.symm (f w))
      simpa using this
  have hdeg : ∀ v, (T'.neighborSet (f v)).ncard = (T.neighborSet v).ncard := fun v => by
    rw [hnbr, Set.ncard_image_of_injective _ f.injective]
  have hmap : ∀ k, Sym2.map f (edge k) ∈ T'.edgeSet := by
    intro k
    have := h.edge_mem k
    induction hk : edge k with
    | h a b =>
      rw [hk] at this
      change T.Adj (f.symm (f a)) (f.symm (f b))
      simpa using this
  refine ⟨n, T', f ∘ φ, fun k => Sym2.map f (edge k), ⟨hT', f.injective.comp h.label_injective, fun v => ?_, hmap, fun k x y => ?_⟩,
    fun u v huv hu hv => ?_, fun v => ?_⟩
  · have hv : v = f (f.symm v) := by simp
    rw [hv, hdeg, ← h.mem_range_iff]
    constructor
    · rintro ⟨x, hx⟩
      refine ⟨x, ?_⟩
      apply f.injective
      simpa using hx
    · rintro ⟨x, hx⟩
      exact ⟨x, by simp [hx]⟩
  · obtain ⟨c, hc⟩ := exists_isCut h.isTree (h.edge_mem k)
    have hc' : IsCut T' (Sym2.map f (edge k)) (c ∘ f.symm) := by
      intro u v huv
      have huv' : T.Adj (f.symm u) (f.symm v) := huv
      have := hc huv'
      simp only [Function.comp_apply]
      rw [this]
      constructor
      · intro heq
        rw [← heq]
        simp
      · intro heq
        have : Sym2.map f.symm s(u, v) = Sym2.map f.symm (Sym2.map f (edge k)) := by rw [heq]
        simpa [Sym2.map_map, Function.comp_def] using this
    rw [h.split, IsCut.sameSide_iff h.isTree.connected.preconnected (h.edge_mem k) hc,
      IsCut.sameSide_iff hconn (hmap k) hc']
    simp
  · have hu' : f.symm u ∉ Set.range φ := fun ⟨x, hx⟩ => hu ⟨x, by simp [hx]⟩
    have hv' : f.symm v ∉ Set.range φ := fun ⟨x, hx⟩ => hv ⟨x, by simp [hx]⟩
    obtain ⟨k, hk⟩ := h₁ _ _ huv hu' hv'
    refine ⟨k, ?_⟩
    change Sym2.map f (edge k) = s(u, v)
    rw [hk]
    simp
  · have hv : v = f (f.symm v) := by simp
    rw [hv, hdeg]
    exact h₂ _

end Gusfield2007
