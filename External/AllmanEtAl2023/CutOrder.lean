module

public import Basic.Phylogenetics.NetworkCuts
public import Basic.Phylogenetics.TreeMetric

/-!
# Cut edges of induced subgraphs, by the arcs that are their top

Working language for the source's Theorems 2 and 3, in a fixed network. An arc is a *cut on the taxa
`Y`* (`IsCutOn`) when it dominates every taxon of `Y` below it; the cut-edge splits of the subgraph
induced on `Y` are exactly the sets of taxa of `Y` below such arcs (`hasCutSplitOn_iff_separates`).
Arcs dominating a common taxon are ordered (`order_of_isBelow_of_dominates`), which gives the
uniqueness of a cut-edge split on four taxa (`inducedCutSplit_unique`).
-/

@[expose] public noncomputable section

open Phylogenetics Phylogenetics.RootedNetwork Finset
open scoped Classical

namespace External.AllmanEtAl2023

variable {V E X : Type*} {N : RootedNetwork V E X}

theorem reaches_split (e : E) {u v : V} (h : N.graph.Reaches u v) :
    N.AvoidingReach e u v ∨
      (N.graph.Reaches u (N.graph.source e) ∧ N.graph.Reaches (N.graph.target e) v) := by
  induction h with
  | refl => exact Or.inl .refl
  | tail hab hbc ih =>
    obtain ⟨g, hg1, hg2⟩ := hbc
    by_cases hge : g = e
    · subst hge
      exact Or.inr ⟨hg1 ▸ hab, hg2 ▸ .refl⟩
    · rcases ih with ih | ⟨h1, h2⟩
      · exact Or.inl (ih.tail ⟨g, hge, hg1, hg2⟩)
      · exact Or.inr ⟨h1, h2.tail ⟨g, hg1, hg2⟩⟩

theorem avoiding_split (e f : E) {u v : V} (h : N.AvoidingReach e u v) :
    N.AvoidingReach f u v ∨
      (N.AvoidingReach e u (N.graph.source f) ∧ N.AvoidingReach e (N.graph.target f) v) := by
  induction h with
  | refl => exact Or.inl .refl
  | tail hab hbc ih =>
    obtain ⟨g, hne, hg1, hg2⟩ := hbc
    by_cases hgf : g = f
    · subst hgf
      exact Or.inr ⟨hg1 ▸ hab, hg2 ▸ .refl⟩
    · rcases ih with ih | ⟨h1, h2⟩
      · exact Or.inl (ih.tail ⟨g, hgf, hg1, hg2⟩)
      · exact Or.inr ⟨h1, h2.tail ⟨g, hne, hg1, hg2⟩⟩

theorem avoiding_step {e f : E} (h : f ≠ e) :
    N.AvoidingReach e (N.graph.source f) (N.graph.target f) :=
  Relation.ReflTransGen.single ⟨f, h, rfl, rfl⟩

theorem dominates_isBelow (hN : N.IsPhylogenetic) {e : E} {x : X} (h : N.Dominates e x) :
    N.IsBelow e x := by
  rcases reaches_split e (hN.root_reaches (N.leaf x)) with h' | ⟨-, h'⟩
  · exact absurd h' h
  · exact h'

/-- An arc dominating a taxon is comparable with any arc above that taxon. -/
theorem order_of_isBelow_of_dominates (hN : N.IsPhylogenetic) {e f : E} {x : X}
    (hb : N.IsBelow e x) (hd : N.Dominates f x) (hne : e ≠ f) :
    N.graph.Reaches (N.graph.target e) (N.graph.source f) ∨
      N.graph.Reaches (N.graph.target f) (N.graph.source e) := by
  rcases reaches_split f (hN.root_reaches (N.graph.source e)) with h1 | ⟨-, h1⟩
  · rcases reaches_split f hb with h2 | ⟨h2, -⟩
    · exact absurd ((h1.trans (avoiding_step hne)).trans h2) hd
    · exact Or.inl h2
  · exact Or.inr h1

theorem isBelow_of_above {e f : E} {x : X} (h : N.graph.Reaches (N.graph.target f) (N.graph.source e))
    (hb : N.IsBelow e x) : N.IsBelow f x :=
  (h.tail ⟨e, rfl, rfl⟩).trans hb

theorem above_antisymm (hN : N.IsPhylogenetic) {e f : E}
    (h : N.graph.Reaches (N.graph.target e) (N.graph.source f))
    (h' : N.graph.Reaches (N.graph.target f) (N.graph.source e)) : False := by
  have h1 : N.graph.Reaches (N.graph.target e) (N.graph.source e) :=
    (h.tail ⟨f, rfl, rfl⟩).trans h'
  have h2 : Relation.TransGen N.graph.Adj (N.graph.target e) (N.graph.target e) :=
    Relation.TransGen.tail' h1 ⟨e, rfl, rfl⟩
  exact hN.acyclic _ h2

/-- The arc `e` is a cut on the taxa `Y`: it dominates every taxon of `Y` below it. -/
def IsCutOn (N : RootedNetwork V E X) (Y : Finset X) (e : E) : Prop :=
  ∀ x ∈ Y, N.IsBelow e x → N.Dominates e x

/-- Two cuts on `Y` are not crossing. -/
theorem not_crossing (hN : N.IsPhylogenetic) {Y : Finset X} {e f : E} (hf : IsCutOn N Y f) {x y z : X} (hx : x ∈ Y) (h1 : N.IsBelow e x) (h2 : N.IsBelow f x)
    (h3 : N.IsBelow e y) (h4 : ¬ N.IsBelow f y) (h5 : ¬ N.IsBelow e z) (h6 : N.IsBelow f z) :
    False := by
  have hne : e ≠ f := fun h => h4 (h ▸ h3)
  rcases order_of_isBelow_of_dominates hN h1 (hf x hx h2) hne with h | h
  · exact h5 (isBelow_of_above h h6)
  · exact h4 (isBelow_of_above h h3)

variable [DecidableEq X]

omit [DecidableEq X] in
/-- A cut-edge split on `Y` is given by a cut on `Y`. -/
theorem exists_isCutOn_of_hasCutSplitOn (hN : N.IsPhylogenetic) {Y : Finset X} {A : Set X}
    (h : N.HasCutSplitOn (Y : Set X) A) :
    ∃ e, IsCutOn N Y e ∧ (∃ x ∈ Y, N.IsBelow e x) ∧
      ((∀ x ∈ Y, N.IsBelow e x ↔ x ∈ A) ∨ (∀ x ∈ Y, N.IsBelow e x ↔ x ∉ A)) := by
  obtain ⟨e, h⟩ := (hasCutSplitOn_iff_separates hN _ _).mp h
  refine ⟨e, ?_⟩
  rcases h with ⟨⟨x, hxY, hxA⟩, h1, h2⟩ | ⟨⟨x, hxY, hxA⟩, h1, h2⟩
  · have hiff : ∀ x ∈ Y, N.IsBelow e x ↔ x ∈ A := fun x hx =>
      ⟨fun hb => by
        by_contra hxA
        exact h2 x ⟨hx, hxA⟩ hb, fun hxA => dominates_isBelow hN (h1 x ⟨hx, hxA⟩)⟩
    exact ⟨fun x hx hb => h1 x ⟨hx, (hiff x hx).mp hb⟩, ⟨x, hxY, (hiff x hxY).mpr hxA⟩, Or.inl hiff⟩
  · have hiff : ∀ x ∈ Y, N.IsBelow e x ↔ x ∉ A := fun x hx =>
      ⟨fun hb hxA => h2 x ⟨hx, hxA⟩ hb, fun hxA => dominates_isBelow hN (h1 x ⟨hx, hxA⟩)⟩
    exact ⟨fun x hx hb => h1 x ⟨hx, (hiff x hx).mp hb⟩, ⟨x, hxY, (hiff x hxY).mpr hxA⟩, Or.inr hiff⟩

omit [DecidableEq X] in
/-- A cut on `Y` with a taxon of `Y` below it gives a cut-edge split on `Y`. -/
theorem hasCutSplitOn_of_isCutOn (hN : N.IsPhylogenetic) {Y : Finset X} {e : E}
    (he : IsCutOn N Y e) {A : Set X} (hA : ∀ x ∈ Y, N.IsBelow e x ↔ x ∈ A) {x : X} (hx : x ∈ Y)
    (hb : N.IsBelow e x) : N.HasCutSplitOn (Y : Set X) A := by
  refine (hasCutSplitOn_iff_separates hN _ _).mpr ⟨e, Or.inl ⟨⟨x, hx, (hA x hx).mp hb⟩, ?_, ?_⟩⟩
  · rintro y ⟨hy, hyA⟩
    exact he y hy ((hA y hy).mpr hyA)
  · rintro y ⟨hy, hyA⟩ hb'
    exact hyA ((hA y hy).mp hb')

variable [Fintype X]

omit [Fintype X] in
/-- A 4-taxon set has at most one quartet tree that is a cut-edge split of its induced network. -/
theorem inducedCutSplit_unique (hN : N.IsPhylogenetic) {s s' : QuartetTree X}
    (hs : InducedCutSplit N s) (hs' : InducedCutSplit N s') (h : s.taxa = s'.taxa) : s = s' := by
  obtain ⟨B, hB, hcB⟩ := hs
  obtain ⟨B', hB', hcB'⟩ := hs'
  rw [← h] at hcB'
  obtain ⟨e, he, -, hor⟩ := exists_isCutOn_of_hasCutSplitOn hN hcB
  obtain ⟨f, hf, -, hor'⟩ := exists_isCutOn_of_hasCutSplitOn hN hcB'
  -- the taxa below `e` and `f` form cherries of `s` and `s'`
  have hS : ∃ C ∈ s.val, ∀ x ∈ s.taxa, N.IsBelow e x ↔ x ∈ C := by
    rcases hor with hor | hor
    · exact ⟨B, hB, fun x hx => by simpa using hor x hx⟩
    · refine ⟨s.taxa \ B, TreeMetric.sdiff_mem_of_mem hB, fun x hx => ?_⟩
      simpa [hx] using hor x hx
  have hS' : ∃ C ∈ s'.val, ∀ x ∈ s.taxa, N.IsBelow f x ↔ x ∈ C := by
    rcases hor' with hor' | hor'
    · exact ⟨B', hB', fun x hx => by simpa using hor' x hx⟩
    · refine ⟨s'.taxa \ B', TreeMetric.sdiff_mem_of_mem hB', fun x hx => ?_⟩
      rw [← h]
      simpa [hx] using hor' x hx
  obtain ⟨C, hC, hCb⟩ := hS
  obtain ⟨C', hC', hCb'⟩ := hS'
  have hCs : C ⊆ s.taxa := TreeMetric.subset_taxa_of_mem hC
  have hCs' : C' ⊆ s.taxa := h ▸ TreeMetric.subset_taxa_of_mem hC'
  have hc2 : C.card = 2 := s.2.2.1 C hC
  have hc2' : C'.card = 2 := s'.2.2.1 C' hC'
  have ht4 : s.taxa.card = 4 := QuartetTree.card_taxa s
  by_cases hEq : C' = C
  · exact TreeMetric.eq_of_mem_of_taxa_eq hC (hEq ▸ hC') h
  by_cases hEq' : C' = s.taxa \ C
  · exact TreeMetric.eq_of_mem_of_taxa_eq (TreeMetric.sdiff_mem_of_mem hC) (hEq' ▸ hC') h
  exfalso
  have hx : ∃ x ∈ C, x ∈ C' := by
    by_contra hno
    push Not at hno
    refine hEq' (Finset.eq_of_subset_of_card_le (fun x hx => ?_) ?_)
    · exact Finset.mem_sdiff.mpr ⟨hCs' hx, fun hxC => hno x hxC hx⟩
    · rw [Finset.card_sdiff_of_subset hCs]; omega
  have hy : ∃ y ∈ C, y ∉ C' := by
    by_contra hno
    push Not at hno
    exact hEq (Finset.eq_of_subset_of_card_le hno (by omega)).symm
  have hz : ∃ z ∈ C', z ∉ C := by
    by_contra hno
    push Not at hno
    exact hEq (Finset.eq_of_subset_of_card_le hno (by omega))
  obtain ⟨x, hxC, hxC'⟩ := hx
  obtain ⟨y, hyC, hyC'⟩ := hy
  obtain ⟨z, hzC', hzC⟩ := hz
  exact not_crossing hN hf (hCs hxC) ((hCb x (hCs hxC)).mpr hxC) ((hCb' x (hCs hxC)).mpr hxC')
    ((hCb y (hCs hyC)).mpr hyC) (fun hb => hyC' ((hCb' y (hCs hyC)).mp hb))
    (fun hb => hzC ((hCb z (hCs' hzC')).mp hb)) ((hCb' z (hCs' hzC')).mpr hzC')

omit [Fintype X] in
/-- A cut side of the network, restricted to four taxa with two on each side, is a cut-edge split of
the induced network. -/
theorem inducedCutSplit_of_hasCutSplit (hN : N.IsPhylogenetic) {A : Finset X}
    (hA : N.HasCutSplit (A : Set X)) {a b c d : X} (h : ({a, b, c, d} : Finset X).card = 4)
    (ha : a ∈ A) (hb : b ∈ A) (hc : c ∉ A) (hd : d ∉ A) :
    InducedCutSplit N (quartetTree a b c d h) := by
  refine ⟨{a, b}, by simp, ?_⟩
  rw [TreeMetric.taxa_quartetTree]
  have h1 : N.HasCutSplitOn ((({a, b, c, d} : Finset X) : Set X)) (A : Set X) :=
    hA.hasCutSplitOn hN ⟨a, by simp, by simpa using ha⟩ ⟨c, by simp, by simpa using hc⟩
  refine (hasCutSplitOn_congr ?_).mp h1
  ext x
  simp only [Set.mem_inter_iff, Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨hx, hxA⟩
    refine ⟨hx, ?_⟩
    rcases hx with rfl | rfl | rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr rfl
    · exact absurd hxA hc
    · exact absurd hxA hd
  · rintro ⟨hx, rfl | rfl⟩
    · exact ⟨hx, ha⟩
    · exact ⟨hx, hb⟩

end External.AllmanEtAl2023
