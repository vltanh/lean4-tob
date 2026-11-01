module

public import Mathlib.Combinatorics.SimpleGraph.Acyclic
public import Mathlib.Combinatorics.SimpleGraph.DeleteEdges
public import Mathlib.Combinatorics.SimpleGraph.Maps
public import Mathlib.Data.Set.Card

/-!
# The Splits Equivalence Theorem (Semple, Steel 2003, Theorem 3.1.4)

Stated with `sorry`. See the `README.md` of this directory.
-/

@[expose] public section

namespace SempleSteel2003

variable {X W W' : Type*}

/-- An `X`-tree: a tree with a map from `X` to its vertices, where every vertex of degree at most two is labelled. -/
structure IsXTree (T : SimpleGraph W) (φ : X → W) : Prop where
  isTree : T.IsTree
  labelled : ∀ v, (T.neighborSet v).ncard ≤ 2 → v ∈ Set.range φ

/-- The side of the split of the edge `e` containing `x`. -/
def edgeSide (T : SimpleGraph W) (φ : X → W) (e : Sym2 W) (x : X) : Set X :=
  {y | (T.deleteEdges {e}).Reachable (φ x) (φ y)}

/-- The split system `Σ(T)`, as the family of sides of the splits of the edges. -/
def splitSides (T : SimpleGraph W) (φ : X → W) : Set (Set X) :=
  {A | ∃ e ∈ T.edgeSet, ∃ x, A = edgeSide T φ e x}

/-- A collection of `X`-splits, as the family of their sides: both sides are nonempty. -/
def IsSplitSystem (F : Set (Set X)) : Prop :=
  ∀ A ∈ F, A.Nonempty ∧ Aᶜ.Nonempty ∧ Aᶜ ∈ F

/-- The splits are pairwise compatible: for any two, one of the four intersections of their sides is empty. -/
def PairwiseCompatible (F : Set (Set X)) : Prop :=
  ∀ A ∈ F, ∀ B ∈ F, A ∩ B = ∅ ∨ A ∩ Bᶜ = ∅ ∨ Aᶜ ∩ B = ∅ ∨ Aᶜ ∩ Bᶜ = ∅

/-- **The Splits Equivalence Theorem** (`ext:splits_equivalence`), existence (Semple, Steel 2003, Theorem 3.1.4). -/
theorem exists_xTree_iff [Finite X] [Nonempty X] {F : Set (Set X)} (hF : IsSplitSystem F) :
    PairwiseCompatible F ↔ ∃ (n : ℕ) (T : SimpleGraph (Fin n)) (φ : X → Fin n), IsXTree T φ ∧ splitSides T φ = F := by
  sorry

/-- **The Splits Equivalence Theorem**, uniqueness (Semple, Steel 2003, Theorem 3.1.4). -/
theorem xTree_unique [Finite X] [Nonempty X] [Finite W] [Finite W'] {T : SimpleGraph W} {T' : SimpleGraph W'}
    {φ : X → W} {φ' : X → W'} (hT : IsXTree T φ) (hT' : IsXTree T' φ') (h : splitSides T φ = splitSides T' φ') :
    ∃ f : T ≃g T', ∀ x, f (φ x) = φ' x := by
  sorry

end SempleSteel2003
