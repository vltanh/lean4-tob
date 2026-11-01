module

public import Gusfield2007.Examples
public import Mathlib.Data.ENat.Lattice
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Data.Finset.BooleanAlgebra

/-!
# Gusfield et al. 2007, Section 5.3.3: time-ordered trees and ordered SPR

For Theorem 11: time-ordered leaf-labelled trees as hierarchies with times on the internal nodes, ordered-SPR operations, `d_oSPR`
and `L(P)`, lines 646 to 654.
-/

@[expose] public noncomputable section

namespace Gusfield2007

variable {X : Type*} [Fintype X] [DecidableEq X]

/-- A time-ordered leaf-labelled tree (line 646): a rooted tree on the leaves `X`, as its clusters, with times on the internal nodes, which strictly increase along
any directed path from the root. Leaves carry no time. -/
structure TimeOrderedTree (X : Type*) [Fintype X] [DecidableEq X] where
  /-- The clusters of the tree. -/
  clusters : Finset (Finset X)
  /-- They form a tree: the same conditions as `Phylogenetics.IsHierarchy` of the library. -/
  isHierarchy : Finset.univ ∈ clusters ∧ (∀ x : X, {x} ∈ clusters) ∧ (∀ A ∈ clusters, A.Nonempty) ∧
    ∀ A ∈ clusters, ∀ B ∈ clusters, A ⊆ B ∨ B ⊆ A ∨ Disjoint A B
  /-- The time of an internal node. Only the values at clusters with at least two leaves matter. -/
  time : Finset X → ℝ
  /-- The times increase away from the root. -/
  time_lt : ∀ A ∈ clusters, ∀ B ∈ clusters, 2 ≤ A.card → A ⊂ B → time B < time A

namespace TimeOrderedTree

/-- The tree `T` is compatible with a column (line 646): some edge has below it all the rows with one state of the column, and the rest are all the rows with the other
state. -/
def CompatibleWith (T : TimeOrderedTree X) (A : X → Bool) : Prop :=
  ∃ C ∈ T.clusters, C ≠ Finset.univ ∧ (C = Finset.univ.filter (A · = true) ∨ C = Finset.univ.filter (A · = false))

/-- The same tree: the same clusters and the same times at internal nodes. -/
def Same (T T' : TimeOrderedTree X) : Prop :=
  T.clusters = T'.clusters ∧ ∀ A ∈ T.clusters, 2 ≤ A.card → T.time A = T'.time A

/-- The clusters of what remains when the subtree on the leaves `A` is pruned. -/
def prunedClusters (T : TimeOrderedTree X) (A : Finset X) : Finset (Finset X) :=
  (T.clusters.filter fun B => ¬ B ⊆ A).image (· \ A)

/-- The time of a cluster of what remains when the subtree on `A` is pruned. A cluster `D ∪ A` whose image `D` is also a cluster is a node of degree two after pruning, which is
suppressed, so `D` keeps its time. -/
def prunedTime (T : TimeOrderedTree X) (A D : Finset X) : ℝ :=
  if D ∈ T.clusters then T.time D else T.time (D ∪ A)

/-- An ordered-SPR operation takes `T` to `T'` (line 646): it prunes the subtree on the leaves `A` and regrafts it, the times of all the nodes in the subtree and of all the nodes left
remaining the same, and the resulting tree being time-ordered, which is in the type of `T'`. The new node has any time, and that it's earlier than the root of the subtree follows from
the time order of `T'`. -/
def IsOrderedSPR (T T' : TimeOrderedTree X) : Prop :=
  ∃ A ∈ T.clusters, A ∈ T'.clusters ∧ A ≠ Finset.univ ∧
    (∀ B ⊆ A, B ∈ T.clusters ↔ B ∈ T'.clusters) ∧
    (∀ B ⊆ A, B ∈ T.clusters → 2 ≤ B.card → T.time B = T'.time B) ∧
    T.prunedClusters A = T'.prunedClusters A ∧
    ∀ D ∈ T.prunedClusters A, 2 ≤ D.card → T.prunedTime A D = T'.prunedTime A D

/-- `T` is taken to `T'` by exactly `k` ordered-SPR operations. -/
def SPRSteps : ℕ → TimeOrderedTree X → TimeOrderedTree X → Prop
  | 0, T, T' => T.Same T'
  | k + 1, T, T' => ∃ T'', T.IsOrderedSPR T'' ∧ SPRSteps k T'' T'

/-- `d_oSPR(T, T')`: the minimum number of ordered-SPR operations needed to transform `T` into `T'` (line 653), infinite when there's none. -/
def doSPR (T T' : TimeOrderedTree X) : ℕ∞ :=
  sInf ((↑) '' {k : ℕ | SPRSteps k T T'})

end TimeOrderedTree

/-- `L(P) = Σ d_oSPR(T_i, T_{i+1})` (line 654). -/
def sprLength : List (TimeOrderedTree X) → ℕ∞
  | a :: b :: l => a.doSPR b + sprLength (b :: l)
  | _ => 0

end Gusfield2007
