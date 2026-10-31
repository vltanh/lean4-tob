module

public import Basic.Phylogenetics.TreeSplits

/-!
# Rhodes 2020: the quartet metrization of a tree

J. A. Rhodes, *Topological metrizations of trees, and new quartet methods of tree inference*, IEEE/ACM
Trans. Comput. Biol. Bioinform. 17 (2020), 2107–2118.

An edge with blocks `X₁, …, X_m` at one end and `Y₁, …, Y_{m'}` at the other has weight
`∑_{i<j} |Xᵢ||Xⱼ| + ∑_{i<j} |Yᵢ||Yⱼ|`. Theorem 2: the tree metric of these weights is
`d(x, y) = 2 |Q_{x,y}| + 2N - 4`, with `Q_{x,y}` the quartets displayed on the tree of the form `xz|yw`
or `xyzw`. Internal edges have weight at least `2`.
-/

@[expose] public noncomputable section

open Phylogenetics Finset
open scoped Classical

namespace External.Rhodes2020

variable {X : Type*} [Fintype X] [DecidableEq X]

/-- Two taxa on the side `A` lie in the same block of the edge when a split properly inside `A`
contains both; the blocks on that side are the maximal sides of `T` properly inside `A`, and single
taxa of `A` in no such side. The number of pairs in distinct blocks is
`∑_{i<j} |Xᵢ||Xⱼ|`. -/
def sidePairs (T : Finset (Finset X)) (A : Finset X) : ℕ :=
  (univ.filter fun p : Finset X =>
    p.card = 2 ∧ p ⊆ A ∧ ¬ ∃ C ∈ T, C ⊂ A ∧ p ⊆ C).card

/-- The quartet metrization `Q` of the tree `T`: the weight of the edge with side `A`. -/
def quartetWeight (T : Finset (Finset X)) (A : Finset X) : ℝ :=
  (sidePairs T A : ℝ) + (sidePairs T Aᶜ : ℝ)

/-- **Theorem 2.** The tree metric of the quartet metrization of an unrooted tree on `N` taxa is
`2 |Q_{x,y}| + 2N - 4`. -/
theorem theorem2 {T : Finset (Finset X)} (hT : IsUnrootedTree T) (hX : 4 ≤ Fintype.card X)
    {x y : X} (hxy : x ≠ y) :
    treeMetric T (quartetWeight T) x y =
      quartetDistance {q | ∀ s ∈ treesOn q, ¬ Displays T s} {s | Displays T s} x y := by
  sorry

/-- Edges have positive weight; internal edges have weight at least `2`, and for at least four taxa
so do pendant edges. -/
theorem quartetWeight_ge_two {T : Finset (Finset X)} (hT : IsUnrootedTree T)
    (hX : 4 ≤ Fintype.card X) {A : Finset X} (hA : A ∈ T) : 2 ≤ quartetWeight T A := by
  sorry

theorem quartetWeight_compl (T : Finset (Finset X)) (A : Finset X) :
    quartetWeight T Aᶜ = quartetWeight T A := by
  sorry

/-- A tree metric with positive weights determines the tree and its weights (Buneman 1971): so
exact distance-based tree builders exist. -/
theorem exists_isExactBuilder : ∃ M : TreeBuilder X, IsExactBuilder M := by
  sorry

end External.Rhodes2020
