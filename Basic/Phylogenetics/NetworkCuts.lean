module

public import Basic.Phylogenetics.AncestralRestriction

/-!
# Cut edges of rooted networks through domination

The working description of cut-edge splits used by every graph proof of this project. An arc `e`
*dominates* a taxon when every directed path from the root to the taxon uses `e`. On a rooted network
a cut edge separates exactly the taxa it dominates from the taxa not below it, so a cut-edge split
is a statement about each taxon separately:

* `HasCutSplitOn Y A` holds exactly when an arc dominates one side of the split on `Y` while the
  other side is not below it (`hasCutSplitOn_iff_separates`);
* consequently a cut edge of the subgraph induced on `Y` remains one on any `Z ⊆ Y`
  (`HasCutSplitOn.mono`), which is the forward direction of Huber et al. 2025, Theorem 5.1.

API: `AvoidingReach`, `Dominates`, `IsBelow`, `Separates`, `hasCutSplitOn_iff_separates`,
`hasCutSplit_iff_hasCutSplitOn_univ`, `HasCutSplitOn.mono`, `Separates.mono`.
-/

@[expose] public section

namespace Phylogenetics.RootedNetwork

variable {V E X : Type*} (N : RootedNetwork V E X)

/-- `v` is reachable from `u` by a directed path not using the arc `e`. -/
def AvoidingReach (e : E) : V → V → Prop :=
  Relation.ReflTransGen fun a b => ∃ f, f ≠ e ∧ N.graph.source f = a ∧ N.graph.target f = b

/-- Every directed path from the root to the taxon `x` uses the arc `e`. -/
def Dominates (e : E) (x : X) : Prop := ¬ N.AvoidingReach e N.root (N.leaf x)

/-- The taxon `x` is below the arc `e`. -/
def IsBelow (e : E) (x : X) : Prop := N.graph.Reaches (N.graph.target e) (N.leaf x)

/-- The arc `e` dominates all taxa of `P`, and no taxon of `Q` is below it. -/
def Separates (e : E) (P Q : Set X) : Prop :=
  (∀ x ∈ P, N.Dominates e x) ∧ ∀ x ∈ Q, ¬ N.IsBelow e x

variable {N}

/-- **The domination characterization of cut-edge splits.** `A ∩ Y | Y \ A` is a cut-edge split of
the network induced on `Y` exactly when an arc dominates one nonempty side and has no taxon of the
other side below it. -/
theorem hasCutSplitOn_iff_separates (hN : N.IsPhylogenetic) (Y A : Set X) :
    N.HasCutSplitOn Y A ↔ ∃ e, ((Y ∩ A).Nonempty ∧ N.Separates e (Y ∩ A) (Y \ A)) ∨
      ((Y \ A).Nonempty ∧ N.Separates e (Y \ A) (Y ∩ A)) := by
  sorry

/-- A cut-edge split of the network is one of the network induced on all the taxa, since every arc
is ancestral to a taxon. -/
theorem hasCutSplit_iff_hasCutSplitOn_univ (hN : N.IsPhylogenetic) (A : Set X) :
    N.HasCutSplit A ↔ N.HasCutSplitOn Set.univ A := by
  sorry

/-- Separation restricts to subsets. -/
theorem Separates.mono {e : E} {P Q P' Q' : Set X} (h : N.Separates e P Q)
    (hP : P' ⊆ P) (hQ : Q' ⊆ Q) : N.Separates e P' Q' := by
  sorry

/-- A cut-edge split of the network induced on `Y` restricts to a cut-edge split of the network
induced on any `Z ⊆ Y` whose two sides are both nonempty. -/
theorem HasCutSplitOn.mono (hN : N.IsPhylogenetic) {Y Z A : Set X} (h : N.HasCutSplitOn Y A)
    (hZ : Z ⊆ Y) (h₁ : (Z ∩ A).Nonempty) (h₂ : (Z \ A).Nonempty) : N.HasCutSplitOn Z A := by
  sorry

/-- A cut side of the network restricts to any taxon set with both sides nonempty. -/
theorem HasCutSplit.hasCutSplitOn (hN : N.IsPhylogenetic) {Z A : Set X} (h : N.HasCutSplit A)
    (h₁ : (Z ∩ A).Nonempty) (h₂ : (Z \ A).Nonempty) : N.HasCutSplitOn Z A := by
  sorry

/-- The split is symmetric. -/
theorem hasCutSplitOn_compl (Y A : Set X) : N.HasCutSplitOn Y Aᶜ ↔ N.HasCutSplitOn Y A := by
  sorry

/-- The split depends only on the side's trace on `Y`. -/
theorem hasCutSplitOn_congr {Y A B : Set X} (h : Y ∩ A = Y ∩ B) :
    N.HasCutSplitOn Y A ↔ N.HasCutSplitOn Y B := by
  sorry

end Phylogenetics.RootedNetwork
