module

public import Basic.Phylogenetics.Coalescent.Tavare
public import Basic.Phylogenetics.Network
public import Basic.Phylogenetics.TreeSplits

/-!
# Basic properties of the network multispecies coalescent on arbitrary networks

For a phylogenetic network with valid numerical parameters and inheritance correlation `0 ≤ ρ ≤ 1`:
`geneTreeDist` is a probability distribution, supported on binary rooted trees on the taxa, on each of
which it is positive. Hence the quartet concordance factors are positive and sum to one on each set of
four taxa, as TINNiK §"Quartet concordance factors" and TOB-QMC's proof of Lemma 3 use.

API: `geneTreeDist_isDist`, `geneTreeDist_support`, `geneTreeDist_pos`, `nmscCF_pos`, `sum_nmscCF`.
-/

@[expose] public noncomputable section

open Finset
open scoped Classical

namespace Phylogenetics

variable {V E X : Type*} [Fintype V] [Fintype E] [Fintype X] [DecidableEq X]
variable {N : RootedNetwork V E X} {θ : RootedNetwork.MetricData E} {ρ : ℝ}

/-- A rooted binary gene tree on `X`, given by its clusters. -/
def IsBinaryHierarchy (G : Finset (Finset X)) : Prop :=
  IsHierarchy G ∧ ∀ A ∈ G, 2 ≤ A.card → (childClusters G A).card = 2

/-- The network multispecies coalescent gives a probability distribution on gene trees. -/
theorem geneTreeDist_nonneg (hN : N.IsPhylogenetic) (hθ : N.IsMetric θ) (hρ : 0 ≤ ρ ∧ ρ ≤ 1)
    (G : Finset (Finset X)) : 0 ≤ geneTreeDist N θ ρ G := by
  sorry

theorem sum_geneTreeDist (hN : N.IsPhylogenetic) (hθ : N.IsMetric θ) (hρ : 0 ≤ ρ ∧ ρ ≤ 1)
    [Nonempty X] : ∑ G, geneTreeDist N θ ρ G = 1 := by
  sorry

/-- Gene trees are binary rooted trees on all the taxa. -/
theorem geneTreeDist_support (hN : N.IsPhylogenetic) (hθ : N.IsMetric θ) (hρ : 0 ≤ ρ ∧ ρ ≤ 1)
    [Nonempty X] {G : Finset (Finset X)} (hG : geneTreeDist N θ ρ G ≠ 0) : IsBinaryHierarchy G := by
  sorry

/-- Every binary rooted tree on the taxa has positive probability. -/
theorem geneTreeDist_pos (hN : N.IsPhylogenetic) (hθ : N.IsMetric θ) (hρ : 0 ≤ ρ ∧ ρ ≤ 1)
    [Nonempty X] {G : Finset (Finset X)} (hG : IsBinaryHierarchy G) : 0 < geneTreeDist N θ ρ G := by
  sorry

/-- Quartet concordance factors are positive. -/
theorem nmscCF_pos (hN : N.IsPhylogenetic) (hθ : N.IsMetric θ) (hρ : 0 ≤ ρ ∧ ρ ≤ 1)
    (s : QuartetTree X) : 0 < nmscCF N θ ρ s := by
  sorry

/-- The quartet concordance factors on a set of four taxa sum to one. -/
theorem sum_nmscCF (hN : N.IsPhylogenetic) (hθ : N.IsMetric θ) (hρ : 0 ≤ ρ ∧ ρ ≤ 1)
    {q : Finset X} (hq : q.card = 4) : ∑ r ∈ treesOn q, nmscCF N θ ρ r = 1 := by
  sorry

end Phylogenetics
