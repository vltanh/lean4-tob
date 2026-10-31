module

public import Basic.Phylogenetics.NMSC.Basic
public import Basic.Probability.QuartetTests
public import External.AllmanEtAl2023.Basic
public import External.Rhodes2020.Theorem2
public import TINNiK.Statistics.AppendixC

/-!
# TINNiK: consistency of the algorithm

Definition 6 for quartet concordance factors, the count of Step 3(a)(i) (E8 of the report), and
Theorem 4. Theorem 4 takes the CF-detectability of 4-blobs from the literature
(`External.AllmanEtAl2023.Corollary1`, TINNiK's Theorem 1 on the induced 4-taxon networks), so it is
conditional on that result. Theorem 2 and the combinatorial part of Theorem 3 are proved in
`External/AllmanEtAl2023/Basic.lean`.
-/

@[expose] public noncomputable section

open Phylogenetics Phylogenetics.RootedNetwork Finset Filter Topology
open scoped Classical

namespace TINNiK

variable {V E X : Type*} [Fintype X] [DecidableEq X]

/-- The count of Step 3(a)(i) of the B-quartet Inference Algorithm, corrected (E8 of the report): a
4-taxon set has exactly `4 (N - 4)` others sharing exactly three of its taxa. The printed `4(N - 1)` is
a misprint. -/
theorem card_sharing_three {q : Finset X} (hq : q.card = 4) :
    (univ.filter fun t : Finset X => t.card = 4 ∧ (t ∩ q).card = 3).card = 4 * (Fintype.card X - 4) := by
  sorry

/-- **Theorem 4** at given parameters (`tinnik:theorem4`). If the NMSC's concordance factors at the
parameters `θ` of a rooted binary network satisfy CF-detectability on all induced 4-taxon networks, then
for levels `α_m → 0` of the cut test with `log(1/α_m) = o(m)`, for any `β > 0` and `0 ≤ δ < 2`, any exact
distance-based tree building method and any selection of maximum likelihood topologies, the
TINNiK algorithm on `m` independent gene trees infers the tree of blobs with probability tending to
one. -/
theorem theorem4_of_detectable [Fintype V] [Fintype E] {N : RootedNetwork V E X}
    (hN : N.IsPhylogenetic) (hBin : N.IsBinary) (hX : 4 ≤ Fintype.card X) {θ : MetricData E}
    (hθ : N.IsMetric θ) (hdet : External.AllmanEtAl2023.CFDetectable N (nmscCF N θ 0))
    {α : ℕ → ℝ} (hα : ∀ m, 0 < α m) (hα₀ : Tendsto α atTop (𝓝 0))
    (hαlog : Tendsto (fun m : ℕ => Real.log (α m) / m) atTop (𝓝 0))
    {β δ : ℝ} (hβ : 0 < β) (hδ : 0 ≤ δ) (hδ₂ : δ < 2) {M : TreeBuilder X} (hM : IsExactBuilder M)
    {ml : (QuartetTree X → ℝ) → Finset X → QuartetTree X} (hml : IsMLSelection ml) :
    Tendsto (fun m => iidProb (geneTreeDist N θ 0) m fun ω =>
      tinnik ml (α m) β δ M (quartetCount unroot ω) = treeOfBlobs N) atTop (𝓝 1) := by
  sorry

/-- **Theorem 4** (`tinnik:theorem4`), conditional on CF-detectability for generic parameters
(`External.AllmanEtAl2023.Corollary1`). For generic numerical parameters on a binary network there is a
sequence `α_m → 0` such that for any `β > 0` and `2 > δ ≥ 0`, the TINNiK algorithm using the cut test on
`m` independent gene trees from the NMSC infers the tree of blobs with probability tending to one. -/
theorem theorem4 [Fintype V] [Fintype E] {N : RootedNetwork V E X}
    (hN : N.IsPhylogenetic) (hBin : N.IsBinary) (hX : 4 ≤ Fintype.card X)
    (hCor : External.AllmanEtAl2023.Corollary1 N) :
    ∃ A : Set (MetricData E), External.AllmanEtAl2023.IsGenericNull N A ∧
      ∀ θ, N.IsMetric θ → θ ∉ A →
        ∃ α : ℕ → ℝ, Tendsto α atTop (𝓝 0) ∧ (∀ m, 0 < α m) ∧
          ∀ (β δ : ℝ), 0 < β → 0 ≤ δ → δ < 2 →
          ∀ (M : TreeBuilder X), IsExactBuilder M →
          ∀ (ml : (QuartetTree X → ℝ) → Finset X → QuartetTree X), IsMLSelection ml →
            Tendsto (fun m => iidProb (geneTreeDist N θ 0) m fun ω =>
              tinnik ml (α m) β δ M (quartetCount unroot ω) = treeOfBlobs N) atTop (𝓝 1) := by
  sorry

end TINNiK
