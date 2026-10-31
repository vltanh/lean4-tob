module

public import TINNiK.Basic
public import TOBQMC.Level1
public import TOBQMC.WQC

/-!
# TOB-QMC §4.3: statistical consistency for level-1 networks

The unnumbered claim at the end of §4.3 (`tob2025:consistency`), combining Theorem 1, Theorem 2 and
TINNiK Theorem 4: for level-1 networks, with levels `α_k → 0` and any `β > 0`, labelling the edges of
any optimal solution of Weighted Quartet Consensus by hypothesis tests on a disjoint cover and
contracting those labelled false positives returns the tree of blobs with probability tending to one.
The tests are TINNiK's star and cut tests; the T3 option is not treated.
-/

@[expose] public noncomputable section

open Phylogenetics Phylogenetics.RootedNetwork Finset Filter Topology
open scoped Classical

namespace TOBQMC

variable {V E X : Type*} [Fintype X] [DecidableEq X]

/-- **The consistency claim of §4.3** (`tob2025:consistency`), conditional on exchangeability. For a
binary level-1 network under the standard assumptions that is T-quartet-nonanomalous, at parameters
where CF-detectability holds, there are levels `α_k → 0` such that for any `β > 0`, any selection of
maximum likelihood topologies, any solver of Weighted Quartet Consensus and any selection of disjoint
covers, the method on `k` independent gene trees returns the tree of blobs with probability tending
to one. -/
theorem consistency [Fintype V] [Fintype E] {N : RootedNetwork V E X} {θ : MetricData E} {ρ : ℝ}
    (hStd : StandardAssumptions N θ ρ) (hLevel : IsLevelOne N)
    (hEx : External.AneEtAl2024.Exchangeability N θ ρ)
    (hNon : IsTQuartetNonanomalous N (nmscCF N θ ρ))
    (hdet : External.AllmanEtAl2023.CFDetectable N (nmscCF N θ ρ)) (hX : 4 ≤ Fintype.card X) :
    ∃ α : ℕ → ℝ, Tendsto α atTop (𝓝 0) ∧ (∀ k, 0 < α k) ∧
      ∀ (β : ℝ), 0 < β →
      ∀ (ml : (QuartetTree X → ℝ) → Finset X → QuartetTree X), IsMLSelection ml →
      ∀ (solve : (QuartetTree X → ℝ) → Finset (Finset X)), (∀ c, IsWQCOptimal c (solve c)) →
      ∀ (cover : Finset (Finset X) → Finset X → Finset (Finset X)),
        (∀ B, IsBinaryTree B → ∀ A ∈ internalSides B, IsDisjointCover B A (cover B A)) →
        Tendsto (fun k => iidProb (geneTreeDist N θ ρ) k fun ω =>
          tobqmc ml (α k) β (quartetCount unroot ω) (solve (quartetCount unroot ω))
            (cover (solve (quartetCount unroot ω))) = treeOfBlobs N) atTop (𝓝 1) := by
  sorry

end TOBQMC
