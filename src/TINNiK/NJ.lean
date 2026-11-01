module

public import AllmanEtAl2023.Basic
public import Basic.Defs
public import Phylogenetics.NMSC.Defs
public import Basic.Testing.Defs
public import Basic.Testing.IID
public import Phylogenetics.Tree.NeighborJoining
public import TINNiK.Basic
public import TINNiK.Counts

/-!
# TINNiK with neighbor joining

TINNiK's Theorem 4 for the distance-based method that the paper names in step 4 of the algorithm
(`notes/tinnik/readable.txt`, line 194), neighbor joining, with any way of breaking ties: `theorem4_nj` and
`theorem4_explicit_nj`, instances of `TINNiK.theorem4` and `TINNiK.theorem4_explicit` by
`Phylogenetics.NJ.isExactBuilder_nj`. The paper's step 4 takes `O(N³)` (line 196):
`Phylogenetics.NJ.ops_run`, `Phylogenetics.NJ.njOps_le`.
-/

@[expose] public noncomputable section

open Phylogenetics Phylogenetics.RootedNetwork Filter Topology
open scoped Classical

namespace TINNiK

variable {V E X : Type*} [Fintype X] [DecidableEq X]

/-- **Theorem 4 with neighbor joining** (`tinnik:theorem4`). For generic numerical parameters on a binary
network there is a sequence `α_m → 0` such that for any `β > 0` and `2 > δ ≥ 0`, and whichever way NJ breaks ties,
the TINNiK algorithm using the cut test and NJ in step 4 on `m` independent gene trees from the NMSC infers the
tree of blobs with probability tending to one. -/
theorem theorem4_nj [Fintype V] [Fintype E] {N : RootedNetwork V E X}
    (hN : N.IsPhylogenetic) (hX : 4 ≤ Fintype.card X) (hBin : N.IsBinary) :
    ∃ A : Set (MetricData E), IsGenericNull N A ∧
      ∀ θ, N.IsMetric θ → θ ∉ A →
        ∃ α : ℕ → ℝ, Tendsto α atTop (𝓝 0) ∧ (∀ m, 0 < α m) ∧
          ∀ (β δ : ℝ), 0 < β → 0 ≤ δ → δ < 2 →
          ∀ (tb : NJ.TieBreak X),
          ∀ (ml : (QuartetTree X → ℝ) → Finset X → QuartetTree X), IsMLSelection ml →
            Tendsto (fun m => iidProb (geneTreeDist N θ 0) m fun ω =>
              tinnik ml (α m) β δ (NJ.nj tb) (quartetCount unroot ω) = treeOfBlobs N) atTop (𝓝 1) := by
  obtain ⟨A, hA, h⟩ := theorem4 hN hX hBin
  refine ⟨A, hA, fun θ hθ hθA => ?_⟩
  obtain ⟨α, h1, h2, h3⟩ := h θ hθ hθA
  exact ⟨α, h1, h2, fun β δ hβ hδ hδ₂ tb ml hml =>
    h3 β δ hβ hδ hδ₂ (NJ.nj tb) (NJ.isExactBuilder_nj tb) ml hml⟩

/-- Theorem 4 with neighbor joining, and one sequence of levels for all networks and parameters: the upper tail of
`χ²₁` at `log m`. -/
theorem theorem4_explicit_nj [Fintype V] [Fintype E] {N : RootedNetwork V E X}
    (hN : N.IsPhylogenetic) (hX : 4 ≤ Fintype.card X) {θ : MetricData E} (hθ : N.IsMetric θ)
    (hdet : AllmanEtAl2023.CFDetectable N (nmscCF N θ 0)) {β δ : ℝ} (hβ : 0 < β) (hδ₂ : δ < 2)
    (tb : NJ.TieBreak X)
    {ml : (QuartetTree X → ℝ) → Finset X → QuartetTree X} (hml : IsMLSelection ml) :
    Tendsto (fun m : ℕ => iidProb (geneTreeDist N θ 0) m fun ω =>
      tinnik ml (chiSqOneTail (Real.log m)) β δ (NJ.nj tb) (quartetCount unroot ω) = treeOfBlobs N)
      atTop (𝓝 1) :=
  theorem4_explicit hN hX hθ hdet hβ hδ₂ (NJ.isExactBuilder_nj tb) hml

/-- **TINNiK's combined time with NJ in step 4**, `O((m + N) N⁴)`: `tinnikOperations_le` with the count of
neighbor joining (`notes/tinnik/readable.txt`, line 196). -/
theorem tinnikOperations_nj_le {N m : ℕ} (hN : 1 ≤ N) :
    tinnikOperations N m (NJ.njOps N) ≤ (68 + 8) * ((m + N) * N ^ 4) :=
  tinnikOperations_le hN (NJ.njOps_le N)

end TINNiK
