module

public import Phylogenetics.NMSC.DisplayedTreeModel

/-!
# No anomalous quartets at `ρ = 1`

The strict form of Proposition 12 of Ané, Fogg, Allman, Baños, Rhodes 2024, and what Remark 3.3 of ECToBlob says of common
inheritance, from the library's bound `RootedNetwork.nmscCF_lt_rho_one_of_separates`.

`src/ECToBlob/Remark33.lean` and `src/ECToBlob/Remark84.lean` import this file.
-/

@[expose] public noncomputable section

open Finset Phylogenetics
open scoped Classical

namespace Phylogenetics.RootedNetwork

variable {V E X : Type*} {N : RootedNetwork V E X}
variable [Fintype V] [Fintype E] [Fintype X] [DecidableEq X] {θ : MetricData E}

/-- **The network multispecies coalescent with common inheritance has no anomalous quartets**, for any valid
parameters: on a cut-edge split of an induced network, the quartet tree of the split is strictly the most
probable. This is Proposition 12 of Ané et al. 2024, for all networks, with the strict inequality. -/
theorem nmscCF_lt_rho_one (hN : N.IsPhylogenetic) (hθ : N.IsMetric θ) {s : QuartetTree X}
    (hs : InducedCutSplit N s) {r : QuartetTree X} (hr : r ∈ s.alternatives) :
    nmscCF N θ 1 r < nmscCF N θ 1 s := by
  obtain ⟨P, hP, e, hd, hn⟩ := exists_separating_arc hN hs
  obtain ⟨a, ha⟩ : P.Nonempty := card_pos.1 (by rw [s.card_of_mem hP]; omega)
  exact nmscCF_lt_rho_one_of_separates hN hθ.isWeakMetric s hP
    (hθ.1 e (NMSC.isTreeArc_of_dominates hN (hd a ha))) hd hn hr

/-- **Equation (3.1) for common inheritance, provided only that cut edges have positive lengths**: other
tree arcs may have length zero, and hybrid arcs inheritance zero. -/
theorem nmscCF_lt_rho_one_of_displays (hN : N.IsPhylogenetic) (hθ : N.IsWeakMetric θ)
    (hcut : ∀ e, N.graph.underlying.IsBridge e → 0 < θ.length e) {s : QuartetTree X}
    (hs : Displays (treeOfBlobs N) s) {r : QuartetTree X} (hr : r ∈ s.alternatives) :
    nmscCF N θ 1 r < nmscCF N θ 1 s := by
  obtain ⟨P, hP, e, hb, hd, hn⟩ := exists_isBridge_separating hN hs
  exact nmscCF_lt_rho_one_of_separates hN hθ s hP (hcut e hb) hd hn hr

end Phylogenetics.RootedNetwork
