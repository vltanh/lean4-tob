module

public import Basic.Phylogenetics.NMSC.Exchangeability

/-!
# Ané, Fogg, Allman, Baños, Rhodes 2024: exchangeability under the network multispecies coalescent

C. Ané, J. Fogg, E. S. Allman, H. Baños, J. A. Rhodes, *Anomalous networks under the multispecies
coalescent: theory and prevalence*, J. Math. Biol. 88 (2024), https://doi.org/10.1007/s00285-024-02050-7.

The exchangeability of taxa on the same side of a cut edge is cited by TOB-QMC's proof of Lemma 3 from
this source and from TINNiK (ECToBlob §5.1 and Remark 3.3 use the same fact). It is proved here for this
project's NMSC, on arbitrary networks and with inheritance correlation; see `External/AneEtAl2024/README.md`.
-/

@[expose] public noncomputable section

open Phylogenetics Phylogenetics.RootedNetwork

namespace External.AneEtAl2024

variable {V E X : Type*} [Fintype V] [Fintype E] [Fintype X] [DecidableEq X]

/-- **Exchangeability under the NMSC.** Concordance factors do not change when a taxon of a quartet tree is
replaced by one that a cut edge groups with it, away from the other three taxa: below that cut edge (or
beyond it, when the root is on the side of those taxa) the two taxa contribute one lineage or a position in a
chain, which the rest of the process cannot distinguish. -/
theorem exchangeability {N : RootedNetwork V E X} {θ : MetricData E} {ρ : ℝ} (hN : N.IsPhylogenetic)
    (hθ : N.IsMetric θ) (hρ : 0 ≤ ρ ∧ ρ ≤ 1) : CutExchangeable N (nmscCF N θ ρ) :=
  NMSC.exchangeability hN hθ hρ

end External.AneEtAl2024
