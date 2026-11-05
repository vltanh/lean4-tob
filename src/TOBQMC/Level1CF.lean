module

public import AllmanEtAl2023.Basic
public import Basic.Defs
public import Basic.Level1CF
public import Phylogenetics.NMSC.TreeCF
/-!
# TOB-QMC §4.3: concordance factors of induced cut-edge splits at level 1

TOB-QMC's consistency claim (lines 596–600 of v5) needs TINNiK's hypothesis tests to be correct on all
four-taxon subsets, that is, CF-detectability at the parameters of the network. The paper's assumptions give
it directly on the non-treelike subsets (6a) and on the subsets that the tree of blobs resolves
(T-quartet-nonanomaly, with exchangeability). The paper does not discuss the third class: an
induced cut-edge split `s` that the tree of blobs does not display. Nothing needs to be assumed there, as
`s` has the strictly largest concordance factor: `Level1.nmscCF_lt_of_not_displays`, in
`src/Basic/Level1CF.lean`, which does not use Lemma 4.

## Main results

* `Level1.nmscCF_lt_of_inducedCutSplit`: T-quartet-nonanomaly gives the same on all induced cut-edge
  splits, condition 6b of the paper, at level 1.
* `Level1.cfDetectable`: CF-detectability under the paper's assumptions.
-/

@[expose] public noncomputable section

open Phylogenetics Phylogenetics.RootedNetwork Finset
open scoped Classical

namespace TOBQMC.Level1

variable {V E X : Type*} [Fintype X] [DecidableEq X] {N : RootedNetwork V E X}

section LevelOne

variable [Fintype V] [Fintype E]

/-- At level 1, condition 4 of TOB-QMC (T-quartet-nonanomaly) gives condition 6b (class 1
quartet-nonanomaly): on every induced cut-edge split, the split has the strictly largest concordance
factor. -/
theorem nmscCF_lt_of_inducedCutSplit (hN : N.IsPhylogenetic) (hLevel : IsLevelOne N)
    {θ : MetricData E} (hθ : N.IsMetric θ) {ρ : ℝ} (hρ : 0 ≤ ρ ∧ ρ ≤ 1)
    (hNon : IsTQuartetNonanomalous N (nmscCF N θ ρ)) {s : QuartetTree X}
    (hs : InducedCutSplit N s) {r : QuartetTree X} (hr : r ∈ s.alternatives) :
    nmscCF N θ ρ r < nmscCF N θ ρ s := by
  by_cases hd : Displays (treeOfBlobs N) s
  · exact hNon s hd r hr
  · exact nmscCF_lt_of_not_displays hN hLevel hθ hρ hs hd hr

/-- **CF-detectability under the assumptions of TOB-QMC**, for all four-taxon subsets of a level-1
network: non-treelike subsets by 6a; subsets the tree of blobs resolves by T-quartet-nonanomaly and
exchangeability; and the other treelike subsets by `nmscCF_lt_of_not_displays`, with no assumption.
This is what TOB-QMC §4.3 needs for TINNiK's tests to be correct on all subsets. -/
theorem cfDetectable {θ : MetricData E} {ρ : ℝ} (hStd : StandardAssumptions N θ ρ)
    (hLevel : IsLevelOne N) (hNon : IsTQuartetNonanomalous N (nmscCF N θ ρ))
    (hBlob : ∀ q : Finset X, q.card = 4 → ¬ IsTreelike N q →
      AllmanEtAl2023.IsNonCut (nmscCF N θ ρ) q) :
    AllmanEtAl2023.CFDetectable N (nmscCF N θ ρ) :=
  ⟨fun s hs => ⟨fun _ hr =>
      (nmscCF_lt_of_inducedCutSplit hStd.phylogenetic hLevel hStd.metric hStd.rho hNon hs hr).ne,
    NMSC.cut_alternatives hStd.phylogenetic hStd.metric hStd.rho s hs⟩, hBlob⟩

end LevelOne

end TOBQMC.Level1
