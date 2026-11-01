module

public import AllmanEtAl2023.Corollary1

/-!
# Allman, Baños, Mitchell, Rhodes 2023: CF-detectability for the later papers

The paper's Corollary 1 (the PMC text, lines 154-157) is `corollary1` in `AllmanEtAl2023.Corollary1`. This file holds what the later papers use: the same content on quartet trees and cut-edge splits,
as `CFDetectable`. TINNiK's Theorem 1 is `cfDetectable_generic`.
-/

@[expose] public noncomputable section

open Phylogenetics Phylogenetics.RootedNetwork
open scoped Classical

namespace AllmanEtAl2023

variable {V E X : Type*} [Fintype V] [Fintype E] [Fintype X] [DecidableEq X] {N : RootedNetwork V E X}

/-- **CF-detectability, for generic parameters**: for a rooted binary phylogenetic network, the numerical parameters at which the NMSC with independent inheritance fails CF-detectability on some induced 4-taxon network form a null set.

This isn't a consequence of the statement of `corollary1`: `readTopology` reads an all-equal `CF` as unresolved, while `CFDetectable` asks for a non-cut `CF` there. So it comes from the step of the proof of Corollary 1 on one 4-taxon network, `forGenericParams_inducedDetectable`, which has statement 2 of Theorem 1, and the bridges from `T_rd` of the induced network to cut-edge splits. -/
theorem cfDetectable_generic (hN : N.IsPhylogenetic) (hBin : N.IsBinary) :
    N.IsGenericNull {θ | N.IsMetric θ ∧ ¬ CFDetectable N (nmscCF N θ 0)} := by
  have hB : IsBinaryNetwork N := isBinaryNetwork_iff.mpr ⟨hN, hBin⟩
  refine (IsGenericNull.iUnion (ι := {Q : Finset X // Q.card = 4}) fun Q => forGenericParams_inducedDetectable hB Q.1 Q.2).mono ?_
  rintro θ ⟨hθ, hnot⟩
  by_contra hall
  have hdet : ∀ (Q : Finset X) (hQ : Q.card = 4), InducedDetectable hB θ Q hQ := by
    intro Q hQ
    by_contra hn
    exact hall (Set.mem_iUnion.mpr ⟨⟨Q, hQ⟩, hθ, hn⟩)
  refine hnot ⟨fun s hs => ?_, fun q hq hnt => ?_⟩
  · obtain ⟨a, b, c, d, h, rfl⟩ := TreeMetric.exists_eq_quartetTree s
    have htop : InducedHasQuartetTopology hB a b c d h := (Bridges.inducedHasQuartetTopology_iff hB h).mpr hs
    have := (hdet {a, b, c, d} h ⟨a, by simp⟩ ⟨b, by simp⟩ ⟨c, by simp⟩ ⟨d, by simp⟩ h).1.mp htop
    exact (isStrictlyCutAtFirst_iff _ h).mp this
  · obtain ⟨a, t, -, rfl, ht⟩ := Finset.card_eq_succ.mp hq
    obtain ⟨b, c, d, -, -, -, rfl⟩ := Finset.card_eq_three.mp ht
    have htop : InducedHasStarTopology hB a b c d hq := (Bridges.inducedHasStarTopology_iff hB hq).mpr hnt
    have := (hdet {a, b, c, d} hq ⟨a, by simp⟩ ⟨b, by simp⟩ ⟨c, by simp⟩ ⟨d, by simp⟩ hq).2.mp htop
    exact (isNonCutCF_iff _ hq).mp this

/-- **Statement (b) of the proof of Theorem 1, on a set of four taxa of a network**: without a cut-edge split on its induced network, the CF is non-cut for generic parameters. From `cfDetectable_generic`. -/
theorem isGenericNull_not_isNonCut (hN : N.IsPhylogenetic) (hBin : N.IsBinary) {q : Finset X} (hq : q.card = 4) (hnt : ¬ IsTreelike N q) :
    IsGenericNull N {θ | N.IsMetric θ ∧ ¬ IsNonCut (nmscCF N θ 0) q} :=
  (cfDetectable_generic hN hBin).mono fun _ hθ => ⟨hθ.1, fun hd => hθ.2 (hd.blob q hq hnt)⟩

end AllmanEtAl2023
