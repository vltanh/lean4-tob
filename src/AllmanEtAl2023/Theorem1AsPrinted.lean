module

public import AllmanEtAl2023.Lemma1

/-!
# Allman, Baños, Mitchell, Rhodes 2023: Theorem 1, as printed

The statement of the paper on `T_rd(𝒩⁻)` and the triple `CF_abcd`, with its statements (a), (b) of the proof, and the claim
of its proof that (a) has "`CF` is `(ab|cd)`-cut for all parameters". `AllmanEtAl2023.theorem1` (`src/AllmanEtAl2023/Theorem1.lean`) has the same content
on `InducedCutSplit` and `IsTreelike`, but its proof departs from the paper in the ways that `notes/allman_inventory.md` lists.
-/

@[expose] public noncomputable section

open Phylogenetics Phylogenetics.RootedNetwork
open scoped Classical

namespace AllmanEtAl2023.Printed

variable {V E X : Type*} [Fintype V] [Fintype E] [Fintype X] [DecidableEq X] {N : RootedNetwork V E X}

/- Inventory. `Phylogenetics.NMSC.cut_alternatives` has this on `InducedCutSplit`. To follow the paper: `Claims.rootedForms`, then coalescence below the blob and exchangeability
above it in each form. -/
/-- **Theorem 1, (a), "for all parameters"** (`a:claim:thm1-cut`). In the proof of Theorem 1: "Thus `CF` is `(ab|cd)`-cut for all
parameters". Proposition 1 needs this form, though it cites "statement 1 of Theorem 1". -/
theorem theorem1_cut (hN : IsBinaryNetwork N) (hcard : Fintype.card X = 4) {a b c d : X}
    (h : ({a, b, c, d} : Finset X).card = 4)
    (hT : (Trd hN (nontrivial_of_card_four hcard)).HasQuartetTopology a b c d) {θ : MetricData E}
    (hθ : N.IsMetric θ) : (cfTriple N θ a b c d h).2.1 = (cfTriple N θ a b c d h).2.2 := by
  sorry

/- Inventory. `AllmanEtAl2023.isGenericNull_not_isStrictlyCut` has it on `InducedCutSplit`, with one argument at the arc, not the paper's three forms (departure D1 of the review). -/
/-- **Statement (a) in the proof of Theorem 1** (`a:claim:thm1a`). If `T` has the quartet tree topology `ab|cd`, then `CF_abcd` is
strictly `(ab|cd)`-cut, for generic parameters. -/
theorem theorem1_a (hN : IsBinaryNetwork N) (hcard : Fintype.card X = 4) :
    ForGenericParams N fun θ => ∀ (a b c d : X) (h : ({a, b, c, d} : Finset X).card = 4),
      (Trd hN (nontrivial_of_card_four hcard)).HasQuartetTopology a b c d →
        IsStrictlyFirstCut (cfTriple N θ a b c d h) := by
  sorry

/- Inventory. `AllmanEtAl2023.isGenericNull_not_isNonCut` has it on `IsTreelike`. It departs from the paper by D2 (no 2-blob step), D3 (no Lemma 1, no single edge), D4 (the order at the
contradiction), D5 and D6 (deleted networks in the coordinates of `𝒩⁺`, and half of "strictly cut"). To build: the deleted networks `𝒩ᵢ⁺` as networks, contraction of 2-blobs of length 0. -/
/-- **Statement (b) in the proof of Theorem 1** (`a:claim:thm1b`). If `T` has the unresolved quartet topology, then `CF_abcd` is
non-cut, for generic parameters. -/
theorem theorem1_b (hN : IsBinaryNetwork N) (hcard : Fintype.card X = 4) :
    ForGenericParams N fun θ => ∀ (a b c d : X) (h : ({a, b, c, d} : Finset X).card = 4),
      (Trd hN (nontrivial_of_card_four hcard)).HasStarTopology a b c d →
        IsNonCutCF (cfTriple N θ a b c d h) := by
  sorry

/- Inventory. `AllmanEtAl2023.theorem1` is the same statement on `InducedCutSplit` and `IsTreelike`, whose last step follows the paper. To connect: `Bridges.hasQuartetTopology_iff_displays`,
`Bridges.hasStarTopology_iff_displaysUnresolved`, `Bridges.splits_Trd`, `isStrictlyFirstCut_iff`, `isNonCutCF_iff`. -/
/-- **Theorem 1** (`a:thm:CFdetect`; `CF`-detectability of 4-blobs on 4-taxon networks). Consider a 4-taxon rooted binary phylogenetic
network `𝒩⁺` on taxa `{a, b, c, d}` with quartet concordance factor `CF = CF_abcd` and reduced unrooted tree of blobs
`T = T_rd(𝒩⁻)`. Then under the NMSC for generic parameters:
1. `T` has the quartet tree topology `ab|cd` if, and only if, `CF_abcd` is strictly `(ab|cd)`-cut.
2. `T` has the unresolved quartet topology if, and only if, `CF_abcd` is non-cut.

One exceptional set serves all namings of the taxa, of which there are finitely many. -/
theorem theorem1 (hN : IsBinaryNetwork N) (hcard : Fintype.card X = 4) :
    ForGenericParams N fun θ => ∀ (a b c d : X) (h : ({a, b, c, d} : Finset X).card = 4),
      ((Trd hN (nontrivial_of_card_four hcard)).HasQuartetTopology a b c d ↔
        IsStrictlyFirstCut (cfTriple N θ a b c d h)) ∧
      ((Trd hN (nontrivial_of_card_four hcard)).HasStarTopology a b c d ↔
        IsNonCutCF (cfTriple N θ a b c d h)) := by
  sorry

end AllmanEtAl2023.Printed
