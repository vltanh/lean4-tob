module

public import Phylogenetics.Network.Cuts

/-!
# Huber, van Iersel, Jones, Moulton, Veenema-Nipius 2025, Theorem 5.1, forward direction

K. T. Huber, L. van Iersel, M. Jones, V. Moulton, L. Veenema-Nipius, *When are quarnets sufficient to
reconstruct semi-directed phylogenetic networks?*, Bull. Math. Biol. 87 (2025), 136.
-/

@[expose] public section

open Phylogenetics Phylogenetics.RootedNetwork

namespace External.HuberEtAl2025

variable {V E X : Type*} [Fintype X] [DecidableEq X] {N : RootedNetwork V E X}

omit [Fintype X] in
/-- **Theorem 5.1, forward direction.** If `A|B` is the split of a cut edge, then for all distinct
`a₁, a₂ ∈ A` and `b₁, b₂ ∈ B`, `a₁a₂|b₁b₂` is the split of a cut edge of the network induced on
these taxa. The source treats binary semi-directed networks; the binary condition is not needed. -/
theorem theorem5_1_forward (hN : N.IsPhylogenetic) {A : Finset X} (hA : N.HasCutSplit (A : Set X))
    {a₁ a₂ b₁ b₂ : X} (ha₁ : a₁ ∈ A) (ha₂ : a₂ ∈ A) (hb₁ : b₁ ∉ A) (hb₂ : b₂ ∉ A) :
    N.HasCutSplitOn (({a₁, a₂, b₁, b₂} : Finset X) : Set X) (({a₁, a₂} : Finset X) : Set X) :=
  HasCutSplit.hasCutSplitOn_quartet hN hA ha₁ ha₂ hb₁ hb₂

end External.HuberEtAl2025
