module

public import Basic.Phylogenetics.NetworkCuts

/-!
# Huber, van Iersel, Jones, Moulton, Veenema-Nipius 2025, Theorem 5.1, forward direction

K. T. Huber, L. van Iersel, M. Jones, V. Moulton, L. Veenema-Nipius, *When are quarnets sufficient to
reconstruct semi-directed phylogenetic networks?*, Bull. Math. Biol. 87 (2025), 136.
-/

@[expose] public section

open Phylogenetics Phylogenetics.RootedNetwork

namespace External.HuberEtAl2025

variable {V E X : Type*} [Fintype X] [DecidableEq X] {N : RootedNetwork V E X}

set_option linter.unusedSectionVars false in
/-- **Theorem 5.1, forward direction.** If `A|B` is the split of a cut edge, then for all distinct
`a₁, a₂ ∈ A` and `b₁, b₂ ∈ B`, `a₁a₂|b₁b₂` is the split of a cut edge of the network induced on
these taxa. The source treats binary semi-directed networks; the binary condition is not needed. -/
theorem theorem5_1_forward (hN : N.IsPhylogenetic) {A : Finset X} (hA : N.HasCutSplit (A : Set X))
    {a₁ a₂ b₁ b₂ : X} (ha₁ : a₁ ∈ A) (ha₂ : a₂ ∈ A) (hb₁ : b₁ ∉ A) (hb₂ : b₂ ∉ A) :
    N.HasCutSplitOn (({a₁, a₂, b₁, b₂} : Finset X) : Set X) (({a₁, a₂} : Finset X) : Set X) := by
  have hcut : N.HasCutSplitOn (({a₁, a₂, b₁, b₂} : Finset X) : Set X) (A : Set X) :=
    hA.hasCutSplitOn hN ⟨a₁, by simp, ha₁⟩ ⟨b₁, by simp, hb₁⟩
  refine (hasCutSplitOn_congr ?_).mp hcut
  ext x
  simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_inter_iff, Set.mem_insert_iff,
    Set.mem_singleton_iff, Finset.mem_coe]
  constructor
  · rintro ⟨hx | hx | hx | hx, hxA⟩
    · exact ⟨Or.inl hx, Or.inl hx⟩
    · exact ⟨Or.inr (Or.inl hx), Or.inr hx⟩
    · exact absurd (hx ▸ hxA) hb₁
    · exact absurd (hx ▸ hxA) hb₂
  · rintro ⟨-, rfl | rfl⟩
    · exact ⟨Or.inl rfl, ha₁⟩
    · exact ⟨Or.inr (Or.inl rfl), ha₂⟩

end External.HuberEtAl2025
