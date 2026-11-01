module

public import Gusfield2007.Components

/-!
# Gusfield et al. 2007, Figure 5: the numbers

`R¹(M(C₁)) = R¹(M(C₂)) = 1` and `R¹(M) = 3` (line 404), and the same numbers for `R` (the caption, line 410). The paper obtains them from the program beagle. Here, the upper bounds are explicit networks, which aren't in
the paper, and the lower bounds are by the verified search of `Gusfield2007.LabelSearch`.
-/

@[expose] public section

open scoped Classical

namespace Gusfield2007

/-- The sites of `C₁`. -/
def fig5Sites₁ : Fin 4 → Fin 8 := Fin.castLE (by decide)

/-- The sites of `C₂`. -/
def fig5Sites₂ : Fin 4 → Fin 8 := Fin.natAdd 4

theorem fig5Sites₁_strictMono : StrictMono fig5Sites₁ := fun a b h => by
  revert a b
  decide

theorem fig5Sites₂_strictMono : StrictMono fig5Sites₂ := fun a b h => by
  revert a b
  decide

theorem fig5Sites₁_range : Set.range fig5Sites₁ = fig5C₁ := Set.ext fun i => by
  change (∃ a, fig5Sites₁ a = i) ↔ i.val < 4
  revert i
  decide

theorem fig5Sites₂_range : Set.range fig5Sites₂ = fig5C₂ := Set.ext fun i => by
  change (∃ a, fig5Sites₂ a = i) ↔ 4 ≤ i.val
  revert i
  decide

/-- A network for `M(C₁)` and `M(C₂)`, which are the same matrix, with one recombination node: `0000` is a recombinant of `1100` and `0011`, the others are on a path. -/
def fig5CompNet : NetSpec 4 12 12 :=
  ⟨[0, 1, 2, 3, 0, 4, 2, 0, 1, 4, 3, 5],
   [1, 2, 3, 4, 5, 5, 6, 7, 8, 9, 10, 11],
   [2, 3, 0, 1],
   [3, 7, 15, 14, 12, 0, 15, 3, 7, 12, 14, 0]⟩

theorem fig5CompNet_valid : fig5CompNet.Valid := by decide +kernel

theorem fig5CompNet_single : fig5CompNet.SingleCheck := by decide +kernel

theorem fig5CompNet_recombs : fig5CompNet.recombs = 1 := by decide +kernel

/-- A network for the matrix of Figure 5, with three recombination nodes, all single crossovers. -/
def fig5Net : NetSpec 8 22 24 :=
  ⟨[0, 0, 1, 2, 3, 5, 4, 6, 7, 8, 0, 9, 0, 9, 3, 0, 1, 6, 5, 9, 10, 11, 7, 8],
   [1, 2, 3, 4, 5, 6, 7, 7, 8, 9, 10, 10, 11, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21],
   [4, 5, 0, 2, 9, 8, 1, 3],
   [3, 7, 67, 15, 195, 14, 12, 192, 224, 240, 48, 112, 15, 3, 7, 12, 14, 240, 48, 112, 192, 224]⟩

theorem fig5Net_valid : fig5Net.Valid := by decide +kernel

theorem fig5Net_derives : fig5Net.DerivesCheck fig5 := by decide +kernel

theorem fig5Net_single : fig5Net.SingleCheck := by decide +kernel

theorem fig5Net_recombs : fig5Net.recombs = 3 := by decide +kernel

/-- The codes of the rows of Figure 5. -/
def fig5Codes : List ℕ := [15, 3, 7, 12, 14, 240, 48, 112, 192, 224]

theorem fig5Codes_codesOf : CodesOf fig5 fig5Codes := by decide +kernel

/-- No network for the matrix of Figure 5 has at most two recombination nodes, in any model. By the search: it's checked in the kernel. -/
theorem fig5_check : LabelSearch.check 8 fig5Codes 2 = false := by decide +kernel

/-- The codes of the rows of `M(C₁)`, `M(C₂)`. -/
def fig5CompCodes : List ℕ := [15, 3, 7, 12, 14, 0]

theorem fig5Comp_check : LabelSearch.check 4 fig5CompCodes 0 = false := by decide +kernel

theorem fig5_R₁ {c : Crossover} (hc : c = .single ∨ c = .multiple) : R c (restrictRows fig5C₁ fig5) = 1 := by
  rw [R_restrictRows fig5Sites₁ fig5Sites₁_strictMono fig5Sites₁_range]
  refine R_eq_of_spec (s := fig5CompNet) (k := 0) fig5CompNet_valid (by decide +kernel) ?_ fig5CompNet_recombs (Mc := fig5CompCodes) (by decide +kernel) fig5Comp_check
  rcases hc with rfl | rfl
  · exact NetSpec.obeys_single_toNetwork _ fig5CompNet_single
  · trivial

theorem fig5_R₂ {c : Crossover} (hc : c = .single ∨ c = .multiple) : R c (restrictRows fig5C₂ fig5) = 1 := by
  rw [R_restrictRows fig5Sites₂ fig5Sites₂_strictMono fig5Sites₂_range]
  refine R_eq_of_spec (s := fig5CompNet) (k := 0) fig5CompNet_valid (by decide +kernel) ?_ fig5CompNet_recombs (Mc := fig5CompCodes) (by decide +kernel) fig5Comp_check
  rcases hc with rfl | rfl
  · exact NetSpec.obeys_single_toNetwork _ fig5CompNet_single
  · trivial

theorem fig5_R {c : Crossover} (hc : c = .single ∨ c = .multiple) : R c fig5 = 3 := by
  refine R_eq_of_spec (s := fig5Net) (k := 2) fig5Net_valid fig5Net_derives ?_ fig5Net_recombs fig5Codes_codesOf fig5_check
  rcases hc with rfl | rfl
  · exact NetSpec.obeys_single_toNetwork _ fig5Net_single
  · trivial

end Gusfield2007
