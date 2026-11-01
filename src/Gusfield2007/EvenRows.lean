module

public import Gusfield2007.Components

/-!
# A smaller counterexample to the multiple-crossover conjecture: the numbers

This isn't in the paper: an independent review of the statements found it. The rows are `evenRows`: `000000`, `000011`, `000101`, `000110`, `011000`, `101000`, `110000`, that is, on each
of the two sets of three sites, the even sequences. Seven rows and six sites, against the thirteen and ten of Figure 8. A triangle of incompatible sites needs two recombination nodes, and each component is one. By the search, `R(M(C_k)) = 2`, and `R(M) = 3`.
-/

@[expose] public section

open scoped Classical

namespace Gusfield2007

/-- The sites of `C₁`. -/
def evenSites₁ : Fin 3 → Fin 6 := Fin.castLE (by decide)

/-- The sites of `C₂`. -/
def evenSites₂ : Fin 3 → Fin 6 := Fin.natAdd 3

theorem evenSites₁_strictMono : StrictMono evenSites₁ := fun a b h => by
  revert a b
  decide

theorem evenSites₂_strictMono : StrictMono evenSites₂ := fun a b h => by
  revert a b
  decide

theorem evenSites₁_range : Set.range evenSites₁ = evenC₁ := Set.ext fun i => by
  change (∃ a, evenSites₁ a = i) ↔ i.val < 3
  revert i
  decide

theorem evenSites₂_range : Set.range evenSites₂ = evenC₂ := Set.ext fun i => by
  change (∃ a, evenSites₂ a = i) ↔ 3 ≤ i.val
  revert i
  decide

/-- A network for `M(C₁)`, `M(C₂)`, which are the same matrix, with root `000` and two recombination nodes. -/
def evenCompNet : NetSpec 3 10 11 :=
  ⟨[0, 0, 1, 1, 2, 2, 3, 0, 5, 3, 4],
   [1, 2, 3, 4, 4, 5, 5, 6, 7, 8, 9],
   [0, 1, 2],
   [0, 1, 2, 5, 3, 6, 0, 6, 5, 3]⟩

theorem evenCompNet_valid : evenCompNet.Valid := by decide +kernel

theorem evenCompNet_recombs : evenCompNet.recombs = 2 := by decide +kernel

/-- The codes of the rows of `M(C₁)`, `M(C₂)`. -/
def evenCompCodes : List ℕ := [0, 6, 5, 3]

theorem evenComp_check : LabelSearch.check 3 evenCompCodes 1 = false := by decide +kernel

/-- `R(M(C₁)) = 2`. -/
theorem even_R₁ : R .multiple (restrictRows evenC₁ evenRows) = 2 := by
  rw [R_restrictRows evenSites₁ evenSites₁_strictMono evenSites₁_range]
  exact R_eq_of_spec (s := evenCompNet) (k := 1) evenCompNet_valid (by decide +kernel) trivial evenCompNet_recombs (Mc := evenCompCodes) (by decide +kernel) evenComp_check

/-- `R(M(C₂)) = 2`. -/
theorem even_R₂ : R .multiple (restrictRows evenC₂ evenRows) = 2 := by
  rw [R_restrictRows evenSites₂ evenSites₂_strictMono evenSites₂_range]
  exact R_eq_of_spec (s := evenCompNet) (k := 1) evenCompNet_valid (by decide +kernel) trivial evenCompNet_recombs (Mc := evenCompCodes) (by decide +kernel) evenComp_check

/-- `R_{000}(M(C₁)) ≤ 2`, for `F`. -/
theorem even_RS₁ : RS .multiple (evenC₁.domRestrict fun _ => false) (restrictRows evenC₁ evenRows) ≤ 2 := by
  rw [RS_restrictRows evenSites₁ evenSites₁_strictMono evenSites₁_range, ← evenCompNet_recombs]
  exact NetSpec.RS_le (c := .multiple) evenCompNet_valid (by decide +kernel) trivial (by decide +kernel)

/-- `R_{000}(M(C₂)) ≤ 2`, for `F`. -/
theorem even_RS₂ : RS .multiple (evenC₂.domRestrict fun _ => false) (restrictRows evenC₂ evenRows) ≤ 2 := by
  rw [RS_restrictRows evenSites₂ evenSites₂_strictMono evenSites₂_range, ← evenCompNet_recombs]
  exact NetSpec.RS_le (c := .multiple) evenCompNet_valid (by decide +kernel) trivial (by decide +kernel)

/-- A network for `evenRows`, with three recombination nodes and the root `000000`. -/
def evenNet : NetSpec 6 17 19 :=
  ⟨[0, 0, 1, 1, 2, 2, 3, 5, 4, 7, 6, 7, 0, 9, 6, 5, 8, 4, 3],
   [1, 2, 3, 4, 5, 6, 7, 7, 8, 8, 9, 9, 10, 11, 12, 13, 14, 15, 16],
   [0, 2, 3, 1, 4, 5],
   [0, 1, 8, 3, 5, 24, 40, 18, 6, 48, 0, 48, 40, 24, 6, 5, 3]⟩

theorem evenNet_valid : evenNet.Valid := by decide +kernel

theorem evenNet_derives : evenNet.DerivesCheck evenRows := by decide +kernel

theorem evenNet_recombs : evenNet.recombs = 3 := by decide +kernel

theorem evenNet_root : evenNet.label 0 = fun _ => false := by decide +kernel

/-- The codes of the rows of `evenRows`. -/
def evenCodes : List ℕ := [0, 48, 40, 24, 6, 5, 3]

theorem evenCodes_codesOf : CodesOf evenRows evenCodes := by decide +kernel

theorem even_check : LabelSearch.check 6 evenCodes 2 = false := by decide +kernel

/-- `R(M) = 3`. -/
theorem even_R : R .multiple evenRows = 3 :=
  R_eq_of_spec (s := evenNet) (k := 2) evenNet_valid evenNet_derives trivial evenNet_recombs evenCodes_codesOf even_check

end Gusfield2007
