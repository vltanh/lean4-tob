module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Tactic.NormNum

/-! Exact checks of the margin problem in TOB-QMC Supplement Lemma 4.
These verify the algebra and the standard quartet-CF formula's specialization;
they do not constitute a formal construction of the multispecies coalescent. -/

public section

namespace TOBQMCGapCheck

noncomputable section

/-- Supplement Equation (1), including all three pairs. -/
def pairwiseGap (p₁ p₂ p₃ : ℝ) : ℝ :=
  min |p₁ - p₂| (min |p₁ - p₃| |p₂ - p₃|)

/-- Every strictly cut CF has a zero minimum over all coordinate pairs. -/
theorem pairwiseGap_repeated (a b : ℝ) : pairwiseGap a b b = 0 := by
  unfold pairwiseGap
  simp only [sub_self, abs_zero]
  rw [min_eq_right (abs_nonneg (a - b)), min_eq_right (abs_nonneg (a - b))]

theorem example_is_positive_normalized_and_strictly_dominant :
    (0 : ℝ) < 1 / 2 ∧ (0 : ℝ) < 1 / 4 ∧
      (1 / 2 : ℝ) + 1 / 4 + 1 / 4 = 1 ∧ (1 / 4 : ℝ) < 1 / 2 := by
  norm_num

theorem example_gap_zero : pairwiseGap (1 / 2) (1 / 4) (1 / 4) = 0 :=
  pairwiseGap_repeated _ _

/-- The intended dominant-versus-alternative margin is positive in this example. -/
theorem dominant_gap_example :
    min ((1 / 2 : ℝ) - 1 / 4) ((1 / 2 : ℝ) - 1 / 4) = 1 / 4 := by
  norm_num

/-- The printed strict accuracy hypothesis has no instances in the example. -/
theorem no_error_less_than_printed_radius (observed expected : ℝ) (M : ℕ) :
    ¬ |observed - expected| < pairwiseGap (1 / 2) (1 / 4) (1 / 4) / (2 * (M : ℝ)) := by
  rw [example_gap_zero, zero_div]
  exact not_lt_of_ge (abs_nonneg _)

/-- A positive internal tree length realizing the example under the standard
quartet MSC formula. The coalescent formula itself is not proved in this file. -/
theorem positive_internal_length : 0 < Real.log (4 / 3 : ℝ) :=
  Real.log_pos (by norm_num)

theorem survival_at_internal_length :
    Real.exp (-Real.log (4 / 3 : ℝ)) = 3 / 4 := by
  rw [Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 4 / 3)]
  norm_num

theorem standard_tree_cf_specialization :
    1 - 2 / 3 * Real.exp (-Real.log (4 / 3 : ℝ)) = 1 / 2 ∧
      1 / 3 * Real.exp (-Real.log (4 / 3 : ℝ)) = 1 / 4 := by
  rw [survival_at_internal_length]
  norm_num

end
end TOBQMCGapCheck

#print axioms TOBQMCGapCheck.pairwiseGap_repeated
#print axioms TOBQMCGapCheck.no_error_less_than_printed_radius
#print axioms TOBQMCGapCheck.standard_tree_cf_specialization
