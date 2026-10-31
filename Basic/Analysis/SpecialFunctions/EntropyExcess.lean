module

public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog

/-!
# The second-order expansion of `x log x`

`entropyExcess v = (1 + v) log (1 + v) - v` is `x log x` at `x = 1 + v` minus its tangent line at `1`.
It is nonnegative, positive off `0`, and `v²/2` up to a cubic error (`abs_entropyExcess_sub_le`). All
likelihood ratio statistics of the trinomial are sums of such terms.
-/

@[expose] public noncomputable section

namespace Real

/-- `x log x` at `x = 1 + v` minus its tangent line at `1`. -/
def entropyExcess (v : ℝ) : ℝ := (1 + v) * log (1 + v) - v

theorem entropyExcess_pos {v : ℝ} (hv : -1 < v) (hne : v ≠ 0) : 0 < entropyExcess v := by
  have hpos : 0 < 1 + v := by linarith
  have hy : 0 < (1 + v)⁻¹ := inv_pos.2 hpos
  have hy1 : (1 + v)⁻¹ ≠ 1 := by
    intro h
    apply hne
    have := inv_eq_one.1 h
    linarith
  have h := log_lt_sub_one_of_pos hy hy1
  rw [log_inv] at h
  have h' : (1 + v) * (-log (1 + v)) < (1 + v) * ((1 + v)⁻¹ - 1) := mul_lt_mul_of_pos_left h hpos
  rw [mul_sub, mul_inv_cancel₀ hpos.ne'] at h'
  unfold entropyExcess
  nlinarith

theorem entropyExcess_zero : entropyExcess 0 = 0 := by
  simp [entropyExcess]

theorem entropyExcess_nonneg {v : ℝ} (hv : -1 ≤ v) : 0 ≤ entropyExcess v := by
  rcases hv.eq_or_lt with rfl | hv
  · simp [entropyExcess]
  · rcases eq_or_ne v 0 with rfl | hne
    · rw [entropyExcess_zero]
    · exact (entropyExcess_pos hv hne).le

/-- The second-order expansion at `0`. -/
theorem abs_entropyExcess_sub_le {v : ℝ} (hv : |v| ≤ 1 / 2) :
    |entropyExcess v - v ^ 2 / 2| ≤ 4 * |v| ^ 3 := by
  have hx : |(-v)| < 1 := by rw [abs_neg]; linarith
  have h := abs_log_sub_add_sum_range_le hx 2
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, sub_neg_eq_add, abs_neg] at h
  norm_num at h
  set e : ℝ := -v + v ^ 2 / 2 + log (1 + v) with he
  have hdenom : 0 < 1 - |v| := by linarith
  have hbound : |e| ≤ 2 * |v| ^ 3 := by
    refine h.trans ?_
    rw [div_le_iff₀ hdenom]
    have : 0 ≤ |v| ^ 3 := by positivity
    nlinarith
  have hlog : log (1 + v) = v - v ^ 2 / 2 + e := by rw [he]; ring
  have hexp : entropyExcess v - v ^ 2 / 2 = -(v * v ^ 2) / 2 + (1 + v) * e := by
    unfold entropyExcess
    rw [hlog]
    ring
  rw [hexp]
  have h₁ : |-(v * v ^ 2) / 2| = |v| ^ 3 / 2 := by
    rw [abs_div, abs_neg, abs_mul, abs_pow]
    simp only [abs_two]
    ring
  have h₂ : |(1 + v) * e| ≤ 3 / 2 * (2 * |v| ^ 3) := by
    rw [abs_mul]
    refine mul_le_mul ?_ hbound (abs_nonneg _) (by norm_num)
    have := (abs_add_le 1 v)
    simp only [abs_one] at this
    linarith
  have h₃ := abs_add_le (-(v * v ^ 2) / 2) ((1 + v) * e)
  have h₄ : 0 ≤ |v| ^ 3 := by positivity
  rw [h₁] at h₃
  linarith

end Real
