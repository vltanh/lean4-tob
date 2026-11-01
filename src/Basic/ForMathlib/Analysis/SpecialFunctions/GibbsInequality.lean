module

public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Analysis.SpecialFunctions.Exponential
public import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset

/-!
# The maximum of a multinomial likelihood

## Main results

* `Real.prod_pow_le_prod_div_pow`: `∏ p i ^ m i`, for a subprobability vector `p`, is at most its value at
  the frequencies `m i / ∑ m`.
-/

@[expose] public section

open Finset

namespace Real

/-- **Gibbs' inequality** for a multinomial likelihood. -/
theorem prod_pow_le_prod_div_pow {ι : Type*} [Fintype ι] (m : ι → ℕ) {p : ι → ℝ}
    (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i ≤ 1) (hN : 0 < ∑ i, (m i : ℝ)) :
    ∏ i, p i ^ m i ≤ ∏ i, ((m i : ℝ) / ∑ j, (m j : ℝ)) ^ m i := by
  set N : ℝ := ∑ j, (m j : ℝ) with hNdef
  have hone : ∀ i, p i ^ m i ≤ ((m i : ℝ) / N) ^ m i * exp (N * p i - m i) := by
    intro i
    rcases Nat.eq_zero_or_pos (m i) with h | h
    · simp only [h, pow_zero, one_mul, Nat.cast_zero, sub_zero]
      exact one_le_exp (mul_nonneg hN.le (hp i))
    · have hmi : (0 : ℝ) < m i := by exact_mod_cast h
      have hq : 0 < (m i : ℝ) / N := div_pos hmi hN
      set q := (m i : ℝ) / N with hqdef
      have hx : p i / q ≤ exp (p i / q - 1) := by
        have := add_one_le_exp (p i / q - 1)
        linarith
      have hpow : (p i / q) ^ m i ≤ exp (p i / q - 1) ^ m i :=
        pow_le_pow_left₀ (div_nonneg (hp i) hq.le) hx _
      have hexp : exp (p i / q - 1) ^ m i = exp (N * p i - m i) := by
        rw [← exp_nat_mul]
        congr 1
        rw [hqdef]
        field_simp
      rw [hexp] at hpow
      calc p i ^ m i = q ^ m i * (p i / q) ^ m i := by
            rw [← mul_pow]
            congr 1
            field_simp
        _ ≤ q ^ m i * exp (N * p i - m i) := by gcongr
  have hprod : ∏ i, p i ^ m i ≤ ∏ i, (((m i : ℝ) / N) ^ m i * exp (N * p i - m i)) :=
    Finset.prod_le_prod₀ (fun i _ ↦ pow_nonneg (hp i) _) fun i _ ↦ hone i
  rw [Finset.prod_mul_distrib, ← exp_sum] at hprod
  have hle : ∑ i, (N * p i - m i) ≤ 0 := by
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← hNdef]
    nlinarith
  have hexp : exp (∑ i, (N * p i - m i)) ≤ 1 := exp_le_one_iff.2 hle
  have hnn : 0 ≤ ∏ i, ((m i : ℝ) / N) ^ m i :=
    Finset.prod_nonneg fun i _ ↦ pow_nonneg (div_nonneg (Nat.cast_nonneg _) hN.le) _
  nlinarith

end Real
