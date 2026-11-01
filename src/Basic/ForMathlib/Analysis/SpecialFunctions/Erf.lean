module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

/-!
# The real error function

## Main results

* `Real.erf`, `Real.hasDerivAt_erf`, `Real.continuous_erf`, `Real.monotone_erf`.
* `Real.tendsto_erf_atTop`, `Real.erf_le_one`: its limit at infinity.
-/

@[expose] public section

namespace Real

/-- The real error function, normalized so its limit at positive infinity is one. -/
noncomputable def erf (x : ℝ) : ℝ :=
  2 / Real.sqrt Real.pi * ∫ t in (0 : ℝ)..x, Real.exp (-(t ^ 2))

/-- The derivative of the error function. -/
theorem hasDerivAt_erf (x : ℝ) :
    HasDerivAt erf (2 / Real.sqrt Real.pi * Real.exp (-(x ^ 2))) x := by
  have hc : Continuous fun t : ℝ => Real.exp (-(t ^ 2)) := by fun_prop
  exact (intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable _ _)
    (hc.stronglyMeasurableAtFilter _ _) hc.continuousAt).const_mul _

theorem continuous_erf : Continuous erf :=
  continuous_iff_continuousAt.2 fun x => (hasDerivAt_erf x).continuousAt

theorem monotone_erf : Monotone erf := by
  refine monotone_of_deriv_nonneg (fun x => (hasDerivAt_erf x).differentiableAt) fun x => ?_
  rw [(hasDerivAt_erf x).deriv]
  positivity

/-- The normalization of the error function: its limit at positive infinity is one. -/
theorem tendsto_erf_atTop : Filter.Tendsto erf Filter.atTop (nhds 1) := by
  have hint : MeasureTheory.IntegrableOn (fun t : ℝ => Real.exp (-(t ^ 2))) (Set.Ioi 0) := by
    have := (integrable_exp_neg_mul_sq (b := 1) one_pos).integrableOn (s := Set.Ioi 0)
    simpa [neg_mul] using this
  have hlim := MeasureTheory.intervalIntegral_tendsto_integral_Ioi (0 : ℝ) hint Filter.tendsto_id
  have hval : ∫ t in Set.Ioi (0 : ℝ), Real.exp (-(t ^ 2)) = Real.sqrt Real.pi / 2 := by
    have := integral_gaussian_Ioi 1
    simpa [neg_mul] using this
  rw [hval] at hlim
  have hpi : Real.sqrt Real.pi ≠ 0 := (Real.sqrt_pos.2 Real.pi_pos).ne'
  have := hlim.const_mul (2 / Real.sqrt Real.pi)
  have h1 : 2 / Real.sqrt Real.pi * (Real.sqrt Real.pi / 2) = 1 := by field_simp
  rw [h1] at this
  exact this

theorem erf_le_one (x : ℝ) : erf x ≤ 1 :=
  monotone_erf.ge_of_tendsto tendsto_erf_atTop x

end Real
