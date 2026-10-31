module

public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.Analysis.SpecialFunctions.PolarCoord
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
public import Mathlib.MeasureTheory.Integral.Prod

/-!
# Tails of squares of standard Gaussians

The tail of `Z₁² + Z₂²` for independent standard Gaussians (the `χ²` distribution with two degrees of
freedom), by polar coordinates, and positivity and a lower bound for the Gaussian on an interval.

Main results: `ProbabilityTheory.gaussianReal_prod_real_lt_sq_add_sq`,
`ProbabilityTheory.gaussianReal_real_Ioo_pos`, `ProbabilityTheory.gaussianPDFReal_le_gaussianReal_real_Ioo`.
-/

@[expose] public noncomputable section

open MeasureTheory Real Set Filter Topology
open scoped ENNReal

namespace ProbabilityTheory

private lemma pdf_mul_pdf (x y : ℝ) :
    gaussianPDFReal 0 1 x * gaussianPDFReal 0 1 y = (2 * π)⁻¹ * exp (-(x ^ 2 + y ^ 2) / 2) := by
  have h2pi : 0 ≤ 2 * π := by positivity
  simp only [gaussianPDFReal, NNReal.coe_one, mul_one, sub_zero]
  have : (√(2 * π))⁻¹ * rexp (-x ^ 2 / 2) * ((√(2 * π))⁻¹ * rexp (-y ^ 2 / 2)) =
      ((√(2 * π)) * (√(2 * π)))⁻¹ * (rexp (-x ^ 2 / 2) * rexp (-y ^ 2 / 2)) := by
    rw [mul_inv]; ring
  rw [this, Real.mul_self_sqrt h2pi, ← Real.exp_add]
  congr 2
  ring

/-- `∫_a^∞ r exp(-r²/2) dr = exp(-a²/2)`. -/
private lemma integral_Ioi_mul_exp (a : ℝ) (ha : 0 ≤ a) :
    ∫ r in Ioi a, r * exp (-r ^ 2 / 2) = exp (-a ^ 2 / 2) := by
  have hderiv : ∀ x ∈ Ici a, HasDerivAt (fun r : ℝ => -exp (-r ^ 2 / 2)) (x * exp (-x ^ 2 / 2)) x := by
    intro x _
    have h1 : HasDerivAt (fun r : ℝ => -r ^ 2 / 2) (-x) x := by
      have := ((hasDerivAt_pow 2 x).neg).div_const 2
      convert this using 1
      simp only [Nat.cast_ofNat, Nat.add_one_sub_one, pow_one]
      ring
    have h2 := (h1.exp).neg
    convert h2 using 1
    ring
  have hpos : ∀ x ∈ Ioi a, 0 ≤ x * exp (-x ^ 2 / 2) := fun x hx =>
    mul_nonneg (ha.trans (le_of_lt hx)) (exp_pos _).le
  have hlim : Tendsto (fun r : ℝ => -exp (-r ^ 2 / 2)) atTop (𝓝 0) := by
    have h1 : Tendsto (fun r : ℝ => -r ^ 2 / 2) atTop atBot := by
      have : Tendsto (fun r : ℝ => r ^ 2 / 2) atTop atTop :=
        (tendsto_pow_atTop (two_ne_zero)).atTop_div_const (by norm_num)
      refine (tendsto_neg_atTop_atBot.comp this).congr fun r => ?_
      simp only [Function.comp]
      ring
    simpa using (tendsto_exp_atBot.comp h1).neg
  have := integral_Ioi_of_hasDerivAt_of_nonneg' hderiv hpos hlim
  rw [this]
  ring

/-- The tail of `Z₁² + Z₂²` for independent standard Gaussians: the `χ²` distribution with two degrees
of freedom is exponential, by polar coordinates. -/
theorem gaussianReal_prod_real_lt_sq_add_sq {t : ℝ} (ht : 0 ≤ t) :
    ((gaussianReal 0 1).prod (gaussianReal 0 1)).real {z : ℝ × ℝ | t < z.1 ^ 2 + z.2 ^ 2} =
      exp (-t / 2) := by
  set S := {z : ℝ × ℝ | t < z.1 ^ 2 + z.2 ^ 2} with hSdef
  have hS : MeasurableSet S := measurableSet_lt measurable_const (by fun_prop)
  set F : ℝ × ℝ → ℝ := fun z => gaussianPDFReal 0 1 z.1 * gaussianPDFReal 0 1 z.2 with hF
  have hFnn : ∀ z, 0 ≤ F z := fun z =>
    mul_nonneg (gaussianPDFReal_nonneg _ _ _) (gaussianPDFReal_nonneg _ _ _)
  have hFm : Measurable F :=
    ((measurable_gaussianPDFReal 0 1).comp measurable_fst).mul
      ((measurable_gaussianPDFReal 0 1).comp measurable_snd)
  have hprod : (gaussianReal 0 1).prod (gaussianReal 0 1) =
      (volume : Measure (ℝ × ℝ)).withDensity fun z => ENNReal.ofReal (F z) := by
    rw [gaussianReal_of_var_ne_zero _ one_ne_zero, Measure.volume_eq_prod,
      prod_withDensity (measurable_gaussianPDF _ _) (measurable_gaussianPDF _ _)]
    congr 1
    funext z
    simp only [hF, gaussianPDF]
    rw [ENNReal.ofReal_mul (gaussianPDFReal_nonneg _ _ _)]
  have h1 : ((gaussianReal 0 1).prod (gaussianReal 0 1)).real S = ∫ z, S.indicator F z := by
    rw [hprod, measureReal_def, withDensity_apply _ hS, integral_indicator hS,
      integral_eq_lintegral_of_nonneg_ae (ae_of_all _ hFnn) hFm.aestronglyMeasurable]
  rw [h1, ← integral_comp_polarCoord_symm]
  have hint : ∀ p ∈ polarCoord.target, p.1 • S.indicator F (polarCoord.symm p) =
      ((2 * π)⁻¹ * (Ioi (√t)).indicator (fun r => r * exp (-r ^ 2 / 2)) p.1) * 1 := by
    rintro ⟨r, θ⟩ hp
    have hr : 0 < r := hp.1
    have hsq : (r * cos θ) ^ 2 + (r * sin θ) ^ 2 = r ^ 2 := by
      have := sin_sq_add_cos_sq θ
      nlinarith [this]
    have hmem : (polarCoord.symm (r, θ)) ∈ S ↔ r ∈ Ioi (√t) := by
      simp only [hSdef, polarCoord, mem_ofPred_eq, mem_Ioi]
      show t < (r * cos θ) ^ 2 + (r * sin θ) ^ 2 ↔ _
      rw [hsq, Real.sqrt_lt' hr]
    by_cases h : r ∈ Ioi (√t)
    · rw [indicator_of_mem (hmem.2 h), indicator_of_mem h]
      simp only [hF, smul_eq_mul, mul_one]
      rw [pdf_mul_pdf]
      show r * ((2 * π)⁻¹ * exp (-((r * cos θ) ^ 2 + (r * sin θ) ^ 2) / 2)) = _
      rw [hsq]
      ring
    · rw [indicator_of_notMem (fun h' => h (hmem.1 h')), indicator_of_notMem h]
      simp
  rw [setIntegral_congr_fun polarCoord.open_target.measurableSet hint, polarCoord_target,
    Measure.volume_eq_prod,
    setIntegral_prod_mul (fun r => (2 * π)⁻¹ * (Ioi (√t)).indicator (fun r => r * exp (-r ^ 2 / 2)) r)
      (fun _ => (1 : ℝ)) (Ioi 0) (Ioo (-π) π), integral_const_mul,
    setIntegral_indicator measurableSet_Ioi, Ioi_inter_Ioi, sup_of_le_right (sqrt_nonneg t),
    integral_Ioi_mul_exp _ (sqrt_nonneg t), Real.sq_sqrt ht, setIntegral_const,
    measureReal_def, Real.volume_Ioo, ENNReal.toReal_ofReal (by linarith [pi_pos])]
  have : π ≠ 0 := pi_ne_zero
  simp only [smul_eq_mul, mul_one]
  field_simp
  ring

/-- The standard Gaussian gives positive probability to a nonempty open interval. -/
theorem gaussianReal_real_Ioo_pos {a b : ℝ} (hab : a < b) :
    0 < (gaussianReal 0 1).real (Ioo a b) := by
  rw [measureReal_def]
  refine ENNReal.toReal_pos (fun h => ?_) (measure_ne_top _ _)
  have := gaussianReal_absolutelyContinuous' 0 (v := 1) one_ne_zero h
  rw [Real.volume_Ioo, ENNReal.ofReal_eq_zero] at this
  linarith

/-- The standard Gaussian on `(a, a + 1)`, `a ≥ 0`, is at least its density at `a + 1`. -/
theorem gaussianPDFReal_le_gaussianReal_real_Ioo {a : ℝ} (ha : 0 ≤ a) :
    gaussianPDFReal 0 1 (a + 1) ≤ (gaussianReal 0 1).real (Ioo a (a + 1)) := by
  have h1 : (gaussianReal 0 1).real (Ioo a (a + 1)) = ∫ x in Ioo a (a + 1), gaussianPDFReal 0 1 x := by
    rw [measureReal_def, gaussianReal_apply_eq_integral _ one_ne_zero, ENNReal.toReal_ofReal]
    exact setIntegral_nonneg measurableSet_Ioo fun x _ => gaussianPDFReal_nonneg _ _ _
  rw [h1]
  have hvol : volume.real (Ioo a (a + 1)) = 1 := by
    rw [measureReal_def, Real.volume_Ioo]; simp
  have h2 : ∫ _x in Ioo a (a + 1), gaussianPDFReal 0 1 (a + 1) = gaussianPDFReal 0 1 (a + 1) := by
    rw [setIntegral_const, hvol, one_smul]
  conv_lhs => rw [← h2]
  refine setIntegral_mono_on ?_ (integrable_gaussianPDFReal _ _).integrableOn measurableSet_Ioo
    fun x hx => ?_
  · exact integrableOn_const (by simp) (by simp)
  simp only [gaussianPDFReal, NNReal.coe_one, mul_one, sub_zero]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  rw [exp_le_exp]
  have h3 : x ^ 2 ≤ (a + 1) ^ 2 := pow_le_pow_left₀ (ha.trans hx.1.le) hx.2.le 2
  linarith

end ProbabilityTheory
