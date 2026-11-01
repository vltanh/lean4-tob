module

public import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.Analysis.SpecialFunctions.PolarCoord
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
public import Mathlib.MeasureTheory.Integral.Prod

/-!
# Tails of squares of standard Gaussians

The tail of `Z₁² + Z₂²` for independent standard Gaussians (the `χ²` distribution with two degrees of
freedom), by polar coordinates, and positivity and a lower bound for the Gaussian on an interval. The Mills
ratio bounds for the Gaussian tail, and from them the asymptotics of the tail of the square of a Gaussian.

Main results: `ProbabilityTheory.gaussianReal_prod_real_lt_sq_add_sq`,
`ProbabilityTheory.gaussianReal_real_Ioo_pos`, `ProbabilityTheory.gaussianPDFReal_le_gaussianReal_real_Ioo`,
`ProbabilityTheory.gaussianReal_real_Ioi_le_div`, `ProbabilityTheory.mul_gaussianPDFReal_le_gaussianReal_real_Ioi`,
`ProbabilityTheory.gaussianReal_real_lt_sq_isEquivalent`.
-/

@[expose] public noncomputable section

open MeasureTheory Real Set Filter Topology Asymptotics
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

/-! ### The Mills ratio -/

private lemma gaussianPDFReal_zero_one (z : ℝ) :
    gaussianPDFReal 0 1 z = (√(2 * π))⁻¹ * exp (-z ^ 2 / 2) := by
  simp only [gaussianPDFReal, NNReal.coe_one, mul_one, sub_zero]

private lemma real_eq_setIntegral (s : Set ℝ) :
    (gaussianReal 0 1).real s = ∫ z in s, gaussianPDFReal 0 1 z := by
  rw [measureReal_def, gaussianReal_apply_eq_integral _ one_ne_zero, ENNReal.toReal_ofReal]
  exact integral_nonneg fun _ => gaussianPDFReal_nonneg _ _ _

/-- The derivative of the standard Gaussian density. -/
theorem hasDerivAt_gaussianPDFReal (z : ℝ) :
    HasDerivAt (gaussianPDFReal 0 1) (-z * gaussianPDFReal 0 1 z) z := by
  have h1 : HasDerivAt (fun r : ℝ => -r ^ 2 / 2) (-z) z := by
    have := ((hasDerivAt_pow 2 z).neg).div_const 2
    convert this using 1
    simp only [Nat.cast_ofNat, Nat.add_one_sub_one, pow_one]
    ring
  have h2 := (h1.exp).const_mul (√(2 * π))⁻¹
  have hfun : gaussianPDFReal 0 1 = fun r : ℝ => (√(2 * π))⁻¹ * exp (-r ^ 2 / 2) :=
    funext gaussianPDFReal_zero_one
  rw [hfun]
  convert h2 using 1
  ring

/-- The standard Gaussian density tends to `0` at infinity. -/
theorem tendsto_gaussianPDFReal_atTop : Tendsto (gaussianPDFReal 0 1) atTop (𝓝 0) := by
  have h1 : Tendsto (fun r : ℝ => -r ^ 2 / 2) atTop atBot := by
    have : Tendsto (fun r : ℝ => r ^ 2 / 2) atTop atTop :=
      (tendsto_pow_atTop (two_ne_zero)).atTop_div_const (by norm_num)
    refine (tendsto_neg_atTop_atBot.comp this).congr fun r => ?_
    simp only [Function.comp]
    ring
  have h2 := (tendsto_exp_atBot.comp h1).const_mul (√(2 * π))⁻¹
  rw [mul_zero] at h2
  exact h2.congr fun r => (gaussianPDFReal_zero_one r).symm

/-- **The upper Mills ratio bound**: `P(Z > x) ≤ φ(x) / x`, for `x > 0`. -/
theorem gaussianReal_real_Ioi_le_div {x : ℝ} (hx : 0 < x) :
    (gaussianReal 0 1).real (Ioi x) ≤ gaussianPDFReal 0 1 x / x := by
  set g' : ℝ → ℝ := fun z => z * gaussianPDFReal 0 1 z / x with hg'
  have hderiv : ∀ z ∈ Ici x, HasDerivAt (fun r => -(gaussianPDFReal 0 1 r / x)) (g' z) z := by
    intro z _
    convert ((hasDerivAt_gaussianPDFReal z).div_const x).neg using 1
    simp only [hg']
    ring
  have hpos : ∀ z ∈ Ioi x, 0 ≤ g' z := fun z hz =>
    div_nonneg (mul_nonneg (hx.le.trans (le_of_lt hz)) (gaussianPDFReal_nonneg _ _ _)) hx.le
  have hlim : Tendsto (fun r => -(gaussianPDFReal 0 1 r / x)) atTop (𝓝 0) := by
    simpa using (tendsto_gaussianPDFReal_atTop.div_const x).neg
  have hint := integral_Ioi_of_hasDerivAt_of_nonneg' hderiv hpos hlim
  have hint' := integrableOn_Ioi_deriv_of_nonneg' hderiv hpos hlim
  rw [real_eq_setIntegral]
  calc ∫ z in Ioi x, gaussianPDFReal 0 1 z ≤ ∫ z in Ioi x, g' z := by
        refine setIntegral_mono_on (integrable_gaussianPDFReal _ _).integrableOn hint'
          measurableSet_Ioi fun z hz => ?_
        have hzx : 1 ≤ z / x := (one_le_div hx).2 (le_of_lt hz)
        have hφ := gaussianPDFReal_nonneg 0 1 z
        simp only [hg']
        have : z * gaussianPDFReal 0 1 z / x = z / x * gaussianPDFReal 0 1 z := by ring
        rw [this]
        nlinarith
    _ = gaussianPDFReal 0 1 x / x := by
        rw [hint]
        ring

/-- **The lower Mills ratio bound**: `x / (1 + x²) · φ(x) ≤ P(Z > x)`, for `x ≥ 1`. -/
theorem mul_gaussianPDFReal_le_gaussianReal_real_Ioi {x : ℝ} (hx : 1 ≤ x) :
    x / (1 + x ^ 2) * gaussianPDFReal 0 1 x ≤ (gaussianReal 0 1).real (Ioi x) := by
  set g' : ℝ → ℝ := fun z => (1 - 2 / (1 + z ^ 2) ^ 2) * gaussianPDFReal 0 1 z with hg'
  have hne : ∀ z : ℝ, 1 + z ^ 2 ≠ 0 := fun z => by positivity
  have hderiv : ∀ z ∈ Ici x, HasDerivAt (fun r => -(r / (1 + r ^ 2) * gaussianPDFReal 0 1 r)) (g' z) z := by
    intro z _
    have h1 : HasDerivAt (fun r : ℝ => 1 + r ^ 2) (2 * z) z := by
      simpa using (hasDerivAt_pow 2 z).const_add 1
    have h2 : HasDerivAt (fun r => -(r / (1 + r ^ 2) * gaussianPDFReal 0 1 r))
        (-((1 * (1 + z ^ 2) - z * (2 * z)) / (1 + z ^ 2) ^ 2 * gaussianPDFReal 0 1 z +
          z / (1 + z ^ 2) * (-z * gaussianPDFReal 0 1 z))) z :=
      (((hasDerivAt_id' z).div h1 (hne z)).mul (hasDerivAt_gaussianPDFReal z)).neg
    convert h2 using 1
    simp only [hg']
    have := hne z
    field_simp
    ring
  have hpos : ∀ z ∈ Ioi x, 0 ≤ g' z := by
    intro z hz
    have hz1 : 1 ≤ z := hx.trans (le_of_lt hz)
    refine mul_nonneg ?_ (gaussianPDFReal_nonneg _ _ _)
    have h1 : (2 : ℝ) ≤ 1 + z ^ 2 := by nlinarith
    have h2 : (2 : ℝ) ≤ (1 + z ^ 2) ^ 2 := by nlinarith
    have h3 : 2 / (1 + z ^ 2) ^ 2 ≤ 1 := (div_le_one (by positivity)).2 h2
    linarith
  have hlim : Tendsto (fun r => -(r / (1 + r ^ 2) * gaussianPDFReal 0 1 r)) atTop (𝓝 0) := by
    have hlow : Tendsto (fun r => -gaussianPDFReal 0 1 r) atTop (𝓝 0) := by
      simpa using tendsto_gaussianPDFReal_atTop.neg
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow tendsto_const_nhds ?_ ?_
    · filter_upwards [eventually_ge_atTop 0] with r hr
      have hφ := gaussianPDFReal_nonneg 0 1 r
      have h1 : r / (1 + r ^ 2) ≤ 1 := (div_le_one (by positivity)).2 (by nlinarith [sq_nonneg (r - 1)])
      nlinarith
    · filter_upwards [eventually_ge_atTop 0] with r hr
      have hφ := gaussianPDFReal_nonneg 0 1 r
      have h1 : 0 ≤ r / (1 + r ^ 2) := by positivity
      nlinarith [mul_nonneg h1 hφ]
  have hint := integral_Ioi_of_hasDerivAt_of_nonneg' hderiv hpos hlim
  have hint' := integrableOn_Ioi_deriv_of_nonneg' hderiv hpos hlim
  rw [real_eq_setIntegral]
  calc x / (1 + x ^ 2) * gaussianPDFReal 0 1 x = ∫ z in Ioi x, g' z := by
        rw [hint]
        ring
    _ ≤ ∫ z in Ioi x, gaussianPDFReal 0 1 z := by
        refine setIntegral_mono_on hint' (integrable_gaussianPDFReal _ _).integrableOn
          measurableSet_Ioi fun z _ => ?_
        have hφ := gaussianPDFReal_nonneg 0 1 z
        have h3 : 0 ≤ 2 / (1 + z ^ 2) ^ 2 := by positivity
        simp only [hg']
        nlinarith

/-- The tail of `Z²` at `x²` is twice the tail of `Z` at `x`, by symmetry. -/
theorem gaussianReal_real_lt_sq_eq {x : ℝ} (hx : 0 ≤ x) :
    (gaussianReal 0 1).real {z : ℝ | x ^ 2 < z ^ 2} = 2 * (gaussianReal 0 1).real (Ioi x) := by
  have hset : {z : ℝ | x ^ 2 < z ^ 2} = Ioi x ∪ Iio (-x) := by
    ext z
    simp only [mem_ofPred_eq, mem_union, mem_Ioi, mem_Iio]
    constructor
    · intro h
      by_contra hcon
      push Not at hcon
      have := sq_le_sq' hcon.2 hcon.1
      linarith
    · rintro (h | h)
      · nlinarith
      · nlinarith
  have hdisj : Disjoint (Ioi x) (Iio (-x)) := by
    rw [Set.disjoint_left]
    intro z h₁ h₂
    have h₃ : x < z := h₁
    have h₄ : z < -x := h₂
    linarith
  have hsymm : (gaussianReal 0 1).real (Iio (-x)) = (gaussianReal 0 1).real (Ioi x) := by
    have h : gaussianReal 0 1 = (gaussianReal 0 1).map (fun y : ℝ => -y) := by
      rw [gaussianReal_map_neg, neg_zero]
    conv_lhs => rw [h]
    rw [measureReal_def, measureReal_def, Measure.map_apply (by fun_prop) measurableSet_Iio]
    congr 2
    ext y
    simp
  rw [hset, measureReal_union hdisj measurableSet_Iio, hsymm]
  ring

/-- `2 φ(√t) / √t = 1 / √(exp t · t · π / 2)`, for `t > 0`. -/
private lemma two_mul_pdf_div_sqrt {t : ℝ} (ht : 0 < t) :
    2 * gaussianPDFReal 0 1 √t / √t = 1 / √(exp t * t * π / 2) := by
  have hst : 0 < √t := Real.sqrt_pos.2 ht
  have hpi : 0 < √(2 * π) := Real.sqrt_pos.2 (by positivity)
  have hexp : exp (t / 2) ^ 2 = exp t := by
    rw [sq, ← Real.exp_add]
    congr 1
    ring
  have hsq : exp t * t * π / 2 = (exp (t / 2) * √t * (√(2 * π) / 2)) ^ 2 := by
    rw [mul_pow, mul_pow, div_pow, Real.sq_sqrt ht.le, Real.sq_sqrt (by positivity), hexp]
    ring
  rw [hsq, Real.sqrt_sq (by positivity), gaussianPDFReal_zero_one, Real.sq_sqrt ht.le,
    show -t / 2 = -(t / 2) by ring, Real.exp_neg]
  have := (Real.exp_pos (t / 2)).ne'
  field_simp

/-- **The tail of `Z²`, asymptotically**: `P(Z² > t) ∼ 1 / √(exp t · t · π / 2)`, by the Mills ratio bounds. -/
theorem gaussianReal_real_lt_sq_isEquivalent :
    (fun t : ℝ => (gaussianReal 0 1).real {z : ℝ | t < z ^ 2}) ~[atTop]
      fun t => 1 / √(exp t * t * π / 2) := by
  refine isEquivalent_of_tendsto_one ?_
  have hlow : Tendsto (fun t : ℝ => 1 - (1 + t)⁻¹) atTop (𝓝 1) := by
    have h1 : Tendsto (fun t : ℝ => 1 + t) atTop atTop := tendsto_atTop_add_const_left _ _ tendsto_id
    simpa using tendsto_const_nhds.sub (tendsto_inv_atTop_zero.comp h1)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow tendsto_const_nhds ?_ ?_
  all_goals
    filter_upwards [eventually_ge_atTop 1] with t ht
    have ht0 : 0 < t := by linarith
    have hst : 0 < √t := Real.sqrt_pos.2 ht0
    have hst1 : 1 ≤ √t := Real.one_le_sqrt.2 ht
    have hsq : √t ^ 2 = t := Real.sq_sqrt ht0.le
    have hpdf : 0 < gaussianPDFReal 0 1 √t := gaussianPDFReal_pos _ _ _ one_ne_zero
    have hmain : (gaussianReal 0 1).real {z : ℝ | t < z ^ 2} =
        2 * (gaussianReal 0 1).real (Ioi √t) := by
      conv_lhs => rw [← hsq]
      exact gaussianReal_real_lt_sq_eq hst.le
    have hup := gaussianReal_real_Ioi_le_div hst
    have hlo := mul_gaussianPDFReal_le_gaussianReal_real_Ioi hst1
    rw [hsq] at hlo
    simp only [Pi.div_apply]
    rw [← two_mul_pdf_div_sqrt ht0, hmain]
  · rw [le_div_iff₀ (by positivity)]
    have hd : (0 : ℝ) < 1 + t := by linarith
    have hkey : (1 - (1 + t)⁻¹) * (2 * gaussianPDFReal 0 1 √t / √t) =
        2 * (√t / (1 + t) * gaussianPDFReal 0 1 √t) := by
      field_simp
      ring_nf
      rw [hsq]
    rw [hkey]
    linarith
  · rw [div_le_one (by positivity)]
    have hkey : 2 * gaussianPDFReal 0 1 √t / √t = 2 * (gaussianPDFReal 0 1 √t / √t) := by ring
    rw [hkey]
    linarith

end ProbabilityTheory
