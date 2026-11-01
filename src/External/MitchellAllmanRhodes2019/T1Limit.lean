module

public import External.MitchellAllmanRhodes2019.T3Limit

/-!
# Mitchell, Allman, Rhodes 2019, Propositions 5.1 and 5.2: the T1 test

Proposition 5.1, for the trinomial: the likelihood ratio statistic of model T1 and the variable `t1Var` under `N((0, μ₀(n)), I)`
converge in distribution to the same limit (`External.MitchellAllmanRhodes2019.proposition5_1`). On a sample of gene trees this is
`QuartetTests.t1Stat_limitLaw`, at the boundary point `(1/3, 1/3, 1/3)`, and `QuartetTests.t1Stat_limitLaw_of_isT1Strict` off it. The
statistic is the likelihood ratio statistic: `Trinomial.t1S_eq_likelihoodRatio`.

Proposition 5.2: the law of `t1Var` has the printed density, with the modified Struve function `struveM₀`
(`QuartetTests.t1Var_density`, also `External.MitchellAllmanRhodes2019.proposition5_2`).

What the source says after it is also here: at `μ₀ = 0` the law is `½ χ²₁ + ½ χ²₂` (`QuartetTests.t1Density_zero`,
`QuartetTests.t1Tail_zero`), and as `n → ∞`, since `M₀(x) → 0` (`QuartetTests.tendsto_struveM₀_atTop`), the density tends to that of
`χ²₁` (`QuartetTests.tendsto_t1Density_atTop`).

The proof of Proposition 5.2 follows the source's Appendix C: by the reflection about the vertical axis, `g_X = 2 d/dx G₁ + d/dx G₂`,
with `G₁` the strip `0 < x₁ ≤ x`, `y > 0`, and `G₂` the semi-disc below the origin, in polar coordinates, and a change of
variables to `M₀` (`QuartetTests.T1Pdf.integral_exp_mul_sin`).

Correction to the source: in the first display of Appendix C, the second line for `d/dx G₁` repeats the line for `d/dx G₂`, a misprint.
The value that the first line gives, and that the source's sum uses, is `(1 / 2π) exp (-x² / 2) √(2π) ½ (1 + erf (μ₀ / √2))`, which is
`T1Pdf.hasDerivAt_G₁`. Appendix C also says that `x` is the distance to the mean `(0, μ₀)`, where it is the distance to the half-line.
Proposition 5.2 holds as printed. The source states it for `φ₀ ∈ (0, 1]`; it holds for every real `μ₀`.

Departure from the source: Proposition 5.1 is taken from its Theorem 3.1, as for Proposition 4.1. See `T3Limit.lean`.

At the boundary point, the p-value `t1PValue` with the fitted parameter is not asymptotically uniform
(`QuartetTests.t1PValue_centroid_not_asymptoticallyUniform`), which makes E13 of the report a theorem, while with the true parameter it
is (`QuartetTests.t1Tail_t1Stat_asymptoticallyUniform`).
-/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal Classical
open External.MitchellAllmanRhodes2019 (normalSample normalSample_map_sub)

namespace Phylogenetics

/-- The modified Struve function `M₀` of Mitchell, Allman, Rhodes 2019, Proposition 5.2, as printed:
`M₀(x) = -(2 / π) ∫_0^{π/2} exp (-x cos θ) dθ`. -/
def struveM₀ (x : ℝ) : ℝ :=
  -(2 / Real.pi) * ∫ θ in (0 : ℝ)..(Real.pi / 2), Real.exp (-x * Real.cos θ)

/-- The variable of Mitchell, Allman, Rhodes 2019, Proposition 5.1, at `(Z, Z̄)`: `Z² + ½ (1 - sgn Z̄) Z̄²`, written as in `t1Tail`. -/
def t1Var (z : ℝ × ℝ) : ℝ := z.1 ^ 2 + if z.2 < 0 then z.2 ^ 2 else 0

/-- The density of Mitchell, Allman, Rhodes 2019, Proposition 5.2, Equation `eq:T1pdf`, as printed, for the mean `μ₀ = μ`; it is `0`
off `λ > 0`, where the source does not give it. -/
def t1Density (μ lam : ℝ) : ℝ :=
  if 0 < lam then
    1 / 4 * Real.exp (-(lam / 2)) *
      (√(2 / (Real.pi * lam)) * (1 + Real.erf (μ / √2)) -
        Real.exp (-(μ ^ 2 / 2)) * struveM₀ (μ * √lam))
  else 0

namespace QuartetTests

/-! ### The Struve function -/

theorem integral_exp_cos_nonneg (x : ℝ) :
    0 ≤ ∫ θ in (0 : ℝ)..(Real.pi / 2), Real.exp (-x * Real.cos θ) :=
  intervalIntegral.integral_nonneg (by positivity) fun _ _ => (Real.exp_pos _).le

theorem struveM₀_nonpos (x : ℝ) : struveM₀ x ≤ 0 := by
  have := integral_exp_cos_nonneg x
  have hπ := Real.pi_pos
  unfold struveM₀
  exact mul_nonpos_of_nonpos_of_nonneg (by simp only [neg_nonpos]; positivity) this

theorem continuous_struveM₀ : Continuous struveM₀ := by
  have hc : Continuous (Function.uncurry fun (x θ : ℝ) => Real.exp (-x * Real.cos θ)) := by
    simp only [Function.uncurry_def]
    fun_prop
  exact continuous_const.mul
    (intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' hc _ _)

theorem struveM₀_zero : struveM₀ 0 = -1 := by
  have hπ := Real.pi_ne_zero
  simp [struveM₀]

/-- "`M₀(x) → 0` as `x → ∞`" (`ext:t1_density_chisq`) (Mitchell, Allman, Rhodes 2019, after Proposition 5.2). -/
theorem tendsto_struveM₀_atTop : Tendsto struveM₀ atTop (𝓝 0) := by
  have hπ := Real.pi_pos
  have hI : Tendsto (fun x : ℝ => ∫ θ in Ioo 0 (Real.pi / 2), Real.exp (-x * Real.cos θ)) atTop
      (𝓝 (∫ _ in Ioo 0 (Real.pi / 2), (0 : ℝ))) := by
    refine tendsto_integral_filter_of_dominated_convergence (fun _ => (1 : ℝ)) ?_ ?_ ?_ ?_
    · exact Eventually.of_forall fun x =>
        (Continuous.aestronglyMeasurable (by fun_prop))
    · filter_upwards [eventually_ge_atTop 0] with x hx
      refine ae_restrict_of_forall_mem measurableSet_Ioo fun θ hθ => ?_
      have hcos : 0 < Real.cos θ := Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1], hθ.2⟩
      rw [Real.norm_of_nonneg (Real.exp_pos _).le, Real.exp_le_one_iff]
      nlinarith [mul_nonneg hx hcos.le]
    · exact integrable_const_iff.2 (Or.inr (by
        rw [isFiniteMeasure_iff]
        simp))
    · refine ae_restrict_of_forall_mem measurableSet_Ioo fun θ hθ => ?_
      have hcos : 0 < Real.cos θ := Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1], hθ.2⟩
      refine Real.tendsto_exp_atBot.comp ?_
      have : Tendsto (fun x : ℝ => x * Real.cos θ) atTop atTop := tendsto_id.atTop_mul_const hcos
      exact (tendsto_neg_atTop_atBot.comp this).congr fun x => by
        simp only [Function.comp]
        ring
  have hrw : struveM₀ = fun x : ℝ => -(2 / Real.pi) *
      ∫ θ in Ioo 0 (Real.pi / 2), Real.exp (-x * Real.cos θ) := by
    funext x
    rw [struveM₀, intervalIntegral.integral_of_le (by positivity), integral_Ioc_eq_integral_Ioo]
  rw [hrw]
  simpa using hI.const_mul (-(2 / Real.pi))

/-! ### The variable -/

theorem t1Var_eq_sqDistHalfLine (z : ℝ × ℝ) : t1Var z = sqDistHalfLine 0 1 z.1 z.2 := by
  unfold t1Var sqDistHalfLine
  by_cases hy : z.2 < 0
  · rw [ite_eq_left hy, ite_eq_right (by linarith)]
  · rw [ite_eq_right hy, ite_eq_left (by linarith [not_lt.1 hy])]
    ring

theorem continuous_t1Var : Continuous t1Var := by
  simp only [funext t1Var_eq_sqDistHalfLine]
  exact continuous_sqDistHalfLine (by norm_num)

theorem t1Var_reflect_x (z : ℝ × ℝ) : t1Var (-z.1, z.2) = t1Var z := by
  simp [t1Var]

theorem t1Tail_eq (μ t : ℝ) : t1Tail μ t = (normalSample μ).real {z | t < t1Var z} := rfl

namespace T1Pdf

/-! ### The source's `g_X = 2 d/dx G₁ + d/dx G₂` -/

/-- The source's region `R₁`, without its bound on the distance: `x > 0`, `y > 0`. -/
def R₁ : Set (ℝ × ℝ) := {z | 0 < z.1 ∧ 0 < z.2}

/-- By the symmetry about the vertical axis, the law of the distance is twice that of `R₁`, and that of the half-plane below. -/
theorem measure_t1Var_le_eq_sum (μ t : ℝ) :
    normalSample μ {z | t1Var z ≤ t} =
      2 * normalSample μ ({z | t1Var z ≤ t} ∩ R₁) +
        normalSample μ ({z | t1Var z ≤ t} ∩ {z | z.2 < 0}) := by
  have hE : MeasurableSet {z | t1Var z ≤ t} :=
    measurableSet_le continuous_t1Var.measurable measurable_const
  have hR : MeasurableSet R₁ :=
    (measurableSet_lt measurable_const measurable_fst).inter
      (measurableSet_lt measurable_const measurable_snd)
  have h₁ := gaussianReal_prod_split (k₁ := 0) (k₂ := 1) (Or.inr one_ne_zero) 0 μ {z | t1Var z ≤ t}
  have h₂ := gaussianReal_prod_split (k₁ := 1) (k₂ := 0) (Or.inl one_ne_zero) 0 μ
    ({z | t1Var z ≤ t} ∩ {z | 0 < z.2})
  have e₁ : {z | t1Var z ≤ t} ∩ {z : ℝ × ℝ | 0 < 0 * z.1 + 1 * z.2} =
      {z | t1Var z ≤ t} ∩ {z | 0 < z.2} := by
    ext z
    simp
  have e₂ : {z | t1Var z ≤ t} ∩ {z : ℝ × ℝ | 0 * z.1 + 1 * z.2 < 0} =
      {z | t1Var z ≤ t} ∩ {z | z.2 < 0} := by
    ext z
    simp
  have e₃ : {z | t1Var z ≤ t} ∩ {z : ℝ × ℝ | 0 < z.2} ∩ {z : ℝ × ℝ | 0 < 1 * z.1 + 0 * z.2} =
      {z | t1Var z ≤ t} ∩ R₁ := by
    ext z
    simp only [mem_inter_iff, mem_ofPred_eq, R₁, one_mul, zero_mul, add_zero]
    tauto
  have e₄ : {z | t1Var z ≤ t} ∩ {z : ℝ × ℝ | 0 < z.2} ∩ {z : ℝ × ℝ | 1 * z.1 + 0 * z.2 < 0} =
      {z | (-z.1, z.2) ∈ {z | t1Var z ≤ t} ∩ R₁} := by
    ext z
    simp only [mem_inter_iff, mem_ofPred_eq, R₁, one_mul, zero_mul, add_zero, t1Var_reflect_x,
      neg_pos]
    tauto
  rw [e₁, e₂] at h₁
  rw [e₃, e₄, measure_reflect_x_preimage μ (hE.inter hR)] at h₂
  rw [h₁, h₂]
  ring

section Polar

open Real

/-- The angles `(0, π / 2)` of `R₁`. -/
theorem sector₁ : IsPolarSector 1 0 (π / 2) 0 := by
  have h := IsPolarSector.right (a := 0) (by linarith [pi_pos]) (by linarith [pi_pos])
  rwa [tan_zero] at h

/-- The first line of the source's display for `d/dx G₁`, corrected: for `x > 0`, it is the density of `x` times `P(Z̄ > 0)`. The second
line of that display repeats the line for `G₂`, a misprint. -/
theorem hasDerivAt_G₁ (μ : ℝ) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (polarStripIntegral 1 0 (π / 2) 0 μ) (stripDensity 0 μ 0 x) x := by
  simpa using sector₁.hasDerivAt_polarStripIntegral_stripDensity 0 μ hx

/-- `G₁`: the probability of the part of `R₁` within distance `√t` of the vertical half-line. -/
theorem measure_inter_R₁ (μ t : ℝ) :
    normalSample μ ({z | t1Var z ≤ t} ∩ R₁) =
      ∫⁻ u in Ioc 0 √t, ENNReal.ofReal (stripDensity 0 μ 0 u) := by
  have hset : {z | t1Var z ≤ t} ∩ R₁ = polarStrip 1 0 √t := by
    ext z
    simp only [mem_inter_iff, mem_ofPred_eq, polarStrip, one_mul, zero_mul, R₁]
    have hv : ∀ hy : 0 < z.2, t1Var z = z.1 ^ 2 := fun hy => by
      rw [t1Var, ite_eq_right (not_lt.2 hy.le), add_zero]
    constructor
    · rintro ⟨hl, hx, hy⟩
      rw [hv hy] at hl
      exact ⟨hx, (Real.le_sqrt' hx).2 hl, hy⟩
    · rintro ⟨hx, hxt, hy⟩
      exact ⟨by rw [hv hy]; exact (Real.le_sqrt' hx).1 hxt, hx, hy⟩
  rw [hset]
  simpa using sector₁.measure_polarStrip_eq_lintegral_stripDensity 0 μ √t

/-- The source's line integral over the semicircle `C₂`, on the angles of Lean's polar coordinates, `(-π, 0)`, where the source has
`(π, 2π)`. -/
def semiDensity (μ r : ℝ) : ℝ :=
  1 / (2 * π) * r * exp (-(1 / 2) * (r ^ 2 + μ ^ 2)) * ∫ θ in (-π)..0, exp (μ * r * sin θ)

/-- The source's change of variables to `M₀`. -/
theorem integral_exp_mul_sin (a : ℝ) : ∫ θ in (-π)..0, exp (a * sin θ) = -π * struveM₀ a := by
  have hc : Continuous fun θ : ℝ => exp (a * sin θ) := by fun_prop
  have h₁ := intervalIntegral.integral_comp_sub_right (a := 0) (b := π / 2)
    (fun θ : ℝ => exp (a * sin θ)) (π / 2)
  have h₂ := intervalIntegral.integral_comp_sub_left (a := 0) (b := π / 2)
    (fun θ : ℝ => exp (a * sin θ)) (-(π / 2))
  have p₁ : ∀ x : ℝ, exp (a * sin (x - π / 2)) = exp (-a * cos x) := fun x => by
    rw [sin_sub_pi_div_two]
    ring_nf
  have p₂ : ∀ x : ℝ, exp (a * sin (-(π / 2) - x)) = exp (-a * cos x) := fun x => by
    rw [show -(π / 2) - x = -(x + π / 2) by ring, sin_neg, sin_add_pi_div_two]
    ring_nf
  simp only [p₁] at h₁
  simp only [p₂] at h₂
  rw [show (0 : ℝ) - π / 2 = -(π / 2) by ring, show π / 2 - π / 2 = (0 : ℝ) by ring] at h₁
  rw [show -(π / 2) - π / 2 = -π by ring, show -(π / 2) - 0 = -(π / 2) by ring] at h₂
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := -(π / 2))
    (hc.intervalIntegrable _ _) (hc.intervalIntegrable _ _), ← h₁, ← h₂, struveM₀]
  have hπ := pi_ne_zero
  field_simp
  ring

theorem semiDensity_eq (μ r : ℝ) :
    semiDensity μ r = 1 / (2 * π) * r * exp (-(1 / 2) * (r ^ 2 + μ ^ 2)) * (-π * struveM₀ (μ * r)) := by
  rw [semiDensity, integral_exp_mul_sin]

theorem semiDensity_nonneg (μ : ℝ) {r : ℝ} (hr : 0 < r) : 0 ≤ semiDensity μ r := by
  rw [semiDensity_eq]
  have := struveM₀_nonpos (μ * r)
  have hπ := pi_pos
  refine mul_nonneg (by positivity) (mul_nonneg_of_nonpos_of_nonpos (by linarith) this)

theorem continuous_semiDensity (μ : ℝ) : Continuous (semiDensity μ) := by
  have hM := continuous_struveM₀
  simp only [funext (semiDensity_eq μ)]
  fun_prop

/-- The density in polar coordinates, factored on the semicircle. -/
theorem polarDensity_mul_eq (μ r θ : ℝ) :
    polarDensity 0 μ r θ * r =
      1 / (2 * π) * r * exp (-(1 / 2) * (r ^ 2 + μ ^ 2)) * exp (μ * r * sin θ) := by
  have e : -(1 / 2) * (r ^ 2 - 2 * r * (0 * cos θ + μ * sin θ) + (0 ^ 2 + μ ^ 2)) =
      -(1 / 2) * (r ^ 2 + μ ^ 2) + μ * r * sin θ := by ring
  rw [polarDensity, e, exp_add]
  ring

/-- The part of the disc below the origin, in polar coordinates. -/
theorem polar_mem_semidisc (t r θ : ℝ) :
    ((r, θ) ∈ polarCoord.target ∧ polarCoord.symm (r, θ) ∈ {z : ℝ × ℝ | z.2 < 0 ∧ z.1 ^ 2 + z.2 ^ 2 ≤ t}) ↔
      r ∈ Ioc 0 √t ∧ θ ∈ Ioo (-π) 0 := by
  have htarget : (r, θ) ∈ polarCoord.target ↔ 0 < r ∧ θ ∈ Ioo (-π) π := by
    simp [polarCoord_target]
  have hsymm : polarCoord.symm (r, θ) = (r * cos θ, r * sin θ) := by simp [polarCoord]
  have hsq : (r * cos θ) ^ 2 + (r * sin θ) ^ 2 = r ^ 2 := by
    linear_combination r ^ 2 * cos_sq_add_sin_sq θ
  rw [htarget, hsymm]
  simp only [mem_ofPred_eq, hsq]
  constructor
  · rintro ⟨⟨hr, hθ⟩, hs, hrt⟩
    have hsn : sin θ < 0 := by
      by_contra hn
      have := mul_nonneg hr.le (not_lt.1 hn)
      linarith
    refine ⟨⟨hr, (Real.le_sqrt' hr).2 hrt⟩, hθ.1, ?_⟩
    by_contra hn
    have := sin_nonneg_of_nonneg_of_le_pi (not_lt.1 hn) hθ.2.le
    linarith
  · rintro ⟨⟨hr, hrt⟩, hθ⟩
    refine ⟨⟨hr, hθ.1, by linarith [hθ.2, pi_pos]⟩, ?_, (Real.le_sqrt' hr).1 hrt⟩
    exact mul_neg_of_pos_of_neg hr (sin_neg_of_neg_of_neg_pi_lt hθ.2 hθ.1)

/-- `G₂`: "using polar coordinates": the probability of the semi-disc below the origin of radius `√t`. -/
theorem measure_semidisc (μ t : ℝ) :
    normalSample μ {z | z.2 < 0 ∧ z.1 ^ 2 + z.2 ^ 2 ≤ t} =
      ∫⁻ r in Ioc 0 √t, ENNReal.ofReal (semiDensity μ r) := by
  set S : Set (ℝ × ℝ) := {z | z.2 < 0 ∧ z.1 ^ 2 + z.2 ^ 2 ≤ t} with hSdef
  have hS : MeasurableSet S := (measurableSet_lt measurable_snd measurable_const).inter
    (measurableSet_le (f := fun z : ℝ × ℝ => z.1 ^ 2 + z.2 ^ 2) (by fun_prop) measurable_const)
  set D : ℝ × ℝ → ℝ≥0∞ := fun z => gaussianPDF 0 1 z.1 * gaussianPDF μ 1 z.2 with hD
  have hDm : Measurable D :=
    ((measurable_gaussianPDF 0 1).comp measurable_fst).mul
      ((measurable_gaussianPDF μ 1).comp measurable_snd)
  have e1 : normalSample μ S = ∫⁻ z, S.indicator D z := by
    change ((gaussianReal 0 1).prod (gaussianReal μ 1)) S = _
    rw [gaussianReal_of_var_ne_zero 0 one_ne_zero, gaussianReal_of_var_ne_zero μ one_ne_zero,
      prod_withDensity (measurable_gaussianPDF _ _) (measurable_gaussianPDF _ _),
      withDensity_apply _ hS, lintegral_indicator hS, Measure.volume_eq_prod]
  have hmeas : Measurable fun p : ℝ × ℝ => polarCoord.target.indicator
      (fun p => ENNReal.ofReal p.1 • S.indicator D (polarCoord.symm p)) p := by
    refine Measurable.indicator ?_ polarCoord.open_target.measurableSet
    refine (ENNReal.measurable_ofReal.comp measurable_fst).smul ?_
    exact (hDm.indicator hS).comp continuous_polarCoord_symm.measurable
  have hpt : ∀ r θ, polarCoord.target.indicator
      (fun p => ENNReal.ofReal p.1 • S.indicator D (polarCoord.symm p)) (r, θ) =
      (Ioc 0 √t).indicator (fun r => (Ioo (-π) 0).indicator
        (fun θ => ENNReal.ofReal (polarDensity 0 μ r θ * r)) θ) r := by
    intro r θ
    by_cases hm : (r, θ) ∈ polarCoord.target ∧ polarCoord.symm (r, θ) ∈ S
    · obtain ⟨hr, hθ⟩ := (polar_mem_semidisc t r θ).1 hm
      rw [indicator_of_mem hm.1, indicator_of_mem hm.2, indicator_of_mem hr, indicator_of_mem hθ]
      have hsymm : polarCoord.symm (r, θ) = (r * cos θ, r * sin θ) := by simp [polarCoord]
      simp only [hD, hsymm, gaussianPDF, smul_eq_mul]
      rw [← ENNReal.ofReal_mul (gaussianPDFReal_nonneg _ _ _),
        gaussianPDFReal_mul_gaussianPDFReal_eq_polarDensity, ← ENNReal.ofReal_mul hr.1.le, mul_comm]
    · have hm' := (not_congr (polar_mem_semidisc t r θ)).1 hm
      have hl : polarCoord.target.indicator
          (fun p => ENNReal.ofReal p.1 • S.indicator D (polarCoord.symm p)) (r, θ) = 0 := by
        by_cases h1 : (r, θ) ∈ polarCoord.target
        · rw [indicator_of_mem h1, indicator_of_notMem (fun h2 => hm ⟨h1, h2⟩), smul_zero]
        · exact indicator_of_notMem h1 _
      rw [hl]
      by_cases h1 : r ∈ Ioc 0 √t
      · rw [indicator_of_mem h1, indicator_of_notMem (fun h2 => hm' ⟨h1, h2⟩)]
      · rw [indicator_of_notMem h1]
  rw [e1, ← lintegral_comp_polarCoord_symm, ← lintegral_indicator
    polarCoord.open_target.measurableSet, Measure.volume_eq_prod, lintegral_prod _
    hmeas.aemeasurable, ← lintegral_indicator measurableSet_Ioc]
  refine lintegral_congr fun r => ?_
  simp only [hpt]
  by_cases hr : r ∈ Ioc 0 √t
  · simp only [indicator_of_mem hr]
    have hc : Continuous fun θ => polarDensity 0 μ r θ * r :=
      ((continuous_polarDensity 0 μ).comp (continuous_const.prodMk continuous_id)).mul
        continuous_const
    have hint : IntegrableOn (fun θ => polarDensity 0 μ r θ * r) (Ioo (-π) 0) :=
      (hc.integrableOn_Icc (a := -π) (b := 0)).mono_set Ioo_subset_Icc_self
    rw [lintegral_indicator measurableSet_Ioo,
      ← ofReal_integral_eq_lintegral_ofReal hint
        (ae_restrict_of_forall_mem measurableSet_Ioo fun θ _ =>
          mul_nonneg (polarDensity_nonneg _ _ _ _) hr.1.le)]
    congr 1
    rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le (by linarith [pi_pos]),
      semiDensity, ← intervalIntegral.integral_const_mul]
    exact intervalIntegral.integral_congr fun θ _ => polarDensity_mul_eq μ r θ
  · simp only [indicator_of_notMem hr]
    simp

end Polar

/-- The source's density `g_X` of the distance: `2 d/dx G₁ + d/dx G₂`. -/
def t1DistDensity (μ u : ℝ) : ℝ := 2 * stripDensity 0 μ 0 u + semiDensity μ u

/-- The law of the distance: `P(Λ ≤ t)` is the integral of `g_X` over `(0, √t]`. -/
theorem measure_t1Var_le (μ t : ℝ) :
    normalSample μ {z | t1Var z ≤ t} = ∫⁻ u in Ioc 0 √t, ENNReal.ofReal (t1DistDensity μ u) := by
  have hset : {z | t1Var z ≤ t} ∩ {z : ℝ × ℝ | z.2 < 0} = {z | z.2 < 0 ∧ z.1 ^ 2 + z.2 ^ 2 ≤ t} := by
    ext z
    simp only [mem_inter_iff, mem_ofPred_eq, t1Var]
    constructor
    · rintro ⟨hl, hy⟩
      rw [ite_eq_left hy] at hl
      exact ⟨hy, hl⟩
    · rintro ⟨hy, hl⟩
      rw [ite_eq_left hy]
      exact ⟨hl, hy⟩
  rw [measure_t1Var_le_eq_sum, hset, measure_inter_R₁, measure_semidisc]
  have hm : Measurable fun u => ENNReal.ofReal (stripDensity 0 μ 0 u) :=
    ENNReal.measurable_ofReal.comp (continuous_stripDensity 0 μ 0).measurable
  have hsplit : ∀ u ∈ Ioc 0 √t, ENNReal.ofReal (t1DistDensity μ u) =
      2 * ENNReal.ofReal (stripDensity 0 μ 0 u) + ENNReal.ofReal (semiDensity μ u) := by
    intro u hu
    simp only [t1DistDensity]
    rw [ENNReal.ofReal_add (mul_nonneg (by norm_num) (stripDensity_nonneg _ _ _ _))
      (semiDensity_nonneg μ hu.1), ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat]
  rw [setLIntegral_congr_fun measurableSet_Ioc hsplit,
    lintegral_add_left (hm.const_mul 2), lintegral_const_mul' _ _ (by norm_num)]

end T1Pdf

open T1Pdf

/-! ### The density -/

/-- `t1Density` is nonnegative, since `erf ≥ -1` and `M₀ ≤ 0`. -/
theorem t1Density_nonneg (μ lam : ℝ) : 0 ≤ t1Density μ lam := by
  simp only [t1Density]
  split_ifs with hl
  · refine mul_nonneg (by positivity) (sub_nonneg_of_le ?_)
    have h₁ : Real.exp (-(μ ^ 2 / 2)) * struveM₀ (μ * √lam) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le (struveM₀_nonpos _)
    have h₂ : 0 ≤ √(2 / (Real.pi * lam)) * (1 + Real.erf (μ / √2)) :=
      mul_nonneg (Real.sqrt_nonneg _) (by linarith [Real.neg_one_le_erf (μ / √2)])
    linarith
  · exact le_rfl

theorem measurable_t1Density (μ : ℝ) : Measurable (t1Density μ) := by
  have hM : Measurable struveM₀ := continuous_struveM₀.measurable
  unfold t1Density
  refine Measurable.ite measurableSet_Ioi ?_ measurable_const
  fun_prop

/-- On `u > 0`, `2 u f(u²)` is the density `g_X` of the distance, where `f` is the printed density: the source's "change of variable
`x = √λ`". -/
theorem two_mul_mul_t1Density (μ : ℝ) {u : ℝ} (hu : 0 < u) :
    2 * u * t1Density μ (u ^ 2) = t1DistDensity μ u := by
  have hu2 : 0 < u ^ 2 := by positivity
  have hπ := Real.pi_pos
  have h2 : (0 : ℝ) < √2 := by positivity
  have hpi : (0 : ℝ) < √Real.pi := Real.sqrt_pos.2 hπ
  have hs₂ : √2 ^ 2 = (2 : ℝ) := Real.sq_sqrt (by norm_num)
  have hspi : √Real.pi ^ 2 = Real.pi := Real.sq_sqrt hπ.le
  have e₁ : √(2 / (Real.pi * u ^ 2)) = √2 / (√Real.pi * u) := by
    rw [Real.sqrt_div (by norm_num), Real.sqrt_mul hπ.le, Real.sqrt_sq hu.le]
  have e₂ : √(2 * Real.pi) = √2 * √Real.pi := Real.sqrt_mul (by norm_num) _
  have e₃ : Real.erf ((0 * u - μ) / √2) = -Real.erf (μ / √2) := by
    rw [show (0 * u - μ) / √2 = -(μ / √2) by ring, Real.erf_neg]
  simp only [t1Density, hu2, ↓reduceIte, Real.sqrt_sq hu.le, t1DistDensity, stripDensity,
    gaussianPDFReal_one, semiDensity_eq]
  rw [e₁, e₂, e₃, show -(1 / 2) * (u ^ 2 + μ ^ 2) = -(u ^ 2 / 2) + -(μ ^ 2 / 2) by ring,
    show -(u - 0) ^ 2 / 2 = -(u ^ 2 / 2) by ring, Real.exp_add]
  generalize Real.exp (-(u ^ 2 / 2)) = A
  generalize Real.exp (-(μ ^ 2 / 2)) = B
  generalize Real.erf (μ / √2) = E
  generalize struveM₀ (μ * u) = M
  field_simp
  linear_combination (4 * A * (1 + E)) * hs₂

/-- **Proposition 5.2** (`ext:t1_density`) of Mitchell, Allman, Rhodes 2019. The random variable of Proposition 5.1, `t1Var (Z, Z̄)` for
independent `Z ~ N(0, 1)` and `Z̄ ~ N(μ, 1)`, has on `λ > 0` the density of Equation `eq:T1pdf`. The value `0` has mass zero, so this
determines the law. The source has `μ = μ₀ ≥ 0`; it holds for every real `μ`. See the module docstring for the proof, and for the
misprint in the source's Appendix C. -/
theorem t1Var_density (μ : ℝ) :
    (∀ lam, 0 ≤ t1Density μ lam) ∧
      ((gaussianReal 0 1).prod (gaussianReal μ 1)).map t1Var =
        volume.withDensity (fun lam => ENNReal.ofReal (t1Density μ lam)) := by
  refine ⟨t1Density_nonneg μ, ?_⟩
  have hc := continuous_t1Var
  have hfin : IsFiniteMeasure (((gaussianReal 0 1).prod (gaussianReal μ 1)).map t1Var) := inferInstance
  refine Measure.ext_of_Iic _ _ fun t => ?_
  have hIic : MeasurableSet (Iic t) := measurableSet_Iic
  rw [Measure.map_apply hc.measurable hIic, withDensity_apply _ hIic]
  refine (measure_t1Var_le μ t).trans ?_
  have hind : ∫⁻ v in Iic t, ENNReal.ofReal (t1Density μ v) =
      ∫⁻ v in Ioc 0 t, ENNReal.ofReal (t1Density μ v) := by
    rw [← lintegral_indicator (measurableSet_Iic : MeasurableSet (Iic t)),
      ← lintegral_indicator (measurableSet_Ioc : MeasurableSet (Ioc 0 t))]
    refine lintegral_congr fun v => ?_
    by_cases hv : 0 < v
    · by_cases hvt : v ≤ t
      · rw [indicator_of_mem (show v ∈ Iic t from hvt),
          indicator_of_mem (show v ∈ Ioc 0 t from ⟨hv, hvt⟩)]
      · rw [indicator_of_notMem (show v ∉ Iic t from hvt),
          indicator_of_notMem (show v ∉ Ioc 0 t from fun h => hvt h.2)]
    · have h0 : ENNReal.ofReal (t1Density μ v) = 0 := by simp [t1Density, hv]
      rw [indicator_of_notMem (show v ∉ Ioc 0 t from fun h => hv h.1)]
      by_cases hvt : v ≤ t
      · rw [indicator_of_mem (show v ∈ Iic t from hvt), h0]
      · rw [indicator_of_notMem (show v ∉ Iic t from hvt)]
  rw [hind, lintegral_Ioc_eq_lintegral_sq t fun v => ENNReal.ofReal (t1Density μ v)]
  refine setLIntegral_congr_fun measurableSet_Ioc fun u hu => ?_
  rw [← ENNReal.ofReal_mul (mul_pos two_pos hu.1).le, two_mul_mul_t1Density μ hu.1]

/-- The tail of the T1 test distribution is the integral of the density. -/
theorem t1Tail_eq_integral (μ t : ℝ) : t1Tail μ t = ∫ v in Ioi t, t1Density μ v := by
  have hm := continuous_t1Var.measurable
  have hset : {z : ℝ × ℝ | t < t1Var z} = t1Var ⁻¹' Ioi t := rfl
  rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ (t1Density_nonneg μ))
      (measurable_t1Density μ).aestronglyMeasurable,
    ← withDensity_apply _ measurableSet_Ioi, ← (t1Var_density μ).2,
    Measure.map_apply hm measurableSet_Ioi, t1Tail_eq, measureReal_def, hset]

/-- The distribution function of the T1 test distribution is the integral of the density. -/
theorem one_sub_t1Tail_eq_integral (μ t : ℝ) : 1 - t1Tail μ t = ∫ v in Iic t, t1Density μ v := by
  have hm := continuous_t1Var.measurable
  have hset : {z : ℝ × ℝ | t < t1Var z} = (t1Var ⁻¹' Iic t)ᶜ := by
    ext z
    simp
  rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ (t1Density_nonneg μ))
      (measurable_t1Density μ).aestronglyMeasurable,
    ← withDensity_apply _ measurableSet_Iic, ← (t1Var_density μ).2,
    Measure.map_apply hm measurableSet_Iic, t1Tail_eq, hset,
    probReal_compl_eq_one_sub (hm measurableSet_Iic), measureReal_def]
  ring

theorem integrable_t1Density (μ : ℝ) : Integrable (t1Density μ) := by
  refine ⟨(measurable_t1Density μ).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (ae_of_all _ (t1Density_nonneg μ))]
  have h := congrArg (fun ν : Measure ℝ => ν univ) (t1Var_density μ).2
  simp only [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ] at h
  rw [← h, Measure.map_apply continuous_t1Var.measurable MeasurableSet.univ, preimage_univ,
    measure_univ]
  exact ENNReal.one_lt_top

theorem one_sub_t1Tail_eq_intervalIntegral (μ t : ℝ) :
    1 - t1Tail μ t = ∫ v in (0 : ℝ)..t, t1Density μ v := by
  have hi := integrable_t1Density μ
  have hzero : ∫ v in Iic (0 : ℝ), t1Density μ v = 0 :=
    setIntegral_eq_zero_of_forall_eq_zero fun v hv => by
      simp [t1Density, not_lt.2 (show v ≤ 0 from hv)]
  have h₂ := intervalIntegral.integral_Iic_sub_Iic (a := 0) (b := t) hi.integrableOn hi.integrableOn
  rw [one_sub_t1Tail_eq_integral μ t]
  linarith

/-- The tail of the T1 test distribution is continuous: the law has no atoms. -/
theorem continuous_t1Tail (μ : ℝ) : Continuous (t1Tail μ) := by
  have hi := integrable_t1Density μ
  have hc : Continuous fun t => 1 - ∫ v in (0 : ℝ)..t, t1Density μ v :=
    continuous_const.sub (intervalIntegral.continuous_primitive (fun _ _ => hi.intervalIntegrable) 0)
  exact hc.congr fun t => by
    rw [← one_sub_t1Tail_eq_intervalIntegral μ t]
    ring

theorem t1Tail_zero_arg (μ : ℝ) : t1Tail μ 0 = 1 := by
  have := one_sub_t1Tail_eq_intervalIntegral μ 0
  rw [intervalIntegral.integral_same] at this
  linarith

/-- Every level in `(0, 1]` is a value of the tail of the T1 test distribution, for `μ ≥ 0`. -/
theorem exists_t1Tail_eq {μ : ℝ} (hμ : 0 ≤ μ) {x : ℝ} (hx : 0 < x) (hx1 : x ≤ 1) :
    ∃ t : ℝ, 0 ≤ t ∧ t1Tail μ t = x := by
  have hlim : Tendsto (fun t : ℝ => Real.exp (-t / 2)) atTop (𝓝 0) := by
    refine Real.tendsto_exp_atBot.comp ?_
    have : Tendsto (fun t : ℝ => t / 2) atTop atTop := tendsto_id.atTop_div_const (by norm_num)
    exact (tendsto_neg_atTop_atBot.comp this).congr fun t => by
      simp only [Function.comp]
      ring
  obtain ⟨T, hT, hT0⟩ := ((hlim.eventually (gt_mem_nhds hx)).and (eventually_ge_atTop 0)).exists
  have hle : t1Tail μ T ≤ Real.exp (-T / 2) := t1Tail_le_chiSqTwoTail hμ hT0
  have hmem : x ∈ Icc (t1Tail μ T) (t1Tail μ 0) :=
    ⟨(hle.trans_lt hT).le, by rwa [t1Tail_zero_arg]⟩
  obtain ⟨t, ht, hty⟩ := intermediate_value_Icc' hT0 (continuous_t1Tail μ).continuousOn hmem
  exact ⟨t, ht.1, hty⟩

/-! ### What the source says of the density -/

/-- **The density at `μ₀ = 0`** (`ext:t1_density_boundary`): "At the singularity, where `μ₀ = 0`, Equation `eq:T1pdf` gives the
probability density function of `½ χ²₁ + ½ χ²₂`" (Mitchell, Allman, Rhodes 2019, after Proposition 5.2): those of `χ²₁` and `χ²₂` are
`exp (-λ / 2) / √(2 π λ)` and `½ exp (-λ / 2)`. -/
theorem t1Density_zero {lam : ℝ} (hl : 0 < lam) :
    t1Density 0 lam = 1 / 2 * (Real.exp (-(lam / 2)) / √(2 * Real.pi * lam)) +
      1 / 2 * (1 / 2 * Real.exp (-(lam / 2))) := by
  have hπ := Real.pi_pos
  have h2 : (0 : ℝ) < √2 := by positivity
  have hs₂ : √2 ^ 2 = (2 : ℝ) := Real.sq_sqrt (by norm_num)
  have hp : 0 < √(Real.pi * lam) := Real.sqrt_pos.2 (by positivity)
  have e₁ : √(2 / (Real.pi * lam)) = √2 / √(Real.pi * lam) := Real.sqrt_div (by norm_num) _
  have e₂ : √(2 * Real.pi * lam) = √2 * √(Real.pi * lam) := by
    rw [mul_assoc, Real.sqrt_mul (by norm_num)]
  simp only [t1Density, hl, ↓reduceIte, zero_div, zero_mul, struveM₀_zero, Trinomial.erf_zero]
  rw [e₁, e₂]
  norm_num
  field_simp
  linear_combination 4 * hs₂

/-- **The T1 test distribution at `μ₀ = 0` is `½ χ²₁ + ½ χ²₂`** (`ext:t1_density_boundary`), as a statement on tails: as "one expects
from Example 1.2 of Drton" (Mitchell, Allman, Rhodes 2019, after Proposition 5.2). -/
theorem t1Tail_zero {t : ℝ} (ht : 0 ≤ t) :
    t1Tail 0 t = 1 / 2 * chiSqOneTail t + 1 / 2 * chiSqTwoTail t := by
  set P := (gaussianReal 0 1).prod (gaussianReal 0 1) with hP
  have hIoi : (gaussianReal 0 1).real (Ioi 0) = 1 / 2 := by
    rw [Trinomial.gaussianReal_real_Ioi]
    simp [Trinomial.erf_zero]
  have hA : MeasurableSet {z : ℝ × ℝ | t < z.1 ^ 2 + z.2 ^ 2} :=
    measurableSet_lt measurable_const (by fun_prop)
  -- the part above the horizontal axis
  have h₁ : P.real ({z | t < t1Var z} ∩ {z | 0 < z.2}) = 1 / 2 * chiSqOneTail t := by
    have hset : {z : ℝ × ℝ | t < t1Var z} ∩ {z | 0 < z.2} = {x : ℝ | t < x ^ 2} ×ˢ Ioi 0 := by
      ext z
      simp only [mem_inter_iff, mem_ofPred_eq, mem_prod, mem_Ioi, t1Var]
      constructor
      · rintro ⟨h, hy⟩
        rw [ite_eq_right (not_lt.2 hy.le), add_zero] at h
        exact ⟨h, hy⟩
      · rintro ⟨h, hy⟩
        rw [ite_eq_right (not_lt.2 hy.le), add_zero]
        exact ⟨h, hy⟩
    rw [hset, hP, measureReal_prod_prod, hIoi, chiSqOneTail]
    ring
  -- the part below it, by the reflection
  have hrefl : P ({z | t < z.1 ^ 2 + z.2 ^ 2} ∩ {z | z.2 < 0}) =
      P ({z | t < z.1 ^ 2 + z.2 ^ 2} ∩ {z | 0 < z.2}) := by
    have h := gaussianReal_prod_map_orthonormal (a := 1) (b := 0) (a' := 0) (b' := -1)
      (by norm_num) (by norm_num) (by norm_num) 0 0
    have e : (fun z : ℝ × ℝ => (1 * z.1 + 0 * z.2, 0 * z.1 + -1 * z.2)) = fun z => (z.1, -z.2) := by
      funext z
      simp
    rw [e, show (1 : ℝ) * 0 + 0 * 0 = 0 by ring, show (0 : ℝ) * 0 + -1 * 0 = 0 by ring] at h
    have hm : Measurable fun z : ℝ × ℝ => (z.1, -z.2) := by fun_prop
    have hBm : MeasurableSet ({z : ℝ × ℝ | t < z.1 ^ 2 + z.2 ^ 2} ∩ {z | 0 < z.2}) :=
      hA.inter (measurableSet_lt measurable_const measurable_snd)
    have hv := Measure.map_apply (μ := P) hm hBm
    rw [hP, h] at hv
    rw [hP, hv]
    congr 1
    ext z
    simp
  have hsplit := gaussianReal_prod_split (k₁ := 0) (k₂ := 1) (Or.inr one_ne_zero) 0 0
    {z : ℝ × ℝ | t < z.1 ^ 2 + z.2 ^ 2}
  have e₁ : {z : ℝ × ℝ | t < z.1 ^ 2 + z.2 ^ 2} ∩ {z : ℝ × ℝ | 0 < 0 * z.1 + 1 * z.2} =
      {z | t < z.1 ^ 2 + z.2 ^ 2} ∩ {z | 0 < z.2} := by
    ext z
    simp
  have e₂ : {z : ℝ × ℝ | t < z.1 ^ 2 + z.2 ^ 2} ∩ {z : ℝ × ℝ | 0 * z.1 + 1 * z.2 < 0} =
      {z | t < z.1 ^ 2 + z.2 ^ 2} ∩ {z | z.2 < 0} := by
    ext z
    simp
  rw [e₁, e₂, ← hP, hrefl] at hsplit
  have h₂ : P.real ({z | t < t1Var z} ∩ {z | z.2 < 0}) = 1 / 2 * chiSqTwoTail t := by
    have hset : {z : ℝ × ℝ | t < t1Var z} ∩ {z | z.2 < 0} =
        {z | t < z.1 ^ 2 + z.2 ^ 2} ∩ {z | z.2 < 0} := by
      ext z
      simp only [mem_inter_iff, mem_ofPred_eq, t1Var]
      constructor
      · rintro ⟨h, hy⟩
        rw [ite_eq_left hy] at h
        exact ⟨h, hy⟩
      · rintro ⟨h, hy⟩
        rw [ite_eq_left hy]
        exact ⟨h, hy⟩
    have hχ := chiSqTwoTail_eq ht
    rw [hset, measureReal_def, hrefl]
    rw [hχ, ← hP, measureReal_def, hsplit, ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _)]
    ring
  have hall := gaussianReal_prod_split (k₁ := 0) (k₂ := 1) (Or.inr one_ne_zero) 0 0
    {z : ℝ × ℝ | t < t1Var z}
  have e₃ : {z : ℝ × ℝ | t < t1Var z} ∩ {z : ℝ × ℝ | 0 < 0 * z.1 + 1 * z.2} =
      {z | t < t1Var z} ∩ {z | 0 < z.2} := by
    ext z
    simp
  have e₄ : {z : ℝ × ℝ | t < t1Var z} ∩ {z : ℝ × ℝ | 0 * z.1 + 1 * z.2 < 0} =
      {z | t < t1Var z} ∩ {z | z.2 < 0} := by
    ext z
    simp
  rw [e₃, e₄, ← hP] at hall
  rw [t1Tail_eq]
  change P.real _ = _
  rw [measureReal_def, hall, ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _),
    ← measureReal_def, ← measureReal_def, h₁, h₂]

/-- **The density tends to that of `χ²₁`** (`ext:t1_density_chisq`): "for `φ₀ ∈ (0, 1)` as `n → ∞` Equation `eq:T1pdf` gives the probability
density function of `χ²₁`, since `M₀(x) → 0` as `x → ∞`" (Mitchell, Allman, Rhodes 2019, after Proposition 5.2), pointwise on `λ > 0`. -/
theorem tendsto_t1Density_atTop {φ : ℝ} (hφ : 0 < φ ∧ φ < 1) {lam : ℝ} (hl : 0 < lam) :
    Tendsto (fun n : ℝ => t1Density (muZero φ n) lam) atTop
      (𝓝 (Real.exp (-(lam / 2)) / √(2 * Real.pi * lam))) := by
  have hμ := tendsto_muZero_atTop hφ
  have hπ := Real.pi_pos
  have hsl : 0 < √lam := Real.sqrt_pos.2 hl
  have herf : Tendsto (fun n : ℝ => Real.erf (muZero φ n / √2)) atTop (𝓝 1) :=
    Real.tendsto_erf_atTop.comp (hμ.atTop_div_const (by positivity))
  have hM : Tendsto (fun n : ℝ => struveM₀ (muZero φ n * √lam)) atTop (𝓝 0) :=
    tendsto_struveM₀_atTop.comp (hμ.atTop_mul_const hsl)
  have hE : Tendsto (fun n : ℝ => Real.exp (-(muZero φ n ^ 2 / 2))) atTop (𝓝 0) := by
    refine Real.tendsto_exp_atBot.comp ?_
    have h₂ : Tendsto (fun n : ℝ => muZero φ n ^ 2) atTop atTop :=
      (tendsto_pow_atTop two_ne_zero).comp hμ
    exact tendsto_neg_atTop_atBot.comp (h₂.atTop_div_const two_pos)
  have hsum := ((((herf.const_add 1).const_mul (√(2 / (Real.pi * lam)))).sub
    (hE.mul hM)).const_mul (1 / 4 * Real.exp (-(lam / 2))))
  have h2 : (0 : ℝ) < √2 := by positivity
  have hs₂ : √2 ^ 2 = (2 : ℝ) := Real.sq_sqrt (by norm_num)
  have hp : 0 < √(Real.pi * lam) := Real.sqrt_pos.2 (by positivity)
  have hval : 1 / 4 * Real.exp (-(lam / 2)) *
      (√(2 / (Real.pi * lam)) * (1 + 1) - 0 * 0) =
      Real.exp (-(lam / 2)) / √(2 * Real.pi * lam) := by
    have e₁ : √(2 / (Real.pi * lam)) = √2 / √(Real.pi * lam) := Real.sqrt_div (by norm_num) _
    have e₂ : √(2 * Real.pi * lam) = √2 * √(Real.pi * lam) := by
      rw [mul_assoc, Real.sqrt_mul (by norm_num)]
    rw [e₁, e₂, show √2 / √(Real.pi * lam) * (1 + 1) - 0 * 0 = 2 * √2 / √(Real.pi * lam) by ring]
    field_simp
    linear_combination (2 : ℝ) * hs₂
  rw [hval] at hsum
  refine hsum.congr fun n => ?_
  simp only [t1Density, hl, ↓reduceIte]

end QuartetTests

end Phylogenetics

namespace Phylogenetics.Trinomial

open Phylogenetics.QuartetTests

/-- The likelihood ratio statistic of model T1, on real counts. -/
def t1S (a b c : ℝ) : ℝ := if (b + c) / 2 ≤ a then lineS b c else starS a b c

/-- The null of model T1, the source's `Θ₀`, where `q = φ₀ / 3`, `φ₀ ∈ (0, 1]`. -/
def t1Null : Set (ℝ × ℝ × ℝ) := {p | ∃ q : ℝ, 0 < q ∧ q ≤ 1 / 3 ∧ p = (1 - 2 * q, q, q)}

/-- **The T1 statistic is the likelihood ratio statistic of the source** (`ext:t1_lrt`) for testing `Θ₀` against the open simplex, on
positive counts. -/
theorem t1S_eq_likelihoodRatio {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    t1S a b c = 2 * (sSup (logLik a b c '' openSimplex) - sSup (logLik a b c '' t1Null)) := by
  have hN : a + b + c = a + b + c := rfl
  obtain ⟨q₁, hq₁, hq₁', hv₁, hu₁⟩ := halfLine_max ha hb hc hN
  have hL := (isGreatest_logLik ha hb hc hN).csSup_eq
  have hG : IsGreatest (logLik a b c '' t1Null)
      (logLikHat (a + b + c) a b c - t1S a b c / 2) := by
    constructor
    · exact ⟨_, ⟨q₁, hq₁, hq₁', rfl⟩, hv₁⟩
    · rintro _ ⟨p, ⟨q, hq, hq3, rfl⟩, rfl⟩
      exact hu₁ q hq hq3
  rw [hL, hG.csSup_eq]
  ring

/-- At the boundary point, the T1 statistic is close to the squared distance to the half-line, uniformly on bounded sets of the
whitened frequencies. -/
theorem closeOnBalls_t1S_centroid :
    CloseOnBalls (fun (n : ℕ) (η : Fin n → Fin 3) ↦ sampleW 1 η)
      (fun (n : ℕ) (η : Fin n → Fin 3) ↦ t1S (count η 0) (count η 1) (count η 2)) t1Var := by
  intro R hR ε hε
  filter_upwards [eventually_lineS_first one_mem_cutRange hR hε, eventually_starS_centroid hR hε,
    eventually_gt_atTop 0] with n h₁ h₄ hn0 η hη₁ hη₂
  have hsum := count_add η
  have hη₁' : |(whiten 1 n (count η 0) (count η 1) (count η 2)).1| < R := hη₁
  have hη₂' : |(whiten 1 n (count η 0) (count η 1) (count η 2)).2| < R := hη₂
  have hl₁ := h₁ _ _ _ hsum hη₁' hη₂'
  have hst := h₄ _ _ _ hsum hη₁' hη₂'
  obtain ⟨e₁, -, -⟩ := centroid_sides hn0 hsum
  have hs : 0 < √(n : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast hn0)
  have hK : 0 < 3 / 2 * (√(n : ℝ) * scaleB 1) := by
    have := scaleB_pos one_mem_cutRange
    positivity
  change |t1S _ _ _ - t1Var (whiten 1 n _ _ _)| < ε
  rw [t1Var_eq_sqDistHalfLine]
  simp only [t1S, sqDistHalfLine]
  refine abs_ite_sub_lt (le_iff_of_sub_eq hK e₁) ?_ hst
  rwa [show ∀ x y : ℝ, (x * 1 - y * 0) ^ 2 = x ^ 2 from fun x y => by ring]

/-- Off the boundary, the T1 statistic is the statistic of the true line, and so close to `Z²`. -/
theorem closeOnBalls_t1S_of_lt {φ : ℝ} (hφ : 0 < φ ∧ φ < 3 / 2) (hφ1 : φ < 1) :
    CloseOnBalls (fun (n : ℕ) (η : Fin n → Fin 3) ↦ sampleW φ η)
      (fun (n : ℕ) (η : Fin n → Fin 3) ↦ t1S (count η 0) (count η 1) (count η 2))
      (fun z ↦ z.1 ^ 2) := by
  intro R hR ε hε
  filter_upwards [eventually_lineS_first hφ hR hε, eventually_first_most_frequent hφ hφ1 (R := R)]
    with n h₁ h₃ η hη₁ hη₂
  have hη₁' : |(whiten φ n (count η 0) (count η 1) (count η 2)).1| < R := hη₁
  have hη₂' : |(whiten φ n (count η 0) (count η 1) (count η 2)).2| < R := hη₂
  have hl := h₁ _ _ _ (count_add η) hη₁' hη₂'
  have hfirst := h₃ _ _ _ (count_add η) hη₂'
  change |t1S _ _ _ - (whiten φ n _ _ _).1 ^ 2| < ε
  rw [t1S, ite_eq_left hfirst]
  exact hl

/-- Off the boundary, the normal sample has a large mean, and the T1 variable is `Z²`. -/
theorem closeOnBalls_t1Var_of_lt {φ : ℝ} (hφ : 0 < φ ∧ φ < 3 / 2) (hφ1 : φ < 1) :
    CloseOnBalls (Ω := fun _ ↦ ℝ × ℝ) (fun (n : ℕ) (z : ℝ × ℝ) ↦ (z.1, z.2 - muZero φ n))
      (fun _ z ↦ t1Var z) (fun z ↦ z.1 ^ 2) := by
  intro R hR ε hε
  have hgap : 0 < |1 - φ| * (2 / 3) := by
    have := abs_pos.2 (sub_ne_zero.2 hφ1.ne')
    positivity
  have hsqrt : Tendsto (fun n : ℕ ↦ √(2 * (n : ℝ))) atTop atTop := by
    refine Real.tendsto_sqrt_atTop.comp ?_
    exact Tendsto.const_mul_atTop (by norm_num) tendsto_natCast_atTop_atTop
  filter_upwards [hsqrt.eventually_ge_atTop (R / (|1 - φ| * (2 / 3)))] with n hn z _ hz₂
  have hz₂' : |z.2 - muZero φ n| < R := hz₂
  have hμ := abs_muZero_ge (m := n) hφ.1 hφ.2
  rw [abs_of_nonneg (muZero_nonneg_of_le_one hφ1.le)] at hμ
  rw [div_le_iff₀ hgap] at hn
  have hμ' : R ≤ muZero φ n := by nlinarith
  have hy : 0 < z.2 := by linarith [(abs_lt.1 hz₂').1]
  change |t1Var z - z.1 ^ 2| < ε
  rw [t1Var, ite_eq_right (not_lt.2 hy.le), add_zero, sub_self, abs_zero]
  exact hε

/-- **The limit law at the boundary point, for the trinomial.** -/
theorem tendstoInDistribution_t1S_centroid :
    TendstoInDistribution (fun (n : ℕ) (η : Fin n → Fin 3) ↦ t1S (count η 0) (count η 1) (count η 2))
      atTop t1Var (fun n ↦ Measure.pi fun _ : Fin n ↦ (cutPoint_isDist one_mem_cutRange).toPMF.toMeasure)
      stdPlane :=
  tendstoInDistribution_of_closeOnBalls (tendstoInDistribution_sampleW one_mem_cutRange)
    (S := fun (n : ℕ) (η : Fin n → Fin 3) ↦ t1S (count η 0) (count η 1) (count η 2))
    (fun _ ↦ Measurable.of_discrete.aemeasurable) continuous_t1Var closeOnBalls_t1S_centroid

/-- The level sets of the T1 variable are null: its law has a density. -/
theorem stdPlane_t1Var_eq_null (t : ℝ) : stdPlane {z | t1Var z = t} = 0 := by
  have hset : {z | t1Var z = t} = t1Var ⁻¹' {t} := rfl
  rw [hset, ← Measure.map_apply continuous_t1Var.measurable (measurableSet_singleton t)]
  have h := (t1Var_density 0).2
  have h' : stdPlane.map t1Var = volume.withDensity (fun lam => ENNReal.ofReal (t1Density 0 lam)) := h
  rw [h']
  exact withDensity_absolutelyContinuous _ _ (by simp)

/-- The distribution function of the T1 statistic at the boundary point, for the trinomial. -/
theorem tendsto_iidProb_lt_t1S_centroid (t : ℝ) :
    Tendsto (fun n ↦ iidProb (cutPoint 1) n fun η ↦ t < t1S (count η 0) (count η 1) (count η 2)) atTop
      (𝓝 (t1Tail 0 t)) := by
  have he : t1Tail 0 t = stdPlane.real {z | t < t1Var z} := rfl
  rw [he]
  refine tendsto_iidProb_of_threshold one_mem_cutRange continuous_t1Var ?_ ?_ (stdPlane_t1Var_eq_null t)
  · intro R hR δ hδ
    filter_upwards [closeOnBalls_t1S_centroid R hR δ hδ] with n hn η h₁ h₂ h₃
    have := (abs_lt.1 (hn η h₁ h₂)).1
    linarith
  · intro R hR δ hδ
    filter_upwards [closeOnBalls_t1S_centroid R hR δ hδ] with n hn η h₁ h₂ h₃ h₄
    have := (abs_lt.1 (hn η h₁ h₂)).2
    linarith

/-- Off the boundary, the tail of the T1 statistic tends to that of `χ²₁`. -/
theorem tendsto_iidProb_lt_t1S_of_lt {φ : ℝ} (hφ : 0 < φ ∧ φ < 3 / 2) (hφ1 : φ < 1) (t : ℝ) :
    Tendsto (fun n ↦ iidProb (cutPoint φ) n fun η ↦ t < t1S (count η 0) (count η 1) (count η 2)) atTop
      (𝓝 (chiSqOneTail t)) := by
  rw [← stdPlane_real_first]
  refine tendsto_iidProb_of_threshold hφ (T := fun z ↦ z.1 ^ 2) (by fun_prop) ?_ ?_ (stdPlane_first_null t)
  · intro R hR δ hδ
    filter_upwards [closeOnBalls_t1S_of_lt hφ hφ1 R hR δ hδ] with n hn η h₁ h₂ h₃
    have := (abs_lt.1 (hn η h₁ h₂)).1
    linarith
  · intro R hR δ hδ
    filter_upwards [closeOnBalls_t1S_of_lt hφ hφ1 R hR δ hδ] with n hn η h₁ h₂ h₃ h₄
    have := (abs_lt.1 (hn η h₁ h₂)).2
    linarith

/-! ### The fitted p-value at the boundary point -/

/-- The T1 test distribution decreases in the mean, for `μ ≥ 0`. -/
theorem t1Tail_le_t1Tail_zero {μ : ℝ} (hμ : 0 ≤ μ) (t : ℝ) : t1Tail μ t ≤ t1Tail 0 t := by
  have hmap : (gaussianReal 0 1).map (fun y ↦ y + μ) = gaussianReal μ 1 := by
    rw [gaussianReal_map_add_const, zero_add]
  have hprod : (gaussianReal 0 1).prod (gaussianReal μ 1) =
      ((gaussianReal 0 1).prod (gaussianReal 0 1)).map (Prod.map id fun y ↦ y + μ) := by
    rw [← Measure.map_prod_map _ _ measurable_id (by fun_prop), Measure.map_id, hmap]
  have hT : MeasurableSet {z : ℝ × ℝ | t < t1Var z} :=
    measurableSet_lt measurable_const continuous_t1Var.measurable
  have e₁ : t1Tail μ t = ((gaussianReal 0 1).prod (gaussianReal μ 1)).real {z | t < t1Var z} := rfl
  have e₂ : t1Tail 0 t = ((gaussianReal 0 1).prod (gaussianReal 0 1)).real {z | t < t1Var z} := rfl
  rw [e₁, e₂, hprod, map_measureReal_apply (by fun_prop) hT]
  refine measureReal_mono ?_
  rintro ⟨x, y⟩ h
  have h' : t < x ^ 2 + if y + μ < 0 then (y + μ) ^ 2 else 0 := h
  change t < x ^ 2 + if y < 0 then y ^ 2 else 0
  split_ifs at h' with hy
  · rw [ite_eq_left (by linarith)]
    nlinarith
  · split_ifs <;> nlinarith [sq_nonneg y]

/-- The tail of `χ²₁` is strictly below that of the T1 test distribution at `μ₀ = 0`, for `t > 0`. -/
theorem chiSqOneTail_lt_t1Tail_zero {t : ℝ} (ht : 0 < t) : chiSqOneTail t < t1Tail 0 t := by
  set r := √t with hr
  have hr0 : 0 < r := Real.sqrt_pos.2 ht
  have hrs : r ^ 2 = t := Real.sq_sqrt ht.le
  set P := (gaussianReal 0 1).prod (gaussianReal 0 1) with hP
  set box : Set (ℝ × ℝ) := Ioo 0 r ×ˢ Ioo (-(r + 1)) (-r) with hbox
  have hboxm : MeasurableSet box := measurableSet_Ioo.prod measurableSet_Ioo
  have hpos : 0 < P.real box := by
    rw [hP, hbox, measureReal_prod_prod]
    exact mul_pos (gaussianReal_real_Ioo_pos hr0) (gaussianReal_real_Ioo_pos (by linarith))
  have hχ : chiSqOneTail t = P.real ({x : ℝ | t < x ^ 2} ×ˢ univ) := by
    rw [hP, measureReal_prod_prod]
    simp [chiSqOneTail]
  have hdisj : Disjoint ({x : ℝ | t < x ^ 2} ×ˢ (univ : Set ℝ)) box := by
    rw [Set.disjoint_left]
    rintro ⟨x, y⟩ ⟨hx, -⟩ ⟨hx', -⟩
    have h₁ : t < x ^ 2 := hx
    have h₂ : 0 < x := hx'.1
    have h₃ : x < r := hx'.2
    nlinarith
  have hsub : ({x : ℝ | t < x ^ 2} ×ˢ (univ : Set ℝ)) ∪ box ⊆ {z | t < t1Var z} := by
    rintro ⟨x, y⟩ (⟨hx, -⟩ | ⟨-, hy⟩)
    · have h₁ : t < x ^ 2 := hx
      change t < x ^ 2 + if y < 0 then y ^ 2 else 0
      split_ifs <;> nlinarith [sq_nonneg y]
    · have h₁ : y < -r := hy.2
      change t < x ^ 2 + if y < 0 then y ^ 2 else 0
      rw [ite_eq_left (by linarith)]
      nlinarith [sq_nonneg x]
  have h₁ := measureReal_mono (μ := P) hsub
  rw [measureReal_union hdisj hboxm, ← hχ] at h₁
  have he : t1Tail 0 t = P.real {z | t < t1Var z} := rfl
  rw [he]
  linarith

/-- The tail of `χ²₁` is continuous. -/
theorem continuous_chiSqOneTail : Continuous chiSqOneTail := by
  have hc : Continuous fun t : ℝ => 1 - Real.erf (√t / √2) := by
    have := Real.continuous_erf
    fun_prop
  have hval : ∀ y : ℝ, chiSqOneTail y = 1 - Real.erf (√y / √2) := by
    intro y
    rcases le_or_gt 0 y with hy | hy
    · exact chiSqOneTail_eq_erf hy
    · have h₁ := chiSqOneTail_le_one y
      have h₂ : chiSqOneTail 0 ≤ chiSqOneTail y := chiSqOneTail_anti hy.le
      rw [chiSqOneTail_zero] at h₂
      rw [le_antisymm h₁ h₂, Real.sqrt_eq_zero_of_nonpos hy.le]
      simp [erf_zero]
  rwa [show chiSqOneTail = fun y : ℝ => 1 - Real.erf (√y / √2) from funext hval]

/-- The p-value of the T1 test at the boundary point is at most the tail at `μ₀ = 0`, and below `a` where the fitted mean is large and the
statistic is past a point where `χ²₁` is below `a`. So there is more mass below `a` than `a`: the p-value is not asymptotically
uniform there. -/
theorem exists_lt_iidProb_t1PValueR_centroid :
    ∃ a c : ℝ, 0 < a ∧ a < 1 ∧ a < c ∧ ∀ᶠ n in atTop,
      c < iidProb (cutPoint 1) n fun η ↦ t1PValueR (count η 0) (count η 1) (count η 2) ≤ a := by
  set t₀ : ℝ := 1 with ht₀
  have ht₀pos : (0 : ℝ) < t₀ := one_pos
  set a := t1Tail 0 t₀ with ha
  have ha0 : 0 < a := (chiSqOneTail_pos t₀).trans (chiSqOneTail_lt_t1Tail_zero ht₀pos)
  have ha1 : a < 1 := by
    rw [ha, t1Tail_zero ht₀pos.le]
    have h₁ := chiSqOneTail_lt_of_lt le_rfl ht₀pos
    rw [chiSqOneTail_zero] at h₁
    have h₂ : chiSqTwoTail t₀ < 1 := by
      unfold chiSqTwoTail
      rw [Real.exp_lt_one_iff]
      linarith
    linarith
  -- a point `t' < t₀` at which `χ²₁` is still below `a`
  have hχ := continuous_chiSqOneTail
  have hlt : chiSqOneTail t₀ < a := chiSqOneTail_lt_t1Tail_zero ht₀pos
  have hnear : ∀ᶠ t in 𝓝 t₀, chiSqOneTail t < a := hχ.continuousAt.eventually_lt_const hlt
  obtain ⟨δ₀, hδ₀, hball⟩ := Metric.eventually_nhds_iff.1 hnear
  set t' := max (t₀ - δ₀ / 2) (t₀ / 2) with ht'
  have ht'lt : t' < t₀ := max_lt (by linarith) (by linarith)
  have ht'pos : 0 < t' := lt_of_lt_of_le (by linarith) (le_max_right _ _)
  have ht'χ : chiSqOneTail t' < a := by
    apply hball
    rw [Real.dist_eq, abs_of_neg (by linarith)]
    have : t₀ - δ₀ / 2 ≤ t' := le_max_left _ _
    linarith
  -- a mean beyond which the T1 tail at `t'` is below `a`
  obtain ⟨M₀, hM₀⟩ := exists_gaussianReal_Iio_lt (sub_pos.2 ht'χ)
  set M := max M₀ 0 with hM
  have hM0 : 0 ≤ M := le_max_right _ _
  have htail : ∀ μ : ℝ, M ≤ μ → t1Tail μ t' ≤ a := by
    intro μ hμ
    have h₁ := t1Tail_le_add μ t'
    have h₂ := hM₀ μ ((le_max_left _ _).trans hμ)
    linarith
  -- the extra mass
  set t'' := (t' + t₀) / 2 with ht''
  have ht''0 : 0 < t'' := by rw [ht'']; linarith
  have ht''lt : t'' < t₀ := by rw [ht'']; linarith
  set ε₁ := (t₀ - t') / 2 with hε₁
  have hε₁pos : 0 < ε₁ := by rw [hε₁]; linarith
  have hsqrt : √t'' < √t₀ := Real.sqrt_lt_sqrt ht''0.le ht''lt
  set A : Set (ℝ × ℝ) := Ioo √t'' √t₀ ×ˢ Ioo (3 / 2 * M) (3 / 2 * M + 1) with hA
  have hAo : IsOpen A := isOpen_Ioo.prod isOpen_Ioo
  have hApos : 0 < stdPlane.real A := by
    rw [stdPlane, hA, measureReal_prod_prod]
    exact mul_pos (gaussianReal_real_Ioo_pos hsqrt) (gaussianReal_real_Ioo_pos (by linarith))
  set c₀ := stdPlane.real A with hc₀
  -- a slightly larger threshold keeps most of the mass of the tail
  have hnear₂ : ∀ᶠ t in 𝓝 t₀, a - c₀ / 2 < t1Tail 0 t :=
    (continuous_t1Tail 0).continuousAt.eventually_const_lt (by linarith)
  obtain ⟨δ₁, hδ₁, hball₂⟩ := Metric.eventually_nhds_iff.1 hnear₂
  set δ := δ₁ / 2 with hδ
  have hδpos : 0 < δ := by positivity
  have htδ : a - c₀ / 2 < t1Tail 0 (t₀ + δ) := by
    apply hball₂
    rw [Real.dist_eq, show t₀ + δ - t₀ = δ by ring, abs_of_pos hδpos]
    rw [hδ]
    linarith
  set U : Set (ℝ × ℝ) := {z | t₀ + δ < t1Var z} ∪ A with hU
  have hUo : IsOpen U := (isOpen_lt continuous_const continuous_t1Var).union hAo
  have hdisj : Disjoint {z : ℝ × ℝ | t₀ + δ < t1Var z} A := by
    rw [Set.disjoint_left]
    rintro ⟨x, y⟩ hz ⟨hx, hy⟩
    have hy0 : 0 < y := lt_of_le_of_lt (by positivity) hy.1
    have h₁ : t₀ + δ < x ^ 2 + if y < 0 then y ^ 2 else 0 := hz
    rw [ite_eq_right (not_lt.2 hy0.le), add_zero] at h₁
    have hx₀ : 0 ≤ x := (Real.sqrt_nonneg _).trans hx.1.le
    have h₂ : x ^ 2 < t₀ := (Real.lt_sqrt hx₀).1 hx.2
    linarith
  have hUval : a + c₀ / 2 < stdPlane.real U := by
    rw [hU, measureReal_union hdisj hAo.measurableSet]
    have : stdPlane.real {z : ℝ × ℝ | t₀ + δ < t1Var z} = t1Tail 0 (t₀ + δ) := rfl
    rw [this]
    linarith
  refine ⟨a, a + c₀ / 2, ha0, ha1, by linarith, ?_⟩
  -- restrict to a ball
  have hc0' : 0 ≤ a + c₀ / 2 := by positivity
  obtain ⟨R, hR, hRc⟩ := exists_lt_measure_box stdPlane
    ((ENNReal.ofReal_lt_iff_lt_toReal hc0' (measure_ne_top _ _)).2 hUval)
  have hopen : IsOpen (U ∩ Metric.ball 0 R) := hUo.inter Metric.isOpen_ball
  refine eventually_lt_iidProb one_mem_cutRange hopen ?_
    ((ENNReal.ofReal_lt_iff_lt_toReal hc0' (measure_ne_top _ _)).1 hRc)
  have hε : 0 < min δ ε₁ := lt_min hδpos hε₁pos
  filter_upwards [closeOnBalls_t1S_centroid R hR _ hε,
    eventually_phiHat_close one_mem_cutRange (R := R) (ε := 1 / 4) (by norm_num),
    eventually_gt_atTop 0] with n hn hphat hn0 η hη
  obtain ⟨hb₁, hb₂⟩ := mem_ball_iff.1 hη.2
  have hsum := count_add η
  have hclose := hn η hb₁ hb₂
  have hclose' : |t1S (count η 0) (count η 1) (count η 2) -
      t1Var (whiten 1 n (count η 0) (count η 1) (count η 2))| < min δ ε₁ := hclose
  obtain ⟨hc₁, hc₂⟩ := abs_lt.1 hclose'
  have hm₁ : min δ ε₁ ≤ δ := min_le_left _ _
  have hm₂ : min δ ε₁ ≤ ε₁ := min_le_right _ _
  set S := t1S (count η 0) (count η 1) (count η 2) with hS
  set phat := min 1 (3 * (count η 1 + count η 2) / (2 * (count η 0 + count η 1 + count η 2))) with hphatdef
  have hG : t1PValueR (count η 0) (count η 1) (count η 2) =
      t1Tail (muZero phat (count η 0 + count η 1 + count η 2)) S := rfl
  have hμ0 : 0 ≤ muZero phat (count η 0 + count η 1 + count η 2) :=
    muZero_nonneg_of_le_one (min_le_left _ _)
  rw [hG]
  rcases hη.1 with hη₁ | hη₁
  · -- past the threshold of the limit
    have h₁ : t₀ + δ < t1Var (whiten 1 n (count η 0) (count η 1) (count η 2)) := hη₁
    have hSt : t₀ ≤ S := by linarith
    exact (t1Tail_le_t1Tail_zero hμ0 S).trans (t1Tail_anti 0 hSt)
  · -- the extra mass: the fitted mean is large
    obtain ⟨hx, hy⟩ := hη₁
    have hx₁ : √t'' < (whiten 1 n (count η 0) (count η 1) (count η 2)).1 := hx.1
    have hy₁ : 3 / 2 * M < (whiten 1 n (count η 0) (count η 1) (count η 2)).2 := hy.1
    set x := (whiten 1 n (count η 0) (count η 1) (count η 2)).1 with hxdef
    set y := (whiten 1 n (count η 0) (count η 1) (count η 2)).2 with hydef
    have hy0 : 0 < y := lt_of_le_of_lt (by positivity) hy₁
    have hx₀ : 0 < x := lt_of_le_of_lt (Real.sqrt_nonneg _) hx₁
    have hxsq : t'' < x ^ 2 := by
      have := Real.lt_sq_of_sqrt_lt hx₁
      exact this
    have hval : t1Var (x, y) = x ^ 2 := by
      rw [t1Var]
      simp only
      rw [ite_eq_right (not_lt.2 hy0.le), add_zero]
    have hSge : t' ≤ S := by
      have h₁ : t1Var (whiten 1 n (count η 0) (count η 1) (count η 2)) = x ^ 2 := hval
      rw [h₁] at hc₁
      rw [ht''] at hxsq
      rw [hε₁] at hm₂
      linarith
    -- the fitted mean
    have hphi := phiHat_eq one_mem_cutRange hn0 hsum
    have hs : 0 < √(n : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast hn0)
    have hB := scaleB_pos one_mem_cutRange
    have hclose₂ := hphat _ _ _ hsum hb₂
    obtain ⟨hp₁, hp₂⟩ := abs_lt.1 hclose₂
    rw [hphi] at hp₁ hp₂
    set ψ := 3 * (count η 1 + count η 2) / (2 * (count η 0 + count η 1 + count η 2)) with hψ
    have hψe : ψ = 1 - 3 / 2 * (scaleB 1 * y) / √(n : ℝ) := hphi
    have hψlt : ψ ≤ 1 := by
      rw [hψe]
      have : 0 ≤ 3 / 2 * (scaleB 1 * y) / √(n : ℝ) := by positivity
      linarith
    have hphatψ : phat = ψ := min_eq_right hψlt
    have hψ0 : 0 < ψ := by
      rw [hψe]
      linarith
    have hψ1 : ψ < 3 / 2 := by linarith
    have hge := abs_muZero_ge (m := count η 0 + count η 1 + count η 2) hψ0 hψ1
    rw [hsum, abs_of_nonneg (muZero_nonneg_of_le_one hψlt),
      abs_of_nonneg (by linarith : 0 ≤ 1 - ψ)] at hge
    have hB2 : scaleB 1 = √2 / 3 := by
      unfold scaleB
      norm_num
    have hs₂ : √(2 * (n : ℝ)) = √2 * √(n : ℝ) := Real.sqrt_mul (by norm_num) _
    have h2 : √2 * √2 = (2 : ℝ) := Real.mul_self_sqrt (by norm_num)
    have hbig : 2 / 3 * y ≤ muZero ψ n := by
      refine le_trans (le_of_eq ?_) hge
      have e : √2 * √(n : ℝ) * (1 - (1 - 3 / 2 * (√2 / 3 * y) / √(n : ℝ))) * (2 / 3) =
          (√2 * √2) * y / 3 := by
        field_simp
        ring
      rw [hψe, hs₂, hB2, e, h2]
      ring
    have hμbig : M ≤ muZero phat (count η 0 + count η 1 + count η 2) := by
      rw [hphatψ, hsum]
      have hMy : M < 2 / 3 * y := by linarith only [hy₁]
      exact hMy.le.trans hbig
    exact (t1Tail_anti _ hSge).trans (htail _ hμbig)

end Phylogenetics.Trinomial

namespace External.MitchellAllmanRhodes2019

open Phylogenetics Phylogenetics.Trinomial Phylogenetics.QuartetTests

/-- **Proposition 5.2** (`ext:t1_density`) of the source, under the name of its number, with `μ₀ = muZero φ n`:
`QuartetTests.t1Var_density`. -/
theorem proposition5_2 (φ n : ℝ) :
    (∀ lam, 0 ≤ t1Density (muZero φ n) lam) ∧
      ((gaussianReal 0 1).prod (gaussianReal (muZero φ n) 1)).map t1Var =
        volume.withDensity (fun lam => ENNReal.ofReal (t1Density (muZero φ n) lam)) :=
  t1Var_density _

/-- **Proposition 5.1** (`ext:t1_approx`) of Mitchell, Allman, Rhodes 2019, for the trinomial. At the true point
`θ₀ = (1 - 2φ/3, φ/3, φ/3)`, `0 < φ ≤ 1`, the likelihood ratio statistic of model T1 and the variable `t1Var`, with `Z ~ N(0, 1)`,
`Z̄ ~ N(μ₀(n), 1)` independent, converge in distribution to the same limit. For `φ < 1` the limit is `χ²₁`; for `φ = 1` it is the law of
`t1Var` under `stdPlane`, which is `½ χ²₁ + ½ χ²₂` (`QuartetTests.t1Tail_zero`).

Departure from the source: it takes the first step from its Theorem 3.1 and so from van der Vaart's Theorem 16.7, which Mathlib lacks.
Here it is proved for this model directly from the central limit theorem. -/
theorem proposition5_1 {φ : ℝ} (hφ : 0 < φ ∧ φ < 3 / 2) (hφ1 : φ ≤ 1) : ∃ ν : ProbabilityMeasure ℝ,
    (∀ f : BoundedContinuousFunction ℝ ℝ,
      Tendsto (fun n : ℕ ↦ ∫ x, f x ∂((Measure.pi fun _ : Fin n ↦
          (cutPoint_isDist hφ).toPMF.toMeasure).map fun η ↦ t1S (count η 0) (count η 1) (count η 2)))
        atTop (𝓝 (∫ x, f x ∂(ν : Measure ℝ)))) ∧
    (∀ f : BoundedContinuousFunction ℝ ℝ,
      Tendsto (fun n : ℕ ↦ ∫ x, f x ∂((normalSample (muZero φ n)).map t1Var))
        atTop (𝓝 (∫ x, f x ∂(ν : Measure ℝ)))) := by
  rcases hφ1.eq_or_lt with rfl | hlt
  · refine ⟨⟨stdPlane.map t1Var, inferInstance⟩, fun f ↦ ?_, fun f ↦ ?_⟩
    · exact ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.1
        tendstoInDistribution_t1S_centroid.tendsto f
    · have hsample : ∀ n : ℕ, normalSample (muZero 1 n) = stdPlane := by
        intro n
        rw [muZero_one]
        rfl
      simp only [hsample]
      exact tendsto_const_nhds
  · have hT : Continuous fun z : ℝ × ℝ ↦ z.1 ^ 2 := by fun_prop
    have hSm : ∀ n : ℕ, AEMeasurable (fun η : Fin n → Fin 3 ↦ t1S (count η 0) (count η 1) (count η 2))
        (Measure.pi fun _ : Fin n ↦ (cutPoint_isDist hφ).toPMF.toMeasure) :=
      fun n ↦ Measurable.of_discrete.aemeasurable
    refine ⟨⟨stdPlane.map fun z ↦ z.1 ^ 2, inferInstance⟩, fun f ↦ ?_, fun f ↦ ?_⟩
    · exact ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.1
        (tendstoInDistribution_of_closeOnBalls (tendstoInDistribution_sampleW hφ) hSm hT
          (closeOnBalls_t1S_of_lt hφ hlt)).tendsto f
    · have hlaw : TendstoInDistribution (fun (n : ℕ) (z : ℝ × ℝ) ↦ (z.1, z.2 - muZero φ n)) atTop
          (fun z : ℝ × ℝ ↦ z) (fun n : ℕ ↦ normalSample (muZero φ n)) stdPlane := by
        refine ⟨fun n ↦ (by fun_prop), by fun_prop, ?_⟩
        simp only [normalSample_map_sub]
        have : stdPlane.map (fun z : ℝ × ℝ ↦ z) = stdPlane := Measure.map_id'
        simp only [this]
        exact tendsto_const_nhds
      exact ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.1
        (tendstoInDistribution_of_closeOnBalls hlaw
          (S := fun (_ : ℕ) (z : ℝ × ℝ) ↦ t1Var z)
          (fun n ↦ continuous_t1Var.aemeasurable)
          hT (closeOnBalls_t1Var_of_lt hφ hlt)).tendsto f

end External.MitchellAllmanRhodes2019

namespace Phylogenetics.QuartetTests

open Trinomial

variable {X : Type*} [Fintype X] [DecidableEq X] {Γ : Type*} [Fintype Γ] {dist : Γ → ℝ}
  {sides : Γ → Finset (Finset X)}

/-- The T1 statistic through the counts of the three topologies. -/
theorem t1Stat_eq_t1S (c : QuartetTree X → ℝ) {s r₁ r₂ : QuartetTree X} (hne : r₁ ≠ r₂)
    (h : s.alternatives = {r₁, r₂}) : t1Stat c s = t1S (c s) (c r₁) (c r₂) := by
  unfold t1Stat t1S
  rw [h, Finset.sum_pair hne, lineStat_eq_lineS c hne h, starStat_eq_starS c hne h]

/-- **The limit law of the T1 statistic at the boundary point** (`ext:t1_limit`). At a concordance factor `(1/3, 1/3, 1/3)`, the tail at every
`t` of the T1 statistic of a sample tends to `t1Tail 0 t`, which is that of `½ χ²₁ + ½ χ²₂` (`t1Tail_zero`).

Departure from the source: it reads this off its Theorem 3.1. Here the limit comes from the central limit theorem for the trinomial. -/
theorem t1Stat_limitLaw (hd : IsDist dist) (hs : DisplaysOne dist sides) {s : QuartetTree X}
    (h : ∀ r ∈ treesOn s.taxa, displayCF dist sides r = 1 / 3) (t : ℝ) :
    Tendsto (fun n => iidProb dist n fun ω => t < t1Stat (quartetCount sides ω) s) atTop
      (𝓝 (t1Tail 0 t)) := by
  obtain ⟨r₁, r₂, hne, hr⟩ := QuartetTree.exists_alternatives s
  have := tendsto_iidProb_lt_t1S_centroid t
  rw [← pushDist_eq_centroid hd hs hne hr h] at this
  refine this.congr fun n ↦ ?_
  rw [← iidProb_three_counts hs hne hr n (fun a b c ↦ t < t1S a b c)]
  simp only [t1Stat_eq_t1S _ hne hr]

/-- **Off the boundary, the limit law of the T1 statistic is `χ²₁`** (`ext:t1_approx`). -/
theorem t1Stat_limitLaw_of_isT1Strict (hd : IsDist dist) (hs : DisplaysOne dist sides) {s : QuartetTree X}
    (hstrict : IsT1Strict (displayCF dist sides) s)
    (hpos : ∀ r ∈ s.alternatives, 0 < displayCF dist sides r) (t : ℝ) :
    Tendsto (fun n => iidProb dist n fun ω => t < t1Stat (quartetCount sides ω) s) atTop
      (𝓝 (chiSqOneTail t)) := by
  obtain ⟨r₁, r₂, hne, hr⟩ := QuartetTree.exists_alternatives s
  have hm₁ : r₁ ∈ s.alternatives := by rw [hr]; simp
  have hm₂ : r₂ ∈ s.alternatives := by rw [hr]; simp
  have heq := hstrict.2 r₁ hm₁ r₂ hm₂
  have hsum := sum_displayCF_treesOn hd hs s.card_taxa
  rw [sum_treesOn _ hne hr, ← heq] at hsum
  have hlt := hstrict.1 r₁ hm₁
  have hq0 := hpos r₁ hm₁
  have hφ : 0 < 3 * displayCF dist sides r₁ ∧ 3 * displayCF dist sides r₁ < 3 / 2 := by
    constructor <;> linarith
  have hφ1 : 3 * displayCF dist sides r₁ < 1 := by linarith
  have := tendsto_iidProb_lt_t1S_of_lt hφ hφ1 t
  rw [← pushDist_eq_cutPoint hd hs hne hr heq] at this
  refine this.congr fun n ↦ ?_
  rw [← iidProb_three_counts hs hne hr n (fun a b c ↦ t < t1S a b c)]
  simp only [t1Stat_eq_t1S _ hne hr]

/-- `t1Stat_limitLaw` on distribution functions, with the density of Proposition 5.2 (`ext:t1_limit`). -/
theorem t1Stat_limitLaw_density (hd : IsDist dist) (hs : DisplaysOne dist sides) {s : QuartetTree X}
    (h : ∀ r ∈ treesOn s.taxa, displayCF dist sides r = 1 / 3) (t : ℝ) :
    Tendsto (fun n => iidProb dist n fun ω => t1Stat (quartetCount sides ω) s ≤ t) atTop
      (𝓝 (∫ v in Iic t, t1Density 0 v)) := by
  rw [← one_sub_t1Tail_eq_integral]
  refine ((tendsto_const_nhds (x := (1 : ℝ))).sub (t1Stat_limitLaw hd hs h t)).congr fun n ↦ ?_
  rw [← iidProb_not hd]
  simp only [not_lt]

/-- The law of the T1 statistic of a sample is that of the trinomial statistic on the three counts, at the boundary point. -/
theorem map_t1Stat_eq [MeasurableSpace Γ] [MeasurableSingletonClass Γ] (hd : IsDist dist)
    (hs : DisplaysOne dist sides) {s r₁ r₂ : QuartetTree X} (hne : r₁ ≠ r₂)
    (hr : s.alternatives = {r₁, r₂}) (h : ∀ r ∈ treesOn s.taxa, displayCF dist sides r = 1 / 3) (n : ℕ) :
    (Measure.pi fun _ : Fin n ↦ hd.toPMF.toMeasure).map (fun ω ↦ t1Stat (quartetCount sides ω) s) =
      (Measure.pi fun _ : Fin n ↦ (cutPoint_isDist one_mem_cutRange).toPMF.toMeasure).map
        (fun η ↦ t1S (count η 0) (count η 1) (count η 2)) := by
  refine Measure.ext fun A hA ↦ ?_
  rw [Measure.map_apply Measurable.of_discrete hA, Measure.map_apply Measurable.of_discrete hA]
  have h₁ := iidProb_eq_pi hd n (fun ω ↦ t1Stat (quartetCount sides ω) s ∈ A)
  have h₂ := iidProb_eq_pi (cutPoint_isDist one_mem_cutRange) n
    (fun η ↦ t1S (count η 0) (count η 1) (count η 2) ∈ A)
  have h₃ := iidProb_three_counts hs hne hr n (fun a b c ↦ t1S a b c ∈ A)
  rw [pushDist_eq_centroid hd hs hne hr h] at h₃
  simp only [← t1Stat_eq_t1S _ hne hr] at h₃
  rw [h₁, h₂] at h₃
  exact (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).1 h₃

/-- `t1Stat_limitLaw` as convergence in distribution (`ext:t1_limit`), for the law of a sample as a product measure. -/
theorem tendstoInDistribution_t1Stat [MeasurableSpace Γ] [MeasurableSingletonClass Γ] (hd : IsDist dist)
    (hs : DisplaysOne dist sides) {s : QuartetTree X}
    (h : ∀ r ∈ treesOn s.taxa, displayCF dist sides r = 1 / 3) :
    TendstoInDistribution (fun (n : ℕ) (ω : Fin n → Γ) ↦ t1Stat (quartetCount sides ω) s) atTop
      t1Var (fun n ↦ Measure.pi fun _ : Fin n ↦ hd.toPMF.toMeasure) stdPlane := by
  obtain ⟨r₁, r₂, hne, hr⟩ := QuartetTree.exists_alternatives s
  refine ⟨fun n ↦ Measurable.of_discrete.aemeasurable, continuous_t1Var.aemeasurable, ?_⟩
  exact tendstoInDistribution_t1S_centroid.tendsto.congr fun n ↦
    Subtype.ext (map_t1Stat_eq hd hs hne hr h n).symm

/-- **With the true parameter, the T1 p-value at the boundary point is asymptotically uniform** (`ext:t1_pvalue_true`): the p-value read from
the law at the true `μ₀ = 0`, as in the source's simulations at the boundary. -/
theorem t1Tail_t1Stat_asymptoticallyUniform (hd : IsDist dist) (hs : DisplaysOne dist sides) {s : QuartetTree X}
    (h : ∀ r ∈ treesOn s.taxa, displayCF dist sides r = 1 / 3) :
    AsymptoticallyUniform dist fun _ ω => t1Tail 0 (t1Stat (quartetCount sides ω) s) :=
  asymptoticallyUniform_of_tendsto_tail hd (G := t1Tail 0)
    (S := fun _ ω => t1Stat (quartetCount sides ω) s)
    (fun _ _ hst => t1Tail_anti 0 hst)
    (fun _ _ => (chiSqOneTail_pos _).trans_le (chiSqOneTail_le_t1Tail _ _))
    (fun _ hx hx1 => (exists_t1Tail_eq le_rfl hx hx1).imp fun _ ht => ht.2)
    (t1Stat_limitLaw hd hs h)

/-- **With the fitted parameter, the T1 p-value at the boundary point is not asymptotically uniform** (`ext:t1_pvalue_fitted`). ECToBlob says of the
T1 test, in its Section 8: "if the expected quartet CFs satisfy the null hypothesis, then the p-value from each individual 4-taxon set has a
uniform distribution on `[0, 1]`, asymptotically as the number of genes increases", just after excepting the boundary point from the `χ²₁`
limit. So that sentence holds off this point only: this is E13 of the report, whose repair is `t1PValue_centroid_tight`. The fitted p-value is
at most the one with the true parameter (`t1Tail_le_t1Tail_zero`), which is asymptotically uniform (`t1Tail_t1Stat_asymptoticallyUniform`), and
strictly below it with positive limit probability, so at the level exhibited here the test rejects too often. -/
theorem t1PValue_centroid_not_asymptoticallyUniform (hd : IsDist dist) (hs : DisplaysOne dist sides)
    {s : QuartetTree X} (h : ∀ r ∈ treesOn s.taxa, displayCF dist sides r = 1 / 3) :
    ¬ AsymptoticallyUniform dist fun _ ω => t1PValue (quartetCount sides ω) s := by
  intro hU
  obtain ⟨r₁, r₂, hne, hr⟩ := QuartetTree.exists_alternatives s
  obtain ⟨a, c, ha0, ha1, hac, hev⟩ := exists_lt_iidProb_t1PValueR_centroid
  rw [← pushDist_eq_centroid hd hs hne hr h] at hev
  have hlim := hU a ha0.le ha1.le
  obtain ⟨n, hn₁, hn₂⟩ := (hev.and (hlim.eventually (gt_mem_nhds hac))).exists
  rw [← iidProb_three_counts hs hne hr n (fun x y z ↦ t1PValueR x y z ≤ a)] at hn₁
  simp only [t1PValue_eq_t1PValueR _ hne hr] at hn₂
  linarith

end Phylogenetics.QuartetTests
