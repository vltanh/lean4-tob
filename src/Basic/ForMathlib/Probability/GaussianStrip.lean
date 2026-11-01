module

public import Basic.ForMathlib.Probability.GaussianPlane

/-!
# The law of the distance in a polar strip of the plane

For a pair of independent unit normals, the probability of a polar strip `polarStrip σ k x` is the
integral over `(0, x]` of a normal density times the probability that a second normal exceeds a line:
the strip's density `stripDensity`. This packages the steps of `Basic.ForMathlib.Probability.GaussianPlane`:
polar coordinates, differentiating under the integral sign, the substitution `y = σ x tan β`, and the
fundamental theorem of calculus from `x = 0`.

Also: the reflections of the plane that send a pair of independent unit normals to a pair of independent
unit normals, and the change of variable from a distance to its square.

Main results: `ProbabilityTheory.IsPolarSector.hasDerivAt_polarStripIntegral_stripDensity`,
`ProbabilityTheory.IsPolarSector.measure_polarStrip_eq_lintegral_stripDensity`,
`ProbabilityTheory.measure_reflect_preimage`, `ProbabilityTheory.measure_reflect_x_preimage`,
`ProbabilityTheory.lintegral_Ioc_eq_lintegral_sq`; and the oddness of the error function, `Real.erf_neg`,
`Real.tendsto_erf_atBot`.
-/

@[expose] public noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace Real

theorem sin_pos_of_mem {α : ℝ} (hα : α ∈ Ioo 0 (π / 2)) : 0 < sin α :=
  sin_pos_of_pos_of_lt_pi hα.1 (by linarith [hα.2, pi_pos])

theorem cos_pos_of_mem {α : ℝ} (hα : α ∈ Ioo 0 (π / 2)) : 0 < cos α :=
  cos_pos_of_mem_Ioo ⟨by linarith [hα.1, pi_pos], hα.2⟩

/-- The error function is odd. -/
theorem erf_neg (x : ℝ) : erf (-x) = -erf x := by
  have h := intervalIntegral.integral_comp_neg (a := 0) (b := x) fun t : ℝ => Real.exp (-(t ^ 2))
  simp only [neg_sq, neg_zero] at h
  have h' : ∫ t in (0 : ℝ)..-x, Real.exp (-(t ^ 2)) = -∫ t in (0 : ℝ)..x, Real.exp (-(t ^ 2)) := by
    rw [h]
    exact intervalIntegral.integral_symm _ _
  unfold erf
  rw [h']
  ring

theorem neg_one_le_erf (x : ℝ) : -1 ≤ erf x := by
  have := erf_le_one (-x)
  rw [erf_neg] at this
  linarith

/-- The limit of the error function at negative infinity is minus one. -/
theorem tendsto_erf_atBot : Tendsto erf atBot (𝓝 (-1)) := by
  have h := (tendsto_erf_atTop.comp tendsto_neg_atBot_atTop).neg
  refine h.congr fun x => ?_
  simp [erf_neg]

end Real

namespace ProbabilityTheory

/-- The density of the strip: a normal density of mean `p` at `u`, times the probability that a unit normal
of mean `q` exceeds `k u`. -/
def stripDensity (p q k u : ℝ) : ℝ :=
  gaussianPDFReal p 1 u * (1 / 2 * (1 - Real.erf ((k * u - q) / √2)))

theorem stripDensity_nonneg (p q k u : ℝ) : 0 ≤ stripDensity p q k u :=
  mul_nonneg (gaussianPDFReal_nonneg _ _ _) (by linarith [Real.erf_le_one ((k * u - q) / √2)])

theorem continuous_stripDensity (p q k : ℝ) : Continuous (stripDensity p q k) := by
  have h1 : Continuous (gaussianPDFReal p 1) := by
    unfold gaussianPDFReal
    fun_prop
  have := Real.continuous_erf
  unfold stripDensity
  fun_prop

variable {σ a b k : ℝ}

/-- For `x > 0`, the derivative of the double integral in polar coordinates is the density of the strip:
differentiation under the integral sign, then the substitution `y = σ x tan β`. -/
theorem IsPolarSector.hasDerivAt_polarStripIntegral_stripDensity (h : IsPolarSector σ a b k)
    (m₁ m₂ : ℝ) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (polarStripIntegral σ a b m₁ m₂) (stripDensity (σ * m₁) m₂ k x) x := by
  have hd := h.hasDerivAt_polarStripIntegral m₁ m₂ hx
  rwa [h.integral_polarDensity_mul m₁ m₂ hx] at hd

/-- **The law of the distance in a polar strip.** The probability of the part of the strip within distance
`x` of the vertical axis is the integral of the density of the strip over `(0, x]`. -/
theorem IsPolarSector.measure_polarStrip_eq_lintegral_stripDensity (h : IsPolarSector σ a b k)
    (m₁ m₂ x : ℝ) :
    ((gaussianReal m₁ 1).prod (gaussianReal m₂ 1)) (polarStrip σ k x) =
      ∫⁻ u in Ioc 0 x, ENNReal.ofReal (stripDensity (σ * m₁) m₂ k u) :=
  measure_polarStrip_eq_lintegral_of_hasDerivAt σ k _ (G := polarStripIntegral σ a b m₁ m₂)
    (fun _ hx => h.toReal_measure_polarStrip m₁ m₂ hx)
    (fun _ hx => h.hasDerivAt_polarStripIntegral_stripDensity m₁ m₂ hx)
    (continuous_stripDensity _ _ _) (stripDensity_nonneg _ _ _) x

/-- The reflection of the plane with matrix `[[s, c], [c, -s]]`, for `s² + c² = 1`, sends a pair of independent
unit normals to a pair of independent unit normals, with the mean reflected. -/
theorem measure_reflect_preimage {s c : ℝ} (hsc : s ^ 2 + c ^ 2 = 1) (m₁ m₂ : ℝ) {A : Set (ℝ × ℝ)}
    (hA : MeasurableSet A) :
    ((gaussianReal m₁ 1).prod (gaussianReal m₂ 1)) {z | (s * z.1 + c * z.2, c * z.1 - s * z.2) ∈ A} =
      ((gaussianReal (s * m₁ + c * m₂) 1).prod (gaussianReal (c * m₁ - s * m₂) 1)) A := by
  have h := gaussianReal_prod_map_orthonormal (a := s) (b := c) (a' := c) (b' := -s) hsc
    (by rw [neg_sq, add_comm]; exact hsc) (by ring) m₁ m₂
  have e : (fun z : ℝ × ℝ => (s * z.1 + c * z.2, c * z.1 + -s * z.2)) =
      fun z => (s * z.1 + c * z.2, c * z.1 - s * z.2) := by
    funext z
    simp only [neg_mul, sub_eq_add_neg]
  rw [e, show c * m₁ + -s * m₂ = c * m₁ - s * m₂ by ring] at h
  have hm : Measurable fun z : ℝ × ℝ => (s * z.1 + c * z.2, c * z.1 - s * z.2) := by fun_prop
  rw [← h, Measure.map_apply hm hA]
  rfl

/-- The reflection about the vertical axis preserves a pair of independent unit normals with first mean zero. -/
theorem measure_reflect_x_preimage (μ : ℝ) {A : Set (ℝ × ℝ)} (hA : MeasurableSet A) :
    ((gaussianReal 0 1).prod (gaussianReal μ 1)) {z | (-z.1, z.2) ∈ A} =
      ((gaussianReal 0 1).prod (gaussianReal μ 1)) A := by
  have h := gaussianReal_prod_map_orthonormal (a := -1) (b := 0) (a' := 0) (b' := 1)
    (by norm_num) (by norm_num) (by norm_num) 0 μ
  have e : (fun z : ℝ × ℝ => (-1 * z.1 + 0 * z.2, 0 * z.1 + 1 * z.2)) = fun z => (-z.1, z.2) := by
    funext z
    simp
  rw [e, show (-1 : ℝ) * 0 + 0 * μ = 0 by ring, show (0 : ℝ) * 0 + 1 * μ = μ by ring] at h
  have hm : Measurable fun z : ℝ × ℝ => (-z.1, z.2) := by fun_prop
  calc ((gaussianReal 0 1).prod (gaussianReal μ 1)) {z | (-z.1, z.2) ∈ A} =
      (((gaussianReal 0 1).prod (gaussianReal μ 1)).map fun z : ℝ × ℝ => (-z.1, z.2)) A :=
        (Measure.map_apply hm hA).symm
    _ = _ := by rw [h]

/-- The image of `(0, √t]` under squaring is `(0, t]`, also when both are empty. -/
theorem sq_image_Ioc_sqrt (t : ℝ) : (fun u : ℝ => u ^ 2) '' Ioc 0 √t = Ioc 0 t := by
  ext v
  simp only [mem_image, mem_Ioc]
  constructor
  · rintro ⟨u, ⟨hu, hut⟩, rfl⟩
    exact ⟨by positivity, (Real.le_sqrt' hu).1 hut⟩
  · rintro ⟨hv, hvt⟩
    exact ⟨√v, ⟨Real.sqrt_pos.2 hv, Real.sqrt_le_sqrt hvt⟩, Real.sq_sqrt hv.le⟩

/-- The change of variable from a distance to its square. -/
theorem lintegral_Ioc_eq_lintegral_sq (t : ℝ) (f : ℝ → ℝ≥0∞) :
    ∫⁻ v in Ioc 0 t, f v = ∫⁻ u in Ioc 0 √t, ENNReal.ofReal (2 * u) * f (u ^ 2) := by
  rw [← sq_image_Ioc_sqrt t, lintegral_image_eq_lintegral_abs_deriv_mul (f' := fun u => 2 * u)
    measurableSet_Ioc]
  · refine setLIntegral_congr_fun measurableSet_Ioc fun u hu => ?_
    simp only [abs_of_pos (mul_pos two_pos hu.1)]
  · intro u _
    simpa using (hasDerivAt_pow 2 u).hasDerivWithinAt
  · intro a ha b hb hab
    exact (sq_eq_sq₀ ha.1.le hb.1.le).1 hab

end ProbabilityTheory
