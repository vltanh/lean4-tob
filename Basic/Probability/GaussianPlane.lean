module

public import Basic.Analysis.SpecialFunctions.Erf
public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic

/-!
# Independent unit normals on the plane

The law of a pair of independent unit normals under an orthonormal change of coordinates, the
probability of half-open strips in such coordinates (in terms of the error function), and the
nullity of lines.

Main results: `ProbabilityTheory.gaussianReal_Ioi_eq_erf`,
`ProbabilityTheory.gaussianReal_prod_map_orthonormal`, `ProbabilityTheory.gaussianReal_prod_strip`,
`ProbabilityTheory.gaussianReal_prod_line_null`, `ProbabilityTheory.gaussianReal_prod_split`.
-/

@[expose] public noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace ProbabilityTheory

/-- The upper tail of a unit normal, by the error function. -/
theorem gaussianReal_Ioi_eq_erf (m a : ℝ) :
    gaussianReal m 1 (Ioi a) = ENNReal.ofReal (1 / 2 * (1 - Real.erf ((a - m) / √2))) := by
  rw [gaussianReal_apply_eq_integral m one_ne_zero]
  congr 1
  have h2 : (0 : ℝ) < √2 := by positivity
  have hderiv : ∀ x ∈ Ici a, HasDerivAt (fun x => 1 / 2 * Real.erf ((x - m) / √2))
      (gaussianPDFReal m 1 x) x := by
    intro x _
    have h := ((Real.hasDerivAt_erf ((x - m) / √2)).comp x
      (((hasDerivAt_id x).sub_const m).div_const √2)).const_mul (1 / 2)
    convert h using 1
    · simp only [id, Function.comp]
    · have hpdf : gaussianPDFReal m 1 x =
          (√(2 * Real.pi))⁻¹ * Real.exp (-(x - m) ^ 2 / 2) := by
        simp [gaussianPDFReal]
      have e1 : ((x - m) / √2) ^ 2 = (x - m) ^ 2 / 2 := by
        rw [div_pow, Real.sq_sqrt (by norm_num)]
      rw [hpdf, e1, Real.sqrt_mul (by norm_num), neg_div]
      have hpi : √Real.pi ≠ 0 := (Real.sqrt_pos.2 Real.pi_pos).ne'
      field_simp
  have hlim : Tendsto (fun x => 1 / 2 * Real.erf ((x - m) / √2)) atTop (𝓝 (1 / 2)) := by
    have h1 : Tendsto (fun x : ℝ => (x - m) / √2) atTop atTop :=
      (tendsto_atTop_add_const_right _ (-m) tendsto_id).atTop_div_const h2
    have := (Real.tendsto_erf_atTop.comp h1).const_mul (1 / 2)
    simpa using this
  rw [integral_Ioi_of_hasDerivAt_of_tendsto' hderiv
    (integrable_gaussianPDFReal m 1).integrableOn hlim]
  ring

private lemma charFunDual_gaussianReal_one (m : ℝ) (L : StrongDual ℝ ℝ) :
    charFunDual (gaussianReal m 1) L =
      Complex.exp (((L 1 * m : ℝ) : ℂ) * Complex.I - (((L 1) ^ 2 : ℝ) : ℂ) / 2) := by
  have h := charFun_gaussianReal (μ := m) (v := 1) (L 1)
  rw [charFun_apply_real] at h
  rw [charFunDual_apply]
  have e : ∀ v : ℝ, ((L v : ℝ) : ℂ) * Complex.I = ((L 1 : ℝ) : ℂ) * (v : ℂ) * Complex.I := by
    intro v
    have : L v = L 1 * v := by
      have := L.map_smul v 1
      simp only [smul_eq_mul, mul_one] at this
      rw [this]; ring
    rw [this]; push_cast; ring
  simp_rw [e]
  rw [h]
  congr 1
  push_cast
  ring

private lemma strongDual_prod_apply (L : StrongDual ℝ (ℝ × ℝ)) (x y : ℝ) :
    L (x, y) = x * L (1, 0) + y * L (0, 1) := by
  have : ((x, y) : ℝ × ℝ) = x • ((1, 0) : ℝ × ℝ) + y • ((0, 1) : ℝ × ℝ) := by
    ext <;> simp
  rw [this, map_add, map_smul, map_smul]
  simp

/-- An orthonormal change of coordinates sends a pair of independent unit normals to a pair of
independent unit normals, with the means transformed in the same way. -/
theorem gaussianReal_prod_map_orthonormal {a b a' b' : ℝ} (h₁ : a ^ 2 + b ^ 2 = 1)
    (h₂ : a' ^ 2 + b' ^ 2 = 1) (h₃ : a * a' + b * b' = 0) (m₁ m₂ : ℝ) :
    ((gaussianReal m₁ 1).prod (gaussianReal m₂ 1)).map
        (fun z : ℝ × ℝ => (a * z.1 + b * z.2, a' * z.1 + b' * z.2)) =
      (gaussianReal (a * m₁ + b * m₂) 1).prod (gaussianReal (a' * m₁ + b' * m₂) 1) := by
  let R : ℝ × ℝ →L[ℝ] ℝ × ℝ :=
    (a • ContinuousLinearMap.fst ℝ ℝ ℝ + b • ContinuousLinearMap.snd ℝ ℝ ℝ).prod
      (a' • ContinuousLinearMap.fst ℝ ℝ ℝ + b' • ContinuousLinearMap.snd ℝ ℝ ℝ)
  have hR : (fun z : ℝ × ℝ => (a * z.1 + b * z.2, a' * z.1 + b' * z.2)) = R := by
    funext z; simp [R]
  rw [hR]
  apply Measure.ext_of_charFunDual
  funext L
  rw [charFunDual_map, charFunDual_prod, charFunDual_prod, charFunDual_gaussianReal_one,
    charFunDual_gaussianReal_one, charFunDual_gaussianReal_one, charFunDual_gaussianReal_one,
    ← Complex.exp_add, ← Complex.exp_add]
  congr 1
  have hR10 : R (1, 0) = (a, a') := by ext <;> simp [R]
  have hR01 : R (0, 1) = (b, b') := by ext <;> simp [R]
  have e1 : ((L.comp R).comp (.inl ℝ ℝ ℝ)) 1 = a * L (1, 0) + a' * L (0, 1) := by
    have : ((L.comp R).comp (.inl ℝ ℝ ℝ)) 1 = L (R (1, 0)) := rfl
    rw [this, hR10, strongDual_prod_apply]
  have e2 : ((L.comp R).comp (.inr ℝ ℝ ℝ)) 1 = b * L (1, 0) + b' * L (0, 1) := by
    have : ((L.comp R).comp (.inr ℝ ℝ ℝ)) 1 = L (R (0, 1)) := rfl
    rw [this, hR01, strongDual_prod_apply]
  have e3 : (L.comp (.inl ℝ ℝ ℝ)) 1 = L (1, 0) := by simp
  have e4 : (L.comp (.inr ℝ ℝ ℝ)) 1 = L (0, 1) := by simp
  rw [e1, e2, e3, e4]
  generalize L (1, 0) = l₁
  generalize L (0, 1) = l₂
  have key : (a * l₁ + a' * l₂) ^ 2 + (b * l₁ + b' * l₂) ^ 2 = l₁ ^ 2 + l₂ ^ 2 := by
    linear_combination l₁ ^ 2 * h₁ + l₂ ^ 2 * h₂ + 2 * l₁ * l₂ * h₃
  have key' : (((a * l₁ + a' * l₂) ^ 2 + (b * l₁ + b' * l₂) ^ 2 : ℝ) : ℂ) =
      ((l₁ ^ 2 + l₂ ^ 2 : ℝ) : ℂ) := congrArg _ key
  push_cast at key' ⊢
  linear_combination (-1 / 2 : ℂ) * key'

/-- The probability of a half-open strip in orthonormal coordinates `u = a x + b y`,
`v = a' x + b' y`: the set where `0 < u ≤ x` and `v > k u`. -/
theorem gaussianReal_prod_strip {a b a' b' : ℝ} (h₁ : a ^ 2 + b ^ 2 = 1)
    (h₂ : a' ^ 2 + b' ^ 2 = 1) (h₃ : a * a' + b * b' = 0) (m₁ m₂ k x : ℝ) :
    ((gaussianReal m₁ 1).prod (gaussianReal m₂ 1))
        {z | 0 < a * z.1 + b * z.2 ∧ a * z.1 + b * z.2 ≤ x ∧
          k * (a * z.1 + b * z.2) < a' * z.1 + b' * z.2} =
      ∫⁻ u in Ioc 0 x, ENNReal.ofReal (gaussianPDFReal (a * m₁ + b * m₂) 1 u *
        (1 / 2 * (1 - Real.erf ((k * u - (a' * m₁ + b' * m₂)) / √2)))) := by
  set T : Set (ℝ × ℝ) := {w | 0 < w.1 ∧ w.1 ≤ x ∧ k * w.1 < w.2} with hTdef
  have hT : MeasurableSet T := by
    refine (measurableSet_lt measurable_const measurable_fst).inter
      ((measurableSet_le measurable_fst measurable_const).inter
        (measurableSet_lt (measurable_const.mul measurable_fst) measurable_snd))
  have hmeas : Measurable (fun z : ℝ × ℝ => (a * z.1 + b * z.2, a' * z.1 + b' * z.2)) := by
    fun_prop
  have hS : {z : ℝ × ℝ | 0 < a * z.1 + b * z.2 ∧ a * z.1 + b * z.2 ≤ x ∧
      k * (a * z.1 + b * z.2) < a' * z.1 + b' * z.2} =
      (fun z : ℝ × ℝ => (a * z.1 + b * z.2, a' * z.1 + b' * z.2)) ⁻¹' T := rfl
  rw [hS, ← Measure.map_apply hmeas hT, gaussianReal_prod_map_orthonormal h₁ h₂ h₃,
    Measure.prod_apply hT]
  set p := a * m₁ + b * m₂
  set q := a' * m₁ + b' * m₂
  have hf : ∀ u : ℝ, gaussianReal q 1 (Prod.mk u ⁻¹' T) = (Ioc 0 x).indicator
      (fun u => ENNReal.ofReal (1 / 2 * (1 - Real.erf ((k * u - q) / √2)))) u := by
    intro u
    by_cases hu : u ∈ Ioc 0 x
    · rw [indicator_of_mem hu, ← gaussianReal_Ioi_eq_erf]
      congr 1
      ext v
      simp [hTdef, hu.1, hu.2]
    · rw [indicator_of_notMem hu]
      have : Prod.mk u ⁻¹' T = ∅ := by
        ext v
        simp only [hTdef, mem_preimage, mem_ofPred_eq, mem_empty_iff_false, iff_false]
        rintro ⟨h1, h2, -⟩
        exact hu ⟨h1, h2⟩
      rw [this, measure_empty]
  simp_rw [hf]
  have hmeas2 : Measurable
      (fun u => ENNReal.ofReal (1 / 2 * (1 - Real.erf ((k * u - q) / √2)))) := by
    apply ENNReal.measurable_ofReal.comp
    apply Continuous.measurable
    have := Real.continuous_erf
    fun_prop
  rw [lintegral_indicator measurableSet_Ioc, gaussianReal_of_var_ne_zero p one_ne_zero,
    restrict_withDensity measurableSet_Ioc,
    lintegral_withDensity_eq_lintegral_mul _ (measurable_gaussianPDF p 1) hmeas2]
  refine lintegral_congr fun u => ?_
  simp only [Pi.mul_apply, gaussianPDF]
  rw [ENNReal.ofReal_mul (gaussianPDFReal_nonneg _ _ _)]

/-- Lines are null for a pair of independent unit normals. -/
theorem gaussianReal_prod_line_null {k₁ k₂ : ℝ} (h : k₁ ≠ 0 ∨ k₂ ≠ 0) (m₁ m₂ : ℝ) :
    ((gaussianReal m₁ 1).prod (gaussianReal m₂ 1)) {z | k₁ * z.1 + k₂ * z.2 = 0} = 0 := by
  have hn₁ := nullSingletonClass_gaussianReal (μ := m₁) (v := 1) one_ne_zero
  have hn₂ := nullSingletonClass_gaussianReal (μ := m₂) (v := 1) one_ne_zero
  by_cases hk : k₂ = 0
  · have hk₁ : k₁ ≠ 0 := h.resolve_right (not_not.2 hk)
    have : {z : ℝ × ℝ | k₁ * z.1 + k₂ * z.2 = 0} = {0} ×ˢ univ := by
      ext z
      simp [hk, hk₁]
    rw [this, Measure.prod_prod, measure_singleton, zero_mul]
  · have hmeas : MeasurableSet {z : ℝ × ℝ | k₁ * z.1 + k₂ * z.2 = 0} :=
      measurableSet_eq_fun (by fun_prop) (by fun_prop)
    rw [Measure.measure_prod_null hmeas]
    refine Eventually.of_forall fun x => ?_
    have : Prod.mk x ⁻¹' {z : ℝ × ℝ | k₁ * z.1 + k₂ * z.2 = 0} = {-(k₁ * x) / k₂} := by
      ext y
      simp only [mem_preimage, mem_ofPred_eq, mem_singleton_iff]
      constructor
      · intro hy
        field_simp
        linarith
      · rintro rfl
        field_simp
        ring
    simp [this, measure_singleton]

/-- A set is split by a line, up to a null set. -/
theorem gaussianReal_prod_split {k₁ k₂ : ℝ} (h : k₁ ≠ 0 ∨ k₂ ≠ 0) (m₁ m₂ : ℝ) (A : Set (ℝ × ℝ)) :
    ((gaussianReal m₁ 1).prod (gaussianReal m₂ 1)) A =
      ((gaussianReal m₁ 1).prod (gaussianReal m₂ 1)) (A ∩ {z | 0 < k₁ * z.1 + k₂ * z.2}) +
        ((gaussianReal m₁ 1).prod (gaussianReal m₂ 1)) (A ∩ {z | k₁ * z.1 + k₂ * z.2 < 0}) := by
  have hmeas : MeasurableSet {z : ℝ × ℝ | 0 < k₁ * z.1 + k₂ * z.2} :=
    measurableSet_lt measurable_const (by fun_prop)
  rw [← measure_inter_add_sdiff A hmeas]
  congr 1
  apply measure_congr
  have hne : ∀ᵐ z ∂((gaussianReal m₁ 1).prod (gaussianReal m₂ 1)), k₁ * z.1 + k₂ * z.2 ≠ 0 := by
    rw [ae_iff]
    simpa using gaussianReal_prod_line_null h m₁ m₂
  filter_upwards [hne] with z hz
  apply propext
  simp only [Set.mem_sdiff, mem_inter_iff, mem_ofPred_eq, not_lt]
  constructor
  · exact fun hh => ⟨hh.1, lt_of_le_of_ne hh.2 hz⟩
  · exact fun hh => ⟨hh.1, hh.2.le⟩

end ProbabilityTheory
