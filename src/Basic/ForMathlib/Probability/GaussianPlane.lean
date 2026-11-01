module

public import Basic.ForMathlib.Analysis.SpecialFunctions.Erf
public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
public import Mathlib.Analysis.SpecialFunctions.PolarCoord
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.MeasureTheory.Function.JacobianOneDim
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv

/-!
# Independent unit normals on the plane

The law of a pair of independent unit normals under an orthonormal change of coordinates and under a
rotation, the nullity of lines, and the probability of half-open strips in polar coordinates: as a
double integral, its derivative in the width of the strip by differentiating under the integral
sign, and the value of this derivative in terms of the error function.

Main results: `ProbabilityTheory.integral_gaussianPDFReal_Ioi`,
`ProbabilityTheory.gaussianReal_Ioi_eq_erf`, `ProbabilityTheory.gaussianReal_prod_map_orthonormal`,
`ProbabilityTheory.gaussianReal_prod_line_null`, `ProbabilityTheory.gaussianReal_prod_split`,
`ProbabilityTheory.IsPolarSector.measure_polarStrip`,
`ProbabilityTheory.IsPolarSector.hasDerivAt_polarStripIntegral`,
`ProbabilityTheory.IsPolarSector.integral_polarDensity_mul`,
`ProbabilityTheory.measure_polarStrip_eq_lintegral_of_hasDerivAt`,
`ProbabilityTheory.measure_rotate_preimage`.
-/

@[expose] public noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace ProbabilityTheory

/-- The upper tail of a unit normal as an integral of its density, by the error function. -/
theorem integral_gaussianPDFReal_Ioi (m a : ℝ) :
    ∫ x in Ioi a, gaussianPDFReal m 1 x = 1 / 2 * (1 - Real.erf ((a - m) / √2)) := by
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

/-- The upper tail of a unit normal, by the error function. -/
theorem gaussianReal_Ioi_eq_erf (m a : ℝ) :
    gaussianReal m 1 (Ioi a) = ENNReal.ofReal (1 / 2 * (1 - Real.erf ((a - m) / √2))) := by
  rw [gaussianReal_apply_eq_integral m one_ne_zero, integral_gaussianPDFReal_Ioi]

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

/-! ### Polar coordinates -/

/-- The value of the normal density with unit variance. -/
theorem gaussianPDFReal_one (m x : ℝ) :
    gaussianPDFReal m 1 x = (√(2 * Real.pi))⁻¹ * Real.exp (-(x - m) ^ 2 / 2) := by
  simp [gaussianPDFReal]

/-- The density of `N((m₁, m₂), I)` at the point of polar coordinates `(r, β)`:
`(1 / 2π) exp (-(r² - 2 r ⟨m, (cos β, sin β)⟩ + |m|²) / 2)`. -/
def polarDensity (m₁ m₂ r β : ℝ) : ℝ :=
  1 / (2 * Real.pi) * Real.exp (-(1 / 2) * (r ^ 2 - 2 * r * (m₁ * Real.cos β + m₂ * Real.sin β) +
    (m₁ ^ 2 + m₂ ^ 2)))

theorem polarDensity_nonneg (m₁ m₂ r β : ℝ) : 0 ≤ polarDensity m₁ m₂ r β := by
  unfold polarDensity
  positivity

theorem gaussianPDFReal_mul_gaussianPDFReal_eq_polarDensity (m₁ m₂ r β : ℝ) :
    gaussianPDFReal m₁ 1 (r * Real.cos β) * gaussianPDFReal m₂ 1 (r * Real.sin β) =
      polarDensity m₁ m₂ r β := by
  rw [gaussianPDFReal_one, gaussianPDFReal_one, polarDensity]
  have hπ : (√(2 * Real.pi))⁻¹ * (√(2 * Real.pi))⁻¹ = 1 / (2 * Real.pi) := by
    rw [← mul_inv, Real.mul_self_sqrt (by positivity), one_div]
  rw [mul_mul_mul_comm, hπ, ← Real.exp_add]
  congr 2
  linear_combination (-(r ^ 2) / 2) * Real.sin_sq_add_cos_sq β

theorem continuous_polarDensity (m₁ m₂ : ℝ) :
    Continuous fun p : ℝ × ℝ => polarDensity m₁ m₂ p.1 p.2 := by
  unfold polarDensity
  fun_prop

/-- The inner integral in polar coordinates is continuous in the angle and the upper limit. -/
theorem continuous_integral_polarDensity (m₁ m₂ : ℝ) :
    Continuous fun p : ℝ × ℝ => ∫ r in (0 : ℝ)..p.2, polarDensity m₁ m₂ r p.1 * r := by
  refine intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
    (f := fun (p : ℝ × ℝ) r => polarDensity m₁ m₂ r p.1 * r) ?_ continuous_snd
  have := continuous_polarDensity m₁ m₂
  have h : Continuous fun q : (ℝ × ℝ) × ℝ => polarDensity m₁ m₂ q.2 q.1.1 :=
    this.comp (continuous_snd.prodMk (continuous_fst.comp continuous_fst))
  exact h.mul continuous_snd

/-- The strip `0 < σ X ≤ x`, `Y > k σ X`, for `σ = ± 1`. -/
def polarStrip (σ k x : ℝ) : Set (ℝ × ℝ) := {z | 0 < σ * z.1 ∧ σ * z.1 ≤ x ∧ k * (σ * z.1) < z.2}

theorem measurableSet_polarStrip (σ k x : ℝ) : MeasurableSet (polarStrip σ k x) := by
  have hm : Measurable fun z : ℝ × ℝ => σ * z.1 := measurable_const.mul measurable_fst
  exact (measurableSet_lt measurable_const hm).inter
    ((measurableSet_le hm measurable_const).inter
      (measurableSet_lt (measurable_const.mul hm) measurable_snd))

/-- The angular sector `(a, b)` of the strip `polarStrip σ k x`, for `σ = ± 1`: the points
`(r cos β, r sin β)` with `r > 0` and `β ∈ (-π, π)` that have `σ X > 0` and `Y > k σ X` are those
with `β ∈ (a, b)`, and `σ tan` is a bijection from `(a, b)` onto `(k, ∞)`. For `σ = 1` the sector is
`(a, π / 2)`, with `k = tan a` (`IsPolarSector.right`); for `σ = -1` it is `(π / 2, b)`, with
`k = -tan b` (`IsPolarSector.left`). -/
structure IsPolarSector (σ a b k : ℝ) : Prop where
  le : a ≤ b
  sq : σ ^ 2 = 1
  subset : Ioo a b ⊆ Ioo (-Real.pi) Real.pi
  mem_iff : ∀ β ∈ Ioo (-Real.pi) Real.pi,
    β ∈ Ioo a b ↔ 0 < σ * Real.cos β ∧ k * (σ * Real.cos β) < Real.sin β
  image : (fun β => σ * Real.tan β) '' Ioo a b = Ioi k
  injOn : InjOn (fun β => σ * Real.tan β) (Ioo a b)

section Sector

open Real

private lemma mem_Ioo_of_cos_pos {β : ℝ} (hβ : β ∈ Ioo (-π) π) (hc : 0 < cos β) :
    β ∈ Ioo (-(π / 2)) (π / 2) := by
  constructor
  · by_contra h
    have : cos (-β) ≤ 0 := cos_nonpos_of_pi_div_two_le_of_le (by linarith) (by linarith [hβ.1])
    rw [cos_neg] at this
    linarith
  · by_contra h
    have : cos β ≤ 0 := cos_nonpos_of_pi_div_two_le_of_le (by linarith) (by linarith [hβ.2])
    linarith

/-- The sector `(a, π / 2)` to the right of the vertical axis, above the ray of angle `a`. -/
theorem IsPolarSector.right {a : ℝ} (h₁ : -(π / 2) < a) (h₂ : a < π / 2) :
    IsPolarSector 1 a (π / 2) (tan a) where
  le := h₂.le
  sq := one_pow 2
  subset := fun β hβ => ⟨by linarith [hβ.1, pi_pos], by linarith [hβ.2, pi_pos]⟩
  mem_iff := by
    intro β hβ
    rw [one_mul]
    constructor
    · rintro ⟨h3, h4⟩
      have hβ' : β ∈ Ioo (-(π / 2)) (π / 2) := ⟨by linarith, h4⟩
      have hc := cos_pos_of_mem_Ioo hβ'
      have hlt := strictMonoOn_tan ⟨h₁, h₂⟩ hβ' h3
      rw [tan_eq_sin_div_cos β, lt_div_iff₀ hc] at hlt
      exact ⟨hc, hlt⟩
    · rintro ⟨h3, h4⟩
      have hβ' := mem_Ioo_of_cos_pos hβ h3
      have hlt : tan a < tan β := by
        rw [tan_eq_sin_div_cos β, lt_div_iff₀ h3]
        exact h4
      exact ⟨(strictMonoOn_tan.lt_iff_lt ⟨h₁, h₂⟩ hβ').1 hlt, hβ'.2⟩
  image := by
    ext y
    simp only [one_mul, mem_image, mem_Ioi]
    constructor
    · rintro ⟨β, hβ, rfl⟩
      exact strictMonoOn_tan ⟨h₁, h₂⟩ ⟨by linarith [hβ.1], hβ.2⟩ hβ.1
    · intro hy
      refine ⟨arctan y, ⟨?_, arctan_lt_pi_div_two y⟩, tan_arctan y⟩
      refine (strictMonoOn_tan.lt_iff_lt ⟨h₁, h₂⟩ ⟨neg_pi_div_two_lt_arctan y,
        arctan_lt_pi_div_two y⟩).1 ?_
      rwa [tan_arctan]
  injOn := by
    intro u hu v hv huv
    simp only [one_mul] at huv
    exact injOn_tan ⟨by linarith [hu.1], hu.2⟩ ⟨by linarith [hv.1], hv.2⟩ huv

private lemma tan_lt_tan_iff_of_mem {u v : ℝ} (hu : u ∈ Ioo (π / 2) π) (hv : v ∈ Ioo (π / 2) π) :
    tan u < tan v ↔ u < v := by
  rw [← tan_sub_pi u, ← tan_sub_pi v, strictMonoOn_tan.lt_iff_lt
    ⟨by linarith [hu.1], by linarith [hu.2, pi_pos]⟩
    ⟨by linarith [hv.1], by linarith [hv.2, pi_pos]⟩]
  constructor <;> intro <;> linarith

private lemma tan_neg_of_mem {v : ℝ} (hv : v ∈ Ioo (π / 2) π) : tan v < 0 := by
  rw [tan_eq_sin_div_cos]
  exact div_neg_of_pos_of_neg (sin_pos_of_pos_of_lt_pi (by linarith [hv.1, pi_pos]) hv.2)
    (cos_neg_of_pi_div_two_lt_of_lt hv.1 (by linarith [hv.2, pi_pos]))

/-- The sector `(π / 2, b)` to the left of the vertical axis, above the ray of angle `b`. -/
theorem IsPolarSector.left {b : ℝ} (h₁ : π / 2 < b) (h₂ : b < π) :
    IsPolarSector (-1) (π / 2) b (-tan b) where
  le := h₁.le
  sq := by norm_num
  subset := fun β hβ => ⟨by linarith [hβ.1, pi_pos], by linarith [hβ.2]⟩
  mem_iff := by
    intro β hβ
    constructor
    · rintro ⟨h3, h4⟩
      have hβ' : β ∈ Ioo (π / 2) π := ⟨h3, by linarith⟩
      have hc := cos_neg_of_pi_div_two_lt_of_lt h3 (by linarith [hβ'.2, pi_pos])
      have hlt := (tan_lt_tan_iff_of_mem hβ' ⟨h₁, h₂⟩).2 h4
      refine ⟨by linarith, ?_⟩
      have := tan_mul_cos hc.ne
      nlinarith
    · rintro ⟨h3, h4⟩
      have hc : cos β < 0 := by linarith
      have hb := tan_neg_of_mem (v := b) ⟨h₁, h₂⟩
      have hs : 0 < sin β := by nlinarith [mul_pos_of_neg_of_neg hb hc]
      have hβ0 : 0 < β := by
        by_contra h
        have := sin_nonpos_of_nonpos_of_neg_pi_le (not_lt.1 h) hβ.1.le
        linarith
      have hβ1 : π / 2 < β := by
        by_contra h
        have := cos_nonneg_of_neg_pi_div_two_le_of_le (by linarith [pi_pos]) (not_lt.1 h)
        linarith
      have hβ' : β ∈ Ioo (π / 2) π := ⟨hβ1, hβ.2⟩
      refine ⟨hβ1, (tan_lt_tan_iff_of_mem hβ' ⟨h₁, h₂⟩).1 ?_⟩
      have := tan_mul_cos hc.ne
      nlinarith
  image := by
    ext y
    simp only [mem_image, mem_Ioi, neg_mul, one_mul]
    constructor
    · rintro ⟨β, hβ, rfl⟩
      have := (tan_lt_tan_iff_of_mem ⟨hβ.1, by linarith [hβ.2]⟩ ⟨h₁, h₂⟩).2 hβ.2
      linarith
    · intro hy
      have hlt : arctan (-y) < b - π := by
        rw [← arctan_tan (x := b - π) (by linarith) (by linarith [pi_pos]), tan_sub_pi]
        exact arctan_strictMono (by linarith)
      refine ⟨arctan (-y) + π, ⟨by linarith [neg_pi_div_two_lt_arctan (-y)], by linarith⟩, ?_⟩
      rw [tan_add_pi, tan_arctan, neg_neg]
  injOn := by
    intro u hu v hv huv
    simp only [neg_mul, one_mul, neg_inj] at huv
    have hu' : u ∈ Ioo (π / 2) π := ⟨hu.1, by linarith [hu.2]⟩
    have hv' : v ∈ Ioo (π / 2) π := ⟨hv.1, by linarith [hv.2]⟩
    rw [← tan_sub_pi u, ← tan_sub_pi v] at huv
    have := injOn_tan ⟨by linarith [hu'.1], by linarith [hu'.2, pi_pos]⟩
      ⟨by linarith [hv'.1], by linarith [hv'.2, pi_pos]⟩ huv
    linarith

end Sector

section Strip

variable {σ a b k : ℝ}

theorem IsPolarSector.ne_zero (h : IsPolarSector σ a b k) : σ ≠ 0 := by
  have := h.sq
  rintro rfl
  norm_num at this

theorem IsPolarSector.cos_pos (h : IsPolarSector σ a b k) {β : ℝ} (hβ : β ∈ Ioo a b) :
    0 < σ * Real.cos β :=
  ((h.mem_iff β (h.subset hβ)).1 hβ).1

theorem IsPolarSector.cos_ne_zero (h : IsPolarSector σ a b k) {β : ℝ} (hβ : β ∈ Ioo a b) :
    Real.cos β ≠ 0 := by
  have := h.cos_pos hβ
  intro h0
  rw [h0, mul_zero] at this
  exact lt_irrefl _ this

/-- The upper limit of the radius in the strip: `σ x / cos β = x / (σ cos β)`. -/
theorem IsPolarSector.mul_div_cos (h : IsPolarSector σ a b k) {β : ℝ} (hβ : β ∈ Ioo a b) (x : ℝ) :
    σ * x / Real.cos β = x / (σ * Real.cos β) := by
  have hc := h.cos_ne_zero hβ
  rw [div_eq_div_iff hc (mul_ne_zero h.ne_zero hc)]
  linear_combination (x * Real.cos β) * h.sq

/-- The strip in polar coordinates. -/
theorem IsPolarSector.polar_mem_iff (h : IsPolarSector σ a b k) (x r β : ℝ) :
    ((r, β) ∈ polarCoord.target ∧ polarCoord.symm (r, β) ∈ polarStrip σ k x) ↔
      β ∈ Ioo a b ∧ r ∈ Ioc 0 (σ * x / Real.cos β) := by
  have htarget : (r, β) ∈ polarCoord.target ↔ 0 < r ∧ β ∈ Ioo (-Real.pi) Real.pi := by
    simp [polarCoord_target]
  have hstrip : polarCoord.symm (r, β) ∈ polarStrip σ k x ↔
      0 < σ * (r * Real.cos β) ∧ σ * (r * Real.cos β) ≤ x ∧
        k * (σ * (r * Real.cos β)) < r * Real.sin β := by
    simp [polarStrip, polarCoord]
  rw [htarget, hstrip]
  constructor
  · rintro ⟨⟨hr, hβ⟩, h1, h2, h3⟩
    have hc : 0 < σ * Real.cos β := by
      have : σ * (r * Real.cos β) = r * (σ * Real.cos β) := by ring
      rw [this] at h1
      exact (mul_pos_iff_of_pos_left hr).1 h1
    have hk : k * (σ * Real.cos β) < Real.sin β := by
      have : k * (σ * (r * Real.cos β)) = r * (k * (σ * Real.cos β)) := by ring
      rw [this] at h3
      exact lt_of_mul_lt_mul_left h3 hr.le
    have hβ' := (h.mem_iff β hβ).2 ⟨hc, hk⟩
    refine ⟨hβ', hr, ?_⟩
    rw [h.mul_div_cos hβ', le_div_iff₀ hc]
    linarith
  · rintro ⟨hβ, hr, hrx⟩
    obtain ⟨hc, hk⟩ := (h.mem_iff β (h.subset hβ)).1 hβ
    rw [h.mul_div_cos hβ, le_div_iff₀ hc] at hrx
    refine ⟨⟨hr, h.subset hβ⟩, ?_, ?_, ?_⟩
    · have := mul_pos hr hc
      linarith
    · linarith
    · have := mul_lt_mul_of_pos_left hk hr
      linarith

/-- The upper limit of the radius is positive. -/
theorem IsPolarSector.radius_pos (h : IsPolarSector σ a b k) {x : ℝ} (hx : 0 < x) {β : ℝ}
    (hβ : β ∈ Ioo a b) : 0 < σ * x / Real.cos β := by
  rw [h.mul_div_cos hβ]
  exact div_pos hx (h.cos_pos hβ)

/-- **Polar coordinates.** The probability of the strip is the integral of the density in polar
coordinates. -/
theorem IsPolarSector.measure_polarStrip_eq_lintegral (h : IsPolarSector σ a b k) (m₁ m₂ : ℝ)
    {x : ℝ} (hx : 0 < x) :
    ((gaussianReal m₁ 1).prod (gaussianReal m₂ 1)) (polarStrip σ k x) =
      ∫⁻ β in Ioo a b, ENNReal.ofReal
        (∫ r in (0 : ℝ)..σ * x / Real.cos β, polarDensity m₁ m₂ r β * r) := by
  have hS := measurableSet_polarStrip σ k x
  set D : ℝ × ℝ → ℝ≥0∞ := fun z => gaussianPDF m₁ 1 z.1 * gaussianPDF m₂ 1 z.2 with hD
  have hDm : Measurable D :=
    ((measurable_gaussianPDF m₁ 1).comp measurable_fst).mul
      ((measurable_gaussianPDF m₂ 1).comp measurable_snd)
  have e1 : ((gaussianReal m₁ 1).prod (gaussianReal m₂ 1)) (polarStrip σ k x) =
      ∫⁻ z, (polarStrip σ k x).indicator D z := by
    rw [gaussianReal_of_var_ne_zero m₁ one_ne_zero, gaussianReal_of_var_ne_zero m₂ one_ne_zero,
      prod_withDensity (measurable_gaussianPDF _ _) (measurable_gaussianPDF _ _),
      withDensity_apply _ hS, lintegral_indicator hS, Measure.volume_eq_prod]
  have hmeas : Measurable fun p : ℝ × ℝ => polarCoord.target.indicator
      (fun p => ENNReal.ofReal p.1 • (polarStrip σ k x).indicator D (polarCoord.symm p)) p := by
    refine Measurable.indicator ?_ polarCoord.open_target.measurableSet
    refine (ENNReal.measurable_ofReal.comp measurable_fst).smul ?_
    exact (hDm.indicator hS).comp continuous_polarCoord_symm.measurable
  have hpt : ∀ r β, polarCoord.target.indicator
      (fun p => ENNReal.ofReal p.1 • (polarStrip σ k x).indicator D (polarCoord.symm p)) (r, β) =
      (Ioo a b).indicator (fun β => (Ioc 0 (σ * x / Real.cos β)).indicator
        (fun r => ENNReal.ofReal (polarDensity m₁ m₂ r β * r)) r) β := by
    intro r β
    by_cases hm : (r, β) ∈ polarCoord.target ∧ polarCoord.symm (r, β) ∈ polarStrip σ k x
    · obtain ⟨hβ, hr⟩ := (h.polar_mem_iff x r β).1 hm
      rw [indicator_of_mem hm.1, indicator_of_mem hm.2, indicator_of_mem hβ, indicator_of_mem hr]
      have hsymm : polarCoord.symm (r, β) = (r * Real.cos β, r * Real.sin β) := by
        simp [polarCoord]
      simp only [hD, hsymm, gaussianPDF, smul_eq_mul]
      rw [← ENNReal.ofReal_mul (gaussianPDFReal_nonneg _ _ _),
        gaussianPDFReal_mul_gaussianPDFReal_eq_polarDensity, ← ENNReal.ofReal_mul hr.1.le,
        mul_comm]
    · have hm' := (not_congr (h.polar_mem_iff x r β)).1 hm
      have hl : polarCoord.target.indicator
          (fun p => ENNReal.ofReal p.1 • (polarStrip σ k x).indicator D (polarCoord.symm p))
          (r, β) = 0 := by
        by_cases h1 : (r, β) ∈ polarCoord.target
        · rw [indicator_of_mem h1, indicator_of_notMem (fun h2 => hm ⟨h1, h2⟩), smul_zero]
        · exact indicator_of_notMem h1 _
      rw [hl]
      by_cases h1 : β ∈ Ioo a b
      · rw [indicator_of_mem h1, indicator_of_notMem (fun h2 => hm' ⟨h1, h2⟩)]
      · rw [indicator_of_notMem h1]
  rw [e1, ← lintegral_comp_polarCoord_symm, ← lintegral_indicator
    polarCoord.open_target.measurableSet, Measure.volume_eq_prod, lintegral_prod_symm _
    hmeas.aemeasurable, ← lintegral_indicator measurableSet_Ioo]
  refine lintegral_congr fun β => ?_
  simp only [hpt]
  by_cases hβ : β ∈ Ioo a b
  · simp only [indicator_of_mem hβ]
    have hR := h.radius_pos hx hβ
    have hint : IntegrableOn (fun r => polarDensity m₁ m₂ r β * r)
        (Ioc 0 (σ * x / Real.cos β)) := by
      have hc : Continuous fun r => polarDensity m₁ m₂ r β * r :=
        ((continuous_polarDensity m₁ m₂).comp (continuous_id.prodMk continuous_const)).mul
          continuous_id
      exact hc.integrableOn_Ioc
    rw [lintegral_indicator measurableSet_Ioc, intervalIntegral.integral_of_le hR.le,
      ofReal_integral_eq_lintegral_ofReal hint]
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
    exact mul_nonneg (polarDensity_nonneg _ _ _ _) hr.1.le
  · simp only [indicator_of_notMem hβ]
    simp

/-- The inner integral is measurable in the angle. -/
theorem measurable_integral_polarDensity (m₁ m₂ σ x : ℝ) :
    Measurable fun β => ∫ r in (0 : ℝ)..σ * x / Real.cos β, polarDensity m₁ m₂ r β * r :=
  (continuous_integral_polarDensity m₁ m₂).measurable.comp
    (measurable_id.prodMk (measurable_const.div Real.measurable_cos))

/-- The inner integral is nonnegative on the sector. -/
theorem IsPolarSector.integral_polarDensity_nonneg (h : IsPolarSector σ a b k) (m₁ m₂ : ℝ)
    {x : ℝ} (hx : 0 < x) {β : ℝ} (hβ : β ∈ Ioo a b) :
    0 ≤ ∫ r in (0 : ℝ)..σ * x / Real.cos β, polarDensity m₁ m₂ r β * r :=
  intervalIntegral.integral_nonneg (h.radius_pos hx hβ).le fun _ hr =>
    mul_nonneg (polarDensity_nonneg _ _ _ _) hr.1

/-- The inner integral is integrable on the sector, since the strip has finite probability. -/
theorem IsPolarSector.integrableOn_integral_polarDensity (h : IsPolarSector σ a b k) (m₁ m₂ : ℝ)
    {x : ℝ} (hx : 0 < x) :
    IntegrableOn (fun β => ∫ r in (0 : ℝ)..σ * x / Real.cos β, polarDensity m₁ m₂ r β * r)
      (Ioo a b) := by
  refine ⟨(measurable_integral_polarDensity m₁ m₂ σ x).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal, ← h.measure_polarStrip_eq_lintegral m₁ m₂ hx]
  · exact measure_lt_top _ _
  · filter_upwards [ae_restrict_mem measurableSet_Ioo] with β hβ
    exact h.integral_polarDensity_nonneg m₁ m₂ hx hβ

/-- The double integral in polar coordinates over the sector `(a, b)`, up to the line at distance
`x` from the vertical axis: `∫_a^b ∫_0^{σ x / cos β} (density) r dr dβ`. -/
def polarStripIntegral (σ a b m₁ m₂ x : ℝ) : ℝ :=
  ∫ β in a..b, ∫ r in (0 : ℝ)..σ * x / Real.cos β, polarDensity m₁ m₂ r β * r

/-- The probability of the strip is the double integral in polar coordinates. -/
theorem IsPolarSector.measure_polarStrip (h : IsPolarSector σ a b k) (m₁ m₂ : ℝ) {x : ℝ}
    (hx : 0 < x) :
    ((gaussianReal m₁ 1).prod (gaussianReal m₂ 1)) (polarStrip σ k x) =
      ENNReal.ofReal (polarStripIntegral σ a b m₁ m₂ x) := by
  rw [h.measure_polarStrip_eq_lintegral m₁ m₂ hx, polarStripIntegral,
    intervalIntegral.integral_of_le h.le, integral_Ioc_eq_integral_Ioo,
    ofReal_integral_eq_lintegral_ofReal (h.integrableOn_integral_polarDensity m₁ m₂ hx)]
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with β hβ
  exact h.integral_polarDensity_nonneg m₁ m₂ hx hβ

theorem IsPolarSector.polarStripIntegral_nonneg (h : IsPolarSector σ a b k) (m₁ m₂ : ℝ) {x : ℝ}
    (hx : 0 < x) : 0 ≤ polarStripIntegral σ a b m₁ m₂ x := by
  rw [polarStripIntegral, intervalIntegral.integral_of_le h.le, integral_Ioc_eq_integral_Ioo]
  exact setIntegral_nonneg measurableSet_Ioo fun β hβ =>
    h.integral_polarDensity_nonneg m₁ m₂ hx hβ

theorem IsPolarSector.toReal_measure_polarStrip (h : IsPolarSector σ a b k) (m₁ m₂ : ℝ) {x : ℝ}
    (hx : 0 < x) :
    (((gaussianReal m₁ 1).prod (gaussianReal m₂ 1)) (polarStrip σ k x)).toReal =
      polarStripIntegral σ a b m₁ m₂ x := by
  rw [h.measure_polarStrip m₁ m₂ hx, ENNReal.toReal_ofReal (h.polarStripIntegral_nonneg m₁ m₂ hx)]

/-- On the sector, the density on the line at distance `x` from the vertical axis factors: the
point has coordinates `(σ x, x σ tan β)`. -/
theorem IsPolarSector.polarDensity_eq (h : IsPolarSector σ a b k) (m₁ m₂ x : ℝ) {β : ℝ}
    (hβ : β ∈ Ioo a b) :
    polarDensity m₁ m₂ (σ * x / Real.cos β) β =
      gaussianPDFReal (σ * m₁) 1 x * gaussianPDFReal m₂ 1 (x * (σ * Real.tan β)) := by
  have hc := h.cos_ne_zero hβ
  rw [← gaussianPDFReal_mul_gaussianPDFReal_eq_polarDensity, div_mul_cancel₀ _ hc]
  have e2 : σ * x / Real.cos β * Real.sin β = x * (σ * Real.tan β) := by
    rw [Real.tan_eq_sin_div_cos]
    ring
  rw [e2]
  congr 1
  rw [gaussianPDFReal_one, gaussianPDFReal_one]
  congr 2
  linear_combination (-(x ^ 2 - m₁ ^ 2) / 2) * h.sq

/-- The derivative in `x` of the inner integral on the sector. -/
theorem IsPolarSector.hasDerivAt_integral_polarDensity (h : IsPolarSector σ a b k) (m₁ m₂ x : ℝ)
    {β : ℝ} (hβ : β ∈ Ioo a b) :
    HasDerivAt (fun x => ∫ r in (0 : ℝ)..σ * x / Real.cos β, polarDensity m₁ m₂ r β * r)
      (polarDensity m₁ m₂ (σ * x / Real.cos β) β * (x / Real.cos β ^ 2)) x := by
  have hc := h.cos_ne_zero hβ
  have hcont : Continuous fun r => polarDensity m₁ m₂ r β * r :=
    ((continuous_polarDensity m₁ m₂).comp (continuous_id.prodMk continuous_const)).mul
      continuous_id
  have hF := (hcont.integral_hasStrictDerivAt 0 (σ * x / Real.cos β)).hasDerivAt
  have hR : HasDerivAt (fun x => σ * x / Real.cos β) (σ / Real.cos β) x := by
    simpa using ((hasDerivAt_id x).const_mul σ).div_const (Real.cos β)
  have e : polarDensity m₁ m₂ (σ * x / Real.cos β) β * (x / Real.cos β ^ 2) =
      polarDensity m₁ m₂ (σ * x / Real.cos β) β * (σ * x / Real.cos β) * (σ / Real.cos β) := by
    have e' : x / Real.cos β ^ 2 = σ * x / Real.cos β * (σ / Real.cos β) := by
      field_simp
      linear_combination (-x) * h.sq
    rw [e', mul_assoc]
  rw [e]
  exact hF.comp x hR

/-- The function `σ tan` has the derivative `σ / cos²` on the sector. -/
theorem IsPolarSector.hasDerivWithinAt_tan (h : IsPolarSector σ a b k) {β : ℝ}
    (hβ : β ∈ Ioo a b) :
    HasDerivWithinAt (fun β => σ * Real.tan β) (σ / Real.cos β ^ 2) (Ioo a b) β := by
  have := (Real.hasDerivAt_tan (h.cos_ne_zero hβ)).const_mul σ
  convert this.hasDerivWithinAt using 1
  ring

/-- `|σ / cos²| = 1 / cos²`. -/
theorem IsPolarSector.abs_div_cos_sq (h : IsPolarSector σ a b k) (β : ℝ) :
    |σ / Real.cos β ^ 2| = 1 / Real.cos β ^ 2 := by
  have hσ : |σ| = 1 :=
    (sq_eq_sq₀ (abs_nonneg σ) zero_le_one).1 (by rw [sq_abs, h.sq, one_pow])
  rw [abs_div, hσ, abs_of_nonneg (by positivity)]

/-- The bound on the derivative in `x` of the inner integral, for `x` in `(x₀ / 2, 2 x₀)`. -/
theorem IsPolarSector.polarDensity_mul_le (h : IsPolarSector σ a b k) (m₁ m₂ : ℝ) {x₀ x : ℝ}
    (hx₀ : 0 < x₀) (hx : x ∈ Ioo (x₀ / 2) (2 * x₀)) {β : ℝ} (hβ : β ∈ Ioo a b) :
    ‖polarDensity m₁ m₂ (σ * x / Real.cos β) β * (x / Real.cos β ^ 2)‖ ≤
      ((√(2 * Real.pi))⁻¹ * (√(2 * Real.pi))⁻¹ * Real.exp (m₂ ^ 2 / 2) * (2 * x₀)) *
        (|σ / Real.cos β ^ 2| • Real.exp (-(x₀ ^ 2 / 16) * (σ * Real.tan β) ^ 2)) := by
  have hxpos : 0 < x := by linarith [hx.1]
  have hK : 0 ≤ (√(2 * Real.pi))⁻¹ := by positivity
  rw [h.polarDensity_eq m₁ m₂ x hβ, h.abs_div_cos_sq, smul_eq_mul, Real.norm_of_nonneg
    (mul_nonneg (mul_nonneg (gaussianPDFReal_nonneg _ _ _) (gaussianPDFReal_nonneg _ _ _))
      (by positivity))]
  set T := σ * Real.tan β
  have h1 : gaussianPDFReal (σ * m₁) 1 x ≤ (√(2 * Real.pi))⁻¹ := by
    rw [gaussianPDFReal_one]
    refine mul_le_of_le_one_right hK (Real.exp_le_one_iff.2 ?_)
    have := sq_nonneg (x - σ * m₁)
    linarith
  have h2 : gaussianPDFReal m₂ 1 (x * T) ≤
      (√(2 * Real.pi))⁻¹ * (Real.exp (m₂ ^ 2 / 2) * Real.exp (-(x₀ ^ 2 / 16) * T ^ 2)) := by
    rw [gaussianPDFReal_one]
    refine mul_le_mul_of_nonneg_left ?_ hK
    rw [← Real.exp_add]
    refine Real.exp_le_exp.2 ?_
    have hx2 : x₀ ^ 2 / 4 ≤ x ^ 2 := by nlinarith [hx.1]
    have hT : (x₀ ^ 2 / 4) * T ^ 2 ≤ x ^ 2 * T ^ 2 :=
      mul_le_mul_of_nonneg_right hx2 (sq_nonneg T)
    nlinarith [sq_nonneg (x * T - 2 * m₂)]
  have h3 : x / Real.cos β ^ 2 ≤ 2 * x₀ * (1 / Real.cos β ^ 2) := by
    rw [mul_one_div]
    exact div_le_div_of_nonneg_right hx.2.le (by positivity)
  calc gaussianPDFReal (σ * m₁) 1 x * gaussianPDFReal m₂ 1 (x * T) * (x / Real.cos β ^ 2)
      ≤ (√(2 * Real.pi))⁻¹ * ((√(2 * Real.pi))⁻¹ *
          (Real.exp (m₂ ^ 2 / 2) * Real.exp (-(x₀ ^ 2 / 16) * T ^ 2))) *
          (2 * x₀ * (1 / Real.cos β ^ 2)) := by
        refine mul_le_mul (mul_le_mul h1 h2 (gaussianPDFReal_nonneg _ _ _) hK) h3
          (by positivity) (by positivity)
    _ = _ := by ring

/-- **Differentiation under the integral sign**: for `x > 0`, the derivative of the double integral
in polar coordinates is the integral over the sector of the derivative of the inner integral. -/
theorem IsPolarSector.hasDerivAt_polarStripIntegral (h : IsPolarSector σ a b k) (m₁ m₂ : ℝ)
    {x₀ : ℝ} (hx₀ : 0 < x₀) :
    HasDerivAt (polarStripIntegral σ a b m₁ m₂)
      (∫ β in a..b, polarDensity m₁ m₂ (σ * x₀ / Real.cos β) β * (x₀ / Real.cos β ^ 2)) x₀ := by
  have hfun : polarStripIntegral σ a b m₁ m₂ = fun x => ∫ β in Ioo a b,
      ∫ r in (0 : ℝ)..σ * x / Real.cos β, polarDensity m₁ m₂ r β * r := by
    funext x
    rw [polarStripIntegral, intervalIntegral.integral_of_le h.le, integral_Ioc_eq_integral_Ioo]
  rw [hfun, intervalIntegral.integral_of_le h.le, integral_Ioc_eq_integral_Ioo]
  have hg : Integrable (fun T : ℝ => Real.exp (-(x₀ ^ 2 / 16) * T ^ 2)) :=
    integrable_exp_neg_mul_sq (by positivity)
  have hbound := (integrableOn_image_iff_integrableOn_abs_deriv_smul measurableSet_Ioo
    (fun β hβ => h.hasDerivWithinAt_tan hβ) h.injOn
    (fun T : ℝ => Real.exp (-(x₀ ^ 2 / 16) * T ^ 2))).1 hg.integrableOn
  have hm : Measurable fun β => polarDensity m₁ m₂ (σ * x₀ / Real.cos β) β :=
    Measurable.comp (g := fun p : ℝ × ℝ => polarDensity m₁ m₂ p.1 p.2)
      (f := fun β => (σ * x₀ / Real.cos β, β)) (continuous_polarDensity m₁ m₂).measurable
      ((measurable_const.div Real.measurable_cos).prodMk measurable_id)
  have h1 : Ioo (x₀ / 2) (2 * x₀) ∈ 𝓝 x₀ := Ioo_mem_nhds (by linarith) (by linarith)
  have h2 : ∀ᶠ x in 𝓝 x₀, AEStronglyMeasurable (fun β => ∫ r in (0 : ℝ)..σ * x / Real.cos β,
      polarDensity m₁ m₂ r β * r) (volume.restrict (Ioo a b)) :=
    Eventually.of_forall fun x => (measurable_integral_polarDensity m₁ m₂ σ x).aestronglyMeasurable
  have h3 : Integrable (fun β => ∫ r in (0 : ℝ)..σ * x₀ / Real.cos β,
      polarDensity m₁ m₂ r β * r) (volume.restrict (Ioo a b)) :=
    h.integrableOn_integral_polarDensity m₁ m₂ hx₀
  have h4 : AEStronglyMeasurable (fun β => polarDensity m₁ m₂ (σ * x₀ / Real.cos β) β *
      (x₀ / Real.cos β ^ 2)) (volume.restrict (Ioo a b)) :=
    (hm.mul (measurable_const.div (Real.measurable_cos.pow_const 2))).aestronglyMeasurable
  have h5 : ∀ᵐ β ∂(volume.restrict (Ioo a b)), ∀ x ∈ Ioo (x₀ / 2) (2 * x₀),
      ‖polarDensity m₁ m₂ (σ * x / Real.cos β) β * (x / Real.cos β ^ 2)‖ ≤
        ((√(2 * Real.pi))⁻¹ * (√(2 * Real.pi))⁻¹ * Real.exp (m₂ ^ 2 / 2) * (2 * x₀)) *
          (|σ / Real.cos β ^ 2| • Real.exp (-(x₀ ^ 2 / 16) * (σ * Real.tan β) ^ 2)) :=
    ae_restrict_of_forall_mem measurableSet_Ioo fun β hβ x hx =>
      h.polarDensity_mul_le m₁ m₂ hx₀ hx hβ
  have h6 : Integrable (fun β => ((√(2 * Real.pi))⁻¹ * (√(2 * Real.pi))⁻¹ *
      Real.exp (m₂ ^ 2 / 2) * (2 * x₀)) *
        (|σ / Real.cos β ^ 2| • Real.exp (-(x₀ ^ 2 / 16) * (σ * Real.tan β) ^ 2)))
      (volume.restrict (Ioo a b)) := hbound.const_mul _
  have h7 : ∀ᵐ β ∂(volume.restrict (Ioo a b)), ∀ x ∈ Ioo (x₀ / 2) (2 * x₀),
      HasDerivAt (fun x => ∫ r in (0 : ℝ)..σ * x / Real.cos β, polarDensity m₁ m₂ r β * r)
        (polarDensity m₁ m₂ (σ * x / Real.cos β) β * (x / Real.cos β ^ 2)) x :=
    ae_restrict_of_forall_mem measurableSet_Ioo fun β hβ x _ =>
      h.hasDerivAt_integral_polarDensity m₁ m₂ x hβ
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le h1 h2 h3 h4 h5 h6 h7).2

/-- **The substitution `y = σ x tan β`**: the integral over the sector of the derivative of the
inner integral, in terms of the error function. -/
theorem IsPolarSector.integral_polarDensity_mul (h : IsPolarSector σ a b k) (m₁ m₂ : ℝ) {x : ℝ}
    (hx : 0 < x) :
    ∫ β in a..b, polarDensity m₁ m₂ (σ * x / Real.cos β) β * (x / Real.cos β ^ 2) =
      gaussianPDFReal (σ * m₁) 1 x * (1 / 2 * (1 - Real.erf ((k * x - m₂) / √2))) := by
  have hf' : ∀ β ∈ Ioo a b, HasDerivWithinAt (fun β => x * (σ * Real.tan β))
      (x * (σ / Real.cos β ^ 2)) (Ioo a b) β :=
    fun β hβ => (h.hasDerivWithinAt_tan hβ).const_mul x
  have hinj : InjOn (fun β => x * (σ * Real.tan β)) (Ioo a b) := fun u hu v hv huv =>
    h.injOn hu hv (mul_left_cancel₀ hx.ne' huv)
  have himg : (fun β => x * (σ * Real.tan β)) '' Ioo a b = Ioi (k * x) := by
    have : (fun β => x * (σ * Real.tan β)) '' Ioo a b =
        (x * ·) '' ((fun β => σ * Real.tan β) '' Ioo a b) := by
      rw [Set.image_image]
    rw [this, h.image, Set.image_mul_left_Ioi hx, mul_comm]
  have hsub := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioo hf' hinj
    (gaussianPDFReal m₂ 1)
  rw [himg, integral_gaussianPDFReal_Ioi] at hsub
  rw [intervalIntegral.integral_of_le h.le, integral_Ioc_eq_integral_Ioo, hsub,
    ← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioo fun β hβ => ?_
  simp only [h.polarDensity_eq m₁ m₂ x hβ, smul_eq_mul, abs_mul, abs_of_pos hx, h.abs_div_cos_sq]
  ring

/-- The strips decrease to the empty set as `x` decreases to `0`, so their probability tends
to `0`. -/
theorem tendsto_measure_polarStrip (σ k : ℝ) (P : Measure (ℝ × ℝ)) [IsFiniteMeasure P] :
    Tendsto (fun x => P (polarStrip σ k x)) (𝓝[>] 0) (𝓝 0) := by
  have hempty : ⋂ r > (0 : ℝ), polarStrip σ k r = ∅ := by
    ext z
    simp only [mem_iInter, mem_empty_iff_false, iff_false, not_forall]
    by_cases hz : 0 < σ * z.1
    · exact ⟨σ * z.1 / 2, by linarith, fun h => by linarith [h.2.1]⟩
    · exact ⟨1, one_pos, fun h => hz h.1⟩
  have := tendsto_measure_biInter_gt (μ := P) (s := polarStrip σ k) (a := (0 : ℝ))
    (fun r _ => (measurableSet_polarStrip σ k r).nullMeasurableSet)
    (fun i j _ hij z hz => ⟨hz.1, hz.2.1.trans hij, hz.2.2⟩)
    ⟨1, one_pos, measure_ne_top _ _⟩
  rwa [hempty, measure_empty] at this

/-- From the derivative of the distribution function to the density: if the probability of the
strip is `G x` for `x > 0`, and `G` has there the derivative `f x ≥ 0` with `f` continuous, then `f`
is the density of the strip's distance. Nothing is assumed at `x = 0`, where the derivative of the
double integral cannot be taken under the integral sign. -/
theorem measure_polarStrip_eq_lintegral_of_hasDerivAt (σ k : ℝ) (P : Measure (ℝ × ℝ))
    [IsFiniteMeasure P] {G f : ℝ → ℝ} (hG : ∀ x, 0 < x → (P (polarStrip σ k x)).toReal = G x)
    (hG' : ∀ x, 0 < x → HasDerivAt G (f x) x) (hf : Continuous f) (hf0 : ∀ x, 0 ≤ f x) (x : ℝ) :
    P (polarStrip σ k x) = ∫⁻ u in Ioc 0 x, ENNReal.ofReal (f u) := by
  by_cases hx : 0 < x
  · have hlim : Tendsto G (𝓝[>] 0) (𝓝 0) := by
      have h1 := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp
        (tendsto_measure_polarStrip σ k P)
      rw [ENNReal.toReal_zero] at h1
      refine h1.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with y hy
      exact hG y hy
    have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto hx
      (fun u hu => hG' u hu.1) (hf.intervalIntegrable _ _) hlim
      ((hG' x hx).continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
    rw [sub_zero] at hFTC
    rw [← ENNReal.ofReal_toReal (measure_ne_top P _), hG x hx, ← hFTC,
      intervalIntegral.integral_of_le hx.le,
      ofReal_integral_eq_lintegral_ofReal (hf.integrableOn_Ioc)]
    exact Eventually.of_forall fun u => hf0 u
  · have hS : polarStrip σ k x = ∅ := by
      ext z
      simp only [polarStrip, mem_ofPred_eq, mem_empty_iff_false, iff_false]
      rintro ⟨h1, h2, -⟩
      exact hx (h1.trans_le h2)
    rw [hS, measure_empty, Ioc_eq_empty hx, Measure.restrict_empty, lintegral_zero_measure]

end Strip

/-! ### Rotations -/

/-- The counter-clockwise rotation of the plane by the angle `θ`. -/
def rotate (θ : ℝ) (z : ℝ × ℝ) : ℝ × ℝ :=
  (Real.cos θ * z.1 - Real.sin θ * z.2, Real.sin θ * z.1 + Real.cos θ * z.2)

/-- A rotation sends a pair of independent unit normals to a pair of independent unit normals, with
the mean rotated. -/
theorem measure_rotate_preimage (θ m₁ m₂ : ℝ) {A : Set (ℝ × ℝ)} (hA : MeasurableSet A) :
    ((gaussianReal m₁ 1).prod (gaussianReal m₂ 1)) {z | rotate θ z ∈ A} =
      ((gaussianReal (Real.cos θ * m₁ - Real.sin θ * m₂) 1).prod
        (gaussianReal (Real.sin θ * m₁ + Real.cos θ * m₂) 1)) A := by
  have h := gaussianReal_prod_map_orthonormal (a := Real.cos θ) (b := -Real.sin θ)
    (a' := Real.sin θ) (b' := Real.cos θ) (by rw [neg_sq]; exact Real.cos_sq_add_sin_sq θ)
    (Real.sin_sq_add_cos_sq θ) (by ring) m₁ m₂
  have e : (fun z : ℝ × ℝ => (Real.cos θ * z.1 + -Real.sin θ * z.2,
      Real.sin θ * z.1 + Real.cos θ * z.2)) = rotate θ := by
    funext z
    simp only [rotate]
    ring_nf
  have hm : Measurable (rotate θ) := by
    rw [← e]
    fun_prop
  rw [e, show Real.cos θ * m₁ + -Real.sin θ * m₂ = Real.cos θ * m₁ - Real.sin θ * m₂ by ring] at h
  rw [← h, Measure.map_apply hm hA]
  rfl

end ProbabilityTheory
