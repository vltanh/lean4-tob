module

public import TINNiK.Statistics.AppendixC
public import Basic.ForMathlib.Probability.GaussianPlane
public import Basic.Testing.Defs

/-!
# TINNiK Appendix C.2: Proposition 6, the density of the test distribution

The proof follows the paper. Write `G` for the cumulative distribution function of the non-squared
distance from the normal sample `N((0, μ₀), I)` to the three lines `x = 0`, `y = ± x tan α₀`. The
three lines and their bisectors cut the half-plane `x > 0` into six sectors, and the points of a
sector within distance `x` of the lines form the paper's strip `R_i`. The reflection about the
vertical axis gives `G = 2 ∑_{i=1}^6 G_i`, where `G_i` is the probability of `R_i`
(`measure_lam_le_eq_sum`).

The plain-text source has no Figure 12, which shows the strips. The sets `R_i` below are matched to
the `G_i` by the paper's formulas: the limits of the integral for `G_i`, in the figure that the
paper uses for it, give the angles of the sector and the line from which the distance is measured.
* `G₁`, unrotated, angles `(α₀ + β₀, π / 2)`, line `x = 0`: this is `R₁`.
* `G₂`, `G₃`, rotated by `2 β₀`, which takes `y = x tan α₀` to the vertical axis and the mean to
  `(-μ₀ cos α₀, μ₀ sin α₀)`. The angles `(π / 2, π / 2 + β₀)` and `(π / 2 - α₀, π / 2)` are the
  angles `(α₀, α₀ + β₀)` and `(0, α₀)` of the original figure: these are `R₂`, `R₃`.
* `G₄`, `G₅`, rotated by `π / 2 + α₀`, which takes `y = -x tan α₀` to the vertical axis and the mean
  to `(-μ₀ cos α₀, -μ₀ sin α₀)`. The angles `(π / 2, π / 2 + α₀)` and `(π / 2 - β₀, π / 2)` are the
  angles `(-α₀, 0)` and `(-α₀ - β₀, -α₀)` of the original figure: these are `R₄`, `R₅`.
* `G₆` is `G₁` with the mean mapped to `(0, -μ₀)`, the reflection of `R₁` about the horizontal axis:
  this is `R₆`.

For `i ≤ 5`, each `G_i` is computed as in the paper, and `G₆` follows from `G₁` as in the paper.
* In polar coordinates, `G_i(x)` is the double integral `Gᵢ` over the sector and `r` up to the line
  at distance `x` (`IsPolarSector.measure_polarStrip`).
* Differentiating under the integral sign gives `hasDerivAt_Gᵢ`, with `Gᵢ'` the second line of the
  paper's display (`IsPolarSector.hasDerivAt_polarStripIntegral`).
* The substitution `y = ± x tan β` gives the integral of a normal density times an `erf` term, the
  paper's last line, which is `Gᵢ'_eq_h` (`IsPolarSector.integral_polarDensity_mul`).

The density of `Λ` comes from the change of variable to the squared distance
(`lintegral_sq_subst`).

Two steps that the paper leaves implicit are proved here. Differentiating under the integral sign
needs a dominating function, which exists for `x > 0`: on `(x₀ / 2, 2 x₀)` the integrand is at most
a constant times `(1 / cos² β) exp (-x₀² tan² β / 16)`. The interchange is false at `x = 0`, where
the derivative of the integrand vanishes while `G₁` has a positive right derivative, but that point
is null. From the derivative to the density needs `G_i(x) → 0` as `x → 0` and the fundamental
theorem of calculus (`measure_polarStrip_eq_lintegral_of_hasDerivAt`).

The strips are stated in terms of `s = sin α₀`, `c = cos α₀`, so that `cot α₀ = c / s` and
`cot β₀ = (1 + s) / c`.
-/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

namespace TINNiK

namespace Prop6

open Set External.MitchellAllmanRhodes2019

/-- The statistic of Proposition 5, in terms of `s = sin α₀`, `c = cos α₀`: the minimal squared
distance to the three lines. -/
def lam (s c : ℝ) (z : ℝ × ℝ) : ℝ :=
  min (z.1 ^ 2) (min ((s * z.1 + c * z.2) ^ 2) ((s * z.1 - c * z.2) ^ 2))

theorem measurable_lam (s c : ℝ) : Measurable (lam s c) := by
  unfold lam
  fun_prop

theorem lam_reflect_x (s c : ℝ) (z : ℝ × ℝ) : lam s c (-z.1, z.2) = lam s c z := by
  simp only [lam]
  rw [show (s * -z.1 + c * z.2) ^ 2 = (s * z.1 - c * z.2) ^ 2 by ring,
    show (s * -z.1 - c * z.2) ^ 2 = (s * z.1 + c * z.2) ^ 2 by ring, neg_sq,
    min_comm ((s * z.1 - c * z.2) ^ 2)]

theorem lam_reflect_y (s c : ℝ) (z : ℝ × ℝ) : lam s c (z.1, -z.2) = lam s c z := by
  simp only [lam]
  rw [show (s * z.1 + c * -z.2) ^ 2 = (s * z.1 - c * z.2) ^ 2 by ring,
    show (s * z.1 - c * -z.2) ^ 2 = (s * z.1 + c * z.2) ^ 2 by ring,
    min_comm ((s * z.1 - c * z.2) ^ 2)]

/-- The paper's strip `R₁` (without its bound on the distance): the points of `x > 0` for which
`x = 0` is the nearest line, above the horizontal axis. Here `(1 + s) x < c y` means
`y > x cot β₀`. -/
def R₁ (s c : ℝ) : Set (ℝ × ℝ) := {z | 0 < z.1 ∧ (1 + s) * z.1 < c * z.2}

/-- The paper's strip `R₂`: the points of `x > 0` above the line `y = x tan α₀`, for which this is
the nearest line. -/
def R₂ (s c : ℝ) : Set (ℝ × ℝ) := {z | s * z.1 < c * z.2 ∧ c * z.2 < (1 + s) * z.1}

/-- The paper's strip `R₃`: the points of `x, y > 0` below the line `y = x tan α₀`, for which this
is the nearest line. -/
def R₃ (s c : ℝ) : Set (ℝ × ℝ) := {z | 0 < z.2 ∧ c * z.2 < s * z.1}

/-- The paper's strip `R₄`: the points of `y < 0` above the line `y = -x tan α₀`, for which this is
the nearest line. -/
def R₄ (s c : ℝ) : Set (ℝ × ℝ) := {z | z.2 < 0 ∧ -s * z.1 < c * z.2}

/-- The paper's strip `R₅`: the points of `x > 0` below the line `y = -x tan α₀`, for which this is
the nearest line. -/
def R₅ (s c : ℝ) : Set (ℝ × ℝ) := {z | c * z.2 < -s * z.1 ∧ -(1 + s) * z.1 < c * z.2}

/-- The paper's strip `R₆`: the points of `x > 0` for which `x = 0` is the nearest line, below the
horizontal axis. It is the reflection of `R₁` about the horizontal axis. -/
def R₆ (s c : ℝ) : Set (ℝ × ℝ) := {z | 0 < z.1 ∧ c * z.2 < -(1 + s) * z.1}

theorem measurableSet_R₁ (s c : ℝ) : MeasurableSet (R₁ s c) := by
  have h1 : MeasurableSet {z : ℝ × ℝ | 0 < z.1} :=
    measurableSet_lt measurable_const measurable_fst
  have h2 : MeasurableSet {z : ℝ × ℝ | (1 + s) * z.1 < c * z.2} :=
    measurableSet_lt (by fun_prop) (by fun_prop)
  exact h1.inter h2

theorem lam_of_mem_R₁ {s c : ℝ} (hs : 0 < s) {z : ℝ × ℝ} (hz : z ∈ R₁ s c) :
    lam s c z = z.1 ^ 2 := by
  obtain ⟨hx, h⟩ := hz
  have hsx := mul_pos hs hx
  refine min_eq_left (le_min ?_ ?_)
  · exact pow_le_pow_left₀ hx.le (by nlinarith) 2
  · rw [show (s * z.1 - c * z.2) ^ 2 = (c * z.2 - s * z.1) ^ 2 by ring]
    exact pow_le_pow_left₀ hx.le (by nlinarith) 2

theorem lam_of_mem_R₂ {s c : ℝ} (hs : 0 < s) {z : ℝ × ℝ} (hz : z ∈ R₂ s c) :
    lam s c z = (-s * z.1 + c * z.2) ^ 2 := by
  obtain ⟨h1, h2⟩ := hz
  have hx : 0 < z.1 := by linarith
  have hsx := mul_pos hs hx
  have hu : 0 ≤ -s * z.1 + c * z.2 := by linarith
  have e : (s * z.1 - c * z.2) ^ 2 = (-s * z.1 + c * z.2) ^ 2 := by ring
  rw [lam, e]
  refine le_antisymm (min_le_of_right_le (min_le_right _ _))
    (le_min ?_ (le_min ?_ le_rfl))
  · exact pow_le_pow_left₀ hu (by linarith) 2
  · exact pow_le_pow_left₀ hu (by linarith) 2

theorem lam_of_mem_R₃ {s c : ℝ} (hs : 0 < s) (hc : 0 < c) (hsc : s ^ 2 + c ^ 2 = 1) {z : ℝ × ℝ}
    (hz : z ∈ R₃ s c) : lam s c z = (s * z.1 + -c * z.2) ^ 2 := by
  obtain ⟨hy, h⟩ := hz
  have hcy := mul_pos hc hy
  have hsx : 0 < s * z.1 := by linarith
  have hx : 0 < z.1 := (mul_pos_iff_of_pos_left hs).1 hsx
  have hs1 : s ≤ 1 := by nlinarith
  have hu : 0 ≤ s * z.1 + -c * z.2 := by linarith
  have e : (s * z.1 - c * z.2) ^ 2 = (s * z.1 + -c * z.2) ^ 2 := by ring
  rw [lam, e]
  refine le_antisymm (min_le_of_right_le (min_le_right _ _))
    (le_min ?_ (le_min ?_ le_rfl))
  · exact pow_le_pow_left₀ hu (by nlinarith) 2
  · exact pow_le_pow_left₀ hu (by linarith) 2

theorem lam_of_mem_R₄ {s c : ℝ} (hs : 0 < s) (hc : 0 < c) (hsc : s ^ 2 + c ^ 2 = 1) {z : ℝ × ℝ}
    (hz : z ∈ R₄ s c) : lam s c z = (s * z.1 + c * z.2) ^ 2 := by
  obtain ⟨hy, h⟩ := hz
  have hcy := mul_neg_of_pos_of_neg hc hy
  have hsx : 0 < s * z.1 := by linarith
  have hx : 0 < z.1 := (mul_pos_iff_of_pos_left hs).1 hsx
  have hs1 : s ≤ 1 := by nlinarith
  have hu : 0 ≤ s * z.1 + c * z.2 := by linarith
  rw [lam]
  refine le_antisymm (min_le_of_right_le (min_le_left _ _)) (le_min ?_ (le_min le_rfl ?_))
  · exact pow_le_pow_left₀ hu (by nlinarith) 2
  · exact pow_le_pow_left₀ hu (by linarith) 2

theorem lam_of_mem_R₅ {s c : ℝ} (hs : 0 < s) {z : ℝ × ℝ} (hz : z ∈ R₅ s c) :
    lam s c z = (-s * z.1 + -c * z.2) ^ 2 := by
  obtain ⟨h1, h2⟩ := hz
  have hx : 0 < z.1 := by linarith
  have hsx := mul_pos hs hx
  have hu : 0 ≤ -s * z.1 + -c * z.2 := by linarith
  have e : (s * z.1 + c * z.2) ^ 2 = (-s * z.1 + -c * z.2) ^ 2 := by ring
  rw [lam, e]
  refine le_antisymm (min_le_of_right_le (min_le_left _ _)) (le_min ?_ (le_min le_rfl ?_))
  · exact pow_le_pow_left₀ hu (by linarith) 2
  · exact pow_le_pow_left₀ hu (by linarith) 2

/-- The paper's last line for `d/dx G_i`: a normal density of mean `p` at `u`, times an `erf` term
with slope `k` and mean `q`. -/
def h (p q k u : ℝ) : ℝ :=
  gaussianPDFReal p 1 u * (1 / 2 * (1 - Real.erf ((k * u - q) / √2)))

theorem h_nonneg (p q k u : ℝ) : 0 ≤ h p q k u :=
  mul_nonneg (gaussianPDFReal_nonneg _ _ _) (by linarith [Real.erf_le_one ((k * u - q) / √2)])

theorem continuous_h (p q k : ℝ) : Continuous (h p q k) := by
  have h1 : Continuous (gaussianPDFReal p 1) := by
    unfold gaussianPDFReal
    fun_prop
  have := Real.continuous_erf
  unfold h
  fun_prop

theorem measurable_h (p q k : ℝ) : Measurable (h p q k) := (continuous_h p q k).measurable

section Polar

open Real

/-- The paper's `β₀`. -/
def β₀ (α : ℝ) : ℝ := (π / 2 - α) / 2

theorem two_mul_β₀ (α : ℝ) : 2 * β₀ α = π / 2 - α := by
  simp only [β₀]
  ring

variable {α : ℝ}

theorem sin_pos_of_mem (hα : α ∈ Ioo 0 (π / 2)) : 0 < sin α :=
  sin_pos_of_pos_of_lt_pi hα.1 (by linarith [hα.2, pi_pos])

theorem cos_pos_of_mem (hα : α ∈ Ioo 0 (π / 2)) : 0 < cos α :=
  cos_pos_of_mem_Ioo ⟨by linarith [hα.1, pi_pos], hα.2⟩

theorem β₀_pos (hα : α ∈ Ioo 0 (π / 2)) : 0 < β₀ α := by
  have := hα.2
  simp only [β₀]
  linarith

theorem β₀_lt (hα : α ∈ Ioo 0 (π / 2)) : β₀ α < π / 4 := by
  have := hα.1
  simp only [β₀]
  linarith

/-- The value of `cot β₀` in terms of `sin α₀` and `cos α₀`. -/
theorem cot_β₀ (hα : α ∈ Ioo 0 (π / 2)) : cot (β₀ α) = (1 + sin α) / cos α := by
  have hb0 := β₀_pos hα
  have hb1 := β₀_lt hα
  have hsb : 0 < sin (β₀ α) := sin_pos_of_pos_of_lt_pi hb0 (by linarith [pi_pos])
  have hcb : 0 < cos (β₀ α) := cos_pos_of_mem_Ioo ⟨by linarith [pi_pos], by linarith [pi_pos]⟩
  have es : sin α = cos (2 * β₀ α) := by rw [two_mul_β₀, cos_pi_div_two_sub]
  have ec : cos α = sin (2 * β₀ α) := by rw [two_mul_β₀, sin_pi_div_two_sub]
  rw [cot_eq_cos_div_sin, es, ec, cos_two_mul, sin_two_mul]
  field_simp
  ring

/-- The paper's `tan (α₀ + β₀) = cot β₀`, in terms of `sin α₀` and `cos α₀`. Also,
`α₀ + β₀ = π / 2 - β₀`. -/
theorem tan_pi_div_two_sub_β₀ (hα : α ∈ Ioo 0 (π / 2)) :
    tan (π / 2 - β₀ α) = (1 + sin α) / cos α := by
  rw [← cot_β₀ hα, tan_eq_sin_div_cos, sin_pi_div_two_sub, cos_pi_div_two_sub,
    cot_eq_cos_div_sin]

theorem tan_add_β₀ (hα : α ∈ Ioo 0 (π / 2)) : tan (α + β₀ α) = (1 + sin α) / cos α := by
  rw [show α + β₀ α = π / 2 - β₀ α by simp only [β₀]; ring, tan_pi_div_two_sub_β₀ hα]

/-- `-tan (π / 2 + x) = tan (π / 2 - x)`. -/
theorem neg_tan_pi_div_two_add (x : ℝ) : -tan (π / 2 + x) = tan (π / 2 - x) := by
  rw [show π / 2 + x = π - (π / 2 - x) by ring, tan_pi_sub, neg_neg]

theorem tan_pi_div_two_sub_α (α : ℝ) : tan (π / 2 - α) = cos α / sin α := by
  rw [tan_eq_sin_div_cos, sin_pi_div_two_sub, cos_pi_div_two_sub]

/-- The sector of `G₁`. -/
theorem sector₁ (hα : α ∈ Ioo 0 (π / 2)) :
    IsPolarSector 1 (α + β₀ α) (π / 2) ((1 + sin α) / cos α) := by
  have hb0 := β₀_pos hα
  have hb1 := β₀_lt hα
  have h := IsPolarSector.right (a := α + β₀ α) (by linarith [hα.1, pi_pos])
    (by simp only [β₀] at hb0 ⊢; linarith)
  rwa [tan_add_β₀ hα] at h

/-- The sector of `G₂`, in the figure rotated by `2 β₀`. -/
theorem sector₂ (hα : α ∈ Ioo 0 (π / 2)) :
    IsPolarSector (-1) (π / 2) (π / 2 + β₀ α) ((1 + sin α) / cos α) := by
  have hb0 := β₀_pos hα
  have hb1 := β₀_lt hα
  have h := IsPolarSector.left (b := π / 2 + β₀ α) (by linarith) (by linarith [pi_pos])
  rwa [neg_tan_pi_div_two_add, tan_pi_div_two_sub_β₀ hα] at h

/-- The sector of `G₃`, in the figure rotated by `2 β₀`. -/
theorem sector₃ (hα : α ∈ Ioo 0 (π / 2)) :
    IsPolarSector 1 (π / 2 - α) (π / 2) (cos α / sin α) := by
  have h := IsPolarSector.right (a := π / 2 - α) (by linarith [hα.2, pi_pos]) (by linarith [hα.1])
  rwa [tan_pi_div_two_sub_α] at h

/-- The sector of `G₄`, in the figure rotated by `π / 2 + α₀`. -/
theorem sector₄ (hα : α ∈ Ioo 0 (π / 2)) :
    IsPolarSector (-1) (π / 2) (π / 2 + α) (cos α / sin α) := by
  have h := IsPolarSector.left (b := π / 2 + α) (by linarith [hα.1]) (by linarith [hα.2])
  rwa [neg_tan_pi_div_two_add, tan_pi_div_two_sub_α] at h

/-- The sector of `G₅`, in the figure rotated by `π / 2 + α₀`. -/
theorem sector₅ (hα : α ∈ Ioo 0 (π / 2)) :
    IsPolarSector 1 (π / 2 - β₀ α) (π / 2) ((1 + sin α) / cos α) := by
  have hb0 := β₀_pos hα
  have hb1 := β₀_lt hα
  have h := IsPolarSector.right (a := π / 2 - β₀ α) (by linarith [pi_pos]) (by linarith)
  rwa [tan_pi_div_two_sub_β₀ hα] at h

/-! ### The paper's integrals -/

/-- The density in polar coordinates in the unrotated figure, as in the paper's `G₁`. -/
theorem polarDensity_unrotated (μ r β : ℝ) :
    polarDensity 0 μ r β = 1 / (2 * π) * exp (-(1 / 2) * (r ^ 2 - 2 * μ * r * sin β + μ ^ 2)) := by
  rw [polarDensity]
  congr 3
  ring

/-- The density in polar coordinates in the figure rotated by `2 β₀`, where the mean is
`(-μ cos α, μ sin α)`, as in the paper's `G₂`, `G₃`. -/
theorem polarDensity_rotated_two_mul_β₀ (α μ r β : ℝ) :
    polarDensity (-μ * cos α) (μ * sin α) r β =
      1 / (2 * π) * exp (-(1 / 2) * (r ^ 2 + 2 * μ * r * cos (α + β) + μ ^ 2)) := by
  rw [polarDensity, cos_add]
  congr 3
  linear_combination (μ ^ 2) * cos_sq_add_sin_sq α

/-- The density in polar coordinates in the figure rotated by `π / 2 + α`, where the mean is
`(-μ cos α, -μ sin α)`, as in the paper's `G₄`, `G₅`. -/
theorem polarDensity_rotated_pi_div_two_add (α μ r β : ℝ) :
    polarDensity (-μ * cos α) (-μ * sin α) r β =
      1 / (2 * π) * exp (-(1 / 2) * (r ^ 2 + 2 * μ * r * cos (α - β) + μ ^ 2)) := by
  rw [polarDensity, cos_sub]
  congr 3
  linear_combination (μ ^ 2) * cos_sq_add_sin_sq α

/-- The paper's `G₁`, in polar coordinates. -/
def G₁ (α μ x : ℝ) : ℝ :=
  ∫ β in (α + β₀ α)..(π / 2), ∫ r in (0 : ℝ)..(x / cos β),
    1 / (2 * π) * exp (-(1 / 2) * (r ^ 2 - 2 * μ * r * sin β + μ ^ 2)) * r

/-- The second line of the paper's display for `d/dx G₁`. -/
def G₁' (α μ x : ℝ) : ℝ :=
  ∫ β in (α + β₀ α)..(π / 2),
    1 / (2 * π) * exp (-(1 / 2) * (x ^ 2 / cos β ^ 2 - 2 * μ * (x / cos β) * sin β + μ ^ 2)) *
      (x / cos β ^ 2)

theorem G₁_eq (α μ : ℝ) : G₁ α μ = polarStripIntegral 1 (α + β₀ α) (π / 2) 0 μ := by
  funext x
  simp only [G₁, polarStripIntegral, polarDensity_unrotated, one_mul]

theorem G₁'_eq (α μ x : ℝ) : G₁' α μ x = ∫ β in (α + β₀ α)..(π / 2),
    polarDensity 0 μ (1 * x / cos β) β * (x / cos β ^ 2) := by
  simp only [G₁', polarDensity_unrotated, one_mul]
  congr 1
  funext β
  congr 4
  ring

theorem hasDerivAt_G₁ (hα : α ∈ Ioo 0 (π / 2)) (μ : ℝ) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (G₁ α μ) (G₁' α μ x) x := by
  rw [G₁_eq, G₁'_eq]
  exact (sector₁ hα).hasDerivAt_polarStripIntegral 0 μ hx

/-- The paper's substitution `y = x tan β` in `d/dx G₁`. -/
theorem G₁'_eq_h (hα : α ∈ Ioo 0 (π / 2)) (μ : ℝ) {x : ℝ} (hx : 0 < x) :
    G₁' α μ x = h 0 μ ((1 + sin α) / cos α) x := by
  rw [G₁'_eq, (sector₁ hα).integral_polarDensity_mul 0 μ hx, h, mul_zero]

/-- The paper's `G₂`, in polar coordinates, in the figure rotated by `2 β₀`. -/
def G₂ (α μ x : ℝ) : ℝ :=
  ∫ β in (π / 2)..(π / 2 + β₀ α), ∫ r in (0 : ℝ)..(-x / cos β),
    1 / (2 * π) * exp (-(1 / 2) * (r ^ 2 + 2 * μ * r * cos (α + β) + μ ^ 2)) * r

/-- The second line of the paper's display for `d/dx G₂`. -/
def G₂' (α μ x : ℝ) : ℝ :=
  ∫ β in (π / 2)..(π / 2 + β₀ α),
    1 / (2 * π) * exp (-(1 / 2) * (x ^ 2 / cos β ^ 2 - 2 * μ * x * (cos (α + β) / cos β) + μ ^ 2)) *
      (x / cos β ^ 2)

theorem G₂_eq (α μ : ℝ) :
    G₂ α μ = polarStripIntegral (-1) (π / 2) (π / 2 + β₀ α) (-μ * cos α) (μ * sin α) := by
  funext x
  simp only [G₂, polarStripIntegral, polarDensity_rotated_two_mul_β₀, neg_one_mul]

theorem G₂'_eq (α μ x : ℝ) : G₂' α μ x = ∫ β in (π / 2)..(π / 2 + β₀ α),
    polarDensity (-μ * cos α) (μ * sin α) (-1 * x / cos β) β * (x / cos β ^ 2) := by
  simp only [G₂', polarDensity_rotated_two_mul_β₀]
  congr 1
  funext β
  congr 4
  ring

theorem hasDerivAt_G₂ (hα : α ∈ Ioo 0 (π / 2)) (μ : ℝ) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (G₂ α μ) (G₂' α μ x) x := by
  rw [G₂_eq, G₂'_eq]
  exact (sector₂ hα).hasDerivAt_polarStripIntegral _ _ hx

/-- The substitution `y = -x tan β` in the paper's `d/dx G₂`. -/
theorem G₂'_eq_h (hα : α ∈ Ioo 0 (π / 2)) (μ : ℝ) {x : ℝ} (hx : 0 < x) :
    G₂' α μ x = h (μ * cos α) (μ * sin α) ((1 + sin α) / cos α) x := by
  rw [G₂'_eq, (sector₂ hα).integral_polarDensity_mul _ _ hx, h,
    show -1 * (-μ * cos α) = μ * cos α by ring]

/-- The paper's `G₃`, in polar coordinates, in the figure rotated by `2 β₀`. -/
def G₃ (α μ x : ℝ) : ℝ :=
  ∫ β in (π / 2 - α)..(π / 2), ∫ r in (0 : ℝ)..(x / cos β),
    1 / (2 * π) * exp (-(1 / 2) * (r ^ 2 + 2 * μ * r * cos (α + β) + μ ^ 2)) * r

/-- The second line of the paper's display for `d/dx G₃`. -/
def G₃' (α μ x : ℝ) : ℝ :=
  ∫ β in (π / 2 - α)..(π / 2),
    1 / (2 * π) * exp (-(1 / 2) * (x ^ 2 / cos β ^ 2 + 2 * μ * x * (cos (α + β) / cos β) + μ ^ 2)) *
      (x / cos β ^ 2)

theorem G₃_eq (α μ : ℝ) :
    G₃ α μ = polarStripIntegral 1 (π / 2 - α) (π / 2) (-μ * cos α) (μ * sin α) := by
  funext x
  simp only [G₃, polarStripIntegral, polarDensity_rotated_two_mul_β₀, one_mul]

theorem G₃'_eq (α μ x : ℝ) : G₃' α μ x = ∫ β in (π / 2 - α)..(π / 2),
    polarDensity (-μ * cos α) (μ * sin α) (1 * x / cos β) β * (x / cos β ^ 2) := by
  simp only [G₃', polarDensity_rotated_two_mul_β₀, one_mul]
  congr 1
  funext β
  congr 4
  ring

theorem hasDerivAt_G₃ (hα : α ∈ Ioo 0 (π / 2)) (μ : ℝ) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (G₃ α μ) (G₃' α μ x) x := by
  rw [G₃_eq, G₃'_eq]
  exact (sector₃ hα).hasDerivAt_polarStripIntegral _ _ hx

/-- The substitution `y = x tan β` in the paper's `d/dx G₃`. -/
theorem G₃'_eq_h (hα : α ∈ Ioo 0 (π / 2)) (μ : ℝ) {x : ℝ} (hx : 0 < x) :
    G₃' α μ x = h (-μ * cos α) (μ * sin α) (cos α / sin α) x := by
  rw [G₃'_eq, (sector₃ hα).integral_polarDensity_mul _ _ hx, h, one_mul]

/-- The paper's `G₄`, in polar coordinates, in the figure rotated by `π / 2 + α₀`. -/
def G₄ (α μ x : ℝ) : ℝ :=
  ∫ β in (π / 2)..(π / 2 + α), ∫ r in (0 : ℝ)..(-x / cos β),
    1 / (2 * π) * exp (-(1 / 2) * (r ^ 2 + 2 * μ * r * cos (α - β) + μ ^ 2)) * r

/-- The second line of the paper's display for `d/dx G₄`. -/
def G₄' (α μ x : ℝ) : ℝ :=
  ∫ β in (π / 2)..(π / 2 + α),
    1 / (2 * π) * exp (-(1 / 2) * (x ^ 2 / cos β ^ 2 - 2 * μ * x * (cos (α - β) / cos β) + μ ^ 2)) *
      (x / cos β ^ 2)

theorem G₄_eq (α μ : ℝ) :
    G₄ α μ = polarStripIntegral (-1) (π / 2) (π / 2 + α) (-μ * cos α) (-μ * sin α) := by
  funext x
  simp only [G₄, polarStripIntegral, polarDensity_rotated_pi_div_two_add, neg_one_mul]

theorem G₄'_eq (α μ x : ℝ) : G₄' α μ x = ∫ β in (π / 2)..(π / 2 + α),
    polarDensity (-μ * cos α) (-μ * sin α) (-1 * x / cos β) β * (x / cos β ^ 2) := by
  simp only [G₄', polarDensity_rotated_pi_div_two_add]
  congr 1
  funext β
  congr 4
  ring

theorem hasDerivAt_G₄ (hα : α ∈ Ioo 0 (π / 2)) (μ : ℝ) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (G₄ α μ) (G₄' α μ x) x := by
  rw [G₄_eq, G₄'_eq]
  exact (sector₄ hα).hasDerivAt_polarStripIntegral _ _ hx

/-- The substitution `y = -x tan β` in the paper's `d/dx G₄`. -/
theorem G₄'_eq_h (hα : α ∈ Ioo 0 (π / 2)) (μ : ℝ) {x : ℝ} (hx : 0 < x) :
    G₄' α μ x = h (μ * cos α) (-μ * sin α) (cos α / sin α) x := by
  rw [G₄'_eq, (sector₄ hα).integral_polarDensity_mul _ _ hx, h,
    show -1 * (-μ * cos α) = μ * cos α by ring]

/-- The paper's `G₅`, in polar coordinates, in the figure rotated by `π / 2 + α₀`. -/
def G₅ (α μ x : ℝ) : ℝ :=
  ∫ β in (π / 2 - β₀ α)..(π / 2), ∫ r in (0 : ℝ)..(x / cos β),
    1 / (2 * π) * exp (-(1 / 2) * (r ^ 2 + 2 * μ * r * cos (α - β) + μ ^ 2)) * r

/-- The second line of the paper's display for `d/dx G₅`. -/
def G₅' (α μ x : ℝ) : ℝ :=
  ∫ β in (π / 2 - β₀ α)..(π / 2),
    1 / (2 * π) * exp (-(1 / 2) * (x ^ 2 / cos β ^ 2 + 2 * μ * x * (cos (α - β) / cos β) + μ ^ 2)) *
      (x / cos β ^ 2)

theorem G₅_eq (α μ : ℝ) :
    G₅ α μ = polarStripIntegral 1 (π / 2 - β₀ α) (π / 2) (-μ * cos α) (-μ * sin α) := by
  funext x
  simp only [G₅, polarStripIntegral, polarDensity_rotated_pi_div_two_add, one_mul]

theorem G₅'_eq (α μ x : ℝ) : G₅' α μ x = ∫ β in (π / 2 - β₀ α)..(π / 2),
    polarDensity (-μ * cos α) (-μ * sin α) (1 * x / cos β) β * (x / cos β ^ 2) := by
  simp only [G₅', polarDensity_rotated_pi_div_two_add, one_mul]
  congr 1
  funext β
  congr 4
  ring

theorem hasDerivAt_G₅ (hα : α ∈ Ioo 0 (π / 2)) (μ : ℝ) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (G₅ α μ) (G₅' α μ x) x := by
  rw [G₅_eq, G₅'_eq]
  exact (sector₅ hα).hasDerivAt_polarStripIntegral _ _ hx

/-- The substitution `y = x tan β` in the paper's `d/dx G₅`. -/
theorem G₅'_eq_h (hα : α ∈ Ioo 0 (π / 2)) (μ : ℝ) {x : ℝ} (hx : 0 < x) :
    G₅' α μ x = h (-μ * cos α) (-μ * sin α) ((1 + sin α) / cos α) x := by
  rw [G₅'_eq, (sector₅ hα).integral_polarDensity_mul _ _ hx, h, one_mul]

/-! ### The rotated figures -/

/-- The rotation by `2 β₀`, in terms of `sin α₀` and `cos α₀`. -/
theorem rotate_two_mul_β₀ (α : ℝ) (z : ℝ × ℝ) :
    rotate (2 * β₀ α) z = (sin α * z.1 - cos α * z.2, cos α * z.1 + sin α * z.2) := by
  rw [rotate, two_mul_β₀, cos_pi_div_two_sub, sin_pi_div_two_sub]

/-- The rotation by `π / 2 + α₀`, in terms of `sin α₀` and `cos α₀`. -/
theorem rotate_pi_div_two_add (α : ℝ) (z : ℝ × ℝ) :
    rotate (π / 2 + α) z = (-sin α * z.1 - cos α * z.2, cos α * z.1 - sin α * z.2) := by
  rw [rotate, add_comm (π / 2) α, cos_add_pi_div_two, sin_add_pi_div_two]
  congr 1
  ring

/-- Rotating the figure `2 β₀` counter-clockwise, the generating parameter is mapped as
`(0, μ) ↦ (-μ cos α, μ sin α)`. -/
theorem P_rotate_two_mul_β₀ (α μ : ℝ) {A : Set (ℝ × ℝ)} (hA : MeasurableSet A) :
    normalSample μ {z | rotate (2 * β₀ α) z ∈ A} =
      ((gaussianReal (-μ * cos α) 1).prod (gaussianReal (μ * sin α) 1)) A := by
  rw [measure_rotate_preimage _ _ _ hA, two_mul_β₀, cos_pi_div_two_sub, sin_pi_div_two_sub,
    show sin α * 0 - cos α * μ = -μ * cos α by ring,
    show cos α * 0 + sin α * μ = μ * sin α by ring]

/-- Rotating the figure `π / 2 + α` counter-clockwise, the generating parameter becomes
`(-μ cos α, -μ sin α)`. -/
theorem P_rotate_pi_div_two_add (α μ : ℝ) {A : Set (ℝ × ℝ)} (hA : MeasurableSet A) :
    normalSample μ {z | rotate (π / 2 + α) z ∈ A} =
      ((gaussianReal (-μ * cos α) 1).prod (gaussianReal (-μ * sin α) 1)) A := by
  rw [measure_rotate_preimage _ _ _ hA, add_comm (π / 2) α, cos_add_pi_div_two, sin_add_pi_div_two,
    show -sin α * 0 - cos α * μ = -μ * cos α by ring,
    show cos α * 0 + -sin α * μ = -μ * sin α by ring]

/-! ### The probabilities of the strips -/

/-- `G₁`: the probability of the part of `R₁` within distance `√t` of `x = 0`. -/
theorem measure_inter_R₁ (hα : α ∈ Ioo 0 (π / 2)) (μ t : ℝ) :
    normalSample μ ({z | lam (sin α) (cos α) z ≤ t} ∩ R₁ (sin α) (cos α)) =
      ∫⁻ u in Ioc 0 √t, ENNReal.ofReal (h 0 μ ((1 + sin α) / cos α) u) := by
  have hs := sin_pos_of_mem hα
  have hc := cos_pos_of_mem hα
  have hset : {z | lam (sin α) (cos α) z ≤ t} ∩ R₁ (sin α) (cos α) =
      polarStrip 1 ((1 + sin α) / cos α) √t := by
    ext z
    simp only [mem_inter_iff, mem_ofPred_eq, polarStrip, one_mul]
    have key : (1 + sin α) / cos α * z.1 < z.2 ↔ (1 + sin α) * z.1 < cos α * z.2 := by
      rw [div_mul_eq_mul_div, div_lt_iff₀ hc, mul_comm z.2]
    constructor
    · rintro ⟨hl, hz⟩
      rw [lam_of_mem_R₁ hs hz] at hl
      exact ⟨hz.1, (Real.le_sqrt' hz.1).2 hl, key.2 hz.2⟩
    · rintro ⟨hx, hxt, hv⟩
      have hz : z ∈ R₁ (sin α) (cos α) := ⟨hx, key.1 hv⟩
      exact ⟨by rw [lam_of_mem_R₁ hs hz]; exact (Real.le_sqrt' hx).1 hxt, hz⟩
  rw [hset]
  exact measure_polarStrip_eq_lintegral_of_hasDerivAt 1 _ (normalSample μ) (G := G₁ α μ)
    (fun x hx => by rw [G₁_eq]; exact (sector₁ hα).toReal_measure_polarStrip 0 μ hx)
    (fun x hx => by rw [← G₁'_eq_h hα μ hx]; exact hasDerivAt_G₁ hα μ hx)
    (continuous_h _ _ _) (h_nonneg _ _ _) _

/-- `G₂`: the probability of the part of `R₂` within distance `√t` of `y = x tan α₀`, in the figure
rotated by `2 β₀`. -/
theorem measure_inter_R₂ (hα : α ∈ Ioo 0 (π / 2)) (μ t : ℝ) :
    normalSample μ ({z | lam (sin α) (cos α) z ≤ t} ∩ R₂ (sin α) (cos α)) =
      ∫⁻ u in Ioc 0 √t, ENNReal.ofReal (h (μ * cos α) (μ * sin α) ((1 + sin α) / cos α) u) := by
  have hs := sin_pos_of_mem hα
  have hc := cos_pos_of_mem hα
  have hsc := sin_sq_add_cos_sq α
  have hset : {z | lam (sin α) (cos α) z ≤ t} ∩ R₂ (sin α) (cos α) =
      {z | rotate (2 * β₀ α) z ∈ polarStrip (-1) ((1 + sin α) / cos α) √t} := by
    ext z
    have e : -1 * (sin α * z.1 - cos α * z.2) = -sin α * z.1 + cos α * z.2 := by ring
    simp only [mem_inter_iff, mem_ofPred_eq, rotate_two_mul_β₀, polarStrip, e]
    have key : (1 + sin α) / cos α * (-sin α * z.1 + cos α * z.2) <
        cos α * z.1 + sin α * z.2 ↔ cos α * z.2 < (1 + sin α) * z.1 := by
      rw [div_mul_eq_mul_div, div_lt_iff₀ hc]
      have : (cos α * z.1 + sin α * z.2) * cos α -
          (1 + sin α) * (-sin α * z.1 + cos α * z.2) =
          (1 + sin α) * z.1 - cos α * z.2 := by linear_combination z.1 * hsc
      constructor <;> intro <;> linarith
    constructor
    · rintro ⟨hl, hz⟩
      rw [lam_of_mem_R₂ hs hz] at hl
      have hu : 0 < -sin α * z.1 + cos α * z.2 := by linarith [hz.1]
      exact ⟨hu, (Real.le_sqrt' hu).2 hl, key.2 hz.2⟩
    · rintro ⟨hu, hut, hv⟩
      have hz : z ∈ R₂ (sin α) (cos α) := ⟨by linarith, key.1 hv⟩
      exact ⟨by rw [lam_of_mem_R₂ hs hz]; exact (Real.le_sqrt' hu).1 hut, hz⟩
  rw [hset, P_rotate_two_mul_β₀ _ _ (measurableSet_polarStrip _ _ _)]
  exact measure_polarStrip_eq_lintegral_of_hasDerivAt (-1) _ _ (G := G₂ α μ)
    (fun x hx => by rw [G₂_eq]; exact (sector₂ hα).toReal_measure_polarStrip _ _ hx)
    (fun x hx => by rw [← G₂'_eq_h hα μ hx]; exact hasDerivAt_G₂ hα μ hx)
    (continuous_h _ _ _) (h_nonneg _ _ _) _

/-- `G₃`: the probability of the part of `R₃` within distance `√t` of `y = x tan α₀`, in the figure
rotated by `2 β₀`. -/
theorem measure_inter_R₃ (hα : α ∈ Ioo 0 (π / 2)) (μ t : ℝ) :
    normalSample μ ({z | lam (sin α) (cos α) z ≤ t} ∩ R₃ (sin α) (cos α)) =
      ∫⁻ u in Ioc 0 √t, ENNReal.ofReal (h (-μ * cos α) (μ * sin α) (cos α / sin α) u) := by
  have hs := sin_pos_of_mem hα
  have hc := cos_pos_of_mem hα
  have hsc := sin_sq_add_cos_sq α
  have hset : {z | lam (sin α) (cos α) z ≤ t} ∩ R₃ (sin α) (cos α) =
      {z | rotate (2 * β₀ α) z ∈ polarStrip 1 (cos α / sin α) √t} := by
    ext z
    have e : sin α * z.1 - cos α * z.2 = sin α * z.1 + -cos α * z.2 := by ring
    simp only [mem_inter_iff, mem_ofPred_eq, rotate_two_mul_β₀, polarStrip, one_mul, e]
    have key : cos α / sin α * (sin α * z.1 + -cos α * z.2) < cos α * z.1 + sin α * z.2 ↔
        0 < z.2 := by
      rw [div_mul_eq_mul_div, div_lt_iff₀ hs]
      have : (cos α * z.1 + sin α * z.2) * sin α - cos α * (sin α * z.1 + -cos α * z.2) = z.2 := by
        linear_combination z.2 * hsc
      constructor <;> intro <;> linarith
    constructor
    · rintro ⟨hl, hz⟩
      rw [lam_of_mem_R₃ hs hc hsc hz] at hl
      have hu : 0 < sin α * z.1 + -cos α * z.2 := by linarith [hz.2]
      exact ⟨hu, (Real.le_sqrt' hu).2 hl, key.2 hz.1⟩
    · rintro ⟨hu, hut, hv⟩
      have hz : z ∈ R₃ (sin α) (cos α) := ⟨key.1 hv, by linarith⟩
      exact ⟨by rw [lam_of_mem_R₃ hs hc hsc hz]; exact (Real.le_sqrt' hu).1 hut, hz⟩
  rw [hset, P_rotate_two_mul_β₀ _ _ (measurableSet_polarStrip _ _ _)]
  exact measure_polarStrip_eq_lintegral_of_hasDerivAt 1 _ _ (G := G₃ α μ)
    (fun x hx => by rw [G₃_eq]; exact (sector₃ hα).toReal_measure_polarStrip _ _ hx)
    (fun x hx => by rw [← G₃'_eq_h hα μ hx]; exact hasDerivAt_G₃ hα μ hx)
    (continuous_h _ _ _) (h_nonneg _ _ _) _

/-- `G₄`: the probability of the part of `R₄` within distance `√t` of `y = -x tan α₀`, in the figure
rotated by `π / 2 + α₀`. -/
theorem measure_inter_R₄ (hα : α ∈ Ioo 0 (π / 2)) (μ t : ℝ) :
    normalSample μ ({z | lam (sin α) (cos α) z ≤ t} ∩ R₄ (sin α) (cos α)) =
      ∫⁻ u in Ioc 0 √t, ENNReal.ofReal (h (μ * cos α) (-μ * sin α) (cos α / sin α) u) := by
  have hs := sin_pos_of_mem hα
  have hc := cos_pos_of_mem hα
  have hsc := sin_sq_add_cos_sq α
  have hset : {z | lam (sin α) (cos α) z ≤ t} ∩ R₄ (sin α) (cos α) =
      {z | rotate (π / 2 + α) z ∈ polarStrip (-1) (cos α / sin α) √t} := by
    ext z
    have e : -1 * (-sin α * z.1 - cos α * z.2) = sin α * z.1 + cos α * z.2 := by ring
    simp only [mem_inter_iff, mem_ofPred_eq, rotate_pi_div_two_add, polarStrip, e]
    have key : cos α / sin α * (sin α * z.1 + cos α * z.2) < cos α * z.1 - sin α * z.2 ↔
        z.2 < 0 := by
      rw [div_mul_eq_mul_div, div_lt_iff₀ hs]
      have : (cos α * z.1 - sin α * z.2) * sin α - cos α * (sin α * z.1 + cos α * z.2) = -z.2 := by
        linear_combination (-z.2) * hsc
      constructor <;> intro <;> linarith
    constructor
    · rintro ⟨hl, hz⟩
      rw [lam_of_mem_R₄ hs hc hsc hz] at hl
      have hu : 0 < sin α * z.1 + cos α * z.2 := by linarith [hz.2]
      exact ⟨hu, (Real.le_sqrt' hu).2 hl, key.2 hz.1⟩
    · rintro ⟨hu, hut, hv⟩
      have hz : z ∈ R₄ (sin α) (cos α) := ⟨key.1 hv, by linarith⟩
      exact ⟨by rw [lam_of_mem_R₄ hs hc hsc hz]; exact (Real.le_sqrt' hu).1 hut, hz⟩
  rw [hset, P_rotate_pi_div_two_add _ _ (measurableSet_polarStrip _ _ _)]
  exact measure_polarStrip_eq_lintegral_of_hasDerivAt (-1) _ _ (G := G₄ α μ)
    (fun x hx => by rw [G₄_eq]; exact (sector₄ hα).toReal_measure_polarStrip _ _ hx)
    (fun x hx => by rw [← G₄'_eq_h hα μ hx]; exact hasDerivAt_G₄ hα μ hx)
    (continuous_h _ _ _) (h_nonneg _ _ _) _

/-- `G₅`: the probability of the part of `R₅` within distance `√t` of `y = -x tan α₀`, in the figure
rotated by `π / 2 + α₀`. -/
theorem measure_inter_R₅ (hα : α ∈ Ioo 0 (π / 2)) (μ t : ℝ) :
    normalSample μ ({z | lam (sin α) (cos α) z ≤ t} ∩ R₅ (sin α) (cos α)) =
      ∫⁻ u in Ioc 0 √t, ENNReal.ofReal
        (h (-μ * cos α) (-μ * sin α) ((1 + sin α) / cos α) u) := by
  have hs := sin_pos_of_mem hα
  have hc := cos_pos_of_mem hα
  have hsc := sin_sq_add_cos_sq α
  have hset : {z | lam (sin α) (cos α) z ≤ t} ∩ R₅ (sin α) (cos α) =
      {z | rotate (π / 2 + α) z ∈ polarStrip 1 ((1 + sin α) / cos α) √t} := by
    ext z
    have e : -sin α * z.1 - cos α * z.2 = -sin α * z.1 + -cos α * z.2 := by ring
    simp only [mem_inter_iff, mem_ofPred_eq, rotate_pi_div_two_add, polarStrip, one_mul, e]
    have key : (1 + sin α) / cos α * (-sin α * z.1 + -cos α * z.2) < cos α * z.1 - sin α * z.2 ↔
        -(1 + sin α) * z.1 < cos α * z.2 := by
      rw [div_mul_eq_mul_div, div_lt_iff₀ hc]
      have : (cos α * z.1 - sin α * z.2) * cos α -
          (1 + sin α) * (-sin α * z.1 + -cos α * z.2) =
          (1 + sin α) * z.1 + cos α * z.2 := by linear_combination z.1 * hsc
      constructor <;> intro <;> linarith
    constructor
    · rintro ⟨hl, hz⟩
      rw [lam_of_mem_R₅ hs hz] at hl
      have hu : 0 < -sin α * z.1 + -cos α * z.2 := by linarith [hz.1]
      exact ⟨hu, (Real.le_sqrt' hu).2 hl, key.2 hz.2⟩
    · rintro ⟨hu, hut, hv⟩
      have hz : z ∈ R₅ (sin α) (cos α) := ⟨by linarith, key.1 hv⟩
      exact ⟨by rw [lam_of_mem_R₅ hs hz]; exact (Real.le_sqrt' hu).1 hut, hz⟩
  rw [hset, P_rotate_pi_div_two_add _ _ (measurableSet_polarStrip _ _ _)]
  exact measure_polarStrip_eq_lintegral_of_hasDerivAt 1 _ _ (G := G₅ α μ)
    (fun x hx => by rw [G₅_eq]; exact (sector₅ hα).toReal_measure_polarStrip _ _ hx)
    (fun x hx => by rw [← G₅'_eq_h hα μ hx]; exact hasDerivAt_G₅ hα μ hx)
    (continuous_h _ _ _) (h_nonneg _ _ _) _

end Polar

/-- The first quadrant is, up to the null lines `y = x tan α₀` and `y = x cot β₀`, the union of the
disjoint sets `R₁`, `R₂`, `R₃`. -/
theorem measure_quadrant {s c : ℝ} (hs : 0 < s) (hc : 0 < c) (μ t : ℝ) :
    normalSample μ ({z | lam s c z ≤ t} ∩ {z | 0 < z.1} ∩ {z | 0 < z.2}) =
      normalSample μ ({z | lam s c z ≤ t} ∩ R₁ s c) + normalSample μ ({z | lam s c z ≤ t} ∩ R₂ s c) +
        normalSample μ ({z | lam s c z ≤ t} ∩ R₃ s c) := by
  have h1 := gaussianReal_prod_split (k₁ := -s) (k₂ := c) (Or.inr hc.ne') 0 μ
    ({z | lam s c z ≤ t} ∩ {z | 0 < z.1} ∩ {z | 0 < z.2})
  have h2 := gaussianReal_prod_split (k₁ := -(1 + s)) (k₂ := c) (Or.inr hc.ne') 0 μ
    ({z | lam s c z ≤ t} ∩ {z | 0 < z.1} ∩ {z | 0 < z.2} ∩ {z | 0 < -s * z.1 + c * z.2})
  have e1 : {z | lam s c z ≤ t} ∩ {z | 0 < z.1} ∩ {z | 0 < z.2} ∩ {z | 0 < -s * z.1 + c * z.2} ∩
      {z | 0 < -(1 + s) * z.1 + c * z.2} = {z | lam s c z ≤ t} ∩ R₁ s c := by
    ext z
    simp only [mem_inter_iff, mem_ofPred_eq, R₁]
    constructor
    · rintro ⟨⟨⟨⟨hE, hx⟩, -⟩, -⟩, hf⟩
      exact ⟨hE, hx, by linarith⟩
    · rintro ⟨hE, hx, hb⟩
      have hsx := mul_pos hs hx
      have hcy : 0 < c * z.2 := by linarith
      exact ⟨⟨⟨⟨hE, hx⟩, (mul_pos_iff_of_pos_left hc).1 hcy⟩, by linarith⟩, by linarith⟩
  have e2 : {z | lam s c z ≤ t} ∩ {z | 0 < z.1} ∩ {z | 0 < z.2} ∩ {z | 0 < -s * z.1 + c * z.2} ∩
      {z | -(1 + s) * z.1 + c * z.2 < 0} = {z | lam s c z ≤ t} ∩ R₂ s c := by
    ext z
    simp only [mem_inter_iff, mem_ofPred_eq, R₂]
    constructor
    · rintro ⟨⟨⟨⟨hE, -⟩, -⟩, hf⟩, hf'⟩
      exact ⟨hE, by linarith, by linarith⟩
    · rintro ⟨hE, hb, hb'⟩
      have hx : 0 < z.1 := by linarith
      have hsx := mul_pos hs hx
      have hcy : 0 < c * z.2 := by linarith
      exact ⟨⟨⟨⟨hE, hx⟩, (mul_pos_iff_of_pos_left hc).1 hcy⟩, by linarith⟩, by linarith⟩
  have e3 : {z | lam s c z ≤ t} ∩ {z | 0 < z.1} ∩ {z | 0 < z.2} ∩ {z | -s * z.1 + c * z.2 < 0} =
      {z | lam s c z ≤ t} ∩ R₃ s c := by
    ext z
    simp only [mem_inter_iff, mem_ofPred_eq, R₃]
    constructor
    · rintro ⟨⟨⟨hE, -⟩, hy⟩, hf⟩
      exact ⟨hE, hy, by linarith⟩
    · rintro ⟨hE, hy, hb⟩
      have hcy := mul_pos hc hy
      have hsx : 0 < s * z.1 := by linarith
      exact ⟨⟨⟨hE, (mul_pos_iff_of_pos_left hs).1 hsx⟩, hy⟩, by linarith⟩
  rw [e1, e2] at h2
  rw [e3, h2] at h1
  exact h1

/-- The reflection about the vertical axis preserves the law of the normal sample. -/
theorem P_reflect_x (μ : ℝ) {A : Set (ℝ × ℝ)} (hA : MeasurableSet A) :
    normalSample μ {z | (-z.1, z.2) ∈ A} = normalSample μ A := by
  have h := gaussianReal_prod_map_orthonormal (a := -1) (b := 0) (a' := 0) (b' := 1)
    (by norm_num) (by norm_num) (by norm_num) 0 μ
  have e : (fun z : ℝ × ℝ => (-1 * z.1 + 0 * z.2, 0 * z.1 + 1 * z.2)) = fun z => (-z.1, z.2) := by
    funext z; simp
  rw [e, show (-1 : ℝ) * 0 + 0 * μ = 0 by ring, show (0 : ℝ) * 0 + 1 * μ = μ by ring] at h
  have hm : Measurable (fun z : ℝ × ℝ => (-z.1, z.2)) := by fun_prop
  calc normalSample μ {z | (-z.1, z.2) ∈ A} = ((normalSample μ).map fun z : ℝ × ℝ => (-z.1, z.2)) A :=
        (Measure.map_apply hm hA).symm
    _ = normalSample μ A := by rw [h]

/-- The reflection about the horizontal axis changes the sign of the mean. -/
theorem P_reflect_y (μ : ℝ) {A : Set (ℝ × ℝ)} (hA : MeasurableSet A) :
    normalSample μ {z | (z.1, -z.2) ∈ A} = normalSample (-μ) A := by
  have h := gaussianReal_prod_map_orthonormal (a := 1) (b := 0) (a' := 0) (b' := -1)
    (by norm_num) (by norm_num) (by norm_num) 0 μ
  have e : (fun z : ℝ × ℝ => (1 * z.1 + 0 * z.2, 0 * z.1 + -1 * z.2)) = fun z => (z.1, -z.2) := by
    funext z; simp
  rw [e, show (1 : ℝ) * 0 + 0 * μ = 0 by ring, show (0 : ℝ) * 0 + -1 * μ = -μ by ring] at h
  have hm : Measurable (fun z : ℝ × ℝ => (z.1, -z.2)) := by fun_prop
  calc normalSample μ {z | (z.1, -z.2) ∈ A} = ((normalSample μ).map fun z : ℝ × ℝ => (z.1, -z.2)) A :=
        (Measure.map_apply hm hA).symm
    _ = normalSample (-μ) A := by rw [h]

/-- The reflection about the horizontal axis, restricted to a level set of the statistic. -/
theorem measure_inter_reflect (s c μ t : ℝ) {A : Set (ℝ × ℝ)} (hA : MeasurableSet A) :
    normalSample μ ({z | lam s c z ≤ t} ∩ {z | (z.1, -z.2) ∈ A}) = normalSample (-μ) ({z | lam s c z ≤ t} ∩ A) := by
  have hE : MeasurableSet {z | lam s c z ≤ t} :=
    measurableSet_le (measurable_lam s c) measurable_const
  rw [← P_reflect_y μ (hE.inter hA)]
  congr 1
  ext z
  simp [lam_reflect_y]

/-- `G₆`, which is identical to `G₁`, but after mapping the generating parameter as
`(0, μ) ↦ (0, -μ)`, as in the paper. -/
theorem measure_inter_R₆ {α : ℝ} (hα : α ∈ Ioo 0 (Real.pi / 2)) (μ t : ℝ) :
    normalSample μ ({z | lam (Real.sin α) (Real.cos α) z ≤ t} ∩ R₆ (Real.sin α) (Real.cos α)) =
      ∫⁻ u in Ioc 0 √t, ENNReal.ofReal (h 0 (-μ) ((1 + Real.sin α) / Real.cos α) u) := by
  have hset : R₆ (Real.sin α) (Real.cos α) = {z | (z.1, -z.2) ∈ R₁ (Real.sin α) (Real.cos α)} := by
    ext z
    simp only [R₆, R₁, mem_ofPred_eq]
    constructor <;> rintro ⟨h1, h2⟩ <;> exact ⟨h1, by linarith⟩
  rw [hset, measure_inter_reflect _ _ _ _ (measurableSet_R₁ _ _), measure_inter_R₁ hα]

/-- The fourth quadrant is, up to the null lines `y = -x tan α₀` and `y = -x cot β₀`, the union of
the disjoint sets `R₄`, `R₅`, `R₆`. -/
theorem measure_quadrant' {s c : ℝ} (hs : 0 < s) (hc : 0 < c) (μ t : ℝ) :
    normalSample μ ({z | lam s c z ≤ t} ∩ {z | 0 < z.1} ∩ {z | z.2 < 0}) =
      normalSample μ ({z | lam s c z ≤ t} ∩ R₄ s c) + normalSample μ ({z | lam s c z ≤ t} ∩ R₅ s c) +
        normalSample μ ({z | lam s c z ≤ t} ∩ R₆ s c) := by
  have h1 := gaussianReal_prod_split (k₁ := s) (k₂ := c) (Or.inr hc.ne') 0 μ
    ({z | lam s c z ≤ t} ∩ {z | 0 < z.1} ∩ {z | z.2 < 0})
  have h2 := gaussianReal_prod_split (k₁ := 1 + s) (k₂ := c) (Or.inr hc.ne') 0 μ
    ({z | lam s c z ≤ t} ∩ {z | 0 < z.1} ∩ {z | z.2 < 0} ∩ {z | s * z.1 + c * z.2 < 0})
  have e4 : {z | lam s c z ≤ t} ∩ {z | 0 < z.1} ∩ {z | z.2 < 0} ∩ {z | 0 < s * z.1 + c * z.2} =
      {z | lam s c z ≤ t} ∩ R₄ s c := by
    ext z
    simp only [mem_inter_iff, mem_ofPred_eq, R₄]
    constructor
    · rintro ⟨⟨⟨hE, -⟩, hy⟩, hf⟩
      exact ⟨hE, hy, by linarith⟩
    · rintro ⟨hE, hy, hb⟩
      have hcy := mul_neg_of_pos_of_neg hc hy
      have hsx : 0 < s * z.1 := by linarith
      exact ⟨⟨⟨hE, (mul_pos_iff_of_pos_left hs).1 hsx⟩, hy⟩, by linarith⟩
  have e5 : {z | lam s c z ≤ t} ∩ {z | 0 < z.1} ∩ {z | z.2 < 0} ∩ {z | s * z.1 + c * z.2 < 0} ∩
      {z | 0 < (1 + s) * z.1 + c * z.2} = {z | lam s c z ≤ t} ∩ R₅ s c := by
    ext z
    simp only [mem_inter_iff, mem_ofPred_eq, R₅]
    constructor
    · rintro ⟨⟨⟨⟨hE, -⟩, -⟩, hf⟩, hf'⟩
      exact ⟨hE, by linarith, by linarith⟩
    · rintro ⟨hE, hb, hb'⟩
      have hx : 0 < z.1 := by linarith
      have hsx := mul_pos hs hx
      have hcy : c * z.2 < 0 := by linarith
      exact ⟨⟨⟨⟨hE, hx⟩, neg_of_mul_neg_right hcy hc.le⟩, by linarith⟩, by linarith⟩
  have e6 : {z | lam s c z ≤ t} ∩ {z | 0 < z.1} ∩ {z | z.2 < 0} ∩ {z | s * z.1 + c * z.2 < 0} ∩
      {z | (1 + s) * z.1 + c * z.2 < 0} = {z | lam s c z ≤ t} ∩ R₆ s c := by
    ext z
    simp only [mem_inter_iff, mem_ofPred_eq, R₆]
    constructor
    · rintro ⟨⟨⟨⟨hE, hx⟩, -⟩, -⟩, hf⟩
      exact ⟨hE, hx, by linarith⟩
    · rintro ⟨hE, hx, hb⟩
      have hsx := mul_pos hs hx
      have hcy : c * z.2 < 0 := by linarith
      exact ⟨⟨⟨⟨hE, hx⟩, neg_of_mul_neg_right hcy hc.le⟩, by linarith⟩, by linarith⟩
  rw [e5, e6] at h2
  rw [e4, h2] at h1
  rw [h1, add_assoc]

/-- The paper's `G = 2 ∑_{i=1}^6 G_i`, for the squared distance: the level set of the statistic is,
up to null sets, the union of the disjoint parts in `R₁, ..., R₆` and of their reflections about
the vertical axis. -/
theorem measure_lam_le_eq_sum {s c : ℝ} (hs : 0 < s) (hc : 0 < c) (μ t : ℝ) :
    normalSample μ {z | lam s c z ≤ t} =
      2 * (normalSample μ ({z | lam s c z ≤ t} ∩ R₁ s c) + normalSample μ ({z | lam s c z ≤ t} ∩ R₂ s c) +
        normalSample μ ({z | lam s c z ≤ t} ∩ R₃ s c) + normalSample μ ({z | lam s c z ≤ t} ∩ R₄ s c) +
        normalSample μ ({z | lam s c z ≤ t} ∩ R₅ s c) + normalSample μ ({z | lam s c z ≤ t} ∩ R₆ s c)) := by
  have hE : MeasurableSet {z | lam s c z ≤ t} :=
    measurableSet_le (measurable_lam s c) measurable_const
  have hx : MeasurableSet {z : ℝ × ℝ | 0 < z.1} := measurableSet_lt measurable_const measurable_fst
  have h1 := gaussianReal_prod_split (k₁ := 1) (k₂ := 0) (Or.inl one_ne_zero) 0 μ
    {z | lam s c z ≤ t}
  have h2 := gaussianReal_prod_split (k₁ := 0) (k₂ := 1) (Or.inr one_ne_zero) 0 μ
    ({z | lam s c z ≤ t} ∩ {z | 0 < z.1})
  have e1 : {z | lam s c z ≤ t} ∩ {z : ℝ × ℝ | 0 < 1 * z.1 + 0 * z.2} =
      {z | lam s c z ≤ t} ∩ {z | 0 < z.1} := by
    ext z; simp
  have e2 : {z | lam s c z ≤ t} ∩ {z : ℝ × ℝ | 1 * z.1 + 0 * z.2 < 0} =
      {z | (-z.1, z.2) ∈ {z | lam s c z ≤ t} ∩ {z : ℝ × ℝ | 0 < z.1}} := by
    ext z
    simp [lam_reflect_x]
  have e3 : {z | lam s c z ≤ t} ∩ {z : ℝ × ℝ | 0 < z.1} ∩ {z : ℝ × ℝ | 0 < 0 * z.1 + 1 * z.2} =
      {z | lam s c z ≤ t} ∩ {z | 0 < z.1} ∩ {z | 0 < z.2} := by
    ext z; simp
  have e4 : {z | lam s c z ≤ t} ∩ {z : ℝ × ℝ | 0 < z.1} ∩ {z : ℝ × ℝ | 0 * z.1 + 1 * z.2 < 0} =
      {z | lam s c z ≤ t} ∩ {z | 0 < z.1} ∩ {z | z.2 < 0} := by
    ext z; simp
  rw [e1, e2, P_reflect_x μ (hE.inter hx)] at h1
  rw [e3, e4, measure_quadrant hs hc, measure_quadrant' hs hc] at h2
  rw [h1, h2]
  ring

private lemma ofReal_add_six {a₁ a₂ a₃ a₄ a₅ a₆ : ℝ} (h₁ : 0 ≤ a₁) (h₂ : 0 ≤ a₂) (h₃ : 0 ≤ a₃)
    (h₄ : 0 ≤ a₄) (h₅ : 0 ≤ a₅) (h₆ : 0 ≤ a₆) :
    ENNReal.ofReal (a₁ + a₂ + a₃ + a₄ + a₅ + a₆) =
      ENNReal.ofReal a₁ + ENNReal.ofReal a₂ + ENNReal.ofReal a₃ + ENNReal.ofReal a₄ +
        ENNReal.ofReal a₅ + ENNReal.ofReal a₆ := by
  rw [ENNReal.ofReal_add (by positivity) h₆, ENNReal.ofReal_add (by positivity) h₅,
    ENNReal.ofReal_add (by positivity) h₄, ENNReal.ofReal_add (by positivity) h₃,
    ENNReal.ofReal_add h₁ h₂]

/-- The paper's density `g` of the (non-squared) distance, `2 ∑_{i=1}^6 d/dx G_i`. -/
def g (s c μ u : ℝ) : ℝ :=
  2 * (h 0 μ ((1 + s) / c) u + h (μ * c) (μ * s) ((1 + s) / c) u + h (-μ * c) (μ * s) (c / s) u +
    h (μ * c) (-μ * s) (c / s) u + h (-μ * c) (-μ * s) ((1 + s) / c) u + h 0 (-μ) ((1 + s) / c) u)

/-- The law of the statistic: `P(Λ ≤ t)` is the integral of `g` over `(0, √t]`. -/
theorem measure_lam_le {α : ℝ} (hα : α ∈ Ioo 0 (Real.pi / 2)) (μ t : ℝ) :
    normalSample μ {z | lam (Real.sin α) (Real.cos α) z ≤ t} =
      ∫⁻ u in Ioc 0 √t, ENNReal.ofReal (g (Real.sin α) (Real.cos α) μ u) := by
  rw [measure_lam_le_eq_sum (sin_pos_of_mem hα) (cos_pos_of_mem hα), measure_inter_R₁ hα,
    measure_inter_R₂ hα, measure_inter_R₃ hα, measure_inter_R₄ hα, measure_inter_R₅ hα,
    measure_inter_R₆ hα]
  set s := Real.sin α
  set c := Real.cos α
  set B := (1 + s) / c
  set A := c / s
  have hsplit : ∀ u, ENNReal.ofReal (g s c μ u) =
      2 * (ENNReal.ofReal (h 0 μ B u) + ENNReal.ofReal (h (μ * c) (μ * s) B u) +
        ENNReal.ofReal (h (-μ * c) (μ * s) A u) + ENNReal.ofReal (h (μ * c) (-μ * s) A u) +
        ENNReal.ofReal (h (-μ * c) (-μ * s) B u) + ENNReal.ofReal (h 0 (-μ) B u)) := by
    intro u
    simp only [g]
    rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat]
    congr 1
    exact ofReal_add_six (h_nonneg _ _ _ _) (h_nonneg _ _ _ _) (h_nonneg _ _ _ _) (h_nonneg _ _ _ _)
      (h_nonneg _ _ _ _) (h_nonneg _ _ _ _)
  have hm : ∀ p q k, Measurable fun u => ENNReal.ofReal (h p q k u) :=
    fun p q k => ENNReal.measurable_ofReal.comp (measurable_h p q k)
  simp_rw [hsplit]
  rw [lintegral_const_mul' _ _ (by norm_num), lintegral_add_right _ (hm _ _ _),
    lintegral_add_right _ (hm _ _ _), lintegral_add_right _ (hm _ _ _),
    lintegral_add_right _ (hm _ _ _), lintegral_add_right _ (hm _ _ _)]

/-- The image of `(0, √t]` under squaring is `(0, t]`, also when both are empty. -/
theorem sq_image_Ioc_sqrt (t : ℝ) : (fun u : ℝ => u ^ 2) '' Ioc 0 √t = Ioc 0 t := by
  ext v
  simp only [mem_image, mem_Ioc]
  constructor
  · rintro ⟨u, ⟨hu, hut⟩, rfl⟩
    exact ⟨by positivity, (Real.le_sqrt' hu).1 hut⟩
  · rintro ⟨hv, hvt⟩
    exact ⟨√v, ⟨Real.sqrt_pos.2 hv, Real.sqrt_le_sqrt hvt⟩, Real.sq_sqrt hv.le⟩

/-- The final substitution of the paper: the change of variable to the squared distance. -/
theorem lintegral_sq_subst (t : ℝ) (f : ℝ → ℝ≥0∞) :
    ∫⁻ v in Ioc 0 t, f v = ∫⁻ u in Ioc 0 √t, ENNReal.ofReal (2 * u) * f (u ^ 2) := by
  rw [← sq_image_Ioc_sqrt t, lintegral_image_eq_lintegral_abs_deriv_mul (f' := fun u => 2 * u)
    measurableSet_Ioc]
  · refine setLIntegral_congr_fun measurableSet_Ioc fun u hu => ?_
    simp only [abs_of_pos (mul_pos two_pos hu.1)]
  · intro u _
    simpa using (hasDerivAt_pow 2 u).hasDerivWithinAt
  · intro a ha b hb hab
    exact (sq_eq_sq₀ ha.1.le hb.1.le).1 hab

theorem alpha0_pos (φ : ℝ) (hφ : 0 < φ ∧ φ < 3 / 2) : 0 < alpha0 φ := by
  have h : 0 < 3 * (3 - 2 * φ) := by linarith [hφ.2]
  have : 0 < 1 / √(3 * (3 - 2 * φ)) := by positivity
  simpa [alpha0, Phylogenetics.alphaZero] using Real.arctan_pos.2 this

theorem alpha0_lt (φ : ℝ) : alpha0 φ < Real.pi / 2 := Real.arctan_lt_pi_div_two _

/-- The value of `cot β₀` in terms of `sin α₀` and `cos α₀`. -/
theorem cot_beta0 (φ : ℝ) (hφ : 0 < φ ∧ φ < 3 / 2) :
    Real.cot (beta0 φ) = (1 + Real.sin (alpha0 φ)) / Real.cos (alpha0 φ) :=
  cot_β₀ ⟨alpha0_pos φ hφ, alpha0_lt φ⟩

/-- The printed density is nonnegative, since `erf ≤ 1`. -/
theorem density_nonneg (φ : ℝ) (n : ℕ) (v : ℝ) : 0 ≤ density φ n v := by
  simp only [density]
  split_ifs with hv
  · have he := Real.erf_le_one
    refine mul_nonneg (by positivity) (add_nonneg (add_nonneg ?_ ?_) ?_) <;>
      refine mul_nonneg (Real.exp_pos _).le ?_ <;>
      linarith [he ((√v * Real.cot (beta0 φ) + mu0 φ n) / √2),
        he ((√v * Real.cot (beta0 φ) - mu0 φ n) / √2),
        he ((√v * Real.cot (alpha0 φ) + mu0 φ n * Real.sin (alpha0 φ)) / √2),
        he ((√v * Real.cot (alpha0 φ) - mu0 φ n * Real.sin (alpha0 φ)) / √2),
        he ((√v * Real.cot (beta0 φ) + mu0 φ n * Real.sin (alpha0 φ)) / √2),
        he ((√v * Real.cot (beta0 φ) - mu0 φ n * Real.sin (alpha0 φ)) / √2)]
  · exact le_rfl

/-- On `u > 0`, `2 u f(u²)` is the density `g` of the distance, where `f` is the printed density. -/
theorem two_mul_mul_density (φ : ℝ) (hφ : 0 < φ ∧ φ < 3 / 2) (n : ℕ) {u : ℝ} (hu : 0 < u) :
    2 * u * density φ n (u ^ 2) =
      g (Real.sin (alpha0 φ)) (Real.cos (alpha0 φ)) (mu0 φ n) u := by
  have hu2 : 0 < u ^ 2 := by positivity
  simp only [density, hu2, ↓reduceIte, Real.sqrt_sq hu.le, cot_beta0 φ hφ,
    Real.cot_eq_cos_div_sin]
  have hsqrt : √(2 * Real.pi * u ^ 2) = √(2 * Real.pi) * u := by
    rw [Real.sqrt_mul (by positivity), Real.sqrt_sq hu.le]
  rw [hsqrt]
  have hC : √(2 * Real.pi) ≠ 0 := (Real.sqrt_pos.2 (by positivity)).ne'
  have hfac : 2 * u * (1 / (2 * (√(2 * Real.pi) * u))) = (√(2 * Real.pi))⁻¹ := by
    field_simp
  rw [← mul_assoc, hfac]
  simp only [g, h, gaussianPDFReal_one]
  ring_nf

/-- The second part of Proposition 6: the law of `Λ_n`, from the distribution function of the
statistic and the substitution to the squared distance. -/
theorem lambdaLaw_eq (φ : ℝ) (hφ : 0 < φ ∧ φ < 3 / 2) (n : ℕ) :
    lambdaLaw φ n = volume.withDensity (fun lam => ENNReal.ofReal (density φ n lam)) := by
  have hL : Measurable (lambdaCandidate φ) := measurable_lam _ _
  have hfin : IsFiniteMeasure (lambdaLaw φ n) := by
    unfold lambdaLaw; infer_instance
  refine Measure.ext_of_Iic _ _ fun t => ?_
  have hIic : MeasurableSet (Iic t) := measurableSet_Iic
  rw [lambdaLaw, Measure.map_apply hL hIic, withDensity_apply _ hIic]
  have hP := measure_lam_le (α := alpha0 φ) ⟨alpha0_pos φ hφ, alpha0_lt φ⟩ (mu0 φ n) t
  have hset : lambdaCandidate φ ⁻¹' Iic t =
      {z | Prop6.lam (Real.sin (alpha0 φ)) (Real.cos (alpha0 φ)) z ≤ t} := rfl
  rw [hset]
  refine hP.trans ?_
  have hind : ∫⁻ v in Iic t, ENNReal.ofReal (density φ n v) =
      ∫⁻ v in Ioc 0 t, ENNReal.ofReal (density φ n v) := by
    rw [← lintegral_indicator (measurableSet_Iic : MeasurableSet (Iic t)),
      ← lintegral_indicator (measurableSet_Ioc : MeasurableSet (Ioc 0 t))]
    refine lintegral_congr fun v => ?_
    by_cases hv : 0 < v
    · by_cases hvt : v ≤ t
      · rw [indicator_of_mem (show v ∈ Iic t from hvt),
          indicator_of_mem (show v ∈ Ioc 0 t from ⟨hv, hvt⟩)]
      · rw [indicator_of_notMem (show v ∉ Iic t from hvt),
          indicator_of_notMem (show v ∉ Ioc 0 t from fun h => hvt h.2)]
    · have h0 : ENNReal.ofReal (density φ n v) = 0 := by simp [density, hv]
      rw [indicator_of_notMem (show v ∉ Ioc 0 t from fun h => hv h.1)]
      by_cases hvt : v ≤ t
      · rw [indicator_of_mem (show v ∈ Iic t from hvt), h0]
      · rw [indicator_of_notMem (show v ∉ Iic t from hvt)]
  have hIoc : MeasurableSet (Ioc 0 √t) := measurableSet_Ioc
  rw [hind, lintegral_sq_subst t fun v => ENNReal.ofReal (density φ n v)]
  refine setLIntegral_congr_fun hIoc fun u hu => ?_
  rw [← ENNReal.ofReal_mul (mul_pos two_pos hu.1).le, two_mul_mul_density φ hφ n hu.1]

end Prop6

/-- **Proposition 6** (`tinnik:proposition6`). The law of `Λ_n` has, on `λ > 0`, the printed
density. The value `0` has mass zero, so this determines the law. See the module docstring for the
proof. -/
theorem proposition6 (φ : ℝ) (hφ : 0 < φ ∧ φ < 3 / 2) (n : ℕ) :
    (∀ lam, 0 ≤ density φ n lam) ∧
      lambdaLaw φ n = volume.withDensity (fun lam => ENNReal.ofReal (density φ n lam)) :=
  ⟨Prop6.density_nonneg φ n, Prop6.lambdaLaw_eq φ hφ n⟩

end TINNiK
