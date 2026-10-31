module

public import TINNiK.Statistics.AppendixC
public import Basic.Probability.GaussianPlane

/-!
# TINNiK Appendix C.2: Proposition 6, the density of the test distribution

The proof follows the paper. Write `G` for the cumulative distribution function of the non-squared
distance from the normal sample `N((0, μ₀), I)` to the three lines `x = 0`, `y = ± x tan α₀`. The
three lines and their bisectors cut the half-plane `x > 0` into six sectors, and the points of a
sector within distance `x` of the lines form the paper's strip `R_i`. The reflection about the
vertical axis gives `G = 2 ∑_{i=1}^6 G_i`, where `G_i` is the probability of `R_i`
(`measure_lam_le_eq_sum`). Each `G_i` is evaluated to an integral of a normal density times an `erf`
term (`measure_inter_R₁`, ..., `measure_inter_R₆`), and the density of `Λ` comes from the change of
variable to the squared distance (`lintegral_sq_subst`).

Notes on the evaluation.
* The integrals over the strips are evaluated in rotated Cartesian coordinates (`u` along the normal
  of the line, `v` along the line) rather than polar coordinates; after the paper's substitution
  `y = x tan β` these are the paper's integrals.
* In place of differentiating `G_i` under the integral sign, `G_i(x)` is written as the integral
  from `0` to `x` of the paper's expression for `d/dx G_i` (Fubini). The expression is `h` below.
* `R₄, R₅, R₆` are the reflections of `R₃, R₂, R₁` about the horizontal axis, so `G₄, G₅, G₆` are
  `G₃, G₂, G₁` with `μ` replaced by `-μ`. The paper observes this for `G₆`, and for `G₄, G₅` repeats
  the computation in a rotated figure, which gives the same formulas.

All statements about the plane are in terms of `s = sin α₀`, `c = cos α₀`, with `0 < s`, `0 < c` and
`s² + c² = 1`; then `cot α₀ = c / s` and `cot β₀ = (1 + s) / c`.
-/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

namespace TINNiK

namespace Prop6

open Set

/-- The law of the normal sample, with mean `(0, μ)` and identity covariance. -/
abbrev P (μ : ℝ) : Measure (ℝ × ℝ) := (gaussianReal 0 1).prod (gaussianReal μ 1)

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

/-- The paper's strip `R₄`: the reflection of `R₃` about the horizontal axis. -/
def R₄ (s c : ℝ) : Set (ℝ × ℝ) := {z | (z.1, -z.2) ∈ R₃ s c}

/-- The paper's strip `R₅`: the reflection of `R₂` about the horizontal axis. -/
def R₅ (s c : ℝ) : Set (ℝ × ℝ) := {z | (z.1, -z.2) ∈ R₂ s c}

/-- The paper's strip `R₆`: the reflection of `R₁` about the horizontal axis. -/
def R₆ (s c : ℝ) : Set (ℝ × ℝ) := {z | (z.1, -z.2) ∈ R₁ s c}

theorem measurableSet_R₁ (s c : ℝ) : MeasurableSet (R₁ s c) := by
  have h1 : MeasurableSet {z : ℝ × ℝ | 0 < z.1} :=
    measurableSet_lt measurable_const measurable_fst
  have h2 : MeasurableSet {z : ℝ × ℝ | (1 + s) * z.1 < c * z.2} :=
    measurableSet_lt (by fun_prop) (by fun_prop)
  exact h1.inter h2

theorem measurableSet_R₂ (s c : ℝ) : MeasurableSet (R₂ s c) := by
  have h1 : MeasurableSet {z : ℝ × ℝ | s * z.1 < c * z.2} :=
    measurableSet_lt (by fun_prop) (by fun_prop)
  have h2 : MeasurableSet {z : ℝ × ℝ | c * z.2 < (1 + s) * z.1} :=
    measurableSet_lt (by fun_prop) (by fun_prop)
  exact h1.inter h2

theorem measurableSet_R₃ (s c : ℝ) : MeasurableSet (R₃ s c) := by
  have h1 : MeasurableSet {z : ℝ × ℝ | 0 < z.2} :=
    measurableSet_lt measurable_const measurable_snd
  have h2 : MeasurableSet {z : ℝ × ℝ | c * z.2 < s * z.1} :=
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

/-- The integrand of the strip with normal coordinate of mean `p`, coordinate along the line of mean
`q`, and slope `k`: the paper's `d/dx G_i`. -/
def h (p q k u : ℝ) : ℝ :=
  gaussianPDFReal p 1 u * (1 / 2 * (1 - Real.erf ((k * u - q) / √2)))

theorem h_nonneg (p q k u : ℝ) : 0 ≤ h p q k u :=
  mul_nonneg (gaussianPDFReal_nonneg _ _ _) (by linarith [Real.erf_le_one ((k * u - q) / √2)])

theorem measurable_h (p q k : ℝ) : Measurable (h p q k) := by
  refine (measurable_gaussianPDFReal p 1).mul (Continuous.measurable ?_)
  have := Real.continuous_erf
  fun_prop

/-- `G₁`: the probability of the part of `R₁` within distance `√t` of `x = 0`. -/
theorem measure_inter_R₁ {s c : ℝ} (hs : 0 < s) (hc : 0 < c) (μ t : ℝ) :
    P μ ({z | lam s c z ≤ t} ∩ R₁ s c) =
      ∫⁻ u in Ioc 0 √t, ENNReal.ofReal (h 0 μ ((1 + s) / c) u) := by
  have hset : {z | lam s c z ≤ t} ∩ R₁ s c =
      {z | 0 < 1 * z.1 + 0 * z.2 ∧ 1 * z.1 + 0 * z.2 ≤ √t ∧
        (1 + s) / c * (1 * z.1 + 0 * z.2) < 0 * z.1 + 1 * z.2} := by
    ext z
    simp only [mem_inter_iff, mem_ofPred_eq, one_mul, zero_mul, add_zero, zero_add]
    have key : (1 + s) / c * z.1 < z.2 ↔ (1 + s) * z.1 < c * z.2 := by
      rw [div_mul_eq_mul_div, div_lt_iff₀ hc, mul_comm z.2 c]
    constructor
    · rintro ⟨hl, hz⟩
      rw [lam_of_mem_R₁ hs hz] at hl
      exact ⟨hz.1, (Real.le_sqrt' hz.1).2 hl, key.2 hz.2⟩
    · rintro ⟨hx, hxt, hv⟩
      have hz : z ∈ R₁ s c := ⟨hx, key.1 hv⟩
      exact ⟨by rw [lam_of_mem_R₁ hs hz]; exact (Real.le_sqrt' hx).1 hxt, hz⟩
  rw [hset, gaussianReal_prod_strip (by norm_num) (by norm_num) (by norm_num)]
  simp only [h]
  rw [show (1 : ℝ) * 0 + 0 * μ = 0 by ring, show (0 : ℝ) * 0 + 1 * μ = μ by ring]

/-- `G₂`: the probability of the part of `R₂` within distance `√t` of `y = x tan α₀`, by the rotated
coordinates `u = -s x + c y`, `v = c x + s y`, in which the mean is `(μ c, μ s)`. -/
theorem measure_inter_R₂ {s c : ℝ} (hs : 0 < s) (hc : 0 < c) (hsc : s ^ 2 + c ^ 2 = 1) (μ t : ℝ) :
    P μ ({z | lam s c z ≤ t} ∩ R₂ s c) =
      ∫⁻ u in Ioc 0 √t, ENNReal.ofReal (h (μ * c) (μ * s) ((1 + s) / c) u) := by
  have hset : {z | lam s c z ≤ t} ∩ R₂ s c =
      {z | 0 < -s * z.1 + c * z.2 ∧ -s * z.1 + c * z.2 ≤ √t ∧
        (1 + s) / c * (-s * z.1 + c * z.2) < c * z.1 + s * z.2} := by
    ext z
    simp only [mem_inter_iff, mem_ofPred_eq]
    have key : (1 + s) / c * (-s * z.1 + c * z.2) < c * z.1 + s * z.2 ↔
        c * z.2 < (1 + s) * z.1 := by
      rw [div_mul_eq_mul_div, div_lt_iff₀ hc]
      have : (c * z.1 + s * z.2) * c - (1 + s) * (-s * z.1 + c * z.2) =
          (1 + s) * z.1 - c * z.2 := by linear_combination z.1 * hsc
      constructor <;> intro <;> linarith
    constructor
    · rintro ⟨hl, hz⟩
      rw [lam_of_mem_R₂ hs hz] at hl
      have hu : 0 < -s * z.1 + c * z.2 := by linarith [hz.1]
      exact ⟨hu, (Real.le_sqrt' hu).2 hl, key.2 hz.2⟩
    · rintro ⟨hu, hut, hv⟩
      have hz : z ∈ R₂ s c := ⟨by linarith, key.1 hv⟩
      exact ⟨by rw [lam_of_mem_R₂ hs hz]; exact (Real.le_sqrt' hu).1 hut, hz⟩
  rw [hset, gaussianReal_prod_strip (by linear_combination hsc) (by linear_combination hsc)
    (by ring)]
  simp only [h]
  rw [show -s * 0 + c * μ = μ * c by ring, show c * 0 + s * μ = μ * s by ring]

/-- `G₃`: the probability of the part of `R₃` within distance `√t` of `y = x tan α₀`, by the rotated
coordinates `u = s x - c y`, `v = c x + s y`, in which the mean is `(-μ c, μ s)`. -/
theorem measure_inter_R₃ {s c : ℝ} (hs : 0 < s) (hc : 0 < c) (hsc : s ^ 2 + c ^ 2 = 1) (μ t : ℝ) :
    P μ ({z | lam s c z ≤ t} ∩ R₃ s c) =
      ∫⁻ u in Ioc 0 √t, ENNReal.ofReal (h (-μ * c) (μ * s) (c / s) u) := by
  have hset : {z | lam s c z ≤ t} ∩ R₃ s c =
      {z | 0 < s * z.1 + -c * z.2 ∧ s * z.1 + -c * z.2 ≤ √t ∧
        c / s * (s * z.1 + -c * z.2) < c * z.1 + s * z.2} := by
    ext z
    simp only [mem_inter_iff, mem_ofPred_eq]
    have key : c / s * (s * z.1 + -c * z.2) < c * z.1 + s * z.2 ↔ 0 < z.2 := by
      rw [div_mul_eq_mul_div, div_lt_iff₀ hs]
      have : (c * z.1 + s * z.2) * s - c * (s * z.1 + -c * z.2) = z.2 := by
        linear_combination z.2 * hsc
      constructor <;> intro <;> linarith
    constructor
    · rintro ⟨hl, hz⟩
      rw [lam_of_mem_R₃ hs hc hsc hz] at hl
      have hu : 0 < s * z.1 + -c * z.2 := by linarith [hz.2]
      exact ⟨hu, (Real.le_sqrt' hu).2 hl, key.2 hz.1⟩
    · rintro ⟨hu, hut, hv⟩
      have hz : z ∈ R₃ s c := ⟨key.1 hv, by linarith⟩
      exact ⟨by rw [lam_of_mem_R₃ hs hc hsc hz]; exact (Real.le_sqrt' hu).1 hut, hz⟩
  rw [hset, gaussianReal_prod_strip (by linear_combination hsc) (by linear_combination hsc)
    (by ring)]
  simp only [h]
  rw [show s * 0 + -c * μ = -μ * c by ring, show c * 0 + s * μ = μ * s by ring]

/-- The first quadrant is, up to the null lines `y = x tan α₀` and `y = x cot β₀`, the union of the
disjoint sets `R₁`, `R₂`, `R₃`. -/
theorem measure_quadrant {s c : ℝ} (hs : 0 < s) (hc : 0 < c) (μ t : ℝ) :
    P μ ({z | lam s c z ≤ t} ∩ {z | 0 < z.1} ∩ {z | 0 < z.2}) =
      P μ ({z | lam s c z ≤ t} ∩ R₁ s c) + P μ ({z | lam s c z ≤ t} ∩ R₂ s c) +
        P μ ({z | lam s c z ≤ t} ∩ R₃ s c) := by
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
    P μ {z | (-z.1, z.2) ∈ A} = P μ A := by
  have h := gaussianReal_prod_map_orthonormal (a := -1) (b := 0) (a' := 0) (b' := 1)
    (by norm_num) (by norm_num) (by norm_num) 0 μ
  have e : (fun z : ℝ × ℝ => (-1 * z.1 + 0 * z.2, 0 * z.1 + 1 * z.2)) = fun z => (-z.1, z.2) := by
    funext z; simp
  rw [e, show (-1 : ℝ) * 0 + 0 * μ = 0 by ring, show (0 : ℝ) * 0 + 1 * μ = μ by ring] at h
  have hm : Measurable (fun z : ℝ × ℝ => (-z.1, z.2)) := by fun_prop
  calc P μ {z | (-z.1, z.2) ∈ A} = ((P μ).map fun z : ℝ × ℝ => (-z.1, z.2)) A :=
        (Measure.map_apply hm hA).symm
    _ = P μ A := by rw [h]

/-- The reflection about the horizontal axis changes the sign of the mean. -/
theorem P_reflect_y (μ : ℝ) {A : Set (ℝ × ℝ)} (hA : MeasurableSet A) :
    P μ {z | (z.1, -z.2) ∈ A} = P (-μ) A := by
  have h := gaussianReal_prod_map_orthonormal (a := 1) (b := 0) (a' := 0) (b' := -1)
    (by norm_num) (by norm_num) (by norm_num) 0 μ
  have e : (fun z : ℝ × ℝ => (1 * z.1 + 0 * z.2, 0 * z.1 + -1 * z.2)) = fun z => (z.1, -z.2) := by
    funext z; simp
  rw [e, show (1 : ℝ) * 0 + 0 * μ = 0 by ring, show (0 : ℝ) * 0 + -1 * μ = -μ by ring] at h
  have hm : Measurable (fun z : ℝ × ℝ => (z.1, -z.2)) := by fun_prop
  calc P μ {z | (z.1, -z.2) ∈ A} = ((P μ).map fun z : ℝ × ℝ => (z.1, -z.2)) A :=
        (Measure.map_apply hm hA).symm
    _ = P (-μ) A := by rw [h]

/-- The reflection about the horizontal axis, restricted to a level set of the statistic. -/
theorem measure_inter_reflect (s c μ t : ℝ) {A : Set (ℝ × ℝ)} (hA : MeasurableSet A) :
    P μ ({z | lam s c z ≤ t} ∩ {z | (z.1, -z.2) ∈ A}) = P (-μ) ({z | lam s c z ≤ t} ∩ A) := by
  have hE : MeasurableSet {z | lam s c z ≤ t} :=
    measurableSet_le (measurable_lam s c) measurable_const
  rw [← P_reflect_y μ (hE.inter hA)]
  congr 1
  ext z
  simp [lam_reflect_y]

/-- `G₄`, which is `G₃` with `μ` replaced by `-μ`. -/
theorem measure_inter_R₄ {s c : ℝ} (hs : 0 < s) (hc : 0 < c) (hsc : s ^ 2 + c ^ 2 = 1) (μ t : ℝ) :
    P μ ({z | lam s c z ≤ t} ∩ R₄ s c) =
      ∫⁻ u in Ioc 0 √t, ENNReal.ofReal (h (μ * c) (-μ * s) (c / s) u) := by
  have e : P μ ({z | lam s c z ≤ t} ∩ R₄ s c) = P (-μ) ({z | lam s c z ≤ t} ∩ R₃ s c) :=
    measure_inter_reflect s c μ t (measurableSet_R₃ s c)
  rw [e, measure_inter_R₃ hs hc hsc, neg_neg]

/-- `G₅`, which is `G₂` with `μ` replaced by `-μ`. -/
theorem measure_inter_R₅ {s c : ℝ} (hs : 0 < s) (hc : 0 < c) (hsc : s ^ 2 + c ^ 2 = 1) (μ t : ℝ) :
    P μ ({z | lam s c z ≤ t} ∩ R₅ s c) =
      ∫⁻ u in Ioc 0 √t, ENNReal.ofReal (h (-μ * c) (-μ * s) ((1 + s) / c) u) := by
  have e : P μ ({z | lam s c z ≤ t} ∩ R₅ s c) = P (-μ) ({z | lam s c z ≤ t} ∩ R₂ s c) :=
    measure_inter_reflect s c μ t (measurableSet_R₂ s c)
  rw [e, measure_inter_R₂ hs hc hsc]

/-- `G₆`, which is `G₁` with `μ` replaced by `-μ`, as in the paper. -/
theorem measure_inter_R₆ {s c : ℝ} (hs : 0 < s) (hc : 0 < c) (μ t : ℝ) :
    P μ ({z | lam s c z ≤ t} ∩ R₆ s c) =
      ∫⁻ u in Ioc 0 √t, ENNReal.ofReal (h 0 (-μ) ((1 + s) / c) u) := by
  have e : P μ ({z | lam s c z ≤ t} ∩ R₆ s c) = P (-μ) ({z | lam s c z ≤ t} ∩ R₁ s c) :=
    measure_inter_reflect s c μ t (measurableSet_R₁ s c)
  rw [e, measure_inter_R₁ hs hc]

/-- The paper's `G = 2 ∑_{i=1}^6 G_i`, for the squared distance: the level set of the statistic is,
up to null sets, the union of the disjoint parts in `R₁, ..., R₆` and of their reflections about
the vertical axis. -/
theorem measure_lam_le_eq_sum {s c : ℝ} (hs : 0 < s) (hc : 0 < c) (μ t : ℝ) :
    P μ {z | lam s c z ≤ t} =
      2 * (P μ ({z | lam s c z ≤ t} ∩ R₁ s c) + P μ ({z | lam s c z ≤ t} ∩ R₂ s c) +
        P μ ({z | lam s c z ≤ t} ∩ R₃ s c) + P μ ({z | lam s c z ≤ t} ∩ R₄ s c) +
        P μ ({z | lam s c z ≤ t} ∩ R₅ s c) + P μ ({z | lam s c z ≤ t} ∩ R₆ s c)) := by
  have hE : MeasurableSet {z | lam s c z ≤ t} :=
    measurableSet_le (measurable_lam s c) measurable_const
  have hx : MeasurableSet {z : ℝ × ℝ | 0 < z.1} := measurableSet_lt measurable_const measurable_fst
  have hy : MeasurableSet {z : ℝ × ℝ | 0 < z.2} := measurableSet_lt measurable_const measurable_snd
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
      {z | (z.1, -z.2) ∈ {z | lam s c z ≤ t} ∩ {z : ℝ × ℝ | 0 < z.1} ∩ {z : ℝ × ℝ | 0 < z.2}} := by
    ext z
    simp [lam_reflect_y]
  rw [e1, e2, P_reflect_x μ (hE.inter hx)] at h1
  rw [e3, e4, P_reflect_y μ ((hE.inter hx).inter hy), measure_quadrant hs hc,
    measure_quadrant hs hc] at h2
  have r4 : P μ ({z | lam s c z ≤ t} ∩ R₄ s c) = P (-μ) ({z | lam s c z ≤ t} ∩ R₃ s c) :=
    measure_inter_reflect s c μ t (measurableSet_R₃ s c)
  have r5 : P μ ({z | lam s c z ≤ t} ∩ R₅ s c) = P (-μ) ({z | lam s c z ≤ t} ∩ R₂ s c) :=
    measure_inter_reflect s c μ t (measurableSet_R₂ s c)
  have r6 : P μ ({z | lam s c z ≤ t} ∩ R₆ s c) = P (-μ) ({z | lam s c z ≤ t} ∩ R₁ s c) :=
    measure_inter_reflect s c μ t (measurableSet_R₁ s c)
  rw [h1, h2, r4, r5, r6]
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
theorem measure_lam_le {s c : ℝ} (hs : 0 < s) (hc : 0 < c) (hsc : s ^ 2 + c ^ 2 = 1) (μ t : ℝ) :
    P μ {z | lam s c z ≤ t} = ∫⁻ u in Ioc 0 √t, ENNReal.ofReal (g s c μ u) := by
  rw [measure_lam_le_eq_sum hs hc, measure_inter_R₁ hs hc, measure_inter_R₂ hs hc hsc,
    measure_inter_R₃ hs hc hsc, measure_inter_R₄ hs hc hsc, measure_inter_R₅ hs hc hsc,
    measure_inter_R₆ hs hc]
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

/-- The value of the normal density with unit variance. -/
theorem pdf_one (p u : ℝ) :
    gaussianPDFReal p 1 u = (√(2 * Real.pi))⁻¹ * Real.exp (-(u - p) ^ 2 / 2) := by
  simp [gaussianPDFReal]

theorem alpha0_pos (φ : ℝ) (hφ : 0 < φ ∧ φ < 3 / 2) : 0 < alpha0 φ := by
  have h : 0 < 3 * (3 - 2 * φ) := by linarith [hφ.2]
  have : 0 < 1 / √(3 * (3 - 2 * φ)) := by positivity
  simpa [alpha0, Phylogenetics.alphaZero] using Real.arctan_pos.2 this

theorem alpha0_lt (φ : ℝ) : alpha0 φ < Real.pi / 2 := Real.arctan_lt_pi_div_two _

theorem sin_alpha0_pos (φ : ℝ) (hφ : 0 < φ ∧ φ < 3 / 2) : 0 < Real.sin (alpha0 φ) :=
  Real.sin_pos_of_pos_of_lt_pi (alpha0_pos φ hφ) (by linarith [alpha0_lt φ, Real.pi_pos])

theorem cos_alpha0_pos (φ : ℝ) (hφ : 0 < φ ∧ φ < 3 / 2) : 0 < Real.cos (alpha0 φ) :=
  Real.cos_pos_of_mem_Ioo ⟨by linarith [alpha0_pos φ hφ, Real.pi_pos], alpha0_lt φ⟩

/-- The paper's `tan (α₀ + β₀) = cot β₀`, in terms of `sin α₀` and `cos α₀`. -/
theorem cot_beta0 (φ : ℝ) (hφ : 0 < φ ∧ φ < 3 / 2) :
    Real.cot (beta0 φ) = (1 + Real.sin (alpha0 φ)) / Real.cos (alpha0 φ) := by
  have ha : alpha0 φ = Real.pi / 2 - 2 * beta0 φ := by
    simp only [beta0]; ring
  have hb0 : 0 < beta0 φ := by
    simp only [beta0]; linarith [alpha0_lt φ]
  have hb1 : beta0 φ < Real.pi / 2 := by
    simp only [beta0]; linarith [alpha0_pos φ hφ, Real.pi_pos]
  have hsb : 0 < Real.sin (beta0 φ) :=
    Real.sin_pos_of_pos_of_lt_pi hb0 (by linarith [Real.pi_pos])
  have hcb : 0 < Real.cos (beta0 φ) :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hb1⟩
  rw [Real.cot_eq_cos_div_sin, ha, Real.sin_pi_div_two_sub, Real.cos_pi_div_two_sub,
    Real.cos_two_mul, Real.sin_two_mul]
  field_simp
  ring

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
  simp only [g, h, pdf_one]
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
  have hP := measure_lam_le (sin_alpha0_pos φ hφ) (cos_alpha0_pos φ hφ)
    (Real.sin_sq_add_cos_sq _) (mu0 φ n) t
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

/-- **Proposition 6** (`tinnik:proposition6`). The law of `Λ_n` has, on `λ > 0`, the printed density.
The value `0` has mass zero, so this determines the law.

Note: the integrals over the strips are evaluated in rotated Cartesian coordinates; after the
paper's substitution `y = x tan β` these are the paper's integrals. Fubini takes the place of
differentiating under the integral sign. See the module docstring. -/
theorem proposition6 (φ : ℝ) (hφ : 0 < φ ∧ φ < 3 / 2) (n : ℕ) :
    (∀ lam, 0 ≤ density φ n lam) ∧
      lambdaLaw φ n = volume.withDensity (fun lam => ENNReal.ofReal (density φ n lam)) :=
  ⟨Prop6.density_nonneg φ n, Prop6.lambdaLaw_eq φ hφ n⟩

end TINNiK
