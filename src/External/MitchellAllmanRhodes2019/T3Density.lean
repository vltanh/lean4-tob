module

public import External.MitchellAllmanRhodes2019.CutModel
public import External.MitchellAllmanRhodes2019.T3Test
public import Basic.ForMathlib.Probability.GaussianStrip

/-!
# Mitchell, Allman, Rhodes 2019, Proposition 4.2: the density of the T3 test distribution

The law of the variable of Proposition 4.1, `t3Var φ` under `N((0, μ₀), I)`, has on `λ > 0` the density printed in
Equation `eq:T3pdf` of the source, `t3Density`: `QuartetTests.t3Var_density`. The tail `t3Tail` used by the p-value
of the T3 test is its integral: `QuartetTests.t3Tail_eq_integral`.

The proof follows the source's Appendix B. Write `G` for the cumulative distribution function of the non-squared
distance from the normal sample to the three half-lines. The half-lines and their bisectors cut the half-plane
`x > 0` into three pieces, whose parts within distance `x` of the half-lines are the source's shaded strips `R₁`, `R₂`,
`R₃`. The reflection about the vertical axis, "bilateral symmetry", gives `G = 2 (G₁ + G₂ + G₃)`
(`T3Pdf.measure_halfLineDist_le_eq_sum`), and the three are computed as follows.

* `G₁`, the strip along the vertical half-line. In polar coordinates it is the double integral
  `polarStripIntegral 1 β₀ (π / 2) 0 μ₀` of the source's first display, differentiation under the integral sign
  gives its second line, and the substitution `y = x tan β` its last (`T3Pdf.hasDerivAt_G₁`).
* `G₂`, `G₃`, the strips on the two sides of the half-line at the angle `-α₀`. The source reflects about the bisector
  `y = x tan β₀`, which takes the half-line to the vertical axis and the mean to `(μ₀ cos α₀, -μ₀ sin α₀)`, and the strips to
  `y ≥ x tan β₀` and `(-x, y)`, `y ≥ x tan α₀` (`T3Pdf.measure_inter_R₂`, `T3Pdf.measure_inter_R₃`). There the source
  goes "more briefly", with the line integral over the outer boundary. Here they go as `G₁` does, in polar coordinates.

The density of the squared distance comes from the change of variable (`lintegral_Ioc_eq_lintegral_sq`).

Two steps that the source leaves implicit are proved in `Basic.ForMathlib.Probability.GaussianPlane`. Differentiating under
the integral sign needs a dominating function, which exists for `x > 0`; the interchange fails at `x = 0`, which is null.
From the derivative to the density needs `Gᵢ(x) → 0` as `x → 0` and the fundamental theorem of calculus. This is the
same as for TINNiK's Proposition 6 (the report's E32).

The source states this for `φ₀ ∈ (0, 1]`. The computation needs only `0 < α₀ < π / 2`, which holds for all `φ₀ < 3 / 2`,
and is stated so; the mean `μ₀` may then have either sign.
-/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal
open External.MitchellAllmanRhodes2019 (normalSample)

namespace Phylogenetics

/-- The angle `β₀ = (π/2 - α₀) / 2` of Mitchell, Allman, Rhodes 2019, Proposition 4.2. -/
def betaZero (φ : ℝ) : ℝ := (Real.pi / 2 - alphaZero φ) / 2

/-- The density of Mitchell, Allman, Rhodes 2019, Proposition 4.2, Equation `eq:T3pdf`, as printed, with `μ₀ = muZero φ n` and
`α₀ = alphaZero φ`; it is `0` off `λ > 0`, where the source does not give it. -/
def t3Density (φ n lam : ℝ) : ℝ :=
  if 0 < lam then
    1 / (2 * √(2 * Real.pi * lam)) *
      (Real.exp (-(lam / 2)) *
          (1 - Real.erf (1 / √2 * (√lam * Real.tan (betaZero φ) - muZero φ n))) +
        Real.exp (-(1 / 2) * (√lam - muZero φ n * Real.cos (alphaZero φ)) ^ 2) *
          (1 - Real.erf (1 / √2 * (√lam * Real.tan (betaZero φ) +
            muZero φ n * Real.sin (alphaZero φ)))) +
        Real.exp (-(1 / 2) * (√lam + muZero φ n * Real.cos (alphaZero φ)) ^ 2) *
          (1 - Real.erf (1 / √2 * (√lam * Real.tan (alphaZero φ) +
            muZero φ n * Real.sin (alphaZero φ)))))
  else 0

namespace QuartetTests

/-! ### The squared distance to a half-line -/

/-- The squared distance to a half-line, in one formula: that of the line, plus the square of the part of the
projection beyond the origin. -/
theorem sqDistHalfLine_eq {u v : ℝ} (h : u ^ 2 + v ^ 2 = 1) (x y : ℝ) :
    sqDistHalfLine u v x y = (x * v - y * u) ^ 2 + (min (x * u + y * v) 0) ^ 2 := by
  unfold sqDistHalfLine
  split_ifs with hw
  · rw [min_eq_right hw]
    ring
  · rw [min_eq_left (not_le.1 hw).le]
    linear_combination (-(x ^ 2 + y ^ 2)) * h

theorem continuous_sqDistHalfLine {u v : ℝ} (h : u ^ 2 + v ^ 2 = 1) :
    Continuous fun z : ℝ × ℝ => sqDistHalfLine u v z.1 z.2 := by
  simp only [sqDistHalfLine_eq h]
  fun_prop

theorem sqDistHalfLine_neg_neg (u v x y : ℝ) :
    sqDistHalfLine (-u) v (-x) y = sqDistHalfLine u v x y := by
  unfold sqDistHalfLine
  rw [show -x * -u + y * v = x * u + y * v by ring, show -x * v - y * -u = -(x * v - y * u) by ring,
    neg_sq, neg_sq]

/-- The least squared distance from `z` to the three half-lines from the origin in the directions `(0, 1)` and
`(± c, -s)`. For `s = sin α₀`, `c = cos α₀` it is the variable of Proposition 4.1, off the vertical axis:
`t3Var_eq_halfLineDist`. -/
def halfLineDist (s c : ℝ) (z : ℝ × ℝ) : ℝ :=
  min (sqDistHalfLine 0 1 z.1 z.2)
    (min (sqDistHalfLine c (-s) z.1 z.2) (sqDistHalfLine (-c) (-s) z.1 z.2))

theorem continuous_halfLineDist {s c : ℝ} (hsc : s ^ 2 + c ^ 2 = 1) :
    Continuous (halfLineDist s c) := by
  have h₀ := continuous_sqDistHalfLine (u := 0) (v := 1) (by norm_num)
  have h₁ := continuous_sqDistHalfLine (u := c) (v := -s) (by rw [neg_sq, add_comm]; exact hsc)
  have h₂ := continuous_sqDistHalfLine (u := -c) (v := -s) (by rw [neg_sq, neg_sq, add_comm]; exact hsc)
  exact h₀.min (h₁.min h₂)

theorem halfLineDist_reflect_x (s c : ℝ) (z : ℝ × ℝ) :
    halfLineDist s c (-z.1, z.2) = halfLineDist s c z := by
  have h₀ : sqDistHalfLine 0 1 (-z.1) z.2 = sqDistHalfLine 0 1 z.1 z.2 := by
    simpa using sqDistHalfLine_neg_neg 0 1 z.1 z.2
  have h₁ : sqDistHalfLine c (-s) (-z.1) z.2 = sqDistHalfLine (-c) (-s) z.1 z.2 := by
    simpa using sqDistHalfLine_neg_neg (-c) (-s) z.1 z.2
  simp only [halfLineDist]
  rw [h₀, h₁, sqDistHalfLine_neg_neg c (-s) z.1 z.2, min_comm (sqDistHalfLine (-c) (-s) z.1 z.2)]

/-- **The variable of Proposition 4.1 is the distance to the three half-lines**, where `Z ≠ 0`. A restatement of
`t3Var_eq_min_sqDistHalfLine`. -/
theorem t3Var_eq_halfLineDist {φ : ℝ} (hφ : φ < 3 / 2) {z : ℝ × ℝ} (hz : z.1 ≠ 0) :
    t3Var φ z = halfLineDist (Real.sin (alphaZero φ)) (Real.cos (alphaZero φ)) z :=
  t3Var_eq_min_sqDistHalfLine hφ hz z.2

/-- Almost surely, the variable of Proposition 4.1 is the distance to the three half-lines. -/
theorem t3Var_ae_eq_halfLineDist {φ : ℝ} (hφ : φ < 3 / 2) (μ : ℝ) :
    t3Var φ =ᵐ[normalSample μ] halfLineDist (Real.sin (alphaZero φ)) (Real.cos (alphaZero φ)) := by
  have hne : ∀ᵐ z ∂(normalSample μ), z.1 ≠ 0 := by
    rw [ae_iff]
    simpa using gaussianReal_prod_line_null (k₁ := 1) (k₂ := 0) (Or.inl one_ne_zero) 0 μ
  filter_upwards [hne] with z hz
  exact t3Var_eq_halfLineDist hφ hz

namespace T3Pdf

variable {s c : ℝ}

/-! ### The three strips -/

/-- The source's strip `R₁`, without its bound on the distance: the points of `x > 0` above the bisector
`y = x tan β₀`, where `tan β₀ = c / (1 + s)`. The vertical half-line is the nearest of the three. -/
def R₁ (s c : ℝ) : Set (ℝ × ℝ) := {z | 0 < z.1 ∧ c * z.1 < (1 + s) * z.2}

/-- The source's strip `R₂`: the points above the half-line `(c, -s)` and below the bisector, for which this half-line is
the nearest of the three. -/
def R₂ (s c : ℝ) : Set (ℝ × ℝ) := {z | 0 < s * z.1 + c * z.2 ∧ (1 + s) * z.2 < c * z.1}

/-- The source's strip `R₃`: the points of `x > 0` below the half-line `(c, -s)`, for which it is the nearest of the
three. -/
def R₃ (s c : ℝ) : Set (ℝ × ℝ) := {z | 0 < z.1 ∧ s * z.1 + c * z.2 < 0}

private lemma sq_add_sq_eq (hsc : s ^ 2 + c ^ 2 = 1) (x y : ℝ) :
    (s * x + c * y) ^ 2 + (c * x - s * y) ^ 2 = x ^ 2 + y ^ 2 := by
  linear_combination (x ^ 2 + y ^ 2) * hsc

/-- On `R₁` the projection to the line of the half-line `(c, -s)` is at least `x`. -/
private lemma le_add_of_mem_R₁ (hs : 0 < s) (hc : 0 < c) (hsc : s ^ 2 + c ^ 2 = 1) {x y : ℝ}
    (h : c * x < (1 + s) * y) : x < s * x + c * y := by
  have h1s : 0 < 1 + s := by linarith
  have e : (1 + s) * (s * x + c * y - x) = c * ((1 + s) * y - c * x) := by
    linear_combination x * hsc
  have hp : 0 < (1 + s) * (s * x + c * y - x) := by
    rw [e]
    exact mul_pos hc (by linarith)
  have := (pos_iff_pos_of_mul_pos hp).1 h1s
  linarith

/-- On the other side of the bisector, `x` is at least the projection. -/
private lemma add_lt_of_mem_R₂ (hs : 0 < s) (hc : 0 < c) (hsc : s ^ 2 + c ^ 2 = 1) {x y : ℝ}
    (h : (1 + s) * y < c * x) : s * x + c * y < x := by
  have h1s : 0 < 1 + s := by linarith
  have e : (1 + s) * (x - (s * x + c * y)) = c * (c * x - (1 + s) * y) := by
    linear_combination (-x) * hsc
  have hp : 0 < (1 + s) * (x - (s * x + c * y)) := by
    rw [e]
    exact mul_pos hc (by linarith)
  have := (pos_iff_pos_of_mul_pos hp).1 h1s
  linarith

theorem pos_of_mem_R₁ (hs : 0 < s) (hc : 0 < c) (hsc : s ^ 2 + c ^ 2 = 1) {z : ℝ × ℝ}
    (hz : z ∈ R₁ s c) : 0 < s * z.1 + c * z.2 :=
  hz.1.trans (le_add_of_mem_R₁ hs hc hsc hz.2)

theorem pos_of_mem_R₂ (hs : 0 < s) (hc : 0 < c) (hsc : s ^ 2 + c ^ 2 = 1) {z : ℝ × ℝ}
    (hz : z ∈ R₂ s c) : 0 < z.1 :=
  hz.1.trans (add_lt_of_mem_R₂ hs hc hsc hz.2)

/-- On `R₁`, the distance is that to the vertical half-line. -/
theorem halfLineDist_of_mem_R₁ (hs : 0 < s) (hc : 0 < c) (hsc : s ^ 2 + c ^ 2 = 1) {z : ℝ × ℝ}
    (hz : z ∈ R₁ s c) : halfLineDist s c z = z.1 ^ 2 := by
  obtain ⟨x, y⟩ := z
  obtain ⟨hx, h⟩ := hz
  simp only at hx h
  have hkey := le_add_of_mem_R₁ hs hc hsc h
  have hy : 0 < y := by
    by_contra hn
    have : (1 + s) * y ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by linarith) (not_lt.1 hn)
    nlinarith [mul_pos hc hx]
  have h₀ : sqDistHalfLine 0 1 x y = x ^ 2 := by
    unfold sqDistHalfLine
    rw [ite_eq_left (by linarith)]
    ring
  have h₁ : x ^ 2 ≤ sqDistHalfLine c (-s) x y := by
    unfold sqDistHalfLine
    split_ifs
    · rw [show (x * -s - y * c) ^ 2 = (s * x + c * y) ^ 2 by ring]
      exact pow_le_pow_left₀ hx.le hkey.le 2
    · nlinarith [sq_nonneg y]
  have h₂ : x ^ 2 ≤ sqDistHalfLine (-c) (-s) x y := by
    unfold sqDistHalfLine
    rw [ite_eq_right (by nlinarith [mul_pos hc hx, mul_pos hs hy])]
    nlinarith [sq_nonneg y]
  simp only [halfLineDist]
  rw [h₀]
  exact min_eq_left (le_min h₁ h₂)

/-- Where `x > 0`, the projection on the half-line `(c, -s)` is positive and, if `y ≥ 0`, its perpendicular is at most `x`,
the distance is that to this half-line. -/
private lemma halfLineDist_of_near (hs : 0 < s) (hc : 0 < c) (hsc : s ^ 2 + c ^ 2 = 1) {x y : ℝ}
    (hx : 0 < x) (hv : 0 ≤ c * x - s * y) (hy : 0 ≤ y → (s * x + c * y) ^ 2 ≤ x ^ 2) :
    halfLineDist s c (x, y) = (s * x + c * y) ^ 2 := by
  have hid := sq_add_sq_eq hsc x y
  have h₀ : (s * x + c * y) ^ 2 ≤ sqDistHalfLine 0 1 x y := by
    unfold sqDistHalfLine
    split_ifs with hw
    · rw [show (x * 1 - y * 0) ^ 2 = x ^ 2 by ring]
      exact hy (by linarith)
    · nlinarith [sq_nonneg (c * x - s * y)]
  have h₁ : sqDistHalfLine c (-s) x y = (s * x + c * y) ^ 2 := by
    unfold sqDistHalfLine
    rw [ite_eq_left (by linarith)]
    ring
  have h₂ : (s * x + c * y) ^ 2 ≤ sqDistHalfLine (-c) (-s) x y := by
    unfold sqDistHalfLine
    split_ifs with hw
    · have hy' : y < 0 := by
        by_contra hn
        have := mul_nonneg hs.le (not_lt.1 hn)
        nlinarith [mul_pos hc hx]
      nlinarith [mul_pos (mul_pos hs hc) (mul_pos hx (neg_pos.2 hy'))]
    · nlinarith [sq_nonneg (c * x - s * y)]
  simp only [halfLineDist]
  rw [h₁]
  exact le_antisymm (min_le_of_right_le (min_le_left _ _)) (le_min h₀ (le_min le_rfl h₂))

/-- On `R₂`, the distance is that to the half-line `(c, -s)`. -/
theorem halfLineDist_of_mem_R₂ (hs : 0 < s) (hc : 0 < c) (hsc : s ^ 2 + c ^ 2 = 1) {z : ℝ × ℝ}
    (hz : z ∈ R₂ s c) : halfLineDist s c z = (s * z.1 + c * z.2) ^ 2 := by
  obtain ⟨x, y⟩ := z
  have hx := pos_of_mem_R₂ hs hc hsc hz
  obtain ⟨hu, h⟩ := hz
  simp only at hx hu h
  have hlt := add_lt_of_mem_R₂ hs hc hsc h
  refine halfLineDist_of_near hs hc hsc hx ?_ fun _ => pow_le_pow_left₀ hu.le hlt.le 2
  by_cases hy : 0 ≤ y
  · nlinarith [mul_nonneg hs.le hy]
  · have := mul_pos hs (neg_pos.2 (not_le.1 hy))
    nlinarith [mul_pos hc hx]

/-- On `R₃`, the distance is that to the half-line `(c, -s)`. -/
theorem halfLineDist_of_mem_R₃ (hs : 0 < s) (hc : 0 < c) (hsc : s ^ 2 + c ^ 2 = 1) {z : ℝ × ℝ}
    (hz : z ∈ R₃ s c) : halfLineDist s c z = (s * z.1 + c * z.2) ^ 2 := by
  obtain ⟨x, y⟩ := z
  obtain ⟨hx, hu⟩ := hz
  simp only at hx hu
  have hsx := mul_pos hs hx
  have hy : y < 0 := by
    by_contra hn
    have := mul_nonneg hc.le (not_lt.1 hn)
    linarith
  refine halfLineDist_of_near hs hc hsc hx ?_ fun h => absurd h (not_le.2 hy)
  have := mul_pos hs (neg_pos.2 hy)
  nlinarith [mul_pos hc hx]

/-! ### The source's `G = 2 (G₁ + G₂ + G₃)` -/

/-- The half-plane `x > 0` is, up to the null lines through the origin, the union of the disjoint sets `R₁`, `R₂`, `R₃`. -/
theorem measure_halfPlane (hs : 0 < s) (hc : 0 < c) (hsc : s ^ 2 + c ^ 2 = 1) (μ t : ℝ) :
    normalSample μ ({z | halfLineDist s c z ≤ t} ∩ {z | 0 < z.1}) =
      normalSample μ ({z | halfLineDist s c z ≤ t} ∩ R₁ s c) +
        normalSample μ ({z | halfLineDist s c z ≤ t} ∩ R₂ s c) +
          normalSample μ ({z | halfLineDist s c z ≤ t} ∩ R₃ s c) := by
  have h1s : 0 < 1 + s := by linarith
  have h₁ := gaussianReal_prod_split (k₁ := s) (k₂ := c) (Or.inr hc.ne') 0 μ
    ({z | halfLineDist s c z ≤ t} ∩ {z | 0 < z.1})
  have h₂ := gaussianReal_prod_split (k₁ := -c) (k₂ := 1 + s) (Or.inr h1s.ne') 0 μ
    ({z | halfLineDist s c z ≤ t} ∩ {z | 0 < z.1} ∩ {z | 0 < s * z.1 + c * z.2})
  have e₁ : {z | halfLineDist s c z ≤ t} ∩ {z | 0 < z.1} ∩ {z | 0 < s * z.1 + c * z.2} ∩
      {z | 0 < -c * z.1 + (1 + s) * z.2} = {z | halfLineDist s c z ≤ t} ∩ R₁ s c := by
    ext z
    simp only [mem_inter_iff, mem_ofPred_eq, R₁]
    constructor
    · rintro ⟨⟨⟨hE, hx⟩, -⟩, hw⟩
      exact ⟨hE, hx, by linarith⟩
    · rintro ⟨hE, hx, hw⟩
      exact ⟨⟨⟨hE, hx⟩, pos_of_mem_R₁ hs hc hsc ⟨hx, hw⟩⟩, by linarith⟩
  have e₂ : {z | halfLineDist s c z ≤ t} ∩ {z | 0 < z.1} ∩ {z | 0 < s * z.1 + c * z.2} ∩
      {z | -c * z.1 + (1 + s) * z.2 < 0} = {z | halfLineDist s c z ≤ t} ∩ R₂ s c := by
    ext z
    simp only [mem_inter_iff, mem_ofPred_eq, R₂]
    constructor
    · rintro ⟨⟨⟨hE, -⟩, hu⟩, hw⟩
      exact ⟨hE, hu, by linarith⟩
    · rintro ⟨hE, hu, hw⟩
      exact ⟨⟨⟨hE, pos_of_mem_R₂ hs hc hsc ⟨hu, hw⟩⟩, hu⟩, by linarith⟩
  have e₃ : {z | halfLineDist s c z ≤ t} ∩ {z | 0 < z.1} ∩ {z | s * z.1 + c * z.2 < 0} =
      {z | halfLineDist s c z ≤ t} ∩ R₃ s c := by
    ext z
    simp only [mem_inter_iff, mem_ofPred_eq, R₃]
    constructor
    · rintro ⟨⟨hE, hx⟩, hu⟩
      exact ⟨hE, hx, hu⟩
    · rintro ⟨hE, hx, hu⟩
      exact ⟨⟨hE, hx⟩, hu⟩
  rw [e₁, e₂] at h₂
  rw [e₃, h₂] at h₁
  exact h₁

/-- The source's `G_X = 2 (G₁ + G₂ + G₃)`, for the squared distance, by the bilateral symmetry. -/
theorem measure_halfLineDist_le_eq_sum (hs : 0 < s) (hc : 0 < c) (hsc : s ^ 2 + c ^ 2 = 1) (μ t : ℝ) :
    normalSample μ {z | halfLineDist s c z ≤ t} =
      2 * (normalSample μ ({z | halfLineDist s c z ≤ t} ∩ R₁ s c) +
        normalSample μ ({z | halfLineDist s c z ≤ t} ∩ R₂ s c) +
          normalSample μ ({z | halfLineDist s c z ≤ t} ∩ R₃ s c)) := by
  have hE : MeasurableSet {z | halfLineDist s c z ≤ t} :=
    measurableSet_le (continuous_halfLineDist hsc).measurable measurable_const
  have hx : MeasurableSet {z : ℝ × ℝ | 0 < z.1} := measurableSet_lt measurable_const measurable_fst
  have h₁ := gaussianReal_prod_split (k₁ := 1) (k₂ := 0) (Or.inl one_ne_zero) 0 μ
    {z | halfLineDist s c z ≤ t}
  have e₁ : {z | halfLineDist s c z ≤ t} ∩ {z : ℝ × ℝ | 0 < 1 * z.1 + 0 * z.2} =
      {z | halfLineDist s c z ≤ t} ∩ {z | 0 < z.1} := by
    ext z
    simp
  have e₂ : {z | halfLineDist s c z ≤ t} ∩ {z : ℝ × ℝ | 1 * z.1 + 0 * z.2 < 0} =
      {z | (-z.1, z.2) ∈ {z | halfLineDist s c z ≤ t} ∩ {z : ℝ × ℝ | 0 < z.1}} := by
    ext z
    simp [halfLineDist_reflect_x]
  rw [e₁, e₂, measure_reflect_x_preimage μ (hE.inter hx), measure_halfPlane hs hc hsc] at h₁
  rw [h₁]
  ring

/-! ### The three integrals -/

section Polar

open Real

variable {α : ℝ}

/-- `tan β₀ = cos α₀ / (1 + sin α₀)`. -/
theorem tan_half_complement (hα : α ∈ Ioo 0 (π / 2)) :
    tan ((π / 2 - α) / 2) = cos α / (1 + sin α) := by
  set β := (π / 2 - α) / 2 with hβ
  have hb₀ : 0 < β := by
    have := hα.2
    rw [hβ]
    linarith
  have hb₁ : β < π / 4 := by
    have := hα.1
    rw [hβ]
    linarith
  have hcb : 0 < cos β := cos_pos_of_mem_Ioo ⟨by linarith [pi_pos], by linarith [pi_pos]⟩
  have h2 : 2 * β = π / 2 - α := by
    rw [hβ]
    ring
  have es : sin α = cos (2 * β) := by rw [h2, cos_pi_div_two_sub]
  have ec : cos α = sin (2 * β) := by rw [h2, sin_pi_div_two_sub]
  rw [tan_eq_sin_div_cos, es, ec, cos_two_mul, sin_two_mul,
    show 1 + (2 * cos β ^ 2 - 1) = 2 * cos β ^ 2 by ring]
  field_simp

/-- The angles `(β₀, π / 2)` of the source's integral for `G₁`, and of `G₂` after the reflection. -/
theorem sector₁ (hα : α ∈ Ioo 0 (π / 2)) :
    IsPolarSector 1 ((π / 2 - α) / 2) (π / 2) (cos α / (1 + sin α)) := by
  have h := IsPolarSector.right (a := (π / 2 - α) / 2)
    (by linarith [hα.2, pi_pos]) (by linarith [hα.1, pi_pos])
  rwa [tan_half_complement hα] at h

/-- The angles of `G₃` after the reflection, where the strip is `(-x, y)`, `y ≥ x tan α₀`. -/
theorem sector₃ (hα : α ∈ Ioo 0 (π / 2)) :
    IsPolarSector (-1) (π / 2) (π - α) (sin α / cos α) := by
  have h := IsPolarSector.left (b := π - α) (by linarith [hα.2]) (by linarith [hα.1])
  rwa [tan_pi_sub, neg_neg, tan_eq_sin_div_cos] at h

/-- The source's first display: for `x > 0`, the derivative of `G₁`, the double integral in polar coordinates over the
angles `(β₀, π / 2)`, is the density of `x` times the probability that `Z̄ ≥ x tan β₀`. -/
theorem hasDerivAt_G₁ (hα : α ∈ Ioo 0 (π / 2)) (μ : ℝ) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (polarStripIntegral 1 ((π / 2 - α) / 2) (π / 2) 0 μ)
      (stripDensity 0 μ (cos α / (1 + sin α)) x) x := by
  simpa using (sector₁ hα).hasDerivAt_polarStripIntegral_stripDensity 0 μ hx

/-- `G₁`: the probability of the part of `R₁` within distance `√t` of the vertical half-line. -/
theorem measure_inter_R₁ (hα : α ∈ Ioo 0 (π / 2)) (μ t : ℝ) :
    normalSample μ ({z | halfLineDist (sin α) (cos α) z ≤ t} ∩ R₁ (sin α) (cos α)) =
      ∫⁻ u in Ioc 0 √t, ENNReal.ofReal (stripDensity 0 μ (cos α / (1 + sin α)) u) := by
  have hs := Real.sin_pos_of_mem hα
  have hc := Real.cos_pos_of_mem hα
  have hsc := sin_sq_add_cos_sq α
  have h1s : 0 < 1 + sin α := by linarith
  have hset : {z | halfLineDist (sin α) (cos α) z ≤ t} ∩ R₁ (sin α) (cos α) =
      polarStrip 1 (cos α / (1 + sin α)) √t := by
    ext z
    simp only [mem_inter_iff, mem_ofPred_eq, polarStrip, one_mul]
    have key : cos α / (1 + sin α) * z.1 < z.2 ↔ cos α * z.1 < (1 + sin α) * z.2 := by
      rw [div_mul_eq_mul_div, div_lt_iff₀ h1s, mul_comm z.2]
    constructor
    · rintro ⟨hl, hz⟩
      rw [halfLineDist_of_mem_R₁ hs hc hsc hz] at hl
      exact ⟨hz.1, (Real.le_sqrt' hz.1).2 hl, key.2 hz.2⟩
    · rintro ⟨hx, hxt, hv⟩
      have hz : z ∈ R₁ (sin α) (cos α) := ⟨hx, key.1 hv⟩
      exact ⟨by rw [halfLineDist_of_mem_R₁ hs hc hsc hz]; exact (Real.le_sqrt' hx).1 hxt, hz⟩
  rw [hset]
  simpa using (sector₁ hα).measure_polarStrip_eq_lintegral_stripDensity 0 μ √t

/-- `G₂`: the probability of the part of `R₂` within distance `√t` of the half-line `(c, -s)`. The source reflects about the
bisector, which takes the mean to `(μ₀ cos α₀, -μ₀ sin α₀)` and `R₂` to the strip of `G₁`. -/
theorem measure_inter_R₂ (hα : α ∈ Ioo 0 (π / 2)) (μ t : ℝ) :
    normalSample μ ({z | halfLineDist (sin α) (cos α) z ≤ t} ∩ R₂ (sin α) (cos α)) =
      ∫⁻ u in Ioc 0 √t,
        ENNReal.ofReal (stripDensity (cos α * μ) (-sin α * μ) (cos α / (1 + sin α)) u) := by
  have hs := Real.sin_pos_of_mem hα
  have hc := Real.cos_pos_of_mem hα
  have hsc := sin_sq_add_cos_sq α
  have h1s : 0 < 1 + sin α := by linarith
  have hset : {z | halfLineDist (sin α) (cos α) z ≤ t} ∩ R₂ (sin α) (cos α) =
      {z | (sin α * z.1 + cos α * z.2, cos α * z.1 - sin α * z.2) ∈
        polarStrip 1 (cos α / (1 + sin α)) √t} := by
    ext z
    simp only [mem_inter_iff, mem_ofPred_eq, polarStrip, one_mul]
    have key : cos α / (1 + sin α) * (sin α * z.1 + cos α * z.2) < cos α * z.1 - sin α * z.2 ↔
        (1 + sin α) * z.2 < cos α * z.1 := by
      rw [div_mul_eq_mul_div, div_lt_iff₀ h1s]
      have : (cos α * z.1 - sin α * z.2) * (1 + sin α) -
          cos α * (sin α * z.1 + cos α * z.2) = cos α * z.1 - (1 + sin α) * z.2 := by
        linear_combination (-z.2) * hsc
      constructor <;> intro <;> linarith
    constructor
    · rintro ⟨hl, hz⟩
      rw [halfLineDist_of_mem_R₂ hs hc hsc hz] at hl
      exact ⟨hz.1, (Real.le_sqrt' hz.1).2 hl, key.2 hz.2⟩
    · rintro ⟨hu, hut, hv⟩
      have hz : z ∈ R₂ (sin α) (cos α) := ⟨hu, key.1 hv⟩
      exact ⟨by rw [halfLineDist_of_mem_R₂ hs hc hsc hz]; exact (Real.le_sqrt' hu).1 hut, hz⟩
  rw [hset, measure_reflect_preimage hsc 0 μ (measurableSet_polarStrip _ _ _),
    (sector₁ hα).measure_polarStrip_eq_lintegral_stripDensity]
  refine lintegral_congr fun u => ?_
  rw [one_mul, show sin α * 0 + cos α * μ = cos α * μ by ring,
    show cos α * 0 - sin α * μ = -sin α * μ by ring]

/-- `G₃`: the probability of the part of `R₃` within distance `√t` of the half-line `(c, -s)`. "The same reflection maps
`L₃` to the vertical half-line `(-x, y)` with `y ≥ x tan α₀`". -/
theorem measure_inter_R₃ (hα : α ∈ Ioo 0 (π / 2)) (μ t : ℝ) :
    normalSample μ ({z | halfLineDist (sin α) (cos α) z ≤ t} ∩ R₃ (sin α) (cos α)) =
      ∫⁻ u in Ioc 0 √t,
        ENNReal.ofReal (stripDensity (-(cos α * μ)) (-sin α * μ) (sin α / cos α) u) := by
  have hs := Real.sin_pos_of_mem hα
  have hc := Real.cos_pos_of_mem hα
  have hsc := sin_sq_add_cos_sq α
  have hset : {z | halfLineDist (sin α) (cos α) z ≤ t} ∩ R₃ (sin α) (cos α) =
      {z | (sin α * z.1 + cos α * z.2, cos α * z.1 - sin α * z.2) ∈
        polarStrip (-1) (sin α / cos α) √t} := by
    ext z
    have e : -1 * (sin α * z.1 + cos α * z.2) = -(sin α * z.1 + cos α * z.2) := by ring
    simp only [mem_inter_iff, mem_ofPred_eq, polarStrip, e]
    have key : sin α / cos α * -(sin α * z.1 + cos α * z.2) < cos α * z.1 - sin α * z.2 ↔
        0 < z.1 := by
      rw [div_mul_eq_mul_div, div_lt_iff₀ hc]
      have : (cos α * z.1 - sin α * z.2) * cos α -
          sin α * -(sin α * z.1 + cos α * z.2) = z.1 := by
        linear_combination z.1 * hsc
      constructor <;> intro <;> linarith
    constructor
    · rintro ⟨hl, hz⟩
      rw [halfLineDist_of_mem_R₃ hs hc hsc hz] at hl
      have hu : 0 < -(sin α * z.1 + cos α * z.2) := by linarith [hz.2]
      refine ⟨hu, ?_, key.2 hz.1⟩
      rw [Real.le_sqrt' hu, neg_sq]
      exact hl
    · rintro ⟨hu, hut, hv⟩
      have hz : z ∈ R₃ (sin α) (cos α) := ⟨key.1 hv, by linarith⟩
      refine ⟨?_, hz⟩
      rw [halfLineDist_of_mem_R₃ hs hc hsc hz, ← neg_sq]
      exact (Real.le_sqrt' hu).1 hut
  rw [hset, measure_reflect_preimage hsc 0 μ (measurableSet_polarStrip _ _ _),
    (sector₃ hα).measure_polarStrip_eq_lintegral_stripDensity]
  refine lintegral_congr fun u => ?_
  rw [show -1 * (sin α * 0 + cos α * μ) = -(cos α * μ) by ring,
    show cos α * 0 - sin α * μ = -sin α * μ by ring]

end Polar

/-- The source's density `g_X` of the distance: `2 (d/dx G₁ + d/dx G₂ + d/dx G₃)`. -/
def distDensity (s c μ u : ℝ) : ℝ :=
  2 * (stripDensity 0 μ (c / (1 + s)) u + stripDensity (c * μ) (-s * μ) (c / (1 + s)) u +
    stripDensity (-(c * μ)) (-s * μ) (s / c) u)

/-- The law of the distance: `P(Λ ≤ t)` is the integral of `g_X` over `(0, √t]`. -/
theorem measure_halfLineDist_le {α : ℝ} (hα : α ∈ Ioo 0 (Real.pi / 2)) (μ t : ℝ) :
    normalSample μ {z | halfLineDist (Real.sin α) (Real.cos α) z ≤ t} =
      ∫⁻ u in Ioc 0 √t, ENNReal.ofReal (distDensity (Real.sin α) (Real.cos α) μ u) := by
  rw [measure_halfLineDist_le_eq_sum (Real.sin_pos_of_mem hα) (Real.cos_pos_of_mem hα)
    (Real.sin_sq_add_cos_sq α), measure_inter_R₁ hα, measure_inter_R₂ hα, measure_inter_R₃ hα]
  set s := Real.sin α
  set c := Real.cos α
  have hm : ∀ p q k, Measurable fun u => ENNReal.ofReal (stripDensity p q k u) :=
    fun p q k => ENNReal.measurable_ofReal.comp (continuous_stripDensity p q k).measurable
  have hsplit : ∀ u, ENNReal.ofReal (distDensity s c μ u) =
      2 * (ENNReal.ofReal (stripDensity 0 μ (c / (1 + s)) u) +
        ENNReal.ofReal (stripDensity (c * μ) (-s * μ) (c / (1 + s)) u) +
        ENNReal.ofReal (stripDensity (-(c * μ)) (-s * μ) (s / c) u)) := by
    intro u
    simp only [distDensity]
    rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat,
      ENNReal.ofReal_add (add_nonneg (stripDensity_nonneg _ _ _ _) (stripDensity_nonneg _ _ _ _))
        (stripDensity_nonneg _ _ _ _),
      ENNReal.ofReal_add (stripDensity_nonneg _ _ _ _) (stripDensity_nonneg _ _ _ _)]
  simp_rw [hsplit]
  rw [lintegral_const_mul' _ _ (by norm_num), lintegral_add_right _ (hm _ _ _),
    lintegral_add_right _ (hm _ _ _)]

end T3Pdf

/-! ### The density -/

open T3Pdf

variable {φ : ℝ}

theorem alphaZero_mem (hφ : φ < 3 / 2) : alphaZero φ ∈ Ioo 0 (Real.pi / 2) := by
  have h : 0 < 3 * (3 - 2 * φ) := by linarith
  have : 0 < 1 / √(3 * (3 - 2 * φ)) := by positivity
  exact ⟨Real.arctan_pos.2 this, Real.arctan_lt_pi_div_two _⟩

/-- `t3Density` is nonnegative, since `erf ≤ 1`. -/
theorem t3Density_nonneg (φ n lam : ℝ) : 0 ≤ t3Density φ n lam := by
  simp only [t3Density]
  split_ifs with hl
  · have he := Real.erf_le_one
    refine mul_nonneg (by positivity) (add_nonneg (add_nonneg ?_ ?_) ?_) <;>
      refine mul_nonneg (Real.exp_pos _).le ?_
    · linarith [he (1 / √2 * (√lam * Real.tan (betaZero φ) - muZero φ n))]
    · linarith [he (1 / √2 * (√lam * Real.tan (betaZero φ) + muZero φ n * Real.sin (alphaZero φ)))]
    · linarith [he (1 / √2 * (√lam * Real.tan (alphaZero φ) + muZero φ n * Real.sin (alphaZero φ)))]
  · exact le_rfl

theorem measurable_t3Density (φ n : ℝ) : Measurable (t3Density φ n) := by
  have herf : Measurable Real.erf := Real.continuous_erf.measurable
  unfold t3Density
  refine Measurable.ite measurableSet_Ioi ?_ measurable_const
  fun_prop

/-- On `u > 0`, `2 u f(u²)` is the density `g_X` of the distance, where `f` is the printed density: the source's "change of
variable to convert to the squared Euclidean distance". -/
theorem two_mul_mul_t3Density (hφ : φ < 3 / 2) (n : ℝ) {u : ℝ} (hu : 0 < u) :
    2 * u * t3Density φ n (u ^ 2) =
      distDensity (Real.sin (alphaZero φ)) (Real.cos (alphaZero φ)) (muZero φ n) u := by
  have hu2 : 0 < u ^ 2 := by positivity
  have htan : Real.tan (betaZero φ) = Real.cos (alphaZero φ) / (1 + Real.sin (alphaZero φ)) :=
    tan_half_complement (alphaZero_mem hφ)
  have htan' : Real.tan (alphaZero φ) = Real.sin (alphaZero φ) / Real.cos (alphaZero φ) :=
    Real.tan_eq_sin_div_cos _
  simp only [t3Density, hu2, ↓reduceIte, Real.sqrt_sq hu.le, htan, htan']
  have hsqrt : √(2 * Real.pi * u ^ 2) = √(2 * Real.pi) * u := by
    rw [Real.sqrt_mul (by positivity), Real.sqrt_sq hu.le]
  rw [hsqrt]
  have hC : √(2 * Real.pi) ≠ 0 := (Real.sqrt_pos.2 (by positivity)).ne'
  have hfac : 2 * u * (1 / (2 * (√(2 * Real.pi) * u))) = (√(2 * Real.pi))⁻¹ := by
    field_simp
  rw [← mul_assoc, hfac]
  simp only [distDensity, stripDensity, gaussianPDFReal_one]
  ring_nf

/-- The law of the distance to the three half-lines has the printed density. -/
theorem map_halfLineDist (hφ : φ < 3 / 2) (n : ℝ) :
    (normalSample (muZero φ n)).map (halfLineDist (Real.sin (alphaZero φ)) (Real.cos (alphaZero φ))) =
      volume.withDensity (fun lam => ENNReal.ofReal (t3Density φ n lam)) := by
  have hc := continuous_halfLineDist (Real.sin_sq_add_cos_sq (alphaZero φ))
  have hfin : IsFiniteMeasure ((normalSample (muZero φ n)).map
      (halfLineDist (Real.sin (alphaZero φ)) (Real.cos (alphaZero φ)))) := inferInstance
  refine Measure.ext_of_Iic _ _ fun t => ?_
  have hIic : MeasurableSet (Iic t) := measurableSet_Iic
  rw [Measure.map_apply hc.measurable hIic, withDensity_apply _ hIic]
  refine (measure_halfLineDist_le (alphaZero_mem hφ) (muZero φ n) t).trans ?_
  have hind : ∫⁻ v in Iic t, ENNReal.ofReal (t3Density φ n v) =
      ∫⁻ v in Ioc 0 t, ENNReal.ofReal (t3Density φ n v) := by
    rw [← lintegral_indicator (measurableSet_Iic : MeasurableSet (Iic t)),
      ← lintegral_indicator (measurableSet_Ioc : MeasurableSet (Ioc 0 t))]
    refine lintegral_congr fun v => ?_
    by_cases hv : 0 < v
    · by_cases hvt : v ≤ t
      · rw [indicator_of_mem (show v ∈ Iic t from hvt),
          indicator_of_mem (show v ∈ Ioc 0 t from ⟨hv, hvt⟩)]
      · rw [indicator_of_notMem (show v ∉ Iic t from hvt),
          indicator_of_notMem (show v ∉ Ioc 0 t from fun h => hvt h.2)]
    · have h0 : ENNReal.ofReal (t3Density φ n v) = 0 := by simp [t3Density, hv]
      rw [indicator_of_notMem (show v ∉ Ioc 0 t from fun h => hv h.1)]
      by_cases hvt : v ≤ t
      · rw [indicator_of_mem (show v ∈ Iic t from hvt), h0]
      · rw [indicator_of_notMem (show v ∉ Iic t from hvt)]
  rw [hind, lintegral_Ioc_eq_lintegral_sq t fun v => ENNReal.ofReal (t3Density φ n v)]
  refine setLIntegral_congr_fun measurableSet_Ioc fun u hu => ?_
  rw [← ENNReal.ofReal_mul (mul_pos two_pos hu.1).le, two_mul_mul_t3Density hφ n hu.1]

/-- **Proposition 4.2** (`ext:t3_density`) of Mitchell, Allman, Rhodes 2019. The random variable of Proposition 4.1,
`t3Var φ (Z, Z̄)` for independent `Z ~ N(0, 1)` and `Z̄ ~ N(μ₀, 1)`, has on `λ > 0` the density of Equation `eq:T3pdf`. The value
`0` has mass zero, so this determines the law. The source states it for `φ₀ ∈ (0, 1]`; it holds for all `φ₀ < 3 / 2`. See the
module docstring for the proof, which is the source's. -/
theorem t3Var_density (hφ : φ < 3 / 2) (n : ℝ) :
    (∀ lam, 0 ≤ t3Density φ n lam) ∧
      ((gaussianReal 0 1).prod (gaussianReal (muZero φ n) 1)).map (t3Var φ) =
        volume.withDensity (fun lam => ENNReal.ofReal (t3Density φ n lam)) :=
  ⟨t3Density_nonneg φ n, by
    rw [← map_halfLineDist hφ n]
    exact Measure.map_congr (t3Var_ae_eq_halfLineDist hφ _)⟩

/-- The tail of the T3 test distribution is the integral of the density (`ext:t3_density`), as the source computes its p-values: "by numerical
integration from the observed value of the statistic to infinity". -/
theorem t3Tail_eq_integral (hφ : φ < 3 / 2) (n t : ℝ) :
    t3Tail φ n t = ∫ v in Ioi t, t3Density φ n v := by
  have hm := measurable_t3Var φ
  have hset : {z : ℝ × ℝ | t < t3Var φ z} = t3Var φ ⁻¹' Ioi t := rfl
  rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ (t3Density_nonneg φ n))
      (measurable_t3Density φ n).aestronglyMeasurable,
    ← withDensity_apply _ measurableSet_Ioi, ← (t3Var_density hφ n).2,
    Measure.map_apply hm measurableSet_Ioi, t3Tail, measureReal_def, hset]

/-- The distribution function of the T3 test distribution is the integral of the density. -/
theorem one_sub_t3Tail_eq_integral (hφ : φ < 3 / 2) (n t : ℝ) :
    1 - t3Tail φ n t = ∫ v in Iic t, t3Density φ n v := by
  have hm := measurable_t3Var φ
  have hset : {z : ℝ × ℝ | t < t3Var φ z} = (t3Var φ ⁻¹' Iic t)ᶜ := by
    ext z
    simp
  rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ (t3Density_nonneg φ n))
      (measurable_t3Density φ n).aestronglyMeasurable,
    ← withDensity_apply _ measurableSet_Iic, ← (t3Var_density hφ n).2,
    Measure.map_apply hm measurableSet_Iic, t3Tail, hset,
    probReal_compl_eq_one_sub (hm measurableSet_Iic), measureReal_def]
  ring

/-- The level sets of the distance to the three half-lines are null: its law has a density. -/
theorem measure_halfLineDist_eq_null (hφ : φ < 3 / 2) (n t : ℝ) :
    normalSample (muZero φ n)
      {z | halfLineDist (Real.sin (alphaZero φ)) (Real.cos (alphaZero φ)) z = t} = 0 := by
  have hc := continuous_halfLineDist (Real.sin_sq_add_cos_sq (alphaZero φ))
  have hset : {z | halfLineDist (Real.sin (alphaZero φ)) (Real.cos (alphaZero φ)) z = t} =
      halfLineDist (Real.sin (alphaZero φ)) (Real.cos (alphaZero φ)) ⁻¹' {t} := rfl
  rw [hset, ← Measure.map_apply hc.measurable (measurableSet_singleton t), map_halfLineDist hφ n]
  exact withDensity_absolutelyContinuous _ _ (by simp)

/-! ### The distribution function -/

/-- The density is integrable: its integral is one. -/
theorem integrable_t3Density (hφ : φ < 3 / 2) (n : ℝ) : Integrable (t3Density φ n) := by
  refine ⟨(measurable_t3Density φ n).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (ae_of_all _ (t3Density_nonneg φ n))]
  have h := congrArg (fun ν : Measure ℝ => ν univ) (t3Var_density hφ n).2
  simp only [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ] at h
  rw [← h, Measure.map_apply (measurable_t3Var φ) MeasurableSet.univ, preimage_univ, measure_univ]
  exact ENNReal.one_lt_top

/-- The density vanishes off `λ > 0`, so that the distribution function is a primitive of it from `0`. -/
theorem one_sub_t3Tail_eq_intervalIntegral (hφ : φ < 3 / 2) (n t : ℝ) :
    1 - t3Tail φ n t = ∫ v in (0 : ℝ)..t, t3Density φ n v := by
  have hi := integrable_t3Density hφ n
  have hzero : ∫ v in Iic (0 : ℝ), t3Density φ n v = 0 :=
    setIntegral_eq_zero_of_forall_eq_zero fun v hv => by
      simp [t3Density, not_lt.2 (show v ≤ 0 from hv)]
  have h₂ := intervalIntegral.integral_Iic_sub_Iic (a := 0) (b := t) hi.integrableOn hi.integrableOn
  rw [one_sub_t3Tail_eq_integral hφ n t]
  linarith

/-- The tail of the T3 test distribution is continuous: the law has no atoms. -/
theorem continuous_t3Tail (hφ : φ < 3 / 2) (n : ℝ) : Continuous (t3Tail φ n) := by
  have hi := integrable_t3Density hφ n
  have hc : Continuous fun t => 1 - ∫ v in (0 : ℝ)..t, t3Density φ n v :=
    continuous_const.sub (intervalIntegral.continuous_primitive (fun _ _ => hi.intervalIntegrable) 0)
  exact hc.congr fun t => by
    rw [← one_sub_t3Tail_eq_intervalIntegral hφ n t]
    ring

/-- Every level in `(0, 1]` is a value of the tail of the T3 test distribution, for `φ ≤ 1`. -/
theorem exists_t3Tail_eq (h1 : φ ≤ 1) (n : ℝ) {x : ℝ} (hx : 0 < x) (hx1 : x ≤ 1) :
    ∃ t : ℝ, 0 ≤ t ∧ t3Tail φ n t = x := by
  have hφ : φ < 3 / 2 := by linarith
  have hG := continuous_t3Tail hφ n
  have h0 : t3Tail φ n 0 = 1 := by
    have := one_sub_t3Tail_eq_intervalIntegral hφ n 0
    rw [intervalIntegral.integral_same] at this
    linarith
  have hlim : Tendsto (fun t : ℝ => Real.exp (-t / 2)) atTop (𝓝 0) := by
    refine Real.tendsto_exp_atBot.comp ?_
    have : Tendsto (fun t : ℝ => t / 2) atTop atTop := tendsto_id.atTop_div_const (by norm_num)
    exact (tendsto_neg_atTop_atBot.comp this).congr fun t => by
      simp only [Function.comp]
      ring
  obtain ⟨T, hT, hT0⟩ := ((hlim.eventually (gt_mem_nhds hx)).and (eventually_ge_atTop 0)).exists
  have hle : t3Tail φ n T ≤ Real.exp (-T / 2) :=
    t3Tail_le_chiSqTwoTail (Trinomial.muZero_nonneg_of_le_one h1) hT0
  have hmem : x ∈ Icc (t3Tail φ n T) (t3Tail φ n 0) := ⟨(hle.trans_lt hT).le, by rwa [h0]⟩
  obtain ⟨t, ht, hty⟩ := intermediate_value_Icc' hT0 hG.continuousOn hmem
  exact ⟨t, ht.1, hty⟩

/-! ### What the source says of the density -/

theorem betaZero_one : betaZero 1 = Real.pi / 6 := by
  rw [betaZero, alphaZero_one]
  ring

/-- **The density at the singularity** (`ext:t3_density_singularity`): "At the singularity, the asymptotic density is given exactly by Equation `eq:T3pdf`,
since there is no dependence on `n`" (Mitchell, Allman, Rhodes 2019, after Proposition 4.2). There `α₀ = β₀ = π / 6` and
`μ₀ = 0`, and the three terms of the printed density are equal. -/
theorem t3Density_one (n lam : ℝ) :
    t3Density 1 n lam = if 0 < lam then
      3 / (2 * √(2 * Real.pi * lam)) * (Real.exp (-(lam / 2)) * (1 - Real.erf √(lam / 6))) else 0 := by
  unfold t3Density
  split_ifs with hl
  · rw [betaZero_one, alphaZero_one, muZero_one, Real.tan_pi_div_six]
    simp only [zero_mul, sub_zero, add_zero]
    have hs : √lam ^ 2 = lam := Real.sq_sqrt hl.le
    have hexp : -(1 / 2) * √lam ^ 2 = -(lam / 2) := by
      rw [hs]
      ring
    have herf : 1 / √2 * (√lam * (1 / √3)) = √(lam / 6) := by
      rw [Real.sqrt_div hl.le, show (6 : ℝ) = 2 * 3 by norm_num, Real.sqrt_mul (by norm_num)]
      field_simp
    rw [hexp, herf]
    ring
  · rfl

/-- `μ₀` runs off as `n → ∞`, off the singularity. -/
theorem tendsto_muZero_atTop (hφ : 0 < φ ∧ φ < 1) : Tendsto (fun n : ℝ => muZero φ n) atTop atTop := by
  have h₁ : 0 < 1 - φ := by linarith [hφ.2]
  have h₂ : 0 < √(φ * (3 - 2 * φ)) := Real.sqrt_pos.2 (mul_pos hφ.1 (by linarith [hφ.2]))
  have h₃ : Tendsto (fun n : ℝ => √(2 * n)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp (tendsto_id.const_mul_atTop two_pos)
  exact (h₃.atTop_mul_const h₁).atTop_div_const h₂

/-- A term of the density with an exponent running off vanishes in the limit. -/
private lemma tendsto_exp_mul_erf_term {f g : ℝ → ℝ} (hf : Tendsto f atTop atTop) :
    Tendsto (fun n => Real.exp (-(1 / 2) * f n ^ 2) * (1 - Real.erf (g n))) atTop (𝓝 0) := by
  have hexp : Tendsto (fun n => Real.exp (-(1 / 2) * f n ^ 2)) atTop (𝓝 0) := by
    refine Real.tendsto_exp_atBot.comp ?_
    have h₂ : Tendsto (fun n => f n ^ 2) atTop atTop :=
      (tendsto_pow_atTop two_ne_zero).comp hf
    exact h₂.const_mul_atTop_of_neg (by norm_num)
  have h2 := hexp.const_mul 2
  rw [mul_zero] at h2
  refine squeeze_zero (fun n => ?_) (fun n => ?_) h2
  · exact mul_nonneg (Real.exp_pos _).le (by linarith [Real.erf_le_one (g n)])
  · have := Real.exp_pos (-(1 / 2) * f n ^ 2)
    nlinarith [Real.neg_one_le_erf (g n)]

/-- **The density tends to that of `χ²₁`** (`ext:t3_density_chisq`): "for `φ₀ ∈ (0, 1)` as `n → ∞` Equation `eq:T3pdf` gives the probability density
function of `χ²₁`" (Mitchell, Allman, Rhodes 2019, after Proposition 4.2), pointwise on `λ > 0`. The limit is
`exp (-λ / 2) / √(2 π λ)`. -/
theorem tendsto_t3Density_atTop (hφ : 0 < φ ∧ φ < 1) {lam : ℝ} (hl : 0 < lam) :
    Tendsto (fun n : ℝ => t3Density φ n lam) atTop
      (𝓝 (Real.exp (-(lam / 2)) / √(2 * Real.pi * lam))) := by
  have hμ := tendsto_muZero_atTop hφ
  have hc : 0 < Real.cos (alphaZero φ) := cos_alphaZero_pos φ
  have hμc : Tendsto (fun n : ℝ => muZero φ n * Real.cos (alphaZero φ)) atTop atTop :=
    hμ.atTop_mul_const hc
  have hd : 0 < √(2 * Real.pi * lam) := Real.sqrt_pos.2 (by positivity)
  have h₁ : Tendsto (fun n : ℝ => Real.exp (-(lam / 2)) *
      (1 - Real.erf (1 / √2 * (√lam * Real.tan (betaZero φ) - muZero φ n)))) atTop
      (𝓝 (Real.exp (-(lam / 2)) * (1 - -1))) := by
    refine Tendsto.const_mul _ (Tendsto.const_sub _ (Real.tendsto_erf_atBot.comp ?_))
    have : Tendsto (fun n : ℝ => √lam * Real.tan (betaZero φ) - muZero φ n) atTop atBot :=
      tendsto_atBot_add_const_left _ _ (tendsto_neg_atTop_atBot.comp hμ)
    exact this.const_mul_atBot (by positivity)
  have h₂ := tendsto_exp_mul_erf_term (f := fun n : ℝ => muZero φ n * Real.cos (alphaZero φ) - √lam)
    (g := fun n : ℝ => 1 / √2 * (√lam * Real.tan (betaZero φ) + muZero φ n * Real.sin (alphaZero φ)))
    (tendsto_atTop_add_const_right _ _ hμc)
  have h₃ := tendsto_exp_mul_erf_term (f := fun n : ℝ => muZero φ n * Real.cos (alphaZero φ) + √lam)
    (g := fun n : ℝ => 1 / √2 * (√lam * Real.tan (alphaZero φ) + muZero φ n * Real.sin (alphaZero φ)))
    (tendsto_atTop_add_const_right _ _ hμc)
  have hsum := ((h₁.add h₂).add h₃).const_mul (1 / (2 * √(2 * Real.pi * lam)))
  have hval : 1 / (2 * √(2 * Real.pi * lam)) * (Real.exp (-(lam / 2)) * (1 - -1) + 0 + 0) =
      Real.exp (-(lam / 2)) / √(2 * Real.pi * lam) := by
    field_simp
    ring
  rw [hval] at hsum
  refine hsum.congr fun n => ?_
  simp only [t3Density, hl, ↓reduceIte]
  rw [show (muZero φ n * Real.cos (alphaZero φ) - √lam) ^ 2 =
      (√lam - muZero φ n * Real.cos (alphaZero φ)) ^ 2 by ring,
    show (muZero φ n * Real.cos (alphaZero φ) + √lam) ^ 2 =
      (√lam + muZero φ n * Real.cos (alphaZero φ)) ^ 2 by ring]

/-- **The density is continuous in `φ₀`** (`ext:t3_density_continuous`), for a fixed sample size and `λ`, across the singularity: "Unlike the asymptotic
densities, which have a jump discontinuity at the singularity, the density of Equation `eq:T3pdf` is a continuous function of
`φ₀`" (Mitchell, Allman, Rhodes 2019, after Proposition 4.2). The source writes `φ₀ ∈ [0, 1)`. Its point is the singularity
`φ₀ = 1`, and `μ₀` has no value at `φ₀ = 0`, so this is stated on `(0, 3 / 2)`, which contains `(0, 1]`. -/
theorem continuousOn_t3Density (n lam : ℝ) :
    ContinuousOn (fun φ => t3Density φ n lam) (Ioo 0 (3 / 2)) := by
  by_cases hl : 0 < lam
  · have hA : ContinuousOn alphaZero (Ioo 0 (3 / 2)) := by
      unfold alphaZero
      refine Real.continuous_arctan.comp_continuousOn (ContinuousOn.div continuousOn_const
        (by fun_prop) fun x hx => (Real.sqrt_pos.2 ?_).ne')
      linarith [hx.2]
    have hM : ContinuousOn (fun φ => muZero φ n) (Ioo 0 (3 / 2)) := by
      unfold muZero
      refine ContinuousOn.div (by fun_prop) (by fun_prop) fun x hx => (Real.sqrt_pos.2 ?_).ne'
      exact mul_pos hx.1 (by linarith [hx.2])
    have hS : ContinuousOn (fun φ => Real.sin (alphaZero φ)) (Ioo 0 (3 / 2)) :=
      Real.continuous_sin.comp_continuousOn hA
    have hC : ContinuousOn (fun φ => Real.cos (alphaZero φ)) (Ioo 0 (3 / 2)) :=
      Real.continuous_cos.comp_continuousOn hA
    have hTa : ContinuousOn (fun φ => Real.tan (alphaZero φ)) (Ioo 0 (3 / 2)) :=
      ContinuousOn.congr (f := fun φ => Real.sin (alphaZero φ) / Real.cos (alphaZero φ))
        (hS.div hC fun x _ => (cos_alphaZero_pos x).ne')
        fun x _ => Real.tan_eq_sin_div_cos _
    have hTb : ContinuousOn (fun φ => Real.tan (betaZero φ)) (Ioo 0 (3 / 2)) :=
      ContinuousOn.congr (f := fun φ => Real.cos (alphaZero φ) / (1 + Real.sin (alphaZero φ)))
        (hC.div (continuousOn_const.add hS) fun x hx =>
          (by linarith [sin_alphaZero_pos (φ := x) hx.2] : 0 < 1 + Real.sin (alphaZero x)).ne')
        fun x hx => tan_half_complement (alphaZero_mem hx.2)
    have herf := Real.continuous_erf
    simp only [t3Density, hl, ↓reduceIte]
    refine continuousOn_const.mul (((continuousOn_const.mul ?_).add
      ((Real.continuous_exp.comp_continuousOn (continuousOn_const.mul
        ((continuousOn_const.sub (hM.mul hC)).pow 2))).mul ?_)).add
      ((Real.continuous_exp.comp_continuousOn (continuousOn_const.mul
        ((continuousOn_const.add (hM.mul hC)).pow 2))).mul ?_))
    · exact continuousOn_const.sub (herf.comp_continuousOn
        (continuousOn_const.mul ((continuousOn_const.mul hTb).sub hM)))
    · exact continuousOn_const.sub (herf.comp_continuousOn
        (continuousOn_const.mul ((continuousOn_const.mul hTb).add (hM.mul hS))))
    · exact continuousOn_const.sub (herf.comp_continuousOn
        (continuousOn_const.mul ((continuousOn_const.mul hTa).add (hM.mul hS))))
  · simp only [t3Density, hl, ↓reduceIte]
    exact continuousOn_const

end QuartetTests

end Phylogenetics

namespace External.MitchellAllmanRhodes2019

/-- **Proposition 4.2** (`ext:t3_density`) of the source, under the name of its number: `QuartetTests.t3Var_density`. -/
theorem proposition4_2 {φ : ℝ} (hφ : φ < 3 / 2) (n : ℝ) :
    (∀ lam, 0 ≤ Phylogenetics.t3Density φ n lam) ∧
      ((gaussianReal 0 1).prod (gaussianReal (Phylogenetics.muZero φ n) 1)).map (Phylogenetics.t3Var φ) =
        volume.withDensity (fun lam => ENNReal.ofReal (Phylogenetics.t3Density φ n lam)) :=
  Phylogenetics.QuartetTests.t3Var_density hφ n

end External.MitchellAllmanRhodes2019
