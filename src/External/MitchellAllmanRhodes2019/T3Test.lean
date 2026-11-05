module

public import Basic.Defs
public import Basic.Testing.Limits
public import Basic.Testing.MissingTaxa
public import Mathlib.Basic.Real.Sign

/-!
# The T3 test

The hypothesis test of Mitchell, Allman, Rhodes 2019 for model T3 ("Three species related by any of the
three possible species trees"), which is TINNiK's "T3" option and TOB-QMC's default: its null hypothesis is
the union of the three half-lines `(p, q, q)`, `q ≤ 1/3`, of the concordance factor simplex.

* The statistic `t3Stat`, the likelihood ratio statistic of this union: the least of the T1 statistics
  of the three topologies.
* The test distribution `t3Tail`, the tail of the law of Proposition `prop:T3approx` of that paper, and
  the p-value `t3PValue`, at the maximum likelihood point.
* Under the null, including at its singularity `(1/3, 1/3, 1/3)`: the p-value does not collapse,
  `QuartetTests.t3Test_nonCollapse`, and off the singularity it is asymptotically uniform,
  `QuartetTests.t3PValue_asymptoticallyUniform`, with the true topology the maximum likelihood one,
  `QuartetTests.t3Test_null`.
* Off the null, for a non-cut concordance factor and for an anomalous cut one: the statistic grows linearly
  and the p-value is exponentially small, `QuartetTests.t3Test_alternative`.
* The nesting of ECToBlob §10: the T1 null is inside the T3 null, `QuartetTests.isT3Null_of_isT1Null`, and
  `t3Stat ≤ t1Stat`, `QuartetTests.t3Stat_le_t1Stat`. The two p-values use different reference laws, and at the
  maximum likelihood topology the comparison of p-values goes the other way: `QuartetTests.t3PValue_le_t1PValue`,
  `QuartetTests.exists_t3PValue_lt_t1PValue`. What holds in the direction of the source is in
  `QuartetTests.t1PValue_le_t1Tail_t3Stat` and `QuartetTests.t1_rejects_where_t3_cannot`.

Proposition `prop:T3approx` is an approximation, with no error stated. What is formalized of it here: the law at a point off the
singularity tends to `χ²₁`, `QuartetTests.abs_t3Tail_sub_chiSqOneTail_lt`; the variable is the squared distance to the three
half-lines, `QuartetTests.t3Var_eq_min_sqDistHalfLine`. Here the statistic at the singularity is only tight, which is all that
non-collapse needs. Its limit law is in `T3Limit.lean`, and the density of the source's next proposition in `T3Density.lean`.
-/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped Classical

namespace Phylogenetics

variable {X : Type*} [Fintype X] [DecidableEq X]

/-- The concordance factor `p` on the taxa `q` is on **model T3** (Mitchell, Allman, Rhodes 2019, Example
`ex:3tree`, and TINNiK Fig. 2 (R)): the union of the three half-lines of the T1 nulls of the topologies on `q`.
This is the test's null, as in Mitchell, Allman, Rhodes 2019, where `φ₀ ∈ (0, 1]` and the centroid is its singularity. TINNiK's
caption, "those cut CFs with smallest entry occurring exactly twice", leaves out the centroid, and TINNiK calls a treelike set
with centroid CF anomalous; `NoAnomalousQuartets` follows that. -/
def IsT3Null (p : QuartetTree X → ℝ) (q : Finset X) : Prop := ∃ s ∈ treesOn q, IsT1Null p s

/-- The likelihood ratio statistic of model T3 on the taxa `q`. The null is the union of the three T1 nulls,
so its maximal likelihood is the largest of theirs, and the statistic is the least of the three T1
statistics. Parallel to `cutStat`, which is the least of the statistics of the three lines. -/
def t3Stat (c : QuartetTree X → ℝ) (q : Finset X) : ℝ := ⨅ s : {s // s ∈ treesOn q}, t1Stat c s.val

/-- The variable of Mitchell, Allman, Rhodes 2019, Proposition `prop:T3approx`, at `(Z, Z̄)`:
`min (Z² + ½ (1 - sgn Z̄) Z̄², sin² α₀ (Z + cot α₀ sgn(Z) Z̄)²)`. As in `t1Tail`, the term `½ (1 - sgn Z̄) Z̄²` is
written as `Z̄²` when `Z̄ < 0` and `0` otherwise. The value is the squared distance from `(Z, Z̄)` to three
half-lines from the origin, the first of them vertical, and `α₀` is the angle `alphaZero φ` of the others to
the horizontal axis. -/
def t3Var (φ : ℝ) (z : ℝ × ℝ) : ℝ :=
  min (z.1 ^ 2 + if z.2 < 0 then z.2 ^ 2 else 0)
    (Real.sin (alphaZero φ) ^ 2 * (z.1 + Real.cot (alphaZero φ) * Real.sign z.1 * z.2) ^ 2)

/-- The upper tail at `t` of the T3 test distribution: the law of `t3Var φ (Z, Z̄)`, for independent
`Z ~ N(0,1)` and `Z̄ ~ N(μ₀,1)`, with `μ₀ = muZero φ n`. This is Proposition `prop:T3approx` of Mitchell, Allman,
Rhodes 2019 for sample size `n` and parameter `φ`. Parallel to `cutTail`. -/
def t3Tail (φ n t : ℝ) : ℝ :=
  ((gaussianReal 0 1).prod (gaussianReal (muZero φ n) 1)).real {z | t < t3Var φ z}

/-- The p-value of the T3 test, with the true parameter replaced by the maximum likelihood estimate
(Mitchell, Allman, Rhodes 2019, after Theorem `maintheorem`: "In practice, `θ₀` ... are estimated using the MLE"):
the quartet tree `s` is the fitted topology, a maximum likelihood topology on model T3, and `φ` is estimated on its
half-line by `t1Phi`. The statistic is `t3Stat`. As with `t1PValue`, the separate procedures for small counts are not
modelled: they do not arise in the limit when the concordance factors are positive. Parallel to `cutPValue`. -/
def t3PValue (c : QuartetTree X → ℝ) (s : QuartetTree X) : ℝ :=
  t3Tail (t1Phi c s) (c s + ∑ r ∈ s.alternatives, c r) (t3Stat c s.taxa)

namespace QuartetTests

open Trinomial

/-! ### The angle -/

variable {φ : ℝ}

private lemma sin_sq_arctan_aux {w : ℝ} (hw : 0 < w) :
    Real.sin (Real.arctan (1 / √w)) ^ 2 = 1 / (w + 1) := by
  have hu : (1 / √w) ^ 2 = 1 / w := by rw [div_pow, one_pow, Real.sq_sqrt hw.le]
  rw [Real.sin_arctan, div_pow, Real.sq_sqrt (by positivity), hu]
  field_simp

private lemma cos_sq_arctan_aux {w : ℝ} (hw : 0 < w) :
    Real.cos (Real.arctan (1 / √w)) ^ 2 = w / (w + 1) := by
  have hu : (1 / √w) ^ 2 = 1 / w := by rw [div_pow, one_pow, Real.sq_sqrt hw.le]
  rw [Real.cos_arctan, div_pow, Real.sq_sqrt (by positivity), hu]
  field_simp

/-- The squared sine of `α₀`. -/
theorem sin_sq_alphaZero (hφ : φ < 3 / 2) :
    Real.sin (alphaZero φ) ^ 2 = 1 / (3 * (3 - 2 * φ) + 1) :=
  sin_sq_arctan_aux (by linarith)

/-- The squared cosine of `α₀`. -/
theorem cos_sq_alphaZero (hφ : φ < 3 / 2) :
    Real.cos (alphaZero φ) ^ 2 = 3 * (3 - 2 * φ) / (3 * (3 - 2 * φ) + 1) :=
  cos_sq_arctan_aux (by linarith)

theorem sin_alphaZero_pos (hφ : φ < 3 / 2) : 0 < Real.sin (alphaZero φ) := by
  rw [alphaZero, Real.sin_arctan_pos]
  have hw : 0 < 3 * (3 - 2 * φ) := by linarith
  positivity

/-- `α₀` is at least `arctan (1/3)`, as Mitchell, Allman, Rhodes 2019 state in Appendix `app1`. In this form:
`sin² α₀ ≥ 1/10`. -/
theorem one_tenth_le_sin_sq_alphaZero (h0 : 0 ≤ φ) (h1 : φ ≤ 1) :
    1 / 10 ≤ Real.sin (alphaZero φ) ^ 2 := by
  rw [sin_sq_alphaZero (by linarith)]
  apply one_div_le_one_div_of_le (by nlinarith)
  linarith

/-- `α₀` is at most `π/6`, as Mitchell, Allman, Rhodes 2019 state in Appendix `app1`. In this form:
`cos α₀ ≥ 1/2`. -/
theorem one_half_le_cos_alphaZero (h1 : φ ≤ 1) : 1 / 2 ≤ Real.cos (alphaZero φ) := by
  have hc := cos_sq_alphaZero (φ := φ) (by linarith)
  have hc0 := cos_alphaZero_pos φ
  have hw : 3 ≤ 3 * (3 - 2 * φ) := by linarith
  have h34 : 1 / 4 ≤ Real.cos (alphaZero φ) ^ 2 := by
    rw [hc, le_div_iff₀ (by linarith)]
    linarith
  nlinarith

/-- The second argument of the T3 variable: `sin² α₀ (Z + cot α₀ sgn(Z) Z̄)²` is
`(sin α₀ Z + cos α₀ sgn(Z) Z̄)²`, the squared distance to the line of the half-line on the side of `Z`, as in
Equation `eq:sqdist2` of Mitchell, Allman, Rhodes 2019. -/
theorem sin_sq_mul_cot (hφ : φ < 3 / 2) (x y : ℝ) :
    Real.sin (alphaZero φ) ^ 2 * (x + Real.cot (alphaZero φ) * Real.sign x * y) ^ 2 =
      (Real.sin (alphaZero φ) * x + Real.cos (alphaZero φ) * Real.sign x * y) ^ 2 := by
  have hs := (sin_alphaZero_pos hφ).ne'
  rw [Real.cot_eq_cos_div_sin, ← mul_pow]
  congr 1
  field_simp

/-- The T3 variable is measurable, so that `t3Tail` is the tail of a random variable. -/
theorem measurable_t3Var (φ : ℝ) : Measurable (t3Var φ) := by
  have hsign : Measurable Real.sign := by
    have : Real.sign = fun r : ℝ => if r < 0 then -1 else if 0 < r then 1 else 0 := rfl
    rw [this]
    exact Measurable.ite measurableSet_Iio measurable_const
      (Measurable.ite measurableSet_Ioi measurable_const measurable_const)
  unfold t3Var
  refine Measurable.min ?_ ?_
  · exact (measurable_fst.pow_const 2).add
      (Measurable.ite (measurableSet_lt measurable_snd measurable_const)
        (measurable_snd.pow_const 2) measurable_const)
  · exact measurable_const.mul ((measurable_fst.add
      ((measurable_const.mul (hsign.comp measurable_fst)).mul measurable_snd)).pow_const 2)

/-! ### The T3 variable as a squared distance -/

/-- The squared distance from `(x, y)` to the half-line from the origin in the unit direction `(u, v)`. -/
def sqDistHalfLine (u v x y : ℝ) : ℝ :=
  if 0 ≤ x * u + y * v then (x * v - y * u) ^ 2 else x ^ 2 + y ^ 2

/-- **The T3 variable is the squared distance to the three half-lines**: "Equation `eq:T3dis` is the minimum squared Euclidean
distance between the sample point and the transformed null parameter space" (Mitchell, Allman, Rhodes 2019, after Proposition
`prop:T3approx`), where `Z ≠ 0`, which has probability one. The half-lines from the origin are vertical, and at the angle `α₀` below the
horizontal axis on either side. The source leaves one step to the reader, in Appendix `app1`: "it can be shown that `Z²` is at most the
value given in Equation `eq:sqdist2` in this case". -/
theorem t3Var_eq_min_sqDistHalfLine (hφ : φ < 3 / 2) {x : ℝ} (hx : x ≠ 0) (y : ℝ) :
    t3Var φ (x, y) = min (sqDistHalfLine 0 1 x y)
      (min (sqDistHalfLine (Real.cos (alphaZero φ)) (-Real.sin (alphaZero φ)) x y)
        (sqDistHalfLine (-Real.cos (alphaZero φ)) (-Real.sin (alphaZero φ)) x y)) := by
  have hS := sin_alphaZero_pos hφ
  have hC := cos_alphaZero_pos φ
  have hSC := Real.sin_sq_add_cos_sq (alphaZero φ)
  have hS1 : Real.sin (alphaZero φ) ≤ 1 := Real.sin_le_one _
  unfold t3Var sqDistHalfLine
  simp only
  rw [sin_sq_mul_cot hφ]
  set S := Real.sin (alphaZero φ)
  set C := Real.cos (alphaZero φ)
  have hfirst : (if 0 ≤ x * 0 + y * 1 then (x * 1 - y * 0) ^ 2 else x ^ 2 + y ^ 2) =
      x ^ 2 + if y < 0 then y ^ 2 else 0 := by
    by_cases hy : y < 0
    · rw [ite_eq_right (by simpa using hy), ite_eq_left hy]
    · rw [ite_eq_left (by simpa using not_lt.1 hy), ite_eq_right hy]
      ring
  rw [hfirst]
  set d₁ := x ^ 2 + if y < 0 then y ^ 2 else 0 with hd₁
  have hd₁x : x ^ 2 ≤ d₁ := by
    rw [hd₁]
    split_ifs <;> nlinarith [sq_nonneg y]
  have hd₁xy : d₁ ≤ x ^ 2 + y ^ 2 := by
    rw [hd₁]
    split_ifs <;> nlinarith [sq_nonneg y]
  have hd₁pos : 0 < y → d₁ = x ^ 2 := by
    intro hy
    rw [hd₁, ite_eq_right (not_lt.2 hy.le), add_zero]
  -- when the projection is beyond the origin, the line is further away than the vertical half-line
  have hbeyond : ∀ a : ℝ, 0 < a → a * C < y * S → a ^ 2 ≤ (S * a + C * y) ^ 2 := by
    intro a ha hlt
    have hy : 0 < y := by
      by_contra hn
      have : y * S ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (not_lt.1 hn) hS.le
      nlinarith [mul_pos ha hC]
    have h₁ : a ≤ S * a + C * y := by
      have h₂ : a * (C * C) ≤ (y * S) * C := by nlinarith
      have h₃ : a * S ≤ S * (S * a + C * y) := by nlinarith [mul_pos hS hS]
      exact le_of_mul_le_mul_left (by nlinarith) hS
    exact pow_le_pow_left₀ ha.le h₁ 2
  rcases lt_or_gt_of_ne hx with hneg | hpos
  · -- `x < 0`, on the side of the third half-line
    rw [Real.sign_of_neg hneg]
    have hform : (S * x + C * -1 * y) ^ 2 = (S * (-x) + C * y) ^ 2 := by ring
    rw [hform]
    have hxx : x ^ 2 = (-x) ^ 2 := by ring
    have h₂ : (if 0 ≤ x * C + y * -S then (x * -S - y * C) ^ 2 else x ^ 2 + y ^ 2) =
        if 0 ≤ x * C + y * -S then (S * x + C * y) ^ 2 else x ^ 2 + y ^ 2 := by
      congr 1
      ring
    have h₃ : (if 0 ≤ x * -C + y * -S then (x * -S - y * -C) ^ 2 else x ^ 2 + y ^ 2) =
        if 0 ≤ x * -C + y * -S then (S * (-x) + C * y) ^ 2 else x ^ 2 + y ^ 2 := by
      congr 1
      ring
    rw [h₂, h₃]
    refine le_antisymm (le_min (min_le_left _ _) (le_min ?_ ?_)) (le_min (min_le_left _ _) ?_)
    · split_ifs with h
      · have hy : y < 0 := by nlinarith [mul_neg_of_neg_of_pos hneg hC]
        exact (min_le_right _ _).trans (by nlinarith [mul_pos hS hC, mul_pos (neg_pos.2 hneg) (neg_pos.2 hy)])
      · exact (min_le_left _ _).trans hd₁xy
    · split_ifs with h
      · exact min_le_right _ _
      · exact (min_le_left _ _).trans hd₁xy
    · by_cases h : 0 ≤ x * -C + y * -S
      · rw [ite_eq_left h]
        exact (min_le_right _ _).trans (min_le_right _ _)
      · rw [ite_eq_right h]
        have := hbeyond (-x) (neg_pos.2 hneg) (by nlinarith)
        exact (min_le_left _ _).trans (by
          have hy : 0 < y := by
            by_contra hn
            have h₁ : y * S ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (not_lt.1 hn) hS.le
            nlinarith [mul_pos (neg_pos.2 hneg) hC]
          rw [hd₁pos hy, hxx]
          exact this)
  · -- `x > 0`, on the side of the second half-line
    rw [Real.sign_of_pos hpos]
    have hform : (S * x + C * 1 * y) ^ 2 = (S * x + C * y) ^ 2 := by ring
    rw [hform]
    have h₂ : (if 0 ≤ x * C + y * -S then (x * -S - y * C) ^ 2 else x ^ 2 + y ^ 2) =
        if 0 ≤ x * C + y * -S then (S * x + C * y) ^ 2 else x ^ 2 + y ^ 2 := by
      congr 1
      ring
    have h₃ : (if 0 ≤ x * -C + y * -S then (x * -S - y * -C) ^ 2 else x ^ 2 + y ^ 2) =
        if 0 ≤ x * -C + y * -S then (S * x - C * y) ^ 2 else x ^ 2 + y ^ 2 := by
      congr 1
      ring
    rw [h₂, h₃]
    refine le_antisymm (le_min (min_le_left _ _) (le_min ?_ ?_)) (le_min (min_le_left _ _) ?_)
    · split_ifs with h
      · exact min_le_right _ _
      · exact (min_le_left _ _).trans hd₁xy
    · split_ifs with h
      · have hy : y < 0 := by nlinarith [mul_pos hpos hC]
        exact (min_le_right _ _).trans (by nlinarith [mul_pos hS hC, mul_pos hpos (neg_pos.2 hy)])
      · exact (min_le_left _ _).trans hd₁xy
    · by_cases h : 0 ≤ x * C + y * -S
      · rw [ite_eq_left h]
        exact (min_le_right _ _).trans (min_le_left _ _)
      · rw [ite_eq_right h]
        have hlt : x * C < y * S := by nlinarith
        have := hbeyond x hpos hlt
        exact (min_le_left _ _).trans (by
          have hy : 0 < y := by
            by_contra hn
            have h₁ : y * S ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (not_lt.1 hn) hS.le
            nlinarith [mul_pos hpos hC]
          rw [hd₁pos hy]
          exact this)


/-! ### Bounds for the test distribution -/

theorem t3Tail_nonneg (φ n t : ℝ) : 0 ≤ t3Tail φ n t := measureReal_nonneg

theorem t3Tail_le_one (φ n t : ℝ) : t3Tail φ n t ≤ 1 := measureReal_le_one

theorem t3Tail_anti (φ n : ℝ) {s t : ℝ} (hst : s ≤ t) : t3Tail φ n t ≤ t3Tail φ n s :=
  measureReal_mono fun _ hz ↦ lt_of_le_of_lt hst hz

/-- **The T3 test distribution is below the T1 test distribution**, at the same parameter: the first argument
of the minimum is the variable of T1, as Mitchell, Allman, Rhodes 2019 note in "Application to Model T1". -/
theorem t3Tail_le_t1Tail (φ n t : ℝ) : t3Tail φ n t ≤ t1Tail (muZero φ n) t :=
  measureReal_mono fun z hz ↦ lt_of_lt_of_le (show t < t3Var φ z from hz) (min_le_left _ _)

/-- The upper bound for `μ₀ ≥ 0`, from that of the T1 test distribution. -/
theorem t3Tail_le_chiSqTwoTail {φ n t : ℝ} (hμ : 0 ≤ muZero φ n) (ht : 0 ≤ t) :
    t3Tail φ n t ≤ chiSqTwoTail t :=
  (t3Tail_le_t1Tail φ n t).trans (t1Tail_le_chiSqTwoTail hμ ht)

/-- Where `Z² > 10 t` and `Z̄ ≥ 0`, the T3 variable exceeds `t`: since `sin² α₀ ≥ 1/10`. -/
private lemma lt_t3Var {t x y : ℝ} (h0 : 0 ≤ φ) (h1 : φ ≤ 1) (ht : 0 ≤ t) (hx : 10 * t < x ^ 2)
    (hy : 0 ≤ y) : t < t3Var φ (x, y) := by
  have hs := one_tenth_le_sin_sq_alphaZero h0 h1
  have hs0 := sin_alphaZero_pos (φ := φ) (by linarith)
  have hc0 := cos_alphaZero_pos φ
  refine lt_min ?_ ?_
  · simp only
    rw [ite_eq_right (not_lt.2 hy)]
    nlinarith
  · rw [sin_sq_mul_cot (by linarith)]
    simp only
    have hxne : x ≠ 0 := by
      rintro rfl
      nlinarith
    set S := Real.sin (alphaZero φ)
    set C := Real.cos (alphaZero φ)
    have hsq : t < S ^ 2 * x ^ 2 := by nlinarith [sq_nonneg x]
    have hge : (S * x) ^ 2 ≤ (S * x + C * Real.sign x * y) ^ 2 := by
      rcases lt_or_gt_of_ne hxne with hneg | hpos
      · rw [Real.sign_of_neg hneg]
        have h₁ : S * x < 0 := mul_neg_of_pos_of_neg hs0 hneg
        have h₂ : 0 ≤ C * y := mul_nonneg hc0.le hy
        nlinarith [mul_nonneg (neg_nonneg.2 h₁.le) h₂, sq_nonneg (C * y)]
      · rw [Real.sign_of_pos hpos]
        have h₁ : 0 < S * x := mul_pos hs0 hpos
        have h₂ : 0 ≤ C * y := mul_nonneg hc0.le hy
        nlinarith [mul_nonneg h₁.le h₂, sq_nonneg (C * y)]
    rw [mul_pow] at hge
    exact hsq.trans_le hge

/-- **A lower bound for the T3 test distribution, uniform in the parameter**: on the fitted range
`0 ≤ φ ≤ 1`, the tail at `t` is at least half that of `χ²₁` at `10 t`. This is what keeps the p-value from collapsing
at the singularity, where the law does not tend to `χ²₁`. -/
theorem half_chiSqOneTail_le_t3Tail {n t : ℝ} (h0 : 0 ≤ φ) (h1 : φ ≤ 1) (ht : 0 ≤ t) :
    1 / 2 * chiSqOneTail (10 * t) ≤ t3Tail φ n t := by
  have hμ : 0 ≤ muZero φ n := muZero_nonneg_of_le_one h1
  have hsub : ({z : ℝ | 10 * t < z ^ 2} ×ˢ Ici (0 : ℝ)) ⊆ {z : ℝ × ℝ | t < t3Var φ z} := by
    rintro ⟨x, y⟩ ⟨hx, hy⟩
    exact lt_t3Var h0 h1 ht hx hy
  have h₂ : ((gaussianReal 0 1).prod (gaussianReal (muZero φ n) 1)).real
      ({z : ℝ | 10 * t < z ^ 2} ×ˢ Ici (0 : ℝ)) =
      chiSqOneTail (10 * t) * (gaussianReal (muZero φ n) 1).real (Ici 0) :=
    measureReal_prod_prod _ _
  have h₃ := gaussianReal_Ici_ge hμ
  have h₄ := chiSqOneTail_nonneg (10 * t)
  have h₅ := measureReal_mono (μ := (gaussianReal 0 1).prod (gaussianReal (muZero φ n) 1)) hsub
  rw [h₂] at h₅
  refine le_trans ?_ h₅
  nlinarith

theorem t3Tail_pos {n t : ℝ} (h0 : 0 ≤ φ) (h1 : φ ≤ 1) (ht : 0 ≤ t) : 0 < t3Tail φ n t :=
  lt_of_lt_of_le (by have := chiSqOneTail_pos (10 * t); positivity)
    (half_chiSqOneTail_le_t3Tail h0 h1 ht)

/-- Where `Z² ≤ κ` and `Z̄ ≥ 2 √κ`, the T3 variable is `Z²`: the two half-lines are further away than the vertical
one. -/
lemma t3Var_eq_of_large {κ x y : ℝ} (h1 : φ ≤ 1) (hx : x ^ 2 ≤ κ) (hy : 2 * √κ ≤ y) :
    t3Var φ (x, y) = x ^ 2 := by
  have hc := one_half_le_cos_alphaZero h1
  have hs0 := sin_alphaZero_pos (φ := φ) (by linarith)
  have hsq : 0 ≤ √κ := Real.sqrt_nonneg κ
  have hy0 : 0 ≤ y := by linarith
  have habs : |x| ≤ √κ := Real.abs_le_sqrt hx
  have hcy : √κ ≤ Real.cos (alphaZero φ) * y := by nlinarith
  unfold t3Var
  simp only
  rw [ite_eq_right (not_lt.2 hy0), add_zero, sin_sq_mul_cot (by linarith)]
  refine min_eq_left ?_
  set S := Real.sin (alphaZero φ)
  set C := Real.cos (alphaZero φ)
  rcases lt_trichotomy x 0 with hneg | rfl | hpos
  · rw [Real.sign_of_neg hneg]
    have h₁ : S * x ≤ 0 := (mul_neg_of_pos_of_neg hs0 hneg).le
    rw [abs_of_neg hneg] at habs
    have h₂ : S * x + C * -1 * y ≤ x := by nlinarith
    nlinarith
  · simp
  · rw [Real.sign_of_pos hpos]
    have h₁ : 0 ≤ S * x := (mul_pos hs0 hpos).le
    rw [abs_of_pos hpos] at habs
    have h₂ : x ≤ S * x + C * 1 * y := by nlinarith
    nlinarith

/-- **The T3 test distribution and the T1 test distribution agree in the limit**: "as the sample size `n` goes to
infinity, `μ₀` also goes to infinity, causing the distribution of `sgn(Z̄)` to concentrate on `1`, and the minimum
in the formula tends toward selecting the first argument" (Mitchell, Allman, Rhodes 2019, after Proposition
`prop:T3approx`). Uniformly on `0 ≤ φ ≤ 1` and in the argument `t`. -/
theorem exists_t1Tail_lt_t3Tail_add {ε : ℝ} (hε : 0 < ε) :
    ∃ M : ℝ, ∀ φ n t : ℝ, φ ≤ 1 → M ≤ muZero φ n → t1Tail (muZero φ n) t < t3Tail φ n t + ε := by
  have hε' : 0 < min (ε / 2) 1 := lt_min (half_pos hε) one_pos
  obtain ⟨κ, hκ0, hκ⟩ := exists_chiSqOneTail_eq hε' (min_le_right _ _)
  obtain ⟨M₀, hM₀⟩ := exists_gaussianReal_Iio_lt (half_pos hε)
  refine ⟨M₀ + 2 * √κ, fun φ n t hφ hM ↦ ?_⟩
  set μ := muZero φ n with hμ
  set ν := (gaussianReal 0 1).prod (gaussianReal μ 1) with hν
  have hsub : {z : ℝ × ℝ | t < z.1 ^ 2 + if z.2 < 0 then z.2 ^ 2 else 0} ⊆
      {z : ℝ × ℝ | t < t3Var φ z} ∪ (({z : ℝ | κ < z ^ 2} ×ˢ univ) ∪ (univ ×ˢ Iio (2 * √κ))) := by
    rintro ⟨x, y⟩ hz
    by_cases hx : κ < x ^ 2
    · exact Or.inr (Or.inl ⟨hx, mem_univ _⟩)
    by_cases hy : y < 2 * √κ
    · exact Or.inr (Or.inr ⟨mem_univ _, hy⟩)
    left
    have e := t3Var_eq_of_large hφ (not_lt.1 hx) (not_lt.1 hy)
    have hy0 : ¬ y < 0 := by
      have := Real.sqrt_nonneg κ
      linarith [not_lt.1 hy]
    have hz' : t < x ^ 2 + if y < 0 then y ^ 2 else 0 := hz
    rw [ite_eq_right hy0, add_zero] at hz'
    change t < t3Var φ (x, y)
    rwa [e]
  have h₁ := (measureReal_mono (μ := ν) hsub).trans (measureReal_union_le _ _)
  have h₂ := measureReal_union_le (μ := ν) ({z : ℝ | κ < z ^ 2} ×ˢ univ) (univ ×ˢ Iio (2 * √κ))
  have h₃ : ν.real ({z : ℝ | κ < z ^ 2} ×ˢ univ) = chiSqOneTail κ := by
    rw [hν, measureReal_prod_prod]
    simp [chiSqOneTail]
  have h₄ : ν.real (univ ×ˢ Iio (2 * √κ)) = (gaussianReal μ 1).real (Iio (2 * √κ)) := by
    rw [hν, measureReal_prod_prod]
    simp
  have h₅ : (gaussianReal μ 1).real (Iio (2 * √κ)) = (gaussianReal (μ - 2 * √κ) 1).real (Iio 0) := by
    rw [gaussianReal_real_Iio, gaussianReal_real_Iio]
    congr 3
    ring
  have h₆ := hM₀ (μ - 2 * √κ) (by linarith)
  have h₇ : chiSqOneTail κ ≤ ε / 2 := by
    rw [hκ]
    exact min_le_left _ _
  have h₈ : t1Tail μ t = ν.real {z : ℝ × ℝ | t < z.1 ^ 2 + if z.2 < 0 then z.2 ^ 2 else 0} := rfl
  have h₉ : t3Tail φ n t = ν.real {z : ℝ × ℝ | t < t3Var φ z} := rfl
  rw [h₈, h₉]
  linarith

/-- **The T3 test distribution tends to `χ²₁`**, uniformly on `0 ≤ φ ≤ 1` and in the argument `t`, as `μ₀` runs off:
"It follows that `Λ̃_n` is asymptotically `χ²₁`-distributed" (Mitchell, Allman, Rhodes 2019, after Proposition
`prop:T3approx`). Parallel to `Trinomial.abs_cutTail_sub_chiSqOneTail_lt`. -/
theorem abs_t3Tail_sub_chiSqOneTail_lt {ε : ℝ} (hε : 0 < ε) :
    ∃ M : ℝ, ∀ φ n t : ℝ, φ ≤ 1 → M ≤ muZero φ n → |t3Tail φ n t - chiSqOneTail t| < ε := by
  obtain ⟨M₁, hM₁⟩ := exists_t1Tail_lt_t3Tail_add hε
  obtain ⟨M₂, hM₂⟩ := exists_gaussianReal_Iio_lt hε
  refine ⟨max M₁ M₂, fun φ n t hφ hM ↦ abs_lt.2 ⟨?_, ?_⟩⟩
  · have h₁ := hM₁ φ n t hφ ((le_max_left _ _).trans hM)
    have h₂ := chiSqOneTail_le_t1Tail (muZero φ n) t
    linarith
  · have h₁ := t3Tail_le_t1Tail φ n t
    have h₂ := t1Tail_le_add (muZero φ n) t
    have h₃ := hM₂ _ ((le_max_right _ _).trans hM)
    linarith

/-- A Gaussian of any mean gives positive probability to a nonempty open interval. -/
private lemma gaussianReal_real_Ioo_pos' (m : ℝ) {a b : ℝ} (hab : a < b) :
    0 < (gaussianReal m 1).real (Ioo a b) := by
  rw [measureReal_def]
  refine ENNReal.toReal_pos (fun h => ?_) (measure_ne_top _ _)
  have := gaussianReal_absolutelyContinuous' m (v := 1) one_ne_zero h
  rw [Real.volume_Ioo, ENNReal.ofReal_eq_zero] at this
  linarith

/-- **The T3 test distribution is strictly below the T1 test distribution**, at every `t > 0`: around a point of
one of the other two half-lines, far enough from the origin, the T3 variable is at most `t` and the T1 variable
is above it. -/
theorem t3Tail_lt_t1Tail {n t : ℝ} (hφ : φ < 3 / 2) (ht : 0 < t) :
    t3Tail φ n t < t1Tail (muZero φ n) t := by
  set S := Real.sin (alphaZero φ) with hSdef
  set C := Real.cos (alphaZero φ) with hCdef
  have hS : 0 < S := sin_alphaZero_pos hφ
  have hC : 0 < C := cos_alphaZero_pos φ
  have hS1 : S ≤ 1 := Real.sin_le_one _
  have hC1 : C ≤ 1 := Real.cos_le_one _
  set r := √t with hr
  have hr0 : 0 < r := Real.sqrt_pos.2 ht
  have hrs : r ^ 2 = t := Real.sq_sqrt ht.le
  set x₀ := 3 / 2 * r with hx₀
  set y₀ := -(S / C * x₀) with hy₀
  have hline : S * x₀ + C * y₀ = 0 := by
    rw [hy₀]
    field_simp
    ring
  set box : Set (ℝ × ℝ) := Ioo r (2 * r) ×ˢ Ioo (y₀ - r / 2) (y₀ + r / 2) with hbox
  set μ := muZero φ n with hμ
  set ν := (gaussianReal 0 1).prod (gaussianReal μ 1) with hν
  have hboxm : MeasurableSet box := measurableSet_Ioo.prod measurableSet_Ioo
  have hboxpos : 0 < ν.real box := by
    rw [hν, hbox, measureReal_prod_prod]
    exact mul_pos (gaussianReal_real_Ioo_pos' 0 (by linarith)) (gaussianReal_real_Ioo_pos' μ (by linarith))
  have hdisj : Disjoint {z : ℝ × ℝ | t < t3Var φ z} box := by
    rw [Set.disjoint_left]
    rintro ⟨x, y⟩ hz ⟨hx, hy⟩
    have hz' : t < t3Var φ (x, y) := hz
    have hx1 : r < x := hx.1
    have hx2 : x < 2 * r := hx.2
    have hy1 : y₀ - r / 2 < y := hy.1
    have hy2 : y < y₀ + r / 2 := hy.2
    have hle : t3Var φ (x, y) ≤ _ := min_le_right _ _
    simp only at hle
    rw [sin_sq_mul_cot hφ, Real.sign_of_pos (by linarith), mul_one] at hle
    have hdec : S * x + C * y = S * (x - x₀) + C * (y - y₀) := by
      linear_combination hline
    have ha : |S * (x - x₀)| ≤ r / 2 := by
      rw [abs_mul, abs_of_pos hS]
      have : |x - x₀| ≤ r / 2 := abs_le.2 ⟨by rw [hx₀]; linarith, by rw [hx₀]; linarith⟩
      nlinarith [abs_nonneg (x - x₀)]
    have hb : |C * (y - y₀)| ≤ r / 2 := by
      rw [abs_mul, abs_of_pos hC]
      have : |y - y₀| ≤ r / 2 := abs_le.2 ⟨by linarith, by linarith⟩
      nlinarith [abs_nonneg (y - y₀)]
    have hsum : |S * x + C * y| ≤ r := by
      rw [hdec]
      exact (abs_add_le _ _).trans (by linarith)
    have hsq : (S * x + C * y) ^ 2 ≤ r ^ 2 := by
      rw [← sq_abs (S * x + C * y)]
      exact pow_le_pow_left₀ (abs_nonneg _) hsum 2
    have : t < t := by
      calc t < t3Var φ (x, y) := hz'
        _ ≤ _ := hle
        _ ≤ t := by rw [← hrs]; exact hsq
    exact lt_irrefl _ this
  have hsub : {z : ℝ × ℝ | t < t3Var φ z} ∪ box ⊆
      {z : ℝ × ℝ | t < z.1 ^ 2 + if z.2 < 0 then z.2 ^ 2 else 0} := by
    rintro ⟨x, y⟩ (hz | ⟨hx, -⟩)
    · exact lt_of_lt_of_le (show t < t3Var φ (x, y) from hz) (min_le_left _ _)
    · have hx1 : r < x := hx.1
      change t < x ^ 2 + if y < 0 then y ^ 2 else 0
      have h₁ : t < x ^ 2 := by rw [← hrs]; nlinarith
      split_ifs <;> nlinarith [sq_nonneg y]
  have h₁ := measureReal_mono (μ := ν) hsub
  rw [measureReal_union hdisj hboxm] at h₁
  have h₈ : t1Tail μ t = ν.real {z : ℝ × ℝ | t < z.1 ^ 2 + if z.2 < 0 then z.2 ^ 2 else 0} := rfl
  have h₉ : t3Tail φ n t = ν.real {z : ℝ × ℝ | t < t3Var φ z} := rfl
  rw [h₈, h₉]
  linarith

/-! ### The statistic -/

theorem t3Stat_le_t1Stat (c : QuartetTree X → ℝ) {q : Finset X} {s : QuartetTree X} (hs : s ∈ treesOn q) :
    t3Stat c q ≤ t1Stat c s :=
  ciInf_le (Set.finite_range _).bddBelow (⟨s, hs⟩ : {t // t ∈ treesOn q})

/-- The least of the three statistics is attained. -/
theorem exists_t3Stat_eq (c : QuartetTree X → ℝ) {q : Finset X} (hq : q.card = 4) :
    ∃ s ∈ treesOn q, t3Stat c q = t1Stat c s := by
  have hne : (treesOn q).Nonempty := by
    rw [← Finset.card_pos, card_treesOn hq]
    norm_num
  obtain ⟨s₀, hs₀⟩ := hne
  have : Nonempty {s // s ∈ treesOn q} := ⟨⟨s₀, hs₀⟩⟩
  obtain ⟨u, hu⟩ := exists_eq_ciInf_of_finite (f := fun u : {s // s ∈ treesOn q} => t1Stat c u.val)
  exact ⟨u.val, u.property, hu.symm⟩

theorem t3Stat_nonneg {c : QuartetTree X → ℝ} (hc : ∀ r, 0 ≤ c r) {q : Finset X} (hq : q.card = 4) :
    0 ≤ t3Stat c q := by
  obtain ⟨s, -, hs⟩ := exists_t3Stat_eq c hq
  rw [hs]
  exact t1Stat_nonneg c hc s

/-- At a topology of least T1 statistic, the maximum likelihood topology of model T3, the T3 statistic is its
T1 statistic. -/
theorem t3Stat_eq_of_isMin {c : QuartetTree X → ℝ} {q : Finset X} (hq : q.card = 4) {s : QuartetTree X}
    (hs : s ∈ treesOn q) (hmin : ∀ r ∈ treesOn q, t1Stat c s ≤ t1Stat c r) :
    t3Stat c q = t1Stat c s := by
  obtain ⟨u, hu, he⟩ := exists_t3Stat_eq c hq
  exact le_antisymm (t3Stat_le_t1Stat c hs) (by rw [he]; exact hmin u hu)

/-- The deviance of the star test splits into that of the line and that of the centroid from the fit on the
line. -/
theorem starS_eq_lineS_add (a b c : ℝ) :
    starS a b c = lineS b c + starS a ((b + c) / 2) ((b + c) / 2) := by
  have hN : a + (b + c) / 2 + (b + c) / 2 = a + b + c := by ring
  have hlog : (b + c) / 2 * Real.log ((b + c) / 2) + (b + c) / 2 * Real.log ((b + c) / 2) =
      (b + c) * Real.log (b + c) - (b + c) * Real.log 2 := by
    by_cases h : b + c = 0
    · simp [h]
    · rw [Real.log_div h two_ne_zero]
      ring
  unfold starS lineS
  rw [hN]
  linear_combination (-2) * hlog

theorem lineS_le_starS {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) : lineS b c ≤ starS a b c := by
  rw [starS_eq_lineS_add]
  have : 0 ≤ (b + c) / 2 := by positivity
  linarith [starS_nonneg ha this this]

/-- The line statistic increases as an entry moves away from the other, by convexity of `x log x`. -/
theorem lineS_le_lineS_of_le {a b c : ℝ} (hc : 0 ≤ c) (hcb : c ≤ b) (hba : b ≤ a) :
    lineS b c ≤ lineS a c := by
  rcases hba.eq_or_lt with rfl | hab
  · exact le_rfl
  have hb : 0 ≤ b := hc.trans hcb
  have ha : 0 ≤ a := hb.trans hba
  set p₁ := (b + c) / 2 with hp₁
  set p₂ := (a + c) / 2 with hp₂
  have hp₁0 : 0 ≤ p₁ := by positivity
  have hw : 0 < a - p₁ := by rw [hp₁]; linarith
  have hlog : ∀ x : ℝ, (x + c) * Real.log (x + c) - (x + c) * Real.log 2 =
      2 * ((x + c) / 2 * Real.log ((x + c) / 2)) := by
    intro x
    by_cases h : x + c = 0
    · simp [h]
    · rw [Real.log_div h two_ne_zero]
      ring
  have hconv := Real.convexOn_mul_log
  have hl₁ : 0 ≤ (b - p₁) / (a - p₁) := div_nonneg (by rw [hp₁]; linarith) hw.le
  have hl₂ : 0 ≤ (a - b) / (a - p₁) := div_nonneg (by linarith) hw.le
  have hμ₁ : 0 ≤ (p₂ - p₁) / (a - p₁) := div_nonneg (by rw [hp₁, hp₂]; linarith) hw.le
  have hμ₂ : 0 ≤ (a - p₂) / (a - p₁) := div_nonneg (by rw [hp₂]; linarith) hw.le
  have h₁ := hconv.2 (show a ∈ Ici (0 : ℝ) from ha) (show p₁ ∈ Ici (0 : ℝ) from hp₁0) hl₁ hl₂
    (by field_simp; ring)
  have h₂ := hconv.2 (show a ∈ Ici (0 : ℝ) from ha) (show p₁ ∈ Ici (0 : ℝ) from hp₁0) hμ₁ hμ₂
    (by field_simp; ring)
  have e₁ : (b - p₁) / (a - p₁) * a + (a - b) / (a - p₁) * p₁ = b := by
    field_simp
    ring
  have e₂ : (p₂ - p₁) / (a - p₁) * a + (a - p₂) / (a - p₁) * p₁ = p₂ := by
    field_simp
    ring
  simp only [smul_eq_mul] at h₁ h₂
  rw [e₁] at h₁
  rw [e₂] at h₂
  set A := a * Real.log a with hA
  set P := p₁ * Real.log p₁ with hP
  have n₃ : (b - p₁) + 2 * (p₂ - p₁) = a - p₁ := by
    rw [hp₁, hp₂]
    ring
  have n₄ : (a - b) + 2 * (a - p₂) = 2 * (a - p₁) := by
    rw [hp₁, hp₂]
    ring
  have e₃ : (b - p₁) / (a - p₁) + 2 * ((p₂ - p₁) / (a - p₁)) = 1 := by
    rw [← mul_div_assoc, ← add_div, n₃, div_self hw.ne']
  have e₄ : (a - b) / (a - p₁) + 2 * ((a - p₂) / (a - p₁)) = 2 := by
    rw [← mul_div_assoc, ← add_div, n₄]
    field_simp
  have hsum : b * Real.log b + 2 * (p₂ * Real.log p₂) ≤ A + 2 * P := by
    have : A + 2 * P = ((b - p₁) / (a - p₁) + 2 * ((p₂ - p₁) / (a - p₁))) * A +
        ((a - b) / (a - p₁) + 2 * ((a - p₂) / (a - p₁))) * P := by
      rw [e₃, e₄]
      ring
    rw [this]
    nlinarith
  have hb' : (b + c) * Real.log (b + c) - (b + c) * Real.log 2 = 2 * (p₁ * Real.log p₁) := hlog b
  have ha' : (a + c) * Real.log (a + c) - (a + c) * Real.log 2 = 2 * (p₂ * Real.log p₂) := hlog a
  unfold lineS
  linarith

/-! ### The statistics as functions of the three counts -/

/-- The statistic of a line is at most that of the star: the star is on the line. -/
theorem lineStat_le_starStat {c : QuartetTree X → ℝ} (hc : ∀ r, 0 ≤ c r) (s : QuartetTree X) :
    lineStat c s ≤ starStat c s.taxa := by
  obtain ⟨r₁, r₂, hne, h⟩ := QuartetTree.exists_alternatives s
  rw [lineStat_eq_lineS c hne h, starStat_eq_starS c hne h]
  exact lineS_le_starS (hc _) (hc _) (hc _)

/-- The T1 null is inside the line, so its statistic is at least that of the line. -/
theorem lineStat_le_t1Stat {c : QuartetTree X → ℝ} (hc : ∀ r, 0 ≤ c r) (s : QuartetTree X) :
    lineStat c s ≤ t1Stat c s := by
  unfold t1Stat
  split_ifs
  · exact le_rfl
  · exact lineStat_le_starStat hc s

private theorem t1Stat_le_aux {c : QuartetTree X → ℝ} (hc : ∀ r, 0 ≤ c r) {s r₁ r₂ : QuartetTree X}
    (hne : r₁ ≠ r₂) (h : s.alternatives = {r₁, r₂}) (h₁ : c r₁ ≤ c s) (h₂ : c r₂ ≤ c s) :
    t1Stat c s ≤ t1Stat c r₁ := by
  obtain ⟨-, hs₂, ha₁, ht₁, -⟩ := alternatives_taxa hne h
  have hs : t1Stat c s = lineS (c r₁) (c r₂) := by
    unfold t1Stat
    rw [h, Finset.sum_pair hne, ite_eq_left (by linarith), lineStat_eq_lineS c hne h]
  rw [hs]
  unfold t1Stat
  rw [ha₁, Finset.sum_pair hs₂]
  split_ifs with hcond
  · rw [lineStat_eq_lineS c hs₂ ha₁]
    exact lineS_le_lineS_of_le (hc _) (by linarith) h₁
  · rw [ht₁, ← lineStat_eq_lineS c hne h]
    exact lineStat_le_starStat hc s

/-- **A topology of highest count is a maximum likelihood topology of model T3**: it has the least T1 statistic of
the three. -/
theorem t1Stat_le_t1Stat_of_max {c : QuartetTree X → ℝ} (hc : ∀ r, 0 ≤ c r) {s : QuartetTree X}
    (hmax : ∀ r ∈ s.alternatives, c r ≤ c s) {r : QuartetTree X} (hr : r ∈ treesOn s.taxa) :
    t1Stat c s ≤ t1Stat c r := by
  obtain ⟨r₁, r₂, hne, h⟩ := QuartetTree.exists_alternatives s
  have h₁ := hmax r₁ (by rw [h]; simp)
  have h₂ := hmax r₂ (by rw [h]; simp)
  by_cases hrs : r = s
  · rw [hrs]
  have hrm : r ∈ s.alternatives := QuartetTree.mem_alternatives.2 ⟨mem_treesOn.1 hr, hrs⟩
  rw [h] at hrm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hrm
  rcases hrm with rfl | rfl
  · exact t1Stat_le_aux hc hne h h₁ h₂
  · exact t1Stat_le_aux hc hne.symm (by rw [h, Finset.pair_comm]) h₂ h₁

/-- **The T3 statistic at the highest count**: if `s` has the highest count, the statistic of model T3 is its T1
statistic, which is the statistic of its line. -/
theorem t3Stat_eq_lineStat_of_max {c : QuartetTree X → ℝ} (hc : ∀ r, 0 ≤ c r) {s : QuartetTree X}
    (hmax : ∀ r ∈ s.alternatives, c r ≤ c s) : t3Stat c s.taxa = lineStat c s := by
  rw [t3Stat_eq_of_isMin s.card_taxa (mem_treesOn_taxa s) fun r hr => t1Stat_le_t1Stat_of_max hc hmax hr]
  unfold t1Stat
  obtain ⟨r₁, r₂, hne, h⟩ := QuartetTree.exists_alternatives s
  have h₁ := hmax r₁ (by rw [h]; simp)
  have h₂ := hmax r₂ (by rw [h]; simp)
  rw [ite_eq_left]
  rw [h, Finset.sum_pair hne]
  linarith

/-! ### Bounds for the p-value -/

theorem t1Phi_nonneg {c : QuartetTree X → ℝ} (hc : ∀ r, 0 ≤ c r) (s : QuartetTree X) : 0 ≤ t1Phi c s := by
  have hA : 0 ≤ ∑ r ∈ s.alternatives, c r := Finset.sum_nonneg fun r _ => hc r
  exact le_min zero_le_one (div_nonneg (by positivity) (by have := hc s; positivity))

theorem t1Phi_le_one (c : QuartetTree X → ℝ) (s : QuartetTree X) : t1Phi c s ≤ 1 := min_le_left _ _

/-- The p-value of the T3 test is at most `χ²₂` at the statistic, whatever the fitted topology. -/
theorem t3PValue_le_chiSqTwoTail {c : QuartetTree X → ℝ} (hc : ∀ r, 0 ≤ c r) (s : QuartetTree X) :
    t3PValue c s ≤ chiSqTwoTail (t3Stat c s.taxa) :=
  t3Tail_le_chiSqTwoTail (muZero_t1Phi_nonneg c s) (t3Stat_nonneg hc s.card_taxa)

/-- The p-value of the T3 test is at least half the tail of `χ²₁` at ten times the statistic, whatever the
fitted topology. -/
theorem half_chiSqOneTail_le_t3PValue {c : QuartetTree X → ℝ} (hc : ∀ r, 0 ≤ c r) (s : QuartetTree X) :
    1 / 2 * chiSqOneTail (10 * t3Stat c s.taxa) ≤ t3PValue c s :=
  half_chiSqOneTail_le_t3Tail (t1Phi_nonneg hc s) (t1Phi_le_one c s) (t3Stat_nonneg hc s.card_taxa)


/-! ### The test on a sample -/

section Sample

variable {Γ : Type*} [Fintype Γ] {dist : Γ → ℝ} {sides : Γ → Finset (Finset X)}

/-- With entries summing to one, the T1 null is the half-line `(1 - 2q, q, q)`, `q ≤ 1/3`. -/
theorem isT1Null_iff_le_third {p : QuartetTree X → ℝ} {s : QuartetTree X}
    (hp : ∑ r ∈ treesOn s.taxa, p r = 1) :
    IsT1Null p s ↔ (∀ r ∈ s.alternatives, p r ≤ 1 / 3) ∧
      ∀ r ∈ s.alternatives, ∀ r' ∈ s.alternatives, p r = p r' := by
  obtain ⟨r₁, r₂, hne, h⟩ := QuartetTree.exists_alternatives s
  rw [sum_treesOn p hne h] at hp
  have hm₁ : r₁ ∈ s.alternatives := by rw [h]; simp
  have hm₂ : r₂ ∈ s.alternatives := by rw [h]; simp
  refine and_congr_left fun heq => ?_
  have he := heq r₁ hm₁ r₂ hm₂
  constructor
  · intro hle r hr
    rw [heq r hr r₁ hm₁]
    have := hle r₁ hm₁
    linarith
  · intro hle r hr
    rw [heq r hr r₁ hm₁]
    have := hle r₁ hm₁
    linarith

theorem IsT1Null.of_isT1Strict {p : QuartetTree X → ℝ} {s : QuartetTree X}
    (h : IsT1Strict p s) : IsT1Null p s :=
  ⟨fun r hr => (h.1 r hr).le, h.2⟩

/-- An **anomalous** concordance factor (TINNiK, "The T3 model and testing": `ab|cd` cut of the form `(p, q, q)`
with `q > 1/3`, off the centroid) is off model T3. -/
theorem not_isT3Null_of_anomalous {p : QuartetTree X → ℝ} {s : QuartetTree X}
    (hlt : ∀ r ∈ s.alternatives, p s < p r) : ¬ IsT3Null p s.taxa := by
  rintro ⟨u, hu, hle, heq⟩
  obtain ⟨r₁, r₂, hne, ha⟩ := QuartetTree.exists_alternatives s
  obtain ⟨hs₁, hs₂, ha₁, ht₁, ht₂⟩ := alternatives_taxa hne ha
  obtain ⟨-, -, ha₂, -, -⟩ := alternatives_taxa hne.symm (by rw [ha, Finset.pair_comm] : s.alternatives = {r₂, r₁})
  have h₁ := hlt r₁ (by rw [ha]; simp)
  have h₂ := hlt r₂ (by rw [ha]; simp)
  by_cases hus : u = s
  · subst hus
    exact absurd (hle r₁ (by rw [ha]; simp)) (not_le.2 h₁)
  have hum : u ∈ s.alternatives := QuartetTree.mem_alternatives.2 ⟨mem_treesOn.1 hu, hus⟩
  rw [ha] at hum
  simp only [Finset.mem_insert, Finset.mem_singleton] at hum
  rcases hum with rfl | rfl
  · have := heq s (by rw [ha₁]; simp) r₂ (by rw [ha₁]; simp)
    linarith
  · have := heq s (by rw [ha₂]; simp) r₁ (by rw [ha₂]; simp)
    linarith

/-- On the null, with positive probabilities, the T1 p-value does not collapse: it is asymptotically uniform off
the boundary, and stays away from `0` at the boundary. -/
private theorem exists_t1PValue_lower (hd : IsDist dist) (hs : DisplaysOne dist sides) {s : QuartetTree X}
    (hnull : IsT1Null (displayCF dist sides) s)
    (hpos : ∀ r ∈ s.alternatives, 0 < displayCF dist sides r) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ n in atTop, 1 - ε < iidProb dist n fun ω =>
      δ ≤ t1PValue (quartetCount sides ω) s := by
  obtain ⟨r₁, r₂, hne, h⟩ := QuartetTree.exists_alternatives s
  obtain ⟨hle, heq⟩ := hnull
  have hm₁ : r₁ ∈ s.alternatives := by rw [h]; simp
  have hm₂ : r₂ ∈ s.alternatives := by rw [h]; simp
  by_cases hlt : displayCF dist sides r₁ < displayCF dist sides s
  · have hlt' : ∀ r ∈ s.alternatives, displayCF dist sides r < displayCF dist sides s := fun r hr => by
      rw [heq r hr r₁ hm₁]
      exact hlt
    have hAU := t1PValue_asymptoticallyUniform hd hs hlt' heq hpos
    have hx0 : 0 < min (ε / 2) 1 := lt_min (half_pos hε) one_pos
    have hx1 : min (ε / 2) 1 ≤ 1 := min_le_right _ _
    have hxε : min (ε / 2) 1 ≤ ε / 2 := min_le_left _ _
    set x := min (ε / 2) 1
    refine ⟨x, hx0, ?_⟩
    have hlim := hAU x hx0.le hx1
    filter_upwards [hlim.eventually (gt_mem_nhds (by linarith : x < x + ε / 2))] with n hn
    have h₁ := iidProb_not hd n fun ω => t1PValue (quartetCount sides ω) s ≤ x
    have h₂ : iidProb dist n (fun ω => ¬ t1PValue (quartetCount sides ω) s ≤ x) ≤
        iidProb dist n fun ω => x ≤ t1PValue (quartetCount sides ω) s :=
      iidProb_mono hd fun ω hω => (not_le.1 hω).le
    linarith
  · have hs₁ : displayCF dist sides r₁ = displayCF dist sides s :=
      le_antisymm (hle r₁ hm₁) (not_lt.1 hlt)
    have hsum := sum_displayCF_treesOn hd hs s.card_taxa
    rw [sum_treesOn _ hne h, ← heq r₁ hm₁ r₂ hm₂, hs₁] at hsum
    have hthird : displayCF dist sides s = 1 / 3 := by linarith
    have hall : ∀ r ∈ treesOn s.taxa, displayCF dist sides r = 1 / 3 := by
      intro r hr
      by_cases hrs : r = s
      · rw [hrs, hthird]
      · have hrm : r ∈ s.alternatives := QuartetTree.mem_alternatives.2 ⟨mem_treesOn.1 hr, hrs⟩
        rw [heq r hrm r₁ hm₁, hs₁, hthird]
    obtain ⟨δ, hδ, -, hev⟩ := t1PValue_centroid_tight hd hs hall hε
    refine ⟨δ, hδ, ?_⟩
    filter_upwards [hev] with n hn
    exact hn.trans_le (iidProb_mono hd fun ω hω => hω.1)

/-- **The T3 test does not reject on its null, including at the singularity.** For a concordance factor `(p, q, q)`
with `0 < q ≤ 1/3` on model T3, and levels `α_n → 0`, with probability tending to one the T3 p-value is at least `α_n`,
whatever the fitted topology.

At the singularity `(1/3, 1/3, 1/3)` the test distribution does not tend to `χ²₁`, and the fitted `μ̂₀` stays bounded in
probability. Two facts carry the proof: the statistic is at most the T1 statistic of the true topology, which is
tight on the null since the T1 p-value does not collapse (`t1PValue_asymptoticallyUniform`,
`t1PValue_centroid_tight`), and the test distribution has a lower bound uniform in the parameter
(`half_chiSqOneTail_le_t3Tail`). The fitted `φ̂` is in `[0, 1]`, so the bound applies at the MLE. -/
theorem t3Test_nonCollapse (hd : IsDist dist) (hs : DisplaysOne dist sides) {s : QuartetTree X}
    (hnull : IsT1Null (displayCF dist sides) s)
    (hpos : ∀ r ∈ s.alternatives, 0 < displayCF dist sides r) {α : ℕ → ℝ}
    (hα : Tendsto α atTop (𝓝 0)) :
    Tendsto (fun n => iidProb dist n fun ω =>
      ∀ u ∈ treesOn s.taxa, α n ≤ t3PValue (quartetCount sides ω) u) atTop (𝓝 1) := by
  refine tendsto_order.2 ⟨fun a ha => ?_, fun a ha =>
    Eventually.of_forall fun n => (iidProb_le_one hd n _).trans_lt ha⟩
  obtain ⟨δ, hδ, hev⟩ := exists_t1PValue_lower hd hs hnull hpos (sub_pos.2 ha)
  set K := -2 * Real.log δ with hK
  have hδ' : 0 < 1 / 2 * chiSqOneTail (10 * K) := by
    have := chiSqOneTail_pos (10 * K)
    positivity
  filter_upwards [hev, hα.eventually (gt_mem_nhds hδ')] with n h₁ h₂
  refine (by linarith : a < _).trans_le (iidProb_mono hd fun ω hω u hu => ?_)
  have hc := quartetCount_nonneg (sides := sides) ω
  have hle : δ ≤ chiSqTwoTail (t1Stat (quartetCount sides ω) s) :=
    hω.trans (t1Tail_le_chiSqTwoTail (muZero_t1Phi_nonneg _ s) (t1Stat_nonneg _ hc s))
  have hstat : t1Stat (quartetCount sides ω) s ≤ K := by
    have := Real.log_le_log hδ hle
    rw [chiSqTwoTail, Real.log_exp] at this
    rw [hK]
    linarith
  have h₃ : t3Stat (quartetCount sides ω) s.taxa ≤ K :=
    (t3Stat_le_t1Stat _ (mem_treesOn_taxa s)).trans hstat
  have h₄ := half_chiSqOneTail_le_t3PValue hc u
  rw [mem_treesOn.1 hu] at h₄
  have h₅ : chiSqOneTail (10 * K) ≤ chiSqOneTail (10 * t3Stat (quartetCount sides ω) s.taxa) :=
    chiSqOneTail_anti (by linarith)
  linarith

/-- At a concordance factor strictly on a T1 null, with positive probabilities, the true topology has strictly the
least T1 statistic with probability tending to one, so that it is the maximum likelihood topology of model T3. -/
theorem tendsto_t1Stat_lt (hd : IsDist dist) (hs : DisplaysOne dist sides) {s : QuartetTree X}
    (hstrict : IsT1Strict (displayCF dist sides) s)
    (hpos : ∀ r ∈ s.alternatives, 0 < displayCF dist sides r) :
    Tendsto (fun n => iidProb dist n fun ω =>
      ∀ r ∈ s.alternatives, t1Stat (quartetCount sides ω) s < t1Stat (quartetCount sides ω) r)
      atTop (𝓝 1) := by
  obtain ⟨r₁, r₂, hne, h⟩ := QuartetTree.exists_alternatives s
  have hm₁ : r₁ ∈ s.alternatives := by rw [h]; simp
  have hm₂ : r₂ ∈ s.alternatives := by rw [h]; simp
  have hpos' : ∀ r ∈ treesOn s.taxa, 0 < displayCF dist sides r := by
    intro r hr
    by_cases hrs : r = s
    · rw [hrs]
      exact (hpos r₁ hm₁).trans (hstrict.1 r₁ hm₁)
    · exact hpos r (QuartetTree.mem_alternatives.2 ⟨mem_treesOn.1 hr, hrs⟩)
  have hline := cutTest_null hd hs (fun r hr => (hstrict.1 r hr).ne) hstrict.2 hpos' (α := fun _ => 0)
    tendsto_const_nhds
  have hF : ∀ᶠ x : QuartetTree X → ℝ in 𝓝 (displayCF dist sides),
      (∑ r ∈ s.alternatives, x r) / 2 < x s := by
    refine ContinuousAt.eventually_lt
      (((continuous_finsetSum _ fun r _ => continuous_apply r).div_const 2).continuousAt)
      (continuous_apply s).continuousAt ?_
    rw [h, Finset.sum_pair hne]
    linarith [hstrict.1 r₁ hm₁, hstrict.1 r₂ hm₂]
  refine tendsto_iidProb_of_imp hd ?_ (tendsto_iidProb_and hd hline (tendsto_iidProb_freq hd hF))
  filter_upwards [eventually_gt_atTop 0] with n hn0 ω hω r hr
  obtain ⟨⟨h₁, -⟩, h₂⟩ := hω
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn0
  have hc := quartetCount_nonneg (sides := sides) ω
  have h₂' : (∑ r ∈ s.alternatives, quartetCount sides ω r / n) / 2 < quartetCount sides ω s / n := h₂
  rw [← Finset.sum_div, div_right_comm, div_lt_div_iff_of_pos_right hn'] at h₂'
  have he : t1Stat (quartetCount sides ω) s = lineStat (quartetCount sides ω) s := by
    unfold t1Stat
    rw [ite_eq_left h₂'.le]
  rw [he]
  exact (h₁ r hr).trans_le (lineStat_le_t1Stat hc r)

/-- **The T3 test at a concordance factor strictly on a half-line** (the null, off its singularity), with positive
probabilities: the line of the true topology has the least T1 statistic with probability tending to one, and for any
levels `α_n → 0` the test does not reject. Parallel to `cutTest_null`. -/
theorem t3Test_null (hd : IsDist dist) (hs : DisplaysOne dist sides) {s : QuartetTree X}
    (hstrict : IsT1Strict (displayCF dist sides) s)
    (hpos : ∀ r ∈ s.alternatives, 0 < displayCF dist sides r) {α : ℕ → ℝ}
    (hα : Tendsto α atTop (𝓝 0)) :
    Tendsto (fun n => iidProb dist n fun ω =>
      (∀ r ∈ s.alternatives, t1Stat (quartetCount sides ω) s < t1Stat (quartetCount sides ω) r) ∧
        α n ≤ t3PValue (quartetCount sides ω) s) atTop (𝓝 1) := by
  refine tendsto_iidProb_of_imp hd (Eventually.of_forall fun n ω hω =>
    ⟨hω.1, hω.2 s (mem_treesOn_taxa s)⟩) (tendsto_iidProb_and hd (tendsto_t1Stat_lt hd hs hstrict hpos)
      (t3Test_nonCollapse hd hs (IsT1Null.of_isT1Strict hstrict) hpos hα))

/-- At a concordance factor strictly on a half-line, with positive probabilities, the fitted `μ̂₀` runs off to infinity:
"`μ₀` also goes to infinity" (Mitchell, Allman, Rhodes 2019, after Proposition `prop:T3approx`), at the MLE. -/
theorem tendsto_muZero_t1Phi_large (hd : IsDist dist) (hs : DisplaysOne dist sides) {s : QuartetTree X}
    (hstrict : IsT1Strict (displayCF dist sides) s)
    (hpos : ∀ r ∈ s.alternatives, 0 < displayCF dist sides r) (M : ℝ) :
    Tendsto (fun n => iidProb dist n fun ω =>
      M ≤ muZero (t1Phi (quartetCount sides ω) s)
        (quartetCount sides ω s + ∑ r ∈ s.alternatives, quartetCount sides ω r)) atTop (𝓝 1) := by
  obtain ⟨r₁, r₂, hne, h⟩ := QuartetTree.exists_alternatives s
  have hm₁ : r₁ ∈ s.alternatives := by rw [h]; simp
  have hm₂ : r₂ ∈ s.alternatives := by rw [h]; simp
  set p := displayCF dist sides with hp
  have hsum : p s + (p r₁ + p r₂) = 1 := by
    have := sum_displayCF_treesOn hd hs s.card_taxa
    rwa [sum_treesOn _ hne h, add_assoc] at this
  have heq : p r₁ = p r₂ := hstrict.2 r₁ hm₁ r₂ hm₂
  have hlt : p r₁ < p s := hstrict.1 r₁ hm₁
  have hq0 : 0 < p r₁ := hpos r₁ hm₁
  have hA : Continuous fun x : QuartetTree X → ℝ => ∑ r ∈ s.alternatives, x r :=
    continuous_finsetSum _ fun r _ => continuous_apply r
  have hN : Continuous fun x : QuartetTree X → ℝ => x s + ∑ r ∈ s.alternatives, x r :=
    (continuous_apply s).add hA
  have hNp : p s + ∑ r ∈ s.alternatives, p r = 1 := by
    rw [h, Finset.sum_pair hne]
    exact hsum
  have hAp : ∑ r ∈ s.alternatives, p r = 2 * p r₁ := by
    rw [h, Finset.sum_pair hne, ← heq]
    ring
  set f : (QuartetTree X → ℝ) → ℝ := fun x =>
    3 * (∑ r ∈ s.alternatives, x r) / (2 * (x s + ∑ r ∈ s.alternatives, x r)) with hf
  have hfc : ContinuousAt f p := by
    refine ContinuousAt.div (continuous_const.mul hA).continuousAt
      (continuous_const.mul hN).continuousAt ?_
    rw [hNp]
    norm_num
  have hfp : f p = 3 * p r₁ := by
    simp only [hf]
    rw [hNp, hAp]
    ring
  have hφ1 : 3 * p r₁ < 1 := by linarith
  set g := (1 - 3 * p r₁) / 2 with hg
  have hg0 : 0 < g := by rw [hg]; linarith
  have hF : ∀ᶠ x in 𝓝 p, 1 / 2 < (x s + ∑ r ∈ s.alternatives, x r) ∧ 0 < f x ∧ f x < 1 - g := by
    refine (hN.continuousAt.eventually_const_lt (by show 1 / 2 < p s + _; rw [hNp]; norm_num)).and
      ((hfc.eventually_const_lt (by rw [hfp]; linarith)).and (hfc.eventually_lt_const ?_))
    rw [hfp, hg]
    linarith
  have hsq : Tendsto (fun n : ℕ => √(n : ℝ)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
  refine tendsto_iidProb_of_imp hd ?_ (tendsto_iidProb_freq hd hF)
  filter_upwards [eventually_gt_atTop 0, hsq.eventually_ge_atTop (M * 3 / (2 * g))] with n hn0 hnM ω hω
  obtain ⟨h₁, h₂, h₃⟩ := hω
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn0
  set c := quartetCount sides ω with hc
  have hsumdiv : ∑ r ∈ s.alternatives, c r / n = (∑ r ∈ s.alternatives, c r) / n :=
    (Finset.sum_div _ _ _).symm
  have h₁' : 1 / 2 < (c s + ∑ r ∈ s.alternatives, c r) / n := by
    have : 1 / 2 < c s / n + ∑ r ∈ s.alternatives, c r / n := h₁
    rwa [hsumdiv, ← add_div] at this
  rw [lt_div_iff₀ hn'] at h₁'
  have hfe : f (fun r => c r / n) = 3 * (∑ r ∈ s.alternatives, c r) / (2 * (c s + ∑ r ∈ s.alternatives, c r)) := by
    simp only [hf]
    rw [hsumdiv, ← add_div]
    have hNpos : c s + ∑ r ∈ s.alternatives, c r ≠ 0 := by
      intro h0
      rw [h0] at h₁'
      linarith
    field_simp
  rw [hfe] at h₂ h₃
  set φ := 3 * (∑ r ∈ s.alternatives, c r) / (2 * (c s + ∑ r ∈ s.alternatives, c r)) with hφ
  have hg1 : 1 - g < 1 := by linarith
  have hphi : t1Phi c s = φ := min_eq_right (by linarith)
  rw [hphi]
  have hge := abs_muZero_ge (m := c s + ∑ r ∈ s.alternatives, c r) h₂ (by linarith)
  rw [abs_of_nonneg (muZero_nonneg_of_le_one (by linarith)),
    abs_of_nonneg (by linarith : 0 ≤ 1 - φ)] at hge
  have hroot : √(n : ℝ) ≤ √(2 * (c s + ∑ r ∈ s.alternatives, c r)) := Real.sqrt_le_sqrt (by linarith)
  rw [div_le_iff₀ (by positivity)] at hnM
  have h₄ : √(n : ℝ) * g ≤ √(2 * (c s + ∑ r ∈ s.alternatives, c r)) * (1 - φ) :=
    mul_le_mul hroot (by linarith) hg0.le (Real.sqrt_nonneg _)
  linarith

/-- Closeness in probability to an asymptotically uniform function. -/
private theorem asymptoticallyUniform_of_close (hd : IsDist dist) {f g : (n : ℕ) → (Fin n → Γ) → ℝ}
    (hg : AsymptoticallyUniform dist g)
    (h : ∀ ε : ℝ, 0 < ε → Tendsto (fun n => iidProb dist n fun ω => |f n ω - g n ω| < ε) atTop (𝓝 1)) :
    AsymptoticallyUniform dist f := by
  have key : ∀ {n : ℕ} {A B E : (Fin n → Γ) → Prop}, (∀ ω, A ω → E ω → B ω) →
      iidProb dist n A ≤ iidProb dist n B + (1 - iidProb dist n E) := by
    intro n A B E himp
    rw [← iidProb_not hd n E]
    refine (iidProb_mono hd fun ω hA => ?_).trans (iidProb_or_le hd B fun ω => ¬ E ω)
    by_cases hE : E ω
    · exact Or.inl (himp ω hA hE)
    · exact Or.inr hE
  intro x h0 h1
  refine tendsto_order.2 ⟨fun a ha => ?_, fun a ha => ?_⟩
  · by_cases ha0 : a < 0
    · exact Eventually.of_forall fun n => ha0.trans_le (iidProb_nonneg hd n _)
    push Not at ha0
    set y := (a + x) / 2 with hy
    have hlim := hg y (by rw [hy]; linarith) (by rw [hy]; linarith)
    have hclose := h ((x - a) / 2) (by linarith)
    have hay : a < y := by rw [hy]; linarith
    filter_upwards [hlim.eventually (lt_mem_nhds (by linarith : a + (y - a) / 2 < y)),
      hclose.eventually (lt_mem_nhds (by linarith : 1 - (y - a) / 2 < 1))] with n h₁ h₂
    have h₃ : iidProb dist n (fun ω => g n ω ≤ y) ≤ iidProb dist n (fun ω => f n ω ≤ x) +
        (1 - iidProb dist n fun ω => |f n ω - g n ω| < (x - a) / 2) := by
      refine key fun ω hA hE => ?_
      have := (abs_lt.1 hE).2
      rw [hy] at hA
      linarith
    linarith
  · by_cases ha1 : 1 < a
    · exact Eventually.of_forall fun n => (iidProb_le_one hd n _).trans_lt ha1
    push Not at ha1
    set y := (x + a) / 2 with hy
    have hlim := hg y (by rw [hy]; linarith) (by rw [hy]; linarith)
    have hclose := h ((a - x) / 2) (by linarith)
    have hay : y < a := by rw [hy]; linarith
    filter_upwards [hlim.eventually (gt_mem_nhds (by linarith : y < y + (a - y) / 2)),
      hclose.eventually (lt_mem_nhds (by linarith : 1 - (a - y) / 2 < 1))] with n h₁ h₂
    have h₃ : iidProb dist n (fun ω => f n ω ≤ x) ≤ iidProb dist n (fun ω => g n ω ≤ y) +
        (1 - iidProb dist n fun ω => |f n ω - g n ω| < (a - x) / 2) := by
      refine key fun ω hA hE => ?_
      have := (abs_lt.1 hE).1
      rw [hy]
      linarith
    linarith

/-- **Off its singularity, the p-value of the T3 test is asymptotically uniform.** With positive probabilities, the true
topology is the maximum likelihood one, and the T3 test distribution at the MLE tends to `χ²₁` along with the T1 test
distribution (`exists_t1Tail_lt_t3Tail_add`, `tendsto_muZero_t1Phi_large`), so it is close to the T1 p-value of that
topology. Parallel to `cutPValue_asymptoticallyUniform`. -/
theorem t3PValue_asymptoticallyUniform (hd : IsDist dist) (hs : DisplaysOne dist sides) {s : QuartetTree X}
    (hstrict : IsT1Strict (displayCF dist sides) s)
    (hpos : ∀ r ∈ s.alternatives, 0 < displayCF dist sides r) :
    AsymptoticallyUniform dist fun _ ω => t3PValue (quartetCount sides ω) s := by
  refine asymptoticallyUniform_of_close hd
    (t1PValue_asymptoticallyUniform hd hs hstrict.1 hstrict.2 hpos) fun ε hε => ?_
  obtain ⟨M, hM⟩ := exists_t1Tail_lt_t3Tail_add hε
  refine tendsto_iidProb_of_imp hd (Eventually.of_forall fun n ω hω => ?_)
    (tendsto_iidProb_and hd (tendsto_t1Stat_lt hd hs hstrict hpos)
      (tendsto_muZero_t1Phi_large hd hs hstrict hpos M))
  obtain ⟨h₁, h₂⟩ := hω
  set c := quartetCount sides ω
  have hmin : ∀ r ∈ treesOn s.taxa, t1Stat c s ≤ t1Stat c r := by
    intro r hr
    by_cases hrs : r = s
    · rw [hrs]
    · exact (h₁ r (QuartetTree.mem_alternatives.2 ⟨mem_treesOn.1 hr, hrs⟩)).le
  have he := t3Stat_eq_of_isMin s.card_taxa (mem_treesOn_taxa s) hmin
  have hp3 : t3PValue c s =
      t3Tail (t1Phi c s) (c s + ∑ r ∈ s.alternatives, c r) (t1Stat c s) := by
    unfold t3PValue
    rw [he]
  have hp1 : t1PValue c s =
      t1Tail (muZero (t1Phi c s) (c s + ∑ r ∈ s.alternatives, c r)) (t1Stat c s) := rfl
  rw [hp3, hp1]
  have h₃ := hM _ _ (t1Stat c s) (t1Phi_le_one c s) h₂
  have h₄ := t3Tail_le_t1Tail (t1Phi c s) (c s + ∑ r ∈ s.alternatives, c r) (t1Stat c s)
  exact abs_lt.2 ⟨by linarith, by linarith [hε]⟩

/-! ### Off the null -/

/-- Off the T1 null of `s`, its statistic exceeds a positive constant near the true frequencies. This is the first step
of `t1PValue_growth`. -/
theorem exists_lt_t1Stat (hd : IsDist dist) (hs : DisplaysOne dist sides) {s : QuartetTree X}
    (h : ¬ IsT1Null (displayCF dist sides) s) :
    ∃ d : ℝ, 0 < d ∧ ∀ᶠ x in 𝓝 (displayCF dist sides), d < t1Stat x s := by
  have hp0 : ∀ r, 0 ≤ displayCF dist sides r := displayCF_nonneg hd
  have hp1 := sum_displayCF_treesOn hd hs s.card_taxa
  obtain ⟨r, r', hne, halts⟩ := QuartetTree.exists_alternatives s
  have hr : r ∈ s.alternatives := by simp [halts]
  have hr' : r' ∈ s.alternatives := by simp [halts]
  have hrT := mem_treesOn_taxa_of_mem_alternatives hr
  have hrT' := mem_treesOn_taxa_of_mem_alternatives hr'
  have hsT := mem_treesOn_taxa s
  by_cases heq : displayCF dist sides r = displayCF dist sides r'
  · have hlt : displayCF dist sides s < displayCF dist sides r := by
      by_contra hcon
      push Not at hcon
      refine h ⟨fun u hu => ?_, fun u hu u' hu' => ?_⟩
      · rw [halts] at hu
        simp only [Finset.mem_insert, Finset.mem_singleton] at hu
        rcases hu with rfl | rfl
        · exact hcon
        · rw [← heq]; exact hcon
      · rw [halts] at hu hu'
        simp only [Finset.mem_insert, Finset.mem_singleton] at hu hu'
        rcases hu with rfl | rfl <;> rcases hu' with rfl | rfl
        · rfl
        · exact heq
        · exact heq.symm
        · rfl
    have hstar : 0 < starStat (displayCF dist sides) s.taxa := by
      refine starStat_pos _ hp0 s.card_taxa hp1 ?_
      by_cases hs3 : displayCF dist sides s = 1 / 3
      · exact ⟨r, hrT, fun h' => by linarith⟩
      · exact ⟨s, hsT, hs3⟩
    refine ⟨starStat (displayCF dist sides) s.taxa / 2, by positivity, ?_⟩
    have h1 : ∀ᶠ x in 𝓝 (displayCF dist sides),
        starStat (displayCF dist sides) s.taxa / 2 < starStat x s.taxa :=
      (continuous_starStat s.taxa).continuousAt.tendsto.eventually_const_lt (by linarith)
    have h2 : ∀ᶠ x : QuartetTree X → ℝ in 𝓝 (displayCF dist sides),
        x s < (x r + x r') / 2 := by
      refine ContinuousAt.eventually_lt (continuous_apply s).continuousAt
        (((continuous_apply r).add (continuous_apply r')).div_const 2).continuousAt ?_
      rw [← heq]
      linarith
    filter_upwards [h1, h2] with x hx1 hx2
    unfold t1Stat
    rw [halts, Finset.sum_pair hne, ite_eq_right (not_le.2 hx2)]
    exact hx1
  · have hline : 0 < lineStat (displayCF dist sides) s :=
      lineStat_pos _ hp0 s ⟨r, hr, r', hr', heq⟩
    have hstar : 0 < starStat (displayCF dist sides) s.taxa := by
      refine starStat_pos _ hp0 s.card_taxa hp1 ?_
      by_cases hs3 : displayCF dist sides r = 1 / 3
      · exact ⟨r', hrT', fun h' => heq (hs3.trans h'.symm)⟩
      · exact ⟨r, hrT, hs3⟩
    have hmin : 0 < min (lineStat (displayCF dist sides) s)
        (starStat (displayCF dist sides) s.taxa) := lt_min hline hstar
    refine ⟨min (lineStat (displayCF dist sides) s) (starStat (displayCF dist sides) s.taxa) / 2,
      by positivity, ?_⟩
    have h1 : ∀ᶠ x in 𝓝 (displayCF dist sides),
        min (lineStat (displayCF dist sides) s) (starStat (displayCF dist sides) s.taxa) / 2 <
          lineStat x s :=
      (continuous_lineStat s).continuousAt.tendsto.eventually_const_lt
        (by have := min_le_left (lineStat (displayCF dist sides) s)
              (starStat (displayCF dist sides) s.taxa); linarith)
    have h2 : ∀ᶠ x in 𝓝 (displayCF dist sides),
        min (lineStat (displayCF dist sides) s) (starStat (displayCF dist sides) s.taxa) / 2 <
          starStat x s.taxa :=
      (continuous_starStat s.taxa).continuousAt.tendsto.eventually_const_lt
        (by have := min_le_right (lineStat (displayCF dist sides) s)
              (starStat (displayCF dist sides) s.taxa); linarith)
    filter_upwards [h1, h2] with x hx1 hx2
    unfold t1Stat
    split_ifs
    · exact hx1
    · exact hx2

/-- **The T3 test off its null**: a non-cut concordance factor (`not_isT3Null_of_isNonCut`), or a cut one with
`q > 1/3`, the anomalous case (`not_isT3Null_of_anomalous`). There is `d > 0` such that, with probability tending to one,
the statistic exceeds `n d` and the p-value at every fitted topology is below `χ²₂` at `n d`. The proof parallels
TINNiK's proof of Theorem 4 for the cut test, as repaired in `cutTest_alternative`. The statistic is a minimum over the three
fitted half-lines, so the limit is the least of the three limits. The test distribution is not dominated by `χ²₁` here,
unlike the cut test's: it is dominated by `χ²₂`, through the T1 test distribution. -/
theorem t3Test_alternative (hd : IsDist dist) (hs : DisplaysOne dist sides) {q : Finset X} (hq : q.card = 4)
    (h : ¬ IsT3Null (displayCF dist sides) q) :
    ∃ d : ℝ, 0 < d ∧ Tendsto (fun n : ℕ => iidProb dist n fun ω =>
      n * d < t3Stat (quartetCount sides ω) q ∧
        ∀ u ∈ treesOn q, t3PValue (quartetCount sides ω) u < chiSqTwoTail (n * d)) atTop (𝓝 1) := by
  have hex : ∀ s : QuartetTree X, ∃ d : ℝ, 0 < d ∧ (s ∈ treesOn q →
      ∀ᶠ x in 𝓝 (displayCF dist sides), d < t1Stat x s) := by
    intro s
    by_cases hsq : s ∈ treesOn q
    · obtain ⟨d, hd0, hF⟩ := exists_lt_t1Stat hd hs (fun hn => h ⟨s, hsq, hn⟩)
      exact ⟨d, hd0, fun _ => hF⟩
    · exact ⟨1, one_pos, fun hn => absurd hn hsq⟩
  choose d hd0 hdF using hex
  have hne : (treesOn q).Nonempty := by
    rw [← Finset.card_pos, card_treesOn hq]
    norm_num
  obtain ⟨s₀, hs₀, hmin⟩ := Finset.exists_min_image _ d hne
  refine ⟨d s₀, hd0 s₀, ?_⟩
  have hF : ∀ᶠ x in 𝓝 (displayCF dist sides), ∀ s ∈ treesOn q, d s₀ < t1Stat x s := by
    rw [Finset.eventually_all]
    intro s hsq
    filter_upwards [hdF s hsq] with x hx
    exact (hmin s hsq).trans_lt hx
  refine tendsto_iidProb_of_imp hd ?_ (tendsto_iidProb_freq hd hF)
  filter_upwards [eventually_gt_atTop 0] with n hn0 ω hω
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn0
  have hc := quartetCount_nonneg (sides := sides) ω
  have hcmul : quartetCount sides ω = fun r => (n : ℝ) * (quartetCount sides ω r / n) := by
    funext r
    field_simp
  have hstat : (n : ℝ) * d s₀ < t3Stat (quartetCount sides ω) q := by
    obtain ⟨u, hu, he⟩ := exists_t3Stat_eq (quartetCount sides ω) hq
    rw [he, hcmul, t1Stat_const_mul hn']
    exact mul_lt_mul_of_pos_left (hω u hu) hn'
  refine ⟨hstat, fun u hu => ?_⟩
  have h₁ := t3PValue_le_chiSqTwoTail hc u
  rw [mem_treesOn.1 hu] at h₁
  refine h₁.trans_lt (Real.exp_lt_exp.2 ?_)
  linarith

/-- The T3 test rejects off its null at levels `α_n` with `log(1/α_n) = o(n)`, with probability tending to one. -/
theorem t3Test_rejects (hd : IsDist dist) (hs : DisplaysOne dist sides) {q : Finset X} (hq : q.card = 4)
    (h : ¬ IsT3Null (displayCF dist sides) q) {α : ℕ → ℝ} (hα : ∀ n, 0 < α n)
    (hαlog : Tendsto (fun n : ℕ => Real.log (α n) / n) atTop (𝓝 0)) :
    Tendsto (fun n => iidProb dist n fun ω =>
      ∀ u ∈ treesOn q, t3PValue (quartetCount sides ω) u < α n) atTop (𝓝 1) := by
  obtain ⟨d, hd0, hlim⟩ := t3Test_alternative hd hs hq h
  refine tendsto_iidProb_of_imp hd ?_ hlim
  have h1 : ∀ᶠ n : ℕ in atTop, -(d / 2) < Real.log (α n) / n :=
    hαlog.eventually (lt_mem_nhds (by linarith))
  filter_upwards [h1, eventually_gt_atTop 0] with n hn hn0 ω hω u hu
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn0
  refine (hω.2 u hu).trans_le ?_
  rw [chiSqTwoTail, ← Real.le_log_iff_exp_le (hα n)]
  have := (lt_div_iff₀ hn').mp hn
  linarith

/-! ### The nesting of the two nulls -/

/-- "The null hypothesis for T1 is nested in that for T3" (ECToBlob §10). -/
theorem isT3Null_of_isT1Null {p : QuartetTree X → ℝ} {q : Finset X} {s : QuartetTree X} (hs : s ∈ treesOn q)
    (h : IsT1Null p s) : IsT3Null p q :=
  ⟨s, hs, h⟩

/-- **The nesting, on the same reference law.** Judged against the same law, the T1 test of `s` gives a p-value at most
that of the T3 statistic, since `t3Stat ≤ t1Stat`. This is the sense of ECToBlob §10, "since the null hypothesis for T1 is
nested in that for T3". It is not a comparison of the p-values of the two tests, which use different reference laws:
see `t3PValue_le_t1PValue`. -/
theorem t1PValue_le_t1Tail_t3Stat (c : QuartetTree X → ℝ) (s : QuartetTree X) :
    t1PValue c s ≤ t1Tail (muZero (t1Phi c s) (c s + ∑ r ∈ s.alternatives, c r)) (t3Stat c s.taxa) :=
  t1Tail_anti _ (t3Stat_le_t1Stat c (mem_treesOn_taxa s))

/-- **The p-values of the two tests compare the other way at the maximum likelihood topology.** If `s` has the least T1
statistic on its taxa, the two statistics agree, and the reference law of T3 is below that of T1
(`t3Tail_le_t1Tail`). So the T3 p-value is at most the T1 p-value: whenever T1 rejects the maximum likelihood topology at a
level, T3 rejects at that level too. -/
theorem t3PValue_le_t1PValue {c : QuartetTree X → ℝ} {s : QuartetTree X}
    (hmin : ∀ r ∈ treesOn s.taxa, t1Stat c s ≤ t1Stat c r) : t3PValue c s ≤ t1PValue c s := by
  unfold t3PValue
  rw [t3Stat_eq_of_isMin s.card_taxa (mem_treesOn_taxa s) hmin]
  exact t3Tail_le_t1Tail _ _ _

/-- `t3PValue_le_t1PValue` is strict when the statistic is positive. -/
theorem t3PValue_lt_t1PValue {c : QuartetTree X → ℝ} {s : QuartetTree X}
    (hmin : ∀ r ∈ treesOn s.taxa, t1Stat c s ≤ t1Stat c r) (hpos : 0 < t1Stat c s) :
    t3PValue c s < t1PValue c s := by
  unfold t3PValue
  rw [t3Stat_eq_of_isMin s.card_taxa (mem_treesOn_taxa s) hmin]
  exact t3Tail_lt_t1Tail (by have := t1Phi_le_one c s; linarith) hpos

/-- **The T1 p-value is not always at most the T3 p-value.** On any quartet tree, take counts `(3, 2, 1)` with `s` the highest:
then `t1PValue c s > t3PValue c s`. So the statement "the T1 p-value is at most the T3 p-value" is false. -/
theorem exists_t3PValue_lt_t1PValue (s : QuartetTree X) :
    ∃ c : QuartetTree X → ℝ, (∀ r, 0 ≤ c r) ∧ t3PValue c s < t1PValue c s := by
  obtain ⟨r₁, r₂, hne, h⟩ := QuartetTree.exists_alternatives s
  obtain ⟨hs₁, hs₂, -, -, -⟩ := alternatives_taxa hne h
  set c : QuartetTree X → ℝ := fun r => if r = s then 3 else if r = r₁ then 2 else if r = r₂ then 1 else 0
    with hc
  have hc0 : ∀ r, 0 ≤ c r := by
    intro r
    simp only [hc]
    split_ifs <;> norm_num
  have hcs : c s = 3 := by simp [hc]
  have hc₁ : c r₁ = 2 := by simp [hc, hs₁.symm]
  have hc₂ : c r₂ = 1 := by simp [hc, hs₂.symm, hne.symm]
  have hmax : ∀ r ∈ s.alternatives, c r ≤ c s := by
    intro r hr
    rw [h] at hr
    simp only [Finset.mem_insert, Finset.mem_singleton] at hr
    rcases hr with rfl | rfl
    · rw [hc₁, hcs]; norm_num
    · rw [hc₂, hcs]; norm_num
  refine ⟨c, hc0, t3PValue_lt_t1PValue (fun r hr => t1Stat_le_t1Stat_of_max hc0 hmax hr) ?_⟩
  have hge := lineStat_le_t1Stat hc0 s
  rw [lineStat_eq_lineS c hne h, hc₁, hc₂] at hge
  exact (lineS_pos (by norm_num) (by norm_num) (by norm_num)).trans_le hge

/-- If the T1 test rejects `s` where the T3 test does not reject, with its fit at `s`, then `s` is not a maximum
likelihood topology. So what ECToBlob §10 calls greater power comes from samples favouring another topology. -/
theorem exists_t1Stat_lt_of_t1_rejects {c : QuartetTree X → ℝ} {s : QuartetTree X} {a : ℝ}
    (h₁ : t1PValue c s < a) (h₃ : a ≤ t3PValue c s) : ∃ r ∈ treesOn s.taxa, t1Stat c r < t1Stat c s := by
  by_contra hn
  push Not at hn
  exact absurd (h₁.trans_le h₃) (not_lt.2 (t3PValue_le_t1PValue hn))

/-- **Where the T1 test has greater power**, in the sense of ECToBlob §10: "the T1 test has greater power to give evidence
that an edge should be contracted". At a concordance factor on the T3 null, through another topology, and off the T1 null
of `s`, the T1 test of `s` rejects at the levels `α_n → 0` with `log(1/α_n) = o(n)` and the T3 test does not, with
probability tending to one. -/
theorem t1_rejects_where_t3_cannot (hd : IsDist dist) (hs : DisplaysOne dist sides) {s s' : QuartetTree X}
    (hst : s'.taxa = s.taxa) (hnull : IsT1Null (displayCF dist sides) s')
    (hpos : ∀ r ∈ s'.alternatives, 0 < displayCF dist sides r)
    (hoff : ¬ IsT1Null (displayCF dist sides) s) {α : ℕ → ℝ} (hα : ∀ n, 0 < α n)
    (hα₀ : Tendsto α atTop (𝓝 0)) (hαlog : Tendsto (fun n : ℕ => Real.log (α n) / n) atTop (𝓝 0)) :
    Tendsto (fun n => iidProb dist n fun ω =>
      t1PValue (quartetCount sides ω) s < α n ∧
        ∀ u ∈ treesOn s.taxa, α n ≤ t3PValue (quartetCount sides ω) u) atTop (𝓝 1) := by
  have hb : Tendsto (fun n : ℕ => (-2 * Real.log (α n)) / n) atTop (𝓝 0) := by
    have := hαlog.const_mul (-2)
    simp only [mul_zero] at this
    exact this.congr fun n => by ring
  have h₁ := t1PValue_growth hd hs (s := s) hoff hb
  have h₂ := t3Test_nonCollapse hd hs hnull hpos hα₀
  rw [hst] at h₂
  refine tendsto_iidProb_of_imp hd (Eventually.of_forall fun n ω hω => ⟨?_, hω.2⟩)
    (tendsto_iidProb_and hd h₁ h₂)
  have h₃ := hω.1
  rwa [show -(-2 * Real.log (α n)) / 2 = Real.log (α n) by ring, Real.exp_log (hα n)] at h₃

end Sample


end QuartetTests

/-! ### The T3 statistic looks only at the taxa -/

section Congr

open Finset

variable {c c' : QuartetTree X → ℝ} {q : Finset X}

theorem t3Stat_congr (h : ∀ r ∈ treesOn q, c r = c' r) : t3Stat c q = t3Stat c' q := by
  unfold t3Stat
  exact iInf_congr fun s => t1Stat_congr s.property h

theorem t3PValue_congr {s : QuartetTree X} (hs : s ∈ treesOn q) (h : ∀ r ∈ treesOn q, c r = c' r) :
    t3PValue c s = t3PValue c' s := by
  have halt : ∀ r ∈ s.alternatives, c r = c' r := fun r hr =>
    h r (mem_treesOn.2 ((QuartetTree.mem_alternatives.1 hr).1.trans (mem_treesOn.1 hs)))
  unfold t3PValue t1Phi
  rw [sum_congr rfl halt, h s hs, mem_treesOn.1 hs, t3Stat_congr h]

end Congr

end Phylogenetics
