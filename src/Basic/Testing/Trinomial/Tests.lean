module

public import Basic.Testing.Trinomial.Gaussian

/-!
# The limits of the quartet tests, for a trinomial sample

The p-values of the T1 test and the cut test as functions of real counts, and the limits under the
null of the three tests:

* the star test, `tendsto_star_lrt`, `tendsto_star_pearson`;
* the T1 test off its boundary, `tendsto_t1`, and at the centroid, `centroid_tight`;
* the likelihood ratio statistic of the cut model: `closeOnBalls_cutS_of_ne`,
  `closeOnBalls_cutS_centroid`;
* the cut test on a strictly cut concordance factor: its distribution tends to `χ²₁` uniformly,
  `abs_cutTail_sub_chiSqOneTail_lt`, so its p-value is asymptotically uniform, `tendsto_cut`, and it does
  not reject at levels tending to `0`, `tendsto_cut_null`.
-/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open Phylogenetics Phylogenetics.QuartetTests
open scoped ENNReal

namespace Phylogenetics.Trinomial

/-! ### The T1 test distribution -/

theorem t1Tail_le_one (μ t : ℝ) : t1Tail μ t ≤ 1 := measureReal_le_one

theorem t1Tail_anti (μ : ℝ) {s t : ℝ} (hst : s ≤ t) : t1Tail μ t ≤ t1Tail μ s :=
  measureReal_mono fun _ hz ↦ lt_of_le_of_lt hst hz

theorem cutTail_anti (φ n : ℝ) {s t : ℝ} (hst : s ≤ t) : cutTail φ n t ≤ cutTail φ n s :=
  measureReal_mono fun _ hz ↦ lt_of_le_of_lt hst hz

/-- The T1 test distribution exceeds `Z²` only when `Z̄ < 0`. -/
theorem t1Tail_le_add (μ t : ℝ) :
    t1Tail μ t ≤ chiSqOneTail t + (gaussianReal μ 1).real (Iio 0) := by
  have h₁ : chiSqOneTail t =
      ((gaussianReal 0 1).prod (gaussianReal μ 1)).real ({z : ℝ | t < z ^ 2} ×ˢ univ) := by
    rw [measureReal_prod_prod]
    simp [chiSqOneTail]
  have h₂ : (gaussianReal μ 1).real (Iio 0) =
      ((gaussianReal 0 1).prod (gaussianReal μ 1)).real (univ ×ˢ Iio 0) := by
    rw [measureReal_prod_prod]
    simp
  rw [h₁, h₂]
  refine (measureReal_mono ?_).trans (measureReal_union_le _ _)
  rintro ⟨x, y⟩ hz
  have hz' : t < x ^ 2 + if y < 0 then y ^ 2 else 0 := hz
  by_cases hy : y < 0
  · exact Or.inr ⟨mem_univ _, hy⟩
  · left
    rw [ite_eq_right hy, add_zero] at hz'
    exact ⟨hz', mem_univ _⟩

/-- The probability that `Z̄ < 0` is small when `μ` is large. -/
theorem exists_gaussianReal_Iio_lt {ε : ℝ} (hε : 0 < ε) :
    ∃ M : ℝ, ∀ μ : ℝ, M ≤ μ → (gaussianReal μ 1).real (Iio 0) < ε := by
  have h₁ : Tendsto (fun μ : ℝ ↦ (μ - 0) / √2) atTop atTop := by
    simp only [sub_zero]
    exact tendsto_id.atTop_div_const (by positivity)
  have h₂ : Tendsto (fun μ : ℝ ↦ 1 / 2 * (1 - Real.erf ((μ - 0) / √2))) atTop (𝓝 0) := by
    have := ((tendsto_const_nhds (x := (1 : ℝ)) (f := atTop (α := ℝ))).sub
      (Real.tendsto_erf_atTop.comp h₁)).const_mul (1 / 2)
    rw [show (1 / 2 : ℝ) * (1 - 1) = 0 by ring] at this
    exact this
  obtain ⟨M, hM⟩ := eventually_atTop.1 (h₂.eventually (gt_mem_nhds hε))
  refine ⟨M, fun μ hμ ↦ ?_⟩
  rw [gaussianReal_real_Iio]
  exact hM μ hμ

/-- The law of `Z̄` puts at least one half on `[0, ∞)`, for `μ ≥ 0`. -/
theorem gaussianReal_Ici_ge {μ : ℝ} (hμ : 0 ≤ μ) : 1 / 2 ≤ (gaussianReal μ 1).real (Ici 0) := by
  have h₁ : (gaussianReal μ 1).real (Ioi 0) ≤ (gaussianReal μ 1).real (Ici 0) :=
    measureReal_mono Ioi_subset_Ici_self
  rw [gaussianReal_real_Ioi] at h₁
  have h₂ : Real.erf ((0 - μ) / √2) ≤ Real.erf 0 := by
    refine Real.monotone_erf ?_
    apply div_nonpos_of_nonpos_of_nonneg <;> first | linarith | positivity
  rw [erf_zero] at h₂
  linarith

theorem measureReal_sq_le_pos {κ : ℝ} (hκ : 0 < κ) :
    0 < (gaussianReal 0 1).real {z : ℝ | z ^ 2 ≤ κ} := by
  have hpos := gaussianReal_real_Ioo_pos (show (0 : ℝ) < √κ by positivity)
  refine hpos.trans_le (measureReal_mono ?_)
  intro z hz
  have h₁ : 0 < z := hz.1
  have h₂ : z < √κ := hz.2
  have : z ^ 2 < κ := (Real.lt_sqrt h₁.le).1 h₂
  exact this.le

/-- The T1 test distribution stays away from `1`: it is below `κ` when `Z² ≤ κ` and `Z̄ ≥ 0`. -/
theorem t1Tail_le_one_sub {μ κ : ℝ} (hμ : 0 ≤ μ) :
    t1Tail μ κ ≤ 1 - 1 / 2 * (gaussianReal 0 1).real {z : ℝ | z ^ 2 ≤ κ} := by
  set B : Set (ℝ × ℝ) := {z : ℝ | z ^ 2 ≤ κ} ×ˢ Ici 0 with hB
  have hBm : MeasurableSet B :=
    (measurableSet_le (by fun_prop) measurable_const).prod measurableSet_Ici
  have hsub : {z : ℝ × ℝ | κ < z.1 ^ 2 + if z.2 < 0 then z.2 ^ 2 else 0} ⊆ Bᶜ := by
    rintro ⟨x, y⟩ hz ⟨hx, hy⟩
    have hz' : κ < x ^ 2 + if y < 0 then y ^ 2 else 0 := hz
    have hx' : x ^ 2 ≤ κ := hx
    have hy' : 0 ≤ y := hy
    rw [ite_eq_right (not_lt.2 hy')] at hz'
    linarith
  have h₁ : t1Tail μ κ ≤ 1 - ((gaussianReal 0 1).prod (gaussianReal μ 1)).real B := by
    rw [← probReal_compl_eq_one_sub hBm]
    exact measureReal_mono hsub
  have h₂ : ((gaussianReal 0 1).prod (gaussianReal μ 1)).real B =
      (gaussianReal 0 1).real {z : ℝ | z ^ 2 ≤ κ} * (gaussianReal μ 1).real (Ici 0) :=
    measureReal_prod_prod _ _
  rw [h₂] at h₁
  have h₃ := gaussianReal_Ici_ge hμ
  have h₄ : 0 ≤ (gaussianReal 0 1).real {z : ℝ | z ^ 2 ≤ κ} := measureReal_nonneg
  nlinarith

/-! ### The cut test distribution -/

/-- The cut test distribution, as the law of a function of two standard normals. -/
theorem cutTail_eq_stdPlane (φ n t : ℝ) :
    cutTail φ n t = stdPlane.real {z : ℝ × ℝ | t < min (z.1 ^ 2)
      (min ((Real.sin (alphaZero φ) * z.1 + Real.cos (alphaZero φ) * (z.2 + muZero φ n)) ^ 2)
        ((Real.sin (alphaZero φ) * z.1 - Real.cos (alphaZero φ) * (z.2 + muZero φ n)) ^ 2))} := by
  have hmap : (gaussianReal 0 1).map (fun y ↦ y + muZero φ n) = gaussianReal (muZero φ n) 1 := by
    rw [gaussianReal_map_add_const, zero_add]
  have hprod : (gaussianReal 0 1).prod (gaussianReal (muZero φ n) 1) =
      stdPlane.map (Prod.map id fun y ↦ y + muZero φ n) := by
    rw [stdPlane, ← Measure.map_prod_map _ _ measurable_id (by fun_prop), Measure.map_id, hmap]
  have hm : MeasurableSet {z : ℝ × ℝ | t < min (z.1 ^ 2)
      (min ((Real.sin (alphaZero φ) * z.1 + Real.cos (alphaZero φ) * z.2) ^ 2)
        ((Real.sin (alphaZero φ) * z.1 - Real.cos (alphaZero φ) * z.2) ^ 2))} :=
    (isOpen_lt continuous_const (by fun_prop)).measurableSet
  unfold cutTail
  rw [hprod, measureReal_def, Measure.map_apply (by fun_prop) hm, measureReal_def]
  rfl

/-- A point near `(0, μ)` is at distance at least `R` from the line `y = -(tan α) x`, when `(0, μ)` is at
distance `|μ| cos α ≥ 3 R` from it. -/
private lemma sq_le_sq_line {s c x y μ R : ℝ} (hs : |s| ≤ 1) (hc : 0 ≤ c) (hc1 : c ≤ 1) (hx : |x| < R)
    (hy : |y| < R) (hM : 3 * R ≤ c * |μ|) : x ^ 2 ≤ (s * x + c * (y + μ)) ^ 2 := by
  have h₁ : |c * y| ≤ R := by
    rw [abs_mul, abs_of_nonneg hc]
    nlinarith [abs_nonneg y]
  have h₂ : |s * x| ≤ R := by
    rw [abs_mul]
    nlinarith [abs_nonneg x, abs_nonneg s]
  have h₃ : 3 * R ≤ |c * μ| := by rwa [abs_mul, abs_of_nonneg hc]
  obtain ⟨h₄, h₅⟩ := abs_le.1 h₁
  obtain ⟨h₆, h₇⟩ := abs_le.1 h₂
  have hline : R ≤ |s * x + c * (y + μ)| := by
    rcases le_abs.1 h₃ with h | h
    · exact (by linarith : R ≤ s * x + c * (y + μ)).trans (le_abs_self _)
    · exact (by linarith : R ≤ -(s * x + c * (y + μ))).trans (neg_le_abs _)
  rw [sq_le_sq]
  exact hx.le.trans hline

/-- **The test distribution converges to `χ²₁` as its parameter runs off**, uniformly in the argument `t`
and in `φ` and `n`: its tail is within `ε` of that of `Z²` once `cos α₀ |μ₀|`, the distance from the
mean `(0, μ₀)` to the two lines `y = ± (tan α₀) x`, is large. On a box around the mean with most of the mass,
the least of the three squares is `Z²`.

Both signs of `μ₀` are covered: the anomalous concordance factors have `μ₀ → -∞`. The condition is on
`cos α₀ |μ₀|` and not on `|μ₀|` alone: `α₀ → π/2` as `φ → 3/2`, so that for fixed `n` there `|μ₀| → ∞`, while
`cos α₀ μ₀ → -√n` and the law tends to that of `min (Z², (Z - √n)², (Z + √n)²)`. -/
theorem abs_cutTail_sub_chiSqOneTail_lt {ε : ℝ} (hε : 0 < ε) :
    ∃ M : ℝ, ∀ φ n t : ℝ, M ≤ Real.cos (alphaZero φ) * |muZero φ n| →
      |cutTail φ n t - chiSqOneTail t| < ε := by
  have hε' : 0 < min ε 1 := lt_min hε one_pos
  have hc0 : 0 ≤ 1 - min ε 1 := by linarith [min_le_right ε 1]
  have hc : ENNReal.ofReal (1 - min ε 1) < stdPlane univ := by
    rw [measure_univ]
    exact ENNReal.ofReal_lt_one.2 (by linarith)
  obtain ⟨R, hR, hRc⟩ := exists_lt_measure_box stdPlane hc
  rw [univ_inter] at hRc
  have hball : 1 - min ε 1 < stdPlane.real (Metric.ball 0 R) :=
    (ENNReal.ofReal_lt_iff_lt_toReal hc0 (measure_ne_top _ _)).1 hRc
  refine ⟨3 * R, fun φ n t hM ↦ abs_lt.2 ⟨?_, ?_⟩⟩
  · set s := Real.sin (alphaZero φ) with hs
    set c := Real.cos (alphaZero φ) with hcdef
    set μ := muZero φ n with hμ
    have hc₀ : 0 ≤ c := (Real.cos_arctan_pos _).le
    have hc₁ : c ≤ 1 := Real.cos_le_one _
    have hs₁ : |s| ≤ 1 := Real.abs_sin_le_one _
    have hsub : {z : ℝ × ℝ | t < z.1 ^ 2} ⊆ {z : ℝ × ℝ | t < min (z.1 ^ 2)
        (min ((s * z.1 + c * (z.2 + μ)) ^ 2) ((s * z.1 - c * (z.2 + μ)) ^ 2))} ∪
        (Metric.ball 0 R)ᶜ := by
      rintro ⟨x, y⟩ hz
      by_cases hb : ((x, y) : ℝ × ℝ) ∈ Metric.ball (0 : ℝ × ℝ) R
      · left
        have hz' : t < x ^ 2 := hz
        obtain ⟨hx, hy⟩ := mem_ball_iff.1 hb
        have h₁ := sq_le_sq_line (μ := μ) hs₁ hc₀ hc₁ hx hy hM
        have h₂ := sq_le_sq_line (μ := μ) (s := -s) (by rwa [abs_neg]) hc₀ hc₁ hx hy hM
        have e : (-s * x + c * (y + μ)) ^ 2 = (s * x - c * (y + μ)) ^ 2 := by ring
        rw [e] at h₂
        change t < min (x ^ 2) (min ((s * x + c * (y + μ)) ^ 2) ((s * x - c * (y + μ)) ^ 2))
        rw [min_eq_left (le_min h₁ h₂)]
        exact hz'
      · exact Or.inr hb
    have h₁ := (measureReal_mono (μ := stdPlane) hsub).trans (measureReal_union_le _ _)
    rw [stdPlane_real_first, probReal_compl_eq_one_sub Metric.isOpen_ball.measurableSet,
      ← cutTail_eq_stdPlane] at h₁
    linarith [min_le_left ε 1]
  · linarith [cutTail_le_chiSqOneTail φ n t]

/-! ### The parameter of the test distributions -/

theorem abs_muZero_ge {x m : ℝ} (hx : 0 < x) (hx' : x < 3 / 2) :
    √(2 * m) * |1 - x| * (2 / 3) ≤ |muZero x m| := by
  have hy : 0 < x * (3 - 2 * x) := mul_pos hx (by linarith)
  have hd : 0 < √(x * (3 - 2 * x)) := Real.sqrt_pos.2 hy
  have hd2 : √(x * (3 - 2 * x)) ≤ 3 / 2 := by
    rw [Real.sqrt_le_left (by norm_num)]
    nlinarith [sq_nonneg (x - 3 / 4)]
  have hrw : muZero x m = √(2 * m) * (1 - x) / √(x * (3 - 2 * x)) := rfl
  rw [hrw, abs_div, abs_mul, abs_of_nonneg (Real.sqrt_nonneg _), abs_of_pos hd, le_div_iff₀ hd]
  have h₁ : 0 ≤ √(2 * m) * |1 - x| := by positivity
  nlinarith

theorem muZero_nonneg_of_le_one {x m : ℝ} (hx : x ≤ 1) : 0 ≤ muZero x m :=
  div_nonneg (mul_nonneg (Real.sqrt_nonneg _) (by linarith)) (Real.sqrt_nonneg _)

variable {φ R : ℝ}

/-- Off the centroid, the parameter at the estimate of `φ` is large. -/
theorem eventually_abs_muZero_large (hφ : 0 < φ ∧ φ < 3 / 2) (hφ1 : φ ≠ 1) (M : ℝ) :
    ∀ᶠ n : ℕ in atTop, ∀ a b c : ℝ, a + b + c = n → |(whiten φ n a b c).2| < R →
      M ≤ |muZero (3 * (b + c) / (2 * (a + b + c))) (a + b + c)| := by
  have hgap : 0 < |1 - φ| := abs_pos.2 (sub_ne_zero.2 hφ1.symm)
  set η₀ := min (min (φ / 2) ((3 / 2 - φ) / 2)) (|1 - φ| / 2) with hη₀
  have hη₀pos : 0 < η₀ := by
    refine lt_min (lt_min ?_ ?_) ?_
    · linarith [hφ.1]
    · linarith [hφ.2]
    · linarith
  have hη₁ : η₀ ≤ φ / 2 := (min_le_left _ _).trans (min_le_left _ _)
  have hη₂ : η₀ ≤ (3 / 2 - φ) / 2 := (min_le_left _ _).trans (min_le_right _ _)
  have hη₃ : η₀ ≤ |1 - φ| / 2 := min_le_right _ _
  have hsqrt : Tendsto (fun n : ℕ ↦ √(n : ℝ)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [eventually_phiHat_close hφ (R := R) hη₀pos,
    hsqrt.eventually_ge_atTop (M * 3 / |1 - φ|)] with n hn hs a b c hsum h₂
  have hclose := hn a b c hsum h₂
  obtain ⟨h₃, h₄⟩ := abs_lt.1 hclose
  set x := 3 * (b + c) / (2 * (a + b + c)) with hx
  rw [hsum] at *
  have hx0 : 0 < x := by linarith
  have hx1 : x < 3 / 2 := by linarith
  have hge := abs_muZero_ge (m := n) hx0 hx1
  have hgap₂ : |1 - φ| / 2 ≤ |1 - x| := by
    have := abs_sub_abs_le_abs_sub (1 - φ) (1 - x)
    have e : |(1 - φ) - (1 - x)| = |x - φ| := by
      congr 1
      ring
    rw [e] at this
    linarith [hclose, hη₃]
  have hs₂ : √(n : ℝ) ≤ √(2 * (n : ℝ)) := Real.sqrt_le_sqrt (by linarith [Nat.cast_nonneg (α := ℝ) n])
  rw [div_le_iff₀ hgap] at hs
  have hprod : √(n : ℝ) * (|1 - φ| / 2) ≤ √(2 * (n : ℝ)) * |1 - x| := by
    apply mul_le_mul hs₂ hgap₂ (by positivity) (Real.sqrt_nonneg _)
  linarith

/-- The cosine of the angle at the estimate of `φ`. -/
theorem eventually_cos_alphaZero_ge (hφ : 0 < φ ∧ φ < 3 / 2) :
    ∀ᶠ n : ℕ in atTop, ∀ a b c : ℝ, a + b + c = n → |(whiten φ n a b c).2| < R →
      Real.cos (alphaZero φ) / 2 ≤ Real.cos (alphaZero (3 * (b + c) / (2 * (a + b + c)))) := by
  have hpos : 0 < Real.cos (alphaZero φ) := Real.cos_arctan_pos _
  have hne : √(3 * (3 - 2 * φ)) ≠ 0 := (Real.sqrt_pos.2 (by linarith [hφ.2])).ne'
  have hcont : ContinuousAt (fun x : ℝ ↦ Real.cos (alphaZero x)) φ := by
    unfold alphaZero
    refine Real.continuous_cos.continuousAt.comp (Real.continuous_arctan.continuousAt.comp ?_)
    refine ContinuousAt.div continuousAt_const ?_ hne
    fun_prop
  have hev : ∀ᶠ x in 𝓝 φ, Real.cos (alphaZero φ) / 2 < Real.cos (alphaZero x) :=
    hcont.eventually_const_lt (by linarith)
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.1 hev
  filter_upwards [eventually_phiHat_close hφ (R := R) hδ] with n hn a b c hsum h₂
  exact (hball (by rw [Real.dist_eq]; exact hn a b c hsum h₂)).le

/-- **The test distribution at the estimate of `φ`** is close to `χ²₁`, at every argument, with
probability tending to one: the estimate is consistent, so that `|μ̂₀|` is large and `cos α̂₀` stays
away from `0`. -/
theorem eventually_abs_cutTail_estimate_sub_lt (hφ : 0 < φ ∧ φ < 3 / 2) (hφ1 : φ ≠ 1) {ε : ℝ}
    (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ a b c : ℝ, a + b + c = n → |(whiten φ n a b c).2| < R → ∀ t : ℝ,
      |cutTail (3 * (b + c) / (2 * (a + b + c))) (a + b + c) t - chiSqOneTail t| < ε := by
  obtain ⟨M, hM⟩ := abs_cutTail_sub_chiSqOneTail_lt hε
  have hc : 0 < Real.cos (alphaZero φ) := Real.cos_arctan_pos _
  filter_upwards [eventually_abs_muZero_large hφ hφ1 (2 * M / Real.cos (alphaZero φ)) (R := R),
    eventually_cos_alphaZero_ge hφ (R := R)] with n h₁ h₂ a b c hsum hb t
  refine hM _ _ _ ?_
  have h₃ := h₁ a b c hsum hb
  have h₄ := mul_le_mul_of_nonneg_right (h₂ a b c hsum hb)
    (abs_nonneg (muZero (3 * (b + c) / (2 * (a + b + c))) (a + b + c)))
  rw [div_le_iff₀ hc] at h₃
  linarith

/-! ### Statistics of samples -/

/-- The p-value of the T1 test, on real counts of the topology `s` and of its alternatives. -/
def t1PValueR (a b c : ℝ) : ℝ :=
  t1Tail (muZero (min 1 (3 * (b + c) / (2 * (a + b + c)))) (a + b + c))
    (if (b + c) / 2 ≤ a then lineS b c else starS a b c)

/-- The p-value of the cut test, on real counts of the topology `s` and of its alternatives. -/
def cutPValueR (a b c : ℝ) : ℝ :=
  cutTail (3 * (b + c) / (2 * (a + b + c))) (a + b + c)
    (min (lineS b c) (min (lineS a c) (lineS a b)))

/-- The distribution function of a statistic close to a continuous function of the whitened
frequencies. -/
theorem tendsto_iidProb_le_stat (hφ : 0 < φ ∧ φ < 3 / 2) {S : ∀ n, (Fin n → Fin 3) → ℝ}
    {T : ℝ × ℝ → ℝ} (hT : Continuous T)
    (hS : ∀ R : ℝ, 0 < R → ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, ∀ η : Fin n → Fin 3,
      |(sampleW φ η).1| < R → |(sampleW φ η).2| < R → |S n η - T (sampleW φ η)| < ε)
    {t : ℝ} (hnull : stdPlane {z | T z = t} = 0) :
    Tendsto (fun n ↦ iidProb (cutPoint φ) n fun η ↦ t ≤ S n η) atTop
      (𝓝 (stdPlane.real {z | t < T z})) := by
  refine tendsto_iidProb_of_threshold hφ hT ?_ ?_ hnull
  · intro R hR δ hδ
    filter_upwards [hS R hR δ hδ] with n hn η h₁ h₂ h₃
    have := (abs_lt.1 (hn η h₁ h₂)).1
    linarith
  · intro R hR δ hδ
    filter_upwards [hS R hR δ hδ] with n hn η h₁ h₂ h₃
    have := (abs_lt.1 (hn η h₁ h₂)).2
    linarith

private lemma iidProb_eq_zero_of_forall_not {Γ : Type*} [Fintype Γ] {dist : Γ → ℝ} {n : ℕ}
    {Ev : (Fin n → Γ) → Prop} (h : ∀ η, ¬ Ev η) : iidProb dist n Ev = 0 :=
  Finset.sum_eq_zero fun η _ ↦ ite_eq_right (h η)

/-- A p-value `exp (-S/2)` for a statistic with limit `χ²₂` is asymptotically uniform. -/
theorem tendsto_chiSqTwoTail_of_close {S : ∀ n, (Fin n → Fin 3) → ℝ}
    (hS : ∀ R : ℝ, 0 < R → ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, ∀ η : Fin n → Fin 3,
      |(sampleW 1 η).1| < R → |(sampleW 1 η).2| < R →
        |S n η - ((sampleW 1 η).1 ^ 2 + (sampleW 1 η).2 ^ 2)| < ε)
    {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 1) :
    Tendsto (fun n ↦ iidProb (cutPoint 1) n fun η ↦ chiSqTwoTail (S n η) ≤ x) atTop (𝓝 x) := by
  have hφ : (0 : ℝ) < 1 ∧ (1 : ℝ) < 3 / 2 := by norm_num
  rcases h0.eq_or_lt with rfl | hx
  · have : ∀ n, iidProb (cutPoint 1) n (fun η ↦ chiSqTwoTail (S n η) ≤ 0) = 0 := fun n ↦
      iidProb_eq_zero_of_forall_not fun η h ↦ absurd h (not_le.2 (Real.exp_pos _))
    simp only [this]
    exact tendsto_const_nhds
  set t := -2 * Real.log x with ht
  have ht0 : 0 ≤ t := by
    have := Real.log_nonpos h0 h1
    rw [ht]
    linarith
  have hiff : ∀ s : ℝ, chiSqTwoTail s ≤ x ↔ t ≤ s := by
    intro s
    unfold chiSqTwoTail
    rw [← Real.le_log_iff_exp_le hx, ht]
    constructor <;> intro h <;> linarith
  have hlim := tendsto_iidProb_le_stat hφ (T := fun z ↦ z.1 ^ 2 + z.2 ^ 2) (by fun_prop) hS
    (stdPlane_norm_null t)
  rw [stdPlane_real_norm ht0] at hlim
  have hval : chiSqTwoTail t = x := by
    unfold chiSqTwoTail
    rw [ht, show -(-2 * Real.log x) / 2 = Real.log x by ring, Real.exp_log hx]
  rw [hval] at hlim
  simpa only [hiff] using hlim

/-- **The star test, likelihood ratio.** -/
theorem tendsto_star_lrt {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 1) :
    Tendsto (fun n ↦ iidProb (cutPoint 1) n fun η ↦
      chiSqTwoTail (starS (count η 0) (count η 1) (count η 2)) ≤ x) atTop (𝓝 x) := by
  refine tendsto_chiSqTwoTail_of_close
    (S := fun n η ↦ starS (count η 0) (count η 1) (count η 2)) ?_ h0 h1
  intro R hR ε hε
  filter_upwards [eventually_starS_centroid hR hε] with n hn η h₁ h₂
  exact hn _ _ _ (count_add η) h₁ h₂

/-- **The star test, Pearson.** -/
theorem tendsto_star_pearson {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 1) :
    Tendsto (fun n ↦ iidProb (cutPoint 1) n fun η ↦
      chiSqTwoTail (pearsonS (count η 0) (count η 1) (count η 2)) ≤ x) atTop (𝓝 x) := by
  refine tendsto_chiSqTwoTail_of_close
    (S := fun n η ↦ pearsonS (count η 0) (count η 1) (count η 2)) ?_ h0 h1
  intro R hR ε hε
  filter_upwards [eventually_gt_atTop 0] with n hn0 η h₁ h₂
  rw [pearsonS_centroid hn0 (count_add η)]
  simpa [sampleW] using hε

theorem t1PValueR_pos (a b c : ℝ) : 0 < t1PValueR a b c :=
  (chiSqOneTail_pos _).trans_le (chiSqOneTail_le_t1Tail _ _)

/-- The T1 p-value is close to the `χ²₁` tail, off the boundary. -/
theorem eventually_t1PValueR_le (hφ : 0 < φ ∧ φ < 3 / 2) (hφ1 : φ < 1) {err : ℝ} (herr : 0 < err) :
    ∀ᶠ n : ℕ in atTop, ∀ a b c : ℝ, a + b + c = n → |(whiten φ n a b c).2| < R →
      t1PValueR a b c = t1Tail (muZero (3 * (b + c) / (2 * (a + b + c))) (a + b + c)) (lineS b c) ∧
      t1PValueR a b c < chiSqOneTail (lineS b c) + err := by
  obtain ⟨M, hM⟩ := exists_gaussianReal_Iio_lt herr
  filter_upwards [eventually_abs_muZero_large hφ hφ1.ne M,
    eventually_first_most_frequent hφ hφ1 (R := R), eventually_gt_atTop 0] with n h₁ h₂ hn0 a b c hsum h
  have hfreq := h₂ a b c hsum h
  have hN : 0 < a + b + c := by
    rw [hsum]
    exact_mod_cast hn0
  have hle : 3 * (b + c) / (2 * (a + b + c)) ≤ 1 := by
    rw [div_le_one (by positivity)]
    linarith
  have hrew : t1PValueR a b c =
      t1Tail (muZero (3 * (b + c) / (2 * (a + b + c))) (a + b + c)) (lineS b c) := by
    unfold t1PValueR
    rw [min_eq_right hle, ite_eq_left hfreq]
  refine ⟨hrew, ?_⟩
  rw [hrew]
  have hμ := h₁ a b c hsum h
  rw [abs_of_nonneg (muZero_nonneg_of_le_one hle)] at hμ
  exact (t1Tail_le_add _ _).trans_lt (by linarith [hM _ hμ])

/-- **The T1 test, off the boundary.** -/
theorem tendsto_t1 (hφ : 0 < φ ∧ φ < 3 / 2) (hφ1 : φ < 1) {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 1) :
    Tendsto (fun n ↦ iidProb (cutPoint φ) n fun η ↦
      t1PValueR (count η 0) (count η 1) (count η 2) ≤ x) atTop (𝓝 x) := by
  rcases h0.eq_or_lt with rfl | hx
  · have : ∀ n, iidProb (cutPoint φ) n
        (fun η ↦ t1PValueR (count η 0) (count η 1) (count η 2) ≤ 0) = 0 := fun n ↦
      iidProb_eq_zero_of_forall_not fun η h ↦ absurd h (not_le.2 (t1PValueR_pos _ _ _))
    simp only [this]
    exact tendsto_const_nhds
  obtain ⟨t, ht0, htx⟩ := exists_chiSqOneTail_eq hx h1
  have hlim : Tendsto (fun n ↦ iidProb (cutPoint φ) n fun η ↦
      t1PValueR (count η 0) (count η 1) (count η 2) ≤ x) atTop
      (𝓝 (stdPlane.real {z | t < z.1 ^ 2})) := by
    refine tendsto_iidProb_of_threshold hφ (T := fun z ↦ z.1 ^ 2) (by fun_prop) ?_ ?_
      (stdPlane_first_null t)
    · intro R hR δ hδ
      have hlt : chiSqOneTail (t + δ / 2) < x := by
        rw [← htx]
        exact chiSqOneTail_lt_of_lt ht0 (by linarith)
      filter_upwards [eventually_lineS_first hφ hR (half_pos hδ),
        eventually_t1PValueR_le hφ hφ1 (R := R) (sub_pos.2 hlt)] with n h₁ h₂ η hη₁ hη₂ hη₃
      obtain ⟨-, h₃⟩ := h₂ _ _ _ (count_add η) hη₂
      have h₄ := (abs_lt.1 (h₁ _ _ _ (count_add η) hη₁ hη₂)).1
      have h₅ : t + δ / 2 ≤ lineS (count η 1) (count η 2) := by
        have : t + δ < (whiten φ n (count η 0) (count η 1) (count η 2)).1 ^ 2 := hη₃
        linarith
      have := chiSqOneTail_anti h₅
      linarith
    · intro R hR δ hδ
      have herr : (0 : ℝ) < 1 := one_pos
      filter_upwards [eventually_lineS_first hφ hR (half_pos hδ),
        eventually_t1PValueR_le hφ hφ1 (R := R) herr] with n h₁ h₂ η hη₁ hη₂ hη₃ hle
      obtain ⟨h₃, -⟩ := h₂ _ _ _ (count_add η) hη₂
      have h₄ := (abs_lt.1 (h₁ _ _ _ (count_add η) hη₁ hη₂)).2
      have hη₃' : (whiten φ n (count η 0) (count η 1) (count η 2)).1 ^ 2 < t - δ := hη₃
      have h₅ : lineS (count η 1) (count η 2) ≤ t - δ / 2 := by linarith
      have h₆ : 0 ≤ t - δ / 2 := by
        nlinarith [sq_nonneg (whiten φ n (count η 0) (count η 1) (count η 2)).1]
      have h₇ : chiSqOneTail t < chiSqOneTail (t - δ / 2) :=
        chiSqOneTail_lt_of_lt h₆ (by linarith)
      have h₈ := chiSqOneTail_anti h₅
      have h₉ := chiSqOneTail_le_t1Tail
        (muZero (3 * (count η 1 + count η 2) / (2 * (count η 0 + count η 1 + count η 2)))
          (count η 0 + count η 1 + count η 2)) (lineS (count η 1) (count η 2))
      rw [h₃] at hle
      linarith
  rwa [stdPlane_real_first, htx] at hlim

lemma sq_lt_of_abs_lt {x R : ℝ} (hx : |x| < R) : x ^ 2 < R ^ 2 := by
  rw [← sq_abs x]
  exact pow_lt_pow_left₀ hx (abs_nonneg x) two_ne_zero

/-- **The T1 test at the centroid**: its p-value stays away from `0` and from `1`. -/
theorem centroid_tight {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ δ < 1 / 2 ∧ ∀ᶠ n : ℕ in atTop, 1 - ε < iidProb (cutPoint 1) n fun η ↦
      δ ≤ t1PValueR (count η 0) (count η 1) (count η 2) ∧
        t1PValueR (count η 0) (count η 1) (count η 2) ≤ 1 - δ := by
  have hφ : (0 : ℝ) < 1 ∧ (1 : ℝ) < 3 / 2 := by norm_num
  set ε' := min ε (1 / 2) with hε'
  have hε'pos : 0 < ε' := lt_min hε (by norm_num)
  have hε'1 : ε' ≤ 1 / 2 := min_le_right _ _
  have hε'2 : ε' ≤ ε := min_le_left _ _
  obtain ⟨κ₀, hκ₀, hF⟩ := exists_chiSqOneTail_gt hε'pos
  set κ := κ₀ / 2 with hκ
  have hκpos : 0 < κ := by positivity
  have hV : 1 - ε' < stdPlane.real {z : ℝ × ℝ | κ₀ < z.1 ^ 2} := by rwa [stdPlane_real_first]
  have hc0 : 0 ≤ 1 - ε' := by linarith
  obtain ⟨R, hR, hRc⟩ := exists_lt_measure_box stdPlane
    ((ENNReal.ofReal_lt_iff_lt_toReal hc0 (measure_ne_top _ _)).2 hV)
  have hopen : IsOpen ({z : ℝ × ℝ | κ₀ < z.1 ^ 2} ∩ Metric.ball 0 R) :=
    (isOpen_lt continuous_const (by fun_prop)).inter Metric.isOpen_ball
  set K := 2 * R ^ 2 + 1 with hK
  set δ := min (min (chiSqOneTail K) (1 / 2 * (gaussianReal 0 1).real {z : ℝ | z ^ 2 ≤ κ})) (1 / 4)
    with hδ
  have hmass := measureReal_sq_le_pos hκpos
  refine ⟨δ, lt_min (lt_min (chiSqOneTail_pos K) (by positivity)) (by norm_num),
    lt_of_le_of_lt (min_le_right _ _) (by norm_num), ?_⟩
  have hδ₁ : δ ≤ chiSqOneTail K := (min_le_left _ _).trans (min_le_left _ _)
  have hδ₂ : δ ≤ 1 / 2 * (gaussianReal 0 1).real {z : ℝ | z ^ 2 ≤ κ} :=
    (min_le_left _ _).trans (min_le_right _ _)
  have hε₁ : 0 < min κ 1 := lt_min hκpos one_pos
  have hmain : ∀ᶠ n : ℕ in atTop, 1 - ε' < iidProb (cutPoint 1) n fun η ↦
      δ ≤ t1PValueR (count η 0) (count η 1) (count η 2) ∧
        t1PValueR (count η 0) (count η 1) (count η 2) ≤ 1 - δ := by
    refine eventually_lt_iidProb hφ hopen ?_
      ((ENNReal.ofReal_lt_iff_lt_toReal hc0 (measure_ne_top _ _)).1 hRc)
    filter_upwards [eventually_lineS_first hφ hR hε₁, eventually_starS_centroid hR hε₁]
      with n h₁ h₂ η hη
    obtain ⟨hη₁, hη₂⟩ := mem_ball_iff.1 hη.2
    have hη₃ : κ₀ < (whiten 1 n (count η 0) (count η 1) (count η 2)).1 ^ 2 := hη.1
    have hη₁' : |(whiten 1 n (count η 0) (count η 1) (count η 2)).1| < R := hη₁
    have hη₂' : |(whiten 1 n (count η 0) (count η 1) (count η 2)).2| < R := hη₂
    have hl := abs_lt.1 (h₁ _ _ _ (count_add η) hη₁' hη₂')
    have hs := abs_lt.1 (h₂ _ _ _ (count_add η) hη₁' hη₂')
    have hsq₁ := sq_lt_of_abs_lt hη₁'
    have hsq₂ := sq_lt_of_abs_lt hη₂'
    have hsq₃ := sq_nonneg (whiten 1 n (count η 0) (count η 1) (count η 2)).2
    have hmin₁ : min κ 1 ≤ κ := min_le_left _ _
    have hmin₂ : min κ 1 ≤ 1 := min_le_right _ _
    have hκ₀ : κ₀ = 2 * κ := by rw [hκ]; ring
    set S := if (count η 1 + count η 2) / 2 ≤ count η 0 then lineS (count η 1) (count η 2)
      else starS (count η 0) (count η 1) (count η 2) with hS
    have hSb : κ ≤ S ∧ S ≤ K := by
      rw [hS]
      split_ifs <;> constructor <;> nlinarith [hl.1, hl.2, hs.1, hs.2]
    set μ := muZero (min 1 (3 * (count η 1 + count η 2) / (2 * (count η 0 + count η 1 + count η 2))))
      (count η 0 + count η 1 + count η 2) with hμ
    have hG : t1PValueR (count η 0) (count η 1) (count η 2) = t1Tail μ S := rfl
    have hμ0 : 0 ≤ μ := muZero_nonneg_of_le_one (min_le_left _ _)
    rw [hG]
    constructor
    · exact hδ₁.trans ((chiSqOneTail_anti hSb.2).trans (chiSqOneTail_le_t1Tail _ _))
    · have := t1Tail_anti μ hSb.1
      have := t1Tail_le_one_sub (κ := κ) hμ0
      linarith
  filter_upwards [hmain] with n hn
  linarith

/-! ### The cut model statistic -/

/-- The likelihood ratio statistic of the cut model: the least of the statistics of its three
lines. -/
def cutS (a b c : ℝ) : ℝ := min (lineS b c) (min (lineS a c) (lineS a b))

/-- Off the centroid, the statistic of the cut model is `Z²` in the limit. -/
theorem closeOnBalls_cutS_of_ne (hφ : 0 < φ ∧ φ < 3 / 2) (hφ1 : φ ≠ 1) :
    CloseOnBalls (fun (n : ℕ) (η : Fin n → Fin 3) ↦ sampleW φ η)
      (fun (n : ℕ) (η : Fin n → Fin 3) ↦ cutS (count η 0) (count η 1) (count η 2))
      (fun z ↦ z.1 ^ 2) := by
  intro R hR ε hε
  filter_upwards [eventually_lineS_first hφ hR (lt_min hε one_pos),
    eventually_lineS_other_large hφ hφ1 hR (R ^ 2 + 1)] with n h₁ h₂ η hη₁ hη₂
  have hη₁' : |(whiten φ n (count η 0) (count η 1) (count η 2)).1| < R := hη₁
  have hη₂' : |(whiten φ n (count η 0) (count η 1) (count η 2)).2| < R := hη₂
  have hl := abs_lt.1 (h₁ _ _ _ (count_add η) hη₁' hη₂')
  have hsq := sq_lt_of_abs_lt hη₁'
  have hm₁ : min ε 1 ≤ ε := min_le_left _ _
  have hm₂ : min ε 1 ≤ 1 := min_le_right _ _
  have hline : lineS (count η 1) (count η 2) < R ^ 2 + 1 := by linarith [hl.2]
  obtain ⟨h₆, h₇⟩ := h₂ _ _ _ (count_add η) hη₁' hη₂'
  have hcut : cutS (count η 0) (count η 1) (count η 2) = lineS (count η 1) (count η 2) := by
    unfold cutS
    rw [min_eq_left (le_min (hline.trans h₆).le (hline.trans h₇).le)]
  rw [hcut]
  exact (h₁ _ _ _ (count_add η) hη₁' hη₂').trans_le hm₁

/-- The limit of the statistic of the cut model at the centroid: the least squared distance to the
three lines. -/
def centroidLimit (z : ℝ × ℝ) : ℝ :=
  min (z.1 ^ 2) (min ((1 / 2 * z.1 + √3 / 2 * z.2) ^ 2) ((1 / 2 * z.1 - √3 / 2 * z.2) ^ 2))

theorem continuous_centroidLimit : Continuous centroidLimit := by
  unfold centroidLimit
  fun_prop

lemma abs_min_sub_min_lt {x x' y y' ε : ℝ} (hx : |x - x'| < ε) (hy : |y - y'| < ε) :
    |min x y - min x' y'| < ε := by
  have h := abs_min_sub_min_le_max x y x' y'
  exact h.trans_lt (max_lt hx hy)

/-- At the centroid, the statistic of the cut model is close to the limit. -/
theorem closeOnBalls_cutS_centroid :
    CloseOnBalls (fun (n : ℕ) (η : Fin n → Fin 3) ↦ sampleW 1 η)
      (fun (n : ℕ) (η : Fin n → Fin 3) ↦ cutS (count η 0) (count η 1) (count η 2)) centroidLimit := by
  have hφ : (0 : ℝ) < 1 ∧ (1 : ℝ) < 3 / 2 := by norm_num
  intro R hR ε hε
  filter_upwards [eventually_lineS_first hφ hR hε, eventually_lineS_second_centroid hR hε,
    eventually_lineS_third_centroid hR hε] with n h₁ h₂ h₃ η hη₁ hη₂
  exact abs_min_sub_min_lt (h₁ _ _ _ (count_add η) hη₁ hη₂)
    (abs_min_sub_min_lt (h₂ _ _ _ (count_add η) hη₁ hη₂) (h₃ _ _ _ (count_add η) hη₁ hη₂))

/-! ### The cut test on a strictly cut concordance factor -/

/-- `tendsto_cut` at the positive levels: each is the tail of `χ²₁` at a threshold `t` of the limit `Z²`. -/
private theorem tendsto_cut_of_pos (hφ : 0 < φ ∧ φ < 3 / 2) (hφ1 : φ ≠ 1) {x : ℝ} (hx : 0 < x)
    (h1 : x ≤ 1) :
    Tendsto (fun n ↦ iidProb (cutPoint φ) n fun η ↦
      cutPValueR (count η 0) (count η 1) (count η 2) ≤ x) atTop (𝓝 x) := by
  obtain ⟨t, ht0, htx⟩ := exists_chiSqOneTail_eq hx h1
  have hclose := closeOnBalls_cutS_of_ne hφ hφ1
  have hlim : Tendsto (fun n ↦ iidProb (cutPoint φ) n fun η ↦
      cutPValueR (count η 0) (count η 1) (count η 2) ≤ x) atTop
      (𝓝 (stdPlane.real {z | t < z.1 ^ 2})) := by
    refine tendsto_iidProb_of_threshold hφ (T := fun z ↦ z.1 ^ 2) (by fun_prop) ?_ ?_
      (stdPlane_first_null t)
    · intro R hR δ hδ
      filter_upwards [hclose R hR δ hδ] with n hn η hη₁ hη₂ hη₃
      have h₄ : |cutS (count η 0) (count η 1) (count η 2) - (sampleW φ η).1 ^ 2| < δ :=
        hn η hη₁ hη₂
      have hη₃' : t + δ < (sampleW φ η).1 ^ 2 := hη₃
      have h₅ : t ≤ cutS (count η 0) (count η 1) (count η 2) := by
        linarith [(abs_lt.1 h₄).1]
      exact (cutTail_le_chiSqOneTail _ _ _).trans ((chiSqOneTail_anti h₅).trans_eq htx)
    · intro R hR δ hδ
      by_cases hδt : t - δ < 0
      · refine Eventually.of_forall fun n η _ _ hη₃ ↦ ?_
        have hη₃' : (sampleW φ η).1 ^ 2 < t - δ := hη₃
        exact absurd (sq_nonneg (sampleW φ η).1) (not_le.2 (hη₃'.trans hδt))
      have h₆ : chiSqOneTail t < chiSqOneTail (t - δ / 2) :=
        chiSqOneTail_lt_of_lt (by linarith) (by linarith)
      filter_upwards [hclose R hR (δ / 2) (half_pos hδ),
        eventually_abs_cutTail_estimate_sub_lt hφ hφ1 (R := R) (sub_pos.2 h₆)]
        with n h₁ h₂ η hη₁ hη₂ hη₃ hle
      have h₃ : |cutS (count η 0) (count η 1) (count η 2) - (sampleW φ η).1 ^ 2| < δ / 2 :=
        h₁ η hη₁ hη₂
      have hη₃' : (sampleW φ η).1 ^ 2 < t - δ := hη₃
      have h₄ : cutS (count η 0) (count η 1) (count η 2) ≤ t - δ / 2 := by
        linarith [(abs_lt.1 h₃).2]
      have h₅ := (abs_lt.1 (h₂ _ _ _ (count_add η) hη₂
        (cutS (count η 0) (count η 1) (count η 2)))).1
      have h₇ := chiSqOneTail_anti h₄
      have hle' : cutTail (3 * (count η 1 + count η 2) /
          (2 * (count η 0 + count η 1 + count η 2))) (count η 0 + count η 1 + count η 2)
          (cutS (count η 0) (count η 1) (count η 2)) ≤ x := hle
      linarith
  rwa [stdPlane_real_first, htx] at hlim

/-- **The cut test on a strictly cut concordance factor: its p-value is asymptotically uniform.** The
statistic tends to `Z²`, and the test distribution at the estimate of `φ` to `χ²₁`. -/
theorem tendsto_cut (hφ : 0 < φ ∧ φ < 3 / 2) (hφ1 : φ ≠ 1) {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 1) :
    Tendsto (fun n ↦ iidProb (cutPoint φ) n fun η ↦
      cutPValueR (count η 0) (count η 1) (count η 2) ≤ x) atTop (𝓝 x) := by
  rcases h0.eq_or_lt with rfl | hx
  · have hd := cutPoint_isDist hφ
    refine tendsto_order.2 ⟨fun c hc ↦ Eventually.of_forall fun n ↦
      hc.trans_le (iidProb_nonneg hd n _), fun c hc ↦ ?_⟩
    have hy : 0 < min c 1 := lt_min hc one_pos
    have h := tendsto_cut_of_pos hφ hφ1 (half_pos hy) (by linarith [min_le_right c 1])
    filter_upwards [h.eventually (gt_mem_nhds (by linarith [min_le_left c 1] : min c 1 / 2 < c))]
      with n hn
    exact (iidProb_mono hd fun η hη ↦ hη.trans (half_pos hy).le).trans_lt hn
  · exact tendsto_cut_of_pos hφ hφ1 hx h1

/-- **The cut test on a strictly cut concordance factor**: the line of the first topology has the
least statistic with probability tending to one, and for any levels `α_n → 0` the test does not
reject, since its p-value is asymptotically uniform (`tendsto_cut`). -/
theorem tendsto_cut_null (hφ : 0 < φ ∧ φ < 3 / 2) (hφ1 : φ ≠ 1) {α : ℕ → ℝ}
    (hα : Tendsto α atTop (𝓝 0)) :
    Tendsto (fun n ↦ iidProb (cutPoint φ) n fun η ↦
      (lineS (count η 1) (count η 2) < lineS (count η 0) (count η 2) ∧
        lineS (count η 1) (count η 2) < lineS (count η 0) (count η 1)) ∧
      α n ≤ cutPValueR (count η 0) (count η 1) (count η 2)) atTop (𝓝 1) := by
  have hd := cutPoint_isDist hφ
  have hline : Tendsto (fun n ↦ iidProb (cutPoint φ) n fun η ↦
      lineS (count η 1) (count η 2) < lineS (count η 0) (count η 2) ∧
        lineS (count η 1) (count η 2) < lineS (count η 0) (count η 1)) atTop (𝓝 1) := by
    refine tendsto_iidProb_one hφ fun R hR ↦ ?_
    filter_upwards [eventually_lineS_first hφ hR one_pos,
      eventually_lineS_other_large hφ hφ1 hR (R ^ 2 + 1)] with n h₁ h₂ η hη₁ hη₂
    have hη₁' : |(whiten φ n (count η 0) (count η 1) (count η 2)).1| < R := hη₁
    have hη₂' : |(whiten φ n (count η 0) (count η 1) (count η 2)).2| < R := hη₂
    have hl := abs_lt.1 (h₁ _ _ _ (count_add η) hη₁' hη₂')
    have hsq := sq_lt_of_abs_lt hη₁'
    have hK : lineS (count η 1) (count η 2) < R ^ 2 + 1 := by linarith [hl.2]
    obtain ⟨h₃, h₄⟩ := h₂ _ _ _ (count_add η) hη₁' hη₂'
    exact ⟨hK.trans h₃, hK.trans h₄⟩
  have hlevel : Tendsto (fun n ↦ iidProb (cutPoint φ) n fun η ↦
      α n ≤ cutPValueR (count η 0) (count η 1) (count η 2)) atTop (𝓝 1) := by
    refine tendsto_order.2 ⟨fun c hc ↦ ?_, fun c hc ↦
      Eventually.of_forall fun n ↦ (iidProb_le_one hd n _).trans_lt hc⟩
    have hc' : 0 < 1 - c := sub_pos.2 hc
    set y := min ((1 - c) / 2) 1 with hy
    have hy₀ : 0 < y := lt_min (half_pos hc') one_pos
    have hy₁ : y ≤ 1 := min_le_right _ _
    have hy₂ : y < 1 - c := (min_le_left _ _).trans_lt (by linarith)
    filter_upwards [(tendsto_cut hφ hφ1 hy₀.le hy₁).eventually (gt_mem_nhds hy₂),
      hα.eventually (gt_mem_nhds hy₀)] with n h₁ h₂
    have h₃ := iidProb_not hd n fun η ↦ cutPValueR (count η 0) (count η 1) (count η 2) ≤ y
    have h₄ : iidProb (cutPoint φ) n (fun η ↦ ¬ cutPValueR (count η 0) (count η 1) (count η 2) ≤ y) ≤
        iidProb (cutPoint φ) n fun η ↦ α n ≤ cutPValueR (count η 0) (count η 1) (count η 2) :=
      iidProb_mono hd fun η hη ↦ h₂.le.trans (not_le.1 hη).le
    linarith
  have h := tendsto_iidProb_forall hd (ι := Bool) (fun b n η ↦ if b = true then
      lineS (count η 1) (count η 2) < lineS (count η 0) (count η 2) ∧
        lineS (count η 1) (count η 2) < lineS (count η 0) (count η 1)
      else α n ≤ cutPValueR (count η 0) (count η 1) (count η 2))
    (by intro b; cases b <;> simpa)
  refine tendsto_iidProb_of_imp hd (Eventually.of_forall fun n η hη ↦ ?_) h
  exact ⟨by simpa using hη true, by simpa using hη false⟩

end Phylogenetics.Trinomial
