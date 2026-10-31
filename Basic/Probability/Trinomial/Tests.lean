module

public import Basic.Probability.Trinomial.Gaussian

/-!
# The limits of the quartet tests, for a trinomial sample

The p-values of the T1 test and the cut test as functions of real counts, and the limits under the
null of the three tests:

* the star test, `tendsto_star_lrt`, `tendsto_star_pearson`;
* the T1 test off its boundary, `tendsto_t1`, and at the centroid, `centroid_tight`;
* the cut test on a strictly cut concordance factor, `tendsto_cut_null`;
* the likelihood ratio statistic of the cut model: `closeOnBalls_cutS_of_ne`,
  `closeOnBalls_cutS_centroid`.
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

/-- `Z²` is at most the variable of the T1 test distribution. -/
theorem chiSqOneTail_le_t1Tail' (μ t : ℝ) : chiSqOneTail t ≤ t1Tail μ t := by
  have h : chiSqOneTail t =
      ((gaussianReal 0 1).prod (gaussianReal μ 1)).real ({z : ℝ | t < z ^ 2} ×ˢ univ) := by
    rw [measureReal_prod_prod]
    simp [chiSqOneTail]
  rw [h]
  refine measureReal_mono ?_
  rintro ⟨x, y⟩ ⟨hx, -⟩
  have hx' : t < x ^ 2 := hx
  change t < x ^ 2 + if y < 0 then y ^ 2 else 0
  split_ifs <;> nlinarith [sq_nonneg y]

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

/-- A shift of the standard normal, on an interval around the mean. -/
theorem gaussianReal_real_abs_sub_lt (μ : ℝ) :
    (gaussianReal μ 1).real {z : ℝ | |z - μ| < 1} = (gaussianReal 0 1).real (Ioo (-1) 1) := by
  have hmap : (gaussianReal 0 1).map (fun x ↦ x + μ) = gaussianReal μ 1 := by
    rw [gaussianReal_map_add_const, zero_add]
  have hm : MeasurableSet {z : ℝ | |z - μ| < 1} := measurableSet_lt (by fun_prop) measurable_const
  rw [← hmap, measureReal_def, measureReal_def, Measure.map_apply (by fun_prop) hm]
  congr 2
  ext x
  simp only [mem_preimage, mem_ofPred_eq, mem_Ioo, abs_lt]
  constructor
  · rintro ⟨h₁, h₂⟩
    exact ⟨by linarith, by linarith⟩
  · rintro ⟨h₁, h₂⟩
    exact ⟨by linarith, by linarith⟩

/-- The cut test distribution has a uniform positive tail at `K` when `|μ₀|` is large and `cos α₀`
is bounded below: there the three lines are far from `Z̄`, unless it is close to `Z = 0`. -/
theorem cutTail_ge {K c₀ : ℝ} (hK : 0 ≤ K) (hc₀ : 0 < c₀) :
    ∃ δ M : ℝ, 0 < δ ∧ ∀ φ n : ℝ, c₀ ≤ Real.cos (alphaZero φ) → M ≤ |muZero φ n| →
      δ ≤ cutTail φ n K := by
  set r := √K with hr
  have hr0 : 0 ≤ r := Real.sqrt_nonneg K
  have hrK : r ^ 2 = K := Real.sq_sqrt hK
  refine ⟨(gaussianReal 0 1).real (Ioo r (r + 1)) * (gaussianReal 0 1).real (Ioo (-1) 1),
    1 + (2 * r + 2) / c₀, mul_pos (gaussianReal_real_Ioo_pos (by linarith))
      (gaussianReal_real_Ioo_pos (by norm_num)), fun φ n hcos hμ ↦ ?_⟩
  set μ := muZero φ n with hμdef
  rw [← gaussianReal_real_abs_sub_lt μ, ← measureReal_prod_prod]
  unfold cutTail
  rw [← hμdef]
  refine measureReal_mono ?_
  rintro ⟨x, y⟩ ⟨hx, hy⟩
  have hx₁ : r < x := hx.1
  have hx₂ : x < r + 1 := hx.2
  have hy' : |y - μ| < 1 := hy
  -- the lower bound on `|y|`
  have hμy : |μ| ≤ |y| + 1 := by
    have := abs_sub_abs_le_abs_sub μ y
    rw [abs_sub_comm μ y] at this
    linarith
  have hcy : (2 * r + 2) ≤ c₀ * |y| := by
    have h₁ : (2 * r + 2) / c₀ ≤ |y| := by linarith
    rw [div_le_iff₀ hc₀] at h₁
    linarith
  set a := alphaZero φ with ha
  have hcosy : 2 * r + 2 ≤ Real.cos a * |y| :=
    hcy.trans (mul_le_mul_of_nonneg_right hcos (abs_nonneg y))
  have hcosabs : Real.cos a * |y| = |Real.cos a * y| := by
    rw [abs_mul, abs_of_pos (hc₀.trans_le hcos)]
  have hsinx : |Real.sin a * x| ≤ r + 1 := by
    rw [abs_mul]
    have h₁ := Real.abs_sin_le_one a
    have h₂ : |x| ≤ r + 1 := by
      rw [abs_le]
      constructor <;> linarith
    calc |Real.sin a| * |x| ≤ 1 * (r + 1) := by gcongr
      _ = r + 1 := one_mul _
  have hsq : ∀ u : ℝ, r < |u| → K < u ^ 2 := by
    intro u hu
    rw [← hrK, ← sq_abs u]
    exact pow_lt_pow_left₀ hu hr0 two_ne_zero
  change K < min (x ^ 2)
    (min ((Real.sin a * x + Real.cos a * y) ^ 2) ((Real.sin a * x - Real.cos a * y) ^ 2))
  refine lt_min ?_ (lt_min ?_ ?_)
  · exact hsq x (by rw [abs_of_pos (by linarith)]; exact hx₁)
  · apply hsq
    have := abs_sub_abs_le_abs_sub (Real.cos a * y) (-(Real.sin a * x))
    rw [abs_neg, sub_neg_eq_add, add_comm] at this
    linarith
  · apply hsq
    have := abs_sub_abs_le_abs_sub (Real.cos a * y) (Real.sin a * x)
    rw [abs_sub_comm] at this
    linarith

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
  (chiSqOneTail_pos _).trans_le (chiSqOneTail_le_t1Tail' _ _)

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
      have h₉ := chiSqOneTail_le_t1Tail'
        (muZero (3 * (count η 1 + count η 2) / (2 * (count η 0 + count η 1 + count η 2)))
          (count η 0 + count η 1 + count η 2)) (lineS (count η 1) (count η 2))
      rw [h₃] at hle
      linarith
  rwa [stdPlane_real_first, htx] at hlim

private lemma sq_lt_of_abs_lt {x R : ℝ} (hx : |x| < R) : x ^ 2 < R ^ 2 := by
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
    · exact hδ₁.trans ((chiSqOneTail_anti hSb.2).trans (chiSqOneTail_le_t1Tail' _ _))
    · have := t1Tail_anti μ hSb.1
      have := t1Tail_le_one_sub (κ := κ) hμ0
      linarith
  filter_upwards [hmain] with n hn
  linarith

/-- **The cut test on a strictly cut concordance factor**: the line of the first topology has the
least statistic with probability tending to one, and for any levels `α_n → 0` the test does not
reject. -/
theorem tendsto_cut_null (hφ : 0 < φ ∧ φ < 3 / 2) (hφ1 : φ ≠ 1) {α : ℕ → ℝ}
    (hα : Tendsto α atTop (𝓝 0)) :
    Tendsto (fun n ↦ iidProb (cutPoint φ) n fun η ↦
      (lineS (count η 1) (count η 2) < lineS (count η 0) (count η 2) ∧
        lineS (count η 1) (count η 2) < lineS (count η 0) (count η 1)) ∧
      α n ≤ cutPValueR (count η 0) (count η 1) (count η 2)) atTop (𝓝 1) := by
  refine tendsto_iidProb_one hφ fun R hR ↦ ?_
  have hc₀ : 0 < Real.cos (alphaZero φ) / 2 := by
    have : 0 < Real.cos (alphaZero φ) := Real.cos_arctan_pos _
    positivity
  set K := R ^ 2 + 1 with hK
  have hK0 : 0 ≤ K := by positivity
  obtain ⟨δ, M, hδ, hcut⟩ := cutTail_ge hK0 hc₀
  filter_upwards [eventually_lineS_first hφ hR one_pos, eventually_lineS_other_large hφ hφ1 hR K,
    eventually_abs_muZero_large hφ hφ1 M (R := R), eventually_cos_alphaZero_ge hφ (R := R),
    hα.eventually (gt_mem_nhds hδ)] with n h₁ h₂ h₃ h₄ h₅ η hη₁ hη₂
  have hη₁' : |(whiten φ n (count η 0) (count η 1) (count η 2)).1| < R := hη₁
  have hη₂' : |(whiten φ n (count η 0) (count η 1) (count η 2)).2| < R := hη₂
  have hl := abs_lt.1 (h₁ _ _ _ (count_add η) hη₁' hη₂')
  have hsq := sq_lt_of_abs_lt hη₁'
  have hline : lineS (count η 1) (count η 2) < K := by linarith [hl.2]
  obtain ⟨h₆, h₇⟩ := h₂ _ _ _ (count_add η) hη₁' hη₂'
  refine ⟨⟨hline.trans h₆, hline.trans h₇⟩, ?_⟩
  have hT : min (lineS (count η 1) (count η 2))
      (min (lineS (count η 0) (count η 2)) (lineS (count η 0) (count η 1))) ≤ K :=
    (min_le_left _ _).trans hline.le
  have h₈ := hcut _ _ (h₄ _ _ _ (count_add η) hη₂') (h₃ _ _ _ (count_add η) hη₂')
  exact h₅.le.trans (h₈.trans (cutTail_anti _ _ hT))

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

private lemma abs_min_sub_min_lt {x x' y y' ε : ℝ} (hx : |x - x'| < ε) (hy : |y - y'| < ε) :
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

end Phylogenetics.Trinomial
