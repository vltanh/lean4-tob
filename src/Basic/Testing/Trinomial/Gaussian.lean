module

public import Basic.Testing.Tails
public import Basic.ForMathlib.Probability.GaussianPlane
public import Basic.Testing.Trinomial.Whiten

/-!
# The limit laws of the quartet statistics

The test distributions, as laws of functions of two independent normals: the closed form of the tail
of `χ²₁` (`chiSqOneTail_eq_erf`), the comparison of the T1 and cut test distributions with it, and the
masses of the sets of the plane in the limits. Also the passage from the central limit theorem to
events of a sample: `eventually_lt_iidProb`, `tendsto_iidProb_one`, `tendsto_iidProb_of_threshold`.
-/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open Phylogenetics Phylogenetics.QuartetTests
open scoped ENNReal

namespace Phylogenetics.Trinomial

/-! ### Normal tails -/

theorem gaussianReal_real_Ioi (m a : ℝ) :
    (gaussianReal m 1).real (Ioi a) = 1 / 2 * (1 - Real.erf ((a - m) / √2)) := by
  rw [measureReal_def, gaussianReal_Ioi_eq_erf, ENNReal.toReal_ofReal]
  have := Real.erf_le_one ((a - m) / √2)
  linarith

theorem gaussianReal_real_Iio (m a : ℝ) :
    (gaussianReal m 1).real (Iio a) = 1 / 2 * (1 - Real.erf ((m - a) / √2)) := by
  have h : gaussianReal (-m) 1 = (gaussianReal m 1).map (fun x ↦ -x) := gaussianReal_map_neg.symm
  have h₂ : (gaussianReal m 1).real (Iio a) = (gaussianReal (-m) 1).real (Ioi (-a)) := by
    rw [h, measureReal_def, measureReal_def, Measure.map_apply (by fun_prop) measurableSet_Ioi]
    congr 2
    ext x
    simp
  rw [h₂, gaussianReal_real_Ioi]
  congr 3
  ring

theorem erf_zero : Real.erf 0 = 0 := by
  simp [Real.erf]

/-- The closed form of the tail of `χ²₁`. -/
theorem chiSqOneTail_eq_erf {t : ℝ} (ht : 0 ≤ t) : chiSqOneTail t = 1 - Real.erf (√t / √2) := by
  have hset : {z : ℝ | t < z ^ 2} = Ioi (√t) ∪ Iio (-√t) := by
    ext z
    simp only [mem_ofPred_eq, mem_union, mem_Ioi, mem_Iio]
    constructor
    · intro h
      have hs : √t < |z| := by
        rw [← Real.sqrt_sq_eq_abs]
        exact Real.sqrt_lt_sqrt ht h
      rcases le_total 0 z with hz | hz
      · left
        rwa [abs_of_nonneg hz] at hs
      · right
        rw [abs_of_nonpos hz] at hs
        linarith
    · rintro (h | h)
      · exact Real.lt_sq_of_sqrt_lt h
      · have : √t < -z := by linarith
        have := Real.lt_sq_of_sqrt_lt this
        rwa [neg_sq] at this
  have hdisj : Disjoint (Ioi (√t)) (Iio (-√t)) := by
    rw [Set.disjoint_left]
    intro z h₁ h₂
    have h₃ := Real.sqrt_nonneg t
    have h₄ : √t < z := h₁
    have h₅ : z < -√t := h₂
    linarith
  unfold chiSqOneTail
  rw [hset, measureReal_union hdisj measurableSet_Iio, gaussianReal_real_Ioi, gaussianReal_real_Iio]
  have : (0 - -√t) / √2 = √t / √2 := by ring
  rw [this, show (√t - 0) / √2 = √t / √2 by ring]
  ring

theorem chiSqOneTail_zero : chiSqOneTail 0 = 1 := by
  rw [chiSqOneTail_eq_erf le_rfl]
  simp [erf_zero]

theorem chiSqOneTail_anti {s t : ℝ} (hst : s ≤ t) : chiSqOneTail t ≤ chiSqOneTail s :=
  measureReal_mono fun _ hz ↦ lt_of_le_of_lt hst hz

/-- Every level in `(0, 1]` is a value of the tail of `χ²₁`. -/
theorem exists_chiSqOneTail_eq {y : ℝ} (hy : 0 < y) (hy1 : y ≤ 1) :
    ∃ t : ℝ, 0 ≤ t ∧ chiSqOneTail t = y := by
  let G : ℝ → ℝ := fun t ↦ 1 - Real.erf (√t / √2)
  have hG : Continuous G := by
    have := Real.continuous_erf
    fun_prop
  have hlim : Tendsto G atTop (𝓝 0) := by
    have h₁ : Tendsto (fun t : ℝ ↦ √t / √2) atTop atTop :=
      Real.tendsto_sqrt_atTop.atTop_div_const (by positivity)
    have h₂ := Real.tendsto_erf_atTop.comp h₁
    have h₃ := tendsto_const_nhds (x := (1 : ℝ)) (f := atTop (α := ℝ)) |>.sub h₂
    simpa [G] using h₃
  obtain ⟨T, hT, hT0⟩ := ((hlim.eventually (gt_mem_nhds hy)).and (eventually_ge_atTop 0)).exists
  have hmem : y ∈ Icc (G T) (G 0) := by
    refine ⟨hT.le, ?_⟩
    simp [G, erf_zero, hy1]
  obtain ⟨t, ht, hty⟩ := intermediate_value_Icc' hT0 hG.continuousOn hmem
  exact ⟨t, ht.1, (chiSqOneTail_eq_erf ht.1).trans hty⟩

/-- The tail of `χ²₁` near `0`. -/
theorem exists_chiSqOneTail_gt {ε : ℝ} (hε : 0 < ε) : ∃ κ : ℝ, 0 < κ ∧ 1 - ε < chiSqOneTail κ := by
  let G : ℝ → ℝ := fun t ↦ 1 - Real.erf (√t / √2)
  have hG : Continuous G := by
    have := Real.continuous_erf
    fun_prop
  have h0 : G 0 = 1 := by simp [G, erf_zero]
  have hev : ∀ᶠ t in 𝓝 (0 : ℝ), 1 - ε < G t :=
    hG.continuousAt.eventually_const_lt (by rw [h0]; linarith)
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.1 hev
  refine ⟨δ / 2, by positivity, ?_⟩
  rw [chiSqOneTail_eq_erf (by positivity)]
  apply hball
  rw [Real.dist_eq, sub_zero, abs_of_pos (by positivity)]
  linarith

theorem measure_sq_eq_null (m c : ℝ) : gaussianReal m 1 {z : ℝ | z ^ 2 = c} = 0 := by
  have hn := nullSingletonClass_gaussianReal (μ := m) (v := 1) one_ne_zero
  have hsub : {z : ℝ | z ^ 2 = c} ⊆ {√c} ∪ {-√c} := by
    intro z hz
    have hz' : z ^ 2 = c := hz
    simp only [mem_union, mem_singleton_iff]
    rw [← hz', Real.sqrt_sq_eq_abs]
    rcases le_total 0 z with h | h
    · left
      rw [abs_of_nonneg h]
    · right
      rw [abs_of_nonpos h, neg_neg]
  exact measure_mono_null hsub (measure_union_null (measure_singleton _) (measure_singleton _))

/-! ### The planar law -/

theorem stdPlane_real_first (t : ℝ) : stdPlane.real {z : ℝ × ℝ | t < z.1 ^ 2} = chiSqOneTail t := by
  have : {z : ℝ × ℝ | t < z.1 ^ 2} = {x : ℝ | t < x ^ 2} ×ˢ univ := by
    ext z
    simp
  rw [this, stdPlane, measureReal_prod_prod]
  simp [chiSqOneTail]

theorem stdPlane_first_null (t : ℝ) : stdPlane {z : ℝ × ℝ | z.1 ^ 2 = t} = 0 := by
  have : {z : ℝ × ℝ | z.1 ^ 2 = t} = {x : ℝ | x ^ 2 = t} ×ˢ univ := by
    ext z
    simp
  rw [this, stdPlane, Measure.prod_prod, measure_sq_eq_null, zero_mul]

theorem stdPlane_real_norm {t : ℝ} (ht : 0 ≤ t) :
    stdPlane.real {z : ℝ × ℝ | t < z.1 ^ 2 + z.2 ^ 2} = chiSqTwoTail t :=
  (chiSqTwoTail_eq ht).symm

theorem stdPlane_norm_null (t : ℝ) : stdPlane {z : ℝ × ℝ | z.1 ^ 2 + z.2 ^ 2 = t} = 0 := by
  have hmeas : MeasurableSet {z : ℝ × ℝ | z.1 ^ 2 + z.2 ^ 2 = t} :=
    measurableSet_eq_fun (by fun_prop) (by fun_prop)
  rw [stdPlane, Measure.measure_prod_null hmeas]
  refine Eventually.of_forall fun x ↦ ?_
  have : Prod.mk x ⁻¹' {z : ℝ × ℝ | z.1 ^ 2 + z.2 ^ 2 = t} = {y : ℝ | y ^ 2 = t - x ^ 2} := by
    ext y
    simp only [mem_preimage, mem_ofPred_eq]
    constructor <;> intro h <;> linarith
  simp [this, measure_sq_eq_null]

/-! ### From the central limit theorem to events of the sample -/

variable {φ : ℝ}

/-- An event containing `W n ∈ U`, for an open set `U`, has probability at least `ν U` in the
limit. -/
theorem eventually_lt_iidProb (hφ : 0 < φ ∧ φ < 3 / 2) {U : Set (ℝ × ℝ)} (hU : IsOpen U)
    {Ev : ∀ n, (Fin n → Fin 3) → Prop}
    (hA : ∀ᶠ n in atTop, ∀ η : Fin n → Fin 3, sampleW φ η ∈ U → Ev n η)
    {c : ℝ} (hc : c < stdPlane.real U) :
    ∀ᶠ n in atTop, c < iidProb (cutPoint φ) n (Ev n) := by
  have hd := cutPoint_isDist hφ
  rcases lt_or_ge c 0 with hc0 | hc0
  · exact Eventually.of_forall fun n ↦ hc0.trans_le (iidProb_nonneg hd n _)
  have hc' : ENNReal.ofReal c < stdPlane U :=
    (ENNReal.ofReal_lt_iff_lt_toReal hc0 (measure_ne_top _ _)).2 hc
  have h := eventually_lt_measure_of_isOpen (tendstoInDistribution_sampleW hφ) hU
    (A := fun n ↦ {η | Ev n η}) hA hc'
  filter_upwards [h] with n hn
  rw [iidProb_eq_pi hd]
  exact (ENNReal.ofReal_lt_iff_lt_toReal hc0 (measure_ne_top _ _)).1 hn

/-- An event containing, for each `R`, the event `‖W n‖ < R` for large `n`, has probability
tending to one. -/
theorem tendsto_iidProb_one (hφ : 0 < φ ∧ φ < 3 / 2) {Ev : ∀ n, (Fin n → Fin 3) → Prop}
    (h : ∀ R : ℝ, 0 < R → ∀ᶠ n in atTop, ∀ η : Fin n → Fin 3,
      |(sampleW φ η).1| < R → |(sampleW φ η).2| < R → Ev n η) :
    Tendsto (fun n ↦ iidProb (cutPoint φ) n (Ev n)) atTop (𝓝 1) := by
  have hd := cutPoint_isDist hφ
  refine tendsto_order.2 ⟨fun c hc ↦ ?_, fun c hc ↦ ?_⟩
  · have hν : stdPlane.real univ = 1 := probReal_univ
    rcases lt_or_ge c 0 with hc0 | hc0
    · exact Eventually.of_forall fun n ↦ hc0.trans_le (iidProb_nonneg hd n _)
    have hc' : ENNReal.ofReal c < stdPlane univ := by
      rw [measure_univ]
      exact ENNReal.ofReal_lt_one.2 hc
    obtain ⟨R, hR, hRc⟩ := exists_lt_measure_box stdPlane hc'
    rw [univ_inter] at hRc
    refine eventually_lt_iidProb hφ Metric.isOpen_ball ?_
      ((ENNReal.ofReal_lt_iff_lt_toReal hc0 (measure_ne_top _ _)).1 hRc)
    filter_upwards [h R hR] with n hn η hη
    obtain ⟨h₁, h₂⟩ := mem_ball_iff.1 hη
    exact hn η h₁ h₂
  · exact Eventually.of_forall fun n ↦ (iidProb_le_one hd n _).trans_lt hc

/-- A lower bound for an event containing `t + δ < T (W n)`, for all `δ > 0`, and for bounded `W n`. -/
theorem eventually_lt_iidProb_of_gt (hφ : 0 < φ ∧ φ < 3 / 2) {Ev : ∀ n, (Fin n → Fin 3) → Prop}
    {T : ℝ × ℝ → ℝ} (hT : Continuous T) {t : ℝ}
    (h : ∀ R : ℝ, 0 < R → ∀ δ : ℝ, 0 < δ → ∀ᶠ n in atTop, ∀ η : Fin n → Fin 3,
      |(sampleW φ η).1| < R → |(sampleW φ η).2| < R → t + δ < T (sampleW φ η) → Ev n η)
    {c : ℝ} (hc : c < stdPlane.real {z | t < T z}) :
    ∀ᶠ n in atTop, c < iidProb (cutPoint φ) n (Ev n) := by
  have hd := cutPoint_isDist hφ
  rcases lt_or_ge c 0 with hc0 | hc0
  · exact Eventually.of_forall fun n ↦ hc0.trans_le (iidProb_nonneg hd n _)
  have hc' : ENNReal.ofReal c < stdPlane {z | t < T z} :=
    (ENNReal.ofReal_lt_iff_lt_toReal hc0 (measure_ne_top _ _)).2 hc
  have hmono : Monotone fun k : ℕ ↦ {z | t + ((k : ℝ) + 1)⁻¹ < T z} := by
    intro j k hjk z hz
    have hz' : t + ((j : ℝ) + 1)⁻¹ < T z := hz
    have hle : (j : ℝ) ≤ k := by exact_mod_cast hjk
    have : ((k : ℝ) + 1)⁻¹ ≤ ((j : ℝ) + 1)⁻¹ := inv_anti₀ (by positivity) (by linarith)
    change t + ((k : ℝ) + 1)⁻¹ < T z
    linarith
  have hunion : ⋃ k : ℕ, {z | t + ((k : ℝ) + 1)⁻¹ < T z} = {z | t < T z} := by
    ext z
    simp only [mem_iUnion, mem_ofPred_eq]
    constructor
    · rintro ⟨k, hk⟩
      have : 0 < ((k : ℝ) + 1)⁻¹ := by positivity
      linarith
    · intro hz
      obtain ⟨k, hk⟩ := exists_nat_one_div_lt (sub_pos.2 hz)
      refine ⟨k, ?_⟩
      rw [one_div] at hk
      linarith
  have ht := tendsto_measure_iUnion_atTop (μ := stdPlane) hmono
  rw [hunion] at ht
  obtain ⟨k, hk⟩ := (ht.eventually (lt_mem_nhds hc')).exists
  obtain ⟨R, hR, hRc⟩ := exists_lt_measure_box stdPlane hk
  have hopen : IsOpen ({z | t + ((k : ℝ) + 1)⁻¹ < T z} ∩ Metric.ball 0 R) :=
    (isOpen_lt continuous_const hT).inter Metric.isOpen_ball
  refine eventually_lt_iidProb hφ hopen ?_
    ((ENNReal.ofReal_lt_iff_lt_toReal hc0 (measure_ne_top _ _)).1 hRc)
  filter_upwards [h R hR _ (by positivity : 0 < ((k : ℝ) + 1)⁻¹)] with n hn η hη
  obtain ⟨h₁, h₂⟩ := mem_ball_iff.1 hη.2
  exact hn η h₁ h₂ hη.1

/-- The probability of an event that holds above a threshold of the limit statistic, and fails below it,
with no mass at the threshold. -/
theorem tendsto_iidProb_of_threshold (hφ : 0 < φ ∧ φ < 3 / 2) {Ev : ∀ n, (Fin n → Fin 3) → Prop}
    {T : ℝ × ℝ → ℝ} (hT : Continuous T) {t : ℝ}
    (h₁ : ∀ R : ℝ, 0 < R → ∀ δ : ℝ, 0 < δ → ∀ᶠ n in atTop, ∀ η : Fin n → Fin 3,
      |(sampleW φ η).1| < R → |(sampleW φ η).2| < R → t + δ < T (sampleW φ η) → Ev n η)
    (h₂ : ∀ R : ℝ, 0 < R → ∀ δ : ℝ, 0 < δ → ∀ᶠ n in atTop, ∀ η : Fin n → Fin 3,
      |(sampleW φ η).1| < R → |(sampleW φ η).2| < R → T (sampleW φ η) < t - δ → ¬ Ev n η)
    (hnull : stdPlane {z | T z = t} = 0) :
    Tendsto (fun n ↦ iidProb (cutPoint φ) n (Ev n)) atTop (𝓝 (stdPlane.real {z | t < T z})) := by
  have hd := cutPoint_isDist hφ
  refine tendsto_order.2 ⟨fun c hc ↦ eventually_lt_iidProb_of_gt hφ hT h₁ hc, fun c hc ↦ ?_⟩
  -- the complementary event
  have hcompl : stdPlane.real {z | -t < -T z} = 1 - stdPlane.real {z | t < T z} := by
    have hdisj : Disjoint {z | t < T z} {z | -t < -T z} := by
      rw [Set.disjoint_left]
      intro z h₁ h₂
      have h₃ : t < T z := h₁
      have h₄ : -t < -T z := h₂
      linarith
    have hm : MeasurableSet {z | -t < -T z} := (isOpen_lt continuous_const hT.neg).measurableSet
    have hsum : stdPlane.real ({z | t < T z} ∪ {z | -t < -T z}) = 1 := by
      have hae : ({z | t < T z} ∪ {z | -t < -T z}) =ᵐ[stdPlane] (univ : Set (ℝ × ℝ)) := by
        rw [ae_eq_univ]
        refine measure_mono_null ?_ hnull
        intro z hz
        have hz' : ¬ (t < T z ∨ -t < -T z) := hz
        push Not at hz'
        have h₃ := hz'.1
        have h₄ := hz'.2
        exact le_antisymm h₃ (by linarith)
      rw [measureReal_def, measure_congr hae, measure_univ]
      rfl
    rw [measureReal_union hdisj hm] at hsum
    linarith
  have hneg : ∀ᶠ n in atTop, 1 - c < iidProb (cutPoint φ) n (fun η ↦ ¬ Ev n η) := by
    refine eventually_lt_iidProb_of_gt hφ (T := fun z ↦ -T z) hT.neg (t := -t) ?_ ?_
    · intro R hR δ hδ
      filter_upwards [h₂ R hR δ hδ] with n hn η hη₁ hη₂ hη₃
      exact hn η hη₁ hη₂ (by linarith)
    · rw [hcompl]
      linarith
  filter_upwards [hneg] with n hn
  rw [iidProb_not hd] at hn
  linarith

end Phylogenetics.Trinomial
