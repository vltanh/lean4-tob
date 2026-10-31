module

public import Basic.Analysis.SpecialFunctions.EntropyExcess
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Order.Filter.AtTopBot.Basic

/-!
# The likelihood ratio statistics of a trinomial, on real counts

`lineS b c`, for counts `b`, `c` of the two alternatives, and `starS a b c` are likelihood ratio
statistics. They are written through `Real.entropyExcess` (`lineS_eq`, `starS_eq`), and the
expansion of this function gives their limits near a point of the model with the counts of order `n`
and their deviations of order `√n` (`eventually_lineS_close`, `eventually_lineS_large`,
`eventually_starS_close`). This one expansion is what the limits of all statistics use.
-/

@[expose] public noncomputable section

open Real Filter Topology

namespace Phylogenetics.Trinomial

/-- The likelihood ratio statistic of the line on which the two alternatives, with counts `a`, `b`,
are equal. -/
def lineS (a b : ℝ) : ℝ :=
  2 * (a * log a + b * log b - (a + b) * log (a + b) + (a + b) * log 2)

/-- The likelihood ratio statistic of the star test. -/
def starS (a b c : ℝ) : ℝ :=
  2 * (a * log a + b * log b + c * log c - (a + b + c) * log ((a + b + c) / 3))

/-- Pearson's statistic of the star test. -/
def pearsonS (a b c : ℝ) : ℝ :=
  (a - (a + b + c) / 3) ^ 2 / ((a + b + c) / 3) + (b - (a + b + c) / 3) ^ 2 / ((a + b + c) / 3) +
    (c - (a + b + c) / 3) ^ 2 / ((a + b + c) / 3)

private lemma mul_log_scale {x k : ℝ} (hx : 0 ≤ x) (hk : 0 < k) :
    x * log (x / k) = x * log x - x * log k := by
  rcases hx.eq_or_lt with rfl | hx
  · simp
  · rw [log_div hx.ne' hk.ne']
    ring

/-- The line statistic through `Real.entropyExcess`. -/
theorem lineS_eq {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hM : 0 < a + b) :
    lineS a b = (a + b) *
      (entropyExcess ((a - b) / (a + b)) + entropyExcess (-((a - b) / (a + b)))) := by
  have hk : 0 < (a + b) / 2 := by positivity
  have h₁ : 1 + (a - b) / (a + b) = a / ((a + b) / 2) := by field_simp; ring
  have h₂ : 1 + -((a - b) / (a + b)) = b / ((a + b) / 2) := by field_simp; ring
  have hlog : log ((a + b) / 2) = log (a + b) - log 2 := log_div hM.ne' two_ne_zero
  have hA := mul_log_scale ha hk
  have hB := mul_log_scale hb hk
  rw [hlog] at hA hB
  have e₁ : (a + b) * (a / ((a + b) / 2)) = 2 * a := by field_simp
  have e₂ : (a + b) * (b / ((a + b) / 2)) = 2 * b := by field_simp
  unfold entropyExcess lineS
  rw [h₁, h₂]
  generalize a / ((a + b) / 2) = x₁ at *
  generalize b / ((a + b) / 2) = x₂ at *
  generalize (a - b) / (a + b) = u at *
  generalize log x₁ = A at *
  generalize log x₂ = B at *
  linear_combination (-A) * e₁ + (-B) * e₂ + (-2) * hA + (-2) * hB

theorem lineS_nonneg {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) : 0 ≤ lineS a b := by
  rcases (add_nonneg ha hb).eq_or_lt with h | hM
  · have ha0 : a = 0 := by linarith
    have hb0 : b = 0 := by linarith
    simp [lineS, ha0, hb0]
  · rw [lineS_eq ha hb hM]
    have habs : |(a - b) / (a + b)| ≤ 1 := by
      rw [abs_div, abs_of_pos hM, div_le_one hM, abs_le]
      constructor <;> linarith
    obtain ⟨h₁, h₂⟩ := abs_le.1 habs
    refine mul_nonneg hM.le (add_nonneg (entropyExcess_nonneg h₁) (entropyExcess_nonneg ?_))
    linarith

theorem lineS_pos {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (hne : a ≠ b) : 0 < lineS a b := by
  have hM : 0 < a + b := by positivity
  rw [lineS_eq ha.le hb.le hM]
  have hu : (a - b) / (a + b) ≠ 0 := div_ne_zero (sub_ne_zero.2 hne) hM.ne'
  have h₁ : -1 < (a - b) / (a + b) := by
    rw [lt_div_iff₀ hM]
    linarith
  have h₂ : (a - b) / (a + b) < 1 := by
    rw [div_lt_one hM]
    linarith
  refine mul_pos hM (add_pos (entropyExcess_pos h₁ hu) (entropyExcess_pos ?_ (neg_ne_zero.2 hu)))
  linarith

/-- The line statistic and Pearson's form of it. -/
theorem abs_lineS_sub_le {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hM : 0 < a + b)
    (hD : |a - b| ≤ (a + b) / 2) :
    |lineS a b - (a - b) ^ 2 / (a + b)| ≤ 8 * |a - b| ^ 3 / (a + b) ^ 2 := by
  set u := (a - b) / (a + b) with hu
  have huabs : |u| = |a - b| / (a + b) := by rw [hu, abs_div, abs_of_pos hM]
  have hu2 : |u| ≤ 1 / 2 := by
    rw [huabs, div_le_iff₀ hM]
    linarith
  have h₁ := abs_entropyExcess_sub_le hu2
  have h₂ := abs_entropyExcess_sub_le (v := -u) (by rwa [abs_neg])
  rw [abs_neg, neg_sq] at h₂
  have hexp : lineS a b - (a - b) ^ 2 / (a + b) =
      (a + b) * ((entropyExcess u - u ^ 2 / 2) + (entropyExcess (-u) - u ^ 2 / 2)) := by
    rw [lineS_eq ha hb hM, hu]
    field_simp
    ring
  rw [hexp, abs_mul, abs_of_pos hM]
  have htot : |(entropyExcess u - u ^ 2 / 2) + (entropyExcess (-u) - u ^ 2 / 2)| ≤ 8 * |u| ^ 3 := by
    have := abs_add_le (entropyExcess u - u ^ 2 / 2) (entropyExcess (-u) - u ^ 2 / 2)
    linarith
  calc (a + b) * |(entropyExcess u - u ^ 2 / 2) + (entropyExcess (-u) - u ^ 2 / 2)|
      ≤ (a + b) * (8 * |u| ^ 3) := by gcongr
    _ = 8 * |a - b| ^ 3 / (a + b) ^ 2 := by
      rw [huabs]
      field_simp

/-- The line statistic near the line, with an explicit error. -/
theorem lineS_close {α R s f g : ℝ} (hα : 0 < α) (hR : 0 < R) (hs : 4 * R / α ≤ s)
    (hf : |f| ≤ R) (hg : |g| ≤ R) :
    |lineS (α * s ^ 2 + s * f) (α * s ^ 2 + s * g) - (f - g) ^ 2 / (2 * α)| ≤
      68 * R ^ 3 / (α ^ 2 * s) := by
  have hs0 : 0 < s := lt_of_lt_of_le (by positivity) hs
  have hRs : 4 * R ≤ α * s := by
    rw [div_le_iff₀ hα] at hs
    linarith
  obtain ⟨hf₁, hf₂⟩ := abs_le.1 hf
  obtain ⟨hg₁, hg₂⟩ := abs_le.1 hg
  have hsR : s * R ≤ α * s ^ 2 / 4 := by nlinarith
  have hsf : |s * f| ≤ s * R := by
    rw [abs_mul, abs_of_pos hs0]
    gcongr
  have hsg : |s * g| ≤ s * R := by
    rw [abs_mul, abs_of_pos hs0]
    gcongr
  obtain ⟨hsf₁, hsf₂⟩ := abs_le.1 hsf
  obtain ⟨hsg₁, hsg₂⟩ := abs_le.1 hsg
  have hαs : 0 < α * s ^ 2 := by positivity
  set a := α * s ^ 2 + s * f with ha_def
  set b := α * s ^ 2 + s * g with hb_def
  have ha : 0 ≤ a := by rw [ha_def]; linarith
  have hb : 0 ≤ b := by rw [hb_def]; linarith
  have hMlow : α * s ^ 2 ≤ a + b := by rw [ha_def, hb_def]; linarith
  have hM : 0 < a + b := by linarith
  have hDeq : a - b = s * (f - g) := by rw [ha_def, hb_def]; ring
  have hfg : |f - g| ≤ 2 * R := by
    rw [abs_le]
    constructor <;> linarith
  have hDabs : |a - b| ≤ 2 * R * s := by
    rw [hDeq, abs_mul, abs_of_pos hs0]
    nlinarith [abs_nonneg (f - g)]
  have hD : |a - b| ≤ (a + b) / 2 := by
    have : 2 * R * s ≤ α * s ^ 2 / 2 := by nlinarith
    linarith
  have h₁ := abs_lineS_sub_le ha hb hM hD
  have h₁' : 8 * |a - b| ^ 3 / (a + b) ^ 2 ≤ 64 * R ^ 3 / (α ^ 2 * s) := by
    calc 8 * |a - b| ^ 3 / (a + b) ^ 2 ≤ 8 * (2 * R * s) ^ 3 / (α * s ^ 2) ^ 2 := by gcongr
      _ = 64 * R ^ 3 / (α ^ 2 * s) := by
        field_simp
        ring
  have hterm2 : (a - b) ^ 2 / (a + b) - (f - g) ^ 2 / (2 * α) =
      -((f - g) ^ 2 * (s * (f + g))) / (2 * α * (a + b)) := by
    have hab : a + b = 2 * α * s ^ 2 + s * (f + g) := by rw [ha_def, hb_def]; ring
    rw [hDeq]
    field_simp
    rw [hab]
    ring
  have h₂ : |(a - b) ^ 2 / (a + b) - (f - g) ^ 2 / (2 * α)| ≤ 4 * R ^ 3 / (α ^ 2 * s) := by
    rw [hterm2, abs_div, abs_neg, abs_mul, abs_mul, abs_of_pos hs0, abs_pow,
      abs_of_pos (by positivity : 0 < 2 * α * (a + b))]
    have hfpg : |f + g| ≤ 2 * R := by
      rw [abs_le]
      constructor <;> linarith
    calc |f - g| ^ 2 * (s * |f + g|) / (2 * α * (a + b))
        ≤ (2 * R) ^ 2 * (s * (2 * R)) / (2 * α * (α * s ^ 2)) := by gcongr
      _ = 4 * R ^ 3 / (α ^ 2 * s) := by
        field_simp
        ring
  have h₃ := abs_add_le (lineS a b - (a - b) ^ 2 / (a + b))
    ((a - b) ^ 2 / (a + b) - (f - g) ^ 2 / (2 * α))
  rw [show lineS a b - (a - b) ^ 2 / (a + b) + ((a - b) ^ 2 / (a + b) - (f - g) ^ 2 / (2 * α)) =
    lineS a b - (f - g) ^ 2 / (2 * α) by ring] at h₃
  have hfin : 64 * R ^ 3 / (α ^ 2 * s) + 4 * R ^ 3 / (α ^ 2 * s) = 68 * R ^ 3 / (α ^ 2 * s) := by
    ring
  linarith

private theorem tendsto_sqrt_natCast : Tendsto (fun n : ℕ ↦ √(n : ℝ)) atTop atTop :=
  tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop

/-- The line statistic near the line: uniformly in the deviations of order `√n`, it is their
quadratic form. -/
theorem eventually_lineS_close {α R ε : ℝ} (hα : 0 < α) (hR : 0 < R) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ f g : ℝ, |f| ≤ R → |g| ≤ R →
      |lineS (α * n + √(n : ℝ) * f) (α * n + √(n : ℝ) * g) - (f - g) ^ 2 / (2 * α)| < ε := by
  have hc : 0 < 68 * R ^ 3 / α ^ 2 := by positivity
  filter_upwards [tendsto_sqrt_natCast.eventually_ge_atTop (4 * R / α),
    tendsto_sqrt_natCast.eventually_gt_atTop (68 * R ^ 3 / α ^ 2 / ε)] with n hn₁ hn₂ f g hf hg
  have hs0 : 0 < √(n : ℝ) := lt_of_lt_of_le (by positivity) hn₁
  have hsq : (n : ℝ) = √(n : ℝ) ^ 2 := (Real.sq_sqrt (Nat.cast_nonneg n)).symm
  have h := lineS_close hα hR hn₁ hf hg
  rw [← hsq] at h
  refine h.trans_lt ?_
  rw [div_lt_iff₀ hε] at hn₂
  rw [div_lt_iff₀ (by positivity)]
  have : 68 * R ^ 3 = 68 * R ^ 3 / α ^ 2 * α ^ 2 := by field_simp
  rw [this]
  nlinarith [sq_pos_of_pos hα]

theorem lineS_mul (x y : ℝ) {k : ℝ} (hk : k ≠ 0) : lineS (k * x) (k * y) = k * lineS x y := by
  have h : ∀ z : ℝ, (k * z) * log (k * z) = k * (z * log z) + k * z * log k := by
    intro z
    rcases eq_or_ne z 0 with rfl | hz
    · simp
    · rw [log_mul hk hz]
      ring
  unfold lineS
  rw [← mul_add k x y, h, h, h]
  ring

theorem continuous_lineS : Continuous fun z : ℝ × ℝ ↦ lineS z.1 z.2 := by
  unfold lineS
  have h : Continuous fun x : ℝ ↦ x * log x := continuous_mul_log
  have h₁ : Continuous fun z : ℝ × ℝ ↦ z.1 * log z.1 := h.comp continuous_fst
  have h₂ : Continuous fun z : ℝ × ℝ ↦ z.2 * log z.2 := h.comp continuous_snd
  have h₃ : Continuous fun z : ℝ × ℝ ↦ (z.1 + z.2) * log (z.1 + z.2) :=
    h.comp (continuous_fst.add continuous_snd)
  fun_prop

/-- Off the line, the line statistic grows like `n`. -/
theorem eventually_lineS_large {α β R : ℝ} (hα : 0 < α) (hβ : 0 < β) (hne : α ≠ β) (hR : 0 < R)
    (K : ℝ) :
    ∀ᶠ n : ℕ in atTop, ∀ f g : ℝ, |f| ≤ R → |g| ≤ R →
      K < lineS (α * n + √(n : ℝ) * f) (β * n + √(n : ℝ) * g) := by
  have hℓ := lineS_pos hα hβ hne
  set ℓ := lineS α β with hℓdef
  have hcont := continuous_lineS.continuousAt (x := (α, β))
  have hev : ∀ᶠ z : ℝ × ℝ in 𝓝 (α, β), ℓ / 2 < lineS z.1 z.2 :=
    hcont.eventually_const_lt (by simp only [← hℓdef]; linarith)
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.1 hev
  have hnlarge : Tendsto (fun n : ℕ ↦ (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  filter_upwards [tendsto_sqrt_natCast.eventually_gt_atTop (R / δ),
    hnlarge.eventually_gt_atTop (2 * K / ℓ)] with n hn₁ hn₂ f g hf hg
  have hs0 : 0 < √(n : ℝ) := lt_of_le_of_lt (by positivity) hn₁
  have hn0 : (0 : ℝ) < n := by
    have : (n : ℝ) = √(n : ℝ) ^ 2 := (Real.sq_sqrt (Nat.cast_nonneg n)).symm
    rw [this]
    positivity
  have hRs : R < δ * √(n : ℝ) := by
    rw [div_lt_iff₀ hδ] at hn₁
    linarith
  have hsmall : ∀ h : ℝ, |h| ≤ R → |h / √(n : ℝ)| < δ := by
    intro h hh
    rw [abs_div, abs_of_pos hs0, div_lt_iff₀ hs0]
    linarith
  have hin : ((α + f / √(n : ℝ), β + g / √(n : ℝ)) : ℝ × ℝ) ∈ Metric.ball (α, β) δ := by
    rw [Metric.mem_ball, Prod.dist_eq, max_lt_iff, Real.dist_eq, Real.dist_eq]
    constructor
    · simpa using hsmall f hf
    · simpa using hsmall g hg
  have hval := hball (y := (α + f / √(n : ℝ), β + g / √(n : ℝ))) (Metric.mem_ball.1 hin)
  simp only at hval
  have hdiv : (n : ℝ) / √(n : ℝ) = √(n : ℝ) := Real.div_sqrt
  have e₁ : α * n + √(n : ℝ) * f = n * (α + f / √(n : ℝ)) := by
    calc α * n + √(n : ℝ) * f = n * α + (n / √(n : ℝ)) * f := by rw [hdiv]; ring
      _ = _ := by ring
  have e₂ : β * n + √(n : ℝ) * g = n * (β + g / √(n : ℝ)) := by
    calc β * n + √(n : ℝ) * g = n * β + (n / √(n : ℝ)) * g := by rw [hdiv]; ring
      _ = _ := by ring
  rw [e₁, e₂, lineS_mul _ _ hn0.ne']
  rw [div_lt_iff₀ hℓ] at hn₂
  nlinarith

/-- The star statistic through `Real.entropyExcess`. -/
theorem starS_eq {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hN : 0 < a + b + c) :
    starS a b c = 2 * (a + b + c) / 3 *
      (entropyExcess (3 * a / (a + b + c) - 1) + entropyExcess (3 * b / (a + b + c) - 1) +
        entropyExcess (3 * c / (a + b + c) - 1)) := by
  have hk : 0 < (a + b + c) / 3 := by positivity
  have hA := mul_log_scale ha hk
  have hB := mul_log_scale hb hk
  have hC := mul_log_scale hc hk
  have h₁ : 1 + (3 * a / (a + b + c) - 1) = a / ((a + b + c) / 3) := by field_simp; ring
  have h₂ : 1 + (3 * b / (a + b + c) - 1) = b / ((a + b + c) / 3) := by field_simp; ring
  have h₃ : 1 + (3 * c / (a + b + c) - 1) = c / ((a + b + c) / 3) := by field_simp; ring
  have e₁ : (a + b + c) * (a / ((a + b + c) / 3)) = 3 * a := by field_simp
  have e₂ : (a + b + c) * (b / ((a + b + c) / 3)) = 3 * b := by field_simp
  have e₃ : (a + b + c) * (c / ((a + b + c) / 3)) = 3 * c := by field_simp
  have hsum : (3 * a / (a + b + c) - 1) + (3 * b / (a + b + c) - 1) +
      (3 * c / (a + b + c) - 1) = 0 := by
    field_simp
    ring
  unfold entropyExcess starS
  rw [h₁, h₂, h₃]
  generalize a / ((a + b + c) / 3) = x₁ at *
  generalize b / ((a + b + c) / 3) = x₂ at *
  generalize c / ((a + b + c) / 3) = x₃ at *
  generalize 3 * a / (a + b + c) - 1 = u₁ at *
  generalize 3 * b / (a + b + c) - 1 = u₂ at *
  generalize 3 * c / (a + b + c) - 1 = u₃ at *
  generalize log x₁ = A at *
  generalize log x₂ = B at *
  generalize log x₃ = C at *
  generalize log ((a + b + c) / 3) = L at *
  have hsum' : (u₁ + u₂ + u₃) * (2 * (a + b + c) / 3) = 0 := by rw [hsum]; ring
  linear_combination (-2 / 3 * A) * e₁ + (-2 / 3 * B) * e₂ + (-2 / 3 * C) * e₃ + (-2) * hA + (-2) * hB +
    (-2) * hC + hsum'

theorem starS_nonneg {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) : 0 ≤ starS a b c := by
  rcases (add_nonneg (add_nonneg ha hb) hc).eq_or_lt with h | hN
  · have ha0 : a = 0 := by linarith
    have hb0 : b = 0 := by linarith
    have hc0 : c = 0 := by linarith
    simp [starS, ha0, hb0, hc0]
  · rw [starS_eq ha hb hc hN]
    have hv : ∀ x : ℝ, 0 ≤ x → -1 ≤ 3 * x / (a + b + c) - 1 := by
      intro x hx
      have : 0 ≤ 3 * x / (a + b + c) := by positivity
      linarith
    exact mul_nonneg (by positivity) (add_nonneg (add_nonneg (entropyExcess_nonneg (hv a ha))
      (entropyExcess_nonneg (hv b hb))) (entropyExcess_nonneg (hv c hc)))

/-- Pearson's statistic near the centroid, for counts summing to `s²`. -/
theorem pearsonS_eq {s f₀ f₁ f₂ : ℝ} (hs : s ≠ 0) (hsum : f₀ + f₁ + f₂ = 0) :
    pearsonS (s ^ 2 / 3 + s * f₀) (s ^ 2 / 3 + s * f₁) (s ^ 2 / 3 + s * f₂) =
      3 * (f₀ ^ 2 + f₁ ^ 2 + f₂ ^ 2) := by
  have hN : (s ^ 2 / 3 + s * f₀) + (s ^ 2 / 3 + s * f₁) + (s ^ 2 / 3 + s * f₂) = s ^ 2 := by
    linear_combination s * hsum
  unfold pearsonS
  rw [hN]
  field_simp
  ring

/-- The star statistic near the centroid, with an explicit error. -/
theorem starS_close {R s f₀ f₁ f₂ : ℝ} (hR : 0 < R) (hs : 6 * R ≤ s) (hsum : f₀ + f₁ + f₂ = 0)
    (hf₀ : |f₀| ≤ R) (hf₁ : |f₁| ≤ R) (hf₂ : |f₂| ≤ R) :
    |starS (s ^ 2 / 3 + s * f₀) (s ^ 2 / 3 + s * f₁) (s ^ 2 / 3 + s * f₂) -
        3 * (f₀ ^ 2 + f₁ ^ 2 + f₂ ^ 2)| ≤ 216 * R ^ 3 / s := by
  have hs0 : 0 < s := by linarith
  have hN : (s ^ 2 / 3 + s * f₀) + (s ^ 2 / 3 + s * f₁) + (s ^ 2 / 3 + s * f₂) = s ^ 2 := by
    linear_combination s * hsum
  have hnn : ∀ f : ℝ, |f| ≤ R → 0 ≤ s ^ 2 / 3 + s * f := by
    intro f hf
    obtain ⟨h₁, -⟩ := abs_le.1 hf
    nlinarith
  have hv : ∀ f : ℝ, 3 * (s ^ 2 / 3 + s * f) / s ^ 2 - 1 = 3 * f / s := by
    intro f
    field_simp
    ring
  rw [starS_eq (hnn _ hf₀) (hnn _ hf₁) (hnn _ hf₂) (by rw [hN]; positivity), hN, hv, hv, hv]
  have hone : ∀ f : ℝ, |f| ≤ R →
      |2 * s ^ 2 / 3 * entropyExcess (3 * f / s) - 3 * f ^ 2| ≤ 72 * R ^ 3 / s := by
    intro f hf
    have hvb : |3 * f / s| ≤ 3 * R / s := by
      rw [abs_div, abs_of_pos hs0, abs_mul]
      simp only [abs_of_pos (by norm_num : (0 : ℝ) < 3)]
      gcongr
    have hvs : |3 * f / s| ≤ 1 / 2 := by
      refine hvb.trans ?_
      rw [div_le_iff₀ hs0]
      linarith
    have hexp := abs_entropyExcess_sub_le hvs
    have heq : 2 * s ^ 2 / 3 * entropyExcess (3 * f / s) - 3 * f ^ 2 =
        2 * s ^ 2 / 3 * (entropyExcess (3 * f / s) - (3 * f / s) ^ 2 / 2) := by
      field_simp
    rw [heq, abs_mul, abs_of_pos (by positivity : 0 < 2 * s ^ 2 / 3)]
    calc 2 * s ^ 2 / 3 * |entropyExcess (3 * f / s) - (3 * f / s) ^ 2 / 2|
        ≤ 2 * s ^ 2 / 3 * (4 * (3 * R / s) ^ 3) := by
          gcongr
          exact hexp.trans (by gcongr)
      _ = 72 * R ^ 3 / s := by
        field_simp
        ring
  have h₀ := hone f₀ hf₀
  have h₁ := hone f₁ hf₁
  have h₂ := hone f₂ hf₂
  have heq : 2 * s ^ 2 / 3 * (entropyExcess (3 * f₀ / s) + entropyExcess (3 * f₁ / s) +
        entropyExcess (3 * f₂ / s)) - 3 * (f₀ ^ 2 + f₁ ^ 2 + f₂ ^ 2) =
      (2 * s ^ 2 / 3 * entropyExcess (3 * f₀ / s) - 3 * f₀ ^ 2) +
        (2 * s ^ 2 / 3 * entropyExcess (3 * f₁ / s) - 3 * f₁ ^ 2) +
        (2 * s ^ 2 / 3 * entropyExcess (3 * f₂ / s) - 3 * f₂ ^ 2) := by ring
  rw [heq]
  have h₃ := abs_add_three (2 * s ^ 2 / 3 * entropyExcess (3 * f₀ / s) - 3 * f₀ ^ 2)
    (2 * s ^ 2 / 3 * entropyExcess (3 * f₁ / s) - 3 * f₁ ^ 2)
    (2 * s ^ 2 / 3 * entropyExcess (3 * f₂ / s) - 3 * f₂ ^ 2)
  have hfin : 216 * R ^ 3 / s = 72 * R ^ 3 / s + 72 * R ^ 3 / s + 72 * R ^ 3 / s := by ring
  linarith

/-- The star statistic near the centroid: uniformly in the deviations of order `√n`, it is their
quadratic form. -/
theorem eventually_starS_close {R ε : ℝ} (hR : 0 < R) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ f₀ f₁ f₂ : ℝ, f₀ + f₁ + f₂ = 0 → |f₀| ≤ R → |f₁| ≤ R → |f₂| ≤ R →
      |starS ((n : ℝ) / 3 + √(n : ℝ) * f₀) ((n : ℝ) / 3 + √(n : ℝ) * f₁)
          ((n : ℝ) / 3 + √(n : ℝ) * f₂) -
        3 * (f₀ ^ 2 + f₁ ^ 2 + f₂ ^ 2)| < ε := by
  filter_upwards [tendsto_sqrt_natCast.eventually_ge_atTop (6 * R),
    tendsto_sqrt_natCast.eventually_gt_atTop (216 * R ^ 3 / ε)]
    with n hn₁ hn₂ f₀ f₁ f₂ hsum hf₀ hf₁ hf₂
  have hs0 : 0 < √(n : ℝ) := by linarith
  have hsq : (n : ℝ) = √(n : ℝ) ^ 2 := (Real.sq_sqrt (Nat.cast_nonneg n)).symm
  have h := starS_close hR hn₁ hsum hf₀ hf₁ hf₂
  rw [← hsq] at h
  refine h.trans_lt ?_
  rw [div_lt_iff₀ hε] at hn₂
  rw [div_lt_iff₀ hs0]
  linarith

end Phylogenetics.Trinomial
