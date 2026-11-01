module

public import Basic.Testing.Trinomial.Tests

/-!
# Mitchell, Allman, Rhodes 2019, Theorem 3.1, for the trinomial cut model

J. D. Mitchell, E. S. Allman, J. A. Rhodes, *Hypothesis testing near singularities and boundaries*,
Electron. J. Stat. 13 (2019), 2150–2193.

Theorem 3.1 of the source is a general theorem: on a regular model, the likelihood ratio statistic and
the difference of the least squared distances from a normal sample to the scaled models converge in
distribution to the same limit. Its proof rests on van der Vaart, *Asymptotic Statistics*, Theorem
16.7, and so on differentiability in quadratic mean, local asymptotic normality and the convergence of
maximum likelihood estimates, which Mathlib lacks.

`cutModel_theorem31` is the special case that TINNiK's Proposition 5 uses, proved directly from the
central limit theorem: the model is the trinomial, the null is the union of the three cut lines and
the true point is `(1 - 2φ/3, φ/3, φ/3)`. In the coordinates of TINNiK Appendix C.2 the alternative is
the whole plane, so that its distance term vanishes, and the lines are `x = 0`, `y = ± γ x`.

The proof: the frequencies, whitened and centred (`Phylogenetics.Trinomial.sampleW`), converge to two
independent normals, and each statistic of the three lines is close to a squared distance, uniformly
on bounded sets of the whitened frequencies (`src/Basic/Testing/Trinomial/`).
-/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open Phylogenetics Phylogenetics.Trinomial

namespace External.MitchellAllmanRhodes2019

/-- The squared distance from `z` to the line `y = γ x` of the plane. -/
def lineDistSq (γ : ℝ) (z : ℝ × ℝ) : ℝ := ⨅ x : ℝ, (z.1 - x) ^ 2 + (z.2 - γ * x) ^ 2

/-- The least squared distance from `z` to the three lines `x = 0`, `y = γ x`, `y = -γ x`. -/
def threeLineDistSq (γ : ℝ) (z : ℝ × ℝ) : ℝ :=
  min (z.1 ^ 2) (min (lineDistSq γ z) (lineDistSq (-γ) z))

/-- The normal sample `N((0, μ), I)`. -/
abbrev normalSample (μ : ℝ) : Measure (ℝ × ℝ) := (gaussianReal 0 1).prod (gaussianReal μ 1)

instance (μ : ℝ) : IsProbabilityMeasure (normalSample μ) := by
  unfold normalSample
  infer_instance

/-- The distance to a line, in closed form. -/
theorem lineDistSq_eq (γ : ℝ) (z : ℝ × ℝ) : lineDistSq γ z = (γ * z.1 - z.2) ^ 2 / (1 + γ ^ 2) := by
  have hpos : 0 < 1 + γ ^ 2 := by positivity
  have hid : ∀ x : ℝ, (z.1 - x) ^ 2 + (z.2 - γ * x) ^ 2 =
      (1 + γ ^ 2) * (x - (z.1 + γ * z.2) / (1 + γ ^ 2)) ^ 2 + (γ * z.1 - z.2) ^ 2 / (1 + γ ^ 2) := by
    intro x
    field_simp
    ring
  unfold lineDistSq
  refine le_antisymm ?_ ?_
  · refine (ciInf_le ⟨(γ * z.1 - z.2) ^ 2 / (1 + γ ^ 2), ?_⟩ ((z.1 + γ * z.2) / (1 + γ ^ 2))).trans ?_
    · rintro _ ⟨x, rfl⟩
      simp only [hid]
      have : 0 ≤ (1 + γ ^ 2) * (x - (z.1 + γ * z.2) / (1 + γ ^ 2)) ^ 2 := by positivity
      linarith
    · rw [hid]
      simp
  · refine le_ciInf fun x ↦ ?_
    rw [hid]
    have : 0 ≤ (1 + γ ^ 2) * (x - (z.1 + γ * z.2) / (1 + γ ^ 2)) ^ 2 := by positivity
    linarith

theorem lineDistSq_tan {α : ℝ} (hα : Real.cos α ≠ 0) (z : ℝ × ℝ) :
    lineDistSq (Real.tan α) z = (Real.sin α * z.1 - Real.cos α * z.2) ^ 2 := by
  rw [lineDistSq_eq]
  have hs : Real.cos α ^ 2 + Real.sin α ^ 2 = 1 := Real.cos_sq_add_sin_sq α
  rw [Real.tan_eq_sin_div_cos]
  field_simp
  rw [hs]
  ring

theorem lineDistSq_neg_tan {α : ℝ} (hα : Real.cos α ≠ 0) (z : ℝ × ℝ) :
    lineDistSq (-Real.tan α) z = (Real.sin α * z.1 + Real.cos α * z.2) ^ 2 := by
  rw [lineDistSq_eq]
  have hs : Real.cos α ^ 2 + Real.sin α ^ 2 = 1 := Real.cos_sq_add_sin_sq α
  rw [Real.tan_eq_sin_div_cos]
  field_simp
  rw [hs]
  ring

theorem continuous_threeLineDistSq {α : ℝ} (hα : Real.cos α ≠ 0) :
    Continuous (threeLineDistSq (Real.tan α)) := by
  have : threeLineDistSq (Real.tan α) = fun z ↦ min (z.1 ^ 2)
      (min ((Real.sin α * z.1 - Real.cos α * z.2) ^ 2) ((Real.sin α * z.1 + Real.cos α * z.2) ^ 2)) := by
    funext z
    unfold threeLineDistSq
    rw [lineDistSq_tan hα, lineDistSq_neg_tan hα]
  rw [this]
  fun_prop

/-- The whitened normal sample has the standard law. -/
theorem normalSample_map_sub (μ : ℝ) :
    (normalSample μ).map (fun z : ℝ × ℝ ↦ (z.1, z.2 - μ)) = stdPlane := by
  have h : (fun z : ℝ × ℝ ↦ (z.1, z.2 - μ)) = Prod.map id (fun y ↦ y - μ) := rfl
  have h₁ : (gaussianReal μ 1).map (fun y ↦ y - μ) = gaussianReal 0 1 := by
    rw [gaussianReal_map_sub_const, sub_self]
  rw [h, normalSample, ← Measure.map_prod_map _ _ measurable_id (by fun_prop), h₁, Measure.map_id]
  rfl

private theorem cos_alphaZero_pos (φ : ℝ) : 0 < Real.cos (alphaZero φ) := Real.cos_arctan_pos _

private lemma sq_lt_of_abs_lt {x R : ℝ} (hx : |x| < R) : x ^ 2 < R ^ 2 := by
  rw [← sq_abs x]
  exact pow_lt_pow_left₀ hx (abs_nonneg x) two_ne_zero

private lemma sq_ge_of_le_abs {x R : ℝ} (hR : 0 ≤ R) (hx : R ≤ |x|) : R ^ 2 ≤ x ^ 2 := by
  rw [← sq_abs x]
  exact pow_le_pow_left₀ hR hx 2

/-- Off the centroid, the mean of the normal sample is large, and the distance to the three lines is
the distance to the line `x = 0`. -/
private theorem closeOnBalls_normalSample {φ : ℝ} (hφ : 0 < φ ∧ φ < 3 / 2) (hφ1 : φ ≠ 1) :
    CloseOnBalls (Ω := fun _ ↦ ℝ × ℝ) (fun (n : ℕ) (z : ℝ × ℝ) ↦ (z.1, z.2 - muZero φ n))
      (fun _ z ↦ threeLineDistSq (Real.tan (alphaZero φ)) z) (fun z ↦ z.1 ^ 2) := by
  intro R hR ε hε
  have hc := cos_alphaZero_pos φ
  set c := Real.cos (alphaZero φ) with hcdef
  have hgap : 0 < |1 - φ| * (2 / 3) := by
    have := abs_pos.2 (sub_ne_zero.2 hφ1.symm)
    positivity
  have hsqrt : Tendsto (fun n : ℕ ↦ √(2 * (n : ℝ))) atTop atTop := by
    refine Real.tendsto_sqrt_atTop.comp ?_
    exact Tendsto.const_mul_atTop (by norm_num) tendsto_natCast_atTop_atTop
  filter_upwards [hsqrt.eventually_ge_atTop ((R + 2 * R / c) / (|1 - φ| * (2 / 3)))] with n hn z hz₁ hz₂
  have hz₁ : |z.1| < R := hz₁
  have hz₂ : |z.2 - muZero φ n| < R := hz₂
  have hμ := abs_muZero_ge (m := n) hφ.1 hφ.2
  rw [div_le_iff₀ hgap] at hn
  have hμ' : R + 2 * R / c ≤ |muZero φ n| := by nlinarith
  have hz₂' : |z.2| ≥ |muZero φ n| - R := by
    have := abs_sub_abs_le_abs_sub (muZero φ n) z.2
    rw [abs_sub_comm (muZero φ n) z.2] at this
    linarith
  have hyb : 2 * R ≤ c * |z.2| := by
    have h₁ : 2 * R / c ≤ |z.2| := by linarith
    rw [div_le_iff₀ hc] at h₁
    linarith
  have hcabs : c * |z.2| = |c * z.2| := by rw [abs_mul, abs_of_pos hc]
  have hsx : |Real.sin (alphaZero φ) * z.1| ≤ R := by
    rw [abs_mul]
    have h₁ := Real.abs_sin_le_one (alphaZero φ)
    calc |Real.sin (alphaZero φ)| * |z.1| ≤ 1 * R := by gcongr
      _ = R := one_mul _
  have hd₁ : R ≤ |Real.sin (alphaZero φ) * z.1 - c * z.2| := by
    have := abs_sub_abs_le_abs_sub (c * z.2) (Real.sin (alphaZero φ) * z.1)
    rw [abs_sub_comm] at this
    linarith
  have hd₂ : R ≤ |Real.sin (alphaZero φ) * z.1 + c * z.2| := by
    have := abs_sub_abs_le_abs_sub (c * z.2) (-(Real.sin (alphaZero φ) * z.1))
    rw [abs_neg, sub_neg_eq_add, add_comm] at this
    linarith
  have hsq₁ := sq_lt_of_abs_lt hz₁
  have hsq₂ := sq_ge_of_le_abs hR.le hd₁
  have hsq₃ := sq_ge_of_le_abs hR.le hd₂
  have hval : threeLineDistSq (Real.tan (alphaZero φ)) z = z.1 ^ 2 := by
    unfold threeLineDistSq
    rw [lineDistSq_tan hc.ne', lineDistSq_neg_tan hc.ne', ← hcdef]
    exact min_eq_left (le_min (hsq₁.le.trans hsq₂) (hsq₁.le.trans hsq₃))
  change |threeLineDistSq (Real.tan (alphaZero φ)) z - z.1 ^ 2| < ε
  rw [hval, sub_self, abs_zero]
  exact hε

private theorem alphaZero_one : alphaZero 1 = Real.pi / 6 := by
  have h : (1 : ℝ) / √(3 * (3 - 2 * 1)) = (√3)⁻¹ := by norm_num
  unfold alphaZero
  rw [h, Real.arctan_inv_sqrt_three]

private theorem threeLineDistSq_centroid (z : ℝ × ℝ) :
    threeLineDistSq (Real.tan (alphaZero 1)) z = centroidLimit z := by
  have hc := cos_alphaZero_pos 1
  unfold threeLineDistSq centroidLimit
  rw [lineDistSq_tan hc.ne', lineDistSq_neg_tan hc.ne', alphaZero_one, Real.sin_pi_div_six,
    Real.cos_pi_div_six, min_comm ((1 / 2 * z.1 - √3 / 2 * z.2) ^ 2)]

private theorem muZero_one (n : ℝ) : muZero 1 n = 0 := by
  simp [muZero]

/-- **Theorem 3.1 of the source, for the trinomial cut model.** For the true point
`θ₀ = (1 - 2φ/3, φ/3, φ/3)`, `0 < φ < 3/2`, the likelihood ratio statistic of the cut model, the least
of the statistics of its three lines, and the least squared distance from the normal sample
`N((0, μ₀(n)), I)` to the lines `x = 0`, `y = ± (tan α₀) x` converge in distribution to the same limit.

Departure from the source: Theorem 3.1 is a general theorem on regular models, through van der Vaart,
*Asymptotic Statistics*, Theorem 16.7, which needs a theory of differentiability in quadratic mean that
Mathlib lacks. This is the statement that the source's theorem gives for this model (with
the alternative model's distance term zero, and the model's segments replaced by whole lines, as in
TINNiK's proof of Proposition 5), proved directly from the central limit theorem. -/
theorem cutModel_theorem31 {φ : ℝ} (hφ : 0 < φ ∧ φ < 3 / 2) : ∃ ν : ProbabilityMeasure ℝ,
    (∀ f : BoundedContinuousFunction ℝ ℝ,
      Tendsto (fun n : ℕ ↦ ∫ x, f x ∂((Measure.pi fun _ : Fin n ↦
          (cutPoint_isDist hφ).toPMF.toMeasure).map fun η ↦ cutS (count η 0) (count η 1) (count η 2)))
        atTop (𝓝 (∫ x, f x ∂(ν : Measure ℝ)))) ∧
    (∀ f : BoundedContinuousFunction ℝ ℝ,
      Tendsto (fun n : ℕ ↦ ∫ x, f x ∂((normalSample (muZero φ n)).map
          (threeLineDistSq (Real.tan (alphaZero φ))))) atTop (𝓝 (∫ x, f x ∂(ν : Measure ℝ)))) := by
  have hclt := tendstoInDistribution_sampleW hφ
  have hSm : ∀ n : ℕ, AEMeasurable (fun η : Fin n → Fin 3 ↦ cutS (count η 0) (count η 1) (count η 2))
      (Measure.pi fun _ : Fin n ↦ (cutPoint_isDist hφ).toPMF.toMeasure) :=
    fun n ↦ Measurable.of_discrete.aemeasurable
  by_cases hφ1 : φ = 1
  · subst hφ1
    refine ⟨⟨stdPlane.map centroidLimit, inferInstance⟩, fun f ↦ ?_, fun f ↦ ?_⟩
    · exact ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.1
        (tendstoInDistribution_of_closeOnBalls hclt hSm continuous_centroidLimit
          closeOnBalls_cutS_centroid).tendsto f
    · have hfun : threeLineDistSq (Real.tan (alphaZero 1)) = centroidLimit :=
        funext threeLineDistSq_centroid
      have hsample : ∀ n : ℕ, normalSample (muZero 1 n) = stdPlane := by
        intro n
        rw [muZero_one]
        rfl
      simp only [hfun, hsample]
      exact tendsto_const_nhds
  · have hT : Continuous fun z : ℝ × ℝ ↦ z.1 ^ 2 := by fun_prop
    refine ⟨⟨stdPlane.map fun z ↦ z.1 ^ 2, inferInstance⟩, fun f ↦ ?_, fun f ↦ ?_⟩
    · exact ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.1
        (tendstoInDistribution_of_closeOnBalls hclt hSm hT
          (closeOnBalls_cutS_of_ne hφ hφ1)).tendsto f
    · have hlaw : TendstoInDistribution (fun (n : ℕ) (z : ℝ × ℝ) ↦ (z.1, z.2 - muZero φ n)) atTop
          (fun z : ℝ × ℝ ↦ z) (fun n : ℕ ↦ normalSample (muZero φ n)) stdPlane := by
        refine ⟨fun n ↦ (by fun_prop), by fun_prop, ?_⟩
        simp only [normalSample_map_sub]
        have : stdPlane.map (fun z : ℝ × ℝ ↦ z) = stdPlane := Measure.map_id'
        simp only [this]
        exact tendsto_const_nhds
      exact ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.1
        (tendstoInDistribution_of_closeOnBalls hlaw
          (S := fun (_ : ℕ) (z : ℝ × ℝ) ↦ threeLineDistSq (Real.tan (alphaZero φ)) z)
          (fun n ↦ (continuous_threeLineDistSq (cos_alphaZero_pos φ).ne').aemeasurable)
          hT (closeOnBalls_normalSample hφ hφ1)).tendsto f

end External.MitchellAllmanRhodes2019
