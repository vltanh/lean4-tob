module

public import TINNiK.Statistics.Definitions
public import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

/-!
# TINNiK Appendix C: the cut test

The maximum likelihood estimates and maximal log-likelihoods of Appendix C.1, and Propositions 5 and 6
of Appendix C.2. The maximum likelihood estimate on the cut model is over the closed simplex, as agreed
with the user: on the open cut model of Definition 7 no maximum exists for counts such as `(1, 0, 0)`
(E9 of the report). The generating parameter stays in the open simplex.
-/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

namespace TINNiK

/-- **Appendix C.1** (`tinnik:cut_line_mle`). The maximum on the closed line of the trinomial
likelihood, at the projection of the empirical CF. -/
theorem cutLineMLE_maximizes (m : Counts) (hm : 0 < sampleSize m) (i : Fin 3) :
    ClosedSimplex (cutLineMLE m i) ∧ OnCutLine i (cutLineMLE m i) ∧
      ∀ p : Coordinates, ClosedSimplex p → OnCutLine i p →
        likelihood m p ≤ likelihood m (cutLineMLE m i) := by
  sorry

/-- The estimate on the line is in the open simplex precisely when the counts allow it. -/
theorem cutLineMLE_open_iff (m : Counts) (hm : 0 < sampleSize m) (i : Fin 3) :
    OpenSimplex (cutLineMLE m i) ↔ 0 < m i ∧ 0 < otherCount m i := by
  sorry

/-- The unconstrained maximum of the likelihood is at the empirical CF. -/
theorem empiricalCF_maximizes (m : Counts) (hm : 0 < sampleSize m) :
    ClosedSimplex (empiricalCF m) ∧
      ∀ p : Coordinates, ClosedSimplex p → likelihood m p ≤ likelihood m (empiricalCF m) := by
  sorry

/-- **Appendix C.1** (`tinnik:cut_log_likelihood`), the maximal log-likelihood on a line, with
the constant `C` omitted, for counts with the estimate positive. -/
theorem lineMaxLogLikelihood_eq (m : Counts) (hm : 0 < sampleSize m) (i : Fin 3)
    (hi : 0 < m i) (ho : ∀ j, j ≠ i → 0 < m j) :
    lineMaxLogLikelihood m i = Real.log (likelihood m (cutLineMLE m i)) := by
  sorry

/-- **Appendix C.1** (`tinnik:full_log_likelihood`), the unconstrained maximal log-likelihood, with
the constant `C` omitted, for positive counts. -/
theorem fullMaxLogLikelihood_eq (m : Counts) (hm : ∀ i, 0 < m i) :
    fullMaxLogLikelihood m = Real.log (likelihood m (empiricalCF m)) := by
  sorry

/-- The likelihood ratio statistic is nonnegative. -/
theorem likelihoodRatio_nonneg (m : Counts) : 0 ≤ likelihoodRatio m := by
  sorry

/-- The closest point to `(z₁, z₂)` on the line `y = γ x`, in the proof of Proposition 5. -/
theorem line_projection_minimizes (γ z₁ z₂ : ℝ) :
    let x₀ := (z₁ + γ * z₂) / (1 + γ ^ 2)
    ∀ x : ℝ, (z₁ - x₀) ^ 2 + (z₂ - γ * x₀) ^ 2 ≤ (z₁ - x) ^ 2 + (z₂ - γ * x) ^ 2 := by
  sorry

/-- The squared distance to the line `y = tan α₀ · x`, in the proof of Proposition 5. -/
theorem line_projection_distance (φ : ℝ) (hφ : 0 < φ ∧ φ < 3 / 2) (z₁ z₂ : ℝ) :
    let γ := Real.tan (alpha0 φ)
    let x₀ := (z₁ + γ * z₂) / (1 + γ ^ 2)
    (z₁ - x₀) ^ 2 + (z₂ - γ * x₀) ^ 2 =
      (Real.sin (alpha0 φ) * z₁ - Real.cos (alpha0 φ) * z₂) ^ 2 := by
  sorry

/-- The law of the likelihood ratio statistic of a sample of size `n` from `θ₀`. -/
def lrLaw (φ : ℝ) (hφ : 0 < φ ∧ φ < 3 / 2) (n : ℕ) : Measure ℝ :=
  (sampleMeasure (thetaCF φ hφ) n).map fun ω => likelihoodRatio (sampleCounts ω)

/-- The law of `Λ_n`. -/
def lambdaLaw (φ : ℝ) (n : ℕ) : Measure ℝ := (gaussianPlane φ n).map (lambdaCandidate φ)

/-- **Proposition 5** (`tinnik:proposition5`). The likelihood ratio statistic for a true parameter
`θ₀ = (1 - 2φ₀/3, φ₀/3, φ₀/3)`, `φ₀ ∈ (0, 3/2)`, of the cut model, with sample size `n`, and the random
variable `Λ_n = min(Z², (sin α₀ Z + cos α₀ Z̄)², (sin α₀ Z - cos α₀ Z̄)²)`, where `Z ~ N(0,1)`,
`Z̄ ~ N(μ₀(n), 1)` are independent, converge in distribution to the same limit. -/
theorem proposition5 (φ : ℝ) (hφ : 0 < φ ∧ φ < 3 / 2) : ∃ ν : ProbabilityMeasure ℝ,
    (∀ f : BoundedContinuousFunction ℝ ℝ,
      Tendsto (fun n => ∫ x, f x ∂(lrLaw φ hφ n)) atTop (𝓝 (∫ x, f x ∂(ν : Measure ℝ)))) ∧
    (∀ f : BoundedContinuousFunction ℝ ℝ,
      Tendsto (fun n => ∫ x, f x ∂(lambdaLaw φ n)) atTop (𝓝 (∫ x, f x ∂(ν : Measure ℝ)))) := by
  sorry

/-- **Proposition 6** (`tinnik:proposition6`). The law of `Λ_n` has, on `λ > 0`, the printed density.
The value `0` has mass zero, so this determines the law. -/
theorem proposition6 (φ : ℝ) (hφ : 0 < φ ∧ φ < 3 / 2) (n : ℕ) :
    (∀ lam, 0 ≤ density φ n lam) ∧
      lambdaLaw φ n = volume.withDensity (fun lam => ENNReal.ofReal (density φ n lam)) := by
  sorry

end TINNiK
