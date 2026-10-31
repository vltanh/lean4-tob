module

public import TINNiK.Statistics.Definitions
public import External.MitchellAllmanRhodes2019.CutModel
public import Basic.Analysis.SpecialFunctions.GibbsInequality
public import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

/-!
# TINNiK Appendix C: the cut test

The maximum likelihood estimates and maximal log-likelihoods of Appendix C.1, and Proposition 5 of
Appendix C.2 (Proposition 6 is in `TINNiK/Statistics/Proposition6.lean`). The maximum likelihood estimate on the cut model is over the closed simplex, as agreed
with the user: on the open cut model of Definition 7 no maximum exists for counts such as `(1, 0, 0)`
(E9 of the report). The generating parameter stays in the open simplex.
-/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

namespace TINNiK

/-! ### Helpers on the lines -/

private lemma exists_other (i : Fin 3) : i + 1 ≠ i := by
  revert i
  decide

private lemma sampleSize_cast (m : Counts) : (sampleSize m : ℝ) = ∑ j, (m j : ℝ) := by
  simp [sampleSize]

private lemma sampleSize_cast_eq (m : Counts) (i : Fin 3) :
    (sampleSize m : ℝ) = m i + otherCount m i := by
  have := otherCount_add m i
  rw [← this]
  push_cast
  ring

private lemma likelihood_on_line (m : Counts) {i : Fin 3} {q : Coordinates} (hq : OnCutLine i q) :
    likelihood m q = q i ^ m i * q (i + 1) ^ otherCount m i := by
  unfold likelihood otherCount
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i)]
  congr 1
  rw [← Finset.prod_pow_eq_pow_sum]
  refine Finset.prod_congr rfl fun j hj ↦ ?_
  rw [hq j (i + 1) (Finset.ne_of_mem_erase hj) (exists_other i)]

private lemma sum_on_line {i : Fin 3} {q : Coordinates} (hq : OnCutLine i q) :
    ∑ j, q j = q i + 2 * q (i + 1) := by
  rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ i)]
  congr 1
  rw [Finset.sum_congr rfl fun j hj ↦ hq j (i + 1) (Finset.ne_of_mem_erase hj) (exists_other i)]
  simp [Finset.card_erase_of_mem]

private lemma cutLineMLE_self (m : Counts) (i : Fin 3) :
    cutLineMLE m i i = (m i : ℝ) / sampleSize m := by
  simp [cutLineMLE]

private lemma cutLineMLE_other (m : Counts) {i j : Fin 3} (hj : j ≠ i) :
    cutLineMLE m i j = (otherCount m i : ℝ) / (2 * sampleSize m) := by
  simp [cutLineMLE, hj]

private lemma cutLineMLE_onLine (m : Counts) (i : Fin 3) : OnCutLine i (cutLineMLE m i) := by
  intro j k hj hk
  rw [cutLineMLE_other m hj, cutLineMLE_other m hk]

/-- **Appendix C.1** (`tinnik:cut_line_mle`). The maximum on the closed line of the trinomial
likelihood, at the projection of the empirical CF. -/
theorem cutLineMLE_maximizes (m : Counts) (hm : 0 < sampleSize m) (i : Fin 3) :
    ClosedSimplex (cutLineMLE m i) ∧ OnCutLine i (cutLineMLE m i) ∧
      ∀ p : Coordinates, ClosedSimplex p → OnCutLine i p →
        likelihood m p ≤ likelihood m (cutLineMLE m i) := by
  have hN : (0 : ℝ) < sampleSize m := by exact_mod_cast hm
  have hline := cutLineMLE_onLine m i
  have hsplit := sampleSize_cast_eq m i
  refine ⟨⟨fun j ↦ ?_, ?_⟩, hline, fun p hp hpl ↦ ?_⟩
  · by_cases hj : j = i
    · rw [hj, cutLineMLE_self]
      positivity
    · rw [cutLineMLE_other m hj]
      positivity
  · rw [sum_on_line hline, cutLineMLE_self, cutLineMLE_other m (exists_other i)]
    field_simp
    linarith
  · have hsum := sum_on_line hpl
    rw [hp.2] at hsum
    let m' : Fin 2 → ℕ := ![m i, otherCount m i]
    let p' : Fin 2 → ℝ := ![p i, 2 * p (i + 1)]
    have hN' : 0 < ∑ j, (m' j : ℝ) := by
      simp only [m', Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
      rw [← hsplit]
      exact hN
    have hg := Real.prod_pow_le_prod_div_pow m' (p := p')
      (by
        intro j
        fin_cases j
        · exact hp.1 i
        · exact mul_nonneg (by norm_num) (hp.1 _))
      (by
        simp only [p', Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
        linarith) hN'
    simp only [m', p', Fin.prod_univ_two, Fin.sum_univ_two, Matrix.cons_val_zero,
      Matrix.cons_val_one] at hg
    rw [← hsplit] at hg
    rw [likelihood_on_line m hpl, likelihood_on_line m hline, cutLineMLE_self,
      cutLineMLE_other m (exists_other i)]
    have h2 : ((otherCount m i : ℝ) / sampleSize m) ^ otherCount m i =
        2 ^ otherCount m i * ((otherCount m i : ℝ) / (2 * sampleSize m)) ^ otherCount m i := by
      rw [← mul_pow]
      congr 1
      field_simp
    rw [mul_pow, h2] at hg
    have h3 : (0 : ℝ) < 2 ^ otherCount m i := by positivity
    have h4 : (2 : ℝ) ^ otherCount m i * (p i ^ m i * p (i + 1) ^ otherCount m i) ≤
        2 ^ otherCount m i * (((m i : ℝ) / sampleSize m) ^ m i *
          ((otherCount m i : ℝ) / (2 * sampleSize m)) ^ otherCount m i) := by
      calc _ = p i ^ m i * (2 ^ otherCount m i * p (i + 1) ^ otherCount m i) := by ring
        _ ≤ _ := hg
        _ = _ := by ring
    exact le_of_mul_le_mul_left h4 h3

/-- The estimate on the line is in the open simplex precisely when the counts allow it. -/
theorem cutLineMLE_open_iff (m : Counts) (hm : 0 < sampleSize m) (i : Fin 3) :
    OpenSimplex (cutLineMLE m i) ↔ 0 < m i ∧ 0 < otherCount m i := by
  have hN : (0 : ℝ) < sampleSize m := by exact_mod_cast hm
  obtain ⟨hclosed, -, -⟩ := cutLineMLE_maximizes m hm i
  constructor
  · intro h
    constructor
    · have := h.1 i
      rw [cutLineMLE_self] at this
      have h₁ : (0 : ℝ) < m i := by
        by_contra hcon
        have h₀ : (m i : ℝ) = 0 := le_antisymm (not_lt.1 hcon) (Nat.cast_nonneg _)
        simp [h₀] at this
      exact_mod_cast h₁
    · have := h.1 (i + 1)
      rw [cutLineMLE_other m (exists_other i)] at this
      have h₁ : (0 : ℝ) < otherCount m i := by
        by_contra hcon
        have h₀ : (otherCount m i : ℝ) = 0 := le_antisymm (not_lt.1 hcon) (Nat.cast_nonneg _)
        simp [h₀] at this
      exact_mod_cast h₁
  · rintro ⟨h₁, h₂⟩
    refine ⟨fun j ↦ ?_, hclosed.2⟩
    have h₁' : (0 : ℝ) < m i := by exact_mod_cast h₁
    have h₂' : (0 : ℝ) < otherCount m i := by exact_mod_cast h₂
    by_cases hj : j = i
    · rw [hj, cutLineMLE_self]
      positivity
    · rw [cutLineMLE_other m hj]
      positivity

/-- The unconstrained maximum of the likelihood is at the empirical CF. -/
theorem empiricalCF_maximizes (m : Counts) (hm : 0 < sampleSize m) :
    ClosedSimplex (empiricalCF m) ∧
      ∀ p : Coordinates, ClosedSimplex p → likelihood m p ≤ likelihood m (empiricalCF m) := by
  have hN : (0 : ℝ) < sampleSize m := by exact_mod_cast hm
  have hcast := sampleSize_cast m
  refine ⟨⟨fun j ↦ ?_, ?_⟩, fun p hp ↦ ?_⟩
  · unfold empiricalCF
    positivity
  · unfold empiricalCF
    rw [← Finset.sum_div, ← hcast, div_self hN.ne']
  · have hg := Real.prod_pow_le_prod_div_pow m hp.1 hp.2.le (by rw [← hcast]; exact hN)
    rw [← hcast] at hg
    exact hg

private lemma xlogx_eq (x : ℝ) : xlogx x = x * Real.log x := by
  unfold xlogx
  split_ifs with h
  · simp [h]
  · rfl

/-- **Appendix C.1** (`tinnik:cut_log_likelihood`), the maximal log-likelihood on a line, with
the constant `C` omitted, for counts with the estimate positive. -/
theorem lineMaxLogLikelihood_eq (m : Counts) (hm : 0 < sampleSize m) (i : Fin 3)
    (hi : 0 < m i) (ho : ∀ j, j ≠ i → 0 < m j) :
    lineMaxLogLikelihood m i = Real.log (likelihood m (cutLineMLE m i)) := by
  have hN : (0 : ℝ) < sampleSize m := by exact_mod_cast hm
  have hi' : (0 : ℝ) < m i := by exact_mod_cast hi
  have ho' : (0 : ℝ) < otherCount m i := by
    have h₁ : m (i + 1) ≤ otherCount m i :=
      Finset.single_le_sum (f := m) (fun _ _ ↦ Nat.zero_le _)
        (Finset.mem_erase.2 ⟨exists_other i, Finset.mem_univ _⟩)
    have h₂ := ho _ (exists_other i)
    exact_mod_cast lt_of_lt_of_le h₂ h₁
  have hsplit := sampleSize_cast_eq m i
  rw [likelihood_on_line m (cutLineMLE_onLine m i), cutLineMLE_self,
    cutLineMLE_other m (exists_other i), Real.log_mul (by positivity) (by positivity),
    Real.log_pow, Real.log_pow, Real.log_div hi'.ne' hN.ne',
    Real.log_div ho'.ne' (by positivity), Real.log_mul two_ne_zero hN.ne']
  unfold lineMaxLogLikelihood
  rw [xlogx_eq, xlogx_eq, xlogx_eq]
  have e : (sampleSize m : ℝ) * Real.log (sampleSize m) =
      ((m i : ℝ) + otherCount m i) * Real.log (sampleSize m) := by rw [← hsplit]
  rw [e]
  ring

/-- **Appendix C.1** (`tinnik:full_log_likelihood`), the unconstrained maximal log-likelihood, with
the constant `C` omitted, for positive counts. -/
theorem fullMaxLogLikelihood_eq (m : Counts) (hm : ∀ i, 0 < m i) :
    fullMaxLogLikelihood m = Real.log (likelihood m (empiricalCF m)) := by
  have hm' : ∀ i, (0 : ℝ) < m i := fun i ↦ by exact_mod_cast hm i
  have hN : (0 : ℝ) < sampleSize m := by
    rw [sampleSize_cast]
    exact Finset.sum_pos (fun i _ ↦ hm' i) Finset.univ_nonempty
  unfold likelihood empiricalCF fullMaxLogLikelihood
  rw [Real.log_prod (fun i _ ↦ pow_ne_zero _ (div_pos (hm' i) hN).ne')]
  simp only [Real.log_pow, Real.log_div (hm' _).ne' hN.ne', xlogx_eq, mul_sub, Finset.sum_sub_distrib]
  rw [← Finset.sum_mul, ← sampleSize_cast]

private lemma otherCount_cast_zero (m : Counts) : (otherCount m 0 : ℝ) = m 1 + m 2 := by
  have : (Finset.univ.erase (0 : Fin 3)) = {1, 2} := by decide
  simp [otherCount, this]

private lemma otherCount_cast_one (m : Counts) : (otherCount m 1 : ℝ) = m 0 + m 2 := by
  have : (Finset.univ.erase (1 : Fin 3)) = {0, 2} := by decide
  simp [otherCount, this]

private lemma otherCount_cast_two (m : Counts) : (otherCount m 2 : ℝ) = m 0 + m 1 := by
  have : (Finset.univ.erase (2 : Fin 3)) = {0, 1} := by decide
  simp [otherCount, this]

/-- The likelihood ratio statistic is the least of the statistics of the three lines. -/
theorem likelihoodRatio_eq_cutS (m : Counts) :
    likelihoodRatio m = Phylogenetics.Trinomial.cutS (m 0) (m 1) (m 2) := by
  have hF := Fin.sum_univ_three (fun i ↦ xlogx (m i : ℝ))
  unfold likelihoodRatio cutMaxLogLikelihood fullMaxLogLikelihood lineMaxLogLikelihood
    Phylogenetics.Trinomial.cutS Phylogenetics.Trinomial.lineS
  rw [hF, otherCount_cast_zero, otherCount_cast_one, otherCount_cast_two, ← min_sub_sub_left,
    ← min_sub_sub_left, mul_min_of_nonneg _ _ (by norm_num), mul_min_of_nonneg _ _ (by norm_num)]
  simp only [xlogx_eq]
  congr 1
  · ring
  · congr 1 <;> ring

/-- The likelihood ratio statistic is nonnegative. -/
theorem likelihoodRatio_nonneg (m : Counts) : 0 ≤ likelihoodRatio m := by
  rw [likelihoodRatio_eq_cutS]
  unfold Phylogenetics.Trinomial.cutS
  exact le_min (Phylogenetics.Trinomial.lineS_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
    (le_min (Phylogenetics.Trinomial.lineS_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
      (Phylogenetics.Trinomial.lineS_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)))

/-- The closest point to `(z₁, z₂)` on the line `y = γ x`, in the proof of Proposition 5. -/
theorem line_projection_minimizes (γ z₁ z₂ : ℝ) :
    let x₀ := (z₁ + γ * z₂) / (1 + γ ^ 2)
    ∀ x : ℝ, (z₁ - x₀) ^ 2 + (z₂ - γ * x₀) ^ 2 ≤ (z₁ - x) ^ 2 + (z₂ - γ * x) ^ 2 := by
  intro x₀ x
  have hpos : 0 < 1 + γ ^ 2 := by positivity
  have hid : (z₁ - x) ^ 2 + (z₂ - γ * x) ^ 2 =
      (z₁ - x₀) ^ 2 + (z₂ - γ * x₀) ^ 2 + (1 + γ ^ 2) * (x - x₀) ^ 2 := by
    have hx₀ : (1 + γ ^ 2) * x₀ = z₁ + γ * z₂ := by
      simp only [x₀]
      field_simp
    clear_value x₀
    linear_combination (2 * x - 2 * x₀) * hx₀
  rw [hid]
  have : 0 ≤ (1 + γ ^ 2) * (x - x₀) ^ 2 := by positivity
  linarith

/-- The squared distance to the line `y = tan α₀ · x`, in the proof of Proposition 5. -/
theorem line_projection_distance (φ : ℝ) (z₁ z₂ : ℝ) :
    let γ := Real.tan (alpha0 φ)
    let x₀ := (z₁ + γ * z₂) / (1 + γ ^ 2)
    (z₁ - x₀) ^ 2 + (z₂ - γ * x₀) ^ 2 =
      (Real.sin (alpha0 φ) * z₁ - Real.cos (alpha0 φ) * z₂) ^ 2 := by
  intro γ x₀
  have hc : Real.cos (alpha0 φ) ≠ 0 := (Real.cos_arctan_pos _).ne'
  have hs : Real.cos (alpha0 φ) ^ 2 + Real.sin (alpha0 φ) ^ 2 = 1 := Real.cos_sq_add_sin_sq _
  have hγ : γ = Real.sin (alpha0 φ) / Real.cos (alpha0 φ) := Real.tan_eq_sin_div_cos _
  have hpos : 0 < 1 + γ ^ 2 := by positivity
  have hx₀ : (1 + γ ^ 2) * x₀ = z₁ + γ * z₂ := by
    simp only [x₀]
    field_simp
  have hval : (z₁ - x₀) ^ 2 + (z₂ - γ * x₀) ^ 2 = (γ * z₁ - z₂) ^ 2 / (1 + γ ^ 2) := by
    simp only [x₀]
    field_simp
    ring
  rw [hval, hγ]
  field_simp
  rw [hs]
  ring

/-- The law of the likelihood ratio statistic of a sample of size `n` from `θ₀`. -/
def lrLaw (φ : ℝ) (hφ : 0 < φ ∧ φ < 3 / 2) (n : ℕ) : Measure ℝ :=
  (sampleMeasure (thetaCF φ hφ) n).map fun ω => likelihoodRatio (sampleCounts ω)

/-- The law of `Λ_n`. -/
def lambdaLaw (φ : ℝ) (n : ℕ) : Measure ℝ := (gaussianPlane φ n).map (lambdaCandidate φ)

/-- The distance to a line is attained at a minimizer. -/
private lemma iInf_eq_of_minimizes {f : ℝ → ℝ} {x₀ : ℝ} (h : ∀ x, f x₀ ≤ f x) : ⨅ x, f x = f x₀ :=
  le_antisymm (ciInf_le ⟨f x₀, by rintro _ ⟨x, rfl⟩; exact h x⟩ x₀) (le_ciInf h)

open External.MitchellAllmanRhodes2019 in
/-- The distances of the proof of Proposition 5: the squared distances from the sample point to the
three lines are the three terms of `Λ_n`, by the projections. -/
private theorem threeLineDistSq_eq_lambdaCandidate (φ : ℝ) (z : ℝ × ℝ) :
    threeLineDistSq (Real.tan (alpha0 φ)) z = lambdaCandidate φ z := by
  have h₁ : lineDistSq (Real.tan (alpha0 φ)) z =
      (Real.sin (alpha0 φ) * z.1 - Real.cos (alpha0 φ) * z.2) ^ 2 := by
    unfold lineDistSq
    rw [iInf_eq_of_minimizes (line_projection_minimizes (Real.tan (alpha0 φ)) z.1 z.2)]
    exact line_projection_distance φ z.1 z.2
  have h₂ : lineDistSq (-Real.tan (alpha0 φ)) z =
      (Real.sin (alpha0 φ) * z.1 + Real.cos (alpha0 φ) * z.2) ^ 2 := by
    unfold lineDistSq
    rw [iInf_eq_of_minimizes (line_projection_minimizes (-Real.tan (alpha0 φ)) z.1 z.2)]
    have h₃ := line_projection_distance φ (-z.1) z.2
    simp only at h₃
    have e : (-z.1 + Real.tan (alpha0 φ) * z.2) / (1 + Real.tan (alpha0 φ) ^ 2) =
        -((z.1 + -Real.tan (alpha0 φ) * z.2) / (1 + (-Real.tan (alpha0 φ)) ^ 2)) := by
      rw [neg_sq]
      ring
    rw [e] at h₃
    calc _ = (-z.1 - -((z.1 + -Real.tan (alpha0 φ) * z.2) / (1 + (-Real.tan (alpha0 φ)) ^ 2))) ^ 2 +
          (z.2 - Real.tan (alpha0 φ) *
            -((z.1 + -Real.tan (alpha0 φ) * z.2) / (1 + (-Real.tan (alpha0 φ)) ^ 2))) ^ 2 := by ring
      _ = _ := by rw [h₃]; ring
  unfold threeLineDistSq lambdaCandidate
  rw [h₁, h₂, min_comm ((Real.sin (alpha0 φ) * z.1 - Real.cos (alpha0 φ) * z.2) ^ 2)]

/-- **Proposition 5** (`tinnik:proposition5`). The likelihood ratio statistic for a true parameter
`θ₀ = (1 - 2φ₀/3, φ₀/3, φ₀/3)`, `φ₀ ∈ (0, 3/2)`, of the cut model, with sample size `n`, and the random
variable `Λ_n = min(Z², (sin α₀ Z + cos α₀ Z̄)², (sin α₀ Z - cos α₀ Z̄)²)`, where `Z ~ N(0,1)`,
`Z̄ ~ N(μ₀(n), 1)` are independent, converge in distribution to the same limit.

The proof is the paper's: the likelihood ratio statistic and the least squared distance from the normal
sample `N((0, μ₀), I)` to the three lines `x = 0`, `y = ± γ₀ x` have the same limit; the distances to
the lines are computed by the projections (`line_projection_minimizes`, `line_projection_distance`);
the minimum is `Λ_n`.

Departure from the paper: it takes the first step from Theorem 3.1 of Mitchell, Allman, Rhodes 2019,
which rests on a general theory (van der Vaart, *Asymptotic Statistics*, Theorem 16.7) that Mathlib
lacks. Here that step is the special case for this model,
`External.MitchellAllmanRhodes2019.cutModel_theorem31`, proved directly from the central limit
theorem; in it, the replacement of the segments by lines is part of the proof, not a further step. -/
theorem proposition5 (φ : ℝ) (hφ : 0 < φ ∧ φ < 3 / 2) : ∃ ν : ProbabilityMeasure ℝ,
    (∀ f : BoundedContinuousFunction ℝ ℝ,
      Tendsto (fun n => ∫ x, f x ∂(lrLaw φ hφ n)) atTop (𝓝 (∫ x, f x ∂(ν : Measure ℝ)))) ∧
    (∀ f : BoundedContinuousFunction ℝ ℝ,
      Tendsto (fun n => ∫ x, f x ∂(lambdaLaw φ n)) atTop (𝓝 (∫ x, f x ∂(ν : Measure ℝ)))) := by
  obtain ⟨ν, h₁, h₂⟩ := External.MitchellAllmanRhodes2019.cutModel_theorem31 hφ
  refine ⟨ν, fun f ↦ (h₁ f).congr fun n ↦ ?_, fun f ↦ (h₂ f).congr fun n ↦ ?_⟩
  · have hlaw : lrLaw φ hφ n = (Measure.pi fun _ : Fin n ↦
        (Phylogenetics.Trinomial.cutPoint_isDist hφ).toPMF.toMeasure).map fun η ↦
          Phylogenetics.Trinomial.cutS (Phylogenetics.Trinomial.count η 0)
            (Phylogenetics.Trinomial.count η 1) (Phylogenetics.Trinomial.count η 2) := by
      unfold lrLaw
      have hfun : (fun ω : Fin n → Fin 3 ↦ likelihoodRatio (sampleCounts ω)) = fun η ↦
          Phylogenetics.Trinomial.cutS (Phylogenetics.Trinomial.count η 0)
            (Phylogenetics.Trinomial.count η 1) (Phylogenetics.Trinomial.count η 2) := by
        funext ω
        rw [likelihoodRatio_eq_cutS]
        rfl
      rw [hfun]
      rfl
    rw [hlaw]
  · have hlaw : lambdaLaw φ n = (External.MitchellAllmanRhodes2019.normalSample
        (Phylogenetics.muZero φ n)).map
          (External.MitchellAllmanRhodes2019.threeLineDistSq
            (Real.tan (Phylogenetics.alphaZero φ))) := by
      unfold lambdaLaw
      have hfun : External.MitchellAllmanRhodes2019.threeLineDistSq
          (Real.tan (Phylogenetics.alphaZero φ)) = lambdaCandidate φ :=
        funext (threeLineDistSq_eq_lambdaCandidate φ)
      rw [hfun]
      rfl
    rw [hlaw]

end TINNiK
