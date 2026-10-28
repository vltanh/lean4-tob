module

public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.Probability.ProbabilityMassFunction.Constructions
public import Mathlib.MeasureTheory.Constructions.Pi
public import Basic.Analysis.SpecialFunctions.Erf
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.FinCases

/-!
TINNiK probability and likelihood definitions and representation bridges.
This module does not state the paper's numbered statistical results.

The generating parameter belongs to the open probability simplex. With the
user's approval, likelihood maximization takes place on the closed simplex.
Coordinates 0,1,2 represent ab|cd, ac|bd, ad|bc in that order. This module does
not identify an arbitrary CF with a network's NMSC concordance factor.

The source's equation numbers below are publisher XML locators, not printed
numbers or original author TeX labels. Assigned labels use the prefix `tinnik:`.
-/

@[expose] public section

open scoped BigOperators ENNReal Topology
open MeasureTheory ProbabilityTheory Filter

namespace TINNiK

noncomputable section

abbrev Coordinates := Fin 3 → ℝ
abbrev Counts := Fin 3 → ℕ

/-- The paper's open simplex for true generating probabilities. -/
def OpenSimplex (p : Coordinates) : Prop :=
  (∀ i, 0 < p i) ∧ ∑ i, p i = 1

/-- The approved closed estimation simplex. -/
def ClosedSimplex (p : Coordinates) : Prop :=
  (∀ i, 0 ≤ p i) ∧ ∑ i, p i = 1

/-- Probability-vector data, with only its defining normalization/positivity laws. -/
structure ClosedCF where
  prob : Coordinates
  nonneg : ∀ i, 0 ≤ prob i
  sum_eq_one : ∑ i, prob i = 1

/-- **Definition 6** (`tinnik:def6`). Equality of some pair of CF coordinates. -/
def IsCut (p : Coordinates) : Prop := ∃ i j, i ≠ j ∧ p i = p j

/-- The cut line whose distinguished coordinate is `i`. -/
def OnCutLine (i : Fin 3) (p : Coordinates) : Prop :=
  ∀ j k, j ≠ i → k ≠ i → p j = p k

/-- Exactly the other two entries coincide and differ from the distinguished one. -/
def IsStrictlyCutAt (i : Fin 3) (p : Coordinates) : Prop :=
  OnCutLine i p ∧ ∀ j, j ≠ i → p i ≠ p j

/-- **Definition 7** (`tinnik:def7`). The source's generative cut model. -/
def GeneratingCutModel (p : Coordinates) : Prop := OpenSimplex p ∧ IsCut p

/-- Departure from the paper: estimation uses the closed simplex, as authorized
by the user after the boundary-data counterexample in Appendix C.1. -/
def EstimationCutModel (p : Coordinates) : Prop := ClosedSimplex p ∧ IsCut p

/-- Representation bridge between the equality-pair and three-line descriptions. -/
theorem isCut_iff_onCutLine (p : Coordinates) :
    IsCut p ↔ ∃ i, OnCutLine i p := by
  have h0 (h : p 1 = p 2) : OnCutLine 0 p := by
    intro j k hj hk
    fin_cases j <;> fin_cases k <;> simp_all
  have h1 (h : p 0 = p 2) : OnCutLine 1 p := by
    intro j k hj hk
    fin_cases j <;> fin_cases k <;> simp_all
  have h2 (h : p 0 = p 1) : OnCutLine 2 p := by
    intro j k hj hk
    fin_cases j <;> fin_cases k <;> simp_all
  constructor
  · rintro ⟨i, j, hne, heq⟩
    fin_cases i <;> fin_cases j
    all_goals first
      | exact False.elim (hne rfl)
      | exact ⟨0, h0 heq⟩
      | exact ⟨0, h0 heq.symm⟩
      | exact ⟨1, h1 heq⟩
      | exact ⟨1, h1 heq.symm⟩
      | exact ⟨2, h2 heq⟩
      | exact ⟨2, h2 heq.symm⟩
  · rintro ⟨i, hi⟩
    fin_cases i
    · exact ⟨1, 2, by decide, hi 1 2 (by decide) (by decide)⟩
    · exact ⟨0, 2, by decide, hi 0 2 (by decide) (by decide)⟩
    · exact ⟨0, 1, by decide, hi 0 1 (by decide) (by decide)⟩

/-- Positive generating CFs remain admissible under closed-simplex estimation. -/
theorem openSimplex_closedSimplex (p : Coordinates) (hp : OpenSimplex p) :
    ClosedSimplex p := by
  exact ⟨fun i ↦ le_of_lt (hp.1 i), hp.2⟩

/-- Count total; the paper uses `m` in the main text and `n` in Appendix C. -/
def sampleSize (m : Counts) : ℕ := ∑ i, m i

/-- Counts outside the distinguished coordinate; no truncated subtraction. -/
def otherCount (m : Counts) (i : Fin 3) : ℕ :=
  ∑ j ∈ Finset.univ.erase i, m j

/-- Bridge to the source's expression `m−m_i`. -/
theorem otherCount_add (m : Counts) (i : Fin 3) :
    otherCount m i + m i = sampleSize m := by
  exact Finset.sum_erase_add Finset.univ m (Finset.mem_univ i)

/-- The parameter-dependent multinomial likelihood, omitting the common positive
multinomial coefficient. It is a polynomial and is well-defined on the boundary. -/
def likelihood (m : Counts) (p : Coordinates) : ℝ := ∏ i, p i ^ m i

/-- `Equ3`: empirical CF (defined also at zero samples, where it is the zero vector). -/
def empiricalCF (m : Counts) : Coordinates := fun i ↦ (m i : ℝ) / sampleSize m

/-- `Equ10`: the maximum-likelihood estimate on one closed cut-model line. -/
def cutLineMLE (m : Counts) (i : Fin 3) : Coordinates := fun j ↦
  if j = i then (m i : ℝ) / sampleSize m
  else (otherCount m i : ℝ) / (2 * sampleSize m)

/-- Explicit zero-count convention. This is used on counts, not as a replacement
for the extended log-likelihood at arbitrary zero-probability candidates. -/
def xlogx (x : ℝ) : ℝ := if x = 0 then 0 else x * Real.log x

/-- `Equ11`, with the parameter-independent multinomial log coefficient omitted. -/
def lineMaxLogLikelihood (m : Counts) (i : Fin 3) : ℝ :=
  xlogx (m i) + xlogx (otherCount m i) - (otherCount m i : ℝ) * Real.log 2 -
    xlogx (sampleSize m)

/-- `Equ12`, with the same parameter-independent multinomial log coefficient omitted. -/
def fullMaxLogLikelihood (m : Counts) : ℝ :=
  (∑ i, xlogx (m i)) - xlogx (sampleSize m)

/-- Largest of the three constrained maximum log-likelihood values. -/
def cutMaxLogLikelihood (m : Counts) : ℝ :=
  max (lineMaxLogLikelihood m 0)
    (max (lineMaxLogLikelihood m 1) (lineMaxLogLikelihood m 2))

/-- The source's nonnegative likelihood-ratio statistic, including zero counts. -/
def likelihoodRatio (m : Counts) : ℝ :=
  2 * (fullMaxLogLikelihood m - cutMaxLogLikelihood m)

/-- A real CF specifies a categorical distribution on the three quartet topologies. -/
noncomputable def categoricalPMF (p : ClosedCF) : PMF (Fin 3) :=
  PMF.ofFintype (fun i ↦ ENNReal.ofReal (p.prob i)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ ↦ p.nonneg i), p.sum_eq_one]
    simp)

/-- Sampling n independent gene quartets, with no gene-tree inference error. -/
noncomputable def sampleMeasure (p : ClosedCF) (n : ℕ) : Measure (Fin n → Fin 3) :=
  Measure.pi (fun _ : Fin n ↦ (categoricalPMF p).toMeasure)

instance sampleMeasure_isProbability (p : ClosedCF) (n : ℕ) :
    IsProbabilityMeasure (sampleMeasure p n) := by
  unfold sampleMeasure
  infer_instance

/-- Observed counts from the n draws. -/
def sampleCounts {n : ℕ} (ω : Fin n → Fin 3) : Counts := fun i ↦
  (Finset.univ.filter (fun k ↦ ω k = i)).card

/-- Sampling representation bridge: count total equals sample size. -/
theorem sampleCounts_total {n : ℕ} (ω : Fin n → Fin 3) :
    sampleSize (sampleCounts ω) = n := by
  simpa [sampleSize, sampleCounts] using
    Finset.sum_card_fiberwise_eq_card_filter
      (Finset.univ : Finset (Fin n)) (Finset.univ : Finset (Fin 3)) ω

/-- Appendix C.2's parametrization of the distinguished cut line. -/
def theta (φ : ℝ) : Coordinates := fun i ↦ if i = 0 then 1 - 2 * φ / 3 else φ / 3

/-- Parameter-range bridge, with the exact open interval from Proposition 5. -/
theorem theta_open (φ : ℝ) (hφ : 0 < φ ∧ φ < 3 / 2) : OpenSimplex (theta φ) := by
  constructor
  · intro i
    fin_cases i <;> norm_num [theta] <;> linarith [hφ.1, hφ.2]
  · simp [theta, Fin.sum_univ_succ]
    ring

noncomputable def thetaCF (φ : ℝ) (hφ : 0 < φ ∧ φ < 3 / 2) : ClosedCF where
  prob := theta φ
  nonneg := (openSimplex_closedSimplex _ (theta_open φ hφ)).1
  sum_eq_one := (theta_open φ hφ).2

/-- The source's mean displacement; it is negative when `φ>1`. -/
noncomputable def mu0 (φ : ℝ) (n : ℕ) : ℝ :=
  Real.sqrt (2 * (n : ℝ)) * (1 - φ) / Real.sqrt (φ * (3 - 2 * φ))

noncomputable def alpha0 (φ : ℝ) : ℝ :=
  Real.arctan (1 / Real.sqrt (3 * (3 - 2 * φ)))

noncomputable def beta0 (φ : ℝ) : ℝ := (Real.pi / 2 - alpha0 φ) / 2

/-- Product measure makes the two marginal normals independent, as required by
Proposition 5's identity-covariance bivariate normal construction. -/
noncomputable def gaussianPlane (φ : ℝ) (n : ℕ) : Measure (ℝ × ℝ) :=
  (gaussianReal 0 1).prod (gaussianReal (mu0 φ n) 1)

instance gaussianPlane_isProbability (φ : ℝ) (n : ℕ) :
    IsProbabilityMeasure (gaussianPlane φ n) := by
  unfold gaussianPlane
  infer_instance

/-- **Proposition 5, `Equ13`** (`tinnik:lambda_candidate`). -/
noncomputable def lambdaCandidate (φ : ℝ) (z : ℝ × ℝ) : ℝ :=
  min (z.1 ^ 2)
    (min ((Real.sin (alpha0 φ) * z.1 + Real.cos (alpha0 φ) * z.2) ^ 2)
      ((Real.sin (alpha0 φ) * z.1 - Real.cos (alpha0 φ) * z.2) ^ 2))

/-- **Proposition 6, `Equ15`** (`tinnik:density_formula`), exactly as printed for
positive lam. Values at nonpositive lam are set to zero; a density's value at zero
has no effect on its associated measure. -/
noncomputable def density (φ : ℝ) (n : ℕ) (lam : ℝ) : ℝ :=
  if 0 < lam then
    let a := alpha0 φ
    let b := beta0 φ
    let μ := mu0 φ n
    let x := Real.sqrt lam
    let cotA := Real.cot a
    let cotB := Real.cot b
    1 / (2 * Real.sqrt (2 * Real.pi * lam)) *
      (Real.exp (-lam / 2) *
        (2 - Real.erf ((x * cotB + μ) / Real.sqrt 2) -
          Real.erf ((x * cotB - μ) / Real.sqrt 2)) +
       Real.exp (-((x - μ * Real.cos a) ^ 2) / 2) *
        (2 - Real.erf ((x * cotA + μ * Real.sin a) / Real.sqrt 2) -
          Real.erf ((x * cotB - μ * Real.sin a) / Real.sqrt 2)) +
       Real.exp (-((x + μ * Real.cos a) ^ 2) / 2) *
        (2 - Real.erf ((x * cotA - μ * Real.sin a) / Real.sqrt 2) -
          Real.erf ((x * cotB + μ * Real.sin a) / Real.sqrt 2)))
  else 0

end

end TINNiK
