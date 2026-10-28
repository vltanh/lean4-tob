module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.Linarith

/-!
Independent check of the open-simplex boundary issue in TINNiK Appendix C.1.
The user authorized using the closed simplex for estimation, while retaining
strictly positive generating probabilities. These checks verify the obstruction
and the selected repair; they are not the full C.1 MLE theorem.
-/

public section

namespace TINNiKBoundaryCheck

/-- The paper's open probability simplex. -/
def OpenSimplex (p₁ p₂ p₃ : ℝ) : Prop :=
  0 < p₁ ∧ 0 < p₂ ∧ 0 < p₃ ∧ p₁ + p₂ + p₃ = 1

/-- The closed probability simplex used for estimation after the approved repair. -/
def ClosedSimplex (p₁ p₂ p₃ : ℝ) : Prop :=
  0 ≤ p₁ ∧ 0 ≤ p₂ ∧ 0 ≤ p₃ ∧ p₁ + p₂ + p₃ = 1

/-- The union of the three cut-model equality lines. -/
def IsCut (p₁ p₂ p₃ : ℝ) : Prop :=
  p₁ = p₂ ∨ p₁ = p₃ ∨ p₂ = p₃

/-- Likelihood for the sample containing one observation of the first topology. -/
def likelihood100 (p₁ p₂ p₃ : ℝ) : ℝ :=
  p₁ ^ 1 * p₂ ^ 0 * p₃ ^ 0

@[simp] theorem likelihood100_eq (p₁ p₂ p₃ : ℝ) :
    likelihood100 p₁ p₂ p₃ = p₁ := by
  simp [likelihood100]

/-- Every open-simplex candidate admits a strictly better open cut-model point. -/
theorem improve_open_candidate (p₁ p₂ p₃ : ℝ) (hp : OpenSimplex p₁ p₂ p₃) :
    OpenSimplex ((1 + p₁) / 2) ((1 - p₁) / 4) ((1 - p₁) / 4) ∧
    IsCut ((1 + p₁) / 2) ((1 - p₁) / 4) ((1 - p₁) / 4) ∧
    likelihood100 p₁ p₂ p₃ <
      likelihood100 ((1 + p₁) / 2) ((1 - p₁) / 4) ((1 - p₁) / 4) := by
  rcases hp with ⟨h₁, h₂, h₃, hsum⟩
  have hlt : p₁ < 1 := by linarith
  refine ⟨⟨?_, ?_, ?_, ?_⟩, Or.inr (Or.inr rfl), ?_⟩
  · linarith
  · linarith
  · linarith
  · linarith
  · simpa only [likelihood100_eq] using (show p₁ < (1 + p₁) / 2 by linarith)

/-- Counts `(1,0,0)` have no maximum over the open cut model. -/
theorem no_open_cut_maximum :
    ¬ ∃ p₁ p₂ p₃ : ℝ,
      OpenSimplex p₁ p₂ p₃ ∧ IsCut p₁ p₂ p₃ ∧
      ∀ q₁ q₂ q₃ : ℝ, OpenSimplex q₁ q₂ q₃ → IsCut q₁ q₂ q₃ →
        likelihood100 q₁ q₂ q₃ ≤ likelihood100 p₁ p₂ p₃ := by
  rintro ⟨p₁, p₂, p₃, hp, _, hmax⟩
  rcases improve_open_candidate p₁ p₂ p₃ hp with ⟨hq, hcut, hbetter⟩
  have hle := hmax ((1 + p₁) / 2) ((1 - p₁) / 4) ((1 - p₁) / 4) hq hcut
  linarith

/-- The selected boundary estimate is excluded from the generating parameter space. -/
theorem boundary_not_open : ¬ OpenSimplex 1 0 0 := by
  simp [OpenSimplex]

/-- The closed cut model contains `(1,0,0)`, which maximizes this likelihood. -/
theorem boundary_attains_closed_cut_maximum :
    ClosedSimplex 1 0 0 ∧ IsCut 1 0 0 ∧
      ∀ p₁ p₂ p₃ : ℝ, ClosedSimplex p₁ p₂ p₃ → IsCut p₁ p₂ p₃ →
        likelihood100 p₁ p₂ p₃ ≤ likelihood100 1 0 0 := by
  refine ⟨by norm_num [ClosedSimplex], Or.inr (Or.inr rfl), ?_⟩
  intro p₁ p₂ p₃ hp _
  rcases hp with ⟨_, h₂, h₃, hsum⟩
  simp only [likelihood100_eq]
  linarith

/-- The generating parameter space embeds into the estimation space. -/
theorem openSimplex_to_closedSimplex (p₁ p₂ p₃ : ℝ)
    (hp : OpenSimplex p₁ p₂ p₃) : ClosedSimplex p₁ p₂ p₃ := by
  rcases hp with ⟨h₁, h₂, h₃, hsum⟩
  exact ⟨le_of_lt h₁, le_of_lt h₂, le_of_lt h₃, hsum⟩

end TINNiKBoundaryCheck

#print axioms TINNiKBoundaryCheck.improve_open_candidate
#print axioms TINNiKBoundaryCheck.no_open_cut_maximum
#print axioms TINNiKBoundaryCheck.boundary_attains_closed_cut_maximum
