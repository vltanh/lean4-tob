module

public import Mathlib.Topology.Algebra.Ring.Real
public import Mathlib.Topology.Separation.Hausdorff
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Linarith

/-!
Minimal checked ingredients of a counterexample to the literal, nongeneric
reading of ECToBlob Theorem 8.2. This file does not implement phylogenetic
networks or probability measures. It checks the exact CF coincidences and
unique-limit obstruction; the construction of the model is explained in
the genericity counterexample in `docs/REPORT.md`.
-/

public section

namespace ECToBlobGenericityCheck

/-- A family having an exceptional, strictly cut CF at `t = 1`. -/
def h (t : ℚ) : ℚ := (t - 1) / (8 * (1 + (t - 1) ^ 2))

def blobCF (t : ℚ) : ℚ × ℚ × ℚ := (1 / 2, 1 / 4 + h t, 1 / 4 - h t)

def treeCF : ℚ × ℚ × ℚ := (1 / 2, 1 / 4, 1 / 4)

theorem exceptional_cf_equals_tree : blobCF 1 = treeCF := by
  norm_num [blobCF, treeCF, h]

theorem regular_cf_exact : blobCF 2 = (1 / 2, 5 / 16, 3 / 16) := by
  norm_num [blobCF, h]

theorem exceptional_probabilities_positive_sum_one :
    (0 : ℚ) < 1 / 2 ∧ (0 : ℚ) < 1 / 4 ∧
      (1 / 2 : ℚ) + 1 / 4 + 1 / 4 = 1 := by
  norm_num

theorem regular_probabilities_positive_distinct_sum_one :
    (0 : ℚ) < 1 / 2 ∧ (0 : ℚ) < 5 / 16 ∧ (0 : ℚ) < 3 / 16 ∧
      (1 / 2 : ℚ) ≠ 5 / 16 ∧ (1 / 2 : ℚ) ≠ 3 / 16 ∧
      (5 / 16 : ℚ) ≠ 3 / 16 ∧ (1 / 2 : ℚ) + 5 / 16 + 3 / 16 = 1 := by
  norm_num

/-- The same parameter family over the real metric parameter space. -/
noncomputable def realH (t : ℝ) : ℝ := (t - 1) / (8 * (1 + (t - 1) ^ 2))

theorem realH_bounds (t : ℝ) : -(1 / 16 : ℝ) ≤ realH t ∧ realH t ≤ 1 / 16 := by
  have hd : 0 < 8 * (1 + (t - 1) ^ 2) := by nlinarith [sq_nonneg (t - 1)]
  constructor
  · rw [realH, le_div_iff₀ hd]
    nlinarith [sq_nonneg t]
  · rw [realH, div_le_iff₀ hd]
    nlinarith [sq_nonneg (t - 2)]

theorem realH_eq_zero_iff (t : ℝ) : realH t = 0 ↔ t = 1 := by
  have hd : 8 * (1 + (t - 1) ^ 2) ≠ 0 := by nlinarith [sq_nonneg (t - 1)]
  simp [realH, div_eq_zero_iff, hd, sub_eq_zero]

/-- Every real parameter gives strictly positive normalized probabilities. -/
theorem family_positive_sum_one (t : ℝ) :
    0 < (1 / 2 : ℝ) ∧ 0 < (1 / 4 : ℝ) + realH t ∧
      0 < (1 / 4 : ℝ) - realH t ∧
      (1 / 2 : ℝ) + (1 / 4 + realH t) + (1 / 4 - realH t) = 1 := by
  rcases realH_bounds t with ⟨hlo, hhi⟩
  refine ⟨by norm_num, ?_, ?_, ?_⟩ <;> linarith

/-- The CF is non-cut exactly away from the single exceptional parameter. -/
theorem family_noncut_iff (t : ℝ) :
    ((1 / 2 : ℝ) ≠ 1 / 4 + realH t ∧
      (1 / 2 : ℝ) ≠ 1 / 4 - realH t ∧
      (1 / 4 : ℝ) + realH t ≠ 1 / 4 - realH t) ↔ t ≠ 1 := by
  rcases realH_bounds t with ⟨hlo, hhi⟩
  constructor
  · intro hh ht
    subst t
    norm_num [realH] at hh
  · intro ht
    have hnz : realH t ≠ 0 := fun hz ↦ ht ((realH_eq_zero_iff t).mp hz)
    refine ⟨?_, ?_, ?_⟩
    · intro heq
      linarith
    · intro heq
      linarith
    · intro heq
      apply hnz
      linarith

/-- Equal probabilities of the same output cannot tend to 1 in one model and
0 in the other. Equal data laws force this equality for any fixed estimator. -/
theorem equal_output_probabilities_cannot_have_opposite_limits
    (p q : ℕ → ℝ) (same : ∀ n, p n = q n)
    (hp : Filter.Tendsto p Filter.atTop (nhds 1))
    (hq : Filter.Tendsto q Filter.atTop (nhds 0)) : False := by
  have heq : p = q := funext same
  subst q
  have hzero : (1 : ℝ) = 0 := tendsto_nhds_unique hp hq
  norm_num at hzero

end ECToBlobGenericityCheck

#print axioms ECToBlobGenericityCheck.exceptional_cf_equals_tree
#print axioms ECToBlobGenericityCheck.regular_cf_exact
#print axioms ECToBlobGenericityCheck.equal_output_probabilities_cannot_have_opposite_limits

#print axioms ECToBlobGenericityCheck.family_positive_sum_one
#print axioms ECToBlobGenericityCheck.family_noncut_iff
