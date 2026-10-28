module

public import Basic.Phylogenetics.Quartet
public import Mathlib.Probability.ProbabilityMassFunction.Basic
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Tactic.Linarith

/-!
Quartet concordance factors indexed by actual unordered split topologies.
An unresolved quartet is `none`; a resolved quartet is `some split`. The raw CF
retains its three resolved probabilities. The normalized CF distributes unresolved
mass equally over the three resolutions. These are defining representation facts,
not identifiability claims about any network model.
-/

@[expose] public section

noncomputable section

open scoped BigOperators

namespace Phylogenetics

universe u

/-- Coordinates 0,1,2 stand for 01|23, 02|13, 03|12, respectively. -/
def standardSplitEquiv : Fin 3 ≃ Pairing (Fin 4) :=
  Equiv.ofBijective ![split01_23, split02_13, split03_12] ⟨by
    intro i j h
    have hdist := standard_splits_distinct
    fin_cases i <;> fin_cases j <;> simp_all,
    by
      intro p
      obtain rfl | rfl | rfl := standard_splits_exhaustive p
      · exact ⟨0, rfl⟩
      · exact ⟨1, rfl⟩
      · exact ⟨2, rfl⟩⟩

@[simp] theorem standardSplitEquiv_zero : standardSplitEquiv 0 = split01_23 := rfl
@[simp] theorem standardSplitEquiv_one : standardSplitEquiv 1 = split02_13 := rfl
@[simp] theorem standardSplitEquiv_two : standardSplitEquiv 2 = split03_12 := rfl

variable {X : Type u} [DecidableEq X]

/-- Ordered coordinates for the three actual splits of a labeled quartet. -/
def quartetSplitEquiv (q : Quartet X) (e : Fin 4 ≃ q.val) : Fin 3 ≃ QuartetSplit q :=
  standardSplitEquiv.trans (QuartetSplit.congr q e)

@[simp] theorem quartetSplitEquiv_zero (q : Quartet X) (e : Fin 4 ≃ q.val) :
    quartetSplitEquiv q e 0 = QuartetSplit.congr q e split01_23 := rfl

@[simp] theorem quartetSplitEquiv_one (q : Quartet X) (e : Fin 4 ≃ q.val) :
    quartetSplitEquiv q e 1 = QuartetSplit.congr q e split02_13 := rfl

@[simp] theorem quartetSplitEquiv_two (q : Quartet X) (e : Fin 4 ≃ q.val) :
    quartetSplitEquiv q e 2 = QuartetSplit.congr q e split03_12 := rfl

/-- Bare real-valued CF data; the probability-vector property is separate. -/
abbrev QuartetCF (q : Quartet X) := QuartetSplit q → ℝ

/-- Nonnegative coordinates with sum one. -/
def IsProbabilityCF {q : Quartet X} (p : QuartetCF q) : Prop :=
  (∀ r, 0 ≤ p r) ∧ (∑ r, p r) = 1

/-- Strict positivity is separate and is not built into a CF or a probability law. -/
def IsPositiveCF {q : Quartet X} (p : QuartetCF q) : Prop := ∀ r, 0 < p r

/-- A discrete probability law on the three resolved topologies and the star. -/
abbrev QuartetLaw (q : Quartet X) := PMF (Option (QuartetSplit q))

/-- Raw resolved-topology probabilities, excluding unresolved mass. -/
def rawCF {q : Quartet X} (p : QuartetLaw q) : QuartetCF q :=
  fun r => (p (some r)).toReal

/-- The probability of an unresolved quartet. -/
def starMass {q : Quartet X} (p : QuartetLaw q) : ℝ := (p none).toReal

/-- The normalized convention assigns one third of the star mass to each split. -/
def normalizedCF {q : Quartet X} (p : QuartetLaw q) : QuartetCF q :=
  fun r => rawCF p r + starMass p / 3

/-- Every raw coordinate is nonnegative. -/
theorem rawCF_nonneg {q : Quartet X} (p : QuartetLaw q) (r : QuartetSplit q) :
    0 ≤ rawCF p r := ENNReal.toReal_nonneg

/-- The unresolved probability is nonnegative. -/
theorem starMass_nonneg {q : Quartet X} (p : QuartetLaw q) :
    0 ≤ starMass p := ENNReal.toReal_nonneg

/-- Resolved and unresolved probabilities together exhaust the quartet law. -/
theorem starMass_add_sum_rawCF {q : Quartet X} (p : QuartetLaw q) :
    starMass p + (∑ r, rawCF p r) = 1 := by
  have hsum : (∑ z, p z) = 1 := by
    simpa only [tsum_fintype] using p.tsum_coe
  have h : (∑ z : Option (QuartetSplit q), (p z).toReal) = 1 := by
    rw [← ENNReal.toReal_sum (fun z _ => p.apply_ne_top z),
      hsum, ENNReal.toReal_one]
  simpa only [Fintype.sum_option, starMass, rawCF] using h

/-- Raw CFs sum to one minus the unresolved mass. -/
theorem sum_rawCF {q : Quartet X} (p : QuartetLaw q) :
    (∑ r, rawCF p r) = 1 - starMass p := by
  linarith [starMass_add_sum_rawCF p]

/-- Normalization preserves nonnegativity. -/
theorem normalizedCF_nonneg {q : Quartet X} (p : QuartetLaw q) (r : QuartetSplit q) :
    0 ≤ normalizedCF p r :=
  add_nonneg (rawCF_nonneg p r) (div_nonneg (starMass_nonneg p) (by norm_num))

/-- Exactly three splits receive the unresolved mass, so the total is one. -/
theorem sum_normalizedCF {q : Quartet X} (p : QuartetLaw q) :
    (∑ r, normalizedCF p r) = 1 := by
  simp only [normalizedCF, Finset.sum_add_distrib, Finset.sum_const,
    Finset.card_univ, card_quartet_splits, nsmul_eq_mul, Nat.cast_ofNat]
  linarith [starMass_add_sum_rawCF p]

/-- A normalized quartet law is a probability vector without any positivity assumption. -/
theorem normalizedCF_isProbabilityCF {q : Quartet X} (p : QuartetLaw q) :
    IsProbabilityCF (normalizedCF p) :=
  ⟨normalizedCF_nonneg p, sum_normalizedCF p⟩

/-- If no stars occur, the normalized and raw conventions agree. -/
theorem normalizedCF_eq_rawCF {q : Quartet X} (p : QuartetLaw q) (h : p none = 0) :
    normalizedCF p = rawCF p := by
  funext r
  simp [normalizedCF, starMass, h]

/-- Three real coordinates in the usual ab|cd, ac|bd, ad|bc order. -/
def cfCoordinates {q : Quartet X} (e : Fin 4 ≃ q.val) (p : QuartetCF q) : Fin 3 → ℝ :=
  fun i => p (quartetSplitEquiv q e i)

/-- Changing labels permutes coordinates and does not change their sum. -/
theorem sum_cfCoordinates {q : Quartet X} (e : Fin 4 ≃ q.val) (p : QuartetCF q) :
    (∑ i, cfCoordinates e p i) = ∑ r, p r :=
  (quartetSplitEquiv q e).sum_comp p

/-- The coordinate representation of a normalized law is a probability vector. -/
theorem normalizedCF_coordinates {q : Quartet X} (e : Fin 4 ≃ q.val)
    (p : QuartetLaw q) :
    (∀ i, 0 ≤ cfCoordinates e (normalizedCF p) i) ∧
      (∑ i, cfCoordinates e (normalizedCF p) i) = 1 := by
  refine ⟨fun i => normalizedCF_nonneg p _, ?_⟩
  rw [sum_cfCoordinates, sum_normalizedCF]

/-- The explicit coordinate permutation induced by a change of quartet ordering. -/
def coordinateRelabeling {q : Quartet X} (e f : Fin 4 ≃ q.val) : Fin 3 ≃ Fin 3 :=
  (quartetSplitEquiv q f).trans (quartetSplitEquiv q e).symm

/-- CF coordinates transform by the actual induced permutation of split topologies. -/
theorem cfCoordinates_relabel {q : Quartet X} (e f : Fin 4 ≃ q.val)
    (p : QuartetCF q) (i : Fin 3) :
    cfCoordinates f p i = cfCoordinates e p (coordinateRelabeling e f i) := by
  simp [cfCoordinates, coordinateRelabeling]

end Phylogenetics
