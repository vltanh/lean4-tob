module

public import Basic.Phylogenetics.TreeTopology
public import Mathlib.Probability.ProbabilityMassFunction.Constructions
public import Mathlib.Data.Fintype.BigOperators

/-!
# Quartet scores and marginal probabilities

The score sums once over each unordered four-taxon subset and evaluates its weight
at the unique quartet resolution induced by the candidate binary tree. A whole-tree
probability mass function induces quartet probabilities by actual restriction.

Observed genes are complete binary tree topologies on the same taxon set. Unresolved
or missing-taxon input trees require separate definitions and are not covered here.
Counts are unnormalized; empirical frequencies divide them by the sample size.

These are finite representation and counting bridges. They neither specify a
coalescent model nor impose independence between different genes.
-/

@[expose] public noncomputable section

open scoped BigOperators
open Classical Finset Phylogenetics

namespace Phylogenetics.QuartetScore

variable {X : Type*} [Fintype X] [DecidableEq X]

/-- Real weights indexed by unordered four-taxon sets and their three resolutions. -/
abbrev QuartetWeights (X : Type*) [DecidableEq X] :=
  (q : Quartet X) → QuartetSplit q → ℝ

/-- One summand for each unordered quartet, evaluated at the induced tree resolution. -/
def score (w : QuartetWeights X) (T : BinaryTopology X) : ℝ :=
  ∑ q : Quartet X, w q (T.quartetSplit q)

/-- The single induced-resolution summand equals the sum over displayed resolutions. -/
theorem score_eq_display_sum (w : QuartetWeights X) (T : BinaryTopology X) :
    score w T = ∑ q : Quartet X, ∑ p : QuartetSplit q,
      if T.val.Displays p then w q p else 0 := by
  simp [score, BinaryTopology.displays_iff]

/-- A probability mass function on actual whole-gene-tree topologies. This type alone
does not impose a coalescent model or independence between different genes. -/
abbrev GeneLaw (X : Type*) [Fintype X] [DecidableEq X] := PMF (BinaryTopology X)

/-- The quartet law is the pushforward of the whole-tree law by actual restriction. -/
def quartetLaw (μ : GeneLaw X) (q : Quartet X) : PMF (QuartetSplit q) :=
  μ.map (fun T => T.quartetSplit q)

/-- Concordance factors are the real-valued masses of that quartet marginal. -/
def geneCF (μ : GeneLaw X) : QuartetWeights X :=
  fun q p => (quartetLaw μ q p).toReal

/-- The marginal mass sums the probabilities of exactly the trees displaying the split. -/
theorem geneCF_eq_display_sum (μ : GeneLaw X) (q : Quartet X) (p : QuartetSplit q) :
    geneCF μ q p = ∑ T : BinaryTopology X,
      if T.val.Displays p then (μ T).toReal else 0 := by
  simp only [geneCF, quartetLaw, PMF.map_apply, tsum_fintype,
    BinaryTopology.displays_iff]
  rw [ENNReal.toReal_sum]
  · apply sum_congr rfl
    intro T _
    split_ifs <;> rfl
  · intro T _
    split_ifs
    · exact μ.apply_ne_top T
    · exact ENNReal.zero_ne_top

/-- Every quartet concordance factor is nonnegative. -/
theorem geneCF_nonneg (μ : GeneLaw X) (q : Quartet X) (p : QuartetSplit q) :
    0 ≤ geneCF μ q p := ENNReal.toReal_nonneg

/-- The three quartet probabilities sum to one, without any model-specific assumption. -/
theorem geneCF_sum (μ : GeneLaw X) (q : Quartet X) :
    ∑ p : QuartetSplit q, geneCF μ q p = 1 := by
  rw [show (∑ p : QuartetSplit q, geneCF μ q p) =
    (∑ p : QuartetSplit q, quartetLaw μ q p).toReal by
      exact (ENNReal.toReal_sum (fun p _ => (quartetLaw μ q).apply_ne_top p)).symm]
  have hsum : ∑ p : QuartetSplit q, quartetLaw μ q p = 1 := by
    simpa only [tsum_fintype] using (quartetLaw μ q).tsum_coe
  rw [hsum, ENNReal.toReal_one]

/-- Count genes with each induced quartet resolution. Counts remain natural numbers. -/
def quartetCounts {n : ℕ} (G : Fin n → BinaryTopology X)
    (q : Quartet X) (p : QuartetSplit q) : ℕ :=
  ∑ i : Fin n, if (G i).quartetSplit q = p then 1 else 0

/-- Display predicates and induced resolutions give the same observed counts. -/
theorem quartetCounts_eq_display_sum {n : ℕ} (G : Fin n → BinaryTopology X)
    (q : Quartet X) (p : QuartetSplit q) :
    quartetCounts G q p = ∑ i : Fin n, if (G i).val.Displays p then 1 else 0 := by
  simp only [quartetCounts, BinaryTopology.displays_iff, eq_comm]

/-- Every gene contributes to exactly one of a quartet's three counts, including n = 0. -/
theorem quartetCounts_sum {n : ℕ} (G : Fin n → BinaryTopology X) (q : Quartet X) :
    ∑ p : QuartetSplit q, quartetCounts G q p = n := by
  simp only [quartetCounts]
  rw [sum_comm]
  simp

/-- Real-valued count weights, without division by the number of genes. -/
def countWeights {n : ℕ} (G : Fin n → BinaryTopology X) : QuartetWeights X :=
  fun q p => quartetCounts G q p

/-- The count weights still sum to the number of sampled genes on each quartet. -/
theorem countWeights_sum {n : ℕ} (G : Fin n → BinaryTopology X) (q : Quartet X) :
    ∑ p : QuartetSplit q, countWeights G q p = n := by
  simpa only [countWeights, Nat.cast_sum] using
    congrArg (fun k : ℕ => (k : ℝ)) (quartetCounts_sum G q)

/-- The exact number of unordered quartets on which two actual binary trees agree. -/
def agreeingQuartets (T G : BinaryTopology X) : ℕ :=
  (univ.filter fun q : Quartet X => G.quartetSplit q = T.quartetSplit q).card

/-- An observed count score is exactly the sum, over genes, of their numbers of
quartets agreeing with the candidate tree. No normalizing factor occurs. -/
theorem score_countWeights_eq_sum_agreeing {n : ℕ} (G : Fin n → BinaryTopology X)
    (T : BinaryTopology X) :
    score (countWeights G) T = ∑ i : Fin n, (agreeingQuartets T (G i) : ℝ) := by
  simp only [score, countWeights, quartetCounts, Nat.cast_sum, Nat.cast_ite,
    Nat.cast_one, Nat.cast_zero]
  rw [sum_comm]
  apply sum_congr rfl
  intro i _
  simp [agreeingQuartets, Finset.sum_boole]

/-- Empirical frequencies are the observed counts divided by the number of genes. -/
def empiricalCF {n : ℕ} (G : Fin n → BinaryTopology X) : QuartetWeights X :=
  fun q p => countWeights G q p / n

/-- A positive sample size makes the empirical frequencies sum to one. -/
theorem empiricalCF_sum {n : ℕ} (G : Fin n → BinaryTopology X) (hn : 0 < n)
    (q : Quartet X) : ∑ p : QuartetSplit q, empiricalCF G q p = 1 := by
  simp only [empiricalCF, ← sum_div, countWeights_sum]
  exact div_self (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn))

/-- Normalizing the quartet counts normalizes the complete score by the same factor. -/
theorem score_empiricalCF {n : ℕ} (G : Fin n → BinaryTopology X)
    (T : BinaryTopology X) : score (empiricalCF G) T = score (countWeights G) T / n := by
  simp only [score, empiricalCF, sum_div]

end Phylogenetics.QuartetScore
