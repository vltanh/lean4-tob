module

public import Basic.Probability.QuartetTests
public import ECToBlob.Section4
public import ECToBlob.Section5
public import ECToBlob.Section6

/-!
# ECToBlob §8: statistical consistency

Lemma 8.1 and Theorem 8.2.

Theorem 8.2 is stated for a network at numerical parameters where both directions of Assumption 1 hold
(E7 of the report: as printed, for all parameters, it fails). The correction was agreed with the user.
`theorem8_2_generic` gives the statement for almost all parameters, from `Assumption1`.

For the corrections `cauchy` and `cbc`, Theorem 8.2 also requires the alternatives of a quartet tree
satisfying (5.2) to have positive probability: without this a p-value is exactly `1`, and the Cauchy
combination is `1` whatever the other p-values (E18 of the report).
-/

@[expose] public noncomputable section

open Phylogenetics Phylogenetics.RootedNetwork Phylogenetics.QuartetTests Finset Filter Topology
open scoped Classical

namespace ECToBlob

universe u

/-- **Lemma 8.1** (`ecto:lem8_1`). For each `K ≥ 1` and `ε > 0` there is `0 < δ < 1/2` such that for any
at most `K` possibly dependent asymptotically uniform random variables in `[0, 1]` there is `M` with
`P(all lie in [δ, 1 - δ]) > 1 - ε` for `n > M`. -/
theorem lemma8_1 (K : ℕ) (hK : 1 ≤ K) {ε : ℝ} (hε : 0 < ε) : ∃ δ : ℝ, 0 < δ ∧ δ < 1 / 2 ∧
    ∀ {Γ ι : Type*} [Fintype Γ] [Fintype ι] (dist : Γ → ℝ) (p : ι → (n : ℕ) → (Fin n → Γ) → ℝ),
      IsDist dist → Fintype.card ι ≤ K → (∀ i n ω, 0 ≤ p i n ω ∧ p i n ω ≤ 1) →
      (∀ i, AsymptoticallyUniform dist (p i)) →
      ∃ M : ℕ, ∀ n, M < n →
        1 - ε < iidProb dist n fun ω => ∀ i, δ ≤ p i n ω ∧ p i n ω ≤ 1 - δ := by
  sorry

variable {V E X : Type*} [Fintype X] [DecidableEq X]

/-- **Theorem 8.2** (`ecto:thm8_2`), with the correction agreed with the user (E7 of the report) and the
one required for the Cauchy combinations (E18). There are sequences `α_n`, `β_n`, independent of the
network, such that for every resolution `T₀` of the tree of blobs, every variant of the algorithm, and
every distribution of binary gene trees whose quartet concordance factors satisfy both directions of
Assumption 1 at the network's parameters, the output on `n` independent gene trees is the tree of blobs
with probability tending to one. -/
theorem theorem8_2 : ∃ α β : ℕ → ℝ, Tendsto α atTop (𝓝 0) ∧ Tendsto β atTop (𝓝 0) ∧
    ∀ {V E X : Type u} [Fintype X] [DecidableEq X] (N : RootedNetwork V E X)
      (_ : N.IsPhylogenetic) (dist : BinaryGeneTree X → ℝ) (_ : IsDist dist)
      (_ : Assumption1Forward N (displayCF dist Subtype.val))
      (_ : Assumption1Converse N (displayCF dist Subtype.val))
      (T₀ : Finset (Finset X)) (_ : IsResolutionOf T₀ (treeOfBlobs N))
      (o : ECToBlobOptions)
      (_ : (o.testCo = .cauchy ∨ o.testCo = .cbc) →
        ∀ s, IsT1Strict (displayCF dist Subtype.val) s →
          ∀ r ∈ s.alternatives, 0 < displayCF dist Subtype.val r),
      Tendsto (fun n => iidProb dist n fun ω =>
        ectoblob o (α n) (β n) (quartetCount Subtype.val ω) T₀ = treeOfBlobs N) atTop (𝓝 1) := by
  sorry

/-- The sequences of `theorem8_2` are the explicit ones of the paper's proof. -/
theorem theorem8_2_explicit {V E X : Type u} [Fintype X] [DecidableEq X] (N : RootedNetwork V E X)
    (hN : N.IsPhylogenetic) (dist : BinaryGeneTree X → ℝ) (hd : IsDist dist)
    (h₁ : Assumption1Forward N (displayCF dist Subtype.val))
    (h₂ : Assumption1Converse N (displayCF dist Subtype.val))
    (T₀ : Finset (Finset X)) (hT₀ : IsResolutionOf T₀ (treeOfBlobs N)) (o : ECToBlobOptions)
    (hpos : (o.testCo = .cauchy ∨ o.testCo = .cbc) →
      ∀ s, IsT1Strict (displayCF dist Subtype.val) s →
        ∀ r ∈ s.alternatives, 0 < displayCF dist Subtype.val r) :
    Tendsto (fun n => iidProb dist n fun ω =>
      ectoblob o (alphaSeq n) (betaSeq n) (quartetCount Subtype.val ω) T₀ = treeOfBlobs N)
      atTop (𝓝 1) := by
  sorry

/-- Theorem 8.2 for a model meeting Assumption 1: it holds at all parameters outside the null set
that Assumption 1 excludes. -/
theorem theorem8_2_generic {V E X : Type u} [Fintype V] [Fintype E] [Fintype X] [DecidableEq X]
    (N : RootedNetwork V E X) (hN : N.IsPhylogenetic)
    (dist : MetricData E → BinaryGeneTree X → ℝ) (hd : ∀ θ, N.IsMetric θ → IsDist (dist θ))
    (hA : Assumption1 N fun θ => displayCF (dist θ) Subtype.val)
    (θ : MetricData E) (hθ : N.IsMetric θ)
    (hgen : Assumption1Converse N (displayCF (dist θ) Subtype.val))
    (T₀ : Finset (Finset X)) (hT₀ : IsResolutionOf T₀ (treeOfBlobs N)) (o : ECToBlobOptions)
    (hpos : (o.testCo = .cauchy ∨ o.testCo = .cbc) →
      ∀ s, IsT1Strict (displayCF (dist θ) Subtype.val) s →
        ∀ r ∈ s.alternatives, 0 < displayCF (dist θ) Subtype.val r) :
    Tendsto (fun n => iidProb (dist θ) n fun ω =>
      ectoblob o (alphaSeq n) (betaSeq n) (quartetCount Subtype.val ω) T₀ = treeOfBlobs N)
      atTop (𝓝 1) := by
  sorry

end ECToBlob
