module

public import Basic.Probability.IID
public import Basic.Phylogenetics.TreeSplits
public import Mathlib.MeasureTheory.Function.ConvergenceInDistribution

/-!
# The asymptotics of the quartet hypothesis tests

For a sample of `n` gene trees, whose displayed quartet trees on a set of four taxa have probabilities
`p`, the statistics of the star test, the T1 test and the cut test behave as ECToBlob §8 and TINNiK's
proof of Theorem 4 use.

Assumed nowhere: the limits under the null come from Mathlib's central limit theorem, the growth under
the alternative from the law of large numbers.

API: `AsymptoticallyUniform`, `starPValue_asymptoticallyUniform`, `t1PValue_asymptoticallyUniform`,
`t1PValue_centroid_tight`, `t1PValue_le`, `chiSqOneTail_le_t1Tail`, `starStat_growth`, `pearsonStat_growth`,
`t1Stat_growth`, `lineStat_growth`, `cutPValue_null`, `alphaSeq`, `betaSeq` facts.
-/

@[expose] public noncomputable section

open Phylogenetics Finset Filter Topology
open scoped Classical

namespace Phylogenetics.QuartetTests

variable {X : Type*} [Fintype X] [DecidableEq X] {Γ : Type*} [Fintype Γ]

/-- `f (ω)` of the sample `ω`, a real function of the sample, is asymptotically uniformly distributed
on `[0,1]` for samples from `dist`: its distribution function converges to that of the uniform law. -/
def AsymptoticallyUniform (dist : Γ → ℝ) (f : (n : ℕ) → (Fin n → Γ) → ℝ) : Prop :=
  ∀ x : ℝ, 0 ≤ x → x ≤ 1 → Tendsto (fun n => iidProb dist n fun ω => f n ω ≤ x) atTop (𝓝 x)

variable {dist : Γ → ℝ} {sides : Γ → Finset (Finset X)}

/-- The gene trees of positive probability are binary, so each displays exactly one quartet tree on
each set of four taxa. -/
def DisplaysOne (dist : Γ → ℝ) (sides : Γ → Finset (Finset X)) : Prop :=
  ∀ (g : Γ), dist g ≠ 0 → ∀ q : Finset X, q.card = 4 → ∃! s, s ∈ treesOn q ∧ Displays (sides g) s

/-- Under the null of the star test, its p-value is asymptotically uniform. -/
theorem starPValue_asymptoticallyUniform (k : StarTest) (hd : IsDist dist) (hs : DisplaysOne dist sides)
    {q : Finset X} (hq : q.card = 4) (h : ∀ r ∈ treesOn q, displayCF dist sides r = 1 / 3) :
    AsymptoticallyUniform dist fun _ ω => starPValue k (quartetCount sides ω) q := by
  sorry

/-- Under the null of the T1 test away from its boundary, with positive probabilities, its p-value is
asymptotically uniform. -/
theorem t1PValue_asymptoticallyUniform (hd : IsDist dist) (hs : DisplaysOne dist sides)
    {s : QuartetTree X}
    (hlt : ∀ r ∈ s.alternatives, displayCF dist sides r < displayCF dist sides s)
    (heq : ∀ r ∈ s.alternatives, ∀ r' ∈ s.alternatives,
      displayCF dist sides r = displayCF dist sides r')
    (hpos : ∀ r ∈ s.alternatives, 0 < displayCF dist sides r) :
    AsymptoticallyUniform dist fun _ ω => t1PValue (quartetCount sides ω) s := by
  sorry

/-- The null of the T1 test with an alternative of probability zero: the alternatives have count zero,
so the p-value is `1`. -/
theorem t1PValue_degenerate (hd : IsDist dist) (hs : DisplaysOne dist sides) {s : QuartetTree X}
    (h : ∀ r ∈ s.alternatives, displayCF dist sides r = 0) {n : ℕ} (ω : Fin n → Γ)
    (hω : ∏ i, dist (ω i) ≠ 0) : t1PValue (quartetCount sides ω) s = 1 := by
  sorry

/-- At the boundary `(1/3, 1/3, 1/3)` of the T1 null its p-value is not asymptotically uniform, but it
stays away from `0` and from `1` in probability. -/
theorem t1PValue_centroid_tight (hd : IsDist dist) (hs : DisplaysOne dist sides) {s : QuartetTree X}
    (h : ∀ r ∈ treesOn s.taxa, displayCF dist sides r = 1 / 3) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ δ < 1 / 2 ∧ ∀ᶠ n in atTop, 1 - ε < iidProb dist n fun ω =>
      δ ≤ t1PValue (quartetCount sides ω) s ∧ t1PValue (quartetCount sides ω) s ≤ 1 - δ := by
  sorry

/-- The T1 test distribution is between `χ²₁` and `χ²₂`, for `μ ≥ 0`. -/
theorem chiSqOneTail_le_t1Tail {μ t : ℝ} (hμ : 0 ≤ μ) (ht : 0 ≤ t) : chiSqOneTail t ≤ t1Tail μ t := by
  sorry

theorem t1Tail_le_chiSqTwoTail {μ t : ℝ} (hμ : 0 ≤ μ) (ht : 0 ≤ t) : t1Tail μ t ≤ chiSqTwoTail t := by
  sorry

/-- The T1 statistic and its estimated parameter are in range, so the tail bounds apply. -/
theorem t1Stat_nonneg (c : QuartetTree X → ℝ) (hc : ∀ r, 0 ≤ c r) (s : QuartetTree X) :
    0 ≤ t1Stat c s := by
  sorry

theorem muZero_t1Phi_nonneg (c : QuartetTree X → ℝ) (hc : ∀ r, 0 ≤ c r) (s : QuartetTree X) :
    0 ≤ muZero (t1Phi c s) (c s + ∑ r ∈ s.alternatives, c r) := by
  sorry

/-- Under the alternative of the star test, its statistic grows faster than any `b_n = o(n)`. -/
theorem starStat_growth (k : StarTest) (hd : IsDist dist) (hs : DisplaysOne dist sides) {q : Finset X}
    (hq : q.card = 4) (h : ¬ ∀ r ∈ treesOn q, displayCF dist sides r = 1 / 3) {b : ℕ → ℝ}
    (hb : Tendsto (fun n => b n / n) atTop (𝓝 0)) :
    Tendsto (fun n => iidProb dist n fun ω =>
      Real.exp (-(b n) / 2) > starPValue k (quartetCount sides ω) q) atTop (𝓝 1) := by
  sorry

/-- Under the alternative of the T1 test, its statistic grows faster than any `b_n = o(n)`, so its
p-value is eventually below `exp(-b_n/2)`. -/
theorem t1PValue_growth (hd : IsDist dist) (hs : DisplaysOne dist sides) {s : QuartetTree X}
    (h : ¬ ((∀ r ∈ s.alternatives, displayCF dist sides r ≤ displayCF dist sides s) ∧
      ∀ r ∈ s.alternatives, ∀ r' ∈ s.alternatives,
        displayCF dist sides r = displayCF dist sides r')) {b : ℕ → ℝ}
    (hb : Tendsto (fun n => b n / n) atTop (𝓝 0)) :
    Tendsto (fun n => iidProb dist n fun ω =>
      t1PValue (quartetCount sides ω) s < Real.exp (-(b n) / 2)) atTop (𝓝 1) := by
  sorry

/-- The upper tail of `χ²₁` tends to zero, and not exponentially fast. -/
theorem tendsto_chiSqOneTail_log : Tendsto (fun n : ℕ => chiSqOneTail (Real.log n)) atTop (𝓝 0) := by
  sorry

theorem chiSqOneTail_log_pos : ∀ᶠ n : ℕ in atTop, 0 < chiSqOneTail (Real.log n) := by
  sorry

theorem tendsto_log_chiSqOneTail_log :
    Tendsto (fun n : ℕ => Real.log (chiSqOneTail (Real.log n)) / n) atTop (𝓝 0) := by
  sorry

/-- `β_n = 1/√n`. -/
theorem chiSqTwoTail_log (n : ℕ) (hn : 0 < n) :
    chiSqTwoTail (Real.log n) = 1 / Real.sqrt n := by
  sorry

/-- The cut test on a strictly cut, positive concordance factor (the null, off its singularity): the
line of the true topology has the least statistic with probability tending to one, and for any levels
`α_m → 0` the test does not reject. -/
theorem cutTest_null (hd : IsDist dist) (hs : DisplaysOne dist sides) {s : QuartetTree X}
    (hne : ∀ r ∈ s.alternatives, displayCF dist sides r ≠ displayCF dist sides s)
    (heq : ∀ r ∈ s.alternatives, ∀ r' ∈ s.alternatives,
      displayCF dist sides r = displayCF dist sides r')
    (hpos : ∀ r ∈ treesOn s.taxa, 0 < displayCF dist sides r) {α : ℕ → ℝ}
    (hα : Tendsto α atTop (𝓝 0)) :
    Tendsto (fun n => iidProb dist n fun ω =>
      (∀ r ∈ s.alternatives, lineStat (quartetCount sides ω) s < lineStat (quartetCount sides ω) r) ∧
        α n ≤ cutPValue (quartetCount sides ω) s) atTop (𝓝 1) := by
  sorry

/-- The cut test on a non-cut, positive concordance factor: for each `b_n = o(n)`, whatever the fitted
line, the p-value is eventually below the `χ²₁` tail at `b_n`, by the domination of the test
distribution by `Z²`. (TINNiK's proof of Theorem 4, repaired: E10 of the report.) -/
theorem cutTest_alternative (hd : IsDist dist) (hs : DisplaysOne dist sides) {q : Finset X}
    (hq : q.card = 4) (hnc : ∀ r ∈ treesOn q, ∀ r' ∈ treesOn q, r ≠ r' →
      displayCF dist sides r ≠ displayCF dist sides r') :
    ∃ d : ℝ, 0 < d ∧ Tendsto (fun n : ℕ => iidProb dist n fun ω =>
      ∀ s ∈ treesOn q, cutPValue (quartetCount sides ω) s < chiSqOneTail (n * d)) atTop (𝓝 1) := by
  sorry

end Phylogenetics.QuartetTests
