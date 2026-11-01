module

public import Phylogenetics.Tree.Defs
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
public import Mathlib.Probability.Distributions.Gaussian.Real

/-!
# Hypothesis tests on quartet counts: definitions

Statistics and p-values of counts `c : QuartetTree X → ℝ` of the quartet trees on a set of four taxa.

* `starStat`, `pearsonStat`, `starPValue`: the star test of the null hypothesis `(1/3, 1/3, 1/3)`,
  against `χ²₂`.
* `lineStat`, `t1Stat`, `t1Tail`, `t1PValue`: the T1 test of the null hypothesis `p_s ≥ p_{s'} = p_{s''}`
  (Mitchell, Allman, Rhodes 2019).
* `cutStat`, `cutTail`, `cutPValue`: the test of the cut model (Allman, Baños, Mitchell, Rhodes 2024).
* `chiSqOneTail`, `chiSqTwoTail`, `muZero`, `alphaZero`: test distributions and their parameters.

## References

* J. D. Mitchell, E. S. Allman, J. A. Rhodes, *Hypothesis testing near singularities and boundaries*,
  Electron. J. Stat. 13 (2019) 2150–2193.
* E. S. Allman, H. Baños, J. D. Mitchell, J. A. Rhodes, *TINNiK: inference of the tree of blobs of a
  species network under the coalescent model*, Algorithms Mol. Biol. 19 (2024), 23.
-/

@[expose] public noncomputable section

open Finset MeasureTheory ProbabilityTheory
open scoped Classical

namespace Phylogenetics

section Tests

variable {X : Type*} [Fintype X] [DecidableEq X]

/-- The likelihood ratio statistic for the cut-model line of the quartet tree `s`: twice the difference
of the maximal trinomial log-likelihoods, unconstrained and on the line `p_{s'} = p_{s''}`, where
`s'`, `s''` are the alternatives of `s` (TINNiK Appendix C.1). `x log x` vanishes at `x = 0`. -/
def lineStat (c : QuartetTree X → ℝ) (s : QuartetTree X) : ℝ :=
  2 * (∑ r ∈ s.alternatives, c r * Real.log (c r) -
    (∑ r ∈ s.alternatives, c r) * Real.log (∑ r ∈ s.alternatives, c r) +
    (∑ r ∈ s.alternatives, c r) * Real.log 2)

/-- The likelihood ratio statistic of the star test on the taxa `q`: twice the difference
of the maximal trinomial log-likelihoods, unconstrained and at `(1/3, 1/3, 1/3)`. -/
def starStat (c : QuartetTree X → ℝ) (q : Finset X) : ℝ :=
  2 * (∑ r ∈ treesOn q, c r * Real.log (c r) -
    (∑ r ∈ treesOn q, c r) * Real.log ((∑ r ∈ treesOn q, c r) / 3))

/-- Pearson's chi-square statistic of the star test on the taxa `q`, the alternative that ECToBlob
§5.2 allows. -/
def pearsonStat (c : QuartetTree X → ℝ) (q : Finset X) : ℝ :=
  ∑ r ∈ treesOn q, (c r - (∑ t ∈ treesOn q, c t) / 3) ^ 2 / ((∑ t ∈ treesOn q, c t) / 3)

/-- The likelihood ratio statistic of the T1 test (Mitchell, Allman, Rhodes 2019, "Model T1"; ECToBlob
§5.2) with null hypothesis `p_s ≥ p_{s'} = p_{s''}`: the maximum on this null is on the line of `s` when the
data have `c s` at least the mean of the alternatives, and otherwise at the centroid. -/
def t1Stat (c : QuartetTree X → ℝ) (s : QuartetTree X) : ℝ :=
  if (∑ r ∈ s.alternatives, c r) / 2 ≤ c s then lineStat c s else starStat c s.taxa

/-- The parameter `μ₀` of the test distributions, `√(2n) (1 - φ) / √(φ (3 - 2φ))`, for the point
`(1 - 2φ/3, φ/3, φ/3)` and sample size `n`. -/
def muZero (φ n : ℝ) : ℝ := Real.sqrt (2 * n) * (1 - φ) / Real.sqrt (φ * (3 - 2 * φ))

/-- The upper tail at `t` of the T1 test distribution of Mitchell, Allman, Rhodes 2019 ("Application to
Model T1"): that of `Z² + ½ (1 - sgn Z̄) Z̄²` for independent `Z ~ N(0,1)` and `Z̄ ~ N(μ,1)`. -/
def t1Tail (μ t : ℝ) : ℝ :=
  ((gaussianReal 0 1).prod (gaussianReal μ 1)).real
    {z | t < z.1 ^ 2 + if z.2 < 0 then z.2 ^ 2 else 0}

/-- The maximum likelihood estimate of `φ` on the T1 null. -/
def t1Phi (c : QuartetTree X → ℝ) (s : QuartetTree X) : ℝ :=
  min 1 (3 * (∑ r ∈ s.alternatives, c r) / (2 * (c s + ∑ r ∈ s.alternatives, c r)))

/-- The p-value of the T1 test, with the estimated `φ` in the test distribution, as in Mitchell, Allman,
Rhodes 2019. The separate procedures of those papers and of MSCquartets for small counts are not modelled:
they do not arise in the limit, when the concordance factors are positive. -/
def t1PValue (c : QuartetTree X → ℝ) (s : QuartetTree X) : ℝ :=
  t1Tail (muZero (t1Phi c s) (c s + ∑ r ∈ s.alternatives, c r)) (t1Stat c s)

/-- The upper tail at `t` of the `χ²` distribution with 2 degrees of freedom. -/
def chiSqTwoTail (t : ℝ) : ℝ := Real.exp (-t / 2)

/-- The star test used: likelihood ratio (the default) or Pearson. -/
inductive StarTest
  | lrt
  | pearson

/-- The p-value of the star test on the taxa `q`, against the `χ²₂` distribution. -/
def starPValue (k : StarTest) (c : QuartetTree X → ℝ) (q : Finset X) : ℝ :=
  match k with
  | .lrt => chiSqTwoTail (starStat c q)
  | .pearson => chiSqTwoTail (pearsonStat c q)

/-- The upper tail at `t` of the `χ²` distribution with 1 degree of freedom. -/
def chiSqOneTail (t : ℝ) : ℝ := (gaussianReal 0 1).real {z | t < z ^ 2}

/-- The cut-model likelihood ratio statistic on the taxa `q`: the least of the statistics of its
three lines. -/
def cutStat (c : QuartetTree X → ℝ) (q : Finset X) : ℝ := ⨅ s : {s // s ∈ treesOn q}, lineStat c s.val

/-- The angle `α₀` of TINNiK Appendix C.2. -/
def alphaZero (φ : ℝ) : ℝ := Real.arctan (1 / Real.sqrt (3 * (3 - 2 * φ)))

/-- The upper tail at `t` of the distribution of TINNiK Proposition 5 for `φ` and sample size `n`:
that of `min(Z², (sin α₀ Z + cos α₀ Z̄)², (sin α₀ Z - cos α₀ Z̄)²)` for independent `Z ~ N(0,1)`
and `Z̄ ~ N(μ₀,1)`. -/
def cutTail (φ n t : ℝ) : ℝ :=
  ((gaussianReal 0 1).prod (gaussianReal (muZero φ n) 1)).real
    {z | t < min (z.1 ^ 2) (min ((Real.sin (alphaZero φ) * z.1 + Real.cos (alphaZero φ) * z.2) ^ 2)
      ((Real.sin (alphaZero φ) * z.1 - Real.cos (alphaZero φ) * z.2) ^ 2))}

/-- The p-value of the cut test, with `φ` estimated on the cut-model line of the quartet tree `s`, a
maximum likelihood topology: TINNiK Appendix C.2. At the edges `φ̂ = 0` or `3/2`, excluded in the paper's
`φ₀ ∈ (0, 3/2)`, division by zero gives arbitrary values; TINNiK uses other procedures for small counts,
and these counts have vanishing probability when the concordance factors are positive. -/
def cutPValue (c : QuartetTree X → ℝ) (s : QuartetTree X) : ℝ :=
  cutTail (3 * (∑ r ∈ s.alternatives, c r) / (2 * (c s + ∑ r ∈ s.alternatives, c r)))
    (c s + ∑ r ∈ s.alternatives, c r) (cutStat c s.taxa)

end Tests

end Phylogenetics
