module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
public import Mathlib.Data.Multiset.Fold

/-!
# Combining p-values

A multiset of p-values, combined by the Bonferroni correction (`bonP`) or by the Cauchy combination test
of Liu and Xie (2020) (`cauchyP`), which allows arbitrary dependence, and the combinations of these two
(`bbcP`, `cbcP`; Rhodes, Allman, Ané, Baños 2026). `combineP` selects a method.

## References

* Y. Liu, J. Xie, *Cauchy combination test: a powerful test with analytic p-value calculation under
  arbitrary dependency structures*, J. Amer. Statist. Assoc. 115 (2020) 393–402.
* J. A. Rhodes, E. S. Allman, C. Ané, H. Baños, *Statistical inference of the Tree of Blobs of a
  phylogenetic network from quartet concordance factors*, bioRxiv 10.64898/2026.05.28.728501.
-/

@[expose] public noncomputable section

namespace Phylogenetics

/-- The Cauchy transform `f(p) = tan(π(1/2 - p))`. -/
def cauchyTransform (p : ℝ) : ℝ := Real.tan (Real.pi * (1 / 2 - p))

/-- The inverse of the Cauchy transform on `(0, 1)`. -/
def cauchyInverse (y : ℝ) : ℝ := 1 / 2 - Real.arctan y / Real.pi

/-- The minimum of a multiset of p-values, with the value `1` for the empty multiset. -/
def minP (P : Multiset ℝ) : ℝ := P.fold min 1

/-- `Bon(P) = min(1, k min(P))`. -/
def bonP (P : Multiset ℝ) : ℝ := min 1 ((Multiset.card P : ℝ) * minP P)

/-- The Cauchy combination `f⁻¹(mean f(pᵢ))`. The transform has infinite values at `0` and `1`,
and the mean is extended continuously: a p-value `0` gives `0`, and otherwise a p-value `1` gives `1`.
(No continuous extension exists at multisets with both `0` and `1`; this definition gives `0` there.) -/
def cauchyP (P : Multiset ℝ) : ℝ :=
  if (0 : ℝ) ∈ P then 0 else if (1 : ℝ) ∈ P then 1 else
    cauchyInverse ((P.map cauchyTransform).sum / (Multiset.card P : ℝ))

/-- `BBC(P) = Bon({Bon(P), Cauchy(P)})`. -/
def bbcP (P : Multiset ℝ) : ℝ := bonP {bonP P, cauchyP P}

/-- `CBC(P) = Cauchy({Bon(P), Cauchy(P)})`. -/
def cbcP (P : Multiset ℝ) : ℝ := cauchyP {bonP P, cauchyP P}

/-- The methods of combining p-values above. -/
inductive TestCorrection
  | bon
  | cauchy
  | bbc
  | cbc

/-- Combining p-values by a correction method. An empty multiset of p-values, with no null hypothesis
to test, gets the value `1`. -/
def combineP (m : TestCorrection) (P : Multiset ℝ) : ℝ :=
  if P = 0 then 1 else
  match m with
  | .bon => bonP P
  | .cauchy => cauchyP P
  | .bbc => bbcP P
  | .cbc => cbcP P

/-- The maximum of a multiset of p-values, with the value `0` for the empty multiset. -/
def maxP (P : Multiset ℝ) : ℝ := P.fold max 0

end Phylogenetics
