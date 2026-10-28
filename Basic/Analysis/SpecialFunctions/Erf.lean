module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

/-!
# The real error function

This general special function is defined independently of its statistical applications.
-/

@[expose] public section

namespace Real

/-- The real error function, normalized so its limit at positive infinity is one. -/
noncomputable def erf (x : ℝ) : ℝ :=
  2 / Real.sqrt Real.pi * ∫ t in (0 : ℝ)..x, Real.exp (-(t ^ 2))

end Real
