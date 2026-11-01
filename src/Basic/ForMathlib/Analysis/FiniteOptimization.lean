module

public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Finset.Max
public import Mathlib.Basic.Real.Basic
public import Mathlib.Order.Filter.Extr
public import Mathlib.Tactic.Linarith

/-!
# Perturbations of finite real-valued optimization problems

Sufficiently small uniform errors cannot introduce new maximizers on a finite search space.

## Main results

* `abs_sum_sub_sum_lt_card_mul`, `uniform_abs_sum_sub_sum_lt_card_mul`: bounds on a perturbed finite sum.
* `isMaxOn_of_uniform_error`, `isMaxOn_sum_of_uniform_coordinate_error`: maximizers of the perturbation
  are maximizers.
* `exists_pos_gap_of_finite_scores`, `exists_pos_radius_isMaxOn`: a positive gap, and a radius that
  suffices.
-/

@[expose] public section

open scoped BigOperators

namespace Finset

variable {ι X : Type*}

/-- Strict coordinate errors give a strict error bound for a sum over a nonempty finite set.
Nonemptiness matters: for an empty sum the proposed strict bound would read `0 < 0`. -/
theorem abs_sum_sub_sum_lt_card_mul (I : Finset ι) (hI : I.Nonempty)
    {f g : ι → ℝ} {ε : ℝ} (herror : ∀ i ∈ I, |f i - g i| < ε) :
    |(∑ i ∈ I, f i) - ∑ i ∈ I, g i| < (I.card : ℝ) * ε := by
  calc
    |(∑ i ∈ I, f i) - ∑ i ∈ I, g i| = |∑ i ∈ I, (f i - g i)| := by
      rw [sum_sub_distrib]
    _ ≤ ∑ i ∈ I, |f i - g i| := abs_sum_le_sum_abs _ _
    _ < ∑ _i ∈ I, ε := sum_lt_sum_of_nonempty hI herror
    _ = (I.card : ℝ) * ε := by simp

/-- A margin at least twice the total error budget preserves a strict ordering of two
finite-sum scores. Equality in the margin hypothesis is allowed because the coordinate
error bounds are strict. -/
theorem sum_lt_sum_of_margin (I : Finset ι) (hI : I.Nonempty)
    {f g : ι → X → ℝ} {x y : X} {ε : ℝ}
    (hx : ∀ i ∈ I, |f i x - g i x| < ε)
    (hy : ∀ i ∈ I, |f i y - g i y| < ε)
    (hmargin : 2 * (I.card : ℝ) * ε ≤ (∑ i ∈ I, f i y) - ∑ i ∈ I, f i x) :
    (∑ i ∈ I, g i x) < ∑ i ∈ I, g i y := by
  have hx' := (abs_lt.mp (abs_sum_sub_sum_lt_card_mul I hI hx)).1
  have hy' := (abs_lt.mp (abs_sum_sub_sum_lt_card_mul I hI hy)).2
  linarith

/-- Coordinate bounds uniform on a finite search space give uniform bounds for its scores. -/
theorem uniform_abs_sum_sub_sum_lt_card_mul (I : Finset ι) (hI : I.Nonempty)
    (S : Finset X) {f g : ι → X → ℝ} {ε : ℝ}
    (herror : ∀ x ∈ S, ∀ i ∈ I, |f i x - g i x| < ε) :
    ∀ x ∈ S, |(∑ i ∈ I, f i x) - ∑ i ∈ I, g i x| < (I.card : ℝ) * ε := by
  intro x hx
  exact abs_sum_sub_sum_lt_card_mul I hI (herror x hx)

/-- A uniform error less than half the gap between unequal true scores ensures that every
feasible estimated maximizer is a true maximizer. The gap hypothesis only concerns pairs
with strictly different true scores, so ties between true maximizers are allowed. -/
theorem isMaxOn_of_uniform_error (S : Finset X) {f g : X → ℝ} {δ γ : ℝ}
    (hgap : ∀ x ∈ S, ∀ y ∈ S, f x < f y → γ ≤ f y - f x)
    (herror : ∀ x ∈ S, |f x - g x| < δ) (hbudget : 2 * δ ≤ γ)
    {x : X} (hx : x ∈ S) (hmax : IsMaxOn g (S : Set X) x) :
    IsMaxOn f (S : Set X) x := by
  intro y hy
  by_contra hxy
  have hlt : f x < f y := lt_of_not_ge hxy
  have hgap' := hgap x hx y hy hlt
  have hx' := (abs_lt.mp (herror x hx)).1
  have hy' := (abs_lt.mp (herror y hy)).2
  have hg : g y ≤ g x := hmax hy
  linarith

/-- The preceding maximizer-stability statement specialized to finite sums with uniform
coordinate errors. The explicit gap must be proved from the true scores in an application. -/
theorem isMaxOn_sum_of_uniform_coordinate_error (I : Finset ι) (hI : I.Nonempty)
    (S : Finset X) {f g : ι → X → ℝ} {ε γ : ℝ}
    (hgap : ∀ x ∈ S, ∀ y ∈ S, (∑ i ∈ I, f i x) < ∑ i ∈ I, f i y →
      γ ≤ (∑ i ∈ I, f i y) - ∑ i ∈ I, f i x)
    (herror : ∀ x ∈ S, ∀ i ∈ I, |f i x - g i x| < ε)
    (hbudget : 2 * ((I.card : ℝ) * ε) ≤ γ)
    {x : X} (hx : x ∈ S) (hmax : IsMaxOn (fun x ↦ ∑ i ∈ I, g i x) (S : Set X) x) :
    IsMaxOn (fun x ↦ ∑ i ∈ I, f i x) (S : Set X) x := by
  exact isMaxOn_of_uniform_error S hgap
    (uniform_abs_sum_sub_sum_lt_card_mul I hI S herror) hbudget hx hmax

/-- On a finite search space, all strictly positive differences of real-valued scores
have a common positive lower bound. If every score is equal, the conclusion is vacuous
and the bound can be chosen to be `1`. -/
theorem exists_pos_gap_of_finite_scores (S : Finset X) (f : X → ℝ) :
    ∃ γ : ℝ, 0 < γ ∧ ∀ x ∈ S, ∀ y ∈ S, f x < f y → γ ≤ f y - f x := by
  classical
  let P := (S ×ˢ S).filter fun p ↦ f p.1 < f p.2
  by_cases hP : P.Nonempty
  · obtain ⟨p, hp, hmin⟩ := exists_min_image P (fun p ↦ f p.2 - f p.1) hP
    refine ⟨f p.2 - f p.1, sub_pos.mpr (mem_filter.mp hp).2, ?_⟩
    intro x hx y hy hxy
    exact hmin (x, y) (mem_filter.mpr ⟨mem_product.mpr ⟨hx, hy⟩, hxy⟩)
  · refine ⟨1, zero_lt_one, ?_⟩
    intro x hx y hy hxy
    exact False.elim (hP ⟨(x, y), mem_filter.mpr ⟨mem_product.mpr ⟨hx, hy⟩, hxy⟩⟩)

/-- Any real-valued score on a finite search space admits a positive uniform perturbation
radius within which the estimated maximizers form a subset of the true maximizers. -/
theorem exists_pos_radius_isMaxOn (S : Finset X) (f : X → ℝ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ g : X → ℝ, (∀ x ∈ S, |f x - g x| < δ) →
      ∀ x ∈ S, IsMaxOn g (S : Set X) x → IsMaxOn f (S : Set X) x := by
  obtain ⟨γ, hγ, hgap⟩ := exists_pos_gap_of_finite_scores S f
  refine ⟨γ / 2, by linarith, ?_⟩
  intro g herror x hx hmax
  exact isMaxOn_of_uniform_error S hgap herror (by linarith) hx hmax

end Finset
