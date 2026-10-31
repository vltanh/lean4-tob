module

public import Basic.Phylogenetics.Defs
public import Mathlib.Probability.ProbabilityMassFunction.Constructions
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.Order.Filter.AtTopBot.Basic

/-!
# Independent samples from a finite distribution

The probability `iidProb dist n Ev` of an event for `n` independent draws from `dist`, as a finite
sum, with the elementary facts the proofs use: bounds, union bounds, and the weak law of large
numbers; and the bridge to Mathlib's product measures, on which the central limit theorem applies.

API: `IsDist`, `iidProb_nonneg`, `iidProb_le_one`, `iidProb_mono`, `iidProb_compl`, `iidProb_univ`,
`tendsto_iidProb_forall`, `tendsto_iidProb_of_imp`, `iidProb_weak_law`.
-/

@[expose] public noncomputable section

open Finset Filter Topology MeasureTheory
open scoped Classical

namespace Phylogenetics

variable {Γ : Type*} [Fintype Γ]

/-- `dist` is a probability distribution. -/
def IsDist (dist : Γ → ℝ) : Prop := (∀ g, 0 ≤ dist g) ∧ ∑ g, dist g = 1

variable {dist : Γ → ℝ}

theorem iidProb_nonneg (hd : IsDist dist) (n : ℕ) (Ev : (Fin n → Γ) → Prop) :
    0 ≤ iidProb dist n Ev := by
  sorry

theorem iidProb_true (hd : IsDist dist) (n : ℕ) : iidProb dist n (fun _ => True) = 1 := by
  sorry

theorem iidProb_le_one (hd : IsDist dist) (n : ℕ) (Ev : (Fin n → Γ) → Prop) :
    iidProb dist n Ev ≤ 1 := by
  sorry

theorem iidProb_mono (hd : IsDist dist) {n : ℕ} {Ev Ev' : (Fin n → Γ) → Prop}
    (h : ∀ ω, Ev ω → Ev' ω) : iidProb dist n Ev ≤ iidProb dist n Ev' := by
  sorry

theorem iidProb_not (hd : IsDist dist) (n : ℕ) (Ev : (Fin n → Γ) → Prop) :
    iidProb dist n (fun ω => ¬ Ev ω) = 1 - iidProb dist n Ev := by
  sorry

/-- If each of finitely many events has probability tending to one, so does their intersection. -/
theorem tendsto_iidProb_forall (hd : IsDist dist) {ι : Type*} [Fintype ι]
    (Ev : ι → (n : ℕ) → (Fin n → Γ) → Prop)
    (h : ∀ i, Tendsto (fun n => iidProb dist n (Ev i n)) atTop (𝓝 1)) :
    Tendsto (fun n => iidProb dist n fun ω => ∀ i, Ev i n ω) atTop (𝓝 1) := by
  sorry

/-- An event containing, for large `n`, an event with probability tending to one. -/
theorem tendsto_iidProb_of_imp (hd : IsDist dist) {Ev Ev' : (n : ℕ) → (Fin n → Γ) → Prop}
    (himp : ∀ᶠ n in atTop, ∀ ω, Ev n ω → Ev' n ω)
    (h : Tendsto (fun n => iidProb dist n (Ev n)) atTop (𝓝 1)) :
    Tendsto (fun n => iidProb dist n (Ev' n)) atTop (𝓝 1) := by
  sorry

/-- **The weak law of large numbers** for a function of `n` independent draws. -/
theorem iidProb_weak_law (hd : IsDist dist) (f : Γ → ℝ) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n => iidProb dist n fun ω =>
      |(∑ i, f (ω i)) / n - ∑ g, dist g * f g| < ε) atTop (𝓝 1) := by
  sorry

end Phylogenetics
