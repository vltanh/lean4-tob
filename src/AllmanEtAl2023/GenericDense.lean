module

public import AllmanEtAl2023.GenericParams

/-!
# Generic parameters are dense

A set of numerical parameters whose complement is null is dense in the valid parameters: a neighbourhood of a valid parameter has an open set of valid parameters. So an
equation between continuous functions that holds for generic parameters holds for all valid parameters. That is how the proof of Proposition 1 can cite statement 1 of Theorem 1, which
is for generic parameters, for the claim on all parameters.
-/

@[expose] public noncomputable section

open Phylogenetics Phylogenetics.RootedNetwork MeasureTheory Filter Topology
open scoped Classical

namespace AllmanEtAl2023

variable {V E X : Type*} [Fintype V] [Fintype E] {N : RootedNetwork V E X}

omit [Fintype V] in
/-- **An equation that holds for generic parameters holds for all valid parameters**, if its two sides are continuous in the coordinates. -/
theorem ForGenericParams.eq_zero_of_continuous (hE : Nonempty E) {Φ : MetricData E → ℝ}
    (hc : ∀ d : V → E, Continuous fun x : (E → ℝ) × (E → ℝ) => Φ (coordMetric N d x.1 x.2))
    (h : ForGenericParams N fun θ => Φ θ = 0) {θ : MetricData E} (hθ : N.IsMetric θ) : Φ θ = 0 := by
  by_contra hne
  obtain ⟨e₀⟩ := hE
  obtain ⟨d, hd⟩ := exists_leftOutParent (N := N) e₀
  let cm : (E → ℝ) × (E → ℝ) → MetricData E := fun x => coordMetric N d x.1 x.2
  have hcm₀ : cm (θ.length, θ.inheritance) = θ := (eq_coordMetric hθ rfl fun _ _ _ => rfl).symm
  have hinh : ∀ e, Continuous fun x => (cm x).inheritance e := fun e =>
    continuousOn_univ.1 (analyticOnNhd_coordMetric_inheritance N d e).continuousOn
  let O₁ : Set ((E → ℝ) × (E → ℝ)) := {x | ∀ e, θ.length e < x.1 e}
  let O₂ : Set ((E → ℝ) × (E → ℝ)) := {x | (∀ e, 0 < (cm x).inheritance e) ∧ Φ (cm x) ≠ 0}
  have hO₁ : IsOpen O₁ := by
    simp only [O₁, Set.ofPred_forall]
    exact isOpen_iInter_of_finite fun e => isOpen_lt continuous_const ((continuous_apply e).comp continuous_fst)
  have hO₂ : IsOpen O₂ := by
    simp only [O₂, Set.ofPred_and, Set.ofPred_forall]
    exact (isOpen_iInter_of_finite fun e => isOpen_lt continuous_const (hinh e)).inter
      (isOpen_ne_fun (hc d) continuous_const)
  have hx₀ : (θ.length, θ.inheritance) ∈ O₂ := by
    refine ⟨fun e => ?_, ?_⟩
    · rw [hcm₀]
      exact NMSC.inheritance_pos hθ e
    · rw [hcm₀]
      exact hne
  -- points of `O₂` with larger lengths than `θ`
  let g : ℝ → (E → ℝ) × (E → ℝ) := fun t => (fun e => θ.length e + t, θ.inheritance)
  have hg : Continuous g := by
    refine Continuous.prodMk (continuous_pi fun e => continuous_const.add continuous_id) continuous_const
  have hg₀ : g 0 = (θ.length, θ.inheritance) := by
    simp [g]
  have hnear : ∀ᶠ t in 𝓝 (0 : ℝ), g t ∈ O₂ := hg.continuousAt.eventually_mem (by
    rw [hg₀]
    exact hO₂.mem_nhds hx₀)
  obtain ⟨t, ht, ht₀⟩ := ((hnear.filter_mono nhdsWithin_le_nhds).and self_mem_nhdsWithin : ∀ᶠ t in 𝓝[>] (0 : ℝ),
    g t ∈ O₂ ∧ t ∈ Set.Ioi 0).exists
  have hgt : g t ∈ O₁ ∩ O₂ := ⟨fun e => by
    have : (0 : ℝ) < t := ht₀
    simp only [g]
    linarith, ht⟩
  have hnull := h d hd
  have hsub : O₁ ∩ O₂ ⊆ {x | ∃ θ' ∈ {θ' | N.IsMetric θ' ∧ ¬ Φ θ' = 0}, N.IsMetric θ' ∧ θ'.length = x.1 ∧
      ∀ e, N.IsHybridArc e → e ≠ d (N.graph.target e) → θ'.inheritance e = x.2 e} := by
    rintro x ⟨hx₁, hx₂, hxΦ⟩
    have hm : N.IsMetric (cm x) := by
      refine ⟨fun e _ => lt_of_le_of_lt (NMSC.length_nonneg hθ e) (hx₁ e), fun e _ => (lt_of_le_of_lt (NMSC.length_nonneg hθ e) (hx₁ e)).le,
        fun e he => coordMetric_inheritance_of_isTreeArc he, fun e _ => hx₂ e, fun v hv => ?_⟩
      exact sum_coordMetric_inheritance hd hv
    exact ⟨cm x, ⟨hm, hxΦ⟩, hm, rfl, fun e he hne => coordMetric_inheritance_of_ne he hne⟩
  have h0 := measure_mono_null hsub hnull
  exact (hO₁.inter hO₂).measure_pos _ ⟨_, hgt⟩ |>.ne' h0

end AllmanEtAl2023
