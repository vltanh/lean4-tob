module

public import AllmanEtAl2023.Concordance
public import AllmanEtAl2023.Theorem1

/-!
# Generic parameters exist

A statement "for generic numerical parameters" has content: the valid parameters of a network do not themselves form a null set. So at least one valid parameter is off
any null set, and `ForGenericParams N P` implies that `P` holds somewhere.
-/

@[expose] public noncomputable section

open Phylogenetics Phylogenetics.RootedNetwork
open scoped Classical

namespace AllmanEtAl2023

variable {V E X : Type*} [Fintype V] [Fintype E] [Fintype X] [DecidableEq X] {N : RootedNetwork V E X}

omit [Fintype V] [Fintype X] [DecidableEq X] in
/-- At stochastic coordinates, `coordMetric` is a valid parameter. -/
theorem isMetric_coordMetric {d : V → E} (hd : ∀ v, 2 ≤ N.graph.indegree v → N.graph.target (d v) = v)
    {x : (E → ℝ) × (E → ℝ)} (hx : IsStochasticCoords x) : N.IsMetric (coordMetric N d x.1 x.2) := by
  have hcard : (0 : ℝ) < (Fintype.card E : ℝ) + 1 := by positivity
  have hsum : ∀ T : Finset E, ∑ f ∈ T, x.2 f < 1 := by
    intro T
    by_cases hT : T = ∅
    · simp [hT]
    · have hlt : ∑ f ∈ T, x.2 f < ∑ _f ∈ T, ((Fintype.card E : ℝ) + 1)⁻¹ :=
        Finset.sum_lt_sum_of_nonempty (Finset.nonempty_iff_ne_empty.mpr hT) fun f _ => (hx.2 f).2
      refine hlt.trans_le ?_
      rw [Finset.sum_const, nsmul_eq_mul, ← div_eq_mul_inv, div_le_one hcard]
      have : (T.card : ℝ) ≤ Fintype.card E := by exact_mod_cast Finset.card_le_univ T
      linarith
  refine ⟨fun e _ => hx.1 e, fun e _ => (hx.1 e).le, fun e he => ?_, fun e he => ?_, fun v hv => ?_⟩
  · exact coordMetric_inheritance_of_not_isHybridArc (not_isHybridArc_of_isTreeArc he)
  · by_cases hde : e = d (N.graph.target e)
    · rw [coordMetric_inheritance_of_eq he hde]
      exact sub_pos.mpr (hsum _)
    · rw [coordMetric_inheritance_of_ne he hde]
      exact (hx.2 e).1
  · have hdv := hd v hv
    rw [← Finset.sum_filter, ← Finset.add_sum_erase _ _
      (Finset.mem_filter.mpr ⟨Finset.mem_univ (d v), hdv⟩ : d v ∈ Finset.univ.filter fun f => N.graph.target f = v)]
    have hh : N.IsHybridArc (d v) := by
      unfold IsHybridArc
      rwa [hdv]
    rw [coordMetric_inheritance_of_eq hh (by rw [hdv])]
    have hcongr : ∑ f ∈ (Finset.univ.filter fun f => N.graph.target f = v).erase (d v),
        (coordMetric N d x.1 x.2).inheritance f = ∑ f ∈ Finset.univ.filter (fun f => N.graph.target f = N.graph.target (d v) ∧ f ≠ d v), x.2 f := by
      refine Finset.sum_congr ?_ fun f hf => ?_
      · ext f
        simp only [Finset.mem_erase, Finset.mem_filter, Finset.mem_univ, true_and, hdv]
        tauto
      · obtain ⟨hft, hfne⟩ := Finset.mem_filter.mp hf |>.2
        have hfh : N.IsHybridArc f := by
          unfold IsHybridArc
          rw [hft, hdv]
          exact hv
        refine coordMetric_inheritance_of_ne hfh ?_
        rw [hft, hdv]
        exact hfne
    rw [hcongr]
    ring

omit [Fintype V] [Fintype X] [DecidableEq X] in
/-- **Generic parameters exist**: the valid parameters of a phylogenetic network do not form a null set. -/
theorem not_isGenericNull_isMetric (hN : N.IsPhylogenetic) (hE : Nonempty E) : ¬ N.IsGenericNull {θ | N.IsMetric θ} := by
  intro hnull
  obtain ⟨e₀⟩ := hE
  have hfin : Finite E := hN.finite_arcs
  let d : V → E := fun v => if h : ∃ e, N.graph.target e = v then Classical.choose h else e₀
  have hd : ∀ v, 2 ≤ N.graph.indegree v → N.graph.target (d v) = v := by
    intro v hv
    have h : ∃ e, N.graph.target e = v := (N.graph.one_le_indegree_iff v).mp (by omega)
    simp only [d, dite_eq_left h]
    exact Classical.choose_spec h
  obtain ⟨x, hx, hnot⟩ := exists_isStochasticCoords_notMem (E := E) (hnull d hd)
  have hm := isMetric_coordMetric hd hx
  exact hnot ⟨_, hm, hm, rfl, fun e he hne => coordMetric_inheritance_of_ne he hne⟩

omit [Fintype V] [Fintype X] [DecidableEq X] in
/-- A statement for generic parameters holds somewhere. -/
theorem ForGenericParams.exists (hN : N.IsPhylogenetic) (hE : Nonempty E) {P : MetricData E → Prop} (h : ForGenericParams N P) :
    ∃ θ, N.IsMetric θ ∧ P θ := by
  by_contra hno
  push Not at hno
  refine not_isGenericNull_isMetric hN hE (h.mono ?_)
  exact fun θ hθ => ⟨hθ, hno θ hθ⟩

end AllmanEtAl2023
