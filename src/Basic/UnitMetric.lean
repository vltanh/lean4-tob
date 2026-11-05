module

public import Phylogenetics.Network.Defs
public import Phylogenetics.Graph.Defs

/-!
# Valid parameters on any network

`unitMetric N`: all lengths `1`, and equal inheritance probabilities at each reticulation. This shows that a statement over the valid parameters of a
network has an instance. Only `Fintype E` is needed.
-/

@[expose] public noncomputable section

open Phylogenetics Phylogenetics.RootedNetwork

namespace ECToBlob

variable {V E X : Type*} [Fintype E]

/-- All lengths `1`, and the inheritance probabilities `1 / indegree`. -/
def unitMetric (N : RootedNetwork V E X) : MetricData E :=
  ⟨fun _ => 1, fun e => 1 / (N.graph.indegree (N.graph.target e) : ℝ)⟩

/-- **Every network has valid parameters.** -/
theorem isMetric_unitMetric (N : RootedNetwork V E X) : N.IsMetric (unitMetric N) := by
  classical
  refine ⟨fun _ _ => one_pos, fun _ _ => zero_le_one, fun e he => ?_, fun e he => ?_, fun v hv => ?_⟩
  · have h1 : N.graph.indegree (N.graph.target e) = 1 := he
    simp [unitMetric, h1]
  · have h2 : 2 ≤ N.graph.indegree (N.graph.target e) := he
    have : (0 : ℝ) < N.graph.indegree (N.graph.target e) := by exact_mod_cast (by omega : 0 < N.graph.indegree (N.graph.target e))
    exact one_div_pos.2 this
  · have hcard : ((Finset.univ.filter fun e => N.graph.target e = v).card : ℝ) = N.graph.indegree v := by
      rw [DirectedMultigraph.indegree, Set.ncard_eq_toFinset_card']
      congr 2
      ext e
      simp
    have hne : (N.graph.indegree v : ℝ) ≠ 0 := by
      have : 0 < N.graph.indegree v := by omega
      exact_mod_cast this.ne'
    have hstep : ∀ e, (if N.graph.target e = v then (unitMetric N).inheritance e else 0) =
        if N.graph.target e = v then 1 / (N.graph.indegree v : ℝ) else 0 := by
      intro e
      split_ifs with h
      · simp [unitMetric, h]
      · rfl
    simp only [hstep]
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, hcard]
    exact mul_one_div_cancel hne

end ECToBlob
