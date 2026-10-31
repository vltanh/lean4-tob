module

public import Basic.Phylogenetics.Defs
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Measure.Dirac.Basic

/-!
# ECToBlob §5: the model assumption

Equations (5.1) and (5.2) and Assumption 1. The paper's "generic" is the exclusion of a null set in
the measure on numerical parameters given after Assumption 1: Lebesgue measure on `(0, ∞)` for tree
edge lengths, `δ₀ + Lebesgue` on `[0, ∞)` for hybrid edge lengths, and Lebesgue measure on the
inheritance probabilities. Of the inheritance probabilities entering a hybrid vertex, those
of all but one parent (`free`) are the coordinates; which parent is left out does not change the null
sets.
-/

@[expose] public noncomputable section

open Phylogenetics Phylogenetics.RootedNetwork MeasureTheory Set
open scoped Classical

namespace ECToBlob

variable {V E X : Type*} [Fintype X] [DecidableEq X]

variable (N : RootedNetwork V E X)

/-- The measure of §5.1 on the length of an edge, tree or hybrid. -/
def lengthMeasure (hybrid : Prop) : Measure ℝ :=
  if hybrid then Measure.dirac 0 + volume.restrict (Ici 0) else volume.restrict (Ioi 0)

instance (hybrid : Prop) : SigmaFinite (lengthMeasure hybrid) := by
  unfold lengthMeasure
  split_ifs <;> infer_instance

variable [Fintype V] [Fintype E]

/-- A choice of one parent arc at each vertex: the coordinate left out of the inheritance
probabilities. -/
def IsParentChoice (d : V → E) : Prop := ∀ v, 2 ≤ N.graph.indegree v → N.graph.target (d v) = v

/-- The numerical parameters with the given edge lengths and free inheritance probabilities. -/
def metricOfCoords (d : V → E) (ℓ g : E → ℝ) : MetricData E where
  length := ℓ
  inheritance e :=
    if N.IsHybridArc e then
      if e = d (N.graph.target e) then
        1 - ∑ f ∈ Finset.univ.filter (fun f => N.graph.target f = N.graph.target e ∧ f ≠ e), g f
      else g e
    else 1

/-- A set of numerical parameters is null for the measure of §5.1 on valid parameters. -/
def IsNullParams (A : Set (MetricData E)) : Prop :=
  ∀ d : V → E, IsParentChoice N d →
    ((Measure.pi fun e => lengthMeasure (N.IsHybridArc e)).prod
      (Measure.pi fun _ : E => volume.restrict (Ioo (0 : ℝ) 1)))
      {x | N.IsMetric (metricOfCoords N d x.1 x.2) ∧ metricOfCoords N d x.1 x.2 ∈ A} = 0

/-- **Assumption 1** (`ecto:assumption1`) for a model that gives concordance factors `model θ` at the
parameters `θ` of the network `N`. -/
def Assumption1 (model : MetricData E → QuartetTree X → ℝ) : Prop :=
  (∀ θ, N.IsMetric θ → Assumption1Forward N (model θ)) ∧
    IsNullParams N {θ | N.IsMetric θ ∧ ¬ Assumption1Converse N (model θ)}

end ECToBlob
