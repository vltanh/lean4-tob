module

public import Basic.Phylogenetics.Network
public import Mathlib.Data.Fintype.Option

/-!
# Rooted star networks

These concrete examples witness the defining network and metric laws. They do
not assert a network-model or statistical theorem of any source paper.
-/

@[expose] public section

namespace Phylogenetics

/-- One root and one pendant arc for every taxon. -/
def starNetwork (X : Type*) : RootedNetwork (Option X) X X where
  graph := ⟨fun _ => none, some⟩
  root := none
  leaf := some

namespace starNetwork

variable (X : Type*)

@[simp] theorem indegree_root : (starNetwork X).graph.indegree none = 0 := by
  simp [starNetwork, DirectedMultigraph.indegree]

@[simp] theorem indegree_leaf (x : X) :
    (starNetwork X).graph.indegree (some x) = 1 := by
  simp [starNetwork, DirectedMultigraph.indegree]

@[simp] theorem outdegree_root :
    (starNetwork X).graph.outdegree none = Nat.card X := by
  simp [starNetwork, DirectedMultigraph.outdegree]

@[simp] theorem outdegree_leaf (x : X) :
    (starNetwork X).graph.outdegree (some x) = 0 := by
  simp [starNetwork, DirectedMultigraph.outdegree]

/-- A rooted star is a valid finite phylogenetic network whenever taxa exist. -/
theorem isPhylogenetic [Finite X] [Nonempty X] : (starNetwork X).IsPhylogenetic := by
  refine ⟨inferInstance, inferInstance, inferInstance, ?_, ?_, indegree_root X, ?_,
    Option.some_injective X, ?_, ?_⟩
  · apply DirectedMultigraph.isAcyclic_of_rank _ (fun v => if v.isSome then 1 else 0)
    intro e
    simp [starNetwork]
  · intro v
    cases v with
    | none => exact .refl
    | some x => exact .single ⟨x, rfl, rfl⟩
  · intro v hv
    cases v with
    | none => exact False.elim (hv rfl)
    | some x => simp
  · exact indegree_leaf X
  · intro v
    cases v with
    | none => simp [starNetwork, DirectedMultigraph.outdegree, Nat.card_pos.ne']
    | some x => simp [starNetwork, DirectedMultigraph.outdegree]

/-- Two taxa give a binary rooted star. -/
theorem fin_two_isBinary : (starNetwork (Fin 2)).IsBinary := by
  constructor
  · simp [starNetwork, DirectedMultigraph.outdegree]
  · intro v hv hout
    cases v with
    | none => exact False.elim (hv rfl)
    | some x => exact False.elim (hout (outdegree_leaf _ x))

end starNetwork
end Phylogenetics

