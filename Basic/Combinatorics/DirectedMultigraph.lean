module

public import Mathlib.Combinatorics.Graph.Connected.EdgeCut
import all Mathlib.Combinatorics.Graph.Connected.EdgeCut
public import Mathlib.Logic.Relation
public import Mathlib.Data.Set.Card

/-!
# Directed multigraphs with individually identified arcs

Distinct arcs may have the same endpoints. Forgetting orientation produces
Mathlib's `Graph`, retaining arc identity, so a pair of parallel arcs does not
become a single bridge. Restriction, deletion and undirected cuts use Mathlib's
multigraph operations. No finiteness, connectivity or network assumptions are
built into the data.
-/

@[expose] public section

/-- A directed multigraph on given vertex and arc types. Every element of the arc
 type is an actual arc; parallel arcs remain distinct. -/
structure DirectedMultigraph (V E : Type*) where
  source : E → V
  target : E → V

namespace DirectedMultigraph
variable {V E X : Type*} (G : DirectedMultigraph V E)

/-- Directed adjacency; reachability may forget multiplicity, cuts do not. -/
def Adj (u v : V) : Prop := ∃ e, G.source e = u ∧ G.target e = v

/-- Reachability permits the empty directed path. -/
def Reaches : V → V → Prop := Relation.ReflTransGen G.Adj

/-- No nonempty directed closed path. -/
def IsAcyclic : Prop := ∀ v, ¬ Relation.TransGen G.Adj v v

/-- The undirected multigraph keeps the same vertices and individually named arcs. -/
def underlying : Graph V E where
  vertexSet := Set.univ
  edgeSet := Set.univ
  IsLink e u v := (G.source e = u ∧ G.target e = v) ∨
    (G.source e = v ∧ G.target e = u)
  isLink_symm := by
    intro e _
    constructor
    intro u v h
    exact h.symm
  eq_or_eq_of_isLink_of_isLink := by
    intro e u v x y h h'
    rcases h with h | h <;> rcases h' with h' | h'
    · exact Or.inl (h.1.symm.trans h'.1)
    · exact Or.inr (h.1.symm.trans h'.1)
    · exact Or.inr (h.2.symm.trans h'.2)
    · exact Or.inl (h.2.symm.trans h'.2)
  edge_mem_iff_exists_isLink := by
    intro e
    exact ⟨fun _ => ⟨G.source e, G.target e, Or.inl ⟨rfl, rfl⟩⟩,
      fun _ => Set.mem_univ e⟩
  left_mem_of_isLink := by intro e u v _; exact Set.mem_univ u

/-- Arc incidence degree, counting parallel arcs separately. -/
noncomputable def indegree (v : V) : ℕ := {e | G.target e = v}.ncard

/-- Arc incidence degree, counting parallel arcs separately. -/
noncomputable def outdegree (v : V) : ℕ := {e | G.source e = v}.ncard

/-- An arc crosses a vertex bipartition, in either orientation. -/
def Crosses (e : E) (S : Set V) : Prop :=
  (G.source e ∈ S ∧ G.target e ∉ S) ∨
    (G.target e ∈ S ∧ G.source e ∉ S)

/-- Bridge to Mathlib's multigraph edge-cut convention. -/
theorem mem_edgeCut_iff (e : E) (S : Set V) :
    e ∈ G.underlying.edgeCut S ↔ G.Crosses e S := by
  constructor
  · rintro ⟨u, v, huv, hu, hv⟩
    rcases huv with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact Or.inl ⟨hu, hv⟩
    · exact Or.inr ⟨hu, hv⟩
  · rintro (⟨hs, ht⟩ | ⟨ht, hs⟩)
    · exact ⟨G.source e, G.target e, Or.inl ⟨rfl, rfl⟩, hs, ht⟩
    · exact ⟨G.target e, G.source e, Or.inr ⟨rfl, rfl⟩, ht, hs⟩

/-- A concrete endpoint characterization of a singleton cut. -/
theorem edgeCut_eq_singleton_iff (e : E) (S : Set V) :
    G.underlying.edgeCut S = {e} ↔ ∀ f, G.Crosses f S ↔ f = e := by
  constructor
  · intro he f
    rw [← G.mem_edgeCut_iff, he, Set.mem_singleton_iff]
  · intro he
    ext f
    exact (G.mem_edgeCut_iff f S).trans (he f)

/-- An individually identified arc is a bridge exactly when it is the only arc
crossing some bipartition. This statement retains parallel-arc information. -/
theorem isBridge_iff (e : E) :
    G.underlying.IsBridge e ↔ ∃ S : Set V, ∀ f, G.Crosses f S ↔ f = e := by
  change (∃ S, G.underlying.edgeCut S = {e}) ↔ _
  exact exists_congr (fun S => G.edgeCut_eq_singleton_iff e S)

/-- Distinct parallel arcs cannot individually be bridges. -/
theorem not_isBridge_of_parallel {e f : E} (hne : e ≠ f)
    (hs : G.source e = G.source f) (ht : G.target e = G.target f) :
    ¬ G.underlying.IsBridge e := by
  intro he
  obtain ⟨S, hS⟩ := (G.isBridge_iff e).mp he
  have heS := (hS e).mpr rfl
  have hfS : G.Crosses f S := by simpa only [Crosses, hs, ht] using heS
  exact hne ((hS f).mp hfS).symm

end DirectedMultigraph
