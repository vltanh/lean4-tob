module

public import Basic.Combinatorics.DirectedMultigraph
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Data.Fintype.Powerset

/-!
Exact finite-cut check for the five-leaf sunlet described in the TOB-QMC supplement audit.
Vertices are `s=0,r=1,u=2,v=3,w=4,h=5,e=6,a=7,b=8,c=9,d=10`.
The directed arcs are `se,sr,ru,uv,vh,rw,wh,ua,vb,wc,hd`, in that order.

The checks below certify acyclicity and the cut obstruction on `Y={e,a,b,c}`:
the full graph has no single-arc cut separating Y two versus two, while deleting
vertices h,d leaves a single-arc cut separating a,b from c,e. They do not assert
that a restriction, suppression, or reduced-tree-of-blobs construction has been
formalized. All finite computations use kernel-checked `decide`.
-/

@[expose] public section

namespace SunletCheck

abbrev V := Fin 11
abbrev E := Fin 11

def graph : DirectedMultigraph V E where
  source := ![0, 0, 1, 2, 3, 1, 4, 2, 3, 4, 5]
  target := ![6, 1, 2, 3, 5, 4, 5, 7, 8, 9, 10]

def quartet : Finset V := {6, 7, 8, 9}

def crossing (edges : Finset E) (S : Finset V) : Finset E :=
  edges.filter fun e ↦
    (graph.source e ∈ S ∧ graph.target e ∉ S) ∨
      (graph.target e ∈ S ∧ graph.source e ∉ S)

theorem mem_crossing_iff (edges : Finset E) (S : Finset V) (e : E) :
    e ∈ crossing edges S ↔ e ∈ edges ∧ graph.Crosses e (S : Set V) := by
  simp only [crossing, Finset.mem_filter, DirectedMultigraph.Crosses, Finset.mem_coe]

theorem source_lt_target : ∀ e : E, graph.source e < graph.target e := by decide

theorem acyclic : graph.IsAcyclic := by
  intro v hv
  have hstep : graph.Adj ≤ (fun a b : V ↦ a < b) := by
    rintro a b ⟨e, rfl, rfl⟩
    exact source_lt_target e
  exact (lt_irrefl v) (Relation.transGen_minimal hstep _ _ hv)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
/-- Exhaustive check of all 2048 vertex cuts. A full-graph singleton-arc cut leaves
zero, one, three, or four of the selected taxa on either chosen side. -/
theorem full_singleton_cut_quartet_card : ∀ S : Finset V,
    (crossing Finset.univ S).card = 1 → (quartet ∩ S).card ∈ ({0, 1, 3, 4} : Finset ℕ) := by
  decide

/-- In particular, the selected quartet has no full-graph cut with two taxa on each side. -/
theorem full_no_two_two_singleton_cut (S : Finset V)
    (hcut : (crossing Finset.univ S).card = 1) : (quartet ∩ S).card ≠ 2 := by
  have hcard := full_singleton_cut_quartet_card S hcut
  intro htwo
  rw [htwo] at hcard
  exact (by decide : 2 ∉ ({0, 1, 3, 4} : Finset ℕ)) hcard

/-- The same obstruction expressed using the project's actual arc-crossing predicate. -/
theorem full_graph_cut_not_two_two (S : Finset V) (e : E)
    (hcut : ∀ f, graph.Crosses f (S : Set V) ↔ f = e) :
    (quartet ∩ S).card ≠ 2 := by
  apply full_no_two_two_singleton_cut S
  have hcrossing : crossing Finset.univ S = {e} := by
    ext f
    simpa only [mem_crossing_iff, Finset.mem_univ, true_and,
      Finset.mem_singleton] using hcut f
  rw [hcrossing, Finset.card_singleton]

def retainedVertices : Finset V := Finset.univ \ {5, 10}

def retainedArcs : Finset E := {0, 1, 2, 3, 5, 7, 8, 9}

/-- These are precisely the arcs retained by deleting h and d. -/
theorem retained_arcs_eq_induced : retainedArcs = Finset.univ.filter (fun e ↦
    graph.source e ∈ retainedVertices ∧ graph.target e ∈ retainedVertices) := by decide

theorem retained_endpoints (e : E) (he : e ∈ retainedArcs) :
    graph.source e ∈ retainedVertices ∧ graph.target e ∈ retainedVertices := by
  rw [retained_arcs_eq_induced] at he
  exact (Finset.mem_filter.mp he).2

/-- Actual vertex and arc subtypes for the graph after deleting h,d. -/
def pruned : DirectedMultigraph {v : V // v ∈ retainedVertices}
    {e : E // e ∈ retainedArcs} where
  source e := ⟨graph.source e.1,
    (retained_endpoints e.1 e.2).1⟩
  target e := ⟨graph.target e.1,
    (retained_endpoints e.1 e.2).2⟩

def abSide : Finset V := {2, 3, 7, 8}

/-- The sole crossing arc after deletion is `r→u`, original arc number2. -/
theorem restricted_crossing : crossing retainedArcs abSide = {2} := by decide

theorem abSide_retained : abSide ⊆ retainedVertices := by decide

theorem quartet_on_abSide : quartet ∩ abSide = {7, 8} := by decide

theorem quartet_off_abSide : quartet \ abSide = {6, 9} := by decide

theorem restricted_two_two_singleton_cut :
    (crossing retainedArcs abSide).card = 1 ∧ (quartet ∩ abSide).card = 2 := by decide

/-- The certified crossing arc is also a bridge in Mathlib's underlying multigraph. -/
theorem pruned_has_bridge :
    pruned.underlying.IsBridge (⟨2, by decide⟩ : {e : E // e ∈ retainedArcs}) := by
  apply (pruned.isBridge_iff _).mpr
  refine ⟨{v | v.1 ∈ abSide}, ?_⟩
  intro e
  have hmem : e.1 ∈ crossing retainedArcs abSide ↔ e.1 = 2 := by
    rw [restricted_crossing, Finset.mem_singleton]
  have hcross : graph.Crosses e.1 (abSide : Set V) ↔ e.1 = 2 := by
    simpa only [mem_crossing_iff, e.2, true_and] using hmem
  simpa only [DirectedMultigraph.Crosses, pruned, Set.mem_ofPred_eq,
    Finset.mem_coe, Subtype.ext_iff] using hcross

#print axioms full_singleton_cut_quartet_card
#print axioms restricted_two_two_singleton_cut
#print axioms acyclic
#print axioms pruned_has_bridge

end SunletCheck
