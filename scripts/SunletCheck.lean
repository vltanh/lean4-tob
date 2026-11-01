module

public import Phylogenetics.Network.AncestralRestriction
public import Mathlib.Tactic.FinCases
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Data.Fintype.Powerset

/-!
Exact finite-cut check for the five-leaf sunlet described in the TOB-QMC supplement audit.
Vertices are `s=0,r=1,u=2,v=3,w=4,h=5,e=6,a=7,b=8,c=9,d=10`.
The directed arcs are `se,sr,ru,uv,vh,rw,wh,ua,vb,wc,hd`, in that order.

The checks below certify rooted phylogenetic validity, binary degrees and the cut
obstruction on `Y={e,a,b,c}`: the full graph has no single-arc cut separating Y
two versus two, while its actual original-root unsuppressed ancestral restriction
has a bridge separating a,b from c,e. Its vertex and arc sets are proved exactly,
and identity-on-label equivalences identify it with the explicit pruned graph.
Suppression, maximal-blob decomposition and the LSA-reduced tree of blobs remain
separate constructions. All finite computations use kernel-checked `decide`.
-/

@[expose] public section

namespace SunletCheck

open Phylogenetics

abbrev V := Fin 11
abbrev E := Fin 11

def graph : DirectedMultigraph V E where
  source := ![0, 0, 1, 2, 3, 1, 4, 2, 3, 4, 5]
  target := ![6, 1, 2, 3, 5, 4, 5, 7, 8, 9, 10]

def network : RootedNetwork V E (Fin 5) where
  graph := graph
  root := 0
  leaf := ![6, 7, 8, 9, 10]

def selectedTaxa : Finset (Fin 5) := {0, 1, 2, 3}

def excludedVertices : Finset V := {5, 10}

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

/-- No arc leaves the deleted hybrid-and-descendant set. -/
theorem excluded_forward_closed : ∀ e : E,
    graph.source e ∈ excludedVertices → graph.target e ∈ excludedVertices := by decide

/-- Forward closure persists along every finite directed path. -/
theorem reaches_preserves_excluded {u v : V} (h : graph.Reaches u v)
    (hu : u ∈ excludedVertices) : v ∈ excludedVertices := by
  induction h with
  | refl => exact hu
  | @tail w z h hstep ih =>
    obtain ⟨e, rfl, rfl⟩ := hstep
    exact excluded_forward_closed e ih

/-- None of the selected labels is in the deleted set. -/
theorem selected_leaf_not_excluded : ∀ x ∈ selectedTaxa,
    network.leaf x ∉ excludedVertices := by decide

/-- The one-arc path for any original arc. -/
theorem edge_reaches (e : E) : graph.Reaches (graph.source e) (graph.target e) :=
  Relation.ReflTransGen.single ⟨e, rfl, rfl⟩

/-- Every retained vertex reaches a selected leaf; the witnesses are explicit paths. -/
theorem retained_ancestral (v : V) (hv : v ∈ retainedVertices) :
    v ∈ network.ancestralVertices (selectedTaxa : Set (Fin 5)) := by
  fin_cases v
  · exact ⟨0, by decide, edge_reaches 0⟩
  · exact ⟨1, by decide, (edge_reaches 2).trans (edge_reaches 7)⟩
  · exact ⟨1, by decide, edge_reaches 7⟩
  · exact ⟨2, by decide, edge_reaches 8⟩
  · exact ⟨3, by decide, edge_reaches 9⟩
  · exact False.elim ((by decide : (5 : V) ∉ retainedVertices) hv)
  · exact ⟨0, by decide, Relation.ReflTransGen.refl⟩
  · exact ⟨1, by decide, Relation.ReflTransGen.refl⟩
  · exact ⟨2, by decide, Relation.ReflTransGen.refl⟩
  · exact ⟨3, by decide, Relation.ReflTransGen.refl⟩
  · exact False.elim ((by decide : (10 : V) ∉ retainedVertices) hv)

/-- The manually retained vertices are exactly the actual ancestral vertex set. -/
theorem ancestralVertices_eq_retained :
    network.ancestralVertices (selectedTaxa : Set (Fin 5)) = (retainedVertices : Set V) := by
  ext v
  constructor
  · rintro ⟨x, hx, hpath⟩
    by_contra hv
    have hex : v ∈ excludedVertices := by
      by_contra hx
      exact hv (Finset.mem_sdiff.mpr ⟨Finset.mem_univ v, hx⟩)
    exact selected_leaf_not_excluded x hx (reaches_preserves_excluded hpath hex)
  · exact retained_ancestral v

/-- The manually retained arcs are exactly the actual ancestral arc set. -/
theorem ancestralArcs_eq_retained :
    network.ancestralArcs (selectedTaxa : Set (Fin 5)) = (retainedArcs : Set E) := by
  ext e
  change graph.target e ∈ network.ancestralVertices (selectedTaxa : Set (Fin 5)) ↔ _
  rw [ancestralVertices_eq_retained]
  have h : ∀ e : E, graph.target e ∈ retainedVertices ↔ e ∈ retainedArcs := by decide
  exact h e

/-- Identity on vertex labels identifies pruning with the ancestral vertex subtype. -/
def retainedVertexEquiv : {v : V // v ∈ retainedVertices} ≃
    network.AncestralVertex (selectedTaxa : Set (Fin 5)) where
  toFun v := ⟨v.val, (Set.ext_iff.mp ancestralVertices_eq_retained v.val).mpr v.property⟩
  invFun v := ⟨v.val, (Set.ext_iff.mp ancestralVertices_eq_retained v.val).mp v.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Identity on arc labels identifies pruning with the ancestral arc subtype. -/
def retainedArcEquiv : {e : E // e ∈ retainedArcs} ≃
    network.AncestralArc (selectedTaxa : Set (Fin 5)) where
  toFun e := ⟨e.val, (Set.ext_iff.mp ancestralArcs_eq_retained e.val).mpr e.property⟩
  invFun e := ⟨e.val, (Set.ext_iff.mp ancestralArcs_eq_retained e.val).mp e.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The vertex and arc equivalences preserve both endpoints: an explicit directed
multigraph isomorphism retaining original arc identity. -/
theorem pruned_ancestral_isomorphism :
    (∀ e, retainedVertexEquiv (pruned.source e) =
      (network.ancestralGraph (selectedTaxa : Set (Fin 5))).source (retainedArcEquiv e)) ∧
    (∀ e, retainedVertexEquiv (pruned.target e) =
      (network.ancestralGraph (selectedTaxa : Set (Fin 5))).target (retainedArcEquiv e)) := by
  constructor <;> intro e <;> rfl

/-- All original vertices are reachable from the specified root. -/
theorem root_reaches : ∀ v, network.graph.Reaches network.root v := by
  intro v
  fin_cases v
  · exact Relation.ReflTransGen.refl
  · exact edge_reaches 1
  · exact (edge_reaches 1).trans (edge_reaches 2)
  · exact ((edge_reaches 1).trans (edge_reaches 2)).trans (edge_reaches 3)
  · exact (edge_reaches 1).trans (edge_reaches 5)
  · exact ((edge_reaches 1).trans (edge_reaches 5)).trans (edge_reaches 6)
  · exact edge_reaches 0
  · exact ((edge_reaches 1).trans (edge_reaches 2)).trans (edge_reaches 7)
  · exact (((edge_reaches 1).trans (edge_reaches 2)).trans (edge_reaches 3)).trans
      (edge_reaches 8)
  · exact ((edge_reaches 1).trans (edge_reaches 5)).trans (edge_reaches 9)
  · exact (((edge_reaches 1).trans (edge_reaches 5)).trans (edge_reaches 6)).trans
      (edge_reaches 10)

/-- Arc incidence degrees computed from the original eleven arc identities. -/
theorem indegrees : ∀ v : V,
    graph.indegree v = ![0, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1] v := by
  simp only [DirectedMultigraph.indegree, Set.ncard_eq_toFinset_card', Set.toFinset_ofPred]
  decide

/-- Outdegrees count both reticulation-parent arcs separately. -/
theorem outdegrees : ∀ v : V,
    graph.outdegree v = ![2, 2, 2, 2, 2, 1, 0, 0, 0, 0, 0] v := by
  simp only [DirectedMultigraph.outdegree, Set.ncard_eq_toFinset_card', Set.toFinset_ofPred]
  decide

/-- The original sunlet satisfies all of the project's rooted phylogenetic laws. -/
theorem network_isPhylogenetic : network.IsPhylogenetic where
  finite_vertices := inferInstance
  finite_arcs := inferInstance
  finite_taxa := inferInstance
  acyclic := acyclic
  root_reaches := root_reaches
  root_indegree := indegrees 0
  nonroot_indegree := by
    change ∀ v, v ≠ 0 → 1 ≤ graph.indegree v
    simp only [indegrees]
    decide
  leaf_injective := by
    change Function.Injective (![6, 7, 8, 9, 10] : Fin 5 → V)
    decide
  leaf_indegree := by
    change ∀ x : Fin 5, graph.indegree (network.leaf x) = 1
    simp only [indegrees]
    decide
  leaves := by
    change ∀ v, graph.outdegree v = 0 ↔ ∃ x, network.leaf x = v
    simp only [outdegrees]
    decide

/-- Binary internal incidence degrees are also certified. -/
theorem network_isBinary : network.IsBinary := by
  change graph.outdegree 0 = 2 ∧
    ∀ v, v ≠ 0 → graph.outdegree v ≠ 0 → graph.indegree v + graph.outdegree v = 3
  simp only [indegrees, outdegrees]
  decide

/-- The selected set is nonempty, so the generic validity theorem applies. -/
theorem selectedTaxa_nonempty : (selectedTaxa : Set (Fin 5)).Nonempty := ⟨0, by decide⟩

/-- The actual original-root ancestral restriction is a rooted phylogenetic network. -/
theorem ancestralNetwork_isPhylogenetic :
    (network.ancestralNetwork (selectedTaxa : Set (Fin 5)) selectedTaxa_nonempty
      network_isPhylogenetic.root_reaches).IsPhylogenetic :=
  network.ancestralNetwork_isPhylogenetic network_isPhylogenetic _ selectedTaxa_nonempty

/-- The a,b side, as a set of vertices in the actual ancestral restriction. -/
def ancestralAbSide : Set (network.AncestralVertex (selectedTaxa : Set (Fin 5))) :=
  {v | v.val ∈ abSide}

/-- The actual ancestral graph has exactly the original arc r→u crossing this side. -/
theorem ancestral_crossing_iff
    (e : network.AncestralArc (selectedTaxa : Set (Fin 5))) :
    (network.ancestralGraph (selectedTaxa : Set (Fin 5))).Crosses e ancestralAbSide ↔
      e.val = 2 := by
  have he : e.val ∈ retainedArcs :=
    (Set.ext_iff.mp ancestralArcs_eq_retained e.val).mp e.property
  have hmem : e.val ∈ crossing retainedArcs abSide ↔ e.val = 2 := by
    rw [restricted_crossing, Finset.mem_singleton]
  have hcross : graph.Crosses e.val (abSide : Set V) ↔ e.val = 2 := by
    simpa only [mem_crossing_iff, he, true_and] using hmem
  exact hcross

/-- The arc r→u is a bridge of the actual unsuppressed ancestral graph. -/
theorem ancestral_has_bridge :
    (network.ancestralGraph (selectedTaxa : Set (Fin 5))).underlying.IsBridge
      (retainedArcEquiv ⟨2, by decide⟩) := by
  apply ((network.ancestralGraph (selectedTaxa : Set (Fin 5))).isBridge_iff _).mpr
  refine ⟨ancestralAbSide, ?_⟩
  intro e
  exact (ancestral_crossing_iff e).trans
    ⟨fun h ↦ Subtype.ext h, fun h ↦ congrArg Subtype.val h⟩

/-- On selected taxon labels, the ancestral cut side is precisely a,b. -/
theorem ancestral_side_taxa :
    (network.ancestralLeaf (selectedTaxa : Set (Fin 5))) ⁻¹' ancestralAbSide =
      {x : (selectedTaxa : Set (Fin 5)) | x.val = 1 ∨ x.val = 2} := by
  ext x
  change network.leaf x.val ∈ abSide ↔ x.val = 1 ∨ x.val = 2
  have h : ∀ x : Fin 5, x ∈ selectedTaxa →
      (network.leaf x ∈ abSide ↔ x = 1 ∨ x = 2) := by decide
  exact h x.val x.property

/-- The rooted ancestral network realizes the actual labelled cut ab|ce.
This remains a graph cut assertion; no suppression or reduced tree is assumed. -/
theorem ancestral_has_cut_split :
    (network.ancestralNetwork (selectedTaxa : Set (Fin 5)) selectedTaxa_nonempty
      root_reaches).HasCutSplit
      {x : (selectedTaxa : Set (Fin 5)) | x.val = 1 ∨ x.val = 2} := by
  refine ⟨retainedArcEquiv ⟨2, by decide⟩, ancestralAbSide, ?_, ancestral_side_taxa⟩
  intro e
  exact (ancestral_crossing_iff e).trans
    ⟨fun h ↦ Subtype.ext h, fun h ↦ congrArg Subtype.val h⟩

#print axioms full_singleton_cut_quartet_card
#print axioms restricted_two_two_singleton_cut
#print axioms acyclic
#print axioms pruned_has_bridge
#print axioms ancestralVertices_eq_retained
#print axioms ancestralArcs_eq_retained
#print axioms pruned_ancestral_isomorphism
#print axioms network_isPhylogenetic
#print axioms network_isBinary
#print axioms ancestralNetwork_isPhylogenetic
#print axioms ancestral_has_bridge
#print axioms ancestral_has_cut_split

end SunletCheck
