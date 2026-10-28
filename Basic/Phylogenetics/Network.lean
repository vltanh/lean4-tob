module

public import Basic.Combinatorics.MultigraphBlobs
public import Mathlib.Basic.Real.Basic

/-!
# Rooted phylogenetic multigraph data

Graph, root and taxon labels are data. Finiteness and the defining network laws
are a separate proposition. In particular, this representation permits parallel
arcs, unary tree vertices, multifurcations and hybrid vertices of higher degree.
It does not impose a level bound or a gene-tree distribution.

The predicates for cuts below concern the original graph. They are not a
definition of its reduced tree of blobs: contraction and suppression require
separate constructions and representation theorems.
-/

@[expose] public section

namespace Phylogenetics

structure RootedNetwork (V E X : Type*) where
  graph : DirectedMultigraph V E
  root : V
  leaf : X → V

namespace RootedNetwork

variable {V E X : Type*} (N : RootedNetwork V E X)

/-- Defining laws of a finite rooted network. A leaf has precisely one incoming
arc and no outgoing arc. Internal vertices of degree two are allowed. -/
structure IsPhylogenetic : Prop where
  finite_vertices : Finite V
  finite_arcs : Finite E
  finite_taxa : Finite X
  acyclic : N.graph.IsAcyclic
  root_reaches : ∀ v, N.graph.Reaches N.root v
  root_indegree : N.graph.indegree N.root = 0
  nonroot_indegree : ∀ v, v ≠ N.root → 1 ≤ N.graph.indegree v
  leaf_injective : Function.Injective N.leaf
  leaf_indegree : ∀ x, N.graph.indegree (N.leaf x) = 1
  leaves : ∀ v, N.graph.outdegree v = 0 ↔ ∃ x, N.leaf x = v

/-- A tree arc enters a vertex with one incoming arc. -/
def IsTreeArc (e : E) : Prop := N.graph.indegree (N.graph.target e) = 1

/-- A hybrid arc enters a vertex with at least two incoming arcs. -/
def IsHybridArc (e : E) : Prop := 2 ≤ N.graph.indegree (N.graph.target e)

/-- Binary is a degree condition, separate from network validity. -/
def IsBinary : Prop :=
  N.graph.outdegree N.root = 2 ∧
    ∀ v, v ≠ N.root → N.graph.outdegree v ≠ 0 →
      N.graph.indegree v + N.graph.outdegree v = 3

/-- A directed path avoiding a vertex, including at its endpoints. -/
def HasPathAvoiding (u v w : V) : Prop :=
  u ≠ w ∧ v ≠ w ∧
    Relation.ReflTransGen (fun a b => N.graph.Adj a b ∧ a ≠ w ∧ b ≠ w) u v

/-- Every root-to-taxon path for the specified taxa passes through this vertex. -/
def IsStableAncestor (Y : Set X) (v : V) : Prop :=
  ∀ x ∈ Y, ¬ N.HasPathAvoiding N.root (N.leaf x) v

/-- A stable ancestor below every other stable ancestor in the directed order. -/
def IsLeastStableAncestor (Y : Set X) (v : V) : Prop :=
  N.IsStableAncestor Y v ∧
    ∀ w, N.IsStableAncestor Y w → N.graph.Reaches w v

/-- The root is the least stable ancestor of all labelled taxa. -/
def IsLSANetwork : Prop := N.IsLeastStableAncestor Set.univ N.root

/-- A taxon bipartition realized by a singleton graph cut. Orientation of the
split is immaterial, as `hasCutSplit_compl` verifies. -/
def HasCutSplit (A : Set X) : Prop :=
  ∃ (e : E) (S : Set V),
    (∀ f, N.graph.Crosses f S ↔ f = e) ∧ N.leaf ⁻¹' S = A

theorem root_isStableAncestor (Y : Set X) : N.IsStableAncestor Y N.root := by
  intro x _ h
  exact h.1 rfl

theorem leaf_ne_root (hN : N.IsPhylogenetic) (x : X) : N.leaf x ≠ N.root := by
  intro h
  have hi := hN.leaf_indegree x
  rw [h, hN.root_indegree] at hi
  exact Nat.zero_ne_one hi

theorem hasCutSplit_compl (A : Set X) : N.HasCutSplit Aᶜ ↔ N.HasCutSplit A := by
  have flip : ∀ B, N.HasCutSplit B → N.HasCutSplit Bᶜ := by
    rintro B ⟨e, S, hS, hB⟩
    refine ⟨e, Sᶜ, ?_, ?_⟩
    · intro f
      have hc : N.graph.Crosses f Sᶜ ↔ N.graph.Crosses f S := by
        simp only [DirectedMultigraph.Crosses, Set.mem_compl_iff, not_not]
        tauto
      exact hc.trans (hS f)
    · rw [Set.preimage_compl, hB]
  exact ⟨fun h => by simpa only [compl_compl] using flip Aᶜ h, flip A⟩

/-- A cut split always has an actual bridge arc in the original multigraph. -/
theorem exists_bridge_of_hasCutSplit {A : Set X} (h : N.HasCutSplit A) :
    ∃ e, N.graph.underlying.IsBridge e := by
  obtain ⟨e, S, he, _⟩ := h
  exact ⟨e, (N.graph.isBridge_iff e).mpr ⟨S, he⟩⟩

/-- Root reachability supplies the connectedness required of the underlying
undirected graph. The root also excludes the empty-vertex case. -/
theorem graph_connected (hN : N.IsPhylogenetic) : N.graph.IsConnected := by
  intro u v
  exact (N.graph.walks_symm (N.graph.walks_of_reaches (hN.root_reaches u))).trans
    (N.graph.walks_of_reaches (hN.root_reaches v))

/-- Root and taxon labels transported to the bridge-component quotient.
This is unsuppressed graph data, not a claim that the output already satisfies
every rooted-network degree convention. -/
def bridgeQuotientData : RootedNetwork N.graph.BlobVertex N.graph.BridgeArc X where
  graph := N.graph.bridgeQuotient
  root := Quotient.mk N.graph.blobSetoid N.root
  leaf x := Quotient.mk N.graph.blobSetoid (N.leaf x)

/-- The unsuppressed bridge contraction preserves every labelled cut split. -/
theorem hasCutSplit_iff_bridgeQuotient (A : Set X) :
    N.HasCutSplit A ↔ N.bridgeQuotientData.HasCutSplit A :=
  N.graph.labelled_cut_iff_quotient N.leaf A

/-- Numerical data; their ranges and normalizations are separate laws. -/
structure MetricData where
  length : E → ℝ
  inheritance : E → ℝ

/-- Nonnegative hybrid lengths are allowed, including zero. Inheritance weights
are positive on hybrid arcs and sum to one at each hybrid vertex. Tree-arc
weights are canonically one; those entries are not additional parameters. -/
def IsMetric [Fintype E] (m : MetricData (E := E)) : Prop := by
  classical
  exact
  (∀ e, N.IsTreeArc e → 0 < m.length e) ∧
  (∀ e, N.IsHybridArc e → 0 ≤ m.length e) ∧
  (∀ e, N.IsTreeArc e → m.inheritance e = 1) ∧
  (∀ e, N.IsHybridArc e → 0 < m.inheritance e) ∧
  ∀ v, 2 ≤ N.graph.indegree v →
    ∑ e, (if N.graph.target e = v then m.inheritance e else 0) = 1

end RootedNetwork
end Phylogenetics
