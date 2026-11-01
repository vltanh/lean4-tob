module

public import Phylogenetics.NMSC.InducedParams
public import Phylogenetics.Network.TreeOfBlobs

/-!
# Allman, Baños, Mitchell, Rhodes 2023: Definitions 1 to 5

*The tree of blobs of a species network: identifiability under the coalescent*, J. Math. Biol. 86 (2023), 10.

Networks as the paper defines them, tied to the representation of the library:

* `IsBinaryNetwork` is Definition 1, in the paper's words; `isBinaryNetwork_iff`: it is
  `RootedNetwork.IsPhylogenetic` with `RootedNetwork.IsBinary`.
* Definition 2 is `G.underlying.IsBridge e`, of the library.
* `IsMetricParams` is Definition 3; `isMetric_iff`: `RootedNetwork.IsMetric` is that, with the convention that
  a tree edge has inheritance `1`, a coordinate that Definition 3 does not have.
* `IsLSA` is Definition 4 (Steel 2016), for any nonempty set of nodes; `existsUnique_isLSA`, `isLSA_image_leaf_iff`.
* `lsaPlus` is the LSA network `𝒩⊕` of Definition 5 (`mem_belowVertices_univ_iff`,
  `mem_belowArcs_univ_iff`: what is kept is what is not above the LSA). `semidirected` is the semidirected
  unrooted network `𝒩⁻` of Definition 5, of type `SemidirectedNetwork`, with its lengths `semidirectedMetric`.

Suppressing the root of `𝒩⊕` needs an edge out of the root that is not hybrid, because the paper's list of
suppressions has no case of two directed out-edges. `exists_isTreeArc_root` proves that this case does not arise.
-/

@[expose] public noncomputable section

open Phylogenetics Phylogenetics.RootedNetwork
open scoped Classical

namespace AllmanEtAl2023

variable {V E X : Type*}

/-! ### Definition 1 -/

section Definition1

variable (N : RootedNetwork V E X)

/-- A *tree node* of Definition 1: in-degree 1 and out-degree 2. -/
def IsTreeNode (v : V) : Prop := N.graph.indegree v = 1 ∧ N.graph.outdegree v = 2

/-- A *hybrid node* of Definition 1: in-degree 2 and out-degree 1. -/
def IsHybridNode (v : V) : Prop := N.graph.indegree v = 2 ∧ N.graph.outdegree v = 1

/-- A *hybrid edge* of Definition 1: its child node is hybrid. -/
def IsHybridEdge (e : E) : Prop := IsHybridNode N (N.graph.target e)

/-- A *tree edge* of Definition 1: its child node is a tree node or a leaf. -/
def IsTreeEdge (e : E) : Prop :=
  IsTreeNode N (N.graph.target e) ∨ ∃ x, N.leaf x = N.graph.target e

/-- **Definition 1** (`a:def::network`). A *topological rooted binary phylogenetic network* on the taxa `X`: a
connected directed acyclic graph whose nodes are the root, the leaves, the tree nodes and the hybrid nodes, with
a bijective leaf labelling. The leaf labelling `f : V_L → X` of the paper is the inverse of `N.leaf : X → V`, and
`V_L` is the range of `N.leaf`. The four kinds of node are disjoint by their degrees, and `E = E_H ⊔ E_T` follows
from the kinds of node (`isTreeArc_iff`, `isHybridArc_iff`). The paper takes graphs to be finite without saying so,
and allows parallel edges, its 2-cycles. -/
structure IsBinaryNetwork : Prop where
  finite_vertices : Finite V
  finite_arcs : Finite E
  connected : N.graph.IsConnected
  acyclic : N.graph.IsAcyclic
  /-- The root has in-degree 0. -/
  root_in : N.graph.indegree N.root = 0
  /-- The root has out-degree 2. -/
  root_out : N.graph.outdegree N.root = 2
  /-- A leaf has in-degree 1. -/
  leaf_in : ∀ x, N.graph.indegree (N.leaf x) = 1
  /-- A leaf has out-degree 0. -/
  leaf_out : ∀ x, N.graph.outdegree (N.leaf x) = 0
  leaf_injective : Function.Injective N.leaf
  /-- `V = {r} ⊔ V_L ⊔ V_H ⊔ V_T`. -/
  node_cases : ∀ v, v = N.root ∨ (∃ x, N.leaf x = v) ∨ IsTreeNode N v ∨ IsHybridNode N v

variable {N}

namespace IsBinaryNetwork

variable (hN : IsBinaryNetwork N)
include hN

theorem finite_taxa : Finite X :=
  have := hN.finite_vertices
  Finite.of_injective _ hN.leaf_injective

theorem one_le_indegree {v : V} (hv : v ≠ N.root) : 1 ≤ N.graph.indegree v := by
  rcases hN.node_cases v with rfl | ⟨x, rfl⟩ | h | h
  · exact absurd rfl hv
  · rw [hN.leaf_in]
  · rw [h.1]
  · rw [h.1]
    omega

/-- "Thus the root is above all other nodes." -/
theorem root_reaches (v : V) : N.graph.Reaches N.root v := by
  have := hN.finite_vertices
  have := hN.finite_arcs
  let r : V → V → Prop := fun a b => Relation.TransGen N.graph.Adj a b
  have : IsTrans V r := ⟨fun _ _ _ h h' => h.trans h'⟩
  have : Std.Irrefl r := ⟨fun a h => hN.acyclic a h⟩
  have hwf : WellFounded r := Finite.wellFounded_of_trans_of_irrefl r
  induction v using hwf.induction with
  | _ v ih =>
    by_cases hv : v = N.root
    · subst hv
      exact .refl
    · obtain ⟨e, he⟩ := (N.graph.one_le_indegree_iff v).mp (hN.one_le_indegree hv)
      have hadj : N.graph.Adj (N.graph.source e) v := ⟨e, rfl, he⟩
      exact (ih _ (.single hadj)).tail hadj

theorem isPhylogenetic : N.IsPhylogenetic := by
  refine ⟨hN.finite_vertices, hN.finite_arcs, hN.finite_taxa, hN.acyclic, hN.root_reaches, hN.root_in,
    fun v hv => hN.one_le_indegree hv, hN.leaf_injective, hN.leaf_in, fun v => ⟨fun h => ?_, ?_⟩⟩
  · rcases hN.node_cases v with rfl | hx | h' | h'
    · rw [hN.root_out] at h
      exact absurd h (by norm_num)
    · exact hx
    · rw [h'.2] at h
      exact absurd h (by norm_num)
    · rw [h'.2] at h
      exact absurd h (by norm_num)
  · rintro ⟨x, rfl⟩
    exact hN.leaf_out x

theorem isBinary : N.IsBinary := by
  refine ⟨hN.root_out, fun v hv h0 => ?_⟩
  rcases hN.node_cases v with rfl | ⟨x, rfl⟩ | h | h
  · exact absurd rfl hv
  · exact absurd (hN.leaf_out x) h0
  · rw [h.1, h.2]
  · rw [h.1, h.2]

end IsBinaryNetwork

/-- **Definition 1 is the library's two predicates.** -/
theorem isBinaryNetwork_iff : IsBinaryNetwork N ↔ N.IsPhylogenetic ∧ N.IsBinary := by
  refine ⟨fun h => ⟨h.isPhylogenetic, h.isBinary⟩, fun ⟨hP, hB⟩ => ?_⟩
  have := hP.finite_arcs
  refine ⟨hP.finite_vertices, hP.finite_arcs, N.graph_connected hP, hP.acyclic, hP.root_indegree, hB.1,
    hP.leaf_indegree, fun x => (hP.leaves _).mpr ⟨x, rfl⟩, hP.leaf_injective, fun v => ?_⟩
  by_cases hr : v = N.root
  · exact Or.inl hr
  refine Or.inr ?_
  by_cases h0 : N.graph.outdegree v = 0
  · exact Or.inl ((hP.leaves v).mp h0)
  have h3 := hB.2 v hr h0
  have h1 := hP.nonroot_indegree v hr
  refine Or.inr ?_
  by_cases h' : N.graph.indegree v = 1
  · exact Or.inl ⟨h', by omega⟩
  · exact Or.inr ⟨by omega, by omega⟩

/-- A *hybrid edge* of Definition 1 is a hybrid arc of the library. -/
theorem isHybridArc_iff (hN : IsBinaryNetwork N) (e : E) : N.IsHybridArc e ↔ IsHybridEdge N e := by
  have := hN.finite_arcs
  have hr : N.graph.target e ≠ N.root := fun h =>
    (N.graph.indegree_eq_zero_iff _).mp hN.root_in e h
  unfold IsHybridArc IsHybridEdge
  rcases hN.node_cases (N.graph.target e) with h | ⟨x, hx⟩ | h | h
  · exact absurd h hr
  · rw [← hx, hN.leaf_in, IsHybridNode, hN.leaf_in]
    simp
  · simp [IsHybridNode, h.1, h.2]
  · simp [IsHybridNode, h.1, h.2]

/-- A *tree edge* of Definition 1 is a tree arc of the library. -/
theorem isTreeArc_iff (hN : IsBinaryNetwork N) (e : E) : N.IsTreeArc e ↔ IsTreeEdge N e := by
  have := hN.finite_arcs
  have hr : N.graph.target e ≠ N.root := fun h =>
    (N.graph.indegree_eq_zero_iff _).mp hN.root_in e h
  unfold IsTreeArc IsTreeEdge
  rcases hN.node_cases (N.graph.target e) with h | hx | h | h
  · exact absurd h hr
  · obtain ⟨x, hx'⟩ := id hx
    simp only [← hx', hN.leaf_in, true_iff]
    exact Or.inr ⟨x, rfl⟩
  · simp [h.1, Or.inl h]
  · have hn : ¬ IsTreeNode N (N.graph.target e) := fun h' => by
      have := h.1.symm.trans h'.1
      omega
    have hl : ¬ ∃ x, N.leaf x = N.graph.target e := by
      rintro ⟨x, hx⟩
      have := h.2
      rw [← hx, hN.leaf_out] at this
      omega
    simp [h.1, hn, hl]

end Definition1

/-! ### Definition 2

**Definition 2** (`a:def:cutedge`). A *cut edge*: an edge whose deletion increases the number of connected components. This is
`G.underlying.IsBridge e`, Mathlib's bridge of the undirected graph, which keeps parallel edges apart;
`DirectedMultigraph.isBridge_iff_not_walks_delete` says that it is an edge whose deletion separates its ends. -/


/-! ### Definition 3 -/

section Definition3

variable (N : RootedNetwork V E X)

/-- **Definition 3** (`a:def:metric`). The numerical parameters of a *metric rooted binary phylogenetic network*:
a tree edge has positive length, a hybrid edge has non-negative length, and the hybridization parameters of two
hybrid edges with the same child are positive and sum to 1. -/
structure IsMetricParams (θ : MetricData E) : Prop where
  tree_length_pos : ∀ e, IsTreeEdge N e → 0 < θ.length e
  hybrid_length_nonneg : ∀ e, IsHybridEdge N e → 0 ≤ θ.length e
  hybrid_param : ∀ e e', e ≠ e' → IsHybridEdge N e → N.graph.target e = N.graph.target e' →
    0 < θ.inheritance e ∧ 0 < θ.inheritance e' ∧ θ.inheritance e + θ.inheritance e' = 1

variable {N}

/-- The two edges into a hybrid node. -/
theorem IsHybridNode.exists_parents {v : V} (hv : IsHybridNode N v) :
    ∃ e e', e ≠ e' ∧ ∀ f, N.graph.target f = v ↔ f = e ∨ f = e' := by
  obtain ⟨e, e', hne, h⟩ := Set.ncard_eq_two.mp hv.1
  refine ⟨e, e', hne, fun f => ?_⟩
  have := Set.ext_iff.mp h f
  simpa using this

/-- **`RootedNetwork.IsMetric` is Definition 3, with the convention that a tree edge has inheritance `1`.**
`MetricData` has an inheritance coordinate on every arc, and Definition 3 has one on hybrid edges only. -/
theorem isMetric_iff [Fintype E] (hN : IsBinaryNetwork N) (θ : MetricData E) :
    N.IsMetric θ ↔ IsMetricParams N θ ∧ ∀ e, IsTreeEdge N e → θ.inheritance e = 1 := by
  have hsum : ∀ {v : V} {e e' : E}, e ≠ e' → (∀ f, N.graph.target f = v ↔ f = e ∨ f = e') →
      (∑ f, if N.graph.target f = v then θ.inheritance f else 0) =
        θ.inheritance e + θ.inheritance e' := by
    intro v e e' hne h
    rw [← Finset.sum_filter, show (Finset.univ.filter fun f => N.graph.target f = v) = {e, e'} by
      ext f
      simp [h f], Finset.sum_pair hne]
  constructor
  · rintro ⟨h₁, h₂, h₃, h₄, h₅⟩
    refine ⟨⟨fun e he => h₁ e ((isTreeArc_iff hN e).mpr he),
      fun e he => h₂ e ((isHybridArc_iff hN e).mpr he), fun e e' hne he ht => ?_⟩,
      fun e he => h₃ e ((isTreeArc_iff hN e).mpr he)⟩
    have he' : IsHybridEdge N e' := by
      unfold IsHybridEdge at he ⊢
      rwa [← ht]
    refine ⟨h₄ e ((isHybridArc_iff hN e).mpr he), h₄ e' ((isHybridArc_iff hN e').mpr he'), ?_⟩
    obtain ⟨f, f', hff, hpar⟩ := IsHybridNode.exists_parents he
    have hef : (f = e ∧ f' = e') ∨ (f = e' ∧ f' = e) := by
      have h1 := (hpar e).mp rfl
      have h2 := (hpar e').mp ht.symm
      rcases h1 with rfl | rfl <;> rcases h2 with rfl | rfl <;> simp_all
    have hall : ∀ g, N.graph.target g = N.graph.target e ↔ g = e ∨ g = e' := by
      intro g
      rw [hpar g]
      rcases hef with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · rfl
      · exact or_comm
    have hhyb : 2 ≤ N.graph.indegree (N.graph.target e) := by
      rw [he.1]
    rw [← hsum hne hall]
    exact h₅ _ hhyb
  · rintro ⟨⟨h₁, h₂, h₃⟩, h₄⟩
    refine ⟨fun e he => h₁ e ((isTreeArc_iff hN e).mp he),
      fun e he => h₂ e ((isHybridArc_iff hN e).mp he), fun e he => h₄ e ((isTreeArc_iff hN e).mp he),
      fun e he => ?_, fun v hv => ?_⟩
    · have he' := (isHybridArc_iff hN e).mp he
      obtain ⟨f, f', hff, hpar⟩ := IsHybridNode.exists_parents he'
      have hf : IsHybridEdge N f := by
        unfold IsHybridEdge
        rw [(hpar f).mpr (Or.inl rfl)]
        exact he'
      obtain ⟨p₁, p₂, -⟩ := h₃ f f' hff hf ((hpar f).mpr (Or.inl rfl) |>.trans ((hpar f').mpr (Or.inr rfl)).symm)
      rcases (hpar e).mp rfl with rfl | rfl
      · exact p₁
      · exact p₂
    · have hh : IsHybridNode N v := by
        rcases hN.node_cases v with rfl | ⟨x, rfl⟩ | h | h
        · rw [hN.root_in] at hv
          omega
        · rw [hN.leaf_in] at hv
          omega
        · rw [h.1] at hv
          omega
        · exact h
      obtain ⟨f, f', hff, hpar⟩ := hh.exists_parents
      have hf : IsHybridEdge N f := by
        unfold IsHybridEdge
        rw [(hpar f).mpr (Or.inl rfl)]
        exact hh
      rw [hsum hff hpar]
      exact (h₃ f f' hff hf ((hpar f).mpr (Or.inl rfl) |>.trans ((hpar f').mpr (Or.inr rfl)).symm)).2.2

end Definition3

/-! ### Definition 4 -/

section Definition4

variable (N : RootedNetwork V E X)

/-- The set `D` of Definition 4: the nodes on every directed path from the root to any `z ∈ Z`. -/
def stableNodes (Z : Set V) : Set V := {u | ∀ z ∈ Z, ¬ N.HasPathAvoiding N.root z u}

/-- **Definition 4** (`a:def::LSA`; Steel 2016). `v` is the *lowest stable ancestor* of the nonempty set of nodes
`Z`: the node of `D` below every other node of `D`. It exists and is unique: `existsUnique_isLSA`. -/
def IsLSA (Z : Set V) (v : V) : Prop :=
  v ∈ stableNodes N Z ∧ ∀ u ∈ stableNodes N Z, u ≠ v → N.graph.Reaches u v

variable {N}

/-- "The unique node": the LSA of a nonempty set of nodes exists and is unique. -/
theorem existsUnique_isLSA (hN : N.IsPhylogenetic) {Z : Set V} (hZ : Z.Nonempty) :
    ∃! v, IsLSA N Z v := by
  have : Finite V := hN.finite_vertices
  let r : V → V → Prop := fun a b => Relation.TransGen N.graph.Adj b a
  have : IsTrans V r := ⟨fun _ _ _ h h' => h'.trans h⟩
  have : Std.Irrefl r := ⟨fun a h => hN.acyclic a h⟩
  have hwf : WellFounded r := Finite.wellFounded_of_trans_of_irrefl r
  have hne : (stableNodes N Z).Nonempty := ⟨N.root, fun _ _ h => h.1 rfl⟩
  obtain ⟨v, hv, hmin⟩ := hwf.has_min _ hne
  obtain ⟨z, hz⟩ := hZ
  have hcomp : ∀ w ∈ stableNodes N Z, N.graph.Reaches w v := fun w hw => by
    rcases reaches_or_reaches_of_not_hasPathAvoiding (hN.root_reaches z) (hw z hz) (hv z hz) with h | h
    · exact h
    · rcases Relation.reflTransGen_iff_eq_or_transGen.mp h with rfl | ht
      · exact .refl
      · exact absurd ht (hmin w hw)
  refine ⟨v, ⟨hv, fun w hw _ => hcomp w hw⟩, fun w hw => ?_⟩
  by_contra hne
  exact hne (eq_of_reaches_of_reaches hN.acyclic (hcomp w hw.1) (hw.2 v hv (Ne.symm hne)))

/-- **Definition 4 on a set of taxa is the library's least stable ancestor.** -/
theorem isLSA_image_leaf_iff {Y : Set X} {v : V} :
    IsLSA N (N.leaf '' Y) v ↔ N.IsLeastStableAncestor Y v := by
  have hst : ∀ u, u ∈ stableNodes N (N.leaf '' Y) ↔ N.IsStableAncestor Y u := fun u => by
    simp [stableNodes, IsStableAncestor]
  constructor
  · rintro ⟨h₁, h₂⟩
    refine ⟨(hst v).mp h₁, fun w hw => ?_⟩
    by_cases hwv : w = v
    · rw [hwv]
      exact .refl
    · exact h₂ w ((hst w).mpr hw) hwv
  · rintro ⟨h₁, h₂⟩
    exact ⟨(hst v).mpr h₁, fun w hw _ => h₂ w ((hst w).mp hw)⟩

end Definition4

/-! ### Definition 5: the LSA network -/

section LSANetwork

variable {N : RootedNetwork V E X}

/-- The same network, with its taxa renamed. -/
def renameTaxa {X' : Type*} (M : RootedNetwork V E X) (f : X' ≃ X) : RootedNetwork V E X' where
  graph := M.graph
  root := M.root
  leaf x := M.leaf (f x)

theorem renameTaxa_isPhylogenetic {X' : Type*} {M : RootedNetwork V E X} (hM : M.IsPhylogenetic)
    (f : X' ≃ X) : (renameTaxa M f).IsPhylogenetic where
  finite_vertices := hM.finite_vertices
  finite_arcs := hM.finite_arcs
  finite_taxa :=
    have := hM.finite_taxa
    Finite.of_equiv _ f.symm
  acyclic := hM.acyclic
  root_reaches := hM.root_reaches
  root_indegree := hM.root_indegree
  nonroot_indegree := hM.nonroot_indegree
  leaf_injective := hM.leaf_injective.comp f.injective
  leaf_indegree x := hM.leaf_indegree (f x)
  leaves v := by
    refine (hM.leaves v).trans ⟨?_, ?_⟩
    · rintro ⟨x, hx⟩
      exact ⟨f.symm x, by simpa [renameTaxa] using hx⟩
    · rintro ⟨x, hx⟩
      exact ⟨f x, hx⟩

/-- `LSA(𝒩⁺)`: the LSA of the leaves (Definition 4). -/
def lsaNode (hN : IsBinaryNetwork N) (hX : Nontrivial X) : V :=
  lsa hN.isPhylogenetic Set.univ Set.univ_nonempty

/-- `lsaNode` is the LSA of Definition 4 of the leaves. -/
theorem isLSA_lsaNode (hN : IsBinaryNetwork N) (hX : Nontrivial X) :
    IsLSA N (Set.range N.leaf) (lsaNode hN hX) := by
  rw [← Set.image_univ, isLSA_image_leaf_iff]
  exact lsa_spec hN.isPhylogenetic Set.univ Set.univ_nonempty

/-- **Definition 5, part 1** (`a:def::undirected`). The *LSA network* `𝒩⊕`: "deleting all edges and nodes above
`LSA(𝒩⁺)`, and designating `LSA(𝒩⁺)` as the root node". The library's `lsaNetwork` on all the taxa, on the
taxa `X` itself. `mem_belowVertices_univ_iff` and `mem_belowArcs_univ_iff` say that it keeps what is not above the
LSA. -/
def lsaPlus (hN : IsBinaryNetwork N) (hX : Nontrivial X) :
    RootedNetwork (N.belowVertices (lsaNode hN hX) Set.univ) (N.belowArcs (lsaNode hN hX) Set.univ) X :=
  renameTaxa (lsaNetwork hN.isPhylogenetic Set.univ Set.univ_nonempty) (Equiv.Set.univ X).symm

theorem lsaPlus_isPhylogenetic (hN : IsBinaryNetwork N) (hX : Nontrivial X) :
    (lsaPlus hN hX).IsPhylogenetic :=
  renameTaxa_isPhylogenetic (lsaNetwork_isPhylogenetic hN.isPhylogenetic Set.nontrivial_univ) _

/-- Every node is above a taxon, so what lies below a node is ancestral to the taxa. -/
theorem mem_ancestralVertices_univ (hN : IsBinaryNetwork N) (v : V) :
    v ∈ N.ancestralVertices Set.univ := by
  obtain ⟨x, hx⟩ := exists_reaches_leaf hN.isPhylogenetic v
  exact ⟨x, Set.mem_univ x, hx⟩

/-- A node is kept in `𝒩⊕` exactly when it is not strictly above the LSA. -/
theorem mem_belowVertices_univ_iff (hN : IsBinaryNetwork N) (hX : Nontrivial X) (v : V) :
    v ∈ N.belowVertices (lsaNode hN hX) Set.univ ↔
      ¬ (N.graph.Reaches v (lsaNode hN hX) ∧ v ≠ lsaNode hN hX) := by
  have hP := hN.isPhylogenetic
  have hst := (lsa_spec hP Set.univ Set.univ_nonempty).1
  constructor
  · rintro ⟨hv, -⟩ ⟨h, hne⟩
    exact hne (eq_of_reaches_of_reaches hP.acyclic h hv)
  · intro h
    refine ⟨?_, mem_ancestralVertices_univ hN v⟩
    obtain ⟨x, hx⟩ := exists_reaches_leaf hP v
    by_cases hv : N.HasPathAvoiding N.root v (lsaNode hN hX)
    · -- a path to `v` avoids the LSA, so the path on to `x` must meet it after `v`
      by_contra hnr
      have hab : ¬ N.HasPathAvoiding v (N.leaf x) (lsaNode hN hX) := fun hp =>
        hst x (Set.mem_univ x) ⟨hv.1, hp.2.1, hv.2.2.trans hp.2.2⟩
      obtain ⟨h₁, -⟩ := reaches_of_not_hasPathAvoiding hx hab
      exact h ⟨h₁, fun hEq => hnr (hEq ▸ .refl)⟩
    · exact (reaches_of_not_hasPathAvoiding (hP.root_reaches v) hv).2

/-- An edge is kept in `𝒩⊕` exactly when it is not above the LSA. -/
theorem mem_belowArcs_univ_iff (hN : IsBinaryNetwork N) (hX : Nontrivial X) (e : E) :
    e ∈ N.belowArcs (lsaNode hN hX) Set.univ ↔ ¬ N.graph.Reaches (N.graph.target e) (lsaNode hN hX) := by
  have hP := hN.isPhylogenetic
  have hst := (lsa_spec hP Set.univ Set.univ_nonempty).1
  constructor
  · rintro ⟨hs, -⟩ h
    exact not_reaches_target_source hP.acyclic e (h.trans hs)
  · intro h
    refine ⟨?_, mem_ancestralVertices_univ hN _⟩
    by_contra hnr
    have hv : N.HasPathAvoiding N.root (N.graph.source e) (lsaNode hN hX) := by
      by_contra hv
      exact hnr (reaches_of_not_hasPathAvoiding (hP.root_reaches _) hv).2
    obtain ⟨x, hx⟩ := exists_reaches_leaf hP (N.graph.target e)
    have hab : N.HasPathAvoiding (N.graph.target e) (N.leaf x) (lsaNode hN hX) := by
      by_contra hab
      exact h (reaches_of_not_hasPathAvoiding hx hab).1
    refine hst x (Set.mem_univ x) ⟨hv.1, hab.2.1, hv.2.2.trans (Relation.ReflTransGen.head
      ⟨⟨e, rfl, rfl⟩, hv.2.1, hab.1⟩ hab.2.2)⟩

end LSANetwork

/-! ### Definition 5: the semidirected unrooted network -/

/-- A *semidirected unrooted network*. Every edge has two ends, given in some order. For the edges with
`IsDirected`, the hybrid edges, that order is the direction retained; for the others it has no meaning: walks,
cut edges and blobs of `graph` forget it. -/
structure SemidirectedNetwork (V E X : Type*) where
  graph : DirectedMultigraph V E
  IsDirected : E → Prop
  leaf : X → V

section Semidirected

variable {N : RootedNetwork V E X}

theorem target_ne_root {M : RootedNetwork V E X} (hM : M.IsPhylogenetic) (e : E) :
    M.graph.target e ≠ M.root :=
  have := hM.finite_arcs
  (M.graph.indegree_eq_zero_iff _).mp hM.root_indegree e

/-- Suppressing the root of a rooted network, undirecting its tree edges and retaining the directions of
its hybrid edges. The root's edge `e₀` and its other edge become one edge, from the child of `e₀` to the child of
the other edge. If `e₀` is a tree edge, this is the paper's "single edge with the out-edge direction" when the
other edge is hybrid; if both are tree edges, the order has no meaning. -/
def unrootAt (M : RootedNetwork V E X) (hM : M.IsPhylogenetic) (e₀ : E) :
    SemidirectedNetwork {v // v ≠ M.root} {e // e ≠ e₀} X where
  graph :=
    { source := fun e =>
        if h : M.graph.source e.1 = M.root then ⟨M.graph.target e₀, target_ne_root hM e₀⟩
        else ⟨M.graph.source e.1, h⟩
      target := fun e => ⟨M.graph.target e.1, target_ne_root hM e.1⟩ }
  IsDirected e := M.IsHybridArc e.1
  leaf x := ⟨M.leaf x, M.leaf_ne_root hM x⟩

/-- **The two out-edges of the root of `𝒩⊕` are not both hybrid**, so the paper's list of suppressions covers the
root. A highest node other than the root has all its parents at the root, so if it were hybrid, it would take both
edges of the root, and would be a stable ancestor below the LSA. -/
theorem exists_isTreeArc_root {M : RootedNetwork V E X} (hM : M.IsPhylogenetic) [Nonempty X]
    (hout : M.graph.outdegree M.root = 2)
    (hlsa : ∀ w, M.IsStableAncestor Set.univ w → M.graph.Reaches w M.root) :
    ∃ e, M.graph.source e = M.root ∧ M.IsTreeArc e := by
  have := hM.finite_vertices
  have := hM.finite_arcs
  let r : V → V → Prop := fun a b => Relation.TransGen M.graph.Adj a b
  have : IsTrans V r := ⟨fun _ _ _ h h' => h.trans h'⟩
  have : Std.Irrefl r := ⟨fun a h => hM.acyclic a h⟩
  have hwf : WellFounded r := Finite.wellFounded_of_trans_of_irrefl r
  obtain ⟨x₀⟩ := ‹Nonempty X›
  obtain ⟨w, hw, hmin⟩ := hwf.has_min {v | v ≠ M.root} ⟨M.leaf x₀, M.leaf_ne_root hM x₀⟩
  have hparent : ∀ f, M.graph.target f = w → M.graph.source f = M.root := fun f hf => by
    by_contra hs
    exact hmin _ hs (.single ⟨f, rfl, hf⟩)
  obtain ⟨e, he⟩ := (M.graph.one_le_indegree_iff w).mp (hM.nonroot_indegree w hw)
  by_cases h1 : M.graph.indegree w = 1
  · exact ⟨e, hparent e he, by unfold IsTreeArc; rwa [he]⟩
  exfalso
  have h2 : 2 ≤ M.graph.indegree w := by
    have := hM.nonroot_indegree w hw
    omega
  have hsub : {f | M.graph.target f = w} ⊆ {f | M.graph.source f = M.root} := fun f hf => hparent f hf
  have heq : {f | M.graph.target f = w} = {f | M.graph.source f = M.root} := by
    refine Set.eq_of_subset_of_ncard_le hsub ?_ (Set.toFinite _)
    change M.graph.outdegree M.root ≤ M.graph.indegree w
    omega
  have hall : ∀ f, M.graph.source f = M.root → M.graph.target f = w := fun f hf =>
    (Set.ext_iff.mp heq f).mpr hf
  have hst : M.IsStableAncestor Set.univ w := by
    rintro x - ⟨-, -, hp⟩
    rcases Relation.ReflTransGen.cases_head hp with h | ⟨a, ⟨⟨f, hfs, hft⟩, -, ha⟩, -⟩
    · exact M.leaf_ne_root hM x h.symm
    · exact ha (hft ▸ hall f hfs)
  exact hw (eq_of_reaches_of_reaches hM.acyclic (hlsa w hst) (hM.root_reaches w))

/-- A stable ancestor of `𝒩⊕` is one of `𝒩⁺`: so the root of `𝒩⊕` is its own LSA. -/
theorem lsaPlus_reaches_root_of_isStableAncestor (hN : IsBinaryNetwork N) (hX : Nontrivial X)
    {w : N.belowVertices (lsaNode hN hX) Set.univ}
    (hw : (lsaPlus hN hX).IsStableAncestor Set.univ w) :
    (lsaPlus hN hX).graph.Reaches w (lsaPlus hN hX).root := by
  have hP := hN.isPhylogenetic
  obtain ⟨hst, hleast⟩ := lsa_spec hP Set.univ Set.univ_nonempty
  by_cases hwl : w.1 = lsaNode hN hX
  · have : w = (lsaPlus hN hX).root := Subtype.ext hwl
    rw [this]
    exact .refl
  exfalso
  -- a path of `𝒩⁺` below the LSA avoiding `w` is a path of `𝒩⊕`
  have hlift : ∀ t, Relation.ReflTransGen (fun a b => N.graph.Adj a b ∧ a ≠ w.1 ∧ b ≠ w.1)
      (lsaNode hN hX) t → ∀ ht : t ∈ N.belowVertices (lsaNode hN hX) Set.univ,
      Relation.ReflTransGen (fun a b => (lsaPlus hN hX).graph.Adj a b ∧ a ≠ w ∧ b ≠ w)
        (lsaPlus hN hX).root ⟨t, ht⟩ := by
    intro t ht
    induction ht with
    | refl => exact fun _ => .refl
    | @tail a b hab hs ih =>
      intro hb
      have ha : a ∈ N.belowVertices (lsaNode hN hX) Set.univ :=
        ⟨Relation.ReflTransGen.mono (fun _ _ h => h.1) _ _ hab, mem_ancestralVertices_univ hN a⟩
      obtain ⟨⟨f, hfs, hft⟩, hsa, hsb⟩ := hs
      refine (ih ha).tail ⟨⟨⟨f, hfs ▸ ha.1, mem_ancestralVertices_univ hN _⟩, Subtype.ext hfs, Subtype.ext hft⟩,
        fun h => hsa (congrArg Subtype.val h), fun h => hsb (congrArg Subtype.val h)⟩
  have hreach : ∀ x, ¬ N.HasPathAvoiding N.root (N.leaf x) w.1 := by
    intro x hp
    have hs := hp.suffix_of_not_hasPathAvoiding (hst x (Set.mem_univ x))
    have hxb : N.leaf x ∈ N.belowVertices (lsaNode hN hX) Set.univ :=
      ⟨hst.reaches_leaf hP (Set.mem_univ x), mem_ancestralVertices_univ hN _⟩
    refine hw x (Set.mem_univ x) ⟨fun h => hwl (congrArg Subtype.val h).symm,
      fun h => hs.2.1 (congrArg Subtype.val h), ?_⟩
    exact hlift _ hs.2.2 hxb
  exact hwl (eq_of_reaches_of_reaches hP.acyclic (hleast w.1 fun x _ => hreach x) w.2.1)

/-- The root of `𝒩⊕` has out-degree 2. -/
theorem lsaPlus_outdegree_root (hN : IsBinaryNetwork N) (hX : Nontrivial X) :
    (lsaPlus hN hX).graph.outdegree (lsaPlus hN hX).root = 2 :=
  lsaNetwork_outdegree_root hN.isPhylogenetic hN.isBinary Set.nontrivial_univ

/-- The edge out of the root of `𝒩⊕` chosen to be merged into the other: a tree edge. -/
def rootTreeArc (hN : IsBinaryNetwork N) (hX : Nontrivial X) :
    N.belowArcs (lsaNode hN hX) Set.univ :=
  Classical.choose (exists_isTreeArc_root (M := lsaPlus hN hX) (lsaPlus_isPhylogenetic hN hX)
    (lsaPlus_outdegree_root hN hX) fun _ hw => lsaPlus_reaches_root_of_isStableAncestor hN hX hw)

theorem rootTreeArc_spec (hN : IsBinaryNetwork N) (hX : Nontrivial X) :
    (lsaPlus hN hX).graph.source (rootTreeArc hN hX) = (lsaPlus hN hX).root ∧
      (lsaPlus hN hX).IsTreeArc (rootTreeArc hN hX) :=
  Classical.choose_spec (exists_isTreeArc_root (M := lsaPlus hN hX) (lsaPlus_isPhylogenetic hN hX)
    (lsaPlus_outdegree_root hN hX) fun _ hw => lsaPlus_reaches_root_of_isStableAncestor hN hX hw)

/-- The nodes of `𝒩⁻`. -/
abbrev SemiV (hN : IsBinaryNetwork N) (hX : Nontrivial X) :=
  {v : N.belowVertices (lsaNode hN hX) Set.univ // v ≠ (lsaPlus hN hX).root}

/-- The edges of `𝒩⁻`. -/
abbrev SemiE (hN : IsBinaryNetwork N) (hX : Nontrivial X) :=
  {e : N.belowArcs (lsaNode hN hX) Set.univ // e ≠ rootTreeArc hN hX}

/-- **Definition 5, part 2** (`a:def::undirected`). The *semidirected unrooted network* `𝒩⁻`: "the unrooted
network obtained from the LSA network `𝒩⊕` by undirecting all tree edges and suppressing the root, but retaining
directions of hybrid edges". -/
def semidirected (hN : IsBinaryNetwork N) (hX : Nontrivial X) :
    SemidirectedNetwork (SemiV hN hX) (SemiE hN hX) X :=
  unrootAt (lsaPlus hN hX) (lsaPlus_isPhylogenetic hN hX) (rootTreeArc hN hX)

/-- The lengths and hybridization parameters of `𝒩⁻`: "for a metric graph the new edge is assigned a length equal
to the sum of lengths of the two replaced. If the out-edge was hybrid, the new edge is also hybrid and retains the
hybridization parameter". The other edge of the root keeps its parameter, and the chosen one is a tree edge. -/
def semidirectedMetric (hN : IsBinaryNetwork N) (hX : Nontrivial X) (θ : MetricData E) :
    MetricData (SemiE hN hX) where
  length e :=
    if (lsaPlus hN hX).graph.source e.1 = (lsaPlus hN hX).root then
      θ.length e.1.1 + θ.length (rootTreeArc hN hX).1
    else θ.length e.1.1
  inheritance e := θ.inheritance e.1.1

end Semidirected

end AllmanEtAl2023
