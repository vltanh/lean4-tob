module

public import AllmanEtAl2023.Bridges

/-!
# Allman, Baños, Mitchell, Rhodes 2023: Corollary 2

"To apply this to induced phylogenetic networks on subsets of taxa, observe that induced networks are obtained from subnetworks by suppressing degree-2 nodes. Under this operation, blobs pass to blobs, and cut edges to cut
edges. Thus we have the following." The sentence on suppression is `Bridges.isBlobQuartetOnInduced_iff`, from `AllmanEtAl2023.BlobsPass`, and the proof applies Lemma 2 to the subnetwork of the edges ancestral to `Y`. That
subnetwork is connected, as Lemma 2 needs (`isConnectedSubnetwork_ancestralArcs`).
-/

@[expose] public noncomputable section

open Phylogenetics Phylogenetics.RootedNetwork
open scoped Classical

namespace AllmanEtAl2023

variable {V E X : Type*} {N : RootedNetwork V E X}

/-- The nodes of the subnetwork of the edges ancestral to `Y` are the nodes ancestral to `Y`. -/
theorem mem_nodesOf_ancestralArcs (hN : N.IsPhylogenetic) {Y : Set X} {v : V} (hv : v ∈ N.ancestralVertices Y) :
    v ∈ nodesOf N.graph (N.ancestralArcs Y) := by
  obtain ⟨x, hx, hr⟩ := hv
  rcases Relation.ReflTransGen.cases_head hr with rfl | ⟨c, ⟨f, hfs, hft⟩, hc⟩
  · -- `v` is a taxon, with its edge
    have : Finite E := hN.finite_arcs
    obtain ⟨g, hg⟩ := (N.graph.indegree_eq_one_iff _).mp (hN.leaf_indegree x)
    refine ⟨g, ⟨x, hx, ?_⟩, Or.inr ((hg g).mpr rfl)⟩
    rw [(hg g).mpr rfl]
    exact .refl
  · exact ⟨f, ⟨x, hx, by rw [hft]; exact hc⟩, Or.inl hfs⟩

/-- A node of the subnetwork of the edges ancestral to `Y` is ancestral to `Y`. -/
theorem mem_ancestralVertices_of_mem_nodesOf {Y : Set X} {v : V} (hv : v ∈ nodesOf N.graph (N.ancestralArcs Y)) :
    v ∈ N.ancestralVertices Y := by
  obtain ⟨f, hf, rfl | rfl⟩ := hv
  · exact N.source_mem_ancestralVertices hf
  · exact hf

/-- **The subnetwork of the edges ancestral to `Y` is connected**, as Lemma 2 needs. -/
theorem isConnectedSubnetwork_ancestralArcs (hN : N.IsPhylogenetic) (Y : Set X) : IsConnectedSubnetwork N.graph (N.ancestralArcs Y) :=
  fun _ hu _ hv => walks_ancestral hN (mem_ancestralVertices_of_mem_nodesOf hu) (mem_ancestralVertices_of_mem_nodesOf hv)

/-- A rooted network is a labelled network in the sense of Lemma 2. -/
theorem isLabelledNetwork_of_isPhylogenetic (hN : N.IsPhylogenetic) : IsLabelledNetwork N.graph N.leaf where
  injective := hN.leaf_injective
  degree_one := nodeDegree_leaf hN

/-- **Corollary 2** (`a:cor:inducedB`). Let `𝒩⁺` be a rooted binary phylogenetic network on `X`, and `ℳ⁺` the induced network on
`Y ⊂ X`. Then any B-quartet on `ℳ⁺` is a B-quartet on `𝒩⁺`. -/
theorem corollary2 (hN : IsBinaryNetwork N) (Y : Set X) (hY : Y.Nontrivial) {Q : Finset X} (hQ : (Q : Set X) ⊆ Y)
    (h : IsBlobQuartetOnInduced hN Y hY Q) : IsBlobQuartet N Q := by
  have hP := hN.isPhylogenetic
  have : Finite E := hP.finite_arcs
  have h4 : Q.card = 4 := by
    have := h.1
    rwa [Finset.card_subtype, Finset.filter_true_of_mem (fun x hx => hQ hx)] at this
  -- blobs of the induced network pass to blobs of the subnetwork
  obtain ⟨v, hv, hd⟩ := (Bridges.isBlobQuartetOnInduced_iff hN Y hY hQ h4).mp h
  have hsub : IsDeterminedBy (restrict N.graph (N.ancestralArcs Y)) N.leaf (blobOf (restrict N.graph (N.ancestralArcs Y)) v) Q :=
    isDeterminedBy_blobOf_restrict_iff.mpr ⟨by omega, hd⟩
  -- Lemma 2
  obtain ⟨hdet, -⟩ := lemma2 (isLabelledNetwork_of_isPhylogenetic hP) (isConnectedSubnetwork_ancestralArcs hP Y)
    (fun y hy => mem_nodesOf_ancestralArcs hP (N.leaf_mem_ancestralVertices hy)) hQ (mem_nodesOf_ancestralArcs hP hv) hsub
  exact ⟨h4, _, hdet⟩

end AllmanEtAl2023
