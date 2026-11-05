module

public import Basic.FinNetwork
public import Phylogenetics.Tree.Detach

/-!
# TOB-QMC: a refinement of the tree of blobs need not be a display tree

TOB-QMC (v5, embedded lines 366-367): "Any tree displayed by a network refines the TOB (as all cut edges are preserved); however, a TOB refinement need not be a display tree of the network (Fig. 1C)." The supplement's line 206 says the same. The first half is
`Phylogenetics.RootedNetwork.treeOfBlobs_subset_displayedSides`. The second is `refinement_not_displayed`, on the binary level-1 network `ECToBlob.FinNetwork.Binary.net` of `src/ECToBlob/DisplayedTreeExample.lean`: a cut edge `de|abc`, and a 4-cycle through `a`, `b`, `c`. Its displayed trees have the cherries `ac` and
`bc`. The tree with the cherries `ab` and `de` refines the tree of blobs, and no parent choice displays it.
-/

@[expose] public noncomputable section

open Phylogenetics Phylogenetics.RootedNetwork Finset
open scoped Classical

namespace TOBQMC.DisplayedRefinement

open ECToBlob.FinNetwork ECToBlob.FinNetwork.Binary ECToBlob.FalseEdge

/-- The rooted tree `((d,e),(c,(a,b)))`. -/
def H₁ : Finset (Finset (Fin 5)) := {univ, {0}, {1}, {2}, {3}, {4}, {3, 4}, {0, 1}, {0, 1, 2}}

/-- The binary tree `T₁`, with cherries `ab` and `de`. -/
def T₁ : Finset (Finset (Fin 5)) := unroot H₁

theorem T₁_isBinaryTree : IsBinaryTree T₁ := ⟨H₁, by unfold IsHierarchy; decide, rfl, by decide⟩

/-- `T₁` refines the tree of blobs. -/
theorem treeOfBlobs_subset_T₁ : treeOfBlobs net ⊆ T₁ := by
  intro A hA
  rw [mem_treeOfBlobs_iff] at hA
  unfold T₁ H₁ unroot
  revert A
  decide

/-- **"A TOB refinement need not be a display tree of the network"** (`tob2025:refinement_not_displayed`): a binary tree refining the tree of blobs of a binary level-1 network, that no parent choice displays. -/
theorem refinement_not_displayed :
    IsBinaryTree T₁ ∧ treeOfBlobs net ⊆ T₁ ∧ ∀ c : net.ParentChoice, net.displayedSides c ≠ T₁ := by
  refine ⟨T₁_isBinaryTree, treeOfBlobs_subset_T₁, fun c hc => ?_⟩
  have hT : IsUnrootedTree T₁ := IsBinaryTree.isUnrootedTree T₁_isBinaryTree
  have h₀ : ({0, 1, 2, 3} : Finset (Fin 5)).card = 4 := by decide
  have hd₀ : Displays T₁ (quartetTree 0 1 2 3 h₀) := by
    refine ⟨{0, 1}, by unfold T₁ H₁ unroot; decide, ?_⟩
    rw [taxa_quartetTree]
    simp only [quartetTree]
    decide
  rcases uh_or_vh c with huh | hvh
  · have h₁ : ({0, 2, 1, 3} : Finset (Fin 5)).card = 4 := by decide
    have hd := displays_of_uh huh (Or.inl rfl) h₁
    rw [hc] at hd
    have heq := hT.displays_unique hd₀ hd (by rw [taxa_quartetTree, taxa_quartetTree]; decide)
    have hv := congrArg Subtype.val heq
    simp only [quartetTree] at hv
    exact absurd hv (by decide)
  · have h₁ : ({1, 2, 0, 3} : Finset (Fin 5)).card = 4 := by decide
    have hd := displays_of_vh hvh (Or.inl rfl) h₁
    rw [hc] at hd
    have heq := hT.displays_unique hd₀ hd (by rw [taxa_quartetTree, taxa_quartetTree]; decide)
    have hv := congrArg Subtype.val heq
    simp only [quartetTree] at hv
    exact absurd hv (by decide)

end TOBQMC.DisplayedRefinement
