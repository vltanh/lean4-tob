module

public import Basic.Phylogenetics.NetworkCuts
public import Basic.Phylogenetics.TreeSplits
public import External.HuberEtAl2025.Theorem51

/-!
# TOB-QMC §4.3: false positives in a refinement, with a linear number of tests, for level-1 networks

Lemma 2, Lemma 4, Corollary 1, Definition 2, Theorem 2 and the 3-fix-1-alter search.
A taxon set's oracle answer *treelike* is `IsTreelike N Y`: the restriction has a cut edge with a
non-trivial split, equivalently no 4-blob.
-/

@[expose] public noncomputable section

open Phylogenetics Phylogenetics.RootedNetwork Finset
open scoped Classical

namespace TOBQMC

variable {V E X : Type*} [Fintype X] [DecidableEq X] {N : RootedNetwork V E X}

/-- **Lemma 2** (`tob2025:lemma2`, the forward direction of Huber et al. Theorem 5.1). If `A|B` is
induced by a cut edge, then for all pairwise distinct `a₁, a₂ ∈ A`, `b₁, b₂ ∈ B`, the bipartition
`a₁, a₂|b₁, b₂` is induced by a cut edge of the network restricted to these taxa. -/
theorem lemma2 (hN : N.IsPhylogenetic) {A : Finset X} (hA : N.HasCutSplit (A : Set X))
    {a₁ a₂ b₁ b₂ : X} (ha₁ : a₁ ∈ A) (ha₂ : a₂ ∈ A) (hb₁ : b₁ ∉ A) (hb₂ : b₂ ∉ A) :
    N.HasCutSplitOn (({a₁, a₂, b₁, b₂} : Finset X) : Set X) (({a₁, a₂} : Finset X) : Set X) :=
  External.HuberEtAl2025.theorem5_1_forward hN hA ha₁ ha₂ hb₁ hb₂

/-- Two taxa are in the same block of the partition `Part` at the blob of `v`: they remain
joined when the blob is deleted. -/
def SameBlock (N : RootedNetwork V E X) (v : V) (x y : X) : Prop :=
  Relation.ReflTransGen (fun a b => ¬ SameBlob N v a ∧ ¬ SameBlob N v b ∧
    ∃ e, (N.graph.source e = a ∧ N.graph.target e = b) ∨ (N.graph.source e = b ∧ N.graph.target e = a))
    (N.leaf x) (N.leaf y)

/-- The edge with side `A` of a refinement refines the blob of `v`: each block at the blob is on one
side of the edge. -/
def RefinesBlob (N : RootedNetwork V E X) (A : Finset X) (v : V) : Prop :=
  ∀ x y, SameBlock N v x y → (x ∈ A ↔ y ∈ A)

variable [Fintype V] [Fintype E]

/-- An edge of a refinement of the tree of blobs of a binary network that is not in the tree of blobs
refines a non-trivial blob, with a reticulation vertex (the premise of Lemma 4). -/
theorem exists_blob_of_false_positive (hN : N.IsPhylogenetic) (hBin : N.IsBinary)
    {B : Finset (Finset X)} (hB : IsUnrootedTree B) (hTB : treeOfBlobs N ⊆ B) {A : Finset X}
    (hA : A ∈ internalSides B) (hAT : A ∉ treeOfBlobs N) :
    ∃ v h, RefinesBlob N A v ∧ SameBlob N v h ∧ 2 ≤ N.graph.indegree h := by
  sorry

/-- **Lemma 4** (`tob2025:lemma4`). Let `N` be binary and level-1, `B` a refinement of its tree of blobs,
`A` the side of an edge of `B` not in the tree of blobs, refining the non-trivial blob of `v`, whose
reticulation vertex is `h`. For a four-taxon set `Y` around the edge, the restriction of the network to
`Y` has a 4-blob if and only if the taxa of `Y` lie in distinct blocks at the blob and exactly one
of them descends from `h`. -/
theorem lemma4 (hN : N.IsPhylogenetic) (hBin : N.IsBinary) (hLevel : IsLevelOne N)
    {B : Finset (Finset X)} (hB : IsUnrootedTree B) (hTB : treeOfBlobs N ⊆ B) {A : Finset X}
    (hA : A ∈ internalSides B) (hAT : A ∉ treeOfBlobs N)
    {v h : V} (hv : RefinesBlob N A v) (hh : SameBlob N v h) (hh₂ : 2 ≤ N.graph.indegree h)
    {Y : Finset X} (hY : Y.card = 4) (hYA : (A ∩ Y).card = 2) :
    ¬ IsTreelike N Y ↔
      (∀ x ∈ Y, ∀ y ∈ Y, x ≠ y → ¬ SameBlock N v x y) ∧
        ∃! x, x ∈ Y ∧ N.graph.Reaches h (N.leaf x) := by
  sorry

/-- **Corollary 1** (`tob2025:corollary1`). For a binary level-1 network and a binary refinement `B` of
its tree of blobs, an edge of `B` is in the tree of blobs exactly when the oracle answers treelike on
all four-taxon subsets around it. -/
theorem corollary1 (hN : N.IsPhylogenetic) (hBin : N.IsBinary) (hLevel : IsLevelOne N)
    {B : Finset (Finset X)} (hB : IsBinaryTree B) (hTB : treeOfBlobs N ⊆ B) {A : Finset X}
    (hA : A ∈ internalSides B) :
    A ∈ treeOfBlobs N ↔ ∀ Y : Finset X, Y.card = 4 → (A ∩ Y).card = 2 → IsTreelike N Y := by
  sorry

/-- **Theorem 2** (`tob2025:theorem2`). For a binary level-1 network with tree of blobs `T_N`, and a
refinement `B` of `T_N`: applying the oracle to a disjoint cover of four-taxon subsets around each
edge of `B`, labelling an edge a false positive if the oracle answers non-treelike on one of them, and
contracting the false positives, returns `T_N`. -/
theorem theorem2 (hN : N.IsPhylogenetic) (hBin : N.IsBinary) (hLevel : IsLevelOne N)
    {B : Finset (Finset X)} (hB : IsUnrootedTree B) (hTB : treeOfBlobs N ⊆ B)
    (Q : Finset X → Finset (Finset X)) (hQ : ∀ A ∈ internalSides B, IsDisjointCover B A (Q A)) :
    contractSides B ((internalSides B).filter fun A => ∃ Y ∈ Q A, ¬ IsTreelike N Y) = treeOfBlobs N := by
  sorry

/-- The 3-fix-1-alter search (§4.3, `tob2025:3f1a_correctness`) on the four blocks `P i`, with anchors
`z i ∈ P i`: for each block, keep the anchors of the other three blocks and vary the taxon of this
one. -/
def threeFixOneAlter (P : Fin 4 → Finset X) (z : Fin 4 → X) : Finset (Finset X) :=
  univ.biUnion fun i => (P i).image fun x => (univ.image (Function.update z i x))

/-- **The 3-fix-1-alter search tests a disjoint cover**, of `n - 3` four-taxon subsets
(`tob2025:3f1a_correctness`), on a binary tree. -/
theorem threeFixOneAlter_isDisjointCover {T : Finset (Finset X)} (hT : IsBinaryTree T) {A : Finset X}
    (hA : A ∈ internalSides T) (P : Fin 4 → Finset X)
    (hP : ∀ i j, i ≠ j → Disjoint (P i) (P j)) (hcover : univ.biUnion P = univ)
    (hP₁ : P 0 ∪ P 1 = A) (hmem : ∀ i, P i ∈ T) (z : Fin 4 → X) (hz : ∀ i, z i ∈ P i) :
    IsDisjointCover T A (threeFixOneAlter P z) ∧
      (threeFixOneAlter P z).card = Fintype.card X - 3 := by
  sorry

end TOBQMC
