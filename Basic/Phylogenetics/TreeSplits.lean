module

public import Basic.Phylogenetics.Hierarchy
public import Basic.Phylogenetics.CutHierarchy

/-!
# Unrooted trees through their split families

The combinatorics of unrooted trees that the three papers use, on the representation by sides of
splits of `Basic/Phylogenetics/Defs.lean`.

* `IsUnrootedTree` is characterized by pairwise compatibility (`isUnrootedTree_iff`);
* the vertices of a tree of degree at least three are its *vertex partitions* (`IsVertexPartition`):
  partitions of the taxa into sides of the tree such that every split of the tree has a side inside a
  block;
* a quartet that a tree does not resolve has a unique centre among these vertices
  (`existsUnique_center`);
* a split with two taxa on each side lies in the tree when all its quartets are displayed
  (`mem_of_forall_displays`).

API: everything below.
-/

@[expose] public noncomputable section

namespace Phylogenetics

open Finset
open scoped Classical

variable {X : Type*} [Fintype X] [DecidableEq X]

/-- The laws of a family of sides of splits: the sides are nonempty and proper, closed under
complement, include the singletons, and are pairwise compatible. -/
structure IsSplitFamily (T : Finset (Finset X)) : Prop where
  nonempty : ∀ A ∈ T, A.Nonempty
  compl_nonempty : ∀ A ∈ T, Aᶜ.Nonempty
  compl_mem : ∀ A ∈ T, Aᶜ ∈ T
  singleton_mem : ∀ x : X, {x} ∈ T
  compatible : ∀ A ∈ T, ∀ B ∈ T, A ⊆ B ∨ B ⊆ A ∨ Disjoint A B ∨ A ∪ B = univ

/-- For at least two taxa, unrooted trees are exactly the pairwise compatible split families. -/
theorem isUnrootedTree_iff (hX : 2 ≤ Fintype.card X) (T : Finset (Finset X)) :
    IsUnrootedTree T ↔ IsSplitFamily T := by
  sorry

/-- The rooting of an unrooted tree at the taxon `r`: its sides avoiding `r`, with the root and `{r}`. -/
def rootedAt (T : Finset (Finset X)) (r : X) : Finset (Finset X) :=
  insert univ (insert {r} (T.filter fun A => r ∉ A))

theorem rootedAt_isHierarchy {T : Finset (Finset X)} (hT : IsSplitFamily T) (r : X) :
    IsHierarchy (rootedAt T r) := by
  sorry

theorem unroot_rootedAt {T : Finset (Finset X)} (hX : 2 ≤ Fintype.card X) (hT : IsSplitFamily T)
    (r : X) : unroot (rootedAt T r) = T := by
  sorry

/-- The tree of blobs is an unrooted tree. -/
theorem treeOfBlobs_isUnrootedTree {V E : Type*} {N : RootedNetwork V E X} (hN : N.IsPhylogenetic)
    [Nonempty X] : IsUnrootedTree (treeOfBlobs N) := by
  sorry

/-- A quartet tree has four taxa. -/
theorem QuartetTree.card_taxa (s : QuartetTree X) : s.taxa.card = 4 := by
  sorry

theorem card_treesOn {q : Finset X} (hq : q.card = 4) : (treesOn q).card = 3 := by
  sorry

theorem QuartetTree.card_alternatives (s : QuartetTree X) : s.alternatives.card = 2 := by
  sorry

/-- The quartet tree with cherries `{a, b}` and `{c, d}`. -/
def quartetTree (a b c d : X) (h : ({a, b, c, d} : Finset X).card = 4) : QuartetTree X :=
  ⟨{{a, b}, {c, d}}, by sorry⟩

/-- A tree displays at most one quartet tree on a set of four taxa. -/
theorem IsUnrootedTree.displays_unique {T : Finset (Finset X)} (hT : IsUnrootedTree T)
    {s s' : QuartetTree X} (hs : Displays T s) (hs' : Displays T s') (h : s.taxa = s'.taxa) :
    s = s' := by
  sorry

theorem Displays.mono {T T' : Finset (Finset X)} (h : T ⊆ T') {s : QuartetTree X}
    (hs : Displays T s) : Displays T' s := by
  sorry

/-- A binary tree displays a quartet tree on every set of four taxa. -/
theorem IsBinaryTree.exists_displays {T : Finset (Finset X)} (hT : IsBinaryTree T) {q : Finset X}
    (hq : q.card = 4) : ∃ s ∈ treesOn q, Displays T s := by
  sorry

/-- A tree displaying the quartet trees of a split with at least two taxa on each side has that
split. (This is the case of Steel's quartet theorem that the papers use.) -/
theorem mem_of_forall_displays {T : Finset (Finset X)} (hT : IsUnrootedTree T) {A : Finset X}
    (hA : 2 ≤ A.card) (hA' : 2 ≤ Aᶜ.card)
    (h : ∀ s ∈ bipartitionQuartets A, Displays T s) : A ∈ T := by
  sorry

/-- A tree displaying all the quartet trees that another tree displays resolves it. -/
theorem subset_of_forall_displays {T T' : Finset (Finset X)} (hT : IsUnrootedTree T)
    (hT' : IsUnrootedTree T') (h : ∀ s, Displays T' s → Displays T s) : T' ⊆ T := by
  sorry

/-- Contracting internal edges of a tree gives a tree. -/
theorem IsUnrootedTree.contractSides {T C : Finset (Finset X)} (hT : IsUnrootedTree T)
    (hC : C ⊆ internalSides T) : IsUnrootedTree (contractSides T C) := by
  sorry

/-- A vertex of degree at least three of the tree `T`: the partition of the taxa according to the
components of the tree with the vertex deleted. -/
structure IsVertexPartition (T P : Finset (Finset X)) : Prop where
  mem : ∀ B ∈ P, B ∈ T
  pairwiseDisjoint : ∀ B ∈ P, ∀ C ∈ P, B ≠ C → Disjoint B C
  cover : P.sup id = univ
  three_le : 3 ≤ P.card
  edge_in_block : ∀ C ∈ T, (∃ B ∈ P, C ⊆ B) ∨ ∃ B ∈ P, Cᶜ ⊆ B

/-- The multifurcations of a tree: its vertices of degree at least four. -/
def multifurcations (T : Finset (Finset X)) : Finset (Finset (Finset X)) :=
  univ.filter fun P => IsVertexPartition T P ∧ 4 ≤ P.card

/-- The taxa of `q` lie in distinct blocks of `P`. -/
def InDistinctBlocks (P : Finset (Finset X)) (q : Finset X) : Prop :=
  ∀ B ∈ P, (B ∩ q).card ≤ 1

/-- A set of four taxa that a tree does not resolve has a unique centre, a multifurcation at whose
blocks the taxa are distinct (ECToBlob's proof of Theorem 3.1, TOB-QMC's proof of Lemma 3). -/
theorem existsUnique_center {T : Finset (Finset X)} (hT : IsUnrootedTree T) {q : Finset X}
    (hq : q.card = 4) (hstar : ∀ s ∈ treesOn q, ¬ Displays T s) :
    ∃! P, P ∈ multifurcations T ∧ InDistinctBlocks P q := by
  sorry

/-- Taxa in distinct blocks of a vertex partition are not resolved by the tree. -/
theorem not_displays_of_inDistinctBlocks {T P : Finset (Finset X)} (hT : IsUnrootedTree T)
    (hP : IsVertexPartition T P) {s : QuartetTree X} (h : InDistinctBlocks P s.taxa) :
    ¬ Displays T s := by
  sorry

end Phylogenetics
