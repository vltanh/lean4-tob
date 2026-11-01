module

public import AllmanEtAl2023.TrdFour

/-!
# Allman, Baños, Mitchell, Rhodes 2023: Lemma 1

The paper omits the proof ("A basic combinatorial observation, whose proof we omit"), and cites nothing for it. The proof here is our own, by the count of the degrees of
the tree `T(𝒩⁻)`: see `AllmanEtAl2023.TrdFour`.
-/

@[expose] public noncomputable section

open Phylogenetics Phylogenetics.RootedNetwork
open scoped Classical

namespace AllmanEtAl2023

variable {V E X : Type*} [Fintype X] [DecidableEq X] {N : RootedNetwork V E X}

/-- **The bridge to the tree of blobs of the library.** On four taxa, the unresolved `T_rd(𝒩⁻)` is a B-quartet. -/
theorem isBlobQuartet_univ_of_hasStarTopology (hN : IsBinaryNetwork N) (hcard : Fintype.card X = 4) {a b c d : X}
    (h : ({a, b, c, d} : Finset X).card = 4) (hT : (Trd hN (nontrivial_of_card_four hcard)).HasStarTopology a b c d) :
    IsBlobQuartet N Finset.univ := by
  have hu : ({a, b, c, d} : Finset X) = Finset.univ := Finset.eq_univ_of_card _ (h.trans hcard.symm)
  have hc : (Finset.univ : Finset X).card = 4 := by rw [Finset.card_univ, hcard]
  obtain ⟨-, hno⟩ := (Bridges.hasStarTopology_iff_displaysUnresolved hN hcard h).mp hT
  rw [hu, Bridges.splits_Trd] at hno
  exact (Bridges.isBlobQuartet_iff_isBQuartet hN.isPhylogenetic hc).mpr hno

/-- **The bridge to the tree of blobs of the library.** On four taxa, a resolved `T_rd(𝒩⁻)` is a T-quartet. -/
theorem isTreeQuartet_univ_of_hasQuartetTopology (hN : IsBinaryNetwork N) (hcard : Fintype.card X = 4) {a b c d : X}
    (h : ({a, b, c, d} : Finset X).card = 4) (hT : (Trd hN (nontrivial_of_card_four hcard)).HasQuartetTopology a b c d) :
    IsTreeQuartet N Finset.univ := by
  have hu : ({a, b, c, d} : Finset X) = Finset.univ := Finset.eq_univ_of_card _ (h.trans hcard.symm)
  have hc : (Finset.univ : Finset X).card = 4 := by rw [Finset.card_univ, hcard]
  refine ⟨hc, fun hB => ?_⟩
  have hd := (Bridges.hasQuartetTopology_iff_displays hN hcard h).mp hT
  rw [Bridges.splits_Trd] at hd
  exact (Bridges.isBlobQuartet_iff_isBQuartet hN.isPhylogenetic hc).mp hB _
    (mem_treesOn.mpr ((quartetTree_taxa _ _ _ _ _).trans hu)) hd

/-- **Lemma 1** (`a:lem:4netblobs`). Let `𝒩⁺` be a 4-taxon rooted binary phylogenetic network. Then the semidirected unrooted
network `𝒩⁻` must have either exactly one 4-blob, or exactly two 3-blobs. In either case, `𝒩⁻` may have any number of 2-blobs, but
no other non-leaf blobs. In case 1, the reduced unrooted tree of blobs `T_rd(𝒩⁻)` is the unresolved quartet tree and the taxa form
a B-quartet. In case 2, `T_rd(𝒩⁻)` is a resolved quartet tree and the taxa form a T-quartet.

The degree of a blob of `𝒩⁻` is `cutDegree`, since `𝒩⁻` has no root. The paper omits the proof, and any route is allowed: this one is ours, by the count of the degrees
of the tree `T(𝒩⁻)` (`trd_cases`). -/
theorem lemma1 (hN : IsBinaryNetwork N) (hcard : Fintype.card X = 4) :
    ((∃! b, cutDegree (semidirected hN (nontrivial_of_card_four hcard)).graph b = 4) ∧
      (∀ b, (∀ x, blobOf _ ((semidirected hN (nontrivial_of_card_four hcard)).leaf x) ≠ b) →
        cutDegree (semidirected hN (nontrivial_of_card_four hcard)).graph b = 2 ∨
          cutDegree (semidirected hN (nontrivial_of_card_four hcard)).graph b = 4) ∧
      (∀ a b c d : X, ({a, b, c, d} : Finset X).card = 4 →
        (Trd hN (nontrivial_of_card_four hcard)).HasStarTopology a b c d) ∧
      IsBlobQuartet N Finset.univ) ∨
    ((∃ b₁ b₂, b₁ ≠ b₂ ∧ ∀ b, cutDegree (semidirected hN (nontrivial_of_card_four hcard)).graph b = 3 ↔
        b = b₁ ∨ b = b₂) ∧
      (∀ b, (∀ x, blobOf _ ((semidirected hN (nontrivial_of_card_four hcard)).leaf x) ≠ b) →
        cutDegree (semidirected hN (nontrivial_of_card_four hcard)).graph b = 2 ∨
          cutDegree (semidirected hN (nontrivial_of_card_four hcard)).graph b = 3) ∧
      (∃ a b c d : X, ({a, b, c, d} : Finset X).card = 4 ∧
        (Trd hN (nontrivial_of_card_four hcard)).HasQuartetTopology a b c d) ∧
      IsTreeQuartet N Finset.univ) := by
  have : Finite E := hN.finite_arcs
  have hX := nontrivial_of_card_four hcard
  have hdeg : ∀ b, cutDegree (semidirected hN hX).graph b = nodeDegree (semidirected hN hX).treeOfBlobs b := fun b =>
    (nodeDegree_bridgeQuotient b).symm
  have hleaf := nodeDegree_treeOfBlobs_leaf hN hX
  rcases trd_cases hN hcard with ⟨⟨z, hz, hd, hrest⟩, hS⟩ | ⟨⟨z₁, z₂, hne, hz₁, hz₂, hd₁, hd₂, hrest⟩, a, b, c, d, h, hT⟩
  · left
    obtain ⟨a, b, c, d, h⟩ := exists_names_of_card_four hcard
    refine ⟨⟨z, (hdeg z).trans hd, fun w hw => ?_⟩, fun w hw => ?_, hS, isBlobQuartet_univ_of_hasStarTopology hN hcard h (hS a b c d h)⟩
    · have hw' : nodeDegree (semidirected hN hX).treeOfBlobs w = 4 := (hdeg w).symm.trans hw
      by_contra hwz
      by_cases hl : ∃ x, blobOf (semidirected hN hX).graph ((semidirected hN hX).leaf x) = w
      · obtain ⟨x, rfl⟩ := hl
        have := hleaf x
        omega
      · push Not at hl
        have := hrest w hl hwz
        omega
    · rw [hdeg]
      by_cases hwz : w = z
      · rw [hwz]
        exact Or.inr hd
      · exact Or.inl (hrest w hw hwz)
  · right
    refine ⟨⟨z₁, z₂, hne, fun w => ⟨fun hw => ?_, ?_⟩⟩, fun w hw => ?_, ⟨a, b, c, d, h, hT⟩, isTreeQuartet_univ_of_hasQuartetTopology hN hcard h hT⟩
    · have hw' : nodeDegree (semidirected hN hX).treeOfBlobs w = 3 := (hdeg w).symm.trans hw
      by_contra hwz
      push Not at hwz
      by_cases hl : ∃ x, blobOf (semidirected hN hX).graph ((semidirected hN hX).leaf x) = w
      · obtain ⟨x, rfl⟩ := hl
        have := hleaf x
        omega
      · push Not at hl
        have := hrest w hl hwz.1 hwz.2
        omega
    · rintro (rfl | rfl)
      · exact (hdeg _).trans hd₁
      · exact (hdeg _).trans hd₂
    · rw [hdeg]
      by_cases hw₁ : w = z₁
      · rw [hw₁]
        exact Or.inr hd₁
      by_cases hw₂ : w = z₂
      · rw [hw₂]
        exact Or.inr hd₂
      exact Or.inl (hrest w hw hw₁ hw₂)

end AllmanEtAl2023
