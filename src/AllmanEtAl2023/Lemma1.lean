module

public import AllmanEtAl2023.Concordance

/-!
# Allman, Baños, Mitchell, Rhodes 2023: Lemma 1

The paper omits the proof ("A basic combinatorial observation, whose proof we omit"), and cites nothing for it. The earlier
project did not state this lemma; here it is stated as printed, and needs a proof of our own, by the count of the degrees
of the tree `T(𝒩⁻)` (see `notes/allman_inventory.md`).
-/

@[expose] public noncomputable section

open Phylogenetics Phylogenetics.RootedNetwork
open scoped Classical

namespace AllmanEtAl2023.Printed

variable {V E X : Type*} [Fintype X] [DecidableEq X] {N : RootedNetwork V E X}

/- Inventory (`notes/allman_inventory.md`). The paper has no proof. Nothing in the seven older files states this. To build: the degree count of the tree `T(𝒩⁻)`
(`treeOfBlobs_semidirected_isTree`, `nodeDegree_bridgeQuotient`), that a blob without a taxon has at least two incident cut edges, and `Bridges.splits_Trd`. -/
/-- **Lemma 1** (`a:lem:4netblobs`). Let `𝒩⁺` be a 4-taxon rooted binary phylogenetic network. Then the semidirected unrooted
network `𝒩⁻` must have either exactly one 4-blob, or exactly two 3-blobs. In either case, `𝒩⁻` may have any number of 2-blobs, but
no other non-leaf blobs. In case 1, the reduced unrooted tree of blobs `T_rd(𝒩⁻)` is the unresolved quartet tree and the taxa form
a B-quartet. In case 2, `T_rd(𝒩⁻)` is a resolved quartet tree and the taxa form a T-quartet.

The degree of a blob of `𝒩⁻` is `cutDegree`, since `𝒩⁻` has no root. The proof is ours: the paper omits it. -/
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
  sorry

end AllmanEtAl2023.Printed
