module

public import AllmanEtAl2023.Bridges
public import AllmanEtAl2023.Theorem2

/-!
# Allman, Baños, Mitchell, Rhodes 2023: the unnumbered claims that the proofs use

Each has a label of our own, `a:claim:…`, in `notes/routes_allman.tsv`. The paper says each of these in passing, and proves none of them except by a
sentence. Those proved here are short, from the bridges.

* `a:claim:cf-induced`: "In passing to an induced network, B-quartets may become T-quartets, although `CF`s remain unchanged": `nmscCF_induced`.
* `a:claim:generic-induced`: "the generic conditions ... give rise to a generic condition on numerical parameter values on the `n`-taxon network":
  `isMetric_inducedParams`, `isGenericNull_inducedParams`. And `induced_isBinaryNetwork` (proved, in `src/AllmanEtAl2023/InducedNetwork.lean`).
* `a:claim:three-taxa`: "On a network `𝒩⁺` every subset of 3 taxa determines a blob": `Bridges.exists_isDeterminedBy_three` (proved).
* `a:claim:b-unresolved`: "the unresolved quartet `abcd` is displayed on the tree of blobs": `isBlobQuartet_iff_displaysUnresolved`.
* `a:claim:t-resolved`: "If `{a, b, c, d}` is not a B-quartet ... the tree of blobs displays a resolved quartet tree for these taxa":
  `exists_displays_of_isTreeQuartet`.
* `a:claim:t-induced`: "any T-quartet on a large network is also a T-quartet on the induced quartet network", with the same quartet:
  `isTreeQuartet_induced`, `inducedHasQuartetTopology_of_displays` (the first proved, and the second from a `Bridges` lemma on four taxa).
* `a:claim:suppress-blobs`: "induced networks are obtained from subnetworks by suppressing degree-2 nodes. Under this operation, blobs pass to blobs, and
  cut edges to cut edges": `Bridges.isBlobQuartetOnInduced_iff` (proved).
* `a:claim:induced-induced`: an induced network of an induced network is an induced network, as far as quartets go; the induction of Theorem 3 uses this
  without saying so: `inducedHasQuartetTopology_induced`, `inducedHasStarTopology_induced`.
* `a:claim:thm3-representatives`: "Choose one taxon from each component which contains a taxon ... all edges in `ℬ` are retained":
  `exists_representatives_induced`.
* `a:claim:rooted-forms`: "the reduced rooted tree of blobs thus has topology `(((a, b), c), d)`, `((a, b), (c, d))`, or `((a, b), c, d)`": `rootedForms`.
* `a:claim:displayed-determine`: "the collection of displayed quartets determine the tree" (Semple and Steel 2005; Rhodes 2020):
  `treeFromQuartets_displays` (proved, from the library's Steel theorem `mem_of_forall_displays`).
* `a:claim:thm4-displayed`: "we thus can identify the topology of every displayed quartet tree on `T_rd(𝒩⁻)`": `displayedFromCF_eq`.

The geometric statements after Proposition 1 are used by no proof, so they are not stated. The first equivalent condition after Definition 12, on deleting the
edges of a blob, is used by no proof either.
-/

@[expose] public noncomputable section

open Phylogenetics Phylogenetics.RootedNetwork
open scoped Classical

namespace AllmanEtAl2023.Printed

variable {V E X : Type*} {N : RootedNetwork V E X}

/-! ### `CF`s of an induced network -/

section CF

variable [Fintype V] [Fintype E] [Fintype X] [DecidableEq X]

/-- **"In passing to an induced network, ... `CF`s remain unchanged"** (`a:claim:cf-induced`; also in Section 4: "The `CF`s computed from the induced 4-taxon networks
are the same as gene tree probabilities from the large network marginalized to 4-taxon sets, by the structure of the NMSC model"). -/
theorem nmscCF_induced (hN : IsBinaryNetwork N) {θ : MetricData E} (hθ : N.IsMetric θ) (Y : Set X) (hY : Y.Nontrivial)
    [Fintype Y] [DecidableEq Y] [Fintype (InducedV hN Y hY)] [Fintype (InducedE hN Y hY)] (s : QuartetTree Y) :
    nmscCF (induced hN Y hY) (inducedParams hN Y hY θ) 0 s = nmscCF N θ 0 (s.map Subtype.val_injective) := by
  sorry

/-- The map of parameters sends valid parameters to valid parameters (`a:claim:generic-induced`). -/
theorem isMetric_inducedParams (hN : IsBinaryNetwork N) {θ : MetricData E} (hθ : N.IsMetric θ) (Y : Set X)
    (hY : Y.Nontrivial) [Fintype (InducedE hN Y hY)] :
    (induced hN Y hY).IsMetric (inducedParams hN Y hY θ) := by
  sorry

/-- **"They give rise to a generic condition on numerical parameter values on the `n`-taxon network"** (`a:claim:generic-induced`, in the proof of Corollary 1):
preimages of null sets under the map of parameters are null. -/
theorem isGenericNull_inducedParams (hN : IsBinaryNetwork N) (Y : Set X) (hY : Y.Nontrivial)
    [Fintype (InducedE hN Y hY)] {A' : Set (MetricData (InducedE hN Y hY))}
    (hA' : (induced hN Y hY).IsGenericNull A') :
    N.IsGenericNull {θ | N.IsMetric θ ∧ inducedParams hN Y hY θ ∈ A'} := by
  sorry

end CF

/-! ### The B-quartets and the tree of blobs -/

section Displayed

variable [Fintype X] [DecidableEq X]

/-- **"The unresolved quartet `abcd` is displayed on the tree of blobs `T_rd(𝒩⁻)`"** (`a:claim:b-unresolved`), among the equivalent conditions after Definition 12. -/
theorem isBlobQuartet_iff_displaysUnresolved (hN : IsBinaryNetwork N) (hX : Nontrivial X) {Q : Finset X} (hQ : Q.card = 4) :
    IsBlobQuartet N Q ↔ (Trd hN hX).DisplaysUnresolved Q := by
  rw [Bridges.isBlobQuartet_iff_isBQuartet hN.isPhylogenetic hQ, LabelledGraph.DisplaysUnresolved, Bridges.splits_Trd hN hX]
  exact ⟨fun h => ⟨hQ, h⟩, fun h => h.2⟩

/-- **"If `{a, b, c, d}` is not a B-quartet, then in the tree of blobs there must be an edge whose deletion disconnects two of these taxa from the others. Consequently,
the tree of blobs displays a resolved quartet tree for these taxa"** (`a:claim:t-resolved`). -/
theorem exists_displays_of_isTreeQuartet (hN : IsBinaryNetwork N) (hX : Nontrivial X) {Q : Finset X} (hQ : IsTreeQuartet N Q) :
    ∃ s ∈ treesOn Q, Displays (Trd hN hX).splits s := by
  have h := hQ.2
  rw [isBlobQuartet_iff_displaysUnresolved hN hX hQ.1, LabelledGraph.DisplaysUnresolved] at h
  by_contra hne
  push Not at hne
  exact h ⟨hQ.1, hne⟩

/-- **"The collection of displayed quartets determine the tree"** (`a:claim:displayed-determine`; Semple and Steel 2005, Rhodes 2020), on split families, from the library's
Steel theorem. -/
theorem treeFromQuartets_displays {T : Finset (Finset X)} (hT : IsUnrootedTree T) (hX : 2 ≤ Fintype.card X) :
    treeFromQuartets {s | Displays T s} = T := by
  have hS := hT.isSplitFamily hX
  ext A
  simp only [treeFromQuartets, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨h₁, h₂, h⟩
    by_cases hA : 2 ≤ A.card
    · by_cases hA' : 2 ≤ Aᶜ.card
      · exact mem_of_forall_displays hT hA hA' h
      · obtain ⟨x, hx⟩ := Finset.card_eq_one.mp (by have := Finset.card_pos.mpr h₂; omega : Aᶜ.card = 1)
        have := hS.compl_mem _ (hS.singleton_mem x)
        rwa [← hx, compl_compl] at this
    · obtain ⟨x, rfl⟩ := Finset.card_eq_one.mp (by have := Finset.card_pos.mpr h₁; omega : A.card = 1)
      exact hS.singleton_mem x
  · intro hA
    exact ⟨hS.nonempty A hA, hS.compl_nonempty A hA, fun s hs => ⟨A, hA, (Finset.mem_filter.mp hs).2⟩⟩

end Displayed

/-! ### Induced networks -/

section Induced

variable [DecidableEq X]

omit [DecidableEq X] in
/-- **"Thus any T-quartet on a large network is also a T-quartet on the induced quartet network"** (`a:claim:t-induced`): the contrapositive of Corollary 2. -/
theorem isTreeQuartet_induced (hN : IsBinaryNetwork N) {Q : Finset X} (hQ : IsTreeQuartet N Q) :
    ¬ IsBlobQuartetOnInduced hN (Q : Set X) (nontrivial_coe_of_card_four hQ.1) Q :=
  fun hB => hQ.2 (corollary2 hN (Q : Set X) (nontrivial_coe_of_card_four hQ.1) subset_rfl hB)

/-- "The resolved quartet associated to a T-quartet" is the topology of the induced quartet network (`a:claim:t-induced`): a cut edge restricts to one on the
induced 4-taxon network. -/
theorem inducedHasQuartetTopology_of_displays [Fintype X] (hN : IsBinaryNetwork N) (hX : Nontrivial X) {a b c d : X}
    (h : ({a, b, c, d} : Finset X).card = 4) (hs : Displays (Trd hN hX).splits (quartetTree a b c d h)) :
    InducedHasQuartetTopology hN a b c d h := by
  rw [Bridges.splits_Trd hN hX] at hs
  exact (Bridges.inducedHasQuartetTopology_iff hN h).mpr (inducedCutSplit_of_displays hN.isPhylogenetic hs)

/-- An induced network of an induced network, as far as resolved quartets go (`a:claim:induced-induced`). The proof of Theorem 3 uses this when it applies the inductive
hypothesis to a network induced on fewer taxa: it does not say so. -/
theorem inducedHasQuartetTopology_induced (hN : IsBinaryNetwork N) {Y : Set X} (hY : Y.Nontrivial) {a b c d : Y}
    (h : ({a, b, c, d} : Finset Y).card = 4) (h' : ({a.1, b.1, c.1, d.1} : Finset X).card = 4) :
    InducedHasQuartetTopology (induced_isBinaryNetwork hN Y hY) a b c d h ↔
      InducedHasQuartetTopology hN a.1 b.1 c.1 d.1 h' := by
  sorry

/-- An induced network of an induced network, as far as unresolved quartets go (`a:claim:induced-induced`). -/
theorem inducedHasStarTopology_induced (hN : IsBinaryNetwork N) {Y : Set X} (hY : Y.Nontrivial) {a b c d : Y}
    (h : ({a, b, c, d} : Finset Y).card = 4) (h' : ({a.1, b.1, c.1, d.1} : Finset X).card = 4) :
    InducedHasStarTopology (induced_isBinaryNetwork hN Y hY) a b c d h ↔
      InducedHasStarTopology hN a.1 b.1 c.1 d.1 h' := by
  sorry

/-- **The first step of the proof of Theorem 3** (`a:claim:thm3-representatives`): "consider the connected components of the graph obtained by deleting `ℬ`. Choose one taxon from each
component which contains a taxon, with four of these being `a, b, c, d`. Passing to the induced network on those taxa, all edges in `ℬ` are retained." So `Q` is a B-quartet there. -/
theorem exists_representatives_induced (hN : IsBinaryNetwork N) {Q : Finset X} {B : N.graph.BlobVertex}
    (hB : IsDeterminedBy N.graph N.leaf B Q) (h4 : Q.card = 4) :
    ∃ R : Finset X, Q ⊆ R ∧ IsDeterminedBy N.graph N.leaf B R ∧
      (∀ x, ∃ r ∈ R, N.graph.Walks (incidentCutEdges N.graph B)ᶜ (N.leaf x) (N.leaf r)) ∧
      ∃ hR : (R : Set X).Nontrivial, IsBlobQuartetOnInduced hN (R : Set X) hR Q := by
  sorry

/-- The non-singleton clusters of a rooted tree: the taxa below an edge. -/
def rootedClusters {V' E' : Type*} (R : RootedNetwork V' E' X) : Set (Set X) :=
  {A | 2 ≤ A.ncard ∧ ∃ e, A = {x | R.IsBelow e x}}

/-- **"Permuting taxon names if necessary, we may assume that the reduced rooted tree of blobs thus has topology `(((a, b), c), d)`, `((a, b), (c, d))`, or `((a, b), c, d)`"**
(`a:claim:rooted-forms`, in the proof of Theorem 1). Here are the seven rooted forms before the permutation: the root on a pendant edge, on the internal edge, or at one of the two nodes.
`AllmanEtAl2023.rootedForm_cases` (`Theorem1.lean`) is a tautology, and doesn't say this. -/
theorem rootedForms [Fintype X] (hN : IsBinaryNetwork N) (hcard : Fintype.card X = 4) {a b c d : X}
    (hT : (Trd hN (nontrivial_of_card_four hcard)).HasQuartetTopology a b c d) :
    rootedClusters (reducedRootedTree hN (nontrivial_of_card_four hcard)) = {{a, b}, {a, b, c}} ∨
      rootedClusters (reducedRootedTree hN (nontrivial_of_card_four hcard)) = {{a, b}, {a, b, d}} ∨
      rootedClusters (reducedRootedTree hN (nontrivial_of_card_four hcard)) = {{c, d}, {c, d, a}} ∨
      rootedClusters (reducedRootedTree hN (nontrivial_of_card_four hcard)) = {{c, d}, {c, d, b}} ∨
      rootedClusters (reducedRootedTree hN (nontrivial_of_card_four hcard)) = {{a, b}, {c, d}} ∨
      rootedClusters (reducedRootedTree hN (nontrivial_of_card_four hcard)) = {{a, b}} ∨
      rootedClusters (reducedRootedTree hN (nontrivial_of_card_four hcard)) = {{c, d}} := by
  sorry

/-- **"Treating B-quartets on `𝒩⁺` as unresolved, we thus can identify the topology of every displayed quartet tree on `T_rd(𝒩⁻)`"** (`a:claim:thm4-displayed`, in the proof of Theorem 4). -/
theorem displayedFromCF_eq [Fintype V] [Fintype E] [Fintype X] (hN : IsBinaryNetwork N) (hX : Nontrivial X) :
    ForGenericParams N fun θ => displayedFromCF (nmscCF N θ 0) = {s | Displays (Trd hN hX).splits s} := by
  sorry

end Induced

end AllmanEtAl2023.Printed
