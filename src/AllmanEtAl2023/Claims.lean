module

public import AllmanEtAl2023.InducedTransfer
public import AllmanEtAl2023.Theorem2

/-!
# Allman, Baños, Mitchell, Rhodes 2023: the unnumbered claims that Theorems 3 and 4 use

Each has a label of our own, `a:claim:…`, in `docs/paper_routes.tsv`. The paper says each of these in passing, and proves none of them except by a
sentence. Those proved here are short, from the bridges. The claims for Theorem 1 and Corollary 1 are in `AllmanEtAl2023.ClaimsTheorem1`.

* `a:claim:three-taxa`: "On a network `𝒩⁺` every subset of 3 taxa determines a blob": `Bridges.exists_isDeterminedBy_three` (proved).
* `a:claim:b-unresolved`: "the unresolved quartet `abcd` is displayed on the tree of blobs": `isBlobQuartet_iff_displaysUnresolved`.
* `a:claim:t-resolved`: "If `{a, b, c, d}` is not a B-quartet ... the tree of blobs displays a resolved quartet tree for these taxa":
  `exists_displays_of_isTreeQuartet`.
* `a:claim:t-induced`: "any T-quartet on a large network is also a T-quartet on the induced quartet network", with the same quartet:
  `isTreeQuartet_induced`, `inducedHasQuartetTopology_of_displays` (the first proved, and the second from a `Bridges` lemma on four taxa).
* `a:claim:suppress-blobs`: "induced networks are obtained from subnetworks by suppressing degree-2 nodes. Under this operation, blobs pass to blobs, and
  cut edges to cut edges": `Bridges.isBlobQuartetOnInduced_iff` (proved).
* `a:claim:induced-induced`: an induced network of an induced network is an induced network, as far as quartets go; the induction of Theorem 3 uses this
  without saying so: `inducedHasQuartetTopology_induced`, `inducedHasStarTopology_induced`, by the steps of Definition 6 in `InducedTransfer`.
* `a:claim:thm3-representatives`: "Choose one taxon from each component which contains a taxon ... all edges in `ℬ` are retained":
  `exists_representatives_induced`.
* `a:claim:displayed-determine`: "the collection of displayed quartets determine the tree" (Semple and Steel 2005; Rhodes 2020):
  `treeFromQuartets_displays` (proved, from the library's Steel theorem `mem_of_forall_displays`).
* `a:claim:thm4-displayed`: "we thus can identify the topology of every displayed quartet tree on `T_rd(𝒩⁻)`": `displayedFromCF_eq`, in `AllmanEtAl2023.Theorem4`, since it uses Theorem 3.

The geometric statements after Proposition 1 are used by no proof, so they are not stated. What else the paper says in passing, and no proof uses, is in `AllmanEtAl2023.InPassing`.
-/

@[expose] public noncomputable section

open Phylogenetics Phylogenetics.RootedNetwork
open scoped Classical

namespace AllmanEtAl2023

variable {V E X : Type*} {N : RootedNetwork V E X}

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
  have : Finite X := hN.finite_taxa
  let _ : Fintype X := Fintype.ofFinite X
  let _ : Fintype Y := Fintype.ofFinite Y
  rw [Bridges.inducedHasQuartetTopology_iff _ h, Bridges.inducedHasQuartetTopology_iff hN h',
    Bridges.inducedCutSplit_induced_iff hN hY, Bridges.map_quartetTree h h']

/-- An induced network of an induced network, as far as unresolved quartets go (`a:claim:induced-induced`). -/
theorem inducedHasStarTopology_induced (hN : IsBinaryNetwork N) {Y : Set X} (hY : Y.Nontrivial) {a b c d : Y}
    (h : ({a, b, c, d} : Finset Y).card = 4) (h' : ({a.1, b.1, c.1, d.1} : Finset X).card = 4) :
    InducedHasStarTopology (induced_isBinaryNetwork hN Y hY) a b c d h ↔
      InducedHasStarTopology hN a.1 b.1 c.1 d.1 h' := by
  have : Finite X := hN.finite_taxa
  let _ : Fintype X := Fintype.ofFinite X
  let _ : Fintype Y := Fintype.ofFinite Y
  rw [Bridges.inducedHasStarTopology_iff _ h, Bridges.inducedHasStarTopology_iff hN h',
    Bridges.isTreelike_induced_iff hN hY h h']

/-- **The first step of the proof of Theorem 3** (`a:claim:thm3-representatives`): "consider the connected components of the graph obtained by deleting `ℬ`. Choose one taxon from each
component which contains a taxon, with four of these being `a, b, c, d`. Passing to the induced network on those taxa, all edges in `ℬ` are retained." So `Q` is a B-quartet there. -/
theorem exists_representatives_induced (hN : IsBinaryNetwork N) {Q : Finset X} {B : N.graph.BlobVertex}
    (hB : IsDeterminedBy N.graph N.leaf B Q) (h4 : Q.card = 4) :
    ∃ R : Finset X, Q ⊆ R ∧ IsDeterminedBy N.graph N.leaf B R ∧
      (∀ x, ∃ r ∈ R, N.graph.Walks (incidentCutEdges N.graph B)ᶜ (N.leaf x) (N.leaf r)) ∧
      ∃ hR : (R : Set X).Nontrivial, IsBlobQuartetOnInduced hN (R : Set X) hR Q := by
  have hP := hN.isPhylogenetic
  have : Finite X := hP.finite_taxa
  let _ : Fintype X := Fintype.ofFinite X
  have : Finite E := hP.finite_arcs
  induction B using Quotient.inductionOn with
  | h v =>
    change IsDeterminedBy N.graph N.leaf (blobOf N.graph v) Q at hB
    change ∃ R : Finset X, Q ⊆ R ∧ IsDeterminedBy N.graph N.leaf (blobOf N.graph v) R ∧
      (∀ x, ∃ r ∈ R, N.graph.Walks (incidentCutEdges N.graph (blobOf N.graph v))ᶜ (N.leaf x) (N.leaf r)) ∧
      ∃ hR : (R : Set X).Nontrivial, IsBlobQuartetOnInduced hN (R : Set X) hR Q
    obtain ⟨h3, hd⟩ := isDeterminedBy_blobOf_iff.mp hB
    have huniv : ((Finset.univ : Finset X) : Set X) = Set.univ := Finset.coe_univ
    have hanc : N.ancestralArcs ((Finset.univ : Finset X) : Set X) = Set.univ := by
      rw [huniv]
      exact Bridges.ancestralArcs_univ hP
    have hv : v ∈ N.ancestralVertices ((Finset.univ : Finset X) : Set X) := by
      rw [huniv, Bridges.ancestralVertices_univ hP]
      exact Set.mem_univ v
    have hdet : Determines N.graph (N.ancestralArcs ((Finset.univ : Finset X) : Set X)) v N.leaf Q := by
      rw [hanc]
      exact hd
    -- one taxon from each component: a largest set containing `Q` with no two in one component
    have hmemq : Q ∈ Finset.univ.powerset.filter fun R => Q ⊆ R ∧ Determines N.graph Set.univ v N.leaf R :=
      Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (Finset.subset_univ _), Finset.Subset.refl _, hd⟩
    obtain ⟨R, hqR, hmem, hmax⟩ := Finset.exists_le_maximal _ hmemq
    obtain ⟨-, -, hdetR⟩ := Finset.mem_filter.mp hmem
    have hcov : ∀ x, ∃ r ∈ R, N.graph.Walks (Set.univ \ incidentCuts N.graph Set.univ v) (N.leaf x) (N.leaf r) := by
      intro x
      by_contra hno
      push Not at hno
      have hins : insert x R ∈ Finset.univ.powerset.filter fun R => Q ⊆ R ∧ Determines N.graph Set.univ v N.leaf R := by
        refine Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (Finset.subset_univ _),
          hqR.trans (Finset.subset_insert _ _), fun s hs t ht hst hw => ?_⟩
        rcases Finset.mem_insert.mp hs with rfl | hs' <;> rcases Finset.mem_insert.mp ht with rfl | ht'
        · exact hst rfl
        · exact hno t ht' hw
        · exact hno s hs' (N.graph.walks_symm hw)
        · exact hdetR s hs' t ht' hst hw
      have hxR : x ∈ R := hmax hins (Finset.subset_insert _ _) (Finset.mem_insert_self _ _)
      exact hno x hxR .refl
    have hR4 : 4 ≤ R.card := h4 ▸ Finset.card_le_card hqR
    have hRnt : (R : Set X).Nontrivial := Finset.one_lt_card_iff_nontrivial.mp (by omega)
    refine ⟨R, hqR, isDeterminedBy_blobOf_iff.mpr ⟨by omega, hdetR⟩, ?_, hRnt, ?_⟩
    · intro x
      obtain ⟨r, hr, hw⟩ := hcov x
      refine ⟨r, hr, ?_⟩
      rwa [incidentCutEdges_blobOf, Set.compl_eq_univ_sdiff]
    · -- all edges of `ℬ` are retained
      have hcov' : ∀ x ∈ (Finset.univ : Finset X), ∃ r ∈ R, N.graph.Walks
          (N.ancestralArcs ((Finset.univ : Finset X) : Set X) \ incidentCuts N.graph (N.ancestralArcs ((Finset.univ : Finset X) : Set X)) v)
          (N.leaf x) (N.leaf r) := by
        intro x _
        rw [hanc]
        exact hcov x
      have hsub : ((R : Finset X) : Set X) ⊆ ((Finset.univ : Finset X) : Set X) := by
        rw [huniv]
        exact Set.subset_univ _
      have harcs : blobArcsIn N.graph (N.ancestralArcs ((Finset.univ : Finset X) : Set X)) v ⊆ N.ancestralArcs (R : Set X) := by
        intro f hf
        obtain ⟨r, hr, hreach⟩ := exists_reaches_rep hP hv (Finset.subset_univ Q) h3 hdet (Finset.subset_univ R) hcov'
          (Relation.ReflTransGen.tail hf.2 ⟨f, hf.1, Or.inl ⟨rfl, rfl⟩⟩)
        exact ⟨r, Finset.mem_coe.mpr hr, hreach⟩
      have hblob : ∀ x, SameBlobIn N.graph (N.ancestralArcs ((Finset.univ : Finset X) : Set X)) v x →
          SameBlobIn N.graph (N.ancestralArcs (R : Set X)) v x := fun x hx =>
        sameBlobIn_of_isBridgelessSubgraph (isBridgelessSubgraph_blob v) harcs Relation.ReflTransGen.refl hx
      obtain ⟨r, hr, hreach⟩ := exists_reaches_rep hP hv (Finset.subset_univ Q) h3 hdet (Finset.subset_univ R) hcov'
        Relation.ReflTransGen.refl
      exact (Bridges.isBlobQuartetOnInduced_iff hN (R : Set X) hRnt (Finset.coe_subset.mpr hqR) h4).mpr
        ⟨v, ⟨r, Finset.mem_coe.mpr hr, hreach⟩, hdet.of_subset (N.ancestralArcs_mono hsub) hblob⟩

end Induced

end AllmanEtAl2023
