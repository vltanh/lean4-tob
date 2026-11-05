module

public import Basic.Level1Blobs
public import Basic.Wedge
public import Phylogenetics.Network.Cuts
public import Phylogenetics.Network.Quartets
public import Phylogenetics.Tree.Splits

/-!
# Blocks at a blob of a level-1 network, and treelike sets of four taxa

The blocks at the blob of a vertex `v` are the classes of taxa that stay joined when the blob is deleted
(`TOBQMC.SameBlock`, `Level1.block`); each is the side of a cut edge (`Level1.hasCutSplit_block`). Four taxa are
treelike exactly when a cut edge of the union of the wedge paths between them induces a `2|2` split
(`Level1.isTreelike_iff_hasWedgeCutSplit`).

At a blob of a binary level-1 network with reticulation `h`, four taxa in distinct blocks are treelike exactly when
none of them is below `h`: `Level1.not_isTreelike_of_distinct` and `Level1.isTreelike_of_not_below`, two of the
three cases of TOB-QMC's Lemma 4, which `TOBQMC.lemma4` in `src/TOBQMC/Level1.lean` assembles. At most one of the
taxa is below `h` (`Level1.existsUnique_below`). NANUQ's Proposition 9
(`src/External/AllmanBanosRhodes2019/Proposition9.lean`) uses these facts too.
-/

@[expose] public noncomputable section

open Phylogenetics Phylogenetics.RootedNetwork Finset
open scoped Classical

namespace TOBQMC

variable {V E X : Type*} [Fintype X] [DecidableEq X] {N : RootedNetwork V E X}

/-- Two taxa are in the same block of the partition `Part` at the blob of `v`: they remain
joined when the blob is deleted. -/
def SameBlock (N : RootedNetwork V E X) (v : V) (x y : X) : Prop :=
  Relation.ReflTransGen (fun a b => ¬ N.graph.blobSetoid v a ∧ ¬ N.graph.blobSetoid v b ∧
    ∃ e, (N.graph.source e = a ∧ N.graph.target e = b) ∨ (N.graph.source e = b ∧ N.graph.target e = a))
    (N.leaf x) (N.leaf y)

variable [Fintype V] [Fintype E]

namespace Level1

/-! ### Blocks and cut sides -/

variable {v : V} {x y : X}

omit [Fintype V] [Fintype E] in
omit [Fintype X] [DecidableEq X] in
theorem sameBlock_symm (h : SameBlock N v x y) : SameBlock N v y x := blockWalk_symm h

/-- The block of `x` at the blob of `v`. -/
def block (N : RootedNetwork V E X) (v : V) (x : X) : Finset X :=
  univ.filter fun z => SameBlock N v x z

omit [DecidableEq X] [Fintype V] [Fintype E] in
theorem mem_block {z : X} : z ∈ block N v x ↔ SameBlock N v x z := by
  simp [block]

omit [Fintype V] [Fintype E] in
omit [DecidableEq X] in
/-- A block at a blob is the side of a cut edge. -/
theorem hasCutSplit_block (hN : N.IsPhylogenetic) (hx : ¬ N.graph.blobSetoid v (N.leaf x)) :
    N.HasCutSplit (block N v x : Set X) := by
  obtain ⟨e, _, hS, _⟩ := exists_blockWalk_cut hN hx
  refine ⟨e, {u | BlockWalk N v (N.leaf x) u}, hS, ?_⟩
  ext z
  simp only [Set.mem_preimage, Set.mem_ofPred_eq, mem_coe, mem_block]
  rfl

omit [Fintype X] [DecidableEq X] [Fintype V] [Fintype E] in
/-- A singleton is the side of the pendant arc. -/
theorem hasCutSplit_singleton (hN : N.IsPhylogenetic) (x : X) :
    N.HasCutSplit (({x} : Finset X) : Set X) := by
  have := hN.finite_arcs
  have h1 := hN.leaf_indegree x
  rw [DirectedMultigraph.indegree, Set.ncard_eq_one] at h1
  obtain ⟨e, he⟩ := h1
  have hmem : ∀ f, N.graph.target f = N.leaf x ↔ f = e := by
    intro f
    have : f ∈ {e | N.graph.target e = N.leaf x} ↔ f ∈ ({e} : Set E) := by rw [he]
    exact this
  have het : N.graph.target e = N.leaf x := (hmem e).mpr rfl
  have h0 := (hN.leaves (N.leaf x)).mpr ⟨x, rfl⟩
  have hno := (DirectedMultigraph.outdegree_eq_zero_iff _ _).mp h0
  refine ⟨e, {N.leaf x}, fun f => ⟨?_, ?_⟩, ?_⟩
  · rintro (⟨hs, _⟩ | ⟨ht, _⟩)
    · exact absurd hs (hno f)
    · exact (hmem f).mp ht
  · rintro rfl
    refine Or.inr ⟨het, ?_⟩
    intro hs
    exact hno f hs
  · ext z
    simp [hN.leaf_injective.eq_iff]

omit [Fintype V] [Fintype E] in
theorem mem_treeOfBlobs_compl {A : Finset X} (hA : A ∈ treeOfBlobs N) : Aᶜ ∈ treeOfBlobs N := by
  simp only [treeOfBlobs, mem_filter, mem_univ, true_and] at hA ⊢
  refine ⟨hA.2.1, by rw [compl_compl]; exact hA.1, ?_⟩
  rw [coe_compl, hasCutSplit_compl]
  exact hA.2.2

omit [Fintype V] [Fintype E] in
theorem mem_treeOfBlobs_of_hasCutSplit {A : Finset X} (h₁ : A.Nonempty) (h₂ : Aᶜ.Nonempty)
    (h : N.HasCutSplit (A : Set X)) : A ∈ treeOfBlobs N := by
  simp only [treeOfBlobs, mem_filter, mem_univ, true_and]
  exact ⟨h₁, h₂, h⟩

/-! ### Treelikeness -/

omit [Fintype V] [Fintype E] in
/-- A cut-edge split with two taxa on each side makes the taxa treelike. -/
theorem isTreelike_of_hasCutSplitOn {Y P : Finset X} (hY : Y.card = 4) (hPY : P ⊆ Y)
    (hP : P.card = 2) (h : N.HasCutSplitOn (Y : Set X) (P : Set X)) : IsTreelike N Y := by
  have hQ : (Y \ P).card = 2 := by
    rw [card_sdiff_of_subset hPY]
    omega
  have hne : P ≠ Y \ P := by
    intro heq
    obtain ⟨a, ha⟩ := card_pos.mp (by omega : 0 < P.card)
    have h2 : a ∈ Y \ P := heq ▸ ha
    exact (mem_sdiff.mp h2).2 ha
  let s : QuartetTree X := ⟨{P, Y \ P}, by
    refine ⟨card_pair hne, ?_, ?_⟩
    · intro C hC
      rcases mem_insert.mp hC with rfl | hC
      · exact hP
      · rw [mem_singleton.mp hC]
        exact hQ
    · intro C hC D hD hCD
      rcases mem_insert.mp hC with rfl | hC <;> rcases mem_insert.mp hD with rfl | hD
      · exact absurd rfl hCD
      · rw [mem_singleton.mp hD]
        exact disjoint_sdiff
      · rw [mem_singleton.mp hC]
        exact sdiff_disjoint
      · rw [mem_singleton.mp hC, mem_singleton.mp hD] at hCD
        exact absurd rfl hCD⟩
  have hs : s.taxa = Y := by
    simp only [QuartetTree.taxa, s, sup_insert, sup_singleton, id, sup_eq_union]
    exact union_sdiff_of_subset hPY
  refine ⟨s, by simp [treesOn, hs], P, by simp [s], ?_⟩
  rw [hs]
  exact h

omit [Fintype V] [Fintype E] in
/-- **The representation bridge on four taxa.** `Y` is treelike exactly when a cut edge of the subnetwork on
`Y`, the union of the wedge paths between its taxa, induces a `2|2` split (TOB-QMC writes that `N⁻|Y`
contains no 4-blob). -/
theorem isTreelike_iff_hasWedgeCutSplit (hN : N.IsPhylogenetic) {Y : Finset X} (hY : Y.card = 4) :
    IsTreelike N Y ↔ ∃ P : Finset X, P ⊆ Y ∧ P.card = 2 ∧ N.HasWedgeCutSplit (Y : Set X) (P : Set X) := by
  have hne : ∀ {P : Finset X}, P ⊆ Y → P.card = 2 → ((Y : Set X) ∩ (P : Set X)).Nonempty ∧
      ((Y : Set X) \ (P : Set X)).Nonempty := by
    intro P hPY hP
    obtain ⟨a, ha⟩ := card_pos.mp (by omega : 0 < P.card)
    obtain ⟨b, hb⟩ := card_pos.mp (by rw [card_sdiff_of_subset hPY]; omega : 0 < (Y \ P).card)
    obtain ⟨hbY, hbP⟩ := mem_sdiff.mp hb
    exact ⟨⟨a, mem_coe.mpr (hPY ha), mem_coe.mpr ha⟩, ⟨b, mem_coe.mpr hbY, fun hc => hbP (mem_coe.mp hc)⟩⟩
  constructor
  · rintro ⟨s, hs, C, hC, hcut⟩
    have hsY : s.taxa = Y := (mem_filter.mp hs).2
    rw [hsY] at hcut
    have hCY : C ⊆ Y := by
      rw [← hsY]
      exact le_sup (f := id) hC
    have hC2 : C.card = 2 := s.2.2.1 C hC
    exact ⟨C, hCY, hC2, (hasWedgeCutSplit_iff_hasCutSplitOn hN (hne hCY hC2).1 (hne hCY hC2).2).mpr hcut⟩
  · rintro ⟨P, hPY, hP, hcut⟩
    exact isTreelike_of_hasCutSplitOn hY hPY hP
      ((hasWedgeCutSplit_iff_hasCutSplitOn hN (hne hPY hP).1 (hne hPY hP).2).mp hcut)

/-! ### Four taxa in distinct blocks: two cases of TOB-QMC's Lemma 4 -/

/-- Lemma 4, `⇐`: taxa in distinct blocks, one of them below the reticulation, are not treelike. The
wedge paths between them form the cycle of the blob, with all four taxa attached, so no cut edge of the
subnetwork on `Y` induces a `2|2` split (`not_hasWedgeCutSplit`). -/
theorem not_isTreelike_of_distinct (hN : N.IsPhylogenetic) (hBin : N.IsBinary) (hLevel : IsLevelOne N)
    {h : V} (hh : N.graph.blobSetoid v h) (hh₂ : 2 ≤ N.graph.indegree h) {Y : Finset X} (hY : Y.card = 4)
    (hdist : ∀ a ∈ Y, ∀ b ∈ Y, a ≠ b → ¬ SameBlock N v a b) {d : X} (hd : d ∈ Y)
    (hdh : N.graph.Reaches h (N.leaf d)) : ¬ IsTreelike N Y := by
  intro ht
  obtain ⟨P, hPY, hP, hcut⟩ := (isTreelike_iff_hasWedgeCutSplit hN hY).mp ht
  exact not_hasWedgeCutSplit hN hBin hLevel hh hh₂ hY hdist hd hdh hPY hP hcut

/-- Lemma 4, `⇒`, no taxon below the reticulation: there is only one wedge path between two attachments
(`wedgePath_unique`), and no wedge path includes the reticulation, so a single path connects the
attachments, and their order along it gives a cut edge of the subnetwork with a `2|2` split
(`exists_hasWedgeCutSplit`). -/
theorem isTreelike_of_not_below (hN : N.IsPhylogenetic) (hBin : N.IsBinary) (hLevel : IsLevelOne N)
    {h : V} (hh : N.graph.blobSetoid v h) (hh₂ : 2 ≤ N.graph.indegree h) {Y : Finset X} (hY : Y.card = 4)
    (hdist : ∀ a ∈ Y, ∀ b ∈ Y, a ≠ b → ¬ SameBlock N v a b)
    (hno : ∀ a ∈ Y, ¬ N.graph.Reaches h (N.leaf a)) : IsTreelike N Y :=
  (isTreelike_iff_hasWedgeCutSplit hN hY).mpr
    (exists_hasWedgeCutSplit hN hBin hLevel hh hh₂ hY hdist hno)

omit [Fintype X] in
/-- In distinct blocks, at most one taxon is below the reticulation: the case of two or more taxa below
it, which the paper's proof of `⇒` does not treat (it states this fact only in the proof of Corollary 1). -/
theorem existsUnique_below (hN : N.IsPhylogenetic) (hBin : N.IsBinary) (hLevel : IsLevelOne N)
    {h : V} (hh : N.graph.blobSetoid v h) (hh₂ : 2 ≤ N.graph.indegree h) {Y : Finset X}
    (hdist : ∀ a ∈ Y, ∀ b ∈ Y, a ≠ b → ¬ SameBlock N v a b) {d : X} (hd : d ∈ Y)
    (hdh : N.graph.Reaches h (N.leaf d)) : ∃! a, a ∈ Y ∧ N.graph.Reaches h (N.leaf a) := by
  refine ⟨d, ⟨hd, hdh⟩, ?_⟩
  rintro a ⟨ha, hah⟩
  by_contra hne
  exact hdist a ha d hd hne (blockWalk_of_below_reticulation hN hBin hLevel hh hh₂ hah hdh)

end Level1

end TOBQMC
