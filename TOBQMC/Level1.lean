module

public import Basic.Phylogenetics.NetworkCuts
public import Basic.Phylogenetics.TreeSplits
public import External.HuberEtAl2025.Theorem51
public import TOBQMC.Level1Blobs
public import TOBQMC.Wedge

/-!
# TOB-QMC §4.3: false positives in a refinement, with a linear number of tests, for level-1 networks

Lemma 2, Lemma 4, Corollary 1, Theorem 2 and the 3-fix-1-alter search. Definition 2 is `IsDisjointCover` in
`Basic/Phylogenetics/Defs.lean`.
A taxon set's oracle answer *treelike* is `IsTreelike N Y`: the restriction has a cut edge with a
non-trivial split, equivalently no 4-blob. On four taxa this is a cut edge of the union of the wedge
paths between them (`Level1.isTreelike_iff_hasWedgeCutSplit`), which is where Lemma 4 is proved.
-/

@[expose] public noncomputable section

open Phylogenetics Phylogenetics.RootedNetwork Finset
open scoped Classical

namespace TOBQMC

variable {V E X : Type*} [Fintype X] [DecidableEq X] {N : RootedNetwork V E X}

omit [Fintype X] in
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
theorem hasCutSplit_block (hN : N.IsPhylogenetic) (hx : ¬ SameBlob N v (N.leaf x)) :
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

/-- The sides of an unrooted tree are nonempty and proper. -/
theorem nonempty_of_mem_isUnrootedTree {B : Finset (Finset X)} (hB : IsUnrootedTree B)
    {A : Finset X} (hA : A ∈ B) : A.Nonempty ∧ Aᶜ.Nonempty := by
  obtain ⟨H, hH, rfl⟩ := hB
  have key : ∀ C ∈ H.erase univ, C.Nonempty ∧ Cᶜ.Nonempty := by
    intro C hC
    obtain ⟨h1, h2⟩ := mem_erase.mp hC
    refine ⟨hH.2.2.1 C h2, ?_⟩
    rw [nonempty_iff_ne_empty, Ne, compl_eq_empty_iff]
    exact h1
  rcases mem_union.mp hA with h | h
  · exact key A h
  · obtain ⟨C, hC, rfl⟩ := mem_image.mp h
    obtain ⟨h1, h2⟩ := key C hC
    exact ⟨h2, by rwa [compl_compl]⟩

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

omit [Fintype V] [Fintype E] in
theorem refinesBlob_compl {A : Finset X} (h : RefinesBlob N A v) : RefinesBlob N Aᶜ v := by
  intro a b hab
  simp only [mem_compl, not_iff_not]
  exact h a b hab

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

omit [Fintype V] [Fintype E] in
/-- A cut side with two taxa of `Y` in it and the other two outside: by **Lemma 2**, `Y` is treelike. -/
theorem isTreelike_of_cut_side (hN : N.IsPhylogenetic) {C P Y : Finset X}
    (hC : N.HasCutSplit (C : Set X)) (hY : Y.card = 4) (hPY : P ⊆ Y) (hP : P.card = 2)
    (hin : ∀ a ∈ P, a ∈ C) (hout : ∀ a ∈ Y, a ∉ P → a ∉ C) : IsTreelike N Y := by
  obtain ⟨a₁, a₂, hne, rfl⟩ := card_eq_two.mp hP
  have hQ : (Y \ {a₁, a₂}).card = 2 := by
    rw [card_sdiff_of_subset hPY, hY, card_pair hne]
  obtain ⟨b₁, b₂, -, hb⟩ := card_eq_two.mp hQ
  have hb₁ : b₁ ∈ Y \ {a₁, a₂} := by rw [hb]; simp
  have hb₂ : b₂ ∈ Y \ {a₁, a₂} := by rw [hb]; simp
  have hcut := lemma2 hN hC (hin a₁ (by simp)) (hin a₂ (by simp))
    (hout b₁ (mem_sdiff.mp hb₁).1 (mem_sdiff.mp hb₁).2)
    (hout b₂ (mem_sdiff.mp hb₂).1 (mem_sdiff.mp hb₂).2)
  have hYeq : ({a₁, a₂, b₁, b₂} : Finset X) = Y := by
    rw [← union_sdiff_of_subset hPY, hb]
    ext z
    simp only [mem_union, mem_insert, mem_singleton]
    tauto
  rw [hYeq] at hcut
  exact isTreelike_of_hasCutSplitOn hY hPY (card_pair hne) hcut

omit [Fintype V] [Fintype E] in
/-- **Lemma 2 applied to an edge of the tree of blobs**: all four-taxon sets around it are treelike. -/
theorem isTreelike_of_hasCutSplit (hN : N.IsPhylogenetic) {A Y : Finset X}
    (hA : N.HasCutSplit (A : Set X)) (hY : Y.card = 4) (hYA : (A ∩ Y).card = 2) :
    IsTreelike N Y :=
  isTreelike_of_cut_side hN hA hY inter_subset_right hYA (fun _ ha => (mem_inter.mp ha).1)
    fun _ ha hna hA' => hna (mem_inter.mpr ⟨hA', ha⟩)

/-! ### The two directions of Lemma 4 -/

/-- Lemma 4, `⇐`: taxa in distinct blocks, one of them below the reticulation, are not treelike. The
wedge paths between them form the cycle of the blob, with all four taxa attached, so no cut edge of the
subnetwork on `Y` induces a `2|2` split (`not_hasWedgeCutSplit`). -/
theorem not_isTreelike_of_distinct (hN : N.IsPhylogenetic) (hBin : N.IsBinary) (hLevel : IsLevelOne N)
    {h : V} (hh : SameBlob N v h) (hh₂ : 2 ≤ N.graph.indegree h) {Y : Finset X} (hY : Y.card = 4)
    (hdist : ∀ a ∈ Y, ∀ b ∈ Y, a ≠ b → ¬ SameBlock N v a b) {d : X} (hd : d ∈ Y)
    (hdh : N.graph.Reaches h (N.leaf d)) : ¬ IsTreelike N Y := by
  intro ht
  obtain ⟨P, hPY, hP, hcut⟩ := (isTreelike_iff_hasWedgeCutSplit hN hY).mp ht
  exact not_hasWedgeCutSplit hN hBin hLevel hh hh₂ hY hdist hd hdh hPY hP hcut

omit [Fintype V] [Fintype E] in
/-- Lemma 4, `⇒`, same block: two taxa in one block, with the other two on the other side of the edge,
are separated by the cut edge of the block, so `Y` is treelike by **Lemma 2**. -/
theorem isTreelike_of_sameBlock (hN : N.IsPhylogenetic) {A Y : Finset X} (hv : RefinesBlob N A v)
    (hY : Y.card = 4) (hYA : (A ∩ Y).card = 2) (hx : x ∈ Y) (hy : y ∈ Y) (hxy : x ≠ y)
    (hs : SameBlock N v x y) : IsTreelike N Y := by
  have hblob : ¬ SameBlob N v (N.leaf x) :=
    not_sameBlob_of_blockWalk_of_ne hs (fun h => hxy (hN.leaf_injective h))
  have hYAc : (Y \ A).card = 2 := by
    have := card_inter_add_card_sdiff Y A
    rw [inter_comm] at this
    omega
  refine isTreelike_of_cut_side hN (hasCutSplit_block hN hblob) hY (P := {x, y}) ?_ (card_pair hxy)
    ?_ ?_
  · intro a ha
    rcases mem_insert.mp ha with rfl | ha
    · exact hx
    · rw [mem_singleton.mp ha]
      exact hy
  · intro a ha
    rcases mem_insert.mp ha with rfl | ha
    · exact mem_block.mpr Relation.ReflTransGen.refl
    · rw [mem_singleton.mp ha]
      exact mem_block.mpr hs
  · intro z hz hzP hzB
    have hzx : z ≠ x := fun h => hzP (by simp [h])
    have hzy : z ≠ y := fun h => hzP (by simp [h])
    have h1 := hv x z (mem_block.mp hzB)
    have h2 := hv x y hs
    have hthree : ({x, y, z} : Finset X).card = 3 := by
      rw [card_eq_three]
      exact ⟨x, y, z, hxy, hzx.symm, hzy.symm, rfl⟩
    by_cases hxA : x ∈ A
    · have hsub : ({x, y, z} : Finset X) ⊆ A ∩ Y := by
        intro a ha
        simp only [mem_insert, mem_singleton] at ha
        rcases ha with rfl | rfl | rfl
        · exact mem_inter.mpr ⟨hxA, hx⟩
        · exact mem_inter.mpr ⟨h2.mp hxA, hy⟩
        · exact mem_inter.mpr ⟨h1.mp hxA, hz⟩
      have := card_le_card hsub
      omega
    · have hsub : ({x, y, z} : Finset X) ⊆ Y \ A := by
        intro a ha
        simp only [mem_insert, mem_singleton] at ha
        rcases ha with rfl | rfl | rfl
        · exact mem_sdiff.mpr ⟨hx, hxA⟩
        · exact mem_sdiff.mpr ⟨hy, fun h => hxA (h2.mpr h)⟩
        · exact mem_sdiff.mpr ⟨hz, fun h => hxA (h1.mpr h)⟩
      have := card_le_card hsub
      omega

/-- Lemma 4, `⇒`, no taxon below the reticulation: there is only one wedge path between two attachments
(`wedgePath_unique`), and no wedge path includes the reticulation, so a single path connects the
attachments, and their order along it gives a cut edge of the subnetwork with a `2|2` split
(`exists_hasWedgeCutSplit`). -/
theorem isTreelike_of_not_below (hN : N.IsPhylogenetic) (hBin : N.IsBinary) (hLevel : IsLevelOne N)
    {h : V} (hh : SameBlob N v h) (hh₂ : 2 ≤ N.graph.indegree h) {Y : Finset X} (hY : Y.card = 4)
    (hdist : ∀ a ∈ Y, ∀ b ∈ Y, a ≠ b → ¬ SameBlock N v a b)
    (hno : ∀ a ∈ Y, ¬ N.graph.Reaches h (N.leaf a)) : IsTreelike N Y :=
  (isTreelike_iff_hasWedgeCutSplit hN hY).mpr
    (exists_hasWedgeCutSplit hN hBin hLevel hh hh₂ hY hdist hno)

omit [Fintype X] in
/-- In distinct blocks, at most one taxon is below the reticulation: the case of two or more taxa below
it, which the paper's proof of `⇒` does not treat (it states this fact only in the proof of Corollary 1). -/
theorem existsUnique_below (hN : N.IsPhylogenetic) (hBin : N.IsBinary) (hLevel : IsLevelOne N)
    {h : V} (hh : SameBlob N v h) (hh₂ : 2 ≤ N.graph.indegree h) {Y : Finset X}
    (hdist : ∀ a ∈ Y, ∀ b ∈ Y, a ≠ b → ¬ SameBlock N v a b) {d : X} (hd : d ∈ Y)
    (hdh : N.graph.Reaches h (N.leaf d)) : ∃! a, a ∈ Y ∧ N.graph.Reaches h (N.leaf a) := by
  refine ⟨d, ⟨hd, hdh⟩, ?_⟩
  rintro a ⟨ha, hah⟩
  by_contra hne
  exact hdist a ha d hd hne (blockWalk_of_below_reticulation hN hBin hLevel hh hh₂ hah hdh)

/-! ### False positives -/

/-- A bridge with taxa of both sides of `A` below it. -/
def Mixed (N : RootedNetwork V E X) (A : Finset X) (g : E) : Prop :=
  IsBridge N g ∧ (∃ a ∈ A, N.IsBelow g a) ∧ ∃ b, b ∉ A ∧ N.IsBelow g b

omit [Fintype V] [Fintype E] in
omit [Fintype X] [DecidableEq X] in
/-- Two taxa in the same block: the block's cut edge either leaves the blob, with the taxa below it, or
enters the blob, with the taxa and the root on its far side. -/
theorem exit_or_entry_of_sameBlock (hN : N.IsPhylogenetic) (hxy : SameBlock N v x y) (hne : x ≠ y) :
    ∃ e, IsBridge N e ∧
      ((SameBlob N v (N.graph.source e) ∧ N.IsBelow e x ∧ N.IsBelow e y) ∨
        (SameBlob N v (N.graph.target e) ∧ BlockWalk N v (N.leaf x) N.root ∧
          ¬ N.IsBelow e x ∧ ¬ N.IsBelow e y)) := by
  have hx : ¬ SameBlob N v (N.leaf x) :=
    not_sameBlob_of_blockWalk_of_ne hxy (fun h => hne (hN.leaf_injective h))
  obtain ⟨e, hb, hS, hor⟩ := exists_blockWalk_cut hN hx
  refine ⟨e, hb, ?_⟩
  rcases hor with ⟨h1, -⟩ | ⟨h1, h2⟩
  · exact Or.inl ⟨h1, reaches_of_blockWalk_of_exit hN hx hS h1 .refl,
      reaches_of_blockWalk_of_exit hN hx hS h1 hxy⟩
  · have ht : ¬ BlockWalk N v (N.leaf x) (N.graph.target e) :=
      fun hc => not_sameBlob_of_blockWalk hx hc h1
    refine Or.inr ⟨h1, blockWalk_root_of_entry hN hS h2, fun hc => ?_, fun hc => ?_⟩
    · exact not_reaches_of_blockWalk_of_entry hS h2 ht hc .refl
    · exact not_reaches_of_blockWalk_of_entry hS h2 ht hc hxy

omit [Fintype V] [Fintype E] in
omit [Fintype X] [DecidableEq X] in
/-- Two bridges entering one blob coincide. -/
theorem eq_of_isBridge_of_sameBlob (hN : N.IsPhylogenetic) {e g : E} (he : IsBridge N e)
    (hg : IsBridge N g) (h : SameBlob N (N.graph.target g) (N.graph.target e)) : e = g := by
  by_contra hne
  have h1 := (isBridge_iff_reaches hN g).mp hg e hne (reaches_of_sameBlob hN hg h)
  have h2 := (isBridge_iff_reaches hN e).mp he g (Ne.symm hne)
    (reaches_of_sameBlob hN he (sameBlob_symm h))
  exact not_reaches_source hN e (h2.trans ((reaches_of_arc N g).trans h1))

omit [Fintype V] in
/-- **The blob refined by a false positive.** Take a lowest bridge with taxa of both sides of `A`
below it, or the root if there is none: the blocks at its blob do not straddle `A`. -/
theorem exists_refinesBlob (hN : N.IsPhylogenetic) {B : Finset (Finset X)} (hfam : IsSplitFamily B)
    (hTB : treeOfBlobs N ⊆ B) {A : Finset X} (hAB : A ∈ B) : ∃ v, RefinesBlob N A v := by
  have reduce : ∀ v, (∀ a b, SameBlock N v a b → a ∈ A → b ∉ A → False) → RefinesBlob N A v := by
    intro v hv a b hab
    constructor
    · intro ha
      by_contra hb
      exact hv a b hab ha hb
    · intro hb
      by_contra ha
      exact hv b a (sameBlock_symm hab) hb ha
  have hne : ∀ {a b : X}, a ∈ A → b ∉ A → a ≠ b := by
    rintro a b ha hb rfl
    exact hb ha
  by_cases hM : ∃ g, Mixed N A g
  · obtain ⟨g₀, hg₀⟩ := hM
    obtain ⟨u, ⟨g, hg, rfl⟩, hmin⟩ := exists_sink hN
      (S := N.graph.target '' {g | Mixed N A g}) ⟨_, g₀, hg₀, rfl⟩
    refine ⟨N.graph.target g, reduce _ fun a b hab ha hb => ?_⟩
    obtain ⟨e, heb, hor⟩ := exit_or_entry_of_sameBlock hN hab (hne ha hb)
    rcases hor with ⟨h1, hae, hbe⟩ | ⟨h1, -, hae, hbe⟩
    · -- the cut edge of the block is a lower mixed bridge
      refine hmin _ ⟨e, ⟨heb, ⟨a, ha, hae⟩, b, hb, hbe⟩, rfl⟩ ?_
      exact Relation.TransGen.tail' (reaches_of_sameBlob hN hg.1 h1) ⟨e, rfl, rfl⟩
    · -- the cut edge of the block is `g`, and its side is incompatible with `A`
      have heg := eq_of_isBridge_of_sameBlob hN heb hg.1 h1
      subst heg
      obtain ⟨-, ⟨p, hpA, hp⟩, q, hqA, hq⟩ := hg
      set P : Finset X := univ.filter fun z => N.IsBelow e z with hP
      have hmem : ∀ z, z ∈ P ↔ N.IsBelow e z := fun z => by simp [hP]
      have hcut : N.HasCutSplit (P : Set X) := by
        refine ⟨e, {u | N.graph.Reaches (N.graph.target e) u}, isBridge_crosses_iff hN heb, ?_⟩
        ext z
        simp only [Set.mem_preimage, Set.mem_ofPred_eq, mem_coe, hmem]
        rfl
      have hPB : P ∈ B := hTB (mem_treeOfBlobs_of_hasCutSplit ⟨p, (hmem p).mpr hp⟩
        ⟨a, mem_compl.mpr fun h => hae ((hmem a).mp h)⟩ hcut)
      rcases hfam.compatible P hPB A hAB with h | h | h | h
      · exact hqA (h ((hmem q).mpr hq))
      · exact hae ((hmem a).mp (h ha))
      · exact disjoint_left.mp h ((hmem p).mpr hp) hpA
      · have hb' : b ∈ P ∪ A := h ▸ mem_univ b
        rcases mem_union.mp hb' with h' | h'
        · exact hbe ((hmem b).mp h')
        · exact hb h'
  · refine ⟨N.root, reduce _ fun a b hab ha hb => ?_⟩
    obtain ⟨e, heb, hor⟩ := exit_or_entry_of_sameBlock hN hab (hne ha hb)
    rcases hor with ⟨-, hae, hbe⟩ | ⟨-, hr, -, -⟩
    · exact hM ⟨e, heb, ⟨a, ha, hae⟩, b, hb, hbe⟩
    · have hx : ¬ SameBlob N N.root (N.leaf a) :=
        not_sameBlob_of_blockWalk_of_ne hab (fun h => hne ha hb (hN.leaf_injective h))
      exact not_sameBlob_of_blockWalk hx hr .refl

omit [Fintype V] [Fintype E] in
omit [DecidableEq X] in
/-- A side that is not a cut side, refining the blob, contains two blocks. -/
theorem exists_not_sameBlock (hN : N.IsPhylogenetic) {C : Finset X} (hC : RefinesBlob N C v)
    (hcut : ¬ N.HasCutSplit (C : Set X)) (h2 : 2 ≤ C.card) {a : X} (ha : a ∈ C) :
    ∃ a' ∈ C, ¬ SameBlock N v a a' := by
  by_contra hall
  push Not at hall
  by_cases hb : SameBlob N v (N.leaf a)
  · obtain ⟨a', ha', hne⟩ := exists_mem_ne (by omega : 1 < C.card) a
    exact not_sameBlob_of_blockWalk_of_ne (hall a' ha')
      (fun h => hne (hN.leaf_injective h).symm) hb
  · apply hcut
    have hset : block N v a = C := by
      ext z
      rw [mem_block]
      exact ⟨fun hz => (hC a z hz).mp ha, fun hz => hall z hz⟩
    rw [← hset]
    exact hasCutSplit_block hN hb

omit [Fintype V] [Fintype E] in
/-- Four taxa in distinct blocks, through a given taxon `d`, two on each side of a side `C` of a false
positive (TOB-QMC, proof of Corollary 1: each side contains at least two blocks). -/
theorem exists_quartet_through (hN : N.IsPhylogenetic) {C : Finset X} (hC : RefinesBlob N C v)
    (hcut : ¬ N.HasCutSplit (C : Set X)) (h2 : 2 ≤ C.card) (h2' : 2 ≤ Cᶜ.card) {d : X} (hd : d ∈ C) :
    ∃ Y : Finset X, d ∈ Y ∧ Y.card = 4 ∧ (C ∩ Y).card = 2 ∧
      ∀ a ∈ Y, ∀ b ∈ Y, a ≠ b → ¬ SameBlock N v a b := by
  obtain ⟨d', hd', hdd⟩ := exists_not_sameBlock hN hC hcut h2 hd
  have hcut' : ¬ N.HasCutSplit (Cᶜ : Finset X) := by
    rwa [coe_compl, hasCutSplit_compl]
  obtain ⟨e₁, he₁⟩ := card_pos.mp (by omega : 0 < Cᶜ.card)
  obtain ⟨e₂, he₂, hee⟩ := exists_not_sameBlock hN (refinesBlob_compl hC) hcut' h2' he₁
  have he₁' : e₁ ∉ C := mem_compl.mp he₁
  have he₂' : e₂ ∉ C := mem_compl.mp he₂
  have across : ∀ {a b : X}, a ∈ C → b ∉ C → ¬ SameBlock N v a b ∧ ¬ SameBlock N v b a := by
    intro a b ha hb
    exact ⟨fun h => hb ((hC a b h).mp ha), fun h => hb ((hC b a h).mpr ha)⟩
  have ne_of : ∀ {a b : X}, ¬ SameBlock N v a b → a ≠ b := by
    rintro a b h rfl
    exact h Relation.ReflTransGen.refl
  have hne₁ : d ≠ d' := ne_of hdd
  have hne₂ : e₁ ≠ e₂ := ne_of hee
  have hne₃ : ∀ {a b : X}, a ∈ C → b ∉ C → a ≠ b := fun ha hb => ne_of (across ha hb).1
  refine ⟨{d, d', e₁, e₂}, by simp, ?_, ?_, ?_⟩
  · rw [card_insert_of_notMem, card_insert_of_notMem, card_pair hne₂]
    · simp only [mem_insert, mem_singleton, not_or]
      exact ⟨hne₃ hd' he₁', hne₃ hd' he₂'⟩
    · simp only [mem_insert, mem_singleton, not_or]
      exact ⟨hne₁, hne₃ hd he₁', hne₃ hd he₂'⟩
  · have : C ∩ {d, d', e₁, e₂} = {d, d'} := by
      ext z
      simp only [mem_inter, mem_insert, mem_singleton]
      constructor
      · rintro ⟨hz, rfl | rfl | rfl | rfl⟩
        · exact Or.inl rfl
        · exact Or.inr rfl
        · exact absurd hz he₁'
        · exact absurd hz he₂'
      · rintro (rfl | rfl)
        · exact ⟨hd, Or.inl rfl⟩
        · exact ⟨hd', Or.inr (Or.inl rfl)⟩
    rw [this, card_pair hne₁]
  · have h12 := hdd
    have h13 := (across hd he₁').1
    have h14 := (across hd he₂').1
    have h23 := (across hd' he₁').1
    have h24 := (across hd' he₂').1
    have h34 := hee
    have h21 : ¬ SameBlock N v d' d := fun h => h12 (sameBlock_symm h)
    have h31 := (across hd he₁').2
    have h41 := (across hd he₂').2
    have h32 := (across hd' he₁').2
    have h42 := (across hd' he₂').2
    have h43 : ¬ SameBlock N v e₂ e₁ := fun h => h34 (sameBlock_symm h)
    simp only [mem_insert, mem_singleton]
    rintro a (rfl | rfl | rfl | rfl) b (rfl | rfl | rfl | rfl) hab <;>
      first | exact absurd rfl hab | assumption

end Level1

open Level1

omit [Fintype V] in
/-- An edge of a refinement of the tree of blobs of a binary network that is not in the tree of blobs
refines a non-trivial blob, with a reticulation vertex (the premise of Lemma 4, which the paper takes
"by the setting"). The blob is the one below a lowest bridge with taxa of both sides of the edge below
it, or that of the root when there is no such bridge (`exists_refinesBlob`); a trivial blob would be a
vertex with at least four blocks, and at most two children (`exists_arc_two_below`). -/
theorem exists_blob_of_false_positive (hN : N.IsPhylogenetic) (hBin : N.IsBinary)
    {B : Finset (Finset X)} (hB : IsUnrootedTree B) (hTB : treeOfBlobs N ⊆ B) {A : Finset X}
    (hA : A ∈ internalSides B) (hAT : A ∉ treeOfBlobs N) :
    ∃ v h, RefinesBlob N A v ∧ SameBlob N v h ∧ 2 ≤ N.graph.indegree h := by
  obtain ⟨hAB, h2, h2'⟩ := mem_filter.mp hA
  have hcard : 2 ≤ Fintype.card X := h2.trans (card_le_univ A)
  have hfam := (isUnrootedTree_iff hcard B).mp hB
  obtain ⟨v, hv⟩ := exists_refinesBlob hN hfam hTB hAB
  refine ⟨v, ?_⟩
  rcases exists_reticulation_or_forall_isBridge hN v with ⟨h, hh, hh₂⟩ | hall
  · exact ⟨h, hv, hh, hh₂⟩
  · -- a trivial blob would be a vertex with four blocks and at most two children
    exfalso
    have hcut : ¬ N.HasCutSplit (A : Set X) := fun hc =>
      hAT (mem_treeOfBlobs_of_hasCutSplit (card_pos.mp (by omega)) (card_pos.mp (by omega)) hc)
    obtain ⟨d, hd⟩ := card_pos.mp (by omega : 0 < A.card)
    obtain ⟨Y, -, hY, -, hdist⟩ := exists_quartet_through hN hv hcut h2 h2' hd
    obtain ⟨k, hs, ht, -⟩ := exists_arc_two_below hN hBin hY hdist
    have h1 := eq_of_sameBlob_of_forall_isBridge hall hs
    have h2 := eq_of_sameBlob_of_forall_isBridge hall ht
    exact target_ne_source hN k (h2.trans h1.symm)

/-- **Lemma 4** (`tob2025:lemma4`). Let `N` be binary and level-1, `B` a refinement of its tree of blobs,
`A` the side of an edge of `B` not in the tree of blobs, refining the non-trivial blob of `v`, whose
reticulation vertex is `h`. For a four-taxon set `Y` around the edge, the restriction of the network to
`Y` has a 4-blob if and only if the taxa of `Y` lie in distinct blocks at the blob and exactly one
of them descends from `h`.

The proof is the paper's, on the subnetwork `N.wedgeArcs Y` of `TOBQMC/Wedge.lean`, the union of the
wedge paths between taxa of `Y`. Its cut edges with both sides nonempty are those of the network induced
on `Y` (`hasWedgeCutSplit_iff_hasCutSplitOn`, `hasWedgeCutSplit_iff_inducedNetwork_hasCutSplit`), so
`IsTreelike N Y` says that one of them induces a `2|2` split (`isTreelike_iff_hasWedgeCutSplit`).

`⇐`: the wedge paths from `h` to the attachments of the other taxa cover the blob
(`exactly_two_wedgePaths`), so the subnetwork contains a cycle with the four taxa attached, and has no cut
edge with a `2|2` split (`not_isTreelike_of_distinct`).

`⇒`: two taxa in one block are separated by the block's cut edge, and `Y` is treelike by **Lemma 2**
(`isTreelike_of_sameBlock`). With distinct blocks and no taxon below `h`, there is one wedge path between
two attachments (`wedgePath_unique`), and the order along the path gives the split
(`isTreelike_of_not_below`). The paper does not treat two or more taxa below `h`, which distinct blocks
exclude (`existsUnique_below`).

Of the hypotheses on the refinement, only `RefinesBlob` is used. -/
theorem lemma4 (hN : N.IsPhylogenetic) (hBin : N.IsBinary) (hLevel : IsLevelOne N) {A : Finset X}
    {v h : V} (hv : RefinesBlob N A v) (hh : SameBlob N v h) (hh₂ : 2 ≤ N.graph.indegree h)
    {Y : Finset X} (hY : Y.card = 4) (hYA : (A ∩ Y).card = 2) :
    ¬ IsTreelike N Y ↔
      (∀ x ∈ Y, ∀ y ∈ Y, x ≠ y → ¬ SameBlock N v x y) ∧
        ∃! x, x ∈ Y ∧ N.graph.Reaches h (N.leaf x) := by
  constructor
  · intro hnt
    have hdist : ∀ x ∈ Y, ∀ y ∈ Y, x ≠ y → ¬ SameBlock N v x y :=
      fun x hx y hy hxy hs => hnt (isTreelike_of_sameBlock hN hv hY hYA hx hy hxy hs)
    refine ⟨hdist, ?_⟩
    have hex : ∃ d ∈ Y, N.graph.Reaches h (N.leaf d) := by
      by_contra hno
      push Not at hno
      exact hnt (isTreelike_of_not_below hN hBin hLevel hh hh₂ hY hdist hno)
    obtain ⟨d, hd, hdh⟩ := hex
    exact existsUnique_below hN hBin hLevel hh hh₂ hdist hd hdh
  · rintro ⟨hdist, d, ⟨hd, hdh⟩, -⟩
    exact not_isTreelike_of_distinct hN hBin hLevel hh hh₂ hY hdist hd hdh

/-- **Corollary 1** (`tob2025:corollary1`). For a binary level-1 network and a binary refinement `B` of
its tree of blobs, an edge of `B` is in the tree of blobs exactly when the oracle answers treelike on
all four-taxon subsets around it. The false positive case follows the paper's observations: (1) the
descendants of the reticulation are in one block (`existsUnique_below`), and (3) each side contains at
least two blocks, which gives (2), at least four blocks. The paper derives (3) from `B` being binary; it
follows from the edge not being in the tree of blobs (`exists_not_sameBlock`). A taxon below the
reticulation and these blocks give a four-taxon subset meeting the conditions of **Lemma 4**
(`exists_quartet_through`). -/
theorem corollary1 (hN : N.IsPhylogenetic) (hBin : N.IsBinary) (hLevel : IsLevelOne N)
    {B : Finset (Finset X)} (hB : IsBinaryTree B) (hTB : treeOfBlobs N ⊆ B) {A : Finset X}
    (hA : A ∈ internalSides B) :
    A ∈ treeOfBlobs N ↔ ∀ Y : Finset X, Y.card = 4 → (A ∩ Y).card = 2 → IsTreelike N Y := by
  have hB' : IsUnrootedTree B := by
    obtain ⟨H, hH, hu, -⟩ := hB
    exact ⟨H, hH, hu⟩
  constructor
  · -- true positives: Lemma 2
    intro hAT Y hY hYA
    exact isTreelike_of_hasCutSplit hN (mem_filter.mp hAT).2.2.2 hY hYA
  · -- false positives: a four-taxon set meeting the conditions of Lemma 4
    intro hall
    by_contra hAT
    obtain ⟨v, h, hv, hh, hh₂⟩ := exists_blob_of_false_positive hN hBin hB' hTB hA hAT
    obtain ⟨d, hd⟩ := exists_leaf_below hN h
    obtain ⟨-, h2, h2'⟩ := mem_filter.mp hA
    have hne : A.Nonempty := card_pos.mp (by omega)
    have hne' : Aᶜ.Nonempty := card_pos.mp (by omega)
    have hcut : ¬ N.HasCutSplit (A : Set X) := fun hc =>
      hAT (mem_treeOfBlobs_of_hasCutSplit hne hne' hc)
    have hex : ∃ Y : Finset X, d ∈ Y ∧ Y.card = 4 ∧ (A ∩ Y).card = 2 ∧
        ∀ a ∈ Y, ∀ b ∈ Y, a ≠ b → ¬ SameBlock N v a b := by
      by_cases hdA : d ∈ A
      · exact exists_quartet_through hN hv hcut h2 h2' hdA
      · have hcut' : ¬ N.HasCutSplit ((Aᶜ : Finset X) : Set X) := by
          rwa [coe_compl, hasCutSplit_compl]
        obtain ⟨Y, hdY, hY, hYA, hdist⟩ := exists_quartet_through hN (refinesBlob_compl hv) hcut'
          h2' (by rwa [compl_compl]) (mem_compl.mpr hdA)
        refine ⟨Y, hdY, hY, ?_, hdist⟩
        have h3 := card_inter_add_card_sdiff Y A
        have h4 : Y \ A = Aᶜ ∩ Y := by
          ext z
          simp [and_comm]
        rw [h4, hY, hYA, inter_comm] at h3
        omega
    obtain ⟨Y, hdY, hY, hYA, hdist⟩ := hex
    exact (lemma4 hN hBin hLevel hv hh hh₂ hY hYA).mpr
      ⟨hdist, existsUnique_below hN hBin hLevel hh hh₂ hdist hdY hd⟩ (hall Y hY hYA)

/-- The core of Theorem 2: a disjoint cover around a false positive contains a four-taxon set meeting
the conditions of Lemma 4. The blocks at the blob are distributed across the multipartition of the
edge, so all sets of the cover meet condition 1, and the cover contains a taxon below the reticulation,
so one of them meets condition 2. -/
theorem Level1.exists_not_isTreelike (hN : N.IsPhylogenetic) (hBin : N.IsBinary) (hLevel : IsLevelOne N)
    {B : Finset (Finset X)} (hB : IsUnrootedTree B) (hTB : treeOfBlobs N ⊆ B) {A : Finset X}
    (hA : A ∈ internalSides B) (hAT : A ∉ treeOfBlobs N) {Q : Finset (Finset X)}
    (hQ : IsDisjointCover B A Q) : ∃ Y ∈ Q, ¬ IsTreelike N Y := by
  obtain ⟨v, h, hv, hh, hh₂⟩ := exists_blob_of_false_positive hN hBin hB hTB hA hAT
  obtain ⟨d, hd⟩ := exists_leaf_below hN h
  obtain ⟨Y, hYQ, hdY⟩ := hQ.cover d
  refine ⟨Y, hYQ, ?_⟩
  obtain ⟨s, hs, rfl⟩ := hQ.around Y hYQ
  obtain ⟨hbi, hm₁, hm₂⟩ := mem_filter.mp hs
  have hYA : (A ∩ s.taxa).card = 2 := s.2.2.1 _ (mem_filter.mp hbi).2
  have hYc : s.taxa.card = 4 := QuartetTree.card_taxa s
  obtain ⟨-, h2, h2'⟩ := mem_filter.mp hA
  have hne : A.Nonempty := card_pos.mp (by omega)
  have hne' : Aᶜ.Nonempty := card_pos.mp (by omega)
  have hcut : ¬ N.HasCutSplit (A : Set X) := fun hc =>
    hAT (mem_treeOfBlobs_of_hasCutSplit hne hne' hc)
  have hcut' : ¬ N.HasCutSplit ((Aᶜ : Finset X) : Set X) := by
    rwa [coe_compl, hasCutSplit_compl]
  have hYAc : (Aᶜ ∩ s.taxa).card = 2 := by
    have h3 := card_inter_add_card_sdiff s.taxa A
    have h4 : s.taxa \ A = Aᶜ ∩ s.taxa := by
      ext z
      simp [and_comm]
    rw [h4, hYc, inter_comm, hYA] at h3
    omega
  -- a block inside a side `C` of the edge with two taxa of `Y` contradicts the multipartition
  have key : ∀ {C : Finset X}, RefinesBlob N C v → ¬ N.HasCutSplit (C : Set X) → Cᶜ.Nonempty →
      (C ∩ s.taxa).card = 2 → (¬ ∃ D ∈ B, D ⊂ C ∧ C ∩ s.taxa ⊆ D) →
      ∀ x y, x ∈ C ∩ s.taxa → y ∈ C ∩ s.taxa → x ≠ y → ¬ SameBlock N v x y := by
    intro C hC hcutC hneC hcard hmul x y hx hy hxy hsb
    have hblob := leaf_not_sameBlob hN hh hh₂ x
    have hcutB := hasCutSplit_block hN hblob (v := v) (x := x)
    have hsub : block N v x ⊆ C := fun z hz => (hC x z (mem_block.mp hz)).mp (mem_inter.mp hx).1
    have hssub : block N v x ⊂ C := by
      refine lt_of_le_of_ne hsub ?_
      intro heq
      apply hcutC
      rw [← heq]
      exact hcutB
    have hmemB : block N v x ∈ B := by
      refine hTB (mem_treeOfBlobs_of_hasCutSplit ⟨x, mem_block.mpr .refl⟩ ?_ hcutB)
      obtain ⟨z, hz⟩ := hneC
      exact ⟨z, mem_compl.mpr fun hc => (mem_compl.mp hz) (hsub hc)⟩
    refine hmul ⟨_, hmemB, hssub, ?_⟩
    have hpair : ({x, y} : Finset X) = C ∩ s.taxa := by
      apply eq_of_subset_of_card_le
      · intro z hz
        rcases mem_insert.mp hz with rfl | hz
        · exact hx
        · rw [mem_singleton.mp hz]
          exact hy
      · rw [hcard, card_pair hxy]
    rw [← hpair]
    intro z hz
    rcases mem_insert.mp hz with rfl | hz
    · exact mem_block.mpr .refl
    · rw [mem_singleton.mp hz]
      exact mem_block.mpr hsb
  have hdist : ∀ x ∈ s.taxa, ∀ y ∈ s.taxa, x ≠ y → ¬ SameBlock N v x y := by
    intro x hx y hy hxy hsb
    have hside := hv x y hsb
    by_cases hxA : x ∈ A
    · exact key hv hcut hne' hYA hm₁ x y (mem_inter.mpr ⟨hxA, hx⟩)
        (mem_inter.mpr ⟨hside.mp hxA, hy⟩) hxy hsb
    · refine key (refinesBlob_compl hv) hcut' (by rwa [compl_compl]) hYAc hm₂ x y
        (mem_inter.mpr ⟨mem_compl.mpr hxA, hx⟩)
        (mem_inter.mpr ⟨mem_compl.mpr fun hc => hxA (hside.mpr hc), hy⟩) hxy hsb
  exact (lemma4 hN hBin hLevel hv hh hh₂ hYc hYA).mpr
    ⟨hdist, existsUnique_below hN hBin hLevel hh hh₂ hdist hdY hd⟩

/-- **Theorem 2** (`tob2025:theorem2`). For a binary level-1 network with tree of blobs `T_N`, and a
refinement `B` of `T_N`: applying the oracle to a disjoint cover of four-taxon subsets around each
edge of `B`, labelling an edge a false positive if the oracle answers non-treelike on one of them, and
contracting the false positives, returns `T_N`. The refinement `B` is any tree, not necessarily
binary: Definition 2's quadripartition is then read as the multipartition of `B` at the edge
(`IsDisjointCover`), across which the blocks at the blob are distributed. -/
theorem theorem2 (hN : N.IsPhylogenetic) (hBin : N.IsBinary) (hLevel : IsLevelOne N)
    {B : Finset (Finset X)} (hB : IsUnrootedTree B) (hTB : treeOfBlobs N ⊆ B)
    (Q : Finset X → Finset (Finset X)) (hQ : ∀ A ∈ internalSides B, IsDisjointCover B A (Q A)) :
    contractSides B ((internalSides B).filter fun A => ∃ Y ∈ Q A, ¬ IsTreelike N Y) = treeOfBlobs N := by
  have hmem : ∀ A, A ∈ (internalSides B).filter (fun A => ∃ Y ∈ Q A, ¬ IsTreelike N Y) ↔
      A ∈ internalSides B ∧ ∃ Y ∈ Q A, ¬ IsTreelike N Y := fun A => mem_filter
  -- true positives are not labelled: Lemma 2
  have htp : ∀ A ∈ treeOfBlobs N, A ∉ (internalSides B).filter fun A => ∃ Y ∈ Q A, ¬ IsTreelike N Y := by
    intro A hAT hC
    obtain ⟨hint, Y, hYQ, hnt⟩ := (hmem A).mp hC
    obtain ⟨s, hs, rfl⟩ := (hQ A hint).around Y hYQ
    have hbi := (mem_filter.mp (mem_filter.mp hs).1).2
    exact hnt (isTreelike_of_hasCutSplit hN (mem_filter.mp hAT).2.2.2 (QuartetTree.card_taxa s)
      (s.2.2.1 _ hbi))
  ext A
  simp only [contractSides, mem_filter (s := B)]
  constructor
  · rintro ⟨hAB, hnA, -⟩
    obtain ⟨hne, hne'⟩ := nonempty_of_mem_isUnrootedTree hB hAB
    by_cases hint : A ∈ internalSides B
    · -- false positives are labelled: Lemma 4
      by_contra hAT
      exact hnA ((hmem A).mpr ⟨hint, exists_not_isTreelike hN hBin hLevel hB hTB hint hAT (hQ A hint)⟩)
    · -- pendant edges are in the tree of blobs
      have hsmall : A.card ≤ 1 ∨ Aᶜ.card ≤ 1 := by
        by_contra hc
        push Not at hc
        exact hint (mem_filter.mpr ⟨hAB, by omega, by omega⟩)
      rcases hsmall with h | h
      · obtain ⟨a, rfl⟩ := card_eq_one.mp (by have := card_pos.mpr hne; omega : A.card = 1)
        exact mem_treeOfBlobs_of_hasCutSplit hne hne' (hasCutSplit_singleton hN a)
      · obtain ⟨a, ha⟩ := card_eq_one.mp (by have := card_pos.mpr hne'; omega : Aᶜ.card = 1)
        have hA : A = ({a} : Finset X)ᶜ := by rw [← ha, compl_compl]
        refine mem_treeOfBlobs_of_hasCutSplit hne hne' ?_
        rw [hA, coe_compl, hasCutSplit_compl]
        exact hasCutSplit_singleton hN a
  · intro hAT
    exact ⟨hTB hAT, htp A hAT, htp Aᶜ (mem_treeOfBlobs_compl hAT)⟩

/-- Two blocks of a tree that a compatible side contains points of are both inside it, provided that
it stays inside their union and the union is not everything. -/
theorem Level1.union_subset_of_two_blocks {T : Finset (Finset X)} (hfam : IsSplitFamily T)
    {P Q C : Finset X} (hP : P ∈ T) (hQ : Q ∈ T) (hC : C ∈ T) (hPQ : Disjoint P Q) {p q w : X}
    (hp : p ∈ P) (hq : q ∈ Q) (hpC : p ∈ C) (hqC : q ∈ C) (hw : w ∉ P ∪ Q) (hCsub : C ⊆ P ∪ Q) :
    P ∪ Q ⊆ C := by
  have hwP : w ∉ P := fun h => hw (mem_union_left _ h)
  have hwQ : w ∉ Q := fun h => hw (mem_union_right _ h)
  have hwC : w ∉ C := fun h => hw (hCsub h)
  have hPC : P ⊆ C := by
    rcases hfam.compatible C hC P hP with h | h | h | h
    · exact absurd (h hqC) (disjoint_right.mp hPQ hq)
    · exact h
    · exact absurd hp (disjoint_left.mp h hpC)
    · have : w ∈ C ∪ P := h ▸ mem_univ w
      rcases mem_union.mp this with h' | h'
      · exact absurd h' hwC
      · exact absurd h' hwP
  have hQC : Q ⊆ C := by
    rcases hfam.compatible C hC Q hQ with h | h | h | h
    · exact absurd (h hpC) (disjoint_left.mp hPQ hp)
    · exact h
    · exact absurd hq (disjoint_left.mp h hqC)
    · have : w ∈ C ∪ Q := h ▸ mem_univ w
      rcases mem_union.mp this with h' | h'
      · exact absurd h' hwC
      · exact absurd h' hwQ
  exact union_subset hPC hQC

/-- The 3-fix-1-alter search (§4.3, `tob2025:3f1a_correctness`) on the four blocks `P i`, with anchors
`z i ∈ P i`: for each block, keep the anchors of the other three blocks and vary the taxon of this
one. -/
def threeFixOneAlter (P : Fin 4 → Finset X) (z : Fin 4 → X) : Finset (Finset X) :=
  univ.biUnion fun i => (P i).image fun x => (univ.image (Function.update z i x))

/-- The 3-fix-1-alter search tests a disjoint cover, of `n - 3` four-taxon subsets, on a binary tree. -/
theorem threeFixOneAlter_isDisjointCover {T : Finset (Finset X)} (hT : IsBinaryTree T) {A : Finset X}
    (hA : A ∈ internalSides T) (P : Fin 4 → Finset X)
    (hP : ∀ i j, i ≠ j → Disjoint (P i) (P j)) (hcover : univ.biUnion P = univ)
    (hP₁ : P 0 ∪ P 1 = A) (hmem : ∀ i, P i ∈ T) (z : Fin 4 → X) (hz : ∀ i, z i ∈ P i) :
    IsDisjointCover T A (threeFixOneAlter P z) ∧
      (threeFixOneAlter P z).card = Fintype.card X - 3 := by
  obtain ⟨hAT, h2, -⟩ := mem_filter.mp hA
  have hTu : IsUnrootedTree T := by
    obtain ⟨H, hH, hu, -⟩ := hT
    exact ⟨H, hH, hu⟩
  have hfam := (isUnrootedTree_iff (h2.trans (card_le_univ A)) T).mp hTu
  have hdis : ∀ i j, i ≠ j → ∀ a, a ∈ P i → a ∉ P j :=
    fun i j hij a hi hj => disjoint_left.mp (hP i j hij) hi hj
  have hcov : ∀ a, ∃ i, a ∈ P i := by
    intro a
    have ha : a ∈ univ.biUnion P := hcover ▸ mem_univ a
    obtain ⟨i, -, hi⟩ := mem_biUnion.mp ha
    exact ⟨i, hi⟩
  have hPc : P 2 ∪ P 3 = Aᶜ := by
    rw [← hP₁]
    ext a
    simp only [mem_union, mem_compl]
    have h02 := hdis 0 2 (by decide) a
    have h03 := hdis 0 3 (by decide) a
    have h12 := hdis 1 2 (by decide) a
    have h13 := hdis 1 3 (by decide) a
    have hc : a ∈ P 0 ∨ a ∈ P 1 ∨ a ∈ P 2 ∨ a ∈ P 3 := by
      obtain ⟨i, hi⟩ := hcov a
      fin_cases i <;> simp_all
    tauto
  have hin₂ : ∀ {a}, a ∈ P 2 → a ∉ A := fun ha hc => (mem_compl.mp (hPc ▸ mem_union_left _ ha)) hc
  have hin₃ : ∀ {a}, a ∈ P 3 → a ∉ A := fun ha hc => (mem_compl.mp (hPc ▸ mem_union_right _ ha)) hc
  have hin₀ : ∀ {a}, a ∈ P 0 → a ∈ A := fun ha => hP₁ ▸ mem_union_left _ ha
  have hin₁ : ∀ {a}, a ∈ P 1 → a ∈ A := fun ha => hP₁ ▸ mem_union_right _ ha
  have hzinj : Function.Injective z := fun i j hij => by
    by_contra hne
    exact hdis i j hne _ (hz i) (hij ▸ hz j)
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · -- every set tested draws one taxon from each block
    intro Y hY
    obtain ⟨i, -, hYi⟩ := mem_biUnion.mp hY
    obtain ⟨x, hx, rfl⟩ := mem_image.mp hYi
    set w := Function.update z i x with hwdef
    have hw : ∀ j, w j ∈ P j := by
      intro j
      by_cases hj : j = i
      · subst hj
        simpa [hwdef] using hx
      · simpa [hwdef, Function.update_of_ne hj] using hz j
    have hwinj : Function.Injective w := fun a b hab => by
      by_contra hne
      exact hdis a b hne _ (hw a) (hab ▸ hw b)
    have him : (univ.image w : Finset X) = {w 0, w 1, w 2, w 3} := by
      ext y
      simp only [mem_image, mem_univ, true_and, mem_insert, mem_singleton]
      constructor
      · rintro ⟨j, rfl⟩
        fin_cases j <;> simp
      · rintro (rfl | rfl | rfl | rfl) <;> exact ⟨_, rfl⟩
    have hcard4 : ({w 0, w 1, w 2, w 3} : Finset X).card = 4 := by
      rw [← him, card_image_of_injective _ hwinj]
      simp
    let s : QuartetTree X := quartetTree (w 0) (w 1) (w 2) (w 3) hcard4
    have hst : s.taxa = {w 0, w 1, w 2, w 3} := by
      simp only [QuartetTree.taxa, s, quartetTree, sup_insert, sup_singleton, id, sup_eq_union]
      ext y
      simp only [mem_union, mem_insert, mem_singleton]
      tauto
    have hAs : A ∩ s.taxa = {w 0, w 1} := by
      rw [hst]
      ext y
      simp only [mem_inter, mem_insert, mem_singleton]
      constructor
      · rintro ⟨hy, rfl | rfl | rfl | rfl⟩
        · exact Or.inl rfl
        · exact Or.inr rfl
        · exact absurd hy (hin₂ (hw 2))
        · exact absurd hy (hin₃ (hw 3))
      · rintro (rfl | rfl)
        · exact ⟨hin₀ (hw 0), Or.inl rfl⟩
        · exact ⟨hin₁ (hw 1), Or.inr (Or.inl rfl)⟩
    have hAcs : Aᶜ ∩ s.taxa = {w 2, w 3} := by
      rw [hst]
      ext y
      simp only [mem_inter, mem_compl, mem_insert, mem_singleton]
      constructor
      · rintro ⟨hy, rfl | rfl | rfl | rfl⟩
        · exact absurd (hin₀ (hw 0)) hy
        · exact absurd (hin₁ (hw 1)) hy
        · exact Or.inl rfl
        · exact Or.inr rfl
      · rintro (rfl | rfl)
        · exact ⟨hin₂ (hw 2), Or.inr (Or.inr (Or.inl rfl))⟩
        · exact ⟨hin₃ (hw 3), Or.inr (Or.inr (Or.inr rfl))⟩
    refine ⟨s, mem_filter.mpr ⟨mem_filter.mpr ⟨mem_univ _, ?_⟩, ?_, ?_⟩, ?_⟩
    · rw [hAs]
      simp [s, quartetTree]
    · rintro ⟨C, hC, hCA, hsub⟩
      rw [hAs] at hsub
      have := union_subset_of_two_blocks hfam (hmem 0) (hmem 1) hC (hP 0 1 (by decide)) (hw 0) (hw 1)
        (hsub (by simp)) (hsub (by simp)) (w := w 2)
        (by rw [hP₁]; exact hin₂ (hw 2)) (by rw [hP₁]; exact hCA.subset)
      rw [hP₁] at this
      exact hCA.2 this
    · rintro ⟨C, hC, hCA, hsub⟩
      rw [hAcs] at hsub
      have := union_subset_of_two_blocks hfam (hmem 2) (hmem 3) hC (hP 2 3 (by decide)) (hw 2) (hw 3)
        (hsub (by simp)) (hsub (by simp)) (w := w 0)
        (by rw [hPc]; exact fun hc => (mem_compl.mp hc) (hin₀ (hw 0)))
        (by rw [hPc]; exact hCA.subset)
      rw [hPc] at this
      exact hCA.2 this
    · rw [hst, him]
  · -- every taxon is tested
    intro a
    obtain ⟨i, hi⟩ := hcov a
    exact ⟨univ.image (Function.update z i a), mem_biUnion.mpr ⟨i, mem_univ _, mem_image.mpr ⟨a, hi, rfl⟩⟩,
      mem_image.mpr ⟨i, mem_univ _, by simp⟩⟩
  · -- `n - 4` nonanchor taxa each give their own set, and the anchors give one more
    choose idx hidx using hcov
    set Zs : Finset X := univ.image z with hZs
    have hZcard : Zs.card = 4 := by
      rw [hZs, card_image_of_injective _ hzinj]
      simp
    let F : X → Finset X := fun a => univ.image (Function.update z (idx a) a)
    have hFself : ∀ a, a ∈ F a := fun a => mem_image.mpr ⟨idx a, mem_univ _, by simp⟩
    have hFsub : ∀ a b, b ∈ F a → b = a ∨ b ∈ Zs := by
      intro a b hb
      obtain ⟨j, -, rfl⟩ := mem_image.mp hb
      by_cases hj : j = idx a
      · subst hj
        left
        simp
      · right
        rw [Function.update_of_ne hj]
        exact mem_image_of_mem z (mem_univ j)
    have hset : threeFixOneAlter P z = insert Zs (Zsᶜ.image F) := by
      ext Y
      simp only [threeFixOneAlter, mem_biUnion, mem_univ, true_and, mem_image, mem_insert, mem_compl]
      constructor
      · rintro ⟨i, x, hx, rfl⟩
        by_cases hxZ : x ∈ Zs
        · obtain ⟨j, -, rfl⟩ := mem_image.mp hxZ
          have hji : j = i := by
            by_contra hne
            exact hdis j i hne _ (hz j) hx
          subst hji
          left
          rw [Function.update_eq_self]
        · right
          have hidxx : idx x = i := by
            by_contra hne
            exact hdis _ i hne _ (hidx x) hx
          exact ⟨x, hxZ, by simp only [F, hidxx]⟩
      · rintro (rfl | ⟨a, -, rfl⟩)
        · exact ⟨0, z 0, hz 0, by rw [Function.update_eq_self]⟩
        · exact ⟨idx a, a, hidx a, rfl⟩
    have hnotmem : Zs ∉ Zsᶜ.image F := by
      intro hc
      obtain ⟨a, ha, hFa⟩ := mem_image.mp hc
      exact (mem_compl.mp ha) (hFa ▸ hFself a)
    have hinj : Set.InjOn F (Zsᶜ : Finset X) := by
      intro a ha b hb hab
      rcases hFsub b a (hab ▸ hFself a) with h | h
      · exact h
      · exact absurd h (mem_compl.mp (mem_coe.mp ha))
    rw [hset, card_insert_of_notMem hnotmem, card_image_of_injOn hinj, card_compl, hZcard]
    have : Zs.card ≤ Fintype.card X := card_le_univ _
    omega

/-- **The correctness of the 3-fix-1-alter search** (`tob2025:3f1a_correctness`, §4.3): on a binary
refinement of the tree of blobs of a binary level-1 network, with the search at each internal edge on the
blocks of its quadripartition, contracting the edges where the oracle answers non-treelike on a tested subset
returns the tree of blobs. "It is easy to see that 3f1a tests a disjoint cover of four-taxon subsets and thus
has a correctness guarantee". -/
theorem threeFixOneAlter_correct (hN : N.IsPhylogenetic) (hBin : N.IsBinary) (hLevel : IsLevelOne N)
    {B : Finset (Finset X)} (hB : IsBinaryTree B) (hTB : treeOfBlobs N ⊆ B)
    (P : Finset X → Fin 4 → Finset X) (z : Finset X → Fin 4 → X)
    (hP : ∀ A ∈ internalSides B, ∀ i j, i ≠ j → Disjoint (P A i) (P A j))
    (hcover : ∀ A ∈ internalSides B, univ.biUnion (P A) = univ)
    (hP₁ : ∀ A ∈ internalSides B, P A 0 ∪ P A 1 = A)
    (hmem : ∀ A ∈ internalSides B, ∀ i, P A i ∈ B)
    (hz : ∀ A ∈ internalSides B, ∀ i, z A i ∈ P A i) :
    contractSides B ((internalSides B).filter fun A =>
      ∃ Y ∈ threeFixOneAlter (P A) (z A), ¬ IsTreelike N Y) = treeOfBlobs N := by
  have hBu : IsUnrootedTree B := by
    obtain ⟨H, hH, hu, -⟩ := hB
    exact ⟨H, hH, hu⟩
  exact theorem2 hN hBin hLevel hBu hTB (fun A => threeFixOneAlter (P A) (z A)) fun A hA =>
    (threeFixOneAlter_isDisjointCover hB hA (P A) (hP A hA) (hcover A hA) (hP₁ A hA) (hmem A hA)
      (z A) (hz A hA)).1

end TOBQMC
