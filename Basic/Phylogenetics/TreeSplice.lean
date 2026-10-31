module

public import Basic.Phylogenetics.TreeSplits

/-!
# Splicing trees into the vertices of a tree

The construction of ECToBlob's proof of Theorem 3.1 and TOB-QMC's proof of Lemma 3: at each
multifurcation of a tree `T`, with blocks `P`, add a family of sides that are unions of blocks and are
pairwise compatible. The result is a tree resolving `T` that, on quartets with taxa in distinct blocks
of `P`, displays exactly what the family at `P` does.

* `IsBlockUnion`, `IsBlockFamily`: the families that can be added at a vertex;
* `splice`, `splice_isUnrootedTree`, `subset_splice`, `displays_splice_iff`: the construction;
* `liftBlocks`, `isBlockFamily_image_liftBlocks`: the family of the lifts of a tree on the blocks;
* `QuartetTree.map`, `pullTree`, `pullTree_isUnrootedTree`, `displays_pullTree_iff`: restriction of a
  tree along an injection, such as a choice of representatives of the blocks;
* `IsRepTuple`, `exists_isRepTuple`: choices of representatives of the blocks;
* `IsRepTuple.mem_pullTree_iff`, `pullTree_eq_of_forall_mem`, `filter_isBlockUnion_eq_image_pullTree`:
  a tree with the blocks as sides has one restriction to all representatives, whose lifts are its sides
  that are unions of blocks;
* `IsBlockAttachment`, `IsBlockAttachment.pullTree_eq`, `attachSubtrees`, `isBlockAttachment_attachSubtrees`,
  `IsBlockAttachment.exists_eq_attachSubtrees`, `isBlockAttachment_splice`: attaching rooted subtrees at the
  leaves of a tree on the blocks; every such tree, and every splice, restricts back to the tree on the blocks;
* `reattach`, `reattach_isUnrootedTree`, `subset_pullTree_reattach`: replacing that restriction by a
  refinement and reattaching the removed taxa;
* `blockWeight`, `innerSum`, `prod_card_mul_sum_eq_sum_innerSum`, `innerSum_eq_quartetScore_pullTree`: a
  sum over quartet trees in distinct blocks as a sum over representative tuples;
* `exists_max_quartetScore`: a maximizing tree exists;
* `sum_ite_taxa_subset_image`: quartet trees on the image of an injection are those of its domain;
* `map_eq_of_cutExchangeable`: by exchangeability, a weight of a quartet tree in distinct blocks does
  not depend on the representatives.
-/

@[expose] public noncomputable section

namespace Phylogenetics

open Finset
open scoped Classical

variable {X : Type*} [Fintype X] [DecidableEq X]


/-! ### Sides that are unions of blocks -/

/-- `A` is a union of blocks of `P`: each block lies inside `A` or misses it. -/
def IsBlockUnion (P : Finset (Finset X)) (A : Finset X) : Prop :=
  ∀ B ∈ P, B ⊆ A ∨ Disjoint B A

/-- The sides that can be added to a tree at the vertex with blocks `P`: nonempty and proper unions of
blocks, closed under complement and pairwise compatible. -/
structure IsBlockFamily (P L : Finset (Finset X)) : Prop where
  blockUnion : ∀ A ∈ L, IsBlockUnion P A
  nonempty : ∀ A ∈ L, A.Nonempty
  compl_nonempty : ∀ A ∈ L, Aᶜ.Nonempty
  compl_mem : ∀ A ∈ L, Aᶜ ∈ L
  compatible : ∀ A ∈ L, ∀ B ∈ L, A ⊆ B ∨ B ⊆ A ∨ Disjoint A B ∨ A ∪ B = univ

private theorem compat_symm {A B : Finset X} (h : A ⊆ B ∨ B ⊆ A ∨ Disjoint A B ∨ A ∪ B = univ) :
    B ⊆ A ∨ A ⊆ B ∨ Disjoint B A ∨ B ∪ A = univ := by
  rcases h with h | h | h | h
  · exact Or.inr (Or.inl h)
  · exact Or.inl h
  · exact Or.inr (Or.inr (Or.inl h.symm))
  · exact Or.inr (Or.inr (Or.inr (union_comm A B ▸ h)))

/-- A union of blocks at a vertex is compatible with every side of the tree. -/
theorem IsVertexPartition.compatible_of_isBlockUnion {T P : Finset (Finset X)}
    (hP : IsVertexPartition T P) {A C : Finset X} (hA : IsBlockUnion P A) (hC : C ∈ T) :
    A ⊆ C ∨ C ⊆ A ∨ Disjoint A C ∨ A ∪ C = univ := by
  rcases hP.edge_in_block C hC with ⟨B, hB, hCB⟩ | ⟨B, hB, hCB⟩
  · rcases hA B hB with h | h
    · exact Or.inr (Or.inl (hCB.trans h))
    · exact Or.inr (Or.inr (Or.inl (h.mono_left hCB).symm))
  · rcases hA B hB with h | h
    · refine Or.inr (Or.inr (Or.inr (eq_univ_iff_forall.2 fun x => ?_)))
      by_cases hx : x ∈ C
      · exact mem_union_right _ hx
      · exact mem_union_left _ (h (hCB (mem_compl.2 hx)))
    · refine Or.inl fun x hx => ?_
      by_contra hxC
      exact disjoint_left.1 h (hCB (mem_compl.2 hxC)) hx

/-- Unions of blocks at two distinct vertices of a tree are compatible. -/
theorem IsVertexPartition.compatible_of_ne {T P P' : Finset (Finset X)} (hT : IsUnrootedTree T)
    (hP : IsVertexPartition T P) (hP' : IsVertexPartition T P') (hne : P ≠ P') {A A' : Finset X}
    (hA : IsBlockUnion P A) (hA' : IsBlockUnion P' A') :
    A ⊆ A' ∨ A' ⊆ A ∨ Disjoint A A' ∨ A ∪ A' = univ := by
  obtain ⟨B, hB, B', hB', hu⟩ := hP.exists_union_eq_univ hT hP' hne
  have hu' : ∀ x, x ∈ B ∨ x ∈ B' := fun x => mem_union.1 (hu ▸ mem_univ x)
  rcases hA B hB with h | h <;> rcases hA' B' hB' with h' | h'
  · refine Or.inr (Or.inr (Or.inr (eq_univ_iff_forall.2 fun x => ?_)))
    rcases hu' x with hx | hx
    · exact mem_union_left _ (h hx)
    · exact mem_union_right _ (h' hx)
  · refine Or.inr (Or.inl fun x hx => ?_)
    rcases hu' x with hx' | hx'
    · exact h hx'
    · exact absurd hx (disjoint_left.1 h' hx')
  · refine Or.inl fun x hx => ?_
    rcases hu' x with hx' | hx'
    · exact absurd hx (disjoint_left.1 h hx')
    · exact h' hx'
  · refine Or.inr (Or.inr (Or.inl (disjoint_left.2 fun x hx hx₂ => ?_)))
    rcases hu' x with hx' | hx'
    · exact disjoint_left.1 h hx' hx
    · exact disjoint_left.1 h' hx' hx₂

/-! ### The splice -/

/-- The tree `T` with, at each multifurcation `P`, the sides `L P` added. -/
def splice (T : Finset (Finset X)) (L : Finset (Finset X) → Finset (Finset X)) :
    Finset (Finset X) :=
  T ∪ (multifurcations T).biUnion L

theorem mem_splice {T : Finset (Finset X)} {L : Finset (Finset X) → Finset (Finset X)}
    {A : Finset X} : A ∈ splice T L ↔ A ∈ T ∨ ∃ P ∈ multifurcations T, A ∈ L P := by
  simp [splice, mem_biUnion]

theorem subset_splice (T : Finset (Finset X)) (L : Finset (Finset X) → Finset (Finset X)) :
    T ⊆ splice T L :=
  subset_union_left

/-- The splice of block families into a tree is a tree. -/
theorem splice_isUnrootedTree {T : Finset (Finset X)} (hT : IsUnrootedTree T)
    {L : Finset (Finset X) → Finset (Finset X)}
    (hL : ∀ P ∈ multifurcations T, IsBlockFamily P (L P)) : IsUnrootedTree (splice T L) := by
  by_cases hX : 2 ≤ Fintype.card X
  · have hSF := hT.isSplitFamily hX
    refine (isUnrootedTree_iff hX _).2 ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro A hA
      rcases mem_splice.1 hA with h | ⟨P, hP, h⟩
      · exact hSF.nonempty A h
      · exact (hL P hP).nonempty A h
    · intro A hA
      rcases mem_splice.1 hA with h | ⟨P, hP, h⟩
      · exact hSF.compl_nonempty A h
      · exact (hL P hP).compl_nonempty A h
    · intro A hA
      rcases mem_splice.1 hA with h | ⟨P, hP, h⟩
      · exact mem_splice.2 (Or.inl (hSF.compl_mem A h))
      · exact mem_splice.2 (Or.inr ⟨P, hP, (hL P hP).compl_mem A h⟩)
    · exact fun x => mem_splice.2 (Or.inl (hSF.singleton_mem x))
    · intro A hA B hB
      rcases mem_splice.1 hA with h | ⟨P, hP, h⟩ <;> rcases mem_splice.1 hB with h' | ⟨P', hP', h'⟩
      · exact hSF.compatible A h B h'
      · exact compat_symm ((mem_multifurcations.1 hP').1.compatible_of_isBlockUnion
          ((hL P' hP').blockUnion B h') h)
      · exact (mem_multifurcations.1 hP).1.compatible_of_isBlockUnion
          ((hL P hP).blockUnion A h) h'
      · by_cases he : P = P'
        · subst he
          exact (hL P hP).compatible A h B h'
        · exact (mem_multifurcations.1 hP).1.compatible_of_ne hT (mem_multifurcations.1 hP').1 he
            ((hL P hP).blockUnion A h) ((hL P' hP').blockUnion B h')
  · have hM : multifurcations T = ∅ := by
      rw [eq_empty_iff_forall_notMem]
      intro P hP
      obtain ⟨hV, h4⟩ := mem_multifurcations.1 hP
      obtain ⟨B, hB⟩ := card_pos.1 (show 0 < P.card by omega)
      exact hX (hT.two_le_card_of_mem (hV.mem B hB))
    simpa [splice, hM] using hT

/-- On a quartet with taxa in distinct blocks of a multifurcation `P`, the spliced tree displays
exactly what the family at `P` does. -/
theorem displays_splice_iff {T : Finset (Finset X)} (hT : IsUnrootedTree T)
    {L : Finset (Finset X) → Finset (Finset X)}
    (hL : ∀ P ∈ multifurcations T, IsBlockFamily P (L P)) {P : Finset (Finset X)}
    (hP : P ∈ multifurcations T) {s : QuartetTree X} (hs : InDistinctBlocks P s.taxa) :
    Displays (splice T L) s ↔ ∃ A ∈ L P, A ∩ s.taxa ∈ s.val := by
  constructor
  · rintro ⟨A, hA, hAs⟩
    rcases mem_splice.1 hA with h | ⟨P', hP', h⟩
    · exact absurd ⟨A, h, hAs⟩ (not_displays_of_inDistinctBlocks (mem_multifurcations.1 hP).1 hs)
    · by_cases he : P = P'
      · subst he
        exact ⟨A, h, hAs⟩
      · exfalso
        obtain ⟨B, hB, B', hB', hu⟩ := (mem_multifurcations.1 hP).1.exists_union_eq_univ hT
          (mem_multifurcations.1 hP').1 he
        have hu' : ∀ x, x ∈ B ∨ x ∈ B' := fun x => mem_union.1 (hu ▸ mem_univ x)
        have h1 := hs B hB
        have hc := s.card_of_mem hAs
        have hc' := s.card_of_mem (s.sdiff_mem hAs)
        rcases (hL P' hP').blockUnion A h B' hB' with hsub | hdis
        · have : s.taxa \ (A ∩ s.taxa) ⊆ B ∩ s.taxa := by
            intro x hx
            obtain ⟨hx1, hx2⟩ := mem_sdiff.1 hx
            refine mem_inter.2 ⟨?_, hx1⟩
            rcases hu' x with hb | hb
            · exact hb
            · exact absurd (mem_inter.2 ⟨hsub hb, hx1⟩) hx2
          have := card_le_card this
          omega
        · have : A ∩ s.taxa ⊆ B ∩ s.taxa := by
            intro x hx
            obtain ⟨hx1, hx2⟩ := mem_inter.1 hx
            refine mem_inter.2 ⟨?_, hx2⟩
            rcases hu' x with hb | hb
            · exact hb
            · exact absurd hx1 (disjoint_left.1 hdis hb)
          have := card_le_card this
          omega
  · rintro ⟨A, hA, hAs⟩
    exact ⟨A, mem_splice.2 (Or.inr ⟨P, hP, hA⟩), hAs⟩

/-! ### Lifts of trees on the blocks -/

/-- The union of a set of blocks. -/
def liftBlocks (P : Finset (Finset X)) (A : Finset {B // B ∈ P}) : Finset X :=
  A.biUnion Subtype.val

omit [Fintype X] in
theorem mem_liftBlocks {P : Finset (Finset X)} {A : Finset {B // B ∈ P}} {x : X} :
    x ∈ liftBlocks P A ↔ ∃ b ∈ A, x ∈ b.val := by
  simp [liftBlocks, mem_biUnion]

section Lift

variable {P : Finset (Finset X)} (hd : ∀ B ∈ P, ∀ C ∈ P, B ≠ C → Disjoint B C)

include hd

omit [Fintype X] in
/-- The block of a taxon is unique. -/
theorem block_eq_of_mem {b c : {B // B ∈ P}} {x : X} (hb : x ∈ b.val) (hc : x ∈ c.val) : b = c := by
  by_contra hne
  exact disjoint_left.1 (hd b.val b.property c.val c.property fun e => hne (Subtype.ext e)) hb hc

omit [Fintype X] in
theorem mem_liftBlocks_of_mem {A : Finset {B // B ∈ P}} {b : {B // B ∈ P}} {x : X}
    (hx : x ∈ b.val) : x ∈ liftBlocks P A ↔ b ∈ A := by
  rw [mem_liftBlocks]
  constructor
  · rintro ⟨c, hc, hxc⟩
    exact block_eq_of_mem hd hx hxc ▸ hc
  · exact fun hb => ⟨b, hb, hx⟩

omit [Fintype X] in
theorem isBlockUnion_liftBlocks (A : Finset {B // B ∈ P}) : IsBlockUnion P (liftBlocks P A) := by
  intro B hB
  by_cases h : (⟨B, hB⟩ : {B // B ∈ P}) ∈ A
  · exact Or.inl fun x hx => mem_liftBlocks.2 ⟨_, h, hx⟩
  · exact Or.inr (disjoint_left.2 fun x hx hxA =>
      h ((mem_liftBlocks_of_mem hd (b := ⟨B, hB⟩) hx).1 hxA))

end Lift

section LiftTree

variable {P : Finset (Finset X)} (hne : ∀ B ∈ P, B.Nonempty)
  (hd : ∀ B ∈ P, ∀ C ∈ P, B ≠ C → Disjoint B C) (hcover : P.sup id = univ)

theorem exists_block (hcover : P.sup id = univ) (x : X) : ∃ b : {B // B ∈ P}, x ∈ b.val := by
  have : x ∈ P.sup id := hcover ▸ mem_univ x
  obtain ⟨B, hB, hx⟩ : ∃ B ∈ P, x ∈ B := by simpa [mem_sup] using this
  exact ⟨⟨B, hB⟩, hx⟩

include hd hcover in
theorem liftBlocks_compl (A : Finset {B // B ∈ P}) :
    liftBlocks P Aᶜ = (liftBlocks P A)ᶜ := by
  ext x
  obtain ⟨b, hb⟩ := exists_block hcover x
  rw [mem_compl, mem_liftBlocks_of_mem hd hb, mem_liftBlocks_of_mem hd hb, mem_compl]

include hne in
omit [Fintype X] in
theorem liftBlocks_nonempty {A : Finset {B // B ∈ P}} (hA : A.Nonempty) :
    (liftBlocks P A).Nonempty := by
  obtain ⟨b, hb⟩ := hA
  obtain ⟨x, hx⟩ := hne b.val b.property
  exact ⟨x, mem_liftBlocks.2 ⟨b, hb, hx⟩⟩

include hne hd hcover in
/-- The lifts of the sides of a tree on the blocks form a block family. -/
theorem isBlockFamily_image_liftBlocks {T : Finset (Finset {B // B ∈ P})} (hT : IsUnrootedTree T) :
    IsBlockFamily P (T.image (liftBlocks P)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro A' hA'
    obtain ⟨A, -, rfl⟩ := mem_image.1 hA'
    exact isBlockUnion_liftBlocks hd A
  · intro A' hA'
    obtain ⟨A, hA, rfl⟩ := mem_image.1 hA'
    exact liftBlocks_nonempty hne (hT.nonempty_of_mem hA)
  · intro A' hA'
    obtain ⟨A, hA, rfl⟩ := mem_image.1 hA'
    rw [← liftBlocks_compl hd hcover]
    exact liftBlocks_nonempty hne (hT.nonempty_of_mem (hT.compl_mem hA))
  · intro A' hA'
    obtain ⟨A, hA, rfl⟩ := mem_image.1 hA'
    rw [← liftBlocks_compl hd hcover]
    exact mem_image_of_mem _ (hT.compl_mem hA)
  · intro A' hA' B' hB'
    obtain ⟨A, hA, rfl⟩ := mem_image.1 hA'
    obtain ⟨B, hB, rfl⟩ := mem_image.1 hB'
    rcases hT.compatible hA hB with h | h | h | h
    · exact Or.inl (biUnion_subset_biUnion_of_subset_left _ h)
    · exact Or.inr (Or.inl (biUnion_subset_biUnion_of_subset_left _ h))
    · refine Or.inr (Or.inr (Or.inl (disjoint_left.2 fun x hx hx' => ?_)))
      obtain ⟨b, hb, hxb⟩ := mem_liftBlocks.1 hx
      exact disjoint_left.1 h hb ((mem_liftBlocks_of_mem hd hxb).1 hx')
    · refine Or.inr (Or.inr (Or.inr (eq_univ_iff_forall.2 fun x => ?_)))
      obtain ⟨b, hb⟩ := exists_block hcover x
      have : b ∈ A ∪ B := h ▸ mem_univ b
      rcases mem_union.1 this with h' | h'
      · exact mem_union_left _ (mem_liftBlocks.2 ⟨b, h', hb⟩)
      · exact mem_union_right _ (mem_liftBlocks.2 ⟨b, h', hb⟩)

end LiftTree

/-! ### Transport of quartet trees along an injection -/

section Map

variable {Y : Type*} [Fintype Y] [DecidableEq Y] {ι : Y → X} (hι : Function.Injective ι)

/-- The image of a quartet tree under an injection. -/
def QuartetTree.map (hι : Function.Injective ι) (s : QuartetTree Y) : QuartetTree X :=
  ⟨s.val.image fun B => B.image ι, by
    obtain ⟨hc, h2, hd⟩ := s.property
    refine ⟨?_, ?_, ?_⟩
    · rw [card_image_of_injective _ (image_injective hι), hc]
    · intro B' hB'
      obtain ⟨B, hB, rfl⟩ := mem_image.1 hB'
      rw [card_image_of_injective _ hι, h2 B hB]
    · intro B' hB' C' hC' hBC
      obtain ⟨B, hB, rfl⟩ := mem_image.1 hB'
      obtain ⟨C, hC, rfl⟩ := mem_image.1 hC'
      rw [disjoint_image hι]
      exact hd B hB C hC fun e => hBC (e ▸ rfl)⟩

omit [Fintype X] [Fintype Y] in
@[simp] theorem QuartetTree.map_val (s : QuartetTree Y) :
    (s.map hι).val = s.val.image fun B => B.image ι := rfl

omit [Fintype X] [Fintype Y] in
@[simp] theorem QuartetTree.map_taxa (s : QuartetTree Y) : (s.map hι).taxa = s.taxa.image ι := by
  ext x
  simp only [QuartetTree.taxa, QuartetTree.map_val, mem_sup, id, mem_image]
  constructor
  · rintro ⟨_, ⟨B, hB, rfl⟩, hx⟩
    obtain ⟨y, hy, rfl⟩ := mem_image.1 hx
    exact ⟨y, ⟨B, hB, hy⟩, rfl⟩
  · rintro ⟨y, ⟨B, hB, hy⟩, rfl⟩
    exact ⟨_, ⟨B, hB, rfl⟩, mem_image_of_mem _ hy⟩

omit [Fintype X] [Fintype Y] in
theorem QuartetTree.map_injective : Function.Injective (QuartetTree.map (X := X) hι) := by
  intro s s' h
  apply Subtype.ext
  exact image_injective (image_injective hι) (congrArg Subtype.val h)

include hι in
omit [Fintype X] in
/-- A quartet tree on the image of an injection comes from its domain. -/
theorem QuartetTree.exists_map_eq (s : QuartetTree X) (h : s.taxa ⊆ univ.image ι) :
    ∃ s₀ : QuartetTree Y, s₀.map hι = s := by
  let f : Finset X → Finset Y := fun B => univ.filter fun y => ι y ∈ B
  have hf : ∀ B ∈ s.val, (f B).image ι = B := by
    intro B hB
    ext x
    simp only [mem_image, f, mem_filter, mem_univ, true_and]
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro hx
      obtain ⟨y, -, rfl⟩ := mem_image.1 (h (s.subset_taxa hB hx))
      exact ⟨y, hx, rfl⟩
  have hfc : ∀ B ∈ s.val, (f B).card = 2 := fun B hB => by
    rw [← card_image_of_injective _ hι, hf B hB, s.card_of_mem hB]
  have hinj : Set.InjOn f s.val := fun B hB C hC e => by
    rw [← hf B hB, ← hf C hC]
    exact congrArg (image ι) e
  refine ⟨⟨s.val.image f, ?_, ?_, ?_⟩, ?_⟩
  · rw [card_image_of_injOn hinj]
    exact s.property.1
  · intro B' hB'
    obtain ⟨B, hB, rfl⟩ := mem_image.1 hB'
    exact hfc B hB
  · intro B' hB' C' hC' hBC
    obtain ⟨B, hB, rfl⟩ := mem_image.1 hB'
    obtain ⟨C, hC, rfl⟩ := mem_image.1 hC'
    have := s.property.2.2 B hB C hC fun e => hBC (e ▸ rfl)
    exact disjoint_left.2 fun y hy hy' =>
      disjoint_left.1 this (mem_filter.1 hy).2 (mem_filter.1 hy').2
  · apply Subtype.ext
    rw [QuartetTree.map_val, image_image]
    ext B
    simp only [mem_image, Function.comp]
    constructor
    · rintro ⟨C, hC, rfl⟩
      rw [hf C hC]
      exact hC
    · exact fun hB => ⟨B, hB, hf B hB⟩

include hι in
/-- Quartet trees on the image of an injection are those of the domain. -/
theorem sum_ite_taxa_subset_image (g : QuartetTree X → ℝ) :
    (∑ s : QuartetTree X, if s.taxa ⊆ univ.image ι then g s else 0) =
      ∑ s₀ : QuartetTree Y, g (s₀.map hι) := by
  rw [← sum_filter]
  have : (univ.filter fun s : QuartetTree X => s.taxa ⊆ univ.image ι) =
      univ.image (QuartetTree.map hι) := by
    ext s
    simp only [mem_filter, mem_univ, true_and, mem_image]
    constructor
    · intro h
      exact QuartetTree.exists_map_eq hι s h
    · rintro ⟨s₀, rfl⟩
      rw [QuartetTree.map_taxa]
      exact image_subset_image (subset_univ _)
  rw [this, sum_image (fun a _ b _ h => QuartetTree.map_injective hι h)]

/-- The restriction of a tree along an injection. -/
def pullTree (ι : Y → X) (T : Finset (Finset X)) : Finset (Finset Y) :=
  (T.image fun A => univ.filter fun y => ι y ∈ A).filter fun A => A.Nonempty ∧ Aᶜ.Nonempty

omit [Fintype X] in
theorem mem_pullTree {T : Finset (Finset X)} {A : Finset Y} :
    A ∈ pullTree ι T ↔ (∃ C ∈ T, (univ.filter fun y => ι y ∈ C) = A) ∧ A.Nonempty ∧ Aᶜ.Nonempty := by
  simp [pullTree, mem_filter, mem_image]

include hι in
/-- The restriction of a tree along an injection, from at least two taxa, is a tree. -/
theorem pullTree_isUnrootedTree {T : Finset (Finset X)} (hT : IsUnrootedTree T)
    (hY : 2 ≤ Fintype.card Y) : IsUnrootedTree (pullTree ι T) := by
  have hX : 2 ≤ Fintype.card X := hY.trans (Fintype.card_le_of_injective ι hι)
  have hSF := hT.isSplitFamily hX
  refine (isUnrootedTree_iff hY _).2 ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact fun A hA => (mem_pullTree.1 hA).2.1
  · exact fun A hA => (mem_pullTree.1 hA).2.2
  · intro A hA
    obtain ⟨⟨C, hC, rfl⟩, h1, h2⟩ := mem_pullTree.1 hA
    refine mem_pullTree.2 ⟨⟨Cᶜ, hSF.compl_mem C hC, ?_⟩, h2, by rwa [compl_compl]⟩
    ext y
    simp
  · intro y
    refine mem_pullTree.2 ⟨⟨{ι y}, hSF.singleton_mem _, ?_⟩, singleton_nonempty y, ?_⟩
    · ext z
      simp [hι.eq_iff]
    · rw [← card_pos, card_compl, card_singleton]
      omega
  · intro A hA B hB
    obtain ⟨⟨C, hC, rfl⟩, -, -⟩ := mem_pullTree.1 hA
    obtain ⟨⟨D, hD, rfl⟩, -, -⟩ := mem_pullTree.1 hB
    rcases hSF.compatible C hC D hD with h | h | h | h
    · exact Or.inl fun y hy => mem_filter.2 ⟨mem_univ y, h (mem_filter.1 hy).2⟩
    · exact Or.inr (Or.inl fun y hy => mem_filter.2 ⟨mem_univ y, h (mem_filter.1 hy).2⟩)
    · exact Or.inr (Or.inr (Or.inl (disjoint_left.2 fun y hy hy' =>
        disjoint_left.1 h (mem_filter.1 hy).2 (mem_filter.1 hy').2)))
    · refine Or.inr (Or.inr (Or.inr (eq_univ_iff_forall.2 fun y => ?_)))
      have : ι y ∈ C ∪ D := h ▸ mem_univ _
      rcases mem_union.1 this with h' | h'
      · exact mem_union_left _ (mem_filter.2 ⟨mem_univ y, h'⟩)
      · exact mem_union_right _ (mem_filter.2 ⟨mem_univ y, h'⟩)

omit [Fintype X] in
/-- The restriction of a tree along an injection displays what the tree does. -/
theorem displays_pullTree_iff {T : Finset (Finset X)} (s₀ : QuartetTree Y) :
    Displays (pullTree ι T) s₀ ↔ Displays T (s₀.map hι) := by
  have hpre : ∀ A : Finset X, ((univ.filter fun y => ι y ∈ A) ∩ s₀.taxa).image ι =
      A ∩ s₀.taxa.image ι := by
    intro A
    ext x
    simp only [mem_image, mem_inter, mem_filter, mem_univ, true_and]
    constructor
    · rintro ⟨y, ⟨h1, h2⟩, rfl⟩
      exact ⟨h1, y, h2, rfl⟩
    · rintro ⟨h1, y, h2, rfl⟩
      exact ⟨y, ⟨h1, h2⟩, rfl⟩
  constructor
  · rintro ⟨A, hA, hAs⟩
    obtain ⟨⟨C, hC, rfl⟩, -, -⟩ := mem_pullTree.1 hA
    refine ⟨C, hC, ?_⟩
    rw [QuartetTree.map_taxa, ← hpre C, QuartetTree.map_val]
    exact mem_image_of_mem _ hAs
  · rintro ⟨A, hA, hAs⟩
    rw [QuartetTree.map_taxa, QuartetTree.map_val, mem_image] at hAs
    obtain ⟨C, hC, hCe⟩ := hAs
    have hCA : (univ.filter fun y => ι y ∈ A) ∩ s₀.taxa = C :=
      image_injective hι (by rw [hpre, hCe])
    have hCc := s₀.card_of_mem hC
    have hCc' := s₀.card_of_mem (s₀.sdiff_mem hC)
    refine ⟨univ.filter fun y => ι y ∈ A, mem_pullTree.2 ⟨⟨A, hA, rfl⟩, ?_, ?_⟩, hCA ▸ hC⟩
    · obtain ⟨y, hy⟩ := card_pos.1 (show 0 < C.card by omega)
      exact ⟨y, (mem_inter.1 (hCA ▸ hy)).1⟩
    · obtain ⟨y, hy⟩ := card_pos.1 (show 0 < (s₀.taxa \ C).card by omega)
      refine ⟨y, mem_compl.2 fun hyA => ?_⟩
      obtain ⟨h1, h2⟩ := mem_sdiff.1 hy
      exact h2 (hCA ▸ mem_inter.2 ⟨hyA, h1⟩)

end Map

/-! ### Representatives of the blocks -/

section Rep

variable {P : Finset (Finset X)}

/-- A choice of a taxon in each block. -/
def IsRepTuple (P : Finset (Finset X)) (x : {B // B ∈ P} → X) : Prop := ∀ b, x b ∈ b.val

omit [Fintype X] [DecidableEq X] in
theorem exists_isRepTuple (hne : ∀ B ∈ P, B.Nonempty) : ∃ x, IsRepTuple P x :=
  ⟨fun b => (hne b.val b.property).choose, fun b => (hne b.val b.property).choose_spec⟩

variable (hd : ∀ B ∈ P, ∀ C ∈ P, B ≠ C → Disjoint B C) {x : {B // B ∈ P} → X} (hx : IsRepTuple P x)

include hd hx

omit [Fintype X] in
theorem IsRepTuple.injective : Function.Injective x := fun b c h =>
  block_eq_of_mem hd (hx b) (h ▸ hx c)

omit [Fintype X] in
/-- Taxa among the representatives of the blocks lie in distinct blocks. -/
theorem IsRepTuple.inDistinctBlocks {q : Finset X} (hq : q ⊆ univ.image x) :
    InDistinctBlocks P q := by
  intro B hB
  refine card_le_one.2 fun y hy z hz => ?_
  obtain ⟨hyB, hyq⟩ := mem_inter.1 hy
  obtain ⟨hzB, hzq⟩ := mem_inter.1 hz
  obtain ⟨b, -, rfl⟩ := mem_image.1 (hq hyq)
  obtain ⟨c, -, rfl⟩ := mem_image.1 (hq hzq)
  have h1 : b = ⟨B, hB⟩ := block_eq_of_mem hd (hx b) hyB
  have h2 : c = ⟨B, hB⟩ := block_eq_of_mem hd (hx c) hzB
  rw [h1, h2]

omit [Fintype X] in
/-- On the representatives, a lift traces the corresponding set of blocks. -/
theorem IsRepTuple.liftBlocks_inter_image (A D : Finset {B // B ∈ P}) :
    liftBlocks P A ∩ D.image x = (A ∩ D).image x := by
  ext y
  simp only [mem_inter, mem_image]
  constructor
  · rintro ⟨h1, b, hb, rfl⟩
    exact ⟨b, ⟨(mem_liftBlocks_of_mem hd (hx b)).1 h1, hb⟩, rfl⟩
  · rintro ⟨b, ⟨h1, h2⟩, rfl⟩
    exact ⟨(mem_liftBlocks_of_mem hd (hx b)).2 h1, b, h2, rfl⟩

end Rep

/-! ### Restricting a tree that has the blocks as sides -/

section Restrict

variable {P : Finset (Finset X)} (hd : ∀ B ∈ P, ∀ C ∈ P, B ≠ C → Disjoint B C)
  {x : {B // B ∈ P} → X} (hx : IsRepTuple P x)

omit [Fintype X] in
@[simp] theorem liftBlocks_singleton (b : {B // B ∈ P}) : liftBlocks P {b} = b.val := by
  simp [liftBlocks]

include hd hx

omit [Fintype X] in
/-- A lift, restricted to representatives, is the set of blocks that was lifted. -/
theorem IsRepTuple.filter_mem_liftBlocks (A : Finset {B // B ∈ P}) :
    (univ.filter fun b => x b ∈ liftBlocks P A) = A := by
  ext b
  simp only [mem_filter, mem_univ, true_and]
  exact mem_liftBlocks_of_mem hd (hx b)

/-- A union of blocks is the lift of the set of blocks whose representatives it contains. -/
theorem IsRepTuple.liftBlocks_filter_mem (hcover : P.sup id = univ) {C : Finset X}
    (hC : IsBlockUnion P C) : liftBlocks P (univ.filter fun b => x b ∈ C) = C := by
  ext y
  obtain ⟨b, hb⟩ := exists_block hcover y
  rw [mem_liftBlocks_of_mem hd hb]
  simp only [mem_filter, mem_univ, true_and]
  rcases hC b.val b.property with h | h
  · exact iff_of_true (h (hx b)) (h hb)
  · exact iff_of_false (disjoint_left.1 h (hx b)) (disjoint_left.1 h hb)

omit hd in
/-- A nonempty union of blocks contains a representative. -/
theorem IsRepTuple.filter_mem_nonempty (hcover : P.sup id = univ) {C : Finset X}
    (hC : IsBlockUnion P C) (hne : C.Nonempty) : (univ.filter fun b => x b ∈ C).Nonempty := by
  obtain ⟨y, hy⟩ := hne
  obtain ⟨b, hb⟩ := exists_block hcover y
  rcases hC b.val b.property with h | h
  · exact ⟨b, mem_filter.2 ⟨mem_univ b, h (hx b)⟩⟩
  · exact absurd hy (disjoint_left.1 h hb)

omit hd in
/-- A union of blocks with a nonempty complement misses a representative. -/
theorem IsRepTuple.compl_filter_mem_nonempty (hcover : P.sup id = univ) {C : Finset X}
    (hC : IsBlockUnion P C) (hne : Cᶜ.Nonempty) : (univ.filter fun b => x b ∈ C)ᶜ.Nonempty := by
  obtain ⟨y, hy⟩ := hne
  obtain ⟨b, hb⟩ := exists_block hcover y
  rcases hC b.val b.property with h | h
  · exact absurd (h hb) (mem_compl.1 hy)
  · exact ⟨b, mem_compl.2 fun hb' => disjoint_left.1 h (hx b) (mem_filter.1 hb').2⟩

omit hd hx in
/-- A side of a tree with the blocks of `P` as sides is a union of blocks, or it or its complement
lies inside a block. -/
theorem IsUnrootedTree.isBlockUnion_or {T : Finset (Finset X)} (hT : IsUnrootedTree T)
    (hall : ∀ B ∈ P, B ∈ T) {C : Finset X} (hC : C ∈ T) :
    IsBlockUnion P C ∨ (∃ B ∈ P, C ⊆ B) ∨ ∃ B ∈ P, C ∪ B = univ := by
  by_contra hcon
  push Not at hcon
  obtain ⟨h1, h2, h3⟩ := hcon
  unfold IsBlockUnion at h1
  push Not at h1
  obtain ⟨B, hB, hnot1, hnot2⟩ := h1
  rcases hT.compatible hC (hall B hB) with h | h | h | h
  · exact h2 B hB h
  · exact hnot1 h
  · exact hnot2 h.symm
  · exact h3 B hB h

/-- The restriction to representatives of a tree with the blocks as sides, without mentioning the
representatives: its sides are the sets of blocks whose lifts are sides of the tree. -/
theorem IsRepTuple.mem_pullTree_iff (hcover : P.sup id = univ) {T : Finset (Finset X)}
    (hT : IsUnrootedTree T) (hall : ∀ B ∈ P, B ∈ T) {A : Finset {B // B ∈ P}} :
    A ∈ pullTree x T ↔ liftBlocks P A ∈ T ∧ A.Nonempty ∧ Aᶜ.Nonempty := by
  constructor
  · intro hA
    obtain ⟨⟨C, hC, hCA⟩, h1, h2⟩ := mem_pullTree.1 hA
    refine ⟨?_, h1, h2⟩
    rcases hT.isBlockUnion_or hall hC with hU | ⟨B, hB, hsub⟩ | ⟨B, hB, hu⟩
    · rw [← hCA, hx.liftBlocks_filter_mem hd hcover hU]
      exact hC
    · have hAe : A = {⟨B, hB⟩} := by
        have key : ∀ c ∈ A, c = ⟨B, hB⟩ := fun c hc => by
          rw [← hCA] at hc
          exact block_eq_of_mem hd (hx c) (hsub (mem_filter.1 hc).2)
        obtain ⟨b, hb⟩ := h1
        ext c
        rw [mem_singleton]
        exact ⟨key c, fun e => e ▸ key b hb ▸ hb⟩
      rw [hAe, liftBlocks_singleton]
      exact hall B hB
    · have hAe : Aᶜ = {⟨B, hB⟩} := by
        have key : ∀ c ∈ Aᶜ, c = ⟨B, hB⟩ := fun c hc => by
          have hxc : x c ∉ C := fun h =>
            mem_compl.1 hc (hCA ▸ mem_filter.2 ⟨mem_univ c, h⟩)
          have hxu : x c ∈ C ∪ B := hu ▸ mem_univ _
          exact block_eq_of_mem hd (hx c) ((mem_union.1 hxu).resolve_left hxc)
        obtain ⟨b, hb⟩ := h2
        ext c
        rw [mem_singleton]
        exact ⟨key c, fun e => e ▸ key b hb ▸ hb⟩
      rw [← compl_compl A, hAe, liftBlocks_compl hd hcover, liftBlocks_singleton]
      exact hT.compl_mem (hall B hB)
  · rintro ⟨h1, h2, h3⟩
    exact mem_pullTree.2 ⟨⟨_, h1, hx.filter_mem_liftBlocks hd A⟩, h2, h3⟩

omit hx in
/-- A tree with the blocks as sides has the same restriction to any choice of representatives. -/
theorem pullTree_eq_of_forall_mem (hcover : P.sup id = univ) {T : Finset (Finset X)}
    (hT : IsUnrootedTree T) (hall : ∀ B ∈ P, B ∈ T) {x x' : {B // B ∈ P} → X}
    (hx : IsRepTuple P x) (hx' : IsRepTuple P x') : pullTree x T = pullTree x' T := by
  ext A
  rw [hx.mem_pullTree_iff hd hcover hT hall, hx'.mem_pullTree_iff hd hcover hT hall]

/-- For a tree with the blocks as sides, the sides that are unions of blocks are the lifts of its
restriction to representatives. -/
theorem filter_isBlockUnion_eq_image_pullTree (hcover : P.sup id = univ) {T : Finset (Finset X)}
    (hT : IsUnrootedTree T) (hall : ∀ B ∈ P, B ∈ T) :
    T.filter (IsBlockUnion P) = (pullTree x T).image (liftBlocks P) := by
  ext A
  simp only [mem_filter, mem_image]
  constructor
  · rintro ⟨hA, hU⟩
    refine ⟨univ.filter fun b => x b ∈ A, mem_pullTree.2 ⟨⟨A, hA, rfl⟩,
      hx.filter_mem_nonempty hcover hU (hT.nonempty_of_mem hA),
      hx.compl_filter_mem_nonempty hcover hU (hT.nonempty_of_mem (hT.compl_mem hA))⟩,
      hx.liftBlocks_filter_mem hd hcover hU⟩
  · rintro ⟨C, hC, rfl⟩
    exact ⟨((hx.mem_pullTree_iff hd hcover hT hall).1 hC).1, isBlockUnion_liftBlocks hd C⟩

end Restrict

/-! ### Attaching rooted subtrees at the leaves of a tree on the blocks -/

section Attach

variable {P : Finset (Finset X)} {T₀ : Finset (Finset {B // B ∈ P})} {T : Finset (Finset X)}

/-- `T` arises from the tree `T₀` on the blocks of `P` by attaching rooted subtrees on the taxa of each
block at the leaf of `T₀` labelled by that block (ECToBlob, lines 495-497 of the paper): the sides of `T`
that are unions of blocks are the lifts of the sides of `T₀`. Each block is then a side of `T`, and the
other sides lie inside a block or have their complement inside one (`IsUnrootedTree.isBlockUnion_or`):
they are the clusters of the attached subtrees, with their complements. `attachSubtrees` is the
construction from arbitrary rooted subtrees, and `isBlockAttachment_splice` says that a splice is such a
tree. -/
def IsBlockAttachment (P : Finset (Finset X)) (T₀ : Finset (Finset {B // B ∈ P}))
    (T : Finset (Finset X)) : Prop :=
  T.filter (IsBlockUnion P) = T₀.image (liftBlocks P)

omit [Fintype X] in
/-- The sides of `T₀` are sides of a tree attached to it, through their lifts, and so the blocks are:
they are the lifts of the leaves of `T₀`. -/
theorem IsBlockAttachment.block_mem (h : IsBlockAttachment P T₀ T) (hT₀ : IsUnrootedTree T₀)
    (hY : 2 ≤ Fintype.card {B // B ∈ P}) {B : Finset X} (hB : B ∈ P) : B ∈ T := by
  have hmem : B ∈ T₀.image (liftBlocks P) := mem_image.2 ⟨{⟨B, hB⟩},
    (hT₀.isSplitFamily hY).singleton_mem _, liftBlocks_singleton _⟩
  rw [← h] at hmem
  exact (mem_filter.1 hmem).1

/-- **Restricting an attachment.** Whatever the attached subtrees are, restricting to any choice of
representatives of the blocks gives back the tree on the blocks. -/
theorem IsBlockAttachment.pullTree_eq (h : IsBlockAttachment P T₀ T)
    (hd : ∀ B ∈ P, ∀ C ∈ P, B ≠ C → Disjoint B C) (hcover : P.sup id = univ)
    (hT₀ : IsUnrootedTree T₀) (hT : IsUnrootedTree T) (hY : 2 ≤ Fintype.card {B // B ∈ P})
    {x : {B // B ∈ P} → X} (hx : IsRepTuple P x) : pullTree x T = T₀ := by
  have hall : ∀ B ∈ P, B ∈ T := fun B hB => h.block_mem hT₀ hY hB
  ext A
  rw [hx.mem_pullTree_iff hd hcover hT hall]
  constructor
  · rintro ⟨hA, -, -⟩
    have hmem : liftBlocks P A ∈ T.filter (IsBlockUnion P) :=
      mem_filter.2 ⟨hA, isBlockUnion_liftBlocks hd A⟩
    rw [h] at hmem
    obtain ⟨A', hA', he⟩ := mem_image.1 hmem
    have hAA : A' = A := by
      rw [← hx.filter_mem_liftBlocks hd A', he, hx.filter_mem_liftBlocks hd A]
    exact hAA ▸ hA'
  · intro hA
    have hmem : liftBlocks P A ∈ T.filter (IsBlockUnion P) := by
      rw [h]
      exact mem_image_of_mem _ hA
    exact ⟨(mem_filter.1 hmem).1, hT₀.nonempty_of_mem hA, hT₀.nonempty_of_mem (hT₀.compl_mem hA)⟩

/-- A proper union of blocks inside a block, or with its complement inside one, is that block or its
complement, so the lift of a side of any tree on the blocks. -/
theorem mem_image_liftBlocks_of_subset (hd : ∀ B ∈ P, ∀ C ∈ P, B ≠ C → Disjoint B C)
    (hcover : P.sup id = univ) (hS : IsSplitFamily T₀) {A : Finset X} (hU : IsBlockUnion P A)
    (hne : A.Nonempty) (hne' : Aᶜ.Nonempty) {B : Finset X} (hB : B ∈ P) (h : A ⊆ B ∨ Aᶜ ⊆ B) :
    A ∈ T₀.image (liftBlocks P) := by
  rcases h with h | h
  · have hBA : B ⊆ A := (hU B hB).resolve_right fun hdis => by
      obtain ⟨y, hy⟩ := hne
      exact disjoint_left.1 hdis (h hy) hy
    exact mem_image.2 ⟨{⟨B, hB⟩}, hS.singleton_mem _, by
      rw [liftBlocks_singleton]
      exact Subset.antisymm hBA h⟩
  · have hdis : Disjoint B A := (hU B hB).resolve_left fun hsub => by
      obtain ⟨y, hy⟩ := hne'
      exact mem_compl.1 hy (hsub (h hy))
    have hAe : Aᶜ = B := Subset.antisymm h fun y hy => mem_compl.2 (disjoint_left.1 hdis hy)
    have hBA : Bᶜ = A := by rw [← hAe, compl_compl]
    refine mem_image.2 ⟨{⟨B, hB⟩}ᶜ, hS.compl_mem _ (hS.singleton_mem _), ?_⟩
    rw [liftBlocks_compl hd hcover, liftBlocks_singleton]
    exact hBA

/-- **A splice is an attachment.** Splicing `T₀` at the multifurcation `P` of `TB` attaches at each leaf
of `T₀` the rooted subtree that the rest of the spliced tree forms on that block. -/
theorem isBlockAttachment_splice {TB : Finset (Finset X)} (hTB : IsUnrootedTree TB)
    {L : Finset (Finset X) → Finset (Finset X)}
    (hL : ∀ P ∈ multifurcations TB, IsBlockFamily P (L P)) (hP : P ∈ multifurcations TB)
    (hT₀ : IsUnrootedTree T₀) (hLP : L P = T₀.image (liftBlocks P)) :
    IsBlockAttachment P T₀ (splice TB L) := by
  obtain ⟨hV, h4⟩ := mem_multifurcations.1 hP
  have hY : 2 ≤ Fintype.card {B // B ∈ P} := by
    rw [Fintype.card_coe]
    omega
  have hS := hT₀.isSplitFamily hY
  have hT := splice_isUnrootedTree hTB hL
  ext A
  rw [mem_filter]
  constructor
  · rintro ⟨hA, hU⟩
    have key : ∀ B ∈ P, (A ⊆ B ∨ Aᶜ ⊆ B) → A ∈ T₀.image (liftBlocks P) := fun B hB h =>
      mem_image_liftBlocks_of_subset hV.pairwiseDisjoint hV.cover hS hU (hT.nonempty_of_mem hA)
        (hT.nonempty_of_mem (hT.compl_mem hA)) hB h
    rcases mem_splice.1 hA with hA' | ⟨P', hP', hA'⟩
    · rcases hV.edge_in_block A hA' with ⟨B, hB, h⟩ | ⟨B, hB, h⟩
      · exact key B hB (Or.inl h)
      · exact key B hB (Or.inr h)
    · by_cases he : P' = P
      · rw [he, hLP] at hA'
        exact hA'
      · obtain ⟨B, hB, B', hB', hu⟩ := hV.exists_union_eq_univ hTB (mem_multifurcations.1 hP').1
          (Ne.symm he)
        have hu' : ∀ y, y ∈ B ∨ y ∈ B' := fun y => mem_union.1 (hu ▸ mem_univ y)
        rcases (hL P' hP').blockUnion A hA' B' hB' with h | h
        · refine key B hB (Or.inr fun y hy => (hu' y).resolve_right fun hy' => ?_)
          exact mem_compl.1 hy (h hy')
        · refine key B hB (Or.inl fun y hy => (hu' y).resolve_right fun hy' => ?_)
          exact disjoint_left.1 h hy' hy
  · intro hA
    obtain ⟨A₀, -, rfl⟩ := mem_image.1 hA
    exact ⟨mem_splice.2 (Or.inr ⟨P, hP, hLP ▸ hA⟩), isBlockUnion_liftBlocks hV.pairwiseDisjoint _⟩

/-- `R` is the family of clusters of a rooted tree on the taxa of `B`: nested or disjoint, with the
root `B` and the single taxa. -/
structure IsRootedTreeOn (B : Finset X) (R : Finset (Finset X)) : Prop where
  subset : ∀ A ∈ R, A ⊆ B
  nonempty : ∀ A ∈ R, A.Nonempty
  top_mem : B ∈ R
  singleton_mem : ∀ z ∈ B, {z} ∈ R
  laminar : ∀ A ∈ R, ∀ C ∈ R, A ⊆ C ∨ C ⊆ A ∨ Disjoint A C

/-- The tree on `X` from the tree `T₀` on the blocks by attaching the rooted tree `R b` on the taxa of the
block `b` at the leaf labelled by `b`: the lifts of the sides of `T₀`, the clusters of the `R b`, and their
complements. -/
def attachSubtrees (P : Finset (Finset X)) (T₀ : Finset (Finset {B // B ∈ P}))
    (R : {B // B ∈ P} → Finset (Finset X)) : Finset (Finset X) :=
  T₀.image (liftBlocks P) ∪ univ.biUnion fun b => R b ∪ (R b).image compl

theorem mem_attachSubtrees {R : {B // B ∈ P} → Finset (Finset X)} {A : Finset X} :
    A ∈ attachSubtrees P T₀ R ↔
      A ∈ T₀.image (liftBlocks P) ∨ ∃ b, A ∈ R b ∨ Aᶜ ∈ R b := by
  simp only [attachSubtrees, mem_union, mem_biUnion, mem_univ, true_and, mem_image]
  refine or_congr_right (exists_congr fun b => or_congr_right ⟨?_, fun h => ⟨Aᶜ, h, compl_compl A⟩⟩)
  rintro ⟨C, hC, rfl⟩
  rwa [compl_compl]

private theorem compat_compl_left {A C : Finset X}
    (h : A ⊆ C ∨ C ⊆ A ∨ Disjoint A C ∨ A ∪ C = univ) :
    Aᶜ ⊆ C ∨ C ⊆ Aᶜ ∨ Disjoint Aᶜ C ∨ Aᶜ ∪ C = univ := by
  rcases h with h | h | h | h
  · refine Or.inr (Or.inr (Or.inr (eq_univ_iff_forall.2 fun y => ?_)))
    by_cases hy : y ∈ A
    · exact mem_union_right _ (h hy)
    · exact mem_union_left _ (mem_compl.2 hy)
  · exact Or.inr (Or.inr (Or.inl (disjoint_left.2 fun y hy hy' => mem_compl.1 hy (h hy'))))
  · exact Or.inr (Or.inl fun y hy => mem_compl.2 (disjoint_right.1 h hy))
  · refine Or.inl fun y hy => ?_
    have : y ∈ A ∪ C := h ▸ mem_univ y
    exact (mem_union.1 this).resolve_left (mem_compl.1 hy)

variable {R : {B // B ∈ P} → Finset (Finset X)}

/-- **Attaching rooted subtrees to a tree on the blocks gives a tree.** -/
theorem attachSubtrees_isUnrootedTree (hd : ∀ B ∈ P, ∀ C ∈ P, B ≠ C → Disjoint B C)
    (hcover : P.sup id = univ) (hP : 2 ≤ P.card) (hT₀ : IsUnrootedTree T₀)
    (hR : ∀ b, IsRootedTreeOn b.val (R b)) : IsUnrootedTree (attachSubtrees P T₀ R) := by
  have hne : ∀ B ∈ P, B.Nonempty := fun B hB =>
    (hR ⟨B, hB⟩).nonempty _ (hR ⟨B, hB⟩).top_mem
  have hfam := isBlockFamily_image_liftBlocks hne hd hcover hT₀
  have hY : 2 ≤ Fintype.card {B // B ∈ P} := by rwa [Fintype.card_coe]
  obtain ⟨x, hx⟩ := exists_isRepTuple hne
  have hX : 2 ≤ Fintype.card X := hY.trans (Fintype.card_le_of_injective x (hx.injective hd))
  -- a cluster of `R b` misses another block
  have hout : ∀ b, ∀ A ∈ R b, Aᶜ.Nonempty := by
    intro b A hA
    obtain ⟨c, hc⟩ : ∃ c : {B // B ∈ P}, c ≠ b := Fintype.exists_ne_of_one_lt_card (by omega) b
    obtain ⟨y, hy⟩ := hne c.val c.property
    refine ⟨y, mem_compl.2 fun hyA => ?_⟩
    exact hc (block_eq_of_mem hd hy ((hR b).subset A hA hyA))
  -- the members before taking complements are compatible
  let Base : Finset X → Prop := fun A => A ∈ T₀.image (liftBlocks P) ∨ ∃ b, A ∈ R b
  have hbase : ∀ {A C}, Base A → Base C → A ⊆ C ∨ C ⊆ A ∨ Disjoint A C ∨ A ∪ C = univ := by
    -- a lift and a cluster
    have hlift : ∀ {A C}, A ∈ T₀.image (liftBlocks P) → (∃ b, C ∈ R b) →
        A ⊆ C ∨ C ⊆ A ∨ Disjoint A C ∨ A ∪ C = univ := by
      rintro A C hA ⟨b, hC⟩
      rcases hfam.blockUnion A hA b.val b.property with h | h
      · exact Or.inr (Or.inl (((hR b).subset C hC).trans h))
      · exact Or.inr (Or.inr (Or.inl (h.symm.mono_right ((hR b).subset C hC))))
    rintro A C (hA | hA) (hC | hC)
    · exact hfam.compatible A hA C hC
    · exact hlift hA hC
    · exact compat_symm (hlift hC hA)
    · obtain ⟨b, hA⟩ := hA
      obtain ⟨c, hC⟩ := hC
      by_cases hbc : b = c
      · subst hbc
        rcases (hR b).laminar A hA C hC with h | h | h
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr (Or.inl h))
      · refine Or.inr (Or.inr (Or.inl (disjoint_left.2 fun y hy hy' => hbc ?_)))
        exact block_eq_of_mem hd ((hR b).subset A hA hy) ((hR c).subset C hC hy')
  -- every member is a base one or the complement of one
  have hor : ∀ {A}, A ∈ attachSubtrees P T₀ R → Base A ∨ Base Aᶜ := by
    intro A hA
    rcases mem_attachSubtrees.1 hA with h | ⟨b, h | h⟩
    · exact Or.inl (Or.inl h)
    · exact Or.inl (Or.inr ⟨b, h⟩)
    · exact Or.inr (Or.inr ⟨b, h⟩)
  refine (isUnrootedTree_iff hX _).2 ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro A hA
    rcases mem_attachSubtrees.1 hA with h | ⟨b, h | h⟩
    · exact hfam.nonempty A h
    · exact (hR b).nonempty A h
    · simpa only [compl_compl] using hout b _ h
  · intro A hA
    rcases mem_attachSubtrees.1 hA with h | ⟨b, h | h⟩
    · exact hfam.compl_nonempty A h
    · exact hout b A h
    · exact (hR b).nonempty _ h
  · intro A hA
    rcases mem_attachSubtrees.1 hA with h | ⟨b, h | h⟩
    · exact mem_attachSubtrees.2 (Or.inl (hfam.compl_mem A h))
    · exact mem_attachSubtrees.2 (Or.inr ⟨b, Or.inr (by rwa [compl_compl])⟩)
    · exact mem_attachSubtrees.2 (Or.inr ⟨b, Or.inl h⟩)
  · intro y
    obtain ⟨b, hb⟩ := exists_block hcover y
    exact mem_attachSubtrees.2 (Or.inr ⟨b, Or.inl ((hR b).singleton_mem y hb)⟩)
  · intro A hA C hC
    rcases hor hA with h | h <;> rcases hor hC with h' | h'
    · exact hbase h h'
    · have := compat_compl_left (compat_symm (hbase h h'))
      rw [compl_compl] at this
      exact compat_symm this
    · have := compat_compl_left (hbase h h')
      rwa [compl_compl] at this
    · have := compat_compl_left (compat_symm (compat_compl_left (hbase h h')))
      rw [compl_compl, compl_compl] at this
      exact compat_symm this

/-- The tree `attachSubtrees P T₀ R` arises from `T₀` by attaching rooted subtrees at its leaves. -/
theorem isBlockAttachment_attachSubtrees (hd : ∀ B ∈ P, ∀ C ∈ P, B ≠ C → Disjoint B C)
    (hcover : P.sup id = univ) (hP : 2 ≤ P.card) (hT₀ : IsUnrootedTree T₀)
    (hR : ∀ b, IsRootedTreeOn b.val (R b)) : IsBlockAttachment P T₀ (attachSubtrees P T₀ R) := by
  have hT := attachSubtrees_isUnrootedTree hd hcover hP hT₀ hR
  have hY : 2 ≤ Fintype.card {B // B ∈ P} := by rwa [Fintype.card_coe]
  have hS := hT₀.isSplitFamily hY
  ext A
  rw [mem_filter]
  constructor
  · rintro ⟨hA, hU⟩
    rcases mem_attachSubtrees.1 hA with h | ⟨b, h | h⟩
    · exact h
    · exact mem_image_liftBlocks_of_subset hd hcover hS hU (hT.nonempty_of_mem hA)
        (hT.nonempty_of_mem (hT.compl_mem hA)) b.property (Or.inl ((hR b).subset A h))
    · exact mem_image_liftBlocks_of_subset hd hcover hS hU (hT.nonempty_of_mem hA)
        (hT.nonempty_of_mem (hT.compl_mem hA)) b.property (Or.inr ((hR b).subset _ h))
  · intro hA
    obtain ⟨A₀, -, rfl⟩ := mem_image.1 hA
    exact ⟨mem_attachSubtrees.2 (Or.inl hA), isBlockUnion_liftBlocks hd _⟩

/-- Conversely, a tree that `IsBlockAttachment` calls attached to `T₀` is the construction, with for rooted
subtrees its sides inside the blocks: the predicate says exactly what the paper says. -/
theorem IsBlockAttachment.exists_eq_attachSubtrees (h : IsBlockAttachment P T₀ T)
    (hT₀ : IsUnrootedTree T₀) (hT : IsUnrootedTree T) (hP : 2 ≤ P.card) :
    ∃ R : {B // B ∈ P} → Finset (Finset X), (∀ b, IsRootedTreeOn b.val (R b)) ∧
      T = attachSubtrees P T₀ R := by
  have hY : 2 ≤ Fintype.card {B // B ∈ P} := by rwa [Fintype.card_coe]
  have hall : ∀ B ∈ P, B ∈ T := fun B hB => h.block_mem hT₀ hY hB
  obtain ⟨B₀, hB₀⟩ := card_pos.1 (by omega : 0 < P.card)
  have hS := hT.isSplitFamily (hT.two_le_card_of_mem (hall B₀ hB₀))
  refine ⟨fun b => T.filter (· ⊆ b.val), fun b => ⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · exact fun A hA => (mem_filter.1 hA).2
  · exact fun A hA => hT.nonempty_of_mem (mem_filter.1 hA).1
  · exact mem_filter.2 ⟨hall _ b.property, Subset.refl _⟩
  · exact fun z hz => mem_filter.2 ⟨hS.singleton_mem z, singleton_subset_iff.2 hz⟩
  · intro A hA C hC
    obtain ⟨hAT, hAb⟩ := mem_filter.1 hA
    obtain ⟨hCT, hCb⟩ := mem_filter.1 hC
    rcases hT.compatible hAT hCT with h' | h' | h' | h'
    · exact Or.inl h'
    · exact Or.inr (Or.inl h')
    · exact Or.inr (Or.inr h')
    · exfalso
      obtain ⟨y, hy⟩ := hT.nonempty_of_mem (hT.compl_mem (hall _ b.property))
      have hyu : y ∈ A ∪ C := h' ▸ mem_univ y
      rcases mem_union.1 hyu with hyA | hyC
      · exact mem_compl.1 hy (hAb hyA)
      · exact mem_compl.1 hy (hCb hyC)
  · ext A
    rw [mem_attachSubtrees]
    constructor
    · intro hA
      rcases hT.isBlockUnion_or hall hA with hU | ⟨B, hB, hsub⟩ | ⟨B, hB, hu⟩
      · exact Or.inl (h ▸ mem_filter.2 ⟨hA, hU⟩)
      · exact Or.inr ⟨⟨B, hB⟩, Or.inl (mem_filter.2 ⟨hA, hsub⟩)⟩
      · refine Or.inr ⟨⟨B, hB⟩, Or.inr (mem_filter.2 ⟨hT.compl_mem hA, fun y hy => ?_⟩)⟩
        have hyu : y ∈ A ∪ B := hu ▸ mem_univ y
        exact (mem_union.1 hyu).resolve_left (mem_compl.1 hy)
    · rintro (hA | ⟨b, hA | hA⟩)
      · rw [← h] at hA
        exact (mem_filter.1 hA).1
      · exact (mem_filter.1 hA).1
      · simpa only [compl_compl] using hT.compl_mem (mem_filter.1 hA).1

end Attach

/-! ### Reattaching the taxa removed by a restriction -/

section Reattach

variable {P : Finset (Finset X)}

/-- The tree `T`, with the blocks of `P` as sides, after replacing its restriction to representatives
of the blocks by a refinement `R` and reattaching the removed taxa: each leaf of `R` is replaced by the
subtree of `T` on that block. The sides of `T` inside a block stay, and the sides of `T` that are unions
of blocks are lifts of sides of `R`. -/
def reattach (P : Finset (Finset X)) (T : Finset (Finset X)) (R : Finset (Finset {B // B ∈ P})) :
    Finset (Finset X) :=
  T ∪ R.image (liftBlocks P)

omit [Fintype X] in
theorem subset_reattach (T : Finset (Finset X)) (R : Finset (Finset {B // B ∈ P})) :
    T ⊆ reattach P T R :=
  subset_union_left

variable (hd : ∀ B ∈ P, ∀ C ∈ P, B ≠ C → Disjoint B C) (hcover : P.sup id = univ)
  {T : Finset (Finset X)} (hT : IsUnrootedTree T) (hall : ∀ B ∈ P, B ∈ T)
  {R : Finset (Finset {B // B ∈ P})} (hR : IsUnrootedTree R)
  {x : {B // B ∈ P} → X} (hx : IsRepTuple P x) (hsub : pullTree x T ⊆ R)

include hd hcover hT hall hR hx hsub in
private theorem compatible_liftBlocks_of_mem {A : Finset X} (hA : A ∈ T) {C : Finset {B // B ∈ P}}
    (hC : C ∈ R) :
    A ⊆ liftBlocks P C ∨ liftBlocks P C ⊆ A ∨ Disjoint A (liftBlocks P C) ∨
      A ∪ liftBlocks P C = univ := by
  have hne : ∀ B ∈ P, B.Nonempty := fun B hB => hT.nonempty_of_mem (hall B hB)
  have hfam := isBlockFamily_image_liftBlocks hne hd hcover hR
  rcases hT.isBlockUnion_or hall hA with hU | ⟨B, hB, hAB⟩ | ⟨B, hB, hu⟩
  · have hmem : (univ.filter fun b => x b ∈ A) ∈ R := hsub (mem_pullTree.2 ⟨⟨A, hA, rfl⟩,
      hx.filter_mem_nonempty hcover hU (hT.nonempty_of_mem hA),
      hx.compl_filter_mem_nonempty hcover hU (hT.nonempty_of_mem (hT.compl_mem hA))⟩)
    have := hfam.compatible _ (mem_image_of_mem _ hmem) _ (mem_image_of_mem _ hC)
    rwa [hx.liftBlocks_filter_mem hd hcover hU] at this
  · rcases isBlockUnion_liftBlocks hd C B hB with h | h
    · exact Or.inl (hAB.trans h)
    · exact Or.inr (Or.inr (Or.inl (h.mono_left hAB)))
  · rcases isBlockUnion_liftBlocks hd C B hB with h | h
    · refine Or.inr (Or.inr (Or.inr (eq_univ_iff_forall.2 fun y => ?_)))
      have : y ∈ A ∪ B := hu ▸ mem_univ y
      rcases mem_union.1 this with h' | h'
      · exact mem_union_left _ h'
      · exact mem_union_right _ (h h')
    · refine Or.inr (Or.inl fun y hy => ?_)
      have : y ∈ A ∪ B := hu ▸ mem_univ y
      rcases mem_union.1 this with h' | h'
      · exact h'
      · exact absurd hy (disjoint_left.1 h h')

include hd hcover hT hall hR hx hsub in
/-- Reattaching the removed taxa to a refinement of the restriction gives a tree. -/
theorem reattach_isUnrootedTree (hP : 2 ≤ P.card) : IsUnrootedTree (reattach P T R) := by
  have hne : ∀ B ∈ P, B.Nonempty := fun B hB => hT.nonempty_of_mem (hall B hB)
  have hfam := isBlockFamily_image_liftBlocks hne hd hcover hR
  have hX : 2 ≤ Fintype.card X :=
    (by rwa [Fintype.card_coe] : 2 ≤ Fintype.card {B // B ∈ P}).trans
      (Fintype.card_le_of_injective x (hx.injective hd))
  have hSF := hT.isSplitFamily hX
  have hmem : ∀ A, A ∈ reattach P T R ↔ A ∈ T ∨ A ∈ R.image (liftBlocks P) := fun A => mem_union
  have hcompat : ∀ A ∈ T, ∀ A' ∈ R.image (liftBlocks P),
      A ⊆ A' ∨ A' ⊆ A ∨ Disjoint A A' ∨ A ∪ A' = univ := by
    intro A hA A' hA'
    obtain ⟨C, hC, rfl⟩ := mem_image.1 hA'
    exact compatible_liftBlocks_of_mem hd hcover hT hall hR hx hsub hA hC
  refine (isUnrootedTree_iff hX _).2 ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro A hA
    rcases (hmem A).1 hA with h | h
    · exact hSF.nonempty A h
    · exact hfam.nonempty A h
  · intro A hA
    rcases (hmem A).1 hA with h | h
    · exact hSF.compl_nonempty A h
    · exact hfam.compl_nonempty A h
  · intro A hA
    rcases (hmem A).1 hA with h | h
    · exact (hmem _).2 (Or.inl (hSF.compl_mem A h))
    · exact (hmem _).2 (Or.inr (hfam.compl_mem A h))
  · exact fun y => (hmem _).2 (Or.inl (hSF.singleton_mem y))
  · intro A hA B hB
    rcases (hmem A).1 hA with h | h <;> rcases (hmem B).1 hB with h' | h'
    · exact hSF.compatible A h B h'
    · exact hcompat A h B h'
    · exact compat_symm (hcompat B h' A h)
    · exact hfam.compatible A h B h'

include hd hR in
omit [Fintype X] in
/-- The restriction of the reattached tree to any representatives contains the refinement. -/
theorem subset_pullTree_reattach {y : {B // B ∈ P} → X} (hy : IsRepTuple P y) :
    R ⊆ pullTree y (reattach P T R) := fun C hC =>
  mem_pullTree.2 ⟨⟨liftBlocks P C, mem_union_right _ (mem_image_of_mem _ hC),
    hy.filter_mem_liftBlocks hd C⟩, hR.nonempty_of_mem hC, hR.nonempty_of_mem (hR.compl_mem hC)⟩

end Reattach

/-! ### A sum over quartet trees in distinct blocks, as a sum over representative tuples -/

section RepSum

variable {P : Finset (Finset X)}

/-- A set of taxa in distinct blocks lies among some representatives of the blocks. -/
theorem exists_isRepTuple_superset (hne : ∀ B ∈ P, B.Nonempty) (hcover : P.sup id = univ)
    {q : Finset X} (hI : InDistinctBlocks P q) : ∃ x, IsRepTuple P x ∧ q ⊆ univ.image x := by
  have h : ∀ b : {B // B ∈ P}, ∃ y ∈ b.val, (b.val ∩ q).Nonempty → y ∈ q := fun b => by
    by_cases hb : (b.val ∩ q).Nonempty
    · obtain ⟨y, hy⟩ := hb
      exact ⟨y, (mem_inter.1 hy).1, fun _ => (mem_inter.1 hy).2⟩
    · obtain ⟨y, hy⟩ := hne b.val b.property
      exact ⟨y, hy, fun h => absurd h hb⟩
  choose x hx hxq using h
  refine ⟨x, hx, fun y hy => ?_⟩
  obtain ⟨b, hb⟩ := exists_block hcover y
  have hmem : (b.val ∩ q).Nonempty := ⟨y, mem_inter.2 ⟨hb, hy⟩⟩
  have : x b = y := card_le_one.1 (hI b.val b.property) _ (mem_inter.2 ⟨hx b, hxq b hmem⟩) _
    (mem_inter.2 ⟨hb, hy⟩)
  exact mem_image.2 ⟨b, mem_univ b, this⟩

/-- The weight of a quartet tree in the sum over representative tuples: the product of the sizes of the
blocks of `P` meeting its taxa. -/
def blockWeight (P : Finset (Finset X)) (s : QuartetTree X) : ℝ :=
  ∏ B ∈ P.filter fun B => (B ∩ s.taxa).Nonempty, (B.card : ℝ)

/-- Counting the representative tuples containing the taxa of a quartet tree in distinct blocks. -/
theorem card_rep_mul_blockWeight
    (hdisj : ∀ B ∈ P, ∀ C ∈ P, B ≠ C → Disjoint B C)
    (hcover : P.sup id = univ) {s : QuartetTree X} (hI : InDistinctBlocks P s.taxa) :
    (((univ : Finset ({B // B ∈ P} → X)).filter
        (fun x => (∀ B, x B ∈ B.val) ∧ s.taxa ⊆ univ.image x)).card : ℝ) * blockWeight P s =
      ∏ B ∈ P, (B.card : ℝ) := by
  set q := s.taxa with hq
  let F : (b : {B // B ∈ P}) → Finset X := fun b =>
    if (b.val ∩ q).Nonempty then b.val ∩ q else b.val
  have hfil : (univ : Finset ({B // B ∈ P} → X)).filter
      (fun x => (∀ B, x B ∈ B.val) ∧ q ⊆ univ.image x) = Fintype.piFinset F := by
    ext x
    simp only [mem_filter, mem_univ, true_and, Fintype.mem_piFinset]
    constructor
    · rintro ⟨hrep, hsub⟩ b
      by_cases hb : (b.val ∩ q).Nonempty
      · simp only [F, ite_eq_left hb]
        obtain ⟨y, hy⟩ := hb
        obtain ⟨hyb, hyq⟩ := mem_inter.1 hy
        obtain ⟨c, -, rfl⟩ := mem_image.1 (hsub hyq)
        have : c = b := block_eq_of_mem hdisj (hrep c) hyb
        exact this ▸ hy
      · simp only [F, ite_eq_right hb]
        exact hrep b
    · intro h
      have hrep : ∀ b, x b ∈ b.val := by
        intro b
        have := h b
        by_cases hb : (b.val ∩ q).Nonempty
        · simp only [F, ite_eq_left hb] at this
          exact (mem_inter.1 this).1
        · simpa only [F, ite_eq_right hb] using this
      refine ⟨hrep, fun y hy => ?_⟩
      obtain ⟨b, hb⟩ := exists_block hcover y
      have hne' : (b.val ∩ q).Nonempty := ⟨y, mem_inter.2 ⟨hb, hy⟩⟩
      have hxb := h b
      simp only [F, ite_eq_left hne'] at hxb
      have : x b = y := card_le_one.1 (hI b.val b.property) _ hxb _ (mem_inter.2 ⟨hb, hy⟩)
      exact mem_image.2 ⟨b, mem_univ b, this⟩
  rw [hfil, Fintype.card_piFinset, blockWeight, prod_filter]
  push_cast
  have hcoe : ∏ b : {B // B ∈ P}, ((F b).card : ℝ) =
      ∏ B ∈ P, ((if (B ∩ q).Nonempty then B ∩ q else B).card : ℝ) :=
    prod_coe_sort P fun B => ((if (B ∩ q).Nonempty then B ∩ q else B).card : ℝ)
  rw [hcoe, ← prod_mul_distrib]
  refine prod_congr rfl fun B hB => ?_
  by_cases hb : (B ∩ q).Nonempty
  · have h1 : (B ∩ q).card = 1 := le_antisymm (hI B hB) (card_pos.2 hb)
    rw [ite_eq_left hb, ite_eq_left hb, h1]
    simp
  · rw [ite_eq_right hb, ite_eq_right hb, mul_one]

/-- The sum at the representative tuple `x`, weighted by the block sizes, of `w` over the quartet trees
that `T` displays on taxa among the representatives. -/
def innerSum (P : Finset (Finset X)) (w : QuartetTree X → ℝ) (T : Finset (Finset X))
    (x : {B // B ∈ P} → X) : ℝ :=
  ∑ s, if InDistinctBlocks P s.taxa ∧ Displays T s ∧ s.taxa ⊆ univ.image x then
    blockWeight P s * w s else 0

/-- A score over quartet trees in distinct blocks, multiplied by the number of representative tuples,
is the sum of the inner sums over the tuples. A quartet tree occurs once for each choice of
representatives of the blocks it does not use, which the block weights compensate. -/
theorem prod_card_mul_sum_eq_sum_innerSum (hdisj : ∀ B ∈ P, ∀ C ∈ P, B ≠ C → Disjoint B C)
    (hcover : P.sup id = univ) (w : QuartetTree X → ℝ) (T : Finset (Finset X)) :
    (∏ B ∈ P, (B.card : ℝ)) * (∑ s, if InDistinctBlocks P s.taxa ∧ Displays T s then w s else 0) =
      ∑ x ∈ (univ : Finset ({B // B ∈ P} → X)).filter (fun x => ∀ B, x B ∈ B.val),
        innerSum P w T x := by
  simp only [innerSum]
  rw [sum_comm, mul_sum]
  refine sum_congr rfl fun s _ => ?_
  by_cases hID : InDistinctBlocks P s.taxa ∧ Displays T s
  · rw [ite_eq_left hID]
    have hstep : ∀ x : {B // B ∈ P} → X,
        (if InDistinctBlocks P s.taxa ∧ Displays T s ∧ s.taxa ⊆ univ.image x then
          blockWeight P s * w s else 0) =
        if s.taxa ⊆ univ.image x then blockWeight P s * w s else 0 := by
      intro x
      by_cases hc : s.taxa ⊆ univ.image x
      · rw [ite_eq_left ⟨hID.1, hID.2, hc⟩, ite_eq_left hc]
      · rw [ite_eq_right fun h => hc h.2.2, ite_eq_right hc]
    simp only [hstep]
    rw [← sum_filter, filter_filter, sum_const, nsmul_eq_mul, ← mul_assoc,
      card_rep_mul_blockWeight hdisj hcover hID.1]
  · rw [ite_eq_right hID, mul_zero]
    exact (sum_eq_zero fun x _ => ite_eq_right fun h => hID ⟨h.1, h.2.1⟩).symm

/-- The product of the sizes of the blocks of a quartet tree on the blocks. -/
def blockSizeProd (s₀ : QuartetTree {B // B ∈ P}) : ℝ :=
  ∏ b ∈ s₀.taxa, (b.val.card : ℝ)

omit [Fintype X] in
theorem blockSizeProd_pos (hne : ∀ B ∈ P, B.Nonempty) (s₀ : QuartetTree {B // B ∈ P}) :
    0 < blockSizeProd s₀ :=
  prod_pos fun b _ => by exact_mod_cast card_pos.2 (hne b.val b.property)

omit [Fintype X] in
theorem blockWeight_map (hd : ∀ B ∈ P, ∀ C ∈ P, B ≠ C → Disjoint B C)
    {x : {B // B ∈ P} → X} (hx : IsRepTuple P x) (s₀ : QuartetTree {B // B ∈ P}) :
    blockWeight P (s₀.map (hx.injective hd)) = blockSizeProd s₀ := by
  have hfil : (P.filter fun B => (B ∩ (s₀.map (hx.injective hd)).taxa).Nonempty) =
      s₀.taxa.image Subtype.val := by
    ext B
    simp only [mem_filter, mem_image, QuartetTree.map_taxa]
    constructor
    · rintro ⟨hB, y, hy⟩
      obtain ⟨hyB, hyt⟩ := mem_inter.1 hy
      obtain ⟨b, hb, rfl⟩ := mem_image.1 hyt
      have : b = ⟨B, hB⟩ := block_eq_of_mem hd (hx b) hyB
      exact ⟨b, hb, by rw [this]⟩
    · rintro ⟨b, hb, rfl⟩
      exact ⟨b.property, x b, mem_inter.2 ⟨hx b, mem_image_of_mem _ hb⟩⟩
  rw [blockWeight, hfil, prod_image fun a _ b _ h => Subtype.ext h, blockSizeProd]

/-- The inner sum at the representative tuple `x` is a score of the restriction of the tree to `x`. -/
theorem innerSum_eq_quartetScore_pullTree (hd : ∀ B ∈ P, ∀ C ∈ P, B ≠ C → Disjoint B C)
    {x : {B // B ∈ P} → X} (hx : IsRepTuple P x) (w : QuartetTree X → ℝ) (T : Finset (Finset X)) :
    innerSum P w T x = quartetScore (fun s₀ => blockSizeProd s₀ * w (s₀.map (hx.injective hd)))
      (pullTree x T) := by
  have hstep : ∀ s : QuartetTree X,
      (if InDistinctBlocks P s.taxa ∧ Displays T s ∧ s.taxa ⊆ univ.image x then
        blockWeight P s * w s else 0) =
      if s.taxa ⊆ univ.image x then (if Displays T s then blockWeight P s * w s else 0) else 0 := by
    intro s
    by_cases hc : s.taxa ⊆ univ.image x
    · have hI := hx.inDistinctBlocks hd hc
      simp only [hI, hc, true_and, and_true, ↓reduceIte]
    · simp only [hc, and_false, ↓reduceIte]
  simp only [innerSum, hstep]
  rw [sum_ite_taxa_subset_image (hx.injective hd), quartetScore]
  refine sum_congr rfl fun s₀ _ => ?_
  simp only [displays_pullTree_iff (hx.injective hd), blockWeight_map hd hx]

end RepSum

/-- If there is a tree, the score of any weights has a maximizing tree. -/
theorem exists_max_quartetScore {T₀ : Finset (Finset X)} (hT₀ : IsUnrootedTree T₀)
    (w : QuartetTree X → ℝ) :
    ∃ T, IsUnrootedTree T ∧ ∀ T', IsUnrootedTree T' → quartetScore w T' ≤ quartetScore w T := by
  obtain ⟨T, hT, hmax⟩ := (univ.filter fun T : Finset (Finset X) => IsUnrootedTree T).exists_max_image
    (quartetScore w) ⟨T₀, by simpa using hT₀⟩
  exact ⟨T, (mem_filter.1 hT).2, fun T' hT' => hmax T' (by simpa using hT')⟩

/-! ### Exchangeability across representatives -/

section Exchange

variable {V E : Type*} {N : RootedNetwork V E X} {p : QuartetTree X → ℝ} {P : Finset (Finset X)}

omit [Fintype X] in
/-- A weight that is exchangeable across cut edges, on a quartet tree with taxa in distinct blocks that
are cut sides, depends only on the blocks. -/
theorem map_eq_of_cutExchangeable (h₂ : CutExchangeable N p)
    (hd : ∀ B ∈ P, ∀ C ∈ P, B ≠ C → Disjoint B C)
    (hcut : ∀ B ∈ P, N.HasCutSplit (B : Set X))
    {x x' : {B // B ∈ P} → X} (hx : IsRepTuple P x) (hx' : IsRepTuple P x')
    (s₀ : QuartetTree {B // B ∈ P}) :
    p (s₀.map (hx.injective hd)) = p (s₀.map (hx'.injective hd)) := by
  have step : ∀ {y y' : {B // B ∈ P} → X} (hy : IsRepTuple P y) (hy' : IsRepTuple P y')
      {b : {B // B ∈ P}}, b ∈ s₀.taxa → y b ≠ y' b → (∀ c, c ≠ b → y c = y' c) →
      p (s₀.map (hy.injective hd)) = p (s₀.map (hy'.injective hd)) := by
    intro y y' hy hy' b hb hne hrest
    have hyi := hy.injective hd
    have hyi' := hy'.injective hd
    refine h₂ _ _ (y b) (y' b) ?_ ?_ ?_ ⟨b.val, hcut _ b.property, hy b, hy' b, ?_⟩
    · rw [QuartetTree.map_taxa]
      exact mem_image_of_mem _ hb
    · rw [QuartetTree.map_taxa]
      intro hmem
      obtain ⟨c, -, hc⟩ := mem_image.1 hmem
      have : c = b := block_eq_of_mem hd (hy c) (hc ▸ hy' b)
      exact hne (this ▸ hc)
    · rw [QuartetTree.map_val, QuartetTree.map_val, image_image]
      refine image_congr fun C hC => ?_
      simp only [Function.comp]
      have hC' : C ∈ s₀.val := hC
      by_cases hbC : b ∈ C
      · have hmem : y b ∈ C.image y := mem_image_of_mem _ hbC
        simp only [hmem, ↓reduceIte]
        ext z
        simp only [mem_image, mem_insert, mem_erase]
        constructor
        · rintro ⟨c, hc, rfl⟩
          by_cases hcb : c = b
          · subst hcb
            exact Or.inl rfl
          · refine Or.inr ⟨fun e => hcb (hyi ((hrest c hcb).trans e)), c, hc, hrest c hcb⟩
        · rintro (rfl | ⟨hz, c, hc, rfl⟩)
          · exact ⟨b, hbC, rfl⟩
          · have hcb : c ≠ b := fun e => hz (e ▸ rfl)
            exact ⟨c, hc, (hrest c hcb).symm⟩
      · have hmem : y b ∉ C.image y := fun h => by
          obtain ⟨c, hc, he⟩ := mem_image.1 h
          exact hbC (hyi he ▸ hc)
        simp only [hmem, ↓reduceIte]
        ext z
        simp only [mem_image]
        constructor
        · rintro ⟨c, hc, rfl⟩
          exact ⟨c, hc, hrest c fun e => hbC (e ▸ hc)⟩
        · rintro ⟨c, hc, rfl⟩
          exact ⟨c, hc, (hrest c fun e => hbC (e ▸ hc)).symm⟩
    · rw [disjoint_left]
      intro z hz hz'
      rw [QuartetTree.map_taxa] at hz'
      obtain ⟨hza, hzt⟩ := mem_erase.1 hz'
      obtain ⟨c, -, rfl⟩ := mem_image.1 hzt
      have : c = b := block_eq_of_mem hd (hy c) hz
      exact hza (this ▸ rfl)
  -- change one block at a time
  have key : ∀ (n : ℕ) (y : {B // B ∈ P} → X) (hy : IsRepTuple P y),
      (s₀.taxa.filter fun b => y b ≠ x' b).card = n →
      p (s₀.map (hy.injective hd)) = p (s₀.map (hx'.injective hd)) := by
    intro n
    induction n with
    | zero =>
      intro y hy hcard
      have hall : ∀ b ∈ s₀.taxa, y b = x' b := by
        intro b hb
        by_contra hne
        have : b ∈ s₀.taxa.filter fun b => y b ≠ x' b := mem_filter.2 ⟨hb, hne⟩
        rw [card_eq_zero.1 hcard] at this
        simp at this
      congr 1
      apply Subtype.ext
      rw [QuartetTree.map_val, QuartetTree.map_val]
      refine image_congr fun C hC => ?_
      exact image_congr fun c hc => hall c (s₀.subset_taxa hC hc)
    | succ n ih =>
      intro y hy hcard
      obtain ⟨b, hb⟩ := card_pos.1 (show 0 < (s₀.taxa.filter fun b => y b ≠ x' b).card by omega)
      obtain ⟨hbt, hbne⟩ := mem_filter.1 hb
      let y₂ := Function.update y b (x' b)
      have hy₂ : IsRepTuple P y₂ := by
        intro c
        by_cases hcb : c = b
        · subst hcb
          simpa [y₂] using hx' c
        · simpa [y₂, Function.update_of_ne hcb] using hy c
      have h1 := step hy hy₂ hbt (by simpa [y₂] using hbne) (fun c hcb => by
        simp [y₂, Function.update_of_ne hcb])
      refine h1.trans (ih y₂ hy₂ ?_)
      have : (s₀.taxa.filter fun c => y₂ c ≠ x' c) =
          (s₀.taxa.filter fun c => y c ≠ x' c).erase b := by
        ext c
        simp only [mem_filter, mem_erase]
        by_cases hcb : c = b
        · subst hcb
          simp [y₂]
        · simp [y₂, hcb]
      rw [this, card_erase_of_mem hb, hcard]
      rfl
  exact key _ x hx rfl

end Exchange

end Phylogenetics
