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
* `IsRepTuple`, `exists_isRepTuple`, `displays_splice_map_iff`: the restriction of a spliced tree to
  representatives of the blocks is the tree that was spliced;
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

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

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
    · exact absurd ⟨A, h, hAs⟩ (not_displays_of_inDistinctBlocks hT (mem_multifurcations.1 hP).1 hs)
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

theorem mem_liftBlocks {P : Finset (Finset X)} {A : Finset {B // B ∈ P}} {x : X} :
    x ∈ liftBlocks P A ↔ ∃ b ∈ A, x ∈ b.val := by
  simp [liftBlocks, mem_biUnion]

section Lift

variable {P : Finset (Finset X)} (hd : ∀ B ∈ P, ∀ C ∈ P, B ≠ C → Disjoint B C)

include hd

/-- The block of a taxon is unique. -/
theorem block_eq_of_mem {b c : {B // B ∈ P}} {x : X} (hb : x ∈ b.val) (hc : x ∈ c.val) : b = c := by
  by_contra hne
  exact disjoint_left.1 (hd b.val b.property c.val c.property fun e => hne (Subtype.ext e)) hb hc

theorem mem_liftBlocks_of_mem {A : Finset {B // B ∈ P}} {b : {B // B ∈ P}} {x : X}
    (hx : x ∈ b.val) : x ∈ liftBlocks P A ↔ b ∈ A := by
  rw [mem_liftBlocks]
  constructor
  · rintro ⟨c, hc, hxc⟩
    exact block_eq_of_mem hd hx hxc ▸ hc
  · exact fun hb => ⟨b, hb, hx⟩

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

@[simp] theorem QuartetTree.map_val (s : QuartetTree Y) :
    (s.map hι).val = s.val.image fun B => B.image ι := rfl

@[simp] theorem QuartetTree.map_taxa (s : QuartetTree Y) : (s.map hι).taxa = s.taxa.image ι := by
  ext x
  simp only [QuartetTree.taxa, QuartetTree.map_val, mem_sup, id, mem_image]
  constructor
  · rintro ⟨_, ⟨B, hB, rfl⟩, hx⟩
    obtain ⟨y, hy, rfl⟩ := mem_image.1 hx
    exact ⟨y, ⟨B, hB, hy⟩, rfl⟩
  · rintro ⟨y, ⟨B, hB, hy⟩, rfl⟩
    exact ⟨_, ⟨B, hB, rfl⟩, mem_image_of_mem _ hy⟩

theorem QuartetTree.map_injective : Function.Injective (QuartetTree.map (X := X) hι) := by
  intro s s' h
  apply Subtype.ext
  exact image_injective (image_injective hι) (congrArg Subtype.val h)

include hι in
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

theorem exists_isRepTuple (hne : ∀ B ∈ P, B.Nonempty) : ∃ x, IsRepTuple P x :=
  ⟨fun b => (hne b.val b.property).choose, fun b => (hne b.val b.property).choose_spec⟩

variable (hd : ∀ B ∈ P, ∀ C ∈ P, B ≠ C → Disjoint B C) {x : {B // B ∈ P} → X} (hx : IsRepTuple P x)

include hd hx

theorem IsRepTuple.injective : Function.Injective x := fun b c h =>
  block_eq_of_mem hd (hx b) (h ▸ hx c)

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

/-- The restriction of a spliced tree to representatives of the blocks of `P` is the tree on the blocks
whose lifts were added at `P`. -/
theorem displays_splice_map_iff {T : Finset (Finset X)} (hT : IsUnrootedTree T)
    {L : Finset (Finset X) → Finset (Finset X)}
    (hL : ∀ P ∈ multifurcations T, IsBlockFamily P (L P)) (hP : P ∈ multifurcations T)
    {T₀ : Finset (Finset {B // B ∈ P})} (hLP : L P = T₀.image (liftBlocks P))
    (s₀ : QuartetTree {B // B ∈ P}) :
    Displays (splice T L) (s₀.map (hx.injective hd)) ↔ Displays T₀ s₀ := by
  have hinj := hx.injective hd
  have hdist : InDistinctBlocks P (s₀.map hinj).taxa :=
    hx.inDistinctBlocks hd (by rw [QuartetTree.map_taxa]; exact image_subset_image (subset_univ _))
  rw [displays_splice_iff hT hL hP hdist, hLP]
  constructor
  · rintro ⟨A', hA', hAs⟩
    obtain ⟨A, hA, rfl⟩ := mem_image.1 hA'
    rw [QuartetTree.map_taxa, hx.liftBlocks_inter_image hd, QuartetTree.map_val, mem_image] at hAs
    obtain ⟨C, hC, hCe⟩ := hAs
    exact ⟨A, hA, (image_injective hinj hCe) ▸ hC⟩
  · rintro ⟨A, hA, hAs⟩
    refine ⟨_, mem_image_of_mem _ hA, ?_⟩
    rw [QuartetTree.map_taxa, hx.liftBlocks_inter_image hd, QuartetTree.map_val]
    exact mem_image_of_mem _ hAs

end Rep

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
        · simp [y₂, Function.update_of_ne hcb, hcb]
      rw [this, card_erase_of_mem hb, hcard]
      rfl
  exact key _ x hx rfl

end Exchange

end Phylogenetics
