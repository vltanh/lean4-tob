module

public import Phylogenetics.Tree.Splice

/-!
# The local objective at a multifurcation: attaching subtrees, and sums over representatives

The tools that `src/ECToBlob/Section3.lean` and `src/TOBQMC/WQC.lean` share, on the splices of `Phylogenetics.Tree.Splice`.

* `IsBlockAttachment`, `IsBlockAttachment.pullTree_eq`, `attachSubtrees`, `isBlockAttachment_attachSubtrees`,
  `IsBlockAttachment.exists_eq_attachSubtrees`, `isBlockAttachment_splice`: attaching rooted subtrees at the
  leaves of a tree on the blocks; every such tree, and every splice, restricts back to the tree on the blocks.
* `blockWeight`, `innerSum`, `prod_card_mul_sum_eq_sum_innerSum`, `innerSum_eq_quartetSupport_pullTree`: a
  sum over quartet trees in distinct blocks as a sum over representative tuples.
* `map_eq_of_cutExchangeable`: by exchangeability, a weight of a quartet tree in distinct blocks does
  not depend on the representatives.
-/

@[expose] public noncomputable section

open Phylogenetics Finset
open scoped Classical

namespace Phylogenetics

variable {X : Type*} [Fintype X] [DecidableEq X]

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
    · exact compatible_symm (hlift hC hA)
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
    · have := compat_compl_left (compatible_symm (hbase h h'))
      rw [compl_compl] at this
      exact compatible_symm this
    · have := compat_compl_left (hbase h h')
      rwa [compl_compl] at this
    · have := compat_compl_left (compatible_symm (compat_compl_left (hbase h h')))
      rw [compl_compl, compl_compl] at this
      exact compatible_symm this

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
theorem innerSum_eq_quartetSupport_pullTree (hd : ∀ B ∈ P, ∀ C ∈ P, B ≠ C → Disjoint B C)
    {x : {B // B ∈ P} → X} (hx : IsRepTuple P x) (w : QuartetTree X → ℝ) (T : Finset (Finset X)) :
    innerSum P w T x = quartetSupport (fun s₀ => blockSizeProd s₀ * w (s₀.map (hx.injective hd)))
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
  rw [sum_ite_taxa_subset_image (hx.injective hd), quartetSupport]
  refine sum_congr rfl fun s₀ _ => ?_
  simp only [displays_pullTree_iff (hx.injective hd), blockWeight_map hd hx]

end RepSum

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
