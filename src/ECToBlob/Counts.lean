module

public import Basic.Defs
public import Basic.Testing.Combining
public import Basic.Testing.Defs
public import Phylogenetics.Tree.Detach
public import ECToBlob.Deterministic
public import ECToBlob.Remark84
public import Basic.TreeCounts
public import TINNiK.Counts

/-!
# ECToBlob: operation counts

The running time of the ECToBlob algorithm (the paper's text, lines 922-935). No machine model is used:
each theorem counts the objects that a step enumerates, and says what each one costs in the paper's terms; the bounds
are explicit.

## `bi` and `quad`: `O(s⁵)`

"Applying the star and T1 test to the `C(s, 4)` sets of 4 taxa requires time `O(s⁴)`" is
`card_fourSets_add_card_quartetTree`. "At most `s - 3` internal edges of a tree `T₀`" is
`card_edgeSides_add_three_le`, for any tree. "Determining which p-values must be combined [...] and combining them" is
one pass over the quartet trees and at most `C(s, 4)` p-values (`Deterministic.card_multipartitionQuartets_le`,
`Deterministic.card_edgeQuartets_le`). "At most `s - 3` edge contracting steps" is `lastIteration_le`, and "a combined
p-value for the tree" is `Deterministic.card_displays_le`. Together: `ectoblobOperations_le`.

What is counted differs from the literal evaluation of `treeSeq`, which computes `edgeT1P` for all edges again at each
iteration. That recomputation is `O(s⁶)` (`ectoblobOperationsRecomputing_le`). The paper's `O(s⁵)` stores the
p-values, which is sound because for `bi` and `quad` they do not depend on the current tree
(`edgeT1P_eq_of_qType_ne_mul`).

## `mul`: `O(s⁶)`

"New combined p-values must be found at each contraction step, for all edges incident to the one contracted" is
`edgeT1P_eq_of_notMem_recomputedSides`, the quartets being unchanged otherwise
(`multipartitionQuartets_eq_of_incident`).

"For a binary `T₀` the `k`th edge contracted might be incident to as many as `4 + k` other internal edges": in the
language of splits, the edges incident to the edge with side `A` of `T` are given by the maximal sides of `T` strictly
inside `A` or `Aᶜ` (`incidentSides`), and `card_incidentSides_le` is the bound. The proof is by going down from `A` in
the tree rooted outside `A` (`card_childClusters_le_of_subset`): a contraction replaces a child by its own children,
one more for each side removed.

The bound `4 + k` is right, with these readings, which the text leaves open:

* `k` is the number of edges contracted so far, including those Step 3 contracted (`afterStar`), and not the
  iteration: `contractStep` contracts all edges tied for the minimum at once, which `card_recomputedSides_le` allows
  for;
* the `4 + k` includes pendant edges. An edge also has at most `s - 4 - k` other internal edges
  (`card_internalSides_add_card_sdiff`), so that for `k > (s - 8) / 2` the bound `4 + k` on internal edges is not
  attained. It is attained for `s = 2 k + 8`, with `k` contracted edges in a path at one end of the edge, and a cherry
  on each of the `4 + k` edges at its two ends;
* the printed sum `∑_{k=0}^{s-3}` has one term too many: at most `s - 3` edges are contracted, for `k = 0, ..., s -
  4`. Its order is unaffected (`two_mul_sum_range_four_add`).

Over all iterations: `sum_card_recomputedSides_le`, which gives `ectoblobOperationsMul_le`. A simpler argument for the
order: `O(s⁶)` does not need the bound on incident edges, since `(s - 3)²` edge computations suffice
(`ectoblobOperationsRecomputing_le`).
-/

@[expose] public noncomputable section

open Phylogenetics Phylogenetics.RootedNetwork Finset
open scoped Classical

namespace ECToBlob.Counts

open ECToBlob.Deterministic

variable {X : Type*} [Fintype X] [DecidableEq X]

/-! ### The internal edges of a tree -/

/-- A family closed under complements has twice as many sides as sides without `r`. -/
theorem card_eq_two_mul_filter {S : Finset (Finset X)} (hS : ∀ A ∈ S, Aᶜ ∈ S) (r : X) :
    S.card = 2 * (S.filter fun A => r ∉ A).card := by
  have himg : S.filter (fun A => ¬ r ∉ A) = (S.filter fun A => r ∉ A).image compl := by
    ext A
    simp only [mem_filter, not_not, mem_image]
    constructor
    · rintro ⟨hA, hr⟩
      exact ⟨Aᶜ, ⟨hS A hA, by simpa using hr⟩, compl_compl A⟩
    · rintro ⟨C, ⟨hC, hr⟩, rfl⟩
      exact ⟨hS C hC, by simpa using hr⟩
  have hsplit := card_filter_add_card_filter_not (s := S) (fun A : Finset X => r ∉ A)
  rw [himg, card_image_of_injective _ compl_injective] at hsplit
  omega

theorem compl_mem_internalSides {T : Finset (Finset X)} (hT : ∀ A ∈ T, Aᶜ ∈ T) {A : Finset X}
    (hA : A ∈ internalSides T) : Aᶜ ∈ internalSides T := by
  obtain ⟨hAT, h₁, h₂⟩ := mem_filter.mp hA
  exact mem_filter.mpr ⟨hT A hAT, h₂, by rwa [compl_compl]⟩

/-- **"At most `s - 3` internal edges of a tree"**: one side per edge, in any tree on `s ≥ 3` taxa. Rooted at `r`, a
tree has at most `s - 1` clusters of at least two taxa, among them the root and `{r}ᶜ`. -/
theorem card_edgeSides_add_three_le {T : Finset (Finset X)} (hT : IsUnrootedTree T) (h3 : 3 ≤ Fintype.card X) (r : X) :
    (TOBQMC.edgeSides r T).card + 3 ≤ Fintype.card X := by
  have hS := hT.isSplitFamily (by omega)
  have hH := rootedAt_isHierarchy hS r
  have hle := TINNiK.card_filter_two_le_add_one_le hH
  have hsub : insert (univ : Finset X) (insert ({r} : Finset X)ᶜ (TOBQMC.edgeSides r T)) ⊆
      (rootedAt T r).filter fun A => 2 ≤ A.card := by
    intro A hA
    rw [mem_insert, mem_insert] at hA
    rcases hA with rfl | rfl | hA
    · exact mem_filter.mpr ⟨mem_rootedAt.mpr (Or.inl rfl), by rw [card_univ]; omega⟩
    · refine mem_filter.mpr ⟨mem_rootedAt.mpr (Or.inr (Or.inr ⟨hS.compl_mem _ (hS.singleton_mem r), by simp⟩)), ?_⟩
      rw [card_compl, card_singleton]
      omega
    · obtain ⟨hint, hr⟩ := mem_filter.mp hA
      obtain ⟨hAT, h₁, -⟩ := mem_filter.mp hint
      exact mem_filter.mpr ⟨mem_rootedAt.mpr (Or.inr (Or.inr ⟨hAT, hr⟩)), h₁⟩
  have hnot₁ : ({r} : Finset X)ᶜ ∉ TOBQMC.edgeSides r T := by
    intro h
    have := (mem_filter.mp (mem_filter.mp h).1).2.2
    rw [compl_compl, card_singleton] at this
    omega
  have hnot₂ : (univ : Finset X) ∉ insert ({r} : Finset X)ᶜ (TOBQMC.edgeSides r T) := by
    rw [mem_insert]
    rintro (h | h)
    · exact (mem_compl.mp (h ▸ mem_univ r)) (mem_singleton_self r)
    · exact (mem_filter.mp h).2 (mem_univ r)
  have hcard := card_le_card hsub
  rw [card_insert_of_notMem hnot₂, card_insert_of_notMem hnot₁] at hcard
  omega

/-- The sides of the internal edges of any tree on `s ≥ 3` taxa: at most `2 (s - 3)`. -/
theorem card_internalSides_add_six_le {T : Finset (Finset X)} (hT : IsUnrootedTree T) (h3 : 3 ≤ Fintype.card X) :
    (internalSides T).card + 6 ≤ 2 * Fintype.card X := by
  have hS := hT.isSplitFamily (by omega)
  obtain ⟨r⟩ : Nonempty X := Fintype.card_pos_iff.mp (by omega)
  rw [card_eq_two_mul_filter (fun A hA => compl_mem_internalSides hS.compl_mem hA) r]
  have := card_edgeSides_add_three_le hT h3 r
  simp only [TOBQMC.edgeSides] at this
  omega

/-! ### The edges incident to an edge -/

/-- The sides that point away from the edge with side `A`, in the tree `T`: the maximal sides of `T` strictly inside
`A` or `Aᶜ`. There is one for each edge of `T` incident to that edge, at the end `A` or at the end `Aᶜ`: two
compatible splits have sides, one of each, with one strictly inside the other, and two edges are incident when no
third edge separates them, that is, when no side of `T` lies between those two sides. By `childClusters_eq_rootedAt`,
these are the children of `A` in the tree rooted outside `A`, so that with `Aᶜ` they are the blocks of a vertex of `T`
(`IsHierarchy.isVertexPartition_insert_compl`). -/
def incidentSides (T : Finset (Finset X)) (A : Finset X) : Finset (Finset X) :=
  childClusters T A ∪ childClusters T Aᶜ

/-- A side strictly inside `A`, for `r ∉ A`, is a cluster of the tree rooted at `r` exactly when it is a side. -/
theorem mem_rootedAt_of_ssubset {T : Finset (Finset X)} {r : X} {A B : Finset X} (hr : r ∉ A) (hB : B ⊂ A) :
    B ∈ rootedAt T r ↔ B ∈ T := by
  have hrB : r ∉ B := fun h => hr (hB.subset h)
  rw [mem_rootedAt]
  constructor
  · rintro (rfl | rfl | h)
    · exact absurd (mem_univ r) hrB
    · exact absurd (mem_singleton_self r) hrB
    · exact h.1
  · exact fun h => Or.inr (Or.inr ⟨h, hrB⟩)

/-- The children of a side `A` in the tree rooted outside `A` are the maximal sides strictly inside `A`. -/
theorem childClusters_eq_rootedAt {T : Finset (Finset X)} {r : X} {A : Finset X} (hr : r ∉ A) :
    childClusters T A = childClusters (rootedAt T r) A := by
  ext B
  rw [mem_childClusters, mem_childClusters]
  constructor
  · rintro ⟨hB, hBA, hmax⟩
    exact ⟨(mem_rootedAt_of_ssubset hr hBA).mpr hB, hBA,
      fun C hC hBC hCA => hmax C ((mem_rootedAt_of_ssubset hr hCA).mp hC) hBC hCA⟩
  · rintro ⟨hB, hBA, hmax⟩
    exact ⟨(mem_rootedAt_of_ssubset hr hBA).mp hB, hBA,
      fun C hC hBC hCA => hmax C ((mem_rootedAt_of_ssubset hr hCA).mpr hC) hBC hCA⟩

/-- A binary hierarchy obtained by rooting a binary tree at a taxon: `2 s - 1` clusters force two children each. -/
theorem card_childClusters_rootedAt {T : Finset (Finset X)} (hT : IsBinaryTree T) (h2 : 2 ≤ Fintype.card X) (r : X) :
    ∀ A ∈ rootedAt T r, 2 ≤ A.card → (childClusters (rootedAt T r) A).card = 2 := by
  have hTu : IsUnrootedTree T := IsBinaryTree.isUnrootedTree hT
  have hS := hTu.isSplitFamily h2
  have hH := rootedAt_isHierarchy hS r
  -- the clusters: `T` has `4 s - 6` sides, half of them without `r`
  have hcardT := TOBQMC.card_of_isBinaryTree hT h2
  have hhalf := card_eq_two_mul_filter hS.compl_mem r
  have hcardH : (rootedAt T r).card + 1 = 2 * Fintype.card X := by
    have h₁ : ({r} : Finset X) ∉ T.filter fun A => r ∉ A := fun h => (mem_filter.mp h).2 (mem_singleton_self r)
    have h₂ : (univ : Finset X) ∉ insert ({r} : Finset X) (T.filter fun A => r ∉ A) := by
      rw [mem_insert]
      rintro (h | h)
      · have := congrArg card h
        rw [card_univ, card_singleton] at this
        omega
      · exact (mem_filter.mp h).2 (mem_univ r)
    rw [rootedAt, card_insert_of_notMem h₂, card_insert_of_notMem h₁]
    omega
  have hsum := TINNiK.sum_card_childClusters hH
  have htot := card_filter_add_card_filter_not (s := rootedAt T r) (fun A : Finset X => 2 ≤ A.card)
  rw [TINNiK.card_filter_not_two_le hH] at htot
  have hsplit := sum_filter_add_sum_filter_not (rootedAt T r) (fun A : Finset X => 2 ≤ A.card)
    (fun A => (childClusters (rootedAt T r) A).card)
  have h₂ : ∑ A ∈ (rootedAt T r).filter (fun A : Finset X => ¬ 2 ≤ A.card),
      (childClusters (rootedAt T r) A).card = 0 := by
    refine sum_eq_zero fun A hA => ?_
    obtain ⟨hAH, h2'⟩ := mem_filter.mp hA
    have hpos := card_pos.mpr (hH.2.2.1 A hAH)
    obtain ⟨x, rfl⟩ := card_eq_one.mp (by omega : A.card = 1)
    rw [hH.childClusters_singleton x, card_empty]
  intro A hA hA2
  have hge := hH.two_le_card_childClusters hA2
  by_contra hne
  have hlt : ∑ _B ∈ (rootedAt T r).filter (fun A : Finset X => 2 ≤ A.card), 2 <
      ∑ B ∈ (rootedAt T r).filter (fun A : Finset X => 2 ≤ A.card), (childClusters (rootedAt T r) B).card :=
    sum_lt_sum (fun B hB => hH.two_le_card_childClusters (mem_filter.mp hB).2)
      ⟨A, mem_filter.mpr ⟨hA, hA2⟩, by omega⟩
  rw [sum_const, smul_eq_mul] at hlt
  omega

/-- **The count in a contraction of a rooted binary tree**: a cluster has at most two children, and one more for each
removed cluster below it. Going down from `A`: a child of `A` in `H₀` that remains is one child in `H`, and one that
was removed passes on its children. -/
theorem card_childClusters_le_of_subset {H₀ H : Finset (Finset X)} (hH₀ : IsHierarchy H₀)
    (hbin : ∀ A ∈ H₀, 2 ≤ A.card → (childClusters H₀ A).card = 2) (hsub : H ⊆ H₀)
    (hsing : ∀ x : X, ({x} : Finset X) ∈ H) (A : Finset X) (hA : A ∈ H₀) (h2 : 2 ≤ A.card) :
    (childClusters H A).card ≤ 2 + ((H₀ \ H).filter fun D => D ⊂ A).card := by
  induction hn : A.card using Nat.strong_induction_on generalizing A with
  | _ n ih =>
    subst hn
    let g : Finset X → Finset (Finset X) := fun C => if C ∈ H then {C} else childClusters H C
    have hg : ∀ C ∈ childClusters H₀ A, (g C).card ≤ 1 + ((H₀ \ H).filter fun D => D ⊆ C).card := by
      intro C hC
      obtain ⟨hCH₀, hCA, -⟩ := mem_childClusters.mp hC
      by_cases hCH : C ∈ H
      · simp [g, hCH]
      · have hC2 : 2 ≤ C.card := by
          have hpos := card_pos.mpr (hH₀.2.2.1 C hCH₀)
          by_contra hlt
          obtain ⟨x, rfl⟩ := card_eq_one.mp (by omega : C.card = 1)
          exact hCH (hsing x)
        have hih := ih C.card (card_lt_card hCA) C hCH₀ hC2 rfl
        have hins : (H₀ \ H).filter (fun D => D ⊆ C) = insert C ((H₀ \ H).filter fun D => D ⊂ C) := by
          ext D
          simp only [mem_filter, mem_insert, mem_sdiff]
          constructor
          · rintro ⟨hD, hDC⟩
            exact (eq_or_ssubset_of_subset hDC).imp_right fun h => ⟨hD, h⟩
          · rintro (rfl | ⟨hD, hDC⟩)
            · exact ⟨⟨hCH₀, hCH⟩, Subset.refl _⟩
            · exact ⟨hD, hDC.subset⟩
        have hnotmem : C ∉ (H₀ \ H).filter fun D => D ⊂ C := fun h => ssubset_irrefl C (mem_filter.mp h).2
        rw [hins, card_insert_of_notMem hnotmem]
        simp only [g, hCH, ite_false]
        omega
    obtain ⟨C₁, C₂, hne, hC⟩ := card_eq_two.mp (hbin A hA h2)
    have hC₁ : C₁ ∈ childClusters H₀ A := hC ▸ mem_insert_self _ _
    have hC₂ : C₂ ∈ childClusters H₀ A := hC ▸ mem_insert_of_mem (mem_singleton_self _)
    -- each child in `H` lies in a child in `H₀`
    have hsup := hH₀.sup_childClusters h2
    rw [hC] at hsup
    simp only [sup_insert, sup_singleton, id, sup_eq_union] at hsup
    have hsubg : childClusters H A ⊆ g C₁ ∪ g C₂ := by
      have hone : ∀ C ∈ childClusters H₀ A, ∀ B ∈ childClusters H A, (B ∩ C).Nonempty → B ∈ g C := by
        intro C hC B hB hBC
        obtain ⟨hCH₀, hCA, hCmax⟩ := mem_childClusters.mp hC
        obtain ⟨hBH, hBA, hBmax⟩ := mem_childClusters.mp hB
        have hBC' : B ⊆ C := by
          rcases hH₀.2.2.2 B (hsub hBH) C hCH₀ with h | h | h
          · exact h
          · rcases eq_or_ssubset_of_subset h with heq | hlt
            · exact heq.symm.subset
            · exact absurd hBA (hCmax B (hsub hBH) hlt)
          · obtain ⟨x, hx⟩ := hBC
            obtain ⟨hx₁, hx₂⟩ := mem_inter.mp hx
            exact absurd hx₂ (disjoint_left.mp h hx₁)
        by_cases hCH : C ∈ H
        · simp only [g, hCH, ite_true, mem_singleton]
          rcases eq_or_ssubset_of_subset hBC' with heq | hlt
          · exact heq
          · exact absurd hCA (hBmax C hCH hlt)
        · simp only [g, hCH, ite_false]
          have hBC'' : B ⊂ C := by
            rcases eq_or_ssubset_of_subset hBC' with heq | hlt
            · exact absurd (heq ▸ hBH) hCH
            · exact hlt
          exact mem_childClusters.mpr ⟨hBH, hBC'', fun D hD hBD hDC => hBmax D hD hBD (hDC.trans hCA)⟩
      intro B hB
      obtain ⟨hBH, hBA, -⟩ := mem_childClusters.mp hB
      obtain ⟨x, hx⟩ := hH₀.2.2.1 B (hsub hBH)
      have hxA : x ∈ C₁ ∪ C₂ := hsup ▸ hBA.subset hx
      rcases mem_union.mp hxA with h | h
      · exact mem_union_left _ (hone C₁ hC₁ B hB ⟨x, mem_inter.mpr ⟨hx, h⟩⟩)
      · exact mem_union_right _ (hone C₂ hC₂ B hB ⟨x, mem_inter.mpr ⟨hx, h⟩⟩)
    -- the removed clusters below the two children are removed clusters below `A`
    have hbelow : ((H₀ \ H).filter fun D => D ⊆ C₁).card + ((H₀ \ H).filter fun D => D ⊆ C₂).card ≤
        ((H₀ \ H).filter fun D => D ⊂ A).card := by
      rw [← card_union_of_disjoint]
      · refine card_le_card fun D hD => ?_
        have hCA₁ := (mem_childClusters.mp hC₁).2.1
        have hCA₂ := (mem_childClusters.mp hC₂).2.1
        rcases mem_union.mp hD with hD | hD
        · obtain ⟨h, hDC⟩ := mem_filter.mp hD
          exact mem_filter.mpr ⟨h, lt_of_le_of_lt hDC hCA₁⟩
        · obtain ⟨h, hDC⟩ := mem_filter.mp hD
          exact mem_filter.mpr ⟨h, lt_of_le_of_lt hDC hCA₂⟩
      · rw [disjoint_left]
        intro D hD hD'
        obtain ⟨h, hDC⟩ := mem_filter.mp hD
        obtain ⟨-, hDC'⟩ := mem_filter.mp hD'
        obtain ⟨x, hx⟩ := hH₀.2.2.1 D (mem_sdiff.mp h).1
        exact disjoint_left.mp (hH₀.disjoint_of_mem_childClusters hC₁ hC₂ hne) (hDC hx) (hDC' hx)
    have h₁ := hg C₁ hC₁
    have h₂ := hg C₂ hC₂
    have h₃ := card_le_card hsubg
    have h₄ := card_union_le (g C₁) (g C₂)
    omega

/-- The count at one end of an edge, in a contraction of a binary tree: at most two sides, and one more for each side
removed inside. -/
theorem card_childClusters_le_of_contraction {T₀ T : Finset (Finset X)} (hT₀ : IsBinaryTree T₀) (hT : IsUnrootedTree T)
    (hsub : T ⊆ T₀) (h2N : 2 ≤ Fintype.card X) {A : Finset X} (hA : A ∈ T₀) (h2 : 2 ≤ A.card) :
    (childClusters T A).card ≤ 2 + ((T₀ \ T).filter fun D => D ⊂ A).card := by
  have hS₀ := (IsBinaryTree.isUnrootedTree hT₀).isSplitFamily h2N
  have hS := hT.isSplitFamily h2N
  obtain ⟨r, hr⟩ := hS₀.compl_nonempty A hA
  have hr' : r ∉ A := mem_compl.mp hr
  have hsubH : rootedAt T r ⊆ rootedAt T₀ r := by
    intro B hB
    rcases mem_rootedAt.mp hB with h | h | ⟨h, hrB⟩
    · exact mem_rootedAt.mpr (Or.inl h)
    · exact mem_rootedAt.mpr (Or.inr (Or.inl h))
    · exact mem_rootedAt.mpr (Or.inr (Or.inr ⟨hsub h, hrB⟩))
  have hbound := card_childClusters_le_of_subset (rootedAt_isHierarchy hS₀ r)
    (card_childClusters_rootedAt hT₀ h2N r) hsubH (rootedAt_isHierarchy hS r).2.1 A
    (mem_rootedAt.mpr (Or.inr (Or.inr ⟨hA, hr'⟩))) h2
  have hfil : ((rootedAt T₀ r \ rootedAt T r).filter fun D => D ⊂ A) = (T₀ \ T).filter fun D => D ⊂ A := by
    ext D
    simp only [mem_filter, mem_sdiff]
    constructor
    · rintro ⟨⟨h₁, h₂⟩, hDA⟩
      exact ⟨⟨(mem_rootedAt_of_ssubset hr' hDA).mp h₁, fun h => h₂ ((mem_rootedAt_of_ssubset hr' hDA).mpr h)⟩, hDA⟩
    · rintro ⟨⟨h₁, h₂⟩, hDA⟩
      exact ⟨⟨(mem_rootedAt_of_ssubset hr' hDA).mpr h₁, fun h => h₂ ((mem_rootedAt_of_ssubset hr' hDA).mp h)⟩, hDA⟩
  rwa [hfil, ← childClusters_eq_rootedAt hr'] at hbound

/-- **After `k` contractions of a binary tree, an internal edge is incident to at most `4 + k` others**, at its two
ends together, for the sum of the two counts. `k` is the number of edges contracted, `(T₀ \ T).card / 2`. The sides
removed inside `A` and inside `Aᶜ` are of different edges. -/
theorem card_childClusters_add_le {T₀ T : Finset (Finset X)} (hT₀ : IsBinaryTree T₀) (hT : IsUnrootedTree T)
    (hsub : T ⊆ T₀) (h2N : 2 ≤ Fintype.card X) {A : Finset X} (hA : A ∈ internalSides T₀) :
    (childClusters T A).card + (childClusters T Aᶜ).card ≤ 4 + (T₀ \ T).card / 2 := by
  have hS₀ := (IsBinaryTree.isUnrootedTree hT₀).isSplitFamily h2N
  have hS := hT.isSplitFamily h2N
  obtain ⟨hAT, h₁, h₂⟩ := mem_filter.mp hA
  have hb₁ := card_childClusters_le_of_contraction hT₀ hT hsub h2N hAT h₁
  have hb₂ := card_childClusters_le_of_contraction hT₀ hT hsub h2N (hS₀.compl_mem A hAT) h₂
  set S₁ := (T₀ \ T).filter fun D => D ⊂ A with hS₁
  set S₂ := (T₀ \ T).filter fun D => D ⊂ Aᶜ with hS₂
  have hmem₀ : ∀ {D}, D ∈ S₁ ∪ S₂ → D ∈ T₀ \ T := fun {D} hD => by
    rcases mem_union.mp hD with h | h
    · exact (mem_filter.mp h).1
    · exact (mem_filter.mp h).1
  have hdis₁₂ : Disjoint S₁ S₂ := by
    rw [disjoint_left]
    intro D hD hD'
    obtain ⟨hDT, hDA⟩ := mem_filter.mp hD
    obtain ⟨-, hDA'⟩ := mem_filter.mp hD'
    obtain ⟨x, hx⟩ := hS₀.nonempty D (mem_sdiff.mp hDT).1
    exact mem_compl.mp (hDA'.subset hx) (hDA.subset hx)
  obtain ⟨y, hy⟩ := hS₀.nonempty A hAT
  obtain ⟨y', hy'⟩ := hS₀.compl_nonempty A hAT
  have hdis : Disjoint (S₁ ∪ S₂) ((S₁ ∪ S₂).image compl) := by
    rw [disjoint_left]
    intro D hD hD'
    obtain ⟨E, hE, rfl⟩ := mem_image.mp hD'
    have hcases : (Eᶜ ⊂ A ∨ Eᶜ ⊂ Aᶜ) ∧ (E ⊂ A ∨ E ⊂ Aᶜ) := by
      constructor
      · rcases mem_union.mp hD with h | h
        · exact Or.inl (mem_filter.mp h).2
        · exact Or.inr (mem_filter.mp h).2
      · rcases mem_union.mp hE with h | h
        · exact Or.inl (mem_filter.mp h).2
        · exact Or.inr (mem_filter.mp h).2
    obtain ⟨h₃ | h₃, h₄ | h₄⟩ := hcases
    · -- both inside `A`: then `A` is everything
      by_cases hyE : y' ∈ E
      · exact mem_compl.mp hy' (h₄.subset hyE)
      · exact mem_compl.mp hy' (h₃.subset (mem_compl.mpr hyE))
    · -- `E ⊂ Aᶜ` makes `A ⊆ Eᶜ`
      refine h₃.2 fun w hw => mem_compl.mpr fun hwE => ?_
      exact mem_compl.mp (h₄.subset hwE) hw
    · refine h₃.2 fun w hw => mem_compl.mpr fun hwE => ?_
      exact (mem_compl.mp hw) (h₄.subset hwE)
    · by_cases hyE : y ∈ E
      · exact mem_compl.mp (h₄.subset hyE) hy
      · exact mem_compl.mp (h₃.subset (mem_compl.mpr hyE)) hy
  have hsubU : (S₁ ∪ S₂) ∪ (S₁ ∪ S₂).image compl ⊆ T₀ \ T := by
    intro D hD
    rcases mem_union.mp hD with hD | hD
    · exact hmem₀ hD
    · obtain ⟨E, hE, rfl⟩ := mem_image.mp hD
      obtain ⟨h₃, h₄⟩ := mem_sdiff.mp (hmem₀ hE)
      refine mem_sdiff.mpr ⟨hS₀.compl_mem E h₃, fun h => h₄ ?_⟩
      have := hS.compl_mem _ h
      rwa [compl_compl] at this
  have hcard := card_le_card hsubU
  rw [card_union_of_disjoint hdis, card_image_of_injective _ compl_injective, card_union_of_disjoint hdis₁₂] at hcard
  omega

/-- **The bound of ECToBlob on incident edges** (the paper's text, line 933): for a binary `T₀`, an
internal edge of a contraction `T` of `T₀`, with `k = (T₀ \ T).card / 2` edges contracted, is incident to at most `4 +
k` other edges. Here `k` counts all edges contracted so far, in Step 3 too, and the count has the pendant edges among
the `4 + k`. -/
theorem card_incidentSides_le {T₀ T : Finset (Finset X)} (hT₀ : IsBinaryTree T₀) (hT : IsUnrootedTree T)
    (hsub : T ⊆ T₀) (h2N : 2 ≤ Fintype.card X) {A : Finset X} (hA : A ∈ internalSides T) :
    (incidentSides T A).card ≤ 4 + (T₀ \ T).card / 2 := by
  obtain ⟨hAT, h₁, h₂⟩ := mem_filter.mp hA
  have h := card_childClusters_add_le hT₀ hT hsub h2N (mem_filter.mpr ⟨hsub hAT, h₁, h₂⟩)
  exact (card_union_le _ _).trans h

/-- The sides of the internal edges remaining after a contraction of a binary tree: each edge contracted is one less.
So an internal edge also has at most `s - 4 - k` other internal edges: for large `k`, this is what limits it, and not
`4 + k`. -/
theorem card_internalSides_add_card_sdiff {T₀ T : Finset (Finset X)} (hT₀ : IsBinaryTree T₀) (hT : IsUnrootedTree T)
    (hsub : T ⊆ T₀) (h3 : 3 ≤ Fintype.card X) :
    (internalSides T).card + (T₀ \ T).card + 6 = 2 * Fintype.card X := by
  have hS := hT.isSplitFamily (by omega)
  have hsplit : internalSides T₀ = internalSides T ∪ (T₀ \ T) := by
    ext A
    simp only [mem_union, mem_sdiff, internalSides, mem_filter]
    constructor
    · rintro ⟨hA, h₁, h₂⟩
      by_cases hAT : A ∈ T
      · exact Or.inl ⟨hAT, h₁, h₂⟩
      · exact Or.inr ⟨hA, hAT⟩
    · rintro (⟨hA, h₁, h₂⟩ | ⟨hA, hAT⟩)
      · exact ⟨hsub hA, h₁, h₂⟩
      · have hpos := card_pos.mpr ((IsBinaryTree.isUnrootedTree hT₀ |>.isSplitFamily (by omega)).nonempty A hA)
        have hpos' := card_pos.mpr ((IsBinaryTree.isUnrootedTree hT₀ |>.isSplitFamily (by omega)).compl_nonempty A hA)
        refine ⟨hA, ?_, ?_⟩
        · by_contra hlt
          obtain ⟨x, rfl⟩ := card_eq_one.mp (by omega : A.card = 1)
          exact hAT (hS.singleton_mem x)
        · by_contra hlt
          obtain ⟨x, hx⟩ := card_eq_one.mp (by omega : Aᶜ.card = 1)
          refine hAT ?_
          have := hS.compl_mem _ (hS.singleton_mem x)
          rwa [← hx, compl_compl] at this
  have hdis : Disjoint (internalSides T) (T₀ \ T) := by
    rw [disjoint_left]
    intro A hA hA'
    exact (mem_sdiff.mp hA').2 (mem_filter.mp hA).1
  have hc := TOBQMC.card_internalSides hT₀ h3
  rw [hsplit, card_union_of_disjoint hdis] at hc
  exact hc

/-! ### Which p-values change -/

section Recompute

variable {o : ECToBlobOptions} {c : QuartetTree X → ℝ} {T₀ T T' : Finset (Finset X)} {A : Finset X}

/-- A side strictly inside `A` lies in a maximal one. -/
theorem exists_mem_childClusters_superset {F : Finset (Finset X)} {D A : Finset X} (hD : D ∈ F) (hDA : D ⊂ A) :
    ∃ B ∈ childClusters F A, D ⊆ B := by
  have hne : (F.filter fun B => D ⊆ B ∧ B ⊂ A).Nonempty := ⟨D, mem_filter.mpr ⟨hD, Subset.refl _, hDA⟩⟩
  obtain ⟨B, hB, hmax⟩ := exists_max_image _ card hne
  obtain ⟨hBF, hDB, hBA⟩ := mem_filter.mp hB
  refine ⟨B, mem_filter.mpr ⟨hBF, hBA, fun C hC hBC hCA => ?_⟩, hDB⟩
  have := hmax C (mem_filter.mpr ⟨hC, hDB.trans hBC.subset, hCA⟩)
  have := card_lt_card hBC
  omega

/-- The quartets of a multipartition do not change when no edge incident to the edge is contracted. -/
theorem multipartitionQuartets_eq_of_incident (hT' : T' ⊆ T) (h : ∀ D ∈ incidentSides T A, D ∈ T') :
    multipartitionQuartets T' A = multipartitionQuartets T A := by
  ext s
  simp only [multipartitionQuartets, mem_filter]
  refine and_congr_right fun _ => and_congr ?_ ?_
  · constructor
    · intro hn hex
      obtain ⟨C, hC, hCA, hsub⟩ := hex
      obtain ⟨B, hB, hCB⟩ := exists_mem_childClusters_superset hC hCA
      exact hn ⟨B, h B (mem_union_left _ hB), (mem_childClusters.mp hB).2.1, hsub.trans hCB⟩
    · intro hn hex
      obtain ⟨C, hC, hCA, hsub⟩ := hex
      exact hn ⟨C, hT' hC, hCA, hsub⟩
  · constructor
    · intro hn hex
      obtain ⟨C, hC, hCA, hsub⟩ := hex
      obtain ⟨B, hB, hCB⟩ := exists_mem_childClusters_superset hC hCA
      exact hn ⟨B, h B (mem_union_right _ hB), (mem_childClusters.mp hB).2.1, hsub.trans hCB⟩
    · intro hn hex
      obtain ⟨C, hC, hCA, hsub⟩ := hex
      exact hn ⟨C, hT' hC, hCA, hsub⟩

/-- **`bi` and `quad`: the p-value of an edge does not depend on the current tree**, which is why the paper computes
it once per edge of `T₀`. Algorithm 7.1 as written in `treeSeq` recomputes it at each iteration, with the same value.
-/
theorem edgeT1P_eq_of_qType_ne_mul (h : o.qType ≠ .mul) (T T' : Finset (Finset X)) (A : Finset X) :
    edgeT1P o c T₀ T A = edgeT1P o c T₀ T' A := by
  have hq : edgeQuartets o T₀ T A = edgeQuartets o T₀ T' A := by
    unfold edgeQuartets
    cases hq : o.qType with
    | bi => rfl
    | mul => exact absurd hq h
    | quad => rfl
  simp only [edgeT1P, hq]

/-- The sides of `T'` whose quartets for `mul` may differ from those in `T`: an edge incident to them was contracted.
-/
def recomputedSides (T T' : Finset (Finset X)) : Finset (Finset X) :=
  (internalSides T').filter fun A => ∃ D ∈ incidentSides T A, D ∉ T'

/-- **`mul`: "new combined p-values must be found at each contraction step, for all edges incident to the one
contracted"**: the others keep their p-value. -/
theorem edgeT1P_eq_of_notMem_recomputedSides (hT' : T' ⊆ T) (hA : A ∈ internalSides T')
    (hR : A ∉ recomputedSides T T') :
    edgeT1P o c T₀ T' A = edgeT1P o c T₀ T A := by
  have hkeep : ∀ D ∈ incidentSides T A, D ∈ T' := by
    intro D hD
    by_contra hn
    exact hR (mem_filter.mpr ⟨hA, D, hD, hn⟩)
  have hq : edgeQuartets o T₀ T' A = edgeQuartets o T₀ T A := by
    unfold edgeQuartets
    cases o.qType with
    | bi => rfl
    | mul => exact multipartitionQuartets_eq_of_incident hT' hkeep
    | quad => rfl
  simp only [edgeT1P, hq]

end Recompute

/-! ### The number of new edge computations -/

section Sum

/-- An edge that a contraction removes is internal: a tree has all its pendant edges. -/
theorem mem_internalSides_of_notMem {T T' : Finset (Finset X)} (hS : IsSplitFamily T) (hS' : IsSplitFamily T')
    {E : Finset X} (hE : E ∈ T) (hE' : E ∉ T') : E ∈ internalSides T := by
  have hpos := card_pos.mpr (hS.nonempty E hE)
  have hpos' := card_pos.mpr (hS.compl_nonempty E hE)
  refine mem_filter.mpr ⟨hE, ?_, ?_⟩
  · by_contra hlt
    obtain ⟨x, rfl⟩ := card_eq_one.mp (by omega : E.card = 1)
    exact hE' (hS'.singleton_mem x)
  · by_contra hlt
    obtain ⟨x, hx⟩ := card_eq_one.mp (by omega : Eᶜ.card = 1)
    refine hE' ?_
    have := hS'.compl_mem _ (hS'.singleton_mem x)
    rwa [← hx, compl_compl] at this

/-- Incidence is symmetric: if `D` is a maximal side inside `A`, then `Aᶜ` is a maximal side inside `Dᶜ`. -/
theorem mem_childClusters_compl {T : Finset (Finset X)} (hc : ∀ C ∈ T, Cᶜ ∈ T) {A D : Finset X} (hA : A ∈ T)
    (hD : D ∈ childClusters T A) : Aᶜ ∈ childClusters T Dᶜ := by
  obtain ⟨hDT, hDA, hmax⟩ := mem_childClusters.mp hD
  refine mem_childClusters.mpr ⟨hc A hA, compl_ssubset_compl.mpr hDA, fun C hC hAC hCD => ?_⟩
  have h₁ : D ⊂ Cᶜ := by
    have := compl_ssubset_compl.mpr hCD
    rwa [compl_compl] at this
  have h₂ : Cᶜ ⊂ A := by
    have := compl_ssubset_compl.mpr hAC
    rwa [compl_compl] at this
  exact hmax Cᶜ (hc C hC) h₁ h₂

/-- **The new edge computations at one contraction step**, in sides: with `j = (T \ T').card / 2` edges contracted
from `T`, itself with `k` edges contracted from a binary `T₀`, at most `j (4 + k)` edges need a new p-value
(`edgeT1P_eq_of_notMem_recomputedSides`), counting two sides per edge. `treeSeq` contracts all edges tied for the
minimum in one step, so `j` may exceed one. -/
theorem card_recomputedSides_le {T₀ T T' : Finset (Finset X)} (hT₀ : IsBinaryTree T₀) (hT : IsUnrootedTree T)
    (hT' : IsUnrootedTree T') (hsub : T ⊆ T₀) (hT'T : T' ⊆ T) (h2N : 2 ≤ Fintype.card X) :
    (recomputedSides T T').card ≤ (T \ T').card * (4 + (T₀ \ T).card / 2) := by
  have hS := hT.isSplitFamily h2N
  have hS' := hT'.isSplitFamily h2N
  have hSc : ∀ E ∈ T \ T', Eᶜ ∈ T \ T' := by
    intro E hE
    obtain ⟨h₁, h₂⟩ := mem_sdiff.mp hE
    refine mem_sdiff.mpr ⟨hS.compl_mem E h₁, fun h => h₂ ?_⟩
    have := hS'.compl_mem _ h
    rwa [compl_compl] at this
  have hcover : recomputedSides T T' ⊆
      (T \ T').biUnion fun E => childClusters T E ∪ (childClusters T E).image compl := by
    intro A hA
    obtain ⟨hAi, D, hD, hDn⟩ := mem_filter.mp hA
    have hAT := hT'T (mem_filter.mp hAi).1
    rcases mem_union.mp hD with hD | hD
    · have h := mem_childClusters_compl hS.compl_mem hAT hD
      exact mem_biUnion.mpr ⟨Dᶜ, hSc D (mem_sdiff.mpr ⟨(mem_childClusters.mp hD).1, hDn⟩),
        mem_union_right _ (mem_image.mpr ⟨Aᶜ, h, compl_compl A⟩)⟩
    · have h := mem_childClusters_compl hS.compl_mem (hS.compl_mem A hAT) hD
      rw [compl_compl] at h
      exact mem_biUnion.mpr ⟨Dᶜ, hSc D (mem_sdiff.mpr ⟨(mem_childClusters.mp hD).1, hDn⟩), mem_union_left _ h⟩
  have h₁ : (recomputedSides T T').card ≤ ∑ E ∈ T \ T', 2 * (childClusters T E).card := by
    refine (card_le_card hcover).trans (card_biUnion_le.trans (sum_le_sum fun E _ => ?_))
    have h₃ := card_union_le (childClusters T E) ((childClusters T E).image compl)
    have h₄ := card_image_le (s := childClusters T E) (f := compl)
    omega
  have h₂ : ∑ E ∈ T \ T', (childClusters T Eᶜ).card = ∑ E ∈ T \ T', (childClusters T E).card :=
    sum_nbij' compl compl hSc hSc (fun E _ => compl_compl E) (fun E _ => compl_compl E)
      (fun E _ => rfl)
  have h₃ : ∑ E ∈ T \ T', ((childClusters T E).card + (childClusters T Eᶜ).card) ≤
      ∑ _E ∈ T \ T', (4 + (T₀ \ T).card / 2) := by
    refine sum_le_sum fun E hE => ?_
    obtain ⟨hET, hEn⟩ := mem_sdiff.mp hE
    obtain ⟨-, h₅, h₆⟩ := mem_filter.mp (mem_internalSides_of_notMem hS hS' hET hEn)
    exact card_childClusters_add_le hT₀ hT hsub h2N (mem_filter.mpr ⟨hsub hET, h₅, h₆⟩)
  rw [sum_add_distrib, h₂, sum_const, smul_eq_mul] at h₃
  have h₄ : ∑ E ∈ T \ T', 2 * (childClusters T E).card =
      ∑ E ∈ T \ T', (childClusters T E).card + ∑ E ∈ T \ T', (childClusters T E).card := by
    rw [← sum_add_distrib]
    exact sum_congr rfl fun _ _ => by ring
  omega

/-- The sum of the printed bound: `∑_{k < n} (4 + k) = n (n + 7) / 2`. The printed sum `∑_{k=0}^{s-3}` is `n = s - 2`,
one more than the number of edges of a binary tree that can be contracted. -/
theorem two_mul_sum_range_four_add (n : ℕ) : 2 * ∑ k ∈ range n, (4 + k) = n * (n + 7) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ, Nat.mul_add, ih]
    ring

/-- `O(s²)`: `∑_{k < s - 3} (4 + k) ≤ s²`. -/
theorem sum_range_four_add_le (s : ℕ) : ∑ k ∈ range (s - 3), (4 + k) ≤ s ^ 2 := by
  have h := two_mul_sum_range_four_add (s - 3)
  by_cases hs : 3 ≤ s
  · obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le' hs
    simp only [Nat.add_sub_cancel] at h ⊢
    nlinarith
  · have h0 : s - 3 = 0 := by omega
    rw [h0]
    simp

/-- The terms from `a` to `b` are at least `(b - a) (4 + a)`. -/
theorem sum_range_add_mul_le {a b : ℕ} (hab : a ≤ b) :
    ∑ m ∈ range a, (4 + m) + (b - a) * (4 + a) ≤ ∑ m ∈ range b, (4 + m) := by
  induction b, hab using Nat.le_induction with
  | base => simp
  | succ b hab ih =>
    rw [sum_range_succ, show b + 1 - a = (b - a) + 1 by omega, Nat.add_mul, one_mul]
    omega

/-- A contraction of `j` edges after `k` has cost `j (4 + k)`, which is below the sum of `4 + m` for `k ≤ m < k + j`.
-/
theorem sum_sub_mul_le (k : ℕ → ℕ) (hk : ∀ i, k i ≤ k (i + 1)) (L : ℕ) :
    ∑ i ∈ range L, (k (i + 1) - k i) * (4 + k i) ≤ ∑ m ∈ range (k L), (4 + m) := by
  induction L with
  | zero => simp
  | succ L ih =>
    rw [sum_range_succ]
    have := sum_range_add_mul_le (hk L)
    omega

variable {o : ECToBlobOptions} {β : ℝ} {c : QuartetTree X → ℝ} {T₀ : Finset (Finset X)}

/-- **"`∑_{k=0}^{s-3} (4 + k) = O(s²)` new edge computations may be needed"** (the paper's text, lines
932-934), over any number of iterations of `treeSeq`, for a binary `T₀`, on `s ≥ 3` taxa. Counted: the sides, two per
edge, whose quartets of `mul` may change at an iteration (`recomputedSides`). -/
theorem sum_card_recomputedSides_le (hT₀ : IsBinaryTree T₀) (h3 : 3 ≤ Fintype.card X) (L : ℕ) :
    ∑ i ∈ range L, (recomputedSides (treeSeq o β c T₀ i) (treeSeq o β c T₀ (i + 1))).card ≤
      2 * ∑ m ∈ range (Fintype.card X - 3), (4 + m) := by
  have h2N : 2 ≤ Fintype.card X := by omega
  have hTu₀ := IsBinaryTree.isUnrootedTree hT₀
  have hS₀ := hTu₀.isSplitFamily h2N
  obtain ⟨r⟩ : Nonempty X := Fintype.card_pos_iff.mp (by omega)
  have hsf := fun i => isSplitFamily_treeSeq (o := o) (β := β) (c := c) hS₀ i
  have hu : ∀ i, IsUnrootedTree (treeSeq o β c T₀ i) := fun i => (isUnrootedTree_iff h2N _).mpr (hsf i)
  have hsub : ∀ i, treeSeq o β c T₀ i ⊆ T₀ := fun i => (treeSeq_subset_afterStar i).trans afterStar_subset
  have hanti : ∀ i, treeSeq o β c T₀ (i + 1) ⊆ treeSeq o β c T₀ i := fun i => treeSeq_anti (Nat.le_succ i)
  let k : ℕ → ℕ := fun i => ((T₀ \ treeSeq o β c T₀ i).filter fun A => r ∉ A).card
  have hk : ∀ i, (T₀ \ treeSeq o β c T₀ i).card = 2 * k i := by
    intro i
    refine card_eq_two_mul_filter (fun A hA => ?_) r
    obtain ⟨h₁, h₂⟩ := mem_sdiff.mp hA
    refine mem_sdiff.mpr ⟨hS₀.compl_mem A h₁, fun h => h₂ ?_⟩
    have := (hsf i).compl_mem _ h
    rwa [compl_compl] at this
  have hadd : ∀ i, (treeSeq o β c T₀ i \ treeSeq o β c T₀ (i + 1)).card + (T₀ \ treeSeq o β c T₀ i).card =
      (T₀ \ treeSeq o β c T₀ (i + 1)).card := by
    intro i
    rw [← card_union_of_disjoint]
    · congr 1
      ext A
      simp only [mem_union, mem_sdiff]
      constructor
      · rintro (⟨h₁, h₂⟩ | ⟨h₁, h₂⟩)
        · exact ⟨hsub i h₁, h₂⟩
        · exact ⟨h₁, fun h => h₂ (hanti i h)⟩
      · rintro ⟨h₁, h₂⟩
        by_cases h : A ∈ treeSeq o β c T₀ i
        · exact Or.inl ⟨h, h₂⟩
        · exact Or.inr ⟨h₁, h⟩
    · rw [disjoint_left]
      intro A hA hA'
      exact (mem_sdiff.mp hA').2 (mem_sdiff.mp hA).1
  have hmono : ∀ i, k i ≤ k (i + 1) := by
    intro i
    have h₁ := hadd i
    rw [hk, hk] at h₁
    omega
  have hstep : ∀ i, (recomputedSides (treeSeq o β c T₀ i) (treeSeq o β c T₀ (i + 1))).card ≤
      2 * ((k (i + 1) - k i) * (4 + k i)) := by
    intro i
    have h₁ := card_recomputedSides_le hT₀ (hu i) (hu (i + 1)) (hsub i) (hanti i) h2N
    have h₂ := hadd i
    rw [hk, hk] at h₂
    have h₃ : (treeSeq o β c T₀ i \ treeSeq o β c T₀ (i + 1)).card = 2 * (k (i + 1) - k i) := by omega
    rw [h₃, hk, Nat.mul_div_cancel_left _ (by norm_num : 0 < 2)] at h₁
    rw [mul_assoc] at h₁
    exact h₁
  have hL : k L ≤ Fintype.card X - 3 := by
    have h₁ := card_internalSides_add_card_sdiff hT₀ (hu L) (hsub L) h3
    rw [hk] at h₁
    omega
  calc _ ≤ ∑ i ∈ range L, 2 * ((k (i + 1) - k i) * (4 + k i)) := sum_le_sum fun i _ => hstep i
    _ = 2 * ∑ i ∈ range L, (k (i + 1) - k i) * (4 + k i) := by rw [mul_sum]
    _ ≤ 2 * ∑ m ∈ range (k L), (4 + m) := Nat.mul_le_mul_left _ (sum_sub_mul_le k hmono L)
    _ ≤ _ := Nat.mul_le_mul_left _
      (sum_le_sum_of_subset (range_mono hL))

end Sum

/-! ### The contraction steps -/

section Steps

variable {o : ECToBlobOptions} {β : ℝ} {c : QuartetTree X → ℝ} {T₀ T : Finset (Finset X)}

theorem internalSides_subset_of_subset {T' : Finset (Finset X)} (h : T' ⊆ T) : internalSides T' ⊆ internalSides T :=
  filter_subset_filter _ h

/-- A contraction step removes at least the two sides of an edge. -/
theorem card_internalSides_contractStep_add_two_le (hS : IsSplitFamily T) (h : (internalSides T).Nonempty) :
    (internalSides (contractStep o c T₀ T)).card + 2 ≤ (internalSides T).card := by
  obtain ⟨A, hA, hmin⟩ := exists_min_image _ (edgeT1P o c T₀ T) h
  have hmem : A ∈ (internalSides T).filter fun A => ∀ B ∈ internalSides T, edgeT1P o c T₀ T A ≤ edgeT1P o c T₀ T B :=
    mem_filter.mpr ⟨hA, hmin⟩
  have hAc := compl_mem_internalSides hS.compl_mem hA
  have hne : A ≠ Aᶜ := by
    intro heq
    obtain ⟨x, hx⟩ := hS.nonempty A (mem_filter.mp hA).1
    exact mem_compl.mp (heq ▸ hx) hx
  have hsub : insert A (insert Aᶜ (internalSides (contractStep o c T₀ T))) ⊆ internalSides T := by
    intro B hB
    rw [mem_insert, mem_insert] at hB
    rcases hB with rfl | rfl | hB
    · exact hA
    · exact hAc
    · obtain ⟨h₁, h₂⟩ := mem_filter.mp hB
      exact mem_filter.mpr ⟨contractStep_subset T h₁, h₂⟩
  have h₁ : Aᶜ ∉ internalSides (contractStep o c T₀ T) := by
    intro hin
    have := (mem_contractSides.mp (mem_filter.mp hin).1).2.2
    rw [compl_compl] at this
    exact this hmem
  have h₂ : A ∉ insert Aᶜ (internalSides (contractStep o c T₀ T)) := by
    rw [mem_insert]
    rintro (h | hin)
    · exact hne h
    · exact (mem_contractSides.mp (mem_filter.mp hin).1).2.1 hmem
  have hc := card_le_card hsub
  rw [card_insert_of_notMem h₂, card_insert_of_notMem h₁] at hc
  omega

/-- **"At each of the at most `s - 3` edge contracting steps"**: the iterations of Algorithm 7.1 are at most `s - 3`,
for any tree `T₀` on `s ≥ 3` taxa. -/
theorem lastIteration_le (hT₀ : IsUnrootedTree T₀) (h3 : 3 ≤ Fintype.card X) :
    lastIteration o β c T₀ ≤ Fintype.card X - 3 := by
  have h2N : 2 ≤ Fintype.card X := by omega
  have hS₀ := hT₀.isSplitFamily h2N
  have hsf := fun i => isSplitFamily_treeSeq (o := o) (β := β) (c := c) hS₀ i
  have hcount : ∀ i, internalSides (treeSeq o β c T₀ i) = ∅ ∨
      (internalSides (treeSeq o β c T₀ i)).card + 2 * i ≤ (internalSides (treeSeq o β c T₀ 0)).card := by
    intro i
    induction i with
    | zero => exact Or.inr (by omega)
    | succ i ih =>
      rcases ih with ih | ih
      · left
        have hsub := internalSides_subset_of_subset (treeSeq_anti (o := o) (β := β) (c := c) (T₀ := T₀) (Nat.le_succ i))
        rw [ih] at hsub
        exact subset_empty.mp hsub
      · by_cases hne : (internalSides (treeSeq o β c T₀ i)).Nonempty
        · right
          have := card_internalSides_contractStep_add_two_le (o := o) (c := c) (T₀ := T₀) (hsf i) hne
          rw [treeSeq_succ]
          omega
        · left
          have hsub := internalSides_subset_of_subset
            (treeSeq_anti (o := o) (β := β) (c := c) (T₀ := T₀) (Nat.le_succ i))
          rw [not_nonempty_iff_eq_empty.mp hne] at hsub
          exact subset_empty.mp hsub
  have hfirst := card_internalSides_add_six_le ((isUnrootedTree_iff h2N _).mpr (hsf 0)) h3
  refine Nat.sInf_le ?_
  rcases hcount (Fintype.card X - 3) with h | h
  · exact h
  · have h0 : (internalSides (treeSeq o β c T₀ (Fintype.card X - 3))).card = 0 := by omega
    exact card_eq_zero.mp h0

end Steps

/-! ### The time of the algorithm -/

section Time

variable (X) in
/-- **"Applying the star and T1 test to the `C(s, 4)` sets of 4 taxa"**: `starPValue` on each set and `t1PValue` on
each of its three quartet trees. -/
theorem card_fourSets_add_card_quartetTree :
    (univ.filter fun q : Finset X => q.card = 4).card + Fintype.card (QuartetTree X) =
      4 * (Fintype.card X).choose 4 := by
  rw [TINNiK.card_fourSets, TINNiK.card_quartetTree]
  ring

/-- The operations of Algorithm 7.1 for `bi` or `quad`, on `s` taxa, as the paper counts them
(the paper's text, lines 922-928). Counted:

* `4 C(s, 4)` p-values (`card_fourSets_add_card_quartetTree`);
* for each of at most `s - 3` edges (`card_edgeSides_add_three_le`), and for the star and T1 tests, deciding
  membership in the filters `multipartitionQuartets`, `edgeQuartets` for each of `3 C(s, 4)` quartet trees, and
  combining at most `C(s, 4)` p-values (`Deterministic.card_multipartitionQuartets_le`,
  `Deterministic.card_edgeQuartets_le`). One computation per edge: the two sides have the same quartets
  (`Coarsening.multipartitionQuartets_compl`, `Coarsening.bipartitionQuartets_compl`), and the p-values of `bi` and `quad` do not depend on
  the current tree (`edgeT1P_eq_of_qType_ne_mul`);
* for each of at most `s - 2` trees (`lastIteration_le`), deciding `Displays` on `3 C(s, 4)` quartet trees and
  combining at most `C(s, 4)` p-values (`Deterministic.card_displays_le`), and choosing the minimal edge among at most
  `2 (s - 3)` sides ("negligible"). -/
def ectoblobOperations (s : ℕ) : ℕ :=
  4 * s.choose 4 + (s - 3) * (2 * (4 * s.choose 4)) + (s - 2) * (4 * s.choose 4 + 2 * (s - 3))

/-- **"This gives time complexity `O(s⁵)` for the entire algorithm"** for `bi` and `quad`. -/
theorem ectoblobOperations_le {s : ℕ} (hs : 1 ≤ s) : ectoblobOperations s ≤ 18 * s ^ 5 := by
  have hC : s.choose 4 ≤ s ^ 4 := Nat.choose_le_pow s 4
  have h₄₅ : s ^ 4 ≤ s ^ 5 := Nat.pow_le_pow_right hs (by norm_num)
  have h₂₅ : s ^ 2 ≤ s ^ 5 := Nat.pow_le_pow_right hs (by norm_num)
  have h₅ : s * s ^ 4 = s ^ 5 := by ring
  have h₂ : s * s = s ^ 2 := by ring
  have t₂ : (s - 3) * (2 * (4 * s.choose 4)) ≤ 8 * s ^ 5 := by
    calc _ ≤ s * (2 * (4 * s ^ 4)) := Nat.mul_le_mul (Nat.sub_le _ _) (by omega)
      _ = 8 * s ^ 5 := by ring
  have t₃ : (s - 2) * (4 * s.choose 4 + 2 * (s - 3)) ≤ 4 * s ^ 5 + 2 * s ^ 2 := by
    calc _ ≤ s * (4 * s ^ 4 + 2 * s) := Nat.mul_le_mul (Nat.sub_le _ _) (by omega)
      _ = 4 * s ^ 5 + 2 * s ^ 2 := by ring
  simp only [ectoblobOperations]
  omega

/-- The operations for `mul`: those of `ectoblobOperations`, and `4 C(s, 4)` for each new edge computation at the
contraction steps (`sum_card_recomputedSides_le`, on a binary `T₀`). -/
def ectoblobOperationsMul (s : ℕ) : ℕ :=
  ectoblobOperations s + (∑ k ∈ range (s - 3), (4 + k)) * (4 * s.choose 4)

/-- **"This gives a total time complexity `O(s⁶)`"** for `mul`. -/
theorem ectoblobOperationsMul_le {s : ℕ} (hs : 1 ≤ s) : ectoblobOperationsMul s ≤ 22 * s ^ 6 := by
  have h₁ := ectoblobOperations_le hs
  have hC : s.choose 4 ≤ s ^ 4 := Nat.choose_le_pow s 4
  have h₅₆ : s ^ 5 ≤ s ^ 6 := Nat.pow_le_pow_right hs (by norm_num)
  have h₂ : (∑ k ∈ range (s - 3), (4 + k)) * (4 * s.choose 4) ≤ 4 * s ^ 6 := by
    calc _ ≤ s ^ 2 * (4 * s ^ 4) := Nat.mul_le_mul (sum_range_four_add_le s) (by omega)
      _ = 4 * s ^ 6 := by ring
  simp only [ectoblobOperationsMul]
  omega

/-- The operations if Algorithm 7.1 is evaluated as `treeSeq` is written, with no p-value stored from one iteration to
the next: each of at most `s - 2` trees has the p-values of all its at most `s - 3` edges computed again. Counted as
in `ectoblobOperations`. -/
def ectoblobOperationsRecomputing (s : ℕ) : ℕ :=
  4 * s.choose 4 + (s - 3) * (4 * s.choose 4) +
    (s - 2) * ((s - 3) * (4 * s.choose 4) + 4 * s.choose 4 + 2 * (s - 3))

/-- As written, the algorithm is `O(s⁶)` for every `qType`. So `O(s⁶)` for `mul` needs no count of incident edges:
there are at most `(s - 3)²` edge computations in all. The paper's `O(s⁵)` for `bi` and `quad` needs that a p-value
computed once is stored (`edgeT1P_eq_of_qType_ne_mul`). -/
theorem ectoblobOperationsRecomputing_le {s : ℕ} (hs : 1 ≤ s) : ectoblobOperationsRecomputing s ≤ 18 * s ^ 6 := by
  have hC : s.choose 4 ≤ s ^ 4 := Nat.choose_le_pow s 4
  have h₄₆ : s ^ 4 ≤ s ^ 6 := Nat.pow_le_pow_right hs (by norm_num)
  have t₂ : (s - 3) * (4 * s.choose 4) ≤ 4 * s ^ 6 := by
    calc _ ≤ s * (4 * s ^ 4) := Nat.mul_le_mul (Nat.sub_le _ _) (by omega)
      _ = 4 * s ^ 5 := by ring
      _ ≤ 4 * s ^ 6 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hs (by norm_num))
  have t₃ : (s - 2) * ((s - 3) * (4 * s.choose 4) + 4 * s.choose 4 + 2 * (s - 3)) ≤ 10 * s ^ 6 := by
    have h₁ : (s - 3) * (4 * s.choose 4) ≤ s * (4 * s ^ 4) := Nat.mul_le_mul (Nat.sub_le _ _) (by omega)
    calc _ ≤ s * (s * (4 * s ^ 4) + 4 * s ^ 4 + 2 * s) := Nat.mul_le_mul (Nat.sub_le _ _) (by omega)
      _ = 4 * s ^ 6 + 4 * s ^ 5 + 2 * s ^ 2 := by ring
      _ ≤ 4 * s ^ 6 + 4 * s ^ 6 + 2 * s ^ 6 :=
        Nat.add_le_add (Nat.add_le_add_left (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hs (by norm_num))) _)
          (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hs (by norm_num)))
      _ = 10 * s ^ 6 := by ring
  simp only [ectoblobOperationsRecomputing]
  omega

end Time

end ECToBlob.Counts
