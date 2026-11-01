module

public import Basic.Defs
public import Phylogenetics.Tree.Splits
public import TINNiK.Counts
public import TOBQMC.BipartitionSearch

/-!
# TOB-QMC: operation counts

The counts behind the running times that TOB-QMC claims (v5). No machine model is used: each
theorem counts the objects that a step of the method enumerates, as the `Finset.card` of a set, and says what each one
costs in the paper's terms; the bounds are explicit.

* Embedded line 91, "reduce the number of four-taxon subsets tested per edge from `O(n⁴)` to `O(n)`": around an edge
  there are `C(|A|, 2) C(|Aᶜ|, 2)` subsets (`card_bipartitionQuartets`), up to `C(n/2, 2)²`, and 3f1a tests `n - 3`
  (`threeFixOneAlter_isDisjointCover`).
* Embedded lines 601-605, "`O(n)` 4-taxon subsets around each edge, so `O(n²)` in total [...] `O(n² k + n log(n) k)`":
  a binary tree has `n - 3` internal edges (`card_internalSides`, `card_edgeSides`), so at most `(n - 3)²` subsets in
  total (`card_threeFixOneAlter_total_le`), each read off `k` gene trees, for three quartet trees
  (`sum_card_evaluations`). `threeFixOneAlterOperations_le` is the total with the costs of an LCA and of the
  precomputation as parameters.
* Embedded lines 616-623 on the bipartition search: `(n - 3) ((n - 3) + 2 limit + 2 (n - 4))` subsets in total
  (`card_search_total_le`), `O(n³)` at a limit of `O(n²)` (`search_total_le_of_limit_le`), so the time claimed is
  unchanged by adding 3f1a to the search.

## An edge and its sides

`internalSides T` holds both sides of each internal edge, and `tobqmc` is written with one disjoint cover per side.
The method runs one search per edge, so the counts here choose one side per edge: `edgeSides r T`, the side without
the taxon `r`.
-/

@[expose] public noncomputable section

open Phylogenetics Phylogenetics.RootedNetwork Finset
open scoped Classical

namespace TOBQMC

variable {X : Type*} [Fintype X] [DecidableEq X]

/-! ### The internal edges of a binary tree -/

section Edges

variable {H : Finset (Finset X)}

/-- A binary hierarchy has exactly `N - 1` clusters of at least two taxa, and `2 N - 1` clusters. -/
theorem card_add_one_of_binary (hH : IsHierarchy H) (hbin : ∀ A ∈ H, 2 ≤ A.card → (childClusters H A).card = 2) :
    H.card + 1 = 2 * Fintype.card X := by
  have hsum := TINNiK.sum_card_childClusters hH
  have htot := card_filter_add_card_filter_not (s := H) (fun A : Finset X => 2 ≤ A.card)
  rw [TINNiK.card_filter_not_two_le hH] at htot
  have hsplit := sum_filter_add_sum_filter_not H (fun A : Finset X => 2 ≤ A.card)
    (fun A => (childClusters H A).card)
  have h₁ : ∑ A ∈ H.filter (fun A : Finset X => 2 ≤ A.card), (childClusters H A).card =
      (H.filter fun A : Finset X => 2 ≤ A.card).card * 2 :=
    (sum_congr rfl fun A hA => hbin A (mem_filter.mp hA).1 (mem_filter.mp hA).2).trans (by
      rw [sum_const, smul_eq_mul])
  have h₂ : ∑ A ∈ H.filter (fun A : Finset X => ¬ 2 ≤ A.card), (childClusters H A).card = 0 := by
    refine sum_eq_zero fun A hA => ?_
    obtain ⟨hAH, h2⟩ := mem_filter.mp hA
    have hpos := card_pos.mpr (hH.2.2.1 A hAH)
    obtain ⟨x, rfl⟩ := card_eq_one.mp (by omega : A.card = 1)
    rw [hH.childClusters_singleton x, card_empty]
  omega

/-- Both sides of an edge of a rooted tree are clusters only at the two children of the root. -/
theorem mem_childClusters_univ_iff (hH : IsHierarchy H) (h2 : 2 ≤ Fintype.card X)
    (hbin : (childClusters H univ).card = 2) {A : Finset X} :
    A ∈ childClusters H univ ↔ (A ∈ H ∧ A ≠ univ) ∧ Aᶜ ∈ H ∧ Aᶜ ≠ univ := by
  have huniv : 2 ≤ (univ : Finset X).card := by rwa [card_univ]
  constructor
  · intro hA
    obtain ⟨hAH, hAu, -⟩ := mem_childClusters.mp hA
    have hAne := (hH.2.2.1 A hAH)
    obtain ⟨C₁, C₂, hne, hC⟩ := card_eq_two.mp hbin
    have hsup := hH.sup_childClusters huniv
    rw [hC] at hsup
    simp only [sup_insert, sup_singleton, id, sup_eq_union] at hsup
    have hdis : Disjoint C₁ C₂ := hH.disjoint_of_mem_childClusters (hC ▸ mem_insert_self _ _)
      (hC ▸ mem_insert_of_mem (mem_singleton_self _)) hne
    have hC₁H : C₁ ∈ H := (mem_childClusters.mp (hC ▸ mem_insert_self _ _)).1
    have hC₂H : C₂ ∈ H := (mem_childClusters.mp (hC ▸ mem_insert_of_mem (mem_singleton_self _))).1
    have hc₁ : C₁ᶜ = C₂ := by
      ext w
      have hw : w ∈ C₁ ∪ C₂ := hsup ▸ mem_univ w
      simp only [mem_compl]
      constructor
      · exact fun h => (mem_union.mp hw).resolve_left h
      · exact fun h h' => disjoint_left.mp hdis h' h
    have hAc : Aᶜ ∈ H := by
      rw [hC] at hA
      rcases mem_insert.mp hA with rfl | hA'
      · rwa [hc₁]
      · rw [mem_singleton.mp hA', ← hc₁, compl_compl]
        exact hC₁H
    refine ⟨⟨hAH, hAu.ne⟩, hAc, ?_⟩
    intro h
    obtain ⟨a, ha⟩ := hAne
    exact (mem_compl.mp (h ▸ mem_univ a)) ha
  · rintro ⟨⟨hAH, hAu⟩, hAc, hAcu⟩
    refine mem_childClusters.mpr ⟨hAH, ssubset_univ_iff.mpr hAu, fun C hC hAC hCu => ?_⟩
    have hAne := hH.2.2.1 A hAH
    rcases hH.2.2.2 C hC Aᶜ hAc with h | h | h
    · obtain ⟨a, ha⟩ := hAne
      exact (mem_compl.mp (h (hAC.subset ha))) ha
    · refine hCu.2 fun w _ => ?_
      by_cases hw : w ∈ A
      · exact hAC.subset hw
      · exact h (mem_compl.mpr hw)
    · refine hAC.2 fun w hw => ?_
      by_contra hwA
      exact disjoint_left.mp h hw (mem_compl.mpr hwA)

/-- A binary tree has `4 N - 6` sides of splits: `2 N - 3` edges. -/
theorem card_of_isBinaryTree {T : Finset (Finset X)} (hT : IsBinaryTree T) (h2 : 2 ≤ Fintype.card X) :
    T.card + 6 = 4 * Fintype.card X := by
  obtain ⟨H, hH, rfl, hbin⟩ := hT
  have hcard := card_add_one_of_binary hH hbin
  have huniv : 2 ≤ (univ : Finset X).card := by rwa [card_univ]
  have hchild := hbin univ hH.1 huniv
  have hinter : (H.erase univ) ∩ (H.erase univ).image compl = childClusters H univ := by
    ext A
    rw [mem_childClusters_univ_iff hH h2 hchild]
    simp only [mem_inter, mem_erase, mem_image]
    constructor
    · rintro ⟨⟨hu, hA⟩, C, ⟨hCu, hC⟩, rfl⟩
      exact ⟨⟨hA, hu⟩, by rwa [compl_compl], by rwa [compl_compl]⟩
    · rintro ⟨⟨hA, hu⟩, hAc, hAcu⟩
      exact ⟨⟨hu, hA⟩, Aᶜ, ⟨hAcu, hAc⟩, compl_compl A⟩
  have hu := card_union_add_card_inter (H.erase univ) ((H.erase univ).image compl)
  rw [hinter, hchild, card_image_of_injective _ compl_injective, card_erase_of_mem hH.1] at hu
  have hT : unroot H = (H.erase univ) ∪ (H.erase univ).image compl := rfl
  rw [hT]
  omega

/-- **A binary tree has `n - 3` internal edges**, for `n ≥ 3`: `2 (n - 3)` sides. The `4 n - 6` sides of its splits
have the pendant ones, `2 n` of them. -/
theorem card_internalSides {T : Finset (Finset X)} (hT : IsBinaryTree T) (h3 : 3 ≤ Fintype.card X) :
    (internalSides T).card + 6 = 2 * Fintype.card X := by
  have hTu : IsUnrootedTree T := by
    obtain ⟨H, hH, hu, -⟩ := hT
    exact ⟨H, hH, hu⟩
  have hcard := card_of_isBinaryTree hT (by omega)
  have hsplit := card_filter_add_card_filter_not (s := T) (fun A : Finset X => 2 ≤ A.card ∧ 2 ≤ Aᶜ.card)
  have hpend : (T.filter fun A : Finset X => ¬ (2 ≤ A.card ∧ 2 ≤ Aᶜ.card)) =
      (univ.image fun x : X => ({x} : Finset X)) ∪ univ.image fun x : X => ({x} : Finset X)ᶜ := by
    ext A
    simp only [mem_filter, mem_union, mem_image, mem_univ, true_and]
    constructor
    · rintro ⟨hA, hsmall⟩
      obtain ⟨hne, hne'⟩ := Level1.nonempty_of_mem_isUnrootedTree hTu hA
      have h₁ := card_pos.mpr hne
      have h₂ := card_pos.mpr hne'
      by_cases hc : A.card = 1
      · obtain ⟨x, rfl⟩ := card_eq_one.mp hc
        exact Or.inl ⟨x, rfl⟩
      · have hc' : Aᶜ.card = 1 := by
          by_contra hc'
          exact hsmall ⟨by omega, by omega⟩
        obtain ⟨x, hx⟩ := card_eq_one.mp hc'
        exact Or.inr ⟨x, by rw [← hx, compl_compl]⟩
    · obtain ⟨H, hH, rfl, -⟩ := hT
      have hsing : ∀ x : X, ({x} : Finset X) ≠ univ := by
        intro x hx
        have := congrArg card hx
        rw [card_singleton, card_univ] at this
        omega
      have hmem : ∀ x : X, ({x} : Finset X) ∈ unroot H := fun x =>
        mem_unroot.mpr (Or.inl ⟨hH.2.1 x, hsing x⟩)
      rintro (⟨x, rfl⟩ | ⟨x, rfl⟩)
      · refine ⟨hmem x, fun h => ?_⟩
        have := h.1
        rw [card_singleton] at this
        omega
      · refine ⟨compl_mem_unroot.mpr (hmem x), fun h => ?_⟩
        have := h.2
        rw [compl_compl, card_singleton] at this
        omega
  have hdis : Disjoint (univ.image fun x : X => ({x} : Finset X)) (univ.image fun x : X => ({x} : Finset X)ᶜ) := by
    rw [disjoint_left]
    intro A hA hA'
    obtain ⟨x, -, rfl⟩ := mem_image.mp hA
    obtain ⟨y, -, hy⟩ := mem_image.mp hA'
    have := congrArg card hy
    rw [card_compl, card_singleton, card_singleton] at this
    omega
  have hinj : Function.Injective fun x : X => ({x} : Finset X)ᶜ := fun a b h =>
    singleton_injective (compl_injective h)
  rw [hpend, card_union_of_disjoint hdis, card_image_of_injective _ singleton_injective,
    card_image_of_injective _ hinj, card_univ] at hsplit
  simp only [internalSides]
  omega

/-- One side per internal edge: the side without the taxon `r`. -/
def edgeSides (r : X) (T : Finset (Finset X)) : Finset (Finset X) := (internalSides T).filter fun A => r ∉ A

/-- **One side per edge: `n - 3` of them.** -/
theorem card_edgeSides {T : Finset (Finset X)} (hT : IsBinaryTree T) (h3 : 3 ≤ Fintype.card X) (r : X) :
    (edgeSides r T).card + 3 = Fintype.card X := by
  have hTc : ∀ A ∈ internalSides T, Aᶜ ∈ internalSides T := by
    intro A hA
    obtain ⟨H, -, rfl, -⟩ := hT
    obtain ⟨hAT, h₁, h₂⟩ := mem_filter.mp hA
    exact mem_filter.mpr ⟨compl_mem_unroot.mpr hAT, h₂, by rwa [compl_compl]⟩
  have himg : (internalSides T).filter (fun A => ¬ r ∉ A) = (edgeSides r T).image compl := by
    ext A
    simp only [mem_filter, not_not, edgeSides, mem_image]
    constructor
    · rintro ⟨hA, hr⟩
      exact ⟨Aᶜ, ⟨hTc A hA, by simpa using hr⟩, compl_compl A⟩
    · rintro ⟨C, ⟨hC, hr⟩, rfl⟩
      exact ⟨hTc C hC, by simpa using hr⟩
  have hsplit := card_filter_add_card_filter_not (s := internalSides T) (fun A : Finset X => r ∉ A)
  rw [himg, card_image_of_injective _ compl_injective] at hsplit
  have hcard := card_internalSides hT h3
  simp only [edgeSides] at hsplit ⊢
  omega

/-- A set of four-taxon subsets per edge, of at most `m` subsets each, is at most `(n - 3) m` subsets in total. -/
theorem card_biUnion_edgeSides_le {T : Finset (Finset X)} (hT : IsBinaryTree T) (h3 : 3 ≤ Fintype.card X) (r : X)
    {Q : Finset X → Finset (Finset X)} {m : ℕ} (hQ : ∀ A ∈ edgeSides r T, (Q A).card ≤ m) :
    ((edgeSides r T).biUnion Q).card ≤ (Fintype.card X - 3) * m := by
  have := card_biUnion_le_card_mul _ _ _ hQ
  have hc := card_edgeSides hT h3 r
  rwa [show (edgeSides r T).card = Fintype.card X - 3 by omega] at this

end Edges

/-! ### 3-fix-1-alter -/

section ThreeFixOneAlter

variable {T : Finset (Finset X)}

/-- **"Our 3f1a algorithm tests just `O(n)` 4-taxon subsets around each edge, so `O(n²)` in total"** (embedded lines
601-602): at most `(n - 3)²` four-taxon subsets on a binary tree, run on one side of each edge. -/
theorem card_threeFixOneAlter_total_le (hT : IsBinaryTree T) (h3 : 3 ≤ Fintype.card X) (r : X)
    {P : Finset X → Fin 4 → Finset X} {z : Finset X → Fin 4 → X}
    (hP : ∀ A ∈ internalSides T, ∀ i j, i ≠ j → Disjoint (P A i) (P A j))
    (hcover : ∀ A ∈ internalSides T, univ.biUnion (P A) = univ)
    (hP₁ : ∀ A ∈ internalSides T, P A 0 ∪ P A 1 = A)
    (hmem : ∀ A ∈ internalSides T, ∀ i, P A i ∈ T)
    (hz : ∀ A ∈ internalSides T, ∀ i, z A i ∈ P A i) :
    ((edgeSides r T).biUnion fun A => threeFixOneAlter (P A) (z A)).card ≤
      (Fintype.card X - 3) * (Fintype.card X - 3) := by
  refine card_biUnion_edgeSides_le hT h3 r fun A hA => ?_
  have hA' := (mem_filter.mp hA).1
  exact (threeFixOneAlter_isDisjointCover hT hA' (P A) (hP A hA') (hcover A hA') (hP₁ A hA') (hmem A hA')
    (z A) (hz A hA')).2.le

/-- **The p-values read off the gene trees.** Each four-taxon subset tested needs its qCFs on `k` gene trees:
`quartetCount` evaluates `Displays` on each of its three quartet trees and each gene tree. Counted: these evaluations,
`3 k` per subset. -/
theorem sum_card_evaluations {Y : Finset (Finset X)} (hY : ∀ q ∈ Y, q.card = 4) (k : ℕ) :
    ∑ q ∈ Y, (treesOn q ×ˢ (univ : Finset (Fin k))).card = 3 * k * Y.card := by
  have h : ∀ q ∈ Y, (treesOn q ×ˢ (univ : Finset (Fin k))).card = 3 * k := fun q hq => by
    rw [card_product, card_treesOn (hY q hq)]
    simp
  rw [sum_congr rfl h, sum_const, smul_eq_mul, mul_comm]

/-- The operations of 3f1a on a binary tree (embedded lines 602-605), counted as: for at most `(n - 3)²` four-taxon
subsets, `3 k` evaluations of `Displays` as in `sum_card_evaluations`, each of cost `L`, the number of LCA queries
with their cost; and the precomputation, of cost `P n ⌊log₂ n⌋` per gene tree. The paper has `L = O(1)`, from an LCA
query of `O(1)` time after a precomputation of `O(n log n)`. -/
def threeFixOneAlterOperations (n k L P : ℕ) : ℕ :=
  (n - 3) * (n - 3) * (3 * k * L) + P * n * Nat.log 2 n * k

/-- **"The total time complexity of applying the 3f1a algorithm to every branch is `O(n² k + n log(n) k)`"** (embedded
line 605), which is `O(n² k)`: the precomputation does not change the order. -/
theorem threeFixOneAlterOperations_le (n k L P : ℕ) :
    threeFixOneAlterOperations n k L P ≤ 3 * L * (n ^ 2 * k) + P * (n * Nat.log 2 n * k) ∧
      threeFixOneAlterOperations n k L P ≤ (3 * L + P) * (n ^ 2 * k) := by
  have h₁ : (n - 3) * (n - 3) ≤ n ^ 2 := by
    rw [sq]
    exact Nat.mul_le_mul (Nat.sub_le _ _) (Nat.sub_le _ _)
  have hfirst : (n - 3) * (n - 3) * (3 * k * L) ≤ n ^ 2 * (3 * k * L) := Nat.mul_le_mul_right _ h₁
  have hlog : n * Nat.log 2 n ≤ n ^ 2 := by
    rw [sq]
    exact Nat.mul_le_mul_left _ (Nat.log_le_self 2 n)
  have hsecond : P * (n * Nat.log 2 n * k) ≤ P * (n ^ 2 * k) :=
    Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ hlog)
  have heq₁ : n ^ 2 * (3 * k * L) = 3 * L * (n ^ 2 * k) := by ring
  have heq₂ : P * n * Nat.log 2 n * k = P * (n * Nat.log 2 n * k) := by ring
  have heq₃ : (3 * L + P) * (n ^ 2 * k) = 3 * L * (n ^ 2 * k) + P * (n ^ 2 * k) := by ring
  simp only [threeFixOneAlterOperations]
  rw [heq₂, heq₃]
  rw [heq₁] at hfirst
  constructor <;> omega

end ThreeFixOneAlter

/-! ### All four-taxon subsets around an edge -/

section Around

variable {A : Finset X}

/-- **The subsets around an edge**: `C(|A|, 2) C(|Aᶜ|, 2)` quartet trees have a cherry on each side. An exhaustive
search around the edge tests these. -/
theorem card_bipartitionQuartets (A : Finset X) :
    (bipartitionQuartets A).card = A.card.choose 2 * Aᶜ.card.choose 2 := by
  rw [← card_powersetCard, ← card_powersetCard, ← card_product]
  refine card_nbij (fun s => (A ∩ s.taxa, Aᶜ ∩ s.taxa)) ?_ ?_ ?_
  · intro s hs
    have hbi : A ∩ s.taxa ∈ s.val := (mem_filter.mp (mem_coe.mp hs)).2
    have hsd : Aᶜ ∩ s.taxa = s.taxa \ (A ∩ s.taxa) := by
      ext x
      simp only [mem_inter, mem_compl, mem_sdiff]
      tauto
    refine mem_coe.mpr (mem_product.mpr ⟨mem_powersetCard.mpr ⟨inter_subset_left, s.card_of_mem hbi⟩,
      mem_powersetCard.mpr ⟨inter_subset_left, ?_⟩⟩)
    change (Aᶜ ∩ s.taxa).card = 2
    rw [hsd]
    exact s.card_of_mem (s.sdiff_mem hbi)
  · intro s hs s' hs' heq
    have hbi : A ∩ s.taxa ∈ s.val := (mem_filter.mp (mem_coe.mp hs)).2
    have hbi' : A ∩ s'.taxa ∈ s'.val := (mem_filter.mp (mem_coe.mp hs')).2
    obtain ⟨h₁, h₂⟩ := Prod.mk.inj heq
    have ht : s.taxa = s'.taxa := by
      ext x
      by_cases hx : x ∈ A
      · have := congrArg (x ∈ ·) h₁
        simpa [hx] using this
      · have := congrArg (x ∈ ·) h₂
        simpa [hx] using this
    exact QuartetTree.eq_of_taxa_eq_of_mem ht hbi (h₁ ▸ hbi')
  · rintro ⟨P, R⟩ hPR
    obtain ⟨hP, hR⟩ := mem_product.mp (mem_coe.mp hPR)
    obtain ⟨hPA, hP2⟩ := mem_powersetCard.mp hP
    obtain ⟨hRA, hR2⟩ := mem_powersetCard.mp hR
    have hdisj : Disjoint P R := disjoint_left.mpr fun x hx hxR => mem_compl.mp (hRA hxR) (hPA hx)
    have hq : (P ∪ R).card = 4 := by
      rw [card_union_of_disjoint hdisj, hP2, hR2]
    refine ⟨quartetOfCherry (P ∪ R) P hq subset_union_left hP2, mem_coe.mpr (mem_filter.mpr ⟨mem_univ _, ?_⟩), ?_⟩
    all_goals
      have ht := quartetOfCherry_taxa (P ∪ R) P hq subset_union_left hP2
      have hi₁ : A ∩ (P ∪ R) = P := by
        ext x
        simp only [mem_inter, mem_union]
        constructor
        · rintro ⟨hx, hx' | hx'⟩
          · exact hx'
          · exact absurd hx (mem_compl.mp (hRA hx'))
        · exact fun hx => ⟨hPA hx, Or.inl hx⟩
    · rw [ht, hi₁]
      simp
    · have hi₂ : Aᶜ ∩ (P ∪ R) = R := by
        ext x
        simp only [mem_inter, mem_union, mem_compl]
        constructor
        · rintro ⟨hx, hx' | hx'⟩
          · exact absurd (hPA hx') hx
          · exact hx'
        · exact fun hx => ⟨mem_compl.mp (hRA hx), Or.inr hx⟩
      simp only [ht, hi₁, hi₂]

/-- **"From `O(n⁴)`"** (embedded line 91): the four-taxon subsets around an edge are at most `n⁴`, and `C(m, 2)²` on
`n = 2 m` taxa when the edge halves the taxa, against `n - 3` for 3f1a. -/
theorem card_bipartitionQuartets_le (A : Finset X) : (bipartitionQuartets A).card ≤ Fintype.card X ^ 4 := by
  rw [card_bipartitionQuartets]
  have h₁ : A.card.choose 2 ≤ Fintype.card X ^ 2 :=
    (Nat.choose_le_pow _ _).trans (Nat.pow_le_pow_left (card_le_univ A) 2)
  have h₂ : Aᶜ.card.choose 2 ≤ Fintype.card X ^ 2 :=
    (Nat.choose_le_pow _ _).trans (Nat.pow_le_pow_left (card_le_univ _) 2)
  calc _ ≤ Fintype.card X ^ 2 * Fintype.card X ^ 2 := Nat.mul_le_mul h₁ h₂
    _ = _ := by ring

/-- When an edge halves the taxa, it has `C(m, 2)²` four-taxon subsets around it: order `n⁴`. -/
theorem card_bipartitionQuartets_of_halves {m : ℕ} (h₁ : A.card = m) (h₂ : Aᶜ.card = m) :
    (bipartitionQuartets A).card = m.choose 2 ^ 2 := by
  rw [card_bipartitionQuartets, h₁, h₂, sq]

end Around

/-! ### The bipartition search with 3f1a -/

section Search

variable {T : Finset (Finset X)}

/-- **The test count of the combination, in total**: `(n - 3) ((n - 3) + 2 limit + 2 (n - 4))` four-taxon subsets, on
one side of each of the `n - 3` edges, the search being Algorithm 2, around each edge, and `Q` having `n - 3` subsets
per edge. -/
theorem card_search_total_le (hT : IsBinaryTree T) (h3 : 3 ≤ Fintype.card X) (r : X)
    {p : Finset X → SearchTuple X → ℝ} {argmin : Finset X → Finset (SearchTuple X) → SearchTuple X} {limit : ℕ}
    {pick : Finset X → ℕ → SearchTuple X} {Q : Finset X → Finset (Finset X)}
    (hargmin : ∀ A ∈ edgeSides r T, IsArgmin (p A) (argmin A))
    (hpick : ∀ A ∈ edgeSides r T, ∀ k, (pick A k).IsAround A)
    (hQ : ∀ A ∈ edgeSides r T, (Q A).card = Fintype.card X - 3) :
    ((edgeSides r T).biUnion fun A => Q A ∪ (bipartitionSearch A (p A) (argmin A) limit (pick A)).testedSets).card ≤
      (Fintype.card X - 3) * ((Fintype.card X - 3) + 2 * limit + 2 * (Fintype.card X - 4)) :=
  card_biUnion_edgeSides_le hT h3 r fun A hA =>
    card_threeFixOneAlter_union_testedSets_le (hargmin A hA) (hpick A hA) (hQ A hA)

/-- **"By default, we bound the number of tests conducted by `O(n²)`"** (embedded line 618): at a limit of at most `C
n²`, the combination tests at most `(2 C + 3) n³` subsets, so with `3 k` evaluations each, `O(n³ k)`. Adding 3f1a adds
`(n - 3)²` to the search's own count, of a lower order: it "does not increase time complexity" (embedded line 623). -/
theorem search_total_le_of_limit_le {n limit C : ℕ} (hn : 1 ≤ n) (hlimit : limit ≤ C * n ^ 2) :
    (n - 3) * ((n - 3) + 2 * limit + 2 * (n - 4)) = (n - 3) * (2 * limit + 2 * (n - 4)) + (n - 3) ^ 2 ∧
      (n - 3) * ((n - 3) + 2 * limit + 2 * (n - 4)) ≤ (2 * C + 3) * n ^ 3 := by
  constructor
  · rw [sq]
    ring
  · have h₁ : (n - 3) + 2 * limit + 2 * (n - 4) ≤ 3 * n + 2 * (C * n ^ 2) := by omega
    have hnn : 3 * n ≤ 3 * n ^ 2 := by nlinarith
    calc (n - 3) * ((n - 3) + 2 * limit + 2 * (n - 4))
        ≤ n * (3 * n ^ 2 + 2 * (C * n ^ 2)) :=
          Nat.mul_le_mul (Nat.sub_le _ _) (h₁.trans (by omega))
      _ = (2 * C + 3) * n ^ 3 := by ring

end Search

end TOBQMC
