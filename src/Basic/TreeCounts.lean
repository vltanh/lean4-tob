module

public import Phylogenetics.Hierarchy.Basic
public import Phylogenetics.Tree.Splits

/-!
# How many splits a tree has

Counts that the running times of TINNiK, TOB-QMC and ECToBlob use.

* A hierarchy has one more cluster than the sum of the numbers of children (`TINNiK.sum_card_childClusters`), and
  as many singletons as taxa (`TINNiK.card_filter_not_two_le`), so a binary hierarchy has `2n - 1` clusters
  (`TOBQMC.card_add_one_of_binary`) and an unrooted tree at most `2n - 3` sides (`TINNiK.card_le_of_isUnrootedTree`).
* A binary tree on `n ≥ 3` taxa has `n - 3` internal edges (`TOBQMC.card_internalSides`, `TOBQMC.card_edgeSides`).
-/

@[expose] public noncomputable section

open scoped Classical

section
open Phylogenetics Finset

namespace TINNiK

variable {X : Type*} [Fintype X] [DecidableEq X]

section Trees

variable {H : Finset (Finset X)}

/-- The clusters other than the root are the children of the clusters, each of one. -/
theorem sum_card_childClusters (hH : IsHierarchy H) : ∑ A ∈ H, (childClusters H A).card + 1 = H.card := by
  have hunion : H.biUnion (childClusters H) = H.erase univ := by
    ext C
    simp only [mem_biUnion, mem_erase]
    constructor
    · rintro ⟨A, -, hC⟩
      obtain ⟨hCH, hCA, -⟩ := mem_childClusters.mp hC
      exact ⟨fun h => (h ▸ hCA).2 (subset_univ A), hCH⟩
    · rintro ⟨hCu, hCH⟩
      exact ⟨_, hH.parentCluster_mem hCH hCu, hH.mem_childClusters_parentCluster hCH hCu⟩
  have hdis : ∀ A ∈ H, ∀ A' ∈ H, A ≠ A' → Disjoint (childClusters H A) (childClusters H A') := by
    intro A hA A' hA' hne
    rw [disjoint_left]
    intro C hC hC'
    exact hne ((hH.parentCluster_eq_of_mem_childClusters hA hC).symm.trans
      (hH.parentCluster_eq_of_mem_childClusters hA' hC'))
  have hcard := card_biUnion hdis
  rw [hunion, card_erase_of_mem hH.1] at hcard
  have := card_pos.mpr ⟨_, hH.1⟩
  omega

omit [DecidableEq X] in
/-- The clusters of one taxon are `N` many. -/
theorem card_filter_not_two_le (hH : IsHierarchy H) : (H.filter fun A => ¬ 2 ≤ A.card).card = Fintype.card X := by
  have heq : (H.filter fun A => ¬ 2 ≤ A.card) = univ.image fun x : X => ({x} : Finset X) := by
    ext A
    simp only [mem_filter, mem_image, mem_univ, true_and]
    constructor
    · rintro ⟨hA, h2⟩
      have hpos := card_pos.mpr (hH.2.2.1 A hA)
      obtain ⟨x, rfl⟩ := card_eq_one.mp (by omega : A.card = 1)
      exact ⟨x, rfl⟩
    · rintro ⟨x, rfl⟩
      exact ⟨hH.2.1 x, by simp⟩
  rw [heq, card_image_of_injective _ singleton_injective, card_univ]

/-- A hierarchy has at most `N - 1` clusters of at least two taxa. -/
theorem card_filter_two_le_add_one_le (hH : IsHierarchy H) :
    (H.filter fun A => 2 ≤ A.card).card + 1 ≤ Fintype.card X := by
  have hsum := sum_card_childClusters hH
  have htot := card_filter_add_card_filter_not (s := H) (fun A : Finset X => 2 ≤ A.card)
  rw [card_filter_not_two_le hH] at htot
  have hle : 2 * (H.filter fun A => 2 ≤ A.card).card ≤ ∑ A ∈ H, (childClusters H A).card := by
    calc 2 * (H.filter fun A => 2 ≤ A.card).card = ∑ _A ∈ H.filter (fun A => 2 ≤ A.card), 2 := by
          rw [sum_const, smul_eq_mul, mul_comm]
      _ ≤ ∑ A ∈ H.filter (fun A => 2 ≤ A.card), (childClusters H A).card :=
          sum_le_sum fun A hA => hH.two_le_card_childClusters (mem_filter.mp hA).2
      _ ≤ ∑ A ∈ H, (childClusters H A).card := sum_le_sum_of_subset (filter_subset _ _)
  omega

/-- A hierarchy has at most `2 N - 1` clusters. -/
theorem card_add_one_le_of_isHierarchy (hH : IsHierarchy H) : H.card + 1 ≤ 2 * Fintype.card X := by
  have htot := card_filter_add_card_filter_not (s := H) (fun A : Finset X => 2 ≤ A.card)
  rw [card_filter_not_two_le hH] at htot
  have := card_filter_two_le_add_one_le hH
  omega

/-- **A tree on `N` taxa has at most `4 N - 4` sides of splits**, so at most `2 N - 2` edges. -/
theorem card_le_of_isUnrootedTree {T : Finset (Finset X)} (hT : IsUnrootedTree T) :
    T.card ≤ 4 * Fintype.card X - 4 := by
  obtain ⟨H, hH, rfl⟩ := hT
  have h₁ := card_add_one_le_of_isHierarchy hH
  have h₂ : (unroot H).card ≤ 2 * (H.erase univ).card := by
    refine (card_union_le _ _).trans ?_
    have := card_image_le (s := H.erase univ) (f := compl)
    omega
  rw [card_erase_of_mem hH.1] at h₂
  omega

end Trees

end TINNiK
end

section
open Phylogenetics Phylogenetics.RootedNetwork Finset

namespace TOBQMC

variable {V E X : Type*} [Fintype X] [DecidableEq X]

namespace Level1

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

end Level1

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

end TOBQMC
end
