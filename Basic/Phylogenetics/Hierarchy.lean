/-
Adapted from https://github.com/vltanh/lean4-phylogenetics,
commit 06f684e526e276ca2ccf668a1c3a808a2b8c181d.
The upstream source is licensed under the Apache License, Version 2.0:
https://www.apache.org/licenses/LICENSE-2.0
Source regions and adaptations are recorded in docs/ADAPTED_SOURCES.md.
-/
module

public import Mathlib.Data.Finset.Max
public import Mathlib.Data.Finset.BooleanAlgebra
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Data.Fintype.Lattice
public import Mathlib.Tactic.Common

/-!
# Finite phylogenetic hierarchies and their split families

The actual hierarchy laws, clusters, split sides and restrictions are represented by
finite sets. The definitions and proofs are extracted from the tree-only part of
`lean4-phylogenetics`; they impose no binary or network-level restriction and import
no coalescent model. A graph realization and graph-to-hierarchy bridge are separate
constructions, not assumptions hidden in this representation.
-/

@[expose] public section

namespace Phylogenetics

open Finset

variable {X : Type*} [Fintype X] [DecidableEq X]


/-- A hierarchy of clusters on `X`. -/
def IsHierarchy (H : Finset (Finset X)) : Prop :=
  univ ∈ H ∧ (∀ x : X, {x} ∈ H) ∧ (∀ A ∈ H, A.Nonempty) ∧
    ∀ A ∈ H, ∀ B ∈ H, A ⊆ B ∨ B ⊆ A ∨ Disjoint A B

/-- The children of a cluster `A` in a family `H` of clusters: the maximal members of `H`
strictly contained in `A`. -/
def childClusters (H : Finset (Finset X)) (A : Finset X) : Finset (Finset X) :=
  H.filter fun B => B ⊂ A ∧ ∀ C ∈ H, B ⊂ C → ¬ C ⊂ A


/-- The unrooted tree of a rooted tree (or of a rooted forest) `G`: the sides of the splits
induced by its non-root clusters. -/
def unroot {L : Type*} [Fintype L] [DecidableEq L]
    (G : Finset (Finset L)) : Finset (Finset L) :=
  G.erase univ ∪ (G.erase univ).image compl

/-- The clusters of `H` that meet `S`, restricted to `S`, as clusters on the subtype `S`. -/
def restrictClusters (S : Finset X) (H : Finset (Finset X)) : Finset (Finset S) :=
  (H.filter fun A => (A ∩ S).Nonempty).image fun A => A.subtype (· ∈ S)

/-- The induced unrooted tree `T(S)` of an unrooted tree `T` (given by the sides of its splits):
the splits of `T` whose two sides both meet `S`, restricted to `S`. -/
def restrictSplits (S : Finset X) (T : Finset (Finset X)) : Finset (Finset S) :=
  (T.filter fun A => (A ∩ S).Nonempty ∧ (Aᶜ ∩ S).Nonempty).image fun A => A.subtype (· ∈ S)

theorem mem_childClusters {H : Finset (Finset X)} {A B : Finset X} :
    B ∈ childClusters H A ↔ B ∈ H ∧ B ⊂ A ∧ ∀ C ∈ H, B ⊂ C → ¬ C ⊂ A :=
  mem_filter

theorem childClusters_subset (H : Finset (Finset X)) (A : Finset X) : childClusters H A ⊆ H :=
  filter_subset _ _

/-- In a hierarchy, the children of a cluster with at least two elements partition it, and a
singleton has no children. -/
theorem IsHierarchy.childClusters_singleton {H : Finset (Finset X)} (hH : IsHierarchy H) (x : X) :
    childClusters H {x} = ∅ := by
  unfold childClusters
  rw [Finset.filter_eq_empty_iff]
  rintro B hB ⟨hBx, -⟩
  rw [Finset.ssubset_singleton_iff] at hBx
  subst hBx
  exact Finset.not_nonempty_empty (hH.2.2.1 _ hB)

/-- Two distinct children of a cluster of a hierarchy are disjoint. -/
theorem IsHierarchy.disjoint_of_mem_childClusters {H : Finset (Finset X)} (hH : IsHierarchy H)
    {A B C : Finset X} (hB : B ∈ childClusters H A) (hC : C ∈ childClusters H A) (hBC : B ≠ C) :
    Disjoint B C := by
  rw [mem_childClusters] at hB hC
  rcases hH.2.2.2 B hB.1 C hC.1 with h | h | h
  · exact absurd hC.2.1 (hB.2.2 C hC.1 (lt_of_le_of_ne h hBC))
  · exact absurd hB.2.1 (hC.2.2 B hB.1 (lt_of_le_of_ne h hBC.symm))
  · exact h


namespace IsHierarchy

variable {H : Finset (Finset X)}


omit [DecidableEq X] in
/-- Two clusters of a hierarchy with a common element are nested. -/
theorem subset_or_subset_of_mem (hH : IsHierarchy H) {A B : Finset X} (hA : A ∈ H) (hB : B ∈ H)
    {x : X} (hxA : x ∈ A) (hxB : x ∈ B) : A ⊆ B ∨ B ⊆ A := by
  rcases hH.2.2.2 A hA B hB with h | h | h
  · exact Or.inl h
  · exact Or.inr h
  · exact absurd hxB (disjoint_left.1 h hxA)

omit [DecidableEq X] in
/-- Two clusters of a hierarchy that are not disjoint are nested. -/
theorem subset_or_subset_of_not_disjoint (hH : IsHierarchy H) {A B : Finset X} (hA : A ∈ H)
    (hB : B ∈ H) (hAB : ¬ Disjoint A B) : A ⊆ B ∨ B ⊆ A := by
  obtain ⟨x, hxA, hxB⟩ := not_disjoint_iff.1 hAB
  exact hH.subset_or_subset_of_mem hA hB hxA hxB

end IsHierarchy


/-- Every element of a cluster `A` with at least two elements lies in a child of `A`. -/
theorem IsHierarchy.exists_mem_childClusters {H : Finset (Finset X)} (hH : IsHierarchy H)
    {A : Finset X} (hA : 2 ≤ #A) {x : X} (hx : x ∈ A) : ∃ B ∈ childClusters H A, x ∈ B := by
  have hxA : ({x} : Finset X) ⊂ A := by
    refine (singleton_subset_iff.2 hx).ssubset_of_ne ?_
    rintro rfl
    simp at hA
  obtain ⟨B, hB, hmax⟩ := (H.filter fun C => x ∈ C ∧ C ⊂ A).exists_max_image card
    ⟨{x}, mem_filter.2 ⟨hH.2.1 x, mem_singleton_self x, hxA⟩⟩
  rw [mem_filter] at hB
  refine ⟨B, mem_childClusters.2 ⟨hB.1, hB.2.2, fun C hC hBC hCA => ?_⟩, hB.2.1⟩
  have := hmax C (mem_filter.2 ⟨hC, hBC.subset hB.2.1, hCA⟩)
  exact absurd (card_lt_card hBC) (not_lt.2 this)

/-- The children of a cluster `A` with at least two elements cover it. -/
theorem IsHierarchy.sup_childClusters {H : Finset (Finset X)} (hH : IsHierarchy H)
    {A : Finset X} (hA : 2 ≤ #A) : (childClusters H A).sup id = A := by
  refine le_antisymm (Finset.sup_le fun B hB => (mem_childClusters.1 hB).2.1.subset) ?_
  intro x hx
  obtain ⟨B, hB, hxB⟩ := hH.exists_mem_childClusters hA hx
  exact Finset.mem_sup.2 ⟨B, hB, hxB⟩

/-- The children of a cluster are pairwise disjoint. -/
theorem IsHierarchy.pairwiseDisjoint_childClusters {H : Finset (Finset X)} (hH : IsHierarchy H)
    (A : Finset X) : (childClusters H A : Set (Finset X)).PairwiseDisjoint id :=
  fun _ hB _ hC hBC => hH.disjoint_of_mem_childClusters hB hC hBC

/-- A cluster with at least two elements has at least two children. -/
theorem IsHierarchy.two_le_card_childClusters {H : Finset (Finset X)} (hH : IsHierarchy H)
    {A : Finset X} (hA : 2 ≤ #A) : 2 ≤ #(childClusters H A) := by
  by_contra hlt
  have hle : #(childClusters H A) ≤ 1 := by omega
  obtain ⟨x, hx⟩ : A.Nonempty := card_pos.1 (by omega)
  obtain ⟨B, hB, -⟩ := hH.exists_mem_childClusters hA hx
  rw [Finset.card_le_one_iff] at hle
  have hAB : A ⊆ B := fun y hy => by
    obtain ⟨C, hC, hyC⟩ := hH.exists_mem_childClusters hA hy
    exact hle hC hB ▸ hyC
  exact not_subset_of_ssubset (mem_childClusters.1 hB).2.1 hAB


omit [Fintype X] in
/-- The clusters of the induced tree on `S` are the nonempty traces on `S` of the clusters. -/
theorem mem_restrictClusters {S : Finset X} {H : Finset (Finset X)} {C : Finset S} :
    C ∈ restrictClusters S H ↔ ∃ A ∈ H, (A ∩ S).Nonempty ∧ A.subtype (· ∈ S) = C := by
  unfold restrictClusters
  rw [mem_image]
  simp only [mem_filter, and_assoc]

/-- The splits of the induced unrooted tree on `S` are the traces of the splits whose two sides
both meet `S`. -/
theorem mem_restrictSplits {S : Finset X} {T : Finset (Finset X)} {C : Finset S} :
    C ∈ restrictSplits S T ↔
      ∃ A ∈ T, (A ∩ S).Nonempty ∧ (Aᶜ ∩ S).Nonempty ∧ A.subtype (· ∈ S) = C := by
  unfold restrictSplits
  rw [mem_image]
  simp only [mem_filter, and_assoc]

/-- Restricting a hierarchy to nonempty taxa preserves all hierarchy laws.
Adapted from `SpeciesTree.restrict_univ_mem`, `restrict_singleton_mem`,
`restrict_nonempty_of_mem` and `restrict_laminar`: their proofs use only the hierarchy,
so the irrelevant metric data are removed. The proof follows the same trace-of-cluster
construction and laminarity cases as the source. -/
theorem IsHierarchy.restrict {H : Finset (Finset X)} (hH : IsHierarchy H)
    (S : Finset X) (hS : S.Nonempty) : IsHierarchy (restrictClusters S H) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold restrictClusters
    rw [mem_image]
    refine ⟨univ, mem_filter.2 ⟨hH.1, by simpa using hS⟩, ?_⟩
    simp
  · intro x
    unfold restrictClusters
    rw [mem_image]
    refine ⟨{x.1}, mem_filter.2 ⟨hH.2.1 x.1, ⟨x.1, by simp [x.2]⟩⟩, ?_⟩
    ext ⟨y, hy⟩
    rw [mem_subtype, mem_singleton, mem_singleton, Subtype.ext_iff]
  · intro C hC
    obtain ⟨A, hA, rfl⟩ := mem_image.1 hC
    obtain ⟨y, hy⟩ := (mem_filter.1 hA).2
    rw [mem_inter] at hy
    exact ⟨⟨y, hy.2⟩, by simp [hy.1]⟩
  · intro C hC D hD
    obtain ⟨A, hA, rfl⟩ := mem_image.1 hC
    obtain ⟨B, hB, rfl⟩ := mem_image.1 hD
    rcases hH.2.2.2 A (mem_filter.1 hA).1 B (mem_filter.1 hB).1 with h | h | h
    · exact Or.inl (subtype_mono h)
    · exact Or.inr (Or.inl (subtype_mono h))
    · refine Or.inr (Or.inr ?_)
      rw [Finset.disjoint_left] at h ⊢
      intro a ha hb
      exact h (mem_subtype.1 ha) (mem_subtype.1 hb)


section Unroot

variable {L : Type*} [Fintype L] [DecidableEq L]

/-- The sides of the splits of the unrooted tree of `G`: the non-root clusters of `G` and their
complements. -/
theorem mem_unroot {G : Finset (Finset L)} {A : Finset L} :
    A ∈ unroot G ↔ (A ∈ G ∧ A ≠ univ) ∨ (Aᶜ ∈ G ∧ Aᶜ ≠ univ) := by
  unfold unroot
  simp only [mem_union, mem_erase, mem_image]
  constructor
  · rintro (⟨h1, h2⟩ | ⟨B, ⟨hB1, hB2⟩, rfl⟩)
    · exact Or.inl ⟨h2, h1⟩
    · exact Or.inr ⟨by rwa [compl_compl], by rwa [compl_compl]⟩
  · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
    · exact Or.inl ⟨h2, h1⟩
    · exact Or.inr ⟨Aᶜ, ⟨h2, h1⟩, compl_compl A⟩

/-- The unrooted tree of `G` is closed under complements. -/
theorem compl_mem_unroot {G : Finset (Finset L)} {A : Finset L} :
    Aᶜ ∈ unroot G ↔ A ∈ unroot G := by
  rw [mem_unroot, mem_unroot, compl_compl, or_comm]

end Unroot

/-- Compatibility of two sets of taxa is symmetric. -/
private theorem hier_compat_symm {A B : Finset X}
    (h : A ⊆ B ∨ B ⊆ A ∨ Disjoint A B ∨ A ∪ B = univ) :
    B ⊆ A ∨ A ⊆ B ∨ Disjoint B A ∨ B ∪ A = univ := by
  rcases h with h | h | h | h
  · exact Or.inr (Or.inl h)
  · exact Or.inl h
  · exact Or.inr (Or.inr (Or.inl h.symm))
  · exact Or.inr (Or.inr (Or.inr (union_comm A B ▸ h)))

/-- Compatibility of two sets of taxa is preserved by complementing one of them. -/
private theorem hier_compat_compl {A B : Finset X}
    (h : A ⊆ B ∨ B ⊆ A ∨ Disjoint A B ∨ A ∪ B = univ) :
    Aᶜ ⊆ B ∨ B ⊆ Aᶜ ∨ Disjoint Aᶜ B ∨ Aᶜ ∪ B = univ := by
  rcases h with h | h | h | h
  · refine Or.inr (Or.inr (Or.inr (eq_univ_iff_forall.2 fun x => ?_)))
    by_cases hx : x ∈ A
    · exact mem_union_right _ (h hx)
    · exact mem_union_left _ (mem_compl.2 hx)
  · exact Or.inr (Or.inr (Or.inl (disjoint_left.2 fun x hxA hxB => mem_compl.1 hxA (h hxB))))
  · exact Or.inr (Or.inl fun x hxB => mem_compl.2 fun hxA => disjoint_left.1 h hxA hxB)
  · refine Or.inl fun x hx => ?_
    have : x ∈ A ∪ B := h ▸ mem_univ x
    exact (mem_union.1 this).resolve_left (mem_compl.1 hx)

/-- The splits of the unrooted tree of a hierarchy are pairwise compatible: for two sides `A`, `B`
of splits, one contains the other, or they are disjoint, or they cover all taxa. -/
theorem IsHierarchy.compatible_of_mem_unroot {H : Finset (Finset X)} (hH : IsHierarchy H)
    {A B : Finset X} (hA : A ∈ unroot H) (hB : B ∈ unroot H) :
    A ⊆ B ∨ B ⊆ A ∨ Disjoint A B ∨ A ∪ B = univ := by
  have base : ∀ P ∈ H, ∀ Q ∈ H, P ⊆ Q ∨ Q ⊆ P ∨ Disjoint P Q ∨ P ∪ Q = univ :=
    fun P hP Q hQ => by
      rcases hH.2.2.2 P hP Q hQ with h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inl h))
  have right : ∀ A B : Finset X, (A ⊆ B ∨ B ⊆ A ∨ Disjoint A B ∨ A ∪ B = univ) →
      A ⊆ Bᶜ ∨ Bᶜ ⊆ A ∨ Disjoint A Bᶜ ∨ A ∪ Bᶜ = univ :=
    fun A B h => hier_compat_symm (hier_compat_compl (hier_compat_symm h))
  rcases mem_unroot.1 hA with ⟨hA', -⟩ | ⟨hA', -⟩ <;>
    rcases mem_unroot.1 hB with ⟨hB', -⟩ | ⟨hB', -⟩
  · exact base A hA' B hB'
  · simpa only [compl_compl] using right A Bᶜ (base A hA' Bᶜ hB')
  · simpa only [compl_compl] using hier_compat_compl (base Aᶜ hA' B hB')
  · simpa only [compl_compl] using right _ _ (hier_compat_compl (base Aᶜ hA' Bᶜ hB'))



omit [Fintype X] in
/-- The trace of `A` on `S` is nonempty if and only if `A` meets `S`. -/
theorem subtype_nonempty_iff {S A : Finset X} :
    (A.subtype (· ∈ S)).Nonempty ↔ (A ∩ S).Nonempty := by
  constructor
  · rintro ⟨⟨x, hxS⟩, hx⟩
    exact ⟨x, mem_inter.2 ⟨mem_subtype.1 hx, hxS⟩⟩
  · rintro ⟨x, hx⟩
    exact ⟨⟨x, (mem_inter.1 hx).2⟩, mem_subtype.2 (mem_inter.1 hx).1⟩

/-- The trace of the complement is the complement of the trace. -/
theorem subtype_compl {S : Finset X} (A : Finset X) :
    Aᶜ.subtype (· ∈ S) = (A.subtype (· ∈ S))ᶜ := by
  ext x
  simp [mem_subtype, mem_compl]

/-- The trace of `A` on `S` is not all of `S` if and only if `Aᶜ` meets `S`. -/
theorem subtype_ne_univ_iff {S A : Finset X} :
    A.subtype (· ∈ S) ≠ univ ↔ (Aᶜ ∩ S).Nonempty := by
  rw [← subtype_nonempty_iff, subtype_compl, Ne, ← compl_eq_empty_iff,
    ← not_nonempty_iff_eq_empty, not_not]

omit [Fintype X] in
/-- The trace of a cluster meeting `S` is a cluster of the induced tree on `S`. -/
theorem subtype_mem_restrictClusters {S : Finset X} {H : Finset (Finset X)}
    {A : Finset X} (hA : A ∈ H) (hAS : (A ∩ S).Nonempty) :
    A.subtype (· ∈ S) ∈ restrictClusters S H :=
  mem_restrictClusters.2 ⟨A, hA, hAS, rfl⟩

/-- Restricting clusters and then taking split sides agrees with restricting split sides.
This finite-family identity is the proof underlying the source's
`SpeciesTree.restrict_unroot`, with the unused metric tree wrapper removed. -/
theorem unroot_restrictClusters (H : Finset (Finset X)) (S : Finset X) :
    unroot (restrictClusters S H) = restrictSplits S (unroot H) := by
  ext C
  rw [mem_unroot, mem_restrictSplits]
  constructor
  · rintro (⟨hC, hCu⟩ | ⟨hC, hCu⟩)
    · obtain ⟨A, hA, hAS, rfl⟩ := mem_restrictClusters.1 hC
      refine ⟨A, mem_unroot.2 (Or.inl ⟨hA, ?_⟩), hAS, subtype_ne_univ_iff.1 hCu, rfl⟩
      rintro rfl
      exact hCu (subtype_univ _)
    · obtain ⟨A, hA, hAS, hAC⟩ := mem_restrictClusters.1 hC
      have hAu : A ≠ univ := by
        rintro rfl
        exact hCu (hAC ▸ subtype_univ _)
      refine ⟨Aᶜ, compl_mem_unroot.2 (mem_unroot.2 (Or.inl ⟨hA, hAu⟩)),
        subtype_ne_univ_iff.1 (hAC ▸ hCu), by rwa [compl_compl], ?_⟩
      rw [subtype_compl, hAC, compl_compl]
  · rintro ⟨A, hA, hAS, hAcS, rfl⟩
    rcases mem_unroot.1 hA with ⟨hA', -⟩ | ⟨hA', -⟩
    · exact Or.inl ⟨subtype_mem_restrictClusters hA' hAS, subtype_ne_univ_iff.2 hAcS⟩
    · refine Or.inr ⟨?_, ?_⟩
      · rw [← subtype_compl]
        exact subtype_mem_restrictClusters hA' hAcS
      · rw [← subtype_compl]
        exact subtype_ne_univ_iff.2 (by rwa [compl_compl])

end Phylogenetics
