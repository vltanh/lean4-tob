/-
Adapted from https://github.com/vltanh/lean4-phylogenetics,
commit 06f684e526e276ca2ccf668a1c3a808a2b8c181d, Apache-2.0.
Exact source regions are recorded in docs/ADAPTED_SOURCES.md.
-/
module

public import Basic.Phylogenetics.Hierarchy

/-! Parent clusters in finite phylogenetic hierarchies. -/

@[expose] public section

namespace Phylogenetics
open Finset
variable {X : Type*} [Fintype X] [DecidableEq X]

namespace IsHierarchy
variable {H : Finset (Finset X)}

/-- The clusters of a hierarchy containing a common element `x` and satisfying `p` are closed
under intersection. -/
private theorem hier_inf_mem (hH : IsHierarchy H) (x : X) (p : Finset X → Prop) :
    ∀ C ∈ {C | C ∈ H ∧ x ∈ C ∧ p C}, ∀ D ∈ {C | C ∈ H ∧ x ∈ C ∧ p C},
      C ⊓ D ∈ {C | C ∈ H ∧ x ∈ C ∧ p C} := by
  rintro C hC D hD
  rcases hH.subset_or_subset_of_mem hC.1 hD.1 hC.2.1 hD.2.1 with h | h
  · rwa [inf_eq_left.2 h]
  · rwa [inf_eq_right.2 h]


end IsHierarchy

/-- The parent of a cluster `A` of `H`: the smallest cluster of `H` strictly containing `A` (the
intersection of the clusters of `H` strictly containing `A`). -/
def parentCluster (H : Finset (Finset X)) (A : Finset X) : Finset X :=
  (H.filter (A ⊂ ·)).inf id

/-- The parent of `A` is contained in every cluster strictly containing `A`. -/
theorem parentCluster_subset {H : Finset (Finset X)} {A C : Finset X} (hC : C ∈ H)
    (hAC : A ⊂ C) : parentCluster H A ⊆ C :=
  Finset.inf_le (f := id) (mem_filter.2 ⟨hC, hAC⟩)

namespace IsHierarchy

variable {H : Finset (Finset X)}

private theorem hier_parentCluster_aux (hH : IsHierarchy H) {A : Finset X} (hA : A ∈ H)
    (hAu : A ≠ univ) : parentCluster H A ∈ H ∧ A ⊂ parentCluster H A := by
  obtain ⟨a, ha⟩ := hH.2.2.1 A hA
  have := Finset.inf_mem {C | C ∈ H ∧ a ∈ C ∧ A ⊂ C} ⟨hH.1, mem_univ a, ssubset_univ_iff.2 hAu⟩
    (hier_inf_mem hH a (A ⊂ ·)) (H.filter (A ⊂ ·)) id
    (fun C hC => ⟨(mem_filter.1 hC).1, (mem_filter.1 hC).2.subset ha, (mem_filter.1 hC).2⟩)
  exact ⟨this.1, this.2.2⟩

/-- The parent of a cluster other than `univ` is a cluster. -/
theorem parentCluster_mem (hH : IsHierarchy H) {A : Finset X} (hA : A ∈ H) (hAu : A ≠ univ) :
    parentCluster H A ∈ H :=
  (hier_parentCluster_aux hH hA hAu).1

/-- A cluster other than `univ` is strictly contained in its parent. -/
theorem ssubset_parentCluster (hH : IsHierarchy H) {A : Finset X} (hA : A ∈ H)
    (hAu : A ≠ univ) : A ⊂ parentCluster H A :=
  (hier_parentCluster_aux hH hA hAu).2

/-- A cluster other than `univ` is a child of its parent. -/
theorem mem_childClusters_parentCluster (hH : IsHierarchy H) {A : Finset X} (hA : A ∈ H)
    (hAu : A ≠ univ) : A ∈ childClusters H (parentCluster H A) :=
  mem_childClusters.2 ⟨hA, hH.ssubset_parentCluster hA hAu,
    fun _ hC hAC hCP => not_subset_of_ssubset hCP (parentCluster_subset hC hAC)⟩

/-- The parent of a child of a cluster `P` is `P`. -/
theorem parentCluster_eq_of_mem_childClusters (hH : IsHierarchy H) {A P : Finset X}
    (hP : P ∈ H) (h : A ∈ childClusters H P) : parentCluster H A = P := by
  obtain ⟨hA, hAP, hmax⟩ := mem_childClusters.1 h
  have hAu : A ≠ univ := fun e => not_subset_of_ssubset hAP (e ▸ subset_univ P)
  have hPm := hH.parentCluster_mem hA hAu
  have hAPm := hH.ssubset_parentCluster hA hAu
  obtain ⟨a, ha⟩ := hH.2.2.1 A hA
  apply Subset.antisymm (parentCluster_subset hP hAP)
  rcases hH.subset_or_subset_of_mem hP hPm (hAP.subset ha) (hAPm.subset ha) with h1 | h1
  · exact h1
  · by_contra h2
    exact hmax _ hPm hAPm (ssubset_of_subset_not_subset h1 h2)

/-- Every cluster other than `univ` has a unique parent. -/
theorem existsUnique_parent (hH : IsHierarchy H) {A : Finset X} (hA : A ∈ H) (hAu : A ≠ univ) :
    ∃! P, P ∈ H ∧ A ∈ childClusters H P :=
  ⟨parentCluster H A, ⟨hH.parentCluster_mem hA hAu, hH.mem_childClusters_parentCluster hA hAu⟩,
    fun _ ⟨hP, h⟩ => (hH.parentCluster_eq_of_mem_childClusters hP h).symm⟩

end IsHierarchy

end Phylogenetics
