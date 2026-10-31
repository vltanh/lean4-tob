/-
Adapted from https://github.com/vltanh/lean4-phylogenetics,
commit 06f684e526e276ca2ccf668a1c3a808a2b8c181d.
Licensed under the Apache License, Version 2.0:
https://www.apache.org/licenses/LICENSE-2.0
Exact source regions and adaptations: docs/COALESCENT_SOURCES.md.
-/
module

public import Basic.Phylogenetics.Coalescent.BinaryForest

/-!
# Relabelling lineages

Kingman's coalescent is natural with respect to bijections of the lineages.

* `relabelFamily e F`: the image of a family of clusters under a bijection `e : L ≃ M`;
  `relabelFamilyEquiv e`: the same map, as an equivalence.

## Main results

* `kingmanGenerator_relabelFamily`, `kingmanTransition_relabelFamily`,
  `kingmanAbsorption_relabelFamily`: Kingman's coalescent is invariant under relabelling the
  lineages.
* `forestBelow_relabelFamily`, `isGoodForest_relabelFamily`, `lineages_relabelFamily`: the operations
  of the network multispecies coalescent are too.
-/

@[expose] public section

namespace Phylogenetics

open Finset

variable {L : Type*} [DecidableEq L] {M : Type*} [DecidableEq M]

/-- The image of a family of clusters under a bijection. -/
def relabelFamily (e : L ≃ M) (F : Finset (Finset L)) : Finset (Finset M) :=
  F.image fun A => A.map e.toEmbedding

omit [DecidableEq L] [DecidableEq M] in
private lemma rel_map_symm_map (e : L ≃ M) (A : Finset L) :
    (A.map e.toEmbedding).map e.symm.toEmbedding = A := by
  ext x
  simp

omit [DecidableEq L] [DecidableEq M] in
private lemma rel_map_map_symm (e : L ≃ M) (B : Finset M) :
    (B.map e.symm.toEmbedding).map e.toEmbedding = B := by
  ext x
  simp

omit [DecidableEq L] in
theorem relabelFamily_injective (e : L ≃ M) : Function.Injective (relabelFamily e) :=
  Finset.image_injective (Finset.map_injective e.toEmbedding)

theorem relabelFamily_symm (e : L ≃ M) (F : Finset (Finset L)) :
    relabelFamily e.symm (relabelFamily e F) = F := by
  unfold relabelFamily
  rw [image_image]
  conv_rhs => rw [← image_id (s := F)]
  congr 1
  funext A
  exact rel_map_symm_map e A

/-- Relabelling families of clusters along `e`, as an equivalence. -/
def relabelFamilyEquiv (e : L ≃ M) : Finset (Finset L) ≃ Finset (Finset M) where
  toFun := relabelFamily e
  invFun := relabelFamily e.symm
  left_inv := relabelFamily_symm e
  right_inv := fun F => by simpa using relabelFamily_symm e.symm F

@[simp] theorem relabelFamilyEquiv_apply (e : L ≃ M) (F : Finset (Finset L)) :
    relabelFamilyEquiv e F = relabelFamily e F := rfl

omit [DecidableEq L] in
theorem mem_relabelFamily {e : L ≃ M} {F : Finset (Finset L)} {B : Finset M} :
    B ∈ relabelFamily e F ↔ B.map e.symm.toEmbedding ∈ F := by
  unfold relabelFamily
  rw [mem_image]
  constructor
  · rintro ⟨A, hA, rfl⟩
    rwa [rel_map_symm_map]
  · intro h
    exact ⟨_, h, rel_map_map_symm e B⟩

omit [DecidableEq L] in
theorem map_mem_relabelFamily {e : L ≃ M} {F : Finset (Finset L)} {A : Finset L} :
    A.map e.toEmbedding ∈ relabelFamily e F ↔ A ∈ F := by
  rw [mem_relabelFamily, rel_map_symm_map]

theorem relabelFamily_union (e : L ≃ M) (F G : Finset (Finset L)) :
    relabelFamily e (F ∪ G) = relabelFamily e F ∪ relabelFamily e G :=
  image_union _ _

omit [DecidableEq L] in
@[simp] theorem relabelFamily_empty (e : L ≃ M) : relabelFamily e ∅ = ∅ := image_empty _

theorem relabelFamily_biUnion {ι : Type*} [DecidableEq ι] (e : L ≃ M) (s : Finset ι)
    (f : ι → Finset (Finset L)) :
    relabelFamily e (s.biUnion f) = s.biUnion fun i => relabelFamily e (f i) := by
  unfold relabelFamily
  rw [biUnion_image]

omit [DecidableEq M] in
theorem relabelFamily_refl (F : Finset (Finset L)) : relabelFamily (Equiv.refl L) F = F := by
  unfold relabelFamily
  conv_rhs => rw [← image_id (s := F)]
  congr 1
  funext A
  ext x
  simp

omit [DecidableEq L] [DecidableEq M] in
theorem card_relabelFamily [DecidableEq M] (e : L ≃ M) (F : Finset (Finset L)) :
    #(relabelFamily e F) = #F :=
  card_image_of_injective _ (Finset.map_injective e.toEmbedding)

theorem roots_relabelFamily [Fintype L] [Fintype M] (e : L ≃ M) (F : Finset (Finset L)) :
    roots (relabelFamily e F) = relabelFamily e (roots F) := by
  unfold roots relabelFamily
  rw [filter_image]
  congr 1
  refine filter_congr fun A _ => ?_
  rw [Finset.forall_mem_image]
  constructor
  · intro h B hB hAB
    exact Finset.map_injective _ (h hB (Finset.map_subset_map.2 hAB))
  · intro h B hB hAB
    rw [h B hB (Finset.map_subset_map.1 hAB)]

section Kernels

variable [Fintype L] [Fintype M]

/-- The generator of Kingman's coalescent is invariant under relabelling the lineages. -/
theorem kingmanGenerator_relabelFamily (e : L ≃ M) (F G : Finset (Finset L)) :
    kingmanGenerator (relabelFamily e F) (relabelFamily e G) = kingmanGenerator F G := by
  unfold kingmanGenerator
  rw [roots_relabelFamily, card_relabelFamily]
  by_cases hGF : G = F
  · subst hGF
    simp
  · have hne : relabelFamily e G ≠ relabelFamily e F := fun h => hGF (relabelFamily_injective e h)
    rw [ite_eq_right hne, ite_eq_right hGF]
    refine if_congr ?_ rfl rfl
    constructor
    · rintro ⟨A', hA', B', hB', hAB', hF⟩
      obtain ⟨A, hA, rfl⟩ := mem_image.1 hA'
      obtain ⟨B, hB, rfl⟩ := mem_image.1 hB'
      refine ⟨A, hA, B, hB, fun h => hAB' (h ▸ rfl), relabelFamily_injective e ?_⟩
      rw [hF]
      unfold relabelFamily
      rw [image_insert, Finset.map_union]
    · rintro ⟨A, hA, B, hB, hAB, rfl⟩
      refine ⟨A.map e.toEmbedding, mem_image_of_mem _ hA, B.map e.toEmbedding,
        mem_image_of_mem _ hB, fun h => hAB (Finset.map_injective _ h), ?_⟩
      unfold relabelFamily
      rw [image_insert, Finset.map_union]

/-- The matrix exponential commutes with reindexing along an equivalence. -/
private lemma rel_exp_submatrix {m n : Type*} [Fintype m] [DecidableEq m] [Fintype n]
    [DecidableEq n] (π : n ≃ m) (A : Matrix m m ℝ) :
    NormedSpace.exp (A.submatrix π π) = (NormedSpace.exp A).submatrix π π := by
  have hpow : ∀ k : ℕ, (A.submatrix π π) ^ k = (A ^ k).submatrix π π := by
    intro k
    induction k with
    | zero => simp [Matrix.submatrix_one_equiv]
    | succ k ih => rw [pow_succ, ih, Matrix.submatrix_mul_equiv, pow_succ]
  let g := Matrix.reindexLinearEquiv ℝ ℝ π.symm π.symm
  have hg : ∀ M : Matrix m m ℝ, g M = M.submatrix π π := fun M => rfl
  have hgc : Continuous g := by
    show Continuous fun M : Matrix m m ℝ => M.submatrix π π
    exact continuous_id.matrix_submatrix π π
  have hg'c : Continuous fun M : Matrix n n ℝ => M.submatrix π.symm π.symm :=
    continuous_id.matrix_submatrix π.symm π.symm
  have hinv : Function.LeftInverse (fun M : Matrix n n ℝ => M.submatrix π.symm π.symm) g := by
    intro M
    show (M.submatrix π π).submatrix π.symm π.symm = M
    rw [Matrix.submatrix_submatrix, π.self_comp_symm, Matrix.submatrix_id_id]
  have key := Function.LeftInverse.map_tsum (L := SummationFilter.unconditional ℕ)
    (fun k : ℕ => ((k.factorial : ℝ)⁻¹) • A ^ k) hgc hg'c hinv
  simp only [hg] at key
  rw [NormedSpace.exp_eq_tsum ℝ, NormedSpace.exp_eq_tsum ℝ]
  dsimp only
  rw [key]
  congr 1
  funext k
  rw [Matrix.submatrix_smul, hpow]
  rfl

/-- Kingman's coalescent is invariant under relabelling the lineages. -/
theorem kingmanTransition_relabelFamily (e : L ≃ M) (t : ℝ) (F G : Finset (Finset L)) :
    kingmanTransition t (relabelFamily e F) (relabelFamily e G) = kingmanTransition t F G := by
  have hQ : (kingmanGenerator (L := M)).submatrix (relabelFamilyEquiv e) (relabelFamilyEquiv e) =
      kingmanGenerator (L := L) := by
    ext F G
    exact kingmanGenerator_relabelFamily e F G
  have hs : t • (kingmanGenerator (L := M)).submatrix (relabelFamilyEquiv e)
      (relabelFamilyEquiv e) = (t • kingmanGenerator (L := M)).submatrix (relabelFamilyEquiv e)
      (relabelFamilyEquiv e) := by
    ext F G
    rfl
  unfold kingmanTransition
  rw [← hQ, hs, rel_exp_submatrix]
  rfl

theorem kingmanAbsorption_relabelFamily (e : L ≃ M) (F G : Finset (Finset L)) :
    kingmanAbsorption (relabelFamily e F) (relabelFamily e G) = kingmanAbsorption F G := by
  unfold kingmanAbsorption
  simp_rw [kingmanTransition_relabelFamily]

end Kernels

/-! ### The operations of the network multispecies coalescent -/

theorem forestBelow_relabelFamily (e : L ≃ M) (F A : Finset (Finset L)) :
    forestBelow (relabelFamily e F) (relabelFamily e A) = relabelFamily e (forestBelow F A) := by
  ext D
  rw [mem_forestBelow, mem_relabelFamily, mem_relabelFamily, mem_forestBelow]
  constructor
  · rintro ⟨hD, C, hC, hDC⟩
    exact ⟨hD, C.map e.symm.toEmbedding, mem_relabelFamily.1 hC, map_subset_map.2 hDC⟩
  · rintro ⟨hD, C, hC, hDC⟩
    refine ⟨hD, C.map e.toEmbedding, map_mem_relabelFamily.2 hC, ?_⟩
    have := map_subset_map (f := e.toEmbedding).2 hDC
    rwa [rel_map_map_symm] at this

omit [DecidableEq L] in
theorem lineages_relabelFamily [DecidableEq L] (e : L ≃ M) (F : Finset (Finset L)) :
    lineages (relabelFamily e F) = (lineages F).map e.toEmbedding := by
  ext l
  rw [mem_map_equiv, mem_lineages, mem_lineages]
  constructor
  · rintro ⟨B, hB, hl⟩
    obtain ⟨A, hA, rfl⟩ := mem_image.1 hB
    exact ⟨A, hA, mem_map_equiv.1 hl⟩
  · rintro ⟨A, hA, hl⟩
    exact ⟨A.map e.toEmbedding, mem_image_of_mem _ hA, mem_map_equiv.2 hl⟩

theorem isGoodForest_relabelFamily (e : L ≃ M) {F : Finset (Finset L)} (hF : IsGoodForest F) :
    IsGoodForest (relabelFamily e F) := by
  unfold relabelFamily
  refine ⟨⟨fun A hA => ?_, fun A hA B hB => ?_⟩, fun A hA h2 => ?_⟩
  · obtain ⟨A, hA', rfl⟩ := mem_image.1 hA
    exact map_nonempty.2 (hF.1.1 A hA')
  · obtain ⟨A, hA', rfl⟩ := mem_image.1 hA
    obtain ⟨B, hB', rfl⟩ := mem_image.1 hB
    rcases hF.1.2 A hA' B hB' with h | h | h
    · exact Or.inl (map_subset_map.2 h)
    · exact Or.inr (Or.inl (map_subset_map.2 h))
    · exact Or.inr (Or.inr ((disjoint_map _).2 h))
  · obtain ⟨A, hA', rfl⟩ := mem_image.1 hA
    rw [card_map] at h2
    obtain ⟨B, hB, C, hC, hBC, rfl⟩ := hF.2 A hA' h2
    exact ⟨B.map e.toEmbedding, mem_image_of_mem _ hB, C.map e.toEmbedding,
      mem_image_of_mem _ hC, (disjoint_map _).2 hBC, (map_union _ _).symm⟩

end Phylogenetics
