/-
Adapted from https://github.com/vltanh/lean4-phylogenetics,
commit 06f684e526e276ca2ccf668a1c3a808a2b8c181d.
Licensed under the Apache License, Version 2.0:
https://www.apache.org/licenses/LICENSE-2.0
Exact source regions and adaptations: docs/COALESCENT_SOURCES.md.
-/
module

public import Basic.Phylogenetics.Coalescent.Absorption
public import Mathlib.Probability.ProbabilityMassFunction.Constructions

/-!
# Probability mass functions for finite Kingman coalescence

The actual matrix-exponential rows and root-absorption rows are wrapped as PMFs
using their proved nonnegativity and total mass one. No renormalization changes
these laws. Invalid forest families have probability zero from a valid input;
lineages and all clusters already formed are preserved.
-/

@[expose] public noncomputable section

namespace Phylogenetics

open scoped BigOperators

variable {L : Type*} [Fintype L] [DecidableEq L]

/-- The finite-time Kingman law from a valid forest, with a nonnegative population length. -/
def kingmanTransitionPMF (F : Finset (Finset L)) (hF : IsForest F)
    (t : ℝ) (ht : 0 ≤ t) : PMF (Finset (Finset L)) :=
  PMF.ofFintype (fun G => ENNReal.ofReal (kingmanTransition t F G)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun G _ => kingmanTransition_nonneg ht F G),
      kingmanTransition_sum hF t, ENNReal.ofReal_one])

/-- PMF masses are the original finite-time transition entries, converted to ENNReal. -/
@[simp] theorem kingmanTransitionPMF_apply (F : Finset (Finset L)) (hF : IsForest F)
    (t : ℝ) (ht : 0 ≤ t) (G : Finset (Finset L)) :
    kingmanTransitionPMF F hF t ht G = ENNReal.ofReal (kingmanTransition t F G) := rfl

/-- Conversion back to real values recovers the exact matrix exponential. -/
@[simp] theorem kingmanTransitionPMF_toReal (F : Finset (Finset L)) (hF : IsForest F)
    (t : ℝ) (ht : 0 ≤ t) (G : Finset (Finset L)) :
    (kingmanTransitionPMF F hF t ht G).toReal = kingmanTransition t F G :=
  ENNReal.toReal_ofReal (kingmanTransition_nonneg ht F G)

/-- At zero elapsed time the forest is unchanged. -/
theorem kingmanTransitionPMF_zero (F : Finset (Finset L)) (hF : IsForest F) :
    kingmanTransitionPMF F hF 0 (by simp) = PMF.pure F := by
  apply PMF.ext
  intro G
  rw [kingmanTransitionPMF_apply, kingmanTransition_zero, PMF.pure_apply, Matrix.one_apply]
  by_cases h : G = F
  · simp [h]
  · simp [h, Ne.symm h]

/-- The transition PMF preserves the valid forest, its existing clusters and its lineages. -/
theorem kingmanTransitionPMF_support {F G : Finset (Finset L)} (hF : IsForest F)
    (t : ℝ) (ht : 0 ≤ t) (h : G ∈ (kingmanTransitionPMF F hF t ht).support) :
    IsForest G ∧ F ⊆ G ∧ lineages G = lineages F ∧ (roots G).card ≤ (roots F).card := by
  refine kingmanTransition_support hF (t := t) fun hzero => ?_
  exact (PMF.mem_support_iff _ _).mp h (by simp [hzero])

/-- The infinite-time population above the root, with its proved limiting law. -/
def kingmanAbsorptionPMF (F : Finset (Finset L)) (hF : IsForest F) :
    PMF (Finset (Finset L)) :=
  PMF.ofFintype (fun G => ENNReal.ofReal (kingmanAbsorption F G)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun G _ => kingmanAbsorption_nonneg hF G),
      kingmanAbsorption_sum hF, ENNReal.ofReal_one])

/-- PMF masses are the original root-absorption entries, converted to ENNReal. -/
@[simp] theorem kingmanAbsorptionPMF_apply (F : Finset (Finset L)) (hF : IsForest F)
    (G : Finset (Finset L)) :
    kingmanAbsorptionPMF F hF G = ENNReal.ofReal (kingmanAbsorption F G) := rfl

/-- Conversion back to real values recovers the exact absorption limit. -/
@[simp] theorem kingmanAbsorptionPMF_toReal (F : Finset (Finset L)) (hF : IsForest F)
    (G : Finset (Finset L)) :
    (kingmanAbsorptionPMF F hF G).toReal = kingmanAbsorption F G :=
  ENNReal.toReal_ofReal (kingmanAbsorption_nonneg hF G)

/-- Root absorption preserves forests and lineages and leaves exactly one root from
nonempty input. The proof follows the forest part of the source's
`kingmanAbsorption_support` (`NMSC/Basic.lean`338–355), with its binary-forest
conjunct removed; no network datatype or network theorem is used. -/
theorem kingmanAbsorption_support_forest {F G : Finset (Finset L)} (hF : IsForest F)
    (h : kingmanAbsorption F G ≠ 0) :
    IsForest G ∧ F ⊆ G ∧ lineages G = lineages F ∧ (F.Nonempty → (roots G).card = 1) := by
  rw [kingmanAbsorption_apply hF] at h
  by_cases h0 : (roots F).card = 0
  · rw [ite_eq_left h0] at h
    have hGF : G = F := by
      by_contra hne
      exact h (ite_eq_right hne)
    subst G
    exact ⟨hF, Finset.Subset.refl _, rfl, fun hne =>
      absurd (card_roots_eq_zero_iff.mp h0) hne.ne_empty⟩
  rw [ite_eq_right h0] at h
  by_cases h1 : (roots G).card = 1
  · rw [ite_eq_left h1] at h
    obtain ⟨hforest, hsub, hlin, _⟩ := jumpMatrix_pow_support hF h
    exact ⟨hforest, hsub, hlin, fun _ => h1⟩
  · rw [ite_eq_right h1] at h
    exact absurd rfl h

/-- The root-absorption PMF is supported on valid forests with unchanged lineages;
nonempty input has become a single rooted gene tree. -/
theorem kingmanAbsorptionPMF_support {F G : Finset (Finset L)} (hF : IsForest F)
    (h : G ∈ (kingmanAbsorptionPMF F hF).support) :
    IsForest G ∧ F ⊆ G ∧ lineages G = lineages F ∧ (F.Nonempty → (roots G).card = 1) := by
  apply kingmanAbsorption_support_forest hF
  intro hzero
  exact (PMF.mem_support_iff _ _).mp h (by simp [hzero])

end Phylogenetics
