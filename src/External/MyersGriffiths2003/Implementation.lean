module

public import External.MyersGriffiths2003.Composite

/-!
# The implementation of the bounds of Myers and Griffiths

Myers and Griffiths 2003, p. 382, "Implementation of the bounds": what a site adds to the number of types, and so which sites can be left out of the subsets for the haplotype bound.
-/

@[expose] public section

open scoped Classical

namespace MyersGriffiths2003

open Gusfield2007

variable {S : ℕ}

/-- Forgetting a site of `T` from the type of a row at `T`. -/
theorem typeCount_eq_image (M : Finset (Fin S → Bool)) (T : Finset (Fin S)) (s : Fin S) :
    typeCount M (T.erase s) = ((M.image fun r a => decide (a ∈ T) && r a).image fun y a => decide (a ∈ T.erase s) && y a).card := by
  unfold typeCount
  rw [Finset.image_image]
  congr 2
  funext r a
  change (decide (a ∈ T.erase s) && r a) = (decide (a ∈ T.erase s) && (decide (a ∈ T) && r a))
  by_cases h : a ∈ T.erase s
  · have hT := Finset.mem_of_mem_erase h
    simp only [decide_eq_true h, decide_eq_true hT, Bool.true_and]
  · simp only [decide_eq_false h, Bool.false_and]

/-- **Lemma 4, (7)** (`ext:mg_lemma4_7`). `H_{S'} ≤ H_S`: removing a site doesn't add types. "Adding the mutation at `s` ... results in a refinement of these equivalence classes." -/
theorem typeCount_erase_le (M : Finset (Fin S → Bool)) (T : Finset (Fin S)) (s : Fin S) : typeCount M (T.erase s) ≤ typeCount M T := by
  rw [typeCount_eq_image]
  exact Finset.card_image_le

/-- **Lemma 4, (8)** (`ext:mg_lemma4_8`). `H_{S'} ≥ H_S - 1` when the site `s` is compatible with the other sites in the region. By the source's argument: if two classes of the rows without `s` are split by `s`, they differ at a site `t`, and `s`, `t` have all four gametes. -/
theorem typeCount_le_erase_add_one (M : Finset (Fin S → Bool)) (T : Finset (Fin S)) (s : Fin S) (hs : ∀ t ∈ T, t ≠ s → ¬ Incompatible M s t) :
    typeCount M T ≤ typeCount M (T.erase s) + 1 := by
  by_cases hsT : s ∈ T
  swap
  · rw [Finset.erase_eq_of_notMem hsT]
    omega
  set types := M.image (fun r a => decide (a ∈ T) && r a) with htypes
  set π : (Fin S → Bool) → Fin S → Bool := fun y a => decide (a ∈ T.erase s) && y a with hπ
  set A₀ := types.filter fun y => y s = false with hA₀
  set A₁ := types.filter fun y => y s = true with hA₁
  have hmasked : ∀ y ∈ types, ∀ a, a ∉ T → y a = false := by
    intro y hy a ha
    obtain ⟨r, -, rfl⟩ := Finset.mem_image.1 hy
    simp [ha]
  -- `π` is injective on each class.
  have hinj : ∀ b : Bool, Set.InjOn π (types.filter fun y => y s = b : Finset (Fin S → Bool)) := by
    intro b y hy y' hy' hπy
    obtain ⟨hy₁, hy₂⟩ := Finset.mem_filter.1 (Finset.mem_coe.1 hy)
    obtain ⟨hy'₁, hy'₂⟩ := Finset.mem_filter.1 (Finset.mem_coe.1 hy')
    funext a
    by_cases ha : a = s
    · rw [ha, hy₂, hy'₂]
    by_cases haT : a ∈ T
    · have := congrFun hπy a
      simpa [hπ, ha, haT] using this
    · rw [hmasked y hy₁ a haT, hmasked y' hy'₁ a haT]
  have hsplit : types.card = A₀.card + A₁.card := by
    rw [← Finset.card_union_of_disjoint]
    · congr 1
      ext y
      simp only [hA₀, hA₁, Finset.mem_union, Finset.mem_filter]
      cases y s <;> simp
    · refine Finset.disjoint_left.2 fun y h₁ h₂ => ?_
      have h₃ := (Finset.mem_filter.1 h₁).2
      have h₄ := (Finset.mem_filter.1 h₂).2
      rw [h₃] at h₄
      exact Bool.false_ne_true h₄
  have hunion : A₀.image π ∪ A₁.image π = types.image π := by
    rw [← Finset.image_union]
    congr 1
    ext y
    simp only [hA₀, hA₁, Finset.mem_union, Finset.mem_filter]
    cases y s <;> simp
  -- At most one class is split.
  have hinter : (A₀.image π ∩ A₁.image π).card ≤ 1 := by
    refine Finset.card_le_one.2 fun y₀ hy₀ y₁ hy₁ => ?_
    by_contra hne
    obtain ⟨hy₀₀, hy₀₁⟩ := Finset.mem_inter.1 hy₀
    obtain ⟨hy₁₀, hy₁₁⟩ := Finset.mem_inter.1 hy₁
    have hmaskπ : ∀ y a, a ∉ T.erase s → π y a = false := fun y a ha => by
      change (decide (a ∈ T.erase s) && y a) = false
      rw [decide_eq_false ha]
      rfl
    have hmem : ∀ z ∈ Finset.image π types, ∀ a, a ∉ T.erase s → z a = false := by
      intro z hz a ha
      obtain ⟨y, -, rfl⟩ := Finset.mem_image.1 hz
      exact hmaskπ y a ha
    obtain ⟨t, ht⟩ : ∃ t, y₀ t ≠ y₁ t := by
      by_contra hno
      push Not at hno
      exact hne (funext hno)
    have htT : t ∈ T.erase s := by
      by_contra hc
      have hy₀t := hmem y₀ (hunion ▸ Finset.mem_union_left _ hy₀₀) t hc
      have hy₁t := hmem y₁ (hunion ▸ Finset.mem_union_left _ hy₁₀) t hc
      exact ht (hy₀t.trans hy₁t.symm)
    obtain ⟨htne, htT'⟩ := Finset.mem_erase.1 htT
    refine hs t htT' htne fun a b => ?_
    -- The row with state `a` at `s` and state `b` at `t`.
    obtain ⟨z, hz, hzb⟩ : ∃ z ∈ ({y₀, y₁} : Finset (Fin S → Bool)), z t = b := by
      by_cases h : y₀ t = b
      · exact ⟨y₀, by simp, h⟩
      · refine ⟨y₁, by simp, ?_⟩
        revert h ht
        cases y₀ t <;> cases y₁ t <;> cases b <;> simp
    have hzA : z ∈ (types.filter fun y => y s = a).image π := by
      rcases Finset.mem_insert.1 hz with rfl | hz'
      · cases a
        · exact hy₀₀
        · exact hy₀₁
      · rw [Finset.mem_singleton.1 hz']
        cases a
        · exact hy₁₀
        · exact hy₁₁
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 hzA
    obtain ⟨hy₁', hy₂'⟩ := Finset.mem_filter.1 hy
    obtain ⟨r, hr, rfl⟩ := Finset.mem_image.1 hy₁'
    refine ⟨r, hr, ?_, ?_⟩
    · simpa [hsT] using hy₂'
    · change (decide (t ∈ T.erase s) && (decide (t ∈ T) && r t)) = b at hzb
      rw [decide_eq_true htT, decide_eq_true htT'] at hzb
      simpa using hzb
  have hcard₀ : (A₀.image π).card = A₀.card := Finset.card_image_of_injOn (hinj false)
  have hcard₁ : (A₁.image π).card = A₁.card := Finset.card_image_of_injOn (hinj true)
  have hadd := Finset.card_union_add_card_inter (A₀.image π) (A₁.image π)
  have hfinal : typeCount M (T.erase s) = (types.image π).card := typeCount_eq_image M T s
  have htypescard : typeCount M T = types.card := rfl
  rw [hunion] at hadd
  omega

/-- The sites of `C` that are incompatible with another site of `C`. -/
noncomputable def incompatibleSites (M : Finset (Fin S → Bool)) (C : Finset (Fin S)) : Finset (Fin S) :=
  C.filter fun s => ∃ t ∈ C, Incompatible M s t

/-- **Corollary 5, on the number of types** (`ext:mg_cor5_types`). "Consider taking the list `C` and removing the nonincompatible sites one at a time. Then from Lemma 4, each successive removal reduces the number of types by either one or zero." -/
theorem typeCount_le_incompatibleSites (M : Finset (Fin S → Bool)) (C : Finset (Fin S)) :
    typeCount M C + (incompatibleSites M C).card ≤ typeCount M (incompatibleSites M C) + C.card := by
  have hcomp : ∀ s ∈ C \ incompatibleSites M C, ∀ t ∈ C, ¬ Incompatible M s t := by
    intro s hs t ht hinc
    obtain ⟨hs₁, hs₂⟩ := Finset.mem_sdiff.1 hs
    exact hs₂ (Finset.mem_filter.2 ⟨hs₁, t, ht, hinc⟩)
  have key : ∀ D : Finset (Fin S), D ⊆ C \ incompatibleSites M C → typeCount M C ≤ typeCount M (C \ D) + D.card := by
    intro D
    induction D using Finset.induction_on with
    | empty =>
      intro _
      simp
    | insert s D hsD ih =>
      intro hsub
      have ih' := ih ((Finset.subset_insert _ _).trans hsub)
      have hs := hsub (Finset.mem_insert_self s D)
      have herase : C \ insert s D = (C \ D).erase s := by
        ext a
        simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_erase]
        tauto
      have hl := typeCount_le_erase_add_one M (C \ D) s fun t ht _ => hcomp s hs t (Finset.mem_sdiff.1 ht).1
      rw [herase, Finset.card_insert_of_notMem hsD]
      omega
  have hk := key _ subset_rfl
  have hsd : C \ (C \ incompatibleSites M C) = incompatibleSites M C := by
    exact Finset.sdiff_sdiff_eq_self (show incompatibleSites M C ⊆ C from Finset.filter_subset _ _)
  rw [hsd] at hk
  have hc := Finset.card_sdiff_add_card_eq_card (Finset.filter_subset (fun s => ∃ t ∈ C, Incompatible M s t) C)
  have hc' : (C \ incompatibleSites M C).card + (incompatibleSites M C).card = C.card := hc
  omega

/-- **Corollary 5** (`ext:mg_cor5`). `R_{C'} ≥ R_C` for `C'` the sites of `C` that are incompatible with another: "so the set `C'` leads to an improved bound compared to `C`". This is for the bound (4) as an integer, and the same for it truncated at zero, `haplotypeAt`. "Thus we need look only at incompatible sites to obtain the best bound for a region." -/
theorem corollary5 (M : Finset (Fin S → Bool)) (C : Finset (Fin S)) :
    (typeCount M C : ℤ) - C.card - 1 ≤ (typeCount M (incompatibleSites M C) : ℤ) - (incompatibleSites M C).card - 1 ∧
      haplotypeAt M C ≤ haplotypeAt M (incompatibleSites M C) := by
  have h := typeCount_le_incompatibleSites M C
  refine ⟨by omega, ?_⟩
  unfold haplotypeAt
  omega

end MyersGriffiths2003
