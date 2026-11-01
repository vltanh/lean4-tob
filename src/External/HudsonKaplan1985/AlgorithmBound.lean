module

public import External.HudsonKaplan1985.Algorithm
public import External.HudsonKaplan1985.Bound

/-!
# `R_M` of a sample is a lower bound on `R¹`

See the `README.md` of this directory. The function of `External.HudsonKaplan1985.Algorithm`, on the matrix `D` of the four-gamete test of a sample, and the bound `card_le_R`: "to each interval we must assign at least one recombination event".
-/

@[expose] public section

namespace HudsonKaplan1985

open Gusfield2007

variable {S : ℕ}

/-- **`R_M` of a sample of sequences** (`ext:hk_rm`). It's computable: `decide` evaluates it. -/
def rM (M : Finset (Fin S → Bool)) : ℕ := hudsonKaplan S (fourGamete M)

/-- The final list of a sample, as pairs of sites. -/
theorem fourGamete_eq_true_iff {M : Finset (Fin S → Bool)} (a b : Fin S) : fourGamete M a.val b.val = true ↔ Incompatible M a b := by
  unfold fourGamete
  rw [dite_eq_left ⟨a.2, b.2⟩, decide_eq_true_eq]
  rfl

/-- The pairs of the final list of a sample are pairs of sites that are incompatible, and they are disjoint. -/
theorem exists_finset_of_finalList (M : Finset (Fin S → Bool)) :
    ∃ P : Finset (Fin S × Fin S), P.card = rM M ∧ (∀ p ∈ P, p.1 < p.2 ∧ Incompatible M p.1 p.2) ∧
      ∀ p ∈ P, ∀ q ∈ P, p ≠ q → p.2 ≤ q.1 ∨ q.2 ≤ p.1 := by
  classical
  set F := finalList S (fourGamete M) with hF
  have hmem : ∀ p ∈ F, p.1 < p.2 ∧ p.2 < S ∧ fourGamete M p.1 p.2 = true := fun p hp => mem_intervalList.1 (finalList_subset p hp)
  have hinj : Function.Injective fun p : Fin S × Fin S => (p.1.val, p.2.val) := fun p q h => by
    simp only [Prod.mk.injEq] at h
    exact Prod.ext (Fin.ext h.1) (Fin.ext h.2)
  refine ⟨Finset.univ.filter fun p => (p.1.val, p.2.val) ∈ F, ?_, ?_, ?_⟩
  · have himage : (Finset.univ.filter fun p : Fin S × Fin S => (p.1.val, p.2.val) ∈ F).image (fun p => (p.1.val, p.2.val)) = F.toFinset := by
      ext q
      simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and, List.mem_toFinset]
      constructor
      · rintro ⟨p, hp, rfl⟩
        exact hp
      · intro hq
        have h := hmem q hq
        exact ⟨(⟨q.1, h.1.trans h.2.1⟩, ⟨q.2, h.2.1⟩), hq, rfl⟩
    rw [← Finset.card_image_of_injective _ hinj, himage, List.toFinset_card_of_nodup (finalList_nodup _ _)]
    rfl
  · intro p hp
    have h := hmem _ (Finset.mem_filter.1 hp).2
    exact ⟨h.1, (fourGamete_eq_true_iff p.1 p.2).1 h.2.2⟩
  · intro p hp q hq hne
    have h := finalList_disjoint _ (Finset.mem_filter.1 hp).2 _ (Finset.mem_filter.1 hq).2 (fun h => hne (hinj h).symm)
    exact h

/-- **`R_M` is a lower bound on `R¹`** (`ext:hk_rm_le`). "At this point all of the intervals are disjoint, and to each interval we must assign at least one recombination event." -/
theorem rM_le_R (M : Finset (Fin S → Bool)) : rM M ≤ R .single M := by
  obtain ⟨P, hcard, h₁, h₂⟩ := exists_finset_of_finalList M
  rw [← hcard]
  exact card_le_R M P h₁ h₂

end HudsonKaplan1985
