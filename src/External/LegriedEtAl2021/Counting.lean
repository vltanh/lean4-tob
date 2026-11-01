module

public import External.LegriedEtAl2021.Model

/-!
# The counting in the proof of Theorem 1 of Legried, Molloy, Warnow and Roch

The tuples of ancestral copies `(w, x, y, z)`, weighted by the table of the positive correlation lemmas, and how they sum.

* `bal_algebra`: the case of a balanced species quartet, equations (3), (4) and the function `h`, and the display of the proof of their
  Theorem 3.
* `cat_algebra`: the case of a caterpillar, equations (9), (10) and the function `g`, and their Appendix A.3.

The function `h(x, y) = x + y - xy - 2 (1 - x) (1 - y) / I` appears here multiplied by the total, as in the proof of Theorem 3:
`(I X⁼) Y + X (I Y⁼) - (I X⁼) (I Y⁼) - I (I - 1) X^≠ [2 (I - 1) Y^≠]`. Their minimum of `h` on `x, y ≥ 1 / I` is the comparison
`X^≠ ≤ X⁼`, `Y^≠ ≤ Y⁼` term by term, in `ℝ≥0∞`, with no subtraction.
-/

@[expose] public noncomputable section

open scoped ENNReal Classical

namespace External.LegriedEtAl2021

variable {I : Type} [Fintype I]

theorem ind_true {P : Prop} (h : P) : ind P = 1 := by simp [ind, h]

theorem ind_false {P : Prop} (h : ¬ P) : ind P = 0 := by simp [ind, h]

theorem ind_congr {P Q : Prop} (h : P ↔ Q) : ind P = ind Q := by rw [propext h]

theorem ind_le_one (P : Prop) : ind P ≤ 1 := by
  unfold ind
  split_ifs <;> simp

/-- One value on the diagonal, and another off it. -/
def tw (a b : ℝ≥0∞) (w x : I) : ℝ≥0∞ := if w = x then a else b

omit [Fintype I] in
theorem tw_self (a b : ℝ≥0∞) (w : I) : tw a b w w = a := by simp [tw]

omit [Fintype I] in
theorem tw_ne (a b : ℝ≥0∞) {w x : I} (h : w ≠ x) : tw a b w x = b := by simp [tw, h]

/-- The number of copies. -/
abbrev Ie (I : Type) [Fintype I] : ℝ≥0∞ := (Fintype.card I : ℝ≥0∞)

/-- The number of copies, less one. -/
abbrev Ne (I : Type) [Fintype I] : ℝ≥0∞ := ((Fintype.card I - 1 : ℕ) : ℝ≥0∞)

theorem Ne_le_Ie : Ne I ≤ Ie I := by
  simp only [Ne, Ie]
  exact_mod_cast Nat.sub_le _ _

theorem Ie_mul_Ie : Ie I * Ie I = Ie I * Ne I + Ie I := by
  by_cases hc : Fintype.card I = 0
  · simp [Ie, hc]
  · have : (Fintype.card I : ℝ≥0∞) = ((Fintype.card I - 1 : ℕ) : ℝ≥0∞) + 1 := by
      have h : Fintype.card I = (Fintype.card I - 1) + 1 := by omega
      conv_lhs => rw [h]
      push_cast
      rfl
    calc Ie I * Ie I = Ie I * (Ne I + 1) := by rw [← this]
      _ = _ := by ring

theorem sum_tw (p q : ℝ≥0∞) (w : I) : ∑ x, tw p q w x = p + Ne I * q := by
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ w), tw_self]
  congr 1
  rw [Finset.sum_congr rfl (g := fun _ => q) fun x hx => tw_ne p q (Finset.ne_of_mem_erase hx).symm]
  simp [Finset.card_erase_of_mem, Finset.card_univ]

theorem sum_sum_tw (p q : ℝ≥0∞) : ∑ w : I, ∑ x, tw p q w x = Ie I * p + Ie I * Ne I * q := by
  simp only [sum_tw, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  ring

theorem sum_ind_ne (c : ℝ≥0∞) (w : I) : ∑ x, ind (w ≠ x) * c = Ne I * c := by
  have h : ∀ x, ind (w ≠ x) * c = tw 0 c w x := by
    intro x
    by_cases hx : w = x
    · subst hx
      simp [ind_false, tw_self]
    · simp [ind_true hx, tw_ne 0 c hx]
  simp only [h, sum_tw, zero_add]

theorem sum_ind_ne' (c : ℝ≥0∞) (w : I) : ∑ x, ind (x ≠ w) * c = Ne I * c := by
  simp only [ne_comm (a := _) (b := w), sum_ind_ne]

/-- All four copies are distinct. -/
def Dist (w x y z : I) : Prop := w ≠ x ∧ w ≠ y ∧ w ≠ z ∧ x ≠ y ∧ x ≠ z ∧ y ≠ z

/-- The tuples of ancestral copies with the species quartet: (3). -/
def GammaAB (P : I → I → I → I → Prop) (w x y z : I) : Prop := (w = x ∨ y = z) ∨ (Dist w x y z ∧ P w x y z)

/-- The tuples of ancestral copies with the quartet `ac|bd`: (4). -/
def GammaAC (P : I → I → I → I → Prop) (w x y z : I) : Prop :=
  (w ≠ x ∧ y ≠ z ∧ (w = y ∨ x = z)) ∨ (Dist w x y z ∧ P w y x z)

/-- **Balanced, the sum of (3).** -/
theorem sum_same_side (u₀ u₁ v₀ v₁ : ℝ≥0∞) :
    ∑ w : I, ∑ x : I, ∑ y : I, ∑ z : I, ind (w = x ∨ y = z) * tw u₀ u₁ w x * tw v₀ v₁ y z =
      (Ie I * u₀) * (Ie I * v₀ + Ie I * Ne I * v₁) + (Ie I * Ne I * u₁) * (Ie I * v₀) := by
  have h : ∀ w x : I, ∑ y : I, ∑ z : I, ind (w = x ∨ y = z) * tw u₀ u₁ w x * tw v₀ v₁ y z =
      tw (u₀ * (Ie I * v₀ + Ie I * Ne I * v₁)) (u₁ * (Ie I * v₀)) w x := by
    intro w x
    by_cases hwx : w = x
    · subst hwx
      have hs : Ie I * v₀ + Ie I * Ne I * v₁ = ∑ y : I, ∑ z : I, tw v₀ v₁ y z := (sum_sum_tw v₀ v₁).symm
      have hr : tw (u₀ * (Ie I * v₀ + Ie I * Ne I * v₁)) (u₁ * (Ie I * v₀)) w w =
          u₀ * (Ie I * v₀ + Ie I * Ne I * v₁) := tw_self _ _ _
      rw [hr, hs, Finset.mul_sum]
      refine Finset.sum_congr rfl fun y _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun z _ => ?_
      rw [ind_true (Or.inl rfl), tw_self u₀ u₁ w, one_mul]
    · have hs : Ie I * v₀ = ∑ y : I, ∑ z : I, tw v₀ 0 y z := by
        rw [sum_sum_tw, mul_zero, add_zero]
      have hr : tw (u₀ * (Ie I * v₀ + Ie I * Ne I * v₁)) (u₁ * (Ie I * v₀)) w x = u₁ * (Ie I * v₀) := tw_ne _ _ hwx
      rw [hr, hs, Finset.mul_sum]
      refine Finset.sum_congr rfl fun y _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun z _ => ?_
      rw [tw_ne u₀ u₁ hwx]
      by_cases hyz : y = z
      · subst hyz
        rw [ind_true (Or.inr rfl), tw_self v₀ v₁ y, tw_self v₀ 0 y, one_mul]
      · rw [ind_false (by simp [hwx, hyz]), tw_ne v₀ 0 hyz]
        simp
  simp only [h, sum_sum_tw]
  ring

/-- The first term of (4), counted. -/
theorem sum_shared_left (c : ℝ≥0∞) :
    ∑ w : I, ∑ x : I, ∑ y : I, ∑ z : I, ind (w ≠ x ∧ y ≠ z ∧ w = y) * c = Ie I * (Ne I * (Ne I * c)) := by
  have h : ∀ w x : I, ∑ y : I, ∑ z : I, ind (w ≠ x ∧ y ≠ z ∧ w = y) * c = ind (w ≠ x) * (Ne I * c) := by
    intro w x
    by_cases hwx : w = x
    · subst hwx
      simp [ind_false]
    · rw [ind_true hwx, one_mul, Finset.sum_eq_single w]
      · rw [← sum_ind_ne c w]
        refine Finset.sum_congr rfl fun z _ => ?_
        by_cases hz : w = z
        · rw [ind_false (by simp [hz]), ind_false (by simp [hz])]
        · rw [ind_true ⟨hwx, hz, rfl⟩, ind_true hz]
      · intro y _ hy
        refine Finset.sum_eq_zero fun z _ => ?_
        rw [ind_false fun h => hy h.2.2.symm, zero_mul]
      · simp
  simp only [h, sum_ind_ne, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

/-- The second term of (4), counted. -/
theorem sum_shared_right (c : ℝ≥0∞) :
    ∑ w : I, ∑ x : I, ∑ y : I, ∑ z : I, ind (w ≠ x ∧ y ≠ z ∧ x = z) * c = Ie I * (Ne I * (Ne I * c)) := by
  have h : ∀ w x : I, ∑ y : I, ∑ z : I, ind (w ≠ x ∧ y ≠ z ∧ x = z) * c = ind (w ≠ x) * (Ne I * c) := by
    intro w x
    by_cases hwx : w = x
    · subst hwx
      simp [ind_false]
    · rw [ind_true hwx, one_mul, ← sum_ind_ne' c x]
      refine Finset.sum_congr rfl fun y _ => ?_
      rw [Finset.sum_eq_single x]
      · by_cases hy : y = x
        · rw [ind_false (by simp [hy]), ind_false (by simp [hy])]
        · rw [ind_true ⟨hwx, hy, rfl⟩, ind_true hy]
      · intro z _ hz
        rw [ind_false fun h => hz h.2.2.symm, zero_mul]
      · simp
  simp only [h, sum_ind_ne, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

/-- **By symmetry, the last terms of (3) and (4) agree**: swap `b` and `c`. -/
theorem sum_distinct_swap (P : I → I → I → I → Prop) (c : ℝ≥0∞) :
    ∑ w : I, ∑ x : I, ∑ y : I, ∑ z : I, ind (Dist w x y z ∧ P w y x z) * c = ∑ w : I, ∑ x : I, ∑ y : I, ∑ z : I, ind (Dist w x y z ∧ P w x y z) * c := by
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun z _ => ?_
  have h : (Dist w y x z ∧ P w x y z) ↔ (Dist w x y z ∧ P w x y z) := by
    unfold Dist
    constructor <;> rintro ⟨⟨h₁, h₂, h₃, h₄, h₅, h₆⟩, h₇⟩ <;> exact ⟨⟨h₂, h₁, h₃, h₄.symm, h₆, h₅⟩, h₇⟩
  rw [ind_congr h]

/-- **The comparison of (3) and (4), on a balanced species quartet.** -/
theorem bal_algebra {u₀ u₁ v₀ v₁ : ℝ≥0∞} (hu : u₁ ≤ u₀) (hv : v₁ ≤ v₀) (P : I → I → I → I → Prop) :
    PDom (∑ w : I, ∑ x : I, ∑ y : I, ∑ z : I, ind (GammaAC P w x y z) * tw u₀ u₁ w x * tw v₀ v₁ y z)
      (∑ w : I, ∑ x : I, ∑ y : I, ∑ z : I, ind (GammaAB P w x y z) * tw u₀ u₁ w x * tw v₀ v₁ y z)
      (∑ w : I, ∑ x : I, ∑ y : I, ∑ z : I, ind True * tw u₀ u₁ w x * tw v₀ v₁ y z) := by
  set T : ℝ≥0∞ := ∑ w : I, ∑ x : I, ∑ y : I, ∑ z : I, ind (Dist w x y z ∧ P w x y z) * (u₁ * v₁) with hTdef
  have hab : ∀ w x y z : I, ind (GammaAB P w x y z) * tw u₀ u₁ w x * tw v₀ v₁ y z =
      ind (w = x ∨ y = z) * tw u₀ u₁ w x * tw v₀ v₁ y z + ind (Dist w x y z ∧ P w x y z) * (u₁ * v₁) := by
    intro w x y z
    by_cases h : w = x ∨ y = z
    · have hD : ¬ (Dist w x y z ∧ P w x y z) := by
        rintro ⟨⟨h₁, -, -, -, -, h₆⟩, -⟩
        exact h.elim h₁ h₆
      have hG : GammaAB P w x y z := Or.inl h
      rw [ind_true hG, ind_true h, ind_false hD]
      simp
    · push Not at h
      have hG : GammaAB P w x y z ↔ (Dist w x y z ∧ P w x y z) := by
        unfold GammaAB
        constructor
        · rintro (h' | h')
          · exact (h'.elim h.1 h.2).elim
          · exact h'
        · exact Or.inr
      rw [ind_false (by simpa using h : ¬ (w = x ∨ y = z)), tw_ne _ _ h.1, tw_ne _ _ h.2]
      rw [ind_congr hG]
      ring
  have hac : ∀ w x y z : I, ind (GammaAC P w x y z) * tw u₀ u₁ w x * tw v₀ v₁ y z =
      ind (w ≠ x ∧ y ≠ z ∧ (w = y ∨ x = z)) * (u₁ * v₁) + ind (Dist w x y z ∧ P w y x z) * (u₁ * v₁) := by
    intro w x y z
    by_cases h : w = x ∨ y = z
    · have hD : ¬ (Dist w x y z ∧ P w y x z) := by
        rintro ⟨⟨h₁, -, -, -, -, h₆⟩, -⟩
        exact h.elim h₁ h₆
      have hS : ¬ (w ≠ x ∧ y ≠ z ∧ (w = y ∨ x = z)) := by
        rintro ⟨h₁, h₂, -⟩
        exact h.elim h₁ h₂
      have hG : ¬ GammaAC P w x y z := by
        rintro (h' | h')
        · exact hS h'
        · exact hD h'
      rw [ind_false hG, ind_false hD, ind_false hS]
      simp
    · push Not at h
      rw [tw_ne _ _ h.1, tw_ne _ _ h.2, mul_assoc]
      by_cases hS : w ≠ x ∧ y ≠ z ∧ (w = y ∨ x = z)
      · have hD : ¬ (Dist w x y z ∧ P w y x z) := by
          rintro ⟨⟨-, h₂, -, -, h₅, -⟩, -⟩
          exact hS.2.2.elim h₂ h₅
        have hG : GammaAC P w x y z := Or.inl hS
        rw [ind_true hG, ind_true hS, ind_false hD]
        simp
      · have hG : GammaAC P w x y z ↔ (Dist w x y z ∧ P w y x z) := by
          unfold GammaAC
          constructor
          · rintro (h' | h')
            · exact (hS h').elim
            · exact h'
          · exact Or.inr
        rw [ind_false hS, zero_mul, zero_add]
        rw [ind_congr hG]
  have hx : (∑ w : I, ∑ x : I, ∑ y : I, ∑ z : I, ind (GammaAB P w x y z) * tw u₀ u₁ w x * tw v₀ v₁ y z) =
      ((Ie I * u₀) * (Ie I * Ne I * v₁) + (Ie I * Ne I * u₁) * (Ie I * v₀) + T) + (Ie I * u₀) * (Ie I * v₀) := by
    simp only [hab, Finset.sum_add_distrib]
    rw [sum_same_side]
    ring
  have hx' : (∑ w : I, ∑ x : I, ∑ y : I, ∑ z : I, ind (GammaAC P w x y z) * tw u₀ u₁ w x * tw v₀ v₁ y z) =
      (∑ w : I, ∑ x : I, ∑ y : I, ∑ z : I, ind (w ≠ x ∧ y ≠ z ∧ (w = y ∨ x = z)) * (u₁ * v₁)) + T := by
    simp only [hac, Finset.sum_add_distrib]
    rw [sum_distinct_swap]
  have hC : (∑ w : I, ∑ x : I, ∑ y : I, ∑ z : I, ind (w ≠ x ∧ y ≠ z ∧ (w = y ∨ x = z)) * (u₁ * v₁)) ≤
      (Ie I * u₀) * (Ie I * Ne I * v₁) + (Ie I * Ne I * u₁) * (Ie I * v₀) := by
    have hle : ∀ w x y z : I, ind (w ≠ x ∧ y ≠ z ∧ (w = y ∨ x = z)) * (u₁ * v₁) ≤
        ind (w ≠ x ∧ y ≠ z ∧ w = y) * (u₁ * v₁) + ind (w ≠ x ∧ y ≠ z ∧ x = z) * (u₁ * v₁) := by
      intro w x y z
      by_cases h₁ : w ≠ x ∧ y ≠ z ∧ w = y
      · rw [ind_true h₁]
        refine le_trans ?_ le_self_add
        rw [one_mul]
        exact mul_le_of_le_one_left' (ind_le_one _)
      · by_cases h₂ : w ≠ x ∧ y ≠ z ∧ x = z
        · rw [ind_true h₂]
          refine le_trans ?_ le_add_self
          rw [one_mul]
          exact mul_le_of_le_one_left' (ind_le_one _)
        · rw [ind_false (P := w ≠ x ∧ y ≠ z ∧ (w = y ∨ x = z)) (by tauto)]
          simp
    calc _ ≤ ∑ w : I, ∑ x : I, ∑ y : I, ∑ z : I, (ind (w ≠ x ∧ y ≠ z ∧ w = y) * (u₁ * v₁) + ind (w ≠ x ∧ y ≠ z ∧ x = z) * (u₁ * v₁)) :=
          Finset.sum_le_sum fun w _ => Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun y _ =>
            Finset.sum_le_sum fun z _ => hle w x y z
      _ = Ie I * (Ne I * (Ne I * (u₁ * v₁))) + Ie I * (Ne I * (Ne I * (u₁ * v₁))) := by
          simp only [Finset.sum_add_distrib]
          rw [sum_shared_left, sum_shared_right]
      _ ≤ _ := by
          have h₁ : Ie I * (Ne I * (Ne I * (u₁ * v₁))) ≤ (Ie I * u₀) * (Ie I * Ne I * v₁) := by
            calc Ie I * (Ne I * (Ne I * (u₁ * v₁))) ≤ Ie I * (Ie I * (Ne I * (u₀ * v₁))) := by
                  gcongr
                  exact Ne_le_Ie
              _ = _ := by ring
          have h₂ : Ie I * (Ne I * (Ne I * (u₁ * v₁))) ≤ (Ie I * Ne I * u₁) * (Ie I * v₀) := by
            calc Ie I * (Ne I * (Ne I * (u₁ * v₁))) ≤ Ie I * (Ne I * (Ie I * (u₁ * v₀))) := by
                  gcongr
                  exact Ne_le_Ie
              _ = _ := by ring
          exact add_le_add h₁ h₂
  have ht : (∑ w : I, ∑ x : I, ∑ y : I, ∑ z : I, ind True * tw u₀ u₁ w x * tw v₀ v₁ y z) =
      (Ie I * u₀ + Ie I * Ne I * u₁) * (Ie I * v₀ + Ie I * Ne I * v₁) := by
    rw [← sum_sum_tw, ← sum_sum_tw, Finset.sum_mul]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun z _ => ?_
    rw [ind_true trivial, one_mul]
  have hyt : ∀ w x y z : I, ind (GammaAB P w x y z) * tw u₀ u₁ w x * tw v₀ v₁ y z ≤ ind True * tw u₀ u₁ w x * tw v₀ v₁ y z := by
    intro w x y z
    rw [ind_true trivial]
    gcongr
    exact ind_le_one _
  refine PDom.of_gap (hx'.le.trans (add_le_add_left hC T)) hx
    (Finset.sum_le_sum fun w _ => Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun y _ =>
      Finset.sum_le_sum fun z _ => hyt w x y z) fun hpos => ?_
  rw [ht] at hpos
  intro hg
  rcases mul_eq_zero.1 hg with hg | hg <;> rcases mul_eq_zero.1 hg with hg | hg
  · simp [hg] at hpos
  · have : u₁ = 0 := le_antisymm (hu.trans hg.le) zero_le
    simp [hg, this] at hpos
  · simp [hg] at hpos
  · have : v₁ = 0 := le_antisymm (hv.trans hg.le) zero_le
    simp [hg, this] at hpos

/-! ### The caterpillar -/

/-- Three distinct copies. -/
def Dist3 (w x y : I) : Prop := w ≠ x ∧ w ≠ y ∧ x ≠ y

/-- The tuples of ancestral copies with the species quartet: (9). -/
def CatAB (P : I → I → I → Path → Prop) (w x y : I) (d : Path) : Prop := w = x ∨ (Dist3 w x y ∧ P w x y d)

/-- The tuples of ancestral copies with the quartet `ac|bd`: (10). -/
def CatAC (P : I → I → I → Path → Prop) (w x y : I) (d : Path) : Prop := (w ≠ x ∧ y = w) ∨ (Dist3 w x y ∧ P w y x d)

theorem sumMS_ind_true (M : Multiset Path) : sumMS M (fun _ => ind True) = (Multiset.card M : ℝ≥0∞) := by
  rw [sumMS_const_of_forall (c := 1) fun _ _ => ind_true trivial, mul_one]

theorem sumMS_add_fun (M : Multiset Path) (h h' : Path → ℝ≥0∞) :
    sumMS M (fun a => h a + h' a) = sumMS M h + sumMS M h' := by
  unfold sumMS
  induction M using Multiset.induction_on with
  | empty => simp
  | cons a M ih =>
    simp only [Multiset.map_cons, Multiset.sum_cons, ih]
    ring

/-- **The comparison of (9) and (10), on a caterpillar.** -/
theorem cat_algebra {u₀ u₁ c : ℝ≥0∞} (hu : u₁ ≤ u₀) (Ld : Multiset Path) (P : I → I → I → Path → Prop) :
    PDom (∑ w : I, ∑ x : I, ∑ y : I, sumMS Ld (fun d => ind (CatAC P w x y d)) * tw u₀ u₁ w x * c)
      (∑ w : I, ∑ x : I, ∑ y : I, sumMS Ld (fun d => ind (CatAB P w x y d)) * tw u₀ u₁ w x * c)
      (∑ w : I, ∑ x : I, ∑ _y : I, sumMS Ld (fun _ => ind True) * tw u₀ u₁ w x * c) := by
  set D : ℝ≥0∞ := (Multiset.card Ld : ℝ≥0∞) with hD
  set T : ℝ≥0∞ := ∑ w : I, ∑ x : I, ∑ y : I, sumMS Ld (fun d => ind (Dist3 w x y ∧ P w x y d)) * (u₁ * c) with hTdef
  have hab : ∀ w x y : I, sumMS Ld (fun d => ind (CatAB P w x y d)) * tw u₀ u₁ w x * c =
      ind (w = x) * (D * u₀ * c) + sumMS Ld (fun d => ind (Dist3 w x y ∧ P w x y d)) * (u₁ * c) := by
    intro w x y
    by_cases hwx : w = x
    · subst hwx
      have h₁ : sumMS Ld (fun d => ind (CatAB P w w y d)) = D := by
        rw [sumMS_const_of_forall (c := 1) fun d _ => ind_true (show CatAB P w w y d from Or.inl rfl), mul_one]
      have h₂ : sumMS Ld (fun d => ind (Dist3 w w y ∧ P w w y d)) = 0 := by
        rw [sumMS_const_of_forall (c := 0) fun d _ => ind_false fun h => h.1.1 rfl, mul_zero]
      rw [h₁, h₂, tw_self, ind_true rfl]
      simp
    · have h₁ : (fun d => ind (CatAB P w x y d)) = fun d => ind (Dist3 w x y ∧ P w x y d) := by
        funext d
        have : CatAB P w x y d ↔ (Dist3 w x y ∧ P w x y d) := by
          unfold CatAB
          simp [hwx]
        exact ind_congr this
      rw [h₁, tw_ne _ _ hwx, ind_false hwx, zero_mul, zero_add, mul_assoc]
  have hac : ∀ w x y : I, sumMS Ld (fun d => ind (CatAC P w x y d)) * tw u₀ u₁ w x * c =
      ind (w ≠ x ∧ y = w) * (D * u₁ * c) + sumMS Ld (fun d => ind (Dist3 w x y ∧ P w y x d)) * (u₁ * c) := by
    intro w x y
    by_cases hwx : w = x
    · subst hwx
      have h₁ : sumMS Ld (fun d => ind (CatAC P w w y d)) = 0 := by
        rw [sumMS_const_of_forall (c := 0) fun d _ => ind_false ?_, mul_zero]
        rintro (h | h)
        · exact h.1 rfl
        · exact h.1.1 rfl
      have h₂ : sumMS Ld (fun d => ind (Dist3 w w y ∧ P w y w d)) = 0 := by
        rw [sumMS_const_of_forall (c := 0) fun d _ => ind_false fun h => h.1.1 rfl, mul_zero]
      rw [h₁, h₂, ind_false fun h => h.1 rfl]
      simp
    · by_cases hyw : y = w
      · subst hyw
        have h₁ : sumMS Ld (fun d => ind (CatAC P y x y d)) = D := by
          rw [sumMS_const_of_forall (c := 1) fun d _ => ind_true (show CatAC P y x y d from Or.inl ⟨hwx, rfl⟩), mul_one]
        have h₂ : sumMS Ld (fun d => ind (Dist3 y x y ∧ P y y x d)) = 0 := by
          rw [sumMS_const_of_forall (c := 0) fun d _ => ind_false fun h => h.1.2.1 rfl, mul_zero]
        rw [h₁, h₂, tw_ne _ _ hwx, ind_true ⟨hwx, rfl⟩]
        simp [mul_assoc]
      · have h₁ : (fun d => ind (CatAC P w x y d)) = fun d => ind (Dist3 w x y ∧ P w y x d) := by
          funext d
          have : CatAC P w x y d ↔ (Dist3 w x y ∧ P w y x d) := by
            unfold CatAC
            simp [hyw]
          exact ind_congr this
        rw [h₁, tw_ne _ _ hwx, ind_false fun h => hyw h.2, zero_mul, zero_add, mul_assoc]
  have hswap : (∑ w : I, ∑ x : I, ∑ y : I, sumMS Ld (fun d => ind (Dist3 w x y ∧ P w y x d)) * (u₁ * c)) = T := by
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
    have h : (fun d => ind (Dist3 w y x ∧ P w x y d)) = fun d => ind (Dist3 w x y ∧ P w x y d) := by
      funext d
      have : (Dist3 w y x ∧ P w x y d) ↔ (Dist3 w x y ∧ P w x y d) := by
        unfold Dist3
        constructor <;> rintro ⟨⟨h₁, h₂, h₃⟩, h₄⟩ <;> exact ⟨⟨h₂, h₁, h₃.symm⟩, h₄⟩
      exact ind_congr this
    rw [h]
  have hsum₁ : ∀ K : ℝ≥0∞, (∑ w : I, ∑ x : I, ∑ _y : I, ind (w = x) * K) = Ie I * (Ie I * K) := by
    intro K
    have h : ∀ w : I, ∑ x : I, ∑ _y : I, ind (w = x) * K = Ie I * K := by
      intro w
      rw [Finset.sum_eq_single w]
      · simp [ind_true]
      · intro x _ hx
        simp [ind_false (Ne.symm hx)]
      · simp
    rw [Finset.sum_congr rfl fun w _ => h w]
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hsum₂ : ∀ K : ℝ≥0∞, (∑ w : I, ∑ x : I, ∑ y : I, ind (w ≠ x ∧ y = w) * K) = Ie I * (Ne I * K) := by
    intro K
    have h : ∀ w x : I, ∑ y : I, ind (w ≠ x ∧ y = w) * K = ind (w ≠ x) * K := by
      intro w x
      rw [Finset.sum_eq_single w]
      · by_cases hx : w ≠ x
        · rw [ind_true ⟨hx, rfl⟩, ind_true hx]
        · rw [ind_false fun h => hx h.1, ind_false hx]
      · intro y _ hy
        rw [ind_false fun h => hy h.2, zero_mul]
      · simp
    simp only [h, sum_ind_ne, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hx : (∑ w : I, ∑ x : I, ∑ y : I, sumMS Ld (fun d => ind (CatAB P w x y d)) * tw u₀ u₁ w x * c) =
      (Ie I * (Ne I * (D * u₀ * c)) + T) + Ie I * (D * u₀ * c) := by
    simp only [hab, Finset.sum_add_distrib]
    rw [hsum₁]
    have : Ie I * (Ie I * (D * u₀ * c)) = Ie I * (Ne I * (D * u₀ * c)) + Ie I * (D * u₀ * c) := by
      calc Ie I * (Ie I * (D * u₀ * c)) = (Ie I * Ie I) * (D * u₀ * c) := by ring
        _ = (Ie I * Ne I + Ie I) * (D * u₀ * c) := by rw [Ie_mul_Ie]
        _ = _ := by ring
    rw [this]
    ring
  have hx' : (∑ w : I, ∑ x : I, ∑ y : I, sumMS Ld (fun d => ind (CatAC P w x y d)) * tw u₀ u₁ w x * c) =
      Ie I * (Ne I * (D * u₁ * c)) + T := by
    simp only [hac, Finset.sum_add_distrib]
    rw [hsum₂, hswap]
  have ht : (∑ w : I, ∑ x : I, ∑ _y : I, sumMS Ld (fun _ => ind True) * tw u₀ u₁ w x * c) =
      Ie I * (Ie I * u₀ + Ie I * Ne I * u₁) * D * c := by
    rw [← sum_sum_tw, sumMS_ind_true]
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun w _ => Finset.sum_congr rfl fun x _ => ?_
    ring
  have hyt : ∀ w x y : I, sumMS Ld (fun d => ind (CatAB P w x y d)) * tw u₀ u₁ w x * c ≤
      sumMS Ld (fun _ => ind True) * tw u₀ u₁ w x * c := by
    intro w x y
    gcongr
    refine sumMS_mono fun d => ?_
    rw [ind_true trivial]
    exact ind_le_one _
  refine PDom.of_gap (y := Ie I * (Ne I * (D * u₀ * c)) + T) (g := Ie I * (D * u₀ * c)) ?_ hx
    (Finset.sum_le_sum fun w _ => Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun y _ => hyt w x y) fun hpos => ?_
  · rw [hx']
    gcongr
  · rw [ht] at hpos
    intro hg
    rcases mul_eq_zero.1 hg with hg | hg
    · simp [hg] at hpos
    · rcases mul_eq_zero.1 hg with hg | hg
      · rcases mul_eq_zero.1 hg with hg | hg
        · simp [hg] at hpos
        · have : u₁ = 0 := le_antisymm (hu.trans hg.le) zero_le
          simp [hg, this] at hpos
      · simp [hg] at hpos

end External.LegriedEtAl2021
