module

public import Basic.Phylogenetics.Defs
public import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv

/-!
# ECToBlob §6: combining p-values

Lemma 6.1. The combination methods are defined in `Basic/Phylogenetics/Defs.lean`.

Departure from the paper, in the bound for the Cauchy combination (E8 of the report): `max(D, η, 1/2)` replaces the
paper's `D`. The printed `f⁻¹(((k-1) f(D) + f(η))/k)` has the properties the lemma claims on `0 < η ≤ D < 1`, the only
region `(min P, max P)` reaches when `min P > 0`, and that is where the paper uses it. But the lemma's statement
also covers `D = 0` and `η > D`. The printed bound is not non-decreasing in `k` for `η > D`, and no
bound agreeing with it for `η ≤ D` can have both properties the lemma claims at `D = 0`: it would equal
`η` at `D = η`, and so, being non-decreasing in `D`, would be at most `η` at `D = 0`, where the claim
is `∼ k η`. So the statement, as printed, needs another bound. The bound here is at least the printed one for `η ≤ D`, equal to it for `1/2 ≤ D`, and
non-decreasing in `k`, `η` and `D`, with the claimed asymptotics for every `D < 1`.

Also exported, for the proof of Theorem 8.2: `minP_le_combineP` and `combineP_le_two_mul`, for multisets
in `[0, 1]`.
-/

@[expose] public noncomputable section

open Phylogenetics Filter Topology

namespace ECToBlob

/-! ### Minimum and maximum of a multiset -/

theorem le_minP_iff {a : ℝ} {P : Multiset ℝ} : a ≤ minP P ↔ a ≤ 1 ∧ ∀ p ∈ P, a ≤ p := by
  induction P using Multiset.induction_on with
  | empty => simp [minP]
  | cons x P ih =>
    simp only [minP] at ih ⊢
    rw [Multiset.fold_cons_left, le_min_iff, ih]
    simp only [Multiset.mem_cons, forall_eq_or_imp]
    tauto

theorem maxP_le_iff {a : ℝ} {P : Multiset ℝ} : maxP P ≤ a ↔ 0 ≤ a ∧ ∀ p ∈ P, p ≤ a := by
  induction P using Multiset.induction_on with
  | empty => simp [maxP]
  | cons x P ih =>
    simp only [maxP] at ih ⊢
    rw [Multiset.fold_cons_left, max_le_iff, ih]
    simp only [Multiset.mem_cons, forall_eq_or_imp]
    tauto

theorem minP_le_one (P : Multiset ℝ) : minP P ≤ 1 := (le_minP_iff.1 le_rfl).1

theorem minP_le_of_mem {P : Multiset ℝ} {p : ℝ} (hp : p ∈ P) : minP P ≤ p :=
  (le_minP_iff.1 le_rfl).2 p hp

theorem le_maxP_of_mem {P : Multiset ℝ} {p : ℝ} (hp : p ∈ P) : p ≤ maxP P :=
  (maxP_le_iff.1 le_rfl).2 p hp

theorem maxP_nonneg (P : Multiset ℝ) : 0 ≤ maxP P := (maxP_le_iff.1 le_rfl).1

theorem minP_nonneg {P : Multiset ℝ} (h : ∀ p ∈ P, 0 ≤ p) : 0 ≤ minP P :=
  le_minP_iff.2 ⟨zero_le_one, h⟩

/-- The minimum of a nonempty multiset in `(-∞, 1]` is one of its elements. -/
theorem minP_mem {P : Multiset ℝ} (hP : P ≠ 0) (h : ∀ p ∈ P, p ≤ 1) : minP P ∈ P := by
  induction P using Multiset.induction_on with
  | empty => exact absurd rfl hP
  | cons x P ih =>
    have hx : x ≤ 1 := h x (Multiset.mem_cons_self x P)
    have hrest : ∀ p ∈ P, p ≤ 1 := fun p hp => h p (Multiset.mem_cons_of_mem hp)
    simp only [minP] at ih ⊢
    rw [Multiset.fold_cons_left]
    by_cases hP0 : P = 0
    · subst hP0
      simp [hx]
    · rcases min_choice x (P.fold min 1) with h' | h'
      · rw [h']
        exact Multiset.mem_cons_self x P
      · rw [h']
        exact Multiset.mem_cons_of_mem (ih hP0 hrest)

theorem maxP_lt {P : Multiset ℝ} {a : ℝ} (ha : 0 < a) (h : ∀ p ∈ P, p < a) : maxP P < a := by
  induction P using Multiset.induction_on with
  | empty => simpa [maxP] using ha
  | cons x P ih =>
    simp only [maxP] at ih ⊢
    rw [Multiset.fold_cons_left, max_lt_iff]
    exact ⟨h x (Multiset.mem_cons_self x P), ih fun p hp => h p (Multiset.mem_cons_of_mem hp)⟩

/-! ### The Cauchy transform -/

theorem cauchyTransform_anti {p q : ℝ} (hp : 0 < p) (hpq : p ≤ q) (hq : q < 1) :
    cauchyTransform q ≤ cauchyTransform p := by
  unfold cauchyTransform
  have hpi := Real.pi_pos
  refine Real.strictMonoOn_tan.monotoneOn ⟨?_, ?_⟩ ⟨?_, ?_⟩ ?_ <;> nlinarith

theorem cauchyInverse_cauchyTransform {p : ℝ} (hp : 0 < p) (hq : p < 1) :
    cauchyInverse (cauchyTransform p) = p := by
  unfold cauchyInverse cauchyTransform
  have hpi := Real.pi_pos
  rw [Real.arctan_tan (by nlinarith) (by nlinarith)]
  field_simp
  ring

theorem cauchyInverse_anti {x y : ℝ} (h : x ≤ y) : cauchyInverse y ≤ cauchyInverse x := by
  unfold cauchyInverse
  have := div_le_div_of_nonneg_right (Real.arctan_mono h) Real.pi_pos.le
  linarith

theorem cauchyInverse_pos (y : ℝ) : 0 < cauchyInverse y := by
  unfold cauchyInverse
  have h := Real.arctan_lt_pi_div_two y
  have hpi := Real.pi_pos
  rw [sub_pos, div_lt_iff₀ hpi]
  linarith

theorem cauchyInverse_lt_one (y : ℝ) : cauchyInverse y < 1 := by
  unfold cauchyInverse
  have h := Real.neg_pi_div_two_lt_arctan y
  have hpi := Real.pi_pos
  have : -(1 / 2 : ℝ) < Real.arctan y / Real.pi := by
    rw [lt_div_iff₀ hpi]
    linarith
  linarith

private lemma cauchyP_of_pos {P : Multiset ℝ} (h0 : ∀ p ∈ P, 0 < p) (h1 : ∀ p ∈ P, p < 1) :
    cauchyP P = cauchyInverse ((P.map cauchyTransform).sum / (Multiset.card P : ℝ)) := by
  unfold cauchyP
  rw [ite_eq_right fun h => lt_irrefl _ (h0 0 h), ite_eq_right fun h => lt_irrefl _ (h1 1 h)]

theorem cauchyP_nonneg (P : Multiset ℝ) : 0 ≤ cauchyP P := by
  unfold cauchyP
  split_ifs
  · exact le_rfl
  · exact zero_le_one
  · exact (cauchyInverse_pos _).le

theorem cauchyP_le_one (P : Multiset ℝ) : cauchyP P ≤ 1 := by
  unfold cauchyP
  split_ifs
  · exact zero_le_one
  · exact le_rfl
  · exact (cauchyInverse_lt_one _).le

theorem bonP_le_one (P : Multiset ℝ) : bonP P ≤ 1 := min_le_left _ _

theorem bonP_le_mul (P : Multiset ℝ) : bonP P ≤ (Multiset.card P : ℝ) * minP P := min_le_right _ _

theorem bonP_nonneg {P : Multiset ℝ} (h : ∀ p ∈ P, 0 ≤ p) : 0 ≤ bonP P :=
  le_min zero_le_one (mul_nonneg (Nat.cast_nonneg _) (minP_nonneg h))

theorem minP_le_bonP {P : Multiset ℝ} (hP : P ≠ 0) (h : ∀ p ∈ P, 0 ≤ p) : minP P ≤ bonP P := by
  refine le_min (minP_le_one P) ?_
  have hk : (1 : ℝ) ≤ Multiset.card P := by
    exact_mod_cast Multiset.card_pos.2 hP
  exact le_mul_of_one_le_left (minP_nonneg h) hk

/-- The Cauchy combination is at least the minimum. -/
theorem minP_le_cauchyP {P : Multiset ℝ} (hP : P ≠ 0) (h : ∀ p ∈ P, 0 ≤ p ∧ p ≤ 1) :
    minP P ≤ cauchyP P := by
  by_cases h0 : (0 : ℝ) ∈ P
  · rw [cauchyP, ite_eq_left h0]
    exact minP_le_of_mem h0
  by_cases h1 : (1 : ℝ) ∈ P
  · rw [cauchyP, ite_eq_right h0, ite_eq_left h1]
    exact minP_le_one P
  have hpos : ∀ p ∈ P, 0 < p := fun p hp =>
    lt_of_le_of_ne (h p hp).1 fun e => h0 (e ▸ hp)
  have hlt : ∀ p ∈ P, p < 1 := fun p hp =>
    lt_of_le_of_ne (h p hp).2 fun e => h1 (e ▸ hp)
  have hm := minP_mem hP fun p hp => (hlt p hp).le
  rw [cauchyP_of_pos hpos hlt]
  conv_lhs => rw [← cauchyInverse_cauchyTransform (hpos _ hm) (hlt _ hm)]
  refine cauchyInverse_anti ?_
  have hk : (0 : ℝ) < Multiset.card P := by
    exact_mod_cast Multiset.card_pos.2 hP
  rw [div_le_iff₀ hk, mul_comm]
  have := Multiset.sum_le_card_nsmul (P.map cauchyTransform) (cauchyTransform (minP P)) (by
    intro y hy
    obtain ⟨p, hp, rfl⟩ := Multiset.mem_map.1 hy
    exact cauchyTransform_anti (hpos _ hm) (minP_le_of_mem hp) (hlt p hp))
  simpa using this

/-- The Cauchy combination of two values is at most their maximum. -/
theorem cauchyP_pair_le_max {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    cauchyP {a, b} ≤ max a b := by
  by_cases h0 : (0 : ℝ) ∈ ({a, b} : Multiset ℝ)
  · rw [cauchyP, ite_eq_left h0]
    exact le_max_of_le_left ha
  by_cases h1 : (1 : ℝ) ∈ ({a, b} : Multiset ℝ)
  · rw [cauchyP, ite_eq_right h0, ite_eq_left h1]
    simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton] at h1
    rcases h1 with rfl | rfl
    · exact le_max_left _ _
    · exact le_max_right _ _
  simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton, not_or] at h0 h1
  rw [cauchyP, ite_eq_right (by simpa using h0), ite_eq_right (by simpa using h1)]
  by_cases hmax : 1 < max a b
  · exact (cauchyInverse_lt_one _).le.trans hmax.le
  push Not at hmax
  have ha0 : 0 < a := lt_of_le_of_ne ha h0.1
  have hb0 : 0 < b := lt_of_le_of_ne hb h0.2
  have ha1 : a < 1 := lt_of_le_of_ne ((le_max_left a b).trans hmax) fun e => h1.1 e.symm
  have hb1 : b < 1 := lt_of_le_of_ne ((le_max_right a b).trans hmax) fun e => h1.2 e.symm
  have hm0 : 0 < max a b := lt_max_of_lt_left ha0
  have hm1 : max a b < 1 := max_lt ha1 hb1
  conv_rhs => rw [← cauchyInverse_cauchyTransform hm0 hm1]
  refine cauchyInverse_anti ?_
  have h1' := cauchyTransform_anti ha0 (le_max_left a b) hm1
  have h2' := cauchyTransform_anti hb0 (le_max_right a b) hm1
  simp only [Multiset.insert_eq_cons, Multiset.map_cons, Multiset.map_singleton, Multiset.sum_cons,
    Multiset.sum_singleton, Multiset.card_cons, Multiset.card_singleton]
  push_cast
  linarith

/-! ### The helpers for Theorem 8.2 -/

private lemma pair_facts {P : Multiset ℝ} (hP : P ≠ 0) (h : ∀ p ∈ P, 0 ≤ p ∧ p ≤ 1) :
    (∀ x ∈ ({bonP P, cauchyP P} : Multiset ℝ), 0 ≤ x ∧ x ≤ 1) ∧
      minP P ≤ minP {bonP P, cauchyP P} := by
  constructor
  · intro x hx
    simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact ⟨bonP_nonneg fun p hp => (h p hp).1, bonP_le_one P⟩
    · exact ⟨cauchyP_nonneg P, cauchyP_le_one P⟩
  · refine le_minP_iff.2 ⟨minP_le_one P, fun x hx => ?_⟩
    simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact minP_le_bonP hP fun p hp => (h p hp).1
    · exact minP_le_cauchyP hP h

private lemma pair_ne_zero (a b : ℝ) : ({a, b} : Multiset ℝ) ≠ 0 := by
  simp [Multiset.insert_eq_cons]

/-- Each combination of a nonempty multiset in `[0, 1]` is at least its minimum. -/
theorem minP_le_combineP (m : TestCorrection) {P : Multiset ℝ} (hP : P ≠ 0)
    (h : ∀ p ∈ P, 0 ≤ p ∧ p ≤ 1) : minP P ≤ combineP m P := by
  have hpair := pair_facts hP h
  unfold combineP
  rw [ite_eq_right hP]
  cases m with
  | bon => exact minP_le_bonP hP fun p hp => (h p hp).1
  | cauchy => exact minP_le_cauchyP hP h
  | bbc =>
    exact hpair.2.trans (minP_le_bonP (pair_ne_zero _ _) fun x hx => (hpair.1 x hx).1)
  | cbc =>
    exact hpair.2.trans (minP_le_cauchyP (pair_ne_zero _ _) hpair.1)

/-- For the Bonferroni and BBC corrections, the combination is at most `2 k min(P)`, whatever the
maximum. -/
theorem combineP_le_two_mul {m : TestCorrection} (hm : m = .bon ∨ m = .bbc) {P : Multiset ℝ}
    (hP : P ≠ 0) (h : ∀ p ∈ P, 0 ≤ p) :
    combineP m P ≤ 2 * (Multiset.card P : ℝ) * minP P := by
  have hk : 0 ≤ (Multiset.card P : ℝ) * minP P :=
    mul_nonneg (Nat.cast_nonneg _) (minP_nonneg h)
  have hbon := bonP_le_mul P
  unfold combineP
  rw [ite_eq_right hP]
  rcases hm with rfl | rfl
  · show bonP P ≤ _
    linarith
  · show bbcP P ≤ _
    have h1 : bbcP P ≤ ((Multiset.card ({bonP P, cauchyP P} : Multiset ℝ) : ℕ) : ℝ) *
        minP {bonP P, cauchyP P} := bonP_le_mul _
    have h2 : minP {bonP P, cauchyP P} ≤ bonP P :=
      minP_le_of_mem (by simp [Multiset.insert_eq_cons])
    have h3 : ((Multiset.card ({bonP P, cauchyP P} : Multiset ℝ) : ℕ) : ℝ) = 2 := by
      simp [Multiset.insert_eq_cons]
    rw [h3] at h1
    linarith

/-! ### The bound for the Cauchy combination -/

/-- The bounding function of Lemma 6.1 for the Cauchy combination, `0` for `η ≤ 0`. -/
def cauchyBound (k : ℕ) (η D : ℝ) : ℝ :=
  if η ≤ 0 then 0 else
    cauchyInverse (((((k : ℝ) - 1) * cauchyTransform (max (max D η) (1 / 2))) +
      cauchyTransform η) / k)

theorem cauchyBound_nonneg (k : ℕ) (η D : ℝ) : 0 ≤ cauchyBound k η D := by
  unfold cauchyBound
  split_ifs
  · exact le_rfl
  · exact (cauchyInverse_pos _).le

private lemma one_le_cast {k : ℕ} (hk : 1 ≤ k) : (1 : ℝ) ≤ k := by exact_mod_cast hk

private lemma le_anchor (D η : ℝ) : η ≤ max (max D η) (1 / 2) :=
  (le_max_right D η).trans (le_max_left _ _)

private lemma anchor_pos (D η : ℝ) : 0 < max (max D η) (1 / 2) :=
  lt_max_of_lt_right (by norm_num)

private lemma anchor_lt_one {D η : ℝ} (hD : D < 1) (hη : η < 1) : max (max D η) (1 / 2) < 1 :=
  max_lt (max_lt hD hη) (by norm_num)

private lemma anchor_mono {D D' η η' : ℝ} (hD : D ≤ D') (hη : η ≤ η') :
    max (max D η) (1 / 2 : ℝ) ≤ max (max D' η') (1 / 2) :=
  max_le_max (max_le_max hD hη) le_rfl

/-- The mean inside the bound is non-increasing in `η` and in the anchor. -/
private lemma mean_anti {k : ℕ} (hk : 1 ≤ k) {η η' E E' : ℝ} (hη : 0 < η) (hηη : η ≤ η')
    (hη' : η' < 1) (hE : 0 < E) (hEE : E ≤ E') (hE' : E' < 1) :
    (((k : ℝ) - 1) * cauchyTransform E' + cauchyTransform η') / k ≤
      (((k : ℝ) - 1) * cauchyTransform E + cauchyTransform η) / k := by
  have hk1 := one_le_cast hk
  refine div_le_div_of_nonneg_right ?_ (by linarith)
  have h1 := cauchyTransform_anti hη hηη hη'
  have h2 := cauchyTransform_anti hE hEE hE'
  have h3 := mul_le_mul_of_nonneg_left h2 (show (0 : ℝ) ≤ (k : ℝ) - 1 by linarith)
  linarith

/-- The mean inside the bound is non-increasing in `k`, when `η` is at most the anchor. -/
private lemma mean_anti_k {k k' : ℕ} (hk : 1 ≤ k) (hkk : k ≤ k') {η E : ℝ} (hη : 0 < η)
    (hηE : η ≤ E) (hE : E < 1) :
    (((k' : ℝ) - 1) * cauchyTransform E + cauchyTransform η) / k' ≤
      (((k : ℝ) - 1) * cauchyTransform E + cauchyTransform η) / k := by
  have hk1 := one_le_cast hk
  have hk2 : (k : ℝ) ≤ k' := by exact_mod_cast hkk
  have hk0 : (0 : ℝ) < k := by linarith
  have hk'0 : (0 : ℝ) < k' := by linarith
  have ha := cauchyTransform_anti hη hηE hE
  have e : ∀ l : ℝ, 0 < l → ((l - 1) * cauchyTransform E + cauchyTransform η) / l =
      cauchyTransform E + (cauchyTransform η - cauchyTransform E) / l := by
    intro l hl
    field_simp
    ring
  rw [e _ hk0, e _ hk'0]
  have := div_le_div_of_nonneg_left (sub_nonneg.2 ha) hk0 hk2
  linarith

private lemma cauchyBound_mono_k {k k' : ℕ} (hk : 1 ≤ k) (hkk : k ≤ k') {η D : ℝ} (hη1 : η < 1)
    (hD1 : D < 1) : cauchyBound k η D ≤ cauchyBound k' η D := by
  unfold cauchyBound
  split_ifs with h
  · exact le_rfl
  · exact cauchyInverse_anti
      (mean_anti_k hk hkk (not_le.1 h) (le_anchor D η) (anchor_lt_one hD1 hη1))

private lemma cauchyBound_mono_eta {k : ℕ} (hk : 1 ≤ k) {η η' D : ℝ} (hηη : η ≤ η')
    (hη1 : η' < 1) (hD1 : D < 1) : cauchyBound k η D ≤ cauchyBound k η' D := by
  by_cases h : η ≤ 0
  · rw [cauchyBound, ite_eq_left h]
    exact cauchyBound_nonneg _ _ _
  · have h' : ¬ η' ≤ 0 := fun h' => h (hηη.trans h')
    rw [cauchyBound, cauchyBound, ite_eq_right h, ite_eq_right h']
    exact cauchyInverse_anti (mean_anti hk (not_le.1 h) hηη hη1 (anchor_pos D η)
      (anchor_mono le_rfl hηη) (anchor_lt_one hD1 hη1))

private lemma cauchyBound_mono_D {k : ℕ} (hk : 1 ≤ k) {η D D' : ℝ} (hη1 : η < 1) (hDD : D ≤ D')
    (hD1 : D' < 1) : cauchyBound k η D ≤ cauchyBound k η D' := by
  unfold cauchyBound
  split_ifs with h
  · exact le_rfl
  · exact cauchyInverse_anti (mean_anti hk (not_le.1 h) le_rfl hη1 (anchor_pos D η)
      (anchor_mono hDD le_rfl) (anchor_lt_one hD1 hη1))

/-- (6.1) for the Cauchy combination, the paper's computation: the transform of the minimum, and `k - 1`
values at least the transform of the maximum. -/
theorem cauchyP_le_cauchyBound {P : Multiset ℝ} (hP : P ≠ 0) (h : ∀ p ∈ P, 0 ≤ p ∧ p < 1) :
    cauchyP P ≤ cauchyBound (Multiset.card P) (minP P) (maxP P) := by
  by_cases h0 : (0 : ℝ) ∈ P
  · rw [cauchyP, ite_eq_left h0]
    exact cauchyBound_nonneg _ _ _
  have hpos : ∀ p ∈ P, 0 < p := fun p hp => lt_of_le_of_ne (h p hp).1 fun e => h0 (e ▸ hp)
  have hlt : ∀ p ∈ P, p < 1 := fun p hp => (h p hp).2
  have hm := minP_mem hP fun p hp => (hlt p hp).le
  have hη := hpos _ hm
  have hη1 := hlt _ hm
  have hD1 : maxP P < 1 := maxP_lt one_pos hlt
  rw [cauchyP_of_pos hpos hlt, cauchyBound, ite_eq_right (not_le.2 hη)]
  refine cauchyInverse_anti ?_
  obtain ⟨P', hP'⟩ := Multiset.exists_cons_of_mem hm
  have hsum : (P.map cauchyTransform).sum =
      cauchyTransform (minP P) + (P'.map cauchyTransform).sum := by
    conv_lhs => rw [hP']
    simp
  have hcard : (Multiset.card P : ℝ) = Multiset.card P' + 1 := by
    conv_lhs => rw [hP']
    simp
  have hmem : ∀ p ∈ P', p ∈ P := fun p hp => by
    rw [hP']
    exact Multiset.mem_cons_of_mem hp
  have hE := anchor_lt_one hD1 hη1
  have hrest := Multiset.card_nsmul_le_sum (s := P'.map cauchyTransform)
    (a := cauchyTransform (max (max (maxP P) (minP P)) (1 / 2))) (by
      intro y hy
      obtain ⟨p, hp, rfl⟩ := Multiset.mem_map.1 hy
      refine cauchyTransform_anti (hpos p (hmem p hp)) ?_ hE
      exact (le_maxP_of_mem (hmem p hp)).trans ((le_max_left _ _).trans (le_max_left _ _)))
  rw [Multiset.card_map, nsmul_eq_mul] at hrest
  have hk0 : (0 : ℝ) < Multiset.card P := by
    exact_mod_cast Multiset.card_pos.2 hP
  refine div_le_div_of_nonneg_right ?_ hk0.le
  rw [hsum, hcard, add_sub_cancel_right]
  linarith

/-- The asymptotics of the bound: `f(η) ∼ 1/(π η)` and `f⁻¹(y) ∼ 1/(π y)`. -/
theorem tendsto_cauchyBound_div {k : ℕ} (hk : 1 ≤ k) (D : ℝ) :
    Tendsto (fun η => cauchyBound k η D / (k * η)) (𝓝[>] 0) (𝓝 1) := by
  have hk1 := one_le_cast hk
  have hk0 : (0 : ℝ) < k := by linarith
  have hpi := Real.pi_pos
  set C := ((k : ℝ) - 1) * cauchyTransform (max D (1 / 2)) with hC
  have hη0 : Tendsto (fun η : ℝ => η) (𝓝[>] 0) (𝓝 0) := tendsto_nhdsWithin_of_tendsto_nhds tendsto_id
  have hπη : Tendsto (fun η : ℝ => Real.pi * η) (𝓝[>] 0) (𝓝[≠] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨by simpa using hη0.const_mul Real.pi, ?_⟩
    filter_upwards [self_mem_nhdsWithin] with η hη
    exact mul_ne_zero hpi.ne' (ne_of_gt hη)
  have htan := Real.tendsto_tan_div_nhdsNE_zero.comp hπη
  have hf : Tendsto (fun η => η * cauchyTransform η) (𝓝[>] 0) (𝓝 (1 / Real.pi)) := by
    have h1 := (htan.inv₀ one_ne_zero).const_mul (1 / Real.pi)
    simp only [inv_one, mul_one] at h1
    refine h1.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with η hη
    have hη' : η ≠ 0 := ne_of_gt hη
    have e : Real.pi * (1 / 2 - η) = Real.pi / 2 - Real.pi * η := by ring
    simp only [Function.comp]
    unfold cauchyTransform
    rw [e, Real.tan_pi_div_two_sub, inv_div]
    field_simp
  set y : ℝ → ℝ := fun η => (C + cauchyTransform η) / k with hy_def
  have hy : Tendsto (fun η => η * y η) (𝓝[>] 0) (𝓝 (1 / (k * Real.pi))) := by
    have h1 := ((hη0.mul_const C).add hf).div_const (k : ℝ)
    have e : (0 * C + 1 / Real.pi) / (k : ℝ) = 1 / (k * Real.pi) := by
      field_simp
      ring
    rw [e] at h1
    refine h1.congr fun η => ?_
    simp only [hy_def]
    ring
  have hlim0 : (0 : ℝ) < 1 / (k * Real.pi) := by positivity
  have hyinf : Tendsto y (𝓝[>] 0) atTop := by
    refine (hy.pos_mul_atTop hlim0 tendsto_inv_nhdsGT_zero).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with η hη
    have hη' : η ≠ 0 := ne_of_gt hη
    field_simp
  have harctan : Tendsto (fun x => Real.arctan x / x) (𝓝[≠] 0) (𝓝 1) := by
    have h1 := (Real.hasDerivAt_arctan 0).tendsto_slope
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, add_zero, div_one] at h1
    refine h1.congr fun x => ?_
    rw [slope_def_field]
    simp
  have hinv : Tendsto (fun η => (y η)⁻¹) (𝓝[>] 0) (𝓝[≠] 0) :=
    (tendsto_inv_atTop_nhdsGT_zero.comp hyinf).mono_right (nhdsGT_le_nhdsNE 0)
  have hT : Tendsto (fun η => cauchyInverse (y η) * y η) (𝓝[>] 0) (𝓝 (1 / Real.pi)) := by
    have h1 := (harctan.comp hinv).div_const Real.pi
    refine h1.congr' ?_
    filter_upwards [hyinf.eventually_gt_atTop 0] with η hη
    simp only [Function.comp]
    rw [Real.arctan_inv_of_pos hη]
    unfold cauchyInverse
    have hy' : y η ≠ 0 := hη.ne'
    field_simp
  have hlim : (k : ℝ) * (1 / (k * Real.pi)) ≠ 0 := by positivity
  have hfinal := hT.div (hy.const_mul (k : ℝ)) hlim
  have e : 1 / Real.pi / ((k : ℝ) * (1 / (k * Real.pi))) = 1 := by
    field_simp
  rw [e] at hfinal
  refine hfinal.congr' ?_
  have hsmall : ∀ᶠ η : ℝ in 𝓝[>] 0, η < 1 / 2 := by
    refine mem_nhdsWithin_of_mem_nhds ?_
    exact gt_mem_nhds (by norm_num)
  filter_upwards [self_mem_nhdsWithin, hsmall, hyinf.eventually_gt_atTop 0] with η hη hη2 hypos
  have hη0' : (0 : ℝ) < η := hη
  have hE : max (max D η) (1 / 2 : ℝ) = max D (1 / 2) := by
    rw [max_assoc, max_eq_right hη2.le]
  simp only [Pi.div_apply]
  have hb : cauchyBound k η D = cauchyInverse (y η) := by
    rw [cauchyBound, ite_eq_right (not_le.2 hη0'), hE]
  rw [hb]
  have hyne : y η ≠ 0 := hypos.ne'
  field_simp

/-! ### Lemma 6.1 -/

/-- The constant `c` of Lemma 6.1: `1` for Bon, Cauchy and CBC, `2` for BBC. -/
def boundConstant : TestCorrection → ℝ
  | .bon => 1
  | .cauchy => 1
  | .bbc => 2
  | .cbc => 1

/-- The bounding functions of Lemma 6.1. -/
def lemma6_1Bound : TestCorrection → ℕ → ℝ → ℝ → ℝ
  | .bon, k, η, _ => k * η
  | .cauchy, k, η, D => cauchyBound k η D
  | .bbc, k, η, D => 2 * min (cauchyBound k η D) (k * η)
  | .cbc, k, η, D => max (cauchyBound k η D) (k * η)

private lemma combineP_le_lemma6_1Bound (m : TestCorrection) {P : Multiset ℝ} (hP : P ≠ 0)
    (h : ∀ p ∈ P, 0 ≤ p ∧ p < 1) :
    combineP m P ≤ lemma6_1Bound m (Multiset.card P) (minP P) (maxP P) := by
  have hC := cauchyP_le_cauchyBound hP h
  have hB := bonP_le_mul P
  have h0 : ∀ p ∈ P, 0 ≤ p := fun p hp => (h p hp).1
  unfold combineP
  rw [ite_eq_right hP]
  cases m with
  | bon => exact hB
  | cauchy => exact hC
  | bbc =>
    show bonP _ ≤ 2 * min _ _
    have h1 : bonP {bonP P, cauchyP P} ≤ ((Multiset.card ({bonP P, cauchyP P} : Multiset ℝ) : ℕ) : ℝ) *
        minP {bonP P, cauchyP P} := bonP_le_mul _
    have h2 : ((Multiset.card ({bonP P, cauchyP P} : Multiset ℝ) : ℕ) : ℝ) = 2 := by
      simp [Multiset.insert_eq_cons]
    rw [h2] at h1
    refine h1.trans (mul_le_mul_of_nonneg_left (le_min ?_ ?_) (by norm_num))
    · exact (minP_le_of_mem (by simp [Multiset.insert_eq_cons])).trans hC
    · exact (minP_le_of_mem (by simp [Multiset.insert_eq_cons])).trans hB
  | cbc =>
    show cauchyP _ ≤ max _ _
    refine (cauchyP_pair_le_max (bonP_nonneg h0) (cauchyP_nonneg P)).trans ?_
    rw [max_comm]
    exact max_le_max hC hB

private lemma lemma6_1Bound_equiv (m : TestCorrection) {k : ℕ} (hk : 1 ≤ k) (D : ℝ) :
    Asymptotics.IsEquivalent (𝓝[>] (0 : ℝ)) (fun η => lemma6_1Bound m k η D)
      (fun η => boundConstant m * k * η) := by
  have hk1 := one_le_cast hk
  have hk0 : (k : ℝ) ≠ 0 := by linarith
  have ht := tendsto_cauchyBound_div hk D
  refine Asymptotics.isEquivalent_of_tendsto_one ?_
  cases m with
  | bon =>
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with η hη
    have hη' : η ≠ 0 := ne_of_gt hη
    simp only [Pi.div_apply, lemma6_1Bound, boundConstant, one_mul]
    field_simp
  | cauchy =>
    refine ht.congr' ?_
    filter_upwards with η
    simp [lemma6_1Bound, boundConstant]
  | bbc =>
    have h1 := ht.min (tendsto_const_nhds (x := (1 : ℝ)))
    rw [min_self] at h1
    refine h1.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with η hη
    have hη' : (0 : ℝ) < η := hη
    have hkη : 0 < (k : ℝ) * η := by positivity
    simp only [Pi.div_apply, lemma6_1Bound, boundConstant]
    have e1 : 2 * min (cauchyBound k η D) ((k : ℝ) * η) / (2 * k * η) =
        min (cauchyBound k η D) ((k : ℝ) * η) / ((k : ℝ) * η) := by
      rw [mul_assoc 2 (k : ℝ) η, mul_div_mul_left _ _ (by norm_num : (2 : ℝ) ≠ 0)]
    rw [e1, ← min_div_div_right hkη.le, div_self hkη.ne']
  | cbc =>
    have h1 := ht.max (tendsto_const_nhds (x := (1 : ℝ)))
    rw [max_self] at h1
    refine h1.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with η hη
    have hη' : (0 : ℝ) < η := hη
    have hkη : 0 < (k : ℝ) * η := by positivity
    simp only [Pi.div_apply, lemma6_1Bound, boundConstant, one_mul]
    rw [← max_div_div_right hkη.le, div_self hkη.ne']

/-- **Lemma 6.1**, part 1 (`ecto:lem6_1`, with (6.1), `ecto:eq6_1`). For each correction method there
is a bounding function `B k η D` non-decreasing in `k`, `η` and `D` with
`testCo(P) ≤ B_k(min(P), max(P))` for every multiset `P ⊂ [0, 1)` of size `k ≥ 1`, and
`B_k(η, D) ∼ c k η` as `η → 0` for `D < 1` fixed.

Departure from the paper: the anchor `max(D, η, 1/2)` replaces `D` in the bound for the Cauchy
combination; see the header of this file. -/
theorem lemma6_1_part1 (m : TestCorrection) : ∃ B : ℕ → ℝ → ℝ → ℝ,
    (∀ P : Multiset ℝ, P ≠ 0 → (∀ p ∈ P, 0 ≤ p ∧ p < 1) →
      combineP m P ≤ B (Multiset.card P) (minP P) (maxP P)) ∧
    (∀ k k' η D, 1 ≤ k → k ≤ k' → 0 ≤ η → η < 1 → 0 ≤ D → D < 1 → B k η D ≤ B k' η D) ∧
    (∀ k η η' D, 1 ≤ k → 0 ≤ η → η ≤ η' → η' < 1 → 0 ≤ D → D < 1 → B k η D ≤ B k η' D) ∧
    (∀ k η D D', 1 ≤ k → 0 ≤ η → η < 1 → 0 ≤ D → D ≤ D' → D' < 1 → B k η D ≤ B k η D') ∧
    ∀ k D, 1 ≤ k → 0 ≤ D → D < 1 →
      Asymptotics.IsEquivalent (𝓝[>] (0 : ℝ)) (fun η => B k η D)
        (fun η => boundConstant m * k * η) := by
  refine ⟨lemma6_1Bound m, fun P hP h => combineP_le_lemma6_1Bound m hP h, ?_, ?_, ?_,
    fun k D hk _ _ => lemma6_1Bound_equiv m hk D⟩
  · intro k k' η D hk hkk hη hη1 _ hD1
    have hC := cauchyBound_mono_k hk hkk hη1 hD1
    have hB : (k : ℝ) * η ≤ k' * η :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast hkk) hη
    cases m with
    | bon => exact hB
    | cauchy => exact hC
    | bbc => exact mul_le_mul_of_nonneg_left (min_le_min hC hB) (by norm_num)
    | cbc => exact max_le_max hC hB
  · intro k η η' D hk hη hηη hη1 _ hD1
    have hC := cauchyBound_mono_eta hk hηη hη1 hD1
    have hB : (k : ℝ) * η ≤ k * η' := mul_le_mul_of_nonneg_left hηη (Nat.cast_nonneg _)
    cases m with
    | bon => exact hB
    | cauchy => exact hC
    | bbc => exact mul_le_mul_of_nonneg_left (min_le_min hC hB) (by norm_num)
    | cbc => exact max_le_max hC hB
  · intro k η D D' hk _ hη1 _ hDD hD1
    have hC := cauchyBound_mono_D hk hη1 hDD hD1
    cases m with
    | bon => exact le_rfl
    | cauchy => exact hC
    | bbc => exact mul_le_mul_of_nonneg_left (min_le_min hC le_rfl) (by norm_num)
    | cbc => exact max_le_max hC le_rfl

/-- **Lemma 6.1**, part 2 (`ecto:lem6_1`). Each combination is at least `min(P)`. -/
theorem lemma6_1_part2 (m : TestCorrection) (P : Multiset ℝ) (hP : P ≠ 0)
    (hP01 : ∀ p ∈ P, 0 ≤ p ∧ p < 1) : minP P ≤ combineP m P :=
  minP_le_combineP m hP fun p hp => ⟨(hP01 p hp).1, (hP01 p hp).2.le⟩

end ECToBlob
