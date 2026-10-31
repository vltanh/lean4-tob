module

public import Basic.Phylogenetics.Defs
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-!
# The correlated inheritance of lineages at a reticulation

The sequential reading of `allocationWeight` (TOB-QMC supplement §1.2): the lineages choose parents
one after another, the first by `γ` and the lineage after `m ≥ 1` others by the Pólya urn law
`((1 - ρ) γ_e + ρ n_e) / ((1 - ρ) + ρ m)`, where `n_e` lineages have taken the parent `e` so far.

The supplement's first line prints `α = ρ/(1-ρ)` for the concentration parameter, while its later
relation `ρ = 1/(1+α)` and both of its stated endpoints give `α = (1-ρ)/ρ`, which is the relation
used here (`urnStep_eq_concentration`).

## Main results

* `urnWeight`, `allocationWeight_eq_urn`, `allocationWeight_eq_urn_of_equiv`: the closed form of
  `allocationWeight` is the joint law of the urn, in any order of the lineages.
* `allocationWeight_nonneg`, `sum_allocationWeight`: it is a probability distribution.
* `allocationWeight_rho_zero`, `allocationWeight_rho_one`, `allocationWeight_rho_one_const`: the
  endpoints, independent and common inheritance.
* `allocationWeight_const_pos`: an assignment of all lineages to a parent of positive inheritance
  has positive probability.
-/

@[expose] public noncomputable section

namespace Phylogenetics

open Finset

variable {R P : Type*} [Fintype R] [Fintype P] [DecidableEq P] {ρ : ℝ} {γ : P → ℝ}

/-! ### The urn -/

/-- The number of lineages of the history `h` that took the parent `e`. -/
def urnCount {m : ℕ} (h : Fin m → P) (e : P) : ℕ := #{i | h i = e}

/-- The probability that the next lineage takes the parent `e` after the history `h`. The empty
history uses `γ`, so that common inheritance has no `0/0`. -/
def urnStep (ρ : ℝ) (γ : P → ℝ) {m : ℕ} (h : Fin m → P) (e : P) : ℝ :=
  if m = 0 then γ e else ((1 - ρ) * γ e + ρ * urnCount h e) / ((1 - ρ) + ρ * m)

/-- The joint probability of an ordered assignment of `m` lineages under the urn: each step
conditions on the whole assignment so far. -/
def urnWeight (ρ : ℝ) (γ : P → ℝ) : (m : ℕ) → (Fin m → P) → ℝ
  | 0, _ => 1
  | m + 1, g => urnWeight ρ γ m (Fin.init g) * urnStep ρ γ (Fin.init g) (g (Fin.last m))

/-- The denominator of the urn is at least one after the first lineage. -/
theorem urn_denominator_pos (hρ : 0 ≤ ρ) {i : ℕ} (hi : 1 ≤ i) : 0 < (1 - ρ) + ρ * i := by
  have hi' : (1 : ℝ) ≤ i := by exact_mod_cast hi
  nlinarith

omit [Fintype P] in
theorem urnCount_snoc {m : ℕ} (g : Fin (m + 1) → P) (e : P) :
    urnCount g e = urnCount (Fin.init g) e + if g (Fin.last m) = e then 1 else 0 := by
  simp only [urnCount, card_filter, Fin.sum_univ_castSucc]
  rfl

theorem sum_urnCount {m : ℕ} (h : Fin m → P) : ∑ e, urnCount h e = m := by
  simp only [urnCount, card_filter]
  rw [sum_comm]
  simp

theorem sum_urnStep (hρ : 0 ≤ ρ) (hγ : ∑ e, γ e = 1) {m : ℕ} (h : Fin m → P) :
    ∑ e, urnStep ρ γ h e = 1 := by
  unfold urnStep
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simpa using hγ
  · have hm' : m ≠ 0 := hm.ne'
    simp only [hm', ↓reduceIte, ← sum_div, sum_add_distrib, ← mul_sum, hγ, mul_one]
    have hc : ∑ e, (urnCount h e : ℝ) = m := by exact_mod_cast sum_urnCount h
    rw [hc]
    exact div_self (urn_denominator_pos hρ hm).ne'

omit [Fintype P] in
theorem urnStep_nonneg (h0 : 0 ≤ ρ) (h1 : ρ ≤ 1) (hγ : ∀ e, 0 ≤ γ e) {m : ℕ} (h : Fin m → P)
    (e : P) : 0 ≤ urnStep ρ γ h e := by
  unfold urnStep
  split_ifs with hm
  · exact hγ e
  · exact div_nonneg (add_nonneg (mul_nonneg (sub_nonneg.2 h1) (hγ e))
      (mul_nonneg h0 (Nat.cast_nonneg _))) (urn_denominator_pos h0 (Nat.pos_of_ne_zero hm)).le

omit [Fintype P] in
/-- The urn in the concentration parameter `α = (1 - ρ) / ρ`. -/
theorem urnStep_eq_concentration (hρ : 0 < ρ) {m : ℕ} (hm : 0 < m) (h : Fin m → P) (e : P) :
    urnStep ρ γ h e = (((1 - ρ) / ρ) * γ e + urnCount h e) / ((1 - ρ) / ρ + m) := by
  have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hd : (1 - ρ) + ρ * m ≠ 0 := (urn_denominator_pos hρ.le hm).ne'
  have hd' : (1 - ρ) / ρ + m ≠ 0 := by
    have : (1 - ρ) / ρ + m = ((1 - ρ) + ρ * m) / ρ := by field_simp
    rw [this]
    exact div_ne_zero hd hρ.ne'
  simp only [urnStep, hm.ne', ↓reduceIte]
  rw [div_eq_div_iff hd hd']
  field_simp

/-- The concentration parameter is compatible with the supplement's correlation equation. -/
theorem concentration_relation (hρ : ρ ≠ 0) : 1 / (1 + (1 - ρ) / ρ) = ρ := by
  field_simp
  ring

/-! ### The closed form -/

section Snoc

variable {m : ℕ} (g : Fin (m + 1) → P)

omit [Fintype P] in
private theorem image_snoc :
    (univ.image g) = insert (g (Fin.last m)) (univ.image (Fin.init g)) := by
  ext e
  simp only [mem_image, mem_univ, true_and, mem_insert, Fin.exists_fin_succ', Fin.init]
  constructor
  · rintro (⟨i, hi⟩ | hi)
    · exact Or.inr ⟨i, hi⟩
    · exact Or.inl hi.symm
  · rintro (hi | ⟨i, hi⟩)
    · exact Or.inr hi.symm
    · exact Or.inl ⟨i, hi⟩

omit [Fintype P] in
private theorem filter_card_eq_urnCount {m : ℕ} (h : Fin m → P) (e : P) :
    (univ.filter fun r => h r = e).card = urnCount h e := rfl

omit [Fintype P] in
private theorem urnCount_pos_of_mem {m : ℕ} {h : Fin m → P} {e : P} (he : e ∈ univ.image h) :
    1 ≤ urnCount h e := by
  obtain ⟨i, -, rfl⟩ := mem_image.1 he
  exact card_pos.2 ⟨i, mem_filter.2 ⟨mem_univ _, rfl⟩⟩

omit [Fintype P] in
private theorem urnCount_eq_zero_of_notMem {m : ℕ} {h : Fin m → P} {e : P}
    (he : e ∉ univ.image h) : urnCount h e = 0 := by
  refine card_eq_zero.2 (filter_eq_empty_iff.2 fun i _ hi => he ?_)
  exact mem_image.2 ⟨i, mem_univ _, hi⟩

variable (ρ γ) in
/-- The part of the numerator of `allocationWeight` at the parent `e`, after `n` lineages. -/
private def numer (n : ℕ) (e : P) : ℝ :=
  γ e * ∏ j ∈ Ico 1 n, ((1 - ρ) * γ e + ρ * j)

omit [Fintype P] in
/-- One more lineage, added to the closed form: the case of a parent that was taken before. -/
private theorem numer_prod_of_mem (he : g (Fin.last m) ∈ univ.image (Fin.init g)) :
    ∏ e ∈ univ.image g, numer ρ γ (urnCount g e) e =
      (∏ e ∈ univ.image (Fin.init g), numer ρ γ (urnCount (Fin.init g) e) e) *
        ((1 - ρ) * γ (g (Fin.last m)) + ρ * urnCount (Fin.init g) (g (Fin.last m))) := by
  have him : univ.image g = univ.image (Fin.init g) := by
    rw [image_snoc, insert_eq_of_mem he]
  rw [him, ← prod_erase_mul _ _ he, ← prod_erase_mul _ _ he, mul_assoc]
  congr 1
  · refine prod_congr rfl fun e he' => ?_
    rw [urnCount_snoc, ite_eq_right (fun h => (ne_of_mem_erase he') h.symm), add_zero]
  · rw [urnCount_snoc]
    simp only [↓reduceIte, numer]
    rw [prod_Ico_succ_top (urnCount_pos_of_mem he)]
    ring

omit [Fintype P] in
/-- One more lineage, added to the closed form: the case of a new parent. -/
private theorem numer_prod_of_notMem (he : g (Fin.last m) ∉ univ.image (Fin.init g)) :
    ∏ e ∈ univ.image g, numer ρ γ (urnCount g e) e =
      (∏ e ∈ univ.image (Fin.init g), numer ρ γ (urnCount (Fin.init g) e) e) *
        γ (g (Fin.last m)) := by
  rw [image_snoc, prod_insert he, mul_comm]
  congr 1
  · refine prod_congr rfl fun e he' => ?_
    have hne : g (Fin.last m) ≠ e := fun h => he (h ▸ he')
    rw [urnCount_snoc, ite_eq_right hne, add_zero]
  · rw [urnCount_snoc, urnCount_eq_zero_of_notMem he]
    simp [numer]

private theorem allocationWeight_eq_numer {m : ℕ} (h : Fin m → P) :
    allocationWeight ρ γ h = (1 - ρ) ^ ((univ.image h).card - 1) *
      (∏ e ∈ univ.image h, numer ρ γ (urnCount h e) e) /
        ∏ i ∈ Ico 1 m, ((1 - ρ) + ρ * i) := by
  simp only [allocationWeight, Fintype.card_fin, numer]
  rfl

/-- **The urn step.** The closed form with one more lineage. -/
theorem allocationWeight_snoc (hρ : 0 ≤ ρ) :
    allocationWeight ρ γ g =
      allocationWeight ρ γ (Fin.init g) * urnStep ρ γ (Fin.init g) (g (Fin.last m)) := by
  rw [allocationWeight_eq_numer, allocationWeight_eq_numer]
  unfold urnStep
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · have he : g (Fin.last 0) ∉ univ.image (Fin.init g) := by simp
    rw [numer_prod_of_notMem g he]
    simp
  · have hm' : m ≠ 0 := hm.ne'
    simp only [hm', ↓reduceIte]
    have hd : (1 - ρ) + ρ * m ≠ 0 := (urn_denominator_pos hρ hm).ne'
    rw [prod_Ico_succ_top hm]
    have hD : ∏ i ∈ Ico 1 m, ((1 - ρ) + ρ * (i : ℝ)) ≠ 0 :=
      prod_ne_zero_iff.2 fun i hi => (urn_denominator_pos hρ (mem_Ico.1 hi).1).ne'
    by_cases he : g (Fin.last m) ∈ univ.image (Fin.init g)
    · rw [numer_prod_of_mem g he, image_snoc, insert_eq_of_mem he]
      field_simp
    · have hne : (univ.image (Fin.init g)).Nonempty :=
        ⟨_, mem_image_of_mem _ (mem_univ (⟨0, hm⟩ : Fin m))⟩
      have hcard : 1 ≤ (univ.image (Fin.init g)).card := card_pos.2 hne
      rw [numer_prod_of_notMem g he, image_snoc, card_insert_of_notMem he,
        urnCount_eq_zero_of_notMem he, Nat.add_sub_cancel]
      obtain ⟨k, hk⟩ : ∃ k, (univ.image (Fin.init g)).card = k + 1 :=
        ⟨_, (Nat.sub_add_cancel hcard).symm⟩
      rw [hk, Nat.add_sub_cancel, pow_succ]
      field_simp
      simp only [Nat.cast_zero, mul_zero, add_zero]
      ring

end Snoc

/-- `allocationWeight` of an ordered assignment is the joint law of the urn. -/
theorem allocationWeight_eq_urn (hρ : 0 ≤ ρ) {m : ℕ} (g : Fin m → P) :
    allocationWeight ρ γ g = urnWeight ρ γ m g := by
  induction m with
  | zero => simp [allocationWeight, urnWeight]
  | succ m ih => rw [allocationWeight_snoc g hρ, ih, urnWeight]

/-- `allocationWeight` does not depend on the names of the lineages. -/
theorem allocationWeight_comp {R' : Type*} [Fintype R'] (σ : R' ≃ R) (a : R → P) :
    allocationWeight ρ γ (a ∘ σ) = allocationWeight ρ γ a := by
  have him : univ.image (a ∘ σ) = univ.image a := by
    ext e
    simp only [mem_image, mem_univ, true_and, Function.comp]
    exact ⟨fun ⟨r, hr⟩ => ⟨σ r, hr⟩, fun ⟨r, hr⟩ => ⟨σ.symm r, by simpa using hr⟩⟩
  have hc : ∀ e,
      (univ.filter fun r => (a ∘ σ) r = e).card = (univ.filter fun r => a r = e).card := by
    intro e
    refine card_equiv σ fun r => ?_
    simp [Function.comp]
  simp only [allocationWeight, him, hc, Fintype.card_congr σ]

/-- `allocationWeight` is the joint law of the urn, in any order of the lineages. -/
theorem allocationWeight_eq_urn_of_equiv (hρ : 0 ≤ ρ) {m : ℕ} (σ : R ≃ Fin m) (a : R → P) :
    allocationWeight ρ γ a = urnWeight ρ γ m (a ∘ σ.symm) := by
  rw [← allocationWeight_eq_urn hρ, allocationWeight_comp]

/-! ### A probability distribution -/

/-- `allocationWeight` is nonnegative. -/
theorem allocationWeight_nonneg (h0 : 0 ≤ ρ) (h1 : ρ ≤ 1) (hγ : ∀ e, 0 ≤ γ e) (a : R → P) :
    0 ≤ allocationWeight ρ γ a := by
  unfold allocationWeight
  refine div_nonneg (mul_nonneg (pow_nonneg (sub_nonneg.2 h1) _) (prod_nonneg fun e _ =>
    mul_nonneg (hγ e) (prod_nonneg fun j _ => ?_))) (prod_nonneg fun i hi => ?_)
  · exact add_nonneg (mul_nonneg (sub_nonneg.2 h1) (hγ e)) (mul_nonneg h0 (Nat.cast_nonneg j))
  · exact (urn_denominator_pos h0 (mem_Ico.1 hi).1).le

private theorem sum_allocationWeight_fin (hρ : 0 ≤ ρ) (hγ : ∑ e, γ e = 1) (m : ℕ) :
    ∑ g : Fin m → P, allocationWeight ρ γ g = 1 := by
  induction m with
  | zero => simp [allocationWeight]
  | succ m ih =>
    rw [← (Fin.snocEquiv fun _ : Fin (m + 1) => P).sum_comp, Fintype.sum_prod_type_right]
    simp only [Fin.snocEquiv_apply]
    rw [← ih]
    refine sum_congr rfl fun h _ => ?_
    simp only [allocationWeight_snoc _ hρ, Fin.init_snoc, Fin.snoc_last]
    rw [← mul_sum, sum_urnStep hρ hγ, mul_one]

/-- **Pólya normalization**: `allocationWeight` sums to one over all assignments. -/
theorem sum_allocationWeight [DecidableEq R] (hρ : 0 ≤ ρ) (hγ : ∑ e, γ e = 1) :
    ∑ a : R → P, allocationWeight ρ γ a = 1 := by
  let σ := Fintype.equivFin R
  rw [← sum_allocationWeight_fin hρ hγ (Fintype.card R)]
  refine Fintype.sum_equiv (Equiv.arrowCongr σ (Equiv.refl P)) _ _ fun a => ?_
  exact (allocationWeight_comp σ.symm a).symm

/-! ### The endpoints -/

/-- At `ρ = 0` the lineages choose independently. -/
theorem allocationWeight_rho_zero (a : R → P) :
    allocationWeight 0 γ a = ∏ r, γ (a r) := by
  rw [prod_comp γ a]
  simp only [allocationWeight, sub_zero, one_pow, one_mul, zero_mul, add_zero, prod_const_one,
    div_one]
  refine prod_congr rfl fun e he => ?_
  have hpos : 1 ≤ (univ.filter fun r => a r = e).card := by
    obtain ⟨r, -, rfl⟩ := mem_image.1 he
    exact card_pos.2 ⟨r, mem_filter.2 ⟨mem_univ _, rfl⟩⟩
  rw [prod_const, Nat.card_Ico, ← pow_succ', Nat.sub_add_cancel hpos]

omit [Fintype P] in
private theorem image_const_of_nonempty [Nonempty R] (e : P) :
    (univ.image fun _ : R => e) = {e} :=
  image_const univ_nonempty e

/-- The closed form on a constant assignment of a nonempty set of lineages. -/
theorem allocationWeight_const [Nonempty R] (e : P) :
    allocationWeight ρ γ (fun _ : R => e) =
      γ e * (∏ j ∈ Ico 1 (Fintype.card R), ((1 - ρ) * γ e + ρ * j)) /
        ∏ i ∈ Ico 1 (Fintype.card R), ((1 - ρ) + ρ * i) := by
  simp only [allocationWeight, image_const_of_nonempty, prod_singleton, card_singleton,
    Nat.sub_self, pow_zero, one_mul, filter_true, card_univ]

/-- At `ρ = 1` all lineages take one parent `e`, with probability `γ_e`. -/
theorem allocationWeight_rho_one (r₀ : R) (a : R → P) :
    allocationWeight 1 γ a = if ∀ r, a r = a r₀ then γ (a r₀) else 0 := by
  have : Nonempty R := ⟨r₀⟩
  split_ifs with h
  · have ha : a = fun _ => a r₀ := funext h
    rw [ha, allocationWeight_const]
    simp only [sub_self, zero_mul, zero_add, one_mul]
    have hne : ∏ i ∈ Ico 1 (Fintype.card R), ((i : ℕ) : ℝ) ≠ 0 :=
      prod_ne_zero_iff.2 fun i hi => by
        have := (mem_Ico.1 hi).1
        positivity
    rw [mul_div_assoc, div_self hne, mul_one]
  · have hr : ∃ r, a r ≠ a r₀ := by simpa using h
    obtain ⟨r, hr⟩ := hr
    have h2 : 2 ≤ (univ.image a).card := by
      have : ({a r, a r₀} : Finset P) ⊆ univ.image a := by
        intro x hx
        simp only [mem_insert, mem_singleton] at hx
        rcases hx with rfl | rfl <;> exact mem_image_of_mem _ (mem_univ _)
      have hc := card_le_card this
      rwa [card_pair hr] at hc
    have hk : (univ.image a).card - 1 ≠ 0 := by omega
    simp [allocationWeight, hk]

/-- At `ρ = 1`, all lineages take the parent `e` with probability `γ_e`. -/
theorem allocationWeight_rho_one_const [Nonempty R] (e : P) :
    allocationWeight 1 γ (fun _ : R => e) = γ e := by
  obtain ⟨r₀⟩ := ‹Nonempty R›
  rw [allocationWeight_rho_one r₀]
  simp

/-- A constant assignment to a parent of positive inheritance has positive probability. -/
theorem allocationWeight_const_pos (h0 : 0 ≤ ρ) (h1 : ρ ≤ 1) {e : P} (he : 0 < γ e) :
    0 < allocationWeight ρ γ (fun _ : R => e) := by
  have hden : 0 < ∏ i ∈ Ico 1 (Fintype.card R), ((1 - ρ) + ρ * (i : ℝ)) :=
    prod_pos fun i hi => urn_denominator_pos h0 (mem_Ico.1 hi).1
  have hnum : ∀ n : ℕ, 0 < ∏ j ∈ Ico 1 n, ((1 - ρ) * γ e + ρ * (j : ℝ)) := fun n =>
    prod_pos fun j hj => by
      have hj' : (1 : ℝ) ≤ j := by exact_mod_cast (mem_Ico.1 hj).1
      by_cases hρ : ρ = 0
      · simpa [hρ] using he
      · have : 0 < ρ := lt_of_le_of_ne h0 (Ne.symm hρ)
        have h2 : 0 ≤ (1 - ρ) * γ e := mul_nonneg (sub_nonneg.2 h1) he.le
        nlinarith
  rcases isEmpty_or_nonempty R with hR | hR
  · simp [allocationWeight]
  · rw [allocationWeight_const]
    exact div_pos (mul_pos he (hnum _)) hden

end Phylogenetics
