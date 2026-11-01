module

public import External.MyersGriffiths2003.Algorithm1

/-!
# Adding constraints to the integer program of Myers and Griffiths

Myers and Griffiths 2003, p. 378: "if we wish to impose `r_k = 0` then we need only remove the term in `r_k` from each constraint. This results in a system of the same form as before, which may readily be solved through the same algorithm; the new system will have no solution if `B_{k(k+1)} > 0`, corresponding to a known recombination in the interval `(s_k, s_{k+1})`. An extension of this is the case where recombination is allowed only between a few sites or even a single adjacent pair of sites; this again results in the same form for the system of equations, which may be solved using the method of Algorithm 1."

Removing the term in `r_k` merges the sites `k` and `k + 1`. So the general form is a monotone map `f` of the sites, onto an initial segment (`IsMerging`), with `r_l = 0` when `f` doesn't separate `l` and `l + 1`. Several constraints of the old system can become one of the new, and it takes the largest of their bounds (`mergedBounds`). The source's "system of the same form" has that much to it.

* `isLeast_of_merging`: the program with these constraints has the optimal value of Algorithm 1 on the new system;
* `exists_ne_zero_of_merging`: it has no solution if a bound between sites that are merged is positive;
* `isLeast_of_eq_zero`, `ne_zero_of_pos`: the case of `r_k = 0`.

The case of "a single adjacent pair of sites" is `f l = if l ≤ k then 0 else 1`, and "a few sites" a map with a few steps.
-/

@[expose] public section

namespace MyersGriffiths2003

open Finset

/-- A merging of consecutive sites: `f` starts at `0` and goes up by `0` or `1`. An interval `l` with `f (l + 1) = f l` is one with `r_l = 0`. -/
structure IsMerging (f : ℕ → ℕ) : Prop where
  zero : f 0 = 0
  step : ∀ l, f (l + 1) = f l ∨ f (l + 1) = f l + 1

variable {f : ℕ → ℕ} {S : ℕ} {B : ℕ → ℕ → ℕ}

theorem IsMerging.monotone (hf : IsMerging f) : Monotone f :=
  monotone_nat_of_le_succ fun n => by
    rcases hf.step n with h | h <;> omega

/-- Between two sites that are merged, every interval is merged. -/
theorem IsMerging.eq_succ_of_eq (hf : IsMerging f) {i j l : ℕ} (h : f i = f j) (hi : i ≤ l) (hj : l < j) : f (l + 1) = f l := by
  have h₁ := hf.monotone hi
  have h₂ := hf.monotone (show l + 1 ≤ j from hj)
  have h₃ := hf.monotone (show l ≤ l + 1 by omega)
  omega

/-- The bounds of the new system: a pair of new sites has the largest bound of the old pairs that it comes from. -/
def mergedBounds (S : ℕ) (B : ℕ → ℕ → ℕ) (f : ℕ → ℕ) : ℕ → ℕ → ℕ := fun p q =>
  ((range S ×ˢ range S).filter fun x => x.1 < x.2 ∧ f x.1 = p ∧ f x.2 = q).sup fun x => B x.1 x.2

theorem le_mergedBounds {i j : ℕ} (hij : i < j) (hj : j < S) : B i j ≤ mergedBounds S B f (f i) (f j) := by
  have hmem : (i, j) ∈ (range S ×ˢ range S).filter fun x : ℕ × ℕ => x.1 < x.2 ∧ f x.1 = f i ∧ f x.2 = f j :=
    mem_filter.2 ⟨mem_product.2 ⟨mem_range.2 (hij.trans hj), mem_range.2 hj⟩, hij, rfl, rfl⟩
  exact Finset.le_sup (f := fun x : ℕ × ℕ => B x.1 x.2) hmem

/-- A vector of the new system, as a vector of the old one, with `0` at what's merged. -/
def liftVector (f : ℕ → ℕ) (r' : ℕ → ℕ) : ℕ → ℕ := fun l => if f (l + 1) = f l then 0 else r' (f l)

/-- A vector of the old system, zero at what's merged, as a vector of the new one. -/
def pushVector (S : ℕ) (f : ℕ → ℕ) (r : ℕ → ℕ) : ℕ → ℕ := fun x => ∑ l ∈ (range (S - 1)).filter (f · = x), r l

theorem sum_liftVector (hf : IsMerging f) (r' : ℕ → ℕ) {i j : ℕ} (hij : i ≤ j) :
    ∑ l ∈ Ico i j, liftVector f r' l = ∑ x ∈ Ico (f i) (f j), r' x := by
  induction j, hij using Nat.le_induction with
  | base => simp
  | succ j hij ih =>
    rw [sum_Ico_succ_top hij, ih]
    unfold liftVector
    rcases hf.step j with h | h
    · rw [ite_eq_left h, h, add_zero]
    · rw [ite_eq_right (by omega), h, sum_Ico_succ_top (hf.monotone hij)]

theorem sum_pushVector (hf : IsMerging f) {r : ℕ → ℕ} (hr : ∀ l, l + 1 < S → f (l + 1) = f l → r l = 0) {i j : ℕ} (hij : i ≤ j) (hj : j < S) :
    ∑ l ∈ Ico i j, r l = ∑ x ∈ Ico (f i) (f j), pushVector S f r x := by
  induction j, hij using Nat.le_induction with
  | base => simp
  | succ j hij ih =>
    rw [sum_Ico_succ_top hij, ih (by omega)]
    rcases hf.step j with h | h
    · rw [h, hr j hj h, add_zero]
    · rw [h, sum_Ico_succ_top (hf.monotone hij)]
      congr 1
      have hjm : j ∈ (range (S - 1)).filter (f · = f j) := mem_filter.2 ⟨mem_range.2 (by omega), rfl⟩
      change r j = ∑ l ∈ (range (S - 1)).filter (f · = f j), r l
      refine (sum_eq_single_of_mem j hjm fun l hl hne => ?_).symm
      obtain ⟨hl₁, hl₂⟩ := mem_filter.1 hl
      have hl₁' := mem_range.1 hl₁
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · exact hr l (by omega) (hf.eq_succ_of_eq hl₂ le_rfl hlt)
      · have := hf.monotone (show j + 1 ≤ l from hgt)
        omega

/-- **The program with the constraints** (`ext:mg_constraints`). If no bound between merged sites is positive, the program "minimize `Σ_{l=s}^{t-1} r_l` subject to (2) and to `r_l = 0` at what's merged" has the optimal value of Algorithm 1 on the new system. -/
theorem isLeast_of_merging (hf : IsMerging f) (hB : ∀ i j, i < j → j < S → f i = f j → B i j = 0) {s t : ℕ} (hst : s ≤ t) (ht : t < S) :
    IsLeast ((fun r : ℕ → ℕ => ∑ l ∈ Ico s t, r l) '' {r | Feasible S B r ∧ ∀ l, l + 1 < S → f (l + 1) = f l → r l = 0})
      (algorithm1 (mergedBounds S B f) (f (S - 1) + 1) (f s) (f t)) := by
  have hle : ∀ j, j < S → f j < f (S - 1) + 1 := fun j hj => Nat.lt_succ_of_le (hf.monotone (by omega))
  obtain ⟨⟨r', hr', hsum⟩, hub⟩ := algorithm1_isOptimalValue (mergedBounds S B f) (hf.monotone hst) (hle t ht)
  refine ⟨⟨liftVector f r', ⟨fun i j hij hj => ?_, fun l _ hl => ite_eq_left hl⟩, ?_⟩, ?_⟩
  · rw [sum_liftVector hf r' hij.le]
    rcases (hf.monotone hij.le).eq_or_lt with heq | hlt
    · rw [hB i j hij hj heq]
      exact Nat.zero_le _
    · exact (le_mergedBounds hij hj).trans (hr' _ _ hlt (hle j hj))
  · change ∑ l ∈ Ico s t, liftVector f r' l = _
    rw [sum_liftVector hf r' hst]
    exact hsum
  · rintro _ ⟨r, ⟨hrF, hrZ⟩, rfl⟩
    change _ ≤ ∑ l ∈ Ico s t, r l
    rw [sum_pushVector hf hrZ hst ht]
    refine hub ⟨pushVector S f r, fun p q _ _ => ?_, rfl⟩
    refine Finset.sup_le fun x hx => ?_
    obtain ⟨hx₁, hx₂, rfl, rfl⟩ := mem_filter.1 hx
    have hx₃ := mem_range.1 (mem_product.1 hx₁).2
    rw [← sum_pushVector hf hrZ hx₂.le hx₃]
    exact hrF _ _ hx₂ hx₃

/-- **No solution** (`ext:mg_constraints_none`). A positive bound between merged sites has no solution with `r_l = 0` at what's merged. -/
theorem exists_ne_zero_of_merging (hf : IsMerging f) {i j : ℕ} (hij : i < j) (hj : j < S) (hfij : f i = f j) (hB : 0 < B i j) {r : ℕ → ℕ} (hr : Feasible S B r) :
    ∃ l, l + 1 < S ∧ f (l + 1) = f l ∧ r l ≠ 0 := by
  by_contra hno
  push Not at hno
  have hzero : ∑ l ∈ Ico i j, r l = 0 := by
    refine sum_eq_zero fun l hl => ?_
    obtain ⟨h₁, h₂⟩ := mem_Ico.1 hl
    exact hno l (by omega) (hf.eq_succ_of_eq hfij h₁ h₂)
  have := hr i j hij hj
  omega

/-- Removing the term in `r_k` merges the sites `k` and `k + 1`. -/
def mergeAt (k : ℕ) : ℕ → ℕ := fun x => if x ≤ k then x else x - 1

theorem isMerging_mergeAt (k : ℕ) : IsMerging (mergeAt k) := by
  refine ⟨by simp [mergeAt], fun l => ?_⟩
  unfold mergeAt
  split_ifs <;> omega

theorem mergeAt_succ_eq_iff {k l : ℕ} : mergeAt k (l + 1) = mergeAt k l ↔ l = k := by
  unfold mergeAt
  split_ifs <;> omega

/-- The constraint of a pair of sites loses the term in `r_k`: the new interval `x` is the old interval `x`, or `x + 1` from `k` on. So this is the source's "remove the term in `r_k` from each constraint". -/
theorem sum_liftVector_mergeAt (k : ℕ) (r' : ℕ → ℕ) {i j : ℕ} (hij : i ≤ j) :
    ∑ l ∈ Ico i j, (if l = k then 0 else r' (mergeAt k l)) = ∑ x ∈ Ico (mergeAt k i) (mergeAt k j), r' x := by
  rw [← sum_liftVector (isMerging_mergeAt k) r' hij]
  refine sum_congr rfl fun l _ => ?_
  unfold liftVector
  simp only [mergeAt_succ_eq_iff]

/-- **Imposing `r_k = 0`** (`ext:mg_r_eq_zero`). With `B_{k(k+1)} = 0`, the program with `r_k = 0` on the sites `0, ..., S - 1` has the optimal value of Algorithm 1 on the system of `S - 1` sites without the term in `r_k`. -/
theorem isLeast_of_eq_zero {k : ℕ} (hk : k + 1 < S) (hB : B k (k + 1) = 0) {s t : ℕ} (hst : s ≤ t) (ht : t < S) :
    IsLeast ((fun r : ℕ → ℕ => ∑ l ∈ Ico s t, r l) '' {r | Feasible S B r ∧ r k = 0})
      (algorithm1 (mergedBounds S B (mergeAt k)) (S - 1) (mergeAt k s) (mergeAt k t)) := by
  have hmain := isLeast_of_merging (S := S) (B := B) (isMerging_mergeAt k) (fun i j hij _ hf => by
    have hi : i = k := by
      unfold mergeAt at hf
      split_ifs at hf <;> omega
    have hj : j = k + 1 := by
      unfold mergeAt at hf
      split_ifs at hf <;> omega
    rw [hi, hj, hB]) hst ht
  have hS : mergeAt k (S - 1) + 1 = S - 1 := by
    unfold mergeAt
    rw [ite_eq_right (by omega)]
    omega
  rw [hS] at hmain
  have hset : {r : ℕ → ℕ | Feasible S B r ∧ r k = 0} = {r | Feasible S B r ∧ ∀ l, l + 1 < S → mergeAt k (l + 1) = mergeAt k l → r l = 0} := by
    ext r
    refine and_congr_right fun _ => ⟨fun h l _ hl => by rw [mergeAt_succ_eq_iff.1 hl]; exact h, fun h => h k hk (mergeAt_succ_eq_iff.2 rfl)⟩
  rw [hset]
  exact hmain

/-- "The new system will have no solution if `B_{k(k+1)} > 0`, corresponding to a known recombination in the interval" (`ext:mg_r_eq_zero_none`). -/
theorem ne_zero_of_pos {k : ℕ} (hk : k + 1 < S) (hB : 0 < B k (k + 1)) {r : ℕ → ℕ} (hr : Feasible S B r) : r k ≠ 0 := by
  have := hr k (k + 1) (Nat.lt_succ_self k) hk
  rw [Nat.Ico_succ_singleton, sum_singleton] at this
  omega

end MyersGriffiths2003
