module

public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Algebra.Order.Group.Int
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-!
# The integer program and Algorithm 1 of Myers and Griffiths

Myers and Griffiths 2003, pp. 377-378 and Appendix A: local bounds `B_ij` on the number of recombination events between sites combine into a bound on a longer stretch, by the integer linear program (2). Algorithm 1 solves it, by dynamic programming. This module has only the optimization, with no networks: `External.MyersGriffiths2003.Composite` has what it says about `R`.

The sites are numbered from `0`, and from `1` in the source. So the source's `S` sites are `0, ..., S - 1`, and its `r_l` is the number of events between the sites `l` and `l + 1`. The bounds and the vector are functions on `ℕ`, of which the system looks only at what's in range.

The order is the source's:

* the system (2) (`Feasible`) and the optimal value of its objective on a region (`IsOptimalValue`);
* the vector of Proposition 6 (`rStar`, `rStarVec`), and Lemma 7 (`lemma7`), with the tight constraint (A1) (`exists_tight`);
* Corollary 8, the maximum over chains of sites (`corollary8`);
* Algorithm 1 (`algorithm1`), with (A4) to (A7) (`algorithm1_isChainMax`, `algorithm1_isOptimalValue`);
* the recovery of the vector of Proposition 6 from the top row (`rStarVec_eq_sub`), which is as far to the right as possible (`sum_rStarVec_le_of_feasible`), and another from the last column (`isOptimalValue_column`), and the bounds of a best chain, tight in all optimal solutions (`sum_eq_of_chainSum_eq`).

A misprint in Appendix A, p. 393: "those bounds `B_pq` with `p < j` or `q > k` can obviously always be satisfied by setting `r_p` or `r_q`, respectively, to be large enough". The constraint `B_pq` has no term in `r_q`: it's `r_{q-1}` that is outside the region and in the constraint. The argument holds with it (`exists_feasible_extend`).
-/

@[expose] public section

namespace MyersGriffiths2003

open Finset

/-! ### The integer program -/

/-- The system (2), for the sites `0, ..., S - 1`: the vector `r` of nonnegative integers satisfies `Σ_{l=i}^{j-1} r_l ≥ B_ij` for `i < j`. -/
def Feasible (S : ℕ) (B : ℕ → ℕ → ℕ) (r : ℕ → ℕ) : Prop :=
  ∀ i j, i < j → j < S → B i j ≤ ∑ l ∈ Ico i j, r l

/-- `v` is the optimal value of the integer linear program of Algorithm 1: minimize `Σ_{l=s}^{t-1} r_l` subject to the system (3), the same as (2). -/
def IsOptimalValue (S : ℕ) (B : ℕ → ℕ → ℕ) (s t v : ℕ) : Prop :=
  IsLeast ((fun r : ℕ → ℕ => ∑ l ∈ Ico s t, r l) '' {r | Feasible S B r}) v

theorem Feasible.mono {S S' : ℕ} {B : ℕ → ℕ → ℕ} {r : ℕ → ℕ} (h : Feasible S B r) (hS : S' ≤ S) : Feasible S' B r :=
  fun i j hij hj => h i j hij (hj.trans_le hS)

theorem IsOptimalValue.unique {S : ℕ} {B : ℕ → ℕ → ℕ} {s t v w : ℕ} (h : IsOptimalValue S B s t v) (h' : IsOptimalValue S B s t w) : v = w :=
  IsLeast.unique h h'

/-! ### Proposition 6: the vector found by sweeping from the left -/

/-- The maximization step of Proposition 6: the largest entry of the column `k + 1` of `U`, over the rows `0, ..., k`. -/
def maxColumn (U : ℕ → ℕ → ℤ) (k : ℕ) : ℤ :=
  (range (k + 1)).sup' nonempty_range_add_one fun i => U i (k + 1)

/-- The bounds of Proposition 6 after the updating steps of the columns before `k`: "for `i = 1, ..., k` and `j = k + 2, ..., S`, subtract `r*_k` from `B_ij`". They can become negative, so they are integers. -/
def updatedBounds (B : ℕ → ℕ → ℕ) : ℕ → ℕ → ℕ → ℤ
  | 0 => fun i j => (B i j : ℤ)
  | k + 1 => fun i j =>
    if i ≤ k ∧ k + 2 ≤ j then updatedBounds B k i j - maxColumn (updatedBounds B k) k else updatedBounds B k i j

/-- `r*_k` of Proposition 6, as an integer: `rStarVec` is the same as a natural number. -/
def rStar (B : ℕ → ℕ → ℕ) (k : ℕ) : ℤ :=
  maxColumn (updatedBounds B k) k

variable {B : ℕ → ℕ → ℕ}

/-- What the updating steps have subtracted by the time `k`, from an entry to the right of them. -/
theorem updatedBounds_eq (k i j : ℕ) (hj : k + 1 ≤ j) :
    updatedBounds B k i j = (B i j : ℤ) - ∑ l ∈ Ico i k, rStar B l := by
  induction k with
  | zero =>
    simp [updatedBounds]
  | succ k ih =>
    have hih := ih (by omega)
    unfold updatedBounds
    by_cases hi : i ≤ k
    · rw [ite_eq_left ⟨hi, by omega⟩, hih, sum_Ico_succ_top hi]
      unfold rStar
      ring
    · rw [ite_eq_right fun h => hi h.1, hih, Ico_eq_empty (by omega), Ico_eq_empty (by omega)]

theorem le_rStar {k i : ℕ} (hi : i ≤ k) : (B i (k + 1) : ℤ) - ∑ l ∈ Ico i k, rStar B l ≤ rStar B k := by
  rw [← updatedBounds_eq k i (k + 1) le_rfl]
  exact le_sup' (fun i => updatedBounds B k i (k + 1)) (mem_range.2 (by omega))

/-- `r*_k` is nonnegative: the entry `B_{k,k+1}` is never updated. -/
theorem rStar_nonneg (k : ℕ) : 0 ≤ rStar B k := by
  have h := le_rStar (B := B) (le_refl k)
  simp only [Ico_self, sum_empty, sub_zero] at h
  exact (Int.natCast_nonneg _).trans h

/-- The maximum of `r*_k` is reached by some `B_{m,k+1}`. This gives (A1): `Σ_{l=m}^{k} r*_l = B_{m,k+1}`. -/
theorem exists_tight (k : ℕ) : ∃ m ≤ k, (B m (k + 1) : ℤ) = ∑ l ∈ Ico m (k + 1), rStar B l := by
  obtain ⟨m, hm, hmax⟩ := exists_mem_eq_sup' (nonempty_range_add_one (n := k)) fun i => updatedBounds B k i (k + 1)
  have hm' : m ≤ k := by
    have := mem_range.1 hm
    omega
  refine ⟨m, hm', ?_⟩
  have h : rStar B k = updatedBounds B k m (k + 1) := hmax
  rw [updatedBounds_eq k m (k + 1) le_rfl] at h
  rw [sum_Ico_succ_top hm', h]
  ring

/-- **The vector of Proposition 6**, as natural numbers. -/
def rStarVec (B : ℕ → ℕ → ℕ) (k : ℕ) : ℕ := (rStar B k).toNat

theorem rStarVec_cast (k : ℕ) : (rStarVec B k : ℤ) = rStar B k :=
  Int.toNat_of_nonneg (rStar_nonneg k)

theorem sum_rStarVec_cast (a b : ℕ) : ((∑ l ∈ Ico a b, rStarVec B l : ℕ) : ℤ) = ∑ l ∈ Ico a b, rStar B l := by
  rw [Nat.cast_sum]
  exact sum_congr rfl fun l _ => rStarVec_cast (B := B) l

/-- The vector of Proposition 6 satisfies the whole system: "at the maximization step ... the smallest value needed to satisfy all the conditions whose last term is `r_k`". -/
theorem rStarVec_feasible (B : ℕ → ℕ → ℕ) (S : ℕ) : Feasible S B (rStarVec B) := by
  intro i j hij _
  obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
  have hi : i ≤ k := by omega
  have h := le_rStar (B := B) hi
  have hgoal : (B i (k + 1) : ℤ) ≤ ((∑ l ∈ Ico i (k + 1), rStarVec B l : ℕ) : ℤ) := by
    rw [sum_rStarVec_cast, sum_Ico_succ_top hi]
    linarith
  exact_mod_cast hgoal

/-- (A1), as natural numbers. -/
theorem exists_tight_nat (k : ℕ) : ∃ m ≤ k, B m (k + 1) = ∑ l ∈ Ico m (k + 1), rStarVec B l := by
  obtain ⟨m, hm, h⟩ := exists_tight (B := B) k
  refine ⟨m, hm, ?_⟩
  have : (B m (k + 1) : ℤ) = ((∑ l ∈ Ico m (k + 1), rStarVec B l : ℕ) : ℤ) := by
    rw [sum_rStarVec_cast, h]
  exact_mod_cast this

/-- The minimality in Lemma 7, by the source's induction: `Σ_{l<n} r*_l ≤ Σ_{l<n} r_l` for a vector `r` satisfying the conditions with `j ≤ n`. -/
theorem sum_rStarVec_le {n : ℕ} {r : ℕ → ℕ} (hr : Feasible (n + 1) B r) : ∑ l ∈ range n, rStarVec B l ≤ ∑ l ∈ range n, r l := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases n with - | k
    · simp
    · obtain ⟨m, hm, htight⟩ := exists_tight_nat (B := B) k
      have hsplit : ∀ f : ℕ → ℕ, ∑ l ∈ range (k + 1), f l = ∑ l ∈ range m, f l + ∑ l ∈ Ico m (k + 1), f l := by
        intro f
        rw [range_eq_Ico, range_eq_Ico, sum_Ico_consecutive f (Nat.zero_le m) (by omega)]
      have h₁ := ih m (by omega) (hr.mono (by omega))
      have h₂ := hr m (k + 1) (by omega) (by omega)
      rw [hsplit, hsplit r, ← htight]
      omega

/-- **Lemma 7** (`ext:mg_lemma7`). For any `k`, the vector `r*_0, ..., r*_k` minimizes `R_k = Σ_{l=0}^{k} r_l` subject to the conditions of (2) with `j ≤ k + 1`. The value is that of the first `k + 1` entries, and the rest of the vector plays no part. -/
theorem lemma7 (B : ℕ → ℕ → ℕ) (k : ℕ) :
    IsLeast ((fun r : ℕ → ℕ => ∑ l ∈ range (k + 1), r l) '' {r | Feasible (k + 2) B r}) (∑ l ∈ range (k + 1), rStarVec B l) := by
  refine ⟨⟨rStarVec B, rStarVec_feasible B _, rfl⟩, ?_⟩
  rintro _ ⟨r, hr, rfl⟩
  exact sum_rStarVec_le hr

/-- **Proposition 6** (`ext:mg_prop6`). An optimal vector for the system (2), on the sites `0, ..., S`, is the vector `r*` generated by the algorithm: Lemma 7 at the last `k`. For `S = 0` there's nothing to minimize. -/
theorem proposition6 (B : ℕ → ℕ → ℕ) (S : ℕ) :
    Feasible (S + 1) B (rStarVec B) ∧ ∀ r, Feasible (S + 1) B r → ∑ l ∈ range S, rStarVec B l ≤ ∑ l ∈ range S, r l :=
  ⟨rStarVec_feasible B _, fun _ hr => sum_rStarVec_le hr⟩

/-! ### Corollary 8: the maximum over chains -/

/-- The sum `Σ_j B_{i_j i_{j+1}}` along the chain with first site `a` and the next sites `l`. -/
def chainSum (B : ℕ → ℕ → ℕ) : ℕ → List ℕ → ℕ
  | _, [] => 0
  | a, b :: l => B a b + chainSum B b l

/-- The sites `a, l` form a chain `a = i_1 < i_2 < ... < i_k = t`. -/
def IsChainTo : ℕ → ℕ → List ℕ → Prop
  | a, t, [] => a = t
  | a, t, b :: l => a < b ∧ IsChainTo b t l

theorem IsChainTo.le {a t : ℕ} {l : List ℕ} (h : IsChainTo a t l) : a ≤ t := by
  induction l generalizing a with
  | nil => exact le_of_eq h
  | cons b l ih => exact h.1.le.trans (ih h.2)

theorem IsChainTo.append_singleton {a i k : ℕ} {l : List ℕ} (h : IsChainTo a i l) (hik : i < k) : IsChainTo a k (l ++ [k]) := by
  induction l generalizing a with
  | nil =>
    obtain rfl : a = i := h
    exact ⟨hik, rfl⟩
  | cons b l ih => exact ⟨h.1, ih h.2⟩

theorem chainSum_append_singleton {a i k : ℕ} {l : List ℕ} (h : IsChainTo a i l) : chainSum B a (l ++ [k]) = chainSum B a l + B i k := by
  induction l generalizing a with
  | nil =>
    obtain rfl : a = i := h
    simp [chainSum]
  | cons b l ih =>
    simp only [List.cons_append, chainSum]
    rw [ih h.2]
    ring

/-- A chain with more than one site has a last step. -/
theorem IsChainTo.exists_last {a k : ℕ} {l : List ℕ} (h : IsChainTo a k l) (hak : a < k) :
    ∃ l' i, l = l' ++ [k] ∧ IsChainTo a i l' ∧ i < k := by
  induction l generalizing a with
  | nil => exact absurd (show a = k from h) hak.ne
  | cons b l ih =>
    rcases l with - | ⟨c, l⟩
    · obtain rfl : b = k := h.2
      exact ⟨[], a, rfl, rfl, h.1⟩
    · have hbk : b < k := h.2.1.trans_le h.2.2.le
      obtain ⟨l', i, hl, hc, hi⟩ := ih h.2 hbk
      refine ⟨b :: l', i, ?_, ⟨h.1, hc⟩, hi⟩
      rw [hl, List.cons_append]

/-- `v` is the maximum of the sum of `B` over the chains from `a` to `t`. -/
def IsChainMax (B : ℕ → ℕ → ℕ) (a t v : ℕ) : Prop :=
  IsGreatest {x | ∃ l, IsChainTo a t l ∧ x = chainSum B a l} v

/-- (A2): "the number of recombinations in the interval `(i_j, i_{j+1})` cannot be below `B_{i_j i_{j+1}}`, and the intervals ... are disjoint". -/
theorem chainSum_le_sum {S a t : ℕ} {l : List ℕ} {r : ℕ → ℕ} (hr : Feasible S B r) (h : IsChainTo a t l) (ht : t < S) :
    chainSum B a l ≤ ∑ m ∈ Ico a t, r m := by
  induction l generalizing a with
  | nil =>
    obtain rfl : a = t := h
    simp [chainSum]
  | cons b l ih =>
    have hbt := h.2.le
    have h₁ := hr a b h.1 (hbt.trans_lt ht)
    have h₂ := ih h.2
    rw [← sum_Ico_consecutive r h.1.le hbt]
    exact add_le_add h₁ h₂

/-- (A3): following the tight constraints from the right gives a chain whose sum is the value of `r*`. -/
theorem exists_chain_eq (B : ℕ → ℕ → ℕ) (n : ℕ) : ∃ l, IsChainTo 0 n l ∧ chainSum B 0 l = ∑ m ∈ range n, rStarVec B m := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases n with - | k
    · exact ⟨[], rfl, by simp [chainSum]⟩
    · obtain ⟨m, hm, htight⟩ := exists_tight_nat (B := B) k
      obtain ⟨l, hl, hsum⟩ := ih m (by omega)
      refine ⟨l ++ [k + 1], hl.append_singleton (by omega), ?_⟩
      rw [chainSum_append_singleton hl, hsum, htight, range_eq_Ico, range_eq_Ico,
        sum_Ico_consecutive _ (Nat.zero_le m) (by omega)]

/-- **Corollary 8** (`ext:mg_cor8`). `R_n = max_{0 = i_1 < i_2 < ... < i_k = n} Σ_j B_{i_j i_{j+1}}`, where `R_n` is the minimum of Lemma 7. "Thus we can write the optimal solution as a sum of bounds corresponding to disjoint intervals." -/
theorem corollary8 (B : ℕ → ℕ → ℕ) (n : ℕ) : IsChainMax B 0 n (∑ m ∈ range n, rStarVec B m) := by
  refine ⟨?_, ?_⟩
  · obtain ⟨l, hl, hsum⟩ := exists_chain_eq B n
    exact ⟨l, hl, hsum.symm⟩
  · rintro _ ⟨l, hl, rfl⟩
    have := chainSum_le_sum (S := n + 1) (rStarVec_feasible B _) hl (Nat.lt_succ_self n)
    rwa [← range_eq_Ico] at this

/-! ### Algorithm 1 -/

/-- Step 2 of Algorithm 1, on the column `k`: "for `j = 1, ..., k - 1` set `R_jk = max{R_ji + B_ik : i = j, j + 1, ..., k - 1}`". -/
def maximizationStep (B : ℕ → ℕ → ℕ) (k : ℕ) (R : ℕ → ℕ → ℕ) : ℕ → ℕ → ℕ := fun j t =>
  if t = k ∧ j < k then (Ico j k).sup (fun i => R j i + B i k) else R j t

/-- **Algorithm 1** (`ext:mg_algorithm1`): the matrix `R` after the columns before `S`, so that `algorithm1 B S` is the matrix for the sites `0, ..., S - 1`. "Set `R = 0`", the maximization step on a column, "if `k < S`, increment `k` by 1 and go to step 2". It's a computable function: `decide` evaluates it. The column `0` has no entry above the diagonal, so that its step does nothing. In particular, the minimum for the whole region is `algorithm1 B S 0 (S - 1)`, which is `R_{1S}` of the source. -/
def algorithm1 (B : ℕ → ℕ → ℕ) : ℕ → ℕ → ℕ → ℕ
  | 0 => fun _ _ => 0
  | S + 1 => maximizationStep B S (algorithm1 B S)

/-- A later step doesn't change an earlier column. -/
theorem algorithm1_succ_of_lt {S j t : ℕ} (ht : t < S) : algorithm1 B (S + 1) j t = algorithm1 B S j t := by
  change maximizationStep B S (algorithm1 B S) j t = _
  unfold maximizationStep
  rw [ite_eq_right fun h => ht.ne h.1]

theorem algorithm1_stable {S S' j t : ℕ} (ht : t < S) (hS : S ≤ S') : algorithm1 B S' j t = algorithm1 B S j t := by
  induction S', hS using Nat.le_induction with
  | base => rfl
  | succ S' hS ih => rw [algorithm1_succ_of_lt (ht.trans_le hS), ih]

/-- The diagonal stays `0`. -/
theorem algorithm1_self (S j : ℕ) : algorithm1 B S j j = 0 := by
  induction S with
  | zero => rfl
  | succ S ih =>
    change maximizationStep B S (algorithm1 B S) j j = _
    unfold maximizationStep
    rw [ite_eq_right fun h => h.2.ne h.1, ih]

/-- (A4): the recursion of the maximization step. Since it only looks at the row `j`, "if only the overall bound is required, this can be obtained easily by performing the algorithm but fixing `j = 1`". -/
theorem algorithm1_eq_sup {S j t : ℕ} (hjt : j < t) (ht : t < S) :
    algorithm1 B S j t = (Ico j t).sup fun i => algorithm1 B S j i + B i t := by
  rw [algorithm1_stable (Nat.lt_succ_self t) (show t + 1 ≤ S from ht)]
  change maximizationStep B t (algorithm1 B t) j t = _
  unfold maximizationStep
  rw [ite_eq_left ⟨rfl, hjt⟩]
  refine sup_congr rfl fun i hi => ?_
  have hi' := (mem_Ico.1 hi).2
  rw [algorithm1_stable (B := B) (j := j) hi' ht.le]

/-- (A6), (A7): the maximum over chains from `j` to `k` is got by the last step. -/
theorem IsChainMax.sup {j k : ℕ} {v : ℕ → ℕ} (hjk : j < k) (h : ∀ i ∈ Ico j k, IsChainMax B j i (v i)) :
    IsChainMax B j k ((Ico j k).sup fun i => v i + B i k) := by
  refine ⟨?_, ?_⟩
  · obtain ⟨i, hi, hmax⟩ := exists_mem_eq_sup (Ico j k) (nonempty_Ico.2 hjk) fun i => v i + B i k
    obtain ⟨l, hl, hsum⟩ := (h i hi).1
    refine ⟨l ++ [k], hl.append_singleton (mem_Ico.1 hi).2, ?_⟩
    rw [hmax, chainSum_append_singleton hl, hsum]
  · rintro _ ⟨l, hl, rfl⟩
    obtain ⟨l', i, rfl, hl', hik⟩ := hl.exists_last hjk
    have hi : i ∈ Ico j k := mem_Ico.2 ⟨hl'.le, hik⟩
    rw [chainSum_append_singleton hl']
    refine le_trans ?_ (le_sup (f := fun i => v i + B i k) hi)
    exact add_le_add_left ((h i hi).2 ⟨l', hl', rfl⟩) _

theorem isChainMax_self (B : ℕ → ℕ → ℕ) (j : ℕ) : IsChainMax B j j 0 := by
  refine ⟨⟨[], rfl, rfl⟩, ?_⟩
  rintro _ ⟨l, hl, rfl⟩
  rcases l with - | ⟨b, l⟩
  · exact le_rfl
  · exact absurd (hl.1.trans_le hl.2.le) (lt_irrefl j)

/-- The induction of the proof of Algorithm 1: the columns are "set correctly" in turn, to the maximum over chains. -/
theorem algorithm1_isChainMax {S j k : ℕ} (hjk : j ≤ k) (hk : k < S) : IsChainMax B j k (algorithm1 B S j k) := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    rcases hjk.eq_or_lt with rfl | hlt
    · rw [algorithm1_self]
      exact isChainMax_self B j
    · rw [algorithm1_eq_sup hlt hk]
      refine IsChainMax.sup hlt fun i hi => ?_
      obtain ⟨h₁, h₂⟩ := mem_Ico.1 hi
      exact ih i h₂ h₁ (h₂.trans hk)

/-! ### The region between two sites -/

/-- The system on the sites from `s` on, as "an ILP of the same form as the original system". -/
def shiftBounds (B : ℕ → ℕ → ℕ) (s : ℕ) : ℕ → ℕ → ℕ := fun p q => B (s + p) (s + q)

theorem chainSum_shift (s a : ℕ) (l : List ℕ) : chainSum (shiftBounds B s) a l = chainSum B (s + a) (l.map (s + ·)) := by
  induction l generalizing a with
  | nil => rfl
  | cons b l ih =>
    simp only [chainSum, List.map_cons, shiftBounds]
    rw [ih]

theorem isChainTo_shift {s a t : ℕ} {l : List ℕ} : IsChainTo (s + a) (s + t) (l.map (s + ·)) ↔ IsChainTo a t l := by
  induction l generalizing a with
  | nil =>
    simp [IsChainTo]
  | cons b l ih =>
    simp only [List.map_cons, IsChainTo, ih, Nat.add_lt_add_iff_left]

/-- A chain starting at `s + a` comes from a chain of the shifted system. -/
theorem exists_map_of_isChainTo {s a t : ℕ} {l : List ℕ} (h : IsChainTo (s + a) t l) : ∃ l' : List ℕ, l = l'.map (s + ·) := by
  induction l generalizing a with
  | nil => exact ⟨[], rfl⟩
  | cons b l ih =>
    obtain ⟨c, rfl⟩ : ∃ c, b = s + c := ⟨b - s, by have := h.1; omega⟩
    have hc : IsChainTo (s + c) t l := h.2
    obtain ⟨l', rfl⟩ := ih hc
    exact ⟨c :: l', rfl⟩

/-- Corollary 8 applied to the system from `s` on. -/
theorem isChainMax_shift (B : ℕ → ℕ → ℕ) (s n : ℕ) : IsChainMax B s (s + n) (∑ m ∈ range n, rStarVec (shiftBounds B s) m) := by
  obtain ⟨⟨l, hl, hsum⟩, hub⟩ := corollary8 (shiftBounds B s) n
  refine ⟨⟨l.map (s + ·), ?_, ?_⟩, ?_⟩
  · exact isChainTo_shift (a := 0).2 hl
  · rw [hsum, chainSum_shift]
    rfl
  · rintro _ ⟨l', hl', rfl⟩
    have hl'' : IsChainTo (s + 0) (s + n) l' := hl'
    obtain ⟨c, rfl⟩ := exists_map_of_isChainTo hl''
    refine hub ⟨c, isChainTo_shift.1 hl'', ?_⟩
    rw [chainSum_shift]
    rfl

/-- What's outside the region: "those bounds `B_pq` with `p < j` or `q > k` can obviously always be satisfied by setting `r_p` or `r_q`, respectively, to be large enough, and such terms will not contribute to the sum". With `r_{q-1}` in place of `r_q`: the constraint has no term in `r_q`. -/
theorem exists_feasible_extend {S s t : ℕ} {r : ℕ → ℕ} (hr : ∀ p q, s ≤ p → p < q → q ≤ t → B p q ≤ ∑ l ∈ Ico p q, r l) :
    ∃ r', Feasible S B r' ∧ ∀ l, s ≤ l → l < t → r' l = r l := by
  set big : ℕ := (range S).sup fun p => (range S).sup fun q => B p q with hbig
  have hle : ∀ p q, p < S → q < S → B p q ≤ big := fun p q hp hq =>
    (le_sup (f := fun q => B p q) (mem_range.2 hq)).trans (le_sup (f := fun p => (range S).sup fun q => B p q) (mem_range.2 hp))
  set r' : ℕ → ℕ := fun l => if s ≤ l ∧ l < t then r l else big with hr'
  have hr'in : ∀ l, s ≤ l → l < t → r' l = r l := fun l h₁ h₂ => ite_eq_left ⟨h₁, h₂⟩
  refine ⟨r', fun p q hpq hq => ?_, hr'in⟩
  by_cases hin : s ≤ p ∧ q ≤ t
  · refine (hr p q hin.1 hpq hin.2).trans (le_of_eq (sum_congr rfl fun l hl => ?_))
    obtain ⟨h₁, h₂⟩ := mem_Ico.1 hl
    exact (hr'in l (hin.1.trans h₁) (h₂.trans_le hin.2)).symm
  · -- An index of the constraint outside the region: `p` or `q - 1`.
    have hex : ∃ l ∈ Ico p q, r' l = big := by
      by_cases hp : s ≤ p
      · have hq' : t < q := by
          by_contra hc
          exact hin ⟨hp, not_lt.1 hc⟩
        refine ⟨q - 1, mem_Ico.2 ⟨by omega, by omega⟩, ite_eq_right fun h => ?_⟩
        have := h.2
        omega
      · exact ⟨p, mem_Ico.2 ⟨le_rfl, hpq⟩, ite_eq_right fun h => hp h.1⟩
    obtain ⟨l, hl, hlb⟩ := hex
    calc B p q ≤ big := hle p q (hpq.trans hq) hq
      _ = r' l := hlb.symm
      _ ≤ ∑ l ∈ Ico p q, r' l := single_le_sum (f := r') (fun _ _ => Nat.zero_le _) hl

theorem sum_Ico_shift (r : ℕ → ℕ) (s p q : ℕ) : ∑ l ∈ Ico (s + p) (s + q), r l = ∑ l ∈ Ico p q, r (s + l) := by
  rw [sum_Ico_add r p q s, add_comm s p, add_comm s q]

/-- **Algorithm 1** (`ext:mg_algorithm1_correct`). The matrix constructed is the matrix of optimal values: for `s ≤ t` among the sites `0, ..., S - 1`, `R_st` is the optimal value of the program "minimize `Σ_{l=s}^{t-1} r_l` over nonnegative integers subject to (3)". The proof is that of Appendix A: the constraints outside the region don't matter, Corollary 8 applies to the system on the region, and the maximum over chains obeys the recursion of the algorithm. -/
theorem algorithm1_isOptimalValue (B : ℕ → ℕ → ℕ) {S s t : ℕ} (hst : s ≤ t) (ht : t < S) :
    IsOptimalValue S B s t (algorithm1 B S s t) := by
  obtain ⟨n, rfl⟩ : ∃ n, t = s + n := ⟨t - s, by omega⟩
  have hval : algorithm1 B S s (s + n) = ∑ m ∈ range n, rStarVec (shiftBounds B s) m :=
    IsGreatest.unique (algorithm1_isChainMax hst ht) (isChainMax_shift B s n)
  rw [hval]
  refine ⟨?_, ?_⟩
  · -- The vector of Proposition 6 on the region, extended outside it.
    set ρ : ℕ → ℕ := fun l => rStarVec (shiftBounds B s) (l - s) with hρ
    have hsum : ∀ p q, s ≤ p → p ≤ q → ∑ l ∈ Ico p q, ρ l = ∑ l ∈ Ico (p - s) (q - s), rStarVec (shiftBounds B s) l := by
      intro p q hp hpq
      obtain ⟨p, rfl⟩ : ∃ p', p = s + p' := ⟨p - s, by omega⟩
      obtain ⟨q, rfl⟩ : ∃ q', q = s + q' := ⟨q - s, by omega⟩
      rw [sum_Ico_shift]
      simp [hρ]
    obtain ⟨r', hr', hr'in⟩ := exists_feasible_extend (B := B) (S := S) (s := s) (t := s + n) (r := ρ) (by
      intro p q hp hpq hq
      rw [hsum p q hp hpq.le]
      have := rStarVec_feasible (shiftBounds B s) (q - s + 1) (p - s) (q - s) (by omega) (Nat.lt_succ_self _)
      have hB : shiftBounds B s (p - s) (q - s) = B p q := by
        unfold shiftBounds
        rw [show s + (p - s) = p by omega, show s + (q - s) = q by omega]
      rwa [hB] at this)
    refine ⟨r', hr', ?_⟩
    change ∑ l ∈ Ico s (s + n), r' l = _
    rw [sum_congr rfl fun l hl => hr'in l (mem_Ico.1 hl).1 (mem_Ico.1 hl).2, hsum s (s + n) le_rfl (by omega),
      Nat.sub_self, Nat.add_sub_cancel_left, Nat.Ico_zero_eq_range]
  · rintro _ ⟨r, hr, rfl⟩
    have hfeas : Feasible (n + 1) (shiftBounds B s) fun l => r (s + l) := by
      intro p q hpq hq
      have := hr (s + p) (s + q) (by omega) (by omega)
      rwa [sum_Ico_shift] at this
    have := sum_rStarVec_le hfeas
    change _ ≤ ∑ l ∈ Ico s (s + n), r l
    have hEq : ∑ l ∈ Ico s (s + n), r l = ∑ l ∈ range n, r (s + l) := by
      have := sum_Ico_shift r s 0 n
      simpa using this
    rw [hEq]
    exact this

/-- `R_st` is a lower bound on the events between `s` and `t` in any vector satisfying the system. -/
theorem algorithm1_le_sum (B : ℕ → ℕ → ℕ) {S s t : ℕ} (hst : s ≤ t) (ht : t < S) {r : ℕ → ℕ} (hr : Feasible S B r) :
    algorithm1 B S s t ≤ ∑ l ∈ Ico s t, r l :=
  (algorithm1_isOptimalValue B hst ht).2 ⟨r, hr, rfl⟩

/-- **The particular solution of the top row** (`ext:mg_top_row`). The vector of Proposition 6 is recovered by subtracting consecutive elements of the top row: `r_j = R_{1(j+1)} - R_{1j}`, in the source's numbering. "A particular optimal solution vector can then be recovered by subtracting consecutive elements of the row `R_1·`". -/
theorem algorithm1_top_row (B : ℕ → ℕ → ℕ) {S k : ℕ} (hk : k < S) : algorithm1 B S 0 k = ∑ l ∈ range k, rStarVec B l :=
  IsGreatest.unique (algorithm1_isChainMax (Nat.zero_le k) hk) (corollary8 B k)

theorem rStarVec_eq_sub (B : ℕ → ℕ → ℕ) {S k : ℕ} (hk : k + 1 < S) : rStarVec B k = algorithm1 B S 0 (k + 1) - algorithm1 B S 0 k := by
  rw [algorithm1_top_row B hk, algorithm1_top_row B (Nat.lt_of_succ_lt hk), sum_range_succ]
  omega

/-- **The placement from the top row is as far to the right as possible** (`ext:mg_rightmost`): "this particular solution results in the placement of all recombination events as far to the right along the sequence as possible". Up to any site, any vector satisfying the system has at least as many events. -/
theorem sum_rStarVec_le_of_feasible {S : ℕ} {r : ℕ → ℕ} (hr : Feasible S B r) {k : ℕ} (hk : k < S) : ∑ l ∈ range k, rStarVec B l ≤ ∑ l ∈ range k, r l :=
  sum_rStarVec_le (hr.mono hk)

/-- **The optimal bounds are tight in all optimal solutions** (`ext:mg_tight`): "since these bounds are exactly satisfied by one optimal solution, they must be satisfied in all optimal solutions". If the sum along a chain from `a` to `t` is the number of events of `r` between them, each step of the chain is an equality. -/
theorem sum_eq_of_chainSum_eq {S a t : ℕ} {l : List ℕ} {r : ℕ → ℕ} (hr : Feasible S B r) (h : IsChainTo a t l) (ht : t < S)
    (heq : chainSum B a l = ∑ m ∈ Ico a t, r m) {b c : ℕ} (hzip : (b, c) ∈ (a :: l).zip l) : B b c = ∑ m ∈ Ico b c, r m := by
  induction l generalizing a with
  | nil => simp at hzip
  | cons d l ih =>
    have hdt := h.2.le
    have h₁ := hr a d h.1 (hdt.trans_lt ht)
    have h₂ := chainSum_le_sum hr h.2 ht
    have hsplit := sum_Ico_consecutive r h.1.le hdt
    have hc : chainSum B a (d :: l) = B a d + chainSum B d l := rfl
    have hs : B a d = ∑ m ∈ Ico a d, r m ∧ chainSum B d l = ∑ m ∈ Ico d t, r m := by omega
    rw [List.zip_cons_cons, List.mem_cons] at hzip
    rcases hzip with heqp | hzip
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj heqp
      exact hs.1
    · rcases l with - | ⟨e, l⟩
      · simp at hzip
      · exact ih h.2 hs.2 hzip

/-- Larger local bounds give a larger value. So `R_m ≤ R_h ≤ R_s`, once their local bounds compare. -/
theorem algorithm1_mono {B B' : ℕ → ℕ → ℕ} {S s t : ℕ} (hB : ∀ i j, i < j → j < S → B i j ≤ B' i j) (hst : s ≤ t) (ht : t < S) :
    algorithm1 B S s t ≤ algorithm1 B' S s t := by
  obtain ⟨⟨r, hr, hsum⟩, -⟩ := algorithm1_isOptimalValue B' hst ht
  have hr' : Feasible S B r := fun i j hij hj => (hB i j hij hj).trans (hr i j hij hj)
  have := algorithm1_le_sum B hst ht hr'
  rw [← hsum]
  exact this

/-- A local bound is a lower bound on its region's value: "this illustrates how the algorithm can improve over using the local bounds alone". -/
theorem le_algorithm1 (B : ℕ → ℕ → ℕ) {S s t : ℕ} (hst : s < t) (ht : t < S) : B s t ≤ algorithm1 B S s t := by
  obtain ⟨⟨r, hr, hsum⟩, -⟩ := algorithm1_isOptimalValue B hst.le ht
  have := hr s t hst ht
  simp only at hsum
  omega

/-- **The composite bound for two regions** (`ext:mg_two_regions`). Regions that share at most an endpoint add up. -/
theorem algorithm1_add_le (B : ℕ → ℕ → ℕ) {S s k t : ℕ} (hsk : s ≤ k) (hkt : k ≤ t) (ht : t < S) :
    algorithm1 B S s k + algorithm1 B S k t ≤ algorithm1 B S s t := by
  obtain ⟨⟨r, hr, hsum⟩, -⟩ := algorithm1_isOptimalValue B (hsk.trans hkt) ht
  have h₁ := algorithm1_le_sum B hsk (hkt.trans_lt ht) hr
  have h₂ := algorithm1_le_sum B hkt ht hr
  simp only at hsum
  rw [← hsum, ← sum_Ico_consecutive r hsk hkt]
  exact add_le_add h₁ h₂

/-- **The solution from the right-hand column** (`ext:mg_right_column`): "by working in the other direction, we can equally subtract consecutive elements of the column `R_·S` to give another (not the same in general) optimal solution". -/
theorem isOptimalValue_column (B : ℕ → ℕ → ℕ) {T : ℕ} :
    Feasible (T + 1) B (fun l => algorithm1 B (T + 1) l T - algorithm1 B (T + 1) (l + 1) T) ∧
      ∑ l ∈ range T, (algorithm1 B (T + 1) l T - algorithm1 B (T + 1) (l + 1) T) = algorithm1 B (T + 1) 0 T := by
  have hmono : ∀ l, l < T → algorithm1 B (T + 1) (l + 1) T ≤ algorithm1 B (T + 1) l T := fun l hl => by
    have := algorithm1_add_le B (S := T + 1) (s := l) (k := l + 1) (t := T) (Nat.le_succ l) hl (Nat.lt_succ_self T)
    omega
  have htel : ∀ i j, i ≤ j → j ≤ T → ∑ l ∈ Ico i j, (algorithm1 B (T + 1) l T - algorithm1 B (T + 1) (l + 1) T) + algorithm1 B (T + 1) j T = algorithm1 B (T + 1) i T := by
    intro i j hij hj
    induction j, hij using Nat.le_induction with
    | base => simp
    | succ j hij ih =>
      rw [sum_Ico_succ_top hij]
      have h₁ := ih (by omega)
      have h₂ := hmono j (by omega)
      omega
  refine ⟨fun i j hij hj => ?_, ?_⟩
  · have hjT : j ≤ T := Nat.lt_succ_iff.1 hj
    have h₁ := htel i j hij.le hjT
    have h₂ := le_algorithm1 B (S := T + 1) hij hj
    have h₃ := algorithm1_add_le B (S := T + 1) hij.le hjT (Nat.lt_succ_self T)
    change B i j ≤ ∑ l ∈ Ico i j, (algorithm1 B (T + 1) l T - algorithm1 B (T + 1) (l + 1) T)
    omega
  · have := htel 0 T (Nat.zero_le T) le_rfl
    rw [algorithm1_self, add_zero, Nat.Ico_zero_eq_range] at this
    exact this

/-! ### The example of the source, pp. 381-382 -/

/-- A matrix given by its rows, with `0` outside them. -/
def ofRows (L : List (List ℕ)) : ℕ → ℕ → ℕ := fun i j => (L.getD i []).getD j 0

/-- `B^I` of (5). -/
def exampleBI : ℕ → ℕ → ℕ := ofRows [[0, 1, 1, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 0]]

/-- `B^H` of (5). -/
def exampleBH : ℕ → ℕ → ℕ := ofRows [[0, 1, 2, 3], [0, 0, 0, 2], [0, 0, 0, 1], [0, 0, 0, 0]]

/-- `B^S` of (6). -/
def exampleBS : ℕ → ℕ → ℕ := ofRows [[0, 1, 2, 4], [0, 0, 0, 2], [0, 0, 0, 1], [0, 0, 0, 0]]

/-- **The example of the source** (`ext:mg_example`): the values `R_m = 2`, `R_h = 3`, `R_s = 4`, with the solution vectors from the top row `(1, 0, 1)`, `(1, 1, 1)`, `(1, 1, 2)`. The source also has `R_h = 3` still when the local bound for `(1, 4)` drops to zero. -/
theorem example_values :
    algorithm1 exampleBI 4 0 3 = 2 ∧ algorithm1 exampleBH 4 0 3 = 3 ∧ algorithm1 exampleBS 4 0 3 = 4 ∧
      (List.range 3).map (rStarVec exampleBI) = [1, 0, 1] ∧ (List.range 3).map (rStarVec exampleBH) = [1, 1, 1] ∧
      (List.range 3).map (rStarVec exampleBS) = [1, 1, 2] ∧
      algorithm1 (ofRows [[0, 1, 2, 0], [0, 0, 0, 2], [0, 0, 0, 1], [0, 0, 0, 0]]) 4 0 3 = 3 := by
  decide +kernel

end MyersGriffiths2003
