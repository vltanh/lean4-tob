module

public import Phylogenetics.Tree.GeneTree.Basic
public import Mathlib.Data.Nat.Log
public import Mathlib.Data.List.GetD
public import Mathlib.Algebra.Order.Group.Nat
public import Mathlib.Data.Finset.Prod

/-!
# Lowest common ancestors on a gene tree

TOB-QMC (v5, embedded lines 602-605): "The qCFs for any four-taxon subset can be computed from gene trees on the fly in `O(k)` time using the
well-known binary lifting algorithm to retrieve the LCA of any pair of leaves in a gene tree in `O(1)` time. This requires a precomputation step with
time and storage complexity of `O(n log(n) k)`". This file models the data structures, with what they read.

**Binary lifting does not answer in `O(1)`.** Its table is that of `up`, the `2^j`-th ancestors, of `O(n log n)` entries, as the sentence says
(`up_eq_iterate`, `card_liftIndices`). Its query (`liftLCA`) is correct (`liftLCA_spec`), and loops over all `j`: it examines `O(log n)` entries, and no way of moving up by powers of two does better, on
a pair of depths differing by `2^J - 1` (`length_ge_of_sum_two_pow`). So with binary lifting the time per quartet and gene tree is `O(log n)`, and not `O(1)`.

**What gives the paper's numbers is a sparse table**, on the leaves in left-to-right order. The depth of the LCA of two leaves is the minimum over the range between them of the
depths at the LCAs of adjacent leaves (`isRangeMin_gaps`), and a table of the minima on ranges of length `2^h` answers a range minimum by reading two entries (`rangeQuery`,
`isRangeMin_rangeQuery`, `rangeQuery_reads`). The table has `n (log₂ n + 1)` entries, each from two others (`card_sparseIndices`).

**Quartets from LCAs.** Whether a gene tree displays `ab|ce` is decided by comparing the depths of five LCAs (`displays_iff_lcaDepth`), so a constant number of queries per gene
tree and quartet tree, which with `TOBQMC.sum_card_evaluations` is `O(k)` per four-taxon subset.
-/

@[expose] public section

open Finset

namespace Phylogenetics

namespace LCA

/-! ### Range minima -/

/-- `v` is the minimum of `a` on `[i, j)`. -/
def IsRangeMin (a : ℕ → ℕ) (i j v : ℕ) : Prop :=
  (∀ t, i ≤ t → t < j → v ≤ a t) ∧ ∃ t, i ≤ t ∧ t < j ∧ a t = v

theorem IsRangeMin.unique {a : ℕ → ℕ} {i j v w : ℕ} (hv : IsRangeMin a i j v) (hw : IsRangeMin a i j w) : v = w := by
  obtain ⟨hv₁, t, ht₁, ht₂, rfl⟩ := hv
  obtain ⟨hw₁, s, hs₁, hs₂, rfl⟩ := hw
  exact le_antisymm (hv₁ s hs₁ hs₂) (hw₁ t ht₁ ht₂)

/-- Two ranges that cover a range: the minimum is the smaller of their minima. -/
theorem IsRangeMin.min {a : ℕ → ℕ} {i j₁ i₂ j v w : ℕ} (hv : IsRangeMin a i j₁ v) (hw : IsRangeMin a i₂ j w) (h₁ : i ≤ i₂)
    (h₂ : j₁ ≤ j) (h₃ : i₂ ≤ j₁) : IsRangeMin a i j (Min.min v w) := by
  obtain ⟨hv₁, s, hs₁, hs₂, hs₃⟩ := hv
  obtain ⟨hw₁, t, ht₁, ht₂, ht₃⟩ := hw
  refine ⟨fun u hu₁ hu₂ => ?_, ?_⟩
  · by_cases hu : u < j₁
    · exact (min_le_left _ _).trans (hv₁ u hu₁ hu)
    · exact (min_le_right _ _).trans (hw₁ u (by omega) hu₂)
  · rcases le_total v w with hvw | hvw
    · exact ⟨s, hs₁, by omega, by rw [min_eq_left hvw]; exact hs₃⟩
    · exact ⟨t, by omega, ht₂, by rw [min_eq_right hvw]; exact ht₃⟩

/-! ### The sparse table -/

/-- The sparse table of the array `a`: `sparse a h i` is the minimum on the `2^h` positions from `i`, computed from two entries of the row before. -/
def sparse (a : ℕ → ℕ) : ℕ → ℕ → ℕ
  | 0, i => a i
  | h + 1, i => Min.min (sparse a h i) (sparse a h (i + 2 ^ h))

theorem isRangeMin_sparse (a : ℕ → ℕ) (h i : ℕ) : IsRangeMin a i (i + 2 ^ h) (sparse a h i) := by
  induction h generalizing i with
  | zero =>
    exact ⟨fun t h₁ h₂ => by
      have : t = i := by simp at h₂; omega
      rw [this]; rfl, i, le_rfl, by simp, rfl⟩
  | succ h ih =>
    have h₁ := ih i
    have h₂ := ih (i + 2 ^ h)
    have hp : i + 2 ^ h + 2 ^ h = i + 2 ^ (h + 1) := by rw [pow_succ]; omega
    rw [hp] at h₂
    have hpos : 0 < 2 ^ h := Nat.two_pow_pos h
    exact h₁.min h₂ (by omega) (by rw [pow_succ]; omega) le_rfl

/-- **The query**: the minimum on `[i, j)`, for `i < j`, from the two entries that cover the range with length `2^h`, where `2^h ≤ j - i < 2^(h+1)`. -/
def rangeQuery (a : ℕ → ℕ) (i j : ℕ) : ℕ :=
  Min.min (sparse a (Nat.log 2 (j - i)) i) (sparse a (Nat.log 2 (j - i)) (j - 2 ^ Nat.log 2 (j - i)))

/-- The entries of the table that the query reads. -/
def rangeQueryReads (i j : ℕ) : List (ℕ × ℕ) :=
  [(Nat.log 2 (j - i), i), (Nat.log 2 (j - i), j - 2 ^ Nat.log 2 (j - i))]

theorem isRangeMin_rangeQuery (a : ℕ → ℕ) {i j : ℕ} (hij : i < j) : IsRangeMin a i j (rangeQuery a i j) := by
  have hne : j - i ≠ 0 := by omega
  have hle : 2 ^ Nat.log 2 (j - i) ≤ j - i := Nat.pow_log_le_self 2 hne
  have hlt : j - i < 2 ^ (Nat.log 2 (j - i) + 1) := Nat.lt_pow_succ_log_self Nat.one_lt_two _
  rw [pow_succ] at hlt
  have h₁ := isRangeMin_sparse a (Nat.log 2 (j - i)) i
  have h₂ := isRangeMin_sparse a (Nat.log 2 (j - i)) (j - 2 ^ Nat.log 2 (j - i))
  rw [Nat.sub_add_cancel (by omega)] at h₂
  exact h₁.min h₂ (by omega) (by omega) (by omega)

/-- The indices of the table for an array of length `n`. -/
def sparseIndices (n : ℕ) : Finset (ℕ × ℕ) := range (Nat.log 2 n + 1) ×ˢ range n

/-- **The storage of the table**: `n (log₂ n + 1)` entries. Each is computed from two others, by `sparse`, so this is its time too. -/
theorem card_sparseIndices (n : ℕ) : (sparseIndices n).card = (Nat.log 2 n + 1) * n := by
  simp [sparseIndices]

/-- **The query reads two entries of the table**, whose indices are in the table. -/
theorem rangeQuery_reads {n i j : ℕ} (hij : i < j) (hj : j ≤ n) :
    (rangeQueryReads i j).length = 2 ∧ ∀ r ∈ rangeQueryReads i j, r ∈ sparseIndices n := by
  have hne : j - i ≠ 0 := by omega
  have hle : 2 ^ Nat.log 2 (j - i) ≤ j - i := Nat.pow_log_le_self 2 hne
  have hpos : 0 < 2 ^ Nat.log 2 (j - i) := Nat.two_pow_pos _
  have hlog : Nat.log 2 (j - i) ≤ Nat.log 2 n := Nat.log_mono_right (by omega)
  refine ⟨rfl, fun r hr => ?_⟩
  simp only [rangeQueryReads, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl <;> simp only [sparseIndices, mem_product, mem_range] <;> omega

/-! ### Binary lifting -/

section Lifting

variable {V : Type*}

/-- The table of binary lifting: `up parent j v` is the `2^j`-th ancestor of `v`, computed from two entries of the row before. -/
def up (parent : V → V) : ℕ → V → V
  | 0, v => parent v
  | j + 1, v => up parent j (up parent j v)

theorem up_eq_iterate (parent : V → V) (j : ℕ) (v : V) : up parent j v = parent^[2 ^ j] v := by
  induction j generalizing v with
  | zero => simp [up]
  | succ j ih =>
    rw [up, ih, ih, ← Function.iterate_add_apply]
    congr 1
    rw [pow_succ]
    omega

/-- The indices of the table for `N` vertices, with `J + 1` rows. -/
def liftIndices [DecidableEq V] (U : Finset V) (J : ℕ) : Finset (ℕ × V) := range (J + 1) ×ˢ U

/-- **The storage of binary lifting**: `(J + 1) N` entries, which is `O(n log n)` when `J = ⌊log₂ N⌋`. -/
theorem card_liftIndices [DecidableEq V] (U : Finset V) (J : ℕ) : (liftIndices U J).card = (J + 1) * U.card := by
  simp [liftIndices]

variable (parent : V → V) (depth : V → ℕ)

/-- A rooted tree given by parents and depths: going to the parent lowers the depth by one, except at the root, the only vertex of depth `0`, which is its own parent. -/
structure IsRootedTree [DecidableEq V] : Prop where
  parent_depth : ∀ v, depth v ≠ 0 → depth (parent v) + 1 = depth v
  parent_root : ∀ v, depth v = 0 → parent v = v
  root_unique : ∀ u v, depth u = 0 → depth v = 0 → u = v

variable {parent depth}
variable [DecidableEq V]

theorem IsRootedTree.depth_iterate (h : IsRootedTree parent depth) (k : ℕ) (v : V) :
    depth (parent^[k] v) = depth v - k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    by_cases hd : depth (parent^[k] v) = 0
    · rw [h.parent_root _ hd, ih] at *
      omega
    · have := h.parent_depth _ hd
      omega

variable (parent depth) in
/-- Step 1 of the query, the row `j`: if the vertex is above its target depth by at least `2^j`, take the jump. -/
def liftStep (target : ℕ) (j : ℕ) (u : V) : V :=
  if target + 2 ^ j ≤ depth u then up parent j u else u

variable (parent depth) in
/-- Step 1 of the query: bring `u` to the depth `target`, looping over the rows from `J` to `0`. -/
def liftTo (target : ℕ) : ℕ → V → V
  | 0, u => u
  | j + 1, u => liftTo target j (liftStep parent depth target j u)

theorem liftTo_spec (h : IsRootedTree parent depth) {target : ℕ} (J : ℕ) {u : V} (h₁ : target ≤ depth u)
    (h₂ : depth u - target < 2 ^ J) : liftTo parent depth target J u = parent^[depth u - target] u := by
  induction J generalizing u with
  | zero =>
    have : depth u - target = 0 := by simpa using h₂
    simp [liftTo, this]
  | succ J ih =>
    rw [liftTo, liftStep]
    split_ifs with hstep
    · have hd : depth (up parent J u) = depth u - 2 ^ J := by
        rw [up_eq_iterate, h.depth_iterate]
      have hrem : depth u - 2 ^ J - target < 2 ^ J := by
        rw [pow_succ] at h₂
        omega
      have hstep' : target + 2 ^ J ≤ depth u := hstep
      rw [ih (by rw [hd]; omega) (by rw [hd]; exact hrem), hd, up_eq_iterate, ← Function.iterate_add_apply]
      congr 1
      omega
    · have hrem : depth u - target < 2 ^ J := by omega
      exact ih h₁ hrem

variable (parent) in
/-- Step 2 of the query, from the rows `J` to `0`: for vertices at the same depth, jump both while the jumps do not meet. -/
def meet : ℕ → V → V → V × V
  | 0, u, v => (u, v)
  | j + 1, u, v => if up parent j u ≠ up parent j v then meet j (up parent j u) (up parent j v) else meet j u v

omit [DecidableEq V] in
/-- Above the point where two vertices meet, their ancestors stay equal. -/
theorem iterate_eq_of_le {u v : V} {a b : ℕ} (hab : a ≤ b) (h : parent^[a] u = parent^[a] v) :
    parent^[b] u = parent^[b] v := by
  obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_le hab
  rw [add_comm, Function.iterate_add_apply, Function.iterate_add_apply, h]

/-- After the rows `J` to `0`, if two different vertices meet within `2^J` steps, they have moved up equally, stay different, and have the same parent. -/
theorem meet_spec {J : ℕ} {u v : V} (hne : u ≠ v) (h : parent^[2 ^ J] u = parent^[2 ^ J] v) :
    ∃ k, (meet parent J u v).1 = parent^[k] u ∧ (meet parent J u v).2 = parent^[k] v ∧
      (meet parent J u v).1 ≠ (meet parent J u v).2 ∧ parent (meet parent J u v).1 = parent (meet parent J u v).2 := by
  induction J generalizing u v with
  | zero => exact ⟨0, rfl, rfl, hne, by simpa [meet] using h⟩
  | succ J ih =>
    rw [meet]
    split_ifs with hjump
    · have h' : parent^[2 ^ J] (up parent J u) = parent^[2 ^ J] (up parent J v) := by
        rw [up_eq_iterate, up_eq_iterate, ← Function.iterate_add_apply, ← Function.iterate_add_apply]
        rwa [show 2 ^ J + 2 ^ J = 2 ^ (J + 1) by rw [pow_succ]; omega]
      obtain ⟨k, hk₁, hk₂, h₁, h₂⟩ := ih hjump h'
      refine ⟨k + 2 ^ J, ?_, ?_, h₁, h₂⟩
      · rw [hk₁, up_eq_iterate, ← Function.iterate_add_apply]
      · rw [hk₂, up_eq_iterate, ← Function.iterate_add_apply]
    · have heq : up parent J u = up parent J v := not_not.1 hjump
      rw [up_eq_iterate, up_eq_iterate] at heq
      exact ih hne heq

variable (parent depth) in
/-- **The query of binary lifting**, with `J + 1` rows: bring both vertices to the same depth, and if they differ, jump both while the jumps do not meet, and take the parent. -/
def liftLCA (J : ℕ) (u v : V) : V :=
  let d := Min.min (depth u) (depth v)
  let u' := liftTo parent depth d (J + 1) u
  let v' := liftTo parent depth d (J + 1) v
  if u' = v' then u' else parent (meet parent (J + 1) u' v').1

/-- `w` is the lowest common ancestor of `u` and `v`: a common ancestor, of the largest depth. -/
def IsLCA (parent : V → V) (depth : V → ℕ) (u v w : V) : Prop :=
  (∃ a, parent^[a] u = w) ∧ (∃ b, parent^[b] v = w) ∧
    ∀ x, (∃ a, parent^[a] u = x) → (∃ b, parent^[b] v = x) → depth x ≤ depth w

/-- An ancestor is the ancestor at the difference of the depths. -/
theorem IsRootedTree.iterate_depth_sub (h : IsRootedTree parent depth) {u : V} {a : ℕ} :
    parent^[depth u - depth (parent^[a] u)] u = parent^[a] u := by
  rw [h.depth_iterate]
  by_cases ha : a ≤ depth u
  · rw [show depth u - (depth u - a) = a by omega]
  · rw [show depth u - (depth u - a) = depth u by omega]
    refine h.root_unique _ _ ?_ ?_ <;> rw [h.depth_iterate] <;> omega

/-- **Binary lifting is correct**, with `J + 2` rows for depths below `2^(J+1)`. -/
theorem liftLCA_spec (h : IsRootedTree parent depth) {J : ℕ} {u v : V} (hu : depth u < 2 ^ (J + 1)) (hv : depth v < 2 ^ (J + 1)) :
    IsLCA parent depth u v (liftLCA parent depth J u v) := by
  set d := Min.min (depth u) (depth v) with hd
  have hdu : d ≤ depth u := min_le_left _ _
  have hdv : d ≤ depth v := min_le_right _ _
  have hdlt : d < 2 ^ (J + 1) := lt_of_le_of_lt hdu hu
  have hu' : liftTo parent depth d (J + 1) u = parent^[depth u - d] u := liftTo_spec h _ hdu (by omega)
  have hv' : liftTo parent depth d (J + 1) v = parent^[depth v - d] v := liftTo_spec h _ hdv (by omega)
  have hval : liftLCA parent depth J u v =
      if parent^[depth u - d] u = parent^[depth v - d] v then parent^[depth u - d] u
      else parent (meet parent (J + 1) (parent^[depth u - d] u) (parent^[depth v - d] v)).1 := by
    simp only [liftLCA, ← hd, hu', hv']
  rw [hval]
  set x := parent^[depth u - d] u with hx
  set y := parent^[depth v - d] v with hy
  have hdx : depth x = d := by
    rw [hx, h.depth_iterate]
    omega
  have hdy : depth y = d := by
    rw [hy, h.depth_iterate]
    omega
  have hxanc : ∀ i, parent^[i] x = parent^[i + (depth u - d)] u := fun i => by
    rw [hx, ← Function.iterate_add_apply]
  have hyanc : ∀ i, parent^[i] y = parent^[i + (depth v - d)] v := fun i => by
    rw [hy, ← Function.iterate_add_apply]
  -- a common ancestor is at the same distance from `x` and `y`, of depth at most `d`
  have hcommon : ∀ z, (∃ a, parent^[a] u = z) → (∃ b, parent^[b] v = z) →
      depth z ≤ d ∧ parent^[d - depth z] x = z ∧ parent^[d - depth z] y = z := by
    rintro z ⟨a, ha⟩ ⟨b, hb⟩
    have hza : depth z ≤ depth u := by
      rw [← ha, h.depth_iterate]
      omega
    have hzb : depth z ≤ depth v := by
      rw [← hb, h.depth_iterate]
      omega
    have hzd : depth z ≤ d := le_min hza hzb
    refine ⟨hzd, ?_, ?_⟩
    · rw [hxanc, show d - depth z + (depth u - d) = depth u - depth z by omega]
      have := h.iterate_depth_sub (u := u) (a := a)
      rwa [ha] at this
    · rw [hyanc, show d - depth z + (depth v - d) = depth v - depth z by omega]
      have := h.iterate_depth_sub (u := v) (a := b)
      rwa [hb] at this
  split_ifs with hxy
  · refine ⟨⟨_, rfl⟩, ⟨_, by rw [← hy]; exact hxy.symm⟩, fun z hz₁ hz₂ => ?_⟩
    rw [hdx]
    exact (hcommon z hz₁ hz₂).1
  · have hroot : parent^[2 ^ (J + 1)] x = parent^[2 ^ (J + 1)] y := by
      refine h.root_unique _ _ ?_ ?_ <;> rw [h.depth_iterate] <;> omega
    obtain ⟨k, hk₁, hk₂, hne, hpar⟩ := meet_spec hxy hroot
    set w := parent (meet parent (J + 1) x y).1 with hw
    have hwx : w = parent^[k + 1] x := by
      rw [hw, hk₁, Function.iterate_succ_apply']
    have hwy : w = parent^[k + 1] y := by
      rw [hpar, hk₂, Function.iterate_succ_apply']
    have hdp : depth (parent^[k] x) ≠ 0 := by
      intro h0
      have h1 : depth (parent^[k] y) = 0 := by
        rw [h.depth_iterate] at h0 ⊢
        omega
      rw [hk₁, hk₂] at hne
      exact hne (h.root_unique _ _ h0 h1)
    have hdk : k < d := by
      rw [h.depth_iterate, hdx] at hdp
      omega
    have hdw : depth w = d - (k + 1) := by
      rw [hwx, h.depth_iterate, hdx]
    refine ⟨⟨k + 1 + (depth u - d), by rw [← hxanc, hwx]⟩, ⟨k + 1 + (depth v - d), by rw [← hyanc, hwy]⟩, fun z hz₁ hz₂ => ?_⟩
    obtain ⟨hzd, hzx, hzy⟩ := hcommon z hz₁ hz₂
    have hgt : k < d - depth z := by
      by_contra hle
      refine hne ?_
      rw [hk₁, hk₂]
      exact iterate_eq_of_le (not_lt.1 hle) (hzx.trans hzy.symm)
    rw [hdw]
    omega

/-- The sum of the binary digits. -/
def bitSum (n : ℕ) : ℕ := if h : n = 0 then 0 else n % 2 + bitSum (n / 2)
decreasing_by exact Nat.div_lt_self (Nat.pos_of_ne_zero h) Nat.one_lt_two

theorem bitSum_eq (n : ℕ) : bitSum n = n % 2 + bitSum (n / 2) := by
  by_cases h : n = 0
  · subst h
    simp
  · rw [bitSum, dite_eq_right h]

theorem bitSum_zero : bitSum 0 = 0 := by
  rw [bitSum, dite_eq_left rfl]

theorem bitSum_add_le (x y : ℕ) : bitSum (x + y) ≤ bitSum x + bitSum y := by
  induction hn : x + y using Nat.strong_induction_on generalizing x y with
  | _ n ih =>
    by_cases hn0 : n = 0
    · subst hn0
      rw [bitSum_zero]
      exact Nat.zero_le _
    rw [bitSum_eq n, bitSum_eq x, bitSum_eq y]
    have hmod : x % 2 = 0 ∨ x % 2 = 1 := by omega
    have hmod' : y % 2 = 0 ∨ y % 2 = 1 := by omega
    rcases hmod with hx | hx <;> rcases hmod' with hy | hy
    · have h₁ : n % 2 = 0 := by omega
      have h₂ : n / 2 = x / 2 + y / 2 := by omega
      have := ih (n / 2) (by omega) (x / 2) (y / 2) h₂.symm
      omega
    · have h₁ : n % 2 = 1 := by omega
      have h₂ : n / 2 = x / 2 + y / 2 := by omega
      have := ih (n / 2) (by omega) (x / 2) (y / 2) h₂.symm
      omega
    · have h₁ : n % 2 = 1 := by omega
      have h₂ : n / 2 = x / 2 + y / 2 := by omega
      have := ih (n / 2) (by omega) (x / 2) (y / 2) h₂.symm
      omega
    · have h₁ : n % 2 = 0 := by omega
      have h₂ : n / 2 = (x / 2 + y / 2) + 1 := by omega
      have h₃ := ih (n / 2) (by omega) (x / 2 + y / 2) 1 h₂.symm
      have h₄ := ih (x / 2 + y / 2) (by omega) (x / 2) (y / 2) rfl
      have h₅ : bitSum 1 = 1 := by
        rw [bitSum_eq 1]
        simp [bitSum_zero]
      omega

theorem bitSum_two_pow (e : ℕ) : bitSum (2 ^ e) = 1 := by
  induction e with
  | zero =>
    rw [pow_zero, bitSum_eq 1]
    simp [bitSum_zero]
  | succ e ih =>
    rw [bitSum_eq, show 2 ^ (e + 1) % 2 = 0 by rw [pow_succ]; omega,
      show 2 ^ (e + 1) / 2 = 2 ^ e by rw [pow_succ]; omega, ih]

theorem bitSum_two_pow_sub_one (J : ℕ) : bitSum (2 ^ J - 1) = J := by
  induction J with
  | zero => simp [bitSum_zero]
  | succ J ih =>
    have hpos : 0 < 2 ^ J := Nat.two_pow_pos J
    rw [bitSum_eq, show (2 ^ (J + 1) - 1) % 2 = 1 by rw [pow_succ]; omega,
      show (2 ^ (J + 1) - 1) / 2 = 2 ^ J - 1 by rw [pow_succ]; omega, ih]
    omega

/-- **No way of moving up by powers of two avoids `log` many jumps.** A sequence of jumps of lengths `2^e` that moves a vertex up by `2^J - 1` has at least `J` jumps, and
each reads an entry of the table. Two leaves of a caterpillar gene tree on more than `2^J` leaves have depths differing by `2^J - 1`, so to bring them to the same depth, binary lifting reads at least `J` entries. -/
theorem length_ge_of_sum_two_pow {l : List ℕ} {J : ℕ} (h : (l.map fun e => 2 ^ e).sum = 2 ^ J - 1) : J ≤ l.length := by
  have key : ∀ l : List ℕ, bitSum (l.map fun e => 2 ^ e).sum ≤ l.length := by
    intro l
    induction l with
    | nil => simp [bitSum_zero]
    | cons e l ih =>
      simp only [List.map_cons, List.sum_cons, List.length_cons]
      have := bitSum_add_le (2 ^ e) (l.map fun e => 2 ^ e).sum
      rw [bitSum_two_pow] at this
      omega
  have := key l
  rwa [h, bitSum_two_pow_sub_one] at this

end Lifting

end LCA

/-! ### On a gene tree -/

namespace GeneTree

open LCA

variable {X : Type*} [DecidableEq X]

/-- The depth of the lowest common ancestor of the taxa `a`, `b` in a gene tree. -/
def lcaDepth : GeneTree X → X → X → ℕ
  | leaf _, _, _ => 0
  | node l r, a, b =>
    if a ∈ l.leaves ∧ b ∈ l.leaves then lcaDepth l a b + 1
    else if a ∈ r.leaves ∧ b ∈ r.leaves then lcaDepth r a b + 1 else 0

/-- The depths of the lowest common ancestors of adjacent leaves, from left to right. -/
def gaps : GeneTree X → List ℕ
  | leaf _ => []
  | node l r => (gaps l).map (· + 1) ++ 0 :: (gaps r).map (· + 1)

/-- The array of `gaps`. -/
def gapAt (t : GeneTree X) (i : ℕ) : ℕ := (gaps t).getD i 0

omit [DecidableEq X] in
theorem length_gaps (t : GeneTree X) : (gaps t).length + 1 = t.leaves.length := by
  induction t with
  | leaf x => simp [gaps, leaves]
  | node l r ihl ihr =>
    simp only [gaps, leaves, List.length_append, List.length_map, List.length_cons]
    omega

omit [DecidableEq X] in
theorem gapAt_node_left {l r : GeneTree X} {i : ℕ} (hi : i < (gaps l).length) :
    gapAt (node l r) i = gapAt l i + 1 := by
  simp only [gapAt, gaps]
  rw [List.getD_append _ _ _ _ (by simpa using hi), List.getD_eq_getElem _ _ (by simpa using hi),
    List.getD_eq_getElem _ _ hi]
  simp

omit [DecidableEq X] in
theorem gapAt_node_mid (l r : GeneTree X) : gapAt (node l r) (gaps l).length = 0 := by
  simp only [gapAt, gaps]
  rw [List.getD_append_right _ _ _ _ (by simp)]
  simp

omit [DecidableEq X] in
theorem gapAt_node_right (l r : GeneTree X) {i : ℕ} (hi : i < (gaps r).length) :
    gapAt (node l r) ((gaps l).length + 1 + i) = gapAt r i + 1 := by
  simp only [gapAt, gaps]
  rw [List.getD_append_right _ _ _ _ (by simp; omega)]
  have : (gaps l).length + 1 + i - ((gaps l).map (· + 1)).length = i + 1 := by simp; omega
  rw [this, List.getD_cons_succ, List.getD_eq_getElem _ _ (by simpa using hi), List.getD_eq_getElem _ _ hi]
  simp

/-- **The depth of the LCA of two leaves is the range minimum of `gaps` between them.** -/
theorem isRangeMin_gaps {t : GeneTree X} (ht : t.leaves.Nodup) {a b : X} (ha : a ∈ t.leaves) (hb : b ∈ t.leaves)
    (hlt : t.leaves.idxOf a < t.leaves.idxOf b) :
    IsRangeMin (gapAt t) (t.leaves.idxOf a) (t.leaves.idxOf b) (lcaDepth t a b) := by
  induction t with
  | leaf x =>
    simp only [leaves, List.mem_singleton] at ha hb
    subst ha
    subst hb
    exact absurd hlt (lt_irrefl _)
  | node l r ihl ihr =>
    have hnd : (l.leaves ++ r.leaves).Nodup := ht
    have hl := (List.nodup_append.1 hnd).1
    have hr := (List.nodup_append.1 hnd).2.1
    have hdisj : ∀ x, x ∈ l.leaves → x ∉ r.leaves := fun x hxl hxr =>
      (List.nodup_append.1 hnd).2.2 x hxl x hxr rfl
    have hlen := length_gaps l
    have hmem : ∀ {x}, x ∈ (node l r).leaves → x ∈ l.leaves ∨ x ∈ r.leaves := fun {x} hx => by
      simpa [leaves] using hx
    have hidxl : ∀ {x}, x ∈ l.leaves → (node l r).leaves.idxOf x = l.leaves.idxOf x := fun hx => by
      simp only [leaves]
      exact List.idxOf_append_of_mem hx
    have hidxr : ∀ {x}, x ∈ r.leaves → (node l r).leaves.idxOf x = (gaps l).length + 1 + r.leaves.idxOf x := fun {x} hx => by
      simp only [leaves]
      rw [List.idxOf_append_of_notMem (fun h => hdisj x h hx)]
      omega
    have hltl : ∀ {x}, x ∈ l.leaves → l.leaves.idxOf x ≤ (gaps l).length := fun hx => by
      have := List.idxOf_lt_length_of_mem hx
      omega
    rcases hmem ha with hal | har <;> rcases hmem hb with hbl | hbr
    · -- both on the left
      rw [hidxl hal, hidxl hbl] at hlt ⊢
      have hv : lcaDepth (node l r) a b = lcaDepth l a b + 1 := by
        simp [lcaDepth, hal, hbl]
      obtain ⟨h₁, s, hs₁, hs₂, hs₃⟩ := ihl hl hal hbl hlt
      have hb' := hltl hbl
      rw [hv]
      refine ⟨fun u hu₁ hu₂ => ?_, s, hs₁, hs₂, ?_⟩
      · rw [gapAt_node_left (by omega)]
        have := h₁ u hu₁ hu₂
        omega
      · rw [gapAt_node_left (by omega), hs₃]
    · -- across the root
      rw [hidxl hal, hidxr hbr] at hlt ⊢
      have hbl' : b ∉ l.leaves := fun h => hdisj b h hbr
      have hv : lcaDepth (node l r) a b = 0 := by
        simp [lcaDepth, hal, hdisj a hal, hbl']
      have ha' := hltl hal
      rw [hv]
      exact ⟨fun _ _ _ => Nat.zero_le _, (gaps l).length, ha', by omega, gapAt_node_mid l r⟩
    · -- a right position is not before a left one
      rw [hidxr har, hidxl hbl] at hlt
      have hb' := hltl hbl
      omega
    · -- both on the right
      rw [hidxr har, hidxr hbr] at hlt ⊢
      have hlt' : r.leaves.idxOf a < r.leaves.idxOf b := by omega
      have hal' : a ∉ l.leaves := fun h => hdisj a h har
      have hv : lcaDepth (node l r) a b = lcaDepth r a b + 1 := by
        simp [lcaDepth, har, hbr, hal']
      obtain ⟨h₁, s, hs₁, hs₂, hs₃⟩ := ihr hr har hbr hlt'
      have hbr' := List.idxOf_lt_length_of_mem hbr
      have hlenr := length_gaps r
      rw [hv]
      refine ⟨fun u hu₁ hu₂ => ?_, (gaps l).length + 1 + s, by omega, by omega, ?_⟩
      · obtain ⟨v, rfl⟩ : ∃ v, u = (gaps l).length + 1 + v := ⟨u - ((gaps l).length + 1), by omega⟩
        rw [gapAt_node_right l r (by omega)]
        have := h₁ v (by omega) (by omega)
        omega
      · rw [gapAt_node_right l r (by omega), hs₃]

theorem lcaDepth_comm (t : GeneTree X) (a b : X) : lcaDepth t a b = lcaDepth t b a := by
  induction t with
  | leaf x => rfl
  | node l r ihl ihr =>
    rw [lcaDepth, lcaDepth, ihl, ihr]
    simp only [and_comm (a := b ∈ l.leaves), and_comm (a := b ∈ r.leaves)]

/-- **The LCA query on a gene tree**: the range query on the positions of the two leaves. -/
def lcaQuery (t : GeneTree X) (a b : X) : ℕ :=
  if t.leaves.idxOf a < t.leaves.idxOf b then rangeQuery (gapAt t) (t.leaves.idxOf a) (t.leaves.idxOf b)
  else rangeQuery (gapAt t) (t.leaves.idxOf b) (t.leaves.idxOf a)

/-- **The query is right**: on two different leaves of a gene tree with distinct leaves, reading two entries of the sparse table of `gaps`, it returns the depth of their LCA. -/
theorem lcaQuery_eq {t : GeneTree X} (ht : t.leaves.Nodup) {a b : X} (ha : a ∈ t.leaves) (hb : b ∈ t.leaves) (hab : a ≠ b) :
    lcaQuery t a b = lcaDepth t a b := by
  have hne : t.leaves.idxOf a ≠ t.leaves.idxOf b := fun h => hab ((List.idxOf_inj ha).1 h)
  unfold lcaQuery
  split_ifs with h
  · exact (isRangeMin_rangeQuery _ h).unique (isRangeMin_gaps ht ha hb h)
  · have h' : t.leaves.idxOf b < t.leaves.idxOf a := by omega
    rw [lcaDepth_comm]
    exact (isRangeMin_rangeQuery _ h').unique (isRangeMin_gaps ht hb ha h')

/-- **A cluster with `a`, `b`, and without `c`, `e`** exists exactly when the LCA of `a`, `b` is lower than those of `a`, `c` and of `a`, `e`. -/
theorem exists_cluster_iff_lcaDepth {t : GeneTree X} (ht : t.leaves.Nodup) {a b c e : X} (ha : a ∈ t.leaves) (hb : b ∈ t.leaves)
    (hc : c ∈ t.leaves) (he : e ∈ t.leaves) (hab : a ≠ b) (hac : a ≠ c) (hae : a ≠ e) :
    (∃ C ∈ t.clusters, a ∈ C ∧ b ∈ C ∧ c ∉ C ∧ e ∉ C) ↔ lcaDepth t a c < lcaDepth t a b ∧ lcaDepth t a e < lcaDepth t a b := by
  induction t generalizing c e with
  | leaf x =>
    simp only [leaves, List.mem_singleton] at ha hb
    exact absurd (ha.trans hb.symm) hab
  | node l r ihl ihr =>
    have hnd : (l.leaves ++ r.leaves).Nodup := ht
    have hl := (List.nodup_append.1 hnd).1
    have hr := (List.nodup_append.1 hnd).2.1
    have hdisj : ∀ x, x ∈ l.leaves → x ∉ r.leaves := fun x hxl hxr =>
      (List.nodup_append.1 hnd).2.2 x hxl x hxr rfl
    have hmem : ∀ {x}, x ∈ (node l r).leaves → x ∈ l.leaves ∨ x ∈ r.leaves := fun {x} hx => by
      simpa [leaves] using hx
    -- the depth in each case
    have dLL : ∀ {x y}, x ∈ l.leaves → y ∈ l.leaves → lcaDepth (node l r) x y = lcaDepth l x y + 1 := fun hx hy => by
      simp [lcaDepth, hx, hy]
    have hdisj' : ∀ x, x ∈ r.leaves → x ∉ l.leaves := fun x hxr hxl => hdisj x hxl hxr
    have dRR : ∀ {x y}, x ∈ r.leaves → y ∈ r.leaves → lcaDepth (node l r) x y = lcaDepth r x y + 1 := fun {x y} hx hy => by
      simp [lcaDepth, hx, hy, hdisj' x hx]
    have dLR : ∀ {x y}, x ∈ l.leaves → y ∈ r.leaves → lcaDepth (node l r) x y = 0 := fun {x y} hx hy => by
      simp [lcaDepth, hx, hdisj x hx, hdisj' y hy]
    have dRL : ∀ {x y}, x ∈ r.leaves → y ∈ l.leaves → lcaDepth (node l r) x y = 0 := fun {x y} hx hy => by
      simp [lcaDepth, hx, hdisj y hy, hdisj' x hx]
    -- the clusters
    have hcl : ∀ {C}, C ∈ (node l r).clusters → C = l.leafSet ∪ r.leafSet ∨ C ∈ l.clusters ∨ C ∈ r.clusters := fun {C} hC => by
      simpa [clusters, Finset.mem_insert, Finset.mem_union] using hC
    have hsubL : ∀ {C x}, C ∈ l.clusters → x ∈ C → x ∈ l.leaves := fun hC hx =>
      mem_leafSet.1 (subset_leafSet_of_mem_clusters hC hx)
    have hsubR : ∀ {C x}, C ∈ r.clusters → x ∈ C → x ∈ r.leaves := fun hC hx =>
      mem_leafSet.1 (subset_leafSet_of_mem_clusters hC hx)
    have hclL : ∀ {C}, C ∈ l.clusters → C ∈ (node l r).clusters := fun hC => by
      simp [clusters, hC]
    have hclR : ∀ {C}, C ∈ r.clusters → C ∈ (node l r).clusters := fun hC => by
      simp [clusters, hC]
    have hroot : ∀ {x}, x ∈ (node l r).leaves → x ∈ l.leafSet ∪ r.leafSet := fun {x} hx => by
      rcases hmem hx with h | h
      · exact Finset.mem_union_left _ (mem_leafSet.2 h)
      · exact Finset.mem_union_right _ (mem_leafSet.2 h)
    rcases hmem ha with hal | har <;> rcases hmem hb with hbl | hbr
    · -- `a`, `b` on the left
      have hdab := dLL hal hbl
      rcases hmem hc with hcl' | hcr <;> rcases hmem he with hel | her
      · rw [hdab, dLL hal hcl', dLL hal hel, Nat.add_lt_add_iff_right, Nat.add_lt_add_iff_right,
          ← ihl hl hal hbl hcl' hel hac hae]
        constructor
        · rintro ⟨C, hC, h₁, h₂, h₃, h₄⟩
          rcases hcl hC with rfl | hC | hC
          · exact absurd (hroot hc) h₃
          · exact ⟨C, hC, h₁, h₂, h₃, h₄⟩
          · exact absurd (hsubR hC h₁) (hdisj a hal)
        · rintro ⟨C, hC, h⟩
          exact ⟨C, hclL hC, h⟩
      · rw [hdab, dLL hal hcl', dLR hal her, Nat.add_lt_add_iff_right]
        have hi := ihl hl hal hbl hcl' hcl' hac hac
        constructor
        · rintro ⟨C, hC, h₁, h₂, h₃, -⟩
          rcases hcl hC with rfl | hC | hC
          · exact absurd (hroot hc) h₃
          · exact ⟨(hi.1 ⟨C, hC, h₁, h₂, h₃, h₃⟩).1, Nat.succ_pos _⟩
          · exact absurd (hsubR hC h₁) (hdisj a hal)
        · rintro ⟨h₁, -⟩
          obtain ⟨C, hC, h₂, h₃, h₄, -⟩ := hi.2 ⟨h₁, h₁⟩
          exact ⟨C, hclL hC, h₂, h₃, h₄, fun h => hdisj e (hsubL hC h) her⟩
      · rw [hdab, dLR hal hcr, dLL hal hel, Nat.add_lt_add_iff_right]
        have hi := ihl hl hal hbl hel hel hae hae
        constructor
        · rintro ⟨C, hC, h₁, h₂, -, h₄⟩
          rcases hcl hC with rfl | hC | hC
          · exact absurd (hroot he) h₄
          · exact ⟨Nat.succ_pos _, (hi.1 ⟨C, hC, h₁, h₂, h₄, h₄⟩).1⟩
          · exact absurd (hsubR hC h₁) (hdisj a hal)
        · rintro ⟨-, h₁⟩
          obtain ⟨C, hC, h₂, h₃, h₄, -⟩ := hi.2 ⟨h₁, h₁⟩
          exact ⟨C, hclL hC, h₂, h₃, fun h => hdisj c (hsubL hC h) hcr, h₄⟩
      · rw [hdab, dLR hal hcr, dLR hal her]
        refine ⟨fun _ => ⟨Nat.succ_pos _, Nat.succ_pos _⟩, fun _ => ⟨l.leafSet, ?_, mem_leafSet.2 hal, mem_leafSet.2 hbl,
          fun h => hdisj c (mem_leafSet.1 h) hcr, fun h => hdisj e (mem_leafSet.1 h) her⟩⟩
        cases l with
        | leaf x => exact hclL (leafSet_mem_clusters _)
        | node l₁ l₂ => exact hclL (leafSet_mem_clusters _)
    · -- `a`, `b` on either side
      rw [dLR hal hbr]
      simp only [Nat.not_lt_zero, and_false, iff_false, not_exists, not_and]
      intro C hC h₁ h₂ h₃ h₄
      rcases hcl hC with rfl | hC | hC
      · exact h₃ (hroot hc)
      · exact hdisj b (hsubL hC h₂) hbr
      · exact hdisj a hal (hsubR hC h₁)
    · rw [dRL har hbl]
      simp only [Nat.not_lt_zero, and_false, iff_false, not_exists, not_and]
      intro C hC h₁ h₂ h₃ h₄
      rcases hcl hC with rfl | hC | hC
      · exact h₃ (hroot hc)
      · exact hdisj a (hsubL hC h₁) har
      · exact hdisj b hbl (hsubR hC h₂)
    · -- `a`, `b` on the right
      have hdab := dRR har hbr
      rcases hmem hc with hcl' | hcr <;> rcases hmem he with hel | her
      · rw [hdab, dRL har hcl', dRL har hel]
        refine ⟨fun _ => ⟨Nat.succ_pos _, Nat.succ_pos _⟩, fun _ => ⟨r.leafSet, hclR (leafSet_mem_clusters _), mem_leafSet.2 har, mem_leafSet.2 hbr,
          fun h => hdisj c hcl' (mem_leafSet.1 h), fun h => hdisj e hel (mem_leafSet.1 h)⟩⟩
      · rw [hdab, dRL har hcl', dRR har her, Nat.add_lt_add_iff_right]
        have hi := ihr hr har hbr her her hae hae
        constructor
        · rintro ⟨C, hC, h₁, h₂, -, h₄⟩
          rcases hcl hC with rfl | hC | hC
          · exact absurd (hroot he) h₄
          · exact absurd (hsubL hC h₁) (fun h => hdisj a h har)
          · exact ⟨Nat.succ_pos _, (hi.1 ⟨C, hC, h₁, h₂, h₄, h₄⟩).1⟩
        · rintro ⟨-, h₁⟩
          obtain ⟨C, hC, h₂, h₃, h₄, -⟩ := hi.2 ⟨h₁, h₁⟩
          exact ⟨C, hclR hC, h₂, h₃, fun h => hdisj c hcl' (hsubR hC h), h₄⟩
      · rw [hdab, dRR har hcr, dRL har hel, Nat.add_lt_add_iff_right]
        have hi := ihr hr har hbr hcr hcr hac hac
        constructor
        · rintro ⟨C, hC, h₁, h₂, h₃, -⟩
          rcases hcl hC with rfl | hC | hC
          · exact absurd (hroot hc) h₃
          · exact absurd (hsubL hC h₁) (fun h => hdisj a h har)
          · exact ⟨(hi.1 ⟨C, hC, h₁, h₂, h₃, h₃⟩).1, Nat.succ_pos _⟩
        · rintro ⟨h₁, -⟩
          obtain ⟨C, hC, h₂, h₃, h₄, -⟩ := hi.2 ⟨h₁, h₁⟩
          exact ⟨C, hclR hC, h₂, h₃, h₄, fun h => hdisj e hel (hsubR hC h)⟩
      · rw [hdab, dRR har hcr, dRR har her, Nat.add_lt_add_iff_right, Nat.add_lt_add_iff_right,
          ← ihr hr har hbr hcr her hac hae]
        constructor
        · rintro ⟨C, hC, h₁, h₂, h₃, h₄⟩
          rcases hcl hC with rfl | hC | hC
          · exact absurd (hroot hc) h₃
          · exact absurd (hsubL hC h₁) (fun h => hdisj a h har)
          · exact ⟨C, hC, h₁, h₂, h₃, h₄⟩
        · rintro ⟨C, hC, h⟩
          exact ⟨C, hclR hC, h⟩

/-- **A quartet from five LCAs**: a gene tree with distinct leaves displays `ab|ce`, for distinct leaves, exactly when the LCA of `a`, `b` is lower than those of `a`, `c` and `a`, `e`,
or the LCA of `c`, `e` is lower than those of `c`, `a` and `c`, `b`. So a constant number of queries decides it. -/
theorem displays_iff_lcaDepth {t : GeneTree X} (ht : t.leaves.Nodup) {a b c e : X} (hab : a ≠ b) (hac : a ≠ c) (hae : a ≠ e)
    (hbc : b ≠ c) (hbe : b ≠ e) (hce : c ≠ e) (ha : a ∈ t.leaves) (hb : b ∈ t.leaves) (hc : c ∈ t.leaves) (he : e ∈ t.leaves) :
    t.Displays a b c e ↔ (lcaDepth t a c < lcaDepth t a b ∧ lcaDepth t a e < lcaDepth t a b) ∨
      (lcaDepth t c a < lcaDepth t c e ∧ lcaDepth t c b < lcaDepth t c e) := by
  rw [displays_iff_geneTreeDisplays hab hac hae hbc hbe hce ha hb hc he, geneTreeDisplays, decide_eq_true_iff,
    ← exists_cluster_iff_lcaDepth ht ha hb hc he hab hac hae,
    ← exists_cluster_iff_lcaDepth ht hc he ha hb hce hac.symm hbc.symm]
  constructor
  · rintro ⟨C, hC, h | h⟩
    · exact Or.inl ⟨C, hC, h⟩
    · exact Or.inr ⟨C, hC, h⟩
  · rintro (⟨C, hC, h⟩ | ⟨C, hC, h⟩)
    · exact ⟨C, hC, Or.inl h⟩
    · exact ⟨C, hC, Or.inr h⟩

/-- **The LCAs that decide a quartet tree `ab|ce`**: five pairs of leaves, each one query of two table reads. -/
def quartetQueries (a b c e : X) : List (X × X) := [(a, b), (a, c), (a, e), (c, e), (c, b)]

/-- The decision by the queries of the sparse table. Only `lcaQuery` is used, on the pairs of `quartetQueries`, up to the order of a pair. -/
def displaysByQueries (t : GeneTree X) (a b c e : X) : Prop :=
  (lcaQuery t a c < lcaQuery t a b ∧ lcaQuery t a e < lcaQuery t a b) ∨
    (lcaQuery t a c < lcaQuery t c e ∧ lcaQuery t c b < lcaQuery t c e)

/-- **Displaying a quartet tree is decided by the queries** of `quartetQueries`, on the sparse table of `gaps`. -/
theorem displays_iff_displaysByQueries {t : GeneTree X} (ht : t.leaves.Nodup) {a b c e : X} (hab : a ≠ b) (hac : a ≠ c)
    (hae : a ≠ e) (hbc : b ≠ c) (hbe : b ≠ e) (hce : c ≠ e) (ha : a ∈ t.leaves) (hb : b ∈ t.leaves) (hc : c ∈ t.leaves)
    (he : e ∈ t.leaves) : t.Displays a b c e ↔ displaysByQueries t a b c e := by
  rw [displays_iff_lcaDepth ht hab hac hae hbc hbe hce ha hb hc he, displaysByQueries,
    lcaQuery_eq ht ha hb hab, lcaQuery_eq ht ha hc hac, lcaQuery_eq ht ha he hae, lcaQuery_eq ht hc he hce,
    lcaQuery_eq ht hc hb hbc.symm, lcaDepth_comm t c a]

/-- The nodes of a gene tree, which the traversal computing `gaps` visits once each. -/
def numNodes : GeneTree X → ℕ
  | leaf _ => 1
  | node l r => numNodes l + numNodes r + 1

omit [DecidableEq X] in
theorem numNodes_add_one (t : GeneTree X) : numNodes t + 1 = 2 * t.leaves.length := by
  induction t with
  | leaf x => simp [numNodes, leaves]
  | node l r ihl ihr =>
    simp only [numNodes, leaves, List.length_append]
    omega

/-- The traversal, with the depth as an argument: it computes `gaps` shifted by the depth, visiting each node once. -/
def gapsFrom : ℕ → GeneTree X → List ℕ
  | _, leaf _ => []
  | d, node l r => gapsFrom (d + 1) l ++ d :: gapsFrom (d + 1) r

omit [DecidableEq X] in
theorem gapsFrom_eq (d : ℕ) (t : GeneTree X) : gapsFrom d t = (gaps t).map (· + d) := by
  induction t generalizing d with
  | leaf x => rfl
  | node l r ihl ihr =>
    have e : (fun x => x + (d + 1)) = (fun x => x + d) ∘ (fun x => x + 1) := by
      funext x
      simp only [Function.comp]
      omega
    simp only [gapsFrom, gaps, ihl, ihr, List.map_append, List.map_map, List.map_cons, e, Nat.zero_add]

omit [DecidableEq X] in
/-- **The precomputation for one gene tree on `n` leaves**, counted: the traversal visits `2 n - 1` nodes, and the sparse table of the `n - 1` gaps has at most `n (log₂ n + 1)` entries. So
`3 n + n log₂ n` at most, `O(n log n)`. -/
theorem precomputation_le (t : GeneTree X) :
    numNodes t + (sparseIndices (gaps t).length).card ≤ 3 * t.leaves.length + t.leaves.length * Nat.log 2 t.leaves.length := by
  have h₁ := numNodes_add_one t
  have h₂ := length_gaps t
  rw [card_sparseIndices]
  have hlog : Nat.log 2 (gaps t).length ≤ Nat.log 2 t.leaves.length := Nat.log_mono_right (by omega)
  have hle : (Nat.log 2 (gaps t).length + 1) * (gaps t).length ≤ (Nat.log 2 t.leaves.length + 1) * t.leaves.length :=
    Nat.mul_le_mul (by omega) (by omega)
  have heq : (Nat.log 2 t.leaves.length + 1) * t.leaves.length =
      t.leaves.length * Nat.log 2 t.leaves.length + t.leaves.length := by
    rw [Nat.add_mul, Nat.one_mul, Nat.mul_comm]
  omega

end GeneTree

end Phylogenetics
