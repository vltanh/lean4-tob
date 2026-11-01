module

public import TINNiK.Counts

/-!
# NANUQ: the running time

The source (lines 1780-1791): "To analyze the running time for this algorithm, suppose `|X| = n` and the input set contains `m` trees. First note that tallying displayed quartets in Step 1 can be done in time `O(n⁴ m)` [...]. The hypothesis tests for Step 2 are performed in
constant time for each set of 4 taxa, for a total of `O(n⁴)`. Step 3 [...] an additional time of `O(n⁴)`. The NeighborNet algorithm in Step 4 takes time `O(n³)` [6]. Since NeighborNet can produce positive weights for all `O(n²)` splits consistent with some circular ordering of the taxa,
results from [7] show that the time for the Circular Network Algorithm in Step 5 is `O(n⁴)`. Thus the total time for NANUQ is `O(n⁴ m)`."

Steps 1 to 3 are counted as in TINNiK (`TINNiK.card_tabulation`, `TINNiK.sum_step2_statistics`, `TINNiK.sum_distance_incidences`). NeighborNet and the Circular Network algorithm are not formalized (the module's README): Steps 4 and 5 are costs `nn`, `cn` from their references, bounded as the source
says. What is proved of them is the count of splits, `card_circularSplits_le`.
-/

@[expose] public noncomputable section

open Finset

namespace External.AllmanBanosRhodes2019

/-- The splits consistent with a circular ordering of `n` taxa: an arc of the circle is given by the pair of its two ends. -/
def circularSplits (n : ℕ) : Finset (Finset (Fin n)) :=
  ((univ : Finset (Fin n)) ×ˢ (univ : Finset (Fin n))).image fun p => univ.filter fun x => p.1 ≤ x ∧ x < p.2

/-- **"All `O(n²)` splits consistent with some circular ordering of the taxa"**: at most `n²` arcs. -/
theorem card_circularSplits_le (n : ℕ) : (circularSplits n).card ≤ n * n := by
  refine card_image_le.trans ?_
  simp

/-- The operations of NANUQ on `n` taxa and `m` gene trees, with costs `nn`, `cn` for Steps 4 and 5. Step 1: `3 C(n, 4) m` as in `TINNiK.card_tabulation`. Step 2: `4 C(n, 4)`, as in `TINNiK.sum_step2_statistics`. Step 3: `6 C(n, 4)`, as in `TINNiK.sum_distance_incidences`. -/
def nanuqOperations (n m nn cn : ℕ) : ℕ := 3 * n.choose 4 * m + 4 * n.choose 4 + 6 * n.choose 4 + nn + cn

/-- **"Thus the total time for NANUQ is `O(n⁴ m)`"** (`nanuq:runtime`), for `m ≥ 1`. -/
theorem nanuqOperations_le {n m nn cn c₁ c₂ : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n) (hnn : nn ≤ c₁ * n ^ 3) (hcn : cn ≤ c₂ * n ^ 4) :
    nanuqOperations n m nn cn ≤ (13 + c₁ + c₂) * (n ^ 4 * m) := by
  have hC : n.choose 4 ≤ n ^ 4 := Nat.choose_le_pow n 4
  have h₁ : n ^ 4 ≤ n ^ 4 * m := Nat.le_mul_of_pos_right _ hm
  have h₂ : n ^ 3 ≤ n ^ 4 := Nat.pow_le_pow_right hn (by norm_num)
  have h₃ : n.choose 4 * m ≤ n ^ 4 * m := Nat.mul_le_mul_right _ hC
  have h₄ : c₁ * n ^ 3 ≤ c₁ * (n ^ 4 * m) := Nat.mul_le_mul_left _ (h₂.trans h₁)
  have h₅ : c₂ * n ^ 4 ≤ c₂ * (n ^ 4 * m) := Nat.mul_le_mul_left _ h₁
  have hexp : (13 + c₁ + c₂) * (n ^ 4 * m) = 13 * (n ^ 4 * m) + c₁ * (n ^ 4 * m) + c₂ * (n ^ 4 * m) := by ring
  rw [hexp]
  simp only [nanuqOperations]
  have e : 3 * n.choose 4 * m = 3 * (n.choose 4 * m) := by ring
  rw [e]
  omega

end External.AllmanBanosRhodes2019
