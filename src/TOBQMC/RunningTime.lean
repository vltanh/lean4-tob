module

public import Basic.LCA
public import External.KaneTao2017.PartitioningClusters
public import Phylogenetics.Tree.AstralDP
public import TINNiK.Counts
public import TOBQMC.Astral
public import TOBQMC.Counts

/-!
# TOB-QMC: the running times, with what they rest on

`src/TOBQMC/Counts.lean` counts the four-taxon subsets. This file goes on to the rest of TOB-QMC's running time claims (v5), each as a count of operations. A measured time on a machine is
not a mathematical claim, and is not treated.

* **Embedded lines 602-605, the time per subset and the precomputation.** `Phylogenetics.GeneTree.displays_iff_displaysByQueries` decides a quartet tree by five LCA queries, and each query reads two entries
  of a sparse table of `O(n log n)` entries (`src/Basic/LCA.lean`). So `threeFixOneAlterReads_le`: `O(n² k + n log(n) k)`, as printed. The sentence names binary lifting, whose query takes `Θ(log n)` steps
  (`Phylogenetics.LCA.length_ge_of_sum_two_pow`); with it, `threeFixOneAlterLifting_le` gives `O(n² k log n)`. So the numbers are right, for a sparse table, and the name of the data structure is
  not.
* **Embedded lines 618-619 and 623, the bipartition search.** `searchReads_le`: `O(n³ k + n log(n) k)`, with or without 3f1a.
* **Embedded line 620, TREE-QMC**, "`O(n³ k)` with some assumptions". `treeQMCWork_eq`, `treeQMCWork_le`: Theorem 3 of Han and Molloy 2023. The assumption is that subproblems are perfectly balanced, on `2^p + 2` taxa, and the cost per
  subproblem `O(s² n k)` is their Theorems 1 and 2, taken as what is counted. `unbalancedWork_ge`: without balance, the same costs give `Ω(n⁴ k)`.
* **Embedded lines 620-622, ASTRAL-III**, "`O(n^1.726 k^1.726 D)`, where `D = O(nk)`". `sum_card_astralSplits_le` counts the steps of the dynamic program by Kane and Tao's theorem (`External.KaneTao2017.theorem1`);
  `qi_eq_qiFast` is Lemma 1 of Zhang et al. 2018, scoring in `Θ(d)`; `sum_card_uniquePartitions_le` is `D = O(nk)`; `astralOperations_le` is their Theorem 1.
* **ASTRAL-III's `|X| = O(nk)`**, read in its Additional file 1, Appendix A: `GreedyRun.card_sides_le`, `card_astral3Space_le` discharge the hypothesis `h𝒞`. The heuristics are parameters with the bounds the source states: their code is not modelled.
* **Embedded lines 21, 123-124, 271, TOB-QMC against TINNiK.** `tobqmcOperations_le`: `O(n³ k)`, against `TINNiK.tinnikOperations_nj_le`.
* **Embedded line 570, the brute force**: "`Ω(n⁴)` per edge and thus `Ω(n⁵)` in total". `sum_choose_mul_choose`: on a caterpillar there are exactly `C(n + 1, 5)` subsets in total, so `Ω(n⁵)` is right there. As a statement about every
  edge or every tree it is not: an edge with `|A| = 2` has `C(n - 2, 2)` (`card_bipartitionQuartets_of_two`), and the balanced tree has at most `n⁴` in all (`balanced_total_le`). The sentence is read as a worst case.
* **Supplement, lines 631-632.** `taxa_ne_of_mem_multipartitionQuartets`: `Q₄(e₁) ∩ Q₄(e₂) = ∅`, so 3f1a "avoids testing the same 4-taxon subsets on different edges".
* **Supplement, lines 642-649, the remark on sampling.** `card_around_of_blocks`: on the printed example, one four-taxon subset around the bipartition in `(m + 1)² / 4` draws one taxon from each block, which is
  `16 / n²`. The printed `4 (n - 2)² / (n - 1)⁴` is not that value, and has the same order, as the remark uses it. `one_sub_pow_le_mul`, `pow_le_exp`: so a quadratic number of samples is what is needed.

No machine model is used. Han and Molloy's supplement and Zhang et al.'s text were read; Kane and Tao's theorem is proved in `src/External/KaneTao2017/`.
-/

@[expose] public noncomputable section

open Phylogenetics Phylogenetics.RootedNetwork Finset
open scoped Classical

namespace TOBQMC

variable {X : Type*} [Fintype X] [DecidableEq X]

/-! ### The time per subset and the precomputation -/

/-- Reads of the sparse table to decide one quartet tree on one gene tree: five LCA queries (`GeneTree.quartetQueries`), of two reads each (`LCA.rangeQuery_reads`). -/
def readsPerEvaluation : ℕ := 5 * 2

theorem readsPerEvaluation_eq : (GeneTree.quartetQueries (X := Unit) () () () ()).length * (LCA.rangeQueryReads 0 1).length = readsPerEvaluation := rfl

/-- The reads to test `tests` four-taxon subsets on `k` gene trees, for three quartet trees each (`sum_card_evaluations`), and the precomputation, by `GeneTree.precomputation_le`: `3 n + n log₂ n` per gene tree. -/
def sparseReads (n k tests : ℕ) : ℕ := tests * (3 * k * readsPerEvaluation) + k * (3 * n + n * Nat.log 2 n)

/-- **"The total time complexity of applying the 3f1a algorithm to every branch is `O(n² k + n log(n) k)`"** (embedded line 605), with the structure that gives it: at most `(n - 3)²` subsets (`TOBQMC.card_threeFixOneAlter_total_le`), each
read off `k` gene trees in `O(1)` per gene tree after the precomputation. -/
theorem threeFixOneAlterReads_le {n k tests : ℕ} (htests : tests ≤ (n - 3) * (n - 3)) :
    sparseReads n k tests ≤ 30 * (n ^ 2 * k) + 3 * (n * k) + n * Nat.log 2 n * k := by
  have h₁ : (n - 3) * (n - 3) ≤ n ^ 2 := by
    rw [sq]
    exact Nat.mul_le_mul (Nat.sub_le _ _) (Nat.sub_le _ _)
  have h₂ : tests * (3 * k * readsPerEvaluation) ≤ n ^ 2 * (3 * k * readsPerEvaluation) :=
    Nat.mul_le_mul_right _ (htests.trans h₁)
  unfold sparseReads
  simp only [readsPerEvaluation] at h₂ ⊢
  nlinarith

/-- **The bipartition search** (embedded lines 618-619 and 623): at `O(n³)` tests in total (`TOBQMC.search_total_le_of_limit_le`), "the time complexity of detecting FPs" is `O(n³ k + n log(n) k)`. -/
theorem searchReads_le {n k tests C : ℕ} (htests : tests ≤ C * n ^ 3) :
    sparseReads n k tests ≤ 30 * C * (n ^ 3 * k) + 3 * (n * k) + n * Nat.log 2 n * k := by
  have h₂ : tests * (3 * k * readsPerEvaluation) ≤ C * n ^ 3 * (3 * k * readsPerEvaluation) :=
    Nat.mul_le_mul_right _ htests
  unfold sparseReads
  simp only [readsPerEvaluation] at h₂ ⊢
  nlinarith

/-- `n log₂ n ≤ n²`, so the precomputation does not change the order: the time of the method's detection step is `O(n³ k)`, the time of TREE-QMC. The sentence at embedded lines 618-621 "does not exceed" is
of this. -/
theorem searchReads_le_cube {n k tests C : ℕ} (htests : tests ≤ C * n ^ 3) (hn : 1 ≤ n) :
    sparseReads n k tests ≤ (30 * C + 4) * (n ^ 3 * k) := by
  refine (searchReads_le htests).trans ?_
  have hlog : n * Nat.log 2 n ≤ n ^ 3 := by
    calc n * Nat.log 2 n ≤ n * n := Nat.mul_le_mul_left _ (Nat.log_le_self 2 n)
      _ ≤ n ^ 3 := by nlinarith [Nat.mul_le_mul hn (le_refl (n * n))]
  have hn3 : n ≤ n ^ 3 := by nlinarith [Nat.mul_le_mul hn hn]
  have h₃ : n * k ≤ n ^ 3 * k := Nat.mul_le_mul_right _ hn3
  have h₄ : n * Nat.log 2 n * k ≤ n ^ 3 * k := Nat.mul_le_mul_right _ hlog
  nlinarith

/-- Steps of binary lifting per LCA query, with `J + 1` rows: `liftTo` on each of the two vertices, and `meet`, each one step per row. -/
def liftingStepsPerQuery (J : ℕ) : ℕ := 3 * (J + 1)

/-- **With binary lifting as the sentence names it**, the same count gives `O(n² k log n)`: each of the five queries takes a step per row, not `O(1)`. Precomputation: a table of `(J + 1) n` entries. -/
theorem threeFixOneAlterLifting_le {n k tests J : ℕ} (htests : tests ≤ (n - 3) * (n - 3)) :
    tests * (3 * k * (5 * liftingStepsPerQuery J)) + k * ((J + 1) * n) ≤ 45 * (J + 1) * (n ^ 2 * k) + (J + 1) * (n * k) := by
  have h₁ : (n - 3) * (n - 3) ≤ n ^ 2 := by
    rw [sq]
    exact Nat.mul_le_mul (Nat.sub_le _ _) (Nat.sub_le _ _)
  have h₂ : tests * (3 * k * (5 * liftingStepsPerQuery J)) ≤ n ^ 2 * (3 * k * (5 * liftingStepsPerQuery J)) :=
    Nat.mul_le_mul_right _ (htests.trans h₁)
  unfold liftingStepsPerQuery at h₂ ⊢
  nlinarith

/-! ### TREE-QMC -/

/-- The work of TREE-QMC on a subproblem of `2^p + 2` taxa, on `k` gene trees with `n` leaves, when divided in a perfectly balanced way into two subproblems of `2^(p-1) + 2`: "`O(s² n k + s²) = O(s² n k)`" per subproblem of size `s` (Han and Molloy 2023,
Supplement, Theorems 1, 2, 3), counted as `s² n k`. Theorem 3's proof stops the recursion at `p = 0`. -/
def treeQMCWork (n k : ℕ) : ℕ → ℕ
  | 0 => (2 ^ 0 + 2) ^ 2 * n * k
  | p + 1 => (2 ^ (p + 1) + 2) ^ 2 * n * k + 2 * treeQMCWork n k p

/-- The sum at the head of the proof of Theorem 3 of Han and Molloy 2023. -/
theorem treeQMCWork_eq (n k p : ℕ) :
    treeQMCWork n k p = ∑ i ∈ range (p + 1), 2 ^ i * ((2 ^ (p - i) + 2) ^ 2 * n * k) := by
  induction p with
  | zero => simp [treeQMCWork]
  | succ p ih =>
    rw [treeQMCWork, sum_range_succ' _ (p + 1), ih, mul_sum]
    simp only [pow_zero, one_mul, Nat.sub_zero]
    rw [add_comm]
    congr 1
    refine sum_congr rfl fun i hi => ?_
    have hi' : i ≤ p := by simpa [Nat.lt_succ_iff] using hi
    rw [show p + 1 - (i + 1) = p - i by omega, pow_succ]
    ring

/-- **Theorem 3 of Han and Molloy 2023** (`ext:treeqmc_theorem3`): "TREE-QMC has time complexity `O(n³ k)` if subproblems are produced in a perfectly balanced fashion". On `n = 2^p + 2` taxa, the work is at most `14 n³ k`. This is what TOB-QMC's "with some assumptions"
refers to. -/
theorem treeQMCWork_le (p k : ℕ) : treeQMCWork (2 ^ p + 2) k p ≤ 14 * (2 ^ p + 2) ^ 3 * k := by
  set n := 2 ^ p + 2 with hn
  rw [treeQMCWork_eq]
  have hterm : ∀ i ∈ range (p + 1), 2 ^ i * (2 ^ (p - i) + 2) ^ 2 ≤ 2 ^ (2 * p - i) + 2 ^ (p + 2) + 2 ^ (i + 2) := by
    intro i hi
    have hi' : i ≤ p := by simpa [Nat.lt_succ_iff] using hi
    have e₁ : 2 ^ i * 2 ^ (p - i) = 2 ^ p := by rw [← pow_add]; congr 1; omega
    have e₂ : 2 ^ i * (2 ^ (p - i) * 2 ^ (p - i)) = 2 ^ (2 * p - i) := by
      rw [← pow_add, ← pow_add]; congr 1; omega
    have e₃ : 2 ^ (p + 2) = 4 * 2 ^ p := by rw [pow_add]; ring
    have e₄ : 2 ^ (i + 2) = 4 * 2 ^ i := by rw [pow_add]; ring
    have : 2 ^ i * (2 ^ (p - i) + 2) ^ 2 = 2 ^ i * (2 ^ (p - i) * 2 ^ (p - i)) + 4 * (2 ^ i * 2 ^ (p - i)) + 4 * 2 ^ i := by ring
    rw [this, e₁, e₂, e₃, e₄]
  have hsum₁ : ∑ i ∈ range (p + 1), 2 ^ (2 * p - i) ≤ 2 * 2 ^ (2 * p) := by
    have key : ∀ q : ℕ, q ≤ p → ∑ i ∈ range (q + 1), 2 ^ (2 * p - i) + 2 ^ (2 * p - q) = 2 * 2 ^ (2 * p) := by
      intro q hq
      induction q with
      | zero => simp; ring
      | succ q ih =>
        rw [sum_range_succ, ← ih (by omega)]
        have e : 2 ^ (2 * p - q) = 2 * 2 ^ (2 * p - (q + 1)) := by
          rw [← pow_succ']; congr 1; omega
        rw [e]
        ring
    exact Nat.le.intro (key p le_rfl)
  have hsum₂ : ∑ _i ∈ range (p + 1), 2 ^ (p + 2) = (p + 1) * 2 ^ (p + 2) := by simp
  have hsum₃ : ∑ i ∈ range (p + 1), 2 ^ (i + 2) ≤ 8 * 2 ^ p := by
    have key : ∀ q : ℕ, ∑ i ∈ range (q + 1), 2 ^ (i + 2) + 4 = 8 * 2 ^ q := by
      intro q
      induction q with
      | zero => simp
      | succ q ih =>
        rw [sum_range_succ, add_right_comm, ih]
        ring
    exact Nat.le.intro (key p)
  have hp1 : p + 1 ≤ 2 ^ p := Nat.lt_two_pow_self
  have hP : 1 ≤ 2 ^ p := Nat.one_le_two_pow
  have hinner : ∑ i ∈ range (p + 1), 2 ^ i * (2 ^ (p - i) + 2) ^ 2 ≤ 14 * n ^ 2 := by
    refine (sum_le_sum hterm).trans ?_
    rw [sum_add_distrib, sum_add_distrib, hsum₂]
    have e₁ : 2 ^ (2 * p) = 2 ^ p * 2 ^ p := by rw [two_mul, pow_add]
    have e₂ : 2 ^ (p + 2) = 4 * 2 ^ p := by rw [pow_add]; ring
    rw [e₂]
    rw [e₁] at hsum₁
    have h₁ : (p + 1) * (4 * 2 ^ p) ≤ 2 ^ p * (4 * 2 ^ p) := Nat.mul_le_mul_right _ hp1
    have h₂ : 2 ^ p * 2 ^ p ≤ n ^ 2 := by
      rw [sq]
      exact Nat.mul_le_mul (by omega) (by omega)
    have h₃ : 2 ^ p ≤ 2 ^ p * 2 ^ p := Nat.le_mul_of_pos_left _ (by omega)
    nlinarith
  have hre : ∑ i ∈ range (p + 1), 2 ^ i * ((2 ^ (p - i) + 2) ^ 2 * n * k) =
      (∑ i ∈ range (p + 1), 2 ^ i * (2 ^ (p - i) + 2) ^ 2) * (n * k) := by
    rw [sum_mul]
    exact sum_congr rfl fun i _ => by ring
  rw [hre]
  calc _ ≤ 14 * n ^ 2 * (n * k) := Nat.mul_le_mul_right _ hinner
    _ = 14 * n ^ 3 * k := by ring

/-- **The assumption matters.** With subproblems of `s` taxa divided off one taxon at a time (`s - 1` and `3` taxa), at the same cost per subproblem, the work on `n` taxa is at least the sum of `s² n k` for `s ≤ n`, which is `Ω(n⁴ k)`. -/
theorem unbalancedWork_ge (n k : ℕ) : n ^ 3 * (n * k) ≤ 3 * (∑ s ∈ range (n + 1), s ^ 2) * (n * k) + 3 * n ^ 2 * (n * k) := by
  have hsum : n ^ 3 ≤ 3 * (∑ s ∈ range (n + 1), s ^ 2) + 3 * n ^ 2 := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [sum_range_succ]
      have e₁ : (n + 1) ^ 3 = n ^ 3 + 3 * n ^ 2 + 3 * n + 1 := by ring
      have e₂ : (n + 1) ^ 2 = n ^ 2 + 2 * n + 1 := by ring
      rw [e₁, e₂]
      omega
  calc n ^ 3 * (n * k) ≤ (3 * (∑ s ∈ range (n + 1), s ^ 2) + 3 * n ^ 2) * (n * k) := Nat.mul_le_mul_right _ hsum
    _ = _ := by ring

/-! ### ASTRAL-III -/

section Astral

/-- **The steps of the dynamic program of ASTRAL** on the clusters `𝒞`: for each cluster, its allowed splits. This is `|Y|` of Zhang et al. 2018 (up to the two orders of a split), and what `astralValue` enumerates. -/
def astralSteps (𝒞 : Finset (Finset X)) : ℕ := ∑ C ∈ 𝒞, (astralSplits 𝒞 C).card

omit [Fintype X] in
/-- Each step is a triple of Kane and Tao's theorem. -/
theorem astralSteps_le_card_triples (𝒞 : Finset (Finset X)) : astralSteps 𝒞 ≤ (External.KaneTao2017.triples 𝒞 𝒞 𝒞).card := by
  rw [astralSteps, ← card_sigma]
  refine card_le_card_of_injOn (fun x => (x.2, x.1 \ x.2, x.1)) (fun x hx => ?_) ?_
  · obtain ⟨hC, hA⟩ := mem_sigma.1 (mem_coe.1 hx)
    obtain ⟨hA𝒞, -, hsub, hdiff⟩ := mem_filter.1 hA
    exact mem_coe.2 (External.KaneTao2017.mem_triples.2 ⟨hA𝒞, hdiff, hC, disjoint_sdiff, union_sdiff_of_subset hsub.subset⟩)
  · rintro ⟨C, A⟩ _ ⟨C', A'⟩ _ h
    simp only [Prod.mk.injEq] at h
    obtain ⟨h₁, -, h₃⟩ := h
    subst h₁
    subst h₃
    rfl

omit [Fintype X] in
/-- **"The size of the set `Y` is `O(|X|^1.726)`"** (Zhang et al. 2018, proof of Theorem 1, from Kane and Tao 2017). -/
theorem astralSteps_le (𝒞 : Finset (Finset X)) : (astralSteps 𝒞 : ℝ) ≤ (𝒞.card : ℝ) ^ (1.726 : ℝ) :=
  (Nat.cast_le.2 (astralSteps_le_card_triples 𝒞)).trans (External.KaneTao2017.card_triples_le_rpow 𝒞)

/-! #### Scoring a tripartition -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Equation 4 of Zhang et al. 2018: `QI(T, M) = ∑_i ∑_{j≠i} ∑_{k≠i,j} (a_i + b_j + c_k - 3) / 2 · a_i b_j c_k`, with `Θ(d³)` terms. -/
def qi (a b c : ι → ℝ) : ℝ :=
  ∑ i, ∑ j, ∑ k, if j ≠ i ∧ k ≠ i ∧ k ≠ j then (a i + b j + c k - 3) / 2 * (a i * b j * c k) else 0

/-- `x choose 2`, as a real number. -/
def choose2 (x : ℝ) : ℝ := x * (x - 1) / 2

/-- Equation 6 of Zhang et al. 2018, from the sums `S_a`, `S_{a,b}`: nine sums of `d` terms. -/
def qiFast (a b c : ι → ℝ) : ℝ :=
  ∑ i, choose2 (a i) * ((∑ j, b j - b i) * (∑ j, c j - c i) - ∑ j, b j * c j + b i * c i) +
  ∑ i, choose2 (b i) * ((∑ j, a j - a i) * (∑ j, c j - c i) - ∑ j, a j * c j + a i * c i) +
  ∑ i, choose2 (c i) * ((∑ j, a j - a i) * (∑ j, b j - b i) - ∑ j, a j * b j + a i * b i)

/-- The inner sum: `∑_{j≠i} ∑_{k≠i,j} b_j c_k`. -/
theorem sum_sum_ite_eq (b c : ι → ℝ) (i : ι) :
    (∑ j, ∑ k, if j ≠ i ∧ k ≠ i ∧ k ≠ j then b j * c k else 0) =
      (∑ j, b j - b i) * (∑ j, c j - c i) - ∑ j, b j * c j + b i * c i := by
  have h₁ : ∀ j, (∑ k, if j ≠ i ∧ k ≠ i ∧ k ≠ j then b j * c k else 0) =
      if j ≠ i then b j * (∑ k, c k - c i - c j) else 0 := by
    intro j
    by_cases hj : j = i
    · simp [hj]
    · have hsplit : ∑ k, c k = c i + (c j + ∑ k ∈ (univ.erase i).erase j, c k) := by
        rw [← add_sum_erase _ _ (mem_univ i), ← add_sum_erase _ _ (mem_erase.2 ⟨hj, mem_univ j⟩)]
      have hsum : (∑ k, if k ≠ i ∧ k ≠ j then c k else 0) = ∑ k ∈ (univ.erase i).erase j, c k := by
        rw [← sum_filter]
        refine sum_congr ?_ fun _ _ => rfl
        ext k
        simp only [mem_filter, mem_univ, true_and, mem_erase, ne_eq]
        tauto
      simp only [hj, ne_eq, not_false_eq_true, true_and, ↓reduceIte]
      have hpull : (∑ k, if ¬ k = i ∧ ¬ k = j then b j * c k else 0) = b j * ∑ k, if ¬ k = i ∧ ¬ k = j then c k else 0 := by
        rw [mul_sum]
        refine sum_congr rfl fun k _ => ?_
        split_ifs <;> simp
      rw [hpull]
      congr 1
      simp only [ne_eq] at hsum
      rw [hsum]
      linarith
  simp only [h₁]
  have h₂ : (∑ j, if j ≠ i then b j * (∑ k, c k - c i - c j) else 0) =
      ∑ j, (b j * (∑ k, c k - c i) - b j * c j) - (b i * (∑ k, c k - c i) - b i * c i) := by
    rw [← add_sum_erase _ (fun j => b j * (∑ k, c k - c i) - b j * c j) (mem_univ i), add_sub_cancel_left,
      ← sum_filter]
    refine sum_congr ?_ fun j _ => by ring
    ext j
    simp [mem_erase]
  rw [h₂, sum_sub_distrib, ← sum_mul]
  ring

/-- **Lemma 1 of Zhang et al. 2018** (`ext:astral3_lemma1`): Equation 4 is Equation 6, which has `Θ(d)` terms. Their derivation is in their Additional file 1, Appendix B.1, by summing over `i`, `j`, `k`; this is the expansion
`(a + b + c - 3) / 2 · a b c = C(a, 2) b c + a C(b, 2) c + a b C(c, 2)`. -/
theorem qi_eq_qiFast (a b c : ι → ℝ) : qi a b c = qiFast a b c := by
  have hterm : ∀ i j k, (if j ≠ i ∧ k ≠ i ∧ k ≠ j then (a i + b j + c k - 3) / 2 * (a i * b j * c k) else 0) =
      choose2 (a i) * (if j ≠ i ∧ k ≠ i ∧ k ≠ j then b j * c k else 0) +
      choose2 (b j) * (if i ≠ j ∧ k ≠ j ∧ k ≠ i then a i * c k else 0) +
      choose2 (c k) * (if i ≠ k ∧ j ≠ k ∧ j ≠ i then a i * b j else 0) := by
    intro i j k
    by_cases h : j ≠ i ∧ k ≠ i ∧ k ≠ j
    · obtain ⟨h₁, h₂, h₃⟩ := h
      have g₁ : i ≠ j ∧ k ≠ j ∧ k ≠ i := ⟨h₁.symm, h₃, h₂⟩
      have g₂ : i ≠ k ∧ j ≠ k ∧ j ≠ i := ⟨h₂.symm, h₃.symm, h₁⟩
      rw [ite_eq_left ⟨h₁, h₂, h₃⟩, ite_eq_left ⟨h₁, h₂, h₃⟩, ite_eq_left g₁, ite_eq_left g₂]
      unfold choose2
      ring
    · have g₁ : ¬ (i ≠ j ∧ k ≠ j ∧ k ≠ i) := fun g => h ⟨g.1.symm, g.2.2, g.2.1⟩
      have g₂ : ¬ (i ≠ k ∧ j ≠ k ∧ j ≠ i) := fun g => h ⟨g.2.2, g.1.symm, g.2.1.symm⟩
      rw [ite_eq_right h, ite_eq_right h, ite_eq_right g₁, ite_eq_right g₂]
      ring
  unfold qi qiFast
  simp only [hterm, sum_add_distrib]
  congr 1
  · congr 1
    · refine sum_congr rfl fun i _ => ?_
      simp only [← mul_sum]
      rw [sum_sum_ite_eq]
    · rw [sum_comm]
      refine sum_congr rfl fun j _ => ?_
      simp only [← mul_sum]
      rw [sum_sum_ite_eq]
  · have hsw : (∑ i, ∑ j, ∑ k, choose2 (c k) * (if i ≠ k ∧ j ≠ k ∧ j ≠ i then a i * b j else 0)) =
        ∑ k, ∑ i, ∑ j, choose2 (c k) * (if i ≠ k ∧ j ≠ k ∧ j ≠ i then a i * b j else 0) :=
      (sum_congr rfl fun _ _ => sum_comm).trans sum_comm
    rw [hsw]
    refine sum_congr rfl fun k _ => ?_
    simp only [← mul_sum]
    rw [sum_sum_ite_eq]

/-- **The operations of Equation 6**: nine sums of `d` terms each, so `Θ(d)`, against `Θ(d³)` in Equation 4. The six sums `S_a`, `S_b`, `S_c`, `S_{a,b}`, `S_{a,c}`, `S_{b,c}`, and the three outer sums. -/
def qiFastTerms (d : ℕ) : ℕ := 9 * d

/-! #### The sum of the degrees -/

/-- The partition at the internal node with cluster `A` of a gene tree: its children, and the rest of the taxa unless `A` is the root. -/
def nodePartition (H : Finset (Finset X)) (A : Finset X) : Finset (Finset X) :=
  if A = univ then childClusters H A else insert Aᶜ (childClusters H A)

/-- The partitions at the internal nodes of a gene tree. -/
def nodePartitions (H : Finset (Finset X)) : Finset (Finset (Finset X)) :=
  (H.filter fun A => 2 ≤ A.card).image (nodePartition H)

/-- `E` of Zhang et al. 2018 without the multiplicities: the unique partitions at the internal nodes of the gene trees. -/
def uniquePartitions {k : ℕ} (G : Fin k → Finset (Finset X)) : Finset (Finset (Finset X)) :=
  univ.biUnion fun i => nodePartitions (G i)

/-- `D`, equation 2 of Zhang et al. 2018: the sum of the degrees of the unique partitions. -/
def sumDegrees {k : ℕ} (G : Fin k → Finset (Finset X)) : ℕ := ∑ M ∈ uniquePartitions G, M.card

/-- A gene tree on `n` taxa has degrees summing to at most `3 n`. -/
theorem sum_card_nodePartitions_le {H : Finset (Finset X)} (hH : IsHierarchy H) :
    ∑ M ∈ nodePartitions H, M.card ≤ 3 * Fintype.card X := by
  have h₁ : ∑ M ∈ nodePartitions H, M.card ≤ ∑ A ∈ H.filter (fun A => 2 ≤ A.card), (nodePartition H A).card := by
    unfold nodePartitions
    induction H.filter (fun A => 2 ≤ A.card) using Finset.induction_on with
    | empty => simp
    | insert a S ha ih =>
      rw [image_insert, sum_insert ha]
      by_cases hmem : nodePartition H a ∈ S.image (nodePartition H)
      · rw [insert_eq_of_mem hmem]
        omega
      · rw [sum_insert hmem]
        omega
  have h₂ : ∀ A ∈ H.filter (fun A => 2 ≤ A.card), (nodePartition H A).card ≤ (childClusters H A).card + 1 := by
    intro A _
    unfold nodePartition
    split_ifs
    · omega
    · exact card_insert_le _ _
  have h₃ := TINNiK.sum_card_childClusters hH
  have h₄ := TINNiK.card_add_one_le_of_isHierarchy hH
  have h₅ : ∑ A ∈ H.filter (fun A => 2 ≤ A.card), (childClusters H A).card ≤ ∑ A ∈ H, (childClusters H A).card :=
    sum_le_sum_of_subset (filter_subset _ _)
  have h₆ := TINNiK.card_filter_two_le_add_one_le hH
  calc _ ≤ _ := h₁
    _ ≤ ∑ A ∈ H.filter (fun A => 2 ≤ A.card), ((childClusters H A).card + 1) := sum_le_sum h₂
    _ = ∑ A ∈ H.filter (fun A => 2 ≤ A.card), (childClusters H A).card + (H.filter fun A => 2 ≤ A.card).card := by
        rw [sum_add_distrib]
        simp
    _ ≤ 3 * Fintype.card X := by omega

/-- **`D = O(nk)`** (TOB-QMC, embedded line 621; Zhang et al. 2018, before Corollary 2): the sum of the degrees of the unique partitions in `k` gene trees on `n` taxa is at most `3 n k`. -/
theorem sumDegrees_le {k : ℕ} {G : Fin k → Finset (Finset X)} (hG : ∀ i, IsHierarchy (G i)) :
    sumDegrees G ≤ 3 * Fintype.card X * k := by
  have key : ∀ S : Finset (Fin k), ∑ M ∈ S.biUnion (fun i => nodePartitions (G i)), M.card ≤ S.card * (3 * Fintype.card X) := by
    intro S
    induction S using Finset.induction_on with
    | empty => simp
    | insert i S hi ih =>
      rw [biUnion_insert, card_insert_of_notMem hi, add_mul, one_mul, add_comm (S.card * _)]
      have hu := sum_union_inter (s₁ := nodePartitions (G i)) (s₂ := S.biUnion fun i => nodePartitions (G i)) (f := fun M => M.card)
      have := sum_card_nodePartitions_le (hG i)
      omega
  have := key univ
  rw [card_univ, Fintype.card_fin] at this
  unfold sumDegrees uniquePartitions
  rw [mul_comm]
  exact this

/-! #### The total -/

/-- **The operations of ASTRAL-III**, as Zhang et al. 2018 count them: for each step of the dynamic program, the scoring of Lemma 2: computing `|W ∩ A|`, `|W ∩ B|`, `|W ∩ C|` for each unique cluster by a traversal with at most `D` edges, and Equation 6, of `9 d` terms for a partition of degree `d`.
"The running time of ASTRAL is dominated by computing the weights". -/
def astralOperations (𝒞 : Finset (Finset X)) (D : ℕ) : ℕ := astralSteps 𝒞 * (3 * D + qiFastTerms D)

omit [Fintype X] in
/-- **Theorem 1 of Zhang et al. 2018** (`ext:astral3_theorem1`), as TOB-QMC quotes it (embedded lines 620-622): "the running time of ASTRAL-III grows as `O(D (nk)^1.726)`", given their "ASTRAL-III forces `|X|` to grow as `O(nk)`",
which here is `h𝒞`. -/
theorem astralOperations_le {𝒞 : Finset (Finset X)} {D c n k : ℕ} (h𝒞 : 𝒞.card ≤ c * n * k) :
    (astralOperations 𝒞 D : ℝ) ≤ 12 * D * ((c : ℝ) ^ (1.726 : ℝ) * (n : ℝ) ^ (1.726 : ℝ) * (k : ℝ) ^ (1.726 : ℝ)) := by
  have hsteps := astralSteps_le 𝒞
  have h₁ : (𝒞.card : ℝ) ^ (1.726 : ℝ) ≤ ((c * n * k : ℕ) : ℝ) ^ (1.726 : ℝ) :=
    Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast h𝒞) (by norm_num)
  have h₂ : ((c * n * k : ℕ) : ℝ) ^ (1.726 : ℝ) = (c : ℝ) ^ (1.726 : ℝ) * (n : ℝ) ^ (1.726 : ℝ) * (k : ℝ) ^ (1.726 : ℝ) := by
    push_cast
    rw [Real.mul_rpow (by positivity) (by positivity), Real.mul_rpow (by positivity) (by positivity)]
  rw [h₂] at h₁
  have hD : (0 : ℝ) ≤ 12 * D := by positivity
  calc (astralOperations 𝒞 D : ℝ) = (astralSteps 𝒞 : ℝ) * (12 * D) := by
        simp only [astralOperations, qiFastTerms]
        push_cast
        ring
    _ ≤ _ := by
        rw [mul_comm]
        exact mul_le_mul_of_nonneg_left (hsteps.trans h₁) hD

/-- The search space of ASTRAL's default mode, the bipartitions of `k` binary gene trees, has `O(nk)` clusters, as `h𝒞` asks: at most `4 n` per gene tree. ASTRAL-III adds to it by heuristics, for which its `|X| = O(nk)` is a claim about them. -/
theorem card_astralClusters_le {Ω : Type*} {G : ℕ → Ω → Finset (Finset X)} {k : ℕ} {ω : Ω}
    (hG : ∀ i < k, IsBinaryTree (unroot (G i ω))) (h2 : 2 ≤ Fintype.card X) :
    (astralClusters G k ω).card ≤ 4 * Fintype.card X * k := by
  have hle : ∀ i ∈ range k, (unroot (G i ω)).card ≤ 4 * Fintype.card X := fun i hi => by
    have := card_of_isBinaryTree (hG i (mem_range.1 hi)) h2
    omega
  have := card_biUnion_le_card_mul _ _ _ hle
  rw [card_range] at this
  unfold astralClusters
  rw [mul_comm]
  exact this

/-! #### The search space of ASTRAL-III -/

/-- **The additions to `X` of Algorithm S1 of Zhang et al. 2018** (their Additional file 1, Appendix A.3), in a run: for each of the thresholds `THS`, each polytomy `p` of the greedy consensus tree of that threshold. `upgma`: the UPGMA resolution. `rounds`: the rounds of the `while` loop, at most `MAXR + RWD`, each adding the
resolutions by a sampled greedy consensus and by UPGMA. `pectinate`: the caterpillar resolutions, one per sampled taxon, in at most `MIT` rounds, and only on the polytomies that the threshold `q` selects. -/
structure GreedyRun (X : Type*) [DecidableEq X] where
  /-- The polytomies of the greedy consensus at a threshold, with their degrees. -/
  polytomies : ℕ → Finset ℕ
  degree : ℕ → ℕ → ℕ
  /-- The sides added by the first UPGMA resolution of a polytomy. -/
  upgma : ℕ → ℕ → Finset (Finset X)
  /-- The sides added by one round on a polytomy. -/
  round : ℕ → ℕ → ℕ → Finset (Finset X)
  /-- The number of rounds on a polytomy. -/
  rounds : ℕ → ℕ → ℕ
  /-- The polytomies that get caterpillar resolutions. -/
  quadratic : ℕ → Finset ℕ
  /-- The sides added by the caterpillar resolutions in one round, on one sampled taxon. -/
  pectinate : ℕ → ℕ → ℕ → ℕ → Finset (Finset X)

/-- The sides that a run of Algorithm S1 adds. -/
def GreedyRun.sides {X : Type*} [DecidableEq X] (R : GreedyRun X) (thresholds mit : ℕ) : Finset (Finset X) :=
  (range thresholds).biUnion fun t => (R.polytomies t).biUnion fun p =>
    R.upgma t p ∪ (range (R.rounds t p)).biUnion (R.round t p) ∪
      if p ∈ R.quadratic t then (range mit).biUnion fun c => (range (R.degree t p)).biUnion (R.pectinate t p c) else ∅

/-- **What the source's sentences say of the run**, on `n` taxa. A resolution of a polytomy of degree `d` is a tree on `d` sides, so it has at most `2 d` sides of new splits. "We find the smallest threshold `q` such that `∑ d_i² ≤ c n`": `hquad`. The degrees of the polytomies of a tree on `n`
taxa sum to at most `3 n` (`sum_card_nodePartitions_le`): `hdeg`. The rounds are bounded by a constant (`MAXR + RWD = 102` in Algorithm S1): `hrounds`. -/
structure GreedyRun.IsBounded {X : Type*} [DecidableEq X] (R : GreedyRun X) (n c maxr : ℕ) : Prop where
  hupgma : ∀ t p, (R.upgma t p).card ≤ 2 * R.degree t p
  hround : ∀ t p r, (R.round t p r).card ≤ 2 * (2 * R.degree t p)
  hpect : ∀ t p r s, (R.pectinate t p r s).card ≤ 2 * R.degree t p
  hrounds : ∀ t p, R.rounds t p ≤ maxr
  hdeg : ∀ t, ∑ p ∈ R.polytomies t, R.degree t p ≤ 3 * n
  hquad : ∀ t, ∑ p ∈ R.quadratic t, R.degree t p ^ 2 ≤ c * n

/-- **"This will ensure that at most `O(n)` bipartitions are added in this step"** (Appendix A.3): the run adds `O(n)` sides, for constant thresholds and rounds. -/
theorem GreedyRun.card_sides_le {X : Type*} [DecidableEq X] {R : GreedyRun X} {n c maxr : ℕ} (h : R.IsBounded n c maxr) (thresholds mit : ℕ) :
    (R.sides thresholds mit).card ≤ thresholds * ((2 + 4 * maxr) * (3 * n) + mit * (2 * (c * n))) := by
  unfold GreedyRun.sides
  refine (card_biUnion_le_card_mul (range thresholds) _ _ fun t _ => ?_).trans (by rw [card_range])
  have hp : ∀ p ∈ R.polytomies t,
      (R.upgma t p ∪ (range (R.rounds t p)).biUnion (R.round t p) ∪
        if p ∈ R.quadratic t then (range mit).biUnion fun c => (range (R.degree t p)).biUnion (R.pectinate t p c) else ∅).card ≤
      (2 + 4 * maxr) * R.degree t p + if p ∈ R.quadratic t then mit * (2 * R.degree t p ^ 2) else 0 := by
    intro p _
    refine (card_union_le _ _).trans (Nat.add_le_add ?_ ?_)
    · refine (card_union_le _ _).trans ?_
      have h₁ := h.hupgma t p
      have h₂ : ((range (R.rounds t p)).biUnion (R.round t p)).card ≤ R.rounds t p * (2 * (2 * R.degree t p)) := by
        have := card_biUnion_le_card_mul (range (R.rounds t p)) (R.round t p) _ fun r _ => h.hround t p r
        rwa [card_range] at this
      have h₃ : R.rounds t p * (2 * (2 * R.degree t p)) ≤ maxr * (2 * (2 * R.degree t p)) :=
        Nat.mul_le_mul_right _ (h.hrounds t p)
      nlinarith
    · split_ifs with hq
      · have hin : ∀ r ∈ range mit, ((range (R.degree t p)).biUnion (R.pectinate t p r)).card ≤ 2 * R.degree t p ^ 2 := by
          intro r _
          have := card_biUnion_le_card_mul (range (R.degree t p)) (R.pectinate t p r) _ fun s _ => h.hpect t p r s
          rw [card_range] at this
          nlinarith
        have := card_biUnion_le_card_mul (range mit) (fun r => (range (R.degree t p)).biUnion (R.pectinate t p r)) _ hin
        rwa [card_range] at this
      · simp
  have hsum : ∑ p ∈ R.polytomies t, ((2 + 4 * maxr) * R.degree t p + if p ∈ R.quadratic t then mit * (2 * R.degree t p ^ 2) else 0) ≤
      (2 + 4 * maxr) * (3 * n) + mit * (2 * (c * n)) := by
    rw [sum_add_distrib, ← mul_sum]
    refine Nat.add_le_add (Nat.mul_le_mul_left _ (h.hdeg t)) ?_
    have hfil : ∑ p ∈ R.polytomies t, (if p ∈ R.quadratic t then mit * (2 * R.degree t p ^ 2) else 0) ≤
        ∑ p ∈ R.quadratic t, mit * (2 * R.degree t p ^ 2) := by
      rw [← sum_filter]
      exact sum_le_sum_of_subset fun p hp => (mem_filter.1 hp).2
    refine hfil.trans ?_
    rw [← mul_sum, ← mul_sum]
    exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (h.hquad t))
  have hbi := card_biUnion_le (s := R.polytomies t) (t := fun p => R.upgma t p ∪ (range (R.rounds t p)).biUnion (R.round t p) ∪
    if p ∈ R.quadratic t then (range mit).biUnion fun c => (range (R.degree t p)).biUnion (R.pectinate t p c) else ∅)
  exact hbi.trans ((sum_le_sum hp).trans hsum)

omit [Fintype X] in
/-- **"ASTRAL-III forces `|X|` to grow as `O(nk)`"** (Zhang et al. 2018, section "New search space"), discharging the hypothesis `h𝒞` of `astralOperations_le`. `X` holds the bipartitions of the `k` gene trees (`card_astralClusters_le` for binary ones), their resolutions at polytomies repeated three times ("handling gene tree polytomies"), of `O(n)` sides per
gene tree, and the additions of Algorithm S1 and of the similarity matrix's UPGMA tree. -/
theorem card_astral3Space_le {𝒞 G P U : Finset (Finset X)} {R : GreedyRun X} {n k c maxr thresholds mit g : ℕ} (h𝒞 : 𝒞 ⊆ G ∪ P ∪ U ∪ R.sides thresholds mit)
    (hG : G.card ≤ 4 * n * k) (hP : P.card ≤ g * n * k) (hU : U.card ≤ 4 * n) (hR : R.IsBounded n c maxr) (hk : 1 ≤ k) :
    𝒞.card ≤ (4 + g + 4 + thresholds * ((2 + 4 * maxr) * 3 + mit * (2 * c))) * n * k := by
  have h₁ := card_le_card h𝒞
  have h₂ := card_union_le (G ∪ P ∪ U) (R.sides thresholds mit)
  have h₃ := card_union_le (G ∪ P) U
  have h₄ := card_union_le G P
  have h₅ := GreedyRun.card_sides_le hR thresholds mit
  have hUk : 4 * n ≤ 4 * n * k := Nat.le_mul_of_pos_right _ hk
  have hS : thresholds * ((2 + 4 * maxr) * (3 * n) + mit * (2 * (c * n))) ≤ thresholds * ((2 + 4 * maxr) * 3 + mit * (2 * c)) * n * k := by
    have e : thresholds * ((2 + 4 * maxr) * (3 * n) + mit * (2 * (c * n))) = thresholds * ((2 + 4 * maxr) * 3 + mit * (2 * c)) * n := by ring
    rw [e]
    exact Nat.le_mul_of_pos_right _ hk
  calc 𝒞.card ≤ 4 * n * k + g * n * k + 4 * n * k + thresholds * ((2 + 4 * maxr) * 3 + mit * (2 * c)) * n * k := by omega
    _ = _ := by ring

end Astral

/-! ### TOB-QMC against TINNiK -/

/-- **"Gives our method time complexity `O(n³ k)`"** (embedded line 21), "versus `O(n⁴ k + n⁵)`" (embedded lines 123-124, 271): `O(n³)` tests in the detection step on `k` gene trees, plus a refinement tree at TREE-QMC's cost. -/
theorem tobqmcOperations_le {n k tests C refine c : ℕ} (htests : tests ≤ C * n ^ 3) (hn : 1 ≤ n) (hrefine : refine ≤ c * n ^ 3 * k) :
    refine + sparseReads n k tests ≤ (c + 30 * C + 4) * (n ^ 3 * k) := by
  have h := searchReads_le_cube (k := k) htests hn
  have h' : c * n ^ 3 * k = c * (n ^ 3 * k) := by ring
  rw [h'] at hrefine
  calc _ ≤ c * (n ^ 3 * k) + (30 * C + 4) * (n ^ 3 * k) := Nat.add_le_add hrefine h
    _ = _ := by ring

/-- The sentence at embedded lines 618-622, "does not exceed the time complexity of seeking a TOB refinement", is about TREE-QMC, as the supplement says at its line 677: `searchReads_le_cube`. As a comparison of bounds, it does not extend to
the ASTRAL-III bound quoted in the same parenthesis: at `D` of order `n k` and `k = 1`, the bound `n^1.726 n` is below `n³` for `n ≥ 2`. -/
theorem rpow_mul_lt_cube {n : ℝ} (hn : 1 < n) : n ^ (1.726 : ℝ) * n < n ^ 3 := by
  have h : n ^ (1.726 : ℝ) < n ^ (2 : ℝ) := Real.rpow_lt_rpow_of_exponent_lt hn (by norm_num)
  have hpos : 0 < n := by linarith
  calc n ^ (1.726 : ℝ) * n < n ^ (2 : ℝ) * n := mul_lt_mul_of_pos_right h hpos
    _ = n ^ 3 := by
      rw [Real.rpow_two]
      ring

/-! ### The brute force -/

section BruteForce

/-- An edge with a cherry on one side has `C(n - 2, 2)` four-taxon subsets around it, not of order `n⁴`. So "`Ω(n⁴)` per edge" (embedded line 570) is a worst case. -/
theorem card_bipartitionQuartets_of_two {A : Finset X} (hA : A.card = 2) :
    (bipartitionQuartets A).card = (Fintype.card X - 2).choose 2 := by
  rw [card_bipartitionQuartets, hA, card_compl, hA]
  simp

/-- `∑_{a ≤ n} C(a, 2) C(n - a, s) = C(n + 1, s + 3)`. -/
theorem sum_choose_mul_choose_aux (n s : ℕ) :
    ∑ a ∈ range (n + 1), a.choose 2 * (n - a).choose s = (n + 1).choose (s + 3) := by
  induction n generalizing s with
  | zero =>
    rw [Nat.choose_eq_zero_of_lt (by omega)]
    simp
  | succ n ih =>
    cases s with
    | zero =>
      have h0 := ih 0
      simp only [Nat.choose_zero_right, mul_one] at h0 ⊢
      rw [sum_range_succ, h0, Nat.choose_succ_succ (n + 1) 2, add_comm]
    | succ s =>
      rw [sum_range_succ]
      have hlast : (n + 1 - (n + 1)).choose (s + 1) = 0 := by simp
      rw [hlast, mul_zero, add_zero]
      have hpascal : ∀ a ∈ range (n + 1), a.choose 2 * (n + 1 - a).choose (s + 1) =
          a.choose 2 * (n - a).choose (s + 1) + a.choose 2 * (n - a).choose s := by
        intro a ha
        have ha' : a ≤ n := by simpa [Nat.lt_succ_iff] using ha
        rw [show n + 1 - a = (n - a) + 1 by omega, Nat.choose_succ_succ]
        ring
      rw [sum_congr rfl hpascal, sum_add_distrib, ih, ih, show s + 1 + 3 = (s + 3) + 1 by ring, Nat.choose_succ_succ (n + 1) (s + 3)]
      ring

/-- **On a caterpillar, the brute force tests `C(n + 1, 5)` subsets**: its edges have one side of each size `a`, for `2 ≤ a ≤ n - 2`, and `TOBQMC.card_bipartitionQuartets` counts each. So `Ω(n⁵)` (embedded line 570) on this tree. The terms with `a < 2` or `n - a < 2` vanish. -/
theorem sum_choose_mul_choose (n : ℕ) :
    ∑ a ∈ range (n + 1), a.choose 2 * (n - a).choose 2 = (n + 1).choose 5 :=
  sum_choose_mul_choose_aux n 2

/-- **The count over the edges of a caterpillar**: a tree whose edges have one side of each size from `2` to `n - 2`. -/
theorem sum_card_bipartitionQuartets_of_caterpillar {E : Finset (Finset X)} (hinj : Set.InjOn Finset.card (E : Set (Finset X)))
    (hsizes : E.image Finset.card = Ico 2 (Fintype.card X - 1)) (h4 : 4 ≤ Fintype.card X) :
    ∑ A ∈ E, (bipartitionQuartets A).card = (Fintype.card X + 1).choose 5 := by
  set n := Fintype.card X with hn
  rw [← sum_choose_mul_choose n]
  have hsum : ∑ A ∈ E, (bipartitionQuartets A).card = ∑ a ∈ Ico 2 (n - 1), a.choose 2 * (n - a).choose 2 := by
    rw [← hsizes, sum_image hinj]
    refine sum_congr rfl fun A _ => ?_
    rw [card_bipartitionQuartets, card_compl]
  rw [hsum]
  refine sum_subset (fun a ha => ?_) fun a ha hna => ?_
  · have := mem_Ico.1 ha
    exact mem_range.2 (by omega)
  · have ha' := mem_range.1 ha
    have hcases : a < 2 ∨ n - 1 ≤ a := by
      by_contra hcon
      push Not at hcon
      exact hna (mem_Ico.2 hcon)
    rcases hcases with h | h
    · rw [Nat.choose_eq_zero_of_lt h, zero_mul]
    · rw [Nat.choose_eq_zero_of_lt (by omega : n - a < 2), mul_zero]

/-- `C(n + 1, 5)` is of order `n⁵`. -/
theorem choose_five_mul (n : ℕ) : 120 * (n + 1).choose 5 = (n + 1) * n * (n - 1) * (n - 2) * (n - 3) := by
  have h := Nat.descFactorial_eq_factorial_mul_choose (n + 1) 5
  have hf : Nat.factorial 5 = 120 := rfl
  rw [hf] at h
  rw [← h]
  simp [Nat.descFactorial]
  ring

/-- **The balanced tree has `O(n⁴)` subsets in total, not `Ω(n⁵)`.** On `n = 2^m` taxa, the balanced tree has `2^j` edges with a side of `2^(m-j)` taxa, each with at most `C(2^(m-j), 2) n²/2` subsets around it, and the sum is at most `n⁴`. So the `Ω(n⁵)` of embedded line 570 is a worst case over trees. -/
theorem balanced_total_le (m : ℕ) :
    ∑ j ∈ range m, 2 ^ j * ((2 ^ (m - j)).choose 2 * (2 ^ m).choose 2) ≤ (2 ^ m) ^ 4 := by
  have hc : ∀ x : ℕ, 2 * x.choose 2 ≤ x * x := fun x => by
    have := Nat.choose_two_right x
    have h2 := Nat.even_mul_pred_self x
    rw [this, Nat.mul_div_cancel' h2.two_dvd]
    exact Nat.mul_le_mul_left _ (Nat.sub_le _ _)
  have hterm : ∀ j ∈ range m, 4 * (2 ^ j * ((2 ^ (m - j)).choose 2 * (2 ^ m).choose 2)) ≤ 2 ^ (m - j) * (2 ^ m) ^ 3 := by
    intro j hj
    have hj' : j ≤ m := (mem_range.1 hj).le
    have h₁ := hc (2 ^ (m - j))
    have h₂ := hc (2 ^ m)
    have e : 2 ^ j * 2 ^ (m - j) = 2 ^ m := by rw [← pow_add]; congr 1; omega
    calc 4 * (2 ^ j * ((2 ^ (m - j)).choose 2 * (2 ^ m).choose 2))
        = 2 ^ j * ((2 * (2 ^ (m - j)).choose 2) * (2 * (2 ^ m).choose 2)) := by ring
      _ ≤ 2 ^ j * ((2 ^ (m - j) * 2 ^ (m - j)) * (2 ^ m * 2 ^ m)) :=
          Nat.mul_le_mul_left _ (Nat.mul_le_mul h₁ h₂)
      _ = (2 ^ j * 2 ^ (m - j)) * 2 ^ (m - j) * (2 ^ m * 2 ^ m) := by ring
      _ = 2 ^ (m - j) * (2 ^ m) ^ 3 := by rw [e]; ring
  have hgeom : ∀ q ≤ m, ∑ j ∈ range q, 2 ^ (m - j) + 2 ^ (m + 1 - q) = 2 ^ (m + 1) := by
    intro q hq
    induction q with
    | zero => simp
    | succ q ih =>
      rw [sum_range_succ, ← ih (by omega), show m + 1 - q = (m - q) + 1 by omega, show m + 1 - (q + 1) = m - q by omega, pow_succ]
      ring
  have hsum : ∑ j ∈ range m, 2 ^ (m - j) ≤ 2 * 2 ^ m := by
    have := Nat.le.intro (hgeom m le_rfl)
    rwa [pow_succ, mul_comm] at this
  have h4 : 4 * ∑ j ∈ range m, 2 ^ j * ((2 ^ (m - j)).choose 2 * (2 ^ m).choose 2) ≤ 2 * (2 ^ m) ^ 4 := by
    rw [mul_sum]
    calc _ ≤ ∑ j ∈ range m, 2 ^ (m - j) * (2 ^ m) ^ 3 := sum_le_sum hterm
      _ = (∑ j ∈ range m, 2 ^ (m - j)) * (2 ^ m) ^ 3 := (sum_mul _ _ _).symm
      _ ≤ 2 * 2 ^ m * (2 ^ m) ^ 3 := Nat.mul_le_mul_right _ hsum
      _ = 2 * (2 ^ m) ^ 4 := by ring
  omega

end BruteForce

/-! ### The quadripartitions of two edges -/

/-- **"For any two edge `e₁, e₂`, `Q₄(e₁) ∩ Q₄(e₂) = ∅`"** (supplement, lines 631-632), so 3f1a "avoids testing the same 4-taxon subsets on different edges": two different splits of an unrooted tree have no four-taxon subset that draws one taxon from each block of both. -/
theorem taxa_ne_of_mem_multipartitionQuartets {T : Finset (Finset X)} (hT : IsUnrootedTree T) {A₁ A₂ : Finset X} (h₁ : A₁ ∈ T)
    (h₂ : A₂ ∈ T) (hne : A₁ ≠ A₂) (hne' : A₁ ≠ A₂ᶜ) {s₁ s₂ : QuartetTree X} (hs₁ : s₁ ∈ multipartitionQuartets T A₁)
    (hs₂ : s₂ ∈ multipartitionQuartets T A₂) : s₁.taxa ≠ s₂.taxa := by
  intro heq
  obtain ⟨hb₁, hc₁, hc₁'⟩ := mem_filter.1 hs₁
  obtain ⟨hb₂, hc₂, hc₂'⟩ := mem_filter.1 hs₂
  set Y := s₁.taxa with hY
  have hcard₁ : (A₁ ∩ Y).card = 2 := s₁.card_of_mem (mem_filter.1 hb₁).2
  have hcard₂ : (A₂ ∩ Y).card = 2 := by
    rw [heq]
    exact s₂.card_of_mem (mem_filter.1 hb₂).2
  have hYcard : Y.card = 4 := s₁.card_taxa
  have hc₁c : (A₁ᶜ ∩ Y).card = 2 := by
    have := card_inter_add_card_sdiff Y A₁
    rw [inter_comm] at this
    have he : Y \ A₁ = A₁ᶜ ∩ Y := by
      ext x
      simp [and_comm]
    rw [he] at this
    omega
  have hc₂c : (A₂ᶜ ∩ Y).card = 2 := by
    have := card_inter_add_card_sdiff Y A₂
    rw [inter_comm] at this
    have he : Y \ A₂ = A₂ᶜ ∩ Y := by
      ext x
      simp [and_comm]
    rw [he] at this
    omega
  have hcompl₁ : A₁ᶜ ∈ T := by
    obtain ⟨H, -, rfl⟩ := hT
    exact compl_mem_unroot.2 h₁
  have hcompl₂ : A₂ᶜ ∈ T := by
    obtain ⟨H, -, rfl⟩ := hT
    exact compl_mem_unroot.2 h₂
  -- a side strictly inside another, with the same trace, is excluded by the bigger side's condition
  have key : ∀ {U W : Finset X}, U ⊆ W → (U ∩ Y).card = 2 → (W ∩ Y).card = 2 → W ∩ Y ⊆ U := by
    intro U W hUW hU hW x hx
    have hsub : U ∩ Y ⊆ W ∩ Y := inter_subset_inter_right hUW
    have heq' := eq_of_subset_of_card_le hsub (by omega)
    rw [← heq'] at hx
    exact (mem_inter.1 hx).1
  rw [← heq] at hc₂ hc₂'
  rcases hT.compatible h₁ h₂ with h | h | h | h
  · exact hc₂ ⟨A₁, h₁, ssubset_of_subset_of_ne h hne, key h hcard₁ hcard₂⟩
  · exact hc₁ ⟨A₂, h₂, ssubset_of_subset_of_ne h hne.symm, key h hcard₂ hcard₁⟩
  · have hsub : A₁ ⊆ A₂ᶜ := fun x hx => mem_compl.2 fun hx' => disjoint_left.1 h hx hx'
    exact hc₂' ⟨A₁, h₁, ssubset_of_subset_of_ne hsub hne', key hsub hcard₁ hc₂c⟩
  · have hsub : A₂ᶜ ⊆ A₁ := fun x hx => by
      have := mem_univ x
      rw [← h] at this
      exact (mem_union.1 this).resolve_right (mem_compl.1 hx)
    exact hc₁ ⟨A₂ᶜ, hcompl₂, ssubset_of_subset_of_ne hsub (fun h' => hne' h'.symm), key hsub hc₂c hcard₁⟩

/-! ### The remark on sampling -/

/-- **The example in the supplement's remark** (lines 642-649): with `|A| = |C| = 1` and `|B| = |D| = m`, so `n = 2 m + 2`, the subsets around the bipartition `A ∪ B | C ∪ D` number `C(m + 1, 2)²`, and those with one taxon from each block number `m²`. Their ratio is `4 / (m + 1)² = 16 / n²`. The printed
value, `4 (n - 2)² / (n - 1)⁴`, is not this ratio: it uses probabilities `2 / (n - 1)` and `(n - 2) / (n - 1)` of picking a taxon, which do not sum over the `n` taxa as those of a sampling would. It is of the same order `1 / n²`, which is what the remark uses. -/
theorem card_around_of_blocks {m : ℕ} (hm : 1 ≤ m) :
    ((m : ℝ) * m) / (((m + 1).choose 2 : ℝ) * ((m + 1).choose 2 : ℝ)) = 16 / (2 * (m : ℝ) + 2) ^ 2 := by
  have hc : ((m + 1).choose 2 : ℝ) = (m + 1) * m / 2 := by
    have h := Nat.cast_choose_two ℝ (m + 1)
    rw [h]
    push_cast
    ring
  rw [hc]
  have hm' : (m : ℝ) ≠ 0 := by exact_mod_cast (by omega : m ≠ 0)
  have hm1 : (m : ℝ) + 1 ≠ 0 := by positivity
  field_simp
  ring

/-- **One way to sample a quadratic number of times**: `t` samples succeed with probability at most `t p`, so success with probability `≥ 1/2` needs `t ≥ 1 / (2 p)`, a quadratic number at `p` of order `1 / n²`. -/
theorem one_sub_pow_le_mul {p : ℝ} (h1 : p ≤ 1) (t : ℕ) : 1 - (1 - p) ^ t ≤ t * p := by
  have := one_add_mul_le_pow (a := -p) (by linarith) t
  have e : (1 + -p) = 1 - p := by ring
  rw [e] at this
  linarith

/-- And a quadratic number suffices: `t` samples fail with probability at most `exp (- t p)`. -/
theorem pow_le_exp {p : ℝ} (h1 : p ≤ 1) (t : ℕ) : (1 - p) ^ t ≤ Real.exp (- (t * p)) := by
  have h := Real.one_sub_le_exp_neg p
  calc (1 - p) ^ t ≤ (Real.exp (-p)) ^ t := pow_le_pow_left₀ (by linarith) h t
    _ = Real.exp (- (t * p)) := by
        rw [← Real.exp_nat_mul]
        congr 1
        ring

end TOBQMC
