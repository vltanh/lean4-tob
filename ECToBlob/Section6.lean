module

public import Basic.Phylogenetics.Defs
public import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent

/-!
# ECToBlob §6: combining p-values

Lemma 6.1. The combination methods are defined in `Basic/Phylogenetics/Defs.lean`.

The lemma's bound for the Cauchy combination uses `min(η, D)` where the paper's uses `η`, so that it is
non-decreasing in `k` on the whole range, as the lemma claims; the two agree for `η ≤ D`, the only
case that the lemma's use reaches (`min(P) ≤ max(P)`). See E-items of the report.
-/

@[expose] public noncomputable section

open Phylogenetics Filter Topology

namespace ECToBlob

/-- The constant `c` of Lemma 6.1: `1` for Bon, Cauchy and CBC, `2` for BBC. -/
def boundConstant : TestCorrection → ℝ
  | .bon => 1
  | .cauchy => 1
  | .bbc => 2
  | .cbc => 1

/-- **Lemma 6.1**, part 1 (`ecto:lem6_1`, with (6.1), `ecto:eq6_1`). For each correction method there
is a bounding function `B k η D` non-decreasing in `k`, `η` and `D` with
`testCo(P) ≤ B_k(min(P), max(P))` for every multiset `P ⊂ [0, 1)` of size `k ≥ 1`, and
`B_k(η, D) ∼ c k η` as `η → 0` for `D < 1` fixed. -/
theorem lemma6_1_part1 (m : TestCorrection) : ∃ B : ℕ → ℝ → ℝ → ℝ,
    (∀ P : Multiset ℝ, P ≠ 0 → (∀ p ∈ P, 0 ≤ p ∧ p < 1) →
      combineP m P ≤ B (Multiset.card P) (minP P) (maxP P)) ∧
    (∀ k k' η D, 1 ≤ k → k ≤ k' → 0 ≤ η → η < 1 → 0 ≤ D → D < 1 → B k η D ≤ B k' η D) ∧
    (∀ k η η' D, 1 ≤ k → 0 ≤ η → η ≤ η' → η' < 1 → 0 ≤ D → D < 1 → B k η D ≤ B k η' D) ∧
    (∀ k η D D', 1 ≤ k → 0 ≤ η → η < 1 → 0 ≤ D → D ≤ D' → D' < 1 → B k η D ≤ B k η D') ∧
    ∀ k D, 1 ≤ k → 0 ≤ D → D < 1 →
      Asymptotics.IsEquivalent (𝓝[>] (0 : ℝ)) (fun η => B k η D)
        (fun η => boundConstant m * k * η) := by
  sorry

/-- **Lemma 6.1**, part 2 (`ecto:lem6_1`). Each combination is at least `min(P)`. -/
theorem lemma6_1_part2 (m : TestCorrection) (P : Multiset ℝ) (hP : P ≠ 0)
    (hP01 : ∀ p ∈ P, 0 ≤ p ∧ p < 1) : minP P ≤ combineP m P := by
  sorry

end ECToBlob
