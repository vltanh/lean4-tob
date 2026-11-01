module

public import ECToBlob.Deterministic
public import TOBQMC.WQC

/-!
# TOB-QMC supplement, Lemma 4: the margin as printed vanishes

E22 of the report. The supplement's Equation (1), lines 395-397: "Let `π(Y)` be the minimum absolute difference between any pair of expected
QCFs on the same taxon set `Y`", and `π_min = min_{Y ∈ S_tree(T_N)} π(Y)`. Lemma 4 then assumes that the errors are below
`δ = π_min / (2 |f₄(S)|)`, and its proof begins: "observe that `π_min > 0` by our assumptions".

By exchangeability, the two alternatives of a quartet tree that `T_N` displays have equal concordance factors. So `π(Y) = 0` for every such `Y`
(`isPrintedPi_zero`), hence `π_min = 0` whenever `T_N` is not a star (`isPrintedPiMin_zero`), so `π_min > 0` is false
(`not_printedPiMin_pos`), and no weights meet the hypothesis of the printed Lemma 4 (`not_exists_printedError_lt`).

The margin that the supplement's proof uses compares the displayed quartet with its alternatives: `TOBQMC.Margin`, with `TOBQMC.supplementLemma4`,
at the same radius, and `TOBQMC.exists_margin`.
-/

@[expose] public noncomputable section

open Phylogenetics Phylogenetics.RootedNetwork Finset
open scoped Classical

namespace TOBQMC

variable {V E X : Type*} [Fintype X] [DecidableEq X]

/-- **Equation (1) of the supplement**: `π` is `π(Y)`, the least absolute difference of `F` on a pair of distinct quartet trees on `Y`. -/
def IsPrintedPi (F : QuartetTree X → ℝ) (Y : Finset X) (π : ℝ) : Prop :=
  IsLeast {d | ∃ r ∈ treesOn Y, ∃ r' ∈ treesOn Y, r ≠ r' ∧ d = |F r - F r'|} π

/-- `π` is the supplement's `π_min`, the least of the `π(Y)` over the sets `Y` of four taxa that the tree of blobs resolves. -/
def IsPrintedPiMin (N : RootedNetwork V E X) (F : QuartetTree X → ℝ) (π : ℝ) : Prop :=
  IsLeast {d | ∃ s, Displays (treeOfBlobs N) s ∧ IsPrintedPi F s.taxa d} π

/-- **`π(Y)` vanishes on a set of four taxa that the tree of blobs resolves** (`tob2025:supplement_eq1_zero`, E22 of the report): the alternatives of
the displayed quartet tree have equal concordance factors. -/
theorem isPrintedPi_zero {N : RootedNetwork V E X} [Fintype V] [Fintype E] (hN : N.IsPhylogenetic) {θ : MetricData E}
    (hθ : N.IsMetric θ) {ρ : ℝ} (hρ : 0 ≤ ρ ∧ ρ ≤ 1) {s : QuartetTree X} (hs : Displays (treeOfBlobs N) s) :
    IsPrintedPi (nmscCF N θ ρ) s.taxa 0 := by
  obtain ⟨A, hA, hAs⟩ := hs
  have hcut : InducedCutSplit N s := ECToBlob.Deterministic.inducedCutSplit_of_mem hN hA hAs
  obtain ⟨r, hr, r', hr', hne⟩ := Finset.one_lt_card.1
    (by rw [s.card_alternatives]; norm_num : 1 < s.alternatives.card)
  have hmem : ∀ {t : QuartetTree X}, t ∈ s.alternatives → t ∈ treesOn s.taxa := fun ht =>
    mem_treesOn.2 (QuartetTree.mem_alternatives.1 ht).1
  refine ⟨⟨r, hmem hr, r', hmem hr', hne, ?_⟩, ?_⟩
  · rw [NMSC.cut_alternatives hN hθ hρ s hcut r hr r' hr', sub_self, abs_zero]
  · rintro d ⟨_, -, _, -, -, rfl⟩
    exact abs_nonneg _

/-- **`π_min` vanishes on every network whose tree of blobs is not a star** (`tob2025:supplement_pi_min_zero`, E22 of the report). -/
theorem isPrintedPiMin_zero {N : RootedNetwork V E X} [Fintype V] [Fintype E] (hN : N.IsPhylogenetic) {θ : MetricData E}
    (hθ : N.IsMetric θ) {ρ : ℝ} (hρ : 0 ≤ ρ ∧ ρ ≤ 1) (hne : ∃ s, Displays (treeOfBlobs N) s) :
    IsPrintedPiMin N (nmscCF N θ ρ) 0 := by
  obtain ⟨s, hs⟩ := hne
  refine ⟨⟨s, hs, isPrintedPi_zero hN hθ hρ hs⟩, ?_⟩
  rintro d ⟨s', hs', hd⟩
  exact (hd.unique (isPrintedPi_zero hN hθ hρ hs')).ge

/-- **"`π_min > 0`" is false** (`tob2025:supplement_pi_min_pos_false`, E22 of the report): the supplement's first sentence of the proof of Lemma 4, for
every network whose tree of blobs is not a star. -/
theorem not_printedPiMin_pos {N : RootedNetwork V E X} [Fintype V] [Fintype E] (hN : N.IsPhylogenetic) {θ : MetricData E}
    (hθ : N.IsMetric θ) {ρ : ℝ} (hρ : 0 ≤ ρ ∧ ρ ≤ 1) (hne : ∃ s, Displays (treeOfBlobs N) s) {π : ℝ}
    (hπ : IsPrintedPiMin N (nmscCF N θ ρ) π) : ¬ 0 < π := by
  rw [hπ.unique (isPrintedPiMin_zero hN hθ hρ hne)]
  exact lt_irrefl 0

/-- **The hypothesis of Lemma 4 as printed has no instance** (`tob2025:supplement_lemma4_vacuous`, E22 of the report): on a network whose tree of blobs is
not a star, no weights have errors below `δ = π_min / (2 |f₄(S)|)`. -/
theorem not_exists_printedError_lt {N : RootedNetwork V E X} [Fintype V] [Fintype E] (hN : N.IsPhylogenetic) {θ : MetricData E}
    (hθ : N.IsMetric θ) {ρ : ℝ} (hρ : 0 ≤ ρ ∧ ρ ≤ 1) (hne : ∃ s, Displays (treeOfBlobs N) s) {π : ℝ}
    (hπ : IsPrintedPiMin N (nmscCF N θ ρ) π) (w : QuartetTree X → ℝ) :
    ¬ ∀ s, |w s - nmscCF N θ ρ s| < π / (2 * ((Fintype.card X).choose 4 : ℝ)) := by
  obtain ⟨s, -⟩ := id hne
  intro h
  have h0 := h s
  rw [hπ.unique (isPrintedPiMin_zero hN hθ hρ hne), zero_div] at h0
  exact absurd h0 (not_lt.2 (abs_nonneg _))

end TOBQMC
