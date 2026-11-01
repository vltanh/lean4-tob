module

public import AllmanEtAl2023.Algorithm
public import TINNiK.NJ
public import Basic.Testing.Tails

/-!
# TINNiK and the outline of an algorithm in Allman, Baños, Mitchell, Rhodes 2023

Section 5 of that paper outlines an algorithm, `AllmanEtAl2023.Algorithm.outline`, with a test it doesn't specify ("step 2 requires the development of a novel statistical test"), and says "Like NANUQ, it can be shown to provide a statistically consistent estimate of the network features it seeks to infer". TINNiK is the later paper that develops it. So this module is the bridge, here because the modules of the earlier paper import no later paper.

* `cutReject`: the cut test at a level `α`, with the maximum likelihood topology. `outline_cut_eq_tinnik`: with this test, the outline is TINNiK's algorithm without its star test and its cutoff: `tinnik ml α β 0 M`, for any `β > 1`.
* `outline_cut_consistent`: **the consistency of the outline for generic parameters**, from `TINNiK.theorem4`; `outline_cut_consistent_nj`, with neighbor joining in step 4. Both have a tree of blobs in the paper's form, `(Trd hN hX).splits`.
* "This can be accomplished in time `O(n⁵)`" and "the computational time is `O((n + m) n⁴)`" are counts of operations in TINNiK's text: `stepThree_count`, `outline_operations_le`.
-/

@[expose] public noncomputable section

open Phylogenetics Phylogenetics.RootedNetwork Finset Filter Topology
open scoped Classical

namespace TINNiK

open AllmanEtAl2023 AllmanEtAl2023.Algorithm

variable {X : Type*} [Fintype X] [DecidableEq X]

section Consistency

variable {V E : Type*} [Fintype V] [Fintype E] {N : RootedNetwork V E X}

/-- **The test of the later paper**: the cut test at the level `α`, at the maximum likelihood topology. -/
def cutReject (ml : (QuartetTree X → ℝ) → Finset X → QuartetTree X) (α : ℝ) (c : QuartetTree X → ℝ) (q : Finset X) : Prop :=
  cutPValue c (ml c q) < α

/-- The star test of TINNiK has no effect at a level above one, since p-values on counts are at most one. -/
theorem not_le_starPValue {c : QuartetTree X → ℝ} (hc : ∀ r, 0 ≤ c r) {q : Finset X} (hq : q.card = 4) {β : ℝ} (hβ : 1 < β) : ¬ β ≤ starPValue .lrt c q := by
  have h0 := QuartetTests.starStat_nonneg c hc hq
  have h1 : starPValue .lrt c q ≤ 1 := by
    change Real.exp (-starStat c q / 2) ≤ 1
    exact Real.exp_le_one_iff.2 (by linarith)
  linarith

/-- **The bridge to TINNiK**: with the cut test, the outline is TINNiK's algorithm, without its star test (a level `β > 1`) and its cutoff (`δ = 0`). -/
theorem outline_cut_eq_tinnik (ml : (QuartetTree X → ℝ) → Finset X → QuartetTree X) (α : ℝ) {β : ℝ} (hβ : 1 < β) (M : TreeBuilder X) {c : QuartetTree X → ℝ} (hc : ∀ r, 0 ≤ c r) :
    outline (cutReject ml α) ml M c = tinnik ml α β 0 M c := by
  have hB : stepTwoB (cutReject ml α) c = testedB ml α β c := by
    ext q
    simp only [stepTwoB, testedB, cutReject, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨h4, h⟩
      exact ⟨h4, Or.inr h⟩
    · rintro ⟨h4, h | h⟩
      · exact absurd h (not_le_starPValue hc h4 hβ)
      · exact ⟨h4, h⟩
  have hT : stepTwoT (cutReject ml α) ml c = testedT ml α β c := by
    ext s
    simp only [stepTwoT, testedT, Set.mem_ofPred_eq]
    rw [← hB]
    simp only [stepTwoB, Set.mem_ofPred_eq, QuartetTree.card_taxa, true_and]
  simp only [outline, tinnik, stepThree, hB, hT]
  refine Finset.filter_congr fun x _ => or_congr Iff.rfl ⟨fun h => ⟨h.le, h⟩, fun h => h.2⟩

omit [Fintype X] in
theorem quartetCount_nonneg [Fintype X] {Γ : Type*} [Fintype Γ] (sides : Γ → Finset (Finset X)) {m : ℕ} (ω : Fin m → Γ) (r : QuartetTree X) : 0 ≤ quartetCount sides ω r := by
  unfold quartetCount
  positivity

/-- **"Like NANUQ, it can be shown to provide a statistically consistent estimate of the network features it seeks to infer"** (`a:claim:outline-consistent`, Section 5). For generic numerical parameters on a binary network, there are levels `α_m → 0` of the cut test such that the outline, with any exact tree building method and any selection of maximum likelihood topologies, returns `T_rd(𝒩⁻)` on `m` independent gene trees with probability tending to one. From `TINNiK.theorem4`. -/
theorem outline_cut_consistent (hN : IsBinaryNetwork N) (hX : 4 ≤ Fintype.card X) :
    ∃ A : Set (MetricData E), N.IsGenericNull A ∧
      ∀ θ, N.IsMetric θ → θ ∉ A →
        ∃ α : ℕ → ℝ, Tendsto α atTop (𝓝 0) ∧ (∀ m, 0 < α m) ∧
          ∀ (M : TreeBuilder X), IsExactBuilder M →
          ∀ (ml : (QuartetTree X → ℝ) → Finset X → QuartetTree X), IsMLSelection ml →
          ∀ hn : Nontrivial X,
            Tendsto (fun m => iidProb (geneTreeDist N θ 0) m fun ω =>
              outline (cutReject ml (α m)) ml M (quartetCount unroot ω) = (Trd hN hn).splits) atTop (𝓝 1) := by
  obtain ⟨A, hA, h⟩ := theorem4 hN.isPhylogenetic hX hN.isBinary
  refine ⟨A, hA, fun θ hθ hθA => ?_⟩
  obtain ⟨α, h1, h2, h3⟩ := h θ hθ hθA
  refine ⟨α, h1, h2, fun M hM ml hml hn => ?_⟩
  have key := h3 2 0 two_pos le_rfl two_pos M hM ml hml
  rw [Bridges.splits_Trd hN hn]
  refine key.congr fun m => ?_
  congr 1
  funext ω
  rw [outline_cut_eq_tinnik ml (α m) (by norm_num : (1 : ℝ) < 2) M (quartetCount_nonneg _ ω)]

/-- **The consistency of the outline with neighbor joining in step 4**: "a tree building method such as Neighbor-Joining". -/
theorem outline_cut_consistent_nj (hN : IsBinaryNetwork N) (hX : 4 ≤ Fintype.card X) :
    ∃ A : Set (MetricData E), N.IsGenericNull A ∧
      ∀ θ, N.IsMetric θ → θ ∉ A →
        ∃ α : ℕ → ℝ, Tendsto α atTop (𝓝 0) ∧ (∀ m, 0 < α m) ∧
          ∀ (tb : NJ.TieBreak X),
          ∀ (ml : (QuartetTree X → ℝ) → Finset X → QuartetTree X), IsMLSelection ml →
          ∀ hn : Nontrivial X,
            Tendsto (fun m => iidProb (geneTreeDist N θ 0) m fun ω =>
              outline (cutReject ml (α m)) ml (NJ.nj tb) (quartetCount unroot ω) = (Trd hN hn).splits) atTop (𝓝 1) := by
  obtain ⟨A, hA, h⟩ := outline_cut_consistent (X := X) hN hX
  refine ⟨A, hA, fun θ hθ hθA => ?_⟩
  obtain ⟨α, h1, h2, h3⟩ := h θ hθ hθA
  exact ⟨α, h1, h2, fun tb ml hml hn => h3 (NJ.nj tb) (NJ.isExactBuilder_nj tb) ml hml hn⟩

end Consistency

/-! ### The counts of operations -/

section Counts

/-- **"By minimizing the number of pairs of B-quartets considered, this can be accomplished in time `O(n⁵)`"**: the worklist of TINNiK's text compares each B-quartet with the `4 (n - 4)` sets sharing three taxa with it, at most `n⁴` times over. So at most `4 n⁵` comparisons, and its output is the closure of the rule. -/
theorem stepThree_count {B₀ : Finset (Finset X)} (hB₀ : ∀ q ∈ B₀, q.card = 4) (τ : Set (QuartetTree X)) :
    (∀ q, q ∈ (bQuartetInference B₀ τ).B ↔ BInferred (B₀ : Set (Finset X)) τ q) ∧
      (bQuartetInference B₀ τ).count ≤ 4 * Fintype.card X ^ 5 := by
  refine ⟨fun q => mem_bQuartetInference_iff hB₀ τ, ?_⟩
  obtain ⟨-, -, -, h4, hc, -⟩ := bQuartetInference_spec hB₀ τ
  rw [hc]
  set n := Fintype.card X
  have hB : (bQuartetInference B₀ τ).B.card ≤ n ^ 4 := by
    have hsub : (bQuartetInference B₀ τ).B ⊆ Finset.powersetCard 4 univ := fun q hq =>
      Finset.mem_powersetCard.2 ⟨Finset.subset_univ _, h4 q hq⟩
    calc (bQuartetInference B₀ τ).B.card ≤ (Finset.powersetCard 4 (univ : Finset X)).card := Finset.card_le_card hsub
      _ = n.choose 4 := by rw [Finset.card_powersetCard, Finset.card_univ]
      _ ≤ n ^ 4 := Nat.choose_le_pow n 4
  calc 4 * (n - 4) * (bQuartetInference B₀ τ).B.card ≤ 4 * n * n ^ 4 :=
        Nat.mul_le_mul (Nat.mul_le_mul_left _ (Nat.sub_le _ _)) hB
    _ = 4 * n ^ 5 := by ring

/-- **"In the end, the computational time is `O((n + m) n⁴)`, where `m` is the number of input gene trees and `n` the number of taxa"**: the count of operations of TINNiK's text, with neighbor joining in step 4. -/
theorem outline_operations_le {n m : ℕ} (hn : 1 ≤ n) : tinnikOperations n m (NJ.njOps n) ≤ (68 + 8) * ((m + n) * n ^ 4) :=
  tinnikOperations_nj_le hn

end Counts

end TINNiK
