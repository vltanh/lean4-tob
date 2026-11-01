module

public import ECToBlob.BinaryLawExample
public import ECToBlob.Section5
public import ECToBlob.SumOfPairs

/-!
# ECToBlob: what the paper says in passing

Each section quotes the paper's text, by its lines.

* **Line 289-306, inferred gene trees**: `tendsto_inferred`.
* **Lines 523-526, a single optimal tree**: `exists_oscillating_optimum`.
* **Lines 673-679, the taxa of Corollary 4.3 cannot be specified**: `Sunlet.not_corollary4_3_with_taxa`.
* **Line 728, "we strongly suspect"**: the statement `Assumption1ForAllRho`.
* **Lines 799-800, the other form of `Bon`**: `tendsto_altBon_div`.
* **Lines 810-813, a p-value tending to one**: `cauchyP_pair`.
* **Lines 892-893, the overall p-values need not increase**: `exists_treeTestP_decreasing`; **lines 914-916, the two rules**:
  `selectedIteration_early_le_late`, `selected_early_eq_late_of_monotone`; **lines 918-921, Step 10 is well defined**:
  `exists_early_selected`.
* **Lines 1164-1167, what valid levels need**: `tendsto_alpha_of_consistent`, `tendsto_beta_of_consistent`, and
  `BinaryLaw.OnFour.tendsto_log_beta_of_consistent` for the `o(n)` cutoffs of `β_n`; for `α_n`, `BinaryLaw.OnBlob.tendsto_log_alpha_of_consistent`, in `ECToBlob.LevelCutoffs`.
* **Lines 760-761, Pearson's statistic is asymptotically equivalent to the LRT**: `tendsto_starS_sub_pearsonS`.
* **Line 882, the nested quartet types**: `multipartitionQuartets_anti`, `multipartitionQuartets_subset_bipartitionQuartets`.
* **Lines 1415-1416, a quartet used for two edges**: `exists_quartet_of_two_edges`.
* **Lines 1437-1440, a p-value given the selection**: `tendsto_prob_le_given_gt`.
-/

@[expose] public noncomputable section

open Phylogenetics Phylogenetics.RootedNetwork Phylogenetics.QuartetTests Finset Filter Topology
open scoped Classical

namespace ECToBlob.InPassing

open ECToBlob.Deterministic ECToBlob.Coarsening ECToBlob.FalseEdge ECToBlob.Framework
open ECToBlob.DisplayedTree ECToBlob.FinNetwork ECToBlob.BinaryLaw

/-! ### The other form of `Bon`: lines 799-800 -/

/-- (`ecto:bon_alt`) "`Bon(P)` is sometimes defined as `1 - (1 - min(P))^k`, which gives almost the same value when `min(P)` is small": the ratio of the
two tends to one. -/
theorem tendsto_altBon_div {k : ℕ} (hk : 0 < k) :
    Tendsto (fun m : ℝ => (1 - (1 - m) ^ k) / (k * m)) (𝓝[>] 0) (𝓝 1) := by
  have hk' : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  have hd : HasDerivAt (fun m : ℝ => 1 - (1 - m) ^ k) (k : ℝ) 0 := by
    have h₁ : HasDerivAt (fun m : ℝ => 1 - m) (-1) 0 := by
      simpa using (hasDerivAt_id (0 : ℝ)).const_sub 1
    have h₂ := h₁.pow k
    have h₃ := h₂.const_sub 1
    simpa using h₃
  have hs := hd.hasDerivWithinAt (s := Set.Ioi 0)
  rw [hasDerivWithinAt_iff_tendsto_slope' (by simp)] at hs
  have hlim : Tendsto (fun m : ℝ => slope (fun m : ℝ => 1 - (1 - m) ^ k) 0 m / k) (𝓝[>] 0)
      (𝓝 ((k : ℝ) / k)) := hs.div_const _
  rw [div_self hk'] at hlim
  refine hlim.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with m hm
  have hm' : m ≠ 0 := (Set.mem_Ioi.1 hm).ne'
  simp only [slope, vsub_eq_sub, sub_zero, smul_eq_mul]
  simp only [one_pow, sub_self, sub_zero]
  field_simp

/-- The inequality between the two forms: the second is at most `k m`. -/
theorem altBon_le {k : ℕ} {m : ℝ} (h1 : m ≤ 1) : 1 - (1 - m) ^ k ≤ k * m := by
  have := one_add_mul_le_pow (a := -m) (by linarith) k
  have h' : (1 : ℝ) + -m = 1 - m := by ring
  rw [h'] at this
  linarith

/-! ### A p-value tending to one: lines 810-813 -/

/-- (`ecto:cauchy_pair`) "If one p-value tends to 1, then the Cauchy combination p-value need not go to 0": with the p-values `η` and `1 - η` it is `1/2` for
all `η`. -/
theorem cauchyP_pair {η : ℝ} (h0 : 0 < η) (h1 : η < 1) : cauchyP {η, 1 - η} = 1 / 2 := by
  have hne₀ : (0 : ℝ) ∉ ({η, 1 - η} : Multiset ℝ) := by
    simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton, not_or]
    constructor <;> intro h <;> linarith
  have hne₁ : (1 : ℝ) ∉ ({η, 1 - η} : Multiset ℝ) := by
    simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton, not_or]
    constructor <;> intro h <;> linarith
  rw [cauchyP, ite_eq_right hne₀, ite_eq_right hne₁]
  have hsum : cauchyTransform η + cauchyTransform (1 - η) = 0 := by
    unfold cauchyTransform
    have h₂ : Real.pi * (1 / 2 - (1 - η)) = -(Real.pi * (1 / 2 - η)) := by ring
    rw [h₂, Real.tan_neg]
    ring
  simp only [Multiset.insert_eq_cons, Multiset.map_cons, Multiset.map_singleton, Multiset.sum_cons,
    Multiset.sum_singleton, hsum, zero_div]
  simp [cauchyInverse]

/-! ### The selection rules: lines 892-893, 914-916, 918-921 -/

section Rules

variable {X : Type*} [Fintype X] [DecidableEq X] (o : ECToBlobOptions) (α β : ℝ)
  (c : QuartetTree X → ℝ) (T₀ : Finset (Finset X))

/-- The last tree has no internal edge. -/
theorem internalSides_last : internalSides (treeSeq o β c T₀ (lastIteration o β c T₀)) = ∅ := by
  have hmem : lastIteration o β c T₀ ∈ {i | internalSides (treeSeq o β c T₀ i) = ∅} :=
    Nat.sInf_mem exists_internalSides_eq_empty
  exact hmem

/-- "When `T_k` is reduced to a star tree ... leading to `p_k = 1`". -/
theorem treeT1P_last : treeT1P o c (treeSeq o β c T₀ (lastIteration o β c T₀)) = 1 := by
  have hemp : (univ.filter fun s => Displays (treeSeq o β c T₀ (lastIteration o β c T₀)) s) = ∅ := by
    refine Finset.eq_empty_of_forall_notMem fun s hs => ?_
    obtain ⟨B, hB, hBs⟩ := (mem_filter.1 hs).2
    have : B ∈ internalSides (treeSeq o β c T₀ (lastIteration o β c T₀)) :=
      mem_internalSides.2 ⟨hB, two_le_card_of_inter_taxa_mem hBs⟩
    rw [internalSides_last] at this
    simp at this
  unfold treeT1P combineP
  rw [hemp]
  simp

/-- (`ecto:step10_defined`) "Therefore, there exists at least one iteration (the last one) with `p_ki ≥ α`, and Step 10 yields well-defined notions." -/
theorem exists_early_selected (hα : α ≤ 1) :
    ∃ i ≤ lastIteration o β c T₀, α ≤ treeT1P o c (treeSeq o β c T₀ i) :=
  ⟨_, le_rfl, by rw [treeT1P_last]; exact hα⟩

/-- The index selected by the early rule. -/
def earlyIndex : ℕ := sInf {i | i ≤ lastIteration o β c T₀ ∧ α ≤ treeT1P o c (treeSeq o β c T₀ i)}

/-- The index selected by the late rule. -/
def lateIndex : ℕ :=
  if ∃ i ≤ lastIteration o β c T₀, treeT1P o c (treeSeq o β c T₀ i) < α then
    sSup {i | i ≤ lastIteration o β c T₀ ∧ treeT1P o c (treeSeq o β c T₀ i) < α} + 1
  else 0

theorem selectedIteration_early {o : ECToBlobOptions} (hr : o.rule = .early) :
    selectedIteration o α β c T₀ = earlyIndex o α β c T₀ := by
  simp [selectedIteration, earlyIndex, hr]

theorem selectedIteration_late {o : ECToBlobOptions} (hr : o.rule = .late) :
    selectedIteration o α β c T₀ = lateIndex o α β c T₀ := by
  simp [selectedIteration, lateIndex, hr]

/-- (`ecto:early_le_late`) **"Otherwise, the early method tree is more resolved than the late one"** (lines 915-916): the early rule selects no later iteration
than the late rule, so the late tree is a contraction of the early tree. -/
theorem selectedIteration_early_le_late (hα : α ≤ 1) :
    earlyIndex o α β c T₀ ≤ lateIndex o α β c T₀ ∧
      treeSeq o β c T₀ (lateIndex o α β c T₀) ⊆ treeSeq o β c T₀ (earlyIndex o α β c T₀) := by
  have hle : earlyIndex o α β c T₀ ≤ lateIndex o α β c T₀ := by
    unfold earlyIndex lateIndex
    split_ifs with h
    · -- the iteration after the last rejection is not rejected, if it exists
      obtain ⟨i₀, hi₀, hi₀'⟩ := h
      set S := {i | i ≤ lastIteration o β c T₀ ∧ treeT1P o c (treeSeq o β c T₀ i) < α} with hS
      have hbdd : BddAbove S := ⟨lastIteration o β c T₀, fun i hi => hi.1⟩
      have hne : S.Nonempty := ⟨i₀, hi₀, hi₀'⟩
      have hmem : sSup S ∈ S := Nat.sSup_mem hne hbdd
      have hlt : sSup S < lastIteration o β c T₀ := by
        refine lt_of_le_of_ne hmem.1 fun heq => ?_
        have h₂ := hmem.2
        rw [heq, treeT1P_last] at h₂
        linarith
      refine Nat.sInf_le ⟨by omega, ?_⟩
      by_contra hcon
      have : sSup S + 1 ∈ S := ⟨by omega, not_le.1 hcon⟩
      have := le_csSup hbdd this
      omega
    · push Not at h
      have h₀ : sInf {i | i ≤ lastIteration o β c T₀ ∧ α ≤ treeT1P o c (treeSeq o β c T₀ i)} = 0 :=
        Nat.sInf_eq_zero.2 (Or.inl ⟨Nat.zero_le _, h 0 (Nat.zero_le _)⟩)
      exact h₀.le
  exact ⟨hle, treeSeq_anti hle⟩

/-- (`ecto:early_eq_late`) **"If the sequence of combined p-values is monotone, then both methods agree"** (lines 914-915). -/
theorem selected_early_eq_late_of_monotone (hα : α ≤ 1)
    (hm : ∀ i j, i ≤ j → j ≤ lastIteration o β c T₀ →
      treeT1P o c (treeSeq o β c T₀ i) ≤ treeT1P o c (treeSeq o β c T₀ j)) :
    earlyIndex o α β c T₀ = lateIndex o α β c T₀ := by
  refine le_antisymm (selectedIteration_early_le_late o α β c T₀ hα).1 ?_
  unfold lateIndex
  split_ifs with h
  · set S := {i | i ≤ lastIteration o β c T₀ ∧ treeT1P o c (treeSeq o β c T₀ i) < α} with hS
    have hbdd : BddAbove S := ⟨lastIteration o β c T₀, fun i hi => hi.1⟩
    obtain ⟨hl, hge⟩ := Nat.sInf_mem (s := {i | i ≤ lastIteration o β c T₀ ∧
      α ≤ treeT1P o c (treeSeq o β c T₀ i)}) (exists_early_selected o α β c T₀ hα)
    refine Nat.succ_le_of_lt ?_
    show sSup S < earlyIndex o α β c T₀
    by_contra hcon
    push Not at hcon
    obtain ⟨i₀, hi₀, hi₀'⟩ := h
    have hmem : sSup S ∈ S := Nat.sSup_mem ⟨i₀, hi₀, hi₀'⟩ hbdd
    have h₁ := hm _ _ hcon hmem.1
    exact absurd hmem.2 (not_lt_of_ge (hge.trans h₁))
  · exact Nat.zero_le _

variable {o α β c T₀} in
/-- If the output with the early rule is `T₀`, with an internal edge, then `T₀` is the first tree and it is not rejected. -/
theorem le_treeT1P_of_ectoblob_eq (hr : o.rule = .early) (hα : α ≤ 1) {A : Finset X}
    (hA : A ∈ T₀) (hAint : 2 ≤ A.card ∧ 2 ≤ Aᶜ.card) (h : ectoblob o α β c T₀ = T₀) :
    α ≤ treeT1P o c T₀ := by
  have hsel : treeSeq o β c T₀ (selectedIteration o α β c T₀) = T₀ := h
  have hsub : T₀ ⊆ treeSeq o β c T₀ 0 := by
    conv_lhs => rw [← hsel]
    exact treeSeq_anti (Nat.zero_le _)
  have hfirst : treeSeq o β c T₀ 0 = T₀ := Finset.Subset.antisymm afterStar_subset hsub
  have hidx : selectedIteration o α β c T₀ = 0 := by
    by_contra hne
    obtain ⟨i, hi⟩ := Nat.exists_eq_succ_of_ne_zero hne
    rw [hi] at hsel
    have hstep : treeSeq o β c T₀ (i + 1) ⊆ treeSeq o β c T₀ i := treeSeq_anti (Nat.le_succ i)
    have hint : (internalSides (treeSeq o β c T₀ i)).Nonempty :=
      ⟨A, mem_internalSides.2 ⟨hstep (hsel.symm ▸ hA), hAint⟩⟩
    have hss : treeSeq o β c T₀ (i + 1) ⊂ treeSeq o β c T₀ i := by
      rw [treeSeq_succ]
      exact contractStep_ssubset (o := o) (c := c) (T₀ := T₀) hint
    have h₃ : treeSeq o β c T₀ i ⊆ T₀ := (treeSeq_anti (Nat.zero_le i)).trans hfirst.le
    exact hss.2 (h₃.trans hsel.ge)
  rw [selectedIteration_early α β c T₀ hr] at hidx
  have hmemset := Nat.sInf_mem (s := {i | i ≤ lastIteration o β c T₀ ∧
    α ≤ treeT1P o c (treeSeq o β c T₀ i)}) (exists_early_selected o α β c T₀ hα)
  have h₅ := hmemset.2
  have h₆ : sInf {i | i ≤ lastIteration o β c T₀ ∧ α ≤ treeT1P o c (treeSeq o β c T₀ i)} = 0 := hidx
  rw [h₆, hfirst] at h₅
  exact h₅

end Rules

/-! ### "We strongly suspect": line 728 -/

/-- (`ecto:line728`) **The statement of line 728**: "We strongly suspect Assumption 1 also holds for the NMSC model with common or correlated
inheritance, but do not verify that here". This is Proposition 5.1 for all inheritance correlations `0 ≤ ρ ≤ 1`. It is stated, and not
proved: `assumption1Forward_rho` is the part that holds, and `ECToBlob.proposition5_1` is `ρ = 0`. -/
def Assumption1ForAllRho : Prop :=
  ∀ {V E X : Type} [Fintype V] [Fintype E] [Fintype X] [DecidableEq X] (N : RootedNetwork V E X),
    N.IsPhylogenetic → BlobDegreeAtMostThree N → ∀ ρ : ℝ, 0 ≤ ρ → ρ ≤ 1 →
    (∀ θ, N.IsMetric θ → NoAnomalousQuartets N (nmscCF N θ ρ) →
      Assumption1Forward N (nmscCF N θ ρ)) ∧
    IsNullParams N {θ | N.IsMetric θ ∧ NoAnomalousQuartets N (nmscCF N θ ρ) ∧
      ¬ Assumption1Converse N (nmscCF N θ ρ)}

/-- The forward half of the statement of line 728 holds, for all `ρ`, on every network. -/
theorem assumption1Forward_rho {V E X : Type*} [Fintype V] [Fintype E] [Fintype X] [DecidableEq X]
    {N : RootedNetwork V E X} (hN : N.IsPhylogenetic) {θ : MetricData E} (hθ : N.IsMetric θ) {ρ : ℝ}
    (hρ : 0 ≤ ρ ∧ ρ ≤ 1) (hano : NoAnomalousQuartets N (nmscCF N θ ρ)) :
    Assumption1Forward N (nmscCF N θ ρ) :=
  ⟨fun q hq ht => NMSC.trivial_uniform hN hθ hρ q hq ht,
    fun s hs => ⟨hano s hs, NMSC.cut_alternatives hN hθ hρ s hs⟩⟩

/-! ### The taxa of Corollary 4.3 cannot be specified: lines 673-679 -/

namespace Sunlet

/-- The tails of the arcs of the 5-sunlet with the hybrid taxon `a`: the taxa are `a, b, c, d, e = 0, …, 4`, the reticulation `h = 5`, and
`v_b, v_e, v_c, v_d = 6, 7, 8, 9`, with the root `10` on the cycle. The arcs are, in order, `r v_c`, `r v_d`, `v_c v_b`, `v_d v_e`, `v_b h`,
`v_e h`, `h a`, `v_b b`, `v_c c`, `v_d d`, `v_e e`. -/
def src : Fin 11 → Fin 11 := ![10, 10, 8, 9, 6, 7, 5, 6, 8, 9, 7]

/-- The heads of the arcs. -/
def tgt : Fin 11 → Fin 11 := ![8, 9, 6, 7, 5, 5, 0, 1, 2, 3, 4]

/-- The taxa, as vertices. -/
def lf : Fin 5 → Fin 11 := ![0, 1, 2, 3, 4]

/-- What each vertex reaches. -/
def desc : Fin 11 → Finset (Fin 11) :=
  ![{0}, {1}, {2}, {3}, {4}, {0, 5}, {0, 1, 5, 6}, {0, 4, 5, 7}, {0, 1, 2, 5, 6, 8}, {0, 3, 4, 5, 7, 9},
    {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10}]

/-- What the root reaches off each arc. -/
def avoid : Fin 11 → Finset (Fin 11) :=
  ![{0, 3, 4, 5, 7, 9, 10}, {0, 1, 2, 5, 6, 8, 10}, {0, 2, 3, 4, 5, 7, 8, 9, 10},
    {0, 1, 2, 3, 5, 6, 8, 9, 10}, {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10}, {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10},
    {1, 2, 3, 4, 5, 6, 7, 8, 9, 10}, {0, 2, 3, 4, 5, 6, 7, 8, 9, 10}, {0, 1, 3, 4, 5, 6, 7, 8, 9, 10},
    {0, 1, 2, 4, 5, 6, 7, 8, 9, 10}, {0, 1, 2, 3, 5, 6, 7, 8, 9, 10}]

theorem tables : Tables src tgt 10 desc avoid :=
  ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩

/-- The 5-sunlet. -/
abbrev net : RootedNetwork (Fin 11) (Fin 11) (Fin 5) := FinNetwork.net src tgt 10 lf

theorem net_isPhylogenetic : net.IsPhylogenetic :=
  isPhylogenetic_of_down (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide)

/-- (`ecto:cor4_3_taxa`) **Lines 673-679.** "Consider a 5-cycle sunlet network on taxa `a, b, c, d, e`, with `a` the hybrid descendant. Set `A1 = {a, b}`,
`A2 = {c}`, `B1 = {d}`, `B2 = {e}`, and specify the taxa `b` in `A1`, and `d` in `B1`. Then no quartets that involve the hybrid taxon `a`
would be considered, and we would erroneously conclude that `abc|de` is a cut-edge split on `N`." The only quartet with the specified taxa
is `bc|de`, a cut split of its induced network, and `abc|de` is not a cut split of the network. -/
theorem not_corollary4_3_with_taxa :
    net.IsPhylogenetic ∧ ¬ net.HasCutSplit (({0, 1, 2} : Finset (Fin 5)) : Set (Fin 5)) ∧
      net.HasCutSplitOn (({1, 2, 3, 4} : Finset (Fin 5)) : Set (Fin 5)) (({1, 2} : Finset (Fin 5)) : Set (Fin 5)) := by
  have hN := net_isPhylogenetic
  refine ⟨hN, ?_, ?_⟩
  · rw [tables.hasCutSplit_iff hN]
    decide
  · have hc : ({1, 2, 3, 4} : Finset (Fin 5)).card = 4 := by decide
    exact FalseEdge.hasCutSplitOn_of_inducedCutSplit hc
      (inducedCutSplit_of_rdom hN hc (tables.rdom_iff.2 (by decide)))

end Sunlet

/-! ### A quartet used for two edges: lines 1415-1416 -/

/-- (`ecto:quartet_two_edges`) "Some individual quartet p-values would be indirectly used multiple times, as some 4-taxon sets may be used to derive `p_e` for
multiple edges `e`": the quartet `bc|de` is in the bipartition sets of the two edges of the tree `FinNetwork.Binary.T₀`. -/
theorem exists_quartet_of_two_edges :
    ∃ s : QuartetTree (Fin 5), s ∈ bipartitionQuartets ({3, 4} : Finset (Fin 5)) ∧
      s ∈ bipartitionQuartets ({1, 2} : Finset (Fin 5)) := by
  have hc : ({3, 4, 1, 2} : Finset (Fin 5)).card = 4 := by decide
  refine ⟨quartetTree 3 4 1 2 hc, mem_filter.2 ⟨mem_univ _, ?_⟩, mem_filter.2 ⟨mem_univ _, ?_⟩⟩
  · rw [taxa_quartetTree, quartetTree_val]
    decide
  · rw [taxa_quartetTree, quartetTree_val]
    decide

/-! ### A p-value given a selection on the same data: lines 1437-1440 -/

/-- (`ecto:sec10_selection`) "Conditional on its split estimated to be in `T₀`, this distribution may be non-uniform". If the event of selection depends on the data
through the p-value, here `1/2 < p`, then the conditional probability of `p ≤ 3/4` tends to `1/2`, not to `3/4`, for an asymptotically
uniform `p`. This is for a selection chosen for the purpose. For the selection by the MQS criterion, the paper's case, a statement would
need the joint limit of the counts of several quartets, and it is not proved here. -/
theorem tendsto_prob_le_given_gt {Γ : Type*} [Fintype Γ] {dist : Γ → ℝ} (hd : IsDist dist)
    {p : (n : ℕ) → (Fin n → Γ) → ℝ} (hp : AsymptoticallyUniform dist p) :
    Tendsto (fun n => iidProb dist n (fun ω => 1 / 2 < p n ω ∧ p n ω ≤ 3 / 4) /
      iidProb dist n fun ω => 1 / 2 < p n ω) atTop (𝓝 (1 / 2)) := by
  have h₁ := hp (1 / 2) (by norm_num) (by norm_num)
  have h₂ := hp (3 / 4) (by norm_num) (by norm_num)
  have hgt : Tendsto (fun n => iidProb dist n fun ω => 1 / 2 < p n ω) atTop (𝓝 (1 / 2)) := by
    have := (tendsto_const_nhds (x := (1 : ℝ))).sub h₁
    norm_num at this
    refine this.congr fun n => ?_
    rw [← iidProb_not hd]
    simp only [not_le]
  have hand : Tendsto (fun n => iidProb dist n fun ω => 1 / 2 < p n ω ∧ p n ω ≤ 3 / 4) atTop (𝓝 (1 / 4)) := by
    have := h₂.sub h₁
    norm_num at this
    refine this.congr fun n => ?_
    rw [sub_eq_iff_eq_add]
    unfold iidProb
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun ω _ => ?_
    by_cases h₃ : p n ω ≤ 1 / 2
    · have h₄ : p n ω ≤ 3 / 4 := by linarith
      have h₆ : ¬ (1 / 2 < p n ω ∧ p n ω ≤ 3 / 4) := fun h => absurd h.1 (not_lt.2 h₃)
      rw [ite_eq_left h₄, ite_eq_right h₆, ite_eq_left h₃, zero_add]
    · have h₅ := not_le.1 h₃
      by_cases h₄ : p n ω ≤ 3 / 4
      · have h₆ : 1 / 2 < p n ω ∧ p n ω ≤ 3 / 4 := ⟨h₅, h₄⟩
        rw [ite_eq_left h₄, ite_eq_left h₆, ite_eq_right h₃, add_zero]
      · have h₆ : ¬ (1 / 2 < p n ω ∧ p n ω ≤ 3 / 4) := fun h => h₄ h.2
        rw [ite_eq_right h₄, ite_eq_right h₆, ite_eq_right h₃, add_zero]
  have := hand.div hgt (by norm_num)
  norm_num at this
  exact this

/-! ### Inferred gene trees: lines 293-306 -/

section Inferred

variable {X : Type*} [Fintype X] [DecidableEq X] {dist : UnrootedGeneTree X → ℝ}

/-- **A method of inference from sequences**: for each length `L` and true gene tree `G`, the law `κ L G` of the inferred tree. It is
*consistent on resolved quartets* if it returns a quartet displayed on `G` with probability tending to one as `L` grows, and *unbiased on
polytomies* if on a quartet that `G` leaves unresolved it gives its three resolutions the same probability, a star being one case. -/
structure IsInference (κ : ℕ → UnrootedGeneTree X → UnrootedGeneTree X → ℝ) : Prop where
  dist : ∀ L G, IsDist (κ L G)
  resolved : ∀ (G : UnrootedGeneTree X) (s : QuartetTree X), Displays G.val s →
    Tendsto (fun L => ∑ H, if Displays H.val s then κ L G H else 0) atTop (𝓝 1)
  unbiased : ∀ (L : ℕ) (G : UnrootedGeneTree X) (s : QuartetTree X), (∀ r ∈ treesOn s.taxa, ¬ Displays G.val r) →
    ∀ r ∈ treesOn s.taxa, (∑ H, if Displays H.val r then κ L G H else 0) =
      ∑ H, if Displays H.val s then κ L G H else 0

/-- The law of the inferred gene tree. -/
def inferredDist (dist : UnrootedGeneTree X → ℝ) (κ : ℕ → UnrootedGeneTree X → UnrootedGeneTree X → ℝ) (L : ℕ)
    (H : UnrootedGeneTree X) : ℝ := ∑ G, dist G * κ L G H

variable {κ : ℕ → UnrootedGeneTree X → UnrootedGeneTree X → ℝ}

theorem inferredDist_isDist (hd : IsDist dist) (hκ : IsInference κ) (L : ℕ) : IsDist (inferredDist dist κ L) := by
  refine ⟨fun H => Finset.sum_nonneg fun G _ => mul_nonneg (hd.1 G) ((hκ.dist L G).1 H), ?_⟩
  unfold inferredDist
  rw [Finset.sum_comm]
  simp only [← Finset.mul_sum, (hκ.dist L _).2, mul_one, hd.2]

/-- The expected contribution of the inferred tree, given the true one, tends to that of the true one. -/
theorem tendsto_contribution (hκ : IsInference κ) (G : UnrootedGeneTree X) (r : QuartetTree X) :
    Tendsto (fun L => ∑ H, κ L G H * geneContribution H.val r) atTop (𝓝 (geneContribution G.val r)) := by
  set a : ℕ → QuartetTree X → ℝ := fun L t => ∑ H, κ L G H * geneContribution H.val t with ha
  have hsum : ∀ L, ∑ t ∈ treesOn r.taxa, a L t = 1 := by
    intro L
    simp only [ha]
    rw [Finset.sum_comm]
    simp only [← Finset.mul_sum, sum_geneContribution (Subtype.property _) r.card_taxa, mul_one]
    exact (hκ.dist L G).2
  have hnn : ∀ L t, 0 ≤ a L t := fun L t => Finset.sum_nonneg fun H _ =>
    mul_nonneg ((hκ.dist L G).1 H) (geneContribution_nonneg _ _)
  have hge : ∀ L t, (∑ H, if Displays H.val t then κ L G H else 0) ≤ a L t := by
    intro L t
    refine Finset.sum_le_sum fun H _ => ?_
    have hk := (hκ.dist L G).1 H
    by_cases h : Displays H.val t
    · simp [geneContribution, h]
    · rw [ite_eq_right h]
      exact mul_nonneg hk (geneContribution_nonneg _ _)
  by_cases hres : ∃ s ∈ treesOn r.taxa, Displays G.val s
  · -- the true tree resolves the quartet
    obtain ⟨s, hs, hds⟩ := hres
    have hle : ∀ L, a L s ≤ 1 := by
      intro L
      rw [← hsum L]
      exact Finset.single_le_sum (fun t _ => hnn L t) hs
    have hs₁ : Tendsto (fun L => a L s) atTop (𝓝 1) :=
      tendsto_of_tendsto_of_tendsto_of_le_of_le (hκ.resolved G s hds) tendsto_const_nhds
        (fun L => hge L s) hle
    obtain ⟨h₁, h₀⟩ := geneContribution_of_displays G.2 hds
    by_cases hrs : r = s
    · rw [hrs, h₁]
      exact hs₁
    · have halt : r ∈ s.alternatives :=
        QuartetTree.mem_alternatives.2 ⟨(mem_treesOn.1 hs).symm, hrs⟩
      rw [h₀ r halt]
      have hup : ∀ L, a L r ≤ 1 - a L s := by
        intro L
        have hpair : a L r + a L s ≤ ∑ t ∈ treesOn r.taxa, a L t := by
          have hsub : ({r, s} : Finset (QuartetTree X)) ⊆ treesOn r.taxa := by
            intro t ht
            simp only [mem_insert, mem_singleton] at ht
            rcases ht with rfl | rfl
            · exact QuartetTests.mem_treesOn_taxa _
            · exact hs
          rw [← Finset.sum_pair hrs]
          exact Finset.sum_le_sum_of_subset_of_nonneg hsub fun t _ _ => hnn L t
        rw [hsum L] at hpair
        linarith
      have hlim : Tendsto (fun L => 1 - a L s) atTop (𝓝 0) := by
        have h := (tendsto_const_nhds (x := (1 : ℝ))).sub hs₁
        rwa [sub_self] at h
      exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim (fun L => hnn L r) hup
  · -- the true tree leaves it unresolved: the contribution is `1/3` for all `L`
    push Not at hres
    have hG : geneContribution G.val r = 1 / 3 := by
      unfold geneContribution
      rw [ite_eq_right (hres r (QuartetTests.mem_treesOn_taxa r)), ite_eq_left hres]
    rw [hG]
    have hconst : ∀ L, a L r = 1 / 3 := by
      intro L
      have heq : ∀ t ∈ treesOn r.taxa, a L t = a L r := by
        intro t ht
        have ht' : t.taxa = r.taxa := mem_treesOn.1 ht
        simp only [ha]
        have hunb := hκ.unbiased L G r hres t ht
        have hsplit : ∀ u : QuartetTree X, u.taxa = r.taxa → ∑ H, κ L G H * geneContribution H.val u =
            (∑ H, if Displays H.val u then κ L G H else 0) +
              (1 / 3) * ∑ H, if ∀ v ∈ treesOn r.taxa, ¬ Displays H.val v then κ L G H else 0 := by
          intro u hu
          rw [Finset.mul_sum, ← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun H _ => ?_
          unfold geneContribution
          rw [hu]
          by_cases h₁ : Displays H.val u
          · have h₂ : ¬ ∀ v ∈ treesOn r.taxa, ¬ Displays H.val v := fun h =>
              h u (mem_treesOn.2 hu) h₁
            rw [ite_eq_left h₁, ite_eq_left h₁, ite_eq_right h₂]
            ring
          · by_cases h₂ : ∀ v ∈ treesOn r.taxa, ¬ Displays H.val v
            · rw [ite_eq_right h₁, ite_eq_left h₂, ite_eq_right h₁, ite_eq_left h₂]
              ring
            · rw [ite_eq_right h₁, ite_eq_right h₂, ite_eq_right h₁, ite_eq_right h₂]
              ring
        rw [hsplit t ht', hsplit r rfl, hunb]
      have := hsum L
      rw [Finset.sum_congr rfl heq, Finset.sum_const, card_treesOn r.card_taxa, nsmul_eq_mul] at this
      push_cast at this
      linarith
    exact Tendsto.congr (fun L => (hconst L).symm) tendsto_const_nhds

/-- The concordance factors of the inferred trees tend to those of the true trees. -/
theorem tendsto_expectedCF_inferred (hκ : IsInference κ) (r : QuartetTree X) :
    Tendsto (fun L => expectedCF (inferredDist dist κ L) r) atTop (𝓝 (expectedCF dist r)) := by
  have heq : ∀ L, expectedCF (inferredDist dist κ L) r =
      ∑ G, dist G * ∑ H, κ L G H * geneContribution H.val r := by
    intro L
    unfold expectedCF inferredDist
    simp only [Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun G _ => Finset.sum_congr rfl fun H _ => by ring
  refine Tendsto.congr (fun L => (heq L).symm) ?_
  have hlim := tendsto_finsetSum (Finset.univ : Finset (UnrootedGeneTree X)) fun G _ =>
    (tendsto_contribution hκ G r).const_mul (dist G)
  exact hlim

/-- (`ecto:inferred_gene_trees`) **Lines 293-306.** "It also holds for gene trees inferred from sequences of growing length, provided that the gene tree inference
method for a true polytomous quartet either returns the correct star topology or is unbiased in which resolution it returns." For `n`
loci, whose sequences have lengths `L n → ∞`, the empirical concordance factors of the inferred trees tend to the concordance factors of
the model. -/
theorem tendsto_inferred (hd : IsDist dist) (hκ : IsInference κ) {L : ℕ → ℕ} (hL : Tendsto L atTop atTop)
    {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n => iidProb (inferredDist dist κ (L n)) n fun ω =>
      ∀ r : QuartetTree X, |empiricalCF ω r - expectedCF dist r| < ε) atTop (𝓝 1) := by
  have hdL := fun n => inferredDist_isDist (dist := dist) hd hκ (L n)
  have hmean : ∀ r, ∀ᶠ n in atTop, |expectedCF (inferredDist dist κ (L n)) r - expectedCF dist r| < ε / 2 :=
    fun r => by
      have h := (tendsto_expectedCF_inferred (dist := dist) hκ r).comp hL
      exact (Metric.tendsto_nhds.1 h (ε / 2) (half_pos hε)).mono fun n hn => by
        simpa [Real.dist_eq] using hn
  set K : ℝ := (Fintype.card (QuartetTree X) : ℝ) with hK
  -- Hoeffding's inequality, uniformly in the law
  have hbound : ∀ n : ℕ, 0 < n → ∀ r, iidProb (inferredDist dist κ (L n)) n (fun ω =>
      ε / 2 ≤ |empiricalCF ω r - expectedCF (inferredDist dist κ (L n)) r|) ≤
        2 * Real.exp (-(n * (ε / 2) ^ 2 / (8 * 2 ^ 2))) := by
    intro n hn r
    set D := inferredDist dist κ (L n) with hD
    have hDd : IsDist D := hdL n
    set μ := expectedCF D r with hμ
    have hμ₀ : 0 ≤ μ := expectedCF_nonneg hDd r
    have hμ₁ : μ ≤ 1 := by
      have := sum_expectedCF hDd r.card_taxa
      rw [← this]
      exact Finset.single_le_sum (fun t _ => expectedCF_nonneg hDd t) (QuartetTests.mem_treesOn_taxa r)
    have hg : ∀ G : UnrootedGeneTree X, 0 ≤ geneContribution G.val r ∧ geneContribution G.val r ≤ 1 := by
      intro G
      unfold geneContribution
      split_ifs <;> norm_num
    have hbd₁ : ∀ G : UnrootedGeneTree X, |geneContribution G.val r - μ| ≤ 2 := fun G => by
      rw [abs_le]
      constructor <;> linarith [(hg G).1, (hg G).2]
    have hbd₂ : ∀ G : UnrootedGeneTree X, |-(geneContribution G.val r - μ)| ≤ 2 := fun G => by
      rw [abs_neg]
      exact hbd₁ G
    have hzero : ∑ G, D G * (geneContribution G.val r - μ) = 0 := by
      simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hDd.2, one_mul]
      unfold expectedCF at hμ
      linarith
    have ht : 0 < ε / 2 := half_pos hε
    have h₁ := SumOfPairs.iidProb_mean_ge_le hDd (by norm_num : (0 : ℝ) < 2) hbd₁ hzero.le ht hn
    have h₂ := SumOfPairs.iidProb_mean_ge_le hDd (by norm_num : (0 : ℝ) < 2) hbd₂
      (by simp only [mul_neg, Finset.sum_neg_distrib, hzero, neg_zero, le_refl]) ht hn
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    have hsumeq : ∀ ω : Fin n → UnrootedGeneTree X,
        (∑ i, (geneContribution (ω i).val r - μ)) / n = empiricalCF ω r - μ := by
      intro ω
      unfold empiricalCF
      rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      field_simp
    have himp : iidProb D n (fun ω => ε / 2 ≤ |empiricalCF ω r - μ|) ≤
        iidProb D n (fun ω => ε / 2 ≤ (∑ i, (geneContribution (ω i).val r - μ)) / n) +
          iidProb D n (fun ω => ε / 2 ≤ (∑ i, -(geneContribution (ω i).val r - μ)) / n) := by
      refine le_trans (iidProb_mono hDd fun ω hω => ?_) (iidProb_or_le hDd _ _)
      rcases le_abs.1 hω with h | h
      · exact Or.inl (by rw [hsumeq]; exact h)
      · refine Or.inr ?_
        rw [Finset.sum_neg_distrib, neg_div, hsumeq]
        exact h
    linarith
  have hexp : Tendsto (fun n : ℕ => (K + 1) * (2 * Real.exp (-(n * (ε / 2) ^ 2 / (8 * 2 ^ 2))))) atTop (𝓝 0) := by
    have h₁ : Tendsto (fun n : ℕ => (n : ℝ) * ((ε / 2) ^ 2 / (8 * 2 ^ 2))) atTop atTop :=
      tendsto_natCast_atTop_atTop.atTop_mul_const (by positivity)
    have h₂ := Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp h₁)
    have h₃ := h₂.const_mul (2 : ℝ)
    have h₄ := h₃.const_mul (K + 1)
    simp only [mul_zero] at h₄
    refine h₄.congr fun n => ?_
    simp only [Function.comp]
    ring_nf
  refine tendsto_order.2 ⟨fun a ha => ?_, fun a ha => ?_⟩
  swap
  · exact Eventually.of_forall fun n => (iidProb_le_one (hdL n) n _).trans_lt ha
  filter_upwards [eventually_all.2 hmean, hexp.eventually (gt_mem_nhds (by linarith : 0 < 1 - a)),
    eventually_gt_atTop 0] with n hn₁ hn₂ hn₃
  have hbad : iidProb (inferredDist dist κ (L n)) n (fun ω => ∃ r, ε / 2 ≤
      |empiricalCF ω r - expectedCF (inferredDist dist κ (L n)) r|) ≤
      K * (2 * Real.exp (-(n * (ε / 2) ^ 2 / (8 * 2 ^ 2)))) := by
    refine (iidProb_exists_le (hdL n) _).trans ?_
    calc _ ≤ ∑ _r : QuartetTree X, 2 * Real.exp (-(n * (ε / 2) ^ 2 / (8 * 2 ^ 2))) :=
          Finset.sum_le_sum fun r _ => hbound n hn₃ r
      _ = _ := by simp [hK]
  have hnot := iidProb_not (hdL n) n fun ω => ∃ r, ε / 2 ≤
      |empiricalCF ω r - expectedCF (inferredDist dist κ (L n)) r|
  have hmono : iidProb (inferredDist dist κ (L n)) n (fun ω => ¬ ∃ r, ε / 2 ≤
      |empiricalCF ω r - expectedCF (inferredDist dist κ (L n)) r|) ≤
      iidProb (inferredDist dist κ (L n)) n fun ω =>
        ∀ r : QuartetTree X, |empiricalCF ω r - expectedCF dist r| < ε := by
    refine iidProb_mono (hdL n) fun ω hω r => ?_
    have h₁ : |empiricalCF ω r - expectedCF (inferredDist dist κ (L n)) r| < ε / 2 := by
      by_contra hcon
      exact hω ⟨r, not_lt.1 hcon⟩
    have h₂ := hn₁ r
    have := abs_sub_le (empiricalCF ω r) (expectedCF (inferredDist dist κ (L n)) r) (expectedCF dist r)
    linarith
  have hKpos : 0 ≤ K := Nat.cast_nonneg _
  have hexppos : 0 < Real.exp (-(n * (ε / 2) ^ 2 / (8 * 2 ^ 2))) := Real.exp_pos _
  nlinarith

end Inferred

/-! ### The star tree on four taxa -/

namespace OnStar

/-- The tails of the arcs of the star tree on four taxa. -/
def src : Fin 4 → Fin 5 := ![4, 4, 4, 4]

/-- The heads of the arcs. -/
def tgt : Fin 4 → Fin 5 := ![0, 1, 2, 3]

/-- The taxa, as vertices. -/
def lf : Fin 4 → Fin 5 := ![0, 1, 2, 3]

/-- What each vertex reaches. -/
def desc : Fin 5 → Finset (Fin 5) := ![{0}, {1}, {2}, {3}, {0, 1, 2, 3, 4}]

/-- What the root reaches off each arc. -/
def avoid : Fin 4 → Finset (Fin 5) := ![{1, 2, 3, 4}, {0, 2, 3, 4}, {0, 1, 3, 4}, {0, 1, 2, 4}]

theorem tables : Tables src tgt 4 desc avoid :=
  ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩

/-- The star tree on four taxa. -/
abbrev net : RootedNetwork (Fin 5) (Fin 4) (Fin 4) := FinNetwork.net src tgt 4 lf

theorem net_isPhylogenetic : net.IsPhylogenetic :=
  isPhylogenetic_of_down (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide)

theorem hasTrivialFourBlob (q : Finset (Fin 4)) (hq : q.card = 4) : HasTrivialFourBlob net q :=
  (tables.hasTrivialFourBlob_iff net_isPhylogenetic hq).2 ⟨4, by
    have : ∀ q : Finset (Fin 4), q.card = 4 → HubT src tgt lf desc avoid q 4 := by decide
    exact this q hq⟩

/-- Its tree of blobs has no internal edge. -/
theorem not_mem_treeOfBlobs_of_two {A : Finset (Fin 4)} (h : A.card = 2) : A ∉ treeOfBlobs net := by
  rw [tables.mem_treeOfBlobs_iff net_isPhylogenetic]
  revert A
  decide

end OnStar

/-! ### A single optimal tree: lines 523-526 -/

section Single

open BinaryLaw.OnFour in
/-- On four taxa, a tree displays at most one quartet tree. -/
theorem card_displays_le_one {T : Finset (Finset (Fin 4))} (hT : IsUnrootedTree T) :
    (univ.filter fun s : QuartetTree (Fin 4) => Displays T s).card ≤ 1 :=
  Finset.card_le_one.2 fun s hs r hr =>
    hT.displays_unique (mem_filter.1 hs).2 (mem_filter.1 hr).2 (by rw [taxa_eq_univ, taxa_eq_univ])

theorem quartetSupport_const (c : ℝ) (T : Finset (Finset (Fin 4))) :
    quartetSupport (fun _ => c) T = (univ.filter fun s : QuartetTree (Fin 4) => Displays T s).card * c := by
  unfold quartetSupport
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]

open BinaryLaw.OnFour in
/-- (`ecto:oscillating_optimum`) **Lines 523-526.** "In general, we cannot say that any algorithm giving a single MQS optimal tree must, on growing datasets, give a
sequence of trees converging to a resolution of the tree of blobs, since such a sequence could have several accumulation points." On
the star tree on four taxa, under the displayed tree model, the empirical concordance factors are `(1/3, 1/3, 1/3)` on every sample, and two
different binary trees are optimal on every sample, both resolutions of the tree of blobs. So an algorithm can return them in turn. -/
theorem exists_oscillating_optimum {θ : MetricData (Fin 4)} :
    ∃ T₁ T₂ : Finset (Finset (Fin 4)), T₁ ≠ T₂ ∧ IsResolutionOf T₁ (treeOfBlobs OnStar.net) ∧
      IsResolutionOf T₂ (treeOfBlobs OnStar.net) ∧
      ∀ (n : ℕ), 0 < n → ∀ ω : Fin n → UnrootedGeneTree (Fin 4),
        (∀ i, displayedTreeDist OnStar.net θ (ω i) ≠ 0) →
          Section3Observations.IsMQSOptimal (empiricalCF ω) T₁ ∧
            Section3Observations.IsMQSOptimal (empiricalCF ω) T₂ := by
  have hb₁ : IsBinaryTree (gene 0).1 := (gene 0).2
  have hb₂ : IsBinaryTree (gene 1).1 := (gene 1).2
  have hu : ∀ {T : Finset (Finset (Fin 4))}, IsBinaryTree T → IsUnrootedTree T := fun ⟨H, h₁, h₂, _⟩ => ⟨H, h₁, h₂⟩
  have hres : ∀ {T : Finset (Finset (Fin 4))}, IsUnrootedTree T → IsResolutionOf T (treeOfBlobs OnStar.net) := by
    intro T hT
    refine ⟨hT, fun A hA => ?_⟩
    obtain ⟨_, hne, hne', _⟩ := mem_filter.1 hA
    have hcard : A.card = 1 ∨ Aᶜ.card = 1 := by
      have hA₂ : A.card ≠ 2 := fun h => OnStar.not_mem_treeOfBlobs_of_two h hA
      have h₁ := Finset.card_pos.2 hne
      have h₂ := Finset.card_pos.2 hne'
      have h₃ := Finset.card_add_card_compl A
      simp only [Fintype.card_fin] at h₃
      omega
    have hsp : IsSplitFamily T := (isUnrootedTree_iff (by simp) T).1 hT
    rcases hcard with h | h
    · obtain ⟨x, rfl⟩ := Finset.card_eq_one.1 h
      exact hsp.singleton_mem x
    · obtain ⟨x, hx⟩ := Finset.card_eq_one.1 h
      have := IsUnrootedTree.compl_mem hT (hsp.singleton_mem x)
      rw [← hx, compl_compl] at this
      exact this
  refine ⟨(gene 0).1, (gene 1).1, ?_, hres (hu hb₁), hres (hu hb₂), fun n hn ω hω => ?_⟩
  · intro h
    have hmem : ({0, 1} : Finset (Fin 4)) ∈ (gene 0).1 := by
      show _ ∈ unroot (hier 0)
      unfold hier unroot
      decide
    rw [h] at hmem
    revert hmem
    show _ ∈ unroot (hier 1) → False
    unfold hier unroot
    decide
  · have hN := OnStar.net_isPhylogenetic
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    have hcf : empiricalCF ω = fun _ => 1 / 3 := by
      funext r
      have hq : (r.taxa).card = 4 := r.card_taxa
      have := conventionCount_of_hasTrivialFourBlob (N := OnStar.net) (θ := θ) hN hq
        (OnStar.hasTrivialFourBlob _ hq) hω (r := r) (QuartetTests.mem_treesOn_taxa r)
      show conventionCount ω r / n = _
      rw [this]
      field_simp
    rw [hcf]
    have hopt : ∀ {T : Finset (Finset (Fin 4))}, IsBinaryTree T →
        Section3Observations.IsMQSOptimal (fun _ => 1 / 3) T := by
      intro T hT
      refine ⟨hu hT, fun T' hT' => ?_⟩
      rw [quartetSupport_const, quartetSupport_const]
      have h₁ := card_displays_le_one hT'
      obtain ⟨s, hs, hd⟩ := hT.exists_displays (q := univ) (by simp)
      have h₂ : 0 < (univ.filter fun s : QuartetTree (Fin 4) => Displays T s).card :=
        Finset.card_pos.2 ⟨s, mem_filter.2 ⟨mem_univ _, hd⟩⟩
      have h₃ : ((univ.filter fun s : QuartetTree (Fin 4) => Displays T' s).card : ℝ) ≤
          (univ.filter fun s : QuartetTree (Fin 4) => Displays T s).card := by
        exact_mod_cast h₁.trans h₂
      exact mul_le_mul_of_nonneg_right h₃ (by norm_num)
    exact ⟨hopt hb₁, hopt hb₂⟩

end Single

/-! ### What valid levels need: lines 1164-1167 -/

section Necessity

open BinaryLaw BinaryLaw.OnFour

/-- A tree on four taxa with its internal edge, and the one quartet tree it displays. -/
theorem displays_T₀_iff {s : QuartetTree (Fin 4)} : Displays T₀ s ↔ ({0, 1} : Finset (Fin 4)) ∈ s.val := by
  have hc : ({0, 1, 2, 3} : Finset (Fin 4)).card = 4 := by decide
  have hu := T₀_isUnrootedTree
  have hd₀ : Displays T₀ (quartetTree 0 1 2 3 hc) := by
    refine ⟨{0, 1}, by unfold T₀ hier unroot; decide, ?_⟩
    rw [taxa_quartetTree, quartetTree_val]
    decide
  constructor
  · intro hd
    have heq := hu.displays_unique hd hd₀ (by rw [taxa_eq_univ, taxa_eq_univ])
    rw [heq]
    simp
  · intro h
    have heq : s = quartetTree 0 1 2 3 hc :=
      QuartetTree.eq_of_taxa_eq_of_mem (by rw [taxa_eq_univ, taxa_eq_univ]) h (by simp)
    rw [heq]
    exact hd₀

/-- The overall T1 p-value with Bonferroni of the tree `T₀` on four taxa is that of its quartet tree. -/
theorem treeT1P_T₀ {o : ECToBlobOptions} (hm : o.testCo = .bon) (c : QuartetTree (Fin 4) → ℝ) :
    treeT1P o c T₀ = t1PValue c (quartetTree 0 1 2 3 (by decide)) := by
  have hc : ({0, 1, 2, 3} : Finset (Fin 4)).card = 4 := by decide
  have hset : (univ.filter fun s => Displays T₀ s) = {quartetTree 0 1 2 3 hc} := by
    ext s
    simp only [mem_filter, mem_univ, true_and, mem_singleton, displays_T₀_iff]
    constructor
    · intro h
      exact QuartetTree.eq_of_taxa_eq_of_mem (by rw [taxa_eq_univ, taxa_eq_univ]) h (by simp)
    · rintro rfl
      simp
  unfold treeT1P
  rw [hset, hm]
  have hval : (({quartetTree 0 1 2 3 hc} : Finset (QuartetTree (Fin 4))).val.map fun s => t1PValue c s) =
      {t1PValue c (quartetTree 0 1 2 3 hc)} := by
    simp
  rw [hval]
  have hne : ({t1PValue c (quartetTree 0 1 2 3 hc)} : Multiset ℝ) ≠ 0 := Multiset.singleton_ne_zero _
  unfold combineP
  rw [ite_eq_right hne]
  show bonP _ = _
  unfold bonP minP
  simp only [Multiset.card_singleton, Nat.cast_one, one_mul, Multiset.fold_singleton]
  have hle : t1PValue c (quartetTree 0 1 2 3 hc) ≤ 1 := Trinomial.t1Tail_le_one _ _
  rw [min_eq_left hle, min_eq_right hle]

/-- (`ecto:valid_alpha`) **Lines 1164-1165: "any valid choice needs `α_n → 0`, in order to fail to reject a true null consistently".** If the output with
Bonferroni and the early rule is the tree of blobs, with probability tending to one, on the law `(1/2 + 1/6, 1/6, 1/6)` on the tree on four
taxa, for levels `α_n ≥ 0`, `α_n ≤ 1`, then `α_n → 0`. The T1 p-value of a true cut split is asymptotically uniform, so it is below any level
that does not vanish, with a probability that does not vanish. -/
theorem tendsto_alpha_of_consistent {α β : ℕ → ℝ} (hα₀ : ∀ᶠ n in atTop, 0 ≤ α n)
    (hα₁ : ∀ᶠ n in atTop, α n ≤ 1) {o : ECToBlobOptions} (hm : o.testCo = .bon) (hr : o.rule = .early)
    (h : Tendsto (fun n => iidProb (law (1 / 6)) n fun ω =>
      ectoblob o (α n) (β n) (quartetCount Subtype.val ω) T₀ = treeOfBlobs net) atTop (𝓝 1)) :
    Tendsto α atTop (𝓝 0) := by
  have hd : IsDist (law (1 / 6)) := law_isDist (by norm_num) (by norm_num)
  have hone := displaysOne_binaryGeneTree (law (1 / 6))
  obtain ⟨h₁, _⟩ := law_assumption1 (q := 1 / 6) (by norm_num)
  have hc : ({0, 1, 2, 3} : Finset (Fin 4)).card = 4 := by decide
  have hcut : InducedCutSplit net (quartetTree 0 1 2 3 hc) :=
    inducedCutSplit_of_rdom net_isPhylogenetic hc (tables.rdom_iff.2 (by decide))
  have hstrict := h₁.t1 _ hcut
  have hpos : ∀ r ∈ (quartetTree 0 1 2 3 hc).alternatives, 0 < displayCF (law (1 / 6)) Subtype.val r := by
    intro r hr'
    obtain ⟨hrt, hrs⟩ := QuartetTree.mem_alternatives.1 hr'
    rw [displayCF_law, pq, ite_eq_right fun h' =>
      hrs (QuartetTree.eq_of_taxa_eq_of_mem hrt h' (by simp))]
    norm_num
  have hU := t1PValue_asymptoticallyUniform hd hone hstrict.1 hstrict.2 hpos
  have hA : ({0, 1} : Finset (Fin 4)) ∈ T₀ := by unfold T₀ hier unroot; decide
  have hAint : ({0, 1} : Finset (Fin 4)) ∈ internalSides T₀ := mem_internalSides.2 ⟨hA, by decide⟩
  refine tendsto_order.2 ⟨fun a ha => ?_, fun a ha => ?_⟩
  · filter_upwards [hα₀] with n hn
    exact ha.trans_le hn
  · -- a level above `a` would reject with probability about `a`
    set a' := min a 1 with ha'
    have ha'pos : 0 < a' := lt_min ha one_pos
    have ha'le : a' ≤ 1 := min_le_right _ _
    have hlim := hU (a' / 2) (by positivity) (by linarith)
    have ev₁ := hlim.eventually_const_lt (show a' / 4 < a' / 2 by linarith)
    have ev₂ := h.eventually_const_lt (show 1 - a' / 8 < 1 by linarith)
    filter_upwards [ev₁, ev₂, hα₁] with n hn₁ hn₂ hn₃
    by_contra hcon
    have hge : a ≤ α n := not_lt.1 hcon
    have hle : (iidProb (law (1 / 6)) n fun ω =>
        ectoblob o (α n) (β n) (quartetCount Subtype.val ω) T₀ = treeOfBlobs net) ≤
        iidProb (law (1 / 6)) n fun ω => ¬ t1PValue (quartetCount Subtype.val ω) (quartetTree 0 1 2 3 hc) ≤ a' / 2 := by
      refine iidProb_mono hd fun ω hω hp => ?_
      have hT : ectoblob o (α n) (β n) (quartetCount Subtype.val ω) T₀ = T₀ := hω.trans treeOfBlobs_eq
      have hat0 := le_treeT1P_of_ectoblob_eq hr hn₃ hA (by decide) hT
      rw [treeT1P_T₀ hm] at hat0
      have hge' : a' ≤ α n := (min_le_left _ _).trans hge
      linarith
    rw [iidProb_not hd] at hle
    linarith

/-- Bonferroni of one p-value in `[0, 1]` is itself. -/
theorem combineP_bon_singleton {x : ℝ} (h1 : x ≤ 1) : combineP .bon {x} = x := by
  have hne : ({x} : Multiset ℝ) ≠ 0 := Multiset.singleton_ne_zero _
  unfold combineP
  rw [ite_eq_right hne]
  show bonP _ = _
  unfold bonP minP
  simp only [Multiset.card_singleton, Nat.cast_one, one_mul, Multiset.fold_singleton]
  rw [min_eq_left h1, min_eq_right h1]

/-- The only quartet around the edge of the tree on four taxa is `01|23`. -/
theorem multipartition_T₀_eq :
    multipartitionQuartets T₀ ({0, 1} : Finset (Fin 4)) = {quartetTree 0 1 2 3 (by decide)} := by
  have hc : ({0, 1, 2, 3} : Finset (Fin 4)).card = 4 := by decide
  obtain ⟨s₀, hs₀⟩ := FalseEdge.exists_mem_multipartitionQuartets (A := {0, 1})
    (isSplitFamily_of_internal T₀_isUnrootedTree (by decide : 2 ≤ ({0, 1} : Finset (Fin 4)).card))
    (by decide) (by decide)
  have hall : ∀ s ∈ multipartitionQuartets T₀ ({0, 1} : Finset (Fin 4)), s = quartetTree 0 1 2 3 hc := by
    intro s hs
    have h₁ : ({0, 1} : Finset (Fin 4)) ∩ s.taxa ∈ s.val := (mem_filter.1 (mem_filter.1 hs).1).2
    rw [taxa_eq_univ, Finset.inter_univ] at h₁
    exact QuartetTree.eq_of_taxa_eq_of_mem (by rw [taxa_eq_univ, taxa_eq_univ]) h₁ (by simp)
  refine Finset.eq_singleton_iff_unique_mem.2 ⟨?_, hall⟩
  rw [← hall s₀ hs₀]
  exact hs₀

/-- (`ecto:valid_beta`) **Lines 1164-1165: "any valid choice needs `β_n → 0`".** If the output with Bonferroni, the early rule and the star test by likelihood
ratio is the tree of blobs, with probability tending to one, on the star tree on four taxa under the uniform law on the three binary trees,
at levels `α_n → 0`, `0 ≤ β_n ≤ 1`, then `β_n → 0`. The star p-value is asymptotically uniform, so it is below any level that does not
vanish, with a probability that does not vanish, and then Step 3 keeps the false edge, which the T1 test does not reject. -/
theorem tendsto_beta_of_consistent {α β : ℕ → ℝ} (hα : Tendsto α atTop (𝓝 0))
    (hβ₀ : ∀ᶠ n in atTop, 0 ≤ β n) {o : ECToBlobOptions} (hm : o.testCo = .bon) (hr : o.rule = .early)
    (hs : o.starTest = .lrt)
    (h : Tendsto (fun n => iidProb (law (1 / 3)) n fun ω =>
      ectoblob o (α n) (β n) (quartetCount Subtype.val ω) T₀ = treeOfBlobs OnStar.net) atTop (𝓝 1)) :
    Tendsto β atTop (𝓝 0) := by
  have hd : IsDist (law (1 / 3)) := by
    refine pointLaw_isDist (fun i => ?_) ?_
    · fin_cases i <;> norm_num
    · rw [Fin.sum_univ_three]
      norm_num
  have hone := displaysOne_binaryGeneTree (law (1 / 3))
  have hc : ({0, 1, 2, 3} : Finset (Fin 4)).card = 4 := by decide
  set s₀ := quartetTree (0 : Fin 4) 1 2 3 hc with hs₀
  have huni : ∀ r ∈ treesOn s₀.taxa, displayCF (law (1 / 3)) Subtype.val r = 1 / 3 := by
    intro r _
    rw [displayCF_law, pq]
    split_ifs <;> norm_num
  have hU := starPValue_asymptoticallyUniform .lrt hd hone s₀.card_taxa huni
  have hA : ({0, 1} : Finset (Fin 4)) ∈ T₀ := by unfold T₀ hier unroot; decide
  have hAc : ({2, 3} : Finset (Fin 4)) = ({0, 1} : Finset (Fin 4))ᶜ := by decide
  refine tendsto_order.2 ⟨fun a ha => ?_, fun a ha => ?_⟩
  · filter_upwards [hβ₀] with n hn
    exact ha.trans_le hn
  · set a' := min a 1 with ha'
    have ha'pos : 0 < a' := lt_min ha one_pos
    have ha'le : a' ≤ 1 := min_le_right _ _
    obtain ⟨δ, hδ₀, _, hδ⟩ := t1PValue_centroid_tight hd hone (s := s₀) huni (ε := a' / 8) (by positivity)
    have ev₀ := (hU (a' / 2) (by positivity) (by linarith)).eventually_const_lt
      (show a' / 4 < a' / 2 by linarith)
    have ev₁ := h.eventually_const_lt (show 1 - a' / 8 < 1 by linarith)
    filter_upwards [ev₀, ev₁, hδ, hα.eventually (gt_mem_nhds hδ₀)] with n hn₀ hn₁ hn₂ hn₃
    by_contra hcon
    have hge : a ≤ β n := not_lt.1 hcon
    have hge' : a' ≤ β n := (min_le_left _ _).trans hge
    have hne : T₀ ≠ treeOfBlobs OnStar.net := fun he =>
      OnStar.not_mem_treeOfBlobs_of_two (A := {0, 1}) (by decide) (he ▸ hA)
    -- on the event, the output is `T₀`
    have himp : (iidProb (law (1 / 3)) n fun ω =>
        starPValue .lrt (quartetCount Subtype.val ω) s₀.taxa ≤ a' / 2 ∧
          (δ ≤ t1PValue (quartetCount Subtype.val ω) s₀ ∧ t1PValue (quartetCount Subtype.val ω) s₀ ≤ 1 - δ)) ≤
        iidProb (law (1 / 3)) n fun ω =>
          ¬ ectoblob o (α n) (β n) (quartetCount Subtype.val ω) T₀ = treeOfBlobs OnStar.net := by
      refine iidProb_mono hd fun ω hω hout => ?_
      obtain ⟨h₁, h₂, _⟩ := hω
      set c := quartetCount (Subtype.val : BinaryGeneTree (Fin 4) → _) ω with hcdef
      -- Step 3 keeps `T₀`
      have hval : ∀ {B : Finset (Fin 4)}, multipartitionQuartets T₀ B = multipartitionQuartets T₀ {0, 1} →
          edgeStarP o c T₀ B ≤ β n := by
        intro B hB
        unfold edgeStarP
        rw [hB, multipartition_T₀_eq, hm, hs]
        simp only [Finset.singleton_val, Multiset.map_singleton]
        have hp₁ : starPValue .lrt c (quartetTree (0 : Fin 4) 1 2 3 hc).taxa ≤ 1 :=
          (starPValue_mem' .lrt (fun r => quartetCount_nonneg ω r) s₀.card_taxa).2
        rw [combineP_bon_singleton hp₁]
        linarith
      have hint : ∀ B ∈ T₀, 2 ≤ B.card ∧ 2 ≤ Bᶜ.card → B = {0, 1} ∨ B = {2, 3} := by
        unfold T₀ hier unroot
        decide
      have hafter : afterStar o (β n) c T₀ = T₀ := by
        have hno : ∀ B ∈ internalSides T₀, ¬ β n < edgeStarP o c T₀ B := by
          intro B hB
          obtain ⟨hB₁, hB₂⟩ := mem_internalSides.1 hB
          refine not_lt.2 (hval ?_)
          rcases hint B hB₁ hB₂ with rfl | rfl
          · rfl
          · rw [hAc]
            exact multipartitionQuartets_compl _ _
        refine Finset.filter_true_of_mem fun B _ => ⟨fun hB => ?_, fun hB => ?_⟩
        · exact hno B (mem_filter.1 hB).1 (mem_filter.1 hB).2
        · exact hno _ (mem_filter.1 hB).1 (mem_filter.1 hB).2
      -- the first tree is not rejected
      have hαn : α n ≤ treeT1P o c T₀ := by
        rw [treeT1P_T₀ hm]
        linarith
      have hzero : treeSeq o (β n) c T₀ 0 = T₀ := hafter
      have hidx : selectedIteration o (α n) (β n) c T₀ = 0 := by
        rw [selectedIteration_early (α n) (β n) c T₀ hr]
        exact Nat.sInf_eq_zero.2 (Or.inl ⟨Nat.zero_le _, by rw [hzero]; exact hαn⟩)
      have : ectoblob o (α n) (β n) c T₀ = T₀ := by
        unfold ectoblob
        rw [hidx, hzero]
      exact hne (this.symm.trans hout)
    rw [iidProb_not hd] at himp
    have hand := iidProb_and_ge' hd n
      (fun ω => starPValue .lrt (quartetCount Subtype.val ω) s₀.taxa ≤ a' / 2)
      (fun ω => δ ≤ t1PValue (quartetCount Subtype.val ω) s₀ ∧
        t1PValue (quartetCount Subtype.val ω) s₀ ≤ 1 - δ)
    linarith

end Necessity

/-! ### The overall p-values need not increase: lines 892-893 -/

section Decreasing

open FinNetwork.Binary BinaryLaw.OnBinary

/-- A table of p-values: `3/250` on the quartets of the edge `de`, and `1/100` on the others. -/
def table (s : QuartetTree (Fin 5)) : ℝ := if ({3, 4} : Finset (Fin 5)) ∈ s.val then 3 / 250 else 1 / 100

/-- The options of the example: Bonferroni, on the bipartition sets. -/
def optsB : ECToBlobOptions := ⟨.bi, .bon, .early, .lrt⟩

theorem table_mem (s : QuartetTree (Fin 5)) : 0 < table s ∧ table s ≤ 1 := by
  unfold table
  split_ifs <;> norm_num

/-- Two sides of a quartet tree: one is given, the other is disjoint from it. -/
theorem exists_other_side {P : Finset (Fin 5)} {s : QuartetTree (Fin 5)} (hP : P ∈ s.val) :
    ∃ D : Finset (Fin 5), D.card = 2 ∧ Disjoint P D ∧ s.val = {P, D} := by
  obtain ⟨B, C, hsv, hB, hC, hd, _⟩ := s.exists_eq_pair
  rw [hsv] at hP
  simp only [mem_insert, mem_singleton] at hP
  rcases hP with rfl | rfl
  · exact ⟨C, hC, hd, hsv⟩
  · exact ⟨B, hB, hd.symm, by rw [hsv, Finset.pair_comm]⟩

/-- The bipartition of the edge `P` has the cherry `P`. -/
theorem mem_val_of_bipartition {P : Finset (Fin 5)} (hc : P.card = 2) {s : QuartetTree (Fin 5)}
    (hs : s ∈ bipartitionQuartets P) : P ∈ s.val := by
  have h₁ := (mem_filter.1 hs).2
  have h₂ : (P ∩ s.taxa).card = 2 := s.card_of_mem h₁
  have h₃ : P ∩ s.taxa = P := Finset.eq_of_subset_of_card_le Finset.inter_subset_left (by rw [h₂, hc])
  rwa [h₃] at h₁

/-- At most three quartet trees around a pair: the two others of the `D`s disjoint from it, up to three. -/
theorem card_bipartition_le {P : Finset (Fin 5)} (hc : P.card = 2) : (bipartitionQuartets P).card ≤ 3 := by
  -- the map to the other cherry is injective, into the pairs of the complement
  have hinj : ∀ s ∈ bipartitionQuartets P, ∀ t ∈ bipartitionQuartets P,
      (s.val.erase P) = (t.val.erase P) → s = t := by
    intro s hs t ht he
    obtain ⟨D, hD, hdj, hsv⟩ := exists_other_side (mem_val_of_bipartition hc hs)
    obtain ⟨D', hD', hdj', htv⟩ := exists_other_side (mem_val_of_bipartition hc ht)
    have hPD : P ≠ D := fun h => by
      rw [← h] at hdj
      have : P = ∅ := disjoint_self.1 hdj
      rw [this] at hc
      simp at hc
    have hPD' : P ≠ D' := fun h => by
      rw [← h] at hdj'
      have : P = ∅ := disjoint_self.1 hdj'
      rw [this] at hc
      simp at hc
    rw [hsv, htv, Finset.erase_insert_eq_erase, Finset.erase_insert_eq_erase,
      Finset.erase_eq_of_notMem (by simpa using hPD), Finset.erase_eq_of_notMem (by simpa using hPD')] at he
    refine Subtype.ext ?_
    rw [hsv, htv, Finset.singleton_injective he]
  have hmap : (bipartitionQuartets P).card ≤ ((powersetCard 2 Pᶜ).image fun D => ({D} : Finset (Finset (Fin 5)))).card := by
    refine Finset.card_le_card_of_injOn (fun s => s.val.erase P) (fun s hs => ?_) fun s hs t ht he => hinj s hs t ht he
    obtain ⟨D, hD, hdj, hsv⟩ := exists_other_side (mem_val_of_bipartition hc hs)
    have hPD : P ≠ D := fun h => by
      rw [← h] at hdj
      have : P = ∅ := disjoint_self.1 hdj
      rw [this] at hc
      simp at hc
    refine mem_image.2 ⟨D, mem_powersetCard.2 ⟨?_, hD⟩, ?_⟩
    · intro x hx
      exact mem_compl.2 fun hP => (disjoint_left.1 hdj) hP hx
    · simp only
      rw [hsv, Finset.erase_insert_eq_erase, Finset.erase_eq_of_notMem (by simpa using hPD)]
  refine hmap.trans (Finset.card_image_le.trans ?_)
  rw [Finset.card_powersetCard, Finset.card_compl, hc]
  simp

/-- Bonferroni of a nonempty multiset, as a formula. -/
theorem combineP_bon_eq {P : Multiset ℝ} (hP : P ≠ 0) :
    combineP .bon P = min 1 ((Multiset.card P : ℝ) * minP P) := by
  unfold combineP
  rw [ite_eq_right hP]
  rfl

/-- (`ecto:tree_p_not_monotone`) **Lines 892-893: "the combined p-value assessing all edges remaining in `T_ki` need not monotonically increase with `i`".** With
Bonferroni on the bipartition sets, on the table of p-values `table`, the step of the algorithm from `T₀` contracts the edge `bc`, since
its combined p-value is the least, and the overall p-value goes down: from at least `4/100`, with four quartets at the least value `1/100`
left, to at most `9/250`. This is a table of p-values given as input, in the form "at its core ECToBlob takes quartet p-values as input"
(line 1421); that counts realize it is not shown. The paper's own evidence for the claim is empirical (lines 907-910). -/
theorem exists_treeTestP_decreasing :
    treeTestP optsB table (seqBy (edgeTestP optsB table T₀) T₀ 1) < treeTestP optsB table T₀ := by
  set e := edgeTestP optsB table T₀ with he
  have hc₁ : ({3, 4, 0, 1} : Finset (Fin 5)).card = 4 := by decide
  have hc₂ : ({3, 4, 0, 2} : Finset (Fin 5)).card = 4 := by decide
  have hc₃ : ({3, 4, 1, 2} : Finset (Fin 5)).card = 4 := by decide
  have hc₄ : ({1, 2, 0, 3} : Finset (Fin 5)).card = 4 := by decide
  have hc₅ : ({1, 2, 0, 4} : Finset (Fin 5)).card = 4 := by decide
  set S₁ := quartetTree 3 4 0 1 hc₁ with hS₁
  set S₂ := quartetTree 3 4 0 2 hc₂ with hS₂
  set S₃ := quartetTree 3 4 1 2 hc₃ with hS₃
  set R₁ := quartetTree 1 2 0 3 hc₄ with hR₁
  set R₂ := quartetTree 1 2 0 4 hc₅ with hR₂
  have hdeS : ∀ {y z : Fin 5} (h : ({3, 4, y, z} : Finset (Fin 5)).card = 4),
      quartetTree 3 4 y z h ∈ bipartitionQuartets ({3, 4} : Finset (Fin 5)) := by
    intro y z h
    refine mem_filter.2 ⟨mem_univ _, ?_⟩
    have hsub : ({3, 4} : Finset (Fin 5)) ⊆ (quartetTree 3 4 y z h).taxa :=
      (quartetTree 3 4 y z h).subset_taxa (by simp)
    rw [Finset.inter_eq_left.2 hsub]
    simp
  have hR₁b : R₁ ∈ bipartitionQuartets ({1, 2} : Finset (Fin 5)) := by
    refine mem_filter.2 ⟨mem_univ _, ?_⟩
    rw [Finset.inter_eq_left.2 (R₁.subset_taxa (by simp [hR₁]))]
    simp [hR₁]
  have hR₂b : R₂ ∈ bipartitionQuartets ({1, 2} : Finset (Fin 5)) := by
    refine mem_filter.2 ⟨mem_univ _, ?_⟩
    rw [Finset.inter_eq_left.2 (R₂.subset_taxa (by simp [hR₂]))]
    simp [hR₂]
  have hne₁₂ : S₁ ≠ S₂ := fun h => by
    have := congrArg Subtype.val h
    simp only [hS₁, hS₂, quartetTree_val] at this
    exact absurd this (by decide)
  have hne₁₃ : S₁ ≠ S₃ := fun h => by
    have := congrArg Subtype.val h
    simp only [hS₁, hS₃, quartetTree_val] at this
    exact absurd this (by decide)
  have hne₂₃ : S₂ ≠ S₃ := fun h => by
    have := congrArg Subtype.val h
    simp only [hS₂, hS₃, quartetTree_val] at this
    exact absurd this (by decide)
  have hvalx : ∀ s, ({3, 4} : Finset (Fin 5)) ∈ s.val → table s = 3 / 250 := fun s h => by
    unfold table
    rw [ite_eq_left h]
  have hR₁v : table R₁ = 1 / 100 := by
    unfold table
    rw [ite_eq_right]
    simp only [hR₁, quartetTree_val]
    decide
  have hR₂v : table R₂ = 1 / 100 := by
    unfold table
    rw [ite_eq_right]
    simp only [hR₂, quartetTree_val]
    decide
  have hmap01 : ∀ (Q : Finset (QuartetTree (Fin 5))), ∀ x ∈ Q.val.map table, 0 < x ∧ x ≤ 1 := by
    intro Q x hx
    obtain ⟨s, _, rfl⟩ := Multiset.mem_map.1 hx
    exact table_mem s
  have hne_of_mem : ∀ {Q : Finset (QuartetTree (Fin 5))} {s}, s ∈ Q → Q.val.map table ≠ 0 := by
    intro Q s hs h
    have : table s ∈ Q.val.map table := Multiset.mem_map_of_mem _ hs
    simp [h] at this
  -- the edge p-values
  have hbide : (bipartitionQuartets ({3, 4} : Finset (Fin 5))).card = 3 := by
    refine le_antisymm (card_bipartition_le (by decide)) ?_
    have hsub : ({S₁, S₂, S₃} : Finset (QuartetTree (Fin 5))) ⊆ bipartitionQuartets {3, 4} := by
      intro r hr
      simp only [mem_insert, mem_singleton] at hr
      rcases hr with rfl | rfl | rfl <;> exact hdeS _
    calc 3 = ({S₁, S₂, S₃} : Finset (QuartetTree (Fin 5))).card :=
          (Finset.card_eq_three.2 ⟨S₁, S₂, S₃, hne₁₂, hne₁₃, hne₂₃, rfl⟩).symm
      _ ≤ _ := Finset.card_le_card hsub
  have hallde : ∀ x ∈ (bipartitionQuartets ({3, 4} : Finset (Fin 5))).val.map table, x = 3 / 250 := by
    intro x hx
    obtain ⟨s, hs, rfl⟩ := Multiset.mem_map.1 hx
    exact hvalx s (mem_val_of_bipartition (by decide) hs)
  have hede : e T₀ {3, 4} = 9 / 250 := by
    have hne := hne_of_mem (hdeS hc₁)
    show combineP .bon ((bipartitionQuartets ({3, 4} : Finset (Fin 5))).val.map table) = _
    rw [combineP_bon_eq hne, hallde _ (minP_mem hne fun x hx => (hmap01 _ x hx).2), Multiset.card_map]
    have : ((bipartitionQuartets ({3, 4} : Finset (Fin 5))).val.card : ℝ) = 3 := by exact_mod_cast hbide
    rw [this]
    norm_num
  have hebc : e T₀ {1, 2} ≤ 3 / 100 := by
    have hne := hne_of_mem hR₁b
    show combineP .bon ((bipartitionQuartets ({1, 2} : Finset (Fin 5))).val.map table) ≤ _
    rw [combineP_bon_eq hne, Multiset.card_map]
    refine (min_le_right _ _).trans ?_
    have hcard : ((bipartitionQuartets ({1, 2} : Finset (Fin 5))).val.card : ℝ) ≤ 3 := by
      exact_mod_cast card_bipartition_le (P := {1, 2}) (by decide)
    have hmin : minP ((bipartitionQuartets ({1, 2} : Finset (Fin 5))).val.map table) ≤ 1 / 100 :=
      hR₁v ▸ minP_le_of_mem (Multiset.mem_map_of_mem _ hR₁b)
    have hmin₀ : 0 ≤ minP ((bipartitionQuartets ({1, 2} : Finset (Fin 5))).val.map table) :=
      minP_nonneg fun x hx => (hmap01 _ x hx).1.le
    nlinarith
  have hcompl : ∀ A : Finset (Fin 5), e T₀ Aᶜ = e T₀ A := by
    intro A
    show combineP .bon ((bipartitionQuartets Aᶜ).val.map table) =
      combineP .bon ((bipartitionQuartets A).val.map table)
    rw [bipartitionQuartets_compl]
  have hc012 : ({0, 1, 2} : Finset (Fin 5)) = ({3, 4} : Finset (Fin 5))ᶜ := by decide
  have hc034 : ({0, 3, 4} : Finset (Fin 5)) = ({1, 2} : Finset (Fin 5))ᶜ := by decide
  have hint : ∀ B ∈ T₀, 2 ≤ B.card ∧ 2 ≤ Bᶜ.card →
      B = {3, 4} ∨ B = {0, 1, 2} ∨ B = {1, 2} ∨ B = {0, 3, 4} := by
    unfold T₀ H₀ unroot
    decide
  have h34 : ({3, 4} : Finset (Fin 5)) ∈ T₀ := T₀_internal_de
  have h12 : ({1, 2} : Finset (Fin 5)) ∈ T₀ := T₀_ne_treeOfBlobs.1
  have hi12 : ({1, 2} : Finset (Fin 5)) ∈ internalSides T₀ := mem_internalSides.2 ⟨h12, by decide⟩
  set C := (internalSides T₀).filter fun A => ∀ B ∈ internalSides T₀, e T₀ A ≤ e T₀ B with hC
  have h12C : ({1, 2} : Finset (Fin 5)) ∈ C := by
    refine mem_filter.2 ⟨hi12, fun B hB => ?_⟩
    obtain ⟨hB₁, hB₂⟩ := mem_internalSides.1 hB
    rcases hint B hB₁ hB₂ with rfl | rfl | rfl | rfl
    · rw [hede]
      linarith
    · rw [hc012, hcompl, hede]
      linarith
    · exact le_rfl
    · rw [hc034, hcompl]
  have hnot34 : ∀ A, A = ({3, 4} : Finset (Fin 5)) ∨ A = ({0, 1, 2} : Finset (Fin 5)) → A ∉ C := by
    intro A hA hmem
    have h₁ := (mem_filter.1 hmem).2 _ hi12
    have h₂ : e T₀ A = 9 / 250 := by
      rcases hA with rfl | rfl
      · exact hede
      · rw [hc012, hcompl, hede]
    rw [h₂] at h₁
    linarith
  have hT' : seqBy e T₀ 1 = contractSides T₀ C := rfl
  have hmem34 : ({3, 4} : Finset (Fin 5)) ∈ seqBy e T₀ 1 := by
    rw [hT']
    refine mem_contractSides.2 ⟨h34, hnot34 _ (Or.inl rfl), hnot34 _ (Or.inr ?_)⟩
    decide
  -- the tree after the step displays only quartets of the edge `de`
  have hdisp : ∀ s, Displays (seqBy e T₀ 1) s → s ∈ bipartitionQuartets ({3, 4} : Finset (Fin 5)) := by
    rintro s ⟨B, hB, hBs⟩
    rw [hT'] at hB
    obtain ⟨hB₁, hB₂, hB₃⟩ := mem_contractSides.1 hB
    have htwo := two_le_card_of_inter_taxa_mem hBs
    rcases hint B hB₁ htwo with rfl | rfl | rfl | rfl
    · exact mem_filter.2 ⟨mem_univ _, hBs⟩
    · have hcc : ({0, 1, 2} : Finset (Fin 5))ᶜ = {3, 4} := by decide
      have := compl_inter_taxa_mem hBs
      rw [hcc] at this
      exact mem_filter.2 ⟨mem_univ _, this⟩
    · exact absurd h12C hB₂
    · refine absurd h12C ?_
      rw [show ({1, 2} : Finset (Fin 5)) = ({0, 3, 4} : Finset (Fin 5))ᶜ by decide]
      exact hB₃
  have hup : treeTestP optsB table (seqBy e T₀ 1) ≤ 9 / 250 := by
    have hS₁d : S₁ ∈ univ.filter fun s => Displays (seqBy e T₀ 1) s :=
      mem_filter.2 ⟨mem_univ _, {3, 4}, hmem34, (mem_filter.1 (hdeS hc₁)).2⟩
    have hne := hne_of_mem hS₁d
    show combineP .bon ((univ.filter fun s => Displays (seqBy e T₀ 1) s).val.map table) ≤ _
    rw [combineP_bon_eq hne, Multiset.card_map]
    refine (min_le_right _ _).trans ?_
    have hval : minP ((univ.filter fun s => Displays (seqBy e T₀ 1) s).val.map table) = 3 / 250 := by
      obtain ⟨s, hs, hs'⟩ := Multiset.mem_map.1 (minP_mem hne fun x hx => (hmap01 _ x hx).2)
      rw [← hs']
      exact hvalx s (mem_val_of_bipartition (by decide) (hdisp s (mem_filter.1 hs).2))
    have hcard : ((univ.filter fun s => Displays (seqBy e T₀ 1) s).val.card : ℝ) ≤ 3 := by
      have hsub : (univ.filter fun s => Displays (seqBy e T₀ 1) s) ⊆ bipartitionQuartets {3, 4} :=
        fun s hs => hdisp s (mem_filter.1 hs).2
      have := (Finset.card_le_card hsub).trans_eq hbide
      exact_mod_cast this
    rw [hval]
    linarith
  have hlow : 1 / 25 ≤ treeTestP optsB table T₀ := by
    have hd₁ : ∀ s ∈ bipartitionQuartets ({3, 4} : Finset (Fin 5)), s ∈ univ.filter fun s => Displays T₀ s :=
      fun s hs => mem_filter.2 ⟨mem_univ _, {3, 4}, h34, (mem_filter.1 hs).2⟩
    have hd₂ : ∀ s ∈ bipartitionQuartets ({1, 2} : Finset (Fin 5)), s ∈ univ.filter fun s => Displays T₀ s :=
      fun s hs => mem_filter.2 ⟨mem_univ _, {1, 2}, h12, (mem_filter.1 hs).2⟩
    have hne := hne_of_mem (hd₁ _ (hdeS hc₁))
    show _ ≤ combineP .bon ((univ.filter fun s => Displays T₀ s).val.map table)
    rw [combineP_bon_eq hne, Multiset.card_map]
    have hne₁ : S₁ ≠ R₁ := fun h => by
      have := congrArg Subtype.val h
      simp only [hS₁, hR₁, quartetTree_val] at this
      exact absurd this (by decide)
    have hne₂ : S₁ ≠ R₂ := fun h => by
      have := congrArg Subtype.val h
      simp only [hS₁, hR₂, quartetTree_val] at this
      exact absurd this (by decide)
    have hne₃ : S₂ ≠ R₁ := fun h => by
      have := congrArg Subtype.val h
      simp only [hS₂, hR₁, quartetTree_val] at this
      exact absurd this (by decide)
    have hne₄ : S₂ ≠ R₂ := fun h => by
      have := congrArg Subtype.val h
      simp only [hS₂, hR₂, quartetTree_val] at this
      exact absurd this (by decide)
    have hne₅ : R₁ ≠ R₂ := fun h => by
      have := congrArg Subtype.val h
      simp only [hR₁, hR₂, quartetTree_val] at this
      exact absurd this (by decide)
    have hfour : 4 ≤ (univ.filter fun s => Displays T₀ s).card := by
      have hsub : ({S₁, S₂, R₁, R₂} : Finset (QuartetTree (Fin 5))) ⊆ univ.filter fun s => Displays T₀ s := by
        intro r hr
        simp only [mem_insert, mem_singleton] at hr
        rcases hr with rfl | rfl | rfl | rfl
        · exact hd₁ _ (hdeS hc₁)
        · exact hd₁ _ (hdeS hc₂)
        · exact hd₂ _ hR₁b
        · exact hd₂ _ hR₂b
      have hcard : ({S₁, S₂, R₁, R₂} : Finset (QuartetTree (Fin 5))).card = 4 := by
        rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_pair hne₅]
        · simp [hne₃, hne₄]
        · simp [hne₁₂, hne₁, hne₂]
      exact hcard ▸ Finset.card_le_card hsub
    have hcardR : (4 : ℝ) ≤ ((univ.filter fun s => Displays T₀ s).val.card : ℝ) := by exact_mod_cast hfour
    have hmin : 1 / 100 ≤ minP ((univ.filter fun s => Displays T₀ s).val.map table) := by
      obtain ⟨s, _, hs'⟩ := Multiset.mem_map.1 (minP_mem hne fun x hx => (hmap01 _ x hx).2)
      rw [← hs']
      unfold table
      split_ifs <;> norm_num
    refine le_min (by norm_num) ?_
    nlinarith
  have hfin : (9 : ℝ) / 250 < 1 / 25 := by norm_num
  linarith

end Decreasing

/-! ### Lines 760-761: the two statistics of the star test -/

/-- **Lines 760-761** (`ecto:star_equivalent`): "the standard chi-square test based on the Pearson test statistic and 2 degrees of
freedom, asymptotically equivalent to the LRT". Under the null, the difference of the two statistics tends to `0` in probability. That
they have the same limit `χ²₂` is `Phylogenetics.Trinomial.tendsto_star_lrt` and `Phylogenetics.Trinomial.tendsto_star_pearson`. -/
theorem tendsto_starS_sub_pearsonS {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n ↦ iidProb (Trinomial.cutPoint 1) n fun η ↦
      ε ≤ |Trinomial.starS (Trinomial.count η 0) (Trinomial.count η 1) (Trinomial.count η 2) -
        Trinomial.pearsonS (Trinomial.count η 0) (Trinomial.count η 1) (Trinomial.count η 2)|) atTop (𝓝 0) := by
  have hd : IsDist (Trinomial.cutPoint 1) := Trinomial.cutPoint_isDist (by norm_num)
  rw [Metric.tendsto_atTop]
  intro δ hδ
  -- the level of the Pearson test
  set x : ℝ := min (δ / 2) (1 / 2) with hxdef
  have hx0 : 0 < x := lt_min (by linarith) (by norm_num)
  have hx1 : x < 1 := (min_le_right _ _).trans_lt (by norm_num)
  set t : ℝ := -2 * Real.log x with htdef
  have ht0 : 0 < t := by
    have : Real.log x < 0 := Real.log_neg hx0 hx1
    rw [htdef]
    linarith
  set R : ℝ := √t + 1 with hRdef
  have hR : 0 < R := by positivity
  have hlim := Trinomial.tendsto_star_pearson hx0.le hx1.le
  have hev := hlim.eventually (gt_mem_nhds (show x < δ by
    exact (min_le_left _ _).trans_lt (by linarith)))
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hev.and ((Trinomial.eventually_starS_centroid hR hε).and (eventually_gt_atTop 0)))
  refine ⟨N, fun n hn => ?_⟩
  obtain ⟨hn₁, hn₂, hn₃⟩ := hN n hn
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (iidProb_nonneg hd _ _)]
  refine lt_of_le_of_lt (iidProb_mono hd fun η hη => ?_) hn₁
  by_contra hnot
  push Not at hnot
  have hS := Trinomial.pearsonS_centroid hn₃ (Trinomial.count_add η)
  have hlt : Trinomial.pearsonS (Trinomial.count η 0) (Trinomial.count η 1) (Trinomial.count η 2) < t := by
    unfold chiSqTwoTail at hnot
    have h₂ := Real.log_lt_log hx0 hnot
    rw [Real.log_exp] at h₂
    rw [htdef]
    linarith
  rw [hS] at hlt
  set w := Trinomial.whiten 1 n (Trinomial.count η 0) (Trinomial.count η 1) (Trinomial.count η 2) with hw
  have hsq : ∀ y : ℝ, y ^ 2 < t → |y| < R := by
    intro y hy
    have h₁ : |y| ≤ √t := Real.abs_le_sqrt hy.le
    rw [hRdef]
    linarith
  have h₁ : |w.1| < R := hsq _ (by nlinarith [sq_nonneg w.2])
  have h₂ : |w.2| < R := hsq _ (by nlinarith [sq_nonneg w.1])
  have hclose := hn₂ _ _ _ (Trinomial.count_add η) h₁ h₂
  rw [hS] at hη
  exact absurd hη (not_le.2 hclose)

/-! ### Line 882: the quartet types -/

/-- **Line 882**, the right inclusion (`ecto:quartet_types_nested`): a tree `T` obtained from `T₀` by contracting edges has at each edge more
quartets of its multipartition, "`Smul(e) ⊇ Squad(e)`". -/
theorem multipartitionQuartets_anti {X : Type*} [Fintype X] [DecidableEq X] {T T₀ : Finset (Finset X)} (hT : T ⊆ T₀) (A : Finset X) :
    multipartitionQuartets T₀ A ⊆ multipartitionQuartets T A := by
  intro s hs
  obtain ⟨h₁, h₂, h₃⟩ := mem_filter.1 hs
  refine mem_filter.2 ⟨h₁, ?_, ?_⟩
  · rintro ⟨C, hC, hrest⟩
    exact h₂ ⟨C, hT hC, hrest⟩
  · rintro ⟨C, hC, hrest⟩
    exact h₃ ⟨C, hT hC, hrest⟩

/-- **Line 882**, the left inclusion (`ecto:quartet_types_nested`): "`Sbi(e) ⊇ Smul(e)`". -/
theorem multipartitionQuartets_subset_bipartitionQuartets {X : Type*} [Fintype X] [DecidableEq X] (T : Finset (Finset X)) (A : Finset X) :
    multipartitionQuartets T A ⊆ bipartitionQuartets A :=
  filter_subset _ _

end ECToBlob.InPassing
