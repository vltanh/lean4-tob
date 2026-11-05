module

public import ECToBlob.LevelCutoffs
public import Basic.UnitMetric

/-!
# ECToBlob Theorem 8.2 on the literal general model: the genericity is needed

E10 of the report. Theorem 8.2 quantifies over "any model" meeting Assumption 1, whose converse clauses hold only off a null set of parameters, while
its proof invokes "our assumption of generic numerical parameters". This file shows that without that exclusion the statement is false: there is no
choice of sequences `α_n`, `β_n`, even with no condition on them, that works at all valid parameters of all models meeting Assumption 1.

* `net`: the rooted 4-cycle with the arcs `s→r, s→d, r→u, r→v, u→h, v→h, u→a, v→b, h→c`, on the taxa `a, b, c, d = 0, 1, 2, 3`. Its tree of blobs
  is the star (`treeOfBlobs_eq`), and it has no trivial 4-blob.
* `model`: the law `(1/2, 1/4 + h(t), 1/4 - h(t))` on the three binary trees on four taxa, for `t` the length of the arc `s→r`, with
  `h(t) = (t - 1) / (8 (1 + (t - 1)²))`. It meets Assumption 1 (`assumption1`): the converse fails only at `t = 1`, a null set of parameters.
* At `t = 1` this law is `(1/2, 1/4, 1/4)` (`model_of_length_eq_one`), the law on the tree `ab|cd` (`BinaryLaw.OnFour.law`), which meets both
  directions of Assumption 1 and has the same `T₀` as a resolution of its tree of blobs. The two trees of blobs differ, so one sample law cannot
  converge to both (`not_theorem8_2_literal`).

This is not a counterexample under the NMSC: `model` is an abstract model in the sense of "any model". Lean's `ECToBlob.theorem8_2` takes parameters
meeting both clauses, and `ECToBlob.theorem8_2_generic` gives the conclusion for almost all parameters.
-/

@[expose] public noncomputable section

open Phylogenetics Phylogenetics.RootedNetwork Phylogenetics.QuartetTests Finset Filter Topology MeasureTheory
open scoped Classical

namespace ECToBlob.Theorem82Literal

open ECToBlob.FinNetwork ECToBlob.FalseEdge ECToBlob.Coarsening ECToBlob.BinaryLaw

/-- The tails of the arcs `s→r, s→d, r→u, r→v, u→h, v→h, u→a, v→b, h→c`, with the taxa `a, b, c, d = 0, 1, 2, 3`, and `h, u, v, r, s = 4, …, 8`. -/
def src : Fin 9 → Fin 9 := ![8, 8, 7, 7, 5, 6, 5, 6, 4]

/-- The heads of the arcs. -/
def tgt : Fin 9 → Fin 9 := ![7, 3, 5, 6, 4, 4, 0, 1, 2]

/-- The taxa, as vertices. -/
def lf : Fin 4 → Fin 9 := ![0, 1, 2, 3]

/-- What each vertex reaches. -/
def desc : Fin 9 → Finset (Fin 9) :=
  ![{0}, {1}, {2}, {3}, {2, 4}, {0, 2, 4, 5}, {1, 2, 4, 6}, {0, 1, 2, 4, 5, 6, 7}, {0, 1, 2, 3, 4, 5, 6, 7, 8}]

/-- What the root reaches off each arc. -/
def avoid : Fin 9 → Finset (Fin 9) :=
  ![{3, 8}, {0, 1, 2, 4, 5, 6, 7, 8}, {1, 2, 3, 4, 6, 7, 8}, {0, 2, 3, 4, 5, 7, 8}, {0, 1, 2, 3, 4, 5, 6, 7, 8},
    {0, 1, 2, 3, 4, 5, 6, 7, 8}, {1, 2, 3, 4, 5, 6, 7, 8}, {0, 2, 3, 4, 5, 6, 7, 8}, {0, 1, 3, 4, 5, 6, 7, 8}]

theorem tables : Tables src tgt 8 desc avoid :=
  ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩

/-- **The rooted 4-cycle of E10.** -/
abbrev net : RootedNetwork (Fin 9) (Fin 9) (Fin 4) := ECToBlob.FinNetwork.net src tgt 8 lf

theorem net_isPhylogenetic : net.IsPhylogenetic :=
  isPhylogenetic_of_down (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

/-- No set of four taxa has a trivial 4-blob. -/
theorem not_hasTrivialFourBlob {Q : Finset (Fin 4)} (hQ : Q.card = 4) : ¬ HasTrivialFourBlob net Q := by
  have : ∀ Q : Finset (Fin 4), Q.card = 4 → ∀ v, ¬ HubT src tgt lf desc avoid Q v := by decide
  rw [tables.hasTrivialFourBlob_iff net_isPhylogenetic hQ]
  rintro ⟨v, hv⟩
  exact this Q hQ v hv

/-- No quartet tree is a cut split of the network. -/
theorem not_inducedCutSplit (s : QuartetTree (Fin 4)) : ¬ InducedCutSplit net s := by
  intro h
  obtain ⟨a, b, c, d, hc, -, hr⟩ := exists_rdom_of_inducedCutSplit net_isPhylogenetic h
  have hdec : ∀ a b c d : Fin 4, ({a, b, c, d} : Finset (Fin 4)).card = 4 → ¬ RDomT tgt lf desc avoid a b c d := by decide
  exact hdec a b c d hc (tables.rdom_iff.1 hr)

/-- **The tree of blobs is the star.** -/
theorem treeOfBlobs_eq : treeOfBlobs net = unroot {univ, {0}, {1}, {2}, {3}} := by
  ext A
  rw [tables.mem_treeOfBlobs_iff net_isPhylogenetic]
  unfold unroot
  revert A
  decide

theorem isResolutionOf_T₀ : IsResolutionOf OnFour.T₀ (treeOfBlobs net) := by
  refine ⟨OnFour.T₀_isUnrootedTree, ?_⟩
  rw [treeOfBlobs_eq]
  unfold OnFour.T₀ OnFour.hier unroot
  decide

theorem T₀_ne : OnFour.T₀ ≠ treeOfBlobs net := by
  rw [treeOfBlobs_eq]
  unfold OnFour.T₀ OnFour.hier unroot
  decide

/-! ### The model -/

/-- The family `h(t) = (t - 1) / (8 (1 + (t - 1)²))`. -/
def h (t : ℝ) : ℝ := (t - 1) / (8 * (1 + (t - 1) ^ 2))

theorem h_bounds (t : ℝ) : -(1 / 16 : ℝ) ≤ h t ∧ h t ≤ 1 / 16 := by
  have hd : 0 < 8 * (1 + (t - 1) ^ 2) := by nlinarith [sq_nonneg (t - 1)]
  constructor
  · rw [h, le_div_iff₀ hd]
    nlinarith [sq_nonneg t]
  · rw [h, div_le_iff₀ hd]
    nlinarith [sq_nonneg (t - 2)]

theorem h_eq_zero_iff (t : ℝ) : h t = 0 ↔ t = 1 := by
  have hd : 8 * (1 + (t - 1) ^ 2) ≠ 0 := by nlinarith [sq_nonneg (t - 1)]
  simp [h, div_eq_zero_iff, hd, sub_eq_zero]

/-- **The model of E10**: at the parameters `θ`, the law `(1/2, 1/4 + h(t), 1/4 - h(t))` on the three binary trees on four taxa, for `t` the length of
the arc `s→r`. -/
def model (θ : MetricData (Fin 9)) : BinaryGeneTree (Fin 4) → ℝ := OnBlob.law (h (θ.length 0))

theorem law_isDist' {q : ℝ} (h0 : -(1 / 4) ≤ q) (h1 : q ≤ 1 / 4) : IsDist (OnBlob.law q) := by
  refine pointLaw_isDist (fun i => ?_) ?_
  · fin_cases i
    · show (0 : ℝ) ≤ 1 / 2
      norm_num
    · show (0 : ℝ) ≤ 1 / 4 + q
      linarith
    · show (0 : ℝ) ≤ 1 / 4 - q
      linarith
  · rw [Fin.sum_univ_three]
    show 1 / 2 + (1 / 4 + q) + (1 / 4 - q) = 1
    ring

theorem model_isDist (θ : MetricData (Fin 9)) : IsDist (model θ) := by
  have := h_bounds (θ.length 0)
  exact law_isDist' (by linarith) (by linarith)

theorem wt_injective' {q : ℝ} (h0 : q ≠ 0) (h1 : -(1 / 16) ≤ q) (h2 : q ≤ 1 / 16) :
    Function.Injective (OnBlob.wt q) := by
  have hne : q ≠ -q := fun he => h0 (by linarith)
  intro i j hij
  fin_cases i <;> fin_cases j <;> first
    | rfl
    | (exfalso; simp only [OnBlob.wt] at hij; norm_num at hij; first | linarith | exact hne (by linarith))

/-- Assumption 1's forward direction holds at all parameters: the network has no trivial 4-blob and no cut split. -/
theorem assumption1Forward (p : QuartetTree (Fin 4) → ℝ) : Assumption1Forward net p :=
  ⟨fun _ hQ htr => absurd htr (not_hasTrivialFourBlob hQ), fun s hs => absurd hs (not_inducedCutSplit s)⟩

/-- Assumption 1's converse holds for the law, off `q = 0`, where the law is on the T1 null of `ab|cd`. -/
theorem assumption1Converse {q : ℝ} (h0 : q ≠ 0) (h1 : -(1 / 16) ≤ q) (h2 : q ≤ 1 / 16) :
    Assumption1Converse net (displayCF (OnBlob.law q) Subtype.val) := by
  refine ⟨fun Q hQ _ hu => ?_, fun s _ hstrict => ?_⟩
  · have hc : ({0, 1, 2, 3} : Finset (Fin 4)).card = 4 := by decide
    have hQu : Q = univ := Finset.eq_univ_of_card Q (by rw [hQ]; rfl)
    have hmem : quartetTree 0 1 2 3 hc ∈ treesOn Q := by
      rw [hQu]
      exact mem_treesOn.2 (OnFour.taxa_eq_univ _)
    have hv := hu _ hmem
    rw [OnBlob.displayCF_law] at hv
    have hcl : OnBlob.cls (quartetTree 0 1 2 3 hc) = 0 := by
      unfold OnBlob.cls
      rw [ite_eq_left (by simp [quartetTree])]
    rw [hcl] at hv
    simp only [OnBlob.wt] at hv
    exact absurd hv (by simp)
  · obtain ⟨r, hr, r', hr', hne⟩ := Finset.one_lt_card.1 (by rw [s.card_alternatives]; norm_num : 1 < s.alternatives.card)
    have heq := hstrict.2 r hr r' hr'
    rw [OnBlob.displayCF_law, OnBlob.displayCF_law] at heq
    exact hne (OnBlob.eq_of_cls_eq (wt_injective' h0 h1 h2 heq))

/-- The arc `s→r` is a tree arc. -/
theorem not_isHybridArc_zero : ¬ net.IsHybridArc 0 := by
  have hin : net.graph.indegree (tgt 0) = (univ.filter fun e => tgt e = tgt 0).card := by
    rw [DirectedMultigraph.indegree, Set.ncard_eq_toFinset_card']
    congr 1
  have h1 : (univ.filter fun e => tgt e = tgt 0).card = 1 := by decide
  change ¬ 2 ≤ net.graph.indegree (tgt 0)
  omega

/-- The parameters at which the arc `s→r` has length `1` are null. -/
theorem isNullParams_length_eq_one : IsNullParams net {θ | θ.length 0 = 1} := by
  intro d _
  have hatoms : NullSingletonClass (lengthMeasure (net.IsHybridArc 0)) := by
    rw [lengthMeasure, ite_eq_right not_isHybridArc_zero]
    infer_instance
  have hz : Measure.pi (fun e => lengthMeasure (net.IsHybridArc e)) {f : Fin 9 → ℝ | f 0 = 1} = 0 :=
    Measure.pi_hyperplane _ 0 1
  have hprod : ((Measure.pi fun e => lengthMeasure (net.IsHybridArc e)).prod
      (Measure.pi fun _ : Fin 9 => volume.restrict (Set.Ioo (0 : ℝ) 1)))
      ({f : Fin 9 → ℝ | f 0 = 1} ×ˢ Set.univ) = 0 := by
    rw [Measure.prod_prod, hz, zero_mul]
  refine measure_mono_null ?_ hprod
  rintro x ⟨-, hx⟩
  exact ⟨hx, Set.mem_univ _⟩

/-- **The model meets Assumption 1** (`ecto:thm8_2_literal_model`). -/
theorem assumption1 : Assumption1 net fun θ => displayCF (model θ) Subtype.val := by
  refine ⟨fun θ _ => assumption1Forward _, IsNullParams.mono isNullParams_length_eq_one ?_⟩
  rintro θ ⟨-, hnot⟩
  by_contra hne
  have hq : h (θ.length 0) ≠ 0 := fun h0 => hne ((h_eq_zero_iff _).1 h0)
  have hb := h_bounds (θ.length 0)
  exact hnot (assumption1Converse hq hb.1 hb.2)

/-- **At `t = 1` the law of the model is the law of a resolved tree**: `(1/2, 1/4, 1/4)`. -/
theorem model_of_length_eq_one {θ : MetricData (Fin 9)} (hθ : θ.length 0 = 1) : model θ = OnFour.law (1 / 4) := by
  have hwt : OnBlob.wt (h (θ.length 0)) = ![1 - 2 * (1 / 4), 1 / 4, 1 / 4] := by
    rw [hθ, (h_eq_zero_iff 1).2 rfl]
    funext i
    fin_cases i <;> simp [OnBlob.wt]
    norm_num
  unfold model OnBlob.law OnFour.law
  rw [hwt]

/-- All the concordance factors of the law of the resolved tree are positive. -/
theorem displayCF_law_pos (r : QuartetTree (Fin 4)) : 0 < displayCF (OnFour.law (1 / 4)) Subtype.val r := by
  rw [OnFour.displayCF_law, OnFour.pq]
  split_ifs <;> norm_num

/-- The law of the resolved tree meets Assumption 1 on it, as a constant model. -/
theorem assumption1_tree : Assumption1 OnFour.net fun _ : MetricData (Fin 6) => displayCF (OnFour.law (1 / 4)) Subtype.val := by
  obtain ⟨h₁, h₂⟩ := OnFour.law_assumption1 (q := 1 / 4) (by norm_num)
  refine ⟨fun _ _ => h₁, fun d _ => ?_⟩
  refine measure_mono_null ?_ measure_empty
  rintro x ⟨-, -, hnot⟩
  exact hnot h₂

/-- (`ecto:thm8_2_literal`) **E10 of the report: Theorem 8.2 is false on the literal general model.** For each variant of the algorithm there are no sequences
`α_n`, `β_n`, whatever they are, such that the output is the tree of blobs with probability tending to one at all valid parameters of all models meeting
Assumption 1. The rooted 4-cycle with `model` at `t = 1` and the tree `ab|cd` with `(1/2, 1/4, 1/4)` have one law on gene trees, and one tree `T₀`
resolving both trees of blobs, which differ. Assumption 1 excludes `t = 1` only through its null set, which `ECToBlob.theorem8_2_generic` takes out. -/
theorem not_theorem8_2_literal (o : ECToBlobOptions) :
    ¬ ∃ α β : ℕ → ℝ, ∀ {V E X : Type} [Fintype V] [Fintype E] [Fintype X] [DecidableEq X] (N : RootedNetwork V E X)
      (_ : N.IsPhylogenetic) (dist : MetricData E → BinaryGeneTree X → ℝ) (_ : ∀ θ, N.IsMetric θ → IsDist (dist θ))
      (_ : Assumption1 N fun θ => displayCF (dist θ) Subtype.val) (θ : MetricData E) (_ : N.IsMetric θ)
      (T₀ : Finset (Finset X)) (_ : IsResolutionOf T₀ (treeOfBlobs N))
      (_ : (o.testCo = .cauchy ∨ o.testCo = .cbc) →
        ∀ s, IsT1Strict (displayCF (dist θ) Subtype.val) s →
          ∀ r ∈ s.alternatives, 0 < displayCF (dist θ) Subtype.val r),
      Tendsto (fun n => iidProb (dist θ) n fun ω =>
        ectoblob o (α n) (β n) (quartetCount Subtype.val ω) T₀ = treeOfBlobs N) atTop (𝓝 1) := by
  rintro ⟨α, β, h⟩
  have hθ₁ : (unitMetric net).length 0 = 1 := rfl
  have hlaw := model_of_length_eq_one hθ₁
  have hd : IsDist (OnFour.law (1 / 4)) := OnFour.law_isDist (by norm_num) (by norm_num)
  have hcycle := h net net_isPhylogenetic model (fun θ _ => model_isDist θ) assumption1 (unitMetric net)
    (isMetric_unitMetric net) OnFour.T₀ isResolutionOf_T₀
    (fun _ _ _ r _ => by rw [hlaw]; exact displayCF_law_pos r)
  rw [hlaw] at hcycle
  have htree := h OnFour.net OnFour.net_isPhylogenetic (fun _ => OnFour.law (1 / 4)) (fun _ _ => hd) assumption1_tree
    (unitMetric OnFour.net) (isMetric_unitMetric _) OnFour.T₀ ⟨OnFour.T₀_isUnrootedTree, OnFour.treeOfBlobs_eq.le⟩
    (fun _ _ _ r _ => displayCF_law_pos r)
  rw [OnFour.treeOfBlobs_eq] at htree
  exact one_ne_zero (tendsto_nhds_unique hcycle (tendsto_eq_zero_of_tendsto_eq hd T₀_ne htree))

end ECToBlob.Theorem82Literal
