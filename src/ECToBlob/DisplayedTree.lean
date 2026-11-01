module

public import ECToBlob.Framework
public import ECToBlob.Remarks

/-!
# ECToBlob Theorem 8.2 for the displayed tree model

`ECToBlob.theorem8_2` takes binary gene trees, so it does not reach the displayed tree model on a non-binary network, where
a gene tree may have polytomies and, by the convention of lines 289-293, a star contributes `(1/3, 1/3, 1/3)` to the
counts (`conventionCount`). This file settles what happens there.

* **Bon and BBC: the conclusion holds** (`theorem8_2_displayed`, `tendsto_ectoblob_displayed_limitTree`). Line 1065, "each
  individual p-value is uniformly distributed", is false for this model (`ECToBlob.not_asymptoticallyUniform_starPValue`),
  and Lemma 8.1 does not apply. But each p-value under the null is exactly `1` on every sample of positive probability, at
  a trivial 4-blob (`ECToBlob.pValues_of_hasTrivialFourBlob`) and at a cut split (`t1PValue_of_inducedCutSplit`), and these
  two methods use only the lower bound on the p-values under the null (E15 of the report). Under the alternative the
  growth of the statistics is that of a law of large numbers, for any law on unrooted gene trees (`starPValue_growth`,
  `t1PValue_growth`). So the tests are `Framework.AdequateTests`.
* **Cauchy and CBC: the T1 tests do nothing** (`ectoblob_eq_afterStar`): if the tree of blobs has an internal edge kept by
  Step 3, then on every sample of positive probability the output is the tree after Step 3, at all levels `α ≤ 1`. The
  reason is E11 of the report: `Cauchy` of positive p-values containing `1` is `1`. So a false edge that Step 3 keeps stays,
  and the output is the tree of blobs with probability tending to zero (`tendsto_ectoblob_displayed_zero`). The
  counterexamples are in `ECToBlob.DisplayedTreeExample`, on a binary network and on a non-binary one.
-/

@[expose] public noncomputable section

open Phylogenetics Phylogenetics.RootedNetwork Phylogenetics.QuartetTests Finset Filter Topology
open scoped Classical

namespace ECToBlob.DisplayedTree

open ECToBlob.Deterministic ECToBlob.Coarsening ECToBlob.Framework

/-! ### Laws on unrooted gene trees: growth under the alternative -/

section Growth

variable {X : Type*} [Fintype X] [DecidableEq X] {dist : UnrootedGeneTree X → ℝ}

omit [DecidableEq X] [Fintype X] in
theorem geneContribution_nonneg [Fintype X] [DecidableEq X] (T : Finset (Finset X)) (s : QuartetTree X) :
    0 ≤ geneContribution T s := by
  unfold geneContribution
  split_ifs <;> norm_num

theorem conventionCount_nonneg {n : ℕ} (ω : Fin n → UnrootedGeneTree X) (r : QuartetTree X) :
    0 ≤ conventionCount ω r :=
  sum_nonneg fun _ _ => geneContribution_nonneg _ _

theorem expectedCF_nonneg (hd : IsDist dist) (r : QuartetTree X) : 0 ≤ expectedCF dist r :=
  sum_nonneg fun G _ => mul_nonneg (hd.1 G) (geneContribution_nonneg _ _)

/-- Under the convention of lines 289-293 the concordance factors on four taxa sum to one, and so do the counts to `n`. -/
theorem sum_expectedCF (hd : IsDist dist) {q : Finset X} (hq : q.card = 4) :
    ∑ r ∈ treesOn q, expectedCF dist r = 1 := by
  unfold expectedCF
  rw [sum_comm, ← hd.2]
  refine sum_congr rfl fun G _ => ?_
  rw [← mul_sum, sum_geneContribution G.2 hq, mul_one]

/-- **The weak law of large numbers** for the counts of the convention of lines 289-293 (line 293). -/
theorem tendsto_iidProb_conventionFreq (hd : IsDist dist) {P : (QuartetTree X → ℝ) → Prop}
    (hP : ∀ᶠ x in 𝓝 (expectedCF dist), P x) :
    Tendsto (fun n : ℕ => iidProb dist n fun ω => P fun r => conventionCount ω r / n) atTop (𝓝 1) := by
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.1 hP
  have h : Tendsto (fun n : ℕ => iidProb dist n fun ω : Fin n → UnrootedGeneTree X => ∀ r : QuartetTree X,
      |(∑ i, geneContribution (ω i).val r) / n - ∑ G, dist G * geneContribution G.val r| < ε)
      atTop (𝓝 1) :=
    tendsto_iidProb_forall hd _ fun r => iidProb_weak_law hd (fun G => geneContribution G.val r) hε
  refine tendsto_iidProb_of_imp hd (Eventually.of_forall fun n ω hω => hball ?_) h
  rw [dist_pi_lt_iff hε]
  intro r
  rw [Real.dist_eq]
  exact hω r

/-- A statistic of degree one which at the concordance factors exceeds `d` exceeds `n d` on the counts, with probability
tending to one. -/
theorem tendsto_stat_gt (hd : IsDist dist) (F : (QuartetTree X → ℝ) → ℝ)
    (hhom : ∀ a : ℝ, 0 < a → ∀ c, F (fun r => a * c r) = a * F c) {d : ℝ}
    (hF : ∀ᶠ x in 𝓝 (expectedCF dist), d < F x) {b : ℕ → ℝ}
    (hb : ∀ᶠ n : ℕ in atTop, b n ≤ n * d) :
    Tendsto (fun n => iidProb dist n fun ω => b n < F (conventionCount ω)) atTop (𝓝 1) := by
  refine tendsto_iidProb_of_imp hd ?_ (tendsto_iidProb_conventionFreq hd hF)
  filter_upwards [hb, eventually_gt_atTop 0] with n hn hn0 ω hω
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn0
  have hc : conventionCount ω = fun r => (n : ℝ) * (conventionCount ω r / n) := by
    funext r
    field_simp
  rw [hc, hhom _ hn']
  exact hn.trans_lt (mul_lt_mul_of_pos_left hω hn')

/-- The statistic of the star test on the counts of a law on unrooted gene trees grows linearly off the centroid, so its
p-value is below `exp(-b_n/2)` for each `b_n = o(n)`. -/
theorem starPValue_growth (k : StarTest) (hd : IsDist dist) {q : Finset X} (hq : q.card = 4)
    (h : ¬ IsUniformOn (expectedCF dist) q) {b : ℕ → ℝ}
    (hb : Tendsto (fun n : ℕ => b n / n) atTop (𝓝 0)) :
    Tendsto (fun n => iidProb dist n fun ω =>
      starPValue k (conventionCount ω) q < Real.exp (-(b n) / 2)) atTop (𝓝 1) := by
  have hp0 := expectedCF_nonneg hd
  have hp1 := sum_expectedCF hd hq
  obtain ⟨r₀, hr₀, hne⟩ : ∃ r ∈ treesOn q, expectedCF dist r ≠ 1 / 3 := by
    unfold IsUniformOn at h
    push Not at h
    exact h
  obtain ⟨F, hhom, hcont, hpos, hval⟩ : ∃ F : (QuartetTree X → ℝ) → ℝ,
      (∀ a : ℝ, 0 < a → ∀ c, F (fun r => a * c r) = a * F c) ∧
      ContinuousAt F (expectedCF dist) ∧ 0 < F (expectedCF dist) ∧
      ∀ c, starPValue k c q = chiSqTwoTail (F c) := by
    cases k with
    | lrt =>
      exact ⟨fun c => starStat c q, fun a ha c => starStat_const_mul ha.ne' c q,
        (continuous_starStat q).continuousAt, starStat_pos _ hp0 hq hp1 ⟨r₀, hr₀, hne⟩,
        fun c => rfl⟩
    | pearson =>
      refine ⟨fun c => pearsonStat c q, fun a ha c => pearsonStat_const_mul ha.ne' c q,
        continuousAt_pearsonStat q (by rw [hp1]; norm_num), ?_, fun c => rfl⟩
      show 0 < pearsonStat _ q
      unfold pearsonStat
      rw [hp1]
      refine Finset.sum_pos' (fun r _ => by positivity) ⟨r₀, hr₀, ?_⟩
      have : expectedCF dist r₀ - 1 / 3 ≠ 0 := sub_ne_zero.2 hne
      positivity
  have hd2 : 0 < F (expectedCF dist) / 2 := by positivity
  have hF : ∀ᶠ x in 𝓝 (expectedCF dist), F (expectedCF dist) / 2 < F x :=
    hcont.tendsto.eventually_const_lt (by linarith)
  refine tendsto_iidProb_of_imp hd (Eventually.of_forall fun n ω hω => ?_)
    (tendsto_stat_gt hd F hhom hF (eventually_le_mul hb hd2))
  rw [hval]
  exact Real.exp_lt_exp.2 (by linarith)

/-- Off the T1 null, at concordance factors summing to one, the T1 statistic is positive around them. -/
theorem exists_t1Stat_gt {p : QuartetTree X → ℝ} (hp0 : ∀ r, 0 ≤ p r) {s : QuartetTree X}
    (hp1 : ∑ r ∈ treesOn s.taxa, p r = 1) (h : ¬ IsT1Null p s) :
    ∃ d : ℝ, 0 < d ∧ ∀ᶠ x in 𝓝 p, d < t1Stat x s := by
  obtain ⟨r, r', hne, halts⟩ := QuartetTree.exists_alternatives s
  have hr : r ∈ s.alternatives := by simp [halts]
  have hr' : r' ∈ s.alternatives := by simp [halts]
  have hrT := mem_treesOn_taxa_of_mem_alternatives hr
  have hrT' := mem_treesOn_taxa_of_mem_alternatives hr'
  have hsT := QuartetTests.mem_treesOn_taxa s
  by_cases heq : p r = p r'
  · -- on the line: the true topology has probability below the alternatives, in the star regime
    have hlt : p s < p r := by
      by_contra hcon
      push Not at hcon
      refine h ⟨fun u hu => ?_, fun u hu u' hu' => ?_⟩
      · rw [halts] at hu
        simp only [Finset.mem_insert, Finset.mem_singleton] at hu
        rcases hu with rfl | rfl
        · exact hcon
        · rw [← heq]; exact hcon
      · rw [halts] at hu hu'
        simp only [Finset.mem_insert, Finset.mem_singleton] at hu hu'
        rcases hu with rfl | rfl <;> rcases hu' with rfl | rfl
        · rfl
        · exact heq
        · exact heq.symm
        · rfl
    have hstar : 0 < starStat p s.taxa := by
      refine starStat_pos _ hp0 s.card_taxa hp1 ?_
      by_cases hs3 : p s = 1 / 3
      · exact ⟨r, hrT, fun h' => by linarith⟩
      · exact ⟨s, hsT, hs3⟩
    refine ⟨starStat p s.taxa / 2, by positivity, ?_⟩
    have h1 : ∀ᶠ x in 𝓝 p, starStat p s.taxa / 2 < starStat x s.taxa :=
      (continuous_starStat s.taxa).continuousAt.tendsto.eventually_const_lt (by linarith)
    have h2 : ∀ᶠ x : QuartetTree X → ℝ in 𝓝 p, x s < (x r + x r') / 2 := by
      refine ContinuousAt.eventually_lt (continuous_apply s).continuousAt
        (((continuous_apply r).add (continuous_apply r')).div_const 2).continuousAt ?_
      rw [← heq]
      linarith
    filter_upwards [h1, h2] with x hx1 hx2
    unfold t1Stat
    rw [halts, Finset.sum_pair hne, ite_eq_right (not_le.2 hx2)]
    exact hx1
  · -- off the line: both statistics of the T1 test are positive
    have hline : 0 < lineStat p s := lineStat_pos _ hp0 s ⟨r, hr, r', hr', heq⟩
    have hstar : 0 < starStat p s.taxa := by
      refine starStat_pos _ hp0 s.card_taxa hp1 ?_
      by_cases hs3 : p r = 1 / 3
      · exact ⟨r', hrT', fun h' => heq (hs3.trans h'.symm)⟩
      · exact ⟨r, hrT, hs3⟩
    have hmin : 0 < min (lineStat p s) (starStat p s.taxa) := lt_min hline hstar
    refine ⟨min (lineStat p s) (starStat p s.taxa) / 2, by positivity, ?_⟩
    have h1 : ∀ᶠ x in 𝓝 p, min (lineStat p s) (starStat p s.taxa) / 2 < lineStat x s :=
      (continuous_lineStat s).continuousAt.tendsto.eventually_const_lt
        (by have := min_le_left (lineStat p s) (starStat p s.taxa); linarith)
    have h2 : ∀ᶠ x in 𝓝 p, min (lineStat p s) (starStat p s.taxa) / 2 < starStat x s.taxa :=
      (continuous_starStat s.taxa).continuousAt.tendsto.eventually_const_lt
        (by have := min_le_right (lineStat p s) (starStat p s.taxa); linarith)
    filter_upwards [h1, h2] with x hx1 hx2
    unfold t1Stat
    split_ifs
    · exact hx1
    · exact hx2

/-- The T1 p-value on the counts of a law on unrooted gene trees, off the T1 null, is below `exp(-b_n/2)` for each
`b_n = o(n)`. -/
theorem t1PValue_growth (hd : IsDist dist) {s : QuartetTree X} (h : ¬ IsT1Null (expectedCF dist) s)
    {b : ℕ → ℝ} (hb : Tendsto (fun n : ℕ => b n / n) atTop (𝓝 0)) :
    Tendsto (fun n => iidProb dist n fun ω =>
      t1PValue (conventionCount ω) s < Real.exp (-(b n) / 2)) atTop (𝓝 1) := by
  obtain ⟨d, hd0, hF⟩ := exists_t1Stat_gt (expectedCF_nonneg hd) (sum_expectedCF hd s.card_taxa) h
  refine tendsto_iidProb_of_imp hd (Eventually.of_forall fun n ω hω => ?_)
    (tendsto_stat_gt hd (fun c => t1Stat c s) (fun a ha c => t1Stat_const_mul ha c s) hF
      (eventually_le_mul hb hd0))
  have hc := conventionCount_nonneg ω
  have hmu := muZero_t1Phi_nonneg (conventionCount ω) s
  have hstat := t1Stat_nonneg (conventionCount ω) hc s
  calc t1PValue (conventionCount ω) s ≤ chiSqTwoTail (t1Stat (conventionCount ω) s) :=
        t1Tail_le_chiSqTwoTail hmu hstat
    _ < _ := Real.exp_lt_exp.2 (by linarith)

/-- The star p-value is in `[0, 1]` on nonnegative counts. -/
theorem starPValue_mem' (k : StarTest) {c : QuartetTree X → ℝ} (hc : ∀ r, 0 ≤ c r) {q : Finset X}
    (hq : q.card = 4) : 0 ≤ starPValue k c q ∧ starPValue k c q ≤ 1 := by
  cases k with
  | lrt => exact ⟨(Real.exp_pos _).le, Real.exp_le_one_iff.2 (by
      have := starStat_nonneg _ hc hq
      linarith)⟩
  | pearson => exact ⟨(Real.exp_pos _).le, Real.exp_le_one_iff.2 (by
      have : 0 ≤ pearsonStat c q := Finset.sum_nonneg fun r _ => div_nonneg (sq_nonneg _)
        (div_nonneg (Finset.sum_nonneg fun t _ => hc t) (by norm_num))
      linarith)⟩

/-- The T1 p-value is positive: it is at least the tail of `χ²₁`. -/
theorem t1PValue_pos (c : QuartetTree X → ℝ) (s : QuartetTree X) : 0 < t1PValue c s :=
  (chiSqOneTail_pos _).trans_le (chiSqOneTail_le_t1Tail _ _)

/-- With no count on the alternatives of `s`, the T1 statistic vanishes and the p-value is `1`. -/
theorem t1PValue_of_alternatives_zero {c : QuartetTree X → ℝ} {s : QuartetTree X}
    (hc : ∀ r ∈ s.alternatives, c r = 0) (hs : 0 ≤ c s) : t1PValue c s = 1 := by
  have hsum : ∑ r ∈ s.alternatives, c r = 0 := sum_eq_zero hc
  have hstat : t1Stat c s = 0 := by
    unfold t1Stat
    rw [ite_eq_left (by rw [hsum]; simpa using hs)]
    unfold lineStat
    rw [hsum, sum_eq_zero fun r hr => by rw [hc r hr, zero_mul]]
    simp
  unfold t1PValue
  rw [hstat]
  refine le_antisymm (Trinomial.t1Tail_le_one _ _) ?_
  have hle := QuartetTests.chiSqOneTail_le_t1Tail
    (muZero (t1Phi c s) (c s + ∑ r ∈ s.alternatives, c r)) 0
  rwa [Trinomial.chiSqOneTail_zero] at hle

/-- Two events hold together with at least the sum of their probabilities, less one. -/
theorem iidProb_and_ge' {Γ : Type*} [Fintype Γ] {dist : Γ → ℝ} (hd : IsDist dist) (n : ℕ)
    (A B : (Fin n → Γ) → Prop) :
    iidProb dist n A + iidProb dist n B - 1 ≤ iidProb dist n fun ω => A ω ∧ B ω := by
  have h1 := iidProb_true hd n
  have hw : ∀ ω : Fin n → Γ, 0 ≤ ∏ i, dist (ω i) := fun ω => Finset.prod_nonneg fun i _ => hd.1 _
  unfold iidProb at h1 ⊢
  rw [← h1, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_le_sum fun ω _ => ?_
  by_cases hA : A ω <;> by_cases hB : B ω <;> simp [hA, hB, hw ω]

/-- With probability one, all draws have positive probability. -/
theorem iidProb_forall_ne_zero {Γ : Type*} [Fintype Γ] {dist : Γ → ℝ} (hd : IsDist dist) (n : ℕ) :
    iidProb dist n (fun ω => ∀ i, dist (ω i) ≠ 0) = 1 := by
  rw [← iidProb_true hd n]
  unfold iidProb
  refine sum_congr rfl fun ω _ => ?_
  by_cases h : ∀ i, dist (ω i) ≠ 0
  · simp [h]
  · push Not at h
    obtain ⟨i, hi⟩ := h
    have h0 : ∏ i, dist (ω i) = 0 := prod_eq_zero (mem_univ i) hi
    simp [h0]

end Growth

/-! ### The displayed tree model -/

section Displayed

variable {V E X : Type*} [Fintype V] [Fintype E] [Fintype X] [DecidableEq X] [Nonempty X]
  {N : RootedNetwork V E X} {θ : MetricData E}

/-- **The forward direction of Assumption 1 holds for the displayed tree model at all parameters**: a trivial 4-blob gives
`(1/3, 1/3, 1/3)`, and a cut split `(1, 0, 0)`. -/
theorem assumption1Forward_displayed (hN : N.IsPhylogenetic) (hθ : N.IsNormalized θ) :
    Assumption1Forward N (displayedCF N θ) := by
  refine ⟨fun q hq ht r hr => ?_, fun s hs => ⟨fun r hr => ?_, fun r hr r' hr' => ?_⟩⟩
  · have hq' : r.taxa = q := mem_treesOn.1 hr
    exact displayedCF_of_hasTrivialFourBlob hN hθ (hq' ▸ ht)
  · obtain ⟨h1, h0⟩ := displayedCF_of_inducedCutSplit hN hθ hs
    rw [h1, h0 r hr]
    exact zero_lt_one
  · obtain ⟨_, h0⟩ := displayedCF_of_inducedCutSplit hN hθ hs
    rw [h0 r hr, h0 r' hr']

omit [Nonempty X] in
/-- A gene tree of positive probability is a displayed tree. -/
theorem exists_displayedSides_eq {G : UnrootedGeneTree X} (hG : displayedTreeDist N θ G ≠ 0) :
    ∃ c : N.ParentChoice, N.displayedSides c = G.val := by
  obtain ⟨c, -, hc⟩ := exists_ne_zero_of_sum_ne_zero hG
  refine ⟨c, ?_⟩
  by_contra hne
  exact hc (ite_eq_right hne)

omit [Nonempty X] in
/-- **At a cut split the T1 p-value is `1`**, on every sample of positive probability: every displayed tree displays it. -/
theorem t1PValue_of_inducedCutSplit (hN : N.IsPhylogenetic) {s : QuartetTree X} (hs : InducedCutSplit N s)
    {n : ℕ} {ω : Fin n → UnrootedGeneTree X} (hω : ∀ i, displayedTreeDist N θ (ω i) ≠ 0) :
    t1PValue (conventionCount ω) s = 1 := by
  refine t1PValue_of_alternatives_zero (fun r hr => ?_) (conventionCount_nonneg ω s)
  refine sum_eq_zero fun i _ => ?_
  obtain ⟨c, hc⟩ := exists_displayedSides_eq (hω i)
  have hd := displays_displayedSides_of_inducedCutSplit hN c hs
  rw [hc] at hd
  exact (geneContribution_of_displays (ω i).2 hd).2 r hr

/-- **Under the T1 null, in the terms of the network, the T1 p-value is `1`**, on every sample of positive probability. -/
theorem t1PValue_of_isNullQuartet (hN : N.IsPhylogenetic) {s : QuartetTree X} (hs : IsNullQuartet N s)
    {n : ℕ} {ω : Fin n → UnrootedGeneTree X} (hω : ∀ i, displayedTreeDist N θ (ω i) ≠ 0) :
    t1PValue (conventionCount ω) s = 1 := by
  rcases hs with hs | hs
  · exact t1PValue_of_inducedCutSplit hN hs hω
  · exact (pValues_of_hasTrivialFourBlob (θ := θ) hN s.card_taxa hs hω .lrt).2 s
      (QuartetTests.mem_treesOn_taxa s)

variable (N θ) in
/-- The tests of the paper on the displayed tree model, with the convention of lines 289-293, are adequate for Bon and BBC
at any levels with `o(n)` cutoffs: they need only the lower bound on the p-values under the null, and these are `1`. -/
theorem adequateTests_displayed (hN : N.IsPhylogenetic) (hθ : N.IsWeakMetric θ)
    (h₂ : Assumption1Converse N (displayedCF N θ)) (o : ECToBlobOptions)
    (hm : o.testCo = .bon ∨ o.testCo = .bbc) {α β : ℕ → ℝ} (hαpos : ∀ᶠ n in atTop, 0 < α n)
    (hβpos : ∀ᶠ n in atTop, 0 < β n)
    (hα : Tendsto (fun n : ℕ => Real.log (α n) / n) atTop (𝓝 0))
    (hβ : Tendsto (fun n : ℕ => Real.log (β n) / n) atTop (𝓝 0)) :
    AdequateTests N (displayedTreeDist N θ) o.testCo α β
      (fun s _ ω => starPValue o.starTest (conventionCount ω) s.taxa)
      (fun s _ ω => t1PValue (conventionCount ω) s) := by
  have hd : IsDist (displayedTreeDist N θ) := displayedTreeDist_isDist hN hθ
  have h₁ := assumption1Forward_displayed hN hθ.isNormalized (θ := θ)
  have hsum : ∀ s : QuartetTree X, ∑ r ∈ treesOn s.taxa, displayedCF N θ r = 1 :=
    fun s => sum_expectedCF hd s.card_taxa
  have hno : ¬ (o.testCo = .cauchy ∨ o.testCo = .cbc) := by
    rcases hm with hm | hm <;> simp [hm]
  have hone : ∀ {Ev : (n : ℕ) → (Fin n → UnrootedGeneTree X) → Prop},
      (∀ n ω, (∀ i, displayedTreeDist N θ (ω i) ≠ 0) → Ev n ω) → ∀ ε : ℝ, 0 < ε →
      ∀ᶠ n : ℕ in atTop, 1 - ε < iidProb (displayedTreeDist N θ) n (Ev n) := by
    intro Ev h ε hε
    refine Eventually.of_forall fun n => ?_
    have := iidProb_mono hd (h n)
    rw [iidProb_forall_ne_zero hd n] at this
    linarith
  refine ⟨fun s n ω => starPValue_mem' _ (conventionCount_nonneg ω) s.card_taxa,
    fun s n ω => ⟨(t1PValue_pos _ _).le, Trinomial.t1Tail_le_one _ _⟩,
    fun ε hε => ⟨1 / 4, by norm_num, by norm_num, ?_⟩, fun s hs c hc => ?_,
    fun ε hε => ⟨1 / 4, by norm_num, by norm_num, ?_⟩, fun s hs c hc => ?_⟩
  · refine hone (fun n ω hω s hs => ⟨?_, fun h => absurd h hno⟩) ε hε
    rw [(pValues_of_hasTrivialFourBlob (θ := θ) hN s.card_taxa hs hω _).1]
    norm_num
  · refine tendsto_lt_level_of_growth hβpos hβ (fun b hb => ?_) hc
    exact starPValue_growth o.starTest hd s.card_taxa
      (fun hu => hs ((uniform_iff h₁ h₂ s).1 hu)) hb
  · refine hone (fun n ω hω s hs => ⟨?_, fun h => absurd h hno⟩) ε hε
    rw [t1PValue_of_isNullQuartet hN hs hω]
    norm_num
  · refine tendsto_lt_level_of_growth hαpos hα (fun b hb => ?_) hc
    exact t1PValue_growth hd (fun hn => hs ((t1Null_iff h₁ h₂ hsum s).1 hn)) hb

variable (N θ) in
/-- **Bon and BBC on the displayed tree model, on an arbitrary tree `T₀`**: the output tends to the limit tree. -/
theorem tendsto_ectoblob_displayed_limitTree (hN : N.IsPhylogenetic) (hθ : N.IsWeakMetric θ)
    (h₂ : Assumption1Converse N (displayedCF N θ)) (T₀ : Finset (Finset X)) (hT₀ : IsUnrootedTree T₀)
    (o : ECToBlobOptions) (hm : o.testCo = .bon ∨ o.testCo = .bbc) {α β : ℕ → ℝ}
    (hα₀ : Tendsto α atTop (𝓝[>] 0)) (hβ₀ : Tendsto β atTop (𝓝[>] 0))
    (hα : Tendsto (fun n : ℕ => Real.log (α n) / n) atTop (𝓝 0))
    (hβ : Tendsto (fun n : ℕ => Real.log (β n) / n) atTop (𝓝 0)) :
    Tendsto (fun n => iidProb (displayedTreeDist N θ) n fun ω =>
      ectoblob o (α n) (β n) (conventionCount ω) T₀ = limitTree N T₀) atTop (𝓝 1) :=
  tendsto_ectoblobBy_limitTree hN (displayedTreeDist_isDist hN hθ) hα₀ hβ₀
    (adequateTests_displayed N θ hN hθ h₂ o hm (hα₀.eventually self_mem_nhdsWithin)
      (hβ₀.eventually self_mem_nhdsWithin) hα hβ) hT₀ rfl

variable (N θ) in
/-- **Bon and BBC on the displayed tree model, at any levels with `o(n)` cutoffs.** -/
theorem consistency_ectoblob_displayed (hN : N.IsPhylogenetic) (hθ : N.IsWeakMetric θ)
    (h₂ : Assumption1Converse N (displayedCF N θ)) (T₀ : Finset (Finset X))
    (hT₀ : IsResolutionOf T₀ (treeOfBlobs N)) (o : ECToBlobOptions)
    (hm : o.testCo = .bon ∨ o.testCo = .bbc) {α β : ℕ → ℝ}
    (hα₀ : Tendsto α atTop (𝓝[>] 0)) (hβ₀ : Tendsto β atTop (𝓝[>] 0))
    (hα : Tendsto (fun n : ℕ => Real.log (α n) / n) atTop (𝓝 0))
    (hβ : Tendsto (fun n : ℕ => Real.log (β n) / n) atTop (𝓝 0)) :
    Tendsto (fun n => iidProb (displayedTreeDist N θ) n fun ω =>
      ectoblob o (α n) (β n) (conventionCount ω) T₀ = treeOfBlobs N) atTop (𝓝 1) := by
  rw [← limitTree_eq_treeOfBlobs hN hT₀]
  exact tendsto_ectoblob_displayed_limitTree N θ hN hθ h₂ T₀ hT₀.1 o hm hα₀ hβ₀ hα hβ

end Displayed

universe u

/-- **Theorem 8.2** (`ecto:thm8_2_displayed`) **for the displayed tree model on any network, for Bon and BBC.** There are sequences
`α_n`, `β_n`, independent of the network, such that for every network, possibly non-binary, every resolution `T₀` of the
tree of blobs, and every variant of the algorithm with Bon or BBC, the output on the counts of `n` displayed trees, with the
convention of lines 289-293 at a star, is the tree of blobs with probability tending to one. The converse of Assumption 1
is a hypothesis at the parameters, as in `ECToBlob.theorem8_2` (E10 of the report); its forward direction holds at all
parameters (`assumption1Forward_displayed`).

The proof is the paper's, with the sequences of the paper's proof, except at the point where it fails.
Departure from the paper: line 1065, "each individual p-value is uniformly distributed", is false for this model
(`ECToBlob.not_asymptoticallyUniform_starPValue`), so Lemma 8.1 does not apply. Here each p-value under the null is `1` on
every sample of positive probability, which gives the lower bound that these two methods use. -/
theorem theorem8_2_displayed : ∃ α β : ℕ → ℝ, Tendsto α atTop (𝓝 0) ∧ Tendsto β atTop (𝓝 0) ∧
    (∀ᶠ n in atTop, 0 < α n ∧ α n < 1) ∧ (∀ᶠ n in atTop, 0 < β n ∧ β n < 1) ∧
    ∀ {V E X : Type u} [Fintype V] [Fintype E] [Fintype X] [DecidableEq X] [Nonempty X]
      (N : RootedNetwork V E X) (_ : N.IsPhylogenetic) (θ : MetricData E) (_ : N.IsWeakMetric θ)
      (_ : Assumption1Converse N (displayedCF N θ))
      (T₀ : Finset (Finset X)) (_ : IsResolutionOf T₀ (treeOfBlobs N))
      (o : ECToBlobOptions) (_ : o.testCo = .bon ∨ o.testCo = .bbc),
      Tendsto (fun n => iidProb (displayedTreeDist N θ) n fun ω =>
        ectoblob o (α n) (β n) (conventionCount ω) T₀ = treeOfBlobs N) atTop (𝓝 1) :=
  ⟨alphaSeq, betaSeq, tendsto_alphaSeq, tendsto_betaSeq,
    (tendsto_alphaSeq.eventually (gt_mem_nhds zero_lt_one)).mono fun _ hn =>
      ⟨chiSqOneTail_pos _, hn⟩,
    (tendsto_betaSeq.eventually (gt_mem_nhds zero_lt_one)).mono fun _ hn =>
      ⟨Real.exp_pos _, hn⟩,
    fun N hN θ hθ h₂ T₀ hT₀ o hm => consistency_ectoblob_displayed N θ hN hθ h₂ T₀ hT₀ o hm
      tendsto_alphaSeq_nhdsGT tendsto_betaSeq_nhdsGT tendsto_log_chiSqOneTail_log
      tendsto_log_betaSeq⟩

/-! ### Cauchy and CBC: the T1 tests do nothing -/

section Sequence

variable {X : Type*} [Fintype X] [DecidableEq X]

/-- The Cauchy combinations of positive p-values with a `1` are `1` (E11 of the report). -/
theorem combineP_eq_one {m : TestCorrection} (hm : m = .cauchy ∨ m = .cbc) {P : Multiset ℝ}
    (h1 : (1 : ℝ) ∈ P) (h : ∀ p ∈ P, 0 < p ∧ p ≤ 1) : combineP m P = 1 := by
  rcases hm with rfl | rfl
  · have hP : P ≠ 0 := fun h' => by simp [h'] at h1
    have h0 : (0 : ℝ) ∉ P := fun h0 => lt_irrefl _ (h 0 h0).1
    unfold combineP
    rw [ite_eq_right hP]
    show cauchyP P = 1
    rw [cauchyP, ite_eq_right h0, ite_eq_left h1]
  · exact Remarks.combineP_cbc_eq_one h1 h

variable {α : ℝ} {edgeP : Finset (Finset X) → Finset X → ℝ} {treeP : Finset (Finset X) → ℝ}
  {T₁ : Finset (Finset X)} {A : Finset X}

/-- If the edge with sides `A`, `Aᶜ` has the largest p-value, `1`, as long as it is there, then the sequence of trees keeps
it until no internal edge is left. -/
theorem mem_seqBy_or (hA : A ∈ T₁) (hAc : Aᶜ ∈ T₁)
    (he : ∀ T ⊆ T₁, A ∈ T → Aᶜ ∈ T → edgeP T A = 1 ∧ edgeP T Aᶜ = 1)
    (hle : ∀ T ⊆ T₁, ∀ B ∈ internalSides T, edgeP T B ≤ 1) (i : ℕ) :
    (A ∈ seqBy edgeP T₁ i ∧ Aᶜ ∈ seqBy edgeP T₁ i) ∨ internalSides (seqBy edgeP T₁ i) = ∅ := by
  induction i with
  | zero => exact Or.inl ⟨hA, hAc⟩
  | succ i ih =>
    rw [seqBy_succ]
    set T := seqBy edgeP T₁ i with hT
    have hTsub : T ⊆ T₁ := seqBy_subset i
    rcases ih with ⟨h₁, h₂⟩ | hemp
    · obtain ⟨he₁, he₂⟩ := he T hTsub h₁ h₂
      set C := (internalSides T).filter fun B => ∀ B' ∈ internalSides T, edgeP T B ≤ edgeP T B' with hC
      by_cases hin : A ∈ C ∨ Aᶜ ∈ C
      · -- all sides have the value `1`, and they all go
        right
        have hall : ∀ B ∈ internalSides T, edgeP T B = 1 := by
          intro B hB
          refine le_antisymm (hle T hTsub B hB) ?_
          rcases hin with hin | hin
          · have := (mem_filter.1 hin).2 B hB
            rwa [he₁] at this
          · have := (mem_filter.1 hin).2 B hB
            rwa [he₂] at this
        have hsub : internalSides T ⊆ C := fun B hB =>
          mem_filter.2 ⟨hB, fun B' hB' => by rw [hall B hB, hall B' hB']⟩
        refine Finset.eq_empty_of_forall_notMem fun B hB => ?_
        obtain ⟨hBT, hB₂⟩ := mem_internalSides.1 hB
        obtain ⟨hBT', hBC, _⟩ := mem_contractSides.1 hBT
        exact hBC (hsub (mem_internalSides.2 ⟨hBT', hB₂⟩))
      · push Not at hin
        left
        exact ⟨mem_contractSides.2 ⟨h₁, hin.1, hin.2⟩,
          mem_contractSides.2 ⟨h₂, hin.2, by rw [compl_compl]; exact hin.1⟩⟩
    · right
      refine Finset.eq_empty_of_forall_notMem fun B hB => ?_
      obtain ⟨hBT, hB₂⟩ := mem_internalSides.1 hB
      have : B ∈ internalSides T := mem_internalSides.2 ⟨contractBy_subset T hBT, hB₂⟩
      rw [hemp] at this
      simp at this

/-- If every tree of the sequence has overall p-value at least the level, then both selection rules select the first tree. -/
theorem outputBy_eq_self_of_forall_le (rule : SelectionRule)
    (hle : ∀ i, α ≤ treeP (seqBy edgeP T₁ i)) : outputBy rule α edgeP treeP T₁ = T₁ := by
  have hsel : selectedBy rule α edgeP treeP T₁ = 0 := by
    cases rule with
    | early =>
      simp only [selectedBy]
      exact Nat.sInf_eq_zero.2 (Or.inl ⟨Nat.zero_le _, hle 0⟩)
    | late =>
      simp only [selectedBy]
      refine ite_eq_right ?_
      rintro ⟨i, -, hi⟩
      exact absurd hi (not_lt_of_ge (hle i))
  rw [outputBy, hsel]
  rfl

/-- **With a `1` on all the quartets of an edge, Cauchy and CBC return the tree after Step 3.** If `f` is a table of positive
p-values with the value `1` on all the quartets of the bipartition of an internal edge that Step 3 keeps, then both selection
rules return the tree after Step 3, for all the quartet types and at every level `α ≤ 1`. -/
theorem ectoblobBy_eq_afterStarBy {o : ECToBlobOptions} (hm : o.testCo = .cauchy ∨ o.testCo = .cbc)
    {α β : ℝ} (hα : α ≤ 1) {g f : QuartetTree X → ℝ} (hf : ∀ s, 0 < f s ∧ f s ≤ 1)
    {T₀ : Finset (Finset X)} (hT₀ : IsUnrootedTree T₀) {A : Finset X} (hint : 2 ≤ A.card ∧ 2 ≤ Aᶜ.card)
    (hA : A ∈ afterStarBy o β g T₀) (hone : ∀ s ∈ bipartitionQuartets A, f s = 1) :
    ectoblobBy o α β g f T₀ = afterStarBy o β g T₀ := by
  set T₁ := afterStarBy o β g T₀ with hT₁
  have hsub : T₁ ⊆ T₀ := afterStarBy_subset
  have hAc : Aᶜ ∈ T₁ := by
    obtain ⟨h₁, h₂, h₃⟩ := mem_contractSides.1 hA
    exact mem_contractSides.2 ⟨IsUnrootedTree.compl_mem hT₀ h₁, h₃, by rwa [compl_compl]⟩
  have hsplit : IsSplitFamily T₀ := isSplitFamily_of_internal hT₀ hint.1
  obtain ⟨s₀, hs₀⟩ := FalseEdge.exists_mem_multipartitionQuartets hsplit hint.1 hint.2
  have hs₀' : A ∩ s₀.taxa ∈ s₀.val := (mem_filter.1 (mem_filter.1 hs₀).1).2
  have hmem : ∀ {Q : Finset (QuartetTree X)}, ∀ x ∈ Q.val.map f, 0 < x ∧ x ≤ 1 := by
    intro Q x hx
    obtain ⟨s, _, rfl⟩ := Multiset.mem_map.1 hx
    exact hf s
  have hedge₁ : ∀ T ⊆ T₁, edgeTestP o f T₀ T A = 1 := by
    intro T hT
    refine combineP_eq_one hm ?_ hmem
    refine Multiset.mem_map.2 ⟨s₀, multipartitionQuartets_subset_edgeQuartets (hT.trans hsub) A hs₀, ?_⟩
    exact hone s₀ (mem_filter.2 ⟨mem_univ _, hs₀'⟩)
  have hedge₂ : ∀ T ⊆ T₁, edgeTestP o f T₀ T Aᶜ = 1 := by
    intro T hT
    refine combineP_eq_one hm ?_ hmem
    have hs₁ : s₀ ∈ multipartitionQuartets T₀ Aᶜ := by rwa [multipartitionQuartets_compl]
    refine Multiset.mem_map.2 ⟨s₀, multipartitionQuartets_subset_edgeQuartets (hT.trans hsub) Aᶜ hs₁, ?_⟩
    exact hone s₀ (mem_filter.2 ⟨mem_univ _, hs₀'⟩)
  have hedge_le : ∀ T ⊆ T₁, ∀ B ∈ internalSides T, edgeTestP o f T₀ T B ≤ 1 := fun T _ B _ =>
    (Remarks.combineP_mem _ fun x hx => ⟨(hmem x hx).1.le, (hmem x hx).2⟩).2
  have htree : ∀ T ⊆ T₁, A ∈ T → α ≤ treeTestP o f T := by
    intro T _ hAT
    have : treeTestP o f T = 1 := by
      refine combineP_eq_one hm ?_ hmem
      refine Multiset.mem_map.2 ⟨s₀, mem_filter.2 ⟨mem_univ _, A, hAT, hs₀'⟩, ?_⟩
      exact hone s₀ (mem_filter.2 ⟨mem_univ _, hs₀'⟩)
    rw [this]
    exact hα
  have hstar : ∀ T : Finset (Finset X), internalSides T = ∅ → α ≤ treeTestP o f T := by
    intro T hT
    have hemp : (univ.filter fun s => Displays T s) = ∅ := by
      refine Finset.eq_empty_of_forall_notMem fun s hs => ?_
      obtain ⟨B, hB, hBs⟩ := (mem_filter.1 hs).2
      have : B ∈ internalSides T := mem_internalSides.2 ⟨hB, two_le_card_of_inter_taxa_mem hBs⟩
      rw [hT] at this
      simp at this
    unfold treeTestP combineP
    rw [hemp]
    simpa using hα
  refine outputBy_eq_self_of_forall_le o.rule fun i => ?_
  rcases mem_seqBy_or (edgeP := edgeTestP o f T₀) hA hAc
      (fun T hT _ _ => ⟨hedge₁ T hT, hedge₂ T hT⟩) hedge_le i with h | h
  · exact htree _ (seqBy_subset i) h.1
  · exact hstar _ h

end Sequence

section DisplayedCauchy

variable {V E X : Type*} [Fintype V] [Fintype E] [Fintype X] [DecidableEq X] [Nonempty X]
  {N : RootedNetwork V E X} {θ : MetricData E}

omit [Nonempty X] in
/-- (`ecto:displayed_cauchy_afterstar`) **Under the displayed tree model, Cauchy and CBC return the tree after Step 3.** If an internal edge of the tree of blobs
survives Step 3, then on every sample of positive probability the T1 tests contract nothing that the output sees: the output
is the tree after Step 3, at every level `α ≤ 1`. -/
theorem ectoblob_eq_afterStar (hN : N.IsPhylogenetic) {o : ECToBlobOptions}
    (hm : o.testCo = .cauchy ∨ o.testCo = .cbc) {α β : ℝ} (hα : α ≤ 1) {T₀ : Finset (Finset X)}
    (hT₀ : IsUnrootedTree T₀) {A : Finset X} (hAB : A ∈ treeOfBlobs N)
    (hint : 2 ≤ A.card ∧ 2 ≤ Aᶜ.card) {n : ℕ} {ω : Fin n → UnrootedGeneTree X}
    (hω : ∀ i, displayedTreeDist N θ (ω i) ≠ 0)
    (hA : A ∈ afterStar o β (conventionCount ω) T₀) :
    ectoblob o α β (conventionCount ω) T₀ = afterStar o β (conventionCount ω) T₀ :=
  ectoblobBy_eq_afterStarBy hm hα (fun _ => ⟨t1PValue_pos _ _, Trinomial.t1Tail_le_one _ _⟩) hT₀ hint hA
    fun _ hs => t1PValue_of_inducedCutSplit hN (inducedCutSplit_of_mem hN hAB (mem_filter.1 hs).2) hω

omit [Fintype V] [Fintype E] [Nonempty X] in
/-- At an edge of `T₀` none of whose quartets is uniform, the star test rejects with probability tending to one, whichever
the combination method: the p-values are all small. -/
theorem eventually_edgeStarP_lt {dist : UnrootedGeneTree X → ℝ} (hd : IsDist dist) (o : ECToBlobOptions)
    {T₀ : Finset (Finset X)} (hT₀ : IsUnrootedTree T₀) {B : Finset X} (hB : 2 ≤ B.card ∧ 2 ≤ Bᶜ.card)
    (hnu : ∀ s ∈ multipartitionQuartets T₀ B, ¬ IsUniformOn (expectedCF dist) s.taxa)
    {β : ℕ → ℝ} (hβ₀ : Tendsto β atTop (𝓝[>] 0))
    (hβ : Tendsto (fun n : ℕ => Real.log (β n) / n) atTop (𝓝 0)) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, 1 - ε < iidProb dist n fun ω =>
      edgeStarP o (conventionCount ω) T₀ B < β n := by
  obtain ⟨s₀, hs₀⟩ := FalseEdge.exists_mem_multipartitionQuartets
    (isSplitFamily_of_internal hT₀ hB.1) hB.1 hB.2
  have h := eventually_testCorrect_of_level hd o.testCo hβ₀ (multipartitionQuartets T₀ B) le_rfl
    (fun s => IsUniformOn (expectedCF dist) s.taxa)
    (fun s _ ω => starPValue o.starTest (conventionCount ω) s.taxa)
    (fun s _ ω => starPValue_mem' _ (conventionCount_nonneg ω) s.card_taxa)
    (fun ε' hε' => ⟨1 / 4, by norm_num, by norm_num, Eventually.of_forall fun n => by
      have hle := iidProb_mono hd (n := n) (Ev := fun _ => True)
        (Ev' := fun ω : Fin n → UnrootedGeneTree X => ∀ s ∈ multipartitionQuartets T₀ B,
          IsUniformOn (expectedCF dist) s.taxa →
            1 / 4 ≤ starPValue o.starTest (conventionCount ω) s.taxa ∧
              ((o.testCo = .cauchy ∨ o.testCo = .cbc) →
                starPValue o.starTest (conventionCount ω) s.taxa ≤ 1 - 1 / 4))
        (fun ω _ s hs hu => absurd hu (hnu s hs))
      rw [iidProb_true hd] at hle
      linarith⟩)
    (fun s _ hs c hc => tendsto_lt_level_of_growth (hβ₀.eventually self_mem_nhdsWithin) hβ
      (fun b hb => starPValue_growth o.starTest hd s.card_taxa hs hb) hc) hε
  filter_upwards [h] with n hn
  exact hn.trans_le (iidProb_mono hd fun ω hω => hω.2 ⟨s₀, hs₀, hnu s₀ hs₀⟩)

/-- (`ecto:displayed_cauchy_false_edge`) **Cauchy and CBC on the displayed tree model: a false edge that Step 3 keeps stays.** Let `T₀` be a tree with an internal
edge `A` of the tree of blobs and an internal edge `F` off it, none of whose quartets has uniform concordance factors. Then
for Cauchy and CBC, at any levels `α_n ≤ 1` and `β_n → 0` with `o(n)` cutoffs, with probability tending to one the output is
the tree after Step 3 and it keeps `F`, so it is the tree of blobs with probability tending to zero. -/
theorem tendsto_ectoblob_displayed_zero (hN : N.IsPhylogenetic) (hθ : N.IsWeakMetric θ)
    {T₀ : Finset (Finset X)} (hT₀ : IsUnrootedTree T₀) {A F : Finset X} (hA : A ∈ T₀) (hF : F ∈ T₀)
    (hAB : A ∈ treeOfBlobs N) (hFB : F ∉ treeOfBlobs N) (hAint : 2 ≤ A.card ∧ 2 ≤ Aᶜ.card)
    (hFint : 2 ≤ F.card ∧ 2 ≤ Fᶜ.card)
    (hnu : ∀ s ∈ multipartitionQuartets T₀ F, ¬ IsUniformOn (displayedCF N θ) s.taxa)
    {o : ECToBlobOptions} (hm : o.testCo = .cauchy ∨ o.testCo = .cbc) {α β : ℕ → ℝ}
    (hα : ∀ᶠ n in atTop, α n ≤ 1) (hβ₀ : Tendsto β atTop (𝓝[>] 0))
    (hβ : Tendsto (fun n : ℕ => Real.log (β n) / n) atTop (𝓝 0)) :
    Tendsto (fun n => iidProb (displayedTreeDist N θ) n fun ω =>
      ectoblob o (α n) (β n) (conventionCount ω) T₀ = treeOfBlobs N) atTop (𝓝 0) := by
  have hd : IsDist (displayedTreeDist N θ) := displayedTreeDist_isDist hN hθ
  have h₁ := assumption1Forward_displayed hN hθ.isNormalized (θ := θ)
  have hnuA : ∀ s ∈ multipartitionQuartets T₀ A, ¬ IsUniformOn (displayedCF N θ) s.taxa := by
    intro s hs
    have hs' : A ∩ s.taxa ∈ s.val := (mem_filter.1 (mem_filter.1 hs).1).2
    exact not_uniform_of_strict (h₁.t1 s (inducedCutSplit_of_mem hN hAB hs'))
  have hmemStar : ∀ {c : QuartetTree X → ℝ} {τ : ℝ} {B : Finset X}, B ∈ T₀ →
      edgeStarP o c T₀ B < τ → B ∈ afterStar o τ c T₀ := by
    intro c τ B hB hlt
    have hlt' : edgeStarP o c T₀ Bᶜ < τ := by
      unfold edgeStarP at hlt ⊢
      rwa [multipartitionQuartets_compl]
    refine mem_contractSides.2 ⟨hB, fun h => ?_, fun h => ?_⟩
    · exact absurd (mem_filter.1 h).2 (not_lt_of_gt hlt)
    · exact absurd (mem_filter.1 h).2 (not_lt_of_gt hlt')
  refine tendsto_order.2 ⟨fun a ha => ?_, fun a ha => ?_⟩
  · exact Eventually.of_forall fun n => ha.trans_le (iidProb_nonneg hd n _)
  · have hε : 0 < a / 2 := half_pos ha
    filter_upwards [eventually_edgeStarP_lt hd o hT₀ hAint hnuA hβ₀ hβ hε,
      eventually_edgeStarP_lt hd o hT₀ hFint hnu hβ₀ hβ hε, hα] with n h₁' h₂' hαn
    have hand := iidProb_and_gt hd n _ _ h₁' h₂'
    have hforall := iidProb_forall_ne_zero hd n
    have hsub : (iidProb (displayedTreeDist N θ) n fun ω =>
        (edgeStarP o (conventionCount ω) T₀ A < β n ∧ edgeStarP o (conventionCount ω) T₀ F < β n) ∧
          ∀ i, displayedTreeDist N θ (ω i) ≠ 0) ≤
        iidProb (displayedTreeDist N θ) n fun ω =>
          ¬ ectoblob o (α n) (β n) (conventionCount ω) T₀ = treeOfBlobs N := by
      refine iidProb_mono hd fun ω hω heq => ?_
      obtain ⟨⟨h₃, h₄⟩, hpos⟩ := hω
      have hmA := hmemStar hA h₃
      have hmF := hmemStar hF h₄
      rw [ectoblob_eq_afterStar hN hm hαn hT₀ hAB hAint hpos hmA] at heq
      exact hFB (heq ▸ hmF)
    rw [iidProb_not hd] at hsub
    have hand₂ := iidProb_and_ge' hd n
      (fun ω => edgeStarP o (conventionCount ω) T₀ A < β n ∧ edgeStarP o (conventionCount ω) T₀ F < β n)
      (fun ω => ∀ i, displayedTreeDist N θ (ω i) ≠ 0)
    rw [hforall] at hand₂
    linarith

/-- **Cauchy and CBC on the displayed tree model, on a tree `T₀` none of whose edges has a uniform quartet.** With an internal
edge of the tree of blobs in `T₀`, the output is `T₀` with probability tending to one. -/
theorem tendsto_ectoblob_displayed_self (hN : N.IsPhylogenetic) (hθ : N.IsWeakMetric θ)
    {T₀ : Finset (Finset X)} (hT₀ : IsUnrootedTree T₀) {A : Finset X} (hA : A ∈ T₀)
    (hAB : A ∈ treeOfBlobs N) (hAint : 2 ≤ A.card ∧ 2 ≤ Aᶜ.card)
    (hnu : ∀ B ∈ internalSides T₀, ∀ s ∈ multipartitionQuartets T₀ B,
      ¬ IsUniformOn (displayedCF N θ) s.taxa)
    {o : ECToBlobOptions} (hm : o.testCo = .cauchy ∨ o.testCo = .cbc) {α β : ℕ → ℝ}
    (hα : ∀ᶠ n in atTop, α n ≤ 1) (hβ₀ : Tendsto β atTop (𝓝[>] 0))
    (hβ : Tendsto (fun n : ℕ => Real.log (β n) / n) atTop (𝓝 0)) :
    Tendsto (fun n => iidProb (displayedTreeDist N θ) n fun ω =>
      ectoblob o (α n) (β n) (conventionCount ω) T₀ = T₀) atTop (𝓝 1) := by
  have hd : IsDist (displayedTreeDist N θ) := displayedTreeDist_isDist hN hθ
  refine tendsto_order.2 ⟨fun a ha => ?_, fun a ha => ?_⟩
  swap
  · exact Eventually.of_forall fun n => (iidProb_le_one hd n _).trans_lt ha
  have hε : 0 < 1 - a := by linarith
  have hall := eventually_forall_mem hd (internalSides T₀)
    (fun B n ω => edgeStarP o (conventionCount ω) T₀ B < β n) hε
    fun B hB ε' hε' => eventually_edgeStarP_lt hd o hT₀ (mem_internalSides.1 hB).2 (hnu B hB) hβ₀ hβ hε'
  filter_upwards [hall, hα] with n hn hαn
  have hforall := iidProb_forall_ne_zero hd n
  have hand := iidProb_and_ge' hd n (fun ω => ∀ B ∈ internalSides T₀,
    edgeStarP o (conventionCount ω) T₀ B < β n) (fun ω => ∀ i, displayedTreeDist N θ (ω i) ≠ 0)
  rw [hforall] at hand
  refine (by linarith : a < _).trans_le (iidProb_mono hd fun ω hω => ?_)
  obtain ⟨hstar, hpos⟩ := hω
  have hafter : afterStar o (β n) (conventionCount ω) T₀ = T₀ := by
    refine Finset.filter_true_of_mem fun B _ => ⟨fun hB => ?_, fun hB => ?_⟩
    · exact absurd (mem_filter.1 hB).2 (not_lt_of_gt (hstar B (mem_filter.1 hB).1))
    · exact absurd (mem_filter.1 hB).2 (not_lt_of_gt (hstar _ (mem_filter.1 hB).1))
  rw [ectoblob_eq_afterStar hN hm hαn hT₀ hAB hAint hpos (by rw [hafter]; exact hA), hafter]

end DisplayedCauchy

end ECToBlob.DisplayedTree
