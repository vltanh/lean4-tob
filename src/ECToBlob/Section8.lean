module

public import Basic.Defs
public import Basic.Testing.Combining
public import Basic.Testing.Limits
public import ECToBlob.Section4
public import ECToBlob.Section5
public import ECToBlob.Lemma81
public import ECToBlob.Section6
public import ECToBlob.Deterministic

/-!
# ECToBlob §8: statistical consistency

Theorem 8.2. Lemma 8.1 is in `src/ECToBlob/Lemma81.lean`, the end of the proof, once all tests come out
right, in `src/ECToBlob/Deterministic.lean`, and the repair of the choice of a quartet at a false edge
in `src/ECToBlob/FalseEdge.lean`.

The proof follows the paper (the paper's text, lines 1047-1158), test by test:

* one combined test (lines 1064-1116): `eventually_lt_combineP` if the null holds on all of its
  quartets, `eventually_combineP_lt` if not, and `eventually_testCorrect` for both;
* the star test at an edge of `T₀`: `exists_delta_star` (Lemma 8.1), `eventually_star_correct`;
* the T1 test at a set of quartets (lines 1123-1132): `exists_delta_t1` (Lemma 8.1, and the two
  cases of the T1 null that it does not cover), `eventually_t1_correct`;
* the union over the tests (lines 1062-1063, 1117-1121, 1127-1128, 1151-1155):
  `eventually_forall_mem`, `eventually_sub_lt_iidProb`.

Theorem 8.2 is stated for a network at numerical parameters where both directions of Assumption 1
hold (E10 of the report: as printed, for all parameters, it fails). The correction was agreed with
the person who asked for this formalization. `theorem8_2_generic` gives the conclusion for almost all parameters, from `Assumption1`.

For the corrections `cauchy` and `cbc`, Theorem 8.2 also requires the alternatives of a quartet tree
satisfying (5.2) to have positive probability: without this a p-value is exactly `1`, and the Cauchy
combination is `1` whatever the other p-values (E11 of the report).
-/

@[expose] public noncomputable section

open Phylogenetics Phylogenetics.RootedNetwork Phylogenetics.QuartetTests Finset Filter Topology
open scoped Classical

namespace ECToBlob

universe u

variable {V E X : Type*} [Fintype X] [DecidableEq X]

/-! ### Binary gene trees -/

/-- A binary gene tree displays exactly one quartet tree on each set of four taxa. -/
theorem displaysOne_binaryGeneTree (dist : BinaryGeneTree X → ℝ) :
    DisplaysOne dist (Subtype.val : BinaryGeneTree X → Finset (Finset X)) := by
  intro g _ q hq
  obtain ⟨s, hs, hds⟩ := g.2.exists_displays hq
  obtain ⟨H, hH, hu, _⟩ := g.2
  have hT : IsUnrootedTree g.1 := ⟨H, hH, hu⟩
  refine ⟨s, ⟨hs, hds⟩, fun r hr => ?_⟩
  exact hT.displays_unique hr.2 hds ((mem_filter.1 hr.1).2.trans (mem_filter.1 hs).2.symm)

/-- The concordance factors on a set of four taxa sum to one, since gene trees are binary. -/
theorem sum_displayCF_binaryGeneTree {dist : BinaryGeneTree X → ℝ} (hd : IsDist dist)
    {q : Finset X} (hq : q.card = 4) : ∑ r ∈ treesOn q, displayCF dist Subtype.val r = 1 := by
  unfold displayCF
  rw [Finset.sum_comm, ← hd.2]
  refine Finset.sum_congr rfl fun g _ => ?_
  obtain ⟨s, ⟨hs, hds⟩, huniq⟩ := displaysOne_binaryGeneTree (fun _ => (1 : ℝ)) g one_ne_zero q hq
  rw [Finset.sum_eq_single_of_mem s hs]
  · simp [hds]
  · intro r hr hrs
    exact ite_eq_right fun hdr => hrs (huniq r ⟨hr, hdr⟩)

/-! ### The p-values are in `[0, 1]` -/

/-- Gibbs' inequality for the star statistic. -/
private theorem starStat_nonneg' (c : QuartetTree X → ℝ) (hc : ∀ r, 0 ≤ c r) {q : Finset X}
    (hq : q.card = 4) : 0 ≤ starStat c q := by
  unfold starStat
  have hcard : (treesOn q).card = 3 := card_treesOn hq
  set m := ∑ r ∈ treesOn q, c r with hm
  have hm₀ : 0 ≤ m := Finset.sum_nonneg fun r _ => hc r
  rcases hm₀.eq_or_lt with hm₁ | hm₁
  · have hz : ∀ r ∈ treesOn q, c r = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg fun r _ => hc r).1 hm₁.symm
    rw [← hm₁, Finset.sum_eq_zero fun r hr => by rw [hz r hr, zero_mul]]
    simp
  · have ht : 0 < m / 3 := by positivity
    have hterm : ∀ r ∈ treesOn q, c r - m / 3 ≤ c r * Real.log (c r) - c r * Real.log (m / 3) := by
      intro r _
      rcases (hc r).eq_or_lt with h0 | h0
      · rw [← h0]
        simp only [zero_mul, sub_zero, zero_sub]
        linarith
      · have hlog := Real.one_sub_inv_le_log_of_pos (div_pos h0 ht)
        rw [Real.log_div h0.ne' ht.ne', inv_div] at hlog
        have := mul_le_mul_of_nonneg_left hlog h0.le
        have heq : c r * (1 - m / 3 / c r) = c r - m / 3 := by
          field_simp
        rw [heq] at this
        linarith
    have hsum := Finset.sum_le_sum hterm
    rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, Finset.sum_const, hcard, ← hm,
      ← Finset.sum_mul, ← hm, nsmul_eq_mul] at hsum
    push_cast at hsum
    have : m - 3 * (m / 3) = 0 := by ring
    linarith

private theorem pearsonStat_nonneg' (c : QuartetTree X → ℝ) (hc : ∀ r, 0 ≤ c r) (q : Finset X) :
    0 ≤ pearsonStat c q :=
  Finset.sum_nonneg fun r _ =>
    div_nonneg (sq_nonneg _) (div_nonneg (Finset.sum_nonneg fun t _ => hc t) (by norm_num))

private theorem starPValue_mem (k : StarTest) (c : QuartetTree X → ℝ) (hc : ∀ r, 0 ≤ c r)
    {q : Finset X} (hq : q.card = 4) : 0 ≤ starPValue k c q ∧ starPValue k c q ≤ 1 := by
  have key : ∀ t : ℝ, 0 ≤ t → 0 ≤ chiSqTwoTail t ∧ chiSqTwoTail t ≤ 1 := fun t ht =>
    ⟨(Real.exp_pos _).le, Real.exp_le_one_iff.2 (by linarith)⟩
  cases k with
  | lrt => exact key _ (starStat_nonneg' c hc hq)
  | pearson => exact key _ (pearsonStat_nonneg' c hc q)

theorem t1PValue_mem (c : QuartetTree X → ℝ) (s : QuartetTree X) :
    0 ≤ t1PValue c s ∧ t1PValue c s ≤ 1 :=
  ⟨MeasureTheory.measureReal_nonneg, MeasureTheory.measureReal_le_one⟩

/-! ### Probabilities of events -/

section Prob

variable {Γ : Type*} [Fintype Γ] {dist : Γ → ℝ}

private theorem iidProb_and_ge (hd : IsDist dist) (n : ℕ) (A B : (Fin n → Γ) → Prop) :
    iidProb dist n A + iidProb dist n B - 1 ≤ iidProb dist n fun ω => A ω ∧ B ω := by
  have h1 := iidProb_true hd n
  have hw : ∀ ω : Fin n → Γ, 0 ≤ ∏ i, dist (ω i) := fun ω => Finset.prod_nonneg fun i _ => hd.1 _
  unfold iidProb at h1 ⊢
  rw [← h1, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_le_sum fun ω _ => ?_
  by_cases hA : A ω <;> by_cases hB : B ω <;> simp [hA, hB, hw ω]

theorem iidProb_and_gt (hd : IsDist dist) (n : ℕ) (A B : (Fin n → Γ) → Prop) {ε : ℝ}
    (hA : 1 - ε / 2 < iidProb dist n A) (hB : 1 - ε / 2 < iidProb dist n B) :
    1 - ε < iidProb dist n fun ω => A ω ∧ B ω := by
  have := iidProb_and_ge hd n A B
  linarith

/-- The union bound. -/
private theorem iidProb_forall_ge (hd : IsDist dist) {ι : Type*} (n : ℕ)
    (E : ι → (Fin n → Γ) → Prop) {ε : ℝ} (s : Finset ι)
    (h : ∀ i ∈ s, 1 - ε ≤ iidProb dist n (E i)) :
    1 - s.card * ε ≤ iidProb dist n fun ω => ∀ i ∈ s, E i ω := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    have := iidProb_mono hd (n := n) (Ev := fun _ => True)
      (Ev' := fun ω => ∀ i ∈ (∅ : Finset ι), E i ω)
      (fun _ _ i hi => absurd hi (Finset.notMem_empty i))
    rw [iidProb_true hd n] at this
    simpa using this
  | insert a s ha ih =>
    have h₀ := h a (Finset.mem_insert_self a s)
    have h₁ := ih fun i hi => h i (Finset.mem_insert_of_mem hi)
    have h₂ := iidProb_and_ge hd n (E a) (fun ω => ∀ i ∈ s, E i ω)
    have h₃ : (iidProb dist n fun ω => E a ω ∧ ∀ i ∈ s, E i ω) ≤
        iidProb dist n fun ω => ∀ i ∈ insert a s, E i ω := by
      refine iidProb_mono hd fun ω hω i hi => ?_
      rcases Finset.mem_insert.1 hi with rfl | hi
      · exact hω.1
      · exact hω.2 i hi
    rw [Finset.card_insert_of_notMem ha]
    push_cast
    linarith

/-- The union bound with strict inequalities: `k` events, each of probability `> 1 - ε'`, with
`k ε' ≤ ε`, hold together with probability `> 1 - ε`. -/
private theorem iidProb_forall_gt (hd : IsDist dist) {ι : Type*} (n : ℕ)
    (E : ι → (Fin n → Γ) → Prop) {ε ε' : ℝ} (hε : 0 < ε) (s : Finset ι)
    (hcard : s.card * ε' ≤ ε) (h : ∀ i ∈ s, 1 - ε' < iidProb dist n (E i)) :
    1 - ε < iidProb dist n fun ω => ∀ i ∈ s, E i ω := by
  classical
  rcases s.eq_empty_or_nonempty with rfl | ⟨a, ha⟩
  · have := iidProb_mono hd (n := n) (Ev := fun _ => True)
      (Ev' := fun ω => ∀ i ∈ (∅ : Finset ι), E i ω)
      (fun _ _ i hi => absurd hi (Finset.notMem_empty i))
    rw [iidProb_true hd n] at this
    linarith
  · have h₀ := h a ha
    have h₁ := iidProb_forall_ge hd n E (ε := ε') (s.erase a)
      fun i hi => (h i (Finset.mem_of_mem_erase hi)).le
    have h₂ := iidProb_and_ge hd n (E a) (fun ω => ∀ i ∈ s.erase a, E i ω)
    have h₃ : (iidProb dist n fun ω => E a ω ∧ ∀ i ∈ s.erase a, E i ω) ≤
        iidProb dist n fun ω => ∀ i ∈ s, E i ω := by
      refine iidProb_mono hd fun ω hω i hi => ?_
      by_cases hia : i = a
      · exact hia ▸ hω.1
      · exact hω.2 i (Finset.mem_erase.2 ⟨hia, hi⟩)
    have hc : ((s.erase a).card : ℝ) + 1 = s.card := by
      exact_mod_cast Finset.card_erase_add_one ha
    rw [← hc, add_mul, one_mul] at hcard
    linarith

/-- The union bound over `K` tests: if each holds eventually with probability `> 1 - ε/K`, then
eventually they hold together with probability `> 1 - ε`. -/
theorem eventually_forall_mem (hd : IsDist dist) {ι : Type*} (s : Finset ι)
    (E : ι → (n : ℕ) → (Fin n → Γ) → Prop) {ε : ℝ} (hε : 0 < ε)
    (h : ∀ i ∈ s, ∀ ε' : ℝ, 0 < ε' → ∀ᶠ n in atTop, 1 - ε' < iidProb dist n (E i n)) :
    ∀ᶠ n in atTop, 1 - ε < iidProb dist n fun ω => ∀ i ∈ s, E i n ω := by
  have hev : ∀ᶠ n in atTop, ∀ i ∈ s, 1 - ε / s.card < iidProb dist n (E i n) := by
    rw [Filter.eventually_all_finset]
    intro i hi
    have hpos : (0 : ℝ) < s.card := by exact_mod_cast Finset.card_pos.2 ⟨i, hi⟩
    exact h i hi _ (div_pos hε hpos)
  filter_upwards [hev] with n hn
  refine iidProb_forall_gt hd n (fun i => E i n) hε s ?_ hn
  rcases s.eq_empty_or_nonempty with rfl | hne
  · simpa using hε.le
  · have hpos : (s.card : ℝ) ≠ 0 := by
      exact_mod_cast (Finset.card_pos.2 hne).ne'
    rw [mul_div_cancel₀ _ hpos]

private theorem iidProb_three (hd : IsDist dist) (n : ℕ) (A C G F : (Fin n → Γ) → Prop)
    (h : ∀ ω, A ω → C ω → G ω → F ω) {ε : ℝ} (hA : 1 - ε / 3 < iidProb dist n A)
    (hC : 1 - ε / 3 < iidProb dist n C) (hG : 1 - ε / 3 < iidProb dist n G) :
    1 - ε < iidProb dist n F := by
  have h₁ := iidProb_and_ge hd n A C
  have h₂ := iidProb_and_ge hd n (fun ω => A ω ∧ C ω) G
  have h₃ : (iidProb dist n fun ω => (A ω ∧ C ω) ∧ G ω) ≤ iidProb dist n F :=
    iidProb_mono hd fun ω hω => h ω hω.1.1 hω.1.2 hω.2
  linarith

/-- With probability one all draws have positive probability. -/
private theorem iidProb_prod_ne_zero (n : ℕ) :
    iidProb dist n (fun ω => ∏ i, dist (ω i) ≠ 0) = iidProb dist n fun _ => True := by
  unfold iidProb
  refine Finset.sum_congr rfl fun ω _ => ?_
  by_cases h : ∏ i, dist (ω i) = 0 <;> simp [h]

end Prob

/-! ### The sequences of the proof -/

theorem tendsto_alphaSeq : Tendsto alphaSeq atTop (𝓝 0) := tendsto_chiSqOneTail_log

theorem eventually_alphaSeq_pos : ∀ᶠ n in atTop, 0 < alphaSeq n := chiSqOneTail_log_pos

theorem betaSeq_eq {n : ℕ} (hn : 0 < n) : betaSeq n = 1 / Real.sqrt n :=
  chiSqTwoTail_log n hn

theorem tendsto_betaSeq : Tendsto betaSeq atTop (𝓝 0) := by
  have h : Tendsto (fun n : ℕ => 1 / Real.sqrt n) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with n hn
  exact (betaSeq_eq hn).symm

private theorem eventually_betaSeq_pos : ∀ᶠ n in atTop, 0 < betaSeq n := by
  filter_upwards [eventually_gt_atTop 0] with n hn
  rw [betaSeq_eq hn]
  have : (0 : ℝ) < n := by exact_mod_cast hn
  positivity

theorem tendsto_log_betaSeq :
    Tendsto (fun n : ℕ => Real.log (betaSeq n) / n) atTop (𝓝 0) :=
  tendsto_log_chiSqTwoTail_log

/-- The threshold `b_n` of the proof, for a threshold `η_n = c₀ a_n`: an individual p-value is below
`η_n` when the test statistic is above `b_n`, and `b_n = o(n)`. -/
private theorem tendsto_threshold {a : ℕ → ℝ} {c₀ : ℝ} (hc₀ : 0 < c₀) (ha : ∀ᶠ n in atTop, 0 < a n)
    (hlog : Tendsto (fun n : ℕ => Real.log (a n) / n) atTop (𝓝 0)) :
    Tendsto (fun n : ℕ => -2 * Real.log (c₀ * a n) / n) atTop (𝓝 0) := by
  have h₁ : Tendsto (fun n : ℕ => Real.log c₀ / (n : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have h₂ := (h₁.add hlog).const_mul (-2 : ℝ)
  simp only [add_zero, mul_zero] at h₂
  refine h₂.congr' ?_
  filter_upwards [ha] with n hn
  rw [Real.log_mul hc₀.ne' hn.ne']
  ring

private theorem exp_threshold {x : ℝ} (hx : 0 < x) : Real.exp (-(-2 * Real.log x) / 2) = x := by
  rw [show -(-2 * Real.log x) / 2 = Real.log x by ring, Real.exp_log hx]

/-! ### One combined test -/

section OneTest

variable {X : Type*} [Fintype X] [DecidableEq X] {Γ : Type*} [Fintype Γ] {dist : Γ → ℝ}

omit [Fintype X] in
/-- A test whose quartets are all under the null (lines 1064-1082). Lemma 8.1 gives `δ` and the
event that the individual p-values are at least `δ`, and at most `1 - δ` as far as Lemma 6.1 needs
it (E15). Then `τ_n < δ` eventually, and Lemma 6.1 item 2 gives that the combined p-value is above
`τ_n`. -/
private theorem eventually_lt_combineP (hd : IsDist dist) (m : TestCorrection) {τ : ℕ → ℝ}
    (hτ : Tendsto τ atTop (𝓝[>] 0)) (Q : Finset (QuartetTree X))
    (f : QuartetTree X → (n : ℕ) → (Fin n → Γ) → ℝ) (h01 : ∀ s n ω, 0 ≤ f s n ω ∧ f s n ω ≤ 1)
    {ε δ : ℝ} (hδ : 0 < δ) (hδ' : δ < 1 / 2)
    (hnull : ∀ᶠ n in atTop, 1 - ε < iidProb dist n fun ω => ∀ s ∈ Q,
      δ ≤ f s n ω ∧ ((m = .cauchy ∨ m = .cbc) → f s n ω ≤ 1 - δ)) :
    ∀ᶠ n in atTop, 1 - ε < iidProb dist n fun ω =>
      τ n < combineP m (Q.val.map fun s => f s n ω) := by
  -- the size of the family matters only for the upper bound on the combined p-value
  obtain ⟨c₀, -, hcomb⟩ := Deterministic.exists_combineBounds m 0 hδ (by linarith)
  have hτ₀ : Tendsto τ atTop (𝓝 0) := hτ.mono_right nhdsWithin_le_nhds
  filter_upwards [hnull, hτ.eventually hcomb, hτ₀.eventually_lt_const hδ] with n hn hc hlt
  refine hn.trans_le (iidProb_mono hd fun ω hω => ?_)
  exact hc.gt_map Q (fun s => f s n ω) (fun s _ => h01 s n ω)
    (fun s hs => hlt.trans_le (hω s hs).1) (fun hm s hs => (hω s hs).2 hm)

omit [Fintype X] in
/-- A test with a quartet off the null (lines 1083-1116). The quartets under the null are as above,
with probability `> 1 - ε/2`, and each quartet `s` of `S^a(e)` has a p-value below `η_n` with
probability `> 1 - ε/(2 |S^a(e)|)`, since the threshold `b_n = -2 log η_n` is `o(n)`. So the least
p-value is below `η_n` and all are at most `1 - δ`, and by Lemma 6.1 item 1 the combined p-value is
below `τ_n`.

Here `η_n = c₀ τ_n` for a small constant `c₀`, since `B(η_n, 1-δ) ∼ τ_n` would not give `< τ_n`
(E14). -/
private theorem eventually_combineP_lt (hd : IsDist dist) (m : TestCorrection) {K : ℕ} {τ : ℕ → ℝ}
    (hτ : Tendsto τ atTop (𝓝[>] 0)) (hlog : Tendsto (fun n : ℕ => Real.log (τ n) / n) atTop (𝓝 0))
    (Q : Finset (QuartetTree X)) (hK : Q.card ≤ K) (Null : QuartetTree X → Prop)
    (f : QuartetTree X → (n : ℕ) → (Fin n → Γ) → ℝ) (h01 : ∀ s n ω, 0 ≤ f s n ω ∧ f s n ω ≤ 1)
    {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ) (hδ' : δ < 1 / 2)
    (hnull : ∀ᶠ n in atTop, 1 - ε / 2 < iidProb dist n fun ω => ∀ s ∈ Q, Null s →
      δ ≤ f s n ω ∧ ((m = .cauchy ∨ m = .cbc) → f s n ω ≤ 1 - δ))
    (halt : ∀ s ∈ Q, ¬ Null s → ∀ b : ℕ → ℝ, Tendsto (fun n : ℕ => b n / n) atTop (𝓝 0) →
      Tendsto (fun n => iidProb dist n fun ω => f s n ω < Real.exp (-(b n) / 2)) atTop (𝓝 1))
    (hne : ∃ s ∈ Q, ¬ Null s) :
    ∀ᶠ n in atTop, 1 - ε < iidProb dist n fun ω =>
      combineP m (Q.val.map fun s => f s n ω) < τ n := by
  obtain ⟨c₀, hc₀, hcomb⟩ := Deterministic.exists_combineBounds m K hδ (by linarith)
  have hτ₀ : Tendsto τ atTop (𝓝 0) := hτ.mono_right nhdsWithin_le_nhds
  have hτpos : ∀ᶠ n in atTop, 0 < τ n := hτ.eventually self_mem_nhdsWithin
  have hη : ∀ᶠ n in atTop, c₀ * τ n ≤ 1 - δ := by
    have h : Tendsto (fun n => c₀ * τ n) atTop (𝓝 (c₀ * 0)) := hτ₀.const_mul c₀
    rw [mul_zero] at h
    exact (h.eventually_lt_const (show (0 : ℝ) < 1 - δ by linarith)).mono fun _ h => h.le
  -- the p-values of `S^a(e)` are below `η_n`
  have hb := tendsto_threshold hc₀ hτpos hlog
  have halts : ∀ᶠ n in atTop, 1 - ε / 2 < iidProb dist n fun ω =>
      ∀ s ∈ Q.filter fun s => ¬ Null s,
        f s n ω < Real.exp (-(-2 * Real.log (c₀ * τ n)) / 2) :=
    eventually_forall_mem hd _ (fun s n ω => f s n ω < Real.exp (-(-2 * Real.log (c₀ * τ n)) / 2))
      (half_pos hε) fun s hs ε' hε' =>
        (halt s (Finset.mem_filter.1 hs).1 (Finset.mem_filter.1 hs).2
          (fun n => -2 * Real.log (c₀ * τ n)) hb).eventually_const_lt (by linarith)
  filter_upwards [hnull, halts, hτ.eventually hcomb, hη, hτpos] with n h₁ h₂ hc hηn hpos
  refine (iidProb_and_gt hd n _ _ h₁ h₂).trans_le (iidProb_mono hd fun ω hω => ?_)
  obtain ⟨hω₁, hω₂⟩ := hω
  have hbelow : ∀ s ∈ Q, ¬ Null s → f s n ω < c₀ * τ n := fun s hs hn => by
    have := hω₂ s (Finset.mem_filter.2 ⟨hs, hn⟩)
    rwa [exp_threshold (mul_pos hc₀ hpos)] at this
  obtain ⟨s₀, hs₀, hn₀⟩ := hne
  refine hc.lt_map Q hK (fun s => f s n ω) (fun s _ => h01 s n ω) ⟨s₀, hs₀, hbelow s₀ hs₀ hn₀⟩ ?_
  intro hm s hs
  by_cases hn : Null s
  · exact (hω₁ s hs hn).2 hm
  · exact (hbelow s hs hn).le.trans hηn

/-- One combined test comes out right with probability `> 1 - ε` for large `n`, by the case split of
the paper (lines 1064 and 1083). -/
theorem eventually_testCorrect (hd : IsDist dist) (m : TestCorrection) {K : ℕ} {τ : ℕ → ℝ}
    (hτ : Tendsto τ atTop (𝓝[>] 0)) (hlog : Tendsto (fun n : ℕ => Real.log (τ n) / n) atTop (𝓝 0))
    (Q : Finset (QuartetTree X)) (hK : Q.card ≤ K) (Null : QuartetTree X → Prop)
    (f : QuartetTree X → (n : ℕ) → (Fin n → Γ) → ℝ) (h01 : ∀ s n ω, 0 ≤ f s n ω ∧ f s n ω ≤ 1)
    (hnull : ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ δ < 1 / 2 ∧ ∀ᶠ n in atTop, 1 - ε <
      iidProb dist n fun ω => ∀ s ∈ Q, Null s →
        δ ≤ f s n ω ∧ ((m = .cauchy ∨ m = .cbc) → f s n ω ≤ 1 - δ))
    (halt : ∀ s ∈ Q, ¬ Null s → ∀ b : ℕ → ℝ, Tendsto (fun n : ℕ => b n / n) atTop (𝓝 0) →
      Tendsto (fun n => iidProb dist n fun ω => f s n ω < Real.exp (-(b n) / 2)) atTop (𝓝 1))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, 1 - ε < iidProb dist n fun ω =>
      Deterministic.TestCorrect Null Q (τ n) (combineP m (Q.val.map fun s => f s n ω)) := by
  by_cases hall : ∀ s ∈ Q, Null s
  · obtain ⟨δ, h0, h1, hev⟩ := hnull ε hε
    have hev' : ∀ᶠ n in atTop, 1 - ε < iidProb dist n fun ω => ∀ s ∈ Q,
        δ ≤ f s n ω ∧ ((m = .cauchy ∨ m = .cbc) → f s n ω ≤ 1 - δ) := by
      filter_upwards [hev] with n hn
      exact hn.trans_le (iidProb_mono hd fun ω hω s hs => hω s hs (hall s hs))
    filter_upwards [eventually_lt_combineP hd m hτ Q f h01 h0 h1 hev'] with n hn
    refine hn.trans_le (iidProb_mono hd fun ω hω => ⟨fun _ => hω, ?_⟩)
    rintro ⟨s, hs, hns⟩
    exact absurd (hall s hs) hns
  · push Not at hall
    obtain ⟨δ, h0, h1, hev⟩ := hnull (ε / 2) (half_pos hε)
    filter_upwards [eventually_combineP_lt hd m hτ hlog Q hK Null f h01 hε h0 h1 hev halt hall]
      with n hn
    refine hn.trans_le (iidProb_mono hd fun ω hω => ⟨fun h => ?_, fun _ => hω⟩)
    obtain ⟨s, hs, hns⟩ := hall
    exact absurd (h s hs) hns

end OneTest

/-! ### The star test and the T1 test -/

section Events

universe w

variable {X : Type w} [Fintype X] [DecidableEq X] {dist : BinaryGeneTree X → ℝ}

/-- The star test: Lemma 8.1 for the uniform 4-taxon sets of one edge (lines 1064-1077). Since "the
null star hypothesis is met, each individual p-value is uniformly distributed as `n → ∞`". -/
private theorem exists_delta_star (hd : IsDist dist) (k : StarTest) (m : TestCorrection)
    (Q : Finset (QuartetTree X)) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ δ < 1 / 2 ∧ ∀ᶠ n : ℕ in atTop, 1 - ε < iidProb dist n fun ω =>
      ∀ s ∈ Q, IsUniformOn (displayCF dist Subtype.val) s.taxa →
        δ ≤ starPValue k (quartetCount Subtype.val ω) s.taxa ∧
          ((m = .cauchy ∨ m = .cbc) →
            starPValue k (quartetCount Subtype.val ω) s.taxa ≤ 1 - δ) := by
  let ι₀ := {s : QuartetTree X // s ∈ Q ∧ IsUniformOn (displayCF dist Subtype.val) s.taxa}
  let fam : ι₀ → (n : ℕ) → (Fin n → BinaryGeneTree X) → ℝ :=
    fun s _ ω => starPValue k (quartetCount Subtype.val ω) s.1.taxa
  have hone := displaysOne_binaryGeneTree dist
  obtain ⟨δ, h0, h1, h⟩ := lemma8_1.{w, w} (Fintype.card ι₀ + 1) (by omega) hε
  obtain ⟨M, hM⟩ := h dist fam hd (by omega)
    (fun s _ _ => starPValue_mem k _ (fun _ => Nat.cast_nonneg _) s.1.card_taxa)
    (fun s => starPValue_asymptoticallyUniform k hd hone s.1.card_taxa s.2.2)
  refine ⟨δ, h0, h1, ?_⟩
  filter_upwards [eventually_gt_atTop M] with n hn
  refine (hM n hn).trans_le (iidProb_mono hd fun ω hω s hs hu => ?_)
  exact ⟨(hω ⟨s, hs, hu⟩).1, fun _ => (hω ⟨s, hs, hu⟩).2⟩

/-- The star test at one edge is right with probability `> 1 - ε` for large `n` (lines 1058-1116):
it fails to reject if all the edge's expected CFs are `(1/3, 1/3, 1/3)`, and rejects otherwise. -/
theorem eventually_star_correct (hd : IsDist dist) (k : StarTest) (m : TestCorrection)
    {K : ℕ} (Q : Finset (QuartetTree X)) (hK : Q.card ≤ K) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, 1 - ε < iidProb dist n fun ω =>
      Deterministic.TestCorrect (fun s => IsUniformOn (displayCF dist Subtype.val) s.taxa) Q
        (betaSeq n)
        (combineP m (Q.val.map fun s => starPValue k (quartetCount Subtype.val ω) s.taxa)) :=
  eventually_testCorrect hd m
    (tendsto_nhdsWithin_iff.2 ⟨tendsto_betaSeq, eventually_betaSeq_pos⟩) tendsto_log_betaSeq Q hK
    (fun s => IsUniformOn (displayCF dist Subtype.val) s.taxa)
    (fun s _ ω => starPValue k (quartetCount Subtype.val ω) s.taxa)
    (fun s _ _ => starPValue_mem k _ (fun _ => Nat.cast_nonneg _) s.card_taxa)
    (fun _ hε' => exists_delta_star hd k m Q hε')
    (fun s _ hu _ hb => starStat_growth k hd (displaysOne_binaryGeneTree dist) s.card_taxa hu hb) hε

/-- The T1 test at the quartets of `Q` that are at the centroid, on which the paper's proof is
silent (E13): it is a boundary point of the null, at which the test is not asymptotically uniform,
so that Lemma 8.1 does not apply, and tightness takes its place. -/
private theorem exists_delta_centroid (hd : IsDist dist) (Q : Finset (QuartetTree X)) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ δ < 1 / 2 ∧ ∀ᶠ n : ℕ in atTop, 1 - ε < iidProb dist n fun ω =>
      ∀ s ∈ Q, IsUniformOn (displayCF dist Subtype.val) s.taxa →
        δ ≤ t1PValue (quartetCount Subtype.val ω) s ∧
          t1PValue (quartetCount Subtype.val ω) s ≤ 1 - δ := by
  let ιc := {s : QuartetTree X // s ∈ Q ∧ IsUniformOn (displayCF dist Subtype.val) s.taxa}
  have hone := displaysOne_binaryGeneTree dist
  have hcard : (0 : ℝ) < (Fintype.card ιc : ℝ) + 1 := by positivity
  have hε' : 0 < ε / (2 * ((Fintype.card ιc : ℝ) + 1)) := by positivity
  have hmain := fun s : ιc => t1PValue_centroid_tight hd hone s.2.2 hε'
  choose δs h0 h1 hev using hmain
  -- the least of the finitely many `δ`
  obtain ⟨d, hd0, hd1, hdle⟩ : ∃ d : ℝ, 0 < d ∧ d < 1 / 2 ∧ ∀ s : ιc, d ≤ δs s := by
    by_cases hne : Nonempty ιc
    · obtain ⟨s₀, hs₀⟩ := Finite.exists_min δs
      exact ⟨δs s₀, h0 s₀, h1 s₀, hs₀⟩
    · exact ⟨1 / 4, by norm_num, by norm_num, fun s => absurd ⟨s⟩ hne⟩
  refine ⟨d, hd0, hd1, ?_⟩
  filter_upwards [eventually_all.2 hev] with n hn
  have hu := iidProb_forall_ge hd n
    (fun (s : ιc) ω => δs s ≤ t1PValue (quartetCount Subtype.val ω) s.1 ∧
      t1PValue (quartetCount Subtype.val ω) s.1 ≤ 1 - δs s)
    (ε := ε / (2 * ((Fintype.card ιc : ℝ) + 1))) Finset.univ (fun s _ => (hn s).le)
  rw [Finset.card_univ] at hu
  have hbound : (Fintype.card ιc : ℝ) * (ε / (2 * ((Fintype.card ιc : ℝ) + 1))) ≤ ε / 2 := by
    rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  have hmono : (iidProb dist n fun ω => ∀ s ∈ (Finset.univ : Finset ιc),
        δs s ≤ t1PValue (quartetCount Subtype.val ω) s.1 ∧
          t1PValue (quartetCount Subtype.val ω) s.1 ≤ 1 - δs s) ≤
      iidProb dist n fun ω => ∀ s ∈ Q, IsUniformOn (displayCF dist Subtype.val) s.taxa →
        d ≤ t1PValue (quartetCount Subtype.val ω) s ∧
          t1PValue (quartetCount Subtype.val ω) s ≤ 1 - d := by
    refine iidProb_mono hd fun ω hω s hs hu => ?_
    have := hω ⟨s, hs, hu⟩ (Finset.mem_univ _)
    have hdle' := hdle ⟨s, hs, hu⟩
    exact ⟨hdle'.trans this.1, this.2.trans (by linarith)⟩
  linarith

/-- The T1 test: the bounds on the p-values of the quartets in `Q` under the T1 null ("the T1 tests
are handled similarly", line 1123). Lemma 8.1 applies to the quartets with (5.2) and positive
alternatives, which are asymptotically uniform. The T1 null has two other cases, which the paper's
proof overlooks: the centroid (E13), and alternatives of probability zero, where the p-value is `1`
with probability one (E11). That second case is excluded by hypothesis for `cauchy` and `cbc`, which
are the only methods using an upper bound on the p-values (E15). -/
theorem exists_delta_t1 (hd : IsDist dist) (m : TestCorrection)
    (hpos : (m = .cauchy ∨ m = .cbc) → ∀ s, IsT1Strict (displayCF dist Subtype.val) s →
      ∀ r ∈ s.alternatives, 0 < displayCF dist Subtype.val r)
    (Q : Finset (QuartetTree X)) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ δ < 1 / 2 ∧ ∀ᶠ n : ℕ in atTop, 1 - ε < iidProb dist n fun ω =>
      ∀ s ∈ Q, IsT1Null (displayCF dist Subtype.val) s →
        δ ≤ t1PValue (quartetCount Subtype.val ω) s ∧
          ((m = .cauchy ∨ m = .cbc) → t1PValue (quartetCount Subtype.val ω) s ≤ 1 - δ) := by
  have hone := displaysOne_binaryGeneTree dist
  have hnn : ∀ r, 0 ≤ displayCF dist Subtype.val r := fun r =>
    Finset.sum_nonneg fun g _ => by
      split_ifs
      · exact hd.1 g
      · exact le_rfl
  let ι₀ := {s : QuartetTree X // s ∈ Q ∧ IsT1Strict (displayCF dist Subtype.val) s ∧
    ∀ r ∈ s.alternatives, 0 < displayCF dist Subtype.val r}
  let fam : ι₀ → (n : ℕ) → (Fin n → BinaryGeneTree X) → ℝ :=
    fun s _ ω => t1PValue (quartetCount Subtype.val ω) s.1
  obtain ⟨δ₁, h0₁, h1₁, h⟩ := lemma8_1.{w, w} (Fintype.card ι₀ + 1) (by omega)
    (show 0 < ε / 3 by positivity)
  obtain ⟨M, hM⟩ := h dist fam hd (by omega) (fun s _ _ => t1PValue_mem _ _)
    (fun s => t1PValue_asymptoticallyUniform hd hone s.2.2.1.1 s.2.2.1.2 s.2.2.2)
  obtain ⟨δ₂, h0₂, _, hC⟩ := exists_delta_centroid hd Q (ε := ε / 3) (by positivity)
  have hm₁ := min_le_left δ₁ δ₂
  have hm₂ := min_le_right δ₁ δ₂
  refine ⟨min δ₁ δ₂, lt_min h0₁ h0₂, min_lt_of_left_lt h1₁, ?_⟩
  filter_upwards [eventually_gt_atTop M, hC] with n hn hnC
  refine iidProb_three hd n _ _ (fun ω => ∏ i, dist (ω i) ≠ 0) _ ?_ (hM n hn) hnC ?_
  · intro ω hu hc hprod s hs hnull
    by_cases hst : IsT1Strict (displayCF dist Subtype.val) s
    · by_cases hp : ∀ r ∈ s.alternatives, 0 < displayCF dist Subtype.val r
      · have := hu ⟨s, hs, hst, hp⟩
        exact ⟨hm₁.trans this.1, fun _ => this.2.trans (by linarith)⟩
      · have hp' := hp
        push Not at hp'
        obtain ⟨r₀, hr₀, hr₀'⟩ := hp'
        have hzero : ∀ r ∈ s.alternatives, displayCF dist Subtype.val r = 0 := fun r hr =>
          (hst.2 r hr r₀ hr₀).trans (le_antisymm hr₀' (hnn r₀))
        rw [t1PValue_degenerate hd hzero ω hprod]
        exact ⟨by linarith, fun hm => absurd (hpos hm s hst) hp⟩
    · by_cases hu' : IsUniformOn (displayCF dist Subtype.val) s.taxa
      · have := hc s hs hu'
        exact ⟨hm₂.trans this.1, fun _ => this.2.trans (by linarith)⟩
      · exact absurd hnull (Deterministic.not_t1Null
          (sum_displayCF_binaryGeneTree hd s.card_taxa) hst hu')
  · rw [iidProb_prod_ne_zero, iidProb_true hd]
    linarith

/-- The T1 test at a set `Q` of quartets is right with probability `> 1 - ε` for large `n`: "arguing
as for the star test" (line 1127). It applies to the edges of a tree `T_k`, and to the overall
p-values `p_k` ("by the same argument as before", line 1158). -/
private theorem eventually_t1_correct (hd : IsDist dist) (m : TestCorrection)
    (hpos : (m = .cauchy ∨ m = .cbc) → ∀ s, IsT1Strict (displayCF dist Subtype.val) s →
      ∀ r ∈ s.alternatives, 0 < displayCF dist Subtype.val r)
    {K : ℕ} (Q : Finset (QuartetTree X)) (hK : Q.card ≤ K) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, 1 - ε < iidProb dist n fun ω =>
      Deterministic.TestCorrect (IsT1Null (displayCF dist Subtype.val)) Q (alphaSeq n)
        (combineP m (Q.val.map fun s => t1PValue (quartetCount Subtype.val ω) s)) :=
  eventually_testCorrect hd m
    (tendsto_nhdsWithin_iff.2 ⟨tendsto_alphaSeq, eventually_alphaSeq_pos⟩)
    tendsto_log_chiSqOneTail_log Q hK (IsT1Null (displayCF dist Subtype.val))
    (fun s _ ω => t1PValue (quartetCount Subtype.val ω) s) (fun s _ _ => t1PValue_mem _ s)
    (fun _ hε' => exists_delta_t1 hd m hpos Q hε')
    (fun _ _ hn _ hb => t1PValue_growth hd (displaysOne_binaryGeneTree dist) hn hb) hε

/-- The T1 tests of all possible states of the algorithm, by the union bound. There is one test for
each pair of a subset `T` of `T₀`, which covers the contractions of `T₀`, and an edge of `T`, since
for the type `mul` the quartets of an edge depend on the current tree `T_k`, which is random; and
one for each overall p-value of a tree `T`, whose set of quartets the paper's "prior choice of `M`"
does not cover (E16). Each has failure probability `< ε / K` for `K` the number of these tests. -/
theorem eventually_t1_all (hd : IsDist dist) (o : ECToBlobOptions)
    (hpos : (o.testCo = .cauchy ∨ o.testCo = .cbc) →
      ∀ s, IsT1Strict (displayCF dist Subtype.val) s →
        ∀ r ∈ s.alternatives, 0 < displayCF dist Subtype.val r)
    {T₀ : Finset (Finset X)} (hT₀ : IsUnrootedTree T₀) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, 1 - ε < iidProb dist n fun ω =>
      (∀ T ⊆ T₀, ∀ A ∈ internalSides T, Deterministic.TestCorrect
        (IsT1Null (displayCF dist Subtype.val)) (edgeQuartets o T₀ T A) (alphaSeq n)
        (edgeT1P o (quartetCount Subtype.val ω) T₀ T A)) ∧
      ∀ T ⊆ T₀, Deterministic.TestCorrect (IsT1Null (displayCF dist Subtype.val))
        (Finset.univ.filter fun s => Displays T s) (alphaSeq n)
        (treeT1P o (quartetCount Subtype.val ω) T) := by
  let tests := (T₀.powerset.sigma fun T => internalSides T).disjSum T₀.powerset
  let quartets : (Σ _ : Finset (Finset X), Finset X) ⊕ Finset (Finset X) →
      Finset (QuartetTree X) :=
    Sum.elim (fun i => edgeQuartets o T₀ i.1 i.2) fun T => Finset.univ.filter fun s => Displays T s
  have hK : ∀ i ∈ tests, (quartets i).card ≤ (Fintype.card X).choose 4 := by
    rintro (⟨T, A⟩ | T) hi
    · obtain ⟨hT, hA⟩ := Finset.mem_sigma.1 (Finset.inl_mem_disjSum.1 hi)
      exact Deterministic.card_edgeQuartets_le hT₀ (Finset.mem_powerset.1 hT)
        (Finset.mem_filter.1 hA).1
    · exact Deterministic.card_displays_le hT₀ (Finset.mem_powerset.1 (Finset.inr_mem_disjSum.1 hi))
  have hall := eventually_forall_mem hd tests (fun i n ω => Deterministic.TestCorrect
      (IsT1Null (displayCF dist Subtype.val)) (quartets i) (alphaSeq n)
      (combineP o.testCo ((quartets i).val.map fun s => t1PValue (quartetCount Subtype.val ω) s)))
    hε fun i hi _ hε' => eventually_t1_correct hd o.testCo hpos (quartets i) (hK i hi) hε'
  filter_upwards [hall] with n hn
  refine hn.trans_le (iidProb_mono hd fun ω hω => ⟨fun T hT A hA => ?_, fun T hT => ?_⟩)
  · exact hω (Sum.inl ⟨T, A⟩) (Finset.inl_mem_disjSum.2
      (Finset.mem_sigma.2 ⟨Finset.mem_powerset.2 hT, hA⟩))
  · exact hω (Sum.inr T) (Finset.inr_mem_disjSum.2 (Finset.mem_powerset.2 hT))

end Events

/-- The proof of Theorem 8.2 at a given `ε`. With probability `> 1 - ε/2` all star tests are right
(lines 1058-1121): each edge of `T₀` has failure probability `< ε/(2K)`, where `K` replaces the
paper's `s` and is the number of sides of internal edges of `T₀`, each edge being counted twice.
With probability `> 1 - ε/2` all T1 tests are right (lines 1123-1132 and 1151-1158,
`eventually_t1_all`). Then the algorithm outputs the tree of blobs (lines 1133-1158,
`Deterministic.ectoblob_eq_treeOfBlobs`). -/
private theorem eventually_sub_lt_iidProb {V E X : Type u} [Fintype X] [DecidableEq X]
    {N : RootedNetwork V E X} (hN : N.IsPhylogenetic) {dist : BinaryGeneTree X → ℝ}
    (hd : IsDist dist) (h₁ : Assumption1Forward N (displayCF dist Subtype.val))
    (h₂ : Assumption1Converse N (displayCF dist Subtype.val))
    {T₀ : Finset (Finset X)} (hT₀ : IsResolutionOf T₀ (treeOfBlobs N)) (o : ECToBlobOptions)
    (hpos : (o.testCo = .cauchy ∨ o.testCo = .cbc) →
      ∀ s, IsT1Strict (displayCF dist Subtype.val) s →
        ∀ r ∈ s.alternatives, 0 < displayCF dist Subtype.val r) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, 1 - ε < iidProb dist n fun ω =>
      ectoblob o (alphaSeq n) (betaSeq n) (quartetCount Subtype.val ω) T₀ = treeOfBlobs N := by
  -- the star tests
  have hS := eventually_forall_mem hd (internalSides T₀)
    (fun A n ω => Deterministic.TestCorrect
      (fun s => IsUniformOn (displayCF dist Subtype.val) s.taxa) (multipartitionQuartets T₀ A)
      (betaSeq n) (edgeStarP o (quartetCount Subtype.val ω) T₀ A))
    (half_pos hε) fun A hA _ hε' => eventually_star_correct hd o.starTest o.testCo _
      (Deterministic.card_multipartitionQuartets_le hT₀.1 (Finset.mem_filter.1 hA).1) hε'
  -- the T1 tests
  have hT := eventually_t1_all hd o hpos hT₀.1 (half_pos hε)
  filter_upwards [hS, hT] with n hnS hnT
  refine (iidProb_and_gt hd n _ _ hnS hnT).trans_le (iidProb_mono hd fun ω hω => ?_)
  exact Deterministic.ectoblob_eq_treeOfBlobs ⟨hN, h₁, h₂,
    fun s => sum_displayCF_binaryGeneTree hd s.card_taxa, hT₀, hω.1, hω.2.1, hω.2.2⟩

/-- Theorem 8.2 for the sequences of the paper's proof. -/
private theorem tendsto_ectoblob {V E X : Type u} [Fintype X] [DecidableEq X]
    (N : RootedNetwork V E X)
    (hN : N.IsPhylogenetic) (dist : BinaryGeneTree X → ℝ) (hd : IsDist dist)
    (h₁ : Assumption1Forward N (displayCF dist Subtype.val))
    (h₂ : Assumption1Converse N (displayCF dist Subtype.val))
    (T₀ : Finset (Finset X)) (hT₀ : IsResolutionOf T₀ (treeOfBlobs N)) (o : ECToBlobOptions)
    (hpos : (o.testCo = .cauchy ∨ o.testCo = .cbc) →
      ∀ s, IsT1Strict (displayCF dist Subtype.val) s →
        ∀ r ∈ s.alternatives, 0 < displayCF dist Subtype.val r) :
    Tendsto (fun n => iidProb dist n fun ω =>
      ectoblob o (alphaSeq n) (betaSeq n) (quartetCount Subtype.val ω) T₀ = treeOfBlobs N)
      atTop (𝓝 1) := by
  refine tendsto_order.2 ⟨fun a ha => ?_, fun a ha => ?_⟩
  · filter_upwards [eventually_sub_lt_iidProb hN hd h₁ h₂ hT₀ o hpos (ε := 1 - a) (by linarith)]
      with n hn
    linarith
  · exact Eventually.of_forall fun n => (iidProb_le_one hd n _).trans_lt ha

/-- **Theorem 8.2** (`ecto:thm8_2`), with the correction agreed with the person who asked for this formalization (E10 of the report)
and the one required for the Cauchy combinations (E11, also agreed). There are sequences `α_n`,
`β_n`, independent of the network, such that for every resolution `T₀` of the tree of blobs, every
variant of the algorithm, and every distribution of binary gene trees whose quartet concordance
factors satisfy both directions of Assumption 1 at the network's parameters, the output on `n`
independent gene trees is the tree of blobs with probability tending to one.

The proof is the paper's (the paper's text, lines 1047-1158), with the same sequences.
Fix `ε`. For each edge of `T₀`, Lemma 8.1 (`ecto:lem8_1`) on the edge's null quartets gives `δ` with
all their p-values in `[δ, 1 - δ]`, and the alternatives have p-values below a threshold `η_n` since
`b_n = -2 log η_n = o(n)`, so by Lemma 6.1 (`ecto:lem6_1`) the combined star p-value is right with
probability `> 1 - ε/(2K)`, and a union bound gives all the star tests with probability `> 1 - ε/2`.
The T1 tests are handled similarly. By Corollaries 4.2 (`ecto:cor4_2`) and 4.3 (`ecto:cor4_3`), a
false edge that Step 3 keeps has a quartet off the T1 null, so it is rejected, while the edges of
the tree of blobs are not.

Departure from the paper, at these points, each repairing a gap or an error of the printed text
unless it says otherwise.

* **The statement (E10).** Printed for any model meeting Assumption 1, it fails at nongeneric
  parameters; here both directions of Assumption 1 hold at the parameters of the network.
* **The Cauchy combinations (E11).** For `cauchy` and `cbc`, the alternatives of a quartet tree with
  (5.2) must have positive probability: otherwise its p-value is exactly `1`, and the Cauchy
  combination is `1` whatever the other p-values. For `bon` and `bbc`, this case is treated apart in
  `exists_delta_t1`.
* **The trivial 4-blob gap (E12).** The paper's witness at a false edge, from Corollaries 4.2 and
  4.3, is not a cut split, and this is what the formal proof starts from
  (`Deterministic.exists_not_inducedCutSplit_edgeQuartets`, and Corollary 4.2 alone for the overall
  p-values). If it has no trivial 4-blob, then the T1 null fails on it, by the converse of
  Assumption 1: this is the paper's argument. If it has a trivial 4-blob, then the T1 null holds on
  it, at the centroid: this case is the gap, and `falseEdge_witness` gives another quartet, for an
  edge that Step 3 keeps (`Deterministic.Run.exists_not_t1Null_of_witness`).
* **The gap at the centroid (E13).** A quartet tree may satisfy the T1 null at its boundary `(1/3,
  1/3, 1/3)`, where its p-value is not asymptotically uniform, so Lemma 8.1 does not apply; the
  proof overlooks this case. Here `t1PValue_centroid_tight` gives the bounds `δ ≤ p ≤ 1 - δ` there
  too. The lower bound serves all methods, and the upper bound only `cauchy` and `cbc`.
* **The slack in `η_n` (E14).** The paper chooses `η_n` with `B(η_n, 1 - δ) ∼ β_n`, which does not
  give `B(η_n, 1 - δ) < β_n`. Here `η_n = c₀ β_n` and `c₀ α_n` for a small constant `c₀`, one for
  each test (`Deterministic.exists_combineBounds`). Only `b_n = o(n)` is used of `b_n = -2 log η_n`.
* **The T1 threshold (E14).** The paper's "an individual p-value is below `η_n` exactly when the
  statistic is above `b_n`" holds for the star test, whose test law is fixed, and not for the T1
  test, whose law depends on an estimated `μ`. The formal proof bounds the T1 p-value above by the
  `χ²₂` tail at the statistic.
* **The upper bound on combined p-values (E15).** The paper's proof says that the combined p-value
  of a cut edge lies in `(α_n, 1 - δ)`. The upper bound fails for `bon`, `bbc` and `cbc`, even with
  positive alternatives: `Bon({3/4, 3/4}) = 1`. Only the lower bound `> α_n` is used. The individual
  upper bounds `p ≤ 1 - δ` are used only for `cauchy` and `cbc`, through Lemma 6.1.
* **The union over the intermediate trees (E16).** The budget `ε/(2s)` is per edge of `T₀`, but for
  the type `mul` the quartets of an edge depend on the current tree, which is random, and the
  paper's "prior choice of `M`" does not cover the overall p-values. Here there is one T1 test for
  each pair of a subset `T ⊆ T₀`, which covers the contractions of `T₀`, and an edge of `T`, and one
  overall test for each `T`, and `K`, the number of these tests, replaces `s` in the budget
  (`eventually_t1_all`).
* **Step 3 (E17).** The paper says that Step 3 contracts "precisely those edges that resolve
  multifurcations". This is false: on a 4-cycle, `ab|cd` resolves a multifurcation of the tree of
  blobs and survives Step 3. The formal proof shows what is needed: the edges of the tree of blobs
  are kept, and each edge that is kept has a nonuniform quartet.
* **Binary gene trees.** The paper says "any model meeting Assumption 1". The statement here takes a law
  on binary gene trees, counted by `quartetCount`, as for the coalescent models. The displayed tree model with
  the paper's convention at a star (lines 289-293) is outside it, and is outside the printed proof too: at a
  trivial 4-blob its counts are `(n/3, n/3, n/3)` on every sample and the p-values are exactly `1`, so line 1065
  fails (`ECToBlob.pValues_of_hasTrivialFourBlob`).
* **The type `quad` (not a gap in the proof).** `S_quad` is defined only for an edge whose ends have degree three
  (line 557), but "any variant" covers `T₀` non-binary. On such a tree `edgeQuartets` takes the multipartition.
* **Late selection (not a gap in the proof).** The paper's late rule is undefined when no `p_k < α` (line 989).
  `selectedIteration` fixes a value there.
* **Bon and BBC under the alternative.** They reject through `2k · min` (`Deterministic.exists_combineBounds`), and
  not through item 1 of Lemma 6.1, whose upper bound on the individual p-values fails at degenerate `p = 1`.
* **Counting (not forced, and immaterial).** For the star tests `K` counts the sides of the internal
  edges of `T₀`, so each edge twice, since a tree is given by the sides of its splits. Each quartet
  of `S^a(e)` gets a share `1/|S^a(e)|` of its half of the test's failure probability, not
  `1/C(s,4)`. Lemma 8.1 is applied to the edge's null quartets with `K` their number plus one, and
  Lemma 6.1 with the paper's `C(s,4)` (`Deterministic.card_le_choose_of_displays`). -/
theorem theorem8_2 : ∃ α β : ℕ → ℝ, Tendsto α atTop (𝓝 0) ∧ Tendsto β atTop (𝓝 0) ∧
    (∀ᶠ n in atTop, 0 < α n ∧ α n < 1) ∧ (∀ᶠ n in atTop, 0 < β n ∧ β n < 1) ∧
    ∀ {V E X : Type u} [Fintype X] [DecidableEq X] (N : RootedNetwork V E X)
      (_ : N.IsPhylogenetic) (dist : BinaryGeneTree X → ℝ) (_ : IsDist dist)
      (_ : Assumption1Forward N (displayCF dist Subtype.val))
      (_ : Assumption1Converse N (displayCF dist Subtype.val))
      (T₀ : Finset (Finset X)) (_ : IsResolutionOf T₀ (treeOfBlobs N))
      (o : ECToBlobOptions)
      (_ : (o.testCo = .cauchy ∨ o.testCo = .cbc) →
        ∀ s, IsT1Strict (displayCF dist Subtype.val) s →
          ∀ r ∈ s.alternatives, 0 < displayCF dist Subtype.val r),
      Tendsto (fun n => iidProb dist n fun ω =>
        ectoblob o (α n) (β n) (quartetCount Subtype.val ω) T₀ = treeOfBlobs N) atTop (𝓝 1) :=
  ⟨alphaSeq, betaSeq, tendsto_alphaSeq, tendsto_betaSeq,
    (tendsto_alphaSeq.eventually (gt_mem_nhds zero_lt_one)).mono fun _ hn =>
      ⟨chiSqOneTail_pos _, hn⟩,
    (tendsto_betaSeq.eventually (gt_mem_nhds zero_lt_one)).mono fun _ hn =>
      ⟨Real.exp_pos _, hn⟩,
    fun N hN dist hd h₁ h₂ T₀ hT₀ o hpos => tendsto_ectoblob N hN dist hd h₁ h₂ T₀ hT₀ o hpos⟩

/-- The sequences of `theorem8_2` are the explicit ones of the paper's proof. -/
theorem theorem8_2_explicit {V E X : Type u} [Fintype X] [DecidableEq X] (N : RootedNetwork V E X)
    (hN : N.IsPhylogenetic) (dist : BinaryGeneTree X → ℝ) (hd : IsDist dist)
    (h₁ : Assumption1Forward N (displayCF dist Subtype.val))
    (h₂ : Assumption1Converse N (displayCF dist Subtype.val))
    (T₀ : Finset (Finset X)) (hT₀ : IsResolutionOf T₀ (treeOfBlobs N)) (o : ECToBlobOptions)
    (hpos : (o.testCo = .cauchy ∨ o.testCo = .cbc) →
      ∀ s, IsT1Strict (displayCF dist Subtype.val) s →
        ∀ r ∈ s.alternatives, 0 < displayCF dist Subtype.val r) :
    Tendsto (fun n => iidProb dist n fun ω =>
      ectoblob o (alphaSeq n) (betaSeq n) (quartetCount Subtype.val ω) T₀ = treeOfBlobs N)
      atTop (𝓝 1) :=
  tendsto_ectoblob N hN dist hd h₁ h₂ T₀ hT₀ o hpos

/-- Theorem 8.2 for a model meeting Assumption 1: the conclusion holds for all resolutions and all
variants at all valid parameters outside a null set of the measure of §5.1, the one that Assumption
1 excludes. -/
theorem theorem8_2_generic {V E X : Type u} [Fintype V] [Fintype E] [Fintype X] [DecidableEq X]
    (N : RootedNetwork V E X) (hN : N.IsPhylogenetic)
    (dist : MetricData E → BinaryGeneTree X → ℝ) (hd : ∀ θ, N.IsMetric θ → IsDist (dist θ))
    (hA : Assumption1 N fun θ => displayCF (dist θ) Subtype.val) :
    IsNullParams N {θ | N.IsMetric θ ∧ ¬ ∀ (T₀ : Finset (Finset X)) (o : ECToBlobOptions),
      IsResolutionOf T₀ (treeOfBlobs N) →
      ((o.testCo = .cauchy ∨ o.testCo = .cbc) →
        ∀ s, IsT1Strict (displayCF (dist θ) Subtype.val) s →
          ∀ r ∈ s.alternatives, 0 < displayCF (dist θ) Subtype.val r) →
      Tendsto (fun n => iidProb (dist θ) n fun ω =>
        ectoblob o (alphaSeq n) (betaSeq n) (quartetCount Subtype.val ω) T₀ = treeOfBlobs N)
        atTop (𝓝 1)} := by
  intro d hd'
  refine MeasureTheory.measure_mono_null ?_ (hA.2 d hd')
  rintro x ⟨hval, hθ, hnot⟩
  refine ⟨hval, hval, fun hconv => hnot fun T₀ o hT₀ hpos => ?_⟩
  exact theorem8_2_explicit N hN (dist _) (hd _ hval) (hA.1 _ hval) hconv T₀ hT₀ o hpos

end ECToBlob
