module

public import Basic.Probability.QuartetLimits
public import ECToBlob.Section4
public import ECToBlob.Section5
public import ECToBlob.Lemma81
public import ECToBlob.Section6
public import ECToBlob.Deterministic

/-!
# ECToBlob §8: statistical consistency

Theorem 8.2. Lemma 8.1 is in `ECToBlob/Lemma81.lean`, the deterministic part of the proof in
`ECToBlob/Deterministic.lean`, and the repair of the choice of a quartet at a false edge in
`ECToBlob/FalseEdge.lean`.

Theorem 8.2 is stated for a network at numerical parameters where both directions of Assumption 1
hold (E7 of the report: as printed, for all parameters, it fails). The correction was agreed with
the user. `theorem8_2_generic` gives the statement for almost all parameters, from `Assumption1`.

For the corrections `cauchy` and `cbc`, Theorem 8.2 also requires the alternatives of a quartet tree
satisfying (5.2) to have positive probability: without this a p-value is exactly `1`, and the Cauchy
combination is `1` whatever the other p-values (E18 of the report).
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
private theorem sum_displayCF_binaryGeneTree {dist : BinaryGeneTree X → ℝ} (hd : IsDist dist)
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

private theorem t1PValue_mem (c : QuartetTree X → ℝ) (s : QuartetTree X) :
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

private theorem eventually_alphaSeq_pos : ∀ᶠ n in atTop, 0 < alphaSeq n := chiSqOneTail_log_pos

private theorem betaSeq_eq {n : ℕ} (hn : 0 < n) : betaSeq n = 1 / Real.sqrt n :=
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

private theorem tendsto_log_betaSeq :
    Tendsto (fun n : ℕ => Real.log (betaSeq n) / n) atTop (𝓝 0) := by
  have h : Tendsto (fun x : ℝ => Real.log x ^ 1 / (1 * x + 0)) atTop (𝓝 0) :=
    Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero
  have h' := (h.comp tendsto_natCast_atTop_atTop).const_mul (-(1 / 2) : ℝ)
  rw [mul_zero] at h'
  refine h'.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with n hn
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hlog : Real.log (1 / Real.sqrt (n : ℝ)) = -(Real.log n / 2) := by
    rw [one_div, Real.log_inv, Real.log_sqrt hn'.le]
  simp only [Function.comp, pow_one, one_mul, add_zero]
  rw [betaSeq_eq hn, hlog]
  ring

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

/-! ### The events of the proof -/

section Events

universe w

variable {X : Type w} [Fintype X] [DecidableEq X] {dist : BinaryGeneTree X → ℝ}

/-- Lemma 8.1 for the asymptotically uniform p-values: the star test on the uniform 4-taxon sets,
and the T1 test on the quartet trees with (5.2) and positive alternatives. -/
private theorem exists_delta_family (hd : IsDist dist) (k : StarTest) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ δ < 1 / 2 ∧ ∃ M : ℕ, ∀ n, M < n → 1 - ε < iidProb dist n fun ω =>
      (∀ q : Finset X, q.card = 4 → IsUniformOn (displayCF dist Subtype.val) q →
        δ ≤ starPValue k (quartetCount Subtype.val ω) q ∧
          starPValue k (quartetCount Subtype.val ω) q ≤ 1 - δ) ∧
      (∀ s : QuartetTree X, IsT1Strict (displayCF dist Subtype.val) s →
        (∀ r ∈ s.alternatives, 0 < displayCF dist Subtype.val r) →
        δ ≤ t1PValue (quartetCount Subtype.val ω) s ∧
          t1PValue (quartetCount Subtype.val ω) s ≤ 1 - δ) := by
  let ιq := {q : Finset X // q.card = 4 ∧ IsUniformOn (displayCF dist Subtype.val) q}
  let ιs := {s : QuartetTree X // IsT1Strict (displayCF dist Subtype.val) s ∧
    ∀ r ∈ s.alternatives, 0 < displayCF dist Subtype.val r}
  let fam : ιq ⊕ ιs → (n : ℕ) → (Fin n → BinaryGeneTree X) → ℝ :=
    Sum.elim (fun q _ ω => starPValue k (quartetCount Subtype.val ω) q.1)
      (fun s _ ω => t1PValue (quartetCount Subtype.val ω) s.1)
  have hone := displaysOne_binaryGeneTree dist
  have hcnt : ∀ (n : ℕ) (ω : Fin n → BinaryGeneTree X) (r : QuartetTree X),
      0 ≤ quartetCount Subtype.val ω r := fun _ _ _ => Nat.cast_nonneg _
  obtain ⟨δ, h0, h1, h⟩ := lemma8_1.{w, w} (Fintype.card (ιq ⊕ ιs) + 1) (by omega) hε
  obtain ⟨M, hM⟩ := h dist fam hd (by omega)
    (by
      rintro (q | s) n ω
      · exact starPValue_mem k _ (hcnt n ω) q.2.1
      · exact t1PValue_mem _ _)
    (by
      rintro (q | s)
      · exact starPValue_asymptoticallyUniform k hd hone q.2.1 q.2.2
      · exact t1PValue_asymptoticallyUniform hd hone s.2.1.1 s.2.1.2 s.2.2)
  refine ⟨δ, h0, h1, M, fun n hn => (hM n hn).trans_le (iidProb_mono hd fun ω hω => ?_)⟩
  exact ⟨fun q hq hu => hω (Sum.inl ⟨q, hq, hu⟩), fun s hs hp => hω (Sum.inr ⟨s, hs, hp⟩)⟩

/-- The T1 test at the centroid, on which the paper's proof is silent (it is a boundary point of the
null, at which the test is not asymptotically uniform). -/
private theorem exists_delta_centroid (hd : IsDist dist) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ δ < 1 / 2 ∧ ∀ᶠ n : ℕ in atTop, 1 - ε < iidProb dist n fun ω =>
      ∀ s : QuartetTree X, IsUniformOn (displayCF dist Subtype.val) s.taxa →
        δ ≤ t1PValue (quartetCount Subtype.val ω) s ∧
          t1PValue (quartetCount Subtype.val ω) s ≤ 1 - δ := by
  let ιc := {s : QuartetTree X // IsUniformOn (displayCF dist Subtype.val) s.taxa}
  have hone := displaysOne_binaryGeneTree dist
  have hcard : (0 : ℝ) < (Fintype.card ιc : ℝ) + 1 := by positivity
  have hε' : 0 < ε / (2 * ((Fintype.card ιc : ℝ) + 1)) := by positivity
  have hmain := fun s : ιc => t1PValue_centroid_tight hd hone s.2 hε'
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
      iidProb dist n fun ω => ∀ s : QuartetTree X,
        IsUniformOn (displayCF dist Subtype.val) s.taxa →
        d ≤ t1PValue (quartetCount Subtype.val ω) s ∧
          t1PValue (quartetCount Subtype.val ω) s ≤ 1 - d := by
    refine iidProb_mono hd fun ω hω s hs => ?_
    have := hω ⟨s, hs⟩ (Finset.mem_univ _)
    have hdle' := hdle ⟨s, hs⟩
    exact ⟨hdle'.trans this.1, this.2.trans (by linarith)⟩
  linarith

/-- The tests that must reject do so, by the growth of their statistics; and all draws have positive
probability. -/
private theorem tendsto_alternative (hd : IsDist dist) (k : StarTest) {bα bβ : ℕ → ℝ}
    (hbα : Tendsto (fun n => bα n / n) atTop (𝓝 0))
    (hbβ : Tendsto (fun n => bβ n / n) atTop (𝓝 0)) :
    Tendsto (fun n => iidProb dist n fun ω =>
      (∀ q : Finset X, q.card = 4 → ¬ IsUniformOn (displayCF dist Subtype.val) q →
        starPValue k (quartetCount Subtype.val ω) q < Real.exp (-(bβ n) / 2)) ∧
      (∀ s : QuartetTree X, ¬ Deterministic.T1Null (displayCF dist Subtype.val) s →
        t1PValue (quartetCount Subtype.val ω) s < Real.exp (-(bα n) / 2)) ∧
      ∏ i, dist (ω i) ≠ 0) atTop (𝓝 1) := by
  have hone := displaysOne_binaryGeneTree dist
  let ιq := {q : Finset X // q.card = 4 ∧ ¬ IsUniformOn (displayCF dist Subtype.val) q}
  let ιs := {s : QuartetTree X // ¬ Deterministic.T1Null (displayCF dist Subtype.val) s}
  let Ev : (ιq ⊕ ιs) ⊕ Unit → (n : ℕ) → (Fin n → BinaryGeneTree X) → Prop :=
    Sum.elim
      (Sum.elim
        (fun q n ω => starPValue k (quartetCount Subtype.val ω) q.1 < Real.exp (-(bβ n) / 2))
        (fun s n ω => t1PValue (quartetCount Subtype.val ω) s.1 < Real.exp (-(bα n) / 2)))
      (fun _ n ω => ∏ i, dist (ω i) ≠ 0)
  have hall : Tendsto (fun n => iidProb dist n fun ω => ∀ i, Ev i n ω) atTop (𝓝 1) := by
    refine tendsto_iidProb_forall hd Ev ?_
    rintro ((q | s) | _)
    · exact starStat_growth k hd hone q.2.1 q.2.2 hbβ
    · exact t1PValue_growth hd hone s.2 hbα
    · refine tendsto_const_nhds.congr fun n => ?_
      exact (iidProb_true hd n).symm.trans (iidProb_prod_ne_zero n).symm
  refine tendsto_iidProb_of_imp hd (Eventually.of_forall fun n ω hω => ?_) hall
  exact ⟨fun q hq hu => hω (Sum.inl (Sum.inl ⟨q, hq, hu⟩)),
    fun s hs => hω (Sum.inl (Sum.inr ⟨s, hs⟩)), hω (Sum.inr ())⟩

end Events

/-- On the events of the proof, the table of counts is one on which every test behaves as it should.
-/
private theorem run_of_events {N : RootedNetwork V E X} (hN : N.IsPhylogenetic)
    {dist : BinaryGeneTree X → ℝ} (hd : IsDist dist)
    (h₁ : Assumption1Forward N (displayCF dist Subtype.val))
    (h₂ : Assumption1Converse N (displayCF dist Subtype.val))
    {T₀ : Finset (Finset X)} (hT₀ : IsResolutionOf T₀ (treeOfBlobs N)) {o : ECToBlobOptions}
    (hpos : (o.testCo = .cauchy ∨ o.testCo = .cbc) →
      ∀ s, IsT1Strict (displayCF dist Subtype.val) s →
        ∀ r ∈ s.alternatives, 0 < displayCF dist Subtype.val r)
    {α β δ ηα ηβ : ℝ} {n : ℕ} {ω : Fin n → BinaryGeneTree X}
    (cα : Deterministic.CombineBounds o.testCo (Fintype.card (QuartetTree X)) δ α ηα)
    (cβ : Deterministic.CombineBounds o.testCo (Fintype.card (QuartetTree X)) δ β ηβ)
    (hαδ : α < δ) (hβδ : β < δ) (hδ : δ < 1 / 2) (hηα : ηα ≤ 1 - δ) (hηβ : ηβ ≤ 1 - δ)
    (star_u : ∀ q : Finset X, q.card = 4 → IsUniformOn (displayCF dist Subtype.val) q →
      δ ≤ starPValue o.starTest (quartetCount Subtype.val ω) q ∧
        starPValue o.starTest (quartetCount Subtype.val ω) q ≤ 1 - δ)
    (t1_s : ∀ s : QuartetTree X, IsT1Strict (displayCF dist Subtype.val) s →
      (∀ r ∈ s.alternatives, 0 < displayCF dist Subtype.val r) →
      δ ≤ t1PValue (quartetCount Subtype.val ω) s ∧
        t1PValue (quartetCount Subtype.val ω) s ≤ 1 - δ)
    (t1_u : ∀ s : QuartetTree X, IsUniformOn (displayCF dist Subtype.val) s.taxa →
      δ ≤ t1PValue (quartetCount Subtype.val ω) s ∧
        t1PValue (quartetCount Subtype.val ω) s ≤ 1 - δ)
    (star_a : ∀ q : Finset X, q.card = 4 → ¬ IsUniformOn (displayCF dist Subtype.val) q →
      starPValue o.starTest (quartetCount Subtype.val ω) q < ηβ)
    (t1_a : ∀ s : QuartetTree X, ¬ Deterministic.T1Null (displayCF dist Subtype.val) s →
      t1PValue (quartetCount Subtype.val ω) s < ηα)
    (hprod : ∏ i, dist (ω i) ≠ 0) :
    Deterministic.Run N (displayCF dist Subtype.val) T₀ o α β δ ηα ηβ
      (quartetCount Subtype.val ω) := by
  have hone := displaysOne_binaryGeneTree dist
  have hsum : ∀ s : QuartetTree X, ∑ r ∈ treesOn s.taxa, displayCF dist Subtype.val r = 1 :=
    fun s => sum_displayCF_binaryGeneTree hd s.card_taxa
  have hnn : ∀ r, 0 ≤ displayCF dist Subtype.val r := fun r =>
    Finset.sum_nonneg fun g _ => by
      split_ifs
      · exact hd.1 g
      · exact le_rfl
  refine ⟨hN, h₁, h₂, hsum, hT₀, cα, cβ, ?_, fun s => t1PValue_mem _ s, ?_, star_a, ?_, t1_a, ?_,
    ?_⟩
  · exact fun q hq => starPValue_mem _ _ (fun r => Nat.cast_nonneg _) hq
  · exact fun q hq hu => hβδ.trans_le (star_u q hq hu).1
  · intro s hnull
    by_cases hs : IsT1Strict (displayCF dist Subtype.val) s
    · by_cases hp : ∀ r ∈ s.alternatives, 0 < displayCF dist Subtype.val r
      · exact hαδ.trans_le (t1_s s hs hp).1
      · push Not at hp
        obtain ⟨r₀, hr₀, hr₀'⟩ := hp
        have hzero : ∀ r ∈ s.alternatives, displayCF dist Subtype.val r = 0 := fun r hr =>
          (hs.2 r hr r₀ hr₀).trans (le_antisymm hr₀' (hnn r₀))
        rw [t1PValue_degenerate hd hone hzero ω hprod]
        linarith
    · by_cases hu : IsUniformOn (displayCF dist Subtype.val) s.taxa
      · exact hαδ.trans_le (t1_u s hu).1
      · exact absurd hnull (Deterministic.not_t1Null (hsum s) hs hu)
  · intro _ q hq
    by_cases hu : IsUniformOn (displayCF dist Subtype.val) q
    · exact (star_u q hq hu).2
    · exact (star_a q hq hu).le.trans hηβ
  · intro hm s
    by_cases hnull : Deterministic.T1Null (displayCF dist Subtype.val) s
    · by_cases hs : IsT1Strict (displayCF dist Subtype.val) s
      · exact (t1_s s hs (hpos hm s hs)).2
      · by_cases hu : IsUniformOn (displayCF dist Subtype.val) s.taxa
        · exact (t1_u s hu).2
        · exact absurd hnull (Deterministic.not_t1Null (hsum s) hs hu)
    · exact (t1_a s hnull).le.trans hηα

/-- The proof of Theorem 8.2 at a given `ε`. -/
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
  -- Lemma 8.1, and the centroid
  obtain ⟨δ₁, hδ₁, hδ₁', M, hM⟩ :=
    exists_delta_family (X := X) hd o.starTest (ε := ε / 3) (by positivity)
  obtain ⟨δ₂, hδ₂, hδ₂', hC⟩ := exists_delta_centroid (X := X) hd (ε := ε / 3) (by positivity)
  have hδ0 : 0 < min δ₁ δ₂ := lt_min hδ₁ hδ₂
  have hδ1 : min δ₁ δ₂ < 1 / 2 := min_lt_of_left_lt hδ₁'
  -- Lemma 6.1, with slack
  obtain ⟨c₀, hc₀, hcomb⟩ := Deterministic.exists_combineBounds o.testCo
    (Fintype.card (QuartetTree X)) hδ0 (by linarith)
  have hα' : Tendsto alphaSeq atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.2 ⟨tendsto_alphaSeq, eventually_alphaSeq_pos⟩
  have hβ' : Tendsto betaSeq atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.2 ⟨tendsto_betaSeq, eventually_betaSeq_pos⟩
  -- the tests that must reject
  have hG := (tendsto_alternative (X := X) hd o.starTest
    (tendsto_threshold hc₀ eventually_alphaSeq_pos tendsto_log_chiSqOneTail_log)
    (tendsto_threshold hc₀ eventually_betaSeq_pos tendsto_log_betaSeq)).eventually_const_lt
      (show 1 - ε / 3 < 1 by linarith)
  have hsm : ∀ {a : ℕ → ℝ}, Tendsto a atTop (𝓝 0) → ∀ᶠ n in atTop, c₀ * a n ≤ 1 - min δ₁ δ₂ := by
    intro a ha
    have : Tendsto (fun n => c₀ * a n) atTop (𝓝 (c₀ * 0)) := ha.const_mul c₀
    rw [mul_zero] at this
    exact (this.eventually_lt_const (show (0 : ℝ) < 1 - min δ₁ δ₂ by linarith)).mono fun _ h => h.le
  filter_upwards [hα'.eventually hcomb, hβ'.eventually hcomb, eventually_gt_atTop M, hC, hG,
    tendsto_alphaSeq.eventually_lt_const hδ0, tendsto_betaSeq.eventually_lt_const hδ0,
    hsm tendsto_alphaSeq, hsm tendsto_betaSeq, eventually_alphaSeq_pos, eventually_betaSeq_pos]
    with n hcα hcβ hnM hnC hnG hαδ hβδ hηα hηβ hαpos hβpos
  refine iidProb_three hd n _ _ _ _ ?_ (hM n hnM) hnC hnG
  rintro ω ⟨hq, hs⟩ hc ⟨g₁, g₂, g₃⟩
  refine Deterministic.ectoblob_eq_treeOfBlobs (run_of_events hN hd h₁ h₂ hT₀ hpos (ω := ω) hcα hcβ
    hαδ hβδ hδ1 hηα hηβ ?_ ?_ ?_ ?_ ?_ g₃)
  · intro q hq' hu
    have := hq q hq' hu
    exact ⟨(min_le_left _ _).trans this.1, this.2.trans (by linarith [min_le_left δ₁ δ₂])⟩
  · intro r hr hp
    have := hs r hr hp
    exact ⟨(min_le_left _ _).trans this.1, this.2.trans (by linarith [min_le_left δ₁ δ₂])⟩
  · intro r hu
    have := hc r hu
    exact ⟨(min_le_right _ _).trans this.1, this.2.trans (by linarith [min_le_right δ₁ δ₂])⟩
  · intro q hq' hu
    have := g₁ q hq' hu
    rwa [exp_threshold (mul_pos hc₀ hβpos)] at this
  · intro r hr
    have := g₂ r hr
    rwa [exp_threshold (mul_pos hc₀ hαpos)] at this

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

/-- **Theorem 8.2** (`ecto:thm8_2`), with the correction agreed with the user (E7 of the report) and
the one required for the Cauchy combinations (E18). There are sequences `α_n`, `β_n`, independent of
the network, such that for every resolution `T₀` of the tree of blobs, every variant of the
algorithm, and every distribution of binary gene trees whose quartet concordance factors satisfy
both directions of Assumption 1 at the network's parameters, the output on `n` independent gene
trees is the tree of blobs with probability tending to one.

The proof is the paper's: the same sequences; Lemma 8.1 for the p-values under the null, then Lemma
6.1 for the combined p-values; the growth of the statistics under the alternative; Corollary 4.3 for
an edge that is not a cut edge. These points differ from the printed text.

* **The statement (E7).** Printed for any model meeting Assumption 1, it fails at nongeneric
  parameters; here both directions of Assumption 1 hold at the parameters of the network.
* **The Cauchy combinations (E18).** For `cauchy` and `cbc`, the alternatives of a quartet tree with
  (5.2) must have positive probability: otherwise its p-value is exactly `1`, and the Cauchy
  combination is `1` whatever the other p-values. So for `bon` and `bbc` the combined p-value of a
  cut edge is above `α_n`, but need not be below `1 - δ` as the paper's proof says; only the lower
  bound is used.
* **The slack in `η_n`.** The paper chooses `η_n` with `B(K, η_n, 1 - δ) ∼ β_n`, which does not give
  `B(K, η_n, 1 - δ) < β_n`. Here `η_n = c₀ β_n` and `c₀ α_n` for a small constant `c₀`
  (`Deterministic.exists_combineBounds`). Only `b_n = o(n)` is used of `b_n = -2 log η_n`.
* **The union over the intermediate trees.** The sequence of trees is random, so a bound for each
  edge of a tree does not cover the run. Here the events are per quartet, not per run
  (`Deterministic.Run`): on one event every combined test on every possible tree comes out right.
* **The gap at the centroid.** A quartet tree may satisfy the T1 null at its boundary `(1/3, 1/3,
  1/3)`, where its p-value is not asymptotically uniform, so Lemma 8.1 does not apply; the proof
  overlooks this case. Here `t1PValue_centroid_tight` gives the bounds `δ ≤ p ≤ 1 - δ` there too.
* **The trivial 4-blob gap.** The paper finds a quartet on which the T1 null fails at a false edge
  from Corollaries 4.2 and 4.3, but their witness may have a trivial 4-blob, on which the null
  holds. Here `falseEdge_witness` gives a quartet that is neither a cut split nor a trivial 4-blob.

Corollary 4.2, which the paper cites for the type `bi`, is not used: the witness of
`falseEdge_witness`, through Corollary 4.3, lies in the multipartition of `T₀`, which is contained
in the quartets of all three types at every stage of the algorithm. -/
theorem theorem8_2 : ∃ α β : ℕ → ℝ, Tendsto α atTop (𝓝 0) ∧ Tendsto β atTop (𝓝 0) ∧
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
  ⟨alphaSeq, betaSeq, tendsto_alphaSeq, tendsto_betaSeq, fun N hN dist hd h₁ h₂ T₀ hT₀ o hpos =>
    tendsto_ectoblob N hN dist hd h₁ h₂ T₀ hT₀ o hpos⟩

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

/-- Theorem 8.2 for a model meeting Assumption 1: it holds at all parameters outside the null set
that Assumption 1 excludes. -/
theorem theorem8_2_generic {V E X : Type u} [Fintype V] [Fintype E] [Fintype X] [DecidableEq X]
    (N : RootedNetwork V E X) (hN : N.IsPhylogenetic)
    (dist : MetricData E → BinaryGeneTree X → ℝ) (hd : ∀ θ, N.IsMetric θ → IsDist (dist θ))
    (hA : Assumption1 N fun θ => displayCF (dist θ) Subtype.val)
    (θ : MetricData E) (hθ : N.IsMetric θ)
    (hgen : Assumption1Converse N (displayCF (dist θ) Subtype.val))
    (T₀ : Finset (Finset X)) (hT₀ : IsResolutionOf T₀ (treeOfBlobs N)) (o : ECToBlobOptions)
    (hpos : (o.testCo = .cauchy ∨ o.testCo = .cbc) →
      ∀ s, IsT1Strict (displayCF (dist θ) Subtype.val) s →
        ∀ r ∈ s.alternatives, 0 < displayCF (dist θ) Subtype.val r) :
    Tendsto (fun n => iidProb (dist θ) n fun ω =>
      ectoblob o (alphaSeq n) (betaSeq n) (quartetCount Subtype.val ω) T₀ = treeOfBlobs N)
      atTop (𝓝 1) :=
  theorem8_2_explicit N hN (dist θ) (hd θ hθ) (hA.1 θ hθ) hgen T₀ hT₀ o hpos

end ECToBlob
