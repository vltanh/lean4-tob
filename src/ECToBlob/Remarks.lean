module

public import AllmanEtAl2023.GenericCF
public import Basic.Defs
public import Phylogenetics.NMSC.Exchangeability
public import Phylogenetics.NMSC.Witness
public import Basic.Testing.Combining
public import Basic.Testing.Trinomial.Gaussian
public import ECToBlob.Remark84

/-!
# ECToBlob §10: variants of the algorithm

The paper's §10 ("Further developments and caveats", the paper's text, lines 1411-1465)
proposes three changes to the algorithm. Here is their consistency.

* **Dropping the no-anomaly assumption** (lines 1455-1457): "it would be desirable to drop the 'no
  anomalous quartet' assumption ... This could easily be done for our use of the T1 test". The T1 test
  is replaced by the test of the cut-model line of the fixed topology, `p_{s'} = p_{s''}` with no
  condition on `p_s` (`LineNull`, `linePValue`, `ectoblobLine`). Then
  `tendsto_ectoblobLine_limitTree` is the analogue of `Coarsening.tendsto_ectoblob_limitTree` and
  `consistency_line` of Theorem 8.2, under `CutLineForward` and `CutLineConverse`, which hold for the
  NMSC at generic parameters with no assumption on anomalies (`cutLine_nmsc`).
* **Using the data twice, or splitting it** (lines 1435-1452): if `T₀` depends on the data in any way,
  and it is a resolution of the tree of blobs with probability tending to one, then the output is the
  tree of blobs with probability tending to one (`consistency_random_tree`). The union over the finitely
  many possible `T₀` makes this short. `consistency_data_splitting` is the case of a tree `T₀` that
  may depend on all genes, with quartet counts from the last `m₂` genes.
* **Combining the edge p-values** (lines 1412-1419): `consistency_edge_combination`.
-/

@[expose] public noncomputable section

open Phylogenetics Phylogenetics.RootedNetwork Phylogenetics.QuartetTests Phylogenetics.Trinomial
open Finset Filter Topology
open scoped Classical

namespace ECToBlob.Remarks

open ECToBlob.Deterministic ECToBlob.Coarsening

/-! ### The test of the cut-model line -/

section LineTest

variable {X : Type*} [Fintype X] [DecidableEq X]

/-- The null hypothesis of the cut model at the quartet tree `s`: `p_{s'} = p_{s''}`, with no
condition on `p_s`. The T1 null is this and `p_{s'} ≤ p_s`. -/
def LineNull (p : QuartetTree X → ℝ) (s : QuartetTree X) : Prop :=
  ∀ r ∈ s.alternatives, ∀ r' ∈ s.alternatives, p r = p r'

/-- The p-value of the likelihood ratio test of the line: the `χ²₁` tail at the statistic `lineStat`
of TINNiK Appendix C.1. -/
def linePValue (c : QuartetTree X → ℝ) (s : QuartetTree X) : ℝ := chiSqOneTail (lineStat c s)

theorem linePValue_mem (c : QuartetTree X → ℝ) (s : QuartetTree X) :
    0 ≤ linePValue c s ∧ linePValue c s ≤ 1 :=
  ⟨chiSqOneTail_nonneg _, chiSqOneTail_le_one _⟩

/-- The likelihood ratio test of the line on three counts: `χ²₁` in the limit. This is the argument of
`Trinomial.tendsto_t1` without the second coordinate. -/
theorem tendsto_line {φ : ℝ} (hφ : 0 < φ ∧ φ < 3 / 2) {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 1) :
    Tendsto (fun n ↦ iidProb (cutPoint φ) n fun η ↦
      chiSqOneTail (lineS (count η 1) (count η 2)) ≤ x) atTop (𝓝 x) := by
  rcases h0.eq_or_lt with rfl | hx
  · have : ∀ n, iidProb (cutPoint φ) n
        (fun η ↦ chiSqOneTail (lineS (count η 1) (count η 2)) ≤ 0) = 0 := fun n ↦
      Finset.sum_eq_zero fun η _ ↦ ite_eq_right (not_le.2 (chiSqOneTail_pos _))
    simp only [this]
    exact tendsto_const_nhds
  obtain ⟨t, ht0, htx⟩ := exists_chiSqOneTail_eq hx h1
  have hlim : Tendsto (fun n ↦ iidProb (cutPoint φ) n fun η ↦
      chiSqOneTail (lineS (count η 1) (count η 2)) ≤ x) atTop
      (𝓝 (stdPlane.real {z | t < z.1 ^ 2})) := by
    refine tendsto_iidProb_of_threshold hφ (T := fun z ↦ z.1 ^ 2) (by fun_prop) ?_ ?_
      (stdPlane_first_null t)
    · intro R hR δ hδ
      filter_upwards [eventually_lineS_first hφ hR (half_pos hδ)] with n h₁ η hη₁ hη₂ hη₃
      have h₄ := (abs_lt.1 (h₁ _ _ _ (count_add η) hη₁ hη₂)).1
      have h₅ : t ≤ lineS (count η 1) (count η 2) := by
        have : t + δ < (whiten φ n (count η 0) (count η 1) (count η 2)).1 ^ 2 := hη₃
        linarith
      exact (chiSqOneTail_anti h₅).trans_eq htx
    · intro R hR δ hδ
      filter_upwards [eventually_lineS_first hφ hR (half_pos hδ)] with n h₁ η hη₁ hη₂ hη₃ hle
      have h₄ := (abs_lt.1 (h₁ _ _ _ (count_add η) hη₁ hη₂)).2
      have hη₃' : (whiten φ n (count η 0) (count η 1) (count η 2)).1 ^ 2 < t - δ := hη₃
      have h₅ : lineS (count η 1) (count η 2) ≤ t - δ / 2 := by linarith
      have h₆ : 0 ≤ t - δ / 2 := by
        nlinarith [sq_nonneg (whiten φ n (count η 0) (count η 1) (count η 2)).1]
      have h₇ : chiSqOneTail t < chiSqOneTail (t - δ / 2) :=
        chiSqOneTail_lt_of_lt h₆ (by linarith)
      have h₈ := chiSqOneTail_anti h₅
      linarith
  rwa [stdPlane_real_first, htx] at hlim

section Sample

variable {Γ : Type*} [Fintype Γ] {dist : Γ → ℝ} {sides : Γ → Finset (Finset X)}

/-- The class of a gene tree: the alternative it displays, or else `0`. -/
private def lab (sides : Γ → Finset (Finset X)) (r₁ r₂ : QuartetTree X) (g : Γ) : Fin 3 :=
  if Displays (sides g) r₁ then 1 else if Displays (sides g) r₂ then 2 else 0

omit [Fintype Γ] in
private theorem lab_spec (hs : DisplaysOne dist sides) {r₁ r₂ : QuartetTree X} (hne : r₁ ≠ r₂)
    (ht : r₁.taxa = r₂.taxa) {g : Γ} (hg : dist g ≠ 0) :
    (lab sides r₁ r₂ g = 1 ↔ Displays (sides g) r₁) ∧
      (lab sides r₁ r₂ g = 2 ↔ Displays (sides g) r₂) := by
  have hboth : ¬ (Displays (sides g) r₁ ∧ Displays (sides g) r₂) := by
    rintro ⟨h₁, h₂⟩
    obtain ⟨t, _, huniq⟩ := hs g hg r₁.taxa r₁.card_taxa
    exact hne ((huniq r₁ ⟨QuartetTests.mem_treesOn_taxa r₁, h₁⟩).trans
      (huniq r₂ ⟨by simp [treesOn, ht], h₂⟩).symm)
  unfold lab
  by_cases h₁ : Displays (sides g) r₁ <;> by_cases h₂ : Displays (sides g) r₂
  · exact absurd ⟨h₁, h₂⟩ hboth
  · simp [h₁, h₂]
  · simp [h₁, h₂]
  · simp [h₁, h₂]

omit [Fintype Γ] in
private theorem count_lab (hs : DisplaysOne dist sides) {r₁ r₂ : QuartetTree X} (hne : r₁ ≠ r₂)
    (ht : r₁.taxa = r₂.taxa) {n : ℕ} {ω : Fin n → Γ} (hω : ∏ i, dist (ω i) ≠ 0) :
    quartetCount sides ω r₁ = count (fun i ↦ lab sides r₁ r₂ (ω i)) 1 ∧
      quartetCount sides ω r₂ = count (fun i ↦ lab sides r₁ r₂ (ω i)) 2 := by
  have hpos : ∀ i, dist (ω i) ≠ 0 := fun i => Finset.prod_ne_zero_iff.1 hω i (Finset.mem_univ i)
  unfold quartetCount count
  refine ⟨?_, ?_⟩ <;> congr 2 <;> ext i <;> simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  · exact (lab_spec hs hne ht (hpos i)).1.symm
  · exact (lab_spec hs hne ht (hpos i)).2.symm

private theorem pushDist_lab (hd : IsDist dist) (hs : DisplaysOne dist sides) {r₁ r₂ : QuartetTree X}
    (hne : r₁ ≠ r₂) (ht : r₁.taxa = r₂.taxa)
    (heq : displayCF dist sides r₁ = displayCF dist sides r₂) :
    pushDist dist (lab sides r₁ r₂) = cutPoint (3 * displayCF dist sides r₁) := by
  have h₁ : pushDist dist (lab sides r₁ r₂) 1 = displayCF dist sides r₁ := by
    unfold pushDist displayCF
    refine Finset.sum_congr rfl fun g _ => ?_
    by_cases hg : dist g = 0
    · simp [hg]
    · simp only [(lab_spec hs hne ht hg).1]
  have h₂ : pushDist dist (lab sides r₁ r₂) 2 = displayCF dist sides r₂ := by
    unfold pushDist displayCF
    refine Finset.sum_congr rfl fun g _ => ?_
    by_cases hg : dist g = 0
    · simp [hg]
    · simp only [(lab_spec hs hne ht hg).2]
  have hsum := (pushDist_isDist hd (lab sides r₁ r₂)).2
  rw [Fin.sum_univ_three, h₁, h₂, ← heq] at hsum
  funext i
  fin_cases i
  · change pushDist dist (lab sides r₁ r₂) 0 = 1 - 2 * (3 * displayCF dist sides r₁) / 3
    linarith
  · change pushDist dist (lab sides r₁ r₂) 1 = 3 * displayCF dist sides r₁ / 3
    rw [h₁]
    ring
  · change pushDist dist (lab sides r₁ r₂) 2 = 3 * displayCF dist sides r₁ / 3
    rw [h₂, ← heq]
    ring

/-- Under the null of the line, with positive probabilities, the p-value of the line is asymptotically
uniform, at the centroid too: the centroid is not a boundary point of the line, unlike that of the T1
null (E13). -/
theorem linePValue_asymptoticallyUniform (hd : IsDist dist) (hs : DisplaysOne dist sides)
    {s : QuartetTree X} (heq : LineNull (displayCF dist sides) s)
    (hpos : ∀ r ∈ treesOn s.taxa, 0 < displayCF dist sides r) :
    AsymptoticallyUniform dist fun _ ω => linePValue (quartetCount sides ω) s := by
  obtain ⟨r₁, r₂, hne, hr⟩ := QuartetTree.exists_alternatives s
  have hmem₁ : r₁ ∈ s.alternatives := by rw [hr]; simp
  have hmem₂ : r₂ ∈ s.alternatives := by rw [hr]; simp
  have ht : r₁.taxa = r₂.taxa :=
    (QuartetTree.mem_alternatives.1 hmem₁).1.trans (QuartetTree.mem_alternatives.1 hmem₂).1.symm
  have heq' := heq r₁ hmem₁ r₂ hmem₂
  have hsum := sum_displayCF_treesOn hd hs s.card_taxa
  rw [← Finset.add_sum_erase _ _ (QuartetTests.mem_treesOn_taxa s), ← s.alternatives_eq, hr,
    Finset.sum_pair hne, ← heq'] at hsum
  have h₀ := hpos s (QuartetTests.mem_treesOn_taxa s)
  have h₁ := hpos r₁ (mem_treesOn_taxa_of_mem_alternatives hmem₁)
  have hφ : 0 < 3 * displayCF dist sides r₁ ∧ 3 * displayCF dist sides r₁ < 3 / 2 := by
    constructor <;> linarith
  have hp := pushDist_lab hd hs hne ht heq'
  intro x hx0 hx1
  have := tendsto_line hφ hx0 hx1
  rw [← hp] at this
  refine this.congr fun n ↦ ?_
  rw [← iidProb_comp_label (lab sides r₁ r₂) n fun η ↦
    chiSqOneTail (lineS (count η 1) (count η 2)) ≤ x]
  unfold iidProb
  refine Finset.sum_congr rfl fun ω _ ↦ ?_
  by_cases hω : ∏ i, dist (ω i) = 0
  · simp [hω]
  · obtain ⟨c₁, c₂⟩ := count_lab hs hne ht hω
    have hstat : lineStat (quartetCount sides ω) s =
        lineS (count (fun i ↦ lab sides r₁ r₂ (ω i)) 1) (count (fun i ↦ lab sides r₁ r₂ (ω i)) 2) := by
      unfold lineStat lineS
      rw [hr, Finset.sum_pair hne, Finset.sum_pair hne, c₁, c₂]
    simp only [linePValue, hstat]

/-- Under the alternative of the line, its statistic grows faster than any `b_n = o(n)`, so its p-value
is eventually below `exp(-b_n/2)`. -/
theorem linePValue_growth (hd : IsDist dist) {s : QuartetTree X}
    (h : ¬ LineNull (displayCF dist sides) s) {b : ℕ → ℝ}
    (hb : Tendsto (fun n => b n / n) atTop (𝓝 0)) :
    Tendsto (fun n => iidProb dist n fun ω =>
      linePValue (quartetCount sides ω) s < Real.exp (-(b n) / 2)) atTop (𝓝 1) := by
  unfold LineNull at h
  push Not at h
  obtain ⟨r, hr, r', hr', hne⟩ := h
  have hline : 0 < lineStat (displayCF dist sides) s :=
    lineStat_pos _ (displayCF_nonneg hd) s ⟨r, hr, r', hr', hne⟩
  set d := lineStat (displayCF dist sides) s / 2 with hd_def
  have hd0 : 0 < d := by positivity
  have hF : ∀ᶠ x in 𝓝 (displayCF dist sides), d < lineStat x s :=
    (continuous_lineStat s).continuousAt.tendsto.eventually_const_lt (by linarith)
  refine tendsto_iidProb_of_imp hd ?_ (tendsto_iidProb_freq hd hF)
  filter_upwards [hb.eventually (gt_mem_nhds hd0), eventually_gt_atTop 0] with n h₁ hn ω hω
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  rw [div_lt_iff₀ hn'] at h₁
  have hc : quartetCount sides ω = fun r => (n : ℝ) * (quartetCount sides ω r / n) := by
    funext r
    field_simp
  have hstat : (n : ℝ) * d < lineStat (quartetCount sides ω) s := by
    rw [hc, lineStat_const_mul hn'.ne']
    exact mul_lt_mul_of_pos_left hω hn'
  have hnn := lineStat_nonneg (quartetCount sides ω) (quartetCount_nonneg ω) s
  calc linePValue (quartetCount sides ω) s
      ≤ chiSqTwoTail (lineStat (quartetCount sides ω) s) := chiSqOneTail_le_chiSqTwoTail hnn
    _ < _ := Real.exp_lt_exp.2 (by linarith)

end Sample

/-- The output of the algorithm with the T1 test replaced by the test of the line. Step 3 is the same. -/
def ectoblobLine (o : ECToBlobOptions) (α β : ℝ) (c : QuartetTree X → ℝ) (T₀ : Finset (Finset X)) :
    Finset (Finset X) :=
  outputBy o.rule α (edgeTestP o (linePValue c) T₀) (treeTestP o (linePValue c))
    (afterStar o β c T₀)

variable {V E : Type*}

/-- The two implications of Assumption 1 with no assumption on anomalies: a trivial 4-blob gives
(5.1), and a cut split gives the line. -/
structure CutLineForward (N : RootedNetwork V E X) (p : QuartetTree X → ℝ) : Prop where
  star : ∀ q : Finset X, q.card = 4 → HasTrivialFourBlob N q → IsUniformOn p q
  line : ∀ s : QuartetTree X, InducedCutSplit N s → LineNull p s

/-- The two converse implications, which hold at generic parameters. -/
structure CutLineConverse (N : RootedNetwork V E X) (p : QuartetTree X → ℝ) : Prop where
  star : ∀ q : Finset X, q.card = 4 → ¬ HasTrivialFourBlob N q → ¬ IsUniformOn p q
  line : ∀ s : QuartetTree X, ¬ InducedCutSplit N s → ¬ HasTrivialFourBlob N s.taxa → ¬ LineNull p s

/-- The null of the line at a quartet tree holds exactly when it is a cut split of its induced network,
or this network has a trivial 4-blob. -/
theorem lineNull_iff {N : RootedNetwork V E X} {p : QuartetTree X → ℝ} (h₁ : CutLineForward N p)
    (h₂ : CutLineConverse N p) (s : QuartetTree X) : LineNull p s ↔ IsNullQuartet N s := by
  constructor
  · intro hn
    by_contra hcon
    unfold IsNullQuartet at hcon
    push Not at hcon
    exact h₂.line s hcon.1 hcon.2 hn
  · rintro (h | h)
    · exact h₁.line s h
    · have hu := h₁.star _ s.card_taxa h
      intro r hr r' hr'
      rw [hu r (mem_treesOn_taxa_of_mem_alternatives hr),
        hu r' (mem_treesOn_taxa_of_mem_alternatives hr')]

section Tests

universe w

variable {X : Type w} [Fintype X] [DecidableEq X] {dist : BinaryGeneTree X → ℝ}

/-- The bounds on the p-values of the quartets in `Q` under the null of the line: Lemma 8.1, which
now applies to all of them. -/
theorem exists_delta_line (hd : IsDist dist) (hpos : ∀ r, 0 < displayCF dist Subtype.val r)
    (Q : Finset (QuartetTree X)) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ δ < 1 / 2 ∧ ∀ᶠ n : ℕ in atTop, 1 - ε < iidProb dist n fun ω =>
      ∀ s ∈ Q, LineNull (displayCF dist Subtype.val) s →
        δ ≤ linePValue (quartetCount Subtype.val ω) s ∧
          linePValue (quartetCount Subtype.val ω) s ≤ 1 - δ := by
  let ι₀ := {s : QuartetTree X // s ∈ Q ∧ LineNull (displayCF dist Subtype.val) s}
  let fam : ι₀ → (n : ℕ) → (Fin n → BinaryGeneTree X) → ℝ :=
    fun s _ ω => linePValue (quartetCount Subtype.val ω) s.1
  obtain ⟨δ, h0, h1, h⟩ := lemma8_1.{w, w} (Fintype.card ι₀ + 1) (by omega) hε
  obtain ⟨M, hM⟩ := h dist fam hd (by omega) (fun s _ _ => linePValue_mem _ _)
    (fun s => linePValue_asymptoticallyUniform hd (displaysOne_binaryGeneTree dist) s.2.2
      fun r _ => hpos r)
  refine ⟨δ, h0, h1, ?_⟩
  filter_upwards [eventually_gt_atTop M] with n hn
  refine (hM n hn).trans_le (iidProb_mono hd fun ω hω s hs hu => ?_)
  exact hω ⟨s, hs, hu⟩

/-- The test of the line at a set `Q` of quartets is right with probability `> 1 - ε` for large `n`,
at a level `τ_n → 0` with `log τ_n = o(n)`. -/
theorem eventually_line_correct (hd : IsDist dist) (m : TestCorrection)
    (hpos : ∀ r, 0 < displayCF dist Subtype.val r) {τ : ℕ → ℝ} (hτ : Tendsto τ atTop (𝓝[>] 0))
    (hlog : Tendsto (fun n : ℕ => Real.log (τ n) / n) atTop (𝓝 0))
    {K : ℕ} (Q : Finset (QuartetTree X)) (hK : Q.card ≤ K) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, 1 - ε < iidProb dist n fun ω =>
      TestCorrect (LineNull (displayCF dist Subtype.val)) Q (τ n)
        (combineP m (Q.val.map fun s => linePValue (quartetCount Subtype.val ω) s)) :=
  eventually_testCorrect hd m hτ hlog Q hK (LineNull (displayCF dist Subtype.val))
    (fun s _ ω => linePValue (quartetCount Subtype.val ω) s) (fun s _ _ => linePValue_mem _ s)
    (fun ε' hε' => by
      obtain ⟨δ, h0, h1, hev⟩ := exists_delta_line hd hpos Q hε'
      refine ⟨δ, h0, h1, ?_⟩
      filter_upwards [hev] with n hn
      refine hn.trans_le (iidProb_mono hd fun ω hω s hs hu => ?_)
      exact ⟨(hω s hs hu).1, fun _ => (hω s hs hu).2⟩)
    (fun _ _ hn _ hb => linePValue_growth hd hn hb) hε

/-- All tests of the variant come out right with probability `> 1 - ε` for large `n`. -/
theorem eventually_line_all (hd : IsDist dist) (o : ECToBlobOptions)
    (hpos : ∀ r, 0 < displayCF dist Subtype.val r) {T₀ : Finset (Finset X)}
    (hT₀ : IsUnrootedTree T₀) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, 1 - ε < iidProb dist n fun ω =>
      (∀ T ⊆ T₀, ∀ A ∈ internalSides T, TestCorrect (LineNull (displayCF dist Subtype.val))
        (edgeQuartets o T₀ T A) (alphaSeq n)
        (edgeTestP o (linePValue (quartetCount Subtype.val ω)) T₀ T A)) ∧
      ∀ T ⊆ T₀, TestCorrect (LineNull (displayCF dist Subtype.val))
        (Finset.univ.filter fun s => Displays T s) (alphaSeq n)
        (treeTestP o (linePValue (quartetCount Subtype.val ω)) T) := by
  let tests := (T₀.powerset.sigma fun T => internalSides T).disjSum T₀.powerset
  let quartets : (Σ _ : Finset (Finset X), Finset X) ⊕ Finset (Finset X) →
      Finset (QuartetTree X) :=
    Sum.elim (fun i => edgeQuartets o T₀ i.1 i.2) fun T => Finset.univ.filter fun s => Displays T s
  have hK : ∀ i ∈ tests, (quartets i).card ≤ (Fintype.card X).choose 4 := by
    rintro (⟨T, A⟩ | T) hi
    · obtain ⟨hT, hA⟩ := Finset.mem_sigma.1 (Finset.inl_mem_disjSum.1 hi)
      exact card_edgeQuartets_le hT₀ (Finset.mem_powerset.1 hT) (Finset.mem_filter.1 hA).1
    · exact card_displays_le hT₀ (Finset.mem_powerset.1 (Finset.inr_mem_disjSum.1 hi))
  have hall := eventually_forall_mem hd tests (fun i n ω => TestCorrect
      (LineNull (displayCF dist Subtype.val)) (quartets i) (alphaSeq n)
      (combineP o.testCo ((quartets i).val.map fun s =>
        linePValue (quartetCount Subtype.val ω) s)))
    hε fun i hi _ hε' => eventually_line_correct hd o.testCo hpos
      (tendsto_nhdsWithin_iff.2 ⟨tendsto_alphaSeq, eventually_alphaSeq_pos⟩)
      tendsto_log_chiSqOneTail_log (quartets i) (hK i hi) hε'
  filter_upwards [hall] with n hn
  refine hn.trans_le (iidProb_mono hd fun ω hω => ⟨fun T hT A hA => ?_, fun T hT => ?_⟩)
  · exact hω (Sum.inl ⟨T, A⟩) (Finset.inl_mem_disjSum.2
      (Finset.mem_sigma.2 ⟨Finset.mem_powerset.2 hT, hA⟩))
  · exact hω (Sum.inr T) (Finset.inr_mem_disjSum.2 (Finset.mem_powerset.2 hT))

/-- The variant tends to the limit tree of `Coarsening.limitTree`, on an arbitrary tree `T₀`, with no
assumption on anomalies. The sequences are those of Theorem 8.2. -/
theorem tendsto_ectoblobLine_limitTree {V E : Type*} (N : RootedNetwork V E X)
    (hN : N.IsPhylogenetic) (dist : BinaryGeneTree X → ℝ) (hd : IsDist dist)
    (h₁ : CutLineForward N (displayCF dist Subtype.val))
    (h₂ : CutLineConverse N (displayCF dist Subtype.val))
    (hpos : ∀ r, 0 < displayCF dist Subtype.val r) (T₀ : Finset (Finset X))
    (hT₀ : IsUnrootedTree T₀) (o : ECToBlobOptions) :
    Tendsto (fun n => iidProb dist n fun ω =>
      ectoblobLine o (alphaSeq n) (betaSeq n) (quartetCount Subtype.val ω) T₀ = limitTree N T₀)
      atTop (𝓝 1) := by
  refine tendsto_order.2 ⟨fun a ha => ?_, fun a ha => ?_⟩
  · have hε : 0 < (1 - a) / 2 := by linarith
    have hS := eventually_forall_mem hd (internalSides T₀)
      (fun A n ω => TestCorrect
        (fun s => IsUniformOn (displayCF dist Subtype.val) s.taxa) (multipartitionQuartets T₀ A)
        (betaSeq n) (edgeStarP o (quartetCount Subtype.val ω) T₀ A))
      hε fun A hA _ hε' => eventually_star_correct hd o.starTest o.testCo _
        (card_multipartitionQuartets_le hT₀ (Finset.mem_filter.1 hA).1) hε'
    filter_upwards [hS, eventually_line_all hd o hpos hT₀ hε] with n hnS hnL
    have hand := iidProb_and_gt hd n _ _ hnS hnL
    refine (by linarith : a ≤ 1 - (1 - a)).trans_lt (hand.trans_le (iidProb_mono hd fun ω hω => ?_))
    have R : CoarseRun N (displayCF dist Subtype.val)
        (linePValue (quartetCount Subtype.val ω)) (LineNull (displayCF dist Subtype.val)) T₀ o
        (alphaSeq n) (betaSeq n) (quartetCount Subtype.val ω) :=
      ⟨hN, hT₀, lineNull_iff h₁ h₂, fun s => ⟨fun hu => by
          by_contra hn
          exact h₂.star _ s.card_taxa hn hu, h₁.star _ s.card_taxa⟩, hω.1, hω.2.1, hω.2.2⟩
    exact R.outputBy_eq
  · exact Eventually.of_forall fun n => (iidProb_le_one hd n _).trans_lt ha

/-- **The T1 test replaced by the test of the line (§10).** ECToBlob's tests, with the test of the line
in the place of the T1 test, are consistent given a resolution `T₀` of the tree of blobs, under
`CutLineForward` and `CutLineConverse`, that is, with no assumption on anomalies. What the no-anomaly
assumption still gives is the resolution, as the paper says. -/
theorem consistency_line {V E : Type*} (N : RootedNetwork V E X)
    (hN : N.IsPhylogenetic) (dist : BinaryGeneTree X → ℝ) (hd : IsDist dist)
    (h₁ : CutLineForward N (displayCF dist Subtype.val))
    (h₂ : CutLineConverse N (displayCF dist Subtype.val))
    (hpos : ∀ r, 0 < displayCF dist Subtype.val r) (T₀ : Finset (Finset X))
    (hT₀ : IsResolutionOf T₀ (treeOfBlobs N)) (o : ECToBlobOptions) :
    Tendsto (fun n => iidProb dist n fun ω =>
      ectoblobLine o (alphaSeq n) (betaSeq n) (quartetCount Subtype.val ω) T₀ = treeOfBlobs N)
      atTop (𝓝 1) := by
  rw [← limitTree_eq_treeOfBlobs hN hT₀]
  exact tendsto_ectoblobLine_limitTree N hN dist hd h₁ h₂ hpos T₀ hT₀.1 o

end Tests

end LineTest

/-! ### The NMSC meets the two implications with no assumption on anomalies -/

section NMSC

variable {V E X : Type*} [Fintype X] [DecidableEq X] {N : RootedNetwork V E X}

/-- The converse implications, from the two generic facts: an induced network with a cut split has
concordance factors off the line of the other two quartet trees, and one with neither a cut split nor
a trivial 4-blob has three distinct concordance factors. -/
theorem cutLineConverse_of {p : QuartetTree X → ℝ}
    (hA : ∀ q : Finset X, q.card = 4 → ¬ IsTreelike N q → ¬ HasTrivialFourBlob N q →
      ∀ r ∈ treesOn q, ∀ r' ∈ treesOn q, r ≠ r' → p r ≠ p r')
    (hB : ∀ s, InducedCutSplit N s → ∀ r ∈ s.alternatives, p r ≠ p s) : CutLineConverse N p := by
  refine ⟨fun q hq htr hu => ?_, fun s hs htr hl => ?_⟩
  · by_cases hnt : IsTreelike N q
    · obtain ⟨s, hsq, hc⟩ := hnt
      obtain ⟨r, hr⟩ : s.alternatives.Nonempty := by
        rw [← Finset.card_pos, s.card_alternatives]
        omega
      have hq' : s.taxa = q := mem_treesOn.1 hsq
      refine hB s hc r hr ?_
      rw [hu s hsq, hu r (hq' ▸ mem_treesOn_taxa_of_mem_alternatives hr)]
    · obtain ⟨r, hr, r', hr', hne⟩ := Finset.one_lt_card.1
        (by rw [card_treesOn hq]; norm_num : 1 < (treesOn q).card)
      exact hA q hq hnt htr r hr r' hr' hne (by rw [hu r hr, hu r' hr'])
  · obtain ⟨r₁, r₂, hne, halts⟩ := QuartetTree.exists_alternatives s
    have hm₁ : r₁ ∈ s.alternatives := by rw [halts]; simp
    have hm₂ : r₂ ∈ s.alternatives := by rw [halts]; simp
    by_cases hnt : IsTreelike N s.taxa
    · -- the true topology is an alternative of `s`, and the third has another probability
      obtain ⟨t, htq, hc⟩ := hnt
      have hts : t ≠ s := by
        rintro rfl
        exact hs hc
      have hta : t ∈ s.alternatives := QuartetTree.mem_alternatives.2 ⟨mem_treesOn.1 htq, hts⟩
      rw [halts] at hta
      simp only [mem_insert, mem_singleton] at hta
      rcases hta with rfl | rfl
      · refine hB t hc r₂ (QuartetTree.mem_alternatives.2 ⟨?_, hne.symm⟩) (hl r₂ hm₂ t hm₁)
        rw [(QuartetTree.mem_alternatives.1 hm₂).1, (QuartetTree.mem_alternatives.1 hm₁).1]
      · refine hB t hc r₁ (QuartetTree.mem_alternatives.2 ⟨?_, hne⟩) (hl r₁ hm₁ t hm₂)
        rw [(QuartetTree.mem_alternatives.1 hm₁).1, (QuartetTree.mem_alternatives.1 hm₂).1]
    · exact hA s.taxa s.card_taxa hnt htr r₁ (mem_treesOn_taxa_of_mem_alternatives hm₁) r₂
        (mem_treesOn_taxa_of_mem_alternatives hm₂) hne (hl r₁ hm₁ r₂ hm₂)

omit [Fintype X] [DecidableEq X] in
/-- An arc dominating a taxon is not a hybrid arc. -/
theorem not_isHybridArc_of_dominates (hN : N.IsPhylogenetic) {e : E} {x : X}
    (h : N.Dominates e x) : ¬ N.IsHybridArc e := by
  intro hh
  obtain ⟨f, hf, hfe⟩ := Set.exists_ne_of_one_lt_ncard (s := {f | N.graph.target f = N.graph.target e})
    hh e
  have hft : N.graph.target f = N.graph.target e := hf
  refine h ?_
  have hsf : N.AvoidingReach e N.root (N.graph.source f) := by
    rcases FalseEdge.reaches_split e (hN.root_reaches (N.graph.source f)) with h₁ | ⟨_, h₁⟩
    · exact h₁
    · exact absurd (by rw [hft]; exact h₁) (FalseEdge.not_reaches_target_source hN f)
  have htf : N.AvoidingReach e N.root (N.graph.target e) := by
    rw [← hft]
    exact hsf.tail ⟨f, hfe, rfl, rfl⟩
  exact htf.trans (avoidingReach_of_target_reaches hN.acyclic .refl
    (Dominates.isBelow hN h))

variable [Fintype V] [Fintype E]

/-- The source's "sufficiently long cut edges" (Allman et al. 2023, line 143), on the face of the
measure of §5.1: the arc of a cut split is a tree arc, so it can have length `3` with the hybrid arcs of
length `0`. There, the concordance factor of the quartet tree differs from those of its alternatives. -/
theorem exists_face_ne (hN : N.IsPhylogenetic) {s r : QuartetTree X} (hs : InducedCutSplit N s)
    (hr : r ∈ s.alternatives) :
    ∃ θ₀, N.IsNormalized θ₀ ∧ (∀ e, N.IsHybridArc e → θ₀.length e = 0) ∧
      nmscCF N θ₀ 0 r ≠ nmscCF N θ₀ 0 s := by
  obtain ⟨e, he⟩ := (AllmanEtAl2023.inducedCutSplit_iff_exists_splitOffAt hN _).mp hs
  obtain ⟨g, hg⟩ : ∃ x, N.Dominates e x := by
    obtain ⟨P, hP, hsep⟩ := he
    obtain ⟨x, hx⟩ : P.Nonempty := Finset.card_pos.1 (by rw [s.card_of_mem hP]; omega)
    have := hsep.1 x (by simpa using hx)
    exact ⟨x, dominatesOff_empty_iff.1 this⟩
  let ℓ : E → ℝ := fun f => if f = e then 3 else 0
  have hℓ : ∀ f, 0 ≤ ℓ f := fun f => by
    simp only [ℓ]
    split_ifs <;> norm_num
  have hℓe : ℓ e = 3 := by simp [ℓ]
  refine ⟨AllmanEtAl2023.deletionMetric N ∅ ℓ,
    AllmanEtAl2023.isNormalized_deletionMetric hN (isDeletion_empty hN) ℓ,
    fun f hf => ?_, ?_⟩
  · have hfe : f ≠ e := by
      rintro rfl
      exact not_isHybridArc_of_dominates hN hg hf
    show ℓ f = 0
    simp [ℓ, hfe]
  · obtain ⟨hrt, hne⟩ := QuartetTree.mem_alternatives.1 hr
    have h₁ := AllmanEtAl2023.three_quarters_lt_nmscCF hN (isDeletion_empty hN) hℓ hℓe he
    have h₂ := NMSC.nmscCF_le_exp_of_splitOffAt (ρ := 0) hN
      (AllmanEtAl2023.isWeakMetric_deletionMetric hN (isDeletion_empty hN) hℓ)
      ⟨le_rfl, zero_le_one⟩ (isDeletion_empty hN) (fun f hf => absurd hf (Set.notMem_empty f)) he hrt hne
    rw [show (AllmanEtAl2023.deletionMetric N ∅ ℓ).length e = 3 from hℓe] at h₂
    have h₃ : Real.exp (-3) < 1 / 4 := by
      rw [Real.exp_neg, one_div]
      refine inv_strictAnti₀ (by norm_num) ?_
      have := Real.add_one_lt_exp (x := 3) (by norm_num)
      linarith
    intro heq
    rw [heq] at h₂
    linarith

/-- **Assumption 1 with no assumption on anomalies, for the NMSC.** Under the same degree condition as
Proposition 5.1, the forward implications hold at all parameters, and the converse implications outside
a null set of the measure of §5.1, with no hypothesis on anomalous quartets. -/
theorem cutLine_nmsc (hN : N.IsPhylogenetic) (hdeg : BlobDegreeAtMostThree N) :
    (∀ θ, N.IsMetric θ → CutLineForward N (nmscCF N θ 0)) ∧
    IsNullParams N {θ | N.IsMetric θ ∧ ¬ CutLineConverse N (nmscCF N θ 0)} := by
  have hρ : (0 : ℝ) ≤ 0 ∧ (0 : ℝ) ≤ 1 := ⟨le_rfl, zero_le_one⟩
  refine ⟨fun θ hθ => ⟨fun q hq ht => NMSC.trivial_uniform hN hθ hρ q hq ht,
    fun s hs => NMSC.cut_alternatives hN hθ hρ s hs⟩, ?_⟩
  have key : ∀ p : {p : (QuartetTree X × QuartetTree X) // InducedCutSplit N p.2 ∧
      p.1 ∈ p.2.alternatives},
      IsNullParams N {θ | nmscCF N θ 0 p.val.1 = nmscCF N θ 0 p.val.2} := by
    rintro ⟨p, hc, hr⟩
    obtain ⟨θ₀, hθ₀, hface, hne⟩ := exists_face_ne hN hc hr
    exact isNullParams_nmscCF_eq hθ₀ hface hne
  have hB := IsNullParams.iUnion key
  have hA := adaptedAllmanTheorem1 hN hdeg
  intro d hd
  refine MeasureTheory.measure_mono_null ?_ (MeasureTheory.measure_union_null (hA d hd) (hB d hd))
  rintro x ⟨hval, hθ, hnot⟩
  by_contra hcon
  simp only [Set.mem_union, not_or] at hcon
  obtain ⟨h₁, h₂⟩ := hcon
  apply hnot
  refine cutLineConverse_of (fun q hq hnt htr r hr r' hr' hne heq => h₁ ⟨hval, hθ, q, hq, hnt, htr, ?_⟩)
    (fun s hs r hr heq => h₂ ⟨hval, Set.mem_iUnion.2 ⟨⟨(r, s), hs, hr⟩, heq⟩⟩)
  intro hall
  exact hall r hr r' hr' hne heq

end NMSC

section Generic

universe u

variable {V E X : Type u} [Fintype V] [Fintype E] [Fintype X] [DecidableEq X]

omit [Fintype V] in
/-- `consistency_line` for a model meeting the two implications, outside a null set of parameters: for
all resolutions and all variants. -/
theorem consistency_line_generic (N : RootedNetwork V E X) (hN : N.IsPhylogenetic)
    (dist : MetricData E → BinaryGeneTree X → ℝ) (hd : ∀ θ, N.IsMetric θ → IsDist (dist θ))
    (h₁ : ∀ θ, N.IsMetric θ → CutLineForward N (displayCF (dist θ) Subtype.val))
    (h₂ : IsNullParams N {θ | N.IsMetric θ ∧ ¬ CutLineConverse N (displayCF (dist θ) Subtype.val)})
    (hpos : ∀ θ, N.IsMetric θ → ∀ r, 0 < displayCF (dist θ) Subtype.val r) :
    IsNullParams N {θ | N.IsMetric θ ∧ ¬ ∀ (T₀ : Finset (Finset X)) (o : ECToBlobOptions),
      IsResolutionOf T₀ (treeOfBlobs N) →
      Tendsto (fun n => iidProb (dist θ) n fun ω =>
        ectoblobLine o (alphaSeq n) (betaSeq n) (quartetCount Subtype.val ω) T₀ = treeOfBlobs N)
        atTop (𝓝 1)} := by
  intro d hd'
  refine MeasureTheory.measure_mono_null ?_ (h₂ d hd')
  rintro x ⟨hval, hθ, hnot⟩
  refine ⟨hval, hval, fun hconv => hnot fun T₀ o hT₀ => ?_⟩
  exact consistency_line N hN (dist _) (hd _ hval) (h₁ _ hval) hconv (hpos _ hval) T₀ hT₀ o

/-- **`consistency_line` for the NMSC.** On a network whose vertices in non-trivial blobs have degree two
or three, for a law of binary gene trees with the concordance factors of the NMSC, the variant is
consistent given a resolution, at all parameters outside a null set, with no assumption on anomalies.
-/
theorem consistency_line_nmsc (N : RootedNetwork V E X) (hN : N.IsPhylogenetic)
    (hdeg : BlobDegreeAtMostThree N) (dist : MetricData E → BinaryGeneTree X → ℝ)
    (hd : ∀ θ, N.IsMetric θ → IsDist (dist θ))
    (hcf : ∀ θ, N.IsMetric θ → displayCF (dist θ) Subtype.val = nmscCF N θ 0) :
    IsNullParams N {θ | N.IsMetric θ ∧ ¬ ∀ (T₀ : Finset (Finset X)) (o : ECToBlobOptions),
      IsResolutionOf T₀ (treeOfBlobs N) →
      Tendsto (fun n => iidProb (dist θ) n fun ω =>
        ectoblobLine o (alphaSeq n) (betaSeq n) (quartetCount Subtype.val ω) T₀ = treeOfBlobs N)
        atTop (𝓝 1)} := by
  obtain ⟨h₁, h₂⟩ := cutLine_nmsc hN hdeg
  refine consistency_line_generic N hN dist hd (fun θ hθ => ?_) ?_ (fun θ hθ r => ?_)
  · rw [hcf θ hθ]
    exact h₁ θ hθ
  · refine IsNullParams.mono h₂ ?_
    rintro θ ⟨hθ, hnot⟩
    rw [hcf θ hθ] at hnot
    exact ⟨hθ, hnot⟩
  · rw [hcf θ hθ]
    exact nmscCF_pos hN hθ ⟨le_rfl, zero_le_one⟩ r

end Generic

/-! ### A random starting tree: the union over the finitely many trees -/

section Random

variable {V E X : Type*} [Fintype X] [DecidableEq X] {dist : BinaryGeneTree X → ℝ}

/-- All the trees at once: with probability `> 1 - ε` for large `n`, the algorithm tends to the limit
tree on every possible tree. The union bound is over the finitely many unrooted trees on `X`. -/
theorem eventually_forall_trees {N : RootedNetwork V E X} (hN : N.IsPhylogenetic)
    (hd : IsDist dist) (h₁ : Assumption1Forward N (displayCF dist Subtype.val))
    (h₂ : Assumption1Converse N (displayCF dist Subtype.val)) (o : ECToBlobOptions)
    (hpos : (o.testCo = .cauchy ∨ o.testCo = .cbc) →
      ∀ s, IsT1Strict (displayCF dist Subtype.val) s →
        ∀ r ∈ s.alternatives, 0 < displayCF dist Subtype.val r) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, 1 - ε < iidProb dist n fun ω => ∀ T : Finset (Finset X), IsUnrootedTree T →
      ectoblob o (alphaSeq n) (betaSeq n) (quartetCount Subtype.val ω) T = limitTree N T := by
  have h := eventually_forall_mem hd (univ.filter fun T : Finset (Finset X) => IsUnrootedTree T)
    (fun T n ω => ectoblob o (alphaSeq n) (betaSeq n) (quartetCount Subtype.val ω) T = limitTree N T)
    hε fun T hT _ hε' => eventually_ectoblob_eq_limitTree hN hd h₁ h₂ o hpos (mem_filter.1 hT).2 hε'
  filter_upwards [h] with n hn
  exact hn.trans_le (iidProb_mono hd fun ω hω T hT => hω T (mem_filter.2 ⟨mem_univ _, hT⟩))

/-- **A random starting tree.** If `T₀` depends on the data in any way, and it is an unrooted tree with
probability tending to one, then the output is the limit tree of `T₀` with probability tending to
one. -/
theorem tendsto_random_limitTree (N : RootedNetwork V E X) (hN : N.IsPhylogenetic)
    (dist : BinaryGeneTree X → ℝ) (hd : IsDist dist)
    (h₁ : Assumption1Forward N (displayCF dist Subtype.val))
    (h₂ : Assumption1Converse N (displayCF dist Subtype.val)) (o : ECToBlobOptions)
    (hpos : (o.testCo = .cauchy ∨ o.testCo = .cbc) →
      ∀ s, IsT1Strict (displayCF dist Subtype.val) s →
        ∀ r ∈ s.alternatives, 0 < displayCF dist Subtype.val r)
    (T₀ : (n : ℕ) → (Fin n → BinaryGeneTree X) → Finset (Finset X))
    (hT : Tendsto (fun n => iidProb dist n fun ω => IsUnrootedTree (T₀ n ω)) atTop (𝓝 1)) :
    Tendsto (fun n => iidProb dist n fun ω =>
      ectoblob o (alphaSeq n) (betaSeq n) (quartetCount Subtype.val ω) (T₀ n ω) =
        limitTree N (T₀ n ω)) atTop (𝓝 1) := by
  refine tendsto_order.2 ⟨fun a ha => ?_, fun a ha => ?_⟩
  · have hε : 0 < 1 - a := by linarith
    filter_upwards [eventually_forall_trees hN hd h₁ h₂ o hpos (half_pos hε),
      hT.eventually_const_lt (show 1 - (1 - a) / 2 < 1 by linarith)] with n hn hnT
    have hand := iidProb_and_gt hd n _ _ hn hnT
    refine (by linarith : a ≤ 1 - (1 - a)).trans_lt (hand.trans_le (iidProb_mono hd fun ω hω => ?_))
    exact hω.1 _ hω.2
  · exact Eventually.of_forall fun n => (iidProb_le_one hd n _).trans_lt ha

/-- **Using the data twice (§10).** If `T₀` depends on the data in any way, and with probability
tending to one it is a resolution of the tree of blobs, then the output is the tree of blobs with
probability tending to one. This is consistency only: the p-values may not be valid given `T₀`. -/
theorem consistency_random_tree (N : RootedNetwork V E X) (hN : N.IsPhylogenetic)
    (dist : BinaryGeneTree X → ℝ) (hd : IsDist dist)
    (h₁ : Assumption1Forward N (displayCF dist Subtype.val))
    (h₂ : Assumption1Converse N (displayCF dist Subtype.val)) (o : ECToBlobOptions)
    (hpos : (o.testCo = .cauchy ∨ o.testCo = .cbc) →
      ∀ s, IsT1Strict (displayCF dist Subtype.val) s →
        ∀ r ∈ s.alternatives, 0 < displayCF dist Subtype.val r)
    (T₀ : (n : ℕ) → (Fin n → BinaryGeneTree X) → Finset (Finset X))
    (hT : Tendsto (fun n => iidProb dist n fun ω => IsResolutionOf (T₀ n ω) (treeOfBlobs N))
      atTop (𝓝 1)) :
    Tendsto (fun n => iidProb dist n fun ω =>
      ectoblob o (alphaSeq n) (betaSeq n) (quartetCount Subtype.val ω) (T₀ n ω) = treeOfBlobs N)
      atTop (𝓝 1) := by
  refine tendsto_order.2 ⟨fun a ha => ?_, fun a ha => ?_⟩
  · have hε : 0 < 1 - a := by linarith
    filter_upwards [eventually_forall_trees hN hd h₁ h₂ o hpos (half_pos hε),
      hT.eventually_const_lt (show 1 - (1 - a) / 2 < 1 by linarith)] with n hn hnT
    have hand := iidProb_and_gt hd n _ _ hn hnT
    refine (by linarith : a ≤ 1 - (1 - a)).trans_lt (hand.trans_le (iidProb_mono hd fun ω hω => ?_))
    rw [hω.1 _ hω.2.1]
    exact limitTree_eq_treeOfBlobs hN hω.2
  · exact Eventually.of_forall fun n => (iidProb_le_one hd n _).trans_lt ha

/-- A random tree in Remark 8.4 for binary networks. -/
theorem remark8_4_random (N : RootedNetwork V E X) (hN : N.IsPhylogenetic) (hb : N.IsBinary)
    (dist : BinaryGeneTree X → ℝ) (hd : IsDist dist)
    (h₁ : Assumption1Forward N (displayCF dist Subtype.val))
    (h₂ : Assumption1Converse N (displayCF dist Subtype.val)) (o : ECToBlobOptions)
    (hpos : (o.testCo = .cauchy ∨ o.testCo = .cbc) →
      ∀ s, IsT1Strict (displayCF dist Subtype.val) s →
        ∀ r ∈ s.alternatives, 0 < displayCF dist Subtype.val r)
    (T₀ : (n : ℕ) → (Fin n → BinaryGeneTree X) → Finset (Finset X))
    (hT : Tendsto (fun n => iidProb dist n fun ω => IsUnrootedTree (T₀ n ω)) atTop (𝓝 1)) :
    Tendsto (fun n => iidProb dist n fun ω =>
      ectoblob o (alphaSeq n) (betaSeq n) (quartetCount Subtype.val ω) (T₀ n ω) =
        T₀ n ω ∩ treeOfBlobs N) atTop (𝓝 1) := by
  refine tendsto_order.2 ⟨fun a ha => ?_, fun a ha => ?_⟩
  · have hε : 0 < 1 - a := by linarith
    filter_upwards [eventually_forall_trees hN hd h₁ h₂ o hpos (half_pos hε),
      hT.eventually_const_lt (show 1 - (1 - a) / 2 < 1 by linarith)] with n hn hnT
    have hand := iidProb_and_gt hd n _ _ hn hnT
    refine (by linarith : a ≤ 1 - (1 - a)).trans_lt (hand.trans_le (iidProb_mono hd fun ω hω => ?_))
    rw [hω.1 _ hω.2]
    exact limitTree_eq_inter_of_noTrivial hN hω.2
      fun _ hq => not_hasTrivialFourBlob_of_isBinary hN hb hq
  · exact Eventually.of_forall fun n => (iidProb_le_one hd n _).trans_lt ha

end Random

/-! ### Data splitting -/

section Splitting

/-- The last `m₂` of `m₁ + m₂` independent draws are `m₂` independent draws. -/
theorem iidProb_natAdd {Γ : Type*} [Fintype Γ] {dist : Γ → ℝ} (hd : IsDist dist) (m₁ m₂ : ℕ)
    (Ev : (Fin m₂ → Γ) → Prop) :
    iidProb dist (m₁ + m₂) (fun ω => Ev fun i => ω (Fin.natAdd m₁ i)) = iidProb dist m₂ Ev := by
  have h₁ := iidProb_true hd m₁
  unfold iidProb at h₁ ⊢
  simp only [ite_true] at h₁
  rw [← Fintype.sum_equiv (Fin.appendEquiv m₁ m₂) (fun p : (Fin m₁ → Γ) × (Fin m₂ → Γ) =>
    if Ev p.2 then (∏ i, dist (p.1 i)) * ∏ j, dist (p.2 j) else 0) _ ?_]
  · rw [Fintype.sum_prod_type]
    have hfac : ∀ a : Fin m₁ → Γ, (∑ b : Fin m₂ → Γ,
        if Ev b then (∏ i, dist (a i)) * ∏ j, dist (b j) else 0) =
        (∏ i, dist (a i)) * ∑ b : Fin m₂ → Γ, if Ev b then ∏ j, dist (b j) else 0 := by
      intro a
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun b _ => ?_
      split_ifs <;> simp
    simp only [hfac]
    rw [← Finset.sum_mul, h₁, one_mul]
  · rintro ⟨a, b⟩
    simp only [Fin.appendEquiv_apply, Fin.prod_univ_add, Fin.append_left, Fin.append_right]

variable {V E X : Type*} [Fintype X] [DecidableEq X] {dist : BinaryGeneTree X → ℝ}

/-- **Data splitting (§10).** Of `m₁ + m₂` genes, the quartet counts come from the last `m₂`, and the
levels are those for `m₂` genes, with `m₂ → ∞`. If `T₀`, which may depend on all the genes and in
particular on the first `m₁` of them, is a resolution of the tree of blobs with probability tending to
one, then the output is the tree of blobs with probability tending to one. -/
theorem consistency_data_splitting (N : RootedNetwork V E X) (hN : N.IsPhylogenetic)
    (dist : BinaryGeneTree X → ℝ) (hd : IsDist dist)
    (h₁ : Assumption1Forward N (displayCF dist Subtype.val))
    (h₂ : Assumption1Converse N (displayCF dist Subtype.val)) (o : ECToBlobOptions)
    (hpos : (o.testCo = .cauchy ∨ o.testCo = .cbc) →
      ∀ s, IsT1Strict (displayCF dist Subtype.val) s →
        ∀ r ∈ s.alternatives, 0 < displayCF dist Subtype.val r)
    (m₁ m₂ : ℕ → ℕ) (hm₂ : Tendsto m₂ atTop atTop)
    (T₀ : (n : ℕ) → (Fin (m₁ n + m₂ n) → BinaryGeneTree X) → Finset (Finset X))
    (hT : Tendsto (fun n => iidProb dist (m₁ n + m₂ n) fun ω =>
      IsResolutionOf (T₀ n ω) (treeOfBlobs N)) atTop (𝓝 1)) :
    Tendsto (fun n => iidProb dist (m₁ n + m₂ n) fun ω =>
      ectoblob o (alphaSeq (m₂ n)) (betaSeq (m₂ n))
        (quartetCount Subtype.val fun i => ω (Fin.natAdd (m₁ n) i)) (T₀ n ω) = treeOfBlobs N)
      atTop (𝓝 1) := by
  refine tendsto_order.2 ⟨fun a ha => ?_, fun a ha => ?_⟩
  · have hε : 0 < 1 - a := by linarith
    filter_upwards [hm₂.eventually (eventually_forall_trees hN hd h₁ h₂ o hpos (half_pos hε)),
      hT.eventually_const_lt (show 1 - (1 - a) / 2 < 1 by linarith)] with n hn hnT
    rw [← iidProb_natAdd hd (m₁ n) (m₂ n)] at hn
    have hand := iidProb_and_gt hd _ _ _ hn hnT
    refine (by linarith : a ≤ 1 - (1 - a)).trans_lt (hand.trans_le (iidProb_mono hd fun ω hω => ?_))
    rw [hω.1 _ hω.2.1]
    exact limitTree_eq_treeOfBlobs hN hω.2
  · exact Eventually.of_forall fun n => (iidProb_le_one hd _ _).trans_lt ha

end Splitting

/-! ### Combining the edge p-values -/

section EdgeCombination

variable {V E X : Type*} [Fintype X] [DecidableEq X] {N : RootedNetwork V E X}

/-- The overall p-value of a tree `T` obtained by combining its edge p-values, "the alternative of
combining the edge p-values" (lines 1412-1419). -/
def treeEdgeP (o : ECToBlobOptions) (c : QuartetTree X → ℝ) (T₀ T : Finset (Finset X)) : ℝ :=
  combineP o.testCo ((internalSides T).val.map (edgeT1P o c T₀ T))

/-- The output of the algorithm with these overall p-values. -/
def ectoblobEdge (o : ECToBlobOptions) (α β : ℝ) (c : QuartetTree X → ℝ) (T₀ : Finset (Finset X)) :
    Finset (Finset X) :=
  outputBy o.rule α (edgeT1P o c T₀) (treeEdgeP o c T₀) (afterStar o β c T₀)

/-- Combined p-values are in `[0, 1]`. -/
theorem combineP_mem (m : TestCorrection) {P : Multiset ℝ} (h : ∀ p ∈ P, 0 ≤ p ∧ p ≤ 1) :
    0 ≤ combineP m P ∧ combineP m P ≤ 1 := by
  unfold combineP
  split_ifs
  · exact ⟨zero_le_one, le_rfl⟩
  · have h0 : ∀ p ∈ P, 0 ≤ p := fun p hp => (h p hp).1
    have hpair : ∀ x ∈ ({bonP P, cauchyP P} : Multiset ℝ), 0 ≤ x := by
      intro x hx
      simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact bonP_nonneg h0
      · exact cauchyP_nonneg P
    cases m with
    | bon => exact ⟨bonP_nonneg h0, bonP_le_one P⟩
    | cauchy => exact ⟨cauchyP_nonneg P, cauchyP_le_one P⟩
    | bbc => exact ⟨bonP_nonneg hpair, bonP_le_one _⟩
    | cbc => exact ⟨cauchyP_nonneg _, cauchyP_le_one _⟩

/-- The Cauchy combination of values at most `D` is at most `D`. -/
theorem cauchyP_le_of_forall_le {P : Multiset ℝ} (hP : P ≠ 0) {D : ℝ} (hD₀ : 0 < D) (hD₁ : D < 1)
    (h : ∀ p ∈ P, 0 ≤ p ∧ p ≤ D) : cauchyP P ≤ D := by
  by_cases h0 : (0 : ℝ) ∈ P
  · rw [cauchyP, ite_eq_left h0]
    exact hD₀.le
  have h1 : (1 : ℝ) ∉ P := fun h1 => absurd (h 1 h1).2 (not_le.2 hD₁)
  rw [cauchyP, ite_eq_right h0, ite_eq_right h1]
  conv_rhs => rw [← cauchyInverse_cauchyTransform hD₀ hD₁]
  refine cauchyInverse_anti ?_
  have hk : (0 : ℝ) < Multiset.card P := by
    exact_mod_cast Multiset.card_pos.2 hP
  rw [le_div_iff₀ hk, mul_comm]
  have := Multiset.card_nsmul_le_sum (s := P.map cauchyTransform) (a := cauchyTransform D) (by
    intro y hy
    obtain ⟨p, hp, rfl⟩ := Multiset.mem_map.1 hy
    have hp₀ : 0 < p := lt_of_le_of_ne (h p hp).1 fun e => h0 (e ▸ hp)
    exact cauchyTransform_anti hp₀ (h p hp).2 hD₁)
  simpa using this

/-- Why the combination of edge p-values fails for CBC. A multiset with a `1` and no `0` has CBC
combination `1`, whatever the other values; and the Bonferroni p-value of an edge with `k` quartets
is `1` when all its p-values are at least `1/k`, so its CBC p-value is too. (E15 of the report.) -/
theorem combineP_cbc_eq_one {P : Multiset ℝ} (h1 : (1 : ℝ) ∈ P) (h : ∀ p ∈ P, 0 < p ∧ p ≤ 1) :
    combineP .cbc P = 1 := by
  have hP : P ≠ 0 := fun h' => by simp [h'] at h1
  have h0 : (0 : ℝ) ∉ P := fun h0 => lt_irrefl _ (h 0 h0).1
  have hc : cauchyP P = 1 := by
    rw [cauchyP, ite_eq_right h0, ite_eq_left h1]
  have hmin : 0 < minP P := (h _ (minP_mem hP fun p hp => (h p hp).2)).1
  have hk : (0 : ℝ) < Multiset.card P := by
    exact_mod_cast Multiset.card_pos.2 hP
  have hb : 0 < bonP P := lt_min one_pos (mul_pos hk hmin)
  unfold combineP cbcP
  rw [ite_eq_right hP]
  show cauchyP {bonP P, cauchyP P} = 1
  rw [cauchyP, ite_eq_right, ite_eq_left]
  · simp [hc, Multiset.insert_eq_cons]
  · simp [hc, hb.ne, Multiset.insert_eq_cons]

/-- On a table on which all tests come out right, with the edge tests also right at the finer level
`η` of `CombineBounds`, and with the edge p-values at most `1 - δ` for the Cauchy combinations, the limit
of the variant is the limit tree. -/
theorem isLimit_edge {p f : QuartetTree X → ℝ} {Null : QuartetTree X → Prop}
    {T₀ : Finset (Finset X)} {o : ECToBlobOptions} {α β : ℝ} {c : QuartetTree X → ℝ}
    (R : CoarseRun N p f Null T₀ o α β c)
    (hf : ∀ s, 0 ≤ f s ∧ f s ≤ 1) (hα : α < 1) {δ η : ℝ}
    (hcomb : CombineBounds o.testCo T₀.card δ α η)
    (hfine : ∀ T ⊆ T₀, ∀ A ∈ internalSides T, (∃ s ∈ edgeQuartets o T₀ T A, ¬ Null s) →
      edgeTestP o f T₀ T A < η)
    (hup : (o.testCo = .cauchy ∨ o.testCo = .cbc) → ∀ T ⊆ T₀, ∀ A ∈ internalSides T,
      edgeTestP o f T₀ T A ≤ 1 - δ) :
    IsLimit α (edgeTestP o f T₀)
      (fun T => combineP o.testCo ((internalSides T).val.map (edgeTestP o f T₀ T)))
      (afterStar o β c T₀) (limitTree N T₀) := by
  have hL := R.isLimit
  have hsub : afterStar o β c T₀ ⊆ T₀ := afterStar_subset
  have hmem : ∀ T A, 0 ≤ edgeTestP o f T₀ T A ∧ edgeTestP o f T₀ T A ≤ 1 := fun T A =>
    combineP_mem _ fun x hx => by
      obtain ⟨s, _, rfl⟩ := Multiset.mem_map.1 hx
      exact hf s
  have hP01 : ∀ T, ∀ x ∈ (internalSides T).val.map (edgeTestP o f T₀ T), 0 ≤ x ∧ x ≤ 1 := by
    intro T x hx
    obtain ⟨A, _, rfl⟩ := Multiset.mem_map.1 hx
    exact hmem T A
  refine ⟨hL.subset, hL.compl, hL.pendant, hL.split, hL.edge_gt, hL.edge_lt, ?_, ?_⟩
  · intro T hT
    by_cases hP : (internalSides T).val.map (edgeTestP o f T₀ T) = 0
    · simp only [combineP, hP, ite_true]
      exact hα
    · refine lt_of_lt_of_le ?_ (minP_le_combineP _ hP (hP01 T))
      obtain ⟨A, hA, hAeq⟩ := Multiset.mem_map.1 (minP_mem hP fun x hx => (hP01 T x hx).2)
      rw [← hAeq]
      exact hL.edge_gt T (hT.trans hL.subset) A hA (hT (mem_internalSides.1 hA).1)
  · intro T hT A hAi hA
    obtain ⟨hAT, h₂⟩ := mem_internalSides.1 hAi
    have hTT₀ := hT.trans hsub
    have hlt := hfine T hTT₀ A hAi (R.exists_not_null_edgeQuartets hTT₀ (hT hAT) h₂ hA)
    have hcard : Multiset.card ((internalSides T).val.map (edgeTestP o f T₀ T)) ≤ T₀.card := by
      rw [Multiset.card_map]
      exact Finset.card_le_card ((Finset.filter_subset _ T).trans hTT₀)
    refine hcomb.lt _ (hP01 T) hcard ⟨_, Multiset.mem_map_of_mem _ hAi, hlt⟩ fun hm x hx => ?_
    obtain ⟨B, hB, rfl⟩ := Multiset.mem_map.1 hx
    exact hup hm T hTT₀ B hB

variable {dist : BinaryGeneTree X → ℝ}

/-- **Combining the edge p-values (§10).** For the corrections `bon`, `bbc` and `cauchy`, the variant in
which the overall p-value combines the edge p-values tends to the limit tree, on an arbitrary tree `T₀`,
so to the tree of blobs on a resolution of it (`consistency_edge_combination`). For `cauchy`, the
hypothesis on the alternatives is that of Theorem 8.2.

For `cbc` this proof does not apply, and the variant is not consistent: the
Bonferroni p-value of a cut edge with two or more quartets is `1` with probability bounded below, so its
CBC p-value is `1`, and a CBC combination with a `1` is `1` whatever the other p-values
(`combineP_cbc_eq_one`), so a tree with a false edge and such a cut edge is not rejected. This is proved on one
law that meets Assumption 1, `ECToBlob.BinaryLaw.OnBinary.not_consistency_edge_combination_cbc`. In general, under the NMSC, it is a sketch. -/
theorem tendsto_ectoblobEdge_limitTree (N : RootedNetwork V E X) (hN : N.IsPhylogenetic)
    (dist : BinaryGeneTree X → ℝ) (hd : IsDist dist)
    (h₁ : Assumption1Forward N (displayCF dist Subtype.val))
    (h₂ : Assumption1Converse N (displayCF dist Subtype.val)) (T₀ : Finset (Finset X))
    (hT₀ : IsUnrootedTree T₀) (o : ECToBlobOptions) (hm : o.testCo ≠ .cbc)
    (hpos : (o.testCo = .cauchy ∨ o.testCo = .cbc) →
      ∀ s, IsT1Strict (displayCF dist Subtype.val) s →
        ∀ r ∈ s.alternatives, 0 < displayCF dist Subtype.val r) :
    Tendsto (fun n => iidProb dist n fun ω =>
      ectoblobEdge o (alphaSeq n) (betaSeq n) (quartetCount Subtype.val ω) T₀ = limitTree N T₀)
      atTop (𝓝 1) := by
  have hone := displaysOne_binaryGeneTree dist
  refine tendsto_order.2 ⟨fun a ha => ?_, fun a ha => ?_⟩
  swap
  · exact Eventually.of_forall fun n => (iidProb_le_one hd n _).trans_lt ha
  have hε : 0 < 1 - a := by linarith
  -- the individual p-values under the null
  obtain ⟨δ, hδ₀, hδ₁, hnull⟩ := exists_delta_t1 hd o.testCo hpos
    (Finset.univ : Finset (QuartetTree X)) (ε := (1 - a) / 2 / 2 / 2) (by positivity)
  -- the combination, and the finer level
  obtain ⟨c₀, hc₀pos, hcomb⟩ := exists_combineBounds o.testCo T₀.card hδ₀ (by linarith)
  have hα₀ : Tendsto alphaSeq atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.2 ⟨tendsto_alphaSeq, eventually_alphaSeq_pos⟩
  have hτ : Tendsto (fun n => c₀ * alphaSeq n) atTop (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · have := tendsto_alphaSeq.const_mul c₀
      rwa [mul_zero] at this
    · filter_upwards [eventually_alphaSeq_pos] with n hn
      exact mul_pos hc₀pos hn
  have hlog : Tendsto (fun n : ℕ => Real.log (c₀ * alphaSeq n) / n) atTop (𝓝 0) := by
    have h₁ : Tendsto (fun n : ℕ => Real.log c₀ / (n : ℝ)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
    have h₂ := h₁.add tendsto_log_chiSqOneTail_log
    rw [add_zero] at h₂
    refine h₂.congr' ?_
    filter_upwards [eventually_alphaSeq_pos] with n hn
    rw [Real.log_mul hc₀pos.ne' hn.ne', add_div]
    rfl
  have hfine := eventually_forall_mem hd (T₀.powerset.sigma fun T => internalSides T)
    (fun i n ω => TestCorrect (IsT1Null (displayCF dist Subtype.val)) (edgeQuartets o T₀ i.1 i.2)
      (c₀ * alphaSeq n) (edgeT1P o (quartetCount Subtype.val ω) T₀ i.1 i.2))
    (half_pos hε) fun i hi _ hε' => eventually_testCorrect hd o.testCo hτ hlog _
      (card_edgeQuartets_le hT₀ (Finset.mem_powerset.1 (Finset.mem_sigma.1 hi).1)
        (Finset.mem_filter.1 (Finset.mem_sigma.1 hi).2).1)
      (IsT1Null (displayCF dist Subtype.val))
      (fun s _ ω => t1PValue (quartetCount Subtype.val ω) s) (fun s _ _ => t1PValue_mem _ s)
      (fun _ hε'' => exists_delta_t1 hd o.testCo hpos _ hε'')
      (fun _ _ hn _ hb => t1PValue_growth hd hone hn hb) hε'
  -- the individual p-values off the null are at most `1 - δ`
  have hδ' : 0 < 1 - δ := by linarith
  have hoff := eventually_forall_mem hd
    (Finset.univ.filter fun s : QuartetTree X => ¬ IsT1Null (displayCF dist Subtype.val) s)
    (fun s n ω => t1PValue (quartetCount Subtype.val ω) s < Real.exp (-(-2 * Real.log (1 - δ)) / 2))
    (ε := (1 - a) / 2 / 2 / 2) (by positivity) fun s hs ε' hε' =>
      (t1PValue_growth hd hone (Finset.mem_filter.1 hs).2 (b := fun _ => -2 * Real.log (1 - δ))
        (tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop)).eventually_const_lt
          (by linarith)
  filter_upwards [hfine, eventually_tests_correct hd o hpos hT₀ (ε := (1 - a) / 2 / 2)
    (by positivity), hnull, hoff, tendsto_alphaSeq.eventually_lt_const one_pos,
    hα₀.eventually hcomb] with n hn₁ hn₂ hn₃ hn₄ hα hc
  have hand₃ := iidProb_and_gt hd n _ _ hn₃ hn₄
  have hand₂ := iidProb_and_gt hd n _ _ hn₂ hand₃
  have hand := iidProb_and_gt hd n _ _ hn₁ hand₂
  refine (by linarith : a ≤ 1 - (1 - a)).trans_lt (hand.trans_le (iidProb_mono hd fun ω hω => ?_))
  obtain ⟨hω₁, hω₂, hω₃, hω₄⟩ := hω
  have R : CoarseRun N (displayCF dist Subtype.val)
      (t1PValue (quartetCount Subtype.val ω)) (IsT1Null (displayCF dist Subtype.val)) T₀ o
      (alphaSeq n) (betaSeq n) (quartetCount Subtype.val ω) :=
    ⟨hN, hT₀, t1Null_iff h₁ h₂ fun s => sum_displayCF_binaryGeneTree hd s.card_taxa,
      uniform_iff h₁ h₂, hω₂.1, hω₂.2.1, hω₂.2.2⟩
  -- the edge p-values are at most `1 - δ`, for the Cauchy combination
  have hexp : Real.exp (-(-2 * Real.log (1 - δ)) / 2) = 1 - δ := by
    rw [show -(-2 * Real.log (1 - δ)) / 2 = Real.log (1 - δ) by ring, Real.exp_log hδ']
  have hup : (o.testCo = .cauchy ∨ o.testCo = .cbc) → ∀ T ⊆ T₀, ∀ A ∈ internalSides T,
      edgeTestP o (t1PValue (quartetCount Subtype.val ω)) T₀ T A ≤ 1 - δ := by
    intro hco T hT A hA
    have hcau : o.testCo = .cauchy := hco.resolve_right hm
    obtain ⟨hAT, h₂', h₃'⟩ := mem_internalSides.1 hA
    obtain ⟨s₀, hs₀⟩ := FalseEdge.exists_mem_multipartitionQuartets (isSplitFamily_of_internal hT₀ h₂')
      h₂' h₃'
    have hne : (edgeQuartets o T₀ T A).val.map (t1PValue (quartetCount Subtype.val ω)) ≠ 0 := by
      intro h
      have hmem : t1PValue (quartetCount Subtype.val ω) s₀ ∈
          (edgeQuartets o T₀ T A).val.map (t1PValue (quartetCount Subtype.val ω)) :=
        Multiset.mem_map_of_mem _ (multipartitionQuartets_subset_edgeQuartets hT A hs₀)
      simp [h] at hmem
    unfold edgeTestP combineP
    rw [ite_eq_right hne, hcau]
    refine cauchyP_le_of_forall_le hne hδ' (by linarith) fun x hx => ?_
    obtain ⟨s, _, rfl⟩ := Multiset.mem_map.1 hx
    refine ⟨(t1PValue_mem _ s).1, ?_⟩
    by_cases hs : IsT1Null (displayCF dist Subtype.val) s
    · exact (hω₃ s (Finset.mem_univ s) hs).2 (Or.inl hcau)
    · have := hω₄ s (Finset.mem_filter.2 ⟨Finset.mem_univ s, hs⟩)
      rw [hexp] at this
      exact this.le
  exact (isLimit_edge R (t1PValue_mem _) hα hc (fun T hT A hA hex =>
    (hω₁ ⟨T, A⟩ (Finset.mem_sigma.2 ⟨Finset.mem_powerset.2 hT, hA⟩)).2 hex) hup).outputBy_eq o.rule

/-- The variant on a resolution of the tree of blobs. -/
theorem consistency_edge_combination (N : RootedNetwork V E X) (hN : N.IsPhylogenetic)
    (dist : BinaryGeneTree X → ℝ) (hd : IsDist dist)
    (h₁ : Assumption1Forward N (displayCF dist Subtype.val))
    (h₂ : Assumption1Converse N (displayCF dist Subtype.val)) (T₀ : Finset (Finset X))
    (hT₀ : IsResolutionOf T₀ (treeOfBlobs N)) (o : ECToBlobOptions) (hm : o.testCo ≠ .cbc)
    (hpos : (o.testCo = .cauchy ∨ o.testCo = .cbc) →
      ∀ s, IsT1Strict (displayCF dist Subtype.val) s →
        ∀ r ∈ s.alternatives, 0 < displayCF dist Subtype.val r) :
    Tendsto (fun n => iidProb dist n fun ω =>
      ectoblobEdge o (alphaSeq n) (betaSeq n) (quartetCount Subtype.val ω) T₀ = treeOfBlobs N)
      atTop (𝓝 1) := by
  rw [← limitTree_eq_treeOfBlobs hN hT₀]
  exact tendsto_ectoblobEdge_limitTree N hN dist hd h₁ h₂ T₀ hT₀.1 o hm hpos

end EdgeCombination

end ECToBlob.Remarks
