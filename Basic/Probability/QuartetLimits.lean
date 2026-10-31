module

public import Basic.Probability.QuartetTails
public import Basic.Probability.Trinomial.Tests

/-!
# The quartet hypothesis tests: limits under the null

For a sample of `n` gene trees whose displayed quartet trees on a set of four taxa have the null
probabilities `p`, the p-values of the star test and the T1 test are asymptotically uniform, as ECToBlob §8
takes "from well-known properties of likelihood ratio tests" and Mitchell, Allman, Rhodes 2019; the T1 p-value
at its boundary stays away from `0` and `1`; and the cut test does not reject a strictly cut concordance
factor, as in TINNiK's proof of Theorem 4. These come from Mathlib's central limit theorem, through
`Basic/Probability/Trinomial/`.
-/

@[expose] public noncomputable section

open Phylogenetics Finset Filter Topology
open scoped Classical

namespace Phylogenetics.QuartetTests

variable {X : Type*} [Fintype X] [DecidableEq X] {Γ : Type*} [Fintype Γ]
variable {dist : Γ → ℝ} {sides : Γ → Finset (Finset X)}

/-! ### The statistics as functions of the three counts -/

open Trinomial

private theorem treesOn_taxa_eq {s r₁ r₂ : QuartetTree X} (h : s.alternatives = {r₁, r₂}) :
    treesOn s.taxa = {s, r₁, r₂} := by
  ext r
  have hr : r ∈ s.alternatives ↔ r.taxa = s.taxa ∧ r ≠ s := by simp [QuartetTree.alternatives]
  rw [h] at hr
  simp only [Finset.mem_insert, Finset.mem_singleton] at hr ⊢
  simp only [treesOn, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro ht
    by_cases hrs : r = s
    · exact Or.inl hrs
    · exact Or.inr (hr.2 ⟨ht, hrs⟩)
  · rintro (rfl | h')
    · rfl
    · exact (hr.1 h').1

private theorem alternatives_facts {s r₁ r₂ : QuartetTree X} (hne : r₁ ≠ r₂)
    (h : s.alternatives = {r₁, r₂}) :
    s ≠ r₁ ∧ s ≠ r₂ ∧ r₁.alternatives = {s, r₂} ∧ r₂.alternatives = {s, r₁} := by
  have hr : ∀ r, r ∈ s.alternatives ↔ r.taxa = s.taxa ∧ r ≠ s := by
    intro r
    simp [QuartetTree.alternatives]
  have h₁ := (hr r₁).1 (by rw [h]; simp)
  have h₂ := (hr r₂).1 (by rw [h]; simp)
  have hmem : ∀ r, r.taxa = s.taxa → r = s ∨ r = r₁ ∨ r = r₂ := by
    intro r ht
    by_cases hrs : r = s
    · exact Or.inl hrs
    · have := (hr r).2 ⟨ht, hrs⟩
      rw [h] at this
      simpa [hrs] using this
  refine ⟨h₁.2.symm, h₂.2.symm, ?_, ?_⟩
  · ext r
    simp only [QuartetTree.alternatives, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨ht, hrr⟩
      rcases hmem r (ht.trans h₁.1) with h' | h' | h'
      · exact Or.inl h'
      · exact absurd h' hrr
      · exact Or.inr h'
    · rintro (rfl | rfl)
      · exact ⟨h₁.1.symm, h₁.2.symm⟩
      · exact ⟨h₂.1.trans h₁.1.symm, hne.symm⟩
  · ext r
    simp only [QuartetTree.alternatives, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨ht, hrr⟩
      rcases hmem r (ht.trans h₂.1) with h' | h' | h'
      · exact Or.inl h'
      · exact Or.inr h'
      · exact absurd h' hrr
    · rintro (rfl | rfl)
      · exact ⟨h₂.1.symm, h₂.2.symm⟩
      · exact ⟨h₁.1.trans h₂.1.symm, hne⟩

private theorem lineStat_eq_lineS (c : QuartetTree X → ℝ) {s r₁ r₂ : QuartetTree X} (hne : r₁ ≠ r₂)
    (h : s.alternatives = {r₁, r₂}) : lineStat c s = lineS (c r₁) (c r₂) := by
  unfold lineStat lineS
  rw [h, Finset.sum_pair hne, Finset.sum_pair hne]

private theorem sum_treesOn (f : QuartetTree X → ℝ) {s r₁ r₂ : QuartetTree X} (hne : r₁ ≠ r₂)
    (h : s.alternatives = {r₁, r₂}) : ∑ r ∈ treesOn s.taxa, f r = f s + f r₁ + f r₂ := by
  obtain ⟨h₁, h₂, -, -⟩ := alternatives_facts hne h
  rw [treesOn_taxa_eq h, Finset.sum_insert (by simp [h₁, h₂]), Finset.sum_pair hne]
  ring

private theorem starStat_eq_starS (c : QuartetTree X → ℝ) {s r₁ r₂ : QuartetTree X} (hne : r₁ ≠ r₂)
    (h : s.alternatives = {r₁, r₂}) : starStat c s.taxa = starS (c s) (c r₁) (c r₂) := by
  unfold starStat starS
  rw [sum_treesOn _ hne h, sum_treesOn _ hne h]

private theorem pearsonStat_eq_pearsonS (c : QuartetTree X → ℝ) {s r₁ r₂ : QuartetTree X}
    (hne : r₁ ≠ r₂) (h : s.alternatives = {r₁, r₂}) :
    pearsonStat c s.taxa = pearsonS (c s) (c r₁) (c r₂) := by
  unfold pearsonStat pearsonS
  rw [sum_treesOn _ hne h, sum_treesOn _ hne h]

private theorem t1PValue_eq_t1PValueR (c : QuartetTree X → ℝ) {s r₁ r₂ : QuartetTree X}
    (hne : r₁ ≠ r₂) (h : s.alternatives = {r₁, r₂}) :
    t1PValue c s = t1PValueR (c s) (c r₁) (c r₂) := by
  unfold t1PValue t1PValueR t1Stat t1Phi
  rw [lineStat_eq_lineS c hne h, starStat_eq_starS c hne h, h, Finset.sum_pair hne, add_assoc]

private theorem cutStat_eq_cutS (c : QuartetTree X → ℝ) {s r₁ r₂ : QuartetTree X} (hne : r₁ ≠ r₂)
    (h : s.alternatives = {r₁, r₂}) : cutStat c s.taxa = cutS (c s) (c r₁) (c r₂) := by
  obtain ⟨h₁, h₂, ha₁, ha₂⟩ := alternatives_facts hne h
  have hT := treesOn_taxa_eq h
  have hs : s ∈ treesOn s.taxa := by rw [hT]; simp
  have hr₁ : r₁ ∈ treesOn s.taxa := by rw [hT]; simp
  have hr₂ : r₂ ∈ treesOn s.taxa := by rw [hT]; simp
  have e₀ := lineStat_eq_lineS c hne h
  have e₁ := lineStat_eq_lineS c h₂ ha₁
  have e₂ := lineStat_eq_lineS c h₁ ha₂
  unfold cutStat
  have : Nonempty {t // t ∈ treesOn s.taxa} := ⟨⟨s, hs⟩⟩
  refine le_antisymm ?_ ?_
  · unfold cutS
    refine le_min ?_ (le_min ?_ ?_)
    · rw [← e₀]
      exact ciInf_le (Set.finite_range _).bddBelow (⟨s, hs⟩ : {t // t ∈ treesOn s.taxa})
    · rw [← e₁]
      exact ciInf_le (Set.finite_range _).bddBelow (⟨r₁, hr₁⟩ : {t // t ∈ treesOn s.taxa})
    · rw [← e₂]
      exact ciInf_le (Set.finite_range _).bddBelow (⟨r₂, hr₂⟩ : {t // t ∈ treesOn s.taxa})
  · refine le_ciInf ?_
    rintro ⟨t, ht⟩
    rw [hT] at ht
    simp only [Finset.mem_insert, Finset.mem_singleton] at ht
    unfold cutS
    rcases ht with rfl | rfl | rfl
    · rw [e₀]
      exact min_le_left _ _
    · rw [e₁]
      exact (min_le_right _ _).trans (min_le_left _ _)
    · rw [e₂]
      exact (min_le_right _ _).trans (min_le_right _ _)

private theorem cutPValue_eq_cutPValueR (c : QuartetTree X → ℝ) {s r₁ r₂ : QuartetTree X}
    (hne : r₁ ≠ r₂) (h : s.alternatives = {r₁, r₂}) :
    cutPValue c s = cutPValueR (c s) (c r₁) (c r₂) := by
  unfold cutPValue cutPValueR
  have := cutStat_eq_cutS c hne h
  unfold cutS at this
  rw [this, h, Finset.sum_pair hne, add_assoc]

/-! ### Reduction of the sample to three classes -/

/-- The class of a gene tree: the quartet tree `s`, `r₁`, or else `r₂`. -/
private def label (sides : Γ → Finset (Finset X)) (s r₁ : QuartetTree X) (g : Γ) : Fin 3 :=
  if Displays (sides g) s then 0 else if Displays (sides g) r₁ then 1 else 2

omit [Fintype Γ] in
private theorem label_spec (hs : DisplaysOne dist sides) {s r₁ r₂ : QuartetTree X} (hne : r₁ ≠ r₂)
    (h : s.alternatives = {r₁, r₂}) {g : Γ} (hg : dist g ≠ 0) :
    (label sides s r₁ g = 0 ↔ Displays (sides g) s) ∧
      (label sides s r₁ g = 1 ↔ Displays (sides g) r₁) ∧
      (label sides s r₁ g = 2 ↔ Displays (sides g) r₂) := by
  obtain ⟨h₁, h₂, -, -⟩ := alternatives_facts hne h
  have hT := treesOn_taxa_eq h
  obtain ⟨t, ⟨ht, htd⟩, huniq⟩ := hs g hg s.taxa s.card_taxa
  have hs' : s ∈ treesOn s.taxa := by rw [hT]; simp
  have hr₁ : r₁ ∈ treesOn s.taxa := by rw [hT]; simp
  have hr₂ : r₂ ∈ treesOn s.taxa := by rw [hT]; simp
  rw [hT] at ht
  simp only [Finset.mem_insert, Finset.mem_singleton] at ht
  have hU : ∀ t', t' ∈ treesOn s.taxa → Displays (sides g) t' → t' = t :=
    fun t' h₃ h₄ ↦ huniq t' ⟨h₃, h₄⟩
  unfold label
  rcases ht with rfl | rfl | rfl
  · have hn₁ : ¬ Displays (sides g) r₁ := fun hd ↦ h₁ (hU r₁ hr₁ hd).symm
    have hn₂ : ¬ Displays (sides g) r₂ := fun hd ↦ h₂ (hU r₂ hr₂ hd).symm
    simp [htd, hn₁, hn₂]
  · have hn₁ : ¬ Displays (sides g) s := fun hd ↦ h₁ (hU s hs' hd)
    have hn₂ : ¬ Displays (sides g) r₂ := fun hd ↦ hne (hU r₂ hr₂ hd).symm
    simp [htd, hn₁, hn₂]
  · have hn₁ : ¬ Displays (sides g) s := fun hd ↦ h₂ (hU s hs' hd)
    have hn₂ : ¬ Displays (sides g) r₁ := fun hd ↦ hne (hU r₁ hr₁ hd)
    simp [htd, hn₁, hn₂]

omit [Fintype Γ] in
private theorem count_label (hs : DisplaysOne dist sides) {s r₁ r₂ : QuartetTree X} (hne : r₁ ≠ r₂)
    (h : s.alternatives = {r₁, r₂}) {n : ℕ} {ω : Fin n → Γ} (hω : ∏ i, dist (ω i) ≠ 0) :
    quartetCount sides ω s = count (fun i ↦ label sides s r₁ (ω i)) 0 ∧
      quartetCount sides ω r₁ = count (fun i ↦ label sides s r₁ (ω i)) 1 ∧
      quartetCount sides ω r₂ = count (fun i ↦ label sides s r₁ (ω i)) 2 := by
  have hpos : ∀ i, dist (ω i) ≠ 0 := Finset.prod_ne_zero_iff.1 hω |> fun h' i ↦ h' i (Finset.mem_univ i)
  unfold quartetCount count
  refine ⟨?_, ?_, ?_⟩ <;> congr 2 <;> ext i <;> simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  · exact (label_spec hs hne h (hpos i)).1.symm
  · exact (label_spec hs hne h (hpos i)).2.1.symm
  · exact (label_spec hs hne h (hpos i)).2.2.symm

private theorem pushDist_label (hs : DisplaysOne dist sides) {s r₁ r₂ : QuartetTree X} (hne : r₁ ≠ r₂)
    (h : s.alternatives = {r₁, r₂}) :
    pushDist dist (label sides s r₁) 0 = displayCF dist sides s ∧
      pushDist dist (label sides s r₁) 1 = displayCF dist sides r₁ ∧
      pushDist dist (label sides s r₁) 2 = displayCF dist sides r₂ := by
  unfold pushDist displayCF
  refine ⟨Finset.sum_congr rfl fun g _ ↦ ?_, Finset.sum_congr rfl fun g _ ↦ ?_,
    Finset.sum_congr rfl fun g _ ↦ ?_⟩ <;> by_cases hg : dist g = 0
  · simp [hg]
  · simp only [(label_spec hs hne h hg).1]
  · simp [hg]
  · simp only [(label_spec hs hne h hg).2.1]
  · simp [hg]
  · simp only [(label_spec hs hne h hg).2.2]

/-- The sample of gene trees, through the three counts. -/
private theorem iidProb_counts (hs : DisplaysOne dist sides) {s r₁ r₂ : QuartetTree X} (hne : r₁ ≠ r₂)
    (h : s.alternatives = {r₁, r₂}) (n : ℕ) (E : ℝ → ℝ → ℝ → Prop) :
    iidProb dist n (fun ω ↦
        E (quartetCount sides ω s) (quartetCount sides ω r₁) (quartetCount sides ω r₂)) =
      iidProb (pushDist dist (label sides s r₁)) n (fun η ↦ E (count η 0) (count η 1) (count η 2)) := by
  rw [← iidProb_comp_label (label sides s r₁) n (fun η ↦ E (count η 0) (count η 1) (count η 2))]
  unfold iidProb
  refine Finset.sum_congr rfl fun ω _ ↦ ?_
  by_cases hω : ∏ i, dist (ω i) = 0
  · simp [hω]
  · obtain ⟨h₁, h₂, h₃⟩ := count_label hs hne h hω
    simp only [h₁, h₂, h₃]

/-- The law of the three classes when two of them have equal probability. -/
private theorem pushDist_eq_cutPoint (hd : IsDist dist) (hs : DisplaysOne dist sides)
    {s r₁ r₂ : QuartetTree X} (hne : r₁ ≠ r₂) (h : s.alternatives = {r₁, r₂})
    (heq : displayCF dist sides r₁ = displayCF dist sides r₂) :
    pushDist dist (label sides s r₁) = cutPoint (3 * displayCF dist sides r₁) := by
  obtain ⟨h₀, h₁, h₂⟩ := pushDist_label hs hne h
  have hsum := sum_displayCF_treesOn hd hs s.card_taxa
  rw [sum_treesOn _ hne h, ← heq] at hsum
  funext i
  fin_cases i
  · change pushDist dist (label sides s r₁) 0 = 1 - 2 * (3 * displayCF dist sides r₁) / 3
    rw [h₀]
    linarith
  · change pushDist dist (label sides s r₁) 1 = 3 * displayCF dist sides r₁ / 3
    rw [h₁]
    ring
  · change pushDist dist (label sides s r₁) 2 = 3 * displayCF dist sides r₁ / 3
    rw [h₂, ← heq]
    ring

/-- Under the null of the star test, its p-value is asymptotically uniform. -/
theorem starPValue_asymptoticallyUniform (k : StarTest) (hd : IsDist dist) (hs : DisplaysOne dist sides)
    {q : Finset X} (hq : q.card = 4) (h : ∀ r ∈ treesOn q, displayCF dist sides r = 1 / 3) :
    AsymptoticallyUniform dist fun _ ω => starPValue k (quartetCount sides ω) q := by
  obtain ⟨t, ht⟩ : (treesOn q).Nonempty := by
    rw [← Finset.card_pos, card_treesOn hq]
    norm_num
  have htq : t.taxa = q := by simpa [treesOn] using ht
  subst htq
  obtain ⟨r₁, r₂, hne, hr⟩ := QuartetTree.exists_alternatives t
  have hT := treesOn_taxa_eq hr
  have h₀ := h t (by rw [hT]; simp)
  have h₁ := h r₁ (by rw [hT]; simp)
  have h₂ := h r₂ (by rw [hT]; simp)
  have hp : pushDist dist (label sides t r₁) = cutPoint 1 := by
    rw [pushDist_eq_cutPoint hd hs hne hr (by rw [h₁, h₂]), h₁]
    norm_num
  intro x hx0 hx1
  cases k with
  | lrt =>
    have := tendsto_star_lrt hx0 hx1
    rw [← hp] at this
    refine this.congr fun n ↦ ?_
    rw [← iidProb_counts hs hne hr n (fun a b c ↦ chiSqTwoTail (starS a b c) ≤ x)]
    simp only [starPValue, starStat_eq_starS _ hne hr]
  | pearson =>
    have := tendsto_star_pearson hx0 hx1
    rw [← hp] at this
    refine this.congr fun n ↦ ?_
    rw [← iidProb_counts hs hne hr n (fun a b c ↦ chiSqTwoTail (pearsonS a b c) ≤ x)]
    simp only [starPValue, pearsonStat_eq_pearsonS _ hne hr]

/-- Under the null of the T1 test away from its boundary, with positive probabilities, its p-value is
asymptotically uniform. -/
theorem t1PValue_asymptoticallyUniform (hd : IsDist dist) (hs : DisplaysOne dist sides)
    {s : QuartetTree X}
    (hlt : ∀ r ∈ s.alternatives, displayCF dist sides r < displayCF dist sides s)
    (heq : ∀ r ∈ s.alternatives, ∀ r' ∈ s.alternatives,
      displayCF dist sides r = displayCF dist sides r')
    (hpos : ∀ r ∈ s.alternatives, 0 < displayCF dist sides r) :
    AsymptoticallyUniform dist fun _ ω => t1PValue (quartetCount sides ω) s := by
  obtain ⟨r₁, r₂, hne, hr⟩ := QuartetTree.exists_alternatives s
  have hmem₁ : r₁ ∈ s.alternatives := by rw [hr]; simp
  have hmem₂ : r₂ ∈ s.alternatives := by rw [hr]; simp
  have heq' := heq r₁ hmem₁ r₂ hmem₂
  have hp := pushDist_eq_cutPoint hd hs hne hr heq'
  have hsum := sum_displayCF_treesOn hd hs s.card_taxa
  rw [sum_treesOn _ hne hr, ← heq'] at hsum
  have h₁ := hlt r₁ hmem₁
  have h₂ := hpos r₁ hmem₁
  have hφ : 0 < 3 * displayCF dist sides r₁ ∧ 3 * displayCF dist sides r₁ < 3 / 2 := by
    constructor <;> linarith
  have hφ1 : 3 * displayCF dist sides r₁ < 1 := by linarith
  intro x hx0 hx1
  have := tendsto_t1 hφ hφ1 hx0 hx1
  rw [← hp] at this
  refine this.congr fun n ↦ ?_
  rw [← iidProb_counts hs hne hr n (fun a b c ↦ t1PValueR a b c ≤ x)]
  simp only [t1PValue_eq_t1PValueR _ hne hr]

/-- The null of the T1 test with an alternative of probability zero: the alternatives have count zero,
so the p-value is `1`. -/
theorem t1PValue_degenerate (hd : IsDist dist) (hs : DisplaysOne dist sides) {s : QuartetTree X}
    (h : ∀ r ∈ s.alternatives, displayCF dist sides r = 0) {n : ℕ} (ω : Fin n → Γ)
    (hω : ∏ i, dist (ω i) ≠ 0) : t1PValue (quartetCount sides ω) s = 1 := by
  have _ := hs
  obtain ⟨r₁, r₂, hne, hr⟩ := QuartetTree.exists_alternatives s
  have hpos : ∀ i, dist (ω i) ≠ 0 :=
    Finset.prod_ne_zero_iff.1 hω |> fun h' i ↦ h' i (Finset.mem_univ i)
  have hzero : ∀ r ∈ s.alternatives, quartetCount sides ω r = 0 := by
    intro r hr'
    have hcf := h r hr'
    unfold displayCF at hcf
    have hterm := (Finset.sum_eq_zero_iff_of_nonneg (fun g _ ↦ by
      split_ifs <;> simp [hd.1 g])).1 hcf
    unfold quartetCount
    rw [Nat.cast_eq_zero, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro i _ hdisp
    have := hterm (ω i) (Finset.mem_univ _)
    rw [ite_eq_left hdisp] at this
    exact hpos i this
  have h₁ := hzero r₁ (by rw [hr]; simp)
  have h₂ := hzero r₂ (by rw [hr]; simp)
  rw [t1PValue_eq_t1PValueR _ hne hr, h₁, h₂]
  have hc : 0 ≤ quartetCount sides ω s := quartetCount_nonneg ω s
  refine le_antisymm (t1Tail_le_one _ _) ?_
  have hle := chiSqOneTail_le_t1Tail'
    (muZero (min 1 (3 * (0 + 0) / (2 * (quartetCount sides ω s + 0 + 0))))
      (quartetCount sides ω s + 0 + 0))
    (if (0 + 0) / 2 ≤ quartetCount sides ω s then lineS 0 0 else starS (quartetCount sides ω s) 0 0)
  have hif : (if ((0 : ℝ) + 0) / 2 ≤ quartetCount sides ω s then lineS 0 0
      else starS (quartetCount sides ω s) 0 0) = 0 := by
    rw [ite_eq_left (by simpa using hc)]
    simp [lineS]
  rw [hif, chiSqOneTail_zero] at hle
  unfold t1PValueR
  rw [hif]
  exact hle

/-- At the boundary `(1/3, 1/3, 1/3)` of the T1 null its p-value is not asymptotically uniform, but it
stays away from `0` and from `1` in probability. -/
theorem t1PValue_centroid_tight (hd : IsDist dist) (hs : DisplaysOne dist sides) {s : QuartetTree X}
    (h : ∀ r ∈ treesOn s.taxa, displayCF dist sides r = 1 / 3) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ δ < 1 / 2 ∧ ∀ᶠ n in atTop, 1 - ε < iidProb dist n fun ω =>
      δ ≤ t1PValue (quartetCount sides ω) s ∧ t1PValue (quartetCount sides ω) s ≤ 1 - δ := by
  obtain ⟨r₁, r₂, hne, hr⟩ := QuartetTree.exists_alternatives s
  have hT := treesOn_taxa_eq hr
  have h₁ := h r₁ (by rw [hT]; simp)
  have h₂ := h r₂ (by rw [hT]; simp)
  have hp : pushDist dist (label sides s r₁) = cutPoint 1 := by
    rw [pushDist_eq_cutPoint hd hs hne hr (by rw [h₁, h₂]), h₁]
    norm_num
  obtain ⟨δ, hδ₀, hδ₁, hev⟩ := centroid_tight hε
  refine ⟨δ, hδ₀, hδ₁, ?_⟩
  filter_upwards [hev] with n hn
  rw [← hp] at hn
  rw [← iidProb_counts hs hne hr n
    (fun a b c ↦ δ ≤ t1PValueR a b c ∧ t1PValueR a b c ≤ 1 - δ)] at hn
  simpa only [t1PValue_eq_t1PValueR _ hne hr] using hn

/-- The cut test on a strictly cut, positive concordance factor (the null, off its singularity): the
line of the true topology has the least statistic with probability tending to one, and for any levels
`α_m → 0` the test does not reject. -/
theorem cutTest_null (hd : IsDist dist) (hs : DisplaysOne dist sides) {s : QuartetTree X}
    (hne : ∀ r ∈ s.alternatives, displayCF dist sides r ≠ displayCF dist sides s)
    (heq : ∀ r ∈ s.alternatives, ∀ r' ∈ s.alternatives,
      displayCF dist sides r = displayCF dist sides r')
    (hpos : ∀ r ∈ treesOn s.taxa, 0 < displayCF dist sides r) {α : ℕ → ℝ}
    (hα : Tendsto α atTop (𝓝 0)) :
    Tendsto (fun n => iidProb dist n fun ω =>
      (∀ r ∈ s.alternatives, lineStat (quartetCount sides ω) s < lineStat (quartetCount sides ω) r) ∧
        α n ≤ cutPValue (quartetCount sides ω) s) atTop (𝓝 1) := by
  obtain ⟨r₁, r₂, hrr, hr⟩ := QuartetTree.exists_alternatives s
  obtain ⟨hs₁, hs₂, ha₁, ha₂⟩ := alternatives_facts hrr hr
  have hT := treesOn_taxa_eq hr
  have hmem₁ : r₁ ∈ s.alternatives := by rw [hr]; simp
  have hmem₂ : r₂ ∈ s.alternatives := by rw [hr]; simp
  have heq' := heq r₁ hmem₁ r₂ hmem₂
  have hp := pushDist_eq_cutPoint hd hs hrr hr heq'
  have hsum := sum_displayCF_treesOn hd hs s.card_taxa
  rw [sum_treesOn _ hrr hr, ← heq'] at hsum
  have h₀ := hpos s (by rw [hT]; simp)
  have h₁ := hpos r₁ (by rw [hT]; simp)
  have hφ : 0 < 3 * displayCF dist sides r₁ ∧ 3 * displayCF dist sides r₁ < 3 / 2 := by
    constructor <;> linarith
  have hφ1 : 3 * displayCF dist sides r₁ ≠ 1 := by
    intro hone
    apply hne r₁ hmem₁
    linarith
  have := tendsto_cut_null hφ hφ1 hα
  rw [← hp] at this
  refine this.congr fun n ↦ ?_
  rw [← iidProb_counts hs hrr hr n (fun a b c ↦ (lineS b c < lineS a c ∧ lineS b c < lineS a b) ∧
    α n ≤ cutPValueR a b c)]
  congr 1
  funext ω
  rw [cutPValue_eq_cutPValueR _ hrr hr, lineStat_eq_lineS _ hrr hr]
  have e₁ := lineStat_eq_lineS (quartetCount sides ω) hs₂ ha₁
  have e₂ := lineStat_eq_lineS (quartetCount sides ω) hs₁ ha₂
  have hforall : (∀ r ∈ s.alternatives, lineS (quartetCount sides ω r₁) (quartetCount sides ω r₂) <
        lineStat (quartetCount sides ω) r) ↔
      lineS (quartetCount sides ω r₁) (quartetCount sides ω r₂) <
          lineS (quartetCount sides ω s) (quartetCount sides ω r₂) ∧
        lineS (quartetCount sides ω r₁) (quartetCount sides ω r₂) <
          lineS (quartetCount sides ω s) (quartetCount sides ω r₁) := by
    rw [hr, ← e₁, ← e₂]
    simp
  rw [hforall]

end Phylogenetics.QuartetTests
