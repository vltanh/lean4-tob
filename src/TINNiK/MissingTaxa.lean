module

public import Basic.Testing.MissingTaxa
public import TINNiK.T3

/-!
# TINNiK with gene trees that have missing taxa

TINNiK's text, after its algorithm (line 198): "The TINNiK algorithm can also be applied when gene trees have missing taxa, provided each subset of 4
taxa occurs on at least one gene tree, so the qcCF is not the zero vector". And before its Theorem 4 (line 202): "For simplicity, we also restrict to
the case that the data is `m` gene trees, each on the full taxon set `X`, since generalizing from this is straightforward".

The procedure is the algorithm on the counts of `Phylogenetics.quartetCountOn`: `tinnik` and `tinnikT3` take the counts as an argument, so
nothing else changes. Three things are claimed or implied.

* The qcCF is the zero vector exactly when the set of four taxa occurs on no gene tree: `Phylogenetics.quartetCountOn_treesOn_eq_zero_iff`. The
  tests need this: on the zero vector, the star test has p-value `1`, and on a set occurring on one gene tree it has p-value `1/3`, so at levels `β`
  below these the set is judged a B-quartet whatever it is: `mem_testedB_of_coverCount_eq_zero`, `mem_testedB_of_coverCount_eq_one`. So the proviso
  makes the algorithm meaningful, and does not make it consistent: consistency needs the number of gene trees containing each set to grow. Reading
  "straightforward": this is the hypothesis `Covers` below.
* **Consistency** with missing taxa: `theorem4_missing`, `theorem4_missing_of_cfDetectable`, and with the T3 option `theorem4T3_missing`. The source states
  no model. The one here is: the gene trees are independent from the NMSC, each with the taxa `on m i` kept, fixed in advance (they may depend on
  the sample size `m`), and `coverCount (on m) q → ∞` for each set `q` of four taxa. A gene tree on a subset of the taxa has the law of the
  induced tree, by sampling consistency, so this is the law of gene trees on subsets.
* The proof is what "straightforward" suggests: on a set `q`, the counts are those of the `coverCount (on m) q` gene trees containing it, an independent
  sample (`Phylogenetics.iidProb_quartetCountOn`). So the limits of the proof of Theorem 4 hold along `coverCount (on m) q`. What is not quite
  immediate is the levels, which must serve all sets at once with different counts: under the alternative, `exists_levels_on` is the
  maximum over `q` of the levels at `coverCount (on m) q`; under the null, any levels tending to zero do
  (`Phylogenetics.tendsto_iidProb_on_level`).

`rejectsOn_of_log` gives levels known in advance, when `log α_m` is small against the number of gene trees containing each set.
-/

@[expose] public noncomputable section

open Phylogenetics Phylogenetics.RootedNetwork Finset Filter Topology
open scoped Classical

namespace TINNiK

variable {V E X : Type*} [Fintype X] [DecidableEq X]

/-! ### The zero vector -/

/-- On the zero vector, the star test has p-value `1`. -/
theorem starPValue_of_forall_eq_zero {c : QuartetTree X → ℝ} {q : Finset X} (h : ∀ r ∈ treesOn q, c r = 0) :
    starPValue .lrt c q = 1 := by
  have h₁ : ∑ r ∈ treesOn q, c r * Real.log (c r) = 0 := sum_eq_zero fun r hr => by rw [h r hr, zero_mul]
  have h₂ : ∑ r ∈ treesOn q, c r = 0 := sum_eq_zero h
  simp [starPValue, chiSqTwoTail, starStat, h₁, h₂]

/-- **Why the proviso is needed.** A set of four taxa that occurs on no gene tree has a zero vector as its qcCF, and is judged a B-quartet at any level
`β ≤ 1`, whatever the network says. -/
theorem mem_testedB_of_coverCount_eq_zero {Γ : Type*} [Fintype Γ] {n : ℕ} {sides : Γ → Finset (Finset X)}
    {on : Fin n → Finset X} {ω : Fin n → Γ} (ml : (QuartetTree X → ℝ) → Finset X → QuartetTree X) (α : ℝ) {β : ℝ}
    (hβ : β ≤ 1) {q : Finset X} (hq : q.card = 4) (h : coverCount on q = 0) :
    q ∈ testedB ml α β (quartetCountOn sides on ω) := by
  have hz : ∀ r ∈ treesOn q, quartetCountOn sides on ω r = 0 := fun r hr => by
    rw [quartetCountOn_eq sides on ω hr]
    have hempty : (coverCount on q) = 0 := h
    simp only [quartetCount, Nat.cast_eq_zero, card_eq_zero]
    exact eq_empty_of_forall_notMem fun j => (hempty ▸ j).elim0
  exact ⟨hq, Or.inl (by rwa [starPValue_of_forall_eq_zero hz])⟩

/-- **The proviso does not give consistency.** A set of four taxa that occurs on one gene tree, which resolves it, has a qcCF `(1, 0, 0)`, and the star
test has p-value `1/3`, so at levels `β ≤ 1/3` it is judged a B-quartet, whatever the network says. So the tests are not right on it however
many gene trees there are, if only one of them contains it. -/
theorem mem_testedB_of_coverCount_eq_one {Γ : Type*} [Fintype Γ] {n : ℕ} {sides : Γ → Finset (Finset X)}
    {on : Fin n → Finset X} {ω : Fin n → Γ} (ml : (QuartetTree X → ℝ) → Finset X → QuartetTree X) (α : ℝ) {β : ℝ}
    (hβ : β ≤ 1 / 3) {q : Finset X} (hq : q.card = 4)
    (hone : ∀ i, q ⊆ on i → ∃! s, s ∈ treesOn q ∧ Displays (sides (ω i)) s) (h : coverCount on q = 1) :
    q ∈ testedB ml α β (quartetCountOn sides on ω) := by
  set c := quartetCountOn sides on ω with hc
  have hsum : ∑ r ∈ treesOn q, c r = 1 := by
    have := sum_quartetCountOn_treesOn hone
    rw [h] at this
    simpa using this
  have hint : ∀ r ∈ treesOn q, c r = 0 ∨ c r = 1 := fun r hr => by
    have h₀ : 0 ≤ c r := quartetCountOn_nonneg sides on ω r
    have hle : c r ≤ 1 := hsum ▸ single_le_sum (f := c) (fun u _ => quartetCountOn_nonneg sides on ω u) hr
    have hnat : ∃ a : ℕ, c r = a := ⟨_, rfl⟩
    obtain ⟨a, ha⟩ := hnat
    rw [ha] at hle ⊢
    have ha1 : a ≤ 1 := by exact_mod_cast hle
    interval_cases a <;> simp
  have hlog : ∑ r ∈ treesOn q, c r * Real.log (c r) = 0 := sum_eq_zero fun r hr => by
    rcases hint r hr with h' | h' <;> simp [h']
  have hp : starPValue .lrt c q = 1 / 3 := by
    simp only [starPValue, chiSqTwoTail, starStat, hlog, hsum]
    have : -(2 * (0 - 1 * Real.log (1 / 3))) / 2 = Real.log (1 / 3) := by ring
    rw [this, Real.exp_log (by norm_num)]
  exact ⟨hq, Or.inl (by rw [hp]; exact hβ)⟩

/-! ### The model -/

/-- The taxa kept on the gene trees, for each sample size, leave each set of four taxa on more and more gene trees. -/
def Covers (on : (m : ℕ) → Fin m → Finset X) : Prop :=
  ∀ q : Finset X, q.card = 4 → Tendsto (fun m => coverCount (on m) q) atTop atTop

/-- The gene trees of the sample, each with all taxa, are the case `on m i = univ`. -/
theorem covers_univ : Covers (X := X) fun _ _ => univ := by
  intro q _
  refine tendsto_atTop_mono (fun m => ?_) tendsto_id
  simp [coverCount, coverIndices]

omit [Fintype X] in
/-- The number of the first `m` terms of a sequence of taxon sets that contain `q`. -/
theorem coverCount_eq_card_range (S : ℕ → Finset X) (m : ℕ) (q : Finset X) :
    coverCount (fun j : Fin m => S j) q = ((range m).filter fun i => q ⊆ S i).card := by
  refine card_bij (fun j _ => j.val) ?_ ?_ ?_
  · intro j hj
    exact mem_filter.2 ⟨mem_range.2 j.isLt, mem_coverIndices.1 hj⟩
  · intro j _ j' _ h
    exact Fin.ext h
  · intro i hi
    obtain ⟨him, hiq⟩ := mem_filter.1 hi
    exact ⟨⟨i, mem_range.1 him⟩, mem_coverIndices.2 hiq, rfl⟩

omit [Fintype X] in
/-- A fixed sequence of taxon sets in which each set of four taxa occurs infinitely often. -/
theorem covers_of_frequently {S : ℕ → Finset X} (h : ∀ q : Finset X, q.card = 4 → ∃ᶠ i in atTop, q ⊆ S i) :
    Covers fun m (i : Fin m) => S i := by
  intro q hq
  refine tendsto_atTop.2 fun b => ?_
  simp only [coverCount_eq_card_range]
  induction b with
  | zero => exact Eventually.of_forall fun _ => Nat.zero_le _
  | succ b ih =>
    obtain ⟨M, hM⟩ := eventually_atTop.1 ih
    obtain ⟨i, hi, hiq⟩ := frequently_atTop.1 (h q hq) M
    refine eventually_atTop.2 ⟨i + 1, fun m hm => ?_⟩
    have hbelow := hM i hi
    have hlt : ((range i).filter fun j => q ⊆ S j).card < ((range m).filter fun j => q ⊆ S j).card := by
      refine card_lt_card ⟨fun j hj => ?_, fun hsub => ?_⟩
      · obtain ⟨hji, hjq⟩ := mem_filter.1 hj
        exact mem_filter.2 ⟨mem_range.2 ((mem_range.1 hji).trans_le (by omega)), hjq⟩
      · have := hsub (mem_filter.2 ⟨mem_range.2 (by omega : i < m), hiq⟩)
        exact absurd (mem_range.1 (mem_filter.1 this).1) (lt_irrefl i)
    omega

/-! ### The tests on a set of four taxa -/

/-- The answers wanted on a set of four taxa, for the p-value `pv` of the cut test or of the T3 test: the star test rejects; a cut-edge split on the
induced network is the fitted topology, and the test does not reject; and without a cut-edge split the test rejects. -/
def GoodOn (N : RootedNetwork V E X) (ml : (QuartetTree X → ℝ) → Finset X → QuartetTree X)
    (pv : (QuartetTree X → ℝ) → QuartetTree X → ℝ) (β a : ℝ) (c : QuartetTree X → ℝ) (q : Finset X) : Prop :=
  starPValue .lrt c q < β ∧ (∀ s ∈ treesOn q, InducedCutSplit N s → ml c q = s ∧ a ≤ pv c s) ∧
    (¬ IsTreelike N q → pv c (ml c q) < a)

/-- **From right answers on each set of four taxa, the algorithm returns the tree of blobs**, for either test. -/
theorem tinnikOf_eq_of_goodOn {N : RootedNetwork V E X} (hN : N.IsPhylogenetic) (hX : 4 ≤ Fintype.card X)
    {ml : (QuartetTree X → ℝ) → Finset X → QuartetTree X} {pv : (QuartetTree X → ℝ) → QuartetTree X → ℝ} {a β δ : ℝ}
    (hδ₂ : δ < 2) {M : TreeBuilder X} (hM : IsExactBuilder M) {c : QuartetTree X → ℝ}
    (h : ∀ q : Finset X, q.card = 4 → GoodOn N ml pv β a c q) :
    tinnikOf {q | q.card = 4 ∧ (β ≤ starPValue .lrt c q ∨ pv c (ml c q) < a)}
      {s | s.taxa ∉ {q | q.card = 4 ∧ (β ≤ starPValue .lrt c q ∨ pv c (ml c q) < a)} ∧ s = ml c s.taxa} δ M =
      treeOfBlobs N := by
  have hnot : ∀ q : Finset X, q.card = 4 → IsTreelike N q → ¬ (β ≤ starPValue .lrt c q ∨ pv c (ml c q) < a) := by
    rintro q hq ⟨s, hs, hcs⟩ (hor | hor)
    · exact absurd (h q hq).1 (not_lt.2 hor)
    · obtain ⟨h₁, h₂⟩ := (h q hq).2.1 s hs hcs
      rw [h₁] at hor
      exact absurd hor (not_lt.2 h₂)
  refine tinnikOf_eq_of_relaxed hN hX hδ₂ hM ?_ ?_ ?_ ?_
  · exact fun q hq hnt => ⟨hq, Or.inr ((h q hq).2.2 hnt)⟩
  · rintro q ⟨hq, hor⟩
    refine ⟨hq, fun s hs hd => ?_⟩
    exact hnot q hq ⟨s, hs, AllmanEtAl2023.inducedCutSplit_of_displays hN hd⟩ hor
  · rintro s ⟨hn, hs⟩
    have hq := s.card_taxa
    have htl : IsTreelike N s.taxa := by
      by_contra hnt
      exact hn ⟨hq, Or.inr ((h _ hq).2.2 hnt)⟩
    obtain ⟨s₀, hs₀, hc₀⟩ := htl
    rw [hs, ((h _ hq).2.1 s₀ hs₀ hc₀).1]
    exact hc₀
  · intro s hc
    have hq := s.card_taxa
    have hsmem : s ∈ treesOn s.taxa := mem_treesOn.2 rfl
    exact Or.inl ⟨fun hmem => hnot _ hq ⟨s, hsmem, hc⟩ hmem.2, ((h _ hq).2.1 s hsmem hc).1.symm⟩

section Sample

variable [Fintype V] [Fintype E] {N : RootedNetwork V E X} {θ : MetricData E} {ρ : ℝ}
  {on : (m : ℕ) → Fin m → Finset X}

/-- The star test rejects a concordance factor off the centroid, along the gene trees containing the set. -/
theorem tendsto_star_on [Nonempty X] (hN : N.IsPhylogenetic) (hd : IsDist (geneTreeDist N θ ρ)) {q : Finset X}
    (hq : q.card = 4) (hk : Tendsto (fun m => coverCount (on m) q) atTop atTop)
    (h : ¬ ∀ r ∈ treesOn q, nmscCF N θ ρ r = 1 / 3) {β : ℝ} (hβ : 0 < β) :
    Tendsto (fun m => iidProb (geneTreeDist N θ ρ) m fun ω =>
      starPValue .lrt (quartetCountOn unroot (on m) ω) q < β) atTop (𝓝 1) := by
  have h0 := QuartetTests.starStat_growth .lrt hd (displaysOne_nmsc hN) hq h (b := fun _ => -2 * Real.log β)
    (tendsto_const_div_atTop_nhds_zero_nat _)
  have he : Real.exp (-(-2 * Real.log β) / 2) = β := by
    rw [show -(-2 * Real.log β) / 2 = Real.log β by ring, Real.exp_log hβ]
  rw [he] at h0
  exact tendsto_iidProb_on (Ev := fun _ c => starPValue .lrt c q < β) hd unroot hk
    (fun _ c c' hcc => by
      change starPValue .lrt c q < β ↔ starPValue .lrt c' q < β
      rw [starPValue_lrt_congr hcc]) h0

/-- The cut test rejects at the levels `α`, with probability tending to one, on the sets of four taxa with no cut-edge split, with the taxa `on` kept.
Parallel to `Rejects`. -/
def RejectsOn (N : RootedNetwork V E X) (θ : MetricData E) (ρ : ℝ) (on : (m : ℕ) → Fin m → Finset X) (α : ℕ → ℝ) : Prop :=
  ∀ q : Finset X, q.card = 4 → ¬ IsTreelike N q →
    Tendsto (fun m => iidProb (geneTreeDist N θ ρ) m fun ω =>
      ∀ s ∈ treesOn q, cutPValue (quartetCountOn unroot (on m) ω) s < α m) atTop (𝓝 1)

/-- The T3 test rejects at the levels `α`, with the taxa `on` kept. Parallel to `T3Rejects`. -/
def T3RejectsOn (N : RootedNetwork V E X) (θ : MetricData E) (ρ : ℝ) (on : (m : ℕ) → Fin m → Finset X) (α : ℕ → ℝ) : Prop :=
  ∀ q : Finset X, q.card = 4 → ¬ IsTreelike N q →
    Tendsto (fun m => iidProb (geneTreeDist N θ ρ) m fun ω =>
      ∀ s ∈ treesOn q, t3PValue (quartetCountOn unroot (on m) ω) s < α m) atTop (𝓝 1)

/-- **On each set of four taxa the tests are right, with missing taxa**, for the cut test. -/
theorem tendsto_goodOn_cut (hN : N.IsPhylogenetic) (hX : 4 ≤ Fintype.card X) (hθ : N.IsMetric θ) (hρ : 0 ≤ ρ ∧ ρ ≤ 1)
    (hdet : AllmanEtAl2023.CFDetectable N (nmscCF N θ ρ)) (hon : Covers on) {α : ℕ → ℝ} (hα₀ : Tendsto α atTop (𝓝 0))
    (hrej : RejectsOn N θ ρ on α) {β : ℝ} (hβ : 0 < β) {ml : (QuartetTree X → ℝ) → Finset X → QuartetTree X}
    (hml : IsMLSelection ml) {q : Finset X} (hq : q.card = 4) :
    Tendsto (fun m => iidProb (geneTreeDist N θ ρ) m fun ω =>
      GoodOn N ml cutPValue β (α m) (quartetCountOn unroot (on m) ω) q) atTop (𝓝 1) := by
  have hne : Nonempty X := Fintype.card_pos_iff.mp (by omega)
  have hd : IsDist (geneTreeDist N θ ρ) := ⟨geneTreeDist_nonneg hN hθ hρ, sum_geneTreeDist hN hθ hρ⟩
  have hs := displaysOne_nmsc (X := X) hN (θ := θ) (ρ := ρ)
  have hk := hon q hq
  have hstar := tendsto_star_on (on := on) hN hd hq hk (noCentroidCF_of_cfDetectable hdet q hq) hβ
  by_cases htl : IsTreelike N q
  · obtain ⟨s₀, hs₀, hc₀⟩ := htl
    have hst : s₀.taxa = q := mem_treesOn.1 hs₀
    obtain ⟨hcne, hceq⟩ := hdet.cut s₀ hc₀
    have hnull := tendsto_iidProb_on_level hd unroot hk (on := on)
      (G := fun c => ∀ r ∈ s₀.alternatives, lineStat c s₀ < lineStat c r) (f := fun c => cutPValue c s₀)
      (fun c c' hcc => by
        have hal : ∀ r ∈ s₀.alternatives, r ∈ treesOn q := fun r hr =>
          mem_treesOn.2 ((QuartetTree.mem_alternatives.1 hr).1.trans hst)
        refine forall₂_congr fun r hr => ?_
        rw [lineStat_congr hs₀ hcc, lineStat_congr (hal r hr) hcc])
      (fun c c' hcc => cutPValue_congr hs₀ hcc)
      (fun a ha => QuartetTests.cutTest_null hd hs (s := s₀) hcne hceq (fun r _ => nmscCF_pos hN hθ hρ r) ha) hα₀
    refine tendsto_iidProb_of_imp hd (Eventually.of_forall fun m ω hω => ?_) (tendsto_iidProb_and hd hstar hnull)
    obtain ⟨h₁, h₂, h₃⟩ := hω
    set c := quartetCountOn unroot (on m) ω
    have hml₀ : ml c q = s₀ := by
      obtain ⟨hm1, hm2⟩ := hml c q hq
      by_contra hneq
      have halt : ml c q ∈ s₀.alternatives :=
        QuartetTree.mem_alternatives.2 ⟨(mem_treesOn.1 hm1).trans hst.symm, hneq⟩
      exact absurd (hm2 s₀ hs₀) (not_le.2 (h₂ _ halt))
    refine ⟨h₁, fun s hsq hcs => ?_, fun hnt => absurd ⟨s₀, hs₀, hc₀⟩ hnt⟩
    have hss : s = s₀ := AllmanEtAl2023.inducedCutSplit_unique hN hcs hc₀ ((mem_treesOn.1 hsq).trans hst.symm)
    subst hss
    exact ⟨hml₀, h₃⟩
  · refine tendsto_iidProb_of_imp hd (Eventually.of_forall fun m ω hω => ?_)
      (tendsto_iidProb_and hd hstar (hrej q hq htl))
    exact ⟨hω.1, fun s hsq hcs => absurd ⟨s, hsq, hcs⟩ htl, fun _ => hω.2 _ (hml _ q hq).1⟩

/-- **On each set of four taxa the tests are right, with missing taxa**, for the T3 test. -/
theorem tendsto_goodOn_t3 (hN : N.IsPhylogenetic) (hX : 4 ≤ Fintype.card X) (hθ : N.IsMetric θ) (hρ : 0 ≤ ρ ∧ ρ ≤ 1)
    (hdet : T3Detectable N (nmscCF N θ ρ)) (hon : Covers on) {α : ℕ → ℝ} (hα₀ : Tendsto α atTop (𝓝 0))
    (hrej : T3RejectsOn N θ ρ on α) {β : ℝ} (hβ : 0 < β) {ml : (QuartetTree X → ℝ) → Finset X → QuartetTree X}
    (hml : IsT3MLSelection ml) {q : Finset X} (hq : q.card = 4) :
    Tendsto (fun m => iidProb (geneTreeDist N θ ρ) m fun ω =>
      GoodOn N ml t3PValue β (α m) (quartetCountOn unroot (on m) ω) q) atTop (𝓝 1) := by
  have hne : Nonempty X := Fintype.card_pos_iff.mp (by omega)
  have hd : IsDist (geneTreeDist N θ ρ) := ⟨geneTreeDist_nonneg hN hθ hρ, sum_geneTreeDist hN hθ hρ⟩
  have hs := displaysOne_nmsc (X := X) hN (θ := θ) (ρ := ρ)
  have hk := hon q hq
  have hstar := tendsto_star_on (on := on) hN hd hq hk (noCentroidCF_of_t3Detectable hdet q hq) hβ
  by_cases htl : IsTreelike N q
  · obtain ⟨s₀, hs₀, hc₀⟩ := htl
    have hst : s₀.taxa = q := mem_treesOn.1 hs₀
    have hnull := tendsto_iidProb_on_level hd unroot hk (on := on)
      (G := fun c => ∀ r ∈ s₀.alternatives, t1Stat c s₀ < t1Stat c r) (f := fun c => t3PValue c s₀)
      (fun c c' hcc => by
        have hal : ∀ r ∈ s₀.alternatives, r ∈ treesOn q := fun r hr =>
          mem_treesOn.2 ((QuartetTree.mem_alternatives.1 hr).1.trans hst)
        refine forall₂_congr fun r hr => ?_
        rw [t1Stat_congr hs₀ hcc, t1Stat_congr (hal r hr) hcc])
      (fun c c' hcc => t3PValue_congr hs₀ hcc)
      (fun a ha => QuartetTests.t3Test_null hd hs (hdet.cut s₀ hc₀) (fun r _ => nmscCF_pos hN hθ hρ r) ha) hα₀
    refine tendsto_iidProb_of_imp hd (Eventually.of_forall fun m ω hω => ?_) (tendsto_iidProb_and hd hstar hnull)
    obtain ⟨h₁, h₂, h₃⟩ := hω
    set c := quartetCountOn unroot (on m) ω
    have hml₀ : ml c q = s₀ := by
      obtain ⟨hm1, hm2⟩ := hml c q hq
      by_contra hneq
      have halt : ml c q ∈ s₀.alternatives :=
        QuartetTree.mem_alternatives.2 ⟨(mem_treesOn.1 hm1).trans hst.symm, hneq⟩
      exact absurd (hm2 s₀ hs₀) (not_le.2 (h₂ _ halt))
    refine ⟨h₁, fun s hsq hcs => ?_, fun hnt => absurd ⟨s₀, hs₀, hc₀⟩ hnt⟩
    have hss : s = s₀ := AllmanEtAl2023.inducedCutSplit_unique hN hcs hc₀ ((mem_treesOn.1 hsq).trans hst.symm)
    subst hss
    exact ⟨hml₀, h₃⟩
  · refine tendsto_iidProb_of_imp hd (Eventually.of_forall fun m ω hω => ?_)
      (tendsto_iidProb_and hd hstar (hrej q hq htl))
    exact ⟨hω.1, fun s hsq hcs => absurd ⟨s, hsq, hcs⟩ htl, fun _ => hω.2 _ (hml _ q hq).1⟩

/-! ### The levels -/

private theorem tendsto_chiSqOneTail_comp {k : ℕ → ℕ} (hk : Tendsto k atTop atTop) {d : ℝ} (hd : 0 < d) :
    Tendsto (fun m => chiSqOneTail (k m * d)) atTop (𝓝 0) := by
  have h1 : Tendsto (fun m : ℕ => (k m : ℝ) * d / 2) atTop atTop :=
    ((tendsto_natCast_atTop_atTop.comp hk).atTop_mul_const hd).atTop_div_const (by norm_num)
  have h : Tendsto (fun m : ℕ => Real.exp (-((k m : ℝ) * d) / 2)) atTop (𝓝 0) := by
    refine (Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp h1)).congr fun m => ?_
    simp [neg_div]
  refine squeeze_zero (fun m => QuartetTests.chiSqOneTail_nonneg _) (fun m => ?_) h
  exact QuartetTests.chiSqOneTail_le_chiSqTwoTail (by positivity)

theorem tendsto_chiSqTwoTail_comp {k : ℕ → ℕ} (hk : Tendsto k atTop atTop) {d : ℝ} (hd : 0 < d) :
    Tendsto (fun m => chiSqTwoTail (k m * d)) atTop (𝓝 0) := by
  have h1 : Tendsto (fun m : ℕ => (k m : ℝ) * d / 2) atTop atTop :=
    ((tendsto_natCast_atTop_atTop.comp hk).atTop_mul_const hd).atTop_div_const (by norm_num)
  refine (Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp h1)).congr fun m => ?_
  simp [chiSqTwoTail, neg_div]

/-- **The levels of Theorem 4 with missing taxa**: as `exists_levels`, with `m` replaced in the level of each set of four taxa by the number of gene trees
containing it. The gene trees that the levels come from are known; the limits `d` of the statistics are not. -/
theorem exists_levels_on [Nonempty X] (hN : N.IsPhylogenetic) (hθ : N.IsMetric θ) (hρ : 0 ≤ ρ ∧ ρ ≤ 1)
    (hdet : AllmanEtAl2023.CFDetectable N (nmscCF N θ ρ)) (hon : Covers on) :
    ∃ α : ℕ → ℝ, Tendsto α atTop (𝓝 0) ∧ (∀ m, 0 < α m) ∧ RejectsOn N θ ρ on α := by
  have hd : IsDist (geneTreeDist N θ ρ) := ⟨geneTreeDist_nonneg hN hθ hρ, sum_geneTreeDist hN hθ hρ⟩
  let Q : Finset (Finset X) := univ.filter fun q => q.card = 4 ∧ ¬ IsTreelike N q
  have hex : ∀ q : Finset X, ∃ d : ℝ, 0 < d ∧ (q ∈ Q → Tendsto (fun n : ℕ =>
      iidProb (geneTreeDist N θ ρ) n fun ω =>
        ∀ s ∈ treesOn q, cutPValue (quartetCount unroot ω) s < chiSqOneTail (n * d)) atTop (𝓝 1)) := by
    intro q
    by_cases hq : q ∈ Q
    · obtain ⟨hq4, hnt⟩ := (mem_filter.mp hq).2
      obtain ⟨d, hd0, h⟩ := QuartetTests.cutTest_alternative hd hq4 (hdet.blob q hq4 hnt)
      exact ⟨d, hd0, fun _ => h⟩
    · exact ⟨1, one_pos, fun h => absurd h hq⟩
  choose d hd0 hdq using hex
  let α : ℕ → ℝ := fun m => Q.fold max (chiSqOneTail (m * 1)) fun q => chiSqOneTail ((coverCount (on m) q : ℕ) * d q)
  have hle : ∀ m : ℕ, ∀ q ∈ Q, chiSqOneTail ((coverCount (on m) q : ℕ) * d q) ≤ α m := fun m q hq =>
    (Finset.le_fold_max _).mpr (Or.inr ⟨q, hq, le_rfl⟩)
  have hbase : ∀ m : ℕ, chiSqOneTail (m * 1) ≤ α m := fun m => (Finset.le_fold_max _).mpr (Or.inl le_rfl)
  refine ⟨α, ?_, fun m => (QuartetTests.chiSqOneTail_pos _).trans_le (hbase m), ?_⟩
  · have hsum : Tendsto (fun m : ℕ => chiSqOneTail (m * 1) +
        ∑ q ∈ Q, chiSqOneTail ((coverCount (on m) q : ℕ) * d q)) atTop (𝓝 0) := by
      have := (tendsto_chiSqOneTail_comp (k := id) tendsto_id one_pos).add
        (tendsto_finsetSum Q fun q hq => tendsto_chiSqOneTail_comp (hon q (mem_filter.mp hq).2.1) (hd0 q))
      simpa using this
    refine squeeze_zero (fun m => (QuartetTests.chiSqOneTail_nonneg _).trans (hbase m)) (fun m => ?_) hsum
    refine Finset.fold_max_le _ |>.mpr ⟨?_, fun q hq => ?_⟩
    · exact le_add_of_nonneg_right (Finset.sum_nonneg fun _ _ => QuartetTests.chiSqOneTail_nonneg _)
    · exact (Finset.single_le_sum (f := fun q => chiSqOneTail ((coverCount (on m) q : ℕ) * d q))
        (fun _ _ => QuartetTests.chiSqOneTail_nonneg _) hq).trans
        (le_add_of_nonneg_left (QuartetTests.chiSqOneTail_nonneg _))
  · intro q hq4 hnt
    have hq : q ∈ Q := mem_filter.mpr ⟨mem_univ _, hq4, hnt⟩
    have hEv : ∀ n : ℕ, DependsOnTaxa q fun c => ∀ s ∈ treesOn q, cutPValue c s < chiSqOneTail (n * d q) :=
      fun n c c' hcc => forall₂_congr fun s hs => by rw [cutPValue_congr hs hcc]
    have h := tendsto_iidProb_on hd unroot (hon q hq4) (on := on) hEv (hdq q hq)
    exact tendsto_iidProb_of_imp hd (Eventually.of_forall fun m ω hω s hs => (hω s hs).trans_le (hle m q hq)) h

/-- The levels with the T3 test. Parallel to `exists_levels_on`, with `χ²₂` for `χ²₁` as in `exists_levels_t3`. -/
theorem exists_levels_t3_on [Nonempty X] (hN : N.IsPhylogenetic) (hθ : N.IsMetric θ) (hρ : 0 ≤ ρ ∧ ρ ≤ 1)
    (hdet : T3Detectable N (nmscCF N θ ρ)) (hon : Covers on) :
    ∃ α : ℕ → ℝ, Tendsto α atTop (𝓝 0) ∧ (∀ m, 0 < α m) ∧ T3RejectsOn N θ ρ on α := by
  have hd : IsDist (geneTreeDist N θ ρ) := ⟨geneTreeDist_nonneg hN hθ hρ, sum_geneTreeDist hN hθ hρ⟩
  have hs := displaysOne_nmsc (X := X) hN (θ := θ) (ρ := ρ)
  let Q : Finset (Finset X) := univ.filter fun q => q.card = 4 ∧ ¬ IsTreelike N q
  have hex : ∀ q : Finset X, ∃ d : ℝ, 0 < d ∧ (q ∈ Q → Tendsto (fun n : ℕ =>
      iidProb (geneTreeDist N θ ρ) n fun ω =>
        ∀ s ∈ treesOn q, t3PValue (quartetCount unroot ω) s < chiSqTwoTail (n * d)) atTop (𝓝 1)) := by
    intro q
    by_cases hq : q ∈ Q
    · obtain ⟨hq4, hnt⟩ := (mem_filter.mp hq).2
      obtain ⟨d, hd0, h⟩ := QuartetTests.t3Test_alternative hd hs hq4 (hdet.blob q hq4 hnt)
      exact ⟨d, hd0, fun _ => tendsto_iidProb_of_imp hd (Eventually.of_forall fun n ω hω => hω.2) h⟩
    · exact ⟨1, one_pos, fun h => absurd h hq⟩
  choose d hd0 hdq using hex
  let α : ℕ → ℝ := fun m => Q.fold max (chiSqTwoTail (m * 1)) fun q => chiSqTwoTail ((coverCount (on m) q : ℕ) * d q)
  have hle : ∀ m : ℕ, ∀ q ∈ Q, chiSqTwoTail ((coverCount (on m) q : ℕ) * d q) ≤ α m := fun m q hq =>
    (Finset.le_fold_max _).mpr (Or.inr ⟨q, hq, le_rfl⟩)
  have hbase : ∀ m : ℕ, chiSqTwoTail (m * 1) ≤ α m := fun m => (Finset.le_fold_max _).mpr (Or.inl le_rfl)
  have hpos : ∀ t : ℝ, 0 < chiSqTwoTail t := fun t => Real.exp_pos _
  refine ⟨α, ?_, fun m => (hpos _).trans_le (hbase m), ?_⟩
  · have hsum : Tendsto (fun m : ℕ => chiSqTwoTail (m * 1) +
        ∑ q ∈ Q, chiSqTwoTail ((coverCount (on m) q : ℕ) * d q)) atTop (𝓝 0) := by
      have := (tendsto_chiSqTwoTail_comp (k := id) tendsto_id one_pos).add
        (tendsto_finsetSum Q fun q hq => tendsto_chiSqTwoTail_comp (hon q (mem_filter.mp hq).2.1) (hd0 q))
      simpa using this
    refine squeeze_zero (fun m => (hpos _).le.trans (hbase m)) (fun m => ?_) hsum
    refine Finset.fold_max_le _ |>.mpr ⟨?_, fun q hq => ?_⟩
    · exact le_add_of_nonneg_right (Finset.sum_nonneg fun _ _ => (hpos _).le)
    · exact (Finset.single_le_sum (f := fun q => chiSqTwoTail ((coverCount (on m) q : ℕ) * d q))
        (fun _ _ => (hpos _).le) hq).trans (le_add_of_nonneg_left (hpos _).le)
  · intro q hq4 hnt
    have hq : q ∈ Q := mem_filter.mpr ⟨mem_univ _, hq4, hnt⟩
    have hEv : ∀ n : ℕ, DependsOnTaxa q fun c => ∀ s ∈ treesOn q, t3PValue c s < chiSqTwoTail (n * d q) :=
      fun n c c' hcc => forall₂_congr fun s hs => by rw [t3PValue_congr hs hcc]
    have h := tendsto_iidProb_on hd unroot (hon q hq4) (on := on) hEv (hdq q hq)
    exact tendsto_iidProb_of_imp hd (Eventually.of_forall fun m ω hω s hs => (hω s hs).trans_le (hle m q hq)) h

/-- Levels known in advance: if `log α_m` is small against the number of gene trees containing each set of four taxa, the cut test rejects. With all
taxa on all gene trees this is `TINNiK.rejects_of_log`. -/
theorem rejectsOn_of_log [Nonempty X] (hN : N.IsPhylogenetic) (hθ : N.IsMetric θ) (hρ : 0 ≤ ρ ∧ ρ ≤ 1)
    (hdet : AllmanEtAl2023.CFDetectable N (nmscCF N θ ρ)) (hon : Covers on) {α : ℕ → ℝ} (hα : ∀ m, 0 < α m)
    (hαlog : ∀ q : Finset X, q.card = 4 → Tendsto (fun m => Real.log (α m) / (coverCount (on m) q : ℕ)) atTop (𝓝 0)) :
    RejectsOn N θ ρ on α := by
  intro q hq4 hnt
  have hd : IsDist (geneTreeDist N θ ρ) := ⟨geneTreeDist_nonneg hN hθ hρ, sum_geneTreeDist hN hθ hρ⟩
  obtain ⟨d, hd0, h⟩ := QuartetTests.cutTest_alternative hd hq4 (hdet.blob q hq4 hnt)
  have hEv : ∀ n : ℕ, DependsOnTaxa q fun c => ∀ s ∈ treesOn q, cutPValue c s < chiSqOneTail (n * d) :=
    fun n c c' hcc => forall₂_congr fun s hs => by rw [cutPValue_congr hs hcc]
  have hlim := tendsto_iidProb_on hd unroot (hon q hq4) (on := on) hEv h
  refine tendsto_iidProb_of_imp hd ?_ hlim
  have h1 : ∀ᶠ m in atTop, -(d / 2) < Real.log (α m) / (coverCount (on m) q : ℕ) :=
    (hαlog q hq4).eventually (lt_mem_nhds (by linarith))
  filter_upwards [h1, (hon q hq4).eventually (eventually_gt_atTop 0)] with m hm hm0 ω hω s hs
  have hm' : (0 : ℝ) < (coverCount (on m) q : ℕ) := by exact_mod_cast hm0
  refine (hω s hs).trans_le ?_
  have ht : (0 : ℝ) ≤ (coverCount (on m) q : ℕ) * d := by positivity
  refine (QuartetTests.chiSqOneTail_le_chiSqTwoTail ht).trans ?_
  rw [chiSqTwoTail, ← Real.le_log_iff_exp_le (hα m)]
  have := (lt_div_iff₀ hm').mp hm
  linarith

/-! ### Theorem 4 with missing taxa -/

/-- The tests are right on all sets of four taxa, with the cut test and missing taxa. -/
theorem tests_correct_on (hN : N.IsPhylogenetic) (hX : 4 ≤ Fintype.card X) (hθ : N.IsMetric θ) (hρ : 0 ≤ ρ ∧ ρ ≤ 1)
    (hdet : AllmanEtAl2023.CFDetectable N (nmscCF N θ ρ)) (hon : Covers on) {α : ℕ → ℝ} (hα₀ : Tendsto α atTop (𝓝 0))
    (hrej : RejectsOn N θ ρ on α) {β : ℝ} (hβ : 0 < β) {ml : (QuartetTree X → ℝ) → Finset X → QuartetTree X}
    (hml : IsMLSelection ml) :
    Tendsto (fun m => iidProb (geneTreeDist N θ ρ) m fun ω => ∀ q : Finset X, q.card = 4 →
      GoodOn N ml cutPValue β (α m) (quartetCountOn unroot (on m) ω) q) atTop (𝓝 1) := by
  have hne : Nonempty X := Fintype.card_pos_iff.mp (by omega)
  have hd : IsDist (geneTreeDist N θ ρ) := ⟨geneTreeDist_nonneg hN hθ hρ, sum_geneTreeDist hN hθ hρ⟩
  refine tendsto_iidProb_of_imp hd (Eventually.of_forall fun m ω hω q hq => hω ⟨q, hq⟩)
    (tendsto_iidProb_forall hd (ι := {q : Finset X // q.card = 4})
      (fun q m ω => GoodOn N ml cutPValue β (α m) (quartetCountOn unroot (on m) ω) q.val)
      fun q => tendsto_goodOn_cut hN hX hθ hρ hdet hon hα₀ hrej hβ hml q.property)

/-- **Theorem 4 with missing taxa at given parameters** (`tinnik:missing_taxa`): at parameters with CF-detectability, for any inheritance correlation, if
each set of four taxa is on more and more gene trees, then for levels `α_m → 0` at which the cut test rejects, any `β > 0`, `δ < 2`, any exact tree
builder and any selection of maximum likelihood topologies, the TINNiK algorithm on the counts of the gene trees with the taxa kept infers the tree of blobs,
with probability tending to one. -/
theorem theorem4_missing_of_rejects (hN : N.IsPhylogenetic) (hX : 4 ≤ Fintype.card X) (hθ : N.IsMetric θ)
    (hρ : 0 ≤ ρ ∧ ρ ≤ 1) (hdet : AllmanEtAl2023.CFDetectable N (nmscCF N θ ρ)) (hon : Covers on)
    {α : ℕ → ℝ} (hα₀ : Tendsto α atTop (𝓝 0)) (hrej : RejectsOn N θ ρ on α) {β δ : ℝ} (hβ : 0 < β) (hδ₂ : δ < 2)
    {M : TreeBuilder X} (hM : IsExactBuilder M) {ml : (QuartetTree X → ℝ) → Finset X → QuartetTree X}
    (hml : IsMLSelection ml) :
    Tendsto (fun m => iidProb (geneTreeDist N θ ρ) m fun ω =>
      tinnik ml (α m) β δ M (quartetCountOn unroot (on m) ω) = treeOfBlobs N) atTop (𝓝 1) := by
  have hne : Nonempty X := Fintype.card_pos_iff.mp (by omega)
  have hd : IsDist (geneTreeDist N θ ρ) := ⟨geneTreeDist_nonneg hN hθ hρ, sum_geneTreeDist hN hθ hρ⟩
  refine tendsto_iidProb_of_imp hd (Eventually.of_forall fun m ω hω => ?_)
    (tests_correct_on hN hX hθ hρ hdet hon hα₀ hrej hβ hml)
  exact tinnikOf_eq_of_goodOn hN hX hδ₂ hM hω

/-- **Theorem 4 with missing taxa at parameters with CF-detectability** (`tinnik:missing_taxa`), with the levels of `exists_levels_on`. -/
theorem theorem4_missing_of_cfDetectable (hN : N.IsPhylogenetic) (hX : 4 ≤ Fintype.card X) (hθ : N.IsMetric θ)
    (hρ : 0 ≤ ρ ∧ ρ ≤ 1) (hdet : AllmanEtAl2023.CFDetectable N (nmscCF N θ ρ)) (hon : Covers on) :
    ∃ α : ℕ → ℝ, Tendsto α atTop (𝓝 0) ∧ (∀ m, 0 < α m) ∧
      ∀ (β δ : ℝ), 0 < β → δ < 2 → ∀ (M : TreeBuilder X), IsExactBuilder M →
      ∀ (ml : (QuartetTree X → ℝ) → Finset X → QuartetTree X), IsMLSelection ml →
        Tendsto (fun m => iidProb (geneTreeDist N θ ρ) m fun ω =>
          tinnik ml (α m) β δ M (quartetCountOn unroot (on m) ω) = treeOfBlobs N) atTop (𝓝 1) := by
  have hne : Nonempty X := Fintype.card_pos_iff.mp (by omega)
  obtain ⟨α, hα₀, hαpos, hrej⟩ := exists_levels_on hN hθ hρ hdet hon
  exact ⟨α, hα₀, hαpos, fun β δ hβ hδ₂ M hM ml hml =>
    theorem4_missing_of_rejects hN hX hθ hρ hdet hon hα₀ hrej hβ hδ₂ hM hml⟩

/-- **Theorem 4 with missing taxa** (`tinnik:missing_taxa`), as Theorem 4 is stated: for generic numerical parameters on a binary network, and for taxa kept on
the gene trees that leave each set of four taxa on more and more of them, there is a sequence `α_m → 0` such that for any `β > 0` and `2 > δ ≥ 0`, the
TINNiK algorithm using the cut test on `m` independent gene trees from the NMSC, with these taxa, infers the tree of blobs with probability tending to one.

This is the sentence before TINNiK's Theorem 4, "generalizing from this is straightforward". All taxa on all gene trees is the case `covers_univ`. -/
theorem theorem4_missing (hN : N.IsPhylogenetic) (hX : 4 ≤ Fintype.card X) (hBin : N.IsBinary) :
    ∃ A : Set (MetricData E), IsGenericNull N A ∧
      ∀ θ, N.IsMetric θ → θ ∉ A → ∀ on : (m : ℕ) → Fin m → Finset X, Covers on →
        ∃ α : ℕ → ℝ, Tendsto α atTop (𝓝 0) ∧ (∀ m, 0 < α m) ∧
          ∀ (β δ : ℝ), 0 < β → 0 ≤ δ → δ < 2 → ∀ (M : TreeBuilder X), IsExactBuilder M →
          ∀ (ml : (QuartetTree X → ℝ) → Finset X → QuartetTree X), IsMLSelection ml →
            Tendsto (fun m => iidProb (geneTreeDist N θ 0) m fun ω =>
              tinnik ml (α m) β δ M (quartetCountOn unroot (on m) ω) = treeOfBlobs N) atTop (𝓝 1) := by
  refine ⟨{θ | N.IsMetric θ ∧ ¬ AllmanEtAl2023.CFDetectable N (nmscCF N θ 0)},
    AllmanEtAl2023.cfDetectable_generic hN hBin, fun θ hθ hA on hon => ?_⟩
  have hdet : AllmanEtAl2023.CFDetectable N (nmscCF N θ 0) := by
    by_contra hn
    exact hA ⟨hθ, hn⟩
  obtain ⟨α, hα₀, hαpos, h⟩ := theorem4_missing_of_cfDetectable hN hX hθ ⟨le_rfl, zero_le_one⟩ hdet hon
  exact ⟨α, hα₀, hαpos, fun β δ hβ _ hδ₂ M hM ml hml => h β δ hβ hδ₂ M hM ml hml⟩

/-- **The T3 option with missing taxa** (`tinnik:missing_taxa`), under what the T3 test needs (`T3Detectable`). -/
theorem theorem4T3_missing (hN : N.IsPhylogenetic) (hX : 4 ≤ Fintype.card X) (hθ : N.IsMetric θ)
    (hρ : 0 ≤ ρ ∧ ρ ≤ 1) (hdet : T3Detectable N (nmscCF N θ ρ)) (hon : Covers on) :
    ∃ α : ℕ → ℝ, Tendsto α atTop (𝓝 0) ∧ (∀ m, 0 < α m) ∧
      ∀ (β δ : ℝ), 0 < β → δ < 2 → ∀ (M : TreeBuilder X), IsExactBuilder M →
      ∀ (ml : (QuartetTree X → ℝ) → Finset X → QuartetTree X), IsT3MLSelection ml →
        Tendsto (fun m => iidProb (geneTreeDist N θ ρ) m fun ω =>
          tinnikT3 ml (α m) β δ M (quartetCountOn unroot (on m) ω) = treeOfBlobs N) atTop (𝓝 1) := by
  have hne : Nonempty X := Fintype.card_pos_iff.mp (by omega)
  have hd : IsDist (geneTreeDist N θ ρ) := ⟨geneTreeDist_nonneg hN hθ hρ, sum_geneTreeDist hN hθ hρ⟩
  obtain ⟨α, hα₀, hαpos, hrej⟩ := exists_levels_t3_on hN hθ hρ hdet hon
  refine ⟨α, hα₀, hαpos, fun β δ hβ hδ₂ M hM ml hml => ?_⟩
  refine tendsto_iidProb_of_imp hd (Eventually.of_forall fun m ω hω => ?_)
    (tendsto_iidProb_forall hd (ι := {q : Finset X // q.card = 4})
      (fun q m ω => GoodOn N ml t3PValue β (α m) (quartetCountOn unroot (on m) ω) q.val)
      fun q => tendsto_goodOn_t3 hN hX hθ hρ hdet hon hα₀ hrej hβ hml q.property)
  exact tinnikOf_eq_of_goodOn hN hX hδ₂ hM fun q hq => hω ⟨q, hq⟩

end Sample

end TINNiK
