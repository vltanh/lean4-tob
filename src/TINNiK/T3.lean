module

public import AllmanEtAl2023.Basic
public import AllmanEtAl2023.CFDetectable
public import AllmanEtAl2023.CutOrder
public import Basic.Defs
public import External.MitchellAllmanRhodes2019.T3Test
public import External.Rhodes2020.Theorem2
public import Phylogenetics.NMSC.Basic
public import Basic.Testing.Tails
public import Phylogenetics.Tree.Metric
public import TINNiK.Basic

/-!
# TINNiK with the T3 test

TINNiK's B-quartet Inference Algorithm takes "a choice of test `T3` or `cut`" (TINNiK's text, lines 174,
192), and the default in MSCquartets is T3. Its Theorem 4 is stated "using the cut test". This file gives the
analogue with the T3 test, whose null is the T3 model of `src/External/MitchellAllmanRhodes2019/T3Test.lean`.

The extra hypothesis is the one the sources state: TINNiK's "it can be reasonable to assume that an unknown network has no
anomalous quartets and use a T3 hypothesis test" (line 144), TOB-QMC's condition 6b (`NoAnomalousQuartets`). Without it
the test rejects a cut concordance factor with `q > 1/3` (`QuartetTests.t3Test_alternative`). The theorem needs no more than
that, and on the sets with a 4-blob it needs less than CF-detectability: only that the concordance factor is off the T3
model (`T3Detectable`).

## Main results

* `testedBT3`, `testedTT3`, `tinnikT3`: the algorithm with the T3 option.
* `tests_correct_t3`: the T3 test's analogue of `tests_correct`.
* `theorem4T3`, `theorem4T3_explicit`: the analogues of `theorem4`, `theorem4_explicit`.
* `theorem4T3_of_tQuartet`: T-quartet-nonanomaly suffices for the output, in place of `NoAnomalousQuartets`: a treelike
  4-taxon set that the tree of blobs does not resolve is a B-quartet, so the T3 test rejecting it does no harm. The tests
  are not then correct on all subsets, as `tests_correct_t3` says they are under `NoAnomalousQuartets`.
-/

@[expose] public noncomputable section

open Phylogenetics Phylogenetics.RootedNetwork Finset Filter Topology
open scoped Classical

namespace TINNiK

variable {V E X : Type*} [Fintype X] [DecidableEq X]

/-! ### The algorithm with the T3 option -/

/-- A selection of maximum likelihood topologies on model T3: on each set of four taxa a quartet tree with the least T1
statistic. A topology of highest count is one (`QuartetTests.t1Stat_le_t1Stat_of_max`). The printed algorithm breaks ties at
random; the results hold for every selection. -/
def IsT3MLSelection (ml : (QuartetTree X → ℝ) → Finset X → QuartetTree X) : Prop :=
  ∀ c q, q.card = 4 → ml c q ∈ treesOn q ∧ ∀ r ∈ treesOn q, t1Stat c (ml c q) ≤ t1Stat c r

section Algorithm

variable (ml : (QuartetTree X → ℝ) → Finset X → QuartetTree X)

/-- Step 2 of the B-quartet inference algorithm with the T3 option: the 4-taxon sets judged B-quartets. A set is judged one
when the star test fails to reject at level `β`, or when the T3 test rejects at level `α`. Parallel to `testedB`. -/
def testedBT3 (α β : ℝ) (c : QuartetTree X → ℝ) : Set (Finset X) :=
  {q | q.card = 4 ∧ (β ≤ starPValue .lrt c q ∨ t3PValue c (ml c q) < α)}

/-- Step 2c with the T3 option: the maximum likelihood quartet trees of the other 4-taxon sets. Parallel to `testedT`. -/
def testedTT3 (α β : ℝ) (c : QuartetTree X → ℝ) : Set (QuartetTree X) :=
  {s | s.taxa ∉ testedBT3 ml α β c ∧ s = ml c s.taxa}

end Algorithm

/-- Steps 3 to 5 of the TINNiK algorithm, from the 4-taxon sets `B₀` and the quartet trees `τ` of Step 2, with cutoff `δ`. An
edge set to length zero is contracted, and so is one the method returned with length zero. `tinnik` is this on `testedB`,
`testedT` (`tinnik_eq_tinnikOf`). -/
def tinnikOf (B₀ : Set (Finset X)) (τ : Set (QuartetTree X)) (δ : ℝ) (M : TreeBuilder X) : Finset (Finset X) :=
  let B := {q | BInferred B₀ τ q}
  let built := M (quartetDistance B {s | s ∈ τ ∧ s.taxa ∉ B})
  built.1.filter fun A => A ∉ internalSides built.1 ∨ (δ ≤ built.2 A ∧ 0 < built.2 A)

theorem tinnik_eq_tinnikOf (ml : (QuartetTree X → ℝ) → Finset X → QuartetTree X) (α β δ : ℝ) (M : TreeBuilder X)
    (c : QuartetTree X → ℝ) : tinnik ml α β δ M c = tinnikOf (testedB ml α β c) (testedT ml α β c) δ M := rfl

/-- The output of the TINNiK algorithm with the T3 option, on the quartet counts `c`, with cutoff `δ`. -/
def tinnikT3 (ml : (QuartetTree X → ℝ) → Finset X → QuartetTree X) (α β δ : ℝ) (M : TreeBuilder X)
    (c : QuartetTree X → ℝ) : Finset (Finset X) :=
  tinnikOf (testedBT3 ml α β c) (testedTT3 ml α β c) δ M

/-! ### The hypotheses -/

/-- What the T3 test needs on all 4-taxon sets. An induced cut-edge split gives a concordance factor strictly on the half-line
of the split, and an induced network without one gives a concordance factor off model T3. This is weaker than CF-detectability
with no anomalous quartets (`T3Detectable.of_cfDetectable`) on the sets with a 4-blob. -/
structure T3Detectable {V E : Type*} (N : RootedNetwork V E X) (p : QuartetTree X → ℝ) : Prop where
  cut : ∀ s : QuartetTree X, InducedCutSplit N s → IsT1Strict p s
  blob : ∀ q : Finset X, q.card = 4 → ¬ IsTreelike N q → ¬ IsT3Null p q

/-- CF-detectability with no anomalous quartets gives what the T3 test needs. -/
theorem T3Detectable.of_cfDetectable {V E : Type*} {N : RootedNetwork V E X} {p : QuartetTree X → ℝ}
    (hdet : AllmanEtAl2023.CFDetectable N p) (hno : NoAnomalousQuartets N p) : T3Detectable N p :=
  ⟨fun s hs => ⟨hno s hs, (hdet.cut s hs).2⟩, fun q hq hnt =>
    QuartetTests.not_isT3Null_of_isNonCut (hdet.blob q hq hnt)⟩

/-- What the T3 test needs excludes the centroid, which is on model T3. -/
theorem noCentroidCF_of_t3Detectable {V E : Type*} {N : RootedNetwork V E X} {p : QuartetTree X → ℝ}
    (hdet : T3Detectable N p) : NoCentroidCF p := by
  intro q hq hall
  by_cases htl : IsTreelike N q
  · obtain ⟨s, hs, hc⟩ := htl
    obtain ⟨r, hr⟩ := Finset.card_pos.mp
      (by rw [QuartetTree.card_alternatives]; norm_num : 0 < s.alternatives.card)
    have hrq : r ∈ treesOn q :=
      mem_treesOn.2 ((QuartetTree.mem_alternatives.1 hr).1.trans (mem_treesOn.1 hs))
    exact ((hdet.cut s hc).1 r hr).ne ((hall r hrq).trans (hall s hs).symm)
  · refine hdet.blob q hq htl ?_
    obtain ⟨s, hs⟩ : (treesOn q).Nonempty := by
      rw [← Finset.card_pos, card_treesOn hq]
      norm_num
    have hmem : ∀ r ∈ s.alternatives, r ∈ treesOn q := fun r hr =>
      mem_treesOn.2 ((QuartetTree.mem_alternatives.1 hr).1.trans (mem_treesOn.1 hs))
    refine ⟨s, hs, fun r hr => ?_, fun r hr r' hr' => ?_⟩
    · rw [hall r (hmem r hr), hall s hs]
    · rw [hall r (hmem r hr), hall r' (hmem r' hr')]

/-! ### The deterministic part -/

/-- Steps 3 to 5 from their outcome: when the closure is the set of B-quartets and the quartet trees of the other sets are those
of the tree of blobs, the algorithm returns the tree of blobs. The quartet distance is then the tree metric of the quartet
metrization of the tree of blobs (Rhodes 2020, Theorem 2); an exact tree builder returns it; and the internal branches of length
at least `2` survive the cutoff `δ < 2`. This is the last part of the private `tinnik_eq_of_tests` of `src/TINNiK/Basic.lean`. -/
theorem tinnikOf_eq_of_closure {V E : Type*} {N : RootedNetwork V E X} (hN : N.IsPhylogenetic)
    (hX : 4 ≤ Fintype.card X) {δ : ℝ} (hδ₂ : δ < 2) {M : TreeBuilder X} (hM : IsExactBuilder M)
    {B₀ : Set (Finset X)} {τ : Set (QuartetTree X)}
    (hBset : {q | BInferred B₀ τ q} = {q | q.card = 4 ∧ IsBQuartet N q})
    (hτ : {s : QuartetTree X | s ∈ τ ∧ s.taxa ∉ {q | q.card = 4 ∧ IsBQuartet N q}} =
      {s | Displays (treeOfBlobs N) s}) :
    tinnikOf B₀ τ δ M = treeOfBlobs N := by
  have hne : Nonempty X := Fintype.card_pos_iff.mp (by omega)
  have hTB : IsUnrootedTree (treeOfBlobs N) := treeOfBlobs_isUnrootedTree hN
  have hdist : quartetDistance {q | q.card = 4 ∧ IsBQuartet N q}
      {s | Displays (treeOfBlobs N) s} =
      treeMetric (treeOfBlobs N) (External.Rhodes2020.quartetWeight (treeOfBlobs N)) := by
    funext x y
    by_cases hxy : x = y
    · subst hxy
      simp only [quartetDistance, ↓reduceIte, treeMetric]
      refine (Finset.sum_eq_zero fun A hA => ?_).symm
      have := Finset.mem_filter.mp hA
      exact absurd this.2.1 this.2.2
    · rw [External.Rhodes2020.theorem2 hTB hxy]
      exact congrFun (congrFun (quartetDistance_congr (fun q h4 => by
        simp only [Set.mem_ofPred_eq, h4, true_and]; rfl) rfl) x) y
  have hw : ∀ A ∈ treeOfBlobs N, 0 < External.Rhodes2020.quartetWeight (treeOfBlobs N) A ∧
      External.Rhodes2020.quartetWeight (treeOfBlobs N) Aᶜ =
        External.Rhodes2020.quartetWeight (treeOfBlobs N) A := fun A hA =>
    ⟨lt_of_lt_of_le two_pos (External.Rhodes2020.quartetWeight_ge_two hTB hX hA),
      External.Rhodes2020.quartetWeight_compl _ _⟩
  obtain ⟨h0, h1, h2, h3⟩ := hM _ _ hTB hw
  simp only [tinnikOf]
  rw [hBset, hτ, hdist]
  have hX2 : 2 ≤ Fintype.card X := by omega
  have hTfam := (isUnrootedTree_iff hX2 _).mp hTB
  have hbuilt := (isUnrootedTree_iff hX2 _).mp h0
  ext A
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨hA, hor⟩
    by_contra hnA
    rcases hor with hor | ⟨-, hpos⟩
    · -- a side of a tree that is not internal is a singleton or the complement of one
      apply hnA
      have hne := hbuilt.nonempty A hA
      have hne' := hbuilt.compl_nonempty A hA
      simp only [internalSides, Finset.mem_filter, not_and_or, not_le] at hor
      rcases hor with hor | hor | hor
      · exact absurd hA hor
      · obtain ⟨x, rfl⟩ := Finset.card_eq_one.mp
          (le_antisymm (by omega) (Finset.card_pos.mpr hne))
        exact hTfam.singleton_mem x
      · obtain ⟨x, hx⟩ := Finset.card_eq_one.mp
          (le_antisymm (by omega) (Finset.card_pos.mpr hne'))
        have := hTfam.compl_mem _ (hTfam.singleton_mem x)
        rwa [← hx, compl_compl] at this
    · exact absurd hpos (not_lt.mpr (h3 A hA hnA))
  · intro hA
    refine ⟨h1 hA, Or.inr ?_⟩
    rw [h2 A hA]
    have h2le := External.Rhodes2020.quartetWeight_ge_two hTB hX hA
    exact ⟨hδ₂.le.trans h2le, lt_of_lt_of_le two_pos h2le⟩

/-- The deterministic part of Theorem 4 with the T3 option: from correct answers on all 4-taxon sets the algorithm returns
the tree of blobs, by `closure_complete` and `closure_sound`. -/
private theorem tinnikT3_eq_of_tests {V E : Type*} {N : RootedNetwork V E X} (hN : N.IsPhylogenetic)
    (hX : 4 ≤ Fintype.card X) {ml : (QuartetTree X → ℝ) → Finset X → QuartetTree X} {a β δ : ℝ}
    (hδ₂ : δ < 2) {M : TreeBuilder X} (hM : IsExactBuilder M) {c : QuartetTree X → ℝ}
    (hB : testedBT3 ml a β c = {q | q.card = 4 ∧ ¬ IsTreelike N q})
    (hT : testedTT3 ml a β c = {s | InducedCutSplit N s}) :
    tinnikT3 ml a β δ M c = treeOfBlobs N := by
  unfold tinnikT3
  rw [hB, hT]
  refine tinnikOf_eq_of_closure hN hX hδ₂ hM ?_ ?_
  · ext q
    simp only [Set.mem_ofPred_eq]
    constructor
    · intro h
      exact ⟨AllmanEtAl2023.Algorithm.card_of_bInferred (B₀ := {q' | q'.card = 4 ∧ ¬ IsTreelike N q'}) (fun q hq => hq.1) h,
        AllmanEtAl2023.closure_sound hN h⟩
    · rintro ⟨h4, h⟩
      exact AllmanEtAl2023.closure_complete hN h4 h
  · ext s
    simp only [Set.mem_ofPred_eq, AllmanEtAl2023.displays_treeOfBlobs_iff hN s,
      QuartetTree.card_taxa, true_and]

/-- The answers wanted on a set of four taxa: the star test rejects; a cut-edge split on the induced network is the maximum
likelihood topology, and the T3 test does not reject; and without a cut-edge split the T3 test rejects. -/
private def QGoodT3 {V E : Type*} (N : RootedNetwork V E X)
    (ml : (QuartetTree X → ℝ) → Finset X → QuartetTree X) (β a : ℝ) (c : QuartetTree X → ℝ)
    (q : Finset X) : Prop :=
  starPValue .lrt c q < β ∧ (∀ s ∈ treesOn q, InducedCutSplit N s → ml c q = s ∧ a ≤ t3PValue c s) ∧
    (¬ IsTreelike N q → t3PValue c (ml c q) < a)

/-- The tests are right when they are right on each set of four taxa. -/
private theorem tests_of_qGoodT3 {V E : Type*} {N : RootedNetwork V E X}
    {ml : (QuartetTree X → ℝ) → Finset X → QuartetTree X}
    {β a : ℝ} {c : QuartetTree X → ℝ} (h : ∀ q : Finset X, q.card = 4 → QGoodT3 N ml β a c q) :
    testedBT3 ml a β c = {q | q.card = 4 ∧ ¬ IsTreelike N q} ∧
      testedTT3 ml a β c = {s | InducedCutSplit N s} := by
  have hB : testedBT3 ml a β c = {q | q.card = 4 ∧ ¬ IsTreelike N q} := by
    ext q
    simp only [testedBT3, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨h4, hor⟩
      obtain ⟨h1, h2, -⟩ := h q h4
      refine ⟨h4, ?_⟩
      rintro ⟨s, hs, hcs⟩
      obtain ⟨h3, h5⟩ := h2 s hs hcs
      rcases hor with hor | hor
      · exact absurd h1 (not_lt.mpr hor)
      · rw [h3] at hor
        exact absurd hor (not_lt.mpr h5)
    · rintro ⟨h4, hnt⟩
      exact ⟨h4, Or.inr ((h q h4).2.2 hnt)⟩
  refine ⟨hB, ?_⟩
  ext s
  simp only [testedTT3, Set.mem_ofPred_eq, hB]
  have hsmem : s ∈ treesOn s.taxa := Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩
  constructor
  · rintro ⟨hn, hs⟩
    have htl : IsTreelike N s.taxa := by
      by_contra hnt
      exact hn ⟨QuartetTree.card_taxa s, hnt⟩
    obtain ⟨s₀, hs₀, hc₀⟩ := htl
    obtain ⟨h1, -⟩ := (h s.taxa (QuartetTree.card_taxa s)).2.1 s₀ hs₀ hc₀
    rw [hs, h1]
    exact hc₀
  · intro hc
    exact ⟨fun hn => hn.2 ⟨s, hsmem, hc⟩,
      ((h s.taxa (QuartetTree.card_taxa s)).2.1 s hsmem hc).1.symm⟩

/-! ### The tests on a sample -/

/-- At a concordance factor strictly on the half-line of `s₀`, the maximum likelihood topology of model T3 is `s₀`, and the T3
test does not reject. -/
private theorem tendsto_good_t3 {V E : Type*} [Fintype V] [Fintype E] [Nonempty X]
    {N : RootedNetwork V E X} (hN : N.IsPhylogenetic) {θ : MetricData E} (hθ : N.IsMetric θ)
    {ρ : ℝ} (hρ : 0 ≤ ρ ∧ ρ ≤ 1) {α : ℕ → ℝ} (hα₀ : Tendsto α atTop (𝓝 0))
    {ml : (QuartetTree X → ℝ) → Finset X → QuartetTree X}
    (hml : IsT3MLSelection ml) {s₀ : QuartetTree X}
    (hc : IsT1Strict (nmscCF N θ ρ) s₀) :
    Tendsto (fun m => iidProb (geneTreeDist N θ ρ) m fun ω =>
      ml (quartetCount unroot ω) s₀.taxa = s₀ ∧
        α m ≤ t3PValue (quartetCount unroot ω) s₀) atTop (𝓝 1) := by
  have hd : IsDist (geneTreeDist N θ ρ) :=
    ⟨geneTreeDist_nonneg hN hθ hρ, sum_geneTreeDist hN hθ hρ⟩
  have hs := displaysOne_nmsc (θ := θ) (ρ := ρ) hN
  have hq := QuartetTree.card_taxa s₀
  have hs₀ : s₀ ∈ treesOn s₀.taxa := Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩
  have hnull := QuartetTests.t3Test_null hd hs (s := s₀) hc
    (fun r _ => nmscCF_pos hN hθ hρ r) hα₀
  refine tendsto_iidProb_of_imp hd (Eventually.of_forall fun m ω hω => ?_) hnull
  obtain ⟨h2, h3⟩ := hω
  refine ⟨?_, h3⟩
  obtain ⟨hm1, hm2⟩ := hml (quartetCount unroot ω) s₀.taxa hq
  by_contra hneq
  have halt : ml (quartetCount unroot ω) s₀.taxa ∈ s₀.alternatives :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hm1).2, hneq⟩
  exact absurd (hm2 s₀ hs₀) (not_le.mpr (h2 _ halt))

/-- The T3 test rejects at the levels `α`, with probability tending to one, on the 4-taxon sets with no cut-edge split on their
induced network. Parallel to `Rejects`. -/
def T3Rejects {V E : Type*} [Fintype V] [Fintype E] (N : RootedNetwork V E X) (θ : MetricData E) (ρ : ℝ)
    (α : ℕ → ℝ) : Prop :=
  ∀ q : Finset X, q.card = 4 → ¬ IsTreelike N q →
    Tendsto (fun m => iidProb (geneTreeDist N θ ρ) m fun ω =>
      ∀ s ∈ treesOn q, t3PValue (quartetCount unroot ω) s < α m) atTop (𝓝 1)

/-- On each set of four taxa, the tests give the wanted answers with probability tending to one. -/
private theorem tendsto_qGoodT3 {V E : Type*} [Fintype V] [Fintype E] {N : RootedNetwork V E X}
    (hN : N.IsPhylogenetic) (hX : 4 ≤ Fintype.card X) {θ : MetricData E} (hθ : N.IsMetric θ)
    {ρ : ℝ} (hρ : 0 ≤ ρ ∧ ρ ≤ 1) (hdet : T3Detectable N (nmscCF N θ ρ))
    {α : ℕ → ℝ} (hα₀ : Tendsto α atTop (𝓝 0)) (hrej : T3Rejects N θ ρ α)
    {β : ℝ} (hβ : 0 < β) {ml : (QuartetTree X → ℝ) → Finset X → QuartetTree X}
    (hml : IsT3MLSelection ml) {q : Finset X} (hq : q.card = 4) :
    Tendsto (fun m => iidProb (geneTreeDist N θ ρ) m fun ω =>
      QGoodT3 N ml β (α m) (quartetCount unroot ω) q) atTop (𝓝 1) := by
  have hne : Nonempty X := Fintype.card_pos_iff.mp (by omega)
  have hd : IsDist (geneTreeDist N θ ρ) :=
    ⟨geneTreeDist_nonneg hN hθ hρ, sum_geneTreeDist hN hθ hρ⟩
  have hcases : Tendsto (fun m => iidProb (geneTreeDist N θ ρ) m fun ω =>
      (∀ s ∈ treesOn q, InducedCutSplit N s →
        ml (quartetCount unroot ω) q = s ∧ α m ≤ t3PValue (quartetCount unroot ω) s) ∧
      (¬ IsTreelike N q → t3PValue (quartetCount unroot ω) (ml (quartetCount unroot ω) q) < α m))
      atTop (𝓝 1) := by
    by_cases htl : IsTreelike N q
    · -- a cut-edge split on the induced network: the T3 test does not reject
      obtain ⟨s₀, hs₀, hc₀⟩ := htl
      have hst : s₀.taxa = q := (Finset.mem_filter.mp hs₀).2
      subst hst
      refine tendsto_iidProb_of_imp hd (Eventually.of_forall fun m ω hω => ?_)
        (tendsto_good_t3 hN hθ hρ hα₀ hml (hdet.cut s₀ hc₀))
      refine ⟨fun s hsq hcs => ?_, fun hnt => absurd ⟨s₀, hs₀, hc₀⟩ hnt⟩
      have hss : s = s₀ := AllmanEtAl2023.inducedCutSplit_unique hN hcs hc₀
        (Finset.mem_filter.mp hsq).2
      subst hss
      exact hω
    · -- no cut-edge split: the T3 test rejects, in particular at the maximum likelihood topology
      refine tendsto_iidProb_of_imp hd (Eventually.of_forall fun m ω hω => ?_) (hrej q hq htl)
      exact ⟨fun s hsq hcs => absurd ⟨s, hsq, hcs⟩ htl,
        fun _ => hω _ (hml (quartetCount unroot ω) q hq).1⟩
  exact tendsto_iidProb_and hd
    (tendsto_star hd (displaysOne_nmsc hN) hq (noCentroidCF_of_t3Detectable hdet q hq) hβ) hcases

/-- **The test-correctness step with the T3 test**, for any inheritance correlation `ρ`, under what the T3 test needs
(`T3Detectable`): for levels `α_m → 0` at which the T3 test rejects on the sets with no cut-edge split, and any `β > 0`, TINNiK's
hypothesis tests with the T3 option return the correct answer on all 4-taxon sets with probability tending to one. -/
theorem tests_correct_t3_of_t3Detectable {V E : Type*} [Fintype V] [Fintype E] {N : RootedNetwork V E X}
    (hN : N.IsPhylogenetic) (hX : 4 ≤ Fintype.card X) {θ : MetricData E} (hθ : N.IsMetric θ)
    {ρ : ℝ} (hρ : 0 ≤ ρ ∧ ρ ≤ 1) (hdet : T3Detectable N (nmscCF N θ ρ))
    {α : ℕ → ℝ} (hα₀ : Tendsto α atTop (𝓝 0)) (hrej : T3Rejects N θ ρ α)
    {β : ℝ} (hβ : 0 < β) {ml : (QuartetTree X → ℝ) → Finset X → QuartetTree X}
    (hml : IsT3MLSelection ml) :
    Tendsto (fun m => iidProb (geneTreeDist N θ ρ) m fun ω =>
      testedBT3 ml (α m) β (quartetCount unroot ω) = {q | q.card = 4 ∧ ¬ IsTreelike N q} ∧
        testedTT3 ml (α m) β (quartetCount unroot ω) = {s | InducedCutSplit N s}) atTop (𝓝 1) := by
  have hne : Nonempty X := Fintype.card_pos_iff.mp (by omega)
  have hd : IsDist (geneTreeDist N θ ρ) :=
    ⟨geneTreeDist_nonneg hN hθ hρ, sum_geneTreeDist hN hθ hρ⟩
  have hall := tendsto_iidProb_forall hd (ι := {q : Finset X // q.card = 4})
    (fun q m ω => QGoodT3 N ml β (α m) (quartetCount unroot ω) q.val)
    (fun q => tendsto_qGoodT3 hN hX hθ hρ hdet hα₀ hrej hβ hml q.property)
  refine tendsto_iidProb_of_imp hd (Eventually.of_forall fun m ω hω => ?_) hall
  exact tests_of_qGoodT3 fun q hq => hω ⟨q, hq⟩

/-- **The analogue of `tests_correct` with the T3 test**: at parameters satisfying CF-detectability with no anomalous quartets,
TINNiK's hypothesis tests with the T3 option return the correct answer on all 4-taxon sets with probability tending to one. -/
theorem tests_correct_t3 {V E : Type*} [Fintype V] [Fintype E] {N : RootedNetwork V E X}
    (hN : N.IsPhylogenetic) (hX : 4 ≤ Fintype.card X) {θ : MetricData E} (hθ : N.IsMetric θ)
    {ρ : ℝ} (hρ : 0 ≤ ρ ∧ ρ ≤ 1) (hdet : AllmanEtAl2023.CFDetectable N (nmscCF N θ ρ))
    (hno : NoAnomalousQuartets N (nmscCF N θ ρ))
    {α : ℕ → ℝ} (hα₀ : Tendsto α atTop (𝓝 0)) (hrej : T3Rejects N θ ρ α)
    {β : ℝ} (hβ : 0 < β) {ml : (QuartetTree X → ℝ) → Finset X → QuartetTree X}
    (hml : IsT3MLSelection ml) :
    Tendsto (fun m => iidProb (geneTreeDist N θ ρ) m fun ω =>
      testedBT3 ml (α m) β (quartetCount unroot ω) = {q | q.card = 4 ∧ ¬ IsTreelike N q} ∧
        testedTT3 ml (α m) β (quartetCount unroot ω) = {s | InducedCutSplit N s}) atTop (𝓝 1) :=
  tests_correct_t3_of_t3Detectable hN hX hθ hρ (T3Detectable.of_cfDetectable hdet hno) hα₀ hrej hβ hml

/-- Theorem 4 with the T3 option at given parameters, under what the T3 test needs, for levels `α_m → 0` at which the T3 test
rejects on the sets with no cut-edge split. -/
theorem theorem4T3_of_rejects [Fintype V] [Fintype E] {N : RootedNetwork V E X}
    (hN : N.IsPhylogenetic) (hX : 4 ≤ Fintype.card X) {θ : MetricData E}
    (hθ : N.IsMetric θ) (hdet : T3Detectable N (nmscCF N θ 0))
    {α : ℕ → ℝ} (hα₀ : Tendsto α atTop (𝓝 0)) (hrej : T3Rejects N θ 0 α)
    {β δ : ℝ} (hβ : 0 < β) (hδ₂ : δ < 2) {M : TreeBuilder X} (hM : IsExactBuilder M)
    {ml : (QuartetTree X → ℝ) → Finset X → QuartetTree X} (hml : IsT3MLSelection ml) :
    Tendsto (fun m => iidProb (geneTreeDist N θ 0) m fun ω =>
      tinnikT3 ml (α m) β δ M (quartetCount unroot ω) = treeOfBlobs N) atTop (𝓝 1) := by
  have hne : Nonempty X := Fintype.card_pos_iff.mp (by omega)
  have hρ : (0 : ℝ) ≤ 0 ∧ (0 : ℝ) ≤ 1 := ⟨le_rfl, zero_le_one⟩
  have hd : IsDist (geneTreeDist N θ 0) :=
    ⟨geneTreeDist_nonneg hN hθ hρ, sum_geneTreeDist hN hθ hρ⟩
  exact tendsto_iidProb_of_imp hd
    (Eventually.of_forall fun m ω hω => tinnikT3_eq_of_tests hN hX hδ₂ hM hω.1 hω.2)
    (tests_correct_t3_of_t3Detectable hN hX hθ hρ hdet hα₀ hrej hβ hml)

/-- Levels with `log(1/α_m) = o(m)` make the T3 test reject on the sets with no cut-edge split. -/
theorem t3Rejects_of_log [Fintype V] [Fintype E] [Nonempty X] {N : RootedNetwork V E X} (hN : N.IsPhylogenetic)
    {θ : MetricData E} (hθ : N.IsMetric θ) {ρ : ℝ} (hρ : 0 ≤ ρ ∧ ρ ≤ 1)
    (hdet : T3Detectable N (nmscCF N θ ρ))
    {α : ℕ → ℝ} (hα : ∀ m, 0 < α m) (hαlog : Tendsto (fun m : ℕ => Real.log (α m) / m) atTop (𝓝 0)) :
    T3Rejects N θ ρ α := fun _ hq htl =>
  QuartetTests.t3Test_rejects ⟨geneTreeDist_nonneg hN hθ hρ, sum_geneTreeDist hN hθ hρ⟩ (displaysOne_nmsc hN) hq
    (hdet.blob _ hq htl) hα hαlog

/-- `P(χ²₂ > m d) = exp(-m d / 2)` tends to zero, for `d > 0`. -/
theorem tendsto_chiSqTwoTail_mul {d : ℝ} (hd : 0 < d) :
    Tendsto (fun m : ℕ => chiSqTwoTail (m * d)) atTop (𝓝 0) := by
  have h1 : Tendsto (fun m : ℕ => (m : ℝ) * d / 2) atTop atTop :=
    (tendsto_natCast_atTop_atTop.atTop_mul_const hd).atTop_div_const (by norm_num)
  refine (Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp h1)).congr fun m => ?_
  simp [chiSqTwoTail, neg_div]

/-- **Levels as in the proof of Theorem 4, for the T3 test.** For each 4-taxon set `q` with no cut-edge split, with `d_q` the limit
of the statistic there, let `α'_m(q) = P(χ²₂ > m d_q)`, and let `α_m` be the maximum of the `α'_m(q)`, with `P(χ²₂ > m)` added so
that the maximum is over a nonempty set. The law `χ²₂` is what dominates the T3 test distribution
(`QuartetTests.t3Tail_le_chiSqTwoTail`), as `χ²₁` dominates the cut test's. -/
theorem exists_levels_t3 [Fintype V] [Fintype E] [Nonempty X] {N : RootedNetwork V E X} (hN : N.IsPhylogenetic)
    {θ : MetricData E} (hθ : N.IsMetric θ) {ρ : ℝ} (hρ : 0 ≤ ρ ∧ ρ ≤ 1)
    (hdet : T3Detectable N (nmscCF N θ ρ)) :
    ∃ α : ℕ → ℝ, Tendsto α atTop (𝓝 0) ∧ (∀ m, 0 < α m) ∧ T3Rejects N θ ρ α := by
  have hd : IsDist (geneTreeDist N θ ρ) :=
    ⟨geneTreeDist_nonneg hN hθ hρ, sum_geneTreeDist hN hθ hρ⟩
  classical
  let Q : Finset (Finset X) := univ.filter fun q => q.card = 4 ∧ ¬ IsTreelike N q
  have hex : ∀ q : Finset X, ∃ d : ℝ, 0 < d ∧ (q ∈ Q → Tendsto (fun n : ℕ =>
      iidProb (geneTreeDist N θ ρ) n fun ω =>
        ∀ s ∈ treesOn q, t3PValue (quartetCount unroot ω) s < chiSqTwoTail (n * d)) atTop (𝓝 1)) := by
    intro q
    by_cases hq : q ∈ Q
    · obtain ⟨hq4, hnt⟩ := (mem_filter.mp hq).2
      obtain ⟨d, hd0, h⟩ := QuartetTests.t3Test_alternative hd (displaysOne_nmsc hN) hq4 (hdet.blob q hq4 hnt)
      exact ⟨d, hd0, fun _ => tendsto_iidProb_of_imp hd (Eventually.of_forall fun n ω hω => hω.2) h⟩
    · exact ⟨1, one_pos, fun h => absurd h hq⟩
  choose d hd0 hdq using hex
  let α : ℕ → ℝ := fun m => Q.fold max (chiSqTwoTail (m * 1)) fun q => chiSqTwoTail (m * d q)
  have hle : ∀ m : ℕ, ∀ q ∈ Q, chiSqTwoTail (m * d q) ≤ α m := fun m q hq =>
    (Finset.le_fold_max _).mpr (Or.inr ⟨q, hq, le_rfl⟩)
  have hbase : ∀ m : ℕ, chiSqTwoTail (m * 1) ≤ α m := fun m =>
    (Finset.le_fold_max _).mpr (Or.inl le_rfl)
  have hpos : ∀ t : ℝ, 0 < chiSqTwoTail t := fun t => Real.exp_pos _
  refine ⟨α, ?_, fun m => (hpos _).trans_le (hbase m), ?_⟩
  · have hsum : Tendsto (fun m : ℕ => chiSqTwoTail (m * 1) + ∑ q ∈ Q, chiSqTwoTail (m * d q)) atTop (𝓝 0) := by
      have := (tendsto_chiSqTwoTail_mul (one_pos)).add
        (tendsto_finsetSum Q fun q _ => tendsto_chiSqTwoTail_mul (hd0 q))
      simpa using this
    refine squeeze_zero (fun m => (hpos _).le.trans (hbase m)) (fun m => ?_) hsum
    refine Finset.fold_max_le _ |>.mpr ⟨?_, fun q hq => ?_⟩
    · exact le_add_of_nonneg_right (Finset.sum_nonneg fun _ _ => (hpos _).le)
    · exact (Finset.single_le_sum (f := fun q => chiSqTwoTail (m * d q))
        (fun _ _ => (hpos _).le) hq).trans
        (le_add_of_nonneg_left (hpos _).le)
  · intro q hq4 hnt
    have hq : q ∈ Q := mem_filter.mpr ⟨mem_univ _, hq4, hnt⟩
    exact tendsto_iidProb_of_imp hd
      (Eventually.of_forall fun m ω hω s hs => (hω s hs).trans_le (hle m q hq)) (hdq q hq)

/-- **The analogue of TINNiK's Theorem 4 with the T3 test.** For generic numerical parameters on a binary network,
**with no anomalous quartets**, there is a sequence `α_m → 0` such that for any `β > 0` and `2 > δ ≥ 0`, the TINNiK algorithm with
the T3 test on `m` independent gene trees from the NMSC infers the tree of blobs with probability tending to one.

TINNiK states Theorem 4 "using the cut test", and states no consistency theorem for the T3 test; it says that it "can be reasonable
to assume that an unknown network has no anomalous quartets and use a T3 hypothesis test" (TINNiK's text, line 144).
The generic parameters are those with CF-detectability on all induced 4-taxon networks (`AllmanEtAl2023.cfDetectable_generic`, TINNiK's
Theorem 1). Having no anomalous quartets is a hypothesis on the parameters, not a generic property: anomalous quartets occur "for some
numerical parameter settings" (TOB-QMC v5, lines 118–120). It excludes the centroid (`noCentroidCF_of_t3Detectable`), so that the paper's
separate generic step for the centroid (`isGenericNull_centroid`) is not needed. -/
theorem theorem4T3 [Fintype V] [Fintype E] {N : RootedNetwork V E X}
    (hN : N.IsPhylogenetic) (hX : 4 ≤ Fintype.card X) (hBin : N.IsBinary) :
    ∃ A : Set (MetricData E), IsGenericNull N A ∧
      ∀ θ, N.IsMetric θ → θ ∉ A → NoAnomalousQuartets N (nmscCF N θ 0) →
        ∃ α : ℕ → ℝ, Tendsto α atTop (𝓝 0) ∧ (∀ m, 0 < α m) ∧
          ∀ (β δ : ℝ), 0 < β → 0 ≤ δ → δ < 2 →
          ∀ (M : TreeBuilder X), IsExactBuilder M →
          ∀ (ml : (QuartetTree X → ℝ) → Finset X → QuartetTree X), IsT3MLSelection ml →
            Tendsto (fun m => iidProb (geneTreeDist N θ 0) m fun ω =>
              tinnikT3 ml (α m) β δ M (quartetCount unroot ω) = treeOfBlobs N) atTop (𝓝 1) := by
  have hne : Nonempty X := Fintype.card_pos_iff.mp (by omega)
  refine ⟨{θ | N.IsMetric θ ∧ ¬ AllmanEtAl2023.CFDetectable N (nmscCF N θ 0)},
    AllmanEtAl2023.cfDetectable_generic hN hBin, fun θ hθ hA hno => ?_⟩
  have hdet : AllmanEtAl2023.CFDetectable N (nmscCF N θ 0) := by
    by_contra hn
    exact hA ⟨hθ, hn⟩
  have hdet' := T3Detectable.of_cfDetectable hdet hno
  obtain ⟨α, hα₀, hαpos, hrej⟩ := exists_levels_t3 hN hθ ⟨le_rfl, zero_le_one⟩ hdet'
  exact ⟨α, hα₀, hαpos, fun β δ hβ _ hδ₂ M hM ml hml =>
    theorem4T3_of_rejects hN hX hθ hdet' hα₀ hrej hβ hδ₂ hM hml⟩

/-- The analogue of `theorem4_explicit` with the T3 test: one sequence of levels for all networks and parameters, the upper tail of
`χ²₁` at `log m`. -/
theorem theorem4T3_explicit [Fintype V] [Fintype E] {N : RootedNetwork V E X}
    (hN : N.IsPhylogenetic) (hX : 4 ≤ Fintype.card X) {θ : MetricData E} (hθ : N.IsMetric θ)
    (hdet : AllmanEtAl2023.CFDetectable N (nmscCF N θ 0))
    (hno : NoAnomalousQuartets N (nmscCF N θ 0)) {β δ : ℝ} (hβ : 0 < β) (hδ₂ : δ < 2)
    {M : TreeBuilder X} (hM : IsExactBuilder M)
    {ml : (QuartetTree X → ℝ) → Finset X → QuartetTree X} (hml : IsT3MLSelection ml) :
    Tendsto (fun m : ℕ => iidProb (geneTreeDist N θ 0) m fun ω =>
      tinnikT3 ml (chiSqOneTail (Real.log m)) β δ M (quartetCount unroot ω) = treeOfBlobs N)
      atTop (𝓝 1) := by
  have hne : Nonempty X := Fintype.card_pos_iff.mp (by omega)
  have hdet' := T3Detectable.of_cfDetectable hdet hno
  exact theorem4T3_of_rejects hN hX hθ hdet' QuartetTests.tendsto_chiSqOneTail_log
    (t3Rejects_of_log hN hθ ⟨le_rfl, zero_le_one⟩ hdet' (fun _ => QuartetTests.chiSqOneTail_pos _)
      QuartetTests.tendsto_log_chiSqOneTail_log) hβ hδ₂ hM hml

/-! ### What the T3 option needs on all subsets, and what it needs for its output -/

/-- **Condition 6b is necessary for the tests to be correct on all subsets**: "Condition 6b regarding anomalous quartets is required by
TINNiK when using the T3 test option; otherwise, the null may be incorrectly rejected" (TOB-QMC v5, lines 115–117). If a cut-edge split
of an induced network has an anomalous concordance factor, the T3 test rejects it at levels with `log(1/α_m) = o(m)`, so its 4-taxon
set is judged a B-quartet with probability tending to one, though it is treelike. -/
theorem tendsto_mem_testedBT3_of_anomalous {V E : Type*} [Fintype V] [Fintype E] [Nonempty X]
    {N : RootedNetwork V E X} (hN : N.IsPhylogenetic) {θ : MetricData E} (hθ : N.IsMetric θ) {ρ : ℝ}
    (hρ : 0 ≤ ρ ∧ ρ ≤ 1) {s : QuartetTree X} (hlt : ∀ r ∈ s.alternatives, nmscCF N θ ρ s < nmscCF N θ ρ r)
    {α : ℕ → ℝ} (hα : ∀ m, 0 < α m) (hαlog : Tendsto (fun m : ℕ => Real.log (α m) / m) atTop (𝓝 0)) {β : ℝ}
    {ml : (QuartetTree X → ℝ) → Finset X → QuartetTree X} (hml : IsT3MLSelection ml) :
    Tendsto (fun m => iidProb (geneTreeDist N θ ρ) m fun ω =>
      s.taxa ∈ testedBT3 ml (α m) β (quartetCount unroot ω)) atTop (𝓝 1) := by
  have hd : IsDist (geneTreeDist N θ ρ) :=
    ⟨geneTreeDist_nonneg hN hθ hρ, sum_geneTreeDist hN hθ hρ⟩
  refine tendsto_iidProb_of_imp hd (Eventually.of_forall fun m ω hω => ?_)
    (QuartetTests.t3Test_rejects hd (displaysOne_nmsc hN) s.card_taxa
      (QuartetTests.not_isT3Null_of_anomalous hlt) hα hαlog)
  exact ⟨s.card_taxa, Or.inr (hω _ (hml _ _ s.card_taxa).1)⟩

/-- The closure from sets `B₀` and quartet trees `τ` that agree with the exact ones, except that a treelike set may be in `B₀` in place
of its split in `τ`, as long as it is a B-quartet. The closure is still the set of B-quartets: a step of the rule from a split of
`τ` is then a step from the set in `B₀`. -/
theorem closure_eq_of_relaxed {V E : Type*} {N : RootedNetwork V E X} (hN : N.IsPhylogenetic)
    {B₀ : Set (Finset X)} {τ : Set (QuartetTree X)}
    (h1 : ∀ q : Finset X, q.card = 4 → ¬ IsTreelike N q → q ∈ B₀)
    (h2 : ∀ q ∈ B₀, q.card = 4 ∧ IsBQuartet N q)
    (h3 : ∀ s ∈ τ, InducedCutSplit N s)
    (h4 : ∀ s, InducedCutSplit N s → s ∈ τ ∨ s.taxa ∈ B₀) :
    {q | BInferred B₀ τ q} = {q | q.card = 4 ∧ IsBQuartet N q} := by
  have hto : ∀ q, BInferred {q' | q'.card = 4 ∧ ¬ IsTreelike N q'} {s | InducedCutSplit N s} q →
      BInferred B₀ τ q := by
    intro q h
    induction h with
    | base q hq => exact .base q (h1 q hq.1 hq.2)
    | ruleB a b c d e t q h5 _ _ ht _ hq ih₁ ih₂ ih₃ => exact .ruleB a b c d e t q h5 ih₁ ih₂ ht ih₃ hq
    | ruleT a b c d e s q h5 _ _ hs hst hsep hq ih₁ ih₂ =>
      rcases h4 s hs with hsτ | hsB
      · exact .ruleT a b c d e s q h5 ih₁ ih₂ hsτ hst hsep hq
      · exact .ruleB a b c d e s.taxa q h5 ih₁ ih₂ hst (.base _ hsB) hq
  have hfrom : ∀ q, BInferred B₀ τ q →
      BInferred {q' | q'.card = 4 ∧ ¬ IsTreelike N q'} {s | InducedCutSplit N s} q := by
    intro q h
    induction h with
    | base q hq => exact AllmanEtAl2023.closure_complete hN (h2 q hq).1 (h2 q hq).2
    | ruleB a b c d e t q h5 _ _ ht _ hq ih₁ ih₂ ih₃ => exact .ruleB a b c d e t q h5 ih₁ ih₂ ht ih₃ hq
    | ruleT a b c d e s q h5 _ _ hs hst hsep hq ih₁ ih₂ =>
      exact .ruleT a b c d e s q h5 ih₁ ih₂ (h3 s hs) hst hsep hq
  ext q
  simp only [Set.mem_ofPred_eq]
  constructor
  · intro h
    have hf := hfrom q h
    exact ⟨AllmanEtAl2023.Algorithm.card_of_bInferred (B₀ := {q' | q'.card = 4 ∧ ¬ IsTreelike N q'}) (fun q hq => hq.1) hf,
      AllmanEtAl2023.closure_sound hN hf⟩
  · rintro ⟨h4', h⟩
    exact hto q (AllmanEtAl2023.closure_complete hN h4' h)

/-- The deterministic part from the relaxed answers of `closure_eq_of_relaxed`. -/
theorem tinnikOf_eq_of_relaxed {V E : Type*} {N : RootedNetwork V E X} (hN : N.IsPhylogenetic)
    (hX : 4 ≤ Fintype.card X) {δ : ℝ} (hδ₂ : δ < 2) {M : TreeBuilder X} (hM : IsExactBuilder M)
    {B₀ : Set (Finset X)} {τ : Set (QuartetTree X)}
    (h1 : ∀ q : Finset X, q.card = 4 → ¬ IsTreelike N q → q ∈ B₀)
    (h2 : ∀ q ∈ B₀, q.card = 4 ∧ IsBQuartet N q)
    (h3 : ∀ s ∈ τ, InducedCutSplit N s)
    (h4 : ∀ s, InducedCutSplit N s → s ∈ τ ∨ s.taxa ∈ B₀) :
    tinnikOf B₀ τ δ M = treeOfBlobs N := by
  refine tinnikOf_eq_of_closure hN hX hδ₂ hM (closure_eq_of_relaxed hN h1 h2 h3 h4) ?_
  ext s
  simp only [Set.mem_ofPred_eq, QuartetTree.card_taxa, true_and,
    AllmanEtAl2023.displays_treeOfBlobs_iff hN s]
  constructor
  · rintro ⟨hτ, hB⟩
    exact ⟨h3 s hτ, hB⟩
  · rintro ⟨hc, hB⟩
    rcases h4 s hc with hτ | hsB
    · exact ⟨hτ, hB⟩
    · exact absurd (h2 _ hsB).2 hB

/-- The answers wanted on a set of four taxa, at the true concordance factors `p`: the star test rejects; a cut-edge split on the
induced network that is strictly on its half-line is the maximum likelihood topology, where the T3 test does not reject; on another
cut-edge split, and without a cut-edge split, the T3 test rejects. -/
private def QGoodRelaxed {V E : Type*} (N : RootedNetwork V E X) (p : QuartetTree X → ℝ)
    (ml : (QuartetTree X → ℝ) → Finset X → QuartetTree X) (β a : ℝ) (c : QuartetTree X → ℝ)
    (q : Finset X) : Prop :=
  starPValue .lrt c q < β ∧
    (∀ s ∈ treesOn q, InducedCutSplit N s →
      (IsT1Strict p s → ml c q = s ∧ a ≤ t3PValue c s) ∧
      (¬ IsT1Strict p s → t3PValue c (ml c q) < a)) ∧
    (¬ IsTreelike N q → t3PValue c (ml c q) < a)

/-- The output is the tree of blobs when the answers are right on each set of four taxa, for a network that is T-quartet-nonanomalous
in the sense that its displayed quartet trees are strictly on their half-lines. -/
private theorem tinnikT3_eq_of_qGoodRelaxed {V E : Type*} {N : RootedNetwork V E X} (hN : N.IsPhylogenetic)
    (hX : 4 ≤ Fintype.card X) {p : QuartetTree X → ℝ}
    (hT : ∀ s, Displays (treeOfBlobs N) s → IsT1Strict p s)
    {ml : (QuartetTree X → ℝ) → Finset X → QuartetTree X} {a β δ : ℝ} (hδ₂ : δ < 2)
    {M : TreeBuilder X} (hM : IsExactBuilder M) {c : QuartetTree X → ℝ}
    (h : ∀ q : Finset X, q.card = 4 → QGoodRelaxed N p ml β a c q) :
    tinnikT3 ml a β δ M c = treeOfBlobs N := by
  have hsmem : ∀ s : QuartetTree X, s ∈ treesOn s.taxa := fun s => mem_treesOn.2 rfl
  refine tinnikOf_eq_of_relaxed hN hX hδ₂ hM ?_ ?_ ?_ ?_
  · exact fun q hq hnt => ⟨hq, Or.inr ((h q hq).2.2 hnt)⟩
  · rintro q ⟨hq, hor⟩
    refine ⟨hq, fun s hs hd => ?_⟩
    obtain ⟨h₁, h₂, -⟩ := h q hq
    obtain ⟨h₃, h₄⟩ := (h₂ s hs (AllmanEtAl2023.inducedCutSplit_of_displays hN hd)).1 (hT s hd)
    rcases hor with hor | hor
    · exact absurd h₁ (not_lt.2 hor)
    · rw [h₃] at hor
      exact absurd hor (not_lt.2 h₄)
  · rintro s ⟨hn, hs⟩
    have hq := s.card_taxa
    obtain ⟨-, h₂, h₃⟩ := h s.taxa hq
    have htl : IsTreelike N s.taxa := by
      by_contra hnt
      exact hn ⟨hq, Or.inr (h₃ hnt)⟩
    obtain ⟨s₀, hs₀, hc₀⟩ := htl
    by_cases hstrict : IsT1Strict p s₀
    · have := ((h₂ s₀ hs₀ hc₀).1 hstrict).1
      rw [hs, this]
      exact hc₀
    · exact absurd ⟨hq, Or.inr ((h₂ s₀ hs₀ hc₀).2 hstrict)⟩ hn
  · intro s hc
    have hq := s.card_taxa
    obtain ⟨h₁, h₂, -⟩ := h s.taxa hq
    by_cases hstrict : IsT1Strict p s
    · obtain ⟨h₃, h₄⟩ := (h₂ s (hsmem s) hc).1 hstrict
      refine Or.inl ⟨?_, h₃.symm⟩
      rintro ⟨-, hor⟩
      rcases hor with hor | hor
      · exact absurd h₁ (not_lt.2 hor)
      · rw [h₃] at hor
        exact absurd hor (not_lt.2 h₄)
    · exact Or.inr ⟨hq, Or.inr ((h₂ s (hsmem s) hc).2 hstrict)⟩

/-- On each set of four taxa, the relaxed answers hold with probability tending to one. -/
private theorem tendsto_qGoodRelaxed {V E : Type*} [Fintype V] [Fintype E] {N : RootedNetwork V E X}
    (hN : N.IsPhylogenetic) (hX : 4 ≤ Fintype.card X) {θ : MetricData E} (hθ : N.IsMetric θ)
    {ρ : ℝ} (hρ : 0 ≤ ρ ∧ ρ ≤ 1) (hdet : AllmanEtAl2023.CFDetectable N (nmscCF N θ ρ))
    {α : ℕ → ℝ} (hα : ∀ m, 0 < α m) (hα₀ : Tendsto α atTop (𝓝 0))
    (hαlog : Tendsto (fun m : ℕ => Real.log (α m) / m) atTop (𝓝 0))
    {β : ℝ} (hβ : 0 < β) {ml : (QuartetTree X → ℝ) → Finset X → QuartetTree X}
    (hml : IsT3MLSelection ml) {q : Finset X} (hq : q.card = 4) :
    Tendsto (fun m => iidProb (geneTreeDist N θ ρ) m fun ω =>
      QGoodRelaxed N (nmscCF N θ ρ) ml β (α m) (quartetCount unroot ω) q) atTop (𝓝 1) := by
  have hne : Nonempty X := Fintype.card_pos_iff.mp (by omega)
  have hd : IsDist (geneTreeDist N θ ρ) :=
    ⟨geneTreeDist_nonneg hN hθ hρ, sum_geneTreeDist hN hθ hρ⟩
  have hsone := displaysOne_nmsc (θ := θ) (ρ := ρ) hN
  have hrej : ∀ {q : Finset X}, q.card = 4 → ¬ IsT3Null (nmscCF N θ ρ) q →
      Tendsto (fun m => iidProb (geneTreeDist N θ ρ) m fun ω =>
        t3PValue (quartetCount unroot ω) (ml (quartetCount unroot ω) q) < α m) atTop (𝓝 1) := by
    intro q hq hn
    exact tendsto_iidProb_of_imp hd (Eventually.of_forall fun m ω hω => hω _ (hml _ _ hq).1)
      (QuartetTests.t3Test_rejects hd hsone hq hn hα hαlog)
  have hcases : Tendsto (fun m => iidProb (geneTreeDist N θ ρ) m fun ω =>
      (∀ s ∈ treesOn q, InducedCutSplit N s →
        (IsT1Strict (nmscCF N θ ρ) s →
          ml (quartetCount unroot ω) q = s ∧ α m ≤ t3PValue (quartetCount unroot ω) s) ∧
        (¬ IsT1Strict (nmscCF N θ ρ) s →
          t3PValue (quartetCount unroot ω) (ml (quartetCount unroot ω) q) < α m)) ∧
      (¬ IsTreelike N q →
        t3PValue (quartetCount unroot ω) (ml (quartetCount unroot ω) q) < α m)) atTop (𝓝 1) := by
    by_cases htl : IsTreelike N q
    · obtain ⟨s₀, hs₀, hc₀⟩ := htl
      have hst : s₀.taxa = q := (Finset.mem_filter.mp hs₀).2
      subst hst
      by_cases hstrict : IsT1Strict (nmscCF N θ ρ) s₀
      · refine tendsto_iidProb_of_imp hd (Eventually.of_forall fun m ω hω => ?_)
          (tendsto_good_t3 hN hθ hρ hα₀ hml hstrict)
        refine ⟨fun s hsq hcs => ?_, fun hnt => absurd ⟨s₀, hs₀, hc₀⟩ hnt⟩
        have hss : s = s₀ := AllmanEtAl2023.inducedCutSplit_unique hN hcs hc₀
          (Finset.mem_filter.mp hsq).2
        subst hss
        exact ⟨fun _ => hω, fun hn => absurd hstrict hn⟩
      · -- strictly cut and not strictly on the half-line: anomalous
        obtain ⟨hcne, hceq⟩ := hdet.cut s₀ hc₀
        have hlt : ∀ r ∈ s₀.alternatives, nmscCF N θ ρ s₀ < nmscCF N θ ρ r := by
          by_contra hcon
          push Not at hcon
          obtain ⟨r, hr, hle⟩ := hcon
          refine hstrict ⟨fun u hu => ?_, hceq⟩
          rw [hceq u hu r hr]
          exact lt_of_le_of_ne hle (hcne r hr)
        refine tendsto_iidProb_of_imp hd (Eventually.of_forall fun m ω hω => ?_)
          (hrej s₀.card_taxa (QuartetTests.not_isT3Null_of_anomalous hlt))
        refine ⟨fun s hsq hcs => ?_, fun hnt => absurd ⟨s₀, hs₀, hc₀⟩ hnt⟩
        have hss : s = s₀ := AllmanEtAl2023.inducedCutSplit_unique hN hcs hc₀
          (Finset.mem_filter.mp hsq).2
        subst hss
        exact ⟨fun hs' => absurd hs' hstrict, fun _ => hω⟩
    · refine tendsto_iidProb_of_imp hd (Eventually.of_forall fun m ω hω => ?_)
        (hrej hq (QuartetTests.not_isT3Null_of_isNonCut (hdet.blob q hq htl)))
      exact ⟨fun s hsq hcs => absurd ⟨s, hsq, hcs⟩ htl, fun _ => hω⟩
  exact tendsto_iidProb_and hd
    (tendsto_star hd hsone hq (noCentroidCF_of_cfDetectable hdet q hq) hβ) hcases

/-- **The output of the T3 option needs only T-quartet-nonanomaly**, not the absence of all anomalous quartets. At parameters with
CF-detectability that are T-quartet-nonanomalous, for levels `α_m → 0` with `log(1/α_m) = o(m)`, any `β > 0` and `δ < 2`, the TINNiK
algorithm with the T3 test infers the tree of blobs with probability tending to one.

An anomalous treelike 4-taxon set that the tree of blobs does not resolve is rejected by the T3 test, so the tests are not correct on
it (`tendsto_mem_testedBT3_of_anomalous`). But such a set is a B-quartet of the network, and a step of the inference rule from its
split is then a step from the set (`closure_eq_of_relaxed`). The sources do not state this; TOB-QMC says that T-quartet-nonanomaly is "no
more restrictive than the one made by TINNiK (T3 option)". -/
theorem theorem4T3_of_tQuartet {V E : Type*} [Fintype V] [Fintype E] {N : RootedNetwork V E X}
    (hN : N.IsPhylogenetic) (hX : 4 ≤ Fintype.card X) {θ : MetricData E} (hθ : N.IsMetric θ)
    {ρ : ℝ} (hρ : 0 ≤ ρ ∧ ρ ≤ 1) (hdet : AllmanEtAl2023.CFDetectable N (nmscCF N θ ρ))
    (hNon : TOBQMC.IsTQuartetNonanomalous N (nmscCF N θ ρ))
    {α : ℕ → ℝ} (hα : ∀ m, 0 < α m) (hα₀ : Tendsto α atTop (𝓝 0))
    (hαlog : Tendsto (fun m : ℕ => Real.log (α m) / m) atTop (𝓝 0))
    {β δ : ℝ} (hβ : 0 < β) (hδ₂ : δ < 2) {M : TreeBuilder X} (hM : IsExactBuilder M)
    {ml : (QuartetTree X → ℝ) → Finset X → QuartetTree X} (hml : IsT3MLSelection ml) :
    Tendsto (fun m => iidProb (geneTreeDist N θ ρ) m fun ω =>
      tinnikT3 ml (α m) β δ M (quartetCount unroot ω) = treeOfBlobs N) atTop (𝓝 1) := by
  have hne : Nonempty X := Fintype.card_pos_iff.mp (by omega)
  have hd : IsDist (geneTreeDist N θ ρ) :=
    ⟨geneTreeDist_nonneg hN hθ hρ, sum_geneTreeDist hN hθ hρ⟩
  have hT : ∀ s, Displays (treeOfBlobs N) s → IsT1Strict (nmscCF N θ ρ) s := fun s hs =>
    ⟨hNon s hs, (hdet.cut s (AllmanEtAl2023.inducedCutSplit_of_displays hN hs)).2⟩
  have hall := tendsto_iidProb_forall hd (ι := {q : Finset X // q.card = 4})
    (fun q m ω => QGoodRelaxed N (nmscCF N θ ρ) ml β (α m) (quartetCount unroot ω) q.val)
    (fun q => tendsto_qGoodRelaxed hN hX hθ hρ hdet hα hα₀ hαlog hβ hml q.property)
  refine tendsto_iidProb_of_imp hd (Eventually.of_forall fun m ω hω => ?_) hall
  exact tinnikT3_eq_of_qGoodRelaxed hN hX hT hδ₂ hM fun q hq => hω ⟨q, hq⟩

end TINNiK
