module

public import Basic.Phylogenetics.NMSC.Exchangeability
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Measure.Dirac.Basic

/-!
# ECToBlob §5: the measure on numerical parameters, Assumption 1, Proposition 5.1

Equations (5.1) and (5.2) are `IsUniformOn` and `IsT1Strict` in the shared definitions, with the two parts of
Assumption 1, `Assumption1Forward` and `Assumption1Converse`. The paper's "generic" is the exclusion of a null
set in the measure on numerical parameters given after Assumption 1: Lebesgue measure on `(0, ∞)` for tree edge
lengths, `δ₀ + Lebesgue` on `[0, ∞)` for hybrid edge lengths, and Lebesgue measure on the inheritance
probabilities. Of the inheritance probabilities entering a hybrid vertex, those of all but one parent are the
coordinates; which parent is left out does not change the null sets.

Proposition 5.1 says that Assumption 1 holds under the NMSC, on networks whose vertices in non-trivial blobs
have degree two or three, for parameters with no anomalous quartets. The paper's proof is a reduction to an
adaptation of Theorem 1 of Allman et al. 2023, whose content it sketches. Here that adaptation is a named
hypothesis, `AdaptedAllmanTheorem1`, so this file checks the reduction only: the statement is conditional on
that hypothesis, which carries most of the mathematics. See `External/AllmanEtAl2023/README.md` for what Lean
lacks.
-/

@[expose] public noncomputable section

open Phylogenetics Phylogenetics.RootedNetwork MeasureTheory Set
open scoped Classical

namespace ECToBlob

variable {V E X : Type*} [Fintype X] [DecidableEq X]

variable (N : RootedNetwork V E X)

/-- The measure of §5.1 on the length of an edge, tree or hybrid. -/
def lengthMeasure (hybrid : Prop) : Measure ℝ :=
  if hybrid then Measure.dirac 0 + volume.restrict (Ici 0) else volume.restrict (Ioi 0)

instance (hybrid : Prop) : SigmaFinite (lengthMeasure hybrid) := by
  unfold lengthMeasure
  split_ifs <;> infer_instance

variable [Fintype V] [Fintype E]

/-- A choice of one parent arc at each vertex: the coordinate left out of the inheritance
probabilities. -/
def IsParentChoice (d : V → E) : Prop := ∀ v, 2 ≤ N.graph.indegree v → N.graph.target (d v) = v

/-- The numerical parameters with the given edge lengths and free inheritance probabilities. -/
def metricOfCoords (d : V → E) (ℓ g : E → ℝ) : MetricData E where
  length := ℓ
  inheritance e :=
    if N.IsHybridArc e then
      if e = d (N.graph.target e) then
        1 - ∑ f ∈ Finset.univ.filter (fun f => N.graph.target f = N.graph.target e ∧ f ≠ e), g f
      else g e
    else 1

/-- A set of numerical parameters is null for the measure of §5.1 on valid parameters. -/
def IsNullParams (A : Set (MetricData E)) : Prop :=
  ∀ d : V → E, IsParentChoice N d →
    ((Measure.pi fun e => lengthMeasure (N.IsHybridArc e)).prod
      (Measure.pi fun _ : E => volume.restrict (Ioo (0 : ℝ) 1)))
      {x | N.IsMetric (metricOfCoords N d x.1 x.2) ∧ metricOfCoords N d x.1 x.2 ∈ A} = 0

/-- **Assumption 1** (`ecto:assumption1`) for a model that gives concordance factors `model θ` at the
parameters `θ` of the network `N`. -/
def Assumption1 (model : MetricData E → QuartetTree X → ℝ) : Prop :=
  (∀ θ, N.IsMetric θ → Assumption1Forward N (model θ)) ∧
    IsNullParams N {θ | N.IsMetric θ ∧ ¬ Assumption1Converse N (model θ)}


variable {N}

/-- Vertices in a non-trivial blob have degree two or three. The blob of `v` is the set of vertices joined
to it by a walk of arcs that are not bridges; it is non-trivial when it contains another vertex. -/
def BlobDegreeAtMostThree (N : RootedNetwork V E X) : Prop :=
  ∀ v w : V, v ≠ w → TOBQMC.SameBlob N v w → N.graph.indegree v + N.graph.outdegree v ≤ 3

/-- **Assumed result: the adaptation of Theorem 1 of Allman et al. 2023 in ECToBlob's proof of Proposition
5.1**, for a network whose vertices in non-trivial blobs have degree two or three, under the NMSC with
independent inheritance: for parameters outside a null set of ECToBlob's measure, an induced network without a
cut-edge split and without a trivial 4-blob has three distinct probabilities ("checking the argument ... shows
that generically, no two gene quartet probabilities are equal"). The paper's other two facts for this proof are
proved: `NMSC.cut_alternatives`, `NMSC.trivial_uniform`. -/
def AdaptedAllmanTheorem1 (N : RootedNetwork V E X) : Prop :=
  BlobDegreeAtMostThree N → IsNullParams N {θ | N.IsMetric θ ∧ ∃ q : Finset X, q.card = 4 ∧
    ¬ IsTreelike N q ∧ ¬ HasTrivialFourBlob N q ∧
    ¬ ∀ r ∈ treesOn q, ∀ r' ∈ treesOn q, r ≠ r' → nmscCF N θ 0 r ≠ nmscCF N θ 0 r'}

/-- No anomalous quartets (ECToBlob §3, TINNiK §"The T3 model and testing"): on an induced network with a
cut-edge split, the quartet tree of the split is more probable than its alternatives. -/
def NoAnomalousQuartets (N : RootedNetwork V E X) (p : QuartetTree X → ℝ) : Prop :=
  ∀ s, InducedCutSplit N s → ∀ r ∈ s.alternatives, p r < p s

/-- A quartet tree `s` and another tree `r ≠ s` on the same taxa: `r` is an alternative of `s`. -/
private theorem mem_alternatives {s r : QuartetTree X} (h : r.taxa = s.taxa) (hne : r ≠ s) :
    r ∈ s.alternatives := by
  simp [QuartetTree.alternatives, h, hne]

/-- A quartet tree belongs to the trees on its taxa. -/
private theorem mem_treesOn_taxa (s : QuartetTree X) : s ∈ treesOn s.taxa := by
  simp [treesOn]

/-- **Proposition 5.1** (`ecto:prop5_1`), conditional on `AdaptedAllmanTheorem1`. Let `N`
be a rooted network whose vertices in non-trivial blobs have degree two or three. Then Assumption 1 holds under
the NMSC, for the numerical parameters with no anomalous quartets. The forward direction holds for every network;
the degree condition is used only through the assumed result, which claims the generic clause under it. -/
theorem proposition5_1 {N : RootedNetwork V E X} (hN : N.IsPhylogenetic) (hdeg : BlobDegreeAtMostThree N)
    (hA : AdaptedAllmanTheorem1 N) :
    (∀ θ, N.IsMetric θ → NoAnomalousQuartets N (nmscCF N θ 0) →
      Assumption1Forward N (nmscCF N θ 0)) ∧
    IsNullParams N {θ | N.IsMetric θ ∧ NoAnomalousQuartets N (nmscCF N θ 0) ∧
      ¬ Assumption1Converse N (nmscCF N θ 0)} := by
  have hρ : (0 : ℝ) ≤ 0 ∧ (0 : ℝ) ≤ 1 := ⟨le_rfl, zero_le_one⟩
  refine ⟨fun θ hθ hano => ⟨fun q hq ht => NMSC.trivial_uniform hN hθ hρ q hq ht,
    fun s hs => ⟨hano s hs, NMSC.cut_alternatives hN hθ hρ s hs⟩⟩, ?_⟩
  intro d hd
  refine measure_mono_null ?_ (hA hdeg d hd)
  rintro x ⟨hval, hθ, hano, hnot⟩
  refine ⟨hval, hval, ?_⟩
  -- A parameter failing a converse has a set of four taxa as in the hypothesis.
  by_contra hcon
  push Not at hcon
  apply hnot
  have key : ∀ q : Finset X, q.card = 4 → ¬ IsTreelike N q → ¬ HasTrivialFourBlob N q →
      ∀ r ∈ treesOn q, ∀ r' ∈ treesOn q, r ≠ r' →
        nmscCF N (metricOfCoords N d x.1 x.2) 0 r ≠ nmscCF N (metricOfCoords N d x.1 x.2) 0 r' := by
    intro q hq hnt htr r hr r' hr' hne
    exact hcon q hq hnt htr r hr r' hr' hne
  refine ⟨?_, ?_⟩
  · -- The star converse.
    intro q hq htr huni
    by_cases hnt : IsTreelike N q
    · obtain ⟨s, hs, hcut⟩ := hnt
      have hsq : s.taxa = q := by simpa [treesOn] using hs
      obtain ⟨r, hr⟩ : (s.alternatives).Nonempty := by
        rw [← Finset.card_pos, QuartetTree.card_alternatives]; norm_num
      have hlt := hano s hcut r hr
      have hrq : r ∈ treesOn q := by
        have : r.taxa = s.taxa := by
          have := hr
          simp only [QuartetTree.alternatives, Finset.mem_filter] at this
          exact this.2.1
        simp [treesOn, this, hsq]
      rw [huni s hs, huni r hrq] at hlt
      exact lt_irrefl _ hlt
    · obtain ⟨r, hr⟩ : (treesOn q).Nonempty := by
        rw [← Finset.card_pos, card_treesOn hq]; norm_num
      obtain ⟨r', hr', hne⟩ : ∃ r' ∈ treesOn q, r' ≠ r := by
        by_contra hall
        push Not at hall
        have : (treesOn q).card ≤ 1 := Finset.card_le_one.mpr fun a ha b hb => by
          rw [hall a ha, hall b hb]
        rw [card_treesOn hq] at this
        norm_num at this
      exact key q hq hnt htr r' hr' r hr hne (by rw [huni r' hr', huni r hr])
  · -- The T1 converse.
    intro s hcut hstrict
    by_cases hnt : IsTreelike N s.taxa
    · obtain ⟨r, hr, hrc⟩ := hnt
      have hrs : r.taxa = s.taxa := by simpa [treesOn] using hr
      have hne : r ≠ s := fun h => hcut (h ▸ hrc)
      have h₁ := hstrict.1 r (mem_alternatives hrs hne)
      have h₂ := hano r hrc s (mem_alternatives hrs.symm hne.symm)
      exact lt_asymm h₁ h₂
    · by_cases htr : HasTrivialFourBlob N s.taxa
      · obtain ⟨r, hr⟩ : (s.alternatives).Nonempty := by
          rw [← Finset.card_pos, QuartetTree.card_alternatives]; norm_num
        have hlt := hstrict.1 r hr
        have hq := s.card_taxa
        have huni := NMSC.trivial_uniform hN hval hρ s.taxa hq htr
        have hrq : r ∈ treesOn s.taxa := by
          have : r.taxa = s.taxa := by
            have := hr
            simp only [QuartetTree.alternatives, Finset.mem_filter] at this
            exact this.2.1
          simp [treesOn, this]
        rw [huni s (mem_treesOn_taxa s), huni r hrq] at hlt
        exact lt_irrefl _ hlt
      · obtain ⟨r, hr, r', hr', hne⟩ : ∃ r ∈ s.alternatives, ∃ r' ∈ s.alternatives, r ≠ r' := by
          have hcard := s.card_alternatives
          obtain ⟨r, r', hne, h⟩ := Finset.card_eq_two.mp hcard
          exact ⟨r, by simp [h], r', by simp [h], hne⟩
        have hreq := hstrict.2 r hr r' hr'
        have hmem : ∀ t ∈ s.alternatives, t ∈ treesOn s.taxa := by
          intro t ht
          have : t.taxa = s.taxa := by
            simp only [QuartetTree.alternatives, Finset.mem_filter] at ht
            exact ht.2.1
          simp [treesOn, this]
        exact key s.taxa s.card_taxa hnt htr r (hmem r hr) r' (hmem r' hr') hne hreq

end ECToBlob
