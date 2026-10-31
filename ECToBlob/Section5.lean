module

public import Basic.Phylogenetics.NMSC.Exchangeability
public import External.AllmanEtAl2023.Theorem1
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
adaptation of Theorem 1 of Allman et al. 2023, whose content it sketches ("checking the argument ... shows
that generically, no two gene quartet probabilities are equal"). `adaptedAllmanTheorem1` proves that adaptation: the
source's argument, with its choice of generic parameters and then of `γ`, runs on the face where all hybrid lengths are
`0`, where the measure has its atom, since under the degree condition the cut arcs of the reduction can be chosen as
tree arcs (`External.AllmanEtAl2023.exists_reduction_of_blobDegree`).
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
abbrev metricOfCoords (d : V → E) (ℓ g : E → ℝ) : MetricData E := coordMetric N d ℓ g

/-- A set of numerical parameters is null for the measure of §5.1 on valid parameters. The inheritance
coordinates of tree arcs and left-out parents are dummies, of mass one: the set is a cylinder over them, so it
is null exactly when its base is. -/
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

omit [Fintype X] [DecidableEq X] [Fintype V] in
/-- A subset of a null set of parameters is null. -/
theorem IsNullParams.mono {A B : Set (MetricData E)} (hB : IsNullParams N B) (h : A ⊆ B) :
    IsNullParams N A := fun d hd => by
  refine measure_mono_null ?_ (hB d hd)
  rintro x ⟨hm, hx⟩
  exact ⟨hm, h hx⟩

omit [Fintype X] [DecidableEq X] [Fintype V] in
/-- A countable union of null sets of parameters is null. -/
theorem IsNullParams.iUnion {ι : Type*} [Countable ι] {A : ι → Set (MetricData E)}
    (h : ∀ i, IsNullParams N (A i)) : IsNullParams N (⋃ i, A i) := fun d hd => by
  refine measure_mono_null ?_ (measure_iUnion_null fun i => h i d hd)
  rintro x ⟨hm, hx⟩
  obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hx
  exact Set.mem_iUnion.2 ⟨i, hm, hi⟩

/-- **The analytic argument for the measure of §5.1.** Two concordance factors that differ at some normalized
parameters with all hybrid lengths `0` differ outside a null set: the parametrization is analytic on all
the coordinates, so the point need not be valid; the second factor of the measure is Lebesgue measure
restricted to `(0, 1)`, and that of the tree lengths to `(0, ∞)`, so only the atoms at hybrid length `0` need the
point to be on a face. -/
theorem isNullParams_nmscCF_eq {r r' : QuartetTree X} {θ₀ : MetricData E} (hθ₀ : N.IsNormalized θ₀)
    (hface : ∀ e, N.IsHybridArc e → θ₀.length e = 0) (h : nmscCF N θ₀ 0 r ≠ nmscCF N θ₀ 0 r') :
    IsNullParams N {θ | nmscCF N θ 0 r = nmscCF N θ 0 r'} := by
  intro d _
  have hf : AnalyticOnNhd ℝ (fun x : (E → ℝ) × (E → ℝ) =>
      nmscCF N (coordMetric N d x.1 x.2) 0 r - nmscCF N (coordMetric N d x.1 x.2) 0 r') univ :=
    (analyticOnNhd_nmscCF_coordMetric N d 0 r).sub (analyticOnNhd_nmscCF_coordMetric N d 0 r')
  have hw : nmscCF N (coordMetric N d θ₀.length θ₀.inheritance) 0 r -
      nmscCF N (coordMetric N d θ₀.length θ₀.inheritance) 0 r' ≠ 0 := by
    rw [External.AllmanEtAl2023.coordMetric_self hθ₀ d]
    exact sub_ne_zero.2 h
  have hnull := AnalyticOnNhd.prod_pi_dirac_add_restrict_setOf_eq_zero (fun e => N.IsHybridArc e)
    (s := Ici 0) (t := Ioi 0) (u := Ioo 0 1) hf ⟨(θ₀.length, θ₀.inheritance), hface, hw⟩
  exact measure_mono_null (fun x hx => sub_eq_zero.2 hx.2) hnull

/-- The source's parameters on the face where all hybrid lengths are `0`, under the degree condition: the reduction,
with cut arcs that are tree arcs, and `External.AllmanEtAl2023.exists_isNonCut_of_reduction` with the hybrid arcs at
length `0`. So the argument is that of the source: generic parameters off the two deletions, on this face, make the two
CFs differ from their alternatives, and then `γ` is picked. -/
theorem exists_face_isNonCut (hN : N.IsPhylogenetic) (hdeg : BlobDegreeAtMostThree N) {q : Finset X}
    (hq : q.card = 4) (hnt : ¬ IsTreelike N q) (htr : ¬ HasTrivialFourBlob N q) :
    ∃ θ, N.IsNormalized θ ∧ (∀ e, N.IsHybridArc e → θ.length e = 0) ∧
      External.AllmanEtAl2023.IsNonCut (nmscCF N θ 0) q := by
  obtain ⟨D, k₁, k₂, a, s₁, s₂, e₁, e₂, hD, hk, ht, hk₁, hk₂, hpar, -, -, hnot, hs₁, hs₂, hss, hsp₁,
    hsp₂, he₁, he₂⟩ := External.AllmanEtAl2023.exists_reduction_of_blobDegree hN hdeg hq hnt htr
  obtain ⟨θ, hθ, hface, hnc⟩ := External.AllmanEtAl2023.exists_isNonCut_of_reduction
    (Z := {e | N.IsHybridArc e}) hN hD hk ht hk₁ hk₂ hpar hq hnot hs₁ hs₂ hss hsp₁ hsp₂
    (not_isHybridArc_of_isTreeArc he₁) (not_isHybridArc_of_isTreeArc he₂)
  exact ⟨θ, hθ.isNormalized, hface, hnc⟩

/-- **The adaptation of Theorem 1 of Allman et al. 2023 in ECToBlob's proof of Proposition 5.1**, for a network
whose vertices in non-trivial blobs have degree two or three, under the NMSC with independent inheritance: for
parameters outside a null set of ECToBlob's measure, an induced network without a cut-edge split and without a
trivial 4-blob has three distinct probabilities ("checking the argument ... shows that generically, no two gene
quartet probabilities are equal"). The paper's other two facts for this proof are `NMSC.cut_alternatives`
and `NMSC.trivial_uniform`.

The measure has atoms at length `0` on hybrid arcs, so the witness must be on the face where all hybrid
lengths are `0` (`exists_face_isNonCut`). The source's parameters can be taken there, since the two cut arcs of its
reduction can be moved down to tree arcs when reticulations have degree three
(`External.AllmanEtAl2023.exists_reduction_of_blobDegree`). So the proof is the source's as formalized in
`External/AllmanEtAl2023/Theorem1.lean` and `External/AllmanEtAl2023/Reduction.lean`, with the departures from the source
listed in their headers, and the paper's sentence holds as written, for this measure.

Departure from the paper: its text goes quarnet by quarnet: "for a quarnet induced from `N⁺`", "for one with a non-trivial
4-blob, checking the argument of [4, Theorem 1]". Here the argument runs on `N` directly, for each set `q` of four taxa,
with domination off a deletion seeing the four taxa alone. Applying it on an induced quarnet would need the map from
the parameters of `N` to those of the quarnet, and that preimages under it of null sets of this measure are null, with its
atoms at hybrid length `0`, which the paper does not discuss. On `N` the same steps need no comparison of parameter
spaces. This is not forced: it avoids that comparison. -/
theorem adaptedAllmanTheorem1 (hN : N.IsPhylogenetic) (hdeg : BlobDegreeAtMostThree N) :
    IsNullParams N {θ | N.IsMetric θ ∧ ∃ q : Finset X, q.card = 4 ∧
      ¬ IsTreelike N q ∧ ¬ HasTrivialFourBlob N q ∧
      ¬ ∀ r ∈ treesOn q, ∀ r' ∈ treesOn q, r ≠ r' → nmscCF N θ 0 r ≠ nmscCF N θ 0 r'} := by
  have key : ∀ p : {p : (QuartetTree X × QuartetTree X) // ∃ θ₀, N.IsNormalized θ₀ ∧
      (∀ e, N.IsHybridArc e → θ₀.length e = 0) ∧ nmscCF N θ₀ 0 p.1 ≠ nmscCF N θ₀ 0 p.2},
      IsNullParams N {θ | nmscCF N θ 0 p.val.1 = nmscCF N θ 0 p.val.2} := by
    rintro ⟨p, θ₀, hθ₀, hface, hne⟩
    exact isNullParams_nmscCF_eq hθ₀ hface hne
  refine (IsNullParams.iUnion key).mono ?_
  rintro θ ⟨-, q, hq, hnt, htr, hnot⟩
  push Not at hnot
  obtain ⟨r, hr, r', hr', hne, heq⟩ := hnot
  obtain ⟨θ₀, hθ₀, hface, hnc⟩ := exists_face_isNonCut hN hdeg hq hnt htr
  exact Set.mem_iUnion.2 ⟨⟨(r, r'), θ₀, hθ₀, hface, hnc r hr r' hr' hne⟩, heq⟩

/-- No anomalous quartets (ECToBlob §3, TINNiK §"The T3 model and testing"): on an induced network with a
cut-edge split, the quartet tree of the split is more probable than its alternatives.

Departure from the paper: this reads "no anomalous quartets" strictly. The definition the paper cites (Definition 2 of
[8], Ané et al. 2024, `notes/sources/ane2024.txt`, lines 295-297) calls a network anomalous when `p_ab|cd < 1/3`, so its
absence is only `1/3 ≤ p_ab|cd`. That does not give the strict inequality of (5.2) at lines 403, 716 and 722: by Example 1
of [8] there are valid parameters with a cut edge and all three concordance factors `1/3`. This is forced, and the example
is worked out at `remark3_3_nmsc` (`ECToBlob/Remark33.lean`). -/
def NoAnomalousQuartets (N : RootedNetwork V E X) (p : QuartetTree X → ℝ) : Prop :=
  ∀ s, InducedCutSplit N s → ∀ r ∈ s.alternatives, p r < p s

/-- A quartet tree `s` and another tree `r ≠ s` on the same taxa: `r` is an alternative of `s`. -/
private theorem mem_alternatives {s r : QuartetTree X} (h : r.taxa = s.taxa) (hne : r ≠ s) :
    r ∈ s.alternatives := by
  simp [QuartetTree.alternatives, h, hne]

/-- A quartet tree belongs to the trees on its taxa. -/
private theorem mem_treesOn_taxa (s : QuartetTree X) : s ∈ treesOn s.taxa := by
  simp [treesOn]

/-- **Proposition 5.1** (`ecto:prop5_1`). Let `N` be a rooted network whose vertices in non-trivial blobs have
degree two or three. Then Assumption 1 holds under the NMSC, for the numerical parameters with no anomalous
quartets, in the strict sense of `NoAnomalousQuartets`. The forward direction holds for every network; the degree
condition is used only for the generic clause, in `adaptedAllmanTheorem1`.

The paper's "for a quarnet induced from `N⁺` which has a non-trivial cut-edge split, there can be no multifurcations outside of
blobs" (lines 720-721) is `Coarsening.not_hasTrivialFourBlob_of_inducedCutSplit` (`ECToBlob/Remark84.lean`), which needs no
degree condition. This proof does not use it, since `NMSC.cut_alternatives` holds on every network, multifurcations or not. -/
theorem proposition5_1 {N : RootedNetwork V E X} (hN : N.IsPhylogenetic) (hdeg : BlobDegreeAtMostThree N) :
    (∀ θ, N.IsMetric θ → NoAnomalousQuartets N (nmscCF N θ 0) →
      Assumption1Forward N (nmscCF N θ 0)) ∧
    IsNullParams N {θ | N.IsMetric θ ∧ NoAnomalousQuartets N (nmscCF N θ 0) ∧
      ¬ Assumption1Converse N (nmscCF N θ 0)} := by
  have hρ : (0 : ℝ) ≤ 0 ∧ (0 : ℝ) ≤ 1 := ⟨le_rfl, zero_le_one⟩
  refine ⟨fun θ hθ hano => ⟨fun q hq ht => NMSC.trivial_uniform hN hθ hρ q hq ht,
    fun s hs => ⟨hano s hs, NMSC.cut_alternatives hN hθ hρ s hs⟩⟩, ?_⟩
  intro d hd
  refine measure_mono_null ?_ (adaptedAllmanTheorem1 hN hdeg d hd)
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
