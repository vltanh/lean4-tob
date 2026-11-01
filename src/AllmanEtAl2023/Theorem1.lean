module

public import Basic.ForMathlib.Analysis.AnalyticZeroSet
public import Phylogenetics.NMSC.Analytic
public import Phylogenetics.NMSC.Exchangeability
public import Phylogenetics.NMSC.Witness
public import AllmanEtAl2023.Basic
public import AllmanEtAl2023.Reduction
public import AllmanEtAl2023.CutOrder

/-!
# Allman, Baños, Mitchell, Rhodes 2023: Theorem 1

CF-detectability of 4-blobs on 4-taxon networks, for generic parameters (`notes/sources/allman2023.txt`,
lines 129-152). The proof has the source's two statements and passes from them to the iff as it does, with the
departures listed below. The two statements are, for generic parameters,

* (a) a cut-edge split `s` gives a strictly `s`-cut CF (`isGenericNull_not_isStrictlyCut`): the alternatives are
  equal for all parameters (`NMSC.cut_alternatives`), and long cut arcs make the CF of `s` near `1`, so the difference
  is a nonzero analytic function. The source's three rooted forms of the tree of blobs are `rootedForm_cases`, a
  theorem which this argument does not use.
* (b) a network without a cut-edge split gives a non-cut CF (`isGenericNull_not_isNonCut`). One point
  suffices, on the boundary, since the parametrization is analytic on all of the coordinates
  (`analyticOnNhd_nmscCF_coordMetric`). The graph side is `exists_reduction`: the arcs `D` have inheritance `0`,
  and the two parents `k₁`, `k₂` of the reticulation left have one taxon below them, so the CF is a mixture
  of the CFs of the two deleted networks (`NMSC.nmscCF_withPair`). By (a) on those networks
  (`measure_nmscCF_eq_offMetric`), generic numerical parameters other than `γ₁`, `γ₂` make the two CFs strictly
  cut with different splits (`exists_isStochasticCoords_notMem`), and then `γ₁`, `γ₂` are picked to avoid the
  finitely many values where two entries of the mixture agree (`exists_mem_Ioo_forall_ne`).

The source's Theorem 1, an iff, is `theorem1`. It follows from (a) and (b) as in the source
(`CFDetectable.inducedCutSplit_iff`, `CFDetectable.not_isTreelike_iff`).

## Departures from the source

* The source removes the 2-blobs of a network first, by setting lengths to `0`, and uses its Lemma 1. This is
  not forced, and neither is done: see `exists_reduction_aux`.
* The source treats three rooted forms of the tree of blobs in turn for (a). Their trichotomy is proved
  (`rootedForm_cases`, `exists_rootedForm`), but the proof of (a) does not branch on it, since one arc dominating
  the cherry `a, b` with `c, d` not below it covers all three: see `isGenericNull_not_isStrictlyCut`.
* The source applies (a) to the two deleted networks, as networks of their own with vertices of degree two
  suppressed, and gets strictly cut CFs. Here they are read off a set `D` of arcs in the coordinates of `N`
  (`Phylogenetics/Network/DeletedArcs.lean`), and only the half of "strictly cut" that the choice of `γ` needs, the
  difference from the alternatives, is proved off a deletion: see `measure_nmscCF_eq_offMetric`.
* "Sufficiently large length" is a concrete value, `3`.

Statements (a) and (b) are proved in a more general form than the source's, for a set of four taxa of a
network with any number of taxa, since `exists_reduction` and `SplitOffAt` see the four taxa alone.
`theorem1` is the case where there are four taxa.

## Main results

* `deletionMetric`, `isWeakMetric_deletionMetric`: boundary parameters off a deletion.
* `coordMetric_self`: every normalized parameter is in the image of `coordMetric`, for every parent choice.
* `isGenericNull_of_analyticOnNhd`, `IsGenericNull.iUnion`: null sets of parameters.
* `offMetric`, `measure_nmscCF_eq_offMetric`: statement (a) on a deleted network.
* `exists_isNonCut_of_reduction`: the source's choice of parameters in (b).
* `rootedForm_cases`, `exists_rootedForm`: the three rooted forms of line 142.
* `isGenericNull_not_isStrictlyCut`, `isGenericNull_not_isNonCut`: statements (a) and (b).
* `theorem1`: Theorem 1 of the source.
-/

@[expose] public noncomputable section

open Phylogenetics Phylogenetics.RootedNetwork Finset MeasureTheory
open scoped Classical

open Phylogenetics.DirectedMultigraph AllmanEtAl2023

open Phylogenetics.NMSC

namespace AllmanEtAl2023

variable {V E X : Type*} [Fintype V] [Fintype E] [Fintype X] [DecidableEq X]
  {N : RootedNetwork V E X}

/-! ### Boundary parameters -/

/-- `exp (-3) < 1/4`: arcs of length `3` are long enough for the source's argument. -/
private theorem exp_neg_three_lt : Real.exp (-3) < 1 / 4 := by
  have h : (3 : ℝ) + 1 < Real.exp 3 := Real.add_one_lt_exp (by norm_num)
  rw [Real.exp_neg, one_div]
  exact inv_strictAnti₀ (by norm_num) (by linarith)

/-- The parameters off a deletion `D`: lengths `ℓ`, inheritance `0` on `D`, and the parents of a vertex
off `D` share its inheritance equally. -/
def deletionMetric (N : RootedNetwork V E X) (D : Set E) (ℓ : E → ℝ) : MetricData E where
  length := ℓ
  inheritance e := if e ∈ D then 0 else
    ((univ.filter fun f => N.graph.target f = N.graph.target e ∧ f ∉ D).card : ℝ)⁻¹

omit [Fintype V] [Fintype X] [DecidableEq X] in
/-- The parameters of `deletionMetric` are normalized. -/
theorem isNormalized_deletionMetric (hN : N.IsPhylogenetic) {D : Set E} (hD : N.IsDeletion D)
    (ℓ : E → ℝ) : N.IsNormalized (deletionMetric N D ℓ) := by
  refine ⟨fun e he => ?_, fun v hv => ?_⟩
  · have heD : e ∉ D := fun h => by
      have := hD.hybrid e h
      unfold IsTreeArc at he
      unfold IsHybridArc at this
      omega
    have h1 : (NMSC.arcsInto N (N.graph.target e)).card = 1 := by rwa [← NMSC.indegree_eq_card]
    have hc : (univ.filter fun f => N.graph.target f = N.graph.target e ∧ f ∉ D) = {e} := by
      ext f
      simp only [mem_filter, mem_univ, true_and, mem_singleton]
      constructor
      · rintro ⟨hf, -⟩
        exact card_le_one.1 h1.le _ (NMSC.mem_arcsInto.2 hf) _ (NMSC.mem_arcsInto.2 rfl)
      · rintro rfl
        exact ⟨rfl, heD⟩
    simp [deletionMetric, heD, hc]
  · have hvr : v ≠ N.root := by
      rintro rfl
      have := hN.root_indegree
      omega
    obtain ⟨f₀, hf₀, hf₀v⟩ := hD.parent v hvr
    set C := univ.filter fun f => N.graph.target f = v ∧ f ∉ D with hC
    have hCpos : (C.card : ℝ) ≠ 0 := by
      have : 0 < C.card := card_pos.2 ⟨f₀, by simp [hC, hf₀, hf₀v]⟩
      positivity
    have hterm : ∀ e, (if N.graph.target e = v then (deletionMetric N D ℓ).inheritance e else 0) =
        if e ∈ C then (C.card : ℝ)⁻¹ else 0 := by
      intro e
      by_cases he : N.graph.target e = v
      · subst he
        by_cases heD : e ∈ D
        · simp [deletionMetric, heD, hC]
        · simp [deletionMetric, heD, hC]
      · simp [he, hC]
    simp only [hterm, sum_ite_mem, univ_inter, sum_const, nsmul_eq_mul]
    exact mul_inv_cancel₀ hCpos

omit [Fintype V] [Fintype X] [DecidableEq X] in
/-- The parameters of `deletionMetric` are weak parameters, for nonnegative lengths. -/
theorem isWeakMetric_deletionMetric (hN : N.IsPhylogenetic) {D : Set E} (hD : N.IsDeletion D)
    {ℓ : E → ℝ} (hℓ : ∀ e, 0 ≤ ℓ e) : N.IsWeakMetric (deletionMetric N D ℓ) := by
  refine ⟨hℓ, fun e _ => ?_, isNormalized_deletionMetric hN hD ℓ⟩
  simp only [deletionMetric]
  split_ifs
  · exact le_rfl
  · positivity

omit [Fintype V] [Fintype X] [DecidableEq X] in
/-- A sum over the arcs with the target of `e`, split at `e`. -/
private theorem sum_target_eq_add (γ : E → ℝ) (e : E) :
    (∑ f, if N.graph.target f = N.graph.target e then γ f else 0) =
      γ e + ∑ f ∈ univ.filter (fun f => N.graph.target f = N.graph.target e ∧ f ≠ e), γ f := by
  rw [← sum_filter, ← add_sum_erase _ _
    (mem_filter.2 ⟨mem_univ e, rfl⟩ : e ∈ univ.filter (fun f => N.graph.target f = N.graph.target e))]
  congr 1
  refine sum_congr ?_ fun _ _ => rfl
  ext f
  simp only [mem_erase, mem_filter, mem_univ, true_and]
  tauto

omit [Fintype V] [Fintype X] [DecidableEq X] in
/-- **Every normalized parameter is reached by the coordinates**, for every choice `d` of the left-out
coordinates: at the coordinates given by its own lengths and inheritance. So a witness on the boundary
is a point of the coordinates of `IsGenericNull`. -/
theorem coordMetric_self {θ : MetricData E} (hθ : N.IsNormalized θ) (d : V → E) :
    coordMetric N d θ.length θ.inheritance = θ := by
  have hinh : (coordMetric N d θ.length θ.inheritance).inheritance = θ.inheritance := by
    funext e
    by_cases he : N.IsHybridArc e
    · by_cases hde : e = d (N.graph.target e)
      · rw [coordMetric_inheritance_of_eq he hde]
        have hs := hθ.2 _ he
        rw [sum_target_eq_add θ.inheritance e] at hs
        linarith
      · exact coordMetric_inheritance_of_ne he hde
    · rw [coordMetric_inheritance_of_not_isHybridArc he]
      refine (hθ.1 e ?_).symm
      have hpos : 0 < N.graph.indegree (N.graph.target e) :=
        (Set.ncard_pos (Set.toFinite _)).2 ⟨e, rfl⟩
      unfold IsHybridArc at he
      unfold IsTreeArc
      omega
  exact congrArg₂ MetricData.mk rfl hinh

/-! ### Null sets of parameters -/

omit [Fintype V] [Fintype X] [DecidableEq X] in
/-- Deleting more arcs keeps a split. -/
theorem _root_.Phylogenetics.RootedNetwork.IsGenericNull.mono {A B : Set (MetricData E)} (hB : IsGenericNull N B) (h : A ⊆ B) :
    IsGenericNull N A := by
  intro d hd
  refine measure_mono_null ?_ (hB d hd)
  rintro x ⟨θ, hθ, rest⟩
  exact ⟨θ, h hθ, rest⟩

omit [Fintype V] [Fintype X] [DecidableEq X] in
/-- A countable union of null sets of parameters is null. -/
theorem _root_.Phylogenetics.RootedNetwork.IsGenericNull.iUnion {ι : Type*} [Countable ι] {A : ι → Set (MetricData E)}
    (h : ∀ i, IsGenericNull N (A i)) : IsGenericNull N (⋃ i, A i) := by
  intro d hd
  refine measure_mono_null ?_ (measure_iUnion_null fun i => h i d hd)
  rintro x ⟨θ, hθ, rest⟩
  obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hθ
  exact Set.mem_iUnion.2 ⟨i, θ, hi, rest⟩

omit [Fintype V] [Fintype X] [DecidableEq X] in
/-- The union of two null sets of parameters is null. -/
theorem _root_.Phylogenetics.RootedNetwork.IsGenericNull.union {A B : Set (MetricData E)} (hA : IsGenericNull N A)
    (hB : IsGenericNull N B) : IsGenericNull N (A ∪ B) := by
  rw [Set.union_eq_iUnion]
  exact IsGenericNull.iUnion fun b => by cases b <;> assumption

omit [Fintype V] [Fintype X] [DecidableEq X] in
/-- **The analytic argument.** A function of the parameters that is analytic in the coordinates, for every
choice of the left-out coordinates, and nonzero at some normalized parameters (which may be on the
boundary), vanishes only on a null set of valid parameters. -/
theorem isGenericNull_of_analyticOnNhd {F : MetricData E → ℝ}
    (hF : ∀ d : V → E, AnalyticOnNhd ℝ (fun x : (E → ℝ) × (E → ℝ) => F (coordMetric N d x.1 x.2))
      Set.univ) {θ₀ : MetricData E} (hθ₀ : N.IsNormalized θ₀) (h : F θ₀ ≠ 0) :
    IsGenericNull N {θ | N.IsMetric θ ∧ F θ = 0} := by
  intro d _
  have hw : F (coordMetric N d θ₀.length θ₀.inheritance) ≠ 0 := by
    rwa [coordMetric_self hθ₀ d]
  refine measure_mono_null ?_
    (AnalyticOnNhd.prod_pi_volume_setOf_eq_zero (hF d) ⟨(θ₀.length, θ₀.inheritance), hw⟩)
  rintro x ⟨θ, ⟨-, hzero⟩, hθ, hℓ, hg⟩
  rw [Set.mem_ofPred_eq, ← eq_coordMetric hθ hℓ hg]
  exact hzero

/-- Two concordance factors that differ at some normalized parameters differ at generic parameters. -/
theorem isGenericNull_nmscCF_eq {r r' : QuartetTree X} {θ₀ : MetricData E}
    (hθ₀ : N.IsNormalized θ₀) (h : nmscCF N θ₀ 0 r ≠ nmscCF N θ₀ 0 r') :
    IsGenericNull N {θ | N.IsMetric θ ∧ nmscCF N θ 0 r = nmscCF N θ 0 r'} :=
  (isGenericNull_of_analyticOnNhd (F := fun θ => nmscCF N θ 0 r - nmscCF N θ 0 r')
    (fun d => (analyticOnNhd_nmscCF_coordMetric N d 0 r).sub
      (analyticOnNhd_nmscCF_coordMetric N d 0 r')) hθ₀ (sub_ne_zero.2 h)).mono
    fun _ hθ => ⟨hθ.1, sub_eq_zero.2 hθ.2⟩

/-! ### Part (a): a long cut arc -/

omit [Fintype V] [Fintype E] [Fintype X] in
/-- Deleting more arcs keeps a split. -/
theorem _root_.Phylogenetics.RootedNetwork.SplitOffAt.mono {D D' : Set E} (hDD : D ⊆ D') {e : E} {s : QuartetTree X}
    (hs : N.SplitOffAt D e s) : N.SplitOffAt D' e s := by
  obtain ⟨P, hP, hdom, hnb⟩ := hs
  exact ⟨P, hP, fun x hx hr => hdom x hx (hr.mono (Set.insert_subset_insert hDD)),
    fun x hx hb => hnb x hx ⟨fun h => hb.1 (hDD h), hb.2.mono hDD⟩⟩

omit [Fintype V] [Fintype E] [Fintype X] in
/-- A cut-edge split of the induced network is a split off the empty deletion, by
`hasCutSplitOn_iff_separates`. -/
theorem exists_splitOffAt_of_inducedCutSplit (hN : N.IsPhylogenetic) {s : QuartetTree X}
    (hs : InducedCutSplit N s) : ∃ e, N.SplitOffAt ∅ e s := by
  have hsep : ∀ {e : E} {P Q : Set X}, N.SeparatesOff ∅ e P Q ↔ N.Separates e P Q := by
    intro e P Q
    simp only [SeparatesOff, Separates, dominatesOff_empty_iff, isBelowOff_empty_iff]
  have hinter : ∀ P : Finset X, P ∈ s.val → (s.taxa : Set X) ∩ P = P := fun P hP =>
    Set.inter_eq_right.mpr (Finset.coe_subset.mpr (s.subset_taxa hP))
  have hdiff : ∀ P : Finset X, (s.taxa : Set X) \ P = ((s.taxa \ P : Finset X) : Set X) := fun P => by
    simp
  obtain ⟨P, hP, hcut⟩ := hs
  obtain ⟨e, ⟨-, hsp⟩ | ⟨-, hsp⟩⟩ := (hasCutSplitOn_iff_separates hN _ _).mp hcut
  · rw [hinter P hP, hdiff] at hsp
    exact ⟨e, P, hP, hsep.mpr hsp⟩
  · rw [hinter P hP, hdiff] at hsp
    refine ⟨e, s.taxa \ P, s.sdiff_mem hP, ?_⟩
    rw [Finset.sdiff_sdiff_eq_self (s.subset_taxa hP)]
    exact hsep.mpr hsp

/-- An arc of length `3` that induces the split of `s` off a deletion makes the CF of `s` more than
`3/4` (the source's "`CF_{ab|cd}` can be made as close to 1 as desired"). -/
theorem three_quarters_lt_nmscCF (hN : N.IsPhylogenetic) {D : Set E} (hD : N.IsDeletion D)
    {ℓ : E → ℝ} (hℓ : ∀ e, 0 ≤ ℓ e) {e : E} (he : ℓ e = 3) {s : QuartetTree X}
    (hs : N.SplitOffAt D e s) : 3 / 4 < nmscCF N (deletionMetric N D ℓ) 0 s := by
  have h := NMSC.one_sub_exp_le_nmscCF (ρ := 0) hN (isWeakMetric_deletionMetric hN hD hℓ)
    ⟨le_rfl, zero_le_one⟩ hD (fun f hf => ite_eq_left hf) hs
  rw [show (deletionMetric N D ℓ).length e = 3 from he] at h
  linarith [exp_neg_three_lt]

/-- At an arc of length `3` that induces the split of `s` off a deletion, the CF of `s` is more than `3/4`,
and those of its alternatives less than `1/4`: "if the cut edges in `𝒩+` are given a sufficiently large length"
(`notes/sources/allman2023.txt`, line 143). -/
theorem nmscCF_lt_nmscCF_of_splitOffAt (hN : N.IsPhylogenetic) {D : Set E} (hD : N.IsDeletion D)
    {ℓ : E → ℝ} (hℓ : ∀ e, 0 ≤ ℓ e) {e : E} (he : ℓ e = 3) {s r : QuartetTree X}
    (hs : N.SplitOffAt D e s) (hr : r ∈ s.alternatives) :
    nmscCF N (deletionMetric N D ℓ) 0 r < nmscCF N (deletionMetric N D ℓ) 0 s := by
  obtain ⟨hrt, hne⟩ := QuartetTree.mem_alternatives.1 hr
  have h₁ := three_quarters_lt_nmscCF hN hD hℓ he hs
  have h₂ := NMSC.nmscCF_le_exp_of_splitOffAt (ρ := 0) hN (isWeakMetric_deletionMetric hN hD hℓ)
    ⟨le_rfl, zero_le_one⟩ hD (fun f hf => ite_eq_left hf) hs hrt hne
  rw [show (deletionMetric N D ℓ).length e = 3 from he] at h₂
  linarith [exp_neg_three_lt]

/-! ### Part (a): the three rooted forms -/

/-- The reduced rooted tree of blobs on the taxa of `s` has the form `(((a, b), c), d)`, with `P = {a, b}`: an
arc dominates `a`, `b` and one more taxon `c`, with the fourth taxon not below it. -/
def IsCaterpillarForm (N : RootedNetwork V E X) (s : QuartetTree X) (P : Finset X) : Prop :=
  ∃ e, ∃ c ∈ s.taxa \ P, (∀ x ∈ insert c P, N.Dominates e x) ∧
    ∀ x ∈ s.taxa, x ∉ insert c P → ¬ N.IsBelow e x

/-- The reduced rooted tree of blobs on the taxa of `s` has the form `((a, b), (c, d))`, with `P = {a, b}`: an
arc dominates the other cherry `c, d`, with `a, b` not below it. -/
def IsBalancedForm (N : RootedNetwork V E X) (s : QuartetTree X) (P : Finset X) : Prop :=
  ∃ e, (∀ x ∈ s.taxa \ P, N.Dominates e x) ∧ ∀ x ∈ P, ¬ N.IsBelow e x

/-- The reduced rooted tree of blobs on the taxa of `s` has the form `((a, b), c, d)`, with `P = {a, b}`: the
only non-trivial cluster below the LSA is the cherry. Every arc that dominates a set `A` of at least two taxa of
`s`, with the rest not below it and some taxon left over, dominates exactly `P`. The taxon left over excludes the
arcs above the LSA, which dominate all four taxa in all three forms. -/
def IsCherryForm (N : RootedNetwork V E X) (s : QuartetTree X) (P : Finset X) : Prop :=
  ∀ (f : E) (A : Finset X), A ⊂ s.taxa → 2 ≤ A.card → (∀ x ∈ A, N.Dominates f x) →
    (∀ x ∈ s.taxa \ A, ¬ N.IsBelow f x) → A = P

omit [Fintype V] [Fintype E] [Fintype X] in
/-- **"Permuting taxon names if necessary, we may assume that the reduced rooted tree of blobs thus has
topology `(((a, b), c), d)`, `((a, b), (c, d))`, or `((a, b), c, d)`"** (`notes/sources/allman2023.txt`, line 142),
for an arc `e` that dominates the cherry `P = {a, b}` of `s` with `c, d` not below it.

An arc `f` dominating a proper subset `A` of the taxa, of at least two, with the rest not below it, does not
cross `e` (`not_crossing`). So if `A` meets `P`, then `A` contains `P`, and is `P` or `P` with one more taxon; and
otherwise `A` is the other cherry. These are the three forms. -/
theorem rootedForm_cases (hN : N.IsPhylogenetic) {s : QuartetTree X} {P : Finset X} (hP : P ∈ s.val)
    {e : E} (hd : ∀ x ∈ P, N.Dominates e x) (hn : ∀ x ∈ s.taxa \ P, ¬ N.IsBelow e x) :
    IsCaterpillarForm N s P ∨ IsBalancedForm N s P ∨ IsCherryForm N s P := by
  have hPt : P ⊆ s.taxa := s.subset_taxa hP
  have hP2 : P.card = 2 := s.card_of_mem hP
  have ht4 : s.taxa.card = 4 := s.card_taxa
  by_contra hcon
  push Not at hcon
  obtain ⟨hcat, hbal, hch⟩ := hcon
  unfold IsCherryForm at hch
  push Not at hch
  obtain ⟨f, A, hA, hA2, hfd, hfn, hAP⟩ := hch
  have hAt : A ⊆ s.taxa := hA.subset
  have hcut : IsCutOn N s.taxa f := fun x hx hb => by
    by_contra hnd
    exact hfn x (mem_sdiff.2 ⟨hx, fun hxA => hnd (hfd x hxA)⟩) hb
  by_cases hmeet : ∃ x ∈ A, x ∈ P
  · obtain ⟨x, hxA, hxP⟩ := hmeet
    by_cases hsub : P ⊆ A
    · -- `A` is `P` with one more taxon
      obtain ⟨c, hcA, hcP⟩ : ∃ c ∈ A, c ∉ P := by
        by_contra hno
        push Not at hno
        exact hAP (eq_of_subset_of_card_le hno (by omega))
      refine hcat ⟨f, c, mem_sdiff.2 ⟨hAt hcA, hcP⟩, fun y hy => hfd y ?_, fun y hy hyc => ?_⟩
      · rcases mem_insert.1 hy with rfl | hy
        · exact hcA
        · exact hsub hy
      · have hcard : (insert c P).card = 3 := by rw [card_insert_of_notMem hcP, hP2]
        have hAc : A = insert c P := (eq_of_subset_of_card_le
          (insert_subset hcA hsub) (by
            have := card_lt_card hA
            omega)).symm
        exact hfn y (mem_sdiff.2 ⟨hy, hAc ▸ hyc⟩)
    · -- `A` crosses `P`
      exfalso
      obtain ⟨y, hyP, hyA⟩ := not_subset.1 hsub
      obtain ⟨z, hzA, hzx⟩ := exists_mem_ne (by omega : 1 < A.card) x
      have hzP : z ∉ P := fun hzP => by
        obtain ⟨u, w, -, hPuw⟩ := card_eq_two.1 hP2
        simp only [hPuw, mem_insert, mem_singleton] at hxP hyP hzP
        have hzy : z ≠ y := fun h => hyA (h ▸ hzA)
        grind
      exact not_crossing hN hcut (hPt hxP) ((hd x hxP).isBelow hN) ((hfd x hxA).isBelow hN)
        ((hd y hyP).isBelow hN) (fun hb => hfn y (mem_sdiff.2 ⟨hPt hyP, hyA⟩) hb)
        (hn z (mem_sdiff.2 ⟨hAt hzA, hzP⟩)) ((hfd z hzA).isBelow hN)
  · -- `A` is the other cherry
    push Not at hmeet
    have hAc : A = s.taxa \ P := eq_of_subset_of_card_le
      (fun y hy => mem_sdiff.2 ⟨hAt hy, hmeet y hy⟩) (by
        rw [card_sdiff_of_subset hPt]
        omega)
    refine hbal ⟨f, fun y hy => hfd y (hAc ▸ hy), fun y hy => ?_⟩
    exact hfn y (mem_sdiff.2 ⟨hPt hy, fun hyA => hmeet y hyA hy⟩)

omit [Fintype V] [Fintype E] [Fintype X] in
/-- The sentence of line 142 for a cut-edge split: an arc dominates one of the two cherries of `s`, with the other
not below it, which is what "permuting taxon names if necessary" chooses as `a, b`, and the three forms follow. -/
theorem exists_rootedForm (hN : N.IsPhylogenetic) {s : QuartetTree X} (hs : InducedCutSplit N s) :
    ∃ P ∈ s.val, (∃ e, N.Separates e (P : Set X) ((s.taxa \ P : Finset X) : Set X)) ∧
      (IsCaterpillarForm N s P ∨ IsBalancedForm N s P ∨ IsCherryForm N s P) := by
  obtain ⟨e, P, hP, hsep⟩ := exists_splitOffAt_of_inducedCutSplit hN hs
  have hsep' : N.Separates e (P : Set X) ((s.taxa \ P : Finset X) : Set X) := by
    simpa only [SeparatesOff, Separates, dominatesOff_empty_iff, isBelowOff_empty_iff] using hsep
  exact ⟨P, hP, ⟨e, hsep'⟩, rootedForm_cases hN hP (fun x hx => hsep'.1 x hx)
    (fun x hx => hsep'.2 x (by simpa using hx))⟩

/-- **Statement (a) in the proof of Theorem 1 of the source** (`notes/sources/allman2023.txt`, lines 142-144):
for a cut-edge split `s` of the induced network, the CF is strictly `s`-cut for generic parameters.

Take the arc `e` that dominates the cherry `P = {a, b}` of `s` and has `c, d` not below it. The source's sentences,
for its rooted forms, are the two facts used.

* In the form `(((a, b), c), d)`: "if a gene tree forms under the NMSC by the `a, b` lineages coalescing
  below the 3-blob determined by `a, c, d`, it contributes to the frequency of unrooted gene quartets with
  topology `ab|cd`. Otherwise, `a, b` enter that blob as exchangeable lineages, and `ac|bd` and `ad|bc` will
  be equally probable".
* In the forms `((a, b), (c, d))` and `((a, b), c, d)`: "Any coalescence below the blob containing the LSA
  leads to gene trees `ab|cd`. If no such coalescence occurs, then upon entering the blob containing the LSA
  the lineages from `a, b` are exchangeable".

These are `NMSC.cut_alternatives`. In all forms, "sufficiently long cut edges" give a point where the CF of `s` differs
from those of its alternatives (`nmscCF_lt_nmscCF_of_splitOffAt`), and "`CF` is an analytic function of parameters"
(`isGenericNull_nmscCF_eq`).

Departure from the paper: the source treats its three rooted forms in turn. Here the trichotomy of line 142 is a theorem
(`rootedForm_cases`, `exists_rootedForm`), but this proof does not branch on it, and no information from it is used. The
argument is at the arc `e`, in place of the source's blob: a coalescence below the source of `e` gives `ab|cd`, and
otherwise `a, b` are exchangeable at the source of `e`. The arc `e` need not be incident to the blob, and
`NMSC.cut_alternatives` does not say which arc it uses. The topmost cut arc over `a, b` would be the one incident to the
source's blob in every form, but choosing it would change nothing here: the form says what is above that arc, and the
argument only looks below it. The case split is not needed, so this departure is not forced. -/
theorem isGenericNull_not_isStrictlyCut (hN : N.IsPhylogenetic) {s : QuartetTree X}
    (hs : InducedCutSplit N s) :
    IsGenericNull N {θ | N.IsMetric θ ∧ ¬ IsStrictlyCut (nmscCF N θ 0) s} := by
  obtain ⟨e, he⟩ := exists_splitOffAt_of_inducedCutSplit hN hs
  have hne : ∀ r ∈ s.alternatives, nmscCF N (deletionMetric N ∅ fun _ => 3) 0 r ≠
      nmscCF N (deletionMetric N ∅ fun _ => 3) 0 s := fun r hr =>
    (nmscCF_lt_nmscCF_of_splitOffAt hN (isDeletion_empty hN) (fun _ => by norm_num) rfl he hr).ne
  refine (IsGenericNull.iUnion (ι := {r // r ∈ s.alternatives}) fun r =>
    isGenericNull_nmscCF_eq (r := r.val) (r' := s)
      (isNormalized_deletionMetric hN (isDeletion_empty hN) fun _ => 3)
      (hne r.val r.property)).mono ?_
  rintro θ ⟨hθ, hnot⟩
  have hex : ∃ r ∈ s.alternatives, nmscCF N θ 0 r = nmscCF N θ 0 s := by
    by_contra hall
    push Not at hall
    exact hnot ⟨hall, NMSC.cut_alternatives hN hθ ⟨le_rfl, zero_le_one⟩ s hs⟩
  obtain ⟨r, hr, heq⟩ := hex
  exact Set.mem_iUnion.2 ⟨⟨r, hr⟩, hθ, heq⟩

/-! ### Part (a) on a deleted network -/

/-- `d` chooses, at each reticulation, a parent off `D`: the inheritance left out of the coordinates off `D`. -/
def IsParentChoiceOff (N : RootedNetwork V E X) (D : Set E) (d : V → E) : Prop :=
  ∀ v, 2 ≤ N.graph.indegree v → N.graph.target (d v) = v ∧ d v ∉ D

omit [Fintype V] [Fintype E] [Fintype X] [DecidableEq X] in
/-- Off a deletion, every reticulation has a parent to leave out. -/
theorem exists_isParentChoiceOff (hN : N.IsPhylogenetic) {D : Set E} (hD : N.IsDeletion D) (e₀ : E) :
    ∃ d : V → E, IsParentChoiceOff N D d := by
  have hex : ∀ v, ∃ f : E, 2 ≤ N.graph.indegree v → N.graph.target f = v ∧ f ∉ D := fun v => by
    by_cases hv : 2 ≤ N.graph.indegree v
    · have hvr : v ≠ N.root := by
        rintro rfl
        have := hN.root_indegree
        omega
      obtain ⟨f, hf, hfv⟩ := hD.parent v hvr
      exact ⟨f, fun _ => ⟨hfv, hf⟩⟩
    · exact ⟨e₀, fun h => absurd h hv⟩
  choose d hd using hex
  exact ⟨d, hd⟩

/-- **The numerical parameters of the network off `D`**, at the coordinates `x`: lengths `x.1`, and inheritance
`x.2`, with inheritance `0` on `D`. At a reticulation, the parent `d` takes what the others leave. The arcs in `Z`
have length `0`; `Z` is empty for the source, and the hybrid arcs in ECToBlob's measure. -/
def offMetric (N : RootedNetwork V E X) (D Z : Set E) (d : V → E) (x : (E → ℝ) × (E → ℝ)) :
    MetricData E :=
  coordMetric N d (fun e => if e ∈ Z then 0 else x.1 e) fun e => if e ∈ D then 0 else x.2 e

variable {D Z : Set E} {d : V → E} {x : (E → ℝ) × (E → ℝ)}

omit [Fintype V] [Fintype X] [DecidableEq X] in
/-- The parameters of `offMetric` are normalized. -/
theorem isNormalized_offMetric (hd : IsParentChoiceOff N D d) : N.IsNormalized (offMetric N D Z d x) :=
  ⟨fun _ he => coordMetric_inheritance_of_isTreeArc he,
    fun _ hv => sum_coordMetric_inheritance (fun v hv => (hd v hv).1) hv⟩

omit [Fintype V] [Fintype X] [DecidableEq X] in
/-- The parameters of `offMetric` have inheritance `0` on `D`. -/
theorem offMetric_inheritance_eq_zero (hD : N.IsDeletion D) (hd : IsParentChoiceOff N D d) {e : E}
    (he : e ∈ D) : (offMetric N D Z d x).inheritance e = 0 := by
  have hh := hD.hybrid e he
  have hne : e ≠ d (N.graph.target e) := fun h => (hd _ hh).2 (h ▸ he)
  rw [offMetric, coordMetric_inheritance_of_ne hh hne]
  simp [he]

/-- Coordinates in the interior of the stochastic parameter space: positive lengths, and inheritance
probabilities small enough that the left-out parent keeps a positive one. -/
def IsStochasticCoords (x : (E → ℝ) × (E → ℝ)) : Prop :=
  (∀ e, 0 < x.1 e) ∧ ∀ e, 0 < x.2 e ∧ x.2 e < ((Fintype.card E : ℝ) + 1)⁻¹

omit [Fintype V] [Fintype X] [DecidableEq X] in
/-- At stochastic coordinates, `offMetric` is on the boundary of the stochastic parameter space. -/
theorem isWeakMetric_offMetric (hd : IsParentChoiceOff N D d) (hx : IsStochasticCoords x) :
    N.IsWeakMetric (offMetric N D Z d x) := by
  have hc : (0 : ℝ) < (Fintype.card E : ℝ) + 1 := by positivity
  have hg₀ : ∀ e, 0 ≤ (if e ∈ D then 0 else x.2 e) := fun e => by
    split_ifs
    · exact le_rfl
    · exact (hx.2 e).1.le
  have hg₁ : ∀ e, (if e ∈ D then 0 else x.2 e) ≤ ((Fintype.card E : ℝ) + 1)⁻¹ := fun e => by
    split_ifs
    · positivity
    · exact (hx.2 e).2.le
  refine ⟨fun e => ?_, fun e he => ?_, isNormalized_offMetric hd⟩
  · change 0 ≤ if e ∈ Z then 0 else x.1 e
    split_ifs
    · exact le_rfl
    · exact (hx.1 e).le
  · by_cases hde : e = d (N.graph.target e)
    · rw [offMetric, coordMetric_inheritance_of_eq he hde, sub_nonneg]
      calc _ ≤ ∑ _ ∈ univ.filter (fun f => N.graph.target f = N.graph.target e ∧ f ≠ e),
            ((Fintype.card E : ℝ) + 1)⁻¹ := sum_le_sum fun f _ => hg₁ f
        _ ≤ ∑ _ : E, ((Fintype.card E : ℝ) + 1)⁻¹ :=
            sum_le_sum_of_subset_of_nonneg (subset_univ _) fun _ _ _ => by positivity
        _ ≤ 1 := by
            rw [sum_const, nsmul_eq_mul, card_univ, ← div_eq_mul_inv, div_le_one hc]
            linarith
    · rw [offMetric, coordMetric_inheritance_of_ne he hde]
      exact hg₀ e

/-- The linear map that sets the coordinates in `A` to zero. -/
private def maskCLM (A : Set E) : (E → ℝ) →L[ℝ] (E → ℝ) :=
  ContinuousLinearMap.pi fun e => if e ∈ A then 0 else ContinuousLinearMap.proj e

omit [Fintype V] [Fintype E] [Fintype X] [DecidableEq X] in
private theorem maskCLM_apply (A : Set E) (g : E → ℝ) :
    maskCLM A g = fun e => if e ∈ A then 0 else g e := by
  funext e
  by_cases he : e ∈ A <;> simp [maskCLM, he]

variable (N D Z d) in
/-- A concordance factor is entire in the coordinates off `D`. -/
theorem analyticOnNhd_nmscCF_offMetric (r : QuartetTree X) :
    AnalyticOnNhd ℝ (fun x : (E → ℝ) × (E → ℝ) => nmscCF N (offMetric N D Z d x) 0 r) Set.univ := by
  have hm : AnalyticOnNhd ℝ (fun x : (E → ℝ) × (E → ℝ) => ((maskCLM Z x.1, maskCLM D x.2) :
      (E → ℝ) × (E → ℝ))) Set.univ :=
    ((maskCLM Z).prodMap (maskCLM D)).analyticOnNhd _
  have h := (analyticOnNhd_nmscCF_coordMetric N d 0 r).comp hm (Set.mapsTo_univ _ _)
  simpa only [Function.comp_def, maskCLM_apply, offMetric] using h

/-- Lebesgue measure on the coordinates `(lengths, inheritance)` of the parameters. -/
abbrev coordVolume (E : Type*) [Fintype E] : Measure ((E → ℝ) × (E → ℝ)) :=
  (Measure.pi fun _ : E => (volume : Measure ℝ)).prod (Measure.pi fun _ : E => (volume : Measure ℝ))

/-- **Statement (a) on a deleted network** (`notes/sources/allman2023.txt`, lines 143 and 152): if, off a deletion
`D`, the arc `e` induces the split of `s`, then for generic parameters off `D` the CF of `s` differs from those of
its alternatives. Long cut arcs give a point (`nmscCF_lt_nmscCF_of_splitOffAt`), and a CF is analytic in the
coordinates. So all the numerical parameters off `D` vary, lengths and the other inheritance probabilities, and the
source's generic parameters on `N̄₁`, `N̄₂` are these.

Departure from the paper: the source applies (a) to `N̄₁`, `N̄₂` as networks of their own, whose edges are paths of `𝒩+`
with vertices of degree two suppressed, and leaves implicit how generic parameters on them come from those on `𝒩+`. Here
the deleted network is read off `D`, in the coordinates of `N`, so that passage is not needed.

Departure from the paper: the source uses all of (a) on the deleted networks, "strictly cut". Off a deletion, this
proves that the CF of `s` differs from its alternatives, and not that the alternatives are equal, since the choice
of `γ` uses only the former (`exists_mem_Ioo_forall_ne`). The latter would need `NMSC.cut_alternatives` at
inheritance `0` on `D`, with the Markov property at an arc (`NMSC.cherryMass_eq_of_lift`) off a deletion, a rewrite
of `Phylogenetics/NMSC/Factor.lean` that nothing here needs. Neither departure is forced by the source. -/
theorem measure_nmscCF_eq_offMetric (hN : N.IsPhylogenetic) (hD : N.IsDeletion D)
    {e : E} (heZ : e ∉ Z) {s r : QuartetTree X}
    (hs : N.SplitOffAt D e s) (hr : r ∈ s.alternatives) :
    coordVolume E {x | nmscCF N (offMetric N D Z d x) 0 r = nmscCF N (offMetric N D Z d x) 0 s} = 0 := by
  let ℓ₀ : E → ℝ := fun f => if f ∈ Z then 0 else 3
  have hℓ₀ : ∀ f, 0 ≤ ℓ₀ f := fun f => by
    simp only [ℓ₀]
    split_ifs <;> norm_num
  have hlt := nmscCF_lt_nmscCF_of_splitOffAt hN hD hℓ₀ (ite_eq_right heZ : ℓ₀ e = 3) hs hr
  have hmask : (fun f => if f ∈ D then 0 else (deletionMetric N D ℓ₀).inheritance f) =
      (deletionMetric N D ℓ₀).inheritance := by
    funext f
    by_cases hf : f ∈ D <;> simp [hf, deletionMetric]
  have hw : offMetric N D Z d ((fun _ => 3), (deletionMetric N D ℓ₀).inheritance) =
      deletionMetric N D ℓ₀ := by
    rw [offMetric]
    simp only [hmask]
    exact coordMetric_self (isNormalized_deletionMetric hN hD ℓ₀) d
  have hf : AnalyticOnNhd ℝ (fun x : (E → ℝ) × (E → ℝ) =>
      nmscCF N (offMetric N D Z d x) 0 r - nmscCF N (offMetric N D Z d x) 0 s) Set.univ :=
    (analyticOnNhd_nmscCF_offMetric N D Z d r).sub (analyticOnNhd_nmscCF_offMetric N D Z d s)
  refine measure_mono_null (fun x hx => sub_eq_zero.2 hx)
    (AnalyticOnNhd.prod_pi_volume_setOf_eq_zero hf ⟨((fun _ => 3), (deletionMetric N D ℓ₀).inheritance), ?_⟩)
  rw [hw]
  exact sub_ne_zero.2 hlt.ne

omit [Fintype V] [Fintype X] [DecidableEq X] in
/-- **A point outside a null set**, with stochastic coordinates: the box of `IsStochasticCoords` has positive
measure. -/
theorem exists_isStochasticCoords_notMem {A : Set ((E → ℝ) × (E → ℝ))} (hA : coordVolume E A = 0) :
    ∃ x, IsStochasticCoords x ∧ x ∉ A := by
  by_contra hall
  push Not at hall
  have hc : (0 : ℝ) < ((Fintype.card E : ℝ) + 1)⁻¹ := by positivity
  have hsub : (Set.univ.pi fun _ : E => Set.Ioi (0 : ℝ)) ×ˢ
      (Set.univ.pi fun _ : E => Set.Ioo (0 : ℝ) ((Fintype.card E : ℝ) + 1)⁻¹) ⊆ A := by
    rintro x ⟨h₁, h₂⟩
    exact hall x ⟨fun e => h₁ e (Set.mem_univ _), fun e => h₂ e (Set.mem_univ _)⟩
  have h0 := measure_mono_null hsub hA
  rw [Measure.prod_prod, Measure.pi_pi, Measure.pi_pi, mul_eq_zero, prod_eq_zero_iff,
    prod_eq_zero_iff] at h0
  rcases h0 with ⟨e, -, he⟩ | ⟨e, -, he⟩
  · simp at he
  · rw [Real.volume_Ioo] at he
    simp only [sub_zero, ENNReal.ofReal_eq_zero] at he
    linarith

/-! ### Part (b): the mixture -/

/-- Two distinct trees on four taxa leave one tree. -/
theorem eq_of_mem_treesOn_of_ne {q : Finset X} (hq : q.card = 4) {s₁ s₂ r r' : QuartetTree X}
    (hs₁ : s₁ ∈ treesOn q) (hs₂ : s₂ ∈ treesOn q) (hss : s₁ ≠ s₂) (hr : r ∈ treesOn q)
    (hr' : r' ∈ treesOn q) (h₁ : r ≠ s₁) (h₂ : r ≠ s₂) (h₃ : r' ≠ s₁) (h₄ : r' ≠ s₂) : r = r' := by
  have hc : (((treesOn q).erase s₁).erase s₂).card ≤ 1 := by
    rw [card_erase_of_mem (mem_erase.2 ⟨hss.symm, hs₂⟩), card_erase_of_mem hs₁, card_treesOn hq]
  exact card_le_one.1 hc _ (mem_erase.2 ⟨h₂, mem_erase.2 ⟨h₁, hr⟩⟩) _
    (mem_erase.2 ⟨h₄, mem_erase.2 ⟨h₃, hr'⟩⟩)

/-- **The choice of `γ`** (the source's "we may then pick values of `γ₁`, `γ₂`",
`notes/sources/allman2023.txt`, line 152). If any two entries differ in one of two vectors `p₁`, `p₀`, then for all
but finitely many `γ` all entries of the mixture `γ p₁ + (1 - γ) p₀` are distinct: for each two entries, the
difference is a nonzero affine function of `γ`, with at most one zero. -/
theorem exists_mem_Ioo_forall_ne {ι : Type*} (T : Finset ι) (p₁ p₀ : ι → ℝ)
    (h : ∀ r ∈ T, ∀ r' ∈ T, r ≠ r' → p₁ r ≠ p₁ r' ∨ p₀ r ≠ p₀ r') :
    ∃ γ ∈ Set.Ioo (0 : ℝ) 1, ∀ r ∈ T, ∀ r' ∈ T, r ≠ r' →
      γ * p₁ r + (1 - γ) * p₀ r ≠ γ * p₁ r' + (1 - γ) * p₀ r' := by
  let bad : ι → ι → Set ℝ := fun r r' => {γ | r ≠ r' ∧ γ * p₁ r + (1 - γ) * p₀ r = γ * p₁ r' + (1 - γ) * p₀ r'}
  have hsub : ∀ r ∈ T, ∀ r' ∈ T, (bad r r').Subsingleton := by
    rintro r hr r' hr' γ ⟨hne, hγ⟩ γ' ⟨-, hγ'⟩
    by_contra hγγ
    have hab : p₁ r - p₁ r' = p₀ r - p₀ r' := by
      have h0 : (γ - γ') * ((p₁ r - p₁ r') - (p₀ r - p₀ r')) = 0 := by linear_combination hγ - hγ'
      have := (mul_eq_zero.1 h0).resolve_left (sub_ne_zero.2 hγγ)
      linarith
    have hb : p₀ r - p₀ r' = 0 := by
      have h0 : γ * (p₁ r - p₁ r') + (1 - γ) * (p₀ r - p₀ r') = 0 := by linear_combination hγ
      rw [hab] at h0
      linear_combination h0
    rcases h r hr r' hr' hne with h' | h'
    · exact h' (by linarith)
    · exact h' (by linarith)
  have hfin : (⋃ r ∈ T, ⋃ r' ∈ T, bad r r').Finite :=
    T.finite_toSet.biUnion fun r hr => T.finite_toSet.biUnion fun r' hr' => (hsub r hr r' hr').finite
  obtain ⟨γ, hγ, hnot⟩ := (Set.Ioo_infinite (zero_lt_one' ℝ)).exists_notMem_finite hfin
  refine ⟨γ, hγ, fun r hr r' hr' hne heq => hnot ?_⟩
  exact Set.mem_biUnion hr (Set.mem_biUnion hr' ⟨hne, heq⟩)

section Pair

variable {k k' : E}

omit [Fintype V] [Fintype E] [Fintype X] [DecidableEq X] in
/-- The parent choice off a deletion, after deleting `k'` and leaving `k` at their common target. -/
theorem IsParentChoiceOff.update (hd : IsParentChoiceOff N D d) (hk : k ≠ k')
    (ht : N.graph.target k = N.graph.target k') (hkD : k ∉ D) :
    IsParentChoiceOff N (insert k' D) (Function.update d (N.graph.target k) k) := by
  intro v hv
  by_cases hvh : v = N.graph.target k
  · subst hvh
    rw [Function.update_self]
    exact ⟨rfl, by simp [hk, hkD]⟩
  · rw [Function.update_of_ne hvh]
    obtain ⟨h₁, h₂⟩ := hd v hv
    refine ⟨h₁, ?_⟩
    rintro (h | h)
    · exact hvh (by rw [← h₁, h, ht])
    · exact h₂ h

omit [Fintype V] [Fintype X] [DecidableEq X] in
/-- **Setting `γ = 0` on `k'` gives the parameters of the deleted network** (the source's `N̄ᵢ`). Let `k`,
`k'` be the only parents of their target off `D`. Off `insert k' D`, the inheritance is `1` on `k`, `0` on
`k'`, and as off `D` on the other arcs. -/
theorem offMetric_insert_inheritance (hN : N.IsPhylogenetic) (hD : N.IsDeletion D)
    (hd : IsParentChoiceOff N D d) (hk : k ≠ k') (ht : N.graph.target k = N.graph.target k')
    (hkD : k ∉ D) (hpar : ∀ f, N.graph.target f = N.graph.target k → f ∉ D → f = k ∨ f = k') (f : E) :
    (offMetric N (insert k' D) Z (Function.update d (N.graph.target k) k) x).inheritance f =
      if f = k then 1 else if f = k' then 0 else (offMetric N D Z d x).inheritance f := by
  have hDi : N.IsDeletion (insert k' D) := hD.insert hN hk.symm ht.symm hkD
  have hdi := hd.update hk ht hkD
  have hhk : N.IsHybridArc k := NMSC.isHybridArc_of_target_eq hk ht.symm
  have hhk' : N.IsHybridArc k' := NMSC.isHybridArc_of_target_eq hk.symm ht
  split_ifs with h₁ h₂
  · subst h₁
    rw [offMetric, coordMetric_inheritance_of_eq hhk (by rw [Function.update_self])]
    rw [sum_eq_zero, sub_zero]
    intro g hg
    obtain ⟨hgt, hgne⟩ := (mem_filter.1 hg).2
    have hgD : g ∈ insert k' D := by
      by_contra hn
      have hn' : g ∉ D := fun h => hn (Or.inr h)
      rcases hpar g hgt hn' with h | h
      · exact hgne h
      · exact hn (Or.inl h)
    simp [hgD]
  · subst h₂
    exact offMetric_inheritance_eq_zero hDi hdi (Or.inl rfl)
  · by_cases hfD : f ∈ D
    · rw [offMetric_inheritance_eq_zero hDi hdi (Or.inr hfD),
        offMetric_inheritance_eq_zero hD hd hfD]
    by_cases hth : N.graph.target f = N.graph.target k
    · rcases hpar f hth hfD with h | h
      · exact absurd h h₁
      · exact absurd h h₂
    have hud : Function.update d (N.graph.target k) k (N.graph.target f) = d (N.graph.target f) :=
      Function.update_of_ne hth _ _
    have hmask : ∀ g, N.graph.target g = N.graph.target f → (g ∈ insert k' D ↔ g ∈ D) := by
      intro g hg
      have hgk : g ≠ k' := by
        rintro rfl
        exact hth (by rw [← hg, ht])
      simp [hgk]
    by_cases hh : N.IsHybridArc f
    · by_cases hfd : f = d (N.graph.target f)
      · rw [offMetric, offMetric, coordMetric_inheritance_of_eq hh (by rw [hud]; exact hfd),
          coordMetric_inheritance_of_eq hh hfd]
        congr 1
        exact sum_congr rfl fun g hg => by simp only [hmask g (mem_filter.1 hg).2.1]
      · rw [offMetric, offMetric, coordMetric_inheritance_of_ne hh (by rw [hud]; exact hfd),
          coordMetric_inheritance_of_ne hh hfd]
        simp only [hmask f rfl]
    · rw [offMetric, offMetric, coordMetric_inheritance_of_not_isHybridArc hh,
        coordMetric_inheritance_of_not_isHybridArc hh]

omit [Fintype E] in
/-- Parameters with the same lengths and inheritance are equal. -/
private theorem metricData_ext {θ θ' : MetricData E} (h₁ : θ.length = θ'.length)
    (h₂ : ∀ f, θ.inheritance f = θ'.inheritance f) : θ = θ' :=
  match θ, θ', h₁, funext h₂ with
  | ⟨_, _⟩, ⟨_, _⟩, rfl, rfl => rfl

omit [Fintype V] [Fintype X] [DecidableEq X] in
/-- At `γ = 1`, the arc `k₂` is deleted. -/
theorem offMetric_withPair_one {k₁ k₂ : E} (hN : N.IsPhylogenetic) (hD : N.IsDeletion D)
    (hd : IsParentChoiceOff N D d) (hk : k₁ ≠ k₂) (ht : N.graph.target k₁ = N.graph.target k₂)
    (hk₁ : k₁ ∉ D) (hpar : ∀ f, N.graph.target f = N.graph.target k₁ → f ∉ D → f = k₁ ∨ f = k₂) :
    (offMetric N D Z d x).withPair k₁ k₂ 1 =
      offMetric N (insert k₂ D) Z (Function.update d (N.graph.target k₁) k₁) x := by
  refine metricData_ext rfl fun f => ?_
  rw [offMetric_insert_inheritance hN hD hd hk ht hk₁ hpar f]
  simp only [MetricData.withPair, sub_self]

omit [Fintype V] [Fintype X] [DecidableEq X] in
/-- At `γ = 0`, the arc `k₁` is deleted. -/
theorem offMetric_withPair_zero {k₁ k₂ : E} (hN : N.IsPhylogenetic) (hD : N.IsDeletion D)
    (hd : IsParentChoiceOff N D d) (hk : k₁ ≠ k₂) (ht : N.graph.target k₁ = N.graph.target k₂)
    (hk₂ : k₂ ∉ D) (hpar : ∀ f, N.graph.target f = N.graph.target k₁ → f ∉ D → f = k₁ ∨ f = k₂) :
    (offMetric N D Z d x).withPair k₁ k₂ 0 =
      offMetric N (insert k₁ D) Z (Function.update d (N.graph.target k₂) k₂) x := by
  refine metricData_ext rfl fun f => ?_
  rw [offMetric_insert_inheritance hN hD hd hk.symm ht.symm hk₂
    (fun f hf hfD => (hpar f (hf.trans ht.symm) hfD).symm) f]
  simp only [MetricData.withPair, sub_zero]
  split_ifs with h₁ h₂ h₃
  · exact absurd (h₁.symm.trans h₂) hk
  · rfl
  · rfl
  · rfl

end Pair

/-- **The source's choice of parameters in part (b) of the proof of Theorem 1**
(`notes/sources/allman2023.txt`, lines 150-152). At the reduction of `exists_reduction`, a set `D` of arcs of
inheritance `0`, and two parents `k₁`, `k₂` with at most `a` below them:

"since `a` is the only taxon below the hybrid node `v`", the CF is the mixture `γ₁ CF¹ + γ₂ CF²` of the CFs of the two
deleted networks (`NMSC.nmscCF_withPair`). "By (a) we have that `CF¹` is strictly `ab|cd`-cut and `CF²` is strictly
`ac|bd`-cut for generic parameters" (`measure_nmscCF_eq_offMetric`, for `insert k₂ D` and `insert k₁ D`). "Thus by first
choosing the numerical parameters other than `γ₁`, `γ₂` on `𝒩+` to yield such generic parameters" (the coordinates
`x`, `exists_isStochasticCoords_notMem`), "we may then pick values of `γ₁`, `γ₂` so that `CF(𝒩+)` is non-cut"
(`exists_mem_Ioo_forall_ne`).

The set `Z` of arcs of length `0`, disjoint from the cut arcs, is empty for the source, and is the set of hybrid arcs
for ECToBlob's measure, which needs a point on that face (`ECToBlob.adaptedAllmanTheorem1`). -/
theorem exists_isNonCut_of_reduction (hN : N.IsPhylogenetic) (hD : N.IsDeletion D) {k₁ k₂ : E}
    (hk : k₁ ≠ k₂) (ht : N.graph.target k₁ = N.graph.target k₂) (hk₁ : k₁ ∉ D) (hk₂ : k₂ ∉ D)
    (hpar : ∀ f, N.graph.target f = N.graph.target k₁ → f ∉ D → f = k₁ ∨ f = k₂)
    {q : Finset X} (hq : q.card = 4) {a : X}
    (hnot : ∀ x ∈ q, x ≠ a → ¬ N.ReachesOff D (N.graph.target k₁) (N.leaf x))
    {s₁ s₂ : QuartetTree X} (hs₁ : s₁ ∈ treesOn q) (hs₂ : s₂ ∈ treesOn q) (hss : s₁ ≠ s₂) {e₁ e₂ : E}
    (hsp₁ : N.SplitOffAt (insert k₂ D) e₁ s₁) (hsp₂ : N.SplitOffAt (insert k₁ D) e₂ s₂)
    (he₁ : e₁ ∉ Z) (he₂ : e₂ ∉ Z) :
    ∃ θ, N.IsWeakMetric θ ∧ (∀ e ∈ Z, θ.length e = 0) ∧ IsNonCut (nmscCF N θ 0) q := by
  obtain ⟨d, hd⟩ := exists_isParentChoiceOff hN hD k₁
  have ht' : N.graph.target k₂ = N.graph.target k₁ := ht.symm
  have hpar' : ∀ f, N.graph.target f = N.graph.target k₂ → f ∉ D → f = k₂ ∨ f = k₁ := fun f hf hfD =>
    (hpar f (hf.trans ht') hfD).symm
  -- (a) on the two deleted networks
  have hnull₁ := (measure_biUnion_null_iff (s₁.alternatives.countable_toSet)).2 fun r hr =>
    measure_nmscCF_eq_offMetric (Z := Z) (d := Function.update d (N.graph.target k₁) k₁) hN
      (hD.insert hN hk.symm ht' hk₁) he₁ hsp₁ (Finset.mem_coe.mp hr)
  have hnull₂ := (measure_biUnion_null_iff (s₂.alternatives.countable_toSet)).2 fun r hr =>
    measure_nmscCF_eq_offMetric (Z := Z) (d := Function.update d (N.graph.target k₂) k₂) hN
      (hD.insert hN hk ht hk₂) he₂ hsp₂ (Finset.mem_coe.mp hr)
  -- the numerical parameters other than `γ₁`, `γ₂`
  obtain ⟨x, hx, hxn⟩ := exists_isStochasticCoords_notMem (measure_union_null hnull₁ hnull₂)
  set θ := offMetric N D Z d x with hθ
  have hw := isWeakMetric_offMetric (Z := Z) hd hx
  have hD0 : ∀ f ∈ D, θ.inheritance f = 0 := fun f hf => offMetric_inheritance_eq_zero hD hd hf
  have h0 : ∀ f, N.graph.target f = N.graph.target k₁ → f ≠ k₁ → f ≠ k₂ → θ.inheritance f = 0 :=
    fun f hf h₁ h₂ => hD0 f (by_contra fun hfD => (hpar f hf hfD).elim h₁ h₂)
  -- the two CFs differ from their alternatives there
  have hcf₁ : ∀ r ∈ s₁.alternatives,
      nmscCF N (θ.withPair k₁ k₂ 1) 0 r ≠ nmscCF N (θ.withPair k₁ k₂ 1) 0 s₁ := fun r hr h => by
    rw [hθ, offMetric_withPair_one hN hD hd hk ht hk₁ hpar] at h
    exact hxn (Or.inl (Set.mem_biUnion (Finset.mem_coe.mpr hr) h))
  have hcf₂ : ∀ r ∈ s₂.alternatives,
      nmscCF N (θ.withPair k₁ k₂ 0) 0 r ≠ nmscCF N (θ.withPair k₁ k₂ 0) 0 s₂ := fun r hr h => by
    rw [hθ, offMetric_withPair_zero hN hD hd hk ht hk₂ hpar] at h
    exact hxn (Or.inr (Set.mem_biUnion (Finset.mem_coe.mpr hr) h))
  have htaxa : ∀ t ∈ treesOn q, ∀ s ∈ treesOn q, t ≠ s → t ∈ s.alternatives := fun t ht s hs hne =>
    QuartetTree.mem_alternatives.2 ⟨(mem_treesOn.1 ht).trans (mem_treesOn.1 hs).symm, hne⟩
  -- two entries differ in one of the two CFs
  have hsep : ∀ r ∈ treesOn q, ∀ r' ∈ treesOn q, r ≠ r' →
      nmscCF N (θ.withPair k₁ k₂ 1) 0 r ≠ nmscCF N (θ.withPair k₁ k₂ 1) 0 r' ∨
        nmscCF N (θ.withPair k₁ k₂ 0) 0 r ≠ nmscCF N (θ.withPair k₁ k₂ 0) 0 r' := by
    intro r hr r' hr' hne
    by_cases h₁ : r = s₁
    · subst h₁
      exact Or.inl (hcf₁ r' (htaxa r' hr' r hr hne.symm)).symm
    by_cases h₂ : r' = s₁
    · subst h₂
      exact Or.inl (hcf₁ r (htaxa r hr r' hr' hne))
    by_cases h₃ : r = s₂
    · subst h₃
      exact Or.inr (hcf₂ r' (htaxa r' hr' r hr hne.symm)).symm
    by_cases h₄ : r' = s₂
    · subst h₄
      exact Or.inr (hcf₂ r (htaxa r hr r' hr' hne))
    · exact absurd (eq_of_mem_treesOn_of_ne hq hs₁ hs₂ hss hr hr' h₁ h₃ h₂ h₄) hne
  -- the choice of `γ`
  obtain ⟨γ, hγ, hne⟩ := exists_mem_Ioo_forall_ne (treesOn q) (fun r => nmscCF N (θ.withPair k₁ k₂ 1) 0 r)
    (fun r => nmscCF N (θ.withPair k₁ k₂ 0) 0 r) hsep
  have hmix : ∀ t ∈ treesOn q, nmscCF N (θ.withPair k₁ k₂ γ) 0 t =
      γ * nmscCF N (θ.withPair k₁ k₂ 1) 0 t + (1 - γ) * nmscCF N (θ.withPair k₁ k₂ 0) 0 t := fun t ht =>
    NMSC.nmscCF_withPair hN hw.isNormalized le_rfl hD0 hk ht' hpar t a
      (fun y hy hya => hnot y (mem_treesOn.1 ht ▸ hy) hya) _
  refine ⟨θ.withPair k₁ k₂ γ, NMSC.isWeakMetric_withPair hw hk ht' h0 ⟨hγ.1.le, hγ.2.le⟩,
    fun e he => ?_, fun r hr r' hr' hrr => ?_⟩
  · change (if e ∈ Z then 0 else x.1 e) = 0
    exact ite_eq_left he
  · rw [hmix r hr, hmix r' hr']
    exact hne r hr r' hr' hrr

/-- The witness of part (b) of the proof of Theorem 1: at the reduction of `exists_reduction`, the parameters of
`exists_isNonCut_of_reduction`. "It is enough to show there is a single choice of numerical parameters that gives
a non-cut CF" (`notes/sources/allman2023.txt`, line 145). -/
theorem exists_isNonCut_of_not_isTreelike (hN : N.IsPhylogenetic) (hBin : N.IsBinary)
    {q : Finset X} (hq : q.card = 4) (hnt : ¬ IsTreelike N q) :
    ∃ θ, N.IsWeakMetric θ ∧ IsNonCut (nmscCF N θ 0) q := by
  obtain ⟨D, k₁, k₂, a, s₁, s₂, e₁, e₂, hD, hk, ht, hk₁, hk₂, hpar, -, -, hnot, hs₁, hs₂, hss, hsp₁,
    hsp₂⟩ := exists_reduction hN hBin hq hnt
  obtain ⟨θ, hθ, -, hnc⟩ := exists_isNonCut_of_reduction (Z := ∅) hN hD hk ht hk₁ hk₂ hpar hq hnot hs₁ hs₂
    hss hsp₁ hsp₂ (Set.notMem_empty _) (Set.notMem_empty _)
  exact ⟨θ, hθ, hnc⟩

/-- **Statement (b) in the proof of Theorem 1 of the source** (`notes/sources/allman2023.txt`, lines 145-152):
for a 4-set without a cut-edge split on its induced network, the CF is non-cut for generic parameters. "Again
using the analyticity of `CF` it is enough to show there is a single choice of numerical parameters that gives
a non-cut CF. We can even choose these parameters to be on the boundary of the stochastic parameter space". -/
theorem isGenericNull_not_isNonCut (hN : N.IsPhylogenetic) (hBin : N.IsBinary) {q : Finset X}
    (hq : q.card = 4) (hnt : ¬ IsTreelike N q) :
    IsGenericNull N {θ | N.IsMetric θ ∧ ¬ IsNonCut (nmscCF N θ 0) q} := by
  obtain ⟨θ₀, hθ₀, hnc⟩ := exists_isNonCut_of_not_isTreelike hN hBin hq hnt
  refine (IsGenericNull.iUnion
    (ι := {p : QuartetTree X × QuartetTree X // p.1 ∈ treesOn q ∧ p.2 ∈ treesOn q ∧ p.1 ≠ p.2})
    fun p => isGenericNull_nmscCF_eq (r := p.val.1) (r' := p.val.2) hθ₀.isNormalized
      (hnc _ p.property.1 _ p.property.2.1 p.property.2.2)).mono ?_
  rintro θ ⟨hθ, hnot⟩
  have hex : ∃ r ∈ treesOn q, ∃ r' ∈ treesOn q, r ≠ r' ∧ nmscCF N θ 0 r = nmscCF N θ 0 r' := by
    by_contra hall
    push Not at hall
    exact hnot hall
  obtain ⟨r, hr, r', hr', hne, heq⟩ := hex
  exact Set.mem_iUnion.2 ⟨⟨(r, r'), hr, hr', hne⟩, hθ, heq⟩

/-! ### Theorem 1 -/

omit [Fintype V] [Fintype E] in
/-- CF-detectability gives the direct implication; the converse is the argument of the source's proof of
Theorem 1. If the CF is strictly `s`-cut, it is not non-cut, so the taxa have a cut-edge split `s₀`. If
`s₀ ≠ s`, the third tree `t` has `p s₀ = p t` as alternatives of `s`, and `p s = p t` as alternatives of
`s₀`, so `p s₀ = p s`, against strictness. -/
theorem CFDetectable.inducedCutSplit_iff {p : QuartetTree X → ℝ} (h : CFDetectable N p)
    (s : QuartetTree X) : InducedCutSplit N s ↔ IsStrictlyCut p s := by
  refine ⟨h.cut s, fun hsc => ?_⟩
  have htl : IsTreelike N s.taxa := by
    by_contra hnt
    obtain ⟨r, r', hne, halt⟩ := card_eq_two.1 s.card_alternatives
    have hr : r ∈ s.alternatives := by simp [halt]
    have hr' : r' ∈ s.alternatives := by simp [halt]
    exact h.blob s.taxa s.card_taxa hnt r (mem_treesOn.2 (QuartetTree.mem_alternatives.1 hr).1) r'
      (mem_treesOn.2 (QuartetTree.mem_alternatives.1 hr').1) hne (hsc.2 r hr r' hr')
  obtain ⟨s₀, hs₀, hc⟩ := htl
  by_contra hns
  have hne : s₀ ≠ s := fun h' => hns (h' ▸ hc)
  have hs₀t := mem_treesOn.1 hs₀
  have hs₀a : s₀ ∈ s.alternatives := QuartetTree.mem_alternatives.2 ⟨hs₀t, hne⟩
  obtain ⟨t, ht, hts₀⟩ := exists_mem_ne (by rw [s.card_alternatives]; norm_num :
    1 < s.alternatives.card) s₀
  have hsc₀ := h.cut s₀ hc
  have hsa : s ∈ s₀.alternatives := QuartetTree.mem_alternatives.2 ⟨hs₀t.symm, hne.symm⟩
  have hta : t ∈ s₀.alternatives :=
    QuartetTree.mem_alternatives.2 ⟨(QuartetTree.mem_alternatives.1 ht).1.trans hs₀t.symm, hts₀⟩
  exact hsc.1 s₀ hs₀a ((hsc.2 s₀ hs₀a t ht).trans (hsc₀.2 s hsa t hta).symm)

omit [Fintype V] [Fintype E] in
/-- CF-detectability gives the direct implication; conversely, a non-cut CF has no cut-edge split, which
would make two entries equal. -/
theorem CFDetectable.not_isTreelike_iff {p : QuartetTree X → ℝ} (h : CFDetectable N p)
    {q : Finset X} (hq : q.card = 4) : ¬ IsTreelike N q ↔ IsNonCut p q := by
  refine ⟨h.blob q hq, fun hnc ⟨s, hs, hc⟩ => ?_⟩
  obtain ⟨r, r', hne, halt⟩ := card_eq_two.1 s.card_alternatives
  have hr : r ∈ s.alternatives := by simp [halt]
  have hr' : r' ∈ s.alternatives := by simp [halt]
  have hst := mem_treesOn.1 hs
  exact hnc r (mem_treesOn.2 ((QuartetTree.mem_alternatives.1 hr).1.trans hst)) r'
    (mem_treesOn.2 ((QuartetTree.mem_alternatives.1 hr').1.trans hst)) hne
    ((h.cut s hc).2 r hr r' hr')

/-- **Theorem 1 of the source (CF-detectability of 4-blobs on 4-taxon networks; TINNiK Theorem 1)**: on a
4-taxon rooted binary phylogenetic network, for generic parameters,

1. a quartet tree `s` is a cut-edge split if, and only if, the CF is strictly `s`-cut;
2. the network has no such split if, and only if, the CF is non-cut.

The proof follows the source. Statements (a) and (b) hold for generic parameters
(`isGenericNull_not_isStrictlyCut`, `isGenericNull_not_isNonCut`). "Were it not for the distinction between 'cut' and
'strictly cut', these statements would immediately yield claims 1 and 2": `CFDetectable.inducedCutSplit_iff` and
`CFDetectable.not_isTreelike_iff` are the source's last step, that "if `CF` is cut, then `T` has a resolved tree
topology, which by (a) implies that `CF` is strictly cut". -/
theorem theorem1 (hN : N.IsPhylogenetic) (hBin : N.IsBinary) (hX : Fintype.card X = 4) :
    IsGenericNull N {θ | N.IsMetric θ ∧
      ¬ ((∀ s : QuartetTree X, InducedCutSplit N s ↔ IsStrictlyCut (nmscCF N θ 0) s) ∧
        (¬ IsTreelike N Finset.univ ↔ IsNonCut (nmscCF N θ 0) Finset.univ))} := by
  have huniv : (Finset.univ : Finset X).card = 4 := by rw [card_univ, hX]
  have hb : IsGenericNull N {θ | N.IsMetric θ ∧ ¬ IsTreelike N Finset.univ ∧
      ¬ IsNonCut (nmscCF N θ 0) Finset.univ} := by
    by_cases hnt : IsTreelike N Finset.univ
    · intro d _
      refine measure_mono_null ?_ measure_empty
      rintro x ⟨θ, ⟨-, h, -⟩, -⟩
      exact h hnt
    · exact (isGenericNull_not_isNonCut hN hBin huniv hnt).mono fun θ hθ => ⟨hθ.1, hθ.2.2⟩
  refine (IsGenericNull.union
    (IsGenericNull.iUnion (ι := {s : QuartetTree X // InducedCutSplit N s}) fun s =>
      isGenericNull_not_isStrictlyCut hN s.property) hb).mono ?_
  rintro θ ⟨hθ, hnot⟩
  by_contra hall
  have hdet : CFDetectable N (nmscCF N θ 0) := by
    refine ⟨fun s hs => ?_, fun q hq hnt => ?_⟩
    · by_contra hsc
      exact hall (Or.inl (Set.mem_iUnion.2 ⟨⟨s, hs⟩, hθ, hsc⟩))
    · have hqu : q = Finset.univ := Finset.eq_univ_of_card q (by rw [hq, hX])
      subst hqu
      by_contra hnc
      exact hall (Or.inr ⟨hθ, hnt, hnc⟩)
  exact hnot ⟨fun s => hdet.inducedCutSplit_iff s, hdet.not_isTreelike_iff huniv⟩

end AllmanEtAl2023
