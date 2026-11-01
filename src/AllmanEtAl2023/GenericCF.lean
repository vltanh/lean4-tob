module

public import Basic.ForMathlib.Analysis.AnalyticZeroSet
public import Basic.General
public import Phylogenetics.NMSC.Analytic
public import Phylogenetics.NMSC.Exchangeability
public import Phylogenetics.NMSC.Witness
public import AllmanEtAl2023.Basic
public import Phylogenetics.Network.DeletedArcs
public import AllmanEtAl2023.CutOrder

/-!
# Allman, Baños, Mitchell, Rhodes 2023: tools for concordance factors at generic parameters

The paper's Theorem 1 (the PMC text, lines 129-152) is `theorem1` in
`AllmanEtAl2023.Theorem1`, through `AllmanEtAl2023.Theorem1a` (statement (a)) and
`AllmanEtAl2023.Theorem1b` (statement (b)).

This file holds the tools those proofs use, and that ECToBlob and TINNiK use on their own.

## Main results

* `deletionMetric`, `isWeakMetric_deletionMetric`: boundary parameters off a deletion.
* `coordMetric_self`: every normalized parameter is in the image of `coordMetric`, for every parent choice.
* `exists_leftOutParent`: the parents left out of the coordinates.
* `isGenericNull_of_analyticOnNhd`, `isGenericNull_nmscCF_eq`: null sets of parameters, from analyticity.
* `three_quarters_lt_nmscCF`, `nmscCF_lt_nmscCF_of_splitOffAt`: long cut arcs make the CF of a split large.
* `exists_isStochasticCoords_notMem`, `exists_mem_Ioo_forall_ne`: the choices of the parameters in (b).
* `CFDetectable.inducedCutSplit_iff`, `CFDetectable.not_isTreelike_iff`: the paper's last step, from (a) and (b) to the iff.
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

omit [Fintype V] [Fintype X] [DecidableEq X] in
/-- **The parents left out of the coordinates**: at each hybrid node, one of its parents. -/
theorem exists_leftOutParent (e₀ : E) : ∃ d : V → E, ∀ v, 2 ≤ N.graph.indegree v → N.graph.target (d v) = v := by
  have hex : ∀ v, ∃ f : E, 2 ≤ N.graph.indegree v → N.graph.target f = v := fun v => by
    by_cases hv : 2 ≤ N.graph.indegree v
    · obtain ⟨f, hf⟩ := (N.graph.one_le_indegree_iff v).mp (by omega)
      exact ⟨f, fun _ => hf⟩
    · exact ⟨e₀, fun h => absurd h hv⟩
  choose d hd using hex
  exact ⟨d, hd⟩

/-! ### Null sets of parameters -/

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

/-! ### A long cut arc -/

omit [Fintype V] [Fintype E] [Fintype X] in
/-- Deleting more arcs keeps a split. -/
theorem _root_.Phylogenetics.RootedNetwork.SplitOffAt.mono {D D' : Set E} (hDD : D ⊆ D') {e : E} {s : QuartetTree X}
    (hs : N.SplitOffAt D e s) : N.SplitOffAt D' e s := by
  obtain ⟨P, hP, hdom, hnb⟩ := hs
  exact ⟨P, hP, fun x hx hr => hdom x hx (hr.mono (Set.insert_subset_insert hDD)),
    fun x hx hb => hnb x hx ⟨fun h => hb.1 (hDD h), hb.2.mono hDD⟩⟩

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
(the PMC text, line 143). -/
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

/-- Coordinates in the interior of the stochastic parameter space: positive lengths, and inheritance
probabilities small enough that the left-out parent keeps a positive one. -/
def IsStochasticCoords (x : (E → ℝ) × (E → ℝ)) : Prop :=
  (∀ e, 0 < x.1 e) ∧ ∀ e, 0 < x.2 e ∧ x.2 e < ((Fintype.card E : ℝ) + 1)⁻¹

/-- Lebesgue measure on the coordinates `(lengths, inheritance)` of the parameters. -/
abbrev coordVolume (E : Type*) [Fintype E] : Measure ((E → ℝ) × (E → ℝ)) :=
  (Measure.pi fun _ : E => (volume : Measure ℝ)).prod (Measure.pi fun _ : E => (volume : Measure ℝ))

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

/-! ### The choice of `γ` -/

/-- Two distinct trees on four taxa leave one tree. -/
theorem eq_of_mem_treesOn_of_ne {q : Finset X} (hq : q.card = 4) {s₁ s₂ r r' : QuartetTree X}
    (hs₁ : s₁ ∈ treesOn q) (hs₂ : s₂ ∈ treesOn q) (hss : s₁ ≠ s₂) (hr : r ∈ treesOn q)
    (hr' : r' ∈ treesOn q) (h₁ : r ≠ s₁) (h₂ : r ≠ s₂) (h₃ : r' ≠ s₁) (h₄ : r' ≠ s₂) : r = r' := by
  have hc : (((treesOn q).erase s₁).erase s₂).card ≤ 1 := by
    rw [card_erase_of_mem (mem_erase.2 ⟨hss.symm, hs₂⟩), card_erase_of_mem hs₁, card_treesOn hq]
  exact card_le_one.1 hc _ (mem_erase.2 ⟨h₂, mem_erase.2 ⟨h₁, hr⟩⟩) _
    (mem_erase.2 ⟨h₄, mem_erase.2 ⟨h₃, hr'⟩⟩)

/-- **The choice of `γ`** (the source's "we may then pick values of `γ₁`, `γ₂`",
the PMC text, line 152). If any two entries differ in one of two vectors `p₁`, `p₀`, then for all
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

/-! ### From (a) and (b) to the iff -/

omit [Fintype V] [Fintype E] in
/-- CF-detectability gives the direct implication; the converse is the argument of the source's proof of
Theorem 1. If the CF is strictly `s`-cut, it is not non-cut, so the taxa have a cut-edge split `s₀`. If
`s₀ ≠ s`, the third tree `t` has `p s₀ = p t` as alternatives of `s`, and `p s = p t` as alternatives of
`s₀`, so `p s₀ = p s`, against strictness. -/
theorem CFDetectable.inducedCutSplit_iff {p : QuartetTree X → ℝ} (h : CFDetectable N p)
    (s : QuartetTree X) : InducedCutSplit N s ↔ IsStrictlyCutAt p s := by
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

end AllmanEtAl2023
