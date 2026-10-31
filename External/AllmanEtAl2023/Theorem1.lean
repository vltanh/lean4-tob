module

public import Basic.Analysis.AnalyticZeroSet
public import Basic.Phylogenetics.NMSC.Analytic
public import Basic.Phylogenetics.NMSC.Exchangeability
public import Basic.Phylogenetics.NMSC.Witness
public import External.AllmanEtAl2023.Reduction

/-!
# Allman, Baños, Mitchell, Rhodes 2023: Theorem 1 and Corollary 1

CF-detectability of 4-blobs for generic parameters (`notes/sources/allman2023.txt`, lines 129-157). The
proof follows the source. Its two statements are, for generic parameters,

* (a) a cut-edge split `s` of the induced network gives a strictly `s`-cut CF
  (`isGenericNull_not_isStrictlyCut`). The two alternatives are equal for all parameters
  (`NMSC.cut_alternatives`), and long arcs make the CF of `s` near `1`, so the difference is a nonzero
  analytic function.
* (b) an induced network without a cut-edge split gives a non-cut CF (`isGenericNull_not_isNonCut`).
  One point suffices, on the boundary, since the parametrization is analytic on all of the coordinates
  (`analyticOnNhd_nmscCF_coordMetric`). At the point, the arcs `D` of `exists_reduction` have
  inheritance `0`, and the two parents of the reticulation left have inheritance `(1/3, 2/3)`, so that
  the CF is the mixture of two strictly cut CFs with different splits, and the three entries are near
  `1/3`, `2/3` and `0`.

The iff form of Theorem 1, the source's actual statement, follows as in the source: `theorem1`, by
`CFDetectable.inducedCutSplit_iff` and `CFDetectable.not_isTreelike_iff`.

## Departures from the source

* The source removes the 2-blobs of a network first, by setting lengths to `0`. This is not needed:
  see `exists_reduction_aux`.
* The source treats the three rooted forms of the tree of blobs in turn for (a). Here one arc dominates
  two of the taxa and has the others off it (`hasCutSplitOn_iff_separates`), which covers all three.
* The source proves Theorem 1 for a 4-taxon network, then derives Corollary 1 by applying it to each
  induced 4-taxon network, and says the null sets on those give a null set on the whole network. That
  would need the map from the parameters of `N` to those of an induced network, and that preimages of
  null sets under it are null, which the source does not discuss. Here (a) and (b) are proved on `N`
  itself: domination off `D` sees the four taxa alone, and a concordance factor is analytic in the
  coordinates of `N`. So `corollary1` needs no comparison of parameter spaces, and the source's
  Theorem 1 for a 4-taxon network is the case `X = q`.
* The source picks `γ` for the mixture after taking generic parameters on the two networks. Long arcs
  make one explicit point suffice: length `3` on the cut arcs and `γ = 1/3`.

## Main results

* `deletionMetric`, `isWeakMetric_deletionMetric`: boundary parameters off a deletion.
* `coordMetric_self`: every normalized parameter is in the image of `coordMetric`, for every parent choice.
* `nmscCF_ne_of_reduction`: the source's single point in (b).
* `isGenericNull_of_analyticOnNhd`, `IsGenericNull.iUnion`: null sets of parameters.
* `corollary1`, `theorem1`.
-/

@[expose] public noncomputable section

open Phylogenetics Phylogenetics.RootedNetwork Finset MeasureTheory
open scoped Classical

namespace External.AllmanEtAl2023

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
`3/4`. -/
theorem three_quarters_lt_nmscCF (hN : N.IsPhylogenetic) {D : Set E} (hD : N.IsDeletion D)
    {ℓ : E → ℝ} (hℓ : ∀ e, 0 ≤ ℓ e) {e : E} (he : ℓ e = 3) {s : QuartetTree X}
    (hs : N.SplitOffAt D e s) : 3 / 4 < nmscCF N (deletionMetric N D ℓ) 0 s := by
  have h := NMSC.one_sub_exp_le_nmscCF (ρ := 0) hN (isWeakMetric_deletionMetric hN hD hℓ)
    ⟨le_rfl, zero_le_one⟩ hD (fun f hf => ite_eq_left hf) hs
  rw [show (deletionMetric N D ℓ).length e = 3 from he] at h
  linarith [exp_neg_three_lt]

/-- The witness of part (a): all lengths `3`. The CF of `s` is more than `3/4`, those of its alternatives
less than `1/4`. -/
theorem nmscCF_lt_nmscCF_of_inducedCutSplit (hN : N.IsPhylogenetic) {s r : QuartetTree X}
    (hs : InducedCutSplit N s) (hr : r ∈ s.alternatives) :
    nmscCF N (deletionMetric N ∅ fun _ => 3) 0 r <
      nmscCF N (deletionMetric N ∅ fun _ => 3) 0 s := by
  have hℓ : ∀ _ : E, (0 : ℝ) ≤ 3 := fun _ => by norm_num
  have hD := isDeletion_empty (N := N) hN
  obtain ⟨e, he⟩ := exists_splitOffAt_of_inducedCutSplit hN hs
  obtain ⟨hrt, hne⟩ := QuartetTree.mem_alternatives.1 hr
  have h₁ := three_quarters_lt_nmscCF hN hD hℓ rfl he
  have h₂ := NMSC.nmscCF_le_exp_of_splitOffAt (ρ := 0) hN (isWeakMetric_deletionMetric hN hD hℓ)
    ⟨le_rfl, zero_le_one⟩ hD (fun f hf => ite_eq_left hf) he hrt hne
  rw [show (deletionMetric N ∅ fun _ => (3 : ℝ)).length e = 3 from rfl] at h₂
  linarith [exp_neg_three_lt]

/-! ### Part (b): the mixture at a single point -/

/-- Two distinct trees on four taxa leave one tree. -/
theorem eq_of_mem_treesOn_of_ne {q : Finset X} (hq : q.card = 4) {s₁ s₂ r r' : QuartetTree X}
    (hs₁ : s₁ ∈ treesOn q) (hs₂ : s₂ ∈ treesOn q) (hss : s₁ ≠ s₂) (hr : r ∈ treesOn q)
    (hr' : r' ∈ treesOn q) (h₁ : r ≠ s₁) (h₂ : r ≠ s₂) (h₃ : r' ≠ s₁) (h₄ : r' ≠ s₂) : r = r' := by
  have hc : (((treesOn q).erase s₁).erase s₂).card ≤ 1 := by
    rw [card_erase_of_mem (mem_erase.2 ⟨hss.symm, hs₂⟩), card_erase_of_mem hs₁, card_treesOn hq]
  exact card_le_one.1 hc _ (mem_erase.2 ⟨h₂, mem_erase.2 ⟨h₁, hr⟩⟩) _
    (mem_erase.2 ⟨h₄, mem_erase.2 ⟨h₃, hr'⟩⟩)

/-- **The source's single point in part (b) of the proof of Theorem 1**
(`notes/sources/allman2023.txt`, lines 150-152): at the reduction of `exists_reduction`, with inheritance
`0` on `D`, `(1/3, 2/3)` on `(k₁, k₂)`, and length `3` on the two cut arcs, the three concordance factors on
`q` are distinct. Since one taxon is below the reticulation, the CF is the mixture of the CFs with `k₂`
deleted and with `k₁` deleted (`NMSC.nmscCF_withPair`), and those are near `(1, 0, 0)` and `(0, 1, 0)`
(`NMSC.one_sub_exp_le_nmscCF`). So the entries are near `1/3`, `2/3` and `0`. Lengths of other arcs are free,
which is what ECToBlob's adaptation needs. -/
theorem nmscCF_ne_of_reduction (hN : N.IsPhylogenetic) {D : Set E} (hD : N.IsDeletion D) {k₁ k₂ : E}
    (hk : k₁ ≠ k₂) (ht : N.graph.target k₁ = N.graph.target k₂) (hk₁ : k₁ ∉ D) (hk₂ : k₂ ∉ D)
    (hpar : ∀ f, N.graph.target f = N.graph.target k₁ → f ∉ D → f = k₁ ∨ f = k₂)
    {q : Finset X} (hq : q.card = 4) {a : X}
    (hnot : ∀ x ∈ q, x ≠ a → ¬ N.ReachesOff D (N.graph.target k₁) (N.leaf x))
    {s₁ s₂ : QuartetTree X} (hs₁ : s₁ ∈ treesOn q) (hs₂ : s₂ ∈ treesOn q) (hss : s₁ ≠ s₂) {e₁ e₂ : E}
    (hsp₁ : N.SplitOffAt (insert k₂ D) e₁ s₁) (hsp₂ : N.SplitOffAt (insert k₁ D) e₂ s₂)
    {ℓ : E → ℝ} (hℓ : ∀ e, 0 ≤ ℓ e) (hℓ₁ : ℓ e₁ = 3) (hℓ₂ : ℓ e₂ = 3) {r r' : QuartetTree X}
    (hr : r ∈ treesOn q) (hr' : r' ∈ treesOn q) (hne : r ≠ r') :
    nmscCF N ((deletionMetric N D ℓ).withPair k₁ k₂ (1 / 3)) 0 r ≠
      nmscCF N ((deletionMetric N D ℓ).withPair k₁ k₂ (1 / 3)) 0 r' := by
  set θ := deletionMetric N D ℓ with hθdef
  have hρ : (0 : ℝ) ≤ 0 ∧ (0 : ℝ) ≤ 1 := ⟨le_rfl, zero_le_one⟩
  have hw : N.IsWeakMetric θ := isWeakMetric_deletionMetric hN hD hℓ
  have hD0 : ∀ f ∈ D, θ.inheritance f = 0 := fun f hf => ite_eq_left hf
  have ht' : N.graph.target k₂ = N.graph.target k₁ := ht.symm
  have h0 : ∀ f, N.graph.target f = N.graph.target k₁ → f ≠ k₁ → f ≠ k₂ → θ.inheritance f = 0 :=
    fun f hf h₁ h₂ => hD0 f (by_contra fun hfD => (hpar f hf hfD).elim h₁ h₂)
  have hw₁ : N.IsWeakMetric (θ.withPair k₁ k₂ 1) :=
    NMSC.isWeakMetric_withPair hw hk ht' h0 ⟨zero_le_one, le_rfl⟩
  have hw₀ : N.IsWeakMetric (θ.withPair k₁ k₂ 0) :=
    NMSC.isWeakMetric_withPair hw hk ht' h0 ⟨le_rfl, zero_le_one⟩
  have hl₁ : Real.exp (-θ.length e₁) = Real.exp (-3) := by rw [show θ.length e₁ = 3 from hℓ₁]
  have hl₂ : Real.exp (-θ.length e₂) = Real.exp (-3) := by rw [show θ.length e₂ = 3 from hℓ₂]
  have hε := exp_neg_three_lt
  have hε₀ := Real.exp_pos (-3)
  -- the endpoints of the mixture
  have hlo₁ := NMSC.one_sub_exp_le_nmscCF_withPair_one (ρ := 0) hN hw hρ hD hD0 hk ht' hk₁ hpar hsp₁
  have hlo₀ := NMSC.one_sub_exp_le_nmscCF_withPair_zero (ρ := 0) hN hw hρ hD hD0 hk ht' hk₂ hpar hsp₂
  rw [hl₁] at hlo₁
  rw [hl₂] at hlo₀
  have htaxa : ∀ t ∈ treesOn q, ∀ s ∈ treesOn q, t.taxa = s.taxa := fun t ht s hs =>
    (mem_treesOn.1 ht).trans (mem_treesOn.1 hs).symm
  have hhi₁ : ∀ t ∈ treesOn q, t ≠ s₁ → nmscCF N (θ.withPair k₁ k₂ 1) 0 t ≤ Real.exp (-3) := by
    intro t htq hts
    have := NMSC.nmscCF_le_exp_of_splitOffAt (ρ := 0) hN hw₁ hρ (hD.insert hN hk.symm ht' hk₁)
      (NMSC.withPair_one_inheritance_eq_zero hD0 hk hk₁) hsp₁ (htaxa t htq s₁ hs₁) hts
    rwa [NMSC.withPair_length, hl₁] at this
  have hhi₀ : ∀ t ∈ treesOn q, t ≠ s₂ → nmscCF N (θ.withPair k₁ k₂ 0) 0 t ≤ Real.exp (-3) := by
    intro t htq hts
    have := NMSC.nmscCF_le_exp_of_splitOffAt (ρ := 0) hN hw₀ hρ (hD.insert hN hk ht hk₂)
      (NMSC.withPair_zero_inheritance_eq_zero hD0 hk₂) hsp₂ (htaxa t htq s₂ hs₂) hts
    rwa [NMSC.withPair_length, hl₂] at this
  have hnn₁ := NMSC.nmscCF_nonneg_weak (ρ := 0) hN hw₁ hρ
  have hnn₀ := NMSC.nmscCF_nonneg_weak (ρ := 0) hN hw₀ hρ
  have hsum₁ := NMSC.sum_nmscCF_weak (ρ := 0) hN hw₁.isNormalized le_rfl hq
  have hsum₀ := NMSC.sum_nmscCF_weak (ρ := 0) hN hw₀.isNormalized le_rfl hq
  have hone₁ : nmscCF N (θ.withPair k₁ k₂ 1) 0 s₁ ≤ 1 :=
    (single_le_sum (f := fun t => nmscCF N (θ.withPair k₁ k₂ 1) 0 t)
      (fun t _ => hnn₁ t) hs₁).trans_eq hsum₁
  have hone₀ : nmscCF N (θ.withPair k₁ k₂ 0) 0 s₂ ≤ 1 :=
    (single_le_sum (f := fun t => nmscCF N (θ.withPair k₁ k₂ 0) 0 t)
      (fun t _ => hnn₀ t) hs₂).trans_eq hsum₀
  -- the mixture
  have hmix : ∀ t ∈ treesOn q, nmscCF N (θ.withPair k₁ k₂ (1 / 3)) 0 t =
      1 / 3 * nmscCF N (θ.withPair k₁ k₂ 1) 0 t +
        (1 - 1 / 3) * nmscCF N (θ.withPair k₁ k₂ 0) 0 t := by
    intro t ht
    refine NMSC.nmscCF_withPair hN hw.isNormalized le_rfl hD0 hk ht' hpar t a (fun x hx hxa => ?_) _
    exact hnot x (mem_treesOn.1 ht ▸ hx) hxa
  have h₁ := hmix s₁ hs₁
  have h₂ := hmix s₂ hs₂
  have h₁₂ := hhi₁ s₂ hs₂ hss.symm
  have h₂₁ := hhi₀ s₁ hs₁ hss
  have hlt : nmscCF N (θ.withPair k₁ k₂ (1 / 3)) 0 s₁ <
      nmscCF N (θ.withPair k₁ k₂ (1 / 3)) 0 s₂ := by
    rw [h₁, h₂]
    linarith [hnn₁ s₂, hnn₀ s₁]
  have hthird : ∀ t ∈ treesOn q, t ≠ s₁ → t ≠ s₂ →
      nmscCF N (θ.withPair k₁ k₂ (1 / 3)) 0 t < nmscCF N (θ.withPair k₁ k₂ (1 / 3)) 0 s₁ := by
    intro t ht ht₁ ht₂
    rw [hmix t ht, h₁]
    linarith [hhi₁ t ht ht₁, hhi₀ t ht ht₂, hnn₀ s₁]
  intro heq
  by_cases h1 : r = s₁
  · subst h1
    by_cases h2 : r' = s₂
    · subst h2
      exact hlt.ne heq
    · exact (hthird r' hr' hne.symm h2).ne heq.symm
  · by_cases h2 : r = s₂
    · subst h2
      by_cases h3 : r' = s₁
      · subst h3
        exact hlt.ne' heq
      · exact ((hthird r' hr' h3 hne.symm).trans hlt).ne heq.symm
    · by_cases h3 : r' = s₁
      · subst h3
        exact (hthird r hr h1 h2).ne heq
      · by_cases h4 : r' = s₂
        · subst h4
          exact ((hthird r hr h1 h2).trans hlt).ne heq
        · exact hne (eq_of_mem_treesOn_of_ne hq hs₁ hs₂ hss hr hr' h1 h2 h3 h4)

/-- The witness of part (b) of the proof of Theorem 1: at the reduction of `exists_reduction`, all lengths
`3`. -/
theorem exists_isNonCut_of_not_isTreelike (hN : N.IsPhylogenetic) (hBin : N.IsBinary)
    {q : Finset X} (hq : q.card = 4) (hnt : ¬ IsTreelike N q) :
    ∃ θ, N.IsNormalized θ ∧ IsNonCut (nmscCF N θ 0) q := by
  obtain ⟨D, k₁, k₂, a, s₁, s₂, e₁, e₂, hD, hk, ht, hk₁, hk₂, hpar, -, -, hnot, hs₁, hs₂, hss, hsp₁,
    hsp₂⟩ := exists_reduction hN hBin hq hnt
  have hℓ : ∀ _ : E, (0 : ℝ) ≤ 3 := fun _ => by norm_num
  have hw := isWeakMetric_deletionMetric hN hD hℓ
  refine ⟨(deletionMetric N D fun _ => 3).withPair k₁ k₂ (1 / 3),
    NMSC.isNormalized_withPair hw.isNormalized hk ht.symm
      (fun f hf h₁ h₂ => ite_eq_left (by_contra fun hfD => (hpar f hf hfD).elim h₁ h₂)) _,
    fun r hr r' hr' hne => nmscCF_ne_of_reduction hN hD hk ht hk₁ hk₂ hpar hq hnot hs₁ hs₂ hss hsp₁
      hsp₂ hℓ rfl rfl hr hr' hne⟩

/-! ### Null sets of parameters -/

omit [Fintype V] [Fintype X] [DecidableEq X] in
/-- A subset of a null set of parameters is null. -/
theorem IsGenericNull.mono {A B : Set (MetricData E)} (hB : IsGenericNull N B) (h : A ⊆ B) :
    IsGenericNull N A := by
  intro d hd
  refine measure_mono_null ?_ (hB d hd)
  rintro x ⟨θ, hθ, rest⟩
  exact ⟨θ, h hθ, rest⟩

omit [Fintype V] [Fintype X] [DecidableEq X] in
/-- A countable union of null sets of parameters is null. -/
theorem IsGenericNull.iUnion {ι : Type*} [Countable ι] {A : ι → Set (MetricData E)}
    (h : ∀ i, IsGenericNull N (A i)) : IsGenericNull N (⋃ i, A i) := by
  intro d hd
  refine measure_mono_null ?_ (measure_iUnion_null fun i => h i d hd)
  rintro x ⟨θ, hθ, rest⟩
  obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hθ
  exact Set.mem_iUnion.2 ⟨i, θ, hi, rest⟩

omit [Fintype V] [Fintype X] [DecidableEq X] in
/-- The union of two null sets of parameters is null. -/
theorem IsGenericNull.union {A B : Set (MetricData E)} (hA : IsGenericNull N A)
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

/-! ### Theorem 1 and Corollary 1 -/

/-- **Statement (a) in the proof of Theorem 1 of the source**: for a cut-edge split `s` of the induced
network, the CF is strictly `s`-cut for generic parameters. The alternatives are equal for all parameters
(`NMSC.cut_alternatives`). Long arcs give a point where the CF of `s` differs from the CF of an
alternative, and the difference is analytic. -/
theorem isGenericNull_not_isStrictlyCut (hN : N.IsPhylogenetic) {s : QuartetTree X}
    (hs : InducedCutSplit N s) :
    IsGenericNull N {θ | N.IsMetric θ ∧ ¬ IsStrictlyCut (nmscCF N θ 0) s} := by
  refine (IsGenericNull.iUnion (ι := {r // r ∈ s.alternatives}) fun r =>
    isGenericNull_nmscCF_eq (r := r.val) (r' := s)
      (isNormalized_deletionMetric hN (isDeletion_empty hN) fun _ => 3)
      (nmscCF_lt_nmscCF_of_inducedCutSplit hN hs r.property).ne).mono ?_
  rintro θ ⟨hθ, hnot⟩
  have hex : ∃ r ∈ s.alternatives, nmscCF N θ 0 r = nmscCF N θ 0 s := by
    by_contra hall
    push Not at hall
    exact hnot ⟨hall, NMSC.cut_alternatives hN hθ ⟨le_rfl, zero_le_one⟩ s hs⟩
  obtain ⟨r, hr, heq⟩ := hex
  exact Set.mem_iUnion.2 ⟨⟨r, hr⟩, hθ, heq⟩

/-- **Statement (b) in the proof of Theorem 1 of the source**: for a 4-set without a cut-edge split on its
induced network, the CF is non-cut for generic parameters. -/
theorem isGenericNull_not_isNonCut (hN : N.IsPhylogenetic) (hBin : N.IsBinary) {q : Finset X}
    (hq : q.card = 4) (hnt : ¬ IsTreelike N q) :
    IsGenericNull N {θ | N.IsMetric θ ∧ ¬ IsNonCut (nmscCF N θ 0) q} := by
  obtain ⟨θ₀, hθ₀, hnc⟩ := exists_isNonCut_of_not_isTreelike hN hBin hq hnt
  refine (IsGenericNull.iUnion
    (ι := {p : QuartetTree X × QuartetTree X // p.1 ∈ treesOn q ∧ p.2 ∈ treesOn q ∧ p.1 ≠ p.2})
    fun p => isGenericNull_nmscCF_eq (r := p.val.1) (r' := p.val.2) hθ₀
      (hnc _ p.property.1 _ p.property.2.1 p.property.2.2)).mono ?_
  rintro θ ⟨hθ, hnot⟩
  have hex : ∃ r ∈ treesOn q, ∃ r' ∈ treesOn q, r ≠ r' ∧ nmscCF N θ 0 r = nmscCF N θ 0 r' := by
    by_contra hall
    push Not at hall
    exact hnot hall
  obtain ⟨r, hr, r', hr', hne, heq⟩ := hex
  exact Set.mem_iUnion.2 ⟨⟨(r, r'), hr, hr', hne⟩, hθ, heq⟩

/-- **Corollary 1 of the source**: for a rooted binary phylogenetic network, the numerical parameters at
which the NMSC with independent inheritance fails CF-detectability on some induced 4-taxon network form a
null set.

Departure from the source: it applies Theorem 1 to each induced 4-taxon network, and says the null sets
there give a null set on `N`. Here statements (a) and (b) are proved on `N` itself, in whose coordinates the
CFs are analytic, so no comparison of parameter spaces is needed. -/
theorem corollary1 (hN : N.IsPhylogenetic) (hBin : N.IsBinary) : Corollary1 N := by
  refine (IsGenericNull.union
    (IsGenericNull.iUnion (ι := {s : QuartetTree X // InducedCutSplit N s}) fun s =>
      isGenericNull_not_isStrictlyCut hN s.property)
    (IsGenericNull.iUnion (ι := {q : Finset X // q.card = 4 ∧ ¬ IsTreelike N q}) fun q =>
      isGenericNull_not_isNonCut hN hBin q.property.1 q.property.2)).mono ?_
  rintro θ ⟨hθ, hnot⟩
  by_contra hall
  refine hnot ⟨fun s hs => ?_, fun q hq hnt => ?_⟩
  · by_contra hsc
    exact hall (Or.inl (Set.mem_iUnion.2 ⟨⟨s, hs⟩, hθ, hsc⟩))
  · by_contra hnc
    exact hall (Or.inr (Set.mem_iUnion.2 ⟨⟨q, hq, hnt⟩, hθ, hnc⟩))

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

/-- **Theorem 1 of the source (CF-detectability of 4-blobs on 4-taxon networks; TINNiK Theorem 1)**, in its
iff form, on all induced 4-taxon networks of a rooted binary phylogenetic network: for generic parameters,

1. a quartet tree `s` is a cut-edge split of the network induced on its taxa if, and only if, the CF is
   strictly `s`-cut;
2. a set `q` of four taxa has no such split if, and only if, the CF on `q` is non-cut.

The source's Theorem 1 is the case `X = q`. The proof follows the source: statements (a) and (b) give
CF-detectability (`corollary1`), and that gives the two equivalences
(`CFDetectable.inducedCutSplit_iff`, `CFDetectable.not_isTreelike_iff`). -/
theorem theorem1 (hN : N.IsPhylogenetic) (hBin : N.IsBinary) :
    IsGenericNull N {θ | N.IsMetric θ ∧
      ¬ ((∀ s, InducedCutSplit N s ↔ IsStrictlyCut (nmscCF N θ 0) s) ∧
        ∀ q : Finset X, q.card = 4 → (¬ IsTreelike N q ↔ IsNonCut (nmscCF N θ 0) q))} := by
  refine IsGenericNull.mono (corollary1 hN hBin) ?_
  rintro θ ⟨hθ, hnot⟩
  exact ⟨hθ, fun hdet => hnot
    ⟨fun s => hdet.inducedCutSplit_iff s, fun q hq => hdet.not_isTreelike_iff hq⟩⟩

end External.AllmanEtAl2023
