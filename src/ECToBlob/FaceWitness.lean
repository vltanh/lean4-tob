module

public import AllmanEtAl2023.GenericCF

/-!
# ECToBlob: non-cut parameters on a face, at a reduction

The witness that ECToBlob's adaptation of Theorem 1 of Allman et al. 2023 needs, for networks whose reticulations have degree three and whose other nodes in non-trivial blobs may have any degree (`ECToBlob.exists_face_isNonCut`). It reads the two deleted networks off a set `D` of arcs of `N`, in the coordinates of `N`, and proves only the half of "strictly cut" that the choice of `γ` uses.

This is not a proof of Theorem 1 of Allman et al. 2023, which is `AllmanEtAl2023.theorem1`.

## Main results

* `offMetric`, `measure_nmscCF_eq_offMetric`: a split off `D` gives, for generic parameters off `D`, a CF that differs from its alternatives.
* `exists_isNonCut_of_reduction`: at a reduction, parameters with a non-cut CF, with length `0` on a set `Z` of arcs other than the cut arcs.
-/

@[expose] public noncomputable section

open Phylogenetics Phylogenetics.RootedNetwork Finset MeasureTheory
open scoped Classical

open Phylogenetics.DirectedMultigraph AllmanEtAl2023

open Phylogenetics.NMSC

namespace ECToBlob

variable {V E X : Type*} [Fintype V] [Fintype E] [Fintype X] [DecidableEq X]
  {N : RootedNetwork V E X}

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
have length `0`: the hybrid arcs in ECToBlob's measure. -/
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

/-- **A split off `D` gives a CF that differs from its alternatives**, for generic parameters off `D`. Long cut arcs give a point (`nmscCF_lt_nmscCF_of_splitOffAt`), and a CF is analytic in the coordinates. So all the numerical parameters off `D` vary, lengths and the other inheritance probabilities. The other half of "strictly cut", that the alternatives are equal, is not needed for the choice of `γ` (`exists_mem_Ioo_forall_ne`). -/
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
/-- **Setting `γ = 0` on `k'` gives the parameters of the deleted network**. Let `k`,
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

/-- **Parameters with a non-cut CF at a reduction** of `exists_reduction_of_blobDegree`: a set `D` of arcs of inheritance `0`, and two parents `k₁`, `k₂` with at most `a` below them. It is the argument of part (b) of the proof of Theorem 1 of Allman et al. 2023 (the PMC text, lines 150-152), read off `D`.

The CF is the mixture `γ₁ CF¹ + γ₂ CF²` of the CFs of the two deleted networks (`NMSC.nmscCF_withPair`). `CF¹` and `CF²` differ from their alternatives for generic parameters (`measure_nmscCF_eq_offMetric`, for `insert k₂ D` and `insert k₁ D`). So a choice of the coordinates `x` (`exists_isStochasticCoords_notMem`), and then of `γ` (`exists_mem_Ioo_forall_ne`), gives a non-cut CF.

The set `Z` of arcs of length `0`, disjoint from the cut arcs, is the set of hybrid arcs for ECToBlob's measure, which needs a point on that face (`exists_face_isNonCut`). -/
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

end ECToBlob
