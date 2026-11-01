module

public import AllmanEtAl2023.InducedCF

/-!
# Allman, Baños, Mitchell, Rhodes 2023: steps 2 and 3 of Definition 6, on any network

An induced network (Definition 6), a network `𝒩ᵢ⁺` of the proof of Theorem 1 (b), and a network with a 2-blob removed (the same proof) are all made from a phylogenetic network `R`, by suppressing the nodes of in- and
out-degree 1 and removing a stem: `removeStem (R.suppress hR) _`, with the map of parameters `stemMetric _ (R.suppressMetric η)`. Each then differs only in how `R` arises. What they share is proved here once.

* `nmscCF_suppressStem`: the `CF`s do not change;
* `isMetric_suppressStem`: valid parameters go to valid parameters;
* `exists_suppressStem_lift`: the map of parameters is onto valid boundary parameters.
-/

@[expose] public noncomputable section

open Phylogenetics Phylogenetics.RootedNetwork Phylogenetics.NMSC Finset
open scoped Classical

namespace AllmanEtAl2023

section Lift

variable {V E X : Type*}

/-- Step 3 of the map of parameters is onto valid boundary parameters: a stem can have any length. -/
theorem exists_stem_lift [Fintype E] [Nontrivial X] {M : RootedNetwork V E X} [Fintype {e // ¬ (HasStem M ∧ M.graph.source e = M.root)}] (hM : M.IsPhylogenetic)
    {θ' : MetricData {e // ¬ (HasStem M ∧ M.graph.source e = M.root)}} (hθ' : (removeStem M hM).IsWeakMetric θ') :
    ∃ θ, M.IsWeakMetric θ ∧ stemMetric M θ = θ' := by
  have hP := removeStem_isPhylogenetic hM
  let θ : MetricData E :=
    { length := fun e => if h : ¬ (HasStem M ∧ M.graph.source e = M.root) then θ'.length ⟨e, h⟩ else 0
      inheritance := fun e => if h : ¬ (HasStem M ∧ M.graph.source e = M.root) then θ'.inheritance ⟨e, h⟩ else 1 }
  have hlen : ∀ e : {e // ¬ (HasStem M ∧ M.graph.source e = M.root)}, θ.length e.1 = θ'.length e := fun e => dite_eq_left_of_eq_true (eq_true e.2)
  have hinh : ∀ e : {e // ¬ (HasStem M ∧ M.graph.source e = M.root)}, θ.inheritance e.1 = θ'.inheritance e := fun e => dite_eq_left_of_eq_true (eq_true e.2)
  have hstem : ∀ e, ¬ ¬ (HasStem M ∧ M.graph.source e = M.root) → θ.inheritance e = 1 := fun e he => dite_eq_right_of_eq_false (eq_false he)
  have hstemL : ∀ e, ¬ ¬ (HasStem M ∧ M.graph.source e = M.root) → θ.length e = 0 := fun e he => dite_eq_right_of_eq_false (eq_false he)
  refine ⟨θ, ⟨fun e => ?_, fun e he => ?_, fun e he => ?_, fun v hv => ?_⟩, ?_⟩
  · by_cases h : ¬ (HasStem M ∧ M.graph.source e = M.root)
    · rw [hlen ⟨e, h⟩]
      exact hθ'.1 _
    · rw [hstemL e h]
  · by_cases h : ¬ (HasStem M ∧ M.graph.source e = M.root)
    · rw [hinh ⟨e, h⟩]
      exact hθ'.2.1 ⟨e, h⟩ (le_of_le_of_eq he (removeStem_indegree_target hM ⟨e, h⟩).symm)
    · rw [hstem e h]
      exact zero_le_one
  · by_cases h : ¬ (HasStem M ∧ M.graph.source e = M.root)
    · rw [hinh ⟨e, h⟩]
      exact hθ'.2.2.1 ⟨e, h⟩ ((removeStem_indegree_target hM ⟨e, h⟩).trans he)
    · exact hstem e h
  · have hne : ¬ (HasStem M ∧ v = M.root) := fun hc => by
      rw [hc.2, hM.root_indegree] at hv
      omega
    have hvr : (⟨v, hne⟩ : {v // ¬ (HasStem M ∧ v = M.root)}) ≠ (removeStem M hM).root := by
      intro hr
      by_cases hs : HasStem M
      · have hv' : v = M.graph.target (stemArc M hs) := by
          have := congrArg Subtype.val hr
          simpa only [removeStem, dite_eq_left hs] using this
        have h1 : M.graph.indegree v = 1 := by
          rw [hv']
          exact (M.graph.indegree_eq_one_iff _).mpr ⟨stemArc M hs, fun f => ⟨eq_stemArc_of_target hM hs, fun hf => hf ▸ rfl⟩⟩
        omega
      · have hv' : v = M.root := by
          have := congrArg Subtype.val hr
          simpa only [removeStem, dite_eq_right hs] using this
        rw [hv', hM.root_indegree] at hv
        omega
    have hs := sum_stemMetric_inheritance (θ := θ) hM hvr
    have hsum := hθ'.2.2.2 ⟨v, hne⟩ (by rw [removeStem_indegree hM hvr]; exact hv)
    rw [← hs]
    refine Eq.trans (Finset.sum_congr rfl fun e _ => ?_) hsum
    congr 1
    exact hinh e
  · have h₁ : (stemMetric M θ).length = θ'.length := funext hlen
    have h₂ : (stemMetric M θ).inheritance = θ'.inheritance := funext hinh
    cases hc : stemMetric M θ with
    | mk l i =>
      cases θ' with
      | mk l' i' =>
        rw [hc] at h₁ h₂
        exact congrArg₂ MetricData.mk h₁ h₂

/-- Step 2 of the map of parameters is onto valid boundary parameters: the length of a composite arc is put on its first arc, and its inheritance on its last. -/
theorem exists_suppress_lift [Fintype E] {M : RootedNetwork V E X} [Fintype {e // ¬ M.IsChainVertex (M.graph.source e)}] (hM : M.IsPhylogenetic)
    {θ' : MetricData {e // ¬ M.IsChainVertex (M.graph.source e)}} (hθ' : (M.suppress hM).IsWeakMetric θ') :
    ∃ θ, M.IsWeakMetric θ ∧ M.suppressMetric θ = θ' := by
  let θ : MetricData E :=
    { length := fun f => if h : ¬ M.IsChainVertex (M.graph.source f) then θ'.length ⟨f, h⟩ else 0
      inheritance := fun f => if M.IsChainVertex (M.graph.target f) then 1 else θ'.inheritance (chainHead hM f) }
  have hinhL : ∀ f, ¬ M.IsChainVertex (M.graph.target f) → θ.inheritance f = θ'.inheritance (chainHead hM f) := fun f hf => ite_eq_right hf
  have hinhC : ∀ f, M.IsChainVertex (M.graph.target f) → θ.inheritance f = 1 := fun f hf => ite_eq_left hf
  have hlast : ∀ e : {e // ¬ M.IsChainVertex (M.graph.source e)}, ¬ M.IsChainVertex (M.graph.target (chainLast hM e.1)) := fun e => by
    rw [target_chainLast]
    exact not_isChainVertex_chainEnd hM _
  have hnorm : M.IsNormalized θ := by
    refine ⟨fun f hf => ?_, fun v hv => ?_⟩
    · by_cases hc : M.IsChainVertex (M.graph.target f)
      · exact hinhC f hc
      · rw [hinhL f hc]
        refine hθ'.2.2.1 _ ((suppress_isTreeArc_iff hM _).mpr ?_)
        rw [chainLast_chainHead hM hc]
        exact hf
    · have hvc : ¬ M.IsChainVertex v := fun hc => by
        have := hc.1
        omega
      have hs := sum_suppress_target hM ⟨v, hvc⟩ θ.inheritance
      rw [← hs]
      refine Eq.trans (Finset.sum_congr rfl fun e _ => ?_) (hθ'.2.2.2 ⟨v, hvc⟩ (by rw [suppress_indegree]; exact hv))
      congr 1
      rw [hinhL _ (hlast e), chainHead_chainLast hM e.2]
  refine ⟨θ, ⟨fun f => ?_, fun f hf => ?_, hnorm⟩, ?_⟩
  · by_cases h : ¬ M.IsChainVertex (M.graph.source f)
    · have : θ.length f = θ'.length ⟨f, h⟩ := dite_eq_left_of_eq_true (eq_true h)
      rw [this]
      exact hθ'.1 _
    · have : θ.length f = 0 := dite_eq_right_of_eq_false (eq_false h)
      rw [this]
  · have hc : ¬ M.IsChainVertex (M.graph.target f) := fun hc => by
      have h1 := hc.1
      have h2 : 2 ≤ M.graph.indegree (M.graph.target f) := hf
      omega
    rw [hinhL f hc]
    refine hθ'.2.1 _ ((suppress_isHybridArc_iff hM _).mpr ?_)
    rw [chainLast_chainHead hM hc]
    exact hf
  · have h₁ : (M.suppressMetric θ).length = θ'.length := by
      funext e
      change ∑ f with M.IsOnChain e.1 f, θ.length f = _
      rw [Finset.sum_eq_single_of_mem e.1 (Finset.mem_filter.2 ⟨Finset.mem_univ _, Or.inl rfl⟩) fun g hg hne => ?_]
      · exact dite_eq_left_of_eq_true (eq_true e.2)
      · rcases (Finset.mem_filter.1 hg).2 with h | ⟨h, -⟩
        · exact absurd h hne
        · exact dite_eq_right_of_eq_false (eq_false (not_not.mpr h))
    have h₂ : (M.suppressMetric θ).inheritance = θ'.inheritance := by
      funext e
      change ∏ f with M.IsOnChain e.1 f, θ.inheritance f = _
      rw [Finset.prod_eq_single_of_mem (chainLast hM e.1) (Finset.mem_filter.2 ⟨Finset.mem_univ _, isOnChain_chainLast hM e.1⟩) fun g hg hne => ?_]
      · rw [hinhL _ (hlast e), chainHead_chainLast hM e.2]
      · rcases (Finset.mem_filter.1 hg).2.eq_chainLast_or hM with h | hc
        · exact absurd h hne
        · exact hinhC g hc
    cases hc : M.suppressMetric θ with
    | mk l i =>
      cases θ' with
      | mk l' i' =>
        rw [hc] at h₁ h₂
        exact congrArg₂ MetricData.mk h₁ h₂

end Lift

section Normalized

variable {V E X : Type*}

/-- **Suppression sends normalized parameters to normalized parameters.** -/
theorem isNormalized_suppressMetric [Fintype E] {M : RootedNetwork V E X} [Fintype {e // ¬ M.IsChainVertex (M.graph.source e)}] (hM : M.IsPhylogenetic)
    {θ : MetricData E} (hθ : M.IsNormalized θ) : (M.suppress hM).IsNormalized (M.suppressMetric θ) := by
  have hinh : ∀ e : {e // ¬ M.IsChainVertex (M.graph.source e)}, (M.suppressMetric θ).inheritance e = θ.inheritance (chainLast hM e.1) := fun e => by
    refine Finset.prod_eq_single_of_mem _ (Finset.mem_filter.2 ⟨Finset.mem_univ _, isOnChain_chainLast hM e.1⟩) fun g hg hne => ?_
    rcases (Finset.mem_filter.1 hg).2.eq_chainLast_or hM with h | hc
    · exact absurd h hne
    · exact hθ.1 g hc.1
  refine ⟨fun e he => ?_, fun v hv => ?_⟩
  · rw [hinh]
    exact hθ.1 _ ((suppress_isTreeArc_iff hM e).1 he)
  · rw [suppress_indegree] at hv
    have hsum := sum_suppress_target hM v θ.inheritance
    rw [hθ.2 v.1 hv] at hsum
    rw [← hsum]
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [hinh]

end Normalized

section SuppressStem

variable {V E X : Type*} [Fintype E] [Nontrivial X] {R : RootedNetwork V E X} [Fintype {e // ¬ R.IsChainVertex (R.graph.source e)}] (hR : R.IsPhylogenetic)

/-- Valid parameters go to valid parameters, through steps 2 and 3. -/
theorem isMetric_suppressStem [Fintype {e // ¬ (HasStem (R.suppress hR) ∧ (R.suppress hR).graph.source e = (R.suppress hR).root)}] {η : MetricData E} (hη : R.IsMetric η) :
    (removeStem (R.suppress hR) (suppress_isPhylogenetic hR)).IsMetric (stemMetric (R.suppress hR) (R.suppressMetric η)) :=
  isMetric_stemMetric (suppress_isPhylogenetic hR) (isMetric_suppressMetric hR hη)

/-- The map of parameters of steps 2 and 3 is onto valid boundary parameters. -/
theorem exists_suppressStem_lift [Fintype {e // ¬ (HasStem (R.suppress hR) ∧ (R.suppress hR).graph.source e = (R.suppress hR).root)}]
    {θ' : MetricData {e // ¬ (HasStem (R.suppress hR) ∧ (R.suppress hR).graph.source e = (R.suppress hR).root)}}
    (hθ' : (removeStem (R.suppress hR) (suppress_isPhylogenetic hR)).IsWeakMetric θ') :
    ∃ η, R.IsWeakMetric η ∧ stemMetric (R.suppress hR) (R.suppressMetric η) = θ' := by
  obtain ⟨θ₂, hθ₂, h₂⟩ := exists_stem_lift (suppress_isPhylogenetic hR) hθ'
  obtain ⟨η, hη, h₁⟩ := exists_suppress_lift hR hθ₂
  exact ⟨η, hη, by rw [h₁, h₂]⟩

variable [Fintype V] [Fintype X] [DecidableEq X] [Fintype {v // ¬ R.IsChainVertex v}]

/-- **Steps 2 and 3 do not change the concordance factors.** -/
theorem nmscCF_suppressStem [Fintype {v // ¬ (HasStem (R.suppress hR) ∧ v = (R.suppress hR).root)}]
    [Fintype {e // ¬ (HasStem (R.suppress hR) ∧ (R.suppress hR).graph.source e = (R.suppress hR).root)}] {η : MetricData E} (hη : R.IsNormalized η) {ρ : ℝ}
    (hρ : 0 ≤ ρ) (s : QuartetTree X) :
    nmscCF (removeStem (R.suppress hR) (suppress_isPhylogenetic hR)) (stemMetric (R.suppress hR) (R.suppressMetric η)) ρ s = nmscCF R η ρ s :=
  (nmscCF_removeStem (suppress_isPhylogenetic hR) (isNormalized_suppressMetric hR hη) hρ s).trans (NMSC.nmscCF_suppress hR hη hρ s)

end SuppressStem

end AllmanEtAl2023
