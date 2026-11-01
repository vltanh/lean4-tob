module

public import AllmanEtAl2023.ContractBlob
public import AllmanEtAl2023.Reduction

/-!
# Allman, Baños, Mitchell, Rhodes 2023: statement (b) in the proof of Theorem 1

If `T_rd(𝒩⁻)` has the unresolved topology, then `CF_abcd` is non-cut, for generic parameters. The proof follows the paper, by induction on the network, on the number of its edges:

* "If there are any 2-blobs on `𝒩⁻`, set all edge lengths in `𝒩⁺` that give rise to them equal to 0, with hybrid parameters arbitrary. Doing so, we have effectively removed these blobs": `exists_isContractible_of_cutDegree_two`, `contracted`, `nmscCF_contracted`, `exists_contracted_lift`.
* "Focus on the lowest hybrid node `w` in this order, and its hybrid edges `k₁`, `k₂`. Consider deleting one of the `kᵢ` ... If the semidirected unrooted network of the resulting network still has a 4-blob, then set `γᵢ = 0` and lengths for the removed edges to be arbitrary": `deleted`, tested with `cutDegree = 4` (`exists_cutDegree_four_iff`), `nmscCF_deleted`, `exists_deleted_lift`, and the inductive hypothesis.
* "If `v` is the lowest hybrid node on `𝒩⁺`, then the subnetwork below `v` must be a tree. But since `𝒩⁻` has no 3-blobs, this tree can only have one leaf, and hence there is only a single edge below `v`": `exists_child_eq_leaf`.
* "Moreover, the semidirected unrooted networks each have exactly two 3-blobs, and possibly 2-blobs": Lemma 1 on `deleted`.
* "For the sake of contradiction, suppose `𝒩₂⁺`'s reduced unrooted tree of blobs also has topology `ab|cd`": `IsLowPair.exists_splitOffAt`.
* "By (a) we have that `𝒩₁⁺` is strictly `(ab|cd)`-cut and `𝒩₂⁺` is strictly `(ac|bd)`-cut for generic parameters. Thus by first choosing the numerical parameters other than `γ₁`, `γ₂` on `𝒩⁺` to yield such generic parameters on the `𝒩ᵢ⁺` ... so that `CF_abcd(𝒩⁺)` is non-cut": `theorem1_a` on `deleted`, `measure_deleted_preimage`, `nmscCF_withPair_mixture`, `exists_mem_Ioo_forall_ne`.

## Notes on the paper

The text here is the PMC manuscript, not the journal's version.

* **The labels of the mixture.** Fig. 5's caption and the figure disagree with `CF = γ₁ CF(𝒩₂⁺) + γ₂ CF(𝒩₁⁺)`, which fits `𝒩ᵢ` removing `hᵢ`. In Lean the two networks are named by the arc deleted, and `θ.withPair k₁ k₂ γ` puts `γ` on `k₁` (`exists_isNonCut_of_deleted`).
* **Implicit in the paper.** The passage from generic parameters of the `𝒩ᵢ⁺` to parameters of `𝒩⁺` (`measure_deleted_preimage`): the preimage of a null set under the map of parameters is null. That a lowest hybrid node exists: a network with none is a tree, and then has a resolved `T` (the last branch of `exists_isNonCut_of_not_isTreelike`). The stem removal in `𝒩ᵢ⁺` (see `AllmanEtAl2023.DeletedNetwork`).
* **"Now `e` must be a cut edge in both `N₁` and `N₂`"** has no reason in the paper: see `IsLowPair.ends_mem_far`.
-/

@[expose] public noncomputable section

open Phylogenetics Phylogenetics.RootedNetwork Phylogenetics.NMSC Finset MeasureTheory
open scoped Classical

namespace AllmanEtAl2023

variable {V E X : Type*}

/-! ### The numerical parameters other than `γ₁`, `γ₂` -/

section Coordinates

variable [Fintype V] [Fintype E] {N : RootedNetwork V E X} {d : V → E} {x : (E → ℝ) × (E → ℝ)}

omit [Fintype V] in
/-- At stochastic coordinates, all hybrid arcs have positive inheritance. -/
theorem coordMetric_inheritance_pos (hx : IsStochasticCoords x) {e : E} (he : N.IsHybridArc e) : 0 < (coordMetric N d x.1 x.2).inheritance e := by
  by_cases hde : e = d (N.graph.target e)
  · rw [coordMetric_inheritance_of_eq he hde, sub_pos]
    have hc : (0 : ℝ) < (Fintype.card E : ℝ) + 1 := by positivity
    calc _ ≤ ∑ _ ∈ univ.filter (fun f => N.graph.target f = N.graph.target e ∧ f ≠ e), ((Fintype.card E : ℝ) + 1)⁻¹ := sum_le_sum fun f _ => (hx.2 f).2.le
      _ ≤ ∑ _ : E, ((Fintype.card E : ℝ) + 1)⁻¹ := sum_le_sum_of_subset_of_nonneg (subset_univ _) fun _ _ _ => by positivity
      _ < 1 := by
          rw [sum_const, nsmul_eq_mul, card_univ, ← div_eq_mul_inv, div_lt_one hc]
          linarith
  · rw [coordMetric_inheritance_of_ne he hde]
    exact (hx.2 e).1

omit [Fintype V] in
/-- The parameters at coordinates are normalized. -/
theorem isNormalized_coordMetric (hd : ∀ v, 2 ≤ N.graph.indegree v → N.graph.target (d v) = v) (ℓ g : E → ℝ) : N.IsNormalized (coordMetric N d ℓ g) :=
  ⟨fun _ he => coordMetric_inheritance_of_isTreeArc he, fun _ hv => sum_coordMetric_inheritance hd hv⟩

end Coordinates

section Preimage

variable [Fintype V] [Fintype E] [Nontrivial X] {N : RootedNetwork V E X} {k k' : E} {d : V → E}

omit [Fintype V] [Nontrivial X] in
/-- The parents of a hybrid node off the one deleted are all kept: a node of `Nᵢ` with two parents is not the child of the deleted arc. -/
theorem target_ne_of_two_le_offNetwork {hroot : N.root ∈ offVertices N {k}} (hpar : ∀ f, N.graph.target f = N.graph.target k → f = k ∨ f = k') {u : offVertices N {k}}
    (hu : 2 ≤ (offNetwork N {k} hroot).graph.indegree u) : u.1 ≠ N.graph.target k := by
  intro h
  obtain ⟨f, g, hf, hg, hne⟩ := (Set.one_lt_ncard_iff (Set.toFinite _)).mp hu
  have hf' : N.graph.target f.1 = N.graph.target k := (congrArg Subtype.val hf).trans h
  have hg' : N.graph.target g.1 = N.graph.target k := (congrArg Subtype.val hg).trans h
  have hfk : f.1 = k' := (hpar _ hf').resolve_left f.2.1
  have hgk : g.1 = k' := (hpar _ hg').resolve_left g.2.1
  exact hne (Subtype.ext (hfk.trans hgk.symm))

omit [Fintype V] in
/-- **"First choosing the numerical parameters other than `γ₁`, `γ₂` on `𝒩⁺` to yield such generic parameters on the `𝒩ᵢ⁺`"**: for parameters at coordinates `x` with the arc `k` deleted, a null set of parameters of `𝒩ᵢ⁺` comes from a null set of
coordinates. The map of coordinates is linear and surjective: a restriction, sums along chains, and a restriction. The paper leaves this implicit. -/
theorem measure_deleted_preimage (hN : IsBinaryNetwork N) (hD : N.IsDeletion {k}) (hk : k ≠ k') (ht : N.graph.target k' = N.graph.target k)
    (hpar : ∀ f, N.graph.target f = N.graph.target k → f = k ∨ f = k') (hd : ∀ v, 2 ≤ N.graph.indegree v → N.graph.target (d v) = v)
    [Fintype {e // ¬ (HasStem (offSuppressed hN hD) ∧ (offSuppressed hN hD).graph.source e = (offSuppressed hN hD).root)}]
    {A : Set (MetricData {e // ¬ (HasStem (offSuppressed hN hD) ∧ (offSuppressed hN hD).graph.source e = (offSuppressed hN hD).root)})} (hA : (deleted hN hD).IsGenericNull A) :
    coordVolume E {x | IsStochasticCoords x ∧ deletedParams hN hD ((coordMetric N d x.1 x.2).withPair k' k 1) ∈ A} = 0 := by
  have hP := hN.isPhylogenetic
  let _ : Fintype (offArcs N {k}) := Fintype.ofFinite _
  let _ : Fintype {e // ¬ (offNet hN hD).IsChainVertex ((offNet hN hD).graph.source e)} := Fintype.ofFinite _
  have hR := offNet_isPhylogenetic hN hD
  have hS := offSuppressed_isPhylogenetic hN hD
  obtain ⟨e₀⟩ := nonempty_arcs_of_isPhylogenetic hS
  obtain ⟨e₁⟩ := nonempty_arcs_of_isPhylogenetic hR
  obtain ⟨e₂⟩ := nonempty_arcs_of_isPhylogenetic (deleted_isPhylogenetic hN hD)
  have hA₁ := isGenericNull_stemMetric hS e₂ hA
  have hA₂ := isGenericNull_suppressMetric hR hA₁
  -- the left-out parents on `Nᵢ`
  let d₁ : offVertices N {k} → offArcs N {k} := fun u => if h : d u.1 ∈ offArcs N {k} then ⟨d u.1, h⟩ else e₁
  have hmem : ∀ u : offVertices N {k}, 2 ≤ (offNet hN hD).graph.indegree u → d u.1 ∈ offArcs N {k} := by
    intro u hu
    have hne := target_ne_of_two_le_offNetwork hpar hu
    have ht' := hd u.1 (hu.trans (offNetwork_indegree_le u))
    refine mem_offArcs_of_target ht' ?_
    intro hdk
    exact hne (ht'.symm.trans (congrArg N.graph.target hdk))
  have hd₁ : ∀ u, 2 ≤ (offNet hN hD).graph.indegree u → (offNet hN hD).graph.target (d₁ u) = u := by
    intro u hu
    simp only [d₁, dite_eq_left_of_eq_true (eq_true (hmem u hu))]
    exact Subtype.ext (hd u.1 (hu.trans (offNetwork_indegree_le u)))
  have hzero := hA₂ d₁ hd₁
  have hval : Function.Injective (Subtype.val : offArcs N {k} → E) := Subtype.val_injective
  have hL := Measure.prod_pi_volume_preimage_eq_zero ((LinearMap.funLeft ℝ ℝ (Subtype.val : offArcs N {k} → E)).prodMap (LinearMap.funLeft ℝ ℝ (Subtype.val : offArcs N {k} → E))) (by
    rw [LinearMap.coe_prodMap]
    exact (LinearMap.funLeft_surjective_of_injective ℝ ℝ _ hval).prodMap (LinearMap.funLeft_surjective_of_injective ℝ ℝ _ hval)) hzero
  refine measure_mono_null ?_ hL
  rintro x ⟨hx, hxA⟩
  -- the parameters at `x`
  set θ₀ := coordMetric N d x.1 x.2 with hθ₀
  have hn₀ : N.IsNormalized θ₀ := isNormalized_coordMetric hd _ _
  have h0 : ∀ f, N.graph.target f = N.graph.target k' → f ≠ k' → f ≠ k → θ₀.inheritance f = 0 := fun f hf h₁ h₂ =>
    absurd ((hpar f (hf.trans ht)).resolve_left h₂) h₁
  have hnorm : N.IsNormalized (θ₀.withPair k' k 1) := isNormalized_withPair hn₀ hk.symm ht.symm h0 1
  have hk0 : (θ₀.withPair k' k 1).inheritance k = 0 := by
    rw [withPair_inheritance_right hk.symm, sub_self]
  have hD0 : ∀ f ∈ ({k} : Set E), (θ₀.withPair k' k 1).inheritance f = 0 := by
    rintro f rfl
    exact hk0
  have hn₁ : (offNet hN hD).IsNormalized (offParams N {k} (θ₀.withPair k' k 1)) := isNormalized_offParams hP hnorm hD0
  have hlen : ∀ e, 0 < (θ₀.withPair k' k 1).length e := fun e => hx.1 e
  have hpos : ∀ e, e ∉ ({k} : Set E) → N.IsHybridArc e → 0 < (θ₀.withPair k' k 1).inheritance e := by
    intro e he hh
    by_cases hek : e = k'
    · subst hek
      rw [withPair_inheritance_left]
      exact one_pos
    · rw [withPair_inheritance_of_ne hek he]
      exact coordMetric_inheritance_pos hx hh
  have hm₁ : (offNet hN hD).IsMetric (offParams N {k} (θ₀.withPair k' k 1)) := by
    refine ⟨fun e _ => hlen e.1, fun e _ => (hlen e.1).le, hn₁.1, fun e he => hpos e.1 e.2.1 ?_, hn₁.2⟩
    exact le_trans he (offNetwork_indegree_le _)
  refine ⟨offParams N {k} (θ₀.withPair k' k 1), ⟨hm₁, isMetric_suppressMetric hR hm₁, hxA⟩, hm₁, ?_, fun e he hne => ?_⟩
  · funext e
    rfl
  · have htu := target_ne_of_two_le_offNetwork hpar (u := (offNet hN hD).graph.target e) he
    have hek : e.1 ≠ k := fun h => e.2.1 h
    have hek' : e.1 ≠ k' := fun h => htu (by
      change N.graph.target e.1 = _
      rw [h, ht])
    have hh : N.IsHybridArc e.1 := le_trans he (offNetwork_indegree_le _)
    have hdne : e.1 ≠ d (N.graph.target e.1) := by
      intro hde
      apply hne
      have hu2 := hmem _ he
      simp only [d₁]
      rw [dite_eq_left_of_eq_true (eq_true hu2)]
      exact Subtype.ext hde
    change (θ₀.withPair k' k 1).inheritance e.1 = x.2 e.1
    rw [withPair_inheritance_of_ne hek' hek, hθ₀, coordMetric_inheritance_of_ne hh hdne]

end Preimage

/-! ### The mixture -/

section Mixture

variable [Fintype V] [Fintype E] [Fintype X] [DecidableEq X] {N : RootedNetwork V E X}

omit [Fintype V] [Fintype E] [Fintype X] [DecidableEq X] in
/-- `γ = 0` on the pair `k₁, k₂` is `γ = 1` on the pair `k₂, k₁`. -/
theorem withPair_zero_eq (θ : MetricData E) {k₁ k₂ : E} (hk : k₁ ≠ k₂) : θ.withPair k₁ k₂ 0 = θ.withPair k₂ k₁ 1 := by
  refine congrArg₂ MetricData.mk rfl (funext fun f => ?_)
  by_cases h₁ : f = k₁
  · subst h₁
    simp [hk]
  · by_cases h₂ : f = k₂
    · subst h₂
      simp [h₁]
    · simp [h₁, h₂]

/-- **`𝒩ᵢ⁺` is strictly cut for generic parameters, in the coordinates of `𝒩⁺`**: (a) on `𝒩ᵢ⁺`, through the map of parameters. -/
theorem measure_not_isStrictlyCutAt_deleted (hN : IsBinaryNetwork N) (hcard : Fintype.card X = 4) {k k' : E} (hD : N.IsDeletion {k}) (hk : k ≠ k') (ht : N.graph.target k' = N.graph.target k)
    (hpar : ∀ f, N.graph.target f = N.graph.target k → f = k ∨ f = k') {d : V → E} (hd : ∀ v, 2 ≤ N.graph.indegree v → N.graph.target (d v) = v) {s : QuartetTree X} {e : E}
    (hs : N.SplitOffAt {k} e s) :
    coordVolume E {x | IsStochasticCoords x ∧ ¬ IsStrictlyCutAt (nmscCF N ((coordMetric N d x.1 x.2).withPair k' k 1) 0) s} = 0 := by
  have hX := nontrivial_of_card_four hcard
  let _ : Fintype {v // ¬ (HasStem (offSuppressed hN hD) ∧ v = (offSuppressed hN hD).root)} := Fintype.ofFinite _
  let _ : Fintype {e // ¬ (HasStem (offSuppressed hN hD) ∧ (offSuppressed hN hD).graph.source e = (offSuppressed hN hD).root)} := Fintype.ofFinite _
  obtain ⟨a, b, c, d', h, rfl⟩ := TreeMetric.exists_eq_quartetTree s
  have hT := (deleted_hasQuartetTopology_iff hN hD hcard h).mpr ⟨e, hs⟩
  have hgen := theorem1_a (deleted_isBinaryNetwork hN hD) hcard
  refine measure_mono_null ?_ (measure_deleted_preimage hN hD hk ht hpar hd hgen)
  rintro x ⟨hx, hnot⟩
  refine ⟨hx, ?_, fun hP => hnot ?_⟩
  · -- the parameters are valid
    have hn₀ : N.IsNormalized (coordMetric N d x.1 x.2) := isNormalized_coordMetric hd _ _
    have h0 : ∀ f, N.graph.target f = N.graph.target k' → f ≠ k' → f ≠ k → (coordMetric N d x.1 x.2).inheritance f = 0 := fun f hf h₁ h₂ =>
      absurd ((hpar f (hf.trans ht)).resolve_left h₂) h₁
    refine isMetric_deletedParams hN hD (fun e => hx.1 e) (fun e he hh => ?_) (isNormalized_withPair hn₀ hk.symm ht.symm h0 1) ?_
    · by_cases hek : e = k'
      · subst hek
        rw [withPair_inheritance_left]
        exact one_pos
      · rw [withPair_inheritance_of_ne hek he]
        exact coordMetric_inheritance_pos hx hh
    · rintro f rfl
      rw [withPair_inheritance_right hk.symm, sub_self]
  · -- so `CF` of `𝒩ᵢ⁺` is strictly cut
    have hn₀ : N.IsNormalized (coordMetric N d x.1 x.2) := isNormalized_coordMetric hd _ _
    have h0 : ∀ f, N.graph.target f = N.graph.target k' → f ≠ k' → f ≠ k → (coordMetric N d x.1 x.2).inheritance f = 0 := fun f hf h₁ h₂ =>
      absurd ((hpar f (hf.trans ht)).resolve_left h₂) h₁
    have hcf : ∀ r, nmscCF (deleted hN hD) (deletedParams hN hD ((coordMetric N d x.1 x.2).withPair k' k 1)) 0 r = nmscCF N ((coordMetric N d x.1 x.2).withPair k' k 1) 0 r := fun r =>
      nmscCF_deleted hN hD (isNormalized_withPair hn₀ hk.symm ht.symm h0 1) (by
        rintro f rfl
        rw [withPair_inheritance_right hk.symm, sub_self]) le_rfl r
    have hS := hP a b c d' h hT
    unfold cfTriple quartetCF at hS
    simp only [hcf] at hS
    exact (isStrictlyCutAtFirst_iff (nmscCF N ((coordMetric N d x.1 x.2).withPair k' k 1) 0) h).mp hS

/-- **The paper's choice of parameters in (b)**: "since `a` is the only taxon below the hybrid node `v`", the `CF` is a mixture of the `CF`s of the two `𝒩ᵢ⁺`. "By (a) we have that `𝒩₁⁺` is strictly `(ab|cd)`-cut and `𝒩₂⁺` is strictly `(ac|bd)`-cut for generic parameters. Thus by first choosing the
numerical parameters other than `γ₁`, `γ₂` on `𝒩⁺` to yield such generic parameters on the `𝒩ᵢ⁺`, we may then pick values of `γ₁`, `γ₂` so that `CF_abcd(𝒩⁺)` is non-cut." -/
theorem exists_isNonCut_of_deleted (hN : IsBinaryNetwork N) (hcard : Fintype.card X = 4) {k₁ k₂ : E} (hk : k₁ ≠ k₂) (ht : N.graph.target k₁ = N.graph.target k₂)
    (hpar : ∀ f, N.graph.target f = N.graph.target k₁ → f = k₁ ∨ f = k₂) {a : X} (honly : ∀ x, x ≠ a → ¬ N.graph.Reaches (N.graph.target k₁) (N.leaf x)) {s₁ s₂ : QuartetTree X}
    (hss : s₁ ≠ s₂) {e₁ e₂ : E} (h₁ : N.SplitOffAt {k₂} e₁ s₁) (h₂ : N.SplitOffAt {k₁} e₂ s₂) :
    ∃ θ, N.IsWeakMetric θ ∧ IsNonCut (nmscCF N θ 0) Finset.univ := by
  have hP := hN.isPhylogenetic
  have hD₁ : N.IsDeletion {k₂} := isDeletion_singleton hP hk.symm ht.symm
  have hD₂ : N.IsDeletion {k₁} := isDeletion_singleton hP hk ht
  have ht' : N.graph.target k₂ = N.graph.target k₁ := ht.symm
  have hpar₂ : ∀ f, N.graph.target f = N.graph.target k₂ → f = k₂ ∨ f = k₁ := fun f hf => (hpar f (hf.trans ht')).symm
  -- the left-out parents
  obtain ⟨d, hd⟩ := exists_leftOutParent (N := N) k₁
  -- generic parameters on the two networks
  have hnull₁ := measure_not_isStrictlyCutAt_deleted hN hcard hD₁ hk.symm ht hpar₂ hd h₁
  have hnull₂ := measure_not_isStrictlyCutAt_deleted hN hcard hD₂ hk ht' hpar hd h₂
  obtain ⟨x, hx, hxn⟩ := exists_isStochasticCoords_notMem (measure_union_null hnull₁ hnull₂)
  set θ₀ := coordMetric N d x.1 x.2 with hθ₀
  have hn₀ : N.IsNormalized θ₀ := isNormalized_coordMetric hd _ _
  have hw₀ : N.IsWeakMetric θ₀ := ⟨fun e => (hx.1 e).le, fun e he => (coordMetric_inheritance_pos hx he).le, hn₀⟩
  have h0 : ∀ f, N.graph.target f = N.graph.target k₁ → f ≠ k₁ → f ≠ k₂ → θ₀.inheritance f = 0 := fun f hf h₁ h₂ =>
    absurd ((hpar f hf).resolve_left h₁) h₂
  -- strictly cut at both ends
  have hc₁ : IsStrictlyCutAt (nmscCF N (θ₀.withPair k₁ k₂ 1) 0) s₁ := by
    by_contra hn
    exact hxn (Or.inl ⟨hx, hn⟩)
  have hc₂ : IsStrictlyCutAt (nmscCF N (θ₀.withPair k₁ k₂ 0) 0) s₂ := by
    rw [withPair_zero_eq θ₀ hk]
    by_contra hn
    exact hxn (Or.inr ⟨hx, hn⟩)
  have hq : (Finset.univ : Finset X).card = 4 := by rw [Finset.card_univ, hcard]
  have hs₁ : s₁ ∈ treesOn (Finset.univ : Finset X) := mem_treesOn.2 (Finset.eq_univ_of_card _ (s₁.card_taxa.trans hcard.symm))
  have hs₂ : s₂ ∈ treesOn (Finset.univ : Finset X) := mem_treesOn.2 (Finset.eq_univ_of_card _ (s₂.card_taxa.trans hcard.symm))
  have htaxa : ∀ t ∈ treesOn (Finset.univ : Finset X), ∀ s ∈ treesOn (Finset.univ : Finset X), t ≠ s → t ∈ s.alternatives := fun t ht s hs hne =>
    QuartetTree.mem_alternatives.2 ⟨(mem_treesOn.1 ht).trans (mem_treesOn.1 hs).symm, hne⟩
  -- two entries differ at one of the two ends
  have hsep : ∀ r ∈ treesOn (Finset.univ : Finset X), ∀ r' ∈ treesOn (Finset.univ : Finset X), r ≠ r' →
      nmscCF N (θ₀.withPair k₁ k₂ 1) 0 r ≠ nmscCF N (θ₀.withPair k₁ k₂ 1) 0 r' ∨ nmscCF N (θ₀.withPair k₁ k₂ 0) 0 r ≠ nmscCF N (θ₀.withPair k₁ k₂ 0) 0 r' := by
    intro r hr r' hr' hne
    by_cases h₁ : r = s₁
    · subst h₁
      exact Or.inl (hc₁.1 r' (htaxa r' hr' r hr hne.symm)).symm
    by_cases h₂ : r' = s₁
    · subst h₂
      exact Or.inl (hc₁.1 r (htaxa r hr r' hr' hne))
    by_cases h₃ : r = s₂
    · subst h₃
      exact Or.inr (hc₂.1 r' (htaxa r' hr' r hr hne.symm)).symm
    by_cases h₄ : r' = s₂
    · subst h₄
      exact Or.inr (hc₂.1 r (htaxa r hr r' hr' hne))
    · exact absurd (eq_of_mem_treesOn_of_ne hq hs₁ hs₂ hss hr hr' h₁ h₃ h₂ h₄) hne
  -- the choice of `γ`
  obtain ⟨γ, hγ, hne⟩ := exists_mem_Ioo_forall_ne (treesOn (Finset.univ : Finset X)) (fun r => nmscCF N (θ₀.withPair k₁ k₂ 1) 0 r) (fun r => nmscCF N (θ₀.withPair k₁ k₂ 0) 0 r) hsep
  have hmix : ∀ t : QuartetTree X, nmscCF N (θ₀.withPair k₁ k₂ γ) 0 t = γ * nmscCF N (θ₀.withPair k₁ k₂ 1) 0 t + (1 - γ) * nmscCF N (θ₀.withPair k₁ k₂ 0) 0 t := fun t =>
    nmscCF_withPair_mixture hP hn₀ hk ht' hpar t a (fun y _ hya => honly y hya) γ
  refine ⟨θ₀.withPair k₁ k₂ γ, isWeakMetric_withPair hw₀ hk ht' h0 ⟨hγ.1.le, hγ.2.le⟩, fun r hr r' hr' hrr => ?_⟩
  rw [hmix r, hmix r']
  exact hne r hr r' hr' hrr

end Mixture

/-! ### Below the lowest hybrid node -/

section SingleEdge

variable {N : RootedNetwork V E X}

/-- **The parent of a cherry is a 3-blob of `𝒩⁻`**, on at least three taxa: its three edges are cut edges, so it is a blob by itself. If its edge up is the edge of the root of `𝒩⊕` that `𝒩⁻` merges into the other, then that other edge is the third edge in `𝒩⁻`. -/
theorem exists_cutDegree_three_of_cherry (hN : IsBinaryNetwork N) (hX : Nontrivial X) {m : V} {g₁ g₂ f : E} {a b c : X} (hf : N.graph.target f = m) (hfu : ∀ k, N.graph.target k = m → k = f)
    (hg₁ : N.graph.source g₁ = m) (hg₂ : N.graph.source g₂ = m) (hgne : g₁ ≠ g₂) (hgu : ∀ k, N.graph.source k = m → k = g₁ ∨ k = g₂) (ha : N.graph.target g₁ = N.leaf a) (hb : N.graph.target g₂ = N.leaf b)
    (hca : c ≠ a) (hcb : c ≠ b) :
    ∃ β, (∀ x, blobOf (semidirected hN hX).graph ((semidirected hN hX).leaf x) ≠ β) ∧ cutDegree (semidirected hN hX).graph β = 3 := by
  have hP := hN.isPhylogenetic
  have : Finite V := hP.finite_vertices
  have : Finite E := hP.finite_arcs
  have hnosrc : ∀ x (k : E), N.graph.source k ≠ N.leaf x := fun x => (N.graph.outdegree_eq_zero_iff _).mp ((hP.leaves _).mpr ⟨x, rfl⟩)
  have hmleaf : ∀ x, m ≠ N.leaf x := fun x h => hnosrc x g₁ (hg₁.trans h)
  have hleafu : ∀ x (k k' : E), N.graph.target k = N.leaf x → N.graph.target k' = N.leaf x → k = k' := fun x k k' hk hk' => by
    obtain ⟨g, hg⟩ := (N.graph.indegree_eq_one_iff _).mp (hP.leaf_indegree x)
    exact ((hg k).mp hk).trans ((hg k').mp hk').symm
  -- the third taxon is not below `m`, so `m` is strictly below the LSA
  have hnrc : ¬ N.graph.Reaches m (N.leaf c) := by
    intro h
    rcases Relation.ReflTransGen.cases_head h with h | ⟨d, ⟨k, hk, rfl⟩, hd⟩
    · exact hmleaf c h
    · rcases hgu k hk with rfl | rfl
      · rw [ha] at hd
        exact hca (eq_of_leaf_reachesOff_leaf hP (reachesOff_empty_iff.mpr hd))
      · rw [hb] at hd
        exact hcb (eq_of_leaf_reachesOff_leaf hP (reachesOff_empty_iff.mpr hd))
  have hnrl : ¬ N.graph.Reaches m (lsaNode hN hX) := fun h => hnrc (h.trans ((lsa_spec hP Set.univ Set.univ_nonempty).1.reaches_leaf hP (Set.mem_univ c)))
  have hbelow : m ∈ N.belowVertices (lsaNode hN hX) Set.univ := (mem_belowVertices_univ_iff hN hX m).mpr fun h => hnrl h.1
  have hml : m ≠ lsaNode hN hX := fun h => hnrl (h ▸ .refl)
  have hsv : ∀ {x y : SemiV hN hX}, x.1.1 = y.1.1 → x = y := fun h => Subtype.ext (Subtype.ext h)
  have hse : ∀ {k k' : SemiE hN hX}, k.1.1 = k'.1.1 → k = k' := fun h => Subtype.ext (Subtype.ext h)
  obtain ⟨wm, hwm⟩ : ∃ w : SemiV hN hX, w.1.1 = m := ⟨⟨⟨m, hbelow⟩, fun h => hml (congrArg Subtype.val h)⟩, rfl⟩
  obtain ⟨wa, hwa⟩ : ∃ w : SemiV hN hX, w.1.1 = N.leaf a := ⟨(semidirected hN hX).leaf a, rfl⟩
  obtain ⟨wb, hwb⟩ : ∃ w : SemiV hN hX, w.1.1 = N.leaf b := ⟨(semidirected hN hX).leaf b, rfl⟩
  have hma : wm ≠ wa := fun h => hmleaf a (hwm.symm.trans ((congrArg (fun z : SemiV hN hX => z.1.1) h).trans hwa))
  have hmb : wm ≠ wb := fun h => hmleaf b (hwm.symm.trans ((congrArg (fun z : SemiV hN hX => z.1.1) h).trans hwb))
  have htv : ∀ k : SemiE hN hX, ((semidirected hN hX).graph.target k).1.1 = N.graph.target k.1.1 := fun _ => rfl
  have hsrc₀ : (rootTreeArc hN hX).1 ≠ g₁ ∧ (rootTreeArc hN hX).1 ≠ g₂ :=
    ⟨fun h => hml (hg₁.symm.trans (h ▸ source_rootTreeArc')), fun h => hml (hg₂.symm.trans (h ▸ source_rootTreeArc'))⟩
  obtain ⟨F₁, rfl⟩ := exists_semiArc (e := g₁) (hg₁ ▸ hbelow.1) hsrc₀.1.symm
  obtain ⟨F₂, rfl⟩ := exists_semiArc (e := g₂) (hg₂ ▸ hbelow.1) hsrc₀.2.symm
  have h1s : (semidirected hN hX).graph.source F₁ = wm := hsv ((semi_source_val_of_ne F₁ (hg₁.trans_ne hml)).trans (hg₁.trans hwm.symm))
  have h2s : (semidirected hN hX).graph.source F₂ = wm := hsv ((semi_source_val_of_ne F₂ (hg₂.trans_ne hml)).trans (hg₂.trans hwm.symm))
  have h1t : (semidirected hN hX).graph.target F₁ = wa := hsv (ha.trans hwa.symm)
  have h2t : (semidirected hN hX).graph.target F₂ = wb := hsv (hb.trans hwb.symm)
  have h12 : F₁ ≠ F₂ := fun h => hgne (congrArg (fun z : SemiE hN hX => z.1.1) h)
  -- the end of an arc of `𝒩⁻` at a node other than `topNode` is its end in `𝒩⁺`
  have hsn : ∀ (k : SemiE hN hX) (w : SemiV hN hX), (semidirected hN hX).graph.source k = w → w ≠ topNode hN hX → N.graph.source k.1.1 = w.1.1 := fun k w hk hw => by
    by_cases hkl : N.graph.source k.1.1 = lsaNode hN hX
    · exact absurd (hk.symm.trans (semi_source_of_eq k hkl)) hw
    · exact (semi_source_val_of_ne k hkl).symm.trans (congrArg (fun z : SemiV hN hX => z.1.1) hk)
  have htopa : wa ≠ topNode hN hX := fun h => by
    have ht₀ : N.graph.target (rootTreeArc hN hX).1 = N.leaf a := (congrArg (fun z : SemiV hN hX => z.1.1) h).symm.trans hwa
    exact hsrc₀.1 (hleafu a _ _ ht₀ ha)
  have htopb : wb ≠ topNode hN hX := fun h => by
    have ht₀ : N.graph.target (rootTreeArc hN hX).1 = N.leaf b := (congrArg (fun z : SemiV hN hX => z.1.1) h).symm.trans hwb
    exact hsrc₀.2 (hleafu b _ _ ht₀ hb)
  -- the edges at the taxa
  have hat₁ : ∀ k : SemiE hN hX, (semidirected hN hX).graph.source k = wa ∨ (semidirected hN hX).graph.target k = wa → k = F₁ := by
    rintro k (h | h)
    · exact absurd ((hsn k wa h htopa).trans hwa) (hnosrc a _)
    · exact hse (hleafu a _ _ ((htv k).symm.trans ((congrArg (fun z : SemiV hN hX => z.1.1) h).trans hwa)) ha)
  have hat₂ : ∀ k : SemiE hN hX, (semidirected hN hX).graph.source k = wb ∨ (semidirected hN hX).graph.target k = wb → k = F₂ := by
    rintro k (h | h)
    · exact absurd ((hsn k wb h htopb).trans hwb) (hnosrc b _)
    · exact hse (hleafu b _ _ ((htv k).symm.trans ((congrArg (fun z : SemiV hN hX => z.1.1) h).trans hwb)) hb)
  have hbr₁ : (semidirected hN hX).graph.underlying.IsBridge F₁ := by
    refine ((semidirected hN hX).graph.isBridge_iff _).mpr ⟨{wa}, fun k => ⟨?_, ?_⟩⟩
    · rintro (⟨h, -⟩ | ⟨h, -⟩)
      · exact hat₁ k (Or.inl h)
      · exact hat₁ k (Or.inr h)
    · rintro rfl
      exact Or.inr ⟨h1t, fun h => hma (h1s.symm.trans h)⟩
  have hbr₂ : (semidirected hN hX).graph.underlying.IsBridge F₂ := by
    refine ((semidirected hN hX).graph.isBridge_iff _).mpr ⟨{wb}, fun k => ⟨?_, ?_⟩⟩
    · rintro (⟨h, -⟩ | ⟨h, -⟩)
      · exact hat₂ k (Or.inl h)
      · exact hat₂ k (Or.inr h)
    · rintro rfl
      exact Or.inr ⟨h2t, fun h => hmb (h2s.symm.trans h)⟩
  -- the third edge at `m`
  obtain ⟨F₃, hat, hend, hS₃, h31, h32⟩ : ∃ F₃ : SemiE hN hX, (∀ k : SemiE hN hX, (semidirected hN hX).graph.source k = wm ∨ (semidirected hN hX).graph.target k = wm → k = F₃ ∨ k = F₁ ∨ k = F₂) ∧
      (((semidirected hN hX).graph.source F₃ = wm ∧ (semidirected hN hX).graph.target F₃ ≠ wm) ∨ ((semidirected hN hX).graph.target F₃ = wm ∧ (semidirected hN hX).graph.source F₃ ≠ wm)) ∧
      (semidirected hN hX).graph.Crosses F₃ {w | w = wm ∨ w = wa ∨ w = wb} ∧ F₃ ≠ F₁ ∧ F₃ ≠ F₂ := by
    by_cases hfe : f = (rootTreeArc hN hX).1
    · -- the edge up is the merged one
      have htop : wm = topNode hN hX := hsv (hwm.trans (hf.symm.trans (congrArg _ hfe)))
      obtain ⟨e₁, hne₁, hroot⟩ := exists_other_root_arc (lsaPlus_outdegree_root hN hX) (rootTreeArc_spec hN hX).1
      have hs₁ : N.graph.source e₁.1 = lsaNode hN hX := congrArg Subtype.val ((hroot e₁).mpr (Or.inr rfl))
      let F₃ : SemiE hN hX := ⟨e₁, hne₁⟩
      have h3s : (semidirected hN hX).graph.source F₃ = wm := (semi_source_of_eq F₃ hs₁).trans htop.symm
      have ht₃m : (semidirected hN hX).graph.target F₃ ≠ wm := fun h => by
        have ht : N.graph.target e₁.1 = m := (congrArg (fun z : SemiV hN hX => z.1.1) h).trans hwm
        exact hne₁ (Subtype.ext ((hfu _ ht).trans hfe))
      have h31 : F₃ ≠ F₁ := fun h => hml (hg₁.symm.trans ((congrArg (fun z : SemiE hN hX => N.graph.source z.1.1) h).symm.trans hs₁))
      have h32 : F₃ ≠ F₂ := fun h => hml (hg₂.symm.trans ((congrArg (fun z : SemiE hN hX => N.graph.source z.1.1) h).symm.trans hs₁))
      refine ⟨F₃, ?_, Or.inl ⟨h3s, ht₃m⟩, Or.inl ⟨Or.inl h3s, ?_⟩, h31, h32⟩
      · rintro k (h | h)
        · by_cases hkl : N.graph.source k.1.1 = lsaNode hN hX
          · rcases (hroot k.1).mp (Subtype.ext hkl) with h₀ | h₁
            · exact absurd h₀ k.2
            · exact Or.inl (Subtype.ext h₁)
          · have := (semi_source_val_of_ne k hkl).symm.trans ((congrArg (fun z : SemiV hN hX => z.1.1) h).trans hwm)
            rcases hgu _ this with h' | h'
            · exact Or.inr (Or.inl (Subtype.ext (Subtype.ext h')))
            · exact Or.inr (Or.inr (Subtype.ext (Subtype.ext h')))
        · have ht : N.graph.target k.1.1 = m := (congrArg (fun z : SemiV hN hX => z.1.1) h).trans hwm
          exact absurd (Subtype.ext ((hfu _ ht).trans hfe)) k.2
      · rintro (h | h | h)
        · exact ht₃m h
        · exact h31 (hat₁ F₃ (Or.inr h))
        · exact h32 (hat₂ F₃ (Or.inr h))
    · -- the edge up is an edge of `𝒩⁻`
      have htop : wm ≠ topNode hN hX := fun h => hfe ((hfu _ ((congrArg (fun z : SemiV hN hX => z.1.1) h).symm.trans hwm)).symm)
      have hlf : N.graph.Reaches (lsaNode hN hX) (N.graph.target f) := hf ▸ hbelow.1
      obtain ⟨F₃, rfl⟩ := exists_semiArc (reaches_source_of_target hlf (hf.trans_ne hml)) hfe
      have h3t : (semidirected hN hX).graph.target F₃ = wm := hsv (hf.trans hwm.symm)
      have h3sm : (semidirected hN hX).graph.source F₃ ≠ wm := fun h => source_ne_target hP F₃.1.1 ((hsn F₃ wm h htop).trans (hwm.trans hf.symm))
      have h31 : F₃ ≠ F₁ := fun h => hmleaf a (hf.symm.trans ((congrArg (fun z : SemiE hN hX => N.graph.target z.1.1) h).trans ha))
      have h32 : F₃ ≠ F₂ := fun h => hmleaf b (hf.symm.trans ((congrArg (fun z : SemiE hN hX => N.graph.target z.1.1) h).trans hb))
      refine ⟨F₃, ?_, Or.inr ⟨h3t, h3sm⟩, Or.inr ⟨Or.inl h3t, ?_⟩, h31, h32⟩
      · rintro k (h | h)
        · rcases hgu _ ((hsn k wm h htop).trans hwm) with h' | h'
          · exact Or.inr (Or.inl (hse h'))
          · exact Or.inr (Or.inr (hse h'))
        · exact Or.inl (hse (hfu _ ((congrArg (fun z : SemiV hN hX => z.1.1) h).trans hwm)))
      · rintro (h | h | h)
        · exact h3sm h
        · exact h31 (hat₁ F₃ (Or.inl h))
        · exact h32 (hat₂ F₃ (Or.inl h))
  have hbr₃ : (semidirected hN hX).graph.underlying.IsBridge F₃ := by
    refine ((semidirected hN hX).graph.isBridge_iff _).mpr ⟨{w | w = wm ∨ w = wa ∨ w = wb}, fun k => ⟨fun hk => ?_, fun h => h ▸ hS₃⟩⟩
    have hnc₁ : ¬ (semidirected hN hX).graph.Crosses F₁ {w | w = wm ∨ w = wa ∨ w = wb} := by
      rintro (⟨-, h⟩ | ⟨-, h⟩)
      · exact h (Or.inr (Or.inl h1t))
      · exact h (Or.inl h1s)
    have hnc₂ : ¬ (semidirected hN hX).graph.Crosses F₂ {w | w = wm ∨ w = wa ∨ w = wb} := by
      rintro (⟨-, h⟩ | ⟨-, h⟩)
      · exact h (Or.inr (Or.inr h2t))
      · exact h (Or.inl h2s)
    have hend' : (semidirected hN hX).graph.source k = wm ∨ (semidirected hN hX).graph.target k = wm ∨ k = F₁ ∨ k = F₂ := by
      rcases hk with ⟨h, -⟩ | ⟨h, -⟩
      · rcases h with h | h | h
        · exact Or.inl h
        · exact Or.inr (Or.inr (Or.inl (hat₁ k (Or.inl h))))
        · exact Or.inr (Or.inr (Or.inr (hat₂ k (Or.inl h))))
      · rcases h with h | h | h
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr (Or.inl (hat₁ k (Or.inr h))))
        · exact Or.inr (Or.inr (Or.inr (hat₂ k (Or.inr h))))
    have hthree : k = F₃ ∨ k = F₁ ∨ k = F₂ := by
      rcases hend' with h | h | h
      · exact hat k (Or.inl h)
      · exact hat k (Or.inr h)
      · exact Or.inr h
    rcases hthree with h | h | h
    · exact h
    · exact absurd (h ▸ hk) hnc₁
    · exact absurd (h ▸ hk) hnc₂
  -- so `m` is a blob by itself
  have hbridge : ∀ k : SemiE hN hX, (semidirected hN hX).graph.source k = wm ∨ (semidirected hN hX).graph.target k = wm → (semidirected hN hX).graph.underlying.IsBridge k := fun k hk => by
    rcases hat k hk with rfl | rfl | rfl
    · exact hbr₃
    · exact hbr₁
    · exact hbr₂
  have hwalk : ∀ x, (semidirected hN hX).graph.Walks {e | ¬ (semidirected hN hX).graph.underlying.IsBridge e} wm x → x = wm := by
    intro x hw
    induction hw with
    | refl => rfl
    | tail _ hab ih =>
      obtain ⟨k, hk, hl⟩ := hab
      rcases hl with ⟨h, -⟩ | ⟨-, h⟩
      · exact absurd (hbridge k (Or.inl (h.trans ih))) hk
      · exact absurd (hbridge k (Or.inr (h.trans ih))) hk
  have hblob : ∀ x, blobOf (semidirected hN hX).graph x = blobOf (semidirected hN hX).graph wm → x = wm := fun x hx => hwalk x (Quotient.exact hx.symm)
  refine ⟨blobOf (semidirected hN hX).graph wm, fun x hx => hmleaf x (hwm.symm.trans (congrArg (fun z : SemiV hN hX => z.1.1) (hblob _ hx)).symm), ?_⟩
  have hne : ∀ {w : SemiV hN hX}, w ≠ wm → blobOf (semidirected hN hX).graph w ≠ blobOf (semidirected hN hX).graph wm := fun hw h => hw (hblob _ h)
  refine Set.ncard_eq_three.mpr ⟨F₃, F₁, F₂, h31, h32, h12, Set.ext fun k => ⟨fun hk => ?_, ?_⟩⟩
  · rcases mem_incidentCutEdges_iff.mp hk with ⟨h, -⟩ | ⟨h, -⟩
    · simpa using hat k (Or.inl (hblob _ h))
    · simpa using hat k (Or.inr (hblob _ h))
  · rintro (rfl | rfl | rfl)
    · refine mem_incidentCutEdges_iff.mpr ?_
      rcases hend with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
      · exact Or.inl ⟨congrArg _ h₁, hne h₂⟩
      · exact Or.inr ⟨congrArg _ h₁, hne h₂⟩
    · exact mem_incidentCutEdges_iff.mpr (Or.inl ⟨congrArg _ h1s, by rw [h1t]; exact hne hma.symm⟩)
    · exact mem_incidentCutEdges_iff.mpr (Or.inl ⟨congrArg _ h2s, by rw [h2t]; exact hne hmb.symm⟩)

variable [Fintype X] [DecidableEq X]

/-- **"If `v` is the lowest hybrid node on `𝒩⁺`, then the subnetwork below `v` must be a tree. But since `𝒩⁻` has no 3-blobs, this tree can only have one leaf, and hence there is only a single edge below `v`."**

If the child of `v` is not a taxon, a lowest node below `v` that is not a taxon has one edge up, as `v` is the lowest hybrid node, and two taxa as children. It is the parent of a cherry: a 3-blob of `𝒩⁻` (`exists_cutDegree_three_of_cherry`). -/
theorem exists_child_eq_leaf (hN : IsBinaryNetwork N) (hcard : Fintype.card X = 4)
    (hno3 : ∀ β, (∀ x, blobOf (semidirected hN (nontrivial_of_card_four hcard)).graph ((semidirected hN (nontrivial_of_card_four hcard)).leaf x) ≠ β) → cutDegree (semidirected hN (nontrivial_of_card_four hcard)).graph β ≠ 3)
    {v : V} (h2 : 2 ≤ N.graph.indegree v)
    (hlow : ∀ w, (∃ k₁ k₂, k₁ ≠ k₂ ∧ N.graph.target k₁ = w ∧ N.graph.target k₂ = w) → N.graph.Reaches v w → w = v) :
    ∃ (g : E) (a : X), N.graph.source g = v ∧ N.graph.target g = N.leaf a ∧ ∀ f, N.graph.source f = v → f = g := by
  have hP := hN.isPhylogenetic
  have : Finite V := hP.finite_vertices
  have : Finite E := hP.finite_arcs
  have hdeg := indegree_eq_two_of_degree_le_three hP h2 (degree_le_three_of_isBinary hP hN.isBinary v)
  obtain ⟨g, hg⟩ := (N.graph.outdegree_eq_one_iff v).mp hdeg.2
  have hgs : N.graph.source g = v := (hg g).mpr rfl
  by_cases hleaf : ∃ a, N.graph.target g = N.leaf a
  · obtain ⟨a, ha⟩ := hleaf
    exact ⟨g, a, hgs, ha, fun f hf => (hg f).mp hf⟩
  exfalso
  -- a lowest node below `v` that is not a taxon
  have : IsTrans V (Function.swap (Relation.TransGen N.graph.Adj)) := ⟨fun _ _ _ h h' => h'.trans h⟩
  have : Std.Irrefl (Function.swap (Relation.TransGen N.graph.Adj)) := ⟨hP.acyclic⟩
  have hwf : WellFounded (Function.swap (Relation.TransGen N.graph.Adj)) := Finite.wellFounded_of_trans_of_irrefl _
  have hmemT : N.graph.target g ∈ {u | Relation.TransGen N.graph.Adj v u ∧ ∀ x, u ≠ N.leaf x} :=
    ⟨Relation.TransGen.single ⟨g, hgs, rfl⟩, fun x hx => hleaf ⟨x, hx⟩⟩
  obtain ⟨m, ⟨hvm, hml⟩, hmin⟩ := hwf.has_min _ ⟨_, hmemT⟩
  have hmr : m ≠ N.root := by
    obtain ⟨c, -, k, -, hk⟩ := Relation.TransGen.tail'_iff.mp hvm
    exact fun h => target_ne_root hP k (hk.trans h)
  have hmv : m ≠ v := fun h => hP.acyclic v (h ▸ hvm)
  have hin : N.graph.indegree m = 1 := by
    by_contra hne
    have hge := hP.nonroot_indegree _ hmr
    have h22 : 2 ≤ N.graph.indegree m := by omega
    obtain ⟨f₁, f₂, hf₁, hf₂, hne'⟩ := (Set.one_lt_ncard_iff (Set.toFinite _)).mp h22
    exact hmv (hlow m ⟨f₁, f₂, hne', hf₁, hf₂⟩ hvm.to_reflTransGen)
  have h0 : N.graph.outdegree m ≠ 0 := fun h => by
    obtain ⟨x, hx⟩ := (hP.leaves _).mp h
    exact hml x hx.symm
  have h3 := hN.isBinary.2 _ hmr h0
  have hout2 : N.graph.outdegree m = 2 := by omega
  obtain ⟨g₁, g₂, hne, hset⟩ := Set.ncard_eq_two.mp hout2
  have hmemset : ∀ k, N.graph.source k = m ↔ k = g₁ ∨ k = g₂ := fun k => by
    have := Set.ext_iff.mp hset k
    simpa using this
  have hg₁ : N.graph.source g₁ = m := (hmemset g₁).mpr (Or.inl rfl)
  have hg₂ : N.graph.source g₂ = m := (hmemset g₂).mpr (Or.inr rfl)
  -- its children are taxa
  have hchild : ∀ k, N.graph.source k = m → ∃ a, N.graph.target k = N.leaf a := fun k hk => by
    by_contra hno
    push Not at hno
    exact hmin _ ⟨hvm.tail ⟨k, hk, rfl⟩, hno⟩ (Relation.TransGen.single ⟨k, hk, rfl⟩)
  obtain ⟨a, ha⟩ := hchild g₁ hg₁
  obtain ⟨b, hb⟩ := hchild g₂ hg₂
  obtain ⟨f, hf⟩ := (N.graph.indegree_eq_one_iff _).mp hin
  obtain ⟨c, hc⟩ : ∃ c, c ∉ ({a, b} : Finset X) := by
    by_contra hall
    push Not at hall
    have h4 : (Finset.univ : Finset X).card ≤ ({a, b} : Finset X).card := Finset.card_le_card fun x _ => hall x
    have h5 : ({a, b} : Finset X).card ≤ 2 := Finset.card_le_two
    rw [Finset.card_univ, hcard] at h4
    omega
  have hca : c ≠ a := fun h => hc (by simp [h])
  have hcb : c ≠ b := fun h => hc (by simp [h])
  obtain ⟨β, hβ, h3β⟩ := exists_cutDegree_three_of_cherry hN (nontrivial_of_card_four hcard) ((hf f).mpr rfl) (fun k hk => (hf k).mp hk) hg₁ hg₂ hne (fun k hk => (hmemset k).mp hk) ha hb hca hcb
  exact hno3 β hβ h3β

end SingleEdge

/-! ### The reduction -/

section Reduction

universe u v w

variable {X : Type w} [Fintype X] [DecidableEq X]

/-- **`𝒩⁻` has a 4-blob exactly when `T_rd(𝒩⁻)` is unresolved**, by Lemma 1. So the paper's test, "still has a 4-blob", is the test for a cut-edge split. -/
theorem exists_cutDegree_four_iff {V : Type u} {E : Type v} {N : RootedNetwork V E X} (hN : IsBinaryNetwork N) (hcard : Fintype.card X = 4) :
    (∃ β, cutDegree (semidirected hN (nontrivial_of_card_four hcard)).graph β = 4) ↔ ¬ IsTreelike N Finset.univ := by
  have : Finite E := hN.finite_arcs
  obtain ⟨a, b, c, d, h⟩ := exists_names_of_card_four hcard
  have hu : ({a, b, c, d} : Finset X) = Finset.univ := Finset.eq_univ_of_card _ (h.trans hcard.symm)
  rcases lemma1 hN hcard with ⟨⟨z, hz, -⟩, -, hS, -⟩ | ⟨-, h₂, ⟨p, q, r, t, hp, hH⟩, -⟩
  · have hnt := (hasStarTopology_iff_not_isTreelike hN hcard h).mp (hS a b c d h)
    rw [hu] at hnt
    exact ⟨fun _ => hnt, fun _ => ⟨z, hz⟩⟩
  · have hup : ({p, q, r, t} : Finset X) = Finset.univ := Finset.eq_univ_of_card _ (hp.trans hcard.symm)
    have hcs := (hasQuartetTopology_iff_inducedCutSplit hN hcard hp).mp hH
    refine ⟨fun ⟨β, hβ⟩ => ?_, fun hnt => absurd ⟨_, mem_treesOn.mpr ((quartetTree_taxa _ _ _ _ _).trans hup), hcs⟩ hnt⟩
    exfalso
    by_cases hl : ∃ x, blobOf (semidirected hN (nontrivial_of_card_four hcard)).graph ((semidirected hN (nontrivial_of_card_four hcard)).leaf x) = β
    · obtain ⟨x, rfl⟩ := hl
      have h₁ := nodeDegree_treeOfBlobs_leaf hN (nontrivial_of_card_four hcard) x
      have hd := nodeDegree_bridgeQuotient (G := (semidirected hN (nontrivial_of_card_four hcard)).graph) (blobOf (semidirected hN (nontrivial_of_card_four hcard)).graph ((semidirected hN (nontrivial_of_card_four hcard)).leaf x))
      rw [hβ] at hd
      have h₁' : nodeDegree (semidirected hN (nontrivial_of_card_four hcard)).graph.bridgeQuotient (blobOf (semidirected hN (nontrivial_of_card_four hcard)).graph ((semidirected hN (nontrivial_of_card_four hcard)).leaf x)) = 1 := h₁
      omega
    · push Not at hl
      rcases h₂ β hl with h' | h' <;> omega

/-- **The choice of parameters of (b), for every network**: "there is a single choice of numerical parameters that gives a non-cut `CF`", on the boundary of the stochastic parameter space. By induction on the number of edges, "after repeatedly 'removing' 2-blobs and one of the lowest hybrid edges in the 4-blob by setting certain parameters to 0, we arrive at a network" for which removing either lowest hybrid edge gives no 4-blob.

The 2-blob step is `contracted` (`AllmanEtAl2023.ContractBlob`), one blob at a time; the deletion step is `deleted`. Once no 2-blob is left, "by Lemma 1, the only non-leaf blob in `𝒩⁻` is a 4-blob" (`hfour`), which is what `exists_child_eq_leaf` uses. -/
theorem exists_isNonCut_of_not_isTreelike (hcard : Fintype.card X = 4) (n : ℕ) : ∀ {V : Type u} {E : Type v} [Fintype V] [Fintype E] {N : RootedNetwork V E X} (_ : IsBinaryNetwork N),
    Fintype.card E = n → ¬ IsTreelike N Finset.univ → ∃ θ, N.IsWeakMetric θ ∧ IsNonCut (nmscCF N θ 0) Finset.univ := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro V E _ _ N hN hn hnt
    have hP := hN.isPhylogenetic
    have hX := nontrivial_of_card_four hcard
    have hq : (Finset.univ : Finset X).card = 4 := by rw [Finset.card_univ, hcard]
    have hnt' : ¬ N.IsTreelikeOff ∅ Finset.univ := fun h => hnt ((isTreelikeOff_empty_iff hP).mp h)
    have hStar : ∀ (w : V), ¬ StarOff N ∅ Finset.univ w := fun w hw => by
      have h₁ := hw.four_le_degree hP hq
      have h₂ := degree_le_three_of_isBinary hP hN.isBinary w
      omega
    -- "If there are any 2-blobs on `𝒩⁻`, set all edge lengths in `𝒩⁺` that give rise to them equal to 0, with hybrid parameters arbitrary"
    by_cases h2b : ∃ b, cutDegree (semidirected hN hX).graph b = 2
    · obtain ⟨b, hb⟩ := h2b
      obtain ⟨r, S, hC⟩ := exists_isContractible_of_cutDegree_two hb
      let _ : Fintype {v // ¬ (HasStem (contractSuppressed hP hC) ∧ v = (contractSuppressed hP hC).root)} := Fintype.ofFinite _
      let _ : Fintype {e // ¬ (HasStem (contractSuppressed hP hC) ∧ (contractSuppressed hP hC).graph.source e = (contractSuppressed hP hC).root)} := Fintype.ofFinite _
      have hlt : Fintype.card {e // ¬ (HasStem (contractSuppressed hP hC) ∧ (contractSuppressed hP hC).graph.source e = (contractSuppressed hP hC).root)} < n := by
        rw [← hn]
        obtain ⟨v, hv⟩ := hC.nonempty
        obtain ⟨k, hk⟩ := (N.graph.one_le_indegree_iff _).mp (hP.nonroot_indegree v fun h => hC.root (h ▸ hv))
        refine Fintype.card_lt_of_injective_of_notMem (fun e => e.1.1.1) (fun e e' h => Subtype.ext (Subtype.ext (Subtype.ext h))) (b := k) ?_
        rintro ⟨e, he⟩
        exact e.1.1.2 (by rw [show e.1.1.1 = k from he, hk]; exact hv)
      have hnd : ¬ IsTreelike (contracted hP hC) Finset.univ := fun ⟨s, hs, hc⟩ => hnt ⟨s, hs, inducedCutSplit_of_contracted hP hC hcard hc⟩
      obtain ⟨θ', hθ', hnc⟩ := ih _ hlt (contracted_isBinaryNetwork hN hC) rfl hnd
      obtain ⟨θ, hθ, h0, rfl⟩ := exists_contracted_lift hP hC hθ'
      refine ⟨θ, hθ, fun r hr r' hr' hne => ?_⟩
      have := hnc r hr r' hr' hne
      rwa [nmscCF_contracted hP hC hθ.isNormalized le_rfl h0, nmscCF_contracted hP hC hθ.isNormalized le_rfl h0] at this
    -- "By Lemma 1, the only non-leaf blob in `𝒩⁻` is a 4-blob."
    have hfour : ∀ β, (∀ x, blobOf (semidirected hN hX).graph ((semidirected hN hX).leaf x) ≠ β) → cutDegree (semidirected hN hX).graph β = 4 := by
      rcases lemma1 hN hcard with ⟨-, h₃, -, -⟩ | ⟨-, -, ⟨p, q, r, t, hp, hH⟩, -⟩
      · exact fun β hβ => (h₃ β hβ).resolve_left fun h => h2b ⟨β, h⟩
      · have hu : ({p, q, r, t} : Finset X) = Finset.univ := Finset.eq_univ_of_card _ (hp.trans hcard.symm)
        have hcs := (hasQuartetTopology_iff_inducedCutSplit hN hcard hp).mp hH
        exact absurd ⟨_, mem_treesOn.mpr ((quartetTree_taxa _ _ _ _ _).trans hu), hcs⟩ hnt
    -- one step: a deleted network on which the unresolved topology stays
    have hstep : ∀ {D : Set E}, ∀ k ∈ D, ∀ hD : N.IsDeletion D, (∃ β, cutDegree (semidirected (deleted_isBinaryNetwork hN hD) hX).graph β = 4) → ∃ θ, N.IsWeakMetric θ ∧ IsNonCut (nmscCF N θ 0) Finset.univ := by
      intro D k hkD hD hnd4
      have hnd := (exists_cutDegree_four_iff (deleted_isBinaryNetwork hN hD) hcard).mp hnd4
      let _ : Fintype {v // ¬ (HasStem (offSuppressed hN hD) ∧ v = (offSuppressed hN hD).root)} := Fintype.ofFinite _
      let _ : Fintype {e // ¬ (HasStem (offSuppressed hN hD) ∧ (offSuppressed hN hD).graph.source e = (offSuppressed hN hD).root)} := Fintype.ofFinite _
      have hlt : Fintype.card {e // ¬ (HasStem (offSuppressed hN hD) ∧ (offSuppressed hN hD).graph.source e = (offSuppressed hN hD).root)} < n := by
        rw [← hn]
        refine Fintype.card_lt_of_injective_of_notMem (fun e => e.1.1.1) (fun e e' h => Subtype.ext (Subtype.ext (Subtype.ext h))) (b := k) ?_
        rintro ⟨e, he⟩
        exact e.1.1.2.1 (by rw [show e.1.1.1 = k from he]; exact hkD)
      obtain ⟨θ', hθ', hnc⟩ := ih _ hlt (deleted_isBinaryNetwork hN hD) rfl hnd
      obtain ⟨θ, hθ, hD0, rfl⟩ := exists_deleted_lift hN hD hθ'
      refine ⟨θ, hθ, fun r hr r' hr' hne => ?_⟩
      have := hnc r hr r' hr' hne
      rwa [nmscCF_deleted hN hD hθ.isNormalized hD0 le_rfl, nmscCF_deleted hN hD hθ.isNormalized hD0 le_rfl] at this
    by_cases hex : ∃ w, ∃ k₁ k₂, k₁ ≠ k₂ ∧ N.graph.target k₁ = w ∧ N.graph.target k₂ = w
    · -- "the lowest hybrid node"
      obtain ⟨v, ⟨k₁, k₂, hk, ht₁, ht₂⟩, hlow⟩ := exists_lowest hP (S := {w | ∃ k₁ k₂, k₁ ≠ k₂ ∧ N.graph.target k₁ = w ∧ N.graph.target k₂ = w}) hex
      have ht : N.graph.target k₁ = N.graph.target k₂ := ht₁.trans ht₂.symm
      have hD₁ : N.IsDeletion {k₁} := isDeletion_singleton hP hk ht
      have hD₂ : N.IsDeletion {k₂} := isDeletion_singleton hP hk.symm ht.symm
      -- "If the semidirected unrooted network of the resulting network still has a 4-blob"
      by_cases h₁ : ¬ ∃ β, cutDegree (semidirected (deleted_isBinaryNetwork hN hD₁) hX).graph β = 4
      · by_cases h₂ : ¬ ∃ β, cutDegree (semidirected (deleted_isBinaryNetwork hN hD₂) hX).graph β = 4
        · -- both deletions lose the 4-blob
          have h2v : 2 ≤ N.graph.indegree (N.graph.target k₁) := (Set.one_lt_ncard_iff (Set.toFinite _)).mpr ⟨k₁, k₂, rfl, ht.symm, hk⟩
          have hdeg := indegree_eq_two_of_degree_le_three hP h2v (degree_le_three_of_isBinary hP hN.isBinary _)
          have hpar : ∀ f, N.graph.target f = N.graph.target k₁ → f = k₁ ∨ f = k₂ := by
            intro f hf
            by_contra hne
            push Not at hne
            have hgt : 2 < N.graph.indegree (N.graph.target k₁) := (Set.two_lt_ncard_iff (Set.toFinite _)).mpr ⟨k₁, k₂, f, rfl, ht.symm, hf, hk, hne.1.symm, hne.2.symm⟩
            omega
          -- "only a single edge below `v`"
          obtain ⟨g, a, hgs, hga, -⟩ := exists_child_eq_leaf hN hcard (fun β hβ => by rw [hfour β hβ]; norm_num) h2v (fun w hw hr => by
            have := hlow w hw (ht₁ ▸ hr)
            rw [this, ht₁])
          have honly : ∀ x, x ≠ a → ¬ N.graph.Reaches (N.graph.target k₁) (N.leaf x) := by
            intro x hxa hr
            have hg' : ∀ f, N.graph.source f = N.graph.target k₁ → f = g := by
              obtain ⟨g', hg'⟩ := (N.graph.outdegree_eq_one_iff _).mp hdeg.2
              exact fun f hf => ((hg' f).mp hf).trans ((hg' g).mp hgs).symm
            rcases Relation.ReflTransGen.cases_head hr with h | ⟨c, ⟨f, hfs, rfl⟩, hc⟩
            · have := hdeg.1
              rw [h, hP.leaf_indegree] at this
              omega
            · rw [hg' f hfs, hga] at hc
              exact hxa (eq_of_leaf_reachesOff_leaf hP (reachesOff_empty_iff.mpr hc))
          -- "each have exactly two 3-blobs": Lemma 1 on each, and the resolved topology is a split off the deleted arc
          have hres : ∀ {k : E} (hDk : N.IsDeletion {k}), (¬ ∃ β, cutDegree (semidirected (deleted_isBinaryNetwork hN hDk) hX).graph β = 4) → ∃ (s : QuartetTree X) (e : E), N.SplitOffAt {k} e s := by
            intro k hDk hl
            rcases lemma1 (deleted_isBinaryNetwork hN hDk) hcard with ⟨⟨z, hz, -⟩, -⟩ | ⟨-, -, ⟨p, q, r, t, hp, hH⟩, -⟩
            · exact absurd ⟨z, hz⟩ hl
            · obtain ⟨e, he⟩ := (deleted_hasQuartetTopology_iff hN hDk hcard hp).mp hH
              exact ⟨_, e, he⟩
          obtain ⟨s₂, e₂, hsp₂⟩ := hres hD₁ h₁
          obtain ⟨s₁, e₁, hsp₁⟩ := hres hD₂ h₂
          -- "For the sake of contradiction, suppose ..."
          have hss : s₁ ≠ s₂ := by
            rintro rfl
            have hL : IsLowPair N ∅ k₁ k₂ a (s₁.taxa : Set X) :=
              { phylogenetic := hP
                deletion := isDeletion_empty hP
                ne := hk
                target_eq := ht
                notMem₁ := Set.notMem_empty _
                notMem₂ := Set.notMem_empty _
                not_reaches := fun x _ hxa hr => honly x hxa (ReachesOff.reaches hr) }
            have hst : s₁.taxa = Finset.univ := Finset.eq_univ_of_card _ (s₁.card_taxa.trans hcard.symm)
            have hsp₁' : N.SplitOffAt (insert k₂ ∅) e₁ s₁ := by rwa [insert_empty_eq]
            have hsp₂' : N.SplitOffAt (insert k₁ ∅) e₂ s₁ := by rwa [insert_empty_eq]
            obtain ⟨e, he⟩ := hL.exists_splitOffAt (hst ▸ Finset.mem_univ a) hsp₁' hsp₂'
            exact hnt' ⟨s₁, mem_treesOn.mpr hst, e, he⟩
          exact exists_isNonCut_of_deleted hN hcard hk ht hpar honly hss hsp₁ hsp₂
        · exact hstep k₂ rfl hD₂ (not_not.mp h₂)
      · exact hstep k₁ rfl hD₁ (not_not.mp h₁)
    · -- no hybrid node: a tree
      exfalso
      have hroot : taxaBelowOff N ∅ Finset.univ N.root = Finset.univ := Finset.filter_true_of_mem fun x _ => (isDeletion_empty hP).root_reachesOff hP (N.leaf x)
      have hT : HasUniqueParentsBelow N ∅ Finset.univ N.root := by
        intro w _ _ _ f g _ _ hfw hgw
        by_contra hfg
        exact hex ⟨w, f, g, hfg, hfw, hgw⟩
      rcases isTreelikeOff_or_starOff hP (isDeletion_empty hP) hq hT (by rw [hroot]; omega) (by rw [hroot]; omega) with hl | ⟨w, hw⟩
      · exact hnt' hl
      · exact hStar w hw

end Reduction


variable {V E X : Type*} [Fintype V] [Fintype E] [Fintype X] [DecidableEq X] {N : RootedNetwork V E X}

/-- **Statement (b) in the proof of Theorem 1** (`a:claim:thm1b`). If `T` has the unresolved quartet topology, then `CF_abcd` is
non-cut, for generic parameters.

"Again using the analyticity of `CF_abcd` it is enough to show there is a single choice of numerical parameters that gives a non-cut `CF`. We can even choose these parameters to be on the boundary of the stochastic parameter space, since the analytic parametrization of the `CF`s
extends to a larger open set." The choice is `exists_isNonCut_of_not_isTreelike`, on deleted networks as networks of their own, with (a), `theorem1_a`, on them. -/
theorem theorem1_b (hN : IsBinaryNetwork N) (hcard : Fintype.card X = 4) :
    ForGenericParams N fun θ => ∀ (a b c d : X) (h : ({a, b, c, d} : Finset X).card = 4),
      (Trd hN (nontrivial_of_card_four hcard)).HasStarTopology a b c d →
        IsNonCutCF (cfTriple N θ a b c d h) := by
  by_cases hstar : ∃ (a b c d : X) (_ : ({a, b, c, d} : Finset X).card = 4), (Trd hN (nontrivial_of_card_four hcard)).HasStarTopology a b c d
  · obtain ⟨a₀, b₀, c₀, d₀, h₀, hT₀⟩ := hstar
    have hu₀ : ({a₀, b₀, c₀, d₀} : Finset X) = Finset.univ := Finset.eq_univ_of_card _ (h₀.trans hcard.symm)
    have hnt := (hasStarTopology_iff_not_isTreelike hN hcard h₀).mp hT₀
    rw [hu₀] at hnt
    obtain ⟨θ₀, hθ₀, hnc⟩ := exists_isNonCut_of_not_isTreelike hcard _ hN rfl hnt
    refine (IsGenericNull.iUnion (ι := {p : QuartetTree X × QuartetTree X // p.1 ∈ treesOn (Finset.univ : Finset X) ∧ p.2 ∈ treesOn (Finset.univ : Finset X) ∧ p.1 ≠ p.2})
      fun p => isGenericNull_nmscCF_eq (r := p.val.1) (r' := p.val.2) hθ₀.isNormalized (hnc _ p.property.1 _ p.property.2.1 p.property.2.2)).mono ?_
    rintro θ ⟨hθ, hnot⟩
    by_contra hall
    refine hnot fun a b c d h _ => ?_
    have hu : ({a, b, c, d} : Finset X) = Finset.univ := Finset.eq_univ_of_card _ (h.trans hcard.symm)
    refine (isNonCutCF_iff (nmscCF N θ 0) h).mpr ?_
    rw [hu]
    intro r hr r' hr' hne heq
    exact hall (Set.mem_iUnion.mpr ⟨⟨(r, r'), hr, hr', hne⟩, hθ, heq⟩)
  · push Not at hstar
    intro d _
    refine MeasureTheory.measure_mono_null ?_ MeasureTheory.measure_empty
    rintro x ⟨θ, ⟨-, hnot⟩, -⟩
    refine hnot fun a b c d h hT => absurd hT (hstar a b c d h)


end AllmanEtAl2023
