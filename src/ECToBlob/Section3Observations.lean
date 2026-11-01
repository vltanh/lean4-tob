module

public import Basic.General
public import Phylogenetics.NMSC.DisplayedTreeModel
public import Phylogenetics.Tree.Detach
public import ECToBlob.Remark33Counterexample
public import ECToBlob.Section5
public import TOBQMC.Level1CF

/-!
# ECToBlob §3: the observations on what MQS infers

"Under the NMSC and other models, one can extend the model parameterization to a continuous function allowing for `γ`s
in the interval `[0, 1]`. Since `γ`s of 0 and 1 correspond to displayed trees, continuity implies that for `γ`s
sufficiently close to 0 and 1, MQS will infer displayed trees as well. Thus, for a positive-measure subset of parameter
space MQS will select a displayed tree of the network. Varying `γ`s continuously between choices of parameters leading to
different trees also shows that there must be parameter values for which multiple optimal MQS trees exist."
(the paper's text, lines 363-369.)

The boundary is a parent choice `c` (`N.choiceMetric θ c`): inheritance `0` on the deleted arcs `N.deletedArcs c`, for
any number of parents at a reticulation. `IsMQSOptimal p T` says that the tree `T` has the largest score.

## Main results

Observation (1), at the boundary:
* `isMQSOptimal_choiceMetric_iff`: the optimal trees are exactly the binary resolutions of the displayed tree, for
  nonnegative lengths with `HasPositiveEdges`; `isBinaryMaximizer_choiceMetric_iff` is the same among binary trees.
* `isMQSOptimal_choiceMetric_iff_eq`: the displayed tree is the unique optimal tree, if it is binary.

Observation (2), near the boundary:
* `eventually_forall_isMQSOptimal_imp`, `eventually_isMQSOptimal_iff_eq`: the same for all coordinates in a neighbourhood
  of the boundary point. `isBinary_eventually_isMQSOptimal_iff_eq` has no hypothesis but valid lengths, on a binary network.
* `not_isNull_resolvesDisplayed`, `not_isNull_selectsDisplayed`: the set of valid parameters where this holds is not null,
  for the measure of §5.1 (`IsNullParams`) and in the coordinates of `IsGenericNull`, on any network.

Observation (3), ties:
* `exists_tie_on_segment`, `exists_tie_of_unique_maximizers`: two valid parameter points with different unique optimal
  trees have a valid point with two optimal trees on the segment between them.
* `exists_tie_of_displayedTrees`: the same for two parent choices with different binary displayed trees, at any positive
  lengths, varying only the `γ`s.

The 4-cycle network, with no hypothesis left:
* `fourCycle`, `displayedSides_choiceU_ne`: a binary network with the different displayed trees `ab|cd` and `ad|bc`.
* `fourCycle_exists_tie`, `fourCycle_not_isNull`.

## What the observation needs

* **A binary displayed tree, for "will select a displayed tree"**: optimal trees are binary, so a displayed tree that is
  not binary is never optimal (`not_isMQSOptimal_of_not_isBinaryTree`); the claim then holds of its binary resolutions.
  The displayed trees of a binary network are binary (`isBinaryTree_displayedSides_of_isBinary`).
* **Positive length on each internal edge of the displayed tree, for "`γ`s sufficiently close to 0 and 1"**
  (`HasPositiveEdges`). It holds on a binary network at valid lengths, since the lowest vertex of an internal edge has two
  kept children, so a tree arc above it (`hasPositiveEdges_of_isBinary`); and when all lengths are positive
  (`hasPositiveEdges_of_pos`). It can fail on a non-binary network, at a hybrid arc of length `0`. On the network `N₁` of
  Figure 1 with both hybrid arcs of length `0`, the displayed tree is `ab|cd` and all concordance factors are `1/3`, at the
  boundary (`zeroLength_boundary`) and for all valid `γ` (`isMQSOptimal_treeAC_of_length_zero`), so `ac|bd` is optimal.
  The measure of §5.1 has an atom there, so this set of valid parameters is not null for it
  (`not_isNullParams_length_zero`). The positive-measure claim is not affected.

The neighbourhood in Observation (2) depends on the lengths: the proof gives no bound on `γ` uniform in the lengths.
-/

@[expose] public noncomputable section

open Phylogenetics Phylogenetics.RootedNetwork Phylogenetics.NMSC Finset Filter Topology MeasureTheory
open scoped Classical

namespace ECToBlob.Section3Observations

variable {V E X : Type*} [Fintype V] [Fintype E] [Fintype X] [DecidableEq X]
variable {N : RootedNetwork V E X} {θ : MetricData E} {ρ : ℝ}

/-- The tree `T` is optimal for the Maximum Quartet Support criterion with the weights `p`. -/
def IsMQSOptimal (p : QuartetTree X → ℝ) (T : Finset (Finset X)) : Prop :=
  IsUnrootedTree T ∧ ∀ T', IsUnrootedTree T' → quartetSupport p T' ≤ quartetSupport p T

/-! ### The score on each set of four taxa -/

omit [Fintype V] [Fintype E] in
/-- A binary tree resolving a tree `U`, for weights for which the quartet trees of `U` are strictly the largest and
the others tie, has the largest score: a comparison on each set of four taxa. -/
theorem quartetScore_le_of_resolves {p : QuartetTree X → ℝ} (hp : ∀ s, 0 ≤ p s) {U T T' : Finset (Finset X)}
    (hT : IsBinaryTree T) (hsub : U ⊆ T) (hT' : IsUnrootedTree T')
    (h₁ : ∀ s, Displays U s → ∀ r ∈ s.alternatives, p r < p s)
    (h₂ : ∀ q : Finset X, #q = 4 → (∀ r ∈ treesOn q, ¬ Displays U r) →
      ∀ r ∈ treesOn q, ∀ r' ∈ treesOn q, p r = p r') :
    quartetSupport p T' ≤ quartetSupport p T := by
  have hTu := hT.isUnrootedTree
  have hmaps : ∀ s ∈ (univ : Finset (QuartetTree X)), s.taxa ∈ univ.filter fun q : Finset X => #q = 4 :=
    fun s _ => mem_filter.2 ⟨mem_univ _, s.card_taxa⟩
  have hfib : ∀ W : Finset (Finset X), quartetSupport p W =
      ∑ q ∈ univ.filter (fun q : Finset X => #q = 4), ∑ s ∈ treesOn q, if Displays W s then p s else 0 :=
    fun W => (Finset.sum_fiberwise_of_maps_to hmaps _).symm
  rw [hfib, hfib]
  refine sum_le_sum fun q hq => ?_
  have hq4 : #q = 4 := (mem_filter.1 hq).2
  obtain ⟨r, hr, hdr⟩ := hT.exists_displays hq4
  have hrq := mem_treesOn.1 hr
  have hval : (∑ s ∈ treesOn q, if Displays T s then p s else 0) = p r := by
    rw [← hrq]
    exact sum_treesOn_eq_of_displays hTu p hdr
  rw [hval]
  by_cases hex : ∃ r' ∈ treesOn q, Displays T' r'
  · obtain ⟨r', hr', hdr'⟩ := hex
    have hr'q := mem_treesOn.1 hr'
    have hval' : (∑ s ∈ treesOn q, if Displays T' s then p s else 0) = p r' := by
      rw [← hr'q]
      exact sum_treesOn_eq_of_displays hT' p hdr'
    rw [hval']
    by_cases hU : ∃ r₀ ∈ treesOn q, Displays U r₀
    · obtain ⟨r₀, hr₀, hd₀⟩ := hU
      have hr₀q := mem_treesOn.1 hr₀
      have hrr₀ : r = r₀ := hTu.displays_unique hdr (hd₀.mono hsub) (hrq.trans hr₀q.symm)
      subst hrr₀
      by_cases hrr' : r' = r
      · rw [hrr']
      · exact (h₁ r hd₀ r' (QuartetTree.mem_alternatives.2 ⟨hr'q.trans hrq.symm, hrr'⟩)).le
    · push Not at hU
      exact (h₂ q hq4 hU r' hr' r hr).le
  · push Not at hex
    rw [sum_eq_zero fun s hs => ite_eq_right (hex s hs)]
    exact hp r

/-! ### At a parent choice -/

/-- The internal edges of the tree of a parent choice have positive length: each one contains a kept arc of positive
length. This is what "displayed tree" needs in the observation of lines 363-369. It holds when the network is binary
(`hasPositiveEdges_of_isBinary`) and when all the arcs have positive length. It can fail otherwise: a reticulation with
several children, whose hybrid arc of length `0` is the whole of an internal edge of the displayed tree. -/
def HasPositiveEdges (θ : MetricData E) (c : N.ParentChoice) : Prop :=
  ∀ u, 2 ≤ #(N.displayedCluster c u) → 2 ≤ #(N.displayedCluster c u)ᶜ →
    ∃ e, e ∉ N.deletedArcs c ∧ N.displayedCluster c (N.graph.target e) = N.displayedCluster c u ∧
      0 < θ.length e

omit [Fintype V] [Fintype E] in
/-- With all arcs of positive length, the internal edges of a tree have positive length. -/
theorem hasPositiveEdges_of_pos (hN : N.IsPhylogenetic) (c : N.ParentChoice) (hℓ : ∀ f, 0 < θ.length f) :
    HasPositiveEdges θ c := by
  intro u h₁ h₂
  have hur : u ≠ N.root := by
    rintro rfl
    have : N.displayedCluster c N.root = univ := eq_univ_of_forall fun x =>
      mem_displayedCluster.2 ((isDeletion_deletedArcs hN c).root_reachesOff hN _)
    rw [this] at h₂
    simp at h₂
  have ht : N.graph.target (c ⟨u, hur⟩).val = u := (c ⟨u, hur⟩).property
  exact ⟨(c ⟨u, hur⟩).val, notMem_deletedArcs_choice c _, by rw [ht], hℓ _⟩

omit [Fintype E] in
/-- A quartet tree displayed by a parent choice is cut by a cluster. -/
theorem exists_cluster_of_displays {c : N.ParentChoice} {s : QuartetTree X}
    (hd : Displays (N.displayedSides c) s) :
    ∃ P ∈ s.val, ∃ u, ∀ x ∈ s.taxa, x ∈ P ↔ x ∈ N.displayedCluster c u := by
  obtain ⟨A, hA, hAs⟩ := hd
  rcases mem_unroot.1 hA with ⟨hAH, -⟩ | ⟨hAH, -⟩
  · obtain ⟨-, u, rfl⟩ := mem_displayedClusters.1 hAH
    exact ⟨_, hAs, u, fun x hx => by simp [hx]⟩
  · obtain ⟨-, u, hu⟩ := mem_displayedClusters.1 hAH
    refine ⟨_, s.sdiff_mem hAs, u, fun x hx => ?_⟩
    rw [hu]
    simp [hx]

/-- The arc of a cluster of a parent choice, for all nonnegative lengths: the split of the arc has the largest
concordance factor, by at least the probability that two lineages coalesce on the arc. -/
theorem one_sub_exp_le_sub_choiceMetric (hN : N.IsPhylogenetic) (c : N.ParentChoice) (hρ : 0 ≤ ρ ∧ ρ ≤ 1)
    (hℓ : ∀ f, 0 ≤ θ.length f) (s : QuartetTree X) {P : Finset X} (hP : P ∈ s.val) {e : E}
    (he : e ∉ N.deletedArcs c)
    (hb : ∀ x ∈ P, N.ReachesOff (N.deletedArcs c) (N.graph.target e) (N.leaf x))
    (hn : ∀ x ∈ s.taxa, x ∉ P → ¬ N.ReachesOff (N.deletedArcs c) (N.graph.target e) (N.leaf x))
    {r : QuartetTree X} (hr : r ∈ s.alternatives) :
    1 - Real.exp (-θ.length e) ≤
      nmscCF N (N.choiceMetric θ c) ρ s - nmscCF N (N.choiceMetric θ c) ρ r := by
  obtain ⟨a, ha⟩ : P.Nonempty := card_pos.1 (by rw [s.card_of_mem hP]; omega)
  have hek : N.IsKeptArc c e := ⟨he, a, hb a ha⟩
  have hM := isPhylogenetic_choiceNetwork hN c a
  have hbound : ∀ ε : ℝ, 0 < ε → 1 - Real.exp (-θ.length e) ≤
      nmscCF N (N.choiceMetric (addLength θ ε) c) ρ s - nmscCF N (N.choiceMetric (addLength θ ε) c) ρ r := by
    intro ε hε
    rw [← nmscCF_choiceNetwork hN c a hρ.1 _ s, ← nmscCF_choiceNetwork hN c a hρ.1 _ r]
    have h := one_sub_exp_le_sub_nmscCF_of_tree (ρ := ρ) hM
      (isMetric_choiceNetworkMetric hN c a (θ := addLength θ ε) fun f _ =>
        add_pos_of_nonneg_of_pos (hℓ f) hε) hρ
      (fun f g h => eq_of_target_choiceNetwork hN c a h) s hP (e := ⟨e, hek⟩)
      (fun x hx => reaches_choiceNetwork hN c a _ _ (hb x hx))
      (fun x hx hxP hb' => hn x hx hxP (reachesOff_of_reaches_choiceNetwork hN c a hb')) hr
    refine le_trans ?_ h
    have : Real.exp (-(N.choiceNetworkMetric (addLength θ ε) c).length ⟨e, hek⟩) ≤ Real.exp (-θ.length e) :=
      Real.exp_le_exp.2 (by
        change -(θ.length e + ε) ≤ _
        linarith)
    linarith
  have hℓa : ∀ f, AnalyticOnNhd ℝ (fun ε : ℝ => (N.choiceMetric (addLength θ ε) c).length f) Set.univ :=
    fun f => analyticOnNhd_const.add analyticOnNhd_id
  have hγa : ∀ f, AnalyticOnNhd ℝ (fun ε : ℝ => (N.choiceMetric (addLength θ ε) c).inheritance f) Set.univ :=
    fun f => analyticOnNhd_const
  have hcont : ∀ t : QuartetTree X, Continuous fun ε : ℝ => nmscCF N (N.choiceMetric (addLength θ ε) c) ρ t :=
    fun t => continuousOn_univ.1 (analyticOnNhd_nmscCF N
      (θ := fun ε => N.choiceMetric (addLength θ ε) c) ρ hℓa hγa t).continuousOn
  have hlim : Tendsto (fun ε : ℝ => nmscCF N (N.choiceMetric (addLength θ ε) c) ρ s -
      nmscCF N (N.choiceMetric (addLength θ ε) c) ρ r) (nhdsWithin 0 (Set.Ioi 0))
      (nhds (nmscCF N (N.choiceMetric θ c) ρ s - nmscCF N (N.choiceMetric θ c) ρ r)) := by
    have he0 : nmscCF N (N.choiceMetric (addLength θ 0) c) ρ s - nmscCF N (N.choiceMetric (addLength θ 0) c) ρ r =
        nmscCF N (N.choiceMetric θ c) ρ s - nmscCF N (N.choiceMetric θ c) ρ r := by rw [addLength_zero]
    rw [← he0]
    exact ((hcont s).sub (hcont r)).tendsto 0 |>.mono_left nhdsWithin_le_nhds
  refine ge_of_tendsto hlim ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact hbound ε hε

/-- **In the parameters of a parent choice, the quartet trees of the displayed tree are strictly the most probable**,
when its internal edges have positive length. -/
theorem nmscCF_lt_choiceMetric (hN : N.IsPhylogenetic) {c : N.ParentChoice} (hρ : 0 ≤ ρ ∧ ρ ≤ 1)
    (hℓ : ∀ f, 0 ≤ θ.length f) (hE : HasPositiveEdges θ c) {s : QuartetTree X}
    (hs : Displays (N.displayedSides c) s) {r : QuartetTree X} (hr : r ∈ s.alternatives) :
    nmscCF N (N.choiceMetric θ c) ρ r < nmscCF N (N.choiceMetric θ c) ρ s := by
  obtain ⟨P, hP, u, hu⟩ := exists_cluster_of_displays hs
  have hQ := s.sdiff_mem hP
  have h₁ : 2 ≤ #(N.displayedCluster c u) := by
    have hsub : P ⊆ N.displayedCluster c u := fun x hx => (hu x (s.subset_taxa hP hx)).1 hx
    have := card_le_card hsub
    rw [s.card_of_mem hP] at this
    exact this
  have h₂ : 2 ≤ #(N.displayedCluster c u)ᶜ := by
    have hsub : s.taxa \ P ⊆ (N.displayedCluster c u)ᶜ := fun x hx => by
      obtain ⟨hx₁, hx₂⟩ := mem_sdiff.1 hx
      exact mem_compl.2 fun h => hx₂ ((hu x hx₁).2 h)
    have := card_le_card hsub
    rw [s.card_of_mem hQ] at this
    exact this
  obtain ⟨e, he, hclu, hpos⟩ := hE u h₁ h₂
  have h := one_sub_exp_le_sub_choiceMetric hN c hρ hℓ s hP he
    (fun x hx => mem_displayedCluster.1 (hclu ▸ (hu x (s.subset_taxa hP hx)).1 hx))
    (fun x hxq hxP hr' => hxP ((hu x hxq).2 (hclu ▸ mem_displayedCluster.2 hr'))) hr
  have : Real.exp (-θ.length e) < 1 := Real.exp_lt_one_iff.2 (by linarith)
  linarith

omit [Fintype E] in
/-- A vertex whose cluster traces a side of a quartet tree makes the tree of the choice display it. -/
theorem displays_of_cluster {c : N.ParentChoice} {s : QuartetTree X}
    {P : Finset X} (hP : P ∈ s.val) {u : V} (hb : ∀ x ∈ P, x ∈ N.displayedCluster c u)
    (hn : ∀ x ∈ s.taxa, x ∉ P → x ∉ N.displayedCluster c u) : Displays (N.displayedSides c) s := by
  have hAq : N.displayedCluster c u ∩ s.taxa = P := by
    ext x
    rw [mem_inter]
    constructor
    · rintro ⟨hxA, hxq⟩
      by_contra hxP
      exact hn x hxq hxP hxA
    · exact fun hx => ⟨hb x hx, s.subset_taxa hP hx⟩
  obtain ⟨a, ha⟩ : P.Nonempty := card_pos.1 (by rw [s.card_of_mem hP]; omega)
  obtain ⟨y, hy⟩ : (s.taxa \ P).Nonempty :=
    card_pos.1 (by rw [s.card_of_mem (s.sdiff_mem hP)]; omega)
  obtain ⟨hyq, hyP⟩ := mem_sdiff.1 hy
  refine ⟨_, mem_unroot.2 (Or.inl ⟨mem_displayedClusters.2 ⟨nonempty_iff_ne_empty.1 ⟨a, hb a ha⟩, u, rfl⟩,
    fun h => hn y hyq hyP (h ▸ mem_univ y)⟩), ?_⟩
  rw [hAq]
  exact hP

/-- **Observation (1) of lines 363-369: at a parent choice, the optimal trees are exactly the binary resolutions of the
displayed tree**, when its internal edges have positive length. This is the score as a sum of strict comparisons on each
set of four taxa, and Theorem 3.1 for the tree of the choice, as a network with no reticulation. -/
theorem isMQSOptimal_choiceMetric_iff [Nonempty X] (hN : N.IsPhylogenetic) (c : N.ParentChoice) (hρ : 0 ≤ ρ ∧ ρ ≤ 1)
    (hℓ : ∀ f, 0 ≤ θ.length f) (hE : HasPositiveEdges θ c) (T : Finset (Finset X)) :
    IsMQSOptimal (nmscCF N (N.choiceMetric θ c) ρ) T ↔ IsBinaryTree T ∧ N.displayedSides c ⊆ T := by
  have hw := isWeakMetric_choiceMetric hN hℓ c
  have hnn := nmscCF_nonneg_weak (ρ := ρ) hN hw hρ
  have h₁ : ∀ s, Displays (N.displayedSides c) s → ∀ r ∈ s.alternatives,
      nmscCF N (N.choiceMetric θ c) ρ r < nmscCF N (N.choiceMetric θ c) ρ s := fun s hs r hr =>
    nmscCF_lt_choiceMetric hN hρ hℓ hE hs hr
  have hU := isUnrootedTree_displayedSides (N := N) hN c
  constructor
  · rintro ⟨hT, hmax⟩
    refine ⟨remark3_2 _ hnn (fun q hq => sum_nmscCF_weak hN hw.isNormalized hρ.1 hq) hT hmax, ?_⟩
    obtain ⟨x₀⟩ := ‹Nonempty X›
    have hM := isPhylogenetic_choiceNetwork hN c x₀
    have hstar : ∀ {f g : {f // N.IsKeptArc c f}}, (N.choiceNetwork hN c x₀).graph.target f =
        (N.choiceNetwork hN c x₀).graph.target g → f = g := fun h => eq_of_target_choiceNetwork hN c x₀ h
    have hF : nmscCF N (N.choiceMetric θ c) ρ = nmscCF (N.choiceNetwork hN c x₀) (N.choiceNetworkMetric θ c) ρ :=
      funext fun s => (nmscCF_choiceNetwork hN c x₀ hρ.1 θ s).symm
    have hsub : treeOfBlobs (N.choiceNetwork hN c x₀) ⊆ T := by
      refine theorem3_1 hM _ hnn (fun s hs r hr => h₁ s ?_ r hr) ?_ hT hmax
      · obtain ⟨P, hP, e', hd, hn⟩ := exists_separating_arc hM
          (inducedCutSplit_of_displays_treeOfBlobs hM hs)
        refine displays_of_cluster hP (u := N.graph.target e'.val) (fun x hx => ?_) (fun x hxq hxP hx => ?_)
        · exact mem_displayedCluster.2 (reachesOff_of_reaches_choiceNetwork hN c x₀ ((hd x hx).isBelow hM))
        · exact hn x hxq hxP (reaches_choiceNetwork hN c x₀ _ _ (mem_displayedCluster.1 hx))
      · rw [hF]
        exact exchangeability_weak hM (isWeakMetric_choiceNetworkMetric hN c x₀ fun f _ => hℓ f) hρ
    refine subset_of_forall_displays hT hU fun s hs => Displays.mono hsub ?_
    obtain ⟨P, hP, u, hu⟩ := exists_cluster_of_displays hs
    have hQ := s.sdiff_mem hP
    have h₂ : 2 ≤ #(N.displayedCluster c u) := by
      have := card_le_card (fun x hx => (hu x (s.subset_taxa hP hx)).1 hx : P ⊆ N.displayedCluster c u)
      rwa [s.card_of_mem hP] at this
    obtain ⟨y, hy⟩ : (s.taxa \ P).Nonempty :=
      card_pos.1 (by rw [s.card_of_mem hQ]; omega)
    obtain ⟨hyq, hyP⟩ := mem_sdiff.1 hy
    have hur : u ≠ N.root := by
      rintro rfl
      exact hyP ((hu y hyq).2 (mem_displayedCluster.2 ((isDeletion_deletedArcs hN c).root_reachesOff hN _)))
    obtain ⟨a, ha⟩ : P.Nonempty := card_pos.1 (by rw [s.card_of_mem hP]; omega)
    have hua := mem_displayedCluster.1 ((hu a (s.subset_taxa hP ha)).1 ha)
    have hek : N.IsKeptArc c (c ⟨u, hur⟩).val := ⟨notMem_deletedArcs_choice c _, a, by
      rw [(c ⟨u, hur⟩).property]
      exact hua⟩
    let e' : {f // N.IsKeptArc c f} := ⟨_, hek⟩
    have ht : N.graph.target e'.val = u := (c ⟨u, hur⟩).property
    have hbel : ∀ x, (N.choiceNetwork hN c x₀).IsBelow e' x ↔ x ∈ N.displayedCluster c u := fun x => by
      constructor
      · intro h
        have := reachesOff_of_reaches_choiceNetwork hN c x₀ h
        exact mem_displayedCluster.2 (ht ▸ this)
      · intro h
        exact reaches_choiceNetwork hN c x₀ _ _ (ht ▸ mem_displayedCluster.1 h)
    refine TOBQMC.Level1.displays_of_isBridge hM s hP (e := e')
      ((DirectedMultigraph.isBridge_iff _ _).2 ⟨_, fun f => crosses_below_iff_of_tree hM (fun _ _ h => hstar h) e' f⟩)
      (fun x hx => ?_)
      (fun x hx hxP hb => hxP ((hu x hx).2 ((hbel x).1 hb)))
    exact not_avoidingReach_of_tree hM (fun _ _ h => hstar h) ((hbel x).2 ((hu x (s.subset_taxa hP hx)).1 hx))
  · rintro ⟨hTb, hsub⟩
    refine ⟨hTb.isUnrootedTree, fun T' hT' => quartetScore_le_of_resolves hnn hTb hsub hT' h₁ ?_⟩
    intro q hq hstar r hr r' hr'
    rw [nmscCF_choiceMetric_eq_third_of_nonneg hN c hρ hℓ hq hstar hr,
      nmscCF_choiceMetric_eq_third_of_nonneg hN c hρ hℓ hq hstar hr']

omit [Fintype V] [Fintype E] in
/-- For weights that sum to one on each set of four taxa, the optimal trees are the maximizers among binary trees
(Remark 3.2). -/
theorem isMQSOptimal_iff_isBinaryMaximizer {p : QuartetTree X → ℝ} (hp : ∀ s, 0 ≤ p s)
    (hsum : ∀ q : Finset X, #q = 4 → ∑ r ∈ treesOn q, p r = 1) {T : Finset (Finset X)} :
    IsMQSOptimal p T ↔ IsBinaryTree T ∧ ∀ T', IsBinaryTree T' → quartetSupport p T' ≤ quartetSupport p T := by
  constructor
  · exact fun h => ⟨remark3_2 p hp hsum h.1 h.2, fun T' hT' => h.2 T' hT'.isUnrootedTree⟩
  · rintro ⟨hT, hmax⟩
    refine ⟨hT.isUnrootedTree, fun T' hT' => ?_⟩
    obtain ⟨S, hS, hSmax⟩ := exists_max_quartetSupport hT.isUnrootedTree p
    exact (hSmax T' hT').trans (hmax S (remark3_2 p hp hsum hS hSmax))

/-- **Observation (1), among binary trees**: at a parent choice, the maximizers among binary trees are exactly the binary
resolutions of the displayed tree. -/
theorem isBinaryMaximizer_choiceMetric_iff [Nonempty X] (hN : N.IsPhylogenetic) (c : N.ParentChoice)
    (hρ : 0 ≤ ρ ∧ ρ ≤ 1) (hℓ : ∀ f, 0 ≤ θ.length f) (hE : HasPositiveEdges θ c) (T : Finset (Finset X)) :
    (IsBinaryTree T ∧ ∀ T', IsBinaryTree T' →
      quartetSupport (nmscCF N (N.choiceMetric θ c) ρ) T' ≤ quartetSupport (nmscCF N (N.choiceMetric θ c) ρ) T) ↔
      IsBinaryTree T ∧ N.displayedSides c ⊆ T := by
  have hw := isWeakMetric_choiceMetric hN hℓ c
  rw [← isMQSOptimal_iff_isBinaryMaximizer (nmscCF_nonneg_weak hN hw hρ)
    (fun _ hq => sum_nmscCF_weak hN hw.isNormalized hρ.1 hq)]
  exact isMQSOptimal_choiceMetric_iff hN c hρ hℓ hE T

omit [Fintype V] [Fintype E] in
/-- A binary tree has no proper resolution. -/
theorem eq_of_isBinaryTree_of_subset {U T : Finset (Finset X)} (hU : IsBinaryTree U) (hT : IsUnrootedTree T)
    (hsub : U ⊆ T) : T = U := by
  refine Subset.antisymm (subset_of_forall_displays hU.isUnrootedTree hT fun s hs => ?_) hsub
  obtain ⟨r, hr, hdr⟩ := hU.exists_displays s.card_taxa
  have := hT.displays_unique (hdr.mono hsub) hs (mem_treesOn.1 hr)
  rwa [this] at hdr

/-- **Observation (1), when the displayed tree is binary: it is the unique optimal tree.** -/
theorem isMQSOptimal_choiceMetric_iff_eq [Nonempty X] (hN : N.IsPhylogenetic) (c : N.ParentChoice)
    (hρ : 0 ≤ ρ ∧ ρ ≤ 1) (hℓ : ∀ f, 0 ≤ θ.length f) (hE : HasPositiveEdges θ c)
    (hU : IsBinaryTree (N.displayedSides c)) (T : Finset (Finset X)) :
    IsMQSOptimal (nmscCF N (N.choiceMetric θ c) ρ) T ↔ T = N.displayedSides c := by
  rw [isMQSOptimal_choiceMetric_iff hN c hρ hℓ hE T]
  constructor
  · rintro ⟨hT, hsub⟩
    exact eq_of_isBinaryTree_of_subset hU hT.isUnrootedTree hsub
  · rintro rfl
    exact ⟨hU, Subset.rfl⟩

/-- **When the displayed tree is not binary, MQS never selects it**, since optimal trees are binary (Remark 3.2): the
observation of lines 363-369 then holds only in the sense of `isMQSOptimal_choiceMetric_iff`. This holds at every point of
parameter space, boundary included. -/
theorem not_isMQSOptimal_of_not_isBinaryTree (hN : N.IsPhylogenetic) (hθ : N.IsWeakMetric θ) (hρ : 0 ≤ ρ ∧ ρ ≤ 1)
    {U : Finset (Finset X)} (hU : ¬ IsBinaryTree U) : ¬ IsMQSOptimal (nmscCF N θ ρ) U := fun h =>
  hU (remark3_2 _ (nmscCF_nonneg_weak hN hθ hρ) (fun _ hq => sum_nmscCF_weak hN hθ.isNormalized hρ.1 hq) h.1 h.2)

/-! ### Binary networks -/

section Binary

omit [Fintype V] [Fintype E] [Fintype X] [DecidableEq X] in
/-- A taxon of the cluster of a vertex, other than the vertex itself, is below a kept child. -/
theorem exists_kept_child [Fintype X] {c : N.ParentChoice} {w : V} {x : X} (hx : x ∈ N.displayedCluster c w)
    (hne : w ≠ N.leaf x) :
    ∃ f, f ∉ N.deletedArcs c ∧ N.graph.source f = w ∧ x ∈ N.displayedCluster c (N.graph.target f) := by
  rcases Relation.ReflTransGen.cases_head (mem_displayedCluster.1 hx) with h | ⟨b, ⟨f, hf, hs, ht⟩, hb⟩
  · exact absurd h hne
  · exact ⟨f, hf, hs, mem_displayedCluster.2 (ht ▸ hb)⟩

omit [Fintype V] [Fintype E] [Fintype X] [DecidableEq X] in
/-- The cluster of a kept child is in the cluster of its parent. -/
theorem displayedCluster_target_subset [Fintype X] {c : N.ParentChoice} {f : E} (hf : f ∉ N.deletedArcs c) :
    N.displayedCluster c (N.graph.target f) ⊆ N.displayedCluster c (N.graph.source f) := fun _ hx =>
  mem_displayedCluster.2 (Relation.ReflTransGen.head ⟨f, hf, rfl, rfl⟩ (mem_displayedCluster.1 hx))

omit [Fintype V] [Fintype X] [DecidableEq X] in
/-- A vertex of outdegree at most two has at most two arcs out. -/
theorem eq_or_eq_of_outdegree_le_two {w : V} (hout : N.graph.outdegree w ≤ 2) {f g k : E} (hf : N.graph.source f = w)
    (hg : N.graph.source g = w) (hk : N.graph.source k = w) (hfg : f ≠ g) : k = f ∨ k = g := by
  by_contra hne
  push Not at hne
  have h3 : ({f, g, k} : Set E).ncard = 3 := Set.ncard_eq_three.2 ⟨f, g, k, hfg, hne.1.symm, hne.2.symm, rfl⟩
  have hsub : ({f, g, k} : Set E) ⊆ {e | N.graph.source e = w} := by
    rintro e (rfl | rfl | rfl)
    · exact hf
    · exact hg
    · exact hk
  have := Set.ncard_le_ncard hsub (Set.toFinite _)
  unfold DirectedMultigraph.outdegree at hout
  omega

omit [Fintype V] [Fintype E] [Fintype X] [DecidableEq X] in
/-- A binary network has outdegree at most two. -/
theorem outdegree_le_two (hN : N.IsPhylogenetic) (hB : N.IsBinary) (v : V) : N.graph.outdegree v ≤ 2 := by
  by_cases hv : v = N.root
  · rw [hv, hB.1]
  · by_cases h0 : N.graph.outdegree v = 0
    · omega
    · have := hB.2 v hv h0
      have := hN.nonroot_indegree v hv
      omega

omit [Fintype V] [Fintype E] [DecidableEq X] in
/-- The cluster of the root has all the taxa. -/
theorem displayedCluster_root (hN : N.IsPhylogenetic) (c : N.ParentChoice) : N.displayedCluster c N.root = univ :=
  eq_univ_of_forall fun _ => mem_displayedCluster.2 ((isDeletion_deletedArcs hN c).root_reachesOff hN _)

omit [Fintype V] [DecidableEq X] in
/-- A vertex with two taxa below it is not a taxon. -/
theorem ne_leaf_of_mem_of_mem (hN : N.IsPhylogenetic) {c : N.ParentChoice} {w : V} {x y : X}
    (hx : x ∈ N.displayedCluster c w) (hy : y ∈ N.displayedCluster c w) (hxy : x ≠ y) (z : X) : w ≠ N.leaf z := by
  intro hz
  have hne : w ≠ N.leaf x ∨ w ≠ N.leaf y := by
    by_contra hc
    push Not at hc
    exact hxy (hN.leaf_injective (hc.1.symm.trans hc.2))
  have hout : N.graph.outdegree w = 0 := (hN.leaves w).2 ⟨z, hz.symm⟩
  obtain ⟨f, hf⟩ : ∃ f, N.graph.source f = w := by
    rcases hne with h | h
    · obtain ⟨f, -, hs, -⟩ := exists_kept_child hx h
      exact ⟨f, hs⟩
    · obtain ⟨f, -, hs, -⟩ := exists_kept_child hy h
      exact ⟨f, hs⟩
  exact Set.ncard_ne_zero_of_mem (s := {e | N.graph.source e = w}) hf (Set.toFinite _) hout

omit [Fintype V] [DecidableEq X] in
/-- **In a binary network, the internal edges of each displayed tree have positive length**: the lowest vertex of an
internal edge has two kept children, so its parent arc is a tree arc, even if the rest of the chain has hybrid arcs of
length `0`. -/
theorem hasPositiveEdges_of_isBinary [DecidableEq X] (hN : N.IsPhylogenetic) (hB : N.IsBinary) (c : N.ParentChoice)
    (hℓ : ∀ e, N.IsTreeArc e → 0 < θ.length e) : HasPositiveEdges θ c := by
  intro u h₁ h₂
  obtain ⟨w, hw, hlow⟩ := exists_lowest hN (S := {w | N.displayedCluster c w = N.displayedCluster c u}) ⟨u, rfl⟩
  have hw' : N.displayedCluster c w = N.displayedCluster c u := hw
  have hwr : w ≠ N.root := by
    rintro rfl
    rw [← hw', displayedCluster_root hN c] at h₂
    simp at h₂
  obtain ⟨x, hx, y, hy, hxy⟩ := one_lt_card.1 (by rwa [← hw'] at h₁ : 1 < #(N.displayedCluster c w))
  have hint := ne_leaf_of_mem_of_mem hN hx hy hxy
  obtain ⟨f, hfD, hfs, hfx⟩ := exists_kept_child hx (hint x)
  have hfne : N.displayedCluster c (N.graph.target f) ≠ N.displayedCluster c w := fun h => by
    have hr : N.graph.Reaches w (N.graph.target f) := Relation.ReflTransGen.single ⟨f, hfs, rfl⟩
    have heq := hlow _ (h.trans hw') hr
    exact hN.acyclic w (Relation.TransGen.single ⟨f, hfs, heq⟩)
  have hfsub : N.displayedCluster c (N.graph.target f) ⊆ N.displayedCluster c w :=
    hfs ▸ displayedCluster_target_subset hfD
  obtain ⟨z, hz, hzf⟩ : ∃ z ∈ N.displayedCluster c w, z ∉ N.displayedCluster c (N.graph.target f) := by
    by_contra hc
    push Not at hc
    exact hfne (Subset.antisymm hfsub hc)
  obtain ⟨g, -, hgs, hgz⟩ := exists_kept_child hz (hint z)
  have hfg : f ≠ g := fun h => hzf (h ▸ hgz)
  have hout : 2 ≤ N.graph.outdegree w := by
    have h2 : ({f, g} : Set E).ncard = 2 := Set.ncard_pair hfg
    have hsub : ({f, g} : Set E) ⊆ {e | N.graph.source e = w} := by
      rintro e (rfl | rfl)
      · exact hfs
      · exact hgs
    have := Set.ncard_le_ncard hsub (Set.toFinite _)
    unfold DirectedMultigraph.outdegree
    omega
  have hin : N.graph.indegree w = 1 := by
    have h3 := hB.2 w hwr (by omega)
    have h4 := hN.nonroot_indegree w hwr
    omega
  have ht : N.graph.target (c ⟨w, hwr⟩).val = w := (c ⟨w, hwr⟩).property
  exact ⟨(c ⟨w, hwr⟩).val, notMem_deletedArcs_choice c _, by rw [ht, hw'], hℓ _ (by
    unfold IsTreeArc
    rw [ht, hin])⟩

omit [Fintype E] in
/-- A vertex whose cluster has exactly two of four taxa gives a quartet tree of the tree of the choice. -/
theorem exists_displays_of_card_inter {c : N.ParentChoice} {v : V} {q : Finset X} (hq : #q = 4)
    (h2 : #(N.displayedCluster c v ∩ q) = 2) : ∃ s ∈ treesOn q, Displays (N.displayedSides c) s := by
  have hne : N.displayedCluster c v ≠ ∅ := by
    intro h
    rw [h, empty_inter, card_empty] at h2
    omega
  have huniv : N.displayedCluster c v ≠ univ := by
    intro h
    rw [h, univ_inter, hq] at h2
    omega
  have hA : N.displayedCluster c v ∈ N.displayedSides c :=
    mem_unroot.2 (Or.inl ⟨mem_displayedClusters.2 ⟨hne, v, rfl⟩, huniv⟩)
  exact ⟨_, mem_treesOn.2 (quartetOfCherry_taxa _ _ hq inter_subset_right h2), displays_quartetOfCherry hA hq h2⟩

/-- **The displayed trees of a binary network are binary.** -/
theorem isBinaryTree_displayedSides_of_isBinary [Nonempty X] (hN : N.IsPhylogenetic) (hB : N.IsBinary)
    (c : N.ParentChoice) : IsBinaryTree (N.displayedSides c) := by
  refine isBinaryTree_of_forall_displays (isUnrootedTree_displayedSides hN c) fun q hq => ?_
  obtain ⟨w, hw, hlow⟩ := exists_lowest hN (S := {w | 3 ≤ #(N.displayedCluster c w ∩ q)}) ⟨N.root, by
    change 3 ≤ #(N.displayedCluster c N.root ∩ q)
    rw [displayedCluster_root hN c, univ_inter, hq]
    omega⟩
  have hw' : 3 ≤ #(N.displayedCluster c w ∩ q) := hw
  have hle : ∀ f, N.graph.source f = w → #(N.displayedCluster c (N.graph.target f) ∩ q) ≤ 2 := fun f hs => by
    by_contra hc
    have heq := hlow (N.graph.target f) (show 3 ≤ #(N.displayedCluster c (N.graph.target f) ∩ q) by omega)
      (Relation.ReflTransGen.single ⟨f, hs, rfl⟩)
    exact hN.acyclic w (Relation.TransGen.single ⟨f, hs, heq⟩)
  obtain ⟨x, hx, x', hx', hxx'⟩ := one_lt_card.1 (by omega : 1 < #(N.displayedCluster c w ∩ q))
  have hint := ne_leaf_of_mem_of_mem hN (mem_inter.1 hx).1 (mem_inter.1 hx').1 hxx'
  obtain ⟨f, -, hfs, hfx⟩ := exists_kept_child (mem_inter.1 hx).1 (hint x)
  by_cases h2 : #(N.displayedCluster c (N.graph.target f) ∩ q) = 2
  · exact exists_displays_of_card_inter hq h2
  have h1 : #(N.displayedCluster c (N.graph.target f) ∩ q) ≤ 1 := by
    have := hle f hfs
    omega
  have huniq : ∀ z ∈ N.displayedCluster c (N.graph.target f) ∩ q, z = x := fun z hz =>
    card_le_one.1 h1 z hz x (mem_inter.2 ⟨hfx, (mem_inter.1 hx).2⟩)
  obtain ⟨y, hy, hyx⟩ := exists_mem_ne (by omega : 1 < #(N.displayedCluster c w ∩ q)) x
  obtain ⟨g, -, hgs, hgy⟩ := exists_kept_child (mem_inter.1 hy).1 (hint y)
  have hfg : f ≠ g := by
    rintro rfl
    exact hyx (huniq y (mem_inter.2 ⟨hgy, (mem_inter.1 hy).2⟩))
  have hsub : (N.displayedCluster c w ∩ q).erase x ⊆ N.displayedCluster c (N.graph.target g) ∩ q := fun z hz => by
    obtain ⟨hzx, hz'⟩ := mem_erase.1 hz
    obtain ⟨hzc, hzq⟩ := mem_inter.1 hz'
    obtain ⟨k, -, hks, hkz⟩ := exists_kept_child hzc (hint z)
    rcases eq_or_eq_of_outdegree_le_two (outdegree_le_two hN hB w) hfs hgs hks hfg with rfl | rfl
    · exact absurd (huniq z (mem_inter.2 ⟨hkz, hzq⟩)) hzx
    · exact mem_inter.2 ⟨hkz, hzq⟩
  have hc := card_le_card hsub
  rw [card_erase_of_mem hx] at hc
  have := hle g hgs
  exact exists_displays_of_card_inter (v := N.graph.target g) hq (by omega)

end Binary

/-! ### Near the boundary -/

section Near

/-- The score of a tree is continuous along a family of continuous weights. -/
theorem continuous_quartetScore {Y : Type*} [TopologicalSpace Y] {p : Y → QuartetTree X → ℝ}
    (hp : ∀ r, Continuous fun y => p y r) (T : Finset (Finset X)) : Continuous fun y => quartetSupport (p y) T := by
  unfold quartetSupport
  refine continuous_finsetSum _ fun s _ => ?_
  split_ifs
  · exact hp s
  · exact continuous_const

omit [Fintype V] [Fintype E] in
/-- A tree that is not optimal has a smaller score than an optimal one. -/
theorem lt_of_not_isMQSOptimal {p : QuartetTree X → ℝ} {T S : Finset (Finset X)} (hT : IsUnrootedTree T)
    (hS : IsMQSOptimal p S) (h : ¬ IsMQSOptimal p T) : quartetSupport p T < quartetSupport p S := by
  by_contra hc
  push Not at hc
  exact h ⟨hT, fun T' hT' => (hS.2 T' hT').trans hc⟩

omit [Fintype V] [Fintype E] in
/-- **The continuity argument**: there are finitely many trees, so what holds of all optimal trees at a point holds of
all optimal trees at nearby points. -/
theorem eventually_forall_imp {Y : Type*} [TopologicalSpace Y] {p : Y → QuartetTree X → ℝ}
    (hp : ∀ r, Continuous fun y => p y r) (y₀ : Y) {T₀ : Finset (Finset X)} (hT₀ : IsUnrootedTree T₀)
    {G : Finset (Finset X) → Prop} (h : ∀ T, IsMQSOptimal (p y₀) T → G T) :
    ∀ᶠ y in 𝓝 y₀, ∀ T, IsMQSOptimal (p y) T → G T := by
  obtain ⟨S, hS, hmax⟩ := exists_max_quartetSupport hT₀ (p y₀)
  have hev : ∀ T, ∀ᶠ y in 𝓝 y₀, IsUnrootedTree T → ¬ G T → quartetSupport (p y) T < quartetSupport (p y) S := fun T => by
    by_cases hc : IsUnrootedTree T ∧ ¬ G T
    · have hlt := lt_of_not_isMQSOptimal hc.1 ⟨hS, hmax⟩ fun hopt => hc.2 (h T hopt)
      filter_upwards [((continuous_quartetScore hp T).tendsto y₀).eventually_lt
        ((continuous_quartetScore hp S).tendsto y₀) hlt] with y hy _ _ using hy
    · exact Eventually.of_forall fun y h₁ h₂ => absurd ⟨h₁, h₂⟩ hc
  filter_upwards [eventually_all.2 hev] with y hy T hopt
  by_contra hG
  exact absurd (hopt.2 S hS) (not_le.2 (hy T hopt.1 hG))

omit [Fintype V] [Fintype E] in
/-- Two parameters with the same lengths and the same inheritance are equal. -/
private theorem metricData_ext {θ θ' : MetricData E} (h₁ : θ.length = θ'.length) (h₂ : θ.inheritance = θ'.inheritance) :
    θ = θ' := by
  cases θ
  cases θ'
  simp_all

/-- The parent arcs of a choice, as the left-out coordinates. -/
def choiceCoords (hN : N.IsPhylogenetic) (c : N.ParentChoice) : V → E := fun v =>
  if h : v ≠ N.root then (c ⟨v, h⟩).val else (nonempty_arcs hN).some

omit [Fintype V] [Fintype E] [DecidableEq X] [Fintype X] in
theorem choiceCoords_of_ne (hN : N.IsPhylogenetic) (c : N.ParentChoice) {v : V} (h : v ≠ N.root) :
    choiceCoords hN c v = (c ⟨v, h⟩).val :=
  dite_eq_left h

omit [Fintype V] [Fintype E] [DecidableEq X] [Fintype X] in
/-- A vertex with two parents is not the root. -/
theorem ne_root_of_two_le_indegree (hN : N.IsPhylogenetic) {v : V} (hv : 2 ≤ N.graph.indegree v) : v ≠ N.root := by
  rintro rfl
  have := hN.root_indegree
  omega

omit [Fintype V] [DecidableEq X] [Fintype X] [Fintype E] in
theorem isParentChoice_choiceCoords [Fintype V] [Fintype E] (hN : N.IsPhylogenetic) (c : N.ParentChoice) :
    IsParentChoice N (choiceCoords hN c) := fun v hv => by
  have hr := ne_root_of_two_le_indegree hN hv
  rw [choiceCoords_of_ne hN c hr]
  exact (c ⟨v, hr⟩).property

omit [Fintype V] [Fintype X] [DecidableEq X] in
/-- **The boundary**: the coordinates with all free inheritance `0` are the parameters of the parent choice. -/
theorem coordMetric_choiceCoords_zero (hN : N.IsPhylogenetic) (c : N.ParentChoice) (ℓ γ : E → ℝ) :
    coordMetric N (choiceCoords hN c) ℓ 0 = N.choiceMetric ⟨ℓ, γ⟩ c := by
  refine metricData_ext rfl (funext fun e => ?_)
  by_cases he : N.IsHybridArc e
  · have hr := ne_root_of_two_le_indegree hN he
    by_cases hde : e = choiceCoords hN c (N.graph.target e)
    · rw [coordMetric_inheritance_of_eq he hde]
      have hkey : ∀ f, f = (c ⟨N.graph.target e, hr⟩).val → (N.choiceMetric ⟨ℓ, γ⟩ c).inheritance f = 1 := by
        rintro f rfl
        exact choiceMetric_inheritance_choice _ c _
      rw [hkey e (hde.trans (choiceCoords_of_ne hN c hr))]
      simp
    · rw [coordMetric_inheritance_of_ne he hde, choiceMetric_inheritance_of_mem _
        (mem_deletedArcs_of_ne (v := ⟨N.graph.target e, hr⟩) rfl
          fun h => hde (h.trans (choiceCoords_of_ne hN c hr).symm))]
      rfl
  · rw [coordMetric_inheritance_of_not_isHybridArc he]
    exact (ite_eq_right fun hm => he ((isDeletion_deletedArcs hN c).hybrid e hm)).symm

/-- The concordance factors are continuous in the coordinates. -/
theorem continuous_nmscCF_coordMetric (d : V → E) (ρ : ℝ) (r : QuartetTree X) :
    Continuous fun x : (E → ℝ) × (E → ℝ) => nmscCF N (coordMetric N d x.1 x.2) ρ r :=
  continuousOn_univ.1 (analyticOnNhd_nmscCF_coordMetric N d ρ r).continuousOn

/-- **Observation (2) of lines 363-369, on an open set**: near a parent choice, in the coordinates, every optimal tree
is a binary resolution of the displayed tree. -/
theorem eventually_forall_isMQSOptimal_imp [Nonempty X] (hN : N.IsPhylogenetic) (c : N.ParentChoice)
    (hρ : 0 ≤ ρ ∧ ρ ≤ 1) {ℓ : E → ℝ} (hℓ : ∀ e, 0 ≤ ℓ e) (hE : HasPositiveEdges ⟨ℓ, 0⟩ c) :
    ∀ᶠ x in 𝓝 (ℓ, (0 : E → ℝ)), ∀ T,
      IsMQSOptimal (nmscCF N (coordMetric N (choiceCoords hN c) x.1 x.2) ρ) T →
        IsBinaryTree T ∧ N.displayedSides c ⊆ T := by
  refine eventually_forall_imp (p := fun x : (E → ℝ) × (E → ℝ) => nmscCF N (coordMetric N (choiceCoords hN c) x.1 x.2) ρ)
    (fun r => continuous_nmscCF_coordMetric _ ρ r) _ (isUnrootedTree_displayedSides hN c) fun T h => ?_
  change IsMQSOptimal (nmscCF N (coordMetric N (choiceCoords hN c) ℓ 0) ρ) T at h
  rw [coordMetric_choiceCoords_zero hN c ℓ 0] at h
  exact (isMQSOptimal_choiceMetric_iff (θ := ⟨ℓ, 0⟩) hN c hρ hℓ hE T).1 h

/-- **Observation (2), when the displayed tree is binary**: near a parent choice, the displayed tree is the unique
optimal tree. -/
theorem eventually_isMQSOptimal_iff_eq [Nonempty X] (hN : N.IsPhylogenetic) (c : N.ParentChoice)
    (hρ : 0 ≤ ρ ∧ ρ ≤ 1) {ℓ : E → ℝ} (hℓ : ∀ e, 0 ≤ ℓ e) (hE : HasPositiveEdges ⟨ℓ, 0⟩ c)
    (hU : IsBinaryTree (N.displayedSides c)) :
    ∀ᶠ x in 𝓝 (ℓ, (0 : E → ℝ)), ∀ T,
      IsMQSOptimal (nmscCF N (coordMetric N (choiceCoords hN c) x.1 x.2) ρ) T ↔ T = N.displayedSides c := by
  filter_upwards [eventually_forall_isMQSOptimal_imp hN c hρ hℓ hE] with x hx T
  constructor
  · intro hopt
    have h := hx T hopt
    exact eq_of_isBinaryTree_of_subset hU h.1.isUnrootedTree h.2
  · rintro rfl
    obtain ⟨S, hS, hmax⟩ := exists_max_quartetSupport hU.isUnrootedTree
      (nmscCF N (coordMetric N (choiceCoords hN c) x.1 x.2) ρ)
    have hS' := hx S ⟨hS, hmax⟩
    rw [← eq_of_isBinaryTree_of_subset hU hS hS'.2]
    exact ⟨hS, hmax⟩

/-- **Observation (2) on a binary network, for all valid lengths**: near each parent choice, its displayed tree is the
unique optimal tree. Hybrid arcs of length `0` are allowed. -/
theorem isBinary_eventually_isMQSOptimal_iff_eq [Nonempty X] (hN : N.IsPhylogenetic) (hB : N.IsBinary)
    (c : N.ParentChoice) (hρ : 0 ≤ ρ ∧ ρ ≤ 1) {ℓ : E → ℝ} (hℓ : ∀ e, 0 ≤ ℓ e) (hℓ' : ∀ e, N.IsTreeArc e → 0 < ℓ e) :
    ∀ᶠ x in 𝓝 (ℓ, (0 : E → ℝ)), ∀ T,
      IsMQSOptimal (nmscCF N (coordMetric N (choiceCoords hN c) x.1 x.2) ρ) T ↔ T = N.displayedSides c :=
  eventually_isMQSOptimal_iff_eq hN c hρ hℓ (hasPositiveEdges_of_isBinary hN hB c hℓ')
    (isBinaryTree_displayedSides_of_isBinary hN hB c)

end Near

/-! ### Positive measure -/

section Measure

omit [Fintype V] [Fintype X] [DecidableEq X] in
/-- The coordinates give valid parameters, for free inheritance positive and of sum less than one, with any number of
parents at a reticulation. -/
theorem isMetric_coordMetric_of_sum_lt' {d : V → E} (hd : IsParentChoice N d) {ℓ g : E → ℝ}
    (hℓ : ∀ e, N.IsTreeArc e → 0 < ℓ e) (hℓ' : ∀ e, N.IsHybridArc e → 0 ≤ ℓ e) (hg : ∀ e, 0 < g e)
    (hs : ∑ e, g e < 1) : N.IsMetric (coordMetric N d ℓ g) := by
  refine ⟨hℓ, hℓ', fun e he => coordMetric_inheritance_of_isTreeArc he,
    fun e he => ?_, fun v hv => sum_coordMetric_inheritance hd hv⟩
  by_cases hde : e = d (N.graph.target e)
  · rw [coordMetric_inheritance_of_eq he hde, sub_pos]
    exact (sum_le_sum_of_subset_of_nonneg (subset_univ _) fun f _ _ => (hg f).le).trans_lt hs
  · rw [coordMetric_inheritance_of_ne he hde]
    exact hg e

omit [Fintype V] [Fintype X] [DecidableEq X] in
/-- The coordinates give valid parameters, with all lengths positive. -/
theorem isMetric_coordMetric_of_sum_lt {d : V → E} (hd : IsParentChoice N d) {ℓ g : E → ℝ}
    (hℓ : ∀ e, 0 < ℓ e) (hg : ∀ e, 0 < g e) (hs : ∑ e, g e < 1) : N.IsMetric (coordMetric N d ℓ g) :=
  isMetric_coordMetric_of_sum_lt' hd (fun e _ => hℓ e) (fun e _ => (hℓ e).le) hg hs

/-- Each factor of the measure of §5.1 on lengths charges an interval with positive points. -/
theorem lengthMeasure_Ioo_ne_zero_of_pos (hybrid : Prop) {a b : ℝ} (hab : a < b) (hb : 0 < b) :
    lengthMeasure hybrid (Set.Ioo a b) ≠ 0 := by
  have hlt : max a 0 < b := max_lt hab hb
  have hvol : ∀ S : Set ℝ, Set.Ioo (max a 0) b ⊆ S → (volume.restrict S) (Set.Ioo a b) ≠ 0 := by
    intro S hS h0
    have := measure_mono_null (Set.Ioo_subset_Ioo_left (le_max_left a 0)) h0
    rw [Measure.restrict_apply measurableSet_Ioo, Set.inter_eq_left.2 hS, Real.volume_Ioo,
      ENNReal.ofReal_eq_zero] at this
    linarith
  unfold lengthMeasure
  split_ifs
  · rw [Measure.add_apply]
    exact fun h => hvol _ (fun x hx => Set.mem_Ici.2 ((le_max_right a 0).trans hx.1.le)) (add_eq_zero.1 h).2
  · exact hvol _ fun x hx => Set.mem_Ioi.2 ((le_max_right a 0).trans_lt hx.1)

omit [Fintype V] [Fintype X] [DecidableEq X] in
/-- **A set of parameters containing all those near a boundary point is not null**, for the measure of §5.1 and in the
coordinates of `IsGenericNull`. -/
theorem not_null_of_eventually {d : V → E} (hd : IsParentChoice N d) {ℓ : E → ℝ} (hℓ : ∀ e, 0 < ℓ e)
    {A : Set (MetricData E)} (h : ∀ᶠ x in 𝓝 (ℓ, (0 : E → ℝ)), coordMetric N d x.1 x.2 ∈ A) :
    ¬ IsNullParams N A ∧ ¬ IsGenericNull N A := by
  have h₁ : ∀ᶠ x : (E → ℝ) × (E → ℝ) in 𝓝 (ℓ, (0 : E → ℝ)), ∀ e, 0 < x.1 e := eventually_all.2 fun e =>
    (((continuous_apply e).comp continuous_fst).tendsto (ℓ, (0 : E → ℝ))).eventually_const_lt (hℓ e)
  have h₂ : ∀ᶠ x : (E → ℝ) × (E → ℝ) in 𝓝 (ℓ, (0 : E → ℝ)), ∑ e, |x.2 e| < 1 := by
    have hc : Continuous fun x : (E → ℝ) × (E → ℝ) => ∑ e, |x.2 e| :=
      continuous_finsetSum _ fun e _ => ((continuous_apply e).comp continuous_snd).abs
    refine (hc.tendsto (ℓ, (0 : E → ℝ))).eventually_lt_const ?_
    simp
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.1 (h.and (h₁.and h₂))
  set η := min δ 1 with hη
  have hη0 : 0 < η := lt_min hδ one_pos
  have hηδ : η ≤ δ := min_le_left _ _
  have hη1 : η ≤ 1 := min_le_right _ _
  have hmem : ∀ x ∈ (Set.pi Set.univ fun e => Set.Ioo (ℓ e - η) (ℓ e + η)) ×ˢ
      (Set.pi Set.univ fun _ : E => Set.Ioo (0 : ℝ) η),
      coordMetric N d x.1 x.2 ∈ A ∧ N.IsMetric (coordMetric N d x.1 x.2) := by
    rintro ⟨l, g⟩ ⟨hl, hg⟩
    have hl' : ∀ e, l e ∈ Set.Ioo (ℓ e - η) (ℓ e + η) := fun e => hl e (Set.mem_univ e)
    have hg' : ∀ e, g e ∈ Set.Ioo (0 : ℝ) η := fun e => hg e (Set.mem_univ e)
    have hdist : dist (l, g) (ℓ, (0 : E → ℝ)) < δ := by
      rw [Prod.dist_eq, max_lt_iff, dist_pi_lt_iff hδ, dist_pi_lt_iff hδ]
      refine ⟨fun e => ?_, fun e => ?_⟩
      · rw [Real.dist_eq, abs_lt]
        have := hl' e
        constructor <;> linarith [this.1, this.2]
      · change dist (g e) 0 < δ
        rw [Real.dist_eq, sub_zero, abs_lt]
        have := hg' e
        constructor <;> linarith [this.1, this.2]
    obtain ⟨hA, hpos, hsum⟩ := hball hdist
    refine ⟨hA, isMetric_coordMetric_of_sum_lt hd hpos (fun e => (hg' e).1) ?_⟩
    exact (sum_le_sum fun e _ => le_abs_self _).trans_lt hsum
  constructor
  · intro hnull
    have hbox : (Set.pi Set.univ fun e => Set.Ioo (ℓ e - η) (ℓ e + η)) ×ˢ
        (Set.pi Set.univ fun _ : E => Set.Ioo (0 : ℝ) η) ⊆
        {x : (E → ℝ) × (E → ℝ) | N.IsMetric (coordMetric N d x.1 x.2) ∧ coordMetric N d x.1 x.2 ∈ A} :=
      fun x hx => ⟨(hmem x hx).2, (hmem x hx).1⟩
    have hz := measure_mono_null hbox (hnull d hd)
    rw [Measure.prod_prod, Measure.pi_pi, Measure.pi_pi, mul_eq_zero, prod_eq_zero_iff, prod_eq_zero_iff] at hz
    rcases hz with ⟨e, -, he⟩ | ⟨e, -, he⟩
    · exact lengthMeasure_Ioo_ne_zero_of_pos _ (by linarith) (by linarith [hℓ e]) he
    · rw [Measure.restrict_apply measurableSet_Ioo, Set.inter_eq_left.2 (Set.Ioo_subset_Ioo_right hη1),
        Real.volume_Ioo, ENNReal.ofReal_eq_zero] at he
      linarith
  · intro hnull
    have hbox : (Set.pi Set.univ fun e => Set.Ioo (ℓ e - η) (ℓ e + η)) ×ˢ
        (Set.pi Set.univ fun _ : E => Set.Ioo (0 : ℝ) η) ⊆
        {x : (E → ℝ) × (E → ℝ) | ∃ θ ∈ A, N.IsMetric θ ∧ θ.length = x.1 ∧
          ∀ e, N.IsHybridArc e → e ≠ d (N.graph.target e) → θ.inheritance e = x.2 e} :=
      fun x hx => ⟨coordMetric N d x.1 x.2, (hmem x hx).1, (hmem x hx).2, rfl,
        fun e he hde => coordMetric_inheritance_of_ne he hde⟩
    have hz := measure_mono_null hbox (hnull d hd)
    rw [Measure.prod_prod, Measure.pi_pi, Measure.pi_pi, mul_eq_zero, prod_eq_zero_iff, prod_eq_zero_iff] at hz
    rcases hz with ⟨e, -, he⟩ | ⟨e, -, he⟩
    · rw [Real.volume_Ioo, ENNReal.ofReal_eq_zero] at he
      linarith
    · rw [Real.volume_Ioo, ENNReal.ofReal_eq_zero] at he
      linarith

/-- **Observation (2) of lines 363-369, positive measure**: for every network and every parent choice, the set of valid
parameters at which every optimal tree is a binary resolution of the displayed tree is not null. No hypothesis on the
network or on the displayed tree is needed: lengths are positive near the point used. -/
theorem not_isNull_resolvesDisplayed [Nonempty X] (hN : N.IsPhylogenetic) (c : N.ParentChoice) (hρ : 0 ≤ ρ ∧ ρ ≤ 1) :
    ¬ IsNullParams N {θ | ∀ T, IsMQSOptimal (nmscCF N θ ρ) T → IsBinaryTree T ∧ N.displayedSides c ⊆ T} ∧
      ¬ IsGenericNull N {θ | ∀ T, IsMQSOptimal (nmscCF N θ ρ) T → IsBinaryTree T ∧ N.displayedSides c ⊆ T} :=
  not_null_of_eventually (isParentChoice_choiceCoords hN c) (ℓ := fun _ => 1) (fun _ => one_pos)
    (eventually_forall_isMQSOptimal_imp hN c hρ (fun _ => zero_le_one)
      (hasPositiveEdges_of_pos hN c fun _ => one_pos))

/-- **Observation (2), positive measure, literally**: when the displayed tree of a parent choice is binary, the set of
valid parameters at which MQS selects exactly it is not null. -/
theorem not_isNull_selectsDisplayed [Nonempty X] (hN : N.IsPhylogenetic) (c : N.ParentChoice) (hρ : 0 ≤ ρ ∧ ρ ≤ 1)
    (hU : IsBinaryTree (N.displayedSides c)) :
    ¬ IsNullParams N {θ | ∀ T, IsMQSOptimal (nmscCF N θ ρ) T ↔ T = N.displayedSides c} ∧
      ¬ IsGenericNull N {θ | ∀ T, IsMQSOptimal (nmscCF N θ ρ) T ↔ T = N.displayedSides c} :=
  not_null_of_eventually (isParentChoice_choiceCoords hN c) (ℓ := fun _ => 1) (fun _ => one_pos)
    (eventually_isMQSOptimal_iff_eq hN c hρ (fun _ => zero_le_one)
      (hasPositiveEdges_of_pos hN c fun _ => one_pos) hU)

end Measure

/-! ### Ties -/

section Tie

/-- The segment between two parameter points. -/
def lineMetric (θ₀ θ₁ : MetricData E) (t : ℝ) : MetricData E where
  length e := (1 - t) * θ₀.length e + t * θ₁.length e
  inheritance e := (1 - t) * θ₀.inheritance e + t * θ₁.inheritance e

omit [Fintype V] in
private theorem convex_pos {a b t : ℝ} (ha : 0 < a) (hb : 0 < b) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    0 < (1 - t) * a + t * b := by
  rcases ht.1.eq_or_lt with rfl | h
  · simpa using ha
  · have h₁ := mul_pos h hb
    have h₂ := mul_nonneg (sub_nonneg.2 ht.2) ha.le
    linarith

omit [Fintype V] [Fintype X] [DecidableEq X] in
/-- **The segment between two valid parameter points is valid.** -/
theorem isMetric_lineMetric {θ₀ θ₁ : MetricData E} (h₀ : N.IsMetric θ₀) (h₁ : N.IsMetric θ₁) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1) : N.IsMetric (lineMetric θ₀ θ₁ t) := by
  refine ⟨fun e he => convex_pos (h₀.1 e he) (h₁.1 e he) ht, fun e he => ?_, fun e he => ?_,
    fun e he => convex_pos (h₀.2.2.2.1 e he) (h₁.2.2.2.1 e he) ht, fun v hv => ?_⟩
  · exact add_nonneg (mul_nonneg (sub_nonneg.2 ht.2) (h₀.2.1 e he)) (mul_nonneg ht.1 (h₁.2.1 e he))
  · change (1 - t) * θ₀.inheritance e + t * θ₁.inheritance e = 1
    rw [h₀.2.2.1 e he, h₁.2.2.1 e he]
    ring
  · have hs : (∑ e, if N.graph.target e = v then (lineMetric θ₀ θ₁ t).inheritance e else 0) =
        (1 - t) * (∑ e, if N.graph.target e = v then θ₀.inheritance e else 0) +
          t * ∑ e, if N.graph.target e = v then θ₁.inheritance e else 0 := by
      rw [mul_sum, mul_sum, ← sum_add_distrib]
      refine sum_congr rfl fun e _ => ?_
      split_ifs
      · rfl
      · ring
    rw [hs, h₀.2.2.2.2 v hv, h₁.2.2.2.2 v hv]
    ring

omit [Fintype V] [Fintype E] in
theorem lineMetric_zero (θ₀ θ₁ : MetricData E) : lineMetric θ₀ θ₁ 0 = θ₀ :=
  metricData_ext (funext fun e => by simp [lineMetric]) (funext fun e => by simp [lineMetric])

omit [Fintype V] [Fintype E] in
theorem lineMetric_one (θ₀ θ₁ : MetricData E) : lineMetric θ₀ θ₁ 1 = θ₁ :=
  metricData_ext (funext fun e => by simp [lineMetric]) (funext fun e => by simp [lineMetric])

omit [Fintype V] [Fintype E] in
/-- **The argument of observation (3)**, for continuous weights on `[0, 1]`: if a tree is optimal at `0` and not at `1`,
then at the last point where it is optimal, another tree is optimal too. At that point the other trees cannot all be
strictly smaller, as that would persist to the right. -/
theorem exists_tie_on_segment {p : ℝ → QuartetTree X → ℝ} (hp : ∀ r, Continuous fun t => p t r)
    {T₀ : Finset (Finset X)} (h₀ : IsMQSOptimal (p 0) T₀) (h₁ : ¬ IsMQSOptimal (p 1) T₀) :
    ∃ t ∈ Set.Ico (0 : ℝ) 1, IsMQSOptimal (p t) T₀ ∧ ∃ T, T ≠ T₀ ∧ IsMQSOptimal (p t) T := by
  have hT₀ := h₀.1
  set A : Set ℝ := {t | t ∈ Set.Icc (0 : ℝ) 1 ∧ IsMQSOptimal (p t) T₀} with hA
  have hAeq : A = Set.Icc (0 : ℝ) 1 ∩ ⋂ T', ⋂ (_ : IsUnrootedTree T'), {t | quartetSupport (p t) T' ≤ quartetSupport (p t) T₀} := by
    ext t
    simp only [hA, Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_iInter, IsMQSOptimal, and_iff_right hT₀]
  have hclosed : IsClosed A := by
    rw [hAeq]
    exact isClosed_Icc.inter (isClosed_iInter fun T' => isClosed_iInter fun _ =>
      isClosed_le (continuous_quartetScore hp T') (continuous_quartetScore hp T₀))
  have hne : A.Nonempty := ⟨0, ⟨le_rfl, zero_le_one⟩, h₀⟩
  have hbdd : BddAbove A := ⟨1, fun t ht => ht.1.2⟩
  have hmem : sSup A ∈ A := hclosed.csSup_mem hne hbdd
  have hlt : sSup A < 1 := by
    refine lt_of_le_of_ne hmem.1.2 fun h => h₁ ?_
    have h2 := hmem.2
    rwa [h] at h2
  refine ⟨sSup A, ⟨hmem.1.1, hlt⟩, hmem.2, ?_⟩
  by_contra hno
  push Not at hno
  have hstrict : ∀ T, IsUnrootedTree T → T ≠ T₀ → quartetSupport (p (sSup A)) T < quartetSupport (p (sSup A)) T₀ :=
    fun T hT hTne => lt_of_not_isMQSOptimal hT hmem.2 (hno T hTne)
  have hev : ∀ T, ∀ᶠ t in 𝓝 (sSup A), IsUnrootedTree T → T ≠ T₀ → quartetSupport (p t) T < quartetSupport (p t) T₀ := by
    intro T
    by_cases hc : IsUnrootedTree T ∧ T ≠ T₀
    · filter_upwards [((continuous_quartetScore hp T).tendsto _).eventually_lt
        ((continuous_quartetScore hp T₀).tendsto _) (hstrict T hc.1 hc.2)] with t ht _ _ using ht
    · exact Eventually.of_forall fun t h₁ h₂ => absurd ⟨h₁, h₂⟩ hc
  have hev' : ∀ᶠ t in 𝓝[>] (sSup A), ∀ T, IsUnrootedTree T → T ≠ T₀ →
      quartetSupport (p t) T < quartetSupport (p t) T₀ := nhdsWithin_le_nhds (eventually_all.2 hev)
  obtain ⟨t, htP, ht⟩ := (hev'.and (Ioo_mem_nhdsGT hlt)).exists
  have htA : t ∈ A := by
    refine ⟨⟨hmem.1.1.trans ht.1.le, ht.2.le⟩, hT₀, fun T' hT' => ?_⟩
    by_cases h : T' = T₀
    · rw [h]
    · exact (htP T' hT' h).le
  exact absurd (le_csSup hbdd htA) (not_le.2 ht.1)

/-- The concordance factors are continuous along a segment. -/
theorem continuous_nmscCF_lineMetric (θ₀ θ₁ : MetricData E) (ρ : ℝ) (r : QuartetTree X) :
    Continuous fun t : ℝ => nmscCF N (lineMetric θ₀ θ₁ t) ρ r := by
  refine continuousOn_univ.1 (analyticOnNhd_nmscCF N (θ := fun t => lineMetric θ₀ θ₁ t) ρ
    (fun e => ?_) (fun e => ?_) r).continuousOn
  · exact ((analyticOnNhd_const.sub analyticOnNhd_id).mul analyticOnNhd_const).add
      (analyticOnNhd_id.mul analyticOnNhd_const)
  · exact ((analyticOnNhd_const.sub analyticOnNhd_id).mul analyticOnNhd_const).add
      (analyticOnNhd_id.mul analyticOnNhd_const)

/-- **Observation (3) of lines 363-369**: on the segment between two valid parameter points with different unique optimal
trees, there is a valid point, in the interior, with two optimal trees. -/
theorem exists_tie_of_unique_maximizers {θ₀ θ₁ : MetricData E} (h₀ : N.IsMetric θ₀) (h₁ : N.IsMetric θ₁)
    {T₀ T₁ : Finset (Finset X)} (hT₀ : ∀ T, IsMQSOptimal (nmscCF N θ₀ ρ) T ↔ T = T₀)
    (hT₁ : ∀ T, IsMQSOptimal (nmscCF N θ₁ ρ) T ↔ T = T₁) (hne : T₀ ≠ T₁) :
    ∃ t ∈ Set.Ioo (0 : ℝ) 1, N.IsMetric (lineMetric θ₀ θ₁ t) ∧ ∃ T T', T ≠ T' ∧
      IsMQSOptimal (nmscCF N (lineMetric θ₀ θ₁ t) ρ) T ∧ IsMQSOptimal (nmscCF N (lineMetric θ₀ θ₁ t) ρ) T' := by
  have hz : IsMQSOptimal (nmscCF N (lineMetric θ₀ θ₁ 0) ρ) T₀ := by
    rw [lineMetric_zero]
    exact (hT₀ T₀).2 rfl
  have ho : ¬ IsMQSOptimal (nmscCF N (lineMetric θ₀ θ₁ 1) ρ) T₀ := by
    rw [lineMetric_one]
    exact fun h => hne ((hT₁ T₀).1 h)
  obtain ⟨t, ht, hopt, T, hT, hoptT⟩ := exists_tie_on_segment
    (p := fun t => nmscCF N (lineMetric θ₀ θ₁ t) ρ) (fun r => continuous_nmscCF_lineMetric θ₀ θ₁ ρ r) hz ho
  have htpos : 0 < t := by
    refine lt_of_le_of_ne ht.1 ?_
    rintro rfl
    rw [lineMetric_zero] at hoptT
    exact hT ((hT₀ T).1 hoptT)
  exact ⟨t, ⟨htpos, ht.2⟩, isMetric_lineMetric h₀ h₁ ⟨ht.1, ht.2.le⟩, T, T₀, hT, hoptT, hopt⟩

omit [Fintype V] [Fintype X] [DecidableEq X] in
/-- Small constant free inheritance has sum less than one. -/
theorem eventually_sum_const_lt_one : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∑ _e : E, ε < 1 := by
  have hc : Continuous fun ε : ℝ => ∑ _e : E, ε := continuous_finsetSum _ fun _ _ => continuous_id
  refine ((hc.tendsto 0).mono_left nhdsWithin_le_nhds).eventually_lt_const ?_
  simp

omit [Fintype V] [Fintype X] [DecidableEq X] in
/-- A statement holding near a boundary point holds at a valid point with the same lengths. -/
theorem exists_coord_of_eventually {d : V → E} (hd : IsParentChoice N d) {ℓ : E → ℝ} (hℓ : ∀ e, 0 < ℓ e)
    {P : MetricData E → Prop} (h : ∀ᶠ x in 𝓝 (ℓ, (0 : E → ℝ)), P (coordMetric N d x.1 x.2)) :
    ∃ g, N.IsMetric (coordMetric N d ℓ g) ∧ P (coordMetric N d ℓ g) := by
  have hφ : Tendsto (fun ε : ℝ => (ℓ, fun _ : E => ε)) (𝓝[>] 0) (𝓝 (ℓ, (0 : E → ℝ))) := by
    have hc : Continuous fun ε : ℝ => (ℓ, fun _ : E => ε) := continuous_const.prodMk (continuous_pi fun _ => continuous_id)
    exact (hc.tendsto 0).mono_left nhdsWithin_le_nhds
  obtain ⟨ε, ⟨hP, hs⟩, hε⟩ := (((hφ.eventually h).and (eventually_sum_const_lt_one (E := E))).and self_mem_nhdsWithin).exists
  exact ⟨fun _ => ε, isMetric_coordMetric_of_sum_lt hd hℓ (fun _ => hε) hs, hP⟩

/-- **Observation (3), for any network and two parent choices with different binary displayed trees**: at any positive
lengths, there are valid inheritance probabilities with two optimal trees. Only the `γ`s vary along the segment. -/
theorem exists_tie_of_displayedTrees [Nonempty X] (hN : N.IsPhylogenetic) (c₁ c₂ : N.ParentChoice)
    (hρ : 0 ≤ ρ ∧ ρ ≤ 1) (hU₁ : IsBinaryTree (N.displayedSides c₁)) (hU₂ : IsBinaryTree (N.displayedSides c₂))
    (hne : N.displayedSides c₁ ≠ N.displayedSides c₂) {ℓ : E → ℝ} (hℓ : ∀ e, 0 < ℓ e) :
    ∃ θ, N.IsMetric θ ∧ θ.length = ℓ ∧ ∃ T T', T ≠ T' ∧
      IsMQSOptimal (nmscCF N θ ρ) T ∧ IsMQSOptimal (nmscCF N θ ρ) T' := by
  obtain ⟨g₁, hm₁, hopt₁⟩ := exists_coord_of_eventually
    (P := fun θ => ∀ T, IsMQSOptimal (nmscCF N θ ρ) T ↔ T = N.displayedSides c₁)
    (isParentChoice_choiceCoords hN c₁) hℓ
    (eventually_isMQSOptimal_iff_eq hN c₁ hρ (fun e => (hℓ e).le) (hasPositiveEdges_of_pos hN c₁ hℓ) hU₁)
  obtain ⟨g₂, hm₂, hopt₂⟩ := exists_coord_of_eventually
    (P := fun θ => ∀ T, IsMQSOptimal (nmscCF N θ ρ) T ↔ T = N.displayedSides c₂)
    (isParentChoice_choiceCoords hN c₂) hℓ
    (eventually_isMQSOptimal_iff_eq hN c₂ hρ (fun e => (hℓ e).le) (hasPositiveEdges_of_pos hN c₂ hℓ) hU₂)
  obtain ⟨t, -, hm, T, T', hTT, h, h'⟩ := exists_tie_of_unique_maximizers hm₁ hm₂ hopt₁ hopt₂ hne
  refine ⟨_, hm, funext fun e => ?_, T, T', hTT, h, h'⟩
  change (1 - t) * ℓ e + t * ℓ e = ℓ e
  ring

end Tie

/-! ### A network with two different displayed trees -/

section Example

open ECToBlob.Remark52 Phylogenetics.NMSC.Chain

/-- The vertices of the 4-cycle network: `h` is the reticulation, and `t`, `u`, `h`, `v` is the cycle. -/
inductive V₄ | r | t | u | v | h | a | b | c | d
  deriving DecidableEq

instance : Fintype V₄ := ⟨{.r, .t, .u, .v, .h, .a, .b, .c, .d}, fun w => by cases w <;> decide⟩

/-- The arcs of the 4-cycle network: `uh`, `vh` enter the reticulation. -/
inductive E₄ | rd | rt | tu | tv | ua | uh | vc | vh | hb
  deriving DecidableEq

instance : Fintype E₄ := ⟨{.rd, .rt, .tu, .tv, .ua, .uh, .vc, .vh, .hb}, fun f => by cases f <;> decide⟩

/-- **The network with a 4-cycle**: the taxon `d` is outside the cycle, `a` hangs at `u`, `c` at `v`, and `b` at the
reticulation. Its displayed trees are `ab|cd` and `ad|bc`. -/
def fourCycle : RootedNetwork V₄ E₄ (Fin 4) where
  graph :=
    { source := fun
        | .rd => .r | .rt => .r | .tu => .t | .tv => .t | .ua => .u | .uh => .u | .vc => .v | .vh => .v | .hb => .h
      target := fun
        | .rd => .d | .rt => .t | .tu => .u | .tv => .v | .ua => .a | .uh => .h | .vc => .c | .vh => .h | .hb => .b }
  root := .r
  leaf := ![.a, .b, .c, .d]

/-- It is a phylogenetic network. -/
theorem isPhylogenetic_fourCycle : fourCycle.IsPhylogenetic := by
  refine isPhylogenetic_of_rank (fun | .r => 0 | .d => 1 | .t => 1 | .u => 2 | .v => 2 | .h => 3 | .a => 3 | .c => 3 | .b => 4)
    (fun f => by cases f <;> decide)
    (fun f => by cases f <;> decide) (fun w hw => ?_) ?_ (fun x => ?_) (fun x f => ?_) (fun w hw => ?_)
  · cases w
    · exact absurd rfl hw
    · exact ⟨.rt, rfl⟩
    · exact ⟨.tu, rfl⟩
    · exact ⟨.tv, rfl⟩
    · exact ⟨.uh, rfl⟩
    · exact ⟨.ua, rfl⟩
    · exact ⟨.hb, rfl⟩
    · exact ⟨.vc, rfl⟩
    · exact ⟨.rd, rfl⟩
  · decide
  · fin_cases x
    · exact ⟨.ua, rfl, fun f hf => by cases f <;> first | rfl | exact absurd hf (by decide)⟩
    · exact ⟨.hb, rfl, fun f hf => by cases f <;> first | rfl | exact absurd hf (by decide)⟩
    · exact ⟨.vc, rfl, fun f hf => by cases f <;> first | rfl | exact absurd hf (by decide)⟩
    · exact ⟨.rd, rfl, fun f hf => by cases f <;> first | rfl | exact absurd hf (by decide)⟩
  · fin_cases x <;> cases f <;> decide
  · cases w
    · exact ⟨.rd, rfl⟩
    · exact ⟨.tu, rfl⟩
    · exact ⟨.ua, rfl⟩
    · exact ⟨.vc, rfl⟩
    · exact ⟨.hb, rfl⟩
    · exact absurd rfl (hw 0)
    · exact absurd rfl (hw 1)
    · exact absurd rfl (hw 2)
    · exact absurd rfl (hw 3)

private theorem ncard_filter {α : Type*} [Fintype α] (p : α → Prop) [DecidablePred p] :
    {a | p a}.ncard = #(univ.filter p) := by
  rw [← Set.ncard_coe_finset]
  congr 1
  ext a
  simp

/-- It is binary. -/
theorem isBinary_fourCycle : fourCycle.IsBinary := by
  refine ⟨?_, fun w hw hout => ?_⟩
  · unfold DirectedMultigraph.outdegree
    rw [ncard_filter]
    decide
  · unfold DirectedMultigraph.outdegree at hout
    unfold DirectedMultigraph.indegree DirectedMultigraph.outdegree
    rw [ncard_filter] at hout
    rw [ncard_filter, ncard_filter]
    revert hw hout
    cases w <;> decide

/-- The parent arcs, with the parent `f` at the reticulation. -/
def parentOf (f : E₄) : V₄ → E₄
  | .r => .rd | .t => .rt | .u => .tu | .v => .tv | .h => f | .a => .ua | .b => .hb | .c => .vc | .d => .rd

/-- The parent choice that keeps `u → h`. -/
def choiceU : fourCycle.ParentChoice := fun w => ⟨parentOf .uh w.val, by
  obtain ⟨w, hw⟩ := w
  cases w <;> first | exact absurd rfl hw | rfl⟩

/-- The parent choice that keeps `v → h`. -/
def choiceV : fourCycle.ParentChoice := fun w => ⟨parentOf .vh w.val, by
  obtain ⟨w, hw⟩ := w
  cases w <;> first | exact absurd rfl hw | rfl⟩

omit [Fintype V] [Fintype E] [Fintype X] [DecidableEq X] in
/-- A set closed under the arcs of a network contains what its members reach. -/
theorem closed_of_reaches {S : V → Prop}
    (hS : ∀ f : E, S (N.graph.source f) → S (N.graph.target f)) {w w' : V}
    (hr : N.graph.Reaches w w') (hw : S w) : S w' := by
  induction hr with
  | refl => exact hw
  | tail _ h ih =>
    obtain ⟨f, hs, ht⟩ := h
    exact ht ▸ hS f (hs ▸ ih)

/-- The tree of `choiceU` displays `ab|cd`. -/
theorem displays_choiceU : Displays (fourCycle.displayedSides choiceU) abcd := by
  have hua : E₄.ua ∉ fourCycle.deletedArcs choiceU := notMem_deletedArcs_choice choiceU ⟨.a, by decide⟩
  have huh : E₄.uh ∉ fourCycle.deletedArcs choiceU := notMem_deletedArcs_choice choiceU ⟨.h, by decide⟩
  have hhb : E₄.hb ∉ fourCycle.deletedArcs choiceU := notMem_deletedArcs_choice choiceU ⟨.b, by decide⟩
  refine displays_of_cluster (P := {0, 1}) (u := V₄.u) (by simp [abcd]) (fun x hx => ?_) (fun x _ hxP hx => ?_)
  · rw [mem_insert, mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact mem_displayedCluster.2 (Relation.ReflTransGen.single ⟨.ua, hua, rfl, rfl⟩)
    · exact mem_displayedCluster.2 (Relation.ReflTransGen.head ⟨.uh, huh, rfl, rfl⟩
        (Relation.ReflTransGen.single ⟨.hb, hhb, rfl, rfl⟩))
  · have hc := closed_of_reaches (N := fourCycle) (S := fun w => w = .u ∨ w = .a ∨ w = .h ∨ w = .b)
      (fun f => by cases f <;> simp [fourCycle]) (mem_displayedCluster.1 hx).reaches (Or.inl rfl)
    revert hc hxP
    fin_cases x <;> simp [fourCycle]

/-- The tree of `choiceV` displays `ad|bc`. -/
theorem displays_choiceV : Displays (fourCycle.displayedSides choiceV) adbc := by
  have hvc : E₄.vc ∉ fourCycle.deletedArcs choiceV := notMem_deletedArcs_choice choiceV ⟨.c, by decide⟩
  have hvh : E₄.vh ∉ fourCycle.deletedArcs choiceV := notMem_deletedArcs_choice choiceV ⟨.h, by decide⟩
  have hhb : E₄.hb ∉ fourCycle.deletedArcs choiceV := notMem_deletedArcs_choice choiceV ⟨.b, by decide⟩
  refine displays_of_cluster (P := {1, 2}) (u := V₄.v) (by simp [adbc]) (fun x hx => ?_) (fun x _ hxP hx => ?_)
  · rw [mem_insert, mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact mem_displayedCluster.2 (Relation.ReflTransGen.head ⟨.vh, hvh, rfl, rfl⟩
        (Relation.ReflTransGen.single ⟨.hb, hhb, rfl, rfl⟩))
    · exact mem_displayedCluster.2 (Relation.ReflTransGen.single ⟨.vc, hvc, rfl, rfl⟩)
  · have hc := closed_of_reaches (N := fourCycle) (S := fun w => w = .v ∨ w = .c ∨ w = .h ∨ w = .b)
      (fun f => by cases f <;> simp [fourCycle]) (mem_displayedCluster.1 hx).reaches (Or.inl rfl)
    revert hc hxP
    fin_cases x <;> simp [fourCycle]

/-- **The two displayed trees of the 4-cycle network are different.** -/
theorem displayedSides_choiceU_ne : fourCycle.displayedSides choiceU ≠ fourCycle.displayedSides choiceV := by
  intro h
  have hd := displays_choiceV
  rw [← h] at hd
  have heq := (isUnrootedTree_displayedSides isPhylogenetic_fourCycle choiceU).displays_unique displays_choiceU hd
    ((taxa_eq_univ _).trans (taxa_eq_univ _).symm)
  exact absurd heq (by decide)

/-- **Observation (3), hypothesis-free, on the 4-cycle network**: for every inheritance correlation and all positive
lengths, there are valid inheritance probabilities with two optimal trees. -/
theorem fourCycle_exists_tie {ρ : ℝ} (hρ : 0 ≤ ρ ∧ ρ ≤ 1) {ℓ : E₄ → ℝ} (hℓ : ∀ e, 0 < ℓ e) :
    ∃ θ, fourCycle.IsMetric θ ∧ θ.length = ℓ ∧ ∃ T T', T ≠ T' ∧
      IsMQSOptimal (nmscCF fourCycle θ ρ) T ∧ IsMQSOptimal (nmscCF fourCycle θ ρ) T' :=
  exists_tie_of_displayedTrees isPhylogenetic_fourCycle choiceU choiceV hρ
    (isBinaryTree_displayedSides_of_isBinary isPhylogenetic_fourCycle isBinary_fourCycle _)
    (isBinaryTree_displayedSides_of_isBinary isPhylogenetic_fourCycle isBinary_fourCycle _)
    displayedSides_choiceU_ne hℓ

/-- **Observation (2), hypothesis-free, on the 4-cycle network**: each of the two different displayed trees is the unique
choice of MQS on a set of parameters of positive measure. -/
theorem fourCycle_not_isNull {ρ : ℝ} (hρ : 0 ≤ ρ ∧ ρ ≤ 1) (c : fourCycle.ParentChoice) :
    ¬ IsNullParams fourCycle {θ | ∀ T, IsMQSOptimal (nmscCF fourCycle θ ρ) T ↔ T = fourCycle.displayedSides c} ∧
      ¬ IsGenericNull fourCycle
        {θ | ∀ T, IsMQSOptimal (nmscCF fourCycle θ ρ) T ↔ T = fourCycle.displayedSides c} :=
  not_isNull_selectsDisplayed isPhylogenetic_fourCycle c hρ
    (isBinaryTree_displayedSides_of_isBinary isPhylogenetic_fourCycle isBinary_fourCycle c)

end Example

/-! ### Two generic steps -/

section Generic

/-- A value of the concordance factors at small positive coordinates is their value at the parent choice. -/
theorem nmscCF_choiceMetric_eq_of_eventually (hN : N.IsPhylogenetic) (c : N.ParentChoice) (ρ : ℝ) (ℓ γ : E → ℝ)
    (r : QuartetTree X) {a : ℝ}
    (hev : ∀ᶠ ε in 𝓝[>] (0 : ℝ), nmscCF N (coordMetric N (choiceCoords hN c) ℓ fun _ => ε) ρ r = a) :
    nmscCF N (N.choiceMetric ⟨ℓ, γ⟩ c) ρ r = a := by
  have hφ : Continuous fun ε : ℝ => ((ℓ, fun _ : E => ε) : (E → ℝ) × (E → ℝ)) :=
    continuous_const.prodMk (continuous_pi fun _ => continuous_id)
  have hcomp := (continuous_nmscCF_coordMetric (N := N) (choiceCoords hN c) ρ r).comp hφ
  have hcont : Continuous fun ε : ℝ => nmscCF N (coordMetric N (choiceCoords hN c) ℓ fun _ => ε) ρ r := hcomp
  have hlim := (hcont.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))
  have hval := tendsto_nhds_unique hlim (tendsto_const_nhds.congr' (hev.mono fun _ h => h.symm))
  rw [← coordMetric_choiceCoords_zero hN c ℓ γ]
  exact hval

omit [Fintype V] [Fintype E] [Fintype X] [DecidableEq X] in
/-- The atom of the measure of §5.1 at length `0` of a hybrid arc. -/
theorem lengthMeasure_singleton_zero_ne_zero {hybrid : Prop} (h : hybrid) : lengthMeasure hybrid {0} ≠ 0 := by
  unfold lengthMeasure
  rw [ite_eq_left h, Measure.add_apply, Measure.dirac_apply' _ (measurableSet_singleton 0)]
  simp

omit [Fintype V] [Fintype X] [DecidableEq X] in
/-- A set of parameters containing a box charged by the measure of §5.1 is not null. -/
theorem not_isNullParams_of_box {d : V → E} (hd : IsParentChoice N d) {A : Set (MetricData E)} {L : E → Set ℝ} {η : ℝ}
    (hη₀ : 0 < η) (hη₁ : η ≤ 1) (hL : ∀ e, lengthMeasure (N.IsHybridArc e) (L e) ≠ 0)
    (h : ∀ l g : E → ℝ, (∀ e, l e ∈ L e) → (∀ e, g e ∈ Set.Ioo (0 : ℝ) η) →
      N.IsMetric (coordMetric N d l g) ∧ coordMetric N d l g ∈ A) : ¬ IsNullParams N A := by
  intro hnull
  have hbox : (Set.pi Set.univ L) ×ˢ (Set.pi Set.univ fun _ : E => Set.Ioo (0 : ℝ) η) ⊆
      {x : (E → ℝ) × (E → ℝ) | N.IsMetric (coordMetric N d x.1 x.2) ∧ coordMetric N d x.1 x.2 ∈ A} := by
    rintro ⟨l, g⟩ ⟨hl, hg⟩
    exact h l g (fun e => hl e (Set.mem_univ e)) fun e => hg e (Set.mem_univ e)
  have hz := measure_mono_null hbox (hnull d hd)
  rw [Measure.prod_prod, Measure.pi_pi, Measure.pi_pi, mul_eq_zero, prod_eq_zero_iff, prod_eq_zero_iff] at hz
  rcases hz with ⟨e, -, he⟩ | ⟨e, -, he⟩
  · exact hL e he
  · rw [Measure.restrict_apply measurableSet_Ioo, Set.inter_eq_left.2 (Set.Ioo_subset_Ioo_right hη₁),
      Real.volume_Ioo, ENNReal.ofReal_eq_zero] at he
    linarith

end Generic

/-! ### Zero lengths: the hypothesis `HasPositiveEdges` is needed -/

section ZeroLength

open ECToBlob.Remark52 Phylogenetics.NMSC.Chain ECToBlob.Remark33Counterexample

/-- The parent choice of the network `N₁` of Figure 1 that keeps the arc `e₁` of the two parallel arcs. -/
def choiceE₁ : N₁.ParentChoice := fun p => ⟨match p.val with
    | .r => .a | .w => .e₁ | .a => .a | .b => .b | .c => .c | .d => .d, by
  obtain ⟨p, hp⟩ := p
  cases p <;> first | exact absurd rfl hp | rfl⟩

/-- The displayed tree of `N₁` is `ab|cd`. -/
theorem displays_choiceE₁ : Displays (N₁.displayedSides choiceE₁) abcd := by
  have hc : E₁.c ∉ N₁.deletedArcs choiceE₁ := notMem_deletedArcs_choice choiceE₁ ⟨.c, by decide⟩
  have hd : E₁.d ∉ N₁.deletedArcs choiceE₁ := notMem_deletedArcs_choice choiceE₁ ⟨.d, by decide⟩
  refine displays_of_cluster (P := {2, 3}) (u := V₀.w) (by simp [abcd]) (fun x hx => ?_) (fun x _ hxP hx => ?_)
  · rw [mem_insert, mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact mem_displayedCluster.2 (Relation.ReflTransGen.single ⟨.c, hc, rfl, rfl⟩)
    · exact mem_displayedCluster.2 (Relation.ReflTransGen.single ⟨.d, hd, rfl, rfl⟩)
  · have hs := closed_of_reaches (N := N₁) (S := fun p => p = .w ∨ p = .c ∨ p = .d)
      (fun f => by cases f <;> simp [N₁]) (mem_displayedCluster.1 hx).reaches (Or.inl rfl)
    revert hs hxP
    fin_cases x <;> simp [N₁]

/-- It is binary, as a tree. -/
theorem isBinaryTree_choiceE₁ : IsBinaryTree (N₁.displayedSides choiceE₁) :=
  isBinaryTree_of_forall_displays (isUnrootedTree_displayedSides isPhylogenetic_N₁ _) fun q hq =>
    ⟨abcd, mem_treesOn.2 ((taxa_eq_univ _).trans (eq_univ_of_card q (by simpa using hq)).symm), displays_choiceE₁⟩

/-- The binary tree `ac|bd`. -/
abbrev treeAC : Finset (Finset (Fin 4)) := unroot (quartetHierarchy {0, 2})

theorem isBinaryTree_treeAC : IsBinaryTree treeAC := isBinaryTree_quartet (Or.inr (Or.inl rfl))

theorem displays_treeAC : Displays treeAC acbd := displays_quartet (Or.inr (Or.inl rfl)) (by decide)

/-- With uniform concordance factors, `ac|bd` is optimal. -/
theorem isMQSOptimal_treeAC {p : QuartetTree (Fin 4) → ℝ} (hp : ∀ r, p r = 1 / 3) : IsMQSOptimal p treeAC := by
  refine ⟨isBinaryTree_treeAC.isUnrootedTree, fun T' hT' => ?_⟩
  rw [(quartetScore_of_third hp isBinaryTree_treeAC.isUnrootedTree).2 acbd displays_treeAC]
  exact (quartetScore_of_third hp hT').1

/-- `ac|bd` does not resolve the displayed tree of `N₁`. -/
theorem not_subset_treeAC : ¬ N₁.displayedSides choiceE₁ ⊆ treeAC := fun hsub => by
  have := isBinaryTree_treeAC.isUnrootedTree.displays_unique (displays_choiceE₁.mono hsub) displays_treeAC
    ((taxa_eq_univ _).trans (taxa_eq_univ _).symm)
  exact absurd this (by decide)

/-- Lengths with both hybrid arcs of length `0`. -/
def zeroLengths : E₁ → ℝ
  | .e₁ => 0 | .e₂ => 0 | _ => 1

private theorem ncard_filter₁ {α : Type*} [Fintype α] (p : α → Prop) [DecidablePred p] :
    {a | p a}.ncard = #(univ.filter p) := by
  rw [← Set.ncard_coe_finset]
  congr 1
  ext a
  simp

theorem isHybridArc_e₁ : N₁.IsHybridArc .e₁ := by
  unfold IsHybridArc DirectedMultigraph.indegree
  rw [ncard_filter₁]
  decide

theorem isHybridArc_e₂ : N₁.IsHybridArc .e₂ := by
  unfold IsHybridArc DirectedMultigraph.indegree
  rw [ncard_filter₁]
  decide

/-- Valid parameters with hybrid arcs of length `0`: all concordance factors are `1/3`, and `ac|bd` is optimal, whatever
the inheritance probabilities, so for `γ` as close to `0` and `1` as we like. -/
theorem isMQSOptimal_treeAC_of_length_zero {μ : MetricData E₁} (hμ : N₁.IsMetric μ) (hρ : 0 ≤ ρ ∧ ρ ≤ 1)
    (h₁ : μ.length .e₁ = 0) (h₂ : μ.length .e₂ = 0) : IsMQSOptimal (nmscCF N₁ μ ρ) treeAC :=
  isMQSOptimal_treeAC fun r => nmscCF_N₁_of_length_zero hμ hρ h₁ h₂ r

theorem zeroLengths_nonneg (e : E₁) : 0 ≤ zeroLengths e := by
  cases e <;> simp [zeroLengths]

theorem zeroLengths_pos_of_isTreeArc {e : E₁} (he : N₁.IsTreeArc e) : 0 < zeroLengths e := by
  cases e
  · exact one_pos
  · exact one_pos
  · exact absurd isHybridArc_e₁ (not_isHybridArc_of_isTreeArc he)
  · exact absurd isHybridArc_e₂ (not_isHybridArc_of_isTreeArc he)
  · exact one_pos
  · exact one_pos

/-- **Finding: the observation of lines 363-369 needs `HasPositiveEdges` at parameters with hybrid arcs of length `0`.**
At the boundary of the non-binary network `N₁` with lengths `zeroLengths`, the displayed tree is binary, `ab|cd`, but the
concordance factors are all `1/3` and the binary tree `ac|bd`, which does not resolve it, is optimal. -/
theorem zeroLength_boundary (hρ : 0 ≤ ρ ∧ ρ ≤ 1) (γ : E₁ → ℝ) :
    (∀ r, nmscCF N₁ (N₁.choiceMetric ⟨zeroLengths, γ⟩ choiceE₁) ρ r = 1 / 3) ∧
      IsMQSOptimal (nmscCF N₁ (N₁.choiceMetric ⟨zeroLengths, γ⟩ choiceE₁) ρ) treeAC ∧
      ¬ N₁.displayedSides choiceE₁ ⊆ treeAC ∧ ¬ HasPositiveEdges ⟨zeroLengths, γ⟩ choiceE₁ := by
  have hN := isPhylogenetic_N₁
  have hthird : ∀ r, nmscCF N₁ (N₁.choiceMetric ⟨zeroLengths, γ⟩ choiceE₁) ρ r = 1 / 3 := fun r => by
    refine nmscCF_choiceMetric_eq_of_eventually hN choiceE₁ ρ zeroLengths γ r ?_
    filter_upwards [eventually_sum_const_lt_one (E := E₁), self_mem_nhdsWithin] with ε hs hε
    have hm : N₁.IsMetric (coordMetric N₁ (choiceCoords hN choiceE₁) zeroLengths fun _ => ε) :=
      isMetric_coordMetric_of_sum_lt' (isParentChoice_choiceCoords hN choiceE₁)
        (fun _ he => zeroLengths_pos_of_isTreeArc he) (fun e _ => zeroLengths_nonneg e) (fun _ => hε) hs
    exact nmscCF_N₁_of_length_zero hm hρ rfl rfl r
  have hopt := isMQSOptimal_treeAC hthird
  refine ⟨hthird, hopt, not_subset_treeAC, fun hE => not_subset_treeAC ?_⟩
  have hiff := isMQSOptimal_choiceMetric_iff (θ := ⟨zeroLengths, γ⟩) hN choiceE₁ hρ zeroLengths_nonneg hE treeAC
  exact (hiff.1 hopt).2

/-- The lengths of the box of `not_isNullParams_length_zero`: both hybrid arcs have length `0`. -/
def zeroBox : E₁ → Set ℝ
  | .e₁ => {0} | .e₂ => {0} | _ => Set.Ioo 1 2

/-- **On the measure of §5.1, which has an atom at length `0` of a hybrid arc, the failure is not negligible**: the valid
parameters of `N₁` where `ac|bd` is optimal, though it resolves no displayed tree, are not null. This does not contradict
the positive-measure observation, which is about another set of parameters. -/
theorem not_isNullParams_length_zero (hρ : 0 ≤ ρ ∧ ρ ≤ 1) :
    ¬ IsNullParams N₁ {μ | IsMQSOptimal (nmscCF N₁ μ ρ) treeAC} := by
  have hN := isPhylogenetic_N₁
  refine not_isNullParams_of_box (isParentChoice_choiceCoords hN choiceE₁) (L := zeroBox) (η := 1 / 6) (by norm_num)
    (by norm_num) (fun e => ?_) fun l g hl hg => ?_
  · cases e
    · exact lengthMeasure_Ioo_ne_zero_of_pos _ (by norm_num) (by norm_num)
    · exact lengthMeasure_Ioo_ne_zero_of_pos _ (by norm_num) (by norm_num)
    · exact lengthMeasure_singleton_zero_ne_zero isHybridArc_e₁
    · exact lengthMeasure_singleton_zero_ne_zero isHybridArc_e₂
    · exact lengthMeasure_Ioo_ne_zero_of_pos _ (by norm_num) (by norm_num)
    · exact lengthMeasure_Ioo_ne_zero_of_pos _ (by norm_num) (by norm_num)
  · have hs : ∑ e, g e < ∑ _e : E₁, (1 / 6 : ℝ) :=
      sum_lt_sum_of_nonempty ⟨E₁.a, mem_univ _⟩ fun e _ => (hg e).2
    have hs1 : ∑ _e : E₁, (1 / 6 : ℝ) = 1 := by
      rw [sum_const, card_univ, show Fintype.card E₁ = 6 from rfl]
      norm_num
    have h₁ : l .e₁ = 0 := hl .e₁
    have h₂ : l .e₂ = 0 := hl .e₂
    have hpos : ∀ e, e ≠ .e₁ → e ≠ .e₂ → 0 < l e := fun e h₁' h₂' => by
      have hle := hl e
      cases e
      · linarith [hle.1]
      · linarith [hle.1]
      · exact absurd rfl h₁'
      · exact absurd rfl h₂'
      · linarith [hle.1]
      · linarith [hle.1]
    have hm : N₁.IsMetric (coordMetric N₁ (choiceCoords hN choiceE₁) l g) :=
      isMetric_coordMetric_of_sum_lt' (isParentChoice_choiceCoords hN choiceE₁)
        (fun e he => hpos e (fun h => not_isHybridArc_of_isTreeArc he (h ▸ isHybridArc_e₁))
          fun h => not_isHybridArc_of_isTreeArc he (h ▸ isHybridArc_e₂))
        (fun e _ => by
          by_cases h₁' : e = .e₁
          · rw [h₁', h₁]
          · by_cases h₂' : e = .e₂
            · rw [h₂', h₂]
            · exact (hpos e h₁' h₂').le)
        (fun e => (hg e).1) (hs.trans_eq hs1)
    exact And.intro hm (isMQSOptimal_treeAC_of_length_zero hm hρ h₁ h₂)

end ZeroLength

end ECToBlob.Section3Observations
