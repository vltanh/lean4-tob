module

public import External.AllmanBanosRhodes2019.NANUQ
public import External.AllmanBanosRhodes2019.Placement
public import TOBQMC.Level1
public import TOBQMC.Lemma1

/-!
# Proposition 9 of NANUQ on binary level-1 networks

The source takes its Proposition 9 (line 462) from its references [1, 3], and prints no proof. It is proved here, with
`Placement.lean`, for the network multispecies coalescent at any `0 ≤ ρ ≤ 1`, on binary level-1 networks, and Theorem
36 no longer has it as a hypothesis.

## Main results

* `proposition9`: parts 1 and 3, which are what Theorem 36 uses. Part 2 is not included: its equality is
  `NMSC.cut_alternatives`, and its bound `CF_AB|CD ≥ 1/6` is not used.
* `nmscCF_lt_of_no_three_two`: part 1. On a cut-edge split of the induced network with no `3₂`-cycle, the quartet tree
  of the split has the strictly largest concordance factor. It does not matter whether the tree of blobs displays the
  split. For a split it does not display, `TOBQMC.Level1.nmscCF_lt_of_not_displays` has this with no condition on
  cycles.
* `exists_cycle_of_not_isTreelike`, `not_isTreelike_iff`: the structure of a set of four taxa with no cut-edge split.
* `exists_two_displayed`: part 3. Such a set has two quartet trees displayed by the grove, and the third has the
  strictly smallest concordance factor.
* `theorem36`, `theorem36_output`, `theorem36_generic`, `t3Detectable`.

## The argument

Write `IsTL` for "the alternatives of `s` have equal masses, at most that of `s`". The lineages start at their taxa,
and `IsTL` passes up by the Markov property (`isTL_pair_lift`, `isTL_two_reticulation`, `IsTL.of_mix`): two lineages
of a cherry of `s` go up an arc dominating them, and a mixture over the parents of a reticulation is a mixture of
masses. It stops at a vertex with three lineages at or below it, where they are exchangeable, or by a cherry of `s`
that has already coalesced (`isTL_hub_sink`, `isTL_hub_blob`).

Part 1: `a, b` are a cherry of `s`, and start at the source of an arc separating them. At a lowest vertex with three
lineages, nothing is left to do unless a lineage is below the reticulation of its blob. Then one or two are. One or
two other than `a, b` go to the parents of the reticulation. If `a, b` are below it, the condition on `3₂`-cycles says
that `c, d` are below one bridge leaving the blob (`isTL_of_no_three_two`), since they are not above the blob, and
then `c, d` go to the source of this bridge. Each case ends at a vertex of the blob.

Part 3: one taxon `a` is below the reticulation, and its lineage alone goes through it, so that the masses are a
mixture over the two parents (`CycleFrame.cherryMass_mix`). With the lineage at the parent `p`, the lowest vertex of
the blob with two lineages below it has exactly two (`CycleFrame.exists_isCycleSide`), and the arc entering it gives a
strictly tree-like mass towards the quartet tree `s_p` with these two as a cherry (`CycleFrame.isTL_and_lt`). The tree
with the other reticulation arc deleted displays `s_p` (`CycleFrame.splitOffAt`), and `s_p` differs for the two
parents (`CycleFrame.side_ne`). Thus the third quartet tree has mass strictly below that of `s_p` in the term of `p`,
and equal to that of the other in the other term.

The source prints no proof, so this is not its route. The argument uses no formula in the branch lengths, and it works
at any `ρ`.
-/

@[expose] public noncomputable section

open Phylogenetics Phylogenetics.RootedNetwork Phylogenetics.NMSC Finset
open TOBQMC TOBQMC.Level1
open External.AllmanBanosRhodes2019.Placement
open scoped Classical

namespace External.AllmanBanosRhodes2019

variable {V E X : Type*} [Fintype V] [Fintype E] [Fintype X] [DecidableEq X]
variable {N : RootedNetwork V E X} {θ : MetricData E} {ρ : ℝ}

/-! ### Mixtures and pairs -/

theorem IsTL.of_mix {inj inj₁ inj₂ : V → Finset (Finset X)} {s : QuartetTree X} {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (h₁ : IsTL N θ ρ inj₁ s) (h₂ : IsTL N θ ρ inj₂ s)
    (h : ∀ r, cherryMass N θ ρ inj r = a * cherryMass N θ ρ inj₁ r + b * cherryMass N θ ρ inj₂ r) :
    IsTL N θ ρ inj s := by
  refine ⟨fun r hr => ?_, fun r hr r' hr' => ?_⟩
  · rw [h, h]
    exact add_le_add (mul_le_mul_of_nonneg_left (h₁.1 r hr) ha) (mul_le_mul_of_nonneg_left (h₂.1 r hr) hb)
  · rw [h, h, h₁.2 r hr r' hr', h₂.2 r hr r' hr']

/-- The lineages of `q` that `P` places at or below `u`. -/
def reach (N : RootedNetwork V E X) (q : Finset X) (P : X → V) (u : V) : Finset X :=
  q.filter fun x => N.graph.Reaches u (P x)

omit [Fintype V] [Fintype E] [Fintype X] [DecidableEq X] in
theorem mem_reach {q : Finset X} {P : X → V} {u : V} {x : X} :
    x ∈ reach N q P u ↔ x ∈ q ∧ N.graph.Reaches u (P x) := by
  simp [reach]

omit [Fintype V] [Fintype E] [Fintype X] [DecidableEq X] in
theorem reach_mono {q : Finset X} {P : X → V} {u w : V} (h : N.graph.Reaches u w) : reach N q P w ⊆ reach N q P u :=
  fun _ hx => mem_reach.2 ⟨(mem_reach.1 hx).1, h.trans (mem_reach.1 hx).2⟩

omit [Fintype V] [Fintype E] [Fintype X] in
/-- What a co-located cherry gives for the pairs of lineages at or below a vertex with at most two of them. -/
theorem mem_val_of_colocated {s : QuartetTree X} {K : Finset X} (hK : K ∈ s.val) {P : X → V}
    (hco : ∀ k ∈ K, ∀ k' ∈ K, P k = P k') {u : V} {x y : X} (hx : x ∈ s.taxa) (hy : y ∈ s.taxa) (hxy : x ≠ y)
    (hrx : N.graph.Reaches u (P x)) (hry : N.graph.Reaches u (P y))
    (hall : ∀ z ∈ s.taxa, N.graph.Reaches u (P z) → z = x ∨ z = y) : ({x, y} : Finset X) ∈ s.val := by
  have hsub : K ⊆ s.taxa := s.subset_taxa hK
  have hK2 := s.card_of_mem hK
  by_cases hxK : x ∈ K ∨ y ∈ K
  · have hin : K ⊆ {x, y} := by
      intro k hk
      have hrk : N.graph.Reaches u (P k) := by
        rcases hxK with h | h
        · rw [hco k hk x h]
          exact hrx
        · rw [hco k hk y h]
          exact hry
      simpa using hall k (hsub hk) hrk
    have : K = {x, y} := eq_of_subset_of_card_le hin (by rw [card_pair hxy, hK2])
    rwa [← this]
  · push Not at hxK
    have hO := s.sdiff_mem hK
    have hin : ({x, y} : Finset X) ⊆ s.taxa \ K := by
      intro z hz
      simp only [mem_insert, mem_singleton] at hz
      rcases hz with rfl | rfl
      · exact mem_sdiff.2 ⟨hx, hxK.1⟩
      · exact mem_sdiff.2 ⟨hy, hxK.2⟩
    have : ({x, y} : Finset X) = s.taxa \ K :=
      eq_of_subset_of_card_le hin (by rw [s.card_of_mem hO, card_pair hxy])
    rwa [this]

/-! ### What is strictly below a vertex -/

/-- The vertices strictly below `v`. -/
def strictBelow (N : RootedNetwork V E X) (v : V) : Finset V := (atOrBelow N v).erase v

omit [Fintype E] [Fintype X] [DecidableEq X] in
theorem mem_strictBelow {v w : V} : w ∈ strictBelow N v ↔ w ≠ v ∧ N.graph.Reaches v w := by
  rw [strictBelow, mem_erase, mem_atOrBelow]

omit [Fintype E] [Fintype X] [DecidableEq X] in
theorem downClosed_strictBelow (hN : N.IsPhylogenetic) (v : V) : DownClosed N (strictBelow N v) := by
  intro f hf
  obtain ⟨hne, hr⟩ := mem_strictBelow.1 hf
  refine mem_strictBelow.2 ⟨fun heq => hne ?_, hr.tail ⟨f, rfl, rfl⟩⟩
  exact eq_of_reaches_of_reaches hN.acyclic (heq ▸ reaches_of_arc N f) hr

omit [Fintype E] [Fintype X] [DecidableEq X] in
theorem root_notMem_strictBelow (hN : N.IsPhylogenetic) (v : V) : N.root ∉ strictBelow N v := fun hm => by
  obtain ⟨hne, hr⟩ := mem_strictBelow.1 hm
  exact hne (eq_of_reaches_of_reaches hN.acyclic hr (hN.root_reaches v)).symm

omit [Fintype V] [Fintype E] [Fintype X] [DecidableEq X] in
/-- An arc entering what is strictly below `v`, from outside it and not from `v`, enters a reticulation of the blob of
`v`. -/
theorem entering_of_strictBelow (hN : N.IsPhylogenetic) {v : V} {f : E} (hr : N.graph.Reaches v (N.graph.target f))
    (hne : N.graph.target f ≠ v) (hs : ¬ N.graph.Reaches v (N.graph.source f)) :
    SameBlob N v (N.graph.target f) ∧ 2 ≤ N.graph.indegree (N.graph.target f) := by
  refine ⟨sameBlob_of_entering hN hr hs, ?_⟩
  rcases Relation.ReflTransGen.cases_tail hr with heq | ⟨c, hc, g, rfl, hg⟩
  · exact absurd heq hne
  · have hgf : f ≠ g := by
      rintro rfl
      exact hs hc
    exact two_le_indegree_of_ne hN hgf hg.symm

/-- **A hub at a sink**: `v₀` has three lineages at or below it, every vertex strictly below it at most two, a
co-located cherry gives the pairs, and no lineage is below a reticulation of the blob of `v₀` other than `v₀`. -/
theorem isTL_hub_sink (hN : N.IsPhylogenetic) (hθ : N.IsMetric θ) (hρ : 0 ≤ ρ ∧ ρ ≤ 1) {s : QuartetTree X}
    {P : X → V} {v₀ : V} (h3 : 3 ≤ #(reach N s.taxa P v₀))
    (hbelow : ∀ u, u ≠ v₀ → N.graph.Reaches v₀ u → #(reach N s.taxa P u) ≤ 2)
    (hret : ∀ y, SameBlob N v₀ y → 2 ≤ N.graph.indegree y → y ≠ v₀ → ∀ x ∈ s.taxa, ¬ N.graph.Reaches y (P x))
    (hpair : ∀ u, ∀ x ∈ s.taxa, ∀ y ∈ s.taxa, x ≠ y → N.graph.Reaches u (P x) → N.graph.Reaches u (P y) →
      (∀ z ∈ s.taxa, N.graph.Reaches u (P z) → z = x ∨ z = y) → ({x, y} : Finset X) ∈ s.val) :
    IsTL N θ ρ (placeInj s.taxa P) s := by
  have hq := s.card_taxa
  -- a lineage such that the others are at or below `v₀`
  obtain ⟨a, ha, hall⟩ : ∃ a ∈ s.taxa, ∀ x ∈ s.taxa, x ≠ a → x ∈ reach N s.taxa P v₀ := by
    by_cases hc : ∃ a ∈ s.taxa, a ∉ reach N s.taxa P v₀
    · obtain ⟨a, ha, hna⟩ := hc
      refine ⟨a, ha, fun x hx hxa => ?_⟩
      by_contra hnx
      have hsub : reach N s.taxa P v₀ ⊆ (s.taxa.erase a).erase x := fun z hz => by
        refine mem_erase.2 ⟨?_, mem_erase.2 ⟨?_, (mem_reach.1 hz).1⟩⟩
        · rintro rfl
          exact hnx hz
        · rintro rfl
          exact hna hz
      have := card_le_card hsub
      rw [card_erase_of_mem (mem_erase.2 ⟨hxa, hx⟩), card_erase_of_mem ha, hq] at this
      omega
    · push Not at hc
      obtain ⟨a, ha⟩ : s.taxa.Nonempty := card_pos.1 (by omega)
      exact ⟨a, ha, fun x hx _ => hc x hx⟩
  refine isTL_hub hN hθ hρ hq rfl (downClosed_strictBelow hN v₀) (root_notMem_strictBelow hN v₀) (v₀ := v₀)
    (fun hm => (mem_strictBelow.1 hm).1 rfl) ?_ ?_ ha ?_
  · intro x hx f hft hfs hne hr
    obtain ⟨htne, htr⟩ := mem_strictBelow.1 hft
    have hsn : ¬ N.graph.Reaches v₀ (N.graph.source f) := fun hc => hfs (mem_strictBelow.2 ⟨hne, hc⟩)
    obtain ⟨hb, h2⟩ := entering_of_strictBelow hN htr htne hsn
    exact hret _ hb h2 htne x hx hr
  · intro u hu x hx y hy hxy hrx hry
    obtain ⟨hune, hur⟩ := mem_strictBelow.1 hu
    refine hpair u x hx y hy hxy hrx hry fun z hz hrz => ?_
    have hle := hbelow u hune hur
    have hsub : ({x, y} : Finset X) ⊆ reach N s.taxa P u := by
      intro w hw
      simp only [mem_insert, mem_singleton] at hw
      rcases hw with rfl | rfl
      · exact mem_reach.2 ⟨hx, hrx⟩
      · exact mem_reach.2 ⟨hy, hry⟩
    have heq : ({x, y} : Finset X) = reach N s.taxa P u :=
      eq_of_subset_of_card_le hsub (by rw [card_pair hxy]; exact hle)
    have hzin : z ∈ ({x, y} : Finset X) := heq ▸ mem_reach.2 ⟨hz, hrz⟩
    simpa using hzin
  · intro x hx hxa
    obtain ⟨-, hr⟩ := mem_reach.1 (hall x hx hxa)
    by_cases he : P x = v₀
    · exact Or.inr he
    · exact Or.inl (mem_strictBelow.2 ⟨he, hr⟩)

/-- **A hub in a blob**: at least three lineages at or below a vertex of the blob of `v`, none at or below its
reticulation, at most two at or below a vertex below the blob and off it, and a co-located cherry gives the pairs. -/
theorem isTL_hub_blob (hN : N.IsPhylogenetic) (hLevel : IsLevelOne N) (hθ : N.IsMetric θ) (hρ : 0 ≤ ρ ∧ ρ ≤ 1)
    {s : QuartetTree X} {P : X → V} {v h : V} (hh : SameBlob N v h) (hh₂ : 2 ≤ N.graph.indegree h)
    (hnb : ∀ x ∈ s.taxa, ¬ N.graph.Reaches h (P x)) {u₀ : V} (hu₀ : SameBlob N v u₀)
    (h3 : 3 ≤ #(reach N s.taxa P u₀))
    (hpend : ∀ u w, SameBlob N v w → N.graph.Reaches w u → ¬ SameBlob N v u → #(reach N s.taxa P u) ≤ 2)
    (hpair : ∀ u, ∀ x ∈ s.taxa, ∀ y ∈ s.taxa, x ≠ y → N.graph.Reaches u (P x) → N.graph.Reaches u (P y) →
      (∀ z ∈ s.taxa, N.graph.Reaches u (P z) → z = x ∨ z = y) → ({x, y} : Finset X) ∈ s.val) :
    IsTL N θ ρ (placeInj s.taxa P) s := by
  obtain ⟨v₁, ⟨hv₁, h₁3⟩, hmin⟩ := exists_sink hN
    (S := {u | SameBlob N v u ∧ 3 ≤ #(reach N s.taxa P u)}) ⟨u₀, hu₀, h3⟩
  refine isTL_hub_sink hN hθ hρ h₁3 (fun u hne hr => ?_) (fun y hy hy₂ _ x hx hr => ?_) hpair
  · by_cases hub : SameBlob N v u
    · by_contra hc
      refine hmin u ⟨hub, by omega⟩ ?_
      rcases Relation.ReflTransGen.cases_head hr with heq | ⟨c, hvc, hcu⟩
      · exact absurd heq.symm hne
      · exact Relation.TransGen.head' hvc hcu
    · exact hpend u v₁ hv₁ hr hub
  · have : y = h := reticulation_unique hN hLevel (sameBlob_trans hv₁ hy) hy₂ hh hh₂
    exact hnb x hx (this ▸ hr)

/-! ### Arcs dominating positions -/

omit [Fintype V] [Fintype E] [Fintype X] [DecidableEq X] in
/-- A bridge dominates what is below it. -/
theorem not_avoidingReach_of_isBridge (hN : N.IsPhylogenetic) {g : E} (hg : IsBridge N g) {z : V}
    (hz : N.graph.Reaches (N.graph.target g) z) : ¬ N.AvoidingReach g N.root z := by
  intro hav
  have hroot : ¬ N.graph.Reaches (N.graph.target g) N.root :=
    fun hr => TOBQMC.Level1.target_ne_root hN g (eq_root_of_reaches_root hN hr)
  obtain ⟨f, hfg, hs, ht, -⟩ := exists_entering_arc hav hroot hz
  exact hs ((isBridge_iff_reaches hN g).1 hg f hfg ht)

omit [Fintype X] [DecidableEq X] in
/-- An arc into a vertex of a blob dominates what is below it and not below the reticulation. -/
theorem not_avoidingReach_of_blob (hN : N.IsPhylogenetic) (hLevel : IsLevelOne N) {v h : V}
    (hh : SameBlob N v h) (hh₂ : 2 ≤ N.graph.indegree h) {k : E} (hc : SameBlob N v (N.graph.target k)) {z : V}
    (hz : N.graph.Reaches (N.graph.target k) z) (hzh : ¬ N.graph.Reaches h z) : ¬ N.AvoidingReach k N.root z := by
  intro hav
  have hroot : ¬ N.graph.Reaches (N.graph.target k) N.root :=
    fun hr => TOBQMC.Level1.target_ne_root hN k (eq_root_of_reaches_root hN hr)
  obtain ⟨f, hfk, hs, ht, hfz⟩ := exists_entering_arc hav hroot hz
  have := target_eq_reticulation hN hLevel hh hh₂ hc hfk ht hs
  rw [this] at hfz
  exact hzh hfz

omit [Fintype X] [DecidableEq X] in
/-- The arc leaving a reticulation: a bridge, and the only arc leaving it. -/
theorem exists_child_arc (hN : N.IsPhylogenetic) (hBin : N.IsBinary) (hLevel : IsLevelOne N) {v h : V}
    (hh : SameBlob N v h) (hh₂ : 2 ≤ N.graph.indegree h) :
    ∃ e, N.graph.source e = h ∧ (∀ g, N.graph.source g = h → g = e) ∧ IsBridge N e := by
  have h1 := outdegree_eq_one_of_reticulation hN hBin hh₂
  rw [DirectedMultigraph.outdegree, Set.ncard_eq_one] at h1
  obtain ⟨e, he⟩ := h1
  have hes : N.graph.source e = h := by
    have : e ∈ {g | N.graph.source g = h} := by rw [he]; rfl
    exact this
  refine ⟨e, hes, fun g hg => ?_, ?_⟩
  · have : g ∈ {g | N.graph.source g = h} := hg
    rw [he] at this
    exact this
  · by_contra hnb
    have hb := sameBlob_of_not_isBridge hnb
    rw [hes] at hb
    have hr := reaches_reticulation hN hLevel hh hh₂ (sameBlob_trans hh hb)
    exact not_reaches_source hN e (hes ▸ hr)

omit [Fintype V] [Fintype E] [Fintype X] [DecidableEq X] in
/-- What is below a vertex with one arc leaving it is below that arc. -/
theorem reaches_target_of_unique_out {h z : V} {e : E} (hu : ∀ g, N.graph.source g = h → g = e)
    (hr : N.graph.Reaches h z) (hz : z ≠ h) : N.graph.Reaches (N.graph.target e) z := by
  rcases Relation.ReflTransGen.cases_head hr with heq | ⟨c, ⟨g, hg, rfl⟩, hc⟩
  · exact absurd heq.symm hz
  · rwa [hu g hg] at hc

omit [Fintype V] [Fintype E] [Fintype X] [DecidableEq X] in
/-- A path leaving a blob leaves it by a bridge. -/
theorem exists_exit_arc {v w u : V} (hw : SameBlob N v w) (hr : N.graph.Reaches w u)
    (hu : ¬ SameBlob N v u) : ∃ g, IsBridge N g ∧ SameBlob N v (N.graph.source g) ∧
      ¬ SameBlob N v (N.graph.target g) ∧ N.graph.Reaches (N.graph.target g) u := by
  induction hr using Relation.ReflTransGen.head_induction_on with
  | refl => exact absurd hw hu
  | @head a b hab hbu ih =>
    obtain ⟨f, rfl, rfl⟩ := hab
    by_cases hb : SameBlob N v (N.graph.target f)
    · exact ih hb
    · refine ⟨f, ?_, hw, hb, hbu⟩
      by_contra hnb
      exact hb (sameBlob_trans hw (sameBlob_of_not_isBridge hnb))

/-! ### A split without a `3₂`-cycle -/

/-- **The masses are tree-like towards a split `s` with no `3₂`-cycle**, with the two lineages of a cherry `a b` of
`s` at the source of an arc separating them from the others. This is part 1 of the source's Proposition 9, on a binary
level-1 network. Take a lowest vertex `v₀` with three lineages at or below it. If no lineage is below the reticulation
of its blob, or `v₀` is that reticulation, or the blob has none, `isTL_hub_sink` applies. Otherwise the lineages below
the reticulation `h` are one or two. One goes to a parent of `h`; `a b` stays together and `isTL_hub_blob` applies.
Two other than `a, b` are lifted to `h` and go to its parents, in the same way. If `a, b` are below `h`, the other two
taxa are not in different blocks, since there is no `3₂`-cycle, and they are not above the blob, as `v₀` has a third
lineage. So they are below a bridge leaving the blob, and they stay together. -/
theorem isTL_of_no_three_two (hN : N.IsPhylogenetic) (hBin : N.IsBinary) (hLevel : IsLevelOne N)
    (hθ : N.IsMetric θ) (hρ : 0 ≤ ρ ∧ ρ ≤ 1) {s : QuartetTree X} (h3 : ¬ HasThreeTwoCycle N s.taxa) {a b : X}
    (hab : a ≠ b) (hA : ({a, b} : Finset X) ∈ s.val) {e : E}
    (hd : ∀ x ∈ ({a, b} : Finset X), N.Dominates e x) :
    IsTL N θ ρ (placeInj s.taxa (movePair N.leaf a b (N.graph.source e))) s := by
  have hne : Nonempty X := ⟨a⟩
  set q := s.taxa with hq
  have hq4 : #q = 4 := s.card_taxa
  have haq : a ∈ q := s.subset_taxa hA (by simp)
  have hbq : b ∈ q := s.subset_taxa hA (by simp)
  set w := N.graph.source e with hw
  set Pos := movePair N.leaf a b w with hPos
  have hPa : Pos a = w := by simp [hPos, movePair]
  have hPb : Pos b = w := by simp [hPos, movePair]
  have hPo : ∀ z, z ≠ a → z ≠ b → Pos z = N.leaf z := fun z h₁ h₂ => by simp [hPos, movePair, h₁, h₂]
  have hco : ∀ k ∈ ({a, b} : Finset X), ∀ k' ∈ ({a, b} : Finset X), Pos k = Pos k' := by
    intro k hk k' hk'
    simp only [mem_insert, mem_singleton] at hk hk'
    rcases hk with rfl | rfl <;> rcases hk' with rfl | rfl <;> simp [hPa, hPb]
  have hpairA : ∀ u, ∀ x ∈ s.taxa, ∀ y ∈ s.taxa, x ≠ y → N.graph.Reaches u (Pos x) → N.graph.Reaches u (Pos y) →
      (∀ z ∈ s.taxa, N.graph.Reaches u (Pos z) → z = x ∨ z = y) → ({x, y} : Finset X) ∈ s.val :=
    fun u x hx y hy hxy hrx hry hall => mem_val_of_colocated hA hco hx hy hxy hrx hry hall
  -- a lowest vertex with three lineages
  have hroot3 : 3 ≤ #(reach N q Pos N.root) := by
    have : reach N q Pos N.root = q := filter_true_of_mem fun x _ => hN.root_reaches _
    rw [this, hq4]
    norm_num
  obtain ⟨v₀, hv₀3, hmin⟩ := exists_sink hN (S := {u | 3 ≤ #(reach N q Pos u)}) ⟨N.root, hroot3⟩
  have hv₀3' : 3 ≤ #(reach N q Pos v₀) := hv₀3
  have hbelow : ∀ u, u ≠ v₀ → N.graph.Reaches v₀ u → #(reach N q Pos u) ≤ 2 := by
    intro u hne' hr
    by_contra hc
    refine hmin u (show 3 ≤ _ by omega) ?_
    rcases Relation.ReflTransGen.cases_head hr with heq | ⟨c, hvc, hcu⟩
    · exact absurd heq.symm hne'
    · exact Relation.TransGen.head' hvc hcu
  by_cases hnone : ∀ y, SameBlob N v₀ y → 2 ≤ N.graph.indegree y → y ≠ v₀ → ∀ x ∈ q, ¬ N.graph.Reaches y (Pos x)
  · exact isTL_hub_sink hN hθ hρ hv₀3' hbelow hnone hpairA
  push Not at hnone
  obtain ⟨h, hh, hh₂, hhv, x₀, hx₀, hrx₀⟩ := hnone
  have hv₀h : N.graph.Reaches v₀ h := reaches_reticulation hN hLevel hh hh₂ .refl
  have hL2 : #(reach N q Pos h) ≤ 2 := hbelow h hhv hv₀h
  have hhr : h ≠ N.root := reticulation_ne_root hN hh₂
  obtain ⟨eh, hehs, hehu, hehb⟩ := exists_child_arc hN hBin hLevel hh hh₂
  have hbelow_h : ∀ {z : V}, N.graph.Reaches h z → z ≠ h → N.graph.Reaches (N.graph.target eh) z :=
    fun hr hz => reaches_target_of_unique_out hehu hr hz
  obtain ⟨T, k₁, k₂, pL, pR, C⟩ := exists_blobCycle hN hBin hLevel hh hh₂
  have hk₁h : N.graph.target k₁ = h := C.target₁
  have hk₂h : N.graph.target k₂ = h := C.target₂
  have hsb₁ : SameBlob N v₀ (N.graph.source k₁) := C.source₁_sameBlob hN
  have hsb₂ : SameBlob N v₀ (N.graph.source k₂) := C.swap.source₁_sameBlob hN
  have hnr₁ : ¬ N.graph.Reaches h (N.graph.source k₁) := C.not_reaches_of_target₁ hN
  have hnr₂ : ¬ N.graph.Reaches h (N.graph.source k₂) := C.swap.not_reaches_of_target₁ hN
  have hTv₀ : N.graph.Reaches T v₀ := C.top_reaches v₀ .refl
  have hT3 : 3 ≤ #(reach N q Pos T) := hv₀3'.trans (card_le_card (reach_mono hTv₀))
  -- at most two lineages below a vertex below the blob and off it
  have hpendR : ∀ u w', SameBlob N v₀ w' → N.graph.Reaches w' u → ¬ SameBlob N v₀ u → #(reach N q Pos u) ≤ 2 := by
    intro u w' hw' hr hu
    by_contra hc
    have hcard : #q < #(reach N q Pos u) + #(reach N q Pos v₀) := by omega
    obtain ⟨x, hx⟩ := inter_nonempty_of_card_lt_card_add_card (filter_subset _ _) (filter_subset _ _) hcard
    obtain ⟨hx₁, hx₂⟩ := mem_inter.1 hx
    obtain ⟨g, hgb, hgs, hgt, hgu⟩ := exists_exit_arc hw' hr hu
    have hnv : ¬ N.graph.Reaches (N.graph.target g) v₀ := fun hc' =>
      not_sameBlob_of_reaches_exit hN hgb hgs hc' .refl
    have hvg : N.graph.Reaches v₀ (N.graph.source g) :=
      reaches_source_of_cut (isBridge_crosses_iff hN hgb) hnv (hgu.trans (mem_reach.1 hx₁).2) (mem_reach.1 hx₂).2
    have hne' : N.graph.target g ≠ v₀ := fun heq => hgt (heq ▸ .refl)
    have := hbelow _ hne' (hvg.tail ⟨g, rfl, rfl⟩)
    have hle := card_le_card (reach_mono (q := q) (P := Pos) hgu)
    omega
  -- the placements with lineages moved to the blob
  have hubP : ∀ {P' : X → V} {K : Finset X}, K ∈ s.val → (∀ k ∈ K, ∀ k' ∈ K, P' k = P' k') →
      (∀ z ∈ q, P' z = Pos z ∨ SameBlob N v₀ (P' z)) → (∀ z ∈ q, ¬ N.graph.Reaches h (P' z)) →
      IsTL N θ ρ (placeInj q P') s := by
    intro P' K hK hcoK hmoved hnb
    refine isTL_hub_blob hN hLevel hθ hρ hh hh₂ hnb (u₀ := T) C.top ?_ ?_ ?_
    · refine hT3.trans (card_le_card fun z hz => ?_)
      obtain ⟨hzq, hzr⟩ := mem_reach.1 hz
      refine mem_reach.2 ⟨hzq, ?_⟩
      rcases hmoved z hzq with he | hb
      · rwa [he]
      · exact C.top_reaches _ hb
    · intro u w' hw' hr hu
      refine (card_le_card fun z hz => ?_).trans (hpendR u w' hw' hr hu)
      obtain ⟨hzq, hzr⟩ := mem_reach.1 hz
      refine mem_reach.2 ⟨hzq, ?_⟩
      rcases hmoved z hzq with he | hb
      · rwa [← he]
      · exact absurd (sameBlob_of_reaches_of_reaches hN hw' hb hr hzr) hu
    · exact fun u x hx y hy hxy hrx hry hall => mem_val_of_colocated hK hcoK hx hy hxy hrx hry hall
  have hhyb₁ : 0 ≤ θ.inheritance k₁ :=
    (hθ.2.2.2.1 k₁ (by unfold RootedNetwork.IsHybridArc; rw [hk₁h]; exact hh₂)).le
  have hhyb₂ : 0 ≤ θ.inheritance k₂ :=
    (hθ.2.2.2.1 k₂ (by unfold RootedNetwork.IsHybridArc; rw [hk₂h]; exact hh₂)).le
  have hleafne : ∀ z, N.leaf z ≠ h := by
    rintro z rfl
    rw [hN.leaf_indegree] at hh₂
    omega
  have hL1 : 1 ≤ #(reach N q Pos h) := card_pos.2 ⟨x₀, mem_reach.2 ⟨hx₀, hrx₀⟩⟩
  have hAL : ∀ k ∈ ({a, b} : Finset X), k ∈ reach N q Pos h → ∀ k' ∈ ({a, b} : Finset X), k' ∈ reach N q Pos h := by
    intro k hk hkL k' hk'
    refine mem_reach.2 ⟨s.subset_taxa hA hk', ?_⟩
    rw [hco k' hk' k hk]
    exact (mem_reach.1 hkL).2
  -- two lineages at the reticulation, the others on the blob or where they were
  have hfour : ∀ {P₁ : X → V} {x y : X} {K : Finset X}, x ∈ q → y ∈ q → x ≠ y → ({x, y} : Finset X) ∈ s.val →
      K ∈ s.val → P₁ x = h → P₁ y = h →
      (∀ z ∈ q, z ≠ x → z ≠ y → (P₁ z = Pos z ∨ SameBlob N v₀ (P₁ z)) ∧ ¬ N.graph.Reaches h (P₁ z)) →
      (∀ k ∈ K, k ≠ x ∧ k ≠ y) → (∀ k ∈ K, ∀ k' ∈ K, P₁ k = P₁ k') → IsTL N θ ρ (placeInj q P₁) s := by
    intro P₁ x y K hxq hyq hxy hxyC hK hPx hPy hoth hKne hKco
    have hmv : ∀ {u u' : V}, SameBlob N v₀ u → ¬ N.graph.Reaches h u → SameBlob N v₀ u' → ¬ N.graph.Reaches h u' →
        IsTL N θ ρ (placeInj q (moveTwo P₁ x y u u')) s := by
      intro u u' hu hun hu' hun'
      have hoff : ∀ z, z ≠ x → z ≠ y → moveTwo P₁ x y u u' z = P₁ z := fun z h₁ h₂ => by simp [moveTwo, h₁, h₂]
      have hmx : moveTwo P₁ x y u u' x = u := by simp [moveTwo]
      have hmy : moveTwo P₁ x y u u' y = u' := by simp [moveTwo, hxy.symm]
      refine hubP hK (fun k hk k' hk' => ?_) (fun z hz => ?_) (fun z hz => ?_)
      · rw [hoff k (hKne k hk).1 (hKne k hk).2, hoff k' (hKne k' hk').1 (hKne k' hk').2]
        exact hKco k hk k' hk'
      · by_cases hzx : z = x
        · subst hzx
          exact Or.inr (by rw [hmx]; exact hu)
        · by_cases hzy : z = y
          · subst hzy
            exact Or.inr (by rw [hmy]; exact hu')
          · rw [hoff z hzx hzy]
            exact (hoth z hz hzx hzy).1
      · by_cases hzx : z = x
        · subst hzx
          rw [hmx]
          exact hun
        · by_cases hzy : z = y
          · subst hzy
            rw [hmy]
            exact hun'
          · rw [hoff z hzx hzy]
            exact (hoth z hz hzx hzy).2
    exact isTL_two_reticulation hN hθ hρ hxq hyq hxy hxyC hhr hPx hPy
      (fun z hz hzx hzy => (hoth z hz hzx hzy).2) hk₁h hk₂h C.arcs (hmv hsb₁ hnr₁ hsb₁ hnr₁) (hmv hsb₁ hnr₁ hsb₂ hnr₂)
      (hmv hsb₂ hnr₂ hsb₁ hnr₁) (hmv hsb₂ hnr₂ hsb₂ hnr₂)
  by_cases hcard1 : #(reach N q Pos h) = 1
  · -- one lineage below the reticulation
    obtain ⟨x, hxL⟩ := card_eq_one.1 hcard1
    have hxmem : x ∈ reach N q Pos h := by rw [hxL]; simp
    obtain ⟨hxq, hxr⟩ := mem_reach.1 hxmem
    have honly : ∀ z ∈ q, z ≠ x → ¬ N.graph.Reaches h (Pos z) := fun z hz hzx hr => hzx (by
      have : z ∈ reach N q Pos h := mem_reach.2 ⟨hz, hr⟩
      rw [hxL] at this
      simpa using this)
    have hxA : x ∉ ({a, b} : Finset X) := by
      intro hx
      have hboth := hAL x hx hxmem
      have h₁ := hboth a (by simp)
      have h₂ := hboth b (by simp)
      rw [hxL, mem_singleton] at h₁ h₂
      exact hab (h₁.trans h₂.symm)
    have hxa : x ≠ a := fun h' => hxA (by simp [h'])
    have hxb : x ≠ b := fun h' => hxA (by simp [h'])
    have hPx : Pos x = N.leaf x := hPo x hxa hxb
    have hlift : ∀ r, cherryMass N θ ρ (placeInj q Pos) r =
        cherryMass N θ ρ (placeInj q (Function.update Pos x h)) r := by
      intro r
      have := cherryMass_placeInj_lift (θ := θ) (ρ := ρ) hN hθ hρ (q := q) (P := Pos) hxq (e := eh)
        (hbelow_h hxr (by rw [hPx]; exact hleafne x))
        (not_avoidingReach_of_isBridge hN hehb (hbelow_h hxr (by rw [hPx]; exact hleafne x)))
        (fun y hy hyx hr => honly y hy hyx (by rw [← hehs]; exact (reaches_of_arc N eh).trans hr)) r
      rwa [hehs] at this
    have hmix := fun r => cherryMass_one_reticulation (θ := θ) (ρ := ρ) hN hθ hρ (q := q) (P := Function.update Pos x h)
      hxq hhr (Function.update_self _ _ _) (fun z hz hzx => by rw [Function.update_of_ne hzx]; exact honly z hz hzx)
      hk₁h hk₂h C.ne C.arcs r
    simp only [Function.update_idem] at hmix
    have hTLi : ∀ {k : E}, SameBlob N v₀ (N.graph.source k) → ¬ N.graph.Reaches h (N.graph.source k) →
        IsTL N θ ρ (placeInj q (Function.update Pos x (N.graph.source k))) s := by
      intro k hks hkn
      have hupd : ∀ z, z ≠ x → Function.update Pos x (N.graph.source k) z = Pos z :=
        fun z hz => Function.update_of_ne hz _ _
      refine hubP hA (fun k₀ hk₀ k₀' hk₀' => ?_) (fun z _ => ?_) (fun z hz => ?_)
      · have hne₀ : k₀ ≠ x := fun h' => hxA (h' ▸ hk₀)
        have hne₀' : k₀' ≠ x := fun h' => hxA (h' ▸ hk₀')
        rw [hupd _ hne₀, hupd _ hne₀']
        exact hco k₀ hk₀ k₀' hk₀'
      · by_cases hzx : z = x
        · subst hzx
          right
          rw [Function.update_self]
          exact hks
        · exact Or.inl (hupd z hzx)
      · by_cases hzx : z = x
        · subst hzx
          rw [Function.update_self]
          exact hkn
        · rw [hupd z hzx]
          exact honly z hz hzx
    refine IsTL.of_mix hhyb₁ hhyb₂ (hTLi hsb₁ hnr₁) (hTLi hsb₂ hnr₂) fun r => ?_
    rw [hlift r, hmix r]
  -- two lineages below the reticulation
  have hcard2 : #(reach N q Pos h) = 2 := by omega
  obtain ⟨x, y, hxy, hLe⟩ := card_eq_two.1 hcard2
  have hxmem : x ∈ reach N q Pos h := by rw [hLe]; simp
  have hymem : y ∈ reach N q Pos h := by rw [hLe]; simp
  obtain ⟨hxq, hxr⟩ := mem_reach.1 hxmem
  obtain ⟨hyq, hyr⟩ := mem_reach.1 hymem
  have honly : ∀ z ∈ q, z ≠ x → z ≠ y → ¬ N.graph.Reaches h (Pos z) := fun z hz hzx hzy hr => by
    have : z ∈ reach N q Pos h := mem_reach.2 ⟨hz, hr⟩
    rw [hLe] at this
    simp only [mem_insert, mem_singleton] at this
    tauto
  have hxyC : ({x, y} : Finset X) ∈ s.val := hpairA h x hxq y hyq hxy hxr hyr fun z hz hr => by
    by_contra hc
    push Not at hc
    exact honly z hz hc.1 hc.2 hr
  by_cases hdisj : x ∈ ({a, b} : Finset X) ∨ y ∈ ({a, b} : Finset X)
  · -- `a`, `b` are below the reticulation
    have hLA : ({a, b} : Finset X) = reach N q Pos h := by
      refine eq_of_subset_of_card_le (fun k hk => ?_) (by rw [hcard2, card_pair hab])
      rcases hdisj with h' | h'
      · exact hAL x h' hxmem k hk
      · exact hAL y h' hymem k hk
    have haL : a ∈ reach N q Pos h := hLA ▸ (by simp)
    have hrw : N.graph.Reaches h w := by
      have := (mem_reach.1 haL).2
      rwa [hPa] at this
    have hQ := s.sdiff_mem hA
    obtain ⟨c, d, hcd, hQe⟩ := card_eq_two.1 (s.card_of_mem hQ)
    have hcmem : c ∈ s.taxa \ ({a, b} : Finset X) := by rw [hQe]; simp
    have hdmem : d ∈ s.taxa \ ({a, b} : Finset X) := by rw [hQe]; simp
    obtain ⟨hcq, hcA⟩ := mem_sdiff.1 hcmem
    obtain ⟨hdq, hdA⟩ := mem_sdiff.1 hdmem
    have hca : c ≠ a := fun h' => hcA (by simp [h'])
    have hcb : c ≠ b := fun h' => hcA (by simp [h'])
    have hda : d ≠ a := fun h' => hdA (by simp [h'])
    have hdb : d ≠ b := fun h' => hdA (by simp [h'])
    have hPc : Pos c = N.leaf c := hPo c hca hcb
    have hPd : Pos d = N.leaf d := hPo d hda hdb
    have hnL : ∀ z ∈ q, z ∉ ({a, b} : Finset X) → ¬ N.graph.Reaches h (Pos z) := fun z hz hzA hr =>
      hzA (hLA ▸ mem_reach.2 ⟨hz, hr⟩)
    have hcn : ¬ N.graph.Reaches h (N.leaf c) := hPc ▸ hnL c hcq hcA
    have hdn : ¬ N.graph.Reaches h (N.leaf d) := hPd ▸ hnL d hdq hdA
    have hzcases : ∀ z ∈ q, z = a ∨ z = b ∨ z = c ∨ z = d := by
      intro z hz
      by_cases hzA : z ∈ ({a, b} : Finset X)
      · simp only [mem_insert, mem_singleton] at hzA
        tauto
      · have : z ∈ s.taxa \ ({a, b} : Finset X) := mem_sdiff.2 ⟨hz, hzA⟩
        rw [hQe] at this
        simp only [mem_insert, mem_singleton] at this
        tauto
    have hbelowA : ∀ k ∈ ({a, b} : Finset X), N.graph.Reaches h (N.leaf k) := fun k hk =>
      (hrw.trans (reaches_of_arc N e)).trans (Dominates.isBelow hN (hd k hk))
    by_cases hblock : BlockWalk N h (N.leaf c) (N.leaf d)
    · -- both go through one bridge off the blob
      have hhc : ¬ SameBlob N h (N.leaf c) := leaf_not_sameBlob hN .refl hh₂ c
      obtain ⟨g, hgb, hS, hcases⟩ := exists_blockWalk_cut hN hhc
      have hgexit : SameBlob N h (N.graph.source g) := by
        rcases hcases with ⟨hs, -⟩ | ⟨ht, hbs⟩
        · exact hs
        · exfalso
          have hnt : ¬ BlockWalk N h (N.leaf c) (N.graph.target g) := fun hc' =>
            not_sameBlob_of_blockWalk hhc hc' ht
          have hgT : N.graph.Reaches (N.graph.target g) T :=
            (reaches_iff_of_sameBlob hN hgb
              (sameBlob_trans (sameBlob_symm ht) (sameBlob_trans (sameBlob_symm hh) C.top))).1 .refl
          have hnc : ∀ {u : V}, N.graph.Reaches (N.graph.target g) u → ¬ BlockWalk N h (N.leaf c) u :=
            fun hu => not_reaches_of_blockWalk_of_entry hS hbs hnt hu
          have hTcd : N.graph.Reaches T (N.leaf c) ∨ N.graph.Reaches T (N.leaf d) := by
            by_contra hcon
            push Not at hcon
            have hsub : reach N q Pos T ⊆ {a, b} := by
              intro z hz
              obtain ⟨hzq, hzr⟩ := mem_reach.1 hz
              rcases hzcases z hzq with rfl | rfl | rfl | rfl
              · simp
              · simp
              · rw [hPc] at hzr
                exact absurd hzr hcon.1
              · rw [hPd] at hzr
                exact absurd hzr hcon.2
            have := card_le_card hsub
            rw [card_pair hab] at this
            omega
          rcases hTcd with hr | hr
          · exact hnc (hgT.trans hr) .refl
          · exact hnc (hgT.trans hr) hblock
      have hgc : N.graph.Reaches (N.graph.target g) (N.leaf c) :=
        reaches_of_blockWalk_of_exit hN hhc hS hgexit .refl
      have hgd : N.graph.Reaches (N.graph.target g) (N.leaf d) :=
        reaches_of_blockWalk_of_exit hN hhc hS hgexit hblock
      have hgh : ¬ N.graph.Reaches (N.graph.target g) h := fun hr =>
        not_sameBlob_of_reaches_exit hN hgb hgexit hr .refl
      have hgn : ¬ N.graph.Reaches h (N.graph.source g) := by
        intro hr
        have heq := eq_of_reaches_of_reaches hN.acyclic hr
          (reaches_reticulation hN hLevel .refl hh₂ hgexit)
        exact hcn (heq ▸ ((reaches_of_arc N g).trans hgc))
      set P₁ := movePair Pos a b h with hP₁
      have hP₁a : P₁ a = h := by simp [hP₁, movePair]
      have hP₁b : P₁ b = h := by simp [hP₁, movePair]
      have hP₁c : P₁ c = N.leaf c := by simp [hP₁, movePair, hca, hcb, hPc]
      have hP₁d : P₁ d = N.leaf d := by simp [hP₁, movePair, hda, hdb, hPd]
      have hTL₂ : IsTL N θ ρ (placeInj q (movePair P₁ c d (N.graph.source g))) s := by
        have hQval : ({c, d} : Finset X) ∈ s.val := hQe ▸ hQ
        have hP₂c : movePair P₁ c d (N.graph.source g) c = N.graph.source g := by simp [movePair]
        have hP₂d : movePair P₁ c d (N.graph.source g) d = N.graph.source g := by simp [movePair]
        have hP₂a : movePair P₁ c d (N.graph.source g) a = h := by simp [movePair, hca.symm, hda.symm, hP₁a]
        have hP₂b : movePair P₁ c d (N.graph.source g) b = h := by simp [movePair, hcb.symm, hdb.symm, hP₁b]
        refine hfour haq hbq hab hA hQval hP₂a hP₂b (fun z hz hza hzb => ?_) (fun k hk => ?_) (fun k hk k' hk' => ?_)
        · rcases hzcases z hz with rfl | rfl | rfl | rfl
          · exact absurd rfl hza
          · exact absurd rfl hzb
          · rw [hP₂c]
            exact ⟨Or.inr (sameBlob_trans hh hgexit), hgn⟩
          · rw [hP₂d]
            exact ⟨Or.inr (sameBlob_trans hh hgexit), hgn⟩
        · simp only [mem_insert, mem_singleton] at hk
          rcases hk with rfl | rfl
          · exact ⟨hca, hcb⟩
          · exact ⟨hda, hdb⟩
        · simp only [mem_insert, mem_singleton] at hk hk'
          rcases hk with rfl | rfl <;> rcases hk' with rfl | rfl <;> simp [hP₂c, hP₂d]
      have hTL₁ : IsTL N θ ρ (placeInj q P₁) s := by
        refine isTL_pair_lift hN hθ hρ hcq hdq hcd (hQe ▸ hQ) (e := g) ?_ ?_ ?_ ?_ (fun z hz hzc hzd => ?_) hTL₂
        · rwa [hP₁c]
        · rwa [hP₁d]
        · rw [hP₁c]
          exact not_avoidingReach_of_isBridge hN hgb hgc
        · rw [hP₁d]
          exact not_avoidingReach_of_isBridge hN hgb hgd
        · rcases hzcases z hz with rfl | rfl | rfl | rfl
          · rwa [hP₁a]
          · rwa [hP₁b]
          · exact absurd rfl hzc
          · exact absurd rfl hzd
      by_cases hwh : w = h
      · have : Pos = P₁ := by
          funext z
          by_cases hz : z = a ∨ z = b
          · rcases hz with rfl | rfl
            · rw [hP₁a, hPa, hwh]
            · rw [hP₁b, hPb, hwh]
          · push Not at hz
            simp [hP₁, movePair, hz.1, hz.2]
        rw [this]
        exact hTL₁
      · have hbw : N.graph.Reaches (N.graph.target eh) w := hbelow_h hrw hwh
        refine isTL_pair_lift hN hθ hρ haq hbq hab hA (e := eh) ?_ ?_ ?_ ?_ (fun z hz hza hzb => ?_) ?_
        · rwa [hPa]
        · rwa [hPb]
        · rw [hPa]
          exact not_avoidingReach_of_isBridge hN hehb hbw
        · rw [hPb]
          exact not_avoidingReach_of_isBridge hN hehb hbw
        · have hzA : z ∉ ({a, b} : Finset X) := by simp [hza, hzb]
          exact fun hr => hnL z hz hzA (hehs ▸ (reaches_of_arc N eh).trans hr)
        · rw [hehs]
          exact hTL₁
    · -- a `3₂`-cycle
      refine absurd ⟨h, hh₂, ?_, ?_⟩ h3
      · have : (q.filter fun z => N.graph.Reaches h (N.leaf z)) = {a, b} := by
          ext z
          rw [mem_filter]
          constructor
          · rintro ⟨hz, hr⟩
            rcases hzcases z hz with rfl | rfl | rfl | rfl
            · simp
            · simp
            · exact absurd hr hcn
            · exact absurd hr hdn
          · intro hz
            exact ⟨s.subset_taxa hA hz, hbelowA z hz⟩
        rw [this, card_pair hab]
      · intro u hu t ht hut hun htn hw'
        have hinA : ∀ {z}, z ∈ q → ¬ N.graph.Reaches h (N.leaf z) → z = c ∨ z = d := by
          intro z hz hzn
          rcases hzcases z hz with rfl | rfl | h' | h'
          · exact absurd (hbelowA _ (by simp)) hzn
          · exact absurd (hbelowA _ (by simp)) hzn
          · exact Or.inl h'
          · exact Or.inr h'
        rcases hinA hu hun with rfl | rfl <;> rcases hinA ht htn with rfl | rfl
        · exact hut rfl
        · exact hblock hw'
        · exact hblock (blockWalk_symm hw')
        · exact hut rfl
  · -- two others below the reticulation
    push Not at hdisj
    obtain ⟨hxA, hyA⟩ := hdisj
    have hxa : x ≠ a := fun h' => hxA (by simp [h'])
    have hxb : x ≠ b := fun h' => hxA (by simp [h'])
    have hya : y ≠ a := fun h' => hyA (by simp [h'])
    have hyb : y ≠ b := fun h' => hyA (by simp [h'])
    have hPx : Pos x = N.leaf x := hPo x hxa hxb
    have hPy : Pos y = N.leaf y := hPo y hya hyb
    have hbx : N.graph.Reaches (N.graph.target eh) (Pos x) := hbelow_h hxr (by rw [hPx]; exact hleafne x)
    have hby : N.graph.Reaches (N.graph.target eh) (Pos y) := hbelow_h hyr (by rw [hPy]; exact hleafne y)
    refine isTL_pair_lift hN hθ hρ hxq hyq hxy hxyC (e := eh) hbx hby (not_avoidingReach_of_isBridge hN hehb hbx)
      (not_avoidingReach_of_isBridge hN hehb hby)
      (fun z hz hzx hzy hr => honly z hz hzx hzy (hehs ▸ (reaches_of_arc N eh).trans hr)) ?_
    rw [hehs]
    have hP₁o : ∀ z, z ≠ x → z ≠ y → movePair Pos x y h z = Pos z := fun z h₁ h₂ => by simp [movePair, h₁, h₂]
    refine hfour hxq hyq hxy hxyC hA (by simp [movePair]) (by simp [movePair]) (fun z hz hzx hzy => ?_)
      (fun k hk => ?_) (fun k hk k' hk' => ?_)
    · rw [hP₁o z hzx hzy]
      exact ⟨Or.inl rfl, honly z hz hzx hzy⟩
    · exact ⟨fun h' => hxA (h' ▸ hk), fun h' => hyA (h' ▸ hk)⟩
    · have hkx : k ≠ x := fun h' => hxA (h' ▸ hk)
      have hky : k ≠ y := fun h' => hyA (h' ▸ hk)
      have hkx' : k' ≠ x := fun h' => hxA (h' ▸ hk')
      have hky' : k' ≠ y := fun h' => hyA (h' ▸ hk')
      rw [hP₁o k hkx hky, hP₁o k' hkx' hky']
      exact hco k hk k' hk'

/-- **Part 1 of Proposition 9 of NANUQ on a binary level-1 network.** On a cut-edge split of the induced network with
no `3₂`-cycle, the quartet tree of the split is strictly the most probable. -/
theorem nmscCF_lt_of_no_three_two (hN : N.IsPhylogenetic) (hBin : N.IsBinary) (hLevel : IsLevelOne N)
    (hθ : N.IsMetric θ) (hρ : 0 ≤ ρ ∧ ρ ≤ 1) {s : QuartetTree X} (hs : InducedCutSplit N s)
    (h3 : ¬ HasThreeTwoCycle N s.taxa) {r : QuartetTree X} (hr : r ∈ s.alternatives) :
    nmscCF N θ ρ r < nmscCF N θ ρ s := by
  obtain ⟨P, hP, e, hd, hn⟩ := Phylogenetics.RootedNetwork.exists_separating_arc hN hs
  obtain ⟨a, b, hab, rfl⟩ := card_eq_two.1 (s.card_of_mem hP)
  have haq : a ∈ s.taxa := s.subset_taxa hP (by simp)
  have hbq : b ∈ s.taxa := s.subset_taxa hP (by simp)
  have hrq : r.taxa = s.taxa := (QuartetTree.mem_alternatives.1 hr).1
  have hda : N.Dominates e a := hd a (by simp)
  have hdb : N.Dominates e b := hd b (by simp)
  rw [nmscCF_eq_cherryMass hN hθ hρ r, nmscCF_eq_cherryMass hN hθ hρ s, hrq, ← placeInj_leaf]
  refine lt_of_pair_lift hN hθ hρ (P := N.leaf) haq hbq hab hP (e := e) (Dominates.isBelow hN hda)
    (Dominates.isBelow hN hdb) hda hdb (fun z hz hza hzb => hn z hz (by simp [hza, hzb])) ?_
    (hθ.1 e (isTreeArc_of_dominates hN hda)) (isTL_of_no_three_two hN hBin hLevel hθ hρ h3 hab hP hd) hr
  ext g
  rw [mem_arcsInto, mem_singleton]
  exact ⟨fun hg => eq_of_target_eq_of_dominates hN hda hg, fun hg => hg ▸ rfl⟩

/-! ### A set of four taxa with no cut-edge split -/

/-- **A set of four taxa with no cut-edge split on its induced network is a `4₁`-cycle**: its taxa are in distinct
blocks at a blob with a reticulation, and exactly one of them is below the reticulation. Take a lowest vertex `v` with
three taxa below it. Two taxa in one block are below a bridge leaving the blob, with no third one (since `v` is
lowest), or not below the blob at all (since `v` has three): in both cases the block is a side of a cut edge with two
taxa of `q`, and `q` is treelike. The blob is not trivial, since an arc of it has two taxa below it
(`exists_arc_two_below`). -/
theorem exists_cycle_of_not_isTreelike (hN : N.IsPhylogenetic) (hBin : N.IsBinary) (hLevel : IsLevelOne N)
    {q : Finset X} (hq : #q = 4) (hnt : ¬ IsTreelike N q) :
    ∃ v h, SameBlob N v h ∧ 2 ≤ N.graph.indegree h ∧ (∀ x ∈ q, ∀ y ∈ q, x ≠ y → ¬ SameBlock N v x y) ∧
      ∃! a, a ∈ q ∧ N.graph.Reaches h (N.leaf a) := by
  have hroot3 : 3 ≤ #(reach N q N.leaf N.root) := by
    have : reach N q N.leaf N.root = q := filter_true_of_mem fun x _ => hN.root_reaches _
    rw [this, hq]
    norm_num
  obtain ⟨v, hv3, hmin⟩ := exists_sink hN (S := {u | 3 ≤ #(reach N q N.leaf u)}) ⟨N.root, hroot3⟩
  have hv3' : 3 ≤ #(reach N q N.leaf v) := hv3
  have hdist : ∀ x ∈ q, ∀ y ∈ q, x ≠ y → ¬ SameBlock N v x y := by
    intro x hx y hy hxy hs
    have hblob : ¬ SameBlob N v (N.leaf x) :=
      not_sameBlob_of_blockWalk_of_ne hs (fun h => hxy (hN.leaf_injective h))
    obtain ⟨e, heb, hS, hcases⟩ := exists_blockWalk_cut hN hblob
    rcases hcases with ⟨hs₁, -⟩ | ⟨ht₁, hs₁⟩
    · -- the block is below a bridge leaving the blob
      have hbel : ∀ z, SameBlock N v x z → N.graph.Reaches (N.graph.target e) (N.leaf z) :=
        fun z hz => reaches_of_blockWalk_of_exit hN hblob hS hs₁ hz
      have hcard : #(block N v x ∩ q) = 2 := by
        apply le_antisymm
        · by_contra hc
          have h3 : 3 ≤ #(reach N q N.leaf (N.graph.target e)) := by
            refine (by omega : 3 ≤ #(block N v x ∩ q)).trans (card_le_card fun z hz => ?_)
            obtain ⟨hzb, hzq⟩ := mem_inter.1 hz
            exact mem_reach.2 ⟨hzq, hbel z (mem_block.1 hzb)⟩
          have hlt : #q < #(reach N q N.leaf (N.graph.target e)) + #(reach N q N.leaf v) := by omega
          obtain ⟨z, hz⟩ := inter_nonempty_of_card_lt_card_add_card (filter_subset _ _) (filter_subset _ _) hlt
          obtain ⟨hz₁, hz₂⟩ := mem_inter.1 hz
          have hnv : ¬ N.graph.Reaches (N.graph.target e) v := fun hc' =>
            not_sameBlob_of_reaches_exit hN heb hs₁ hc' .refl
          have hvg : N.graph.Reaches v (N.graph.source e) :=
            reaches_source_of_cut (isBridge_crosses_iff hN heb) hnv (mem_reach.1 hz₁).2 (mem_reach.1 hz₂).2
          exact hmin _ h3 (Relation.TransGen.tail' hvg ⟨e, rfl, rfl⟩)
        · have hsub : ({x, y} : Finset X) ⊆ block N v x ∩ q := by
            intro z hz
            simp only [mem_insert, mem_singleton] at hz
            rcases hz with rfl | rfl
            · exact mem_inter.2 ⟨mem_block.2 .refl, hx⟩
            · exact mem_inter.2 ⟨mem_block.2 hs, hy⟩
          have := card_le_card hsub
          rwa [card_pair hxy] at this
      exact hnt (isTreelike_of_hasCutSplit hN (hasCutSplit_block hN hblob) hq hcard)
    · -- the block is not below the blob
      have hnt' : ¬ BlockWalk N v (N.leaf x) (N.graph.target e) := fun hc => not_sameBlob_of_blockWalk hblob hc ht₁
      have hev : N.graph.Reaches (N.graph.target e) v :=
        (reaches_iff_of_sameBlob hN heb (sameBlob_symm ht₁)).1 .refl
      have hnr : ∀ z, SameBlock N v x z → ¬ N.graph.Reaches v (N.leaf z) := fun z hz hr =>
        not_reaches_of_blockWalk_of_entry hS hs₁ hnt' (hev.trans hr) hz
      have hsub : reach N q N.leaf v ⊆ q \ {x, y} := by
        intro z hz
        obtain ⟨hzq, hzr⟩ := mem_reach.1 hz
        refine mem_sdiff.2 ⟨hzq, fun hzp => ?_⟩
        simp only [mem_insert, mem_singleton] at hzp
        rcases hzp with rfl | rfl
        · exact hnr z .refl hzr
        · exact hnr z hs hzr
      have hle := card_le_card hsub
      rw [card_sdiff_of_subset (by
        intro z hz
        simp only [mem_insert, mem_singleton] at hz
        rcases hz with rfl | rfl
        · exact hx
        · exact hy), hq, card_pair hxy] at hle
      omega
  rcases exists_reticulation_or_forall_isBridge hN v with ⟨h, hh, hh₂⟩ | hall
  · refine ⟨v, h, hh, hh₂, hdist, ?_⟩
    have hex : ∃ d ∈ q, N.graph.Reaches h (N.leaf d) := by
      by_contra hno
      push Not at hno
      exact hnt (isTreelike_of_not_below hN hBin hLevel hh hh₂ hq hdist hno)
    obtain ⟨d, hd, hdh⟩ := hex
    exact existsUnique_below hN hBin hLevel hh hh₂ hdist hd hdh
  · exfalso
    obtain ⟨k, hs, ht, -⟩ := exists_arc_two_below hN hBin hq hdist
    have h1 := eq_of_sameBlob_of_forall_isBridge hall hs
    have h2 := eq_of_sameBlob_of_forall_isBridge hall ht
    exact target_ne_source hN k (h2.trans h1.symm)

/-- **What a `4₁`-cycle is, in terms of blocks.** On a binary level-1 network, a set of four taxa has no cut-edge
split on its induced network if and only if its taxa are in distinct blocks at a blob with a reticulation, with
exactly one of them below the reticulation. This is the description by contraction of the source (lines 455-461) with
no contraction: four taxa in distinct blocks are four pendant parts around the cycle of the blob. -/
theorem not_isTreelike_iff (hN : N.IsPhylogenetic) (hBin : N.IsBinary) (hLevel : IsLevelOne N) {q : Finset X}
    (hq : #q = 4) :
    ¬ IsTreelike N q ↔ ∃ v h, SameBlob N v h ∧ 2 ≤ N.graph.indegree h ∧
      (∀ x ∈ q, ∀ y ∈ q, x ≠ y → ¬ SameBlock N v x y) ∧ ∃! a, a ∈ q ∧ N.graph.Reaches h (N.leaf a) := by
  refine ⟨exists_cycle_of_not_isTreelike hN hBin hLevel hq, ?_⟩
  rintro ⟨v, h, hh, hh₂, hdist, a, ⟨ha, hah⟩, -⟩
  exact not_isTreelike_of_distinct hN hBin hLevel hh hh₂ hq hdist ha hah

/-! ### The two sides of the cycle -/

/-- Four taxa around the cycle of a blob, with `a` the only one below its reticulation `h`. -/
structure CycleFrame (N : RootedNetwork V E X) (q : Finset X) (a : X) (v h T : V) (k₁ k₂ : E) (pL pR : List E) :
    Prop where
  card : #q = 4
  two_le : 2 ≤ N.graph.indegree h
  distinct : ∀ x ∈ q, ∀ y ∈ q, x ≠ y → ¬ BlockWalk N v (N.leaf x) (N.leaf y)
  mem : a ∈ q
  below : N.graph.Reaches h (N.leaf a)
  only : ∀ z ∈ q, z ≠ a → ¬ N.graph.Reaches h (N.leaf z)
  cycle : BlobCycle N v h T k₁ k₂ pL pR

/-- The lineages when that of `a` has gone to the source of the reticulation arc `k`. -/
def sidePos (N : RootedNetwork V E X) (a : X) (k : E) : X → V := Function.update N.leaf a (N.graph.source k)

omit [Fintype V] [Fintype E] [Fintype X] in
@[simp] theorem sidePos_self {a : X} {k : E} : sidePos N a k a = N.graph.source k := Function.update_self _ _ _

omit [Fintype V] [Fintype E] [Fintype X] in
theorem sidePos_of_ne {a z : X} {k : E} (h : z ≠ a) : sidePos N a k z = N.leaf z := Function.update_of_ne h _ _

/-- The lowest vertex of the blob with two lineages below it, when the lineage of `a` is at the source of `k`, is the
target of the arc `f`, and has exactly `x`, `y` below it. -/
structure IsCycleSide (N : RootedNetwork V E X) (q : Finset X) (a : X) (v h T : V) (k : E) (f : E) (x y : X) :
    Prop where
  mem₁ : x ∈ q
  mem₂ : y ∈ q
  ne : x ≠ y
  blob : SameBlob N v (N.graph.target f)
  ne_reticulation : N.graph.target f ≠ h
  ne_top : N.graph.target f ≠ T
  iff : ∀ z ∈ q, N.graph.Reaches (N.graph.target f) (sidePos N a k z) ↔ z = x ∨ z = y

namespace CycleFrame

variable {q : Finset X} {a : X} {v h T : V} {k₁ k₂ : E} {pL pR : List E}

omit [Fintype V] [Fintype E] [Fintype X] [DecidableEq X] in
theorem swap (F : CycleFrame N q a v h T k₁ k₂ pL pR) : CycleFrame N q a v h T k₂ k₁ pR pL :=
  ⟨F.card, F.two_le, F.distinct, F.mem, F.below, F.only, F.cycle.swap⟩

omit [Fintype V] [Fintype E] [Fintype X] in
theorem not_reaches_sidePos (hN : N.IsPhylogenetic) (F : CycleFrame N q a v h T k₁ k₂ pL pR) :
    ∀ z ∈ q, ¬ N.graph.Reaches h (sidePos N a k₁ z) := by
  intro z hz
  by_cases hza : z = a
  · rw [hza, sidePos_self]
    exact F.cycle.not_reaches_of_target₁ hN
  · rw [sidePos_of_ne hza]
    exact F.only z hz hza

omit [Fintype V] [Fintype E] [Fintype X] in
theorem three_le_reach_top (hN : N.IsPhylogenetic) (F : CycleFrame N q a v h T k₁ k₂ pL pR) :
    3 ≤ #(reach N q (sidePos N a k₁) T) := by
  by_contra hc
  have hcard : 1 < #(q \ reach N q (sidePos N a k₁) T) := by
    rw [card_sdiff_of_subset (show reach N q (sidePos N a k₁) T ⊆ q from filter_subset _ _), F.card]
    omega
  obtain ⟨x, hx, y, hy, hxy⟩ := one_lt_card.1 hcard
  obtain ⟨hxq, hxn⟩ := mem_sdiff.1 hx
  obtain ⟨hyq, hyn⟩ := mem_sdiff.1 hy
  have hne : ∀ z, z ∈ q → z ∉ reach N q (sidePos N a k₁) T → ¬ N.graph.Reaches T (N.leaf z) := by
    intro z hzq hzn hr
    have hza : z ≠ a := by
      intro hza
      refine hzn (mem_reach.2 ⟨hzq, ?_⟩)
      rw [hza, sidePos_self]
      exact F.cycle.left.reaches
    exact hzn (mem_reach.2 ⟨hzq, by rw [sidePos_of_ne hza]; exact hr⟩)
  rcases reaches_top_of_not_blockWalk hN F.cycle.top_reaches (F.distinct x hxq y hyq hxy) with hr | hr
  · exact hne x hxq hxn hr
  · exact hne y hyq hyn hr

omit [Fintype V] [Fintype E] [Fintype X] in
/-- **The lowest vertex of the blob with two lineages below it** has exactly two. Below it, each child has at most one
lineage: a child in the blob since the vertex is lowest, and a child off the blob since two taxa below it would be in
one block. A third lineage would give a third arc leaving the vertex, against binarity. The source of `k₁` has the arc
`k₁` as well, with no lineage below it, when the lineage of `a` is at this source. -/
theorem exists_isCycleSide (hN : N.IsPhylogenetic) (hBin : N.IsBinary)
    (F : CycleFrame N q a v h T k₁ k₂ pL pR) : ∃ f x y, IsCycleSide N q a v h T k₁ f x y := by
  have C := F.cycle
  have hh := C.reticulation
  have hh₂ := F.two_le
  have hPa : sidePos N a k₁ a = N.graph.source k₁ := sidePos_self
  have hPo : ∀ z, z ≠ a → sidePos N a k₁ z = N.leaf z := fun z hz => sidePos_of_ne hz
  have hnb := F.not_reaches_sidePos hN
  have hT3 := F.three_le_reach_top hN
  obtain ⟨u, ⟨hub, hu2⟩, hmin⟩ := exists_sink hN
    (S := {u | SameBlob N v u ∧ 2 ≤ #(reach N q (sidePos N a k₁) u)}) ⟨T, C.top, by omega⟩
  have hu2' : 2 ≤ #(reach N q (sidePos N a k₁) u) := hu2
  have hrh : ∀ t, t ∉ reach N q (sidePos N a k₁) h := fun t ht => hnb t (mem_reach.1 ht).1 (mem_reach.1 ht).2
  have huh : u ≠ h := by
    intro heq
    obtain ⟨z, hz⟩ : (reach N q (sidePos N a k₁) u).Nonempty := card_pos.1 (by omega)
    exact hrh z (heq ▸ hz)
  have hchild : ∀ g, N.graph.source g = u → #(reach N q (sidePos N a k₁) (N.graph.target g)) ≤ 1 := by
    intro g hg
    by_contra hc
    have hc2 : 2 ≤ #(reach N q (sidePos N a k₁) (N.graph.target g)) := by omega
    by_cases hb : SameBlob N v (N.graph.target g)
    · exact hmin _ ⟨hb, hc2⟩ (.single ⟨g, hg, rfl⟩)
    · have hgs : SameBlob N v (N.graph.source g) := hg ▸ hub
      have hgb : IsBridge N g := by
        by_contra hnb'
        exact hb (sameBlob_trans hgs (sameBlob_of_not_isBridge hnb'))
      obtain ⟨x, hx, y, hy, hxy⟩ :=
        one_lt_card.1 (show 1 < #(reach N q (sidePos N a k₁) (N.graph.target g)) by omega)
      have hnota : ∀ z ∈ reach N q (sidePos N a k₁) (N.graph.target g), z ≠ a := by
        intro z hz hza
        have hr := (mem_reach.1 hz).2
        rw [hza, hPa] at hr
        exact not_sameBlob_of_reaches_exit hN hgb hgs hr (C.source₁_sameBlob hN)
      have hxr := (mem_reach.1 hx).2
      rw [hPo x (hnota x hx)] at hxr
      have hyr := (mem_reach.1 hy).2
      rw [hPo y (hnota y hy)] at hyr
      exact F.distinct x (mem_reach.1 hx).1 y (mem_reach.1 hy).1 hxy
        (blockWalk_of_both_below (fun w hw => not_sameBlob_of_reaches_exit hN hgb hgs hw) hxr hyr)
  have hstep : ∀ z ∈ reach N q (sidePos N a k₁) u, ∃ g, N.graph.source g = u ∧
      (z ∈ reach N q (sidePos N a k₁) (N.graph.target g) ∨ (g = k₁ ∧ z = a)) := by
    intro z hz
    obtain ⟨hzq, hzr⟩ := mem_reach.1 hz
    rcases Relation.ReflTransGen.cases_head hzr with heq | ⟨c, ⟨g, hg, rfl⟩, hc⟩
    · by_cases hza : z = a
      · rw [hza, hPa] at heq
        exact ⟨k₁, heq.symm, Or.inr ⟨rfl, hza⟩⟩
      · rw [hPo z hza] at heq
        exact absurd (heq ▸ hub) (leaf_not_sameBlob hN hh hh₂ z)
    · exact ⟨g, hg, Or.inl (mem_reach.2 ⟨hzq, hc⟩)⟩
  have hdiff : ∀ z z' g, z ≠ z' → N.graph.source g = u →
      (z ∈ reach N q (sidePos N a k₁) (N.graph.target g) ∨ (g = k₁ ∧ z = a)) →
      (z' ∈ reach N q (sidePos N a k₁) (N.graph.target g) ∨ (g = k₁ ∧ z' = a)) → False := by
    intro z z' g hzz hg h₁ h₂
    have hk : ∀ t, g = k₁ → t ∉ reach N q (sidePos N a k₁) (N.graph.target g) := by
      intro t hgk
      rw [hgk, C.target₁]
      exact hrh t
    rcases h₁ with h₁ | ⟨hgk, hza⟩ <;> rcases h₂ with h₂ | ⟨hgk', hza'⟩
    · have := hchild g hg
      have hc : 1 < #(reach N q (sidePos N a k₁) (N.graph.target g)) := one_lt_card.2 ⟨z, h₁, z', h₂, hzz⟩
      omega
    · exact hk z hgk' h₁
    · exact hk z' hgk h₂
    · exact hzz (hza.trans hza'.symm)
  have hcard2 : #(reach N q (sidePos N a k₁) u) = 2 := by
    by_contra hc
    obtain ⟨z₁, z₂, z₃, h₁, h₂, h₃, h₁₂, h₁₃, h₂₃⟩ :=
      two_lt_card_iff.1 (show 2 < #(reach N q (sidePos N a k₁) u) by omega)
    obtain ⟨g₁, hg₁, hp₁⟩ := hstep z₁ h₁
    obtain ⟨g₂, hg₂, hp₂⟩ := hstep z₂ h₂
    obtain ⟨g₃, hg₃, hp₃⟩ := hstep z₃ h₃
    refine false_of_three_out_arcs hN hBin ?_ ?_ ?_ hg₁ hg₂ hg₃
    · intro he
      exact hdiff z₁ z₂ g₁ h₁₂ hg₁ hp₁ (he ▸ hp₂)
    · intro he
      exact hdiff z₁ z₃ g₁ h₁₃ hg₁ hp₁ (he ▸ hp₃)
    · intro he
      exact hdiff z₂ z₃ g₂ h₂₃ hg₂ hp₂ (he ▸ hp₃)
  obtain ⟨x, y, hxy, he⟩ := card_eq_two.1 hcard2
  have huT : u ≠ T := by
    intro heq
    rw [heq] at hcard2
    omega
  have hmemx : x ∈ reach N q (sidePos N a k₁) u := by rw [he]; simp
  have hmemy : y ∈ reach N q (sidePos N a k₁) u := by rw [he]; simp
  rcases Relation.ReflTransGen.cases_tail (C.top_reaches u hub) with heq | ⟨c, -, f, -, hft⟩
  · exact absurd heq huT
  · subst hft
    refine ⟨f, x, y, (mem_reach.1 hmemx).1, (mem_reach.1 hmemy).1, hxy, hub, huh, huT, fun z hz => ⟨fun hr => ?_, ?_⟩⟩
    · have hzm : z ∈ reach N q (sidePos N a k₁) (N.graph.target f) := mem_reach.2 ⟨hz, hr⟩
      rw [he] at hzm
      simpa using hzm
    · rintro (rfl | rfl)
      · exact (mem_reach.1 hmemx).2
      · exact (mem_reach.1 hmemy).2

omit [Fintype X] in
/-- The source of the arc entering the lowest vertex with two lineages. -/
theorem source_mem (hN : N.IsPhylogenetic) (hLevel : IsLevelOne N) (F : CycleFrame N q a v h T k₁ k₂ pL pR) {f : E}
    {x y : X} (S : IsCycleSide N q a v h T k₁ f x y) :
    SameBlob N v (N.graph.source f) ∧ ¬ N.graph.Reaches h (N.graph.source f) := by
  have C := F.cycle
  constructor
  · rcases Relation.ReflTransGen.cases_tail (C.top_reaches _ S.blob) with heq | ⟨c, hTc, g, hgs, hgt⟩
    · exact absurd heq S.ne_top
    · have hgf := arc_eq_of_target_eq hN hLevel C.reticulation F.two_le S.blob S.ne_reticulation hgt rfl
      subst hgf
      exact sameBlob_of_reaches_of_reaches hN C.top S.blob (hgs ▸ hTc) (reaches_of_arc N _)
  · intro hr
    have h₁ := reaches_reticulation hN hLevel C.reticulation F.two_le S.blob
    exact S.ne_reticulation (eq_of_reaches_of_reaches hN.acyclic h₁ (hr.trans (reaches_of_arc N f)))

/-- **The masses on one side of the cycle**: with the lineage of `a` at the source of `k₁`, they are tree-like towards
the quartet tree with cherry `x, y` of the lowest vertex with two lineages, and strictly so. These lineages go up the
arc entering the vertex, and then `isTL_hub_blob` applies, with the top of the blob as the hub and `x, y` together. -/
theorem isTL_and_lt (hN : N.IsPhylogenetic) (hLevel : IsLevelOne N) (hθ : N.IsMetric θ) (hρ : 0 ≤ ρ ∧ ρ ≤ 1)
    (F : CycleFrame N q a v h T k₁ k₂ pL pR) {f : E} {x y : X} (S : IsCycleSide N q a v h T k₁ f x y)
    {s : QuartetTree X} (hsq : s.taxa = q) (hC : ({x, y} : Finset X) ∈ s.val) :
    IsTL N θ ρ (placeInj q (sidePos N a k₁)) s ∧ ∀ r ∈ s.alternatives,
      cherryMass N θ ρ (placeInj q (sidePos N a k₁)) r < cherryMass N θ ρ (placeInj q (sidePos N a k₁)) s := by
  subst hsq
  have C := F.cycle
  have hh := C.reticulation
  have hh₂ := F.two_le
  have hnb := F.not_reaches_sidePos hN
  have hT3 := F.three_le_reach_top hN
  obtain ⟨hsf, hsfn⟩ := F.source_mem hN hLevel S
  have hxq := S.mem₁
  have hyq := S.mem₂
  have hxy := S.ne
  set P' := movePair (sidePos N a k₁) x y (N.graph.source f) with hP'
  have hP'x : P' x = N.graph.source f := by simp [hP', movePair]
  have hP'y : P' y = N.graph.source f := by simp [hP', movePair]
  have hP'o : ∀ z, z ≠ x → z ≠ y → P' z = sidePos N a k₁ z := fun z h₁ h₂ => by simp [hP', movePair, h₁, h₂]
  have hco : ∀ k ∈ ({x, y} : Finset X), ∀ k' ∈ ({x, y} : Finset X), P' k = P' k' := by
    intro k hk k' hk'
    simp only [mem_insert, mem_singleton] at hk hk'
    rcases hk with rfl | rfl <;> rcases hk' with rfl | rfl <;> simp [hP'x, hP'y]
  have hub : IsTL N θ ρ (placeInj s.taxa P') s := by
    refine isTL_hub_blob hN hLevel hθ hρ hh hh₂ (fun z hz => ?_) (u₀ := T) C.top ?_ ?_ ?_
    · by_cases hzx : z = x
      · rw [hzx, hP'x]
        exact hsfn
      · by_cases hzy : z = y
        · rw [hzy, hP'y]
          exact hsfn
        · rw [hP'o z hzx hzy]
          exact hnb z hz
    · refine hT3.trans (card_le_card fun z hz => ?_)
      obtain ⟨hzq, hzr⟩ := mem_reach.1 hz
      refine mem_reach.2 ⟨hzq, ?_⟩
      by_cases hzx : z = x
      · rw [hzx, hP'x]
        exact C.top_reaches _ hsf
      · by_cases hzy : z = y
        · rw [hzy, hP'y]
          exact C.top_reaches _ hsf
        · rwa [hP'o z hzx hzy]
    · intro u w hw hr hu
      have hsub : reach N s.taxa P' u ⊆ s.taxa \ {x, y} := by
        intro z hz
        obtain ⟨hzq, hzr⟩ := mem_reach.1 hz
        refine mem_sdiff.2 ⟨hzq, fun hzp => hu ?_⟩
        have hzs : P' z = N.graph.source f := by
          simp only [mem_insert, mem_singleton] at hzp
          rcases hzp with rfl | rfl
          · exact hP'x
          · exact hP'y
        rw [hzs] at hzr
        exact sameBlob_of_reaches_of_reaches hN hw hsf hr hzr
      refine (card_le_card hsub).trans ?_
      rw [s.card_of_mem (s.sdiff_mem hC)]
    · exact fun u x' hx' y' hy' hne hrx hry hall => mem_val_of_colocated hC hco hx' hy' hne hrx hry hall
  have hbx : N.graph.Reaches (N.graph.target f) (sidePos N a k₁ x) := (S.iff x hxq).2 (Or.inl rfl)
  have hby : N.graph.Reaches (N.graph.target f) (sidePos N a k₁ y) := (S.iff y hyq).2 (Or.inr rfl)
  have hdx := not_avoidingReach_of_blob hN hLevel hh hh₂ S.blob hbx (hnb x hxq)
  have hdy := not_avoidingReach_of_blob hN hLevel hh hh₂ S.blob hby (hnb y hyq)
  have hoth : ∀ z ∈ s.taxa, z ≠ x → z ≠ y → ¬ N.graph.Reaches (N.graph.target f) (sidePos N a k₁ z) := by
    intro z hz hzx hzy hr
    rcases (S.iff z hz).1 hr with h' | h'
    · exact hzx h'
    · exact hzy h'
  have htree : arcsInto N (N.graph.target f) = {f} := by
    ext g
    rw [mem_arcsInto, mem_singleton]
    exact ⟨fun hg => arc_eq_of_target_eq hN hLevel hh hh₂ S.blob S.ne_reticulation hg rfl, fun hg => hg ▸ rfl⟩
  have hlen : 0 < θ.length f := hθ.1 f (by
    unfold RootedNetwork.IsTreeArc
    rw [indegree_eq_card, htree, card_singleton])
  exact ⟨isTL_pair_lift hN hθ hρ hxq hyq hxy hC hbx hby hdx hdy hoth hub,
    fun r hr => lt_of_pair_lift hN hθ hρ hxq hyq hxy hC hbx hby hdx hdy hoth htree hlen hub hr⟩

omit [Fintype V] [Fintype E] [Fintype X] [DecidableEq X] in
/-- Off a set of arcs, a path to what an arc dominates goes through the arc, if it starts above it. -/
theorem _root_.Phylogenetics.RootedNetwork.ReachesOff.to_source_of_dominated (hN : N.IsPhylogenetic) {D : Set E} {e : E}
    {u z : V} (hd : ¬ N.AvoidingReach e N.root z) (hu : ¬ N.graph.Reaches (N.graph.target e) u)
    (hp : N.ReachesOff D u z) : N.ReachesOff D u (N.graph.source e) := by
  induction hp with
  | refl =>
    rcases avoidingReach_or_reaches e (hN.root_reaches u) with h | h
    · exact absurd h hd
    · exact absurd h hu
  | @tail b c hub hbc ih =>
    obtain ⟨g, -, rfl, rfl⟩ := hbc
    by_cases hge : g = e
    · subst hge
      exact hub
    · exact ih fun hav => hd (hav.tail ⟨g, hge, rfl, rfl⟩)

omit [Fintype X] in
/-- **The tree with `k₂` deleted displays the quartet tree of the side of `k₁`.** The lineage of `a` follows `k₁`,
with what is on this side of the cycle: the arc `f` dominates the taxa `x`, `y` with `k₂` deleted, and no other taxon
of `q` is below it. -/
theorem splitOffAt (hN : N.IsPhylogenetic) (hBin : N.IsBinary) (hLevel : IsLevelOne N)
    (F : CycleFrame N q a v h T k₁ k₂ pL pR) {f : E} {x y : X} (S : IsCycleSide N q a v h T k₁ f x y)
    {s : QuartetTree X} (hsq : s.taxa = q) (hC : ({x, y} : Finset X) ∈ s.val) {D : Set E} (hk₂ : k₂ ∈ D) :
    N.SplitOffAt D f s := by
  subst hsq
  have C := F.cycle
  have hh := C.reticulation
  have hh₂ := F.two_le
  obtain ⟨eh, hehs, hehu, hehb⟩ := exists_child_arc hN hBin hLevel hh hh₂
  have hleaf : N.leaf a ≠ h := by
    intro he
    have := hN.leaf_indegree a
    rw [he] at this
    omega
  have hra : N.graph.Reaches (N.graph.target eh) (N.leaf a) := reaches_target_of_unique_out hehu F.below hleaf
  have hda := not_avoidingReach_of_isBridge hN hehb hra
  have hparent : ∀ {D' : Set E} {u : V}, k₂ ∈ D' → u ≠ h → ¬ N.graph.Reaches (N.graph.target eh) u →
      N.ReachesOff D' u (N.leaf a) → N.ReachesOff D' u (N.graph.source k₁) := by
    intro D' u hk hu hue hp
    have hph : N.ReachesOff D' u h := by
      have := hp.to_source_of_dominated hN hda hue
      rwa [hehs] at this
    rcases Relation.ReflTransGen.cases_tail hph with heq | ⟨c, hc, g, hg, hgs, hgt⟩
    · exact absurd heq.symm hu
    · rcases C.arcs g hgt with hg₁ | hg₂
      · rw [← hg₁, hgs]
        exact hc
      · exact absurd (hg₂ ▸ hk) hg
  refine ⟨{x, y}, hC, fun z hz => ?_, fun z hz => ?_⟩
  · have hzm := mem_coe.1 hz
    have hzq : z ∈ s.taxa := s.subset_taxa hC hzm
    have hrz : N.graph.Reaches (N.graph.target f) (sidePos N a k₁ z) := (S.iff z hzq).2 (by simpa using hzm)
    by_cases hza : z = a
    · rw [hza, sidePos_self] at hrz
      rw [hza]
      intro hp
      have hroot : ¬ N.graph.Reaches (N.graph.target eh) N.root := fun hr =>
        TOBQMC.Level1.target_ne_root hN eh (eq_root_of_reaches_root hN hr)
      have := hparent (Set.mem_insert_of_mem f hk₂) (reticulation_ne_root hN hh₂).symm hroot hp
      exact not_avoidingReach_of_blob hN hLevel hh hh₂ S.blob hrz (C.not_reaches_of_target₁ hN)
        this.avoidingReach_of_insert
    · rw [sidePos_of_ne hza] at hrz
      exact Dominates.dominatesOff (not_avoidingReach_of_blob hN hLevel hh hh₂ S.blob hrz (F.only z hzq hza))
  · rintro ⟨-, hr⟩
    obtain ⟨hzq, hzP⟩ := mem_sdiff.1 (mem_coe.1 hz)
    have hzo : ¬ N.graph.Reaches (N.graph.target f) (sidePos N a k₁ z) := fun hr' =>
      hzP (by simpa using (S.iff z hzq).1 hr')
    by_cases hza : z = a
    · rw [hza] at hr hzo
      rw [sidePos_self] at hzo
      have hne : ¬ N.graph.Reaches (N.graph.target eh) (N.graph.target f) := fun hc =>
        not_sameBlob_of_reaches_exit hN hehb (hehs ▸ hh) hc S.blob
      exact hzo (hparent hk₂ S.ne_reticulation hne hr).reaches
    · rw [sidePos_of_ne hza] at hzo
      exact hzo hr.reaches

omit [Fintype X] [DecidableEq X] in
/-- A vertex of the blob other than the top is on one side of the cycle only. -/
theorem exclusive (hN : N.IsPhylogenetic) (hLevel : IsLevelOne N) (F : CycleFrame N q a v h T k₁ k₂ pL pR) {w : V}
    (hw : SameBlob N v w) (hwT : w ≠ T) (h₁ : N.graph.Reaches w (N.graph.source k₁))
    (h₂ : N.graph.Reaches w (N.graph.source k₂)) : False := by
  have C := F.cycle
  rcases List.mem_cons.1 (C.mem_left_of_reaches hN hLevel F.two_le hw h₁) with h' | h'
  · exact hwT h'
  · rcases List.mem_cons.1 (C.swap.mem_left_of_reaches hN hLevel F.two_le hw h₂) with h'' | h''
    · exact hwT h''
    · exact C.disjoint _ h' h''

omit [Fintype X] [DecidableEq X] in
/-- Vertices of the blob on opposite sides of the cycle have nothing below them in common, other than below the
reticulation. -/
theorem false_of_opposite (hN : N.IsPhylogenetic) (hLevel : IsLevelOne N) (F : CycleFrame N q a v h T k₁ k₂ pL pR)
    {f : E} {u' z : V} (hb : SameBlob N v (N.graph.target f)) (hfT : N.graph.target f ≠ T) (hu' : SameBlob N v u')
    (hu'T : u' ≠ T) (h₁ : N.graph.Reaches (N.graph.target f) (N.graph.source k₁))
    (h₂ : N.graph.Reaches u' (N.graph.source k₂)) (hz : N.graph.Reaches (N.graph.target f) z)
    (hz' : N.graph.Reaches u' z) (hzh : ¬ N.graph.Reaches h z) : False := by
  have hd := not_avoidingReach_of_blob hN hLevel F.cycle.reticulation F.two_le hb hz hzh
  have hnu : ¬ N.graph.Reaches (N.graph.target f) u' := fun hr => F.exclusive hN hLevel hb hfT h₁ (hr.trans h₂)
  have hav : N.AvoidingReach f N.root u' := (avoidingReach_or_reaches f (hN.root_reaches u')).resolve_right hnu
  have hnav : ¬ N.AvoidingReach f u' z := fun h' => hd (Relation.ReflTransGen.trans hav h')
  have hs := reaches_source_of_not_avoidingReach hz' hnav
  exact F.exclusive hN hLevel hu' hu'T ((hs.trans (reaches_of_arc N f)).trans h₁) h₂

omit [Fintype X] [DecidableEq X] in
private theorem exists_ne_of_ne {x y a : X} (h : x ≠ y) : ∃ z, (z = x ∨ z = y) ∧ z ≠ a := by
  by_cases hxa : x = a
  · exact ⟨y, Or.inr rfl, fun h' => h (hxa.trans h'.symm)⟩
  · exact ⟨x, Or.inl rfl, hxa⟩

omit [Fintype X] in
/-- The cherries of the two sides are not complementary with the lineage `a` in the cherry of `k₁`. Both lowest
vertices are on the side of `k₁`, so one is below the other. -/
theorem false_of_complement (hN : N.IsPhylogenetic) (hLevel : IsLevelOne N) (F : CycleFrame N q a v h T k₁ k₂ pL pR)
    {f f' : E} {x y x' y' : X} (S : IsCycleSide N q a v h T k₁ f x y) (S' : IsCycleSide N q a v h T k₂ f' x' y')
    (hcompl : ∀ z ∈ q, (z = x' ∨ z = y') ↔ ¬ (z = x ∨ z = y)) (ha : a = x ∨ a = y) : False := by
  have C := F.cycle
  have ha₁ : N.graph.Reaches (N.graph.target f) (N.graph.source k₁) := by
    have := (S.iff a F.mem).2 ha
    rwa [sidePos_self] at this
  have hn₂ : ¬ N.graph.Reaches (N.graph.target f') (N.graph.source k₂) := fun h' =>
    (hcompl a F.mem).1 ((S'.iff a F.mem).1 (by rw [sidePos_self]; exact h')) ha
  have h₂ : N.graph.Reaches (N.graph.target f') (N.graph.source k₁) :=
    (C.reaches_source hN hLevel F.two_le S'.blob S'.ne_reticulation).resolve_right hn₂
  rcases C.left.total (C.mem_left_of_reaches hN hLevel F.two_le S.blob ha₁)
    (C.mem_left_of_reaches hN hLevel F.two_le S'.blob h₂) with hr | hr
  · have hx' := (S'.iff x' S'.mem₁).2 (Or.inl rfl)
    have hxa : x' ≠ a := fun h' => (hcompl a F.mem).1 (Or.inl h'.symm) ha
    rw [sidePos_of_ne hxa] at hx'
    have := (S.iff x' S'.mem₁).1 (by rw [sidePos_of_ne hxa]; exact hr.trans hx')
    exact (hcompl x' S'.mem₁).1 (Or.inl rfl) this
  · obtain ⟨z, hzC, hza⟩ := exists_ne_of_ne (a := a) S.ne
    have hzq : z ∈ q := by
      rcases hzC with rfl | rfl
      · exact S.mem₁
      · exact S.mem₂
    have hz := (S.iff z hzq).2 hzC
    rw [sidePos_of_ne hza] at hz
    have := (S'.iff z hzq).1 (by rw [sidePos_of_ne hza]; exact hr.trans hz)
    exact (hcompl z hzq).1 this hzC

omit [Fintype X] in
/-- **The two sides of the cycle give two different quartet trees.** The cherries of one quartet tree are equal or
complementary. If they are equal, the two lowest vertices are on opposite sides, and they share a taxon that is not
below the reticulation. If they are complementary, they are on one side, nested, and that puts three lineages below
one. -/
theorem side_ne (hN : N.IsPhylogenetic) (hLevel : IsLevelOne N) (F : CycleFrame N q a v h T k₁ k₂ pL pR) {f f' : E}
    {x y x' y' : X} (S : IsCycleSide N q a v h T k₁ f x y) (S' : IsCycleSide N q a v h T k₂ f' x' y')
    {s s' : QuartetTree X} (hs : s.taxa = q) (hC : ({x, y} : Finset X) ∈ s.val)
    (hC' : ({x', y'} : Finset X) ∈ s'.val) : s ≠ s' := by
  rintro rfl
  have C := F.cycle
  have hC'' : ({x', y'} : Finset X) = {x, y} ∨ ({x', y'} : Finset X) = s.taxa \ {x, y} := by
    have h' := hC'
    rw [s.eq_pair_of_mem hC] at h'
    simpa using h'
  rcases hC'' with heq | heq
  · have hiffz : ∀ z, (z = x' ∨ z = y') ↔ (z = x ∨ z = y) := fun z => by
      have := Finset.ext_iff.1 heq z
      simpa using this
    obtain ⟨z, hzC, hza⟩ := exists_ne_of_ne (a := a) S.ne
    have hzq : z ∈ q := by
      rcases hzC with rfl | rfl
      · exact S.mem₁
      · exact S.mem₂
    have hz₁ := (S.iff z hzq).2 hzC
    rw [sidePos_of_ne hza] at hz₁
    have hz₂ := (S'.iff z hzq).2 ((hiffz z).2 hzC)
    rw [sidePos_of_ne hza] at hz₂
    by_cases haC : a = x ∨ a = y
    · have h₁ := (S.iff a F.mem).2 haC
      rw [sidePos_self] at h₁
      have h₂ := (S'.iff a F.mem).2 ((hiffz a).2 haC)
      rw [sidePos_self] at h₂
      exact F.false_of_opposite hN hLevel S.blob S.ne_top S'.blob S'.ne_top h₁ h₂ hz₁ hz₂ (F.only z hzq hza)
    · have hn₁ : ¬ N.graph.Reaches (N.graph.target f) (N.graph.source k₁) := fun h' =>
        haC ((S.iff a F.mem).1 (by rw [sidePos_self]; exact h'))
      have hn₂ : ¬ N.graph.Reaches (N.graph.target f') (N.graph.source k₂) := fun h' =>
        haC ((hiffz a).1 ((S'.iff a F.mem).1 (by rw [sidePos_self]; exact h')))
      have h₁ := (C.reaches_source hN hLevel F.two_le S.blob S.ne_reticulation).resolve_left hn₁
      have h₂ := (C.reaches_source hN hLevel F.two_le S'.blob S'.ne_reticulation).resolve_right hn₂
      exact F.false_of_opposite hN hLevel S'.blob S'.ne_top S.blob S.ne_top h₂ h₁ hz₂ hz₁ (F.only z hzq hza)
  · have hcompl : ∀ z ∈ q, (z = x' ∨ z = y') ↔ ¬ (z = x ∨ z = y) := fun z hz => by
      have := Finset.ext_iff.1 heq z
      simp only [mem_insert, mem_singleton, mem_sdiff, hs, hz, true_and] at this
      exact this
    by_cases haC : a = x ∨ a = y
    · exact F.false_of_complement hN hLevel S S' hcompl haC
    · refine F.swap.false_of_complement hN hLevel S' S (fun z hz => ?_) ((hcompl a F.mem).2 haC)
      have := hcompl z hz
      tauto

/-- **The mixture over the two parents of the reticulation**: the lineage of `a` is the only one to pass through it.
-/
theorem cherryMass_mix (hN : N.IsPhylogenetic) (hBin : N.IsBinary) (hLevel : IsLevelOne N) (hθ : N.IsMetric θ)
    (hρ : 0 ≤ ρ ∧ ρ ≤ 1) (F : CycleFrame N q a v h T k₁ k₂ pL pR) (r : QuartetTree X) :
    cherryMass N θ ρ (placeInj q N.leaf) r =
      θ.inheritance k₁ * cherryMass N θ ρ (placeInj q (sidePos N a k₁)) r +
        θ.inheritance k₂ * cherryMass N θ ρ (placeInj q (sidePos N a k₂)) r := by
  have C := F.cycle
  have hh := C.reticulation
  have hh₂ := F.two_le
  obtain ⟨eh, hehs, hehu, hehb⟩ := exists_child_arc hN hBin hLevel hh hh₂
  have hleaf : N.leaf a ≠ h := by
    intro he
    have := hN.leaf_indegree a
    rw [he] at this
    omega
  have hra : N.graph.Reaches (N.graph.target eh) (N.leaf a) := reaches_target_of_unique_out hehu F.below hleaf
  have hlift := cherryMass_placeInj_lift (θ := θ) (ρ := ρ) hN hθ hρ (q := q) (P := N.leaf) F.mem (e := eh) hra
    (not_avoidingReach_of_isBridge hN hehb hra)
    (fun y hy hya hr => F.only y hy hya (hehs ▸ (reaches_of_arc N eh).trans hr)) r
  rw [hehs] at hlift
  have hmix := cherryMass_one_reticulation (θ := θ) (ρ := ρ) hN hθ hρ (q := q) (P := Function.update N.leaf a h) F.mem
    (reticulation_ne_root hN hh₂) (Function.update_self _ _ _)
    (fun z hz hza => by rw [Function.update_of_ne hza]; exact F.only z hz hza) C.target₁ C.target₂ C.ne C.arcs r
  simp only [Function.update_idem] at hmix
  rw [hlift, hmix]
  rfl

end CycleFrame

omit [Fintype V] [Fintype E] [Fintype X] [DecidableEq X] in
theorem nonempty_parentChoice (hN : N.IsPhylogenetic) : Nonempty N.ParentChoice := by
  have := hN.finite_arcs
  have hex : ∀ w : {w : V // w ≠ N.root}, ∃ e : E, N.graph.target e = w.val := fun w =>
    (N.graph.one_le_indegree_iff _).1 (hN.nonroot_indegree _ w.2)
  choose c₀ hc₀ using hex
  exact ⟨fun w => ⟨c₀ w, hc₀ w⟩⟩

omit [Fintype V] [Fintype E] [Fintype X] [DecidableEq X] in
/-- A choice of parents that leaves out `k'`, keeping `k` at its target. -/
theorem exists_deletion_keeping (hN : N.IsPhylogenetic) {k k' : E} (ht : N.graph.target k' = N.graph.target k)
    (hne : k' ≠ k) :
    ∃ D : Set E, N.IsDeletion D ∧ (∀ f g, f ∉ D → g ∉ D → N.graph.target f = N.graph.target g → f = g) ∧ k' ∈ D := by
  obtain ⟨c₀⟩ := nonempty_parentChoice hN
  let c : N.ParentChoice := fun w => if hw : w.val = N.graph.target k then ⟨k, hw.symm⟩ else c₀ w
  refine ⟨N.deletedArcs c, isDeletion_deletedArcs hN c, fun f g hf hg hfg => eq_of_notMem_deletedArcs hN hf hg hfg, ?_⟩
  refine mem_deletedArcs_of_ne (v := ⟨N.graph.target k, TOBQMC.Level1.target_ne_root hN k⟩) ht ?_
  simpa [c] using hne

/-- **A `4₁`-cycle, by the two sides of its cycle.** On a binary level-1 network, a set of four taxa with no cut-edge
split has exactly two quartet trees that the grove displays, and the third has a strictly smaller concordance factor
than each of them, for all valid parameters. The mixture over the two parents of the reticulation (`cherryMass_mix`)
is what the lineage of the only taxon below the reticulation does, and each term is tree-like towards one of the two
trees (`isTL_and_lt`). -/
theorem exists_two_displayed (hN : N.IsPhylogenetic) (hBin : N.IsBinary) (hLevel : IsLevelOne N) {q : Finset X}
    (hq : #q = 4) (hnt : ¬ IsTreelike N q) :
    ∃ s₁ s₂ : QuartetTree X, s₁.taxa = q ∧ s₂.taxa = q ∧ s₁ ≠ s₂ ∧ GroveDisplays N s₁ ∧ GroveDisplays N s₂ ∧
      (∀ s : QuartetTree X, s.taxa = q → GroveDisplays N s → s = s₁ ∨ s = s₂) ∧
      ∀ (θ : MetricData E) (ρ : ℝ), N.IsMetric θ → 0 ≤ ρ ∧ ρ ≤ 1 → ∀ s₀ : QuartetTree X, s₀.taxa = q → s₀ ≠ s₁ →
        s₀ ≠ s₂ → nmscCF N θ ρ s₀ < nmscCF N θ ρ s₁ ∧ nmscCF N θ ρ s₀ < nmscCF N θ ρ s₂ := by
  obtain ⟨v, h, hh, hh₂, hdist, a, ⟨ha, hah⟩, hu⟩ := exists_cycle_of_not_isTreelike hN hBin hLevel hq hnt
  obtain ⟨T, k₁, k₂, pL, pR, C⟩ := exists_blobCycle hN hBin hLevel hh hh₂
  have F : CycleFrame N q a v h T k₁ k₂ pL pR :=
    ⟨hq, hh₂, hdist, ha, hah, fun z hz hza hr => hza (hu z ⟨hz, hr⟩), C⟩
  obtain ⟨f, x, y, S⟩ := F.exists_isCycleSide hN hBin
  obtain ⟨f', x', y', S'⟩ := F.swap.exists_isCycleSide hN hBin
  have hquartet : ∀ {x y : X}, x ∈ q → y ∈ q → x ≠ y →
      ∃ s : QuartetTree X, s.taxa = q ∧ ({x, y} : Finset X) ∈ s.val := by
    intro x y hx hy hxy
    have hsub : ({x, y} : Finset X) ⊆ q := by
      intro z hz
      simp only [mem_insert, mem_singleton] at hz
      rcases hz with rfl | rfl
      · exact hx
      · exact hy
    refine ⟨quartetOfCherry q {x, y} hq hsub (card_pair hxy), quartetOfCherry_taxa _ _ _ _ _, ?_⟩
    rw [quartetOfCherry_val]
    simp
  obtain ⟨s₁, hs₁, hC₁⟩ := hquartet S.mem₁ S.mem₂ S.ne
  obtain ⟨s₂, hs₂, hC₂⟩ := hquartet S'.mem₁ S'.mem₂ S'.ne
  have hne : s₁ ≠ s₂ := F.side_ne hN hLevel S S' hs₁ hC₁ hC₂
  have hsp₁ : ∀ {D : Set E}, k₂ ∈ D → N.SplitOffAt D f s₁ := fun hD => F.splitOffAt hN hBin hLevel S hs₁ hC₁ hD
  have hsp₂ : ∀ {D : Set E}, k₁ ∈ D → N.SplitOffAt D f' s₂ := fun hD =>
    F.swap.splitOffAt hN hBin hLevel S' hs₂ hC₂ hD
  have ht₁₂ : N.graph.target k₁ = N.graph.target k₂ := C.target₁.trans C.target₂.symm
  refine ⟨s₁, s₂, hs₁, hs₂, hne, ?_, ?_, ?_, ?_⟩
  · obtain ⟨D, hD, hun, hk⟩ := exists_deletion_keeping hN ht₁₂.symm C.ne.symm
    exact ⟨D, hD, hun, f, hsp₁ hk⟩
  · obtain ⟨D, hD, hun, hk⟩ := exists_deletion_keeping hN ht₁₂ C.ne
    exact ⟨D, hD, hun, f', hsp₂ hk⟩
  · rintro s hs ⟨D, hD, hun, e, hse⟩
    obtain ⟨g, hg, hgt⟩ := hD.parent h (reticulation_ne_root hN hh₂)
    rcases C.arcs g hgt with hg₁ | hg₂
    · have hk₂ : k₂ ∈ D := by
        by_contra hc
        exact C.ne (hun _ _ (hg₁ ▸ hg) hc ht₁₂)
      exact Or.inl (eq_of_splitOffAt hN hD (hs.trans hs₁.symm) hse (hsp₁ hk₂))
    · have hk₁ : k₁ ∈ D := by
        by_contra hc
        exact C.ne (hun _ _ hc (hg₂ ▸ hg) ht₁₂)
      exact Or.inr (eq_of_splitOffAt hN hD (hs.trans hs₂.symm) hse (hsp₂ hk₁))
  · intro θ ρ hθ hρ s₀ hs₀ h₁ h₂
    obtain ⟨tl₁, lt₁⟩ := F.isTL_and_lt hN hLevel hθ hρ S hs₁ hC₁
    obtain ⟨tl₂, lt₂⟩ := F.swap.isTL_and_lt hN hLevel hθ hρ S' hs₂ hC₂
    have hmix := F.cherryMass_mix (θ := θ) (ρ := ρ) hN hBin hLevel hθ hρ
    have hγ₁ : 0 < θ.inheritance k₁ :=
      hθ.2.2.2.1 k₁ (by unfold RootedNetwork.IsHybridArc; rw [C.target₁]; exact hh₂)
    have hγ₂ : 0 < θ.inheritance k₂ :=
      hθ.2.2.2.1 k₂ (by unfold RootedNetwork.IsHybridArc; rw [C.target₂]; exact hh₂)
    rw [nmscCF_eq_cherryMass hN hθ hρ s₀, nmscCF_eq_cherryMass hN hθ hρ s₁, nmscCF_eq_cherryMass hN hθ hρ s₂, hs₀, hs₁,
      hs₂, ← placeInj_leaf, hmix, hmix, hmix]
    have hm₁₂ : s₂ ∈ s₁.alternatives := QuartetTree.mem_alternatives.2 ⟨hs₂.trans hs₁.symm, hne.symm⟩
    have hm₁₀ : s₀ ∈ s₁.alternatives := QuartetTree.mem_alternatives.2 ⟨hs₀.trans hs₁.symm, h₁⟩
    have hm₂₁ : s₁ ∈ s₂.alternatives := QuartetTree.mem_alternatives.2 ⟨hs₁.trans hs₂.symm, hne⟩
    have hm₂₀ : s₀ ∈ s₂.alternatives := QuartetTree.mem_alternatives.2 ⟨hs₀.trans hs₂.symm, h₂⟩
    have a₁ := lt₁ s₀ hm₁₀
    have a₂ := tl₁.2 s₀ hm₁₀ s₂ hm₁₂
    have b₁ := lt₂ s₀ hm₂₀
    have b₂ := tl₂.2 s₀ hm₂₀ s₁ hm₂₁
    constructor
    · have := mul_lt_mul_of_pos_left a₁ hγ₁
      rw [b₂]
      linarith
    · have := mul_lt_mul_of_pos_left b₁ hγ₂
      rw [a₂]
      linarith

/-- **Part 3 of Proposition 9, its topological half.** On a binary level-1 network, a set of four taxa with no
cut-edge split has a quartet tree that the grove does not display, with an alternative that it does. -/
theorem exists_not_groveDisplays (hN : N.IsPhylogenetic) (hBin : N.IsBinary) (hLevel : IsLevelOne N) {q : Finset X}
    (hq : #q = 4) (hnt : ¬ IsTreelike N q) :
    ∃ s ∈ treesOn q, ¬ GroveDisplays N s ∧ ∃ r ∈ s.alternatives, GroveDisplays N r := by
  obtain ⟨s₁, s₂, hs₁, hs₂, hne, hg₁, -, huniq, -⟩ := exists_two_displayed hN hBin hLevel hq hnt
  obtain ⟨r₁, r₂, hr, ha⟩ := QuartetTests.QuartetTree.exists_alternatives s₁
  have hm : s₂ ∈ s₁.alternatives := QuartetTree.mem_alternatives.2 ⟨hs₂.trans hs₁.symm, hne.symm⟩
  obtain ⟨s₀, hs₀a, hs₀ne⟩ : ∃ s₀ ∈ s₁.alternatives, s₀ ≠ s₂ := by
    rw [ha] at hm ⊢
    simp only [mem_insert, mem_singleton] at hm
    rcases hm with he | he
    · exact ⟨r₂, by simp, fun h' => hr (he.symm.trans h'.symm)⟩
    · exact ⟨r₁, by simp, fun h' => hr (h'.trans he)⟩
  obtain ⟨hs₀t, hs₀1⟩ := QuartetTree.mem_alternatives.1 hs₀a
  have hs₀q : s₀.taxa = q := hs₀t.trans hs₁
  refine ⟨s₀, mem_treesOn.2 hs₀q, fun hg => ?_, s₁, QuartetTree.mem_alternatives.2 ⟨hs₁.trans hs₀q.symm, hs₀1.symm⟩,
    hg₁⟩
  rcases huniq s₀ hs₀q hg with h' | h'
  · exact hs₀1 h'
  · exact hs₀ne h'

/-- **Part 3 of Proposition 9, on the concordance factors.** The quartet tree that the grove does not display has the
strictly smallest concordance factor. -/
theorem isStrictMin_of_not_groveDisplays (hN : N.IsPhylogenetic) (hBin : N.IsBinary) (hLevel : IsLevelOne N)
    (hθ : N.IsMetric θ) (hρ : 0 ≤ ρ ∧ ρ ≤ 1) {s : QuartetTree X} (hnt : ¬ IsTreelike N s.taxa)
    (hng : ¬ GroveDisplays N s) : IsStrictMin (nmscCF N θ ρ) s := by
  intro r hr
  obtain ⟨s₁, s₂, hs₁, hs₂, hne, hg₁, hg₂, -, hmass⟩ := exists_two_displayed hN hBin hLevel s.card_taxa hnt
  have hs1 : s ≠ s₁ := fun h' => hng (h' ▸ hg₁)
  have hs2 : s ≠ s₂ := fun h' => hng (h' ▸ hg₂)
  obtain ⟨h₁, h₂⟩ := hmass θ ρ hθ hρ s rfl hs1 hs2
  obtain ⟨r₁, r₂, hrr, ha⟩ := QuartetTests.QuartetTree.exists_alternatives s
  have hm₁ : s₁ ∈ s.alternatives := QuartetTree.mem_alternatives.2 ⟨hs₁, hs1.symm⟩
  have hm₂ : s₂ ∈ s.alternatives := QuartetTree.mem_alternatives.2 ⟨hs₂, hs2.symm⟩
  rw [ha] at hr hm₁ hm₂
  simp only [mem_insert, mem_singleton] at hr hm₁ hm₂
  have hcases : r = s₁ ∨ r = s₂ := by grind
  rcases hcases with rfl | rfl
  · exact h₁
  · exact h₂

/-- **Proposition 9 of NANUQ** (`nanuq:proposition9`), parts 1 and 3, on binary level-1 networks, for the network
multispecies coalescent with any `0 ≤ ρ ≤ 1` and any valid parameters. The source prints no proof: it takes the
proposition from its references [1, 3] (line 462). The proof here is the placement calculus of `Placement.lean`.

Part 2 is not included: its equality is `NMSC.cut_alternatives`, and its bound `CF_AB|CD ≥ 1/6` is not used.

Departure from the paper, in the statement. The source states this on a quartet network `N⁺`, with the conditions on
`N⁻` and `N_c⁻`. Here it is on a set of four taxa of a whole network, the concordance factor being the marginal of the
gene tree on all the taxa, and the conditions are by blocks, cut edges and the grove. That these conditions agree with
the source's is not proved: see the section below. -/
theorem proposition9 (hN : N.IsPhylogenetic) (hBin : N.IsBinary) (hLevel : IsLevelOne N) (hθ : N.IsMetric θ)
    (hρ : 0 ≤ ρ ∧ ρ ≤ 1) : Proposition9 N (nmscCF N θ ρ) where
  no_three_two := fun _ hs h3 _ hr => nmscCF_lt_of_no_three_two hN hBin hLevel hθ hρ
    (inducedCutSplit_of_displays_treeOfBlobs hN hs) h3 hr
  cycle_exists := fun _ hq hnt => exists_not_groveDisplays hN hBin hLevel hq hnt
  cycle_min := fun _ hnt hng => isStrictMin_of_not_groveDisplays hN hBin hLevel hθ hρ hnt hng

/-! ### The definitions by blocks and the source's by contraction

The source reads `Q̃` and the types of cycle on `N_c⁻` and `N⁻`, the unrooted induced network with its 2- and 3-cycles
contracted. Neither is formalized. `HasThreeTwoCycle` and `networkClass` are stated instead by blocks, cut edges and
the grove, and **that these agree with the source's definitions by contraction is not proved**. What is proved, and is
what one would use to prove it, is the following.

* `not_isTreelike_iff`: no cut-edge split on the induced network is the same as four taxa in distinct blocks at a blob
  with a reticulation, with one taxon below it, so four pendant parts around a cycle: the type `4₁`.
* `exists_two_displayed`: there the grove displays exactly two quartet trees.
* `networkClass_eq_cycle`: there `networkClass` is the third one.
* `networkClass_eq_tree`: with a cut-edge split on the induced network, `networkClass` is its quartet tree, and it is
  the only one.
* `isTreelike_of_hasThreeTwoCycle`: a `3₂`-cycle has a cut-edge split, with the taxa below the reticulation on one
  side, so it gives a quartet tree and not a 4-cycle, as contracting a 3-cycle does.
* `networkClass_ne_star_of_binary`: the star tree does not occur on a binary level-1 network. -/

omit [Fintype E] in
/-- With a parent choice, whose tree displays the cut-edge splits, the split of a set of four taxa is unique. -/
theorem eq_of_inducedCutSplit [Nonempty X] (hN : N.IsPhylogenetic) {s s' : QuartetTree X} (hs : InducedCutSplit N s)
    (hs' : InducedCutSplit N s') (ht : s.taxa = s'.taxa) : s = s' := by
  obtain ⟨c⟩ := nonempty_parentChoice hN
  exact (isUnrootedTree_displayedSides hN c).displays_unique (displays_displayedSides_of_inducedCutSplit hN c hs)
    (displays_displayedSides_of_inducedCutSplit hN c hs') ht

omit [Fintype E] in
/-- On a cut-edge split of the induced network, `networkClass` is its quartet tree. -/
theorem networkClass_eq_tree [Nonempty X] (hN : N.IsPhylogenetic) {s : QuartetTree X} (hs : InducedCutSplit N s) :
    networkClass N s.taxa = .tree s := by
  have hex : ∃ r ∈ treesOn s.taxa, InducedCutSplit N r := ⟨s, mem_treesOn.2 rfl, hs⟩
  unfold networkClass
  rw [dite_eq_left hex]
  congr 1
  exact eq_of_inducedCutSplit hN hex.choose_spec.2 hs (mem_treesOn.1 hex.choose_spec.1)

/-- With no cut-edge split, only one quartet tree is not displayed by the grove. -/
theorem eq_of_not_groveDisplays (hN : N.IsPhylogenetic) (hBin : N.IsBinary) (hLevel : IsLevelOne N)
    {s s' : QuartetTree X} (hnt : ¬ IsTreelike N s.taxa) (hs : ¬ GroveDisplays N s) (hs' : ¬ GroveDisplays N s')
    (ht : s'.taxa = s.taxa) :
    s' = s := by
  by_contra hne
  obtain ⟨s₁, s₂, hs₁, hs₂, hne₁₂, hg₁, hg₂, -, -⟩ := exists_two_displayed hN hBin hLevel s.card_taxa hnt
  have hs1 : s ≠ s₁ := fun h' => hs (h' ▸ hg₁)
  have hs2 : s ≠ s₂ := fun h' => hs (h' ▸ hg₂)
  have hs1' : s' ≠ s₁ := fun h' => hs' (h' ▸ hg₁)
  have hs2' : s' ≠ s₂ := fun h' => hs' (h' ▸ hg₂)
  obtain ⟨r₁, r₂, hrr, ha⟩ := QuartetTests.QuartetTree.exists_alternatives s
  have hm₁ : s₁ ∈ s.alternatives := QuartetTree.mem_alternatives.2 ⟨hs₁, hs1.symm⟩
  have hm₂ : s₂ ∈ s.alternatives := QuartetTree.mem_alternatives.2 ⟨hs₂, hs2.symm⟩
  have hm₃ : s' ∈ s.alternatives := QuartetTree.mem_alternatives.2 ⟨ht, hne⟩
  rw [ha] at hm₁ hm₂ hm₃
  simp only [mem_insert, mem_singleton] at hm₁ hm₂ hm₃
  grind

/-- On a `4₁`-cycle, `networkClass` is the quartet tree that the grove does not display. -/
theorem networkClass_eq_cycle (hN : N.IsPhylogenetic) (hBin : N.IsBinary) (hLevel : IsLevelOne N) {s : QuartetTree X}
    (hnt : ¬ IsTreelike N s.taxa) (hng : ¬ GroveDisplays N s) : networkClass N s.taxa = .cycle s := by
  have hex := exists_not_groveDisplays hN hBin hLevel s.card_taxa hnt
  have h₁ : ¬ ∃ r ∈ treesOn s.taxa, InducedCutSplit N r := hnt
  unfold networkClass
  rw [dite_eq_right h₁, dite_eq_left hex]
  congr 1
  exact eq_of_not_groveDisplays hN hBin hLevel hnt hng hex.choose_spec.2.1 (mem_treesOn.1 hex.choose_spec.1)

/-- On a binary level-1 network `networkClass` has no star tree. -/
theorem networkClass_ne_star_of_binary (hN : N.IsPhylogenetic) (hBin : N.IsBinary) (hLevel : IsLevelOne N)
    {q : Finset X} (hq : #q = 4) : networkClass N q ≠ .star :=
  networkClass_ne_star (fun _ hq' hnt => exists_not_groveDisplays hN hBin hLevel hq' hnt) hq

/-- A `3₂`-cycle has a cut-edge split on the induced network: the arc below the reticulation has the two taxa on one
side. -/
theorem isTreelike_of_hasThreeTwoCycle (hN : N.IsPhylogenetic) (hBin : N.IsBinary) (hLevel : IsLevelOne N)
    {q : Finset X} (hq : #q = 4) (h3 : HasThreeTwoCycle N q) : IsTreelike N q := by
  obtain ⟨h, hh₂, hcard, -⟩ := h3
  obtain ⟨eh, hehs, hehu, hehb⟩ := exists_child_arc hN hBin hLevel (v := h) .refl hh₂
  have hcut : N.HasCutSplit
      (((univ.filter fun x => N.graph.Reaches (N.graph.target eh) (N.leaf x) : Finset X)) : Set X) :=
    ⟨eh, {u | N.graph.Reaches (N.graph.target eh) u}, isBridge_crosses_iff hN hehb, by ext x; simp⟩
  refine isTreelike_of_hasCutSplit hN hcut hq ?_
  have hset : (univ.filter fun x => N.graph.Reaches (N.graph.target eh) (N.leaf x)) ∩ q =
      q.filter fun x => N.graph.Reaches h (N.leaf x) := by
    ext x
    simp only [mem_inter, mem_filter, mem_univ, true_and]
    constructor
    · rintro ⟨hr, hx⟩
      exact ⟨hx, hehs ▸ (reaches_of_arc N eh).trans hr⟩
    · rintro ⟨hx, hr⟩
      refine ⟨reaches_target_of_unique_out hehu hr ?_, hx⟩
      intro he
      have := hN.leaf_indegree x
      rw [he] at this
      omega
  rw [hset]
  exact hcard

/-! ### Theorem 36 -/

section Theorem36

open Filter Topology

/-- The hypotheses of Theorem 36 give what the T3 test needs, in `TINNiK/T3.lean`, on a binary level-1 network. -/
theorem t3Detectable [Nonempty X] (hN : N.IsPhylogenetic) (hBin : N.IsBinary) (hLevel : IsLevelOne N)
    (hθ : N.IsMetric θ) (hρ : 0 ≤ ρ ∧ ρ ≤ 1) (h32 : ThreeTwoTreelike N (nmscCF N θ ρ))
    (hcen : TINNiK.NoCentroidCF (nmscCF N θ ρ)) :
    TINNiK.T3Detectable N (nmscCF N θ ρ) :=
  t3Detectable_of_proposition9 hN hLevel hθ hρ (proposition9 hN hBin hLevel hθ hρ) h32 hcen

/-- **Theorem 36** (`nanuq:theorem36`), the part that is mathematics. "Under the NMSC model on a binary level-1 metric
phylogenetic network `N⁺`, for numerical parameters in which all induced quartet networks with `3₂`-cycles are
tree-like, there exists a sequence `α₁, α₂, …`, with `0 < α_m < 1` and `α_m → 0` such that for any `0 < β < 1` the
NANUQ algorithm with significance levels `α_m` and `β` on a data set of `m` gene trees will, with probability
approaching 1 as `m → ∞`, infer the binary unrooted phylogenetic network associated to `N⁺` by Theorem 34."

The conclusion here is what the source's proof shows: the distance of Step 3 exactly agrees with the theoretical
quartet distance (line 2009). `theorem36_output` gives the steps after it. The hypotheses are as follows.

* `h32`, the hypothesis of the theorem as printed.
* `hcen`, not in the source. **Correction of the statement**: tree-like in the sense of Definition 8 includes the
  centroid, which a `3₂`-cycle reaches (`figure5_centroid`). There the theorem as printed fails, at the level of the
  distance (`not_theorem36AsPrinted`). For generic parameters it holds (`theorem36_generic`).

Proposition 9 is proved (`proposition9`), for binary level-1 networks. The level-1 hypothesis is used also in
`isT1Strict_of_inducedCutSplit`.

The proof follows the source. The star test (`tendsto_starPValue_lt`) and the second test on a tree-like concordance
factor (`tendsto_maxCount_t3`) are as printed; off the null the statistic grows like `m d` (`tendsto_half_lt_t3Stat`).
Departure from the paper: `α'_m` and `α_m` of the source are changed as `tendsto_t3PValue_lt_level` and
`exists_levels` say, the second since the printed choice of a minimum does not work (`not_rejects_at_minimum`). -/
theorem theorem36 [Nonempty X] (hN : N.IsPhylogenetic) (hBin : N.IsBinary) (hLevel : IsLevelOne N) (hθ : N.IsMetric θ)
    (h32 : ThreeTwoTreelike N (nmscCF N θ 0)) (hcen : TINNiK.NoCentroidCF (nmscCF N θ 0)) :
    ∃ α : ℕ → ℝ, (∀ m, 0 < α m) ∧ (∀ m, 1 ≤ m → α m < 1) ∧ Tendsto α atTop (𝓝 0) ∧
      ∀ β : ℝ, 0 < β → β < 1 → ∀ mlT mlC : (QuartetTree X → ℝ) → Finset X → QuartetTree X,
        IsMaxCountSelection mlT → IsMinCountSelection mlC →
        Tendsto (fun m => iidProb (geneTreeDist N θ 0) m fun ω =>
          (∀ q : Finset X, q.card = 4 → classify mlT mlC (α m) β (quartetCount unroot ω) q = networkClass N q) ∧
            nanuqDistance (classify mlT mlC (α m) β (quartetCount unroot ω)) = networkDistance N)
          atTop (𝓝 1) :=
  theorem36_of_proposition9 hN hLevel hθ (proposition9 hN hBin hLevel hθ ⟨le_rfl, zero_le_one⟩) h32 hcen

/-- **The steps after the distance.** NeighborNet and the Circular Network algorithm (Steps 4, 5), with the reading of
the splits graph by Theorem 34, are not formalized. Whatever they are, they compute a function `A` of the distance, so
that if they give the wanted object `y` on the theoretical distance, as the source's Corollary 24 and Theorem 34 and
the references [6, 7] say, they give it with probability tending to one on the sample. The hypothesis `hA` is that
statement. -/
theorem theorem36_output [Nonempty X] (hN : N.IsPhylogenetic) (hBin : N.IsBinary) (hLevel : IsLevelOne N)
    (hθ : N.IsMetric θ) (h32 : ThreeTwoTreelike N (nmscCF N θ 0)) (hcen : TINNiK.NoCentroidCF (nmscCF N θ 0)) :
    ∃ α : ℕ → ℝ, (∀ m, 0 < α m) ∧ (∀ m, 1 ≤ m → α m < 1) ∧ Tendsto α atTop (𝓝 0) ∧
      ∀ β : ℝ, 0 < β → β < 1 → ∀ mlT mlC : (QuartetTree X → ℝ) → Finset X → QuartetTree X,
        IsMaxCountSelection mlT → IsMinCountSelection mlC →
        ∀ {Y : Type*} (A : (X → X → ℝ) → Y) (y : Y), A (networkDistance N) = y →
        Tendsto (fun m => iidProb (geneTreeDist N θ 0) m fun ω =>
          A (nanuqDistance (classify mlT mlC (α m) β (quartetCount unroot ω))) = y) atTop (𝓝 1) :=
  theorem36_output_of_proposition9 hN hLevel hθ (proposition9 hN hBin hLevel hθ ⟨le_rfl, zero_le_one⟩) h32 hcen

/-- **Theorem 36 for generic parameters**, with the hypothesis as printed. The centroid is excluded on a null set of
parameters of a binary network (`TINNiK.isGenericNull_centroid`). -/
theorem theorem36_generic [Nonempty X] (hN : N.IsPhylogenetic) (hBin : N.IsBinary) (hLevel : IsLevelOne N) :
    ∃ A : Set (MetricData E), External.AllmanEtAl2023.IsGenericNull N A ∧
      ∀ θ, N.IsMetric θ → θ ∉ A → ThreeTwoTreelike N (nmscCF N θ 0) →
      ∃ α : ℕ → ℝ, (∀ m, 0 < α m) ∧ (∀ m, 1 ≤ m → α m < 1) ∧ Tendsto α atTop (𝓝 0) ∧
        ∀ β : ℝ, 0 < β → β < 1 → ∀ mlT mlC : (QuartetTree X → ℝ) → Finset X → QuartetTree X,
          IsMaxCountSelection mlT → IsMinCountSelection mlC →
          Tendsto (fun m => iidProb (geneTreeDist N θ 0) m fun ω =>
            nanuqDistance (classify mlT mlC (α m) β (quartetCount unroot ω)) = networkDistance N)
            atTop (𝓝 1) := by
  obtain ⟨A, hA, h⟩ := theorem36_generic_of_proposition9 (X := X) hN hBin hLevel
  exact ⟨A, hA, fun θ hθ hθA h32 => h θ hθ hθA (proposition9 hN hBin hLevel hθ ⟨le_rfl, zero_le_one⟩) h32⟩

end Theorem36

end External.AllmanBanosRhodes2019
