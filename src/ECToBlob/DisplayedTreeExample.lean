module

public import Basic.FinNetwork
public import Basic.NMSCChain
public import ECToBlob.DisplayedTree
public import ECToBlob.Section3Observations

/-!
# ECToBlob Theorem 8.2 for Cauchy and CBC on the displayed tree model: the counterexamples

Two networks with a 4-cycle and a cut edge, given by tables of arcs:

* `Binary.net`, on the taxa `a, b, c, d, e = 0, …, 4`: a binary network, with the cut edge `de|abc` and a 4-cycle through
  `a, b, c`. Its tree of blobs has one internal edge.
* `NonBinary.net`, on the taxa `a, …, f = 0, …, 5`: the same with `de` replaced by the polytomy `def`, so that it has a trivial
  4-blob on `x, d, e, f` for `x ∈ {a, b, c}`, and gene trees that are not binary.

At all valid parameters both directions of Assumption 1 hold. On a tree `T₀` that resolves the tree of blobs with the false
edge `bc`, with probability tending to one:

* for Bon and BBC the output is the tree of blobs (`ECToBlob.DisplayedTree.theorem8_2_displayed`);
* for Cauchy and CBC the output is `T₀`, which has the false edge (`Binary.counterexample`, `NonBinary.counterexample`).

The tables are checked by `decide`: `FinNetwork.Tables` gives reachability, with and without one arc, and from it what the
statements of `HasTrivialFourBlob` and `InducedCutSplit` need.
-/

@[expose] public noncomputable section

open Phylogenetics Phylogenetics.RootedNetwork Phylogenetics.QuartetTests Finset Filter Topology
open scoped Classical

namespace ECToBlob.FinNetwork

open ECToBlob.Deterministic ECToBlob.Coarsening ECToBlob.FalseEdge ECToBlob.Framework
open ECToBlob.DisplayedTree ECToBlob.Section3Observations

/-! ### Networks from tables -/

section Tables

variable {k m t : ℕ}

variable {src tgt : Fin m → Fin k} {root : Fin k} {lf : Fin t → Fin k}
  {desc : Fin k → Finset (Fin k)} {avoid : Fin m → Finset (Fin k)}

/-- `IsHub` in a decidable form. -/
def HubT (src tgt : Fin m → Fin k) (lf : Fin t → Fin k) (desc : Fin k → Finset (Fin k))
    (avoid : Fin m → Finset (Fin k)) (q : Finset (Fin t)) (v : Fin k) : Prop :=
  ∀ x ∈ q, ∃ e : Fin m, (src e = v ∧ lf x ∉ avoid e ∧ ∀ y ∈ q, y ≠ x → lf y ∉ desc (tgt e)) ∨
    (tgt e = v ∧ (∀ y ∈ q, y ≠ x → lf y ∉ avoid e) ∧ lf x ∉ desc (tgt e))

instance (src tgt : Fin m → Fin k) (lf : Fin t → Fin k) (desc : Fin k → Finset (Fin k))
    (avoid : Fin m → Finset (Fin k)) (q : Finset (Fin t)) (v : Fin k) :
    Decidable (HubT src tgt lf desc avoid q v) :=
  inferInstanceAs (Decidable (∀ x ∈ q, ∃ e : Fin m,
    (src e = v ∧ lf x ∉ avoid e ∧ ∀ y ∈ q, y ≠ x → lf y ∉ desc (tgt e)) ∨
    (tgt e = v ∧ (∀ y ∈ q, y ≠ x → lf y ∉ avoid e) ∧ lf x ∉ desc (tgt e))))

theorem Tables.isHub_iff (h : Tables src tgt root desc avoid) {q : Finset (Fin t)} {v : Fin k} :
    IsHub (net src tgt root lf) q v ↔ HubT src tgt lf desc avoid q v := by
  simp only [IsHub, Leaves, Enters, h.dominates_iff, h.isBelow_iff]
  rfl

theorem Tables.hasTrivialFourBlob_iff (h : Tables src tgt root desc avoid)
    (hN : (net src tgt root lf).IsPhylogenetic) {q : Finset (Fin t)} (hq : q.card = 4) :
    HasTrivialFourBlob (net src tgt root lf) q ↔ ∃ v, HubT src tgt lf desc avoid q v := by
  constructor
  · intro htr
    obtain ⟨v, hv⟩ := exists_isHub hN (by omega) htr
    exact ⟨v, h.isHub_iff.1 hv⟩
  · rintro ⟨v, hv⟩
    exact hasTrivialFourBlob_of_isHub hN (by omega) (h.isHub_iff.2 hv)

end Tables

/-! ### The converse of Assumption 1, set by set -/

section Converse

variable {V E X : Type*} [Fintype X] [DecidableEq X] {N : RootedNetwork V E X}
  {p : QuartetTree X → ℝ}

/-- The converse of Assumption 1, from what happens on each set of four taxa: a trivial 4-blob, a cut split, or three trees of
which one has concordance factor `0` and the others positive ones. The first two need only the forward direction. -/
theorem assumption1Converse_of_cases (hF : Assumption1Forward N p)
    (h : ∀ q : Finset X, q.card = 4 → HasTrivialFourBlob N q ∨ (∃ s ∈ treesOn q, InducedCutSplit N s) ∨
      ∃ s₁ ∈ treesOn q, ∃ s₂ ∈ treesOn q, ∃ s₃ ∈ treesOn q,
        s₁ ≠ s₂ ∧ s₁ ≠ s₃ ∧ s₂ ≠ s₃ ∧ p s₃ = 0 ∧ 0 < p s₁ ∧ 0 < p s₂) :
    Assumption1Converse N p := by
  refine ⟨fun q hq htr hu => ?_, fun s hs hstrict => ?_⟩
  · rcases h q hq with h' | ⟨s, hsq, hc⟩ | ⟨s₁, _, s₂, _, s₃, h₃, _, _, _, h0, _, _⟩
    · exact htr h'
    · have hq' : s.taxa = q := mem_treesOn.1 hsq
      exact not_uniform_of_strict (hF.t1 s hc) (hq' ▸ hu)
    · have := hu s₃ h₃
      rw [h0] at this
      norm_num at this
  · rcases h s.taxa s.card_taxa with h' | ⟨s₀, hs₀, hc⟩ | ⟨s₁, h₁, s₂, h₂, s₃, h₃, h12, h13, h23, h0, hp₁, hp₂⟩
    · exact not_uniform_of_strict hstrict (hF.star _ s.card_taxa h')
    · have hne : s₀ ≠ s := fun he => hs (he ▸ hc)
      have htaxa : s₀.taxa = s.taxa := mem_treesOn.1 hs₀
      have h₁ := hstrict.1 s₀ (QuartetTree.mem_alternatives.2 ⟨htaxa, hne⟩)
      have h₂ := (hF.t1 s₀ hc).1 s (QuartetTree.mem_alternatives.2 ⟨htaxa.symm, hne.symm⟩)
      exact lt_asymm h₁ h₂
    · -- the three trees are all the trees on the taxa of `s`
      have hall : treesOn s.taxa = {s₁, s₂, s₃} := by
        symm
        refine Finset.eq_of_subset_of_card_le ?_ ?_
        · intro r hr
          simp only [mem_insert, mem_singleton] at hr
          rcases hr with rfl | rfl | rfl <;> assumption
        · rw [card_treesOn s.card_taxa, Finset.card_eq_three.2 ⟨s₁, s₂, s₃, h12, h13, h23, rfl⟩]
      have hsm := QuartetTests.mem_treesOn_taxa s
      rw [hall] at hsm
      simp only [mem_insert, mem_singleton] at hsm
      have halt : ∀ {r : QuartetTree X}, r ∈ treesOn s.taxa → r ≠ s → r ∈ s.alternatives := fun hr hne =>
        QuartetTree.mem_alternatives.2 ⟨mem_treesOn.1 hr, hne⟩
      rcases hsm with rfl | rfl | rfl
      · -- at `s₁`: the alternatives `s₂`, `s₃` would have equal values
        have := hstrict.2 s₂ (halt h₂ h12.symm) s₃ (halt h₃ h13.symm)
        rw [h0] at this
        exact hp₂.ne' this
      · have := hstrict.2 s₁ (halt h₁ h12) s₃ (halt h₃ h23.symm)
        rw [h0] at this
        exact hp₁.ne' this
      · -- at `s₃`: its value `0` would be above that of `s₁`
        have h₄ := hstrict.1 s₁ (halt h₁ h13)
        rw [h0] at h₄
        exact lt_asymm h₄ hp₁

end Converse

/-! ### Parent choices -/

section Choices

variable {k m t : ℕ} {N : RootedNetwork (Fin k) (Fin m) (Fin t)}

/-- The weight of a parent choice at valid parameters is positive. -/
theorem choiceWeight_pos {θ : MetricData (Fin m)} (hθ : N.IsMetric θ)
    (c : N.ParentChoice) : 0 < N.choiceWeight θ c :=
  prod_pos fun _ _ => NMSC.inheritance_pos hθ _

/-- A quartet tree displayed by a parent choice has a positive concordance factor, at valid parameters. -/
theorem displayedCF_pos_of_displays [Nonempty (Fin t)] (hN : N.IsPhylogenetic) {θ : MetricData (Fin m)}
    (hθ : N.IsMetric θ) (c : N.ParentChoice) {s : QuartetTree (Fin t)}
    (hd : Displays (N.displayedSides c) s) : 0 < displayedCF N θ s := by
  rw [displayedCF_eq hN]
  refine lt_of_lt_of_le ?_ (Finset.single_le_sum
    (fun c' _ => mul_nonneg (choiceWeight_nonneg hθ.isWeakMetric c') (geneContribution_nonneg _ _))
    (by simp : c ∈ _))
  rw [(geneContribution_of_displays (isUnrootedTree_displayedSides hN c) hd).1, mul_one]
  exact choiceWeight_pos hθ c

/-- A quartet tree with an alternative displayed by every parent choice has concordance factor `0`. -/
theorem displayedCF_eq_zero_of_forall [Nonempty (Fin t)] (hN : N.IsPhylogenetic) {θ : MetricData (Fin m)}
    {s : QuartetTree (Fin t)}
    (h : ∀ c : N.ParentChoice, ∃ r, s ∈ r.alternatives ∧ Displays (N.displayedSides c) r) :
    displayedCF N θ s = 0 := by
  rw [displayedCF_eq hN]
  refine sum_eq_zero fun c _ => ?_
  obtain ⟨r, hr, hd⟩ := h c
  rw [(geneContribution_of_displays (isUnrootedTree_displayedSides hN c) hd).2 s hr, mul_zero]

/-- If the output is `T₀` with probability tending to one, then it is another tree with probability tending to zero. -/
theorem tendsto_eq_zero_of_tendsto_eq {Γ Y : Type*} [Fintype Γ] {dist : Γ → ℝ} (hd : IsDist dist)
    {out : (n : ℕ) → (Fin n → Γ) → Y} {y y' : Y} (hne : y ≠ y')
    (h : Tendsto (fun n => iidProb dist n fun ω => out n ω = y) atTop (𝓝 1)) :
    Tendsto (fun n => iidProb dist n fun ω => out n ω = y') atTop (𝓝 0) := by
  have hlim := (tendsto_const_nhds (x := (1 : ℝ))).sub h
  rw [sub_self] at hlim
  refine squeeze_zero (fun n => iidProb_nonneg hd n _) (fun n => ?_) hlim
  rw [← iidProb_not hd]
  refine iidProb_mono hd fun ω hω hy => hne ?_
  rw [← hy]
  exact hω

end Choices

/-! ### A binary network -/

namespace Binary

/-- It has no trivial 4-blob. -/
theorem not_hasTrivialFourBlob {q : Finset (Fin 5)} (hq : q.card = 4) : ¬ HasTrivialFourBlob net q := by
  rw [tables.hasTrivialFourBlob_iff net_isPhylogenetic hq]
  have : ∀ q : Finset (Fin 5), q.card = 4 → ∀ v, ¬ HubT src tgt lf desc avoid q v := by decide
  exact fun ⟨v, hv⟩ => this q hq v hv

/-! #### The starting tree -/

/-- The rooted tree `((d,e),(a,(b,c)))`. -/
def H₀ : Finset (Finset (Fin 5)) := {univ, {0}, {1}, {2}, {3}, {4}, {3, 4}, {1, 2}, {0, 1, 2}}

/-- The binary tree `T₀` with cherries `de` and `bc`. It resolves the tree of blobs, with the false edge `bc`. -/
def T₀ : Finset (Finset (Fin 5)) := unroot H₀

theorem T₀_isBinaryTree : IsBinaryTree T₀ := ⟨H₀, by unfold IsHierarchy; decide, rfl, by decide⟩

theorem T₀_isUnrootedTree : IsUnrootedTree T₀ :=
  let ⟨H, h₁, h₂, _⟩ := T₀_isBinaryTree
  ⟨H, h₁, h₂⟩

theorem T₀_isResolution : IsResolutionOf T₀ (treeOfBlobs net) := by
  refine ⟨T₀_isUnrootedTree, fun A hA => ?_⟩
  rw [mem_treeOfBlobs_iff] at hA
  unfold T₀ H₀ unroot
  revert A
  decide

theorem T₀_ne_treeOfBlobs : ({1, 2} : Finset (Fin 5)) ∈ T₀ ∧ ({1, 2} : Finset (Fin 5)) ∉ treeOfBlobs net := by
  refine ⟨by unfold T₀ H₀ unroot; decide, ?_⟩
  rw [mem_treeOfBlobs_iff]
  decide

/-! #### The concordance factors of the displayed trees -/

variable {x : Fin 5}

/-- **Both directions of Assumption 1 hold at all valid parameters.** -/
theorem displayed_converse {θ : MetricData (Fin 11)} (hθ : net.IsMetric θ) :
    Assumption1Converse net (displayedCF net θ) := by
  have hN := net_isPhylogenetic
  have h₁ := assumption1Forward_displayed hN hθ.isWeakMetric.isNormalized (θ := θ)
  refine assumption1Converse_of_cases h₁ fun q hq => ?_
  have hcases : ∀ q : Finset (Fin 5), q.card = 4 →
      (∃ y z : Fin 5, q = {3, 4, y, z} ∧ RDomT tgt lf desc avoid 3 4 y z) ∨
        ∃ x : Fin 5, (x = 3 ∨ x = 4) ∧ q = {0, 1, 2, x} := by decide
  rcases hcases q hq with ⟨y, z, rfl, hr⟩ | ⟨x, hx, rfl⟩
  · exact Or.inr (Or.inl ⟨quartetTree 3 4 y z hq, by simp [treesOn],
      inducedCutSplit_of_rdom hN hq (tables.rdom_iff.2 hr)⟩)
  · right; right
    have h₁' : ({0, 2, 1, x} : Finset (Fin 5)).card = 4 := by
      rcases hx with rfl | rfl <;> decide
    have h₂' : ({1, 2, 0, x} : Finset (Fin 5)).card = 4 := by
      rcases hx with rfl | rfl <;> decide
    have ht₁ : ({0, 2, 1, x} : Finset (Fin 5)) = {0, 1, 2, x} := by
      rcases hx with rfl | rfl <;> decide
    have ht₂ : ({1, 2, 0, x} : Finset (Fin 5)) = {0, 1, 2, x} := by
      rcases hx with rfl | rfl <;> decide
    have hm₁ : quartetTree 0 2 1 x h₁' ∈ treesOn ({0, 1, 2, x} : Finset (Fin 5)) := by
      simp only [treesOn, mem_filter, mem_univ, true_and]
      rw [taxa_quartetTree, ht₁]
    have hm₂ : quartetTree 1 2 0 x h₂' ∈ treesOn ({0, 1, 2, x} : Finset (Fin 5)) := by
      simp only [treesOn, mem_filter, mem_univ, true_and]
      rw [taxa_quartetTree, ht₂]
    have hm₃ : quartetTree 0 1 2 x hq ∈ treesOn ({0, 1, 2, x} : Finset (Fin 5)) := by
      simp only [treesOn, mem_filter, mem_univ, true_and]
      rw [taxa_quartetTree]
    have h12 : quartetTree 0 2 1 x h₁' ≠ quartetTree 1 2 0 x h₂' := by
      intro h
      have := congrArg Subtype.val h
      simp only [quartetTree_val] at this
      rcases hx with rfl | rfl <;> exact absurd this (by decide)
    have h13 : quartetTree 0 2 1 x h₁' ≠ quartetTree 0 1 2 x hq := by
      intro h
      have := congrArg Subtype.val h
      simp only [quartetTree_val] at this
      rcases hx with rfl | rfl <;> exact absurd this (by decide)
    have h23 : quartetTree 1 2 0 x h₂' ≠ quartetTree 0 1 2 x hq := by
      intro h
      have := congrArg Subtype.val h
      simp only [quartetTree_val] at this
      rcases hx with rfl | rfl <;> exact absurd this (by decide)
    refine ⟨_, hm₁, _, hm₂, _, hm₃, h12, h13, h23, ?_,
      displayedCF_pos_of_displays hN hθ choiceU (displays_of_uh choiceU_keeps hx h₁'),
      displayedCF_pos_of_displays hN hθ choiceV (displays_of_vh choiceV_keeps hx h₂')⟩
    refine displayedCF_eq_zero_of_forall hN fun c => ?_
    rcases uh_or_vh c with h | h
    · refine ⟨_, ?_, displays_of_uh h hx h₁'⟩
      refine QuartetTree.mem_alternatives.2 ⟨?_, h13.symm⟩
      rw [taxa_quartetTree, taxa_quartetTree, ht₁]
    · refine ⟨_, ?_, displays_of_vh h hx h₂'⟩
      refine QuartetTree.mem_alternatives.2 ⟨?_, h23.symm⟩
      rw [taxa_quartetTree, taxa_quartetTree, ht₂]

/-- (`ecto:thm8_2_displayed_binary`) **The counterexample on a binary network.** At all valid parameters of the network, under the displayed tree model, both
directions of Assumption 1 hold, and `T₀` resolves the tree of blobs. On `T₀`, at any levels `α_n ≤ 1`, `β_n → 0` from above
with `o(n)` cutoffs, the output with Cauchy or CBC is `T₀` with probability tending to one, for both selection rules and all
quartet types, so it is the tree of blobs with probability tending to zero. With Bon or BBC, at any levels with `o(n)` cutoffs,
it is the tree of blobs with probability tending to one.

This is E11 of the report, on another network than its 5-sunlet: at a cut split the concordance factor is `(1, 0, 0)` and
the T1 p-value is `1`, and the Cauchy transform takes `p = 1` to `-∞` by its continuous extension (E7). -/
theorem counterexample {θ : MetricData (Fin 11)} (hθ : net.IsMetric θ) :
    Assumption1Forward net (displayedCF net θ) ∧ Assumption1Converse net (displayedCF net θ) ∧
      IsResolutionOf T₀ (treeOfBlobs net) ∧ T₀ ≠ treeOfBlobs net ∧
      (∀ o : ECToBlobOptions, (o.testCo = .cauchy ∨ o.testCo = .cbc) → ∀ {α β : ℕ → ℝ},
        (∀ᶠ n in atTop, α n ≤ 1) → Tendsto β atTop (𝓝[>] 0) →
        Tendsto (fun n : ℕ => Real.log (β n) / n) atTop (𝓝 0) →
        Tendsto (fun n => iidProb (displayedTreeDist net θ) n fun ω =>
          ectoblob o (α n) (β n) (conventionCount ω) T₀ = T₀) atTop (𝓝 1) ∧
        Tendsto (fun n => iidProb (displayedTreeDist net θ) n fun ω =>
          ectoblob o (α n) (β n) (conventionCount ω) T₀ = treeOfBlobs net) atTop (𝓝 0)) ∧
      (∀ o : ECToBlobOptions, (o.testCo = .bon ∨ o.testCo = .bbc) → ∀ {α β : ℕ → ℝ},
        Tendsto α atTop (𝓝[>] 0) → Tendsto β atTop (𝓝[>] 0) →
        Tendsto (fun n : ℕ => Real.log (α n) / n) atTop (𝓝 0) →
        Tendsto (fun n : ℕ => Real.log (β n) / n) atTop (𝓝 0) →
        Tendsto (fun n => iidProb (displayedTreeDist net θ) n fun ω =>
          ectoblob o (α n) (β n) (conventionCount ω) T₀ = treeOfBlobs net) atTop (𝓝 1)) := by
  have hN := net_isPhylogenetic
  have hw := hθ.isWeakMetric
  have h₁ := assumption1Forward_displayed hN hw.isNormalized (θ := θ)
  have h₂ := displayed_converse hθ
  have hne : T₀ ≠ treeOfBlobs net := fun h => T₀_ne_treeOfBlobs.2 (h ▸ T₀_ne_treeOfBlobs.1)
  refine ⟨h₁, h₂, T₀_isResolution, hne, fun o hm {α β} hα hβ₀ hβ => ?_, fun o hm {α β} hα₀ hβ₀ hα hβ => ?_⟩
  · have hself := tendsto_ectoblob_displayed_self (N := net) (θ := θ) hN hw T₀_isUnrootedTree
      (A := {3, 4}) (by unfold T₀ H₀ unroot; decide) (mem_treeOfBlobs_iff.2 (by decide)) (by decide)
      (fun B _ s _ hu => not_hasTrivialFourBlob s.card_taxa
        ((uniform_iff h₁ h₂ s).1 hu)) hm hα hβ₀ hβ
    exact ⟨hself, tendsto_eq_zero_of_tendsto_eq (displayedTreeDist_isDist hN hw) hne hself⟩
  · exact consistency_ectoblob_displayed net θ hN hw h₂ T₀ T₀_isResolution o hm hα₀ hβ₀ hα hβ

end Binary

/-! ### A non-binary network -/

namespace NonBinary

/-- The tails of the arcs: the vertices `0, …, 5` are the taxa `a, b, c, d, e, f`, and `6, …, 11` are the reticulation `h`, its
parents `u`, `v`, the top of the cycle `r`, the parent `w` of `d, e, f`, and the root `s`. The arcs are, in order, `sw`, `sr`,
`wd`, `we`, `wf`, `ru`, `rv`, `ua`, `uh`, `vb`, `vh`, `hc`. -/
def src : Fin 12 → Fin 12 := ![11, 11, 10, 10, 10, 9, 9, 7, 7, 8, 8, 6]

/-- The heads of the arcs. -/
def tgt : Fin 12 → Fin 12 := ![10, 9, 3, 4, 5, 7, 8, 0, 6, 1, 6, 2]

/-- The taxa, as vertices. -/
def lf : Fin 6 → Fin 12 := ![0, 1, 2, 3, 4, 5]

/-- What each vertex reaches. -/
def desc : Fin 12 → Finset (Fin 12) :=
  ![{0}, {1}, {2}, {3}, {4}, {5}, {2, 6}, {0, 2, 6, 7}, {1, 2, 6, 8}, {0, 1, 2, 6, 7, 8, 9},
    {3, 4, 5, 10}, {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11}]

/-- What the root reaches off each arc. -/
def avoid : Fin 12 → Finset (Fin 12) :=
  ![{0, 1, 2, 6, 7, 8, 9, 11}, {3, 4, 5, 10, 11}, {0, 1, 2, 4, 5, 6, 7, 8, 9, 10, 11},
    {0, 1, 2, 3, 5, 6, 7, 8, 9, 10, 11}, {0, 1, 2, 3, 4, 6, 7, 8, 9, 10, 11},
    {1, 2, 3, 4, 5, 6, 8, 9, 10, 11}, {0, 2, 3, 4, 5, 6, 7, 9, 10, 11},
    {1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11}, {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11},
    {0, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11}, {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11},
    {0, 1, 3, 4, 5, 6, 7, 8, 9, 10, 11}]

theorem tables : Tables src tgt 11 desc avoid :=
  ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩

/-- **The network**: the cut edge `def|abc`, the polytomy at `w` with `d, e, f`, and the 4-cycle `r, u, h, v` with the taxa `a` at
`u`, `b` at `v` and `c` at `h`. -/
abbrev net : RootedNetwork (Fin 12) (Fin 12) (Fin 6) := FinNetwork.net src tgt 11 lf

theorem net_isPhylogenetic : net.IsPhylogenetic :=
  isPhylogenetic_of_down (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide)

/-- It is not binary: `w` has three children. -/
theorem not_isBinary : ¬ net.IsBinary := by
  rintro ⟨_, h⟩
  have h₁ := h 10 (by decide)
  unfold DirectedMultigraph.outdegree DirectedMultigraph.indegree at h₁
  rw [ncard_setOf_eq_card_filter (fun e => net.graph.source e = 10), ncard_setOf_eq_card_filter (fun e => net.graph.target e = 10)] at h₁
  exact absurd (h₁ (by decide)) (by decide)

/-- Its trivial 4-blobs: `x, d, e, f` with `x ∈ {a, b, c}`. -/
theorem hasTrivialFourBlob_iff {q : Finset (Fin 6)} (hq : q.card = 4) :
    HasTrivialFourBlob net q ↔ ∃ x : Fin 6, x.val < 3 ∧ q = {x, 3, 4, 5} := by
  rw [tables.hasTrivialFourBlob_iff net_isPhylogenetic hq]
  revert q
  decide

/-- The sides of the tree of blobs. -/
theorem mem_treeOfBlobs_iff {A : Finset (Fin 6)} :
    A ∈ treeOfBlobs net ↔ A.card = 1 ∨ Aᶜ.card = 1 ∨ A = {3, 4, 5} ∨ A = {0, 1, 2} := by
  rw [tables.mem_treeOfBlobs_iff net_isPhylogenetic]
  revert A
  decide

/-! #### The starting tree -/

/-- The rooted tree `((d,e,f),(a,(b,c)))`. -/
def H₀ : Finset (Finset (Fin 6)) := {univ, {0}, {1}, {2}, {3}, {4}, {5}, {3, 4, 5}, {1, 2}, {0, 1, 2}}

/-- The tree `T₀`, with the cherry `bc` and the polytomy at `def`. It resolves the tree of blobs, with the false edge `bc`, and it
is not binary, like the tree of blobs. -/
def T₀ : Finset (Finset (Fin 6)) := unroot H₀

set_option maxRecDepth 4000 in
theorem T₀_isUnrootedTree : IsUnrootedTree T₀ :=
  ⟨H₀, ⟨by decide, by decide, by decide, by decide⟩, rfl⟩

theorem T₀_isResolution : IsResolutionOf T₀ (treeOfBlobs net) := by
  refine ⟨T₀_isUnrootedTree, fun A hA => ?_⟩
  rw [mem_treeOfBlobs_iff] at hA
  unfold T₀ H₀ unroot
  revert A
  decide

theorem T₀_ne_treeOfBlobs : ({1, 2} : Finset (Fin 6)) ∈ T₀ ∧ ({1, 2} : Finset (Fin 6)) ∉ treeOfBlobs net := by
  refine ⟨by unfold T₀ H₀ unroot; decide, ?_⟩
  rw [mem_treeOfBlobs_iff]
  decide

/-! #### The concordance factors of the displayed trees -/

/-- The parent arcs, with the parent `f` at the reticulation. -/
def parentOf (f : Fin 12) : Fin 12 → Fin 12 := ![7, 9, 11, 2, 3, 4, f, 5, 6, 1, 0, 0]

/-- The parent choice that keeps `u → h`. -/
def choiceU : net.ParentChoice := fun w => ⟨parentOf 8 w.val, by
  obtain ⟨w, hw⟩ := w
  revert w
  decide⟩

/-- The parent choice that keeps `v → h`. -/
def choiceV : net.ParentChoice := fun w => ⟨parentOf 10 w.val, by
  obtain ⟨w, hw⟩ := w
  revert w
  decide⟩

variable {x : Fin 6}

/-- A parent choice that keeps `u → h` has the cherry `ac`. -/
theorem displays_of_uh {c : net.ParentChoice} (huh : (8 : Fin 12) ∉ net.deletedArcs c)
    (hx : x = 3 ∨ x = 4 ∨ x = 5) (hc : ({0, 2, 1, x} : Finset (Fin 6)).card = 4) :
    Displays (net.displayedSides c) (quartetTree 0 2 1 x hc) := by
  have h₇ : (7 : Fin 12) ∉ net.deletedArcs c :=
    notMem_deletedArcs_of_unique c (by decide) (by decide)
  have h₁₁ : (11 : Fin 12) ∉ net.deletedArcs c :=
    notMem_deletedArcs_of_unique c (by decide) (by decide)
  refine displays_of_cluster (P := {0, 2}) (u := (7 : Fin 12)) (by simp) (fun y hy => ?_)
    (fun y hyt hyP hy => ?_)
  · rw [mem_insert, mem_singleton] at hy
    rcases hy with rfl | rfl
    · exact mem_displayedCluster.2 (Relation.ReflTransGen.single ⟨7, h₇, rfl, rfl⟩)
    · exact mem_displayedCluster.2 (Relation.ReflTransGen.head ⟨8, huh, rfl, rfl⟩
        (Relation.ReflTransGen.single ⟨11, h₁₁, rfl, rfl⟩))
  · have hr : lf y ∈ desc 7 := tables.reaches_iff.1 (mem_displayedCluster.1 hy).reaches
    rw [taxa_quartetTree] at hyt
    simp only [mem_insert, mem_singleton] at hyt hyP
    clear hy
    rcases hx with rfl | rfl | rfl <;> revert y <;> decide

/-- A parent choice that keeps `v → h` has the cherry `bc`. -/
theorem displays_of_vh {c : net.ParentChoice} (hvh : (10 : Fin 12) ∉ net.deletedArcs c)
    (hx : x = 3 ∨ x = 4 ∨ x = 5) (hc : ({1, 2, 0, x} : Finset (Fin 6)).card = 4) :
    Displays (net.displayedSides c) (quartetTree 1 2 0 x hc) := by
  have h₉ : (9 : Fin 12) ∉ net.deletedArcs c :=
    notMem_deletedArcs_of_unique c (by decide) (by decide)
  have h₁₁ : (11 : Fin 12) ∉ net.deletedArcs c :=
    notMem_deletedArcs_of_unique c (by decide) (by decide)
  refine displays_of_cluster (P := {1, 2}) (u := (8 : Fin 12)) (by simp) (fun y hy => ?_)
    (fun y hyt hyP hy => ?_)
  · rw [mem_insert, mem_singleton] at hy
    rcases hy with rfl | rfl
    · exact mem_displayedCluster.2 (Relation.ReflTransGen.single ⟨9, h₉, rfl, rfl⟩)
    · exact mem_displayedCluster.2 (Relation.ReflTransGen.head ⟨10, hvh, rfl, rfl⟩
        (Relation.ReflTransGen.single ⟨11, h₁₁, rfl, rfl⟩))
  · have hr : lf y ∈ desc 8 := tables.reaches_iff.1 (mem_displayedCluster.1 hy).reaches
    rw [taxa_quartetTree] at hyt
    simp only [mem_insert, mem_singleton] at hyt hyP
    clear hy
    rcases hx with rfl | rfl | rfl <;> revert y <;> decide

/-- A parent choice keeps one of the two arcs into the reticulation. -/
theorem uh_or_vh (c : net.ParentChoice) :
    (8 : Fin 12) ∉ net.deletedArcs c ∨ (10 : Fin 12) ∉ net.deletedArcs c := by
  have hne := notMem_deletedArcs_choice c ⟨6, by decide⟩
  have ht : tgt (c ⟨6, by decide⟩).val = 6 := (c ⟨6, by decide⟩).property
  have hdec : ∀ f : Fin 12, tgt f = 6 → f = 8 ∨ f = 10 := by decide
  rcases hdec _ ht with h | h
  · exact Or.inl (h ▸ hne)
  · exact Or.inr (h ▸ hne)

theorem choiceU_keeps : (8 : Fin 12) ∉ net.deletedArcs choiceU :=
  notMem_deletedArcs_choice choiceU ⟨6, by decide⟩

theorem choiceV_keeps : (10 : Fin 12) ∉ net.deletedArcs choiceV :=
  notMem_deletedArcs_choice choiceV ⟨6, by decide⟩

/-- The pairs among `d, e, f`. -/
def dp : Fin 3 → Fin 6 × Fin 6 := ![(3, 4), (3, 5), (4, 5)]

/-- The pairs among `a, b, c`. -/
def ap : Fin 3 → Fin 6 × Fin 6 := ![(0, 1), (0, 2), (1, 2)]

/-- **Both directions of Assumption 1 hold at all valid parameters.** -/
theorem displayed_converse {θ : MetricData (Fin 12)} (hθ : net.IsMetric θ) :
    Assumption1Converse net (displayedCF net θ) := by
  have hN := net_isPhylogenetic
  have h₁ := assumption1Forward_displayed hN hθ.isWeakMetric.isNormalized (θ := θ)
  refine assumption1Converse_of_cases h₁ fun q hq => ?_
  have hcases : ∀ q : Finset (Fin 6), q.card = 4 →
      (∃ x : Fin 6, x.val < 3 ∧ q = {x, 3, 4, 5}) ∨
      (∃ i j : Fin 3, q = {(dp i).1, (dp i).2, (ap j).1, (ap j).2}) ∨
        ∃ x : Fin 6, (x = 3 ∨ x = 4 ∨ x = 5) ∧ q = {0, 1, 2, x} := by decide
  have hr : ∀ i j : Fin 3, RDomT tgt lf desc avoid (dp i).1 (dp i).2 (ap j).1 (ap j).2 := by decide
  rcases hcases q hq with h | ⟨i, j, rfl⟩ | ⟨x, hx, rfl⟩
  · exact Or.inl ((hasTrivialFourBlob_iff hq).2 h)
  · exact Or.inr (Or.inl ⟨quartetTree _ _ _ _ hq, by simp [treesOn],
      inducedCutSplit_of_rdom hN hq (tables.rdom_iff.2 (hr i j))⟩)
  · right; right
    have h₁' : ({0, 2, 1, x} : Finset (Fin 6)).card = 4 := by
      rcases hx with rfl | rfl | rfl <;> decide
    have h₂' : ({1, 2, 0, x} : Finset (Fin 6)).card = 4 := by
      rcases hx with rfl | rfl | rfl <;> decide
    have ht₁ : ({0, 2, 1, x} : Finset (Fin 6)) = {0, 1, 2, x} := by
      rcases hx with rfl | rfl | rfl <;> decide
    have ht₂ : ({1, 2, 0, x} : Finset (Fin 6)) = {0, 1, 2, x} := by
      rcases hx with rfl | rfl | rfl <;> decide
    have hm₁ : quartetTree 0 2 1 x h₁' ∈ treesOn ({0, 1, 2, x} : Finset (Fin 6)) := by
      simp only [treesOn, mem_filter, mem_univ, true_and]
      rw [taxa_quartetTree, ht₁]
    have hm₂ : quartetTree 1 2 0 x h₂' ∈ treesOn ({0, 1, 2, x} : Finset (Fin 6)) := by
      simp only [treesOn, mem_filter, mem_univ, true_and]
      rw [taxa_quartetTree, ht₂]
    have hm₃ : quartetTree 0 1 2 x hq ∈ treesOn ({0, 1, 2, x} : Finset (Fin 6)) := by
      simp only [treesOn, mem_filter, mem_univ, true_and]
      rw [taxa_quartetTree]
    have h12 : quartetTree 0 2 1 x h₁' ≠ quartetTree 1 2 0 x h₂' := by
      intro h
      have := congrArg Subtype.val h
      simp only [quartetTree_val] at this
      rcases hx with rfl | rfl | rfl <;> exact absurd this (by decide)
    have h13 : quartetTree 0 2 1 x h₁' ≠ quartetTree 0 1 2 x hq := by
      intro h
      have := congrArg Subtype.val h
      simp only [quartetTree_val] at this
      rcases hx with rfl | rfl | rfl <;> exact absurd this (by decide)
    have h23 : quartetTree 1 2 0 x h₂' ≠ quartetTree 0 1 2 x hq := by
      intro h
      have := congrArg Subtype.val h
      simp only [quartetTree_val] at this
      rcases hx with rfl | rfl | rfl <;> exact absurd this (by decide)
    refine ⟨_, hm₁, _, hm₂, _, hm₃, h12, h13, h23, ?_,
      displayedCF_pos_of_displays hN hθ choiceU (displays_of_uh choiceU_keeps hx h₁'),
      displayedCF_pos_of_displays hN hθ choiceV (displays_of_vh choiceV_keeps hx h₂')⟩
    refine displayedCF_eq_zero_of_forall hN fun c => ?_
    rcases uh_or_vh c with h | h
    · refine ⟨_, ?_, displays_of_uh h hx h₁'⟩
      refine QuartetTree.mem_alternatives.2 ⟨?_, h13.symm⟩
      rw [taxa_quartetTree, taxa_quartetTree, ht₁]
    · refine ⟨_, ?_, displays_of_vh h hx h₂'⟩
      refine QuartetTree.mem_alternatives.2 ⟨?_, h23.symm⟩
      rw [taxa_quartetTree, taxa_quartetTree, ht₂]

/-- No quartet around an edge of `T₀` has a trivial 4-blob: the edges of `T₀` have two taxa of such a quartet on each side. -/
theorem not_trivial_of_mem_multipartition {B : Finset (Fin 6)} (hB : B ∈ internalSides T₀)
    {s : QuartetTree (Fin 6)} (hs : s ∈ multipartitionQuartets T₀ B) :
    ¬ HasTrivialFourBlob net s.taxa := by
  have h₁ : (B ∩ s.taxa).card = 2 := s.card_of_mem (mem_filter.1 (mem_filter.1 hs).1).2
  rw [hasTrivialFourBlob_iff s.card_taxa]
  rintro ⟨x, hx, hq⟩
  rw [hq] at h₁
  have hB' := (mem_internalSides.1 hB)
  have hdec : ∀ B ∈ T₀, 2 ≤ B.card ∧ 2 ≤ Bᶜ.card → ∀ x : Fin 6, x.val < 3 →
      (B ∩ {x, 3, 4, 5}).card ≠ 2 := by
    unfold T₀ H₀ unroot
    decide
  exact hdec B hB'.1 hB'.2 x hx h₁

/-- (`ecto:thm8_2_displayed_nonbinary`) **The counterexample on a non-binary network**, with a trivial 4-blob and gene trees with polytomies. The statement is that
of `Binary.counterexample`. -/
theorem counterexample {θ : MetricData (Fin 12)} (hθ : net.IsMetric θ) :
    ¬ net.IsBinary ∧ HasTrivialFourBlob net {0, 3, 4, 5} ∧
    Assumption1Forward net (displayedCF net θ) ∧ Assumption1Converse net (displayedCF net θ) ∧
      IsResolutionOf T₀ (treeOfBlobs net) ∧ T₀ ≠ treeOfBlobs net ∧
      (∀ o : ECToBlobOptions, (o.testCo = .cauchy ∨ o.testCo = .cbc) → ∀ {α β : ℕ → ℝ},
        (∀ᶠ n in atTop, α n ≤ 1) → Tendsto β atTop (𝓝[>] 0) →
        Tendsto (fun n : ℕ => Real.log (β n) / n) atTop (𝓝 0) →
        Tendsto (fun n => iidProb (displayedTreeDist net θ) n fun ω =>
          ectoblob o (α n) (β n) (conventionCount ω) T₀ = T₀) atTop (𝓝 1) ∧
        Tendsto (fun n => iidProb (displayedTreeDist net θ) n fun ω =>
          ectoblob o (α n) (β n) (conventionCount ω) T₀ = treeOfBlobs net) atTop (𝓝 0)) ∧
      (∀ o : ECToBlobOptions, (o.testCo = .bon ∨ o.testCo = .bbc) → ∀ {α β : ℕ → ℝ},
        Tendsto α atTop (𝓝[>] 0) → Tendsto β atTop (𝓝[>] 0) →
        Tendsto (fun n : ℕ => Real.log (α n) / n) atTop (𝓝 0) →
        Tendsto (fun n : ℕ => Real.log (β n) / n) atTop (𝓝 0) →
        Tendsto (fun n => iidProb (displayedTreeDist net θ) n fun ω =>
          ectoblob o (α n) (β n) (conventionCount ω) T₀ = treeOfBlobs net) atTop (𝓝 1)) := by
  have hN := net_isPhylogenetic
  have hw := hθ.isWeakMetric
  have h₁ := assumption1Forward_displayed hN hw.isNormalized (θ := θ)
  have h₂ := displayed_converse hθ
  have hne : T₀ ≠ treeOfBlobs net := fun h => T₀_ne_treeOfBlobs.2 (h ▸ T₀_ne_treeOfBlobs.1)
  refine ⟨not_isBinary, (hasTrivialFourBlob_iff (by decide)).2 ⟨0, by decide, rfl⟩, h₁, h₂, T₀_isResolution,
    hne, fun o hm {α β} hα hβ₀ hβ => ?_, fun o hm {α β} hα₀ hβ₀ hα hβ => ?_⟩
  · have hself := tendsto_ectoblob_displayed_self (N := net) (θ := θ) hN hw T₀_isUnrootedTree
      (A := {3, 4, 5}) (by unfold T₀ H₀ unroot; decide) (mem_treeOfBlobs_iff.2 (by decide)) (by decide)
      (fun B hB s hs hu => not_trivial_of_mem_multipartition hB hs
        ((uniform_iff h₁ h₂ s).1 hu)) hm hα hβ₀ hβ
    exact ⟨hself, tendsto_eq_zero_of_tendsto_eq (displayedTreeDist_isDist hN hw) hne hself⟩
  · exact consistency_ectoblob_displayed net θ hN hw h₂ T₀ T₀_isResolution o hm hα₀ hβ₀ hα hβ

end NonBinary

end ECToBlob.FinNetwork
