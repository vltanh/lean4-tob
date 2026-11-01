module

public import Phylogenetics.NMSC.DisplayedTreeModel
public import ECToBlob.Remark52
public import TOBQMC.Wedge

/-!
# Singleton lineages at given vertices: comparing the masses of the quartet trees

Tools for the concordance factors of quartet trees on a network, for
`src/External/AllmanBanosRhodes2019/Proposition9.lean`. A placement puts the four lineages of `q` as singletons at given
vertices (`placeInj`). `IsTL inj s` says that the masses are tree-like towards `s`: the alternatives of `s` have equal
mass, at most that of `s`.

* `isTL_of_forall_lift`, `lt_of_forall_lift`: the Markov property at a set closed under children.
* `liftSet_eq_placeInj`: what is lifted, when the forests at the top of the arcs leaving the set are singletons.
* `isTL_hub`: a vertex with three lineages at or below it, where only cherries of `s` can form below it, gives `IsTL`.
* `isTL_pair_lift`, `lt_of_pair_lift`: two lineages below an arc dominating them, a cherry of `s`.
* `isTL_two_reticulation`: two lineages at a reticulation.
* `cherryMass_one_reticulation`: one lineage at a reticulation, the exact mixture.
-/

@[expose] public noncomputable section

open Phylogenetics Phylogenetics.RootedNetwork Phylogenetics.NMSC Finset
open ECToBlob.Remark52
open scoped Classical

namespace External.AllmanBanosRhodes2019.Placement

variable {V E X : Type*} [Fintype V] [Fintype E] [Fintype X] [DecidableEq X]
variable {N : RootedNetwork V E X} {θ : MetricData E} {ρ : ℝ}

variable (N θ ρ) in
/-- The masses of the quartet trees are tree-like towards `s`. -/
def IsTL (inj : V → Finset (Finset X)) (s : QuartetTree X) : Prop :=
  (∀ r ∈ s.alternatives, cherryMass N θ ρ inj r ≤ cherryMass N θ ρ inj s) ∧
    ∀ r ∈ s.alternatives, ∀ r' ∈ s.alternatives, cherryMass N θ ρ inj r = cherryMass N θ ρ inj r'

/-- **The Markov property at a set closed under children**, for `IsTL`. -/
theorem isTL_of_forall_lift (hN : N.IsPhylogenetic) (hθ : N.IsMetric θ) (hρ : 0 ≤ ρ ∧ ρ ≤ 1)
    {inj : V → Finset (Finset X)} (hinj : ValidInj inj) {D : Finset V} (hD : DownClosed N D)
    (hroot : N.root ∉ D) {s : QuartetTree X}
    (h : ∀ bot top : E → Finset (Finset X), ∏ u ∈ D, vertexWeight N θ ρ inj u bot top ≠ 0 →
      IsTL N θ ρ (liftSet N D inj top) s) : IsTL N θ ρ inj s := by
  have hpos := setMass_pos (X := X) (N := N) D
  have hM := fun r => setMass_mul_cherryMass (θ := θ) (ρ := ρ) hN hθ.isNormalized hρ.1 hinj hD hroot r
  refine ⟨fun r hr => ?_, fun r hr r' hr' => ?_⟩
  · refine le_of_mul_le_mul_left ?_ hpos
    rw [hM, hM]
    refine sum_le_sum fun bot _ => sum_le_sum fun top _ => ?_
    by_cases hz : ∏ u ∈ D, vertexWeight N θ ρ inj u bot top = 0
    · simp [hz]
    · exact mul_le_mul_of_nonneg_left ((h bot top hz).1 r hr) (prod_vertexWeight_nonneg hθ hρ _ _ _ _)
  · refine mul_left_cancel₀ hpos.ne' ?_
    rw [hM, hM]
    refine sum_congr rfl fun bot _ => sum_congr rfl fun top _ => ?_
    by_cases hz : ∏ u ∈ D, vertexWeight N θ ρ inj u bot top = 0
    · simp [hz]
    · rw [(h bot top hz).2 r hr r' hr']

/-- The strict inequality, from a history of positive weight where it is strict. -/
theorem lt_of_forall_lift (hN : N.IsPhylogenetic) (hθ : N.IsMetric θ) (hρ : 0 ≤ ρ ∧ ρ ≤ 1)
    {inj : V → Finset (Finset X)} (hinj : ValidInj inj) {D : Finset V} (hD : DownClosed N D)
    (hroot : N.root ∉ D) {s r : QuartetTree X} (hr : r ∈ s.alternatives)
    (h : ∀ bot top : E → Finset (Finset X), ∏ u ∈ D, vertexWeight N θ ρ inj u bot top ≠ 0 →
      IsTL N θ ρ (liftSet N D inj top) s)
    {bot₁ top₁ : E → Finset (Finset X)} (hw : 0 < ∏ u ∈ D, vertexWeight N θ ρ inj u bot₁ top₁)
    (hlt : cherryMass N θ ρ (liftSet N D inj top₁) r < cherryMass N θ ρ (liftSet N D inj top₁) s) :
    cherryMass N θ ρ inj r < cherryMass N θ ρ inj s := by
  have hpos := setMass_pos (X := X) (N := N) D
  have hM := fun r => setMass_mul_cherryMass (θ := θ) (ρ := ρ) hN hθ.isNormalized hρ.1 hinj hD hroot r
  have hterm : ∀ bot top : E → Finset (Finset X),
      (∏ u ∈ D, vertexWeight N θ ρ inj u bot top) * cherryMass N θ ρ (liftSet N D inj top) r ≤
        (∏ u ∈ D, vertexWeight N θ ρ inj u bot top) * cherryMass N θ ρ (liftSet N D inj top) s := by
    intro bot top
    by_cases hz : ∏ u ∈ D, vertexWeight N θ ρ inj u bot top = 0
    · simp [hz]
    · exact mul_le_mul_of_nonneg_left ((h bot top hz).1 r hr) (prod_vertexWeight_nonneg hθ hρ _ _ _ _)
  refine lt_of_mul_lt_mul_left ?_ hpos.le
  rw [hM, hM]
  exact sum_lt_sum (fun bot _ => sum_le_sum fun top _ => hterm bot top)
    ⟨bot₁, mem_univ _, sum_lt_sum (fun top _ => hterm bot₁ top)
      ⟨top₁, mem_univ _, mul_lt_mul_of_pos_left hlt hw⟩⟩

/-- A cherry of `s` decides. -/
theorem isTL_of_cherry (hN : N.IsPhylogenetic) (hθ : N.IsMetric θ) (hρ : 0 ≤ ρ ∧ ρ ≤ 1)
    {inj : V → Finset (Finset X)} (hinj : ValidInj inj) {v : V} {s : QuartetTree X} {C : Finset X}
    (hC : C ∈ inj v) (hCs : C ∈ s.val) : IsTL N θ ρ inj s := by
  refine ⟨fun r hr => ?_, fun r hr r' hr' => ?_⟩
  · obtain ⟨h0, h1⟩ := cherryMass_of_mem_val hN hθ hρ hinj hC hCs hr
    rw [h0, h1]
    exact zero_le_one
  · rw [(cherryMass_of_mem_val hN hθ hρ hinj hC hCs hr).1, (cherryMass_of_mem_val hN hθ hρ hinj hC hCs hr').1]

/-- Three singletons at one vertex, the fourth anywhere. -/
theorem isTL_of_three (hN : N.IsPhylogenetic) (hθ : N.IsMetric θ) (hρ : 0 ≤ ρ ∧ ρ ≤ 1)
    {q : Finset X} (hq : #q = 4) {s : QuartetTree X} (hs : s.taxa = q) {P : X → V} {a : X} (ha : a ∈ q) {v : V}
    (hP : ∀ x ∈ q, x ≠ a → P x = v) : IsTL N θ ρ (placeInj q P) s := by
  have hthird : ∀ r ∈ s.alternatives, cherryMass N θ ρ (placeInj q P) r = 1 / 3 := fun r hr =>
    cherryMass_placeInj_eq_third hN hθ hρ hq ha hP
      (mem_treesOn.2 ((QuartetTree.mem_alternatives.1 hr).1.trans hs))
  refine ⟨fun r hr => ?_, fun r hr r' hr' => by rw [hthird r hr, hthird r' hr']⟩
  rw [hthird r hr, cherryMass_placeInj_eq_third hN hθ hρ hq ha hP (mem_treesOn.2 hs)]

omit [Fintype V] in
/-- **What is lifted, from singletons.** If the forests at the top of the arcs leaving `D` are singletons, and `P'`
places each lineage in `D` at the source of the arc that carries it, the lifted forests are the placement `P'`. -/
theorem liftSet_eq_placeInj {q : Finset X} {P P' : X → V} {D : Finset V} {bot top : E → Finset (Finset X)}
    (hF : Frontier N (placeInj q P) D bot top)
    (hsing : ∀ f, N.graph.target f ∈ D → N.graph.source f ∉ D →
      top f = (lineages (top f)).image fun x => ({x} : Finset X))
    (hout : ∀ z ∈ q, P z ∉ D → P' z = P z)
    (hin : ∀ z ∈ q, P z ∈ D → P' z ∉ D ∧ ∃ f, N.graph.source f = P' z ∧ N.graph.target f ∈ D ∧ z ∈ lineages (top f)) :
    liftSet N D (placeInj q P) top = placeInj q P' := by
  funext v
  by_cases hv : v ∈ D
  · have : placeInj q P' v = ∅ := by
      refine eq_empty_of_forall_notMem fun A hA => ?_
      obtain ⟨z, hz, -⟩ := mem_image.1 hA
      obtain ⟨hzq, hzv⟩ := mem_filter.1 hz
      by_cases hzD : P z ∈ D
      · exact (hin z hzq hzD).1 (hzv ▸ hv)
      · exact hzD (by rw [← hout z hzq hzD, hzv]; exact hv)
    rw [this]
    simp [liftSet, hv]
  · unfold liftSet
    rw [ite_eq_right hv]
    ext A
    simp only [mem_union, mem_biUnion, mem_filter, mem_univ, true_and]
    constructor
    · rintro (hA | ⟨f, ⟨hfs, hft⟩, hA⟩)
      · obtain ⟨z, hz, rfl⟩ := mem_image.1 hA
        obtain ⟨hzq, hzv⟩ := mem_filter.1 hz
        refine mem_image.2 ⟨z, mem_filter.2 ⟨hzq, ?_⟩, rfl⟩
        rw [hout z hzq (hzv ▸ hv), hzv]
      · have hfsD : N.graph.source f ∉ D := hfs ▸ hv
        rw [hsing f hft hfsD] at hA
        obtain ⟨z, hz, rfl⟩ := mem_image.1 hA
        obtain ⟨u, hu, hzu⟩ := (hF.mem z).1 ⟨f, hft, hfsD, hz⟩
        obtain ⟨hzq, hzP⟩ := mem_lineages_placeInj.1 hzu
        obtain ⟨hnot, f', hf's, hf't, hzf'⟩ := hin z hzq (hzP ▸ hu)
        have hff : f' = f := by
          by_contra hne
          exact disjoint_left.1 (hF.disj f' f hf't (hf's ▸ hnot) hft hfsD hne) hzf' hz
        refine mem_image.2 ⟨z, mem_filter.2 ⟨hzq, ?_⟩, rfl⟩
        rw [← hf's, hff, hfs]
    · intro hA
      obtain ⟨z, hz, rfl⟩ := mem_image.1 hA
      obtain ⟨hzq, hzv⟩ := mem_filter.1 hz
      by_cases hzD : P z ∈ D
      · obtain ⟨-, f, hfs, hft, hzf⟩ := hin z hzq hzD
        refine Or.inr ⟨f, ⟨hfs.trans hzv, hft⟩, ?_⟩
        obtain ⟨B, hB, hzB⟩ := mem_lineages.1 hzf
        exact (hF.good_top f hft).singleton_mem hB hzB
      · refine Or.inl (mem_image.2 ⟨z, mem_filter.2 ⟨hzq, ?_⟩, rfl⟩)
        rw [← hout z hzq hzD, hzv]

/-- **A hub.** At least three of the lineages of `q` are at `v₀` or in a set `D` closed under children, from which
lineages leave only through `v₀`, and in `D` only cherries of `s` can form. Then the masses are tree-like towards `s`:
given the forest arriving at `v₀`, a cherry decides, and otherwise three singletons at `v₀` make the three quartet
trees equally likely. -/
theorem isTL_hub (hN : N.IsPhylogenetic) (hθ : N.IsMetric θ) (hρ : 0 ≤ ρ ∧ ρ ≤ 1) {q : Finset X} (hq : #q = 4)
    {s : QuartetTree X} (hs : s.taxa = q) {P : X → V} {D : Finset V} (hD : DownClosed N D) (hroot : N.root ∉ D)
    {v₀ : V} (hv₀ : v₀ ∉ D)
    (hsrc : ∀ x ∈ q, ∀ f, N.graph.target f ∈ D → N.graph.source f ∉ D → N.graph.source f ≠ v₀ →
      ¬ N.graph.Reaches (N.graph.target f) (P x))
    (hpair : ∀ u ∈ D, ∀ x ∈ q, ∀ y ∈ q, x ≠ y → N.graph.Reaches u (P x) → N.graph.Reaches u (P y) →
      ({x, y} : Finset X) ∈ s.val)
    {a : X} (ha : a ∈ q) (hthree : ∀ x ∈ q, x ≠ a → P x ∈ D ∨ P x = v₀) : IsTL N θ ρ (placeInj q P) s := by
  have hv := validInj_placeInj q P
  refine isTL_of_forall_lift hN hθ hρ hv hD hroot fun bot top hz => ?_
  have hF := frontier_of_prod_ne_zero hN hv hD hz
  have hl := validInj_liftSet hv hF
  -- the arcs leaving `D` that carry lineages leave `v₀`
  have hbelow : ∀ f x, N.graph.target f ∈ D → x ∈ lineages (top f) →
      x ∈ q ∧ N.graph.Reaches (N.graph.target f) (P x) := by
    intro f x hft hx
    obtain ⟨u, hu, hxu⟩ := hF.below f hft x hx
    obtain ⟨hxq, rfl⟩ := mem_lineages_placeInj.1 hxu
    exact ⟨hxq, hu⟩
  have hsrc' : ∀ f x, N.graph.target f ∈ D → N.graph.source f ∉ D → x ∈ lineages (top f) →
      N.graph.source f = v₀ := by
    intro f x hft hfs hx
    by_contra hne
    obtain ⟨hxq, hr⟩ := hbelow f x hft hx
    exact hsrc x hxq f hft hfs hne hr
  by_cases h2 : ∃ f, N.graph.target f ∈ D ∧ N.graph.source f ∉ D ∧ ∃ C ∈ top f, #C = 2
  · -- a cherry
    obtain ⟨f, hft, hfs, C, hC, hC2⟩ := h2
    obtain ⟨x, y, hxy, rfl⟩ := card_eq_two.1 hC2
    have hxl : x ∈ lineages (top f) := mem_lineages.2 ⟨_, hC, by simp⟩
    have hyl : y ∈ lineages (top f) := mem_lineages.2 ⟨_, hC, by simp⟩
    obtain ⟨hxq, hxr⟩ := hbelow f x hft hxl
    obtain ⟨hyq, hyr⟩ := hbelow f y hft hyl
    have hCs := hpair _ hft x hxq y hyq hxy hxr hyr
    have hmem : ({x, y} : Finset X) ∈ liftSet N D (placeInj q P) top (N.graph.source f) := by
      unfold liftSet
      rw [ite_eq_right hfs]
      exact mem_union_right _ (mem_biUnion.2 ⟨f, mem_filter.2 ⟨mem_univ _, rfl, hft⟩, hC⟩)
    exact isTL_of_cherry hN hθ hρ hl hmem hCs
  · -- singletons at `v₀`
    push Not at h2
    have hsing : ∀ f, N.graph.target f ∈ D → N.graph.source f ∉ D →
        top f = (lineages (top f)).image fun x => ({x} : Finset X) := fun f hft hfs =>
      (hF.good_top f hft).eq_singletons fun ⟨C, hC, hC2⟩ => h2 f hft hfs C hC hC2
    have heq : liftSet N D (placeInj q P) top = placeInj q fun x => if P x ∈ D then v₀ else P x := by
      refine liftSet_eq_placeInj hF hsing (fun z _ hz' => ite_eq_right hz') fun z hzq hzD => ?_
      rw [ite_eq_left hzD]
      obtain ⟨f, hft, hfs, hzf⟩ := (hF.mem z).2 ⟨P z, hzD, mem_lineages_placeInj.2 ⟨hzq, rfl⟩⟩
      exact ⟨hv₀, f, hsrc' f z hft hfs hzf, hft, hzf⟩
    rw [heq]
    refine isTL_of_three hN hθ hρ hq hs ha (v := v₀) fun x hx hxa => ?_
    rcases hthree x hx hxa with h | h
    · simp only [ite_eq_left h]
    · simp only [h, ite_self]

/-- The placement with the lineages `x`, `y` moved to `u`. -/
def movePair (P : X → V) (x y : X) (u : V) : X → V := fun z => if z = x ∨ z = y then u else P z

omit [Fintype E] [Fintype X] in
/-- The hypotheses on a pair of lineages below an arc give that the arc dominates what is placed below it. -/
private theorem dominatedInj_of_pair {q : Finset X} {P : X → V} {x y : X} {e : E}
    (hdx : ¬ N.AvoidingReach e N.root (P x)) (hdy : ¬ N.AvoidingReach e N.root (P y))
    (hoth : ∀ z ∈ q, z ≠ x → z ≠ y → ¬ N.graph.Reaches (N.graph.target e) (P z)) :
    DominatedInj N e (placeInj q P) := by
  rintro u hu ⟨A, hA⟩
  obtain ⟨z, hz, rfl⟩ := mem_image.1 hA
  obtain ⟨hzq, rfl⟩ := mem_filter.1 hz
  by_cases hzx : z = x
  · rw [hzx]
    exact hdx
  by_cases hzy : z = y
  · rw [hzy]
    exact hdy
  · exact absurd (mem_belowSet.1 hu) (hoth z hzq hzx hzy)

/-- What the forest at the top of the arc gives, in `isTL_pair_lift` and `lt_of_pair_lift`. -/
private theorem isTL_lift_pair (hN : N.IsPhylogenetic) (hθ : N.IsMetric θ) (hρ : 0 ≤ ρ ∧ ρ ≤ 1)
    {q : Finset X} {P : X → V} {x y : X} (hxq : x ∈ q) (hyq : y ∈ q) (hxy : x ≠ y) {s : QuartetTree X}
    (hC : ({x, y} : Finset X) ∈ s.val) {e : E} (hbx : N.graph.Reaches (N.graph.target e) (P x))
    (hby : N.graph.Reaches (N.graph.target e) (P y)) (hdx : ¬ N.AvoidingReach e N.root (P x))
    (hdy : ¬ N.AvoidingReach e N.root (P y))
    (hoth : ∀ z ∈ q, z ≠ x → z ≠ y → ¬ N.graph.Reaches (N.graph.target e) (P z))
    (hTL : IsTL N θ ρ (placeInj q (movePair P x y (N.graph.source e))) s)
    {bot top : E → Finset (Finset X)}
    (hz : ∏ u ∈ belowSet N e, vertexWeight N θ ρ (placeInj q P) u bot top ≠ 0) :
    IsTL N θ ρ (liftSet N (belowSet N e) (placeInj q P) top) s := by
  have hv := validInj_placeInj q P
  have hdom := dominatedInj_of_pair hdx hdy hoth
  have hF := frontier_of_prod_ne_zero hN hv (downClosed_belowSet e) hz
  have hl := validInj_liftSet hv hF
  have hse := source_notMem_belowSet hN e
  have htg := target_mem_belowSet (N := N) e
  have hlin : ∀ z, z ∈ lineages (top e) ↔ z = x ∨ z = y := by
    intro z
    rw [lineages_top_of_prod_ne_zero hN hv hdom hz z]
    constructor
    · rintro ⟨u, hu, hzu⟩
      obtain ⟨hzq, rfl⟩ := mem_lineages_placeInj.1 hzu
      by_contra hne
      push Not at hne
      exact hoth z hzq hne.1 hne.2 (mem_belowSet.1 hu)
    · rintro (rfl | rfl)
      · exact ⟨_, mem_belowSet.2 hbx, mem_lineages_placeInj.2 ⟨hxq, rfl⟩⟩
      · exact ⟨_, mem_belowSet.2 hby, mem_lineages_placeInj.2 ⟨hyq, rfl⟩⟩
  have hemp : ∀ f, N.graph.target f ∈ belowSet N e → N.graph.source f ∉ belowSet N e → f ≠ e → top f = ∅ :=
    fun f hft hfs hfe => frontier_top_eq_empty hN hdom hF hft hfs hfe
  by_cases h2 : ∃ C ∈ top e, #C = 2
  · obtain ⟨C, hCt, hC2⟩ := h2
    have hCe : C = {x, y} := by
      refine eq_of_subset_of_card_le (fun z hz' => ?_) (by rw [hC2, card_pair hxy])
      have := (hlin z).1 (mem_lineages.2 ⟨C, hCt, hz'⟩)
      simpa using this
    subst hCe
    have hmem : ({x, y} : Finset X) ∈ liftSet N (belowSet N e) (placeInj q P) top (N.graph.source e) := by
      unfold liftSet
      rw [ite_eq_right hse]
      exact mem_union_right _ (mem_biUnion.2 ⟨e, mem_filter.2 ⟨mem_univ _, rfl, htg⟩, hCt⟩)
    exact isTL_of_cherry hN hθ hρ hl hmem hC
  · have hsing : ∀ f, N.graph.target f ∈ belowSet N e → N.graph.source f ∉ belowSet N e →
        top f = (lineages (top f)).image fun x => ({x} : Finset X) := by
      intro f hft hfs
      by_cases hfe : f = e
      · subst hfe
        exact (hF.good_top f htg).eq_singletons h2
      · rw [hemp f hft hfs hfe]
        simp
    have heq : liftSet N (belowSet N e) (placeInj q P) top = placeInj q (movePair P x y (N.graph.source e)) := by
      refine liftSet_eq_placeInj hF hsing (fun z hzq hzD => ?_) fun z hzq hzD => ?_
      · refine ite_eq_right ?_
        rintro (rfl | rfl)
        · exact hzD (mem_belowSet.2 hbx)
        · exact hzD (mem_belowSet.2 hby)
      · have hzxy : z = x ∨ z = y := by
          by_contra hne
          push Not at hne
          exact hoth z hzq hne.1 hne.2 (mem_belowSet.1 hzD)
        have hm : movePair P x y (N.graph.source e) z = N.graph.source e := ite_eq_left hzxy
        rw [hm]
        exact ⟨hse, e, rfl, htg, (hlin z).2 hzxy⟩
    rw [heq]
    exact hTL

/-- **Two lineages below an arc dominating them**, a cherry of `s`: it is enough to have them apart at the source of
the arc. -/
theorem isTL_pair_lift (hN : N.IsPhylogenetic) (hθ : N.IsMetric θ) (hρ : 0 ≤ ρ ∧ ρ ≤ 1)
    {q : Finset X} {P : X → V} {x y : X} (hxq : x ∈ q) (hyq : y ∈ q) (hxy : x ≠ y) {s : QuartetTree X}
    (hC : ({x, y} : Finset X) ∈ s.val) {e : E} (hbx : N.graph.Reaches (N.graph.target e) (P x))
    (hby : N.graph.Reaches (N.graph.target e) (P y)) (hdx : ¬ N.AvoidingReach e N.root (P x))
    (hdy : ¬ N.AvoidingReach e N.root (P y))
    (hoth : ∀ z ∈ q, z ≠ x → z ≠ y → ¬ N.graph.Reaches (N.graph.target e) (P z))
    (hTL : IsTL N θ ρ (placeInj q (movePair P x y (N.graph.source e))) s) : IsTL N θ ρ (placeInj q P) s :=
  isTL_of_forall_lift hN hθ hρ (validInj_placeInj q P) (downClosed_belowSet e) (root_notMem_belowSet hN e)
    fun _ _ hz => isTL_lift_pair hN hθ hρ hxq hyq hxy hC hbx hby hdx hdy hoth hTL hz

/-- A history where the two lineages below the arc `e` have coalesced at its top. As `exists_history_cherry`, for a
placement. -/
theorem exists_history_pair (hN : N.IsPhylogenetic) (hθ : N.IsMetric θ) (hρ : 0 ≤ ρ ∧ ρ ≤ 1)
    {q : Finset X} {P : X → V} {x y : X} (hxq : x ∈ q) (hyq : y ∈ q) (hxy : x ≠ y) {e : E}
    (hbx : N.graph.Reaches (N.graph.target e) (P x)) (hby : N.graph.Reaches (N.graph.target e) (P y))
    (hdx : ¬ N.AvoidingReach e N.root (P x)) (hdy : ¬ N.AvoidingReach e N.root (P y))
    (hoth : ∀ z ∈ q, z ≠ x → z ≠ y → ¬ N.graph.Reaches (N.graph.target e) (P z))
    (htree : arcsInto N (N.graph.target e) = {e}) (hlen : 0 < θ.length e) :
    ∃ bot top : E → Finset (Finset X),
      0 < ∏ u ∈ belowSet N e, vertexWeight N θ ρ (placeInj q P) u bot top ∧ ({x, y} : Finset X) ∈ top e := by
  have hv := validInj_placeInj q P
  have hdom : DominatedInj N e (placeInj q P) := dominatedInj_of_pair hdx hdy hoth
  have hP2 : #({x, y} : Finset X) = 2 := card_pair hxy
  set Q : Finset X := {x, y} with hQ
  have hsum := sum_sum_below (θ := θ) (ρ := ρ) hN hθ hρ hv e
  have hne : ∑ bot : E → Finset (Finset X), ∑ top : E → Finset (Finset X),
      ∏ v ∈ belowSet N e, vertexWeight N θ ρ (placeInj q P) v bot top ≠ 0 := by
    rw [hsum]
    exact (belowMass_pos e).ne'
  obtain ⟨bot, -, hbot⟩ := exists_ne_zero_of_sum_ne_zero hne
  obtain ⟨top, -, hg⟩ := exists_ne_zero_of_sum_ne_zero hbot
  have hnonneg : ∀ b t : E → Finset (Finset X),
      0 ≤ ∏ u ∈ belowSet N e, vertexWeight N θ ρ (placeInj q P) u b t := fun b t =>
    prod_vertexWeight_nonneg hθ hρ _ _ _ _
  by_cases hPt : Q ∈ top e
  · exact ⟨bot, top, lt_of_le_of_ne (hnonneg _ _) (Ne.symm hg), hPt⟩
  have hgood := good_top_of_prod_ne_zero hN hv hg
  have hlin : ∀ z, z ∈ lineages (top e) ↔ z ∈ Q := by
    intro z
    rw [lineages_top_of_prod_ne_zero hN hv hdom hg z, hQ, mem_insert, mem_singleton]
    constructor
    · rintro ⟨u, hu, hzu⟩
      obtain ⟨hzq, rfl⟩ := mem_lineages_placeInj.1 hzu
      by_contra hne
      push Not at hne
      exact hoth z hzq hne.1 hne.2 (mem_belowSet.1 hu)
    · rintro (rfl | rfl)
      · exact ⟨_, mem_belowSet.2 hbx, mem_lineages_placeInj.2 ⟨hxq, rfl⟩⟩
      · exact ⟨_, mem_belowSet.2 hby, mem_lineages_placeInj.2 ⟨hyq, rfl⟩⟩
  have hno2 : ¬ ∃ C ∈ top e, #C = 2 := by
    rintro ⟨C, hC, hC2⟩
    apply hPt
    rwa [← eq_of_subset_of_card_le (fun z hz => (hlin z).1 (mem_lineages.2 ⟨C, hC, hz⟩))
      (by rw [hP2, hC2])]
  have hF : top e = Q.image fun x => ({x} : Finset X) := by
    have := hgood.eq_singletons hno2
    rwa [show lineages (top e) = Q from Finset.ext hlin] at this
  set v := N.graph.target e with hvdef
  have hvD : v ∈ belowSet N e := target_mem_belowSet e
  rw [← mul_prod_erase _ _ hvD] at hg
  have hwv := left_ne_zero_of_mul hg
  have hrest := right_ne_zero_of_mul hg
  unfold vertexWeight at hwv
  rw [htree, prod_singleton] at hwv
  have halloc := left_ne_zero_of_mul hwv
  have hkin := right_ne_zero_of_mul hwv
  have hFr := frontier_of_prod_ne_zero hN hv (downClosed_belowSet e)
    (show ∏ u ∈ belowSet N e, vertexWeight N θ ρ (placeInj q P) u bot top ≠ 0 by
      rw [← mul_prod_erase _ _ hvD]
      exact hg)
  have hgb := hFr.good_bot e hvD
  obtain ⟨-, hsub, hlb⟩ := kingmanTransition_support_good hgb hkin
  have hbF : bot e = top e := by
    refine Subset.antisymm hsub fun A hA => ?_
    rw [hF] at hA
    obtain ⟨z, hz, rfl⟩ := mem_image.1 hA
    have hxb : z ∈ lineages (bot e) := hlb ▸ (hlin z).2 hz
    obtain ⟨B, hB, hxB⟩ := mem_lineages.1 hxb
    exact hgb.singleton_mem hB hxB
  refine ⟨bot, Function.update top e (insert Q (top e)), ?_, by simp⟩
  have hsrc : ∀ g, N.graph.source g = v → g ≠ e := by
    rintro g hgv rfl
    exact source_ne_target hN g hgv
  have hu : ∀ u ∈ (belowSet N e).erase v,
      vertexWeight N θ ρ (placeInj q P) u bot (Function.update top e (insert Q (top e))) =
        vertexWeight N θ ρ (placeInj q P) u bot top := by
    intro u hu
    have huv := ne_of_mem_erase hu
    have huB := mem_of_mem_erase hu
    refine vertexWeight_congr rfl (fun _ _ => rfl) (fun g hgu => ?_) (fun g hgu => ?_)
    · refine Function.update_of_ne ?_ _ _
      rintro rfl
      exact huv hgu.symm
    · refine Function.update_of_ne ?_ _ _
      rintro rfl
      exact source_notMem_belowSet hN g (hgu ▸ huB)
  have hw₁ : vertexWeight N θ ρ (placeInj q P) v bot (Function.update top e (insert Q (top e))) =
      allocationFactor N θ ρ (arriving N (placeInj q P) top v) v bot * (1 - Real.exp (-θ.length e)) := by
    unfold vertexWeight
    rw [htree, prod_singleton, Function.update_self, hbF, hF,
      kingmanTransition_singletons_cherry hP2,
      arriving_congr rfl fun g hgv => Function.update_of_ne (hsrc g hgv) _ _]
  rw [← mul_prod_erase _ _ hvD, hw₁, prod_congr rfl hu]
  have hpos1 : 0 < 1 - Real.exp (-θ.length e) := sub_pos.2 (Real.exp_lt_one_iff.2 (by linarith))
  have hpos2 : 0 < allocationFactor N θ ρ (arriving N (placeInj q P) top v) v bot :=
    lt_of_le_of_ne (allocationFactor_nonneg hθ hρ _ _ _) (Ne.symm halloc)
  have hpos3 : 0 < ∏ u ∈ (belowSet N e).erase v, vertexWeight N θ ρ (placeInj q P) u bot top :=
    lt_of_le_of_ne (prod_vertexWeight_nonneg hθ hρ _ _ _ _) (Ne.symm hrest)
  positivity

/-- **Two lineages below an arc of positive length dominating them**, a cherry of `s`: the alternatives of `s` have
strictly less mass. -/
theorem lt_of_pair_lift (hN : N.IsPhylogenetic) (hθ : N.IsMetric θ) (hρ : 0 ≤ ρ ∧ ρ ≤ 1)
    {q : Finset X} {P : X → V} {x y : X} (hxq : x ∈ q) (hyq : y ∈ q) (hxy : x ≠ y) {s : QuartetTree X}
    (hC : ({x, y} : Finset X) ∈ s.val) {e : E} (hbx : N.graph.Reaches (N.graph.target e) (P x))
    (hby : N.graph.Reaches (N.graph.target e) (P y)) (hdx : ¬ N.AvoidingReach e N.root (P x))
    (hdy : ¬ N.AvoidingReach e N.root (P y))
    (hoth : ∀ z ∈ q, z ≠ x → z ≠ y → ¬ N.graph.Reaches (N.graph.target e) (P z))
    (htree : arcsInto N (N.graph.target e) = {e}) (hlen : 0 < θ.length e)
    (hTL : IsTL N θ ρ (placeInj q (movePair P x y (N.graph.source e))) s) {r : QuartetTree X}
    (hr : r ∈ s.alternatives) : cherryMass N θ ρ (placeInj q P) r < cherryMass N θ ρ (placeInj q P) s := by
  have hv := validInj_placeInj q P
  obtain ⟨bot₁, top₁, hw, hmem⟩ := exists_history_pair (θ := θ) (ρ := ρ) hN hθ hρ hxq hyq hxy hbx hby hdx hdy hoth
    htree hlen
  refine lt_of_forall_lift hN hθ hρ hv (downClosed_belowSet e) (root_notMem_belowSet hN e) hr
    (fun _ _ hz => isTL_lift_pair hN hθ hρ hxq hyq hxy hC hbx hby hdx hdy hoth hTL hz) hw ?_
  have hF := frontier_of_prod_ne_zero hN hv (downClosed_belowSet e) hw.ne'
  have hl := validInj_liftSet hv hF
  have hm : ({x, y} : Finset X) ∈ liftSet N (belowSet N e) (placeInj q P) top₁ (N.graph.source e) := by
    unfold liftSet
    rw [ite_eq_right (source_notMem_belowSet hN e)]
    exact mem_union_right _ (mem_biUnion.2 ⟨e, mem_filter.2 ⟨mem_univ _, rfl, target_mem_belowSet e⟩, hmem⟩)
  obtain ⟨h0, h1⟩ := cherryMass_of_mem_val hN hθ hρ hl hm hC hr
  rw [h0, h1]
  exact zero_lt_one

/-! ### A reticulation -/

/-- The vertices at or below `h`. -/
def atOrBelow (N : RootedNetwork V E X) (h : V) : Finset V := univ.filter fun w => N.graph.Reaches h w

omit [Fintype E] [Fintype X] [DecidableEq X] in
theorem mem_atOrBelow {h w : V} : w ∈ atOrBelow N h ↔ N.graph.Reaches h w := by
  simp [atOrBelow]

omit [Fintype E] [Fintype X] [DecidableEq X] in
theorem downClosed_atOrBelow (h : V) : DownClosed N (atOrBelow N h) := fun f hf =>
  mem_atOrBelow.2 ((mem_atOrBelow.1 hf).tail ⟨f, rfl, rfl⟩)

omit [Fintype E] [Fintype X] [DecidableEq X] in
theorem root_notMem_atOrBelow (hN : N.IsPhylogenetic) {h : V} (hh : h ≠ N.root) : N.root ∉ atOrBelow N h := fun hm =>
  hh (TOBQMC.Level1.eq_root_of_reaches_root hN (mem_atOrBelow.1 hm))

/-- The placement with the lineages `x`, `y` moved to `u`, `u'`. -/
def moveTwo (P : X → V) (x y : X) (u u' : V) : X → V := fun z => if z = x then u else if z = y then u' else P z

/-- **Two lineages at a reticulation**: it is enough to have them, apart, at its two parents, in the four ways, if
they are a cherry of `s`. -/
theorem isTL_two_reticulation (hN : N.IsPhylogenetic) (hθ : N.IsMetric θ) (hρ : 0 ≤ ρ ∧ ρ ≤ 1)
    {q : Finset X} {P : X → V} {x y : X} (hxq : x ∈ q) (hyq : y ∈ q) (hxy : x ≠ y) {s : QuartetTree X}
    (hC : ({x, y} : Finset X) ∈ s.val) {h : V} (hhr : h ≠ N.root) (hPx : P x = h) (hPy : P y = h)
    (hoth : ∀ z ∈ q, z ≠ x → z ≠ y → ¬ N.graph.Reaches h (P z)) {k₁ k₂ : E} (hk₁ : N.graph.target k₁ = h)
    (hk₂ : N.graph.target k₂ = h) (hk : ∀ f, N.graph.target f = h → f = k₁ ∨ f = k₂)
    (h₁₁ : IsTL N θ ρ (placeInj q (moveTwo P x y (N.graph.source k₁) (N.graph.source k₁))) s)
    (h₁₂ : IsTL N θ ρ (placeInj q (moveTwo P x y (N.graph.source k₁) (N.graph.source k₂))) s)
    (h₂₁ : IsTL N θ ρ (placeInj q (moveTwo P x y (N.graph.source k₂) (N.graph.source k₁))) s)
    (h₂₂ : IsTL N θ ρ (placeInj q (moveTwo P x y (N.graph.source k₂) (N.graph.source k₂))) s) :
    IsTL N θ ρ (placeInj q P) s := by
  have hv := validInj_placeInj q P
  refine isTL_of_forall_lift hN hθ hρ hv (downClosed_atOrBelow h) (root_notMem_atOrBelow hN hhr)
    fun bot top hz => ?_
  have hF := frontier_of_prod_ne_zero hN hv (downClosed_atOrBelow h) hz
  have hl := validInj_liftSet hv hF
  have hsrcn : ∀ {k : E}, N.graph.target k = h → N.graph.source k ∉ atOrBelow N h := fun hk' hm =>
    TOBQMC.Level1.not_reaches_source hN _ (hk' ▸ mem_atOrBelow.1 hm)
  have hhD : h ∈ atOrBelow N h := mem_atOrBelow.2 .refl
  -- only the arcs into `h` carry lineages
  have hemp : ∀ f, N.graph.target f ∈ atOrBelow N h → N.graph.source f ∉ atOrBelow N h →
      N.graph.target f ≠ h → top f = ∅ := by
    intro f hft hfs hne
    refine eq_empty_of_forall_notMem fun A hA => ?_
    obtain ⟨z, hzA⟩ := (hF.good_top f hft).1.1 A hA
    obtain ⟨u, hu, hzu⟩ := hF.below f hft z (mem_lineages.2 ⟨A, hA, hzA⟩)
    obtain ⟨hzq, rfl⟩ := mem_lineages_placeInj.1 hzu
    have hreach : N.graph.Reaches h (P z) := (mem_atOrBelow.1 hft).trans hu
    by_cases hzx : z = x ∨ z = y
    · have hPz : P z = h := by
        rcases hzx with rfl | rfl
        · exact hPx
        · exact hPy
      rw [hPz] at hu
      exact hne (eq_of_reaches_of_reaches hN.acyclic hu (mem_atOrBelow.1 hft))
    · push Not at hzx
      exact hoth z hzq hzx.1 hzx.2 hreach
  have hlin : ∀ z, (z = x ∨ z = y) → z ∈ lineages (top k₁) ∨ z ∈ lineages (top k₂) := by
    intro z hzxy
    have hzq : z ∈ q := by
      rcases hzxy with rfl | rfl
      · exact hxq
      · exact hyq
    have hPz : P z = h := by
      rcases hzxy with rfl | rfl
      · exact hPx
      · exact hPy
    obtain ⟨f, hft, hfs, hzf⟩ := (hF.mem z).2 ⟨h, hhD, mem_lineages_placeInj.2 ⟨hzq, hPz⟩⟩
    by_cases hfh : N.graph.target f = h
    · rcases hk f hfh with rfl | rfl
      · exact Or.inl hzf
      · exact Or.inr hzf
    · rw [hemp f hft hfs hfh] at hzf
      simp at hzf
  have hzone : ∀ {k : E}, N.graph.target k = h → ∀ z, z ∈ lineages (top k) → z = x ∨ z = y := by
    intro k hk' z hz'
    have hft : N.graph.target k ∈ atOrBelow N h := by rw [hk']; exact hhD
    obtain ⟨u, hu, hzu⟩ := hF.below k hft z hz'
    obtain ⟨hzq, rfl⟩ := mem_lineages_placeInj.1 hzu
    by_contra hne
    push Not at hne
    exact hoth z hzq hne.1 hne.2 (hk' ▸ hu)
  by_cases h2 : ∃ k, N.graph.target k = h ∧ ∃ C ∈ top k, #C = 2
  · obtain ⟨k, hk', C, hCt, hC2⟩ := h2
    have hCe : C = {x, y} := by
      refine eq_of_subset_of_card_le (fun z hz' => ?_) (by rw [hC2, card_pair hxy])
      have := hzone hk' z (mem_lineages.2 ⟨C, hCt, hz'⟩)
      simpa using this
    subst hCe
    have hmem : ({x, y} : Finset X) ∈ liftSet N (atOrBelow N h) (placeInj q P) top (N.graph.source k) := by
      unfold liftSet
      rw [ite_eq_right (hsrcn hk')]
      exact mem_union_right _ (mem_biUnion.2 ⟨k, mem_filter.2 ⟨mem_univ _, rfl, by rw [hk']; exact hhD⟩, hCt⟩)
    exact isTL_of_cherry hN hθ hρ hl hmem hC
  · push Not at h2
    have hsing : ∀ f, N.graph.target f ∈ atOrBelow N h → N.graph.source f ∉ atOrBelow N h →
        top f = (lineages (top f)).image fun x => ({x} : Finset X) := by
      intro f hft hfs
      by_cases hfh : N.graph.target f = h
      · exact (hF.good_top f hft).eq_singletons fun ⟨C, hC, hC2⟩ => h2 f hfh C hC hC2
      · rw [hemp f hft hfs hfh]
        simp
    have key : ∀ {a b : E}, N.graph.target a = h → N.graph.target b = h → x ∈ lineages (top a) →
        y ∈ lineages (top b) → liftSet N (atOrBelow N h) (placeInj q P) top =
          placeInj q (moveTwo P x y (N.graph.source a) (N.graph.source b)) := by
      intro a b ha hb hxa hyb
      refine liftSet_eq_placeInj hF hsing (fun z hzq hzD => ?_) fun z hzq hzD => ?_
      · have hzx : z ≠ x := by
          rintro rfl
          exact hzD (hPx ▸ hhD)
        have hzy : z ≠ y := by
          rintro rfl
          exact hzD (hPy ▸ hhD)
        simp [moveTwo, hzx, hzy]
      · have hzxy : z = x ∨ z = y := by
          by_contra hne
          push Not at hne
          exact hoth z hzq hne.1 hne.2 (mem_atOrBelow.1 hzD)
        rcases hzxy with rfl | rfl
        · have hm : moveTwo P z y (N.graph.source a) (N.graph.source b) z = N.graph.source a := by simp [moveTwo]
          rw [hm]
          exact ⟨hsrcn ha, a, rfl, by rw [ha]; exact hhD, hxa⟩
        · have hm : moveTwo P x z (N.graph.source a) (N.graph.source b) z = N.graph.source b := by
            simp [moveTwo, hxy.symm]
          rw [hm]
          exact ⟨hsrcn hb, b, rfl, by rw [hb]; exact hhD, hyb⟩
    rcases hlin x (Or.inl rfl) with hx₁ | hx₂ <;> rcases hlin y (Or.inr rfl) with hy₁ | hy₂
    · rw [key hk₁ hk₁ hx₁ hy₁]
      exact h₁₁
    · rw [key hk₁ hk₂ hx₁ hy₂]
      exact h₁₂
    · rw [key hk₂ hk₁ hx₂ hy₁]
      exact h₂₁
    · rw [key hk₂ hk₂ hx₂ hy₂]
      exact h₂₂

/-- The Markov property as a mean, as in `src/ECToBlob/Remark33Counterexample.lean`. -/
theorem cherryMass_eq_meanOn_lift (hN : N.IsPhylogenetic) (hθ : N.IsNormalized θ)
    (hρ : 0 ≤ ρ) {inj : V → Finset (Finset X)} (hinj : ValidInj inj) {D : Finset V} (hD : DownClosed N D)
    (hroot : N.root ∉ D) (r : QuartetTree X) :
    cherryMass N θ ρ inj r = meanOn N θ ρ inj D fun top => cherryMass N θ ρ (liftSet N D inj top) r := by
  have hB : (0 : ℝ) < ((Fintype.card (Finset (Finset X)) : ℕ) : ℝ) := by exact_mod_cast Fintype.card_pos
  have hM := setMass_mul_cherryMass hN hθ hρ hinj hD hroot r
  have hpos := setMass_pos (X := X) (N := N) D
  unfold meanOn
  rw [← hM]
  unfold setMass arcsIn
  field_simp

/-- **One lineage at a reticulation, the exact mixture.** With nothing else at or below the reticulation, the lineage
goes to each of its two parents with the inheritance probabilities. -/
theorem cherryMass_one_reticulation (hN : N.IsPhylogenetic) (hθ : N.IsMetric θ) (hρ : 0 ≤ ρ ∧ ρ ≤ 1)
    {q : Finset X} {P : X → V} {x : X} (hxq : x ∈ q) {h : V} (hhr : h ≠ N.root) (hPx : P x = h)
    (hoth : ∀ z ∈ q, z ≠ x → ¬ N.graph.Reaches h (P z)) {k₁ k₂ : E} (hk₁ : N.graph.target k₁ = h)
    (hk₂ : N.graph.target k₂ = h) (hne : k₁ ≠ k₂) (hk : ∀ f, N.graph.target f = h → f = k₁ ∨ f = k₂)
    (r : QuartetTree X) :
    cherryMass N θ ρ (placeInj q P) r =
      θ.inheritance k₁ * cherryMass N θ ρ (placeInj q (Function.update P x (N.graph.source k₁))) r +
        θ.inheritance k₂ * cherryMass N θ ρ (placeInj q (Function.update P x (N.graph.source k₂))) r := by
  have hv := validInj_placeInj q P
  set D₀ := (atOrBelow N h).erase h with hD₀
  have hmemD₀ : ∀ w, w ∈ D₀ ↔ w ≠ h ∧ N.graph.Reaches h w := fun w => by
    rw [hD₀, mem_erase, mem_atOrBelow]
  have hDown₀ : DownClosed N D₀ := by
    intro f hf
    obtain ⟨hne', hr⟩ := (hmemD₀ _).1 hf
    refine (hmemD₀ _).2 ⟨fun heq => ?_, hr.tail ⟨f, rfl, rfl⟩⟩
    exact hne' (eq_of_reaches_of_reaches hN.acyclic (heq ▸ TOBQMC.Level1.reaches_of_arc N f) hr)
  have hch : ∀ f, N.graph.source f = h → N.graph.target f ∈ D₀ := fun f hf => by
    refine (hmemD₀ _).2 ⟨fun heq => source_ne_target hN f (hf.trans heq.symm), ?_⟩
    rw [← hf]
    exact TOBQMC.Level1.reaches_of_arc N f
  have hhD₀ : h ∉ D₀ := fun hm => ((hmemD₀ _).1 hm).1 rfl
  have hroot₀ : N.root ∉ D₀ := fun hm => root_notMem_atOrBelow hN hhr (mem_atOrBelow.2 ((hmemD₀ _).1 hm).2)
  have hDeq : atOrBelow N h = insert h D₀ := (insert_erase (mem_atOrBelow.2 .refl)).symm
  have hsame : ∀ z ∈ q, P z ∈ atOrBelow N h → z = x := fun z hzq hzD => by
    by_contra hne'
    exact hoth z hzq hne' (mem_atOrBelow.1 hzD)
  have hempty : ∀ u ∈ D₀, placeInj q P u = ∅ := by
    intro u hu
    refine eq_empty_of_forall_notMem fun A hA => ?_
    obtain ⟨z, hz, -⟩ := mem_image.1 hA
    obtain ⟨hzq, rfl⟩ := mem_filter.1 hz
    obtain ⟨hne', hr⟩ := (hmemD₀ _).1 hu
    have := hsame z hzq (mem_atOrBelow.2 hr)
    subst this
    exact hne' hPx
  have hinjh : placeInj q P h = {{x}} := by
    unfold placeInj
    have : (q.filter fun z => P z = h) = {x} := by
      ext z
      simp only [mem_filter, mem_singleton]
      exact ⟨fun ⟨hzq, hz⟩ => hsame z hzq (hz ▸ mem_atOrBelow.2 .refl), fun hz => hz ▸ ⟨hxq, hPx⟩⟩
    rw [this, image_singleton]
  rw [cherryMass_eq_meanOn_lift hN hθ.isNormalized hρ.1 hv (downClosed_atOrBelow h) (root_notMem_atOrBelow hN hhr) r,
    hDeq, meanOn_insert hDown₀ hhD₀ hch]
  refine meanOn_eq_const hN hθ.isNormalized hρ.1 hv hDown₀ hroot₀ fun bot top hz => ?_
  have htop : ∀ f, N.graph.target f ∈ D₀ → top f = ∅ := fun f hf =>
    top_eq_empty_of_inj_empty hN hDown₀ hv hempty hz hf
  have harr : arriving N (placeInj q P) top h = {{x}} := by
    rw [arriving_eq_biUnion (S := univ.filter fun f => N.graph.source f = h) (fun f => by simp), hinjh]
    refine union_eq_left.2 fun A hA => ?_
    obtain ⟨f, hf, hAf⟩ := mem_biUnion.1 hA
    rw [htop f (hch f (mem_filter.1 hf).2)] at hAf
    simp at hAf
  -- the lifted forests
  have hlift : ∀ {k : E} (T : E → Finset (Finset X)), N.graph.target k = h → T k = {{x}} →
      (∀ f, N.graph.target f = h → f ≠ k → T f = ∅) →
      liftSet N (insert h D₀) (placeInj q P) (ow (arcsInto N h) top T) =
        placeInj q (Function.update P x (N.graph.source k)) := by
    intro k T hkt hTk hTo
    have hks : N.graph.source k ∉ insert h D₀ := by
      rw [← hDeq, mem_atOrBelow]
      exact fun hc => TOBQMC.Level1.not_reaches_source hN k (hkt ▸ hc)
    funext w
    by_cases hw : w ∈ insert h D₀
    · have hrhs : placeInj q (Function.update P x (N.graph.source k)) w = ∅ := by
        refine eq_empty_of_forall_notMem fun A hA => ?_
        obtain ⟨z, hz, -⟩ := mem_image.1 hA
        obtain ⟨hzq, hzw⟩ := mem_filter.1 hz
        by_cases hzx : z = x
        · subst hzx
          rw [Function.update_self] at hzw
          exact hks (hzw ▸ hw)
        · rw [Function.update_of_ne hzx] at hzw
          rw [← hDeq] at hw
          exact hzx (hsame z hzq (hzw ▸ hw))
      rw [hrhs]
      simp [liftSet, hw]
    · unfold liftSet
      rw [ite_eq_right hw]
      ext A
      simp only [mem_union, mem_biUnion, mem_filter, mem_univ, true_and]
      constructor
      · rintro (hA | ⟨f, ⟨hfs, hft⟩, hA⟩)
        · obtain ⟨z, hz, rfl⟩ := mem_image.1 hA
          obtain ⟨hzq, hzw⟩ := mem_filter.1 hz
          have hzx : z ≠ x := by
            rintro rfl
            rw [← hDeq] at hw
            exact hw (mem_atOrBelow.2 (hzw ▸ hPx ▸ .refl))
          refine mem_image.2 ⟨z, mem_filter.2 ⟨hzq, ?_⟩, rfl⟩
          rwa [Function.update_of_ne hzx]
        · by_cases hfh : N.graph.target f = h
          · rw [ow_of_mem (mem_arcsInto.2 hfh)] at hA
            by_cases hfk : f = k
            · subst hfk
              rw [hTk, mem_singleton] at hA
              subst hA
              refine mem_image.2 ⟨x, mem_filter.2 ⟨hxq, ?_⟩, rfl⟩
              rw [Function.update_self, hfs]
            · rw [hTo f hfh hfk] at hA
              simp at hA
          · have hft' : N.graph.target f ∈ D₀ := by
              rcases mem_insert.1 hft with h' | h'
              · exact absurd h' hfh
              · exact h'
            rw [ow_of_notMem (by rw [mem_arcsInto]; exact hfh), htop f hft'] at hA
            simp at hA
      · intro hA
        obtain ⟨z, hz, rfl⟩ := mem_image.1 hA
        obtain ⟨hzq, hzw⟩ := mem_filter.1 hz
        by_cases hzx : z = x
        · subst hzx
          rw [Function.update_self] at hzw
          refine Or.inr ⟨k, ⟨hzw, by rw [hkt]; exact mem_insert_self _ _⟩, ?_⟩
          rw [ow_of_mem (mem_arcsInto.2 hkt), hTk]
          exact mem_singleton_self _
        · rw [Function.update_of_ne hzx] at hzw
          exact Or.inl (mem_image.2 ⟨z, mem_filter.2 ⟨hzq, hzw⟩, rfl⟩)
  have hstep := stepOf_two_one (N := N) (θ := θ) (ρ := ρ) (v := h) (k₁ := k₁) (k₂ := k₂) hk₁ hk₂ hne hk
    (isForest_singleton_singleton x) (roots_singleton_singleton x)
    (fun t => (fun top' => cherryMass N θ ρ (liftSet N (insert h D₀) (placeInj q P) top') r) (ow (arcsInto N h) top t))
    (ow_dep (arcsInto N h) top fun top' => cherryMass N θ ρ (liftSet N (insert h D₀) (placeInj q P) top') r)
  unfold stepKernel
  rw [harr, hstep]
  simp only
  rw [hlift (k := k₁) _ hk₁ (pairFn_left _ _ _ _) ?_, hlift (k := k₂) _ hk₂ (pairFn_right hne _ _) ?_]
  · intro f hf hfk
    rcases hk f hf with rfl | rfl
    · exact pairFn_left _ _ _ _
    · exact absurd rfl hfk
  · intro f hf hfk
    rcases hk f hf with rfl | rfl
    · exact absurd rfl hfk
    · exact pairFn_right hne _ _

end External.AllmanBanosRhodes2019.Placement
