module

public import External.AllmanBanosRhodes2019.Proposition9

/-!
# Proposition 9 of NANUQ, part 2

"If `N⁻` has a `3₂`-cycle, then its concordance factor `CF` may or may not be tree-like. In particular, `CF` is on the
extended line segment in `Δ₂` containing the tree-like concordance factors that support the quartet `N_c⁻`. Specifically,
if `N_c⁻ = ab|cd`, then `CF_AB|CD ≥ 1/6`, and `CF_AC|BD = CF_AD|BC`, and any such tree-like `CF` supports `ab|cd`" (line 476).

* `proposition9_part2`: all of this, on a binary level-1 network, at any `0 ≤ ρ ≤ 1`.
* `third_le_cherryMass_of_isTL`, `le_cherryMass_of_forall_lift`, `le_cherryMass_of_pair_lift`,
  `half_le_cherryMass_two_reticulation`: what the proof needs of the placement calculus.

## The argument

The source takes the proposition from its references and prints no proof. The formula it prints for a `3₂`-cycle
(line 585) reaches the bound in the limit: at `x₁ = x₂ = x₄ = 1`, `x₃ = 0`, `γ = 1/2`, the formula has `CF_AB|CD = 1/6`
(`figure5_one_sixth`), so that the constant cannot be improved, though valid parameters have `x₁ < 1`. The proof here has no formula. The lineages of `a`, `b` go up to the reticulation, if
they have not coalesced, which decides for `ab|cd`. There they take the same parent with probability at least `1/2`
(`half_le_cherryMass_two_reticulation`), whatever the inheritance probabilities and `ρ`. With both at one parent, the
masses are tree-like towards `ab|cd` (`isTL_of_colocated`), so that this tree has mass at least `1/3`.
-/

@[expose] public noncomputable section

open Phylogenetics Phylogenetics.RootedNetwork Phylogenetics.NMSC Finset
open TOBQMC TOBQMC.Level1
open External.AllmanBanosRhodes2019.Placement
open Phylogenetics.NMSC.Chain
open scoped Classical

namespace External.AllmanBanosRhodes2019

variable {V E X : Type*} [Fintype V] [Fintype E] [Fintype X] [DecidableEq X]
variable {N : RootedNetwork V E X} {θ : MetricData E} {ρ : ℝ}

/-- The source's formula at the limit of its parameters has `CF_AB|CD = 1/6`: `1/6` is the best constant. -/
theorem figure5_one_sixth : figure5CFab (1 / 2) 1 1 0 1 = 1 / 6 := by
  norm_num [figure5CFab]

/-! ### Lower bounds through the Markov property -/

omit [Fintype V] [Fintype E] [DecidableEq X] [Fintype X] in
theorem lineages_placeInj_iff [Fintype X] [DecidableEq X] {q : Finset X} {P : X → V} (x : X) :
    (∃ u, x ∈ lineages (placeInj q P u)) ↔ x ∈ q :=
  ⟨fun ⟨_, hu⟩ => (mem_lineages_placeInj.1 hu).1, fun hx => ⟨P x, mem_lineages_placeInj.2 ⟨hx, rfl⟩⟩⟩

/-- **Tree-like masses give the tree at least `1/3`**, since the three masses sum to one. -/
theorem third_le_cherryMass_of_isTL (hN : N.IsPhylogenetic) (hθ : N.IsMetric θ) (hρ : 0 ≤ ρ ∧ ρ ≤ 1)
    {s : QuartetTree X} {P : X → V} (h : IsTL N θ ρ (placeInj s.taxa P) s) :
    1 / 3 ≤ cherryMass N θ ρ (placeInj s.taxa P) s := by
  have hsum := sum_cherryMass (θ := θ) (ρ := ρ) hN hθ hρ (validInj_placeInj s.taxa P) s.card_taxa lineages_placeInj_iff
  obtain ⟨r₁, r₂, hne₂, ha⟩ := QuartetTests.QuartetTree.exists_alternatives s
  have hr₁ : r₁ ∈ s.alternatives := by rw [ha]; simp
  have hr₂ : r₂ ∈ s.alternatives := by rw [ha]; simp
  have hT : treesOn s.taxa = {s, r₁, r₂} := by
    ext r
    simp only [mem_treesOn, mem_insert, mem_singleton]
    constructor
    · intro hr
      by_cases hrs : r = s
      · exact Or.inl hrs
      · have : r ∈ s.alternatives := QuartetTree.mem_alternatives.2 ⟨hr, hrs⟩
        rw [ha] at this
        simpa using Or.inr (by simpa using this)
    · rintro (rfl | rfl | rfl)
      · rfl
      · exact (QuartetTree.mem_alternatives.1 hr₁).1
      · exact (QuartetTree.mem_alternatives.1 hr₂).1
  have hsr₁ : s ≠ r₁ := (QuartetTree.mem_alternatives.1 hr₁).2.symm
  have hsr₂ : s ≠ r₂ := (QuartetTree.mem_alternatives.1 hr₂).2.symm
  rw [hT, sum_insert (by simp [hsr₁, hsr₂]), sum_pair hne₂] at hsum
  have h₁ := h.1 r₁ hr₁
  have h₂ := h.1 r₂ hr₂
  linarith

/-- **The Markov property at a set closed under children**, for a lower bound. -/
theorem le_cherryMass_of_forall_lift (hN : N.IsPhylogenetic) (hθ : N.IsMetric θ) (hρ : 0 ≤ ρ ∧ ρ ≤ 1)
    {inj : V → Finset (Finset X)} (hinj : ValidInj inj) {D : Finset V} (hD : DownClosed N D)
    (hroot : N.root ∉ D) {s : QuartetTree X} {c : ℝ}
    (h : ∀ bot top : E → Finset (Finset X), ∏ u ∈ D, vertexWeight N θ ρ inj u bot top ≠ 0 →
      c ≤ cherryMass N θ ρ (liftSet N D inj top) s) : c ≤ cherryMass N θ ρ inj s := by
  have hpos := setMass_pos (X := X) (N := N) D
  have hM := setMass_mul_cherryMass (θ := θ) (ρ := ρ) hN hθ.isNormalized hρ.1 hinj hD hroot s
  have hT := sum_sum_prod_eq_setMass (θ := θ) (ρ := ρ) hN hθ.isNormalized hρ.1 hinj hD hroot
  refine le_of_mul_le_mul_left ?_ hpos
  rw [hM, ← hT, sum_mul]
  refine sum_le_sum fun bot _ => ?_
  rw [sum_mul]
  refine sum_le_sum fun top _ => ?_
  by_cases hz : ∏ u ∈ D, vertexWeight N θ ρ inj u bot top = 0
  · simp [hz]
  · exact mul_le_mul_of_nonneg_left (h bot top hz) (prod_vertexWeight_nonneg hθ hρ _ _ _ _)

/-- A lower bound on a mean, from a lower bound on the histories of nonzero weight. -/
theorem le_meanOn (hN : N.IsPhylogenetic) (hθ : N.IsMetric θ) (hρ : 0 ≤ ρ ∧ ρ ≤ 1)
    {inj : V → Finset (Finset X)} (hinj : ValidInj inj) {D : Finset V} (hD : DownClosed N D)
    (hroot : N.root ∉ D) {φ : (E → Finset (Finset X)) → ℝ} {c : ℝ}
    (h : ∀ bot top : E → Finset (Finset X), ∏ u ∈ D, vertexWeight N θ ρ inj u bot top ≠ 0 → c ≤ φ top) :
    c ≤ meanOn N θ ρ inj D φ := by
  have hB : (0 : ℝ) < ((Fintype.card (Finset (Finset X)) : ℕ) : ℝ) := by exact_mod_cast Fintype.card_pos
  have hmass := sum_sum_prod_vertexWeight_weak (θ := θ) (ρ := ρ) hN hθ.isNormalized hρ.1 hinj hD hroot
  have hsum : c * ∑ bot : E → Finset (Finset X), ∑ top : E → Finset (Finset X),
        ∏ u ∈ D, vertexWeight N θ ρ inj u bot top ≤
      ∑ bot : E → Finset (Finset X), ∑ top : E → Finset (Finset X),
        (∏ u ∈ D, vertexWeight N θ ρ inj u bot top) * φ top := by
    rw [mul_sum]
    refine sum_le_sum fun bot _ => ?_
    rw [mul_sum]
    refine sum_le_sum fun top _ => ?_
    by_cases hw : ∏ u ∈ D, vertexWeight N θ ρ inj u bot top = 0
    · simp [hw]
    · rw [mul_comm]
      exact mul_le_mul_of_nonneg_left (h bot top hw) (prod_vertexWeight_nonneg hθ hρ _ _ _ _)
  unfold meanOn
  have hne : (0 : ℝ) < (((Fintype.card (Finset (Finset X)) : ℕ) : ℝ) ^ Fintype.card E) ^ 2 := by positivity
  rw [le_div_iff₀ hne, ← hmass]
  have hnn : (0 : ℝ) ≤ (((Fintype.card (Finset (Finset X)) : ℕ) : ℝ) ^
      #(univ.filter fun e => N.graph.target e ∈ D)) ^ 2 := by positivity
  calc c * ((((Fintype.card (Finset (Finset X)) : ℕ) : ℝ) ^ #(univ.filter fun e => N.graph.target e ∈ D)) ^ 2 *
        ∑ bot : E → Finset (Finset X), ∑ top : E → Finset (Finset X), ∏ u ∈ D, vertexWeight N θ ρ inj u bot top)
      = (((Fintype.card (Finset (Finset X)) : ℕ) : ℝ) ^ #(univ.filter fun e => N.graph.target e ∈ D)) ^ 2 *
        (c * ∑ bot : E → Finset (Finset X), ∑ top : E → Finset (Finset X),
          ∏ u ∈ D, vertexWeight N θ ρ inj u bot top) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hsum hnn

/-- **Two lineages below an arc dominating them**, a cherry of `s`: a lower bound at most one on the mass of `s` with
them apart at the source of the arc passes down. -/
theorem le_cherryMass_of_pair_lift (hN : N.IsPhylogenetic) (hθ : N.IsMetric θ) (hρ : 0 ≤ ρ ∧ ρ ≤ 1)
    {q : Finset X} {P : X → V} {x y : X} (hxq : x ∈ q) (hyq : y ∈ q) (hxy : x ≠ y) {s : QuartetTree X}
    (hC : ({x, y} : Finset X) ∈ s.val) {e : E} (hbx : N.graph.Reaches (N.graph.target e) (P x))
    (hby : N.graph.Reaches (N.graph.target e) (P y)) (hdx : ¬ N.AvoidingReach e N.root (P x))
    (hdy : ¬ N.AvoidingReach e N.root (P y))
    (hoth : ∀ z ∈ q, z ≠ x → z ≠ y → ¬ N.graph.Reaches (N.graph.target e) (P z)) {c : ℝ} (hc : c ≤ 1)
    (hge : c ≤ cherryMass N θ ρ (placeInj q (movePair P x y (N.graph.source e))) s) :
    c ≤ cherryMass N θ ρ (placeInj q P) s := by
  have hv := validInj_placeInj q P
  refine le_cherryMass_of_forall_lift hN hθ hρ hv (downClosed_belowSet e) (root_notMem_belowSet hN e)
    fun bot top hz => ?_
  have hl := validInj_liftSet hv (frontier_of_prod_ne_zero hN hv (downClosed_belowSet e) hz)
  rcases liftSet_pair_cases hN hxq hyq hxy hbx hby hdx hdy hoth hz with hmem | heq
  · obtain ⟨r₁, r₂, -, ha⟩ := QuartetTests.QuartetTree.exists_alternatives s
    have hr₁ : r₁ ∈ s.alternatives := by rw [ha]; simp
    rw [(cherryMass_of_mem_val hN hθ hρ hl hmem hC hr₁).2]
    exact hc
  · rw [heq]
    exact hge

/-! ### Two lineages at a reticulation -/

omit [Fintype V] [Fintype E] in
/-- A placement, with a cherry of two lineages placed together added at their vertex, is a valid injection. -/
theorem validInj_insert_pair {q : Finset X} {P : X → V} {x y : X} (hxq : x ∈ q) (hyq : y ∈ q) (hxy : x ≠ y) {u : V}
    (hPx : P x = u) (hPy : P y = u) :
    ValidInj fun w => if w = u then insert ({x, y} : Finset X) (placeInj q P u) else placeInj q P w := by
  have hv := validInj_placeInj q P
  have hx : ({x} : Finset X) ∈ roots (placeInj q P u) := by
    rw [placeInj, roots_singletons]
    exact mem_image.2 ⟨x, mem_filter.2 ⟨hxq, hPx⟩, rfl⟩
  have hy : ({y} : Finset X) ∈ roots (placeInj q P u) := by
    rw [placeInj, roots_singletons]
    exact mem_image.2 ⟨y, mem_filter.2 ⟨hyq, hPy⟩, rfl⟩
  have hne : ({x} : Finset X) ≠ {y} := by simpa using hxy
  have hgood : IsGoodForest (insert ({x, y} : Finset X) (placeInj q P u)) := by
    have := (hv.good u).merge hx hy hne
    rwa [show ({x} : Finset X) ∪ {y} = {x, y} by ext; simp] at this
  have hlin : ∀ z, z ∈ lineages (insert ({x, y} : Finset X) (placeInj q P u)) ↔ z ∈ lineages (placeInj q P u) := by
    intro z
    constructor
    · intro hz
      obtain ⟨A, hA, hzA⟩ := mem_lineages.1 hz
      rcases mem_insert.1 hA with rfl | hA
      · simp only [mem_insert, mem_singleton] at hzA
        rcases hzA with rfl | rfl
        · exact mem_lineages_placeInj.2 ⟨hxq, hPx⟩
        · exact mem_lineages_placeInj.2 ⟨hyq, hPy⟩
      · exact mem_lineages.2 ⟨A, hA, hzA⟩
    · intro hz
      obtain ⟨A, hA, hzA⟩ := mem_lineages.1 hz
      exact mem_lineages.2 ⟨A, mem_insert_of_mem hA, hzA⟩
  refine ⟨fun w => ?_, fun w w' hww => ?_⟩
  · by_cases hw : w = u
    · simp only [hw, ↓reduceIte]
      exact hgood
    · simp only [hw, ↓reduceIte]
      exact hv.good w
  · refine disjoint_left.2 fun z hz hz' => ?_
    have h₁ : z ∈ lineages (placeInj q P w) := by
      by_cases hw : w = u
      · simp only [hw, ↓reduceIte] at hz
        rw [hw]
        exact (hlin z).1 hz
      · simpa only [hw, ↓reduceIte] using hz
    have h₂ : z ∈ lineages (placeInj q P w') := by
      by_cases hw : w' = u
      · simp only [hw, ↓reduceIte] at hz'
        rw [hw]
        exact (hlin z).1 hz'
      · simpa only [hw, ↓reduceIte] using hz'
    exact disjoint_left.1 (hv.disj w w' hww) h₁ h₂

/-- **Two lineages at a reticulation, a cherry of `s`.** They take one parent with probability at least `1/2`, whatever
the inheritance probabilities and `ρ`. So a lower bound `c ≤ 1` on the mass of `s` with both at either parent gives the
bound `c / 2`, the mass being nonnegative when they take different parents. This is the source's term
`(1 - γ)² ... + γ² ...` of the line 585, with `(1 - γ)² + γ² ≥ 1/2`. -/
theorem half_le_cherryMass_two_reticulation (hN : N.IsPhylogenetic) (hθ : N.IsMetric θ) (hρ : 0 ≤ ρ ∧ ρ ≤ 1)
    {q : Finset X} {P : X → V} {x y : X} (hxq : x ∈ q) (hyq : y ∈ q) (hxy : x ≠ y) {s : QuartetTree X}
    (hC : ({x, y} : Finset X) ∈ s.val) {h : V} (hhr : h ≠ N.root) (hPx : P x = h) (hPy : P y = h)
    (hoth : ∀ z ∈ q, z ≠ x → z ≠ y → ¬ N.graph.Reaches h (P z)) {k₁ k₂ : E} (hk₁ : N.graph.target k₁ = h)
    (hk₂ : N.graph.target k₂ = h) (hne : k₁ ≠ k₂) (hk : ∀ f, N.graph.target f = h → f = k₁ ∨ f = k₂)
    {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1)
    (h₁ : c ≤ cherryMass N θ ρ (placeInj q (movePair P x y (N.graph.source k₁))) s)
    (h₂ : c ≤ cherryMass N θ ρ (placeInj q (movePair P x y (N.graph.source k₂))) s) :
    c / 2 ≤ cherryMass N θ ρ (placeInj q P) s := by
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
  have hsame : ∀ z ∈ q, P z ∈ atOrBelow N h → z = x ∨ z = y := fun z hzq hzD => by
    by_contra hne'
    push Not at hne'
    exact hoth z hzq hne'.1 hne'.2 (mem_atOrBelow.1 hzD)
  have hPz : ∀ z, z = x ∨ z = y → P z = h := by
    rintro z (rfl | rfl)
    · exact hPx
    · exact hPy
  have hempty : ∀ u ∈ D₀, placeInj q P u = ∅ := by
    intro u hu
    refine eq_empty_of_forall_notMem fun A hA => ?_
    obtain ⟨z, hz, -⟩ := mem_image.1 hA
    obtain ⟨hzq, rfl⟩ := mem_filter.1 hz
    obtain ⟨hne', hr⟩ := (hmemD₀ _).1 hu
    exact hne' (hPz z (hsame z hzq (mem_atOrBelow.2 hr)))
  set F : Finset (Finset X) := ({x, y} : Finset X).image fun x => ({x} : Finset X) with hF
  have hinjh : placeInj q P h = F := by
    unfold placeInj
    rw [hF]
    congr 1
    ext z
    simp only [mem_filter, mem_insert, mem_singleton]
    constructor
    · rintro ⟨hzq, hz⟩
      exact hsame z hzq (hz ▸ mem_atOrBelow.2 .refl)
    · intro hz
      refine ⟨?_, hPz z hz⟩
      rcases hz with rfl | rfl
      · exact hxq
      · exact hyq
  rw [cherryMass_eq_meanOn_lift hN hθ.isNormalized hρ.1 hv (downClosed_atOrBelow h) (root_notMem_atOrBelow hN hhr) s,
    hDeq, meanOn_insert hDown₀ hhD₀ hch]
  refine le_meanOn hN hθ hρ hv hDown₀ hroot₀ fun bot top hz => ?_
  have htop : ∀ f, N.graph.target f ∈ D₀ → top f = ∅ := fun f hf =>
    top_eq_empty_of_inj_empty hN hDown₀ hv hempty hz hf
  have harr : arriving N (placeInj q P) top h = F := by
    rw [arriving_eq_biUnion (S := univ.filter fun f => N.graph.source f = h) (fun f => by simp), hinjh]
    refine union_eq_left.2 fun A hA => ?_
    obtain ⟨f, hf, hAf⟩ := mem_biUnion.1 hA
    rw [htop f (hch f (mem_filter.1 hf).2)] at hAf
    simp at hAf
  -- what is lifted, from a forest on one parent
  have hsrcD : ∀ {k : E}, N.graph.target k = h → N.graph.source k ∉ insert h D₀ := fun hkt => by
    rw [← hDeq, mem_atOrBelow]
    exact fun hc' => TOBQMC.Level1.not_reaches_source hN _ (hkt ▸ hc')
  have hliftAt : ∀ {k : E} (G : Finset (Finset X)) (T : E → Finset (Finset X)), N.graph.target k = h → T k = G →
      (∀ f, N.graph.target f = h → f ≠ k → T f = ∅) → ∀ w,
      liftSet N (insert h D₀) (placeInj q P) (ow (arcsInto N h) top T) w =
        if w ∈ insert h D₀ then ∅ else if w = N.graph.source k then placeInj q P w ∪ G else placeInj q P w := by
    intro k G T hkt hTk hTo w
    unfold liftSet
    by_cases hw : w ∈ insert h D₀
    · rw [ite_eq_left hw, ite_eq_left hw]
    · rw [ite_eq_right hw, ite_eq_right hw]
      have hunion : (univ.filter fun f => N.graph.source f = w ∧ N.graph.target f ∈ insert h D₀).biUnion
          (ow (arcsInto N h) top T) = if w = N.graph.source k then G else ∅ := by
        ext A
        simp only [mem_biUnion, mem_filter, mem_univ, true_and]
        constructor
        · rintro ⟨f, ⟨hfs, hft⟩, hA⟩
          by_cases hfh : N.graph.target f = h
          · rw [ow_of_mem (mem_arcsInto.2 hfh)] at hA
            by_cases hfk : f = k
            · subst hfk
              rw [ite_eq_left hfs.symm, ← hTk]
              exact hA
            · rw [hTo f hfh hfk] at hA
              simp at hA
          · have hft' : N.graph.target f ∈ D₀ := by
              rcases mem_insert.1 hft with h' | h'
              · exact absurd h' hfh
              · exact h'
            rw [ow_of_notMem (by rw [mem_arcsInto]; exact hfh), htop f hft'] at hA
            simp at hA
        · intro hA
          by_cases hwk : w = N.graph.source k
          · rw [ite_eq_left hwk] at hA
            refine ⟨k, ⟨hwk.symm, by rw [hkt]; exact mem_insert_self _ _⟩, ?_⟩
            rw [ow_of_mem (mem_arcsInto.2 hkt), hTk]
            exact hA
          · rw [ite_eq_right hwk] at hA
            simp at hA
      rw [hunion]
      split_ifs <;> simp
  -- both lineages apart on one parent
  have hApart : ∀ {k : E} (T : E → Finset (Finset X)), N.graph.target k = h → T k = F →
      (∀ f, N.graph.target f = h → f ≠ k → T f = ∅) →
      liftSet N (insert h D₀) (placeInj q P) (ow (arcsInto N h) top T) =
        placeInj q (movePair P x y (N.graph.source k)) := by
    intro k T hkt hTk hTo
    funext w
    rw [hliftAt F T hkt hTk hTo w]
    have hks := hsrcD hkt
    have hxyq : ∀ z, z = x ∨ z = y → z ∈ q := by
      rintro z (rfl | rfl)
      · exact hxq
      · exact hyq
    by_cases hw : w ∈ insert h D₀
    · rw [ite_eq_left hw]
      symm
      refine eq_empty_of_forall_notMem fun A hA => ?_
      obtain ⟨z, hz, -⟩ := mem_image.1 hA
      obtain ⟨hzq, hzw⟩ := mem_filter.1 hz
      by_cases hzxy : z = x ∨ z = y
      · have : movePair P x y (N.graph.source k) z = N.graph.source k := ite_eq_left hzxy
        rw [this] at hzw
        exact hks (hzw ▸ hw)
      · have : movePair P x y (N.graph.source k) z = P z := ite_eq_right hzxy
        rw [this] at hzw
        rw [← hDeq] at hw
        exact hzxy (hsame z hzq (hzw ▸ hw))
    · rw [ite_eq_right hw]
      ext A
      simp only [placeInj, mem_image, mem_filter]
      by_cases hwk : w = N.graph.source k
      · rw [ite_eq_left hwk]
        simp only [mem_union, mem_image, mem_filter]
        constructor
        · rintro (⟨z, ⟨hzq, hzw⟩, rfl⟩ | hA)
          · refine ⟨z, ⟨hzq, ?_⟩, rfl⟩
            have hzxy : ¬ (z = x ∨ z = y) := fun hc' => by
              rw [hPz z hc'] at hzw
              exact hw (hzw ▸ mem_insert_self _ _)
            have : movePair P x y (N.graph.source k) z = P z := ite_eq_right hzxy
            rw [this]
            exact hzw
          · rw [hF] at hA
            obtain ⟨z, hz, rfl⟩ := mem_image.1 hA
            have hz' : z = x ∨ z = y := by simpa using hz
            refine ⟨z, ⟨hxyq z hz', ?_⟩, rfl⟩
            have : movePair P x y (N.graph.source k) z = N.graph.source k := ite_eq_left hz'
            rw [this, hwk]
        · rintro ⟨z, ⟨hzq, hzw⟩, rfl⟩
          by_cases hzxy : z = x ∨ z = y
          · right
            rw [hF]
            exact mem_image.2 ⟨z, by simpa using hzxy, rfl⟩
          · left
            have : movePair P x y (N.graph.source k) z = P z := ite_eq_right hzxy
            rw [this] at hzw
            exact ⟨z, ⟨hzq, hzw⟩, rfl⟩
      · rw [ite_eq_right hwk]
        simp only [mem_image, mem_filter]
        constructor
        · rintro ⟨z, ⟨hzq, hzw⟩, rfl⟩
          have hzxy : ¬ (z = x ∨ z = y) := fun hc' => by
            rw [hPz z hc'] at hzw
            exact hw (hzw ▸ mem_insert_self _ _)
          have : movePair P x y (N.graph.source k) z = P z := ite_eq_right hzxy
          exact ⟨z, ⟨hzq, by rw [this]; exact hzw⟩, rfl⟩
        · rintro ⟨z, ⟨hzq, hzw⟩, rfl⟩
          by_cases hzxy : z = x ∨ z = y
          · have : movePair P x y (N.graph.source k) z = N.graph.source k := ite_eq_left hzxy
            rw [this] at hzw
            exact absurd hzw.symm hwk
          · have : movePair P x y (N.graph.source k) z = P z := ite_eq_right hzxy
            rw [this] at hzw
            exact ⟨z, ⟨hzq, hzw⟩, rfl⟩
  -- the cherry on one parent
  have hCherry : ∀ {k : E} (T : E → Finset (Finset X)), N.graph.target k = h → T k = insert {x, y} F →
      (∀ f, N.graph.target f = h → f ≠ k → T f = ∅) →
      cherryMass N θ ρ (liftSet N (insert h D₀) (placeInj q P) (ow (arcsInto N h) top T)) s = 1 := by
    intro k T hkt hTk hTo
    have hks := hsrcD hkt
    set P' := movePair P x y (N.graph.source k) with hP'
    have hP'x : P' x = N.graph.source k := ite_eq_left (Or.inl rfl)
    have hP'y : P' y = N.graph.source k := ite_eq_left (Or.inr rfl)
    have heq : liftSet N (insert h D₀) (placeInj q P) (ow (arcsInto N h) top T) =
        fun w => if w = N.graph.source k then insert ({x, y} : Finset X) (placeInj q P' (N.graph.source k))
          else placeInj q P' w := by
      have hbase := hApart (k := k) (Function.update T k F) hkt (Function.update_self _ _ _)
        (fun f hf hfk => by rw [Function.update_of_ne hfk]; exact hTo f hf hfk)
      funext w
      rw [hliftAt (insert {x, y} F) T hkt hTk hTo w]
      have hb := congrFun hbase w
      rw [hliftAt F _ hkt (Function.update_self _ _ _)
        (fun f hf hfk => by rw [Function.update_of_ne hfk]; exact hTo f hf hfk) w] at hb
      by_cases hw : w ∈ insert h D₀
      · have hwk : w ≠ N.graph.source k := fun he => hks (he ▸ hw)
        rw [ite_eq_left hw] at hb ⊢
        rw [ite_eq_right hwk]
        exact hb
      · rw [ite_eq_right hw] at hb ⊢
        by_cases hwk : w = N.graph.source k
        · rw [ite_eq_left hwk] at hb ⊢
          rw [ite_eq_left hwk, ← hwk, ← hb, union_insert]
        · rw [ite_eq_right hwk] at hb ⊢
          rw [ite_eq_right hwk]
          exact hb
    rw [heq]
    obtain ⟨r₁, r₂, -, ha⟩ := QuartetTests.QuartetTree.exists_alternatives s
    have hr₁ : r₁ ∈ s.alternatives := by rw [ha]; simp
    have hval := validInj_insert_pair (P := P') hxq hyq hxy hP'x hP'y
    refine (cherryMass_of_mem_val hN hθ hρ hval (v := N.graph.source k) (C := {x, y}) ?_ hC hr₁).2
    simp
  have hstep := stepOf_two_two (N := N) (θ := θ) (ρ := ρ) (v := h) (k₁ := k₁) (k₂ := k₂) hk₁ hk₂ hne hk hxy
    (fun t => (fun top' => cherryMass N θ ρ (liftSet N (insert h D₀) (placeInj q P) top') s) (ow (arcsInto N h) top t))
    (ow_dep (arcsInto N h) top fun top' => cherryMass N θ ρ (liftSet N (insert h D₀) (placeInj q P) top') s)
  unfold stepKernel
  rw [harr, hstep]
  simp only
  have hemp₁ : ∀ A : Finset (Finset X), ∀ f, N.graph.target f = h → f ≠ k₁ → pairFn k₁ A k₂ ∅ f = ∅ := by
    intro A f hf hfk
    rcases hk f hf with rfl | rfl
    · exact absurd rfl hfk
    · exact pairFn_right hne _ _
  have hemp₂ : ∀ A : Finset (Finset X), ∀ f, N.graph.target f = h → f ≠ k₂ → pairFn k₁ ∅ k₂ A f = ∅ := by
    intro A f hf hfk
    rcases hk f hf with rfl | rfl
    · exact pairFn_left _ _ _ _
    · exact absurd rfl hfk
  rw [hApart (k := k₁) _ hk₁ (pairFn_left _ _ _ _) (hemp₁ F), hCherry (k := k₁) _ hk₁ (pairFn_left _ _ _ _) (hemp₁ _),
    hApart (k := k₂) _ hk₂ (pairFn_right hne _ _) (hemp₂ F), hCherry (k := k₂) _ hk₂ (pairFn_right hne _ _) (hemp₂ _)]
  -- the masses of the mixed terms are nonnegative
  have hγ : θ.inheritance k₁ + θ.inheritance k₂ = 1 := inheritance_add_eq_one hθ.isNormalized hk₁ hk₂ hne hk
  have hdeg₁ : N.IsHybridArc k₁ := two_le_indegree_of_ne hN hne (hk₁.trans hk₂.symm)
  have hdeg₂ : N.IsHybridArc k₂ := two_le_indegree_of_ne hN hne.symm (hk₂.trans hk₁.symm)
  have hγ₁ : 0 ≤ θ.inheritance k₁ := (hθ.2.2.2.1 k₁ hdeg₁).le
  have hγ₂ : 0 ≤ θ.inheritance k₂ := (hθ.2.2.2.1 k₂ hdeg₂).le
  have hMix : ∀ {a b : X}, (a = x ∧ b = y ∨ a = y ∧ b = x) →
      0 ≤ cherryMass N θ ρ (liftSet N (insert h D₀) (placeInj q P)
        (ow (arcsInto N h) top (pairFn k₁ {{a}} k₂ {{b}}))) s := by
    intro a b hab
    have hax : a = x ∨ a = y := by tauto
    have hbx : b = x ∨ b = y := by tauto
    have haq : a ∈ q := by
      rcases hax with rfl | rfl
      · exact hxq
      · exact hyq
    have hbq : b ∈ q := by
      rcases hbx with rfl | rfl
      · exact hxq
      · exact hyq
    have hab' : a ≠ b := by
      rcases hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact hxy
      · exact hxy.symm
    have hoth' : ∀ z, z ≠ a → z ≠ b → z ≠ x ∧ z ≠ y := by
      intro z hza hzb
      rcases hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact ⟨hza, hzb⟩
      · exact ⟨hzb, hza⟩
    have heq : liftSet N (insert h D₀) (placeInj q P) (ow (arcsInto N h) top (pairFn k₁ {{a}} k₂ {{b}})) =
        placeInj q (moveTwo P a b (N.graph.source k₁) (N.graph.source k₂)) := by
      have hm₁ : moveTwo P a b (N.graph.source k₁) (N.graph.source k₂) a = N.graph.source k₁ := by simp [moveTwo]
      have hm₂ : moveTwo P a b (N.graph.source k₁) (N.graph.source k₂) b = N.graph.source k₂ := by
        simp [moveTwo, hab'.symm]
      have hm₃ : ∀ z, z ≠ a → z ≠ b → moveTwo P a b (N.graph.source k₁) (N.graph.source k₂) z = P z := by
        intro z h₁ h₂
        simp [moveTwo, h₁, h₂]
      funext w
      unfold liftSet
      by_cases hw : w ∈ insert h D₀
      · rw [ite_eq_left hw]
        symm
        refine eq_empty_of_forall_notMem fun A hA => ?_
        obtain ⟨z, hz, -⟩ := mem_image.1 hA
        obtain ⟨hzq, hzw⟩ := mem_filter.1 hz
        by_cases hza : z = a
        · rw [hza, hm₁] at hzw
          exact hsrcD hk₁ (hzw ▸ hw)
        by_cases hzb : z = b
        · rw [hzb, hm₂] at hzw
          exact hsrcD hk₂ (hzw ▸ hw)
        rw [hm₃ z hza hzb] at hzw
        rw [← hDeq] at hw
        obtain ⟨hzx, hzy⟩ := hoth' z hza hzb
        rcases hsame z hzq (hzw ▸ hw) with h' | h'
        · exact hzx h'
        · exact hzy h'
      · rw [ite_eq_right hw]
        ext A
        simp only [mem_union, mem_biUnion, mem_filter, mem_univ, true_and, placeInj, mem_image]
        constructor
        · rintro (⟨z, ⟨hzq, hzw⟩, rfl⟩ | ⟨f, ⟨hfs, hft⟩, hA⟩)
          · have hza : z ≠ a := fun he => by
              have : P z = h := hPz z (he ▸ hax)
              exact hw (by rw [← hzw, this]; exact mem_insert_self _ _)
            have hzb : z ≠ b := fun he => by
              have : P z = h := hPz z (he ▸ hbx)
              exact hw (by rw [← hzw, this]; exact mem_insert_self _ _)
            exact ⟨z, ⟨hzq, by rw [hm₃ z hza hzb]; exact hzw⟩, rfl⟩
          · by_cases hfh : N.graph.target f = h
            · rw [ow_of_mem (mem_arcsInto.2 hfh)] at hA
              rcases hk f hfh with rfl | rfl
              · rw [pairFn_left, mem_singleton] at hA
                exact ⟨a, ⟨haq, by rw [hm₁]; exact hfs⟩, hA.symm⟩
              · rw [pairFn_right hne, mem_singleton] at hA
                exact ⟨b, ⟨hbq, by rw [hm₂]; exact hfs⟩, hA.symm⟩
            · have hft' : N.graph.target f ∈ D₀ := by
                rcases mem_insert.1 hft with h' | h'
                · exact absurd h' hfh
                · exact h'
              rw [ow_of_notMem (by rw [mem_arcsInto]; exact hfh), htop f hft'] at hA
              simp at hA
        · rintro ⟨z, ⟨hzq, hzw⟩, rfl⟩
          by_cases hza : z = a
          · rw [hza, hm₁] at hzw
            refine Or.inr ⟨k₁, ⟨hzw, by rw [hk₁]; exact mem_insert_self _ _⟩, ?_⟩
            rw [ow_of_mem (mem_arcsInto.2 hk₁), pairFn_left, hza]
            exact mem_singleton_self _
          by_cases hzb : z = b
          · rw [hzb, hm₂] at hzw
            refine Or.inr ⟨k₂, ⟨hzw, by rw [hk₂]; exact mem_insert_self _ _⟩, ?_⟩
            rw [ow_of_mem (mem_arcsInto.2 hk₂), pairFn_right hne, hzb]
            exact mem_singleton_self _
          · rw [hm₃ z hza hzb] at hzw
            exact Or.inl ⟨z, ⟨hzq, hzw⟩, rfl⟩
    rw [heq]
    unfold cherryMass
    refine sum_nonneg fun H _ => ?_
    split_ifs
    · exact injDist_nonneg hN hθ hρ (validInj_placeInj q _) H
    · exact le_rfl
  have hm₁ := hMix (a := x) (b := y) (Or.inl ⟨rfl, rfl⟩)
  have hm₂ := hMix (a := y) (b := x) (Or.inr ⟨rfl, rfl⟩)
  have he₁ : 0 < Real.exp (-θ.length k₁) := Real.exp_pos _
  have he₂ : 0 < Real.exp (-θ.length k₂) := Real.exp_pos _
  have hl₁ : 0 ≤ θ.length k₁ := hθ.2.1 k₁ hdeg₁
  have hl₂ : 0 ≤ θ.length k₂ := hθ.2.1 k₂ hdeg₂
  have he₁' : Real.exp (-θ.length k₁) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
  have he₂' : Real.exp (-θ.length k₂) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
  set γ₁ := θ.inheritance k₁
  set γ₂ := θ.inheritance k₂
  set e₁ := Real.exp (-θ.length k₁)
  set e₂ := Real.exp (-θ.length k₂)
  set M₁ := cherryMass N θ ρ (placeInj q (movePair P x y (N.graph.source k₁))) s
  set M₂ := cherryMass N θ ρ (placeInj q (movePair P x y (N.graph.source k₂))) s
  set Ψ₁ := cherryMass N θ ρ (liftSet N (insert h D₀) (placeInj q P)
    (ow (arcsInto N h) top (pairFn k₁ {{x}} k₂ {{y}}))) s
  set Ψ₂ := cherryMass N θ ρ (liftSet N (insert h D₀) (placeInj q P)
    (ow (arcsInto N h) top (pairFn k₁ {{y}} k₂ {{x}}))) s
  obtain ⟨hρ₀, hρ₁⟩ := hρ
  have hbound₁ : c ≤ e₁ * M₁ + (1 - e₁) * 1 := by nlinarith
  have hbound₂ : c ≤ e₂ * M₂ + (1 - e₂) * 1 := by nlinarith
  have hw₁ : 0 ≤ γ₁ * ((1 - ρ) * γ₁ + ρ) := mul_nonneg hγ₁ (add_nonneg (mul_nonneg (sub_nonneg.2 hρ₁) hγ₁) hρ₀)
  have hw₂ : 0 ≤ γ₂ * ((1 - ρ) * γ₂ + ρ) := mul_nonneg hγ₂ (add_nonneg (mul_nonneg (sub_nonneg.2 hρ₁) hγ₂) hρ₀)
  have hw₃ : 0 ≤ (1 - ρ) * γ₁ * γ₂ := mul_nonneg (mul_nonneg (sub_nonneg.2 hρ₁) hγ₁) hγ₂
  have hw₄ : 0 ≤ (1 - ρ) * γ₂ * γ₁ := mul_nonneg (mul_nonneg (sub_nonneg.2 hρ₁) hγ₂) hγ₁
  have hsame₁ := mul_le_mul_of_nonneg_left hbound₁ hw₁
  have hsame₂ := mul_le_mul_of_nonneg_left hbound₂ hw₂
  have hmixed₁ := mul_nonneg hw₃ hm₁
  have hmixed₂ := mul_nonneg hw₄ hm₂
  -- both lineages take one parent with probability at least one half
  have hhalf : 1 / 2 ≤ γ₁ * ((1 - ρ) * γ₁ + ρ) + γ₂ * ((1 - ρ) * γ₂ + ρ) := by
    have hγ₂' : γ₂ = 1 - γ₁ := by linarith
    rw [hγ₂']
    nlinarith [sq_nonneg (γ₁ - 1 / 2), mul_nonneg (sub_nonneg.2 hρ₁) (sq_nonneg (γ₁ - 1 / 2))]
  have hcc := mul_le_mul_of_nonneg_right hhalf hc0
  linarith

/-! ### The bound -/

omit [Fintype V] [Fintype E] [DecidableEq X] [Fintype X] in
theorem movePair_movePair [DecidableEq X] (P : X → V) (x y : X) (u u' : V) :
    movePair (movePair P x y u) x y u' = movePair P x y u' := by
  funext z
  unfold movePair
  split_ifs <;> rfl

/-- **Two lineages of a cherry of `s` placed together on the blob of a reticulation with nothing below it**, the other
two being in different blocks: the masses are tree-like towards `s`. The top of the blob has three lineages at or below
it, by the blocks. -/
theorem isTL_of_colocated (hN : N.IsPhylogenetic) (hLevel : IsLevelOne N) (hθ : N.IsMetric θ) (hρ : 0 ≤ ρ ∧ ρ ≤ 1)
    {s : QuartetTree X} {a b : X} (hab : a ≠ b) (hA : ({a, b} : Finset X) ∈ s.val) {v h T : V} {k₁ k₂ : E}
    {pL pR : List E} (C : BlobCycle N v h T k₁ k₂ pL pR) (hh₂ : 2 ≤ N.graph.indegree h)
    (hbelow : ∀ z ∈ s.taxa, z ≠ a → z ≠ b → ¬ N.graph.Reaches h (N.leaf z))
    (hblock : ∀ x ∈ s.taxa, ∀ y ∈ s.taxa, x ≠ y → x ∉ ({a, b} : Finset X) → y ∉ ({a, b} : Finset X) →
      ¬ BlockWalk N v (N.leaf x) (N.leaf y)) {u : V} (hu : N.graph.blobSetoid v u)
    (hun : ¬ N.graph.Reaches h u) :
    IsTL N θ ρ (placeInj s.taxa (movePair N.leaf a b u)) s := by
  set P' := movePair N.leaf a b u with hP'
  have hPa : P' a = u := ite_eq_left (Or.inl rfl)
  have hPb : P' b = u := ite_eq_left (Or.inr rfl)
  have hPo : ∀ z, z ≠ a → z ≠ b → P' z = N.leaf z := fun z h₁ h₂ => ite_eq_right (by tauto)
  have haq : a ∈ s.taxa := s.subset_taxa hA (by simp)
  have hbq : b ∈ s.taxa := s.subset_taxa hA (by simp)
  have hco : ∀ k ∈ ({a, b} : Finset X), ∀ k' ∈ ({a, b} : Finset X), P' k = P' k' := by
    intro k hk k' hk'
    simp only [mem_insert, mem_singleton] at hk hk'
    rcases hk with rfl | rfl <;> rcases hk' with rfl | rfl <;> simp [hPa, hPb]
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
  refine isTL_hub_blob hN hLevel hθ hρ C.reticulation hh₂ (fun z hz => ?_) (u₀ := T) C.top ?_ ?_ ?_
  · by_cases hza : z = a
    · rw [hza, hPa]
      exact hun
    by_cases hzb : z = b
    · rw [hzb, hPb]
      exact hun
    rw [hPo z hza hzb]
    exact hbelow z hz hza hzb
  · have hTu := C.top_reaches u hu
    have hra : a ∈ reach N s.taxa P' T := mem_reach.2 ⟨haq, by rw [hPa]; exact hTu⟩
    have hrb : b ∈ reach N s.taxa P' T := mem_reach.2 ⟨hbq, by rw [hPb]; exact hTu⟩
    have hcase := reaches_top_of_not_blockWalk hN C.top_reaches (hblock c hcq d hdq hcd hcA hdA)
    have hsub : ∀ z, z ≠ a → z ≠ b → z ∈ s.taxa → N.graph.Reaches T (N.leaf z) →
        3 ≤ #(reach N s.taxa P' T) := by
      intro z hza hzb hzq hr
      have hrz : z ∈ reach N s.taxa P' T := mem_reach.2 ⟨hzq, by rw [hPo z hza hzb]; exact hr⟩
      have hsubset : ({a, b, z} : Finset X) ⊆ reach N s.taxa P' T := by
        intro w hw
        simp only [mem_insert, mem_singleton] at hw
        rcases hw with rfl | rfl | rfl
        · exact hra
        · exact hrb
        · exact hrz
      have hc3 : #({a, b, z} : Finset X) = 3 := card_eq_three.2 ⟨a, b, z, hab, hza.symm, hzb.symm, rfl⟩
      rw [← hc3]
      exact card_le_card hsubset
    rcases hcase with hr | hr
    · exact hsub c hca hcb hcq hr
    · exact hsub d hda hdb hdq hr
  · intro w w' hw' hr hwb
    have hsub : reach N s.taxa P' w ⊆ s.taxa \ {a, b} := by
      intro z hz
      obtain ⟨hzq, hzr⟩ := mem_reach.1 hz
      refine mem_sdiff.2 ⟨hzq, fun hzp => hwb ?_⟩
      have hzs : P' z = u := by
        simp only [mem_insert, mem_singleton] at hzp
        rcases hzp with rfl | rfl
        · exact hPa
        · exact hPb
      rw [hzs] at hzr
      exact sameBlob_of_reaches_of_reaches hN hw' hu hr hzr
    refine (card_le_card hsub).trans ?_
    rw [s.card_of_mem hQ]
  · exact fun w x' hx' y' hy' hne hrx hry hall => mem_val_of_colocated hA hco hx' hy' hne hrx hry hall

/-- **The bound `CF_AB|CD ≥ 1/6` of a `3₂`-cycle** with `a, b` below the reticulation `h`. -/
theorem one_sixth_le_nmscCF (hN : N.IsPhylogenetic) (hBin : N.IsBinary) (hLevel : IsLevelOne N)
    (hθ : N.IsMetric θ) (hρ : 0 ≤ ρ ∧ ρ ≤ 1) {s : QuartetTree X} {a b : X} (hab : a ≠ b)
    (hA : ({a, b} : Finset X) ∈ s.val) {h : V} (hh₂ : 2 ≤ N.graph.indegree h)
    (hba : N.graph.Reaches h (N.leaf a)) (hbb : N.graph.Reaches h (N.leaf b))
    (hbelow : ∀ z ∈ s.taxa, z ≠ a → z ≠ b → ¬ N.graph.Reaches h (N.leaf z))
    (hblock : ∀ x ∈ s.taxa, ∀ y ∈ s.taxa, x ≠ y → x ∉ ({a, b} : Finset X) → y ∉ ({a, b} : Finset X) →
      ¬ BlockWalk N h (N.leaf x) (N.leaf y)) :
    1 / 6 ≤ nmscCF N θ ρ s := by
  have hne : Nonempty X := ⟨a⟩
  obtain ⟨T, k₁, k₂, pL, pR, C⟩ := exists_blobCycle hN hBin hLevel (v := h) .refl hh₂
  obtain ⟨eh, hehs, hehu, hehb⟩ := exists_child_arc hN hBin hLevel (v := h) .refl hh₂
  have haq : a ∈ s.taxa := s.subset_taxa hA (by simp)
  have hbq : b ∈ s.taxa := s.subset_taxa hA (by simp)
  have hhr : h ≠ N.root := reticulation_ne_root hN hh₂
  have hleaf : ∀ z, N.leaf z ≠ h := by
    rintro z rfl
    rw [hN.leaf_indegree] at hh₂
    omega
  have hra : N.graph.Reaches (N.graph.target eh) (N.leaf a) := reaches_target_of_unique_out hehu hba (hleaf a)
  have hrb : N.graph.Reaches (N.graph.target eh) (N.leaf b) := reaches_target_of_unique_out hehu hbb (hleaf b)
  have hmove : ∀ {k : E}, N.graph.blobSetoid h (N.graph.source k) → ¬ N.graph.Reaches h (N.graph.source k) →
      1 / 3 ≤ cherryMass N θ ρ (placeInj s.taxa (movePair (movePair N.leaf a b h) a b (N.graph.source k))) s := by
    intro k hks hkn
    rw [movePair_movePair]
    exact third_le_cherryMass_of_isTL hN hθ hρ (isTL_of_colocated hN hLevel hθ hρ hab hA C hh₂ hbelow hblock hks hkn)
  have hP₁o : ∀ z, z ≠ a → z ≠ b → movePair N.leaf a b h z = N.leaf z := fun z h₁ h₂ => ite_eq_right (by tauto)
  have hat : 1 / 3 / 2 ≤ cherryMass N θ ρ (placeInj s.taxa (movePair N.leaf a b h)) s :=
    half_le_cherryMass_two_reticulation hN hθ hρ haq hbq hab hA hhr (ite_eq_left (Or.inl rfl)) (ite_eq_left (Or.inr rfl))
      (fun z hz hza hzb => by rw [hP₁o z hza hzb]; exact hbelow z hz hza hzb) C.target₁ C.target₂ C.ne C.arcs
      (by norm_num) (by norm_num) (hmove (C.source₁_sameBlob hN) (C.not_reaches_of_target₁ hN))
      (hmove (C.swap.source₁_sameBlob hN) (C.swap.not_reaches_of_target₁ hN))
  have hgoal : 1 / 3 / 2 ≤ cherryMass N θ ρ (placeInj s.taxa N.leaf) s := by
    refine le_cherryMass_of_pair_lift hN hθ hρ haq hbq hab hA (e := eh) hra hrb
      (not_avoidingReach_of_isBridge hN hehb hra) (not_avoidingReach_of_isBridge hN hehb hrb)
      (fun z hz hza hzb hr => hbelow z hz hza hzb (hehs ▸ (reaches_of_arc N eh).trans hr)) (by norm_num) ?_
    rw [hehs]
    exact hat
  rw [nmscCF_eq_cherryMass hN hθ hρ s, ← placeInj_leaf]
  linarith

/-! ### Part 2 -/

/-- **Proposition 9, part 2** (`nanuq:proposition9-2`), on a binary level-1 network, for the network multispecies
coalescent with any `0 ≤ ρ ≤ 1` and any valid parameters. If the set of four taxa `q` has a `3₂`-cycle, there is a quartet
tree `s` on `q`, the `N_c⁻` of the source, with the taxa below the reticulation as a cherry and `networkClass N q = .tree s`,
such that `CF_s ≥ 1/6`, the two alternatives of `s` have equal concordance factors, and any tree-like concordance factor
supports `s`: strictly, or at the centroid, which "supports all three quartets" (Definition 8).

The source's "may or may not be tree-like" is `ThreeTwo.exists_not_isT3Null_N₃` and `ThreeTwo.isT1Strict_N₃`.

The source prints no proof, and its bound is not used in the rest of the source. Departure from the paper, in the statement:
as for `proposition9`, it is on a set of four taxa of a whole network, the concordance factor being the marginal of the gene
tree on all the taxa. `Quartet.hasThreeTwoCycle_iff` is the bridge with the source's `3₂`-cycle, and `Quartet.proposition9_source` has all
three parts in the source's terms. -/
theorem proposition9_part2 (hN : N.IsPhylogenetic) (hBin : N.IsBinary) (hLevel : IsLevelOne N) (hθ : N.IsMetric θ)
    (hρ : 0 ≤ ρ ∧ ρ ≤ 1) {q : Finset X} (hq : #q = 4) (h3 : HasThreeTwoCycle N q) :
    ∃ s ∈ treesOn q, InducedCutSplit N s ∧ networkClass N q = .tree s ∧ 1 / 6 ≤ nmscCF N θ ρ s ∧
      (∀ r ∈ s.alternatives, ∀ r' ∈ s.alternatives, nmscCF N θ ρ r = nmscCF N θ ρ r') ∧
      (IsT3Null (nmscCF N θ ρ) q →
        (∀ r ∈ s.alternatives, nmscCF N θ ρ r < nmscCF N θ ρ s) ∨ ∀ r ∈ treesOn q, nmscCF N θ ρ r = 1 / 3) := by
  obtain ⟨h, hh₂, hcard, hblock⟩ := h3
  obtain ⟨a, b, hab, hB⟩ := card_eq_two.1 hcard
  have hne : Nonempty X := ⟨a⟩
  have hmemB : ∀ z, z ∈ ({a, b} : Finset X) ↔ z ∈ q ∧ N.graph.Reaches h (N.leaf z) := fun z => by
    rw [← hB, mem_filter]
  have hsub : ({a, b} : Finset X) ⊆ q := fun z hz => ((hmemB z).1 hz).1
  set s := quartetOfCherry q {a, b} hq hsub (card_pair hab) with hs
  have hsq : s.taxa = q := quartetOfCherry_taxa _ _ _ _ _
  have hA : ({a, b} : Finset X) ∈ s.val := by
    rw [hs, quartetOfCherry_val]
    simp
  have hba : N.graph.Reaches h (N.leaf a) := ((hmemB a).1 (by simp)).2
  have hbb : N.graph.Reaches h (N.leaf b) := ((hmemB b).1 (by simp)).2
  have hnotb : ∀ z ∈ s.taxa, z ∉ ({a, b} : Finset X) → ¬ N.graph.Reaches h (N.leaf z) := fun z hz hzn hr =>
    hzn ((hmemB z).2 ⟨hsq ▸ hz, hr⟩)
  obtain ⟨eh, hehs, hehu, hehb⟩ := exists_child_arc hN hBin hLevel (v := h) .refl hh₂
  have hleaf : ∀ z, N.leaf z ≠ h := by
    rintro z rfl
    rw [hN.leaf_indegree] at hh₂
    omega
  have hcut : InducedCutSplit N s := by
    refine ⟨{a, b}, hA, eh, ⟨a, by rw [hsq]; exact hsub (by simp), reaches_target_of_unique_out hehu hba (hleaf a)⟩,
      {u | N.graph.Reaches (N.graph.target eh) u}, fun f _ => isBridge_crosses_iff hN hehb f, fun x hx => ?_⟩
    simp only [Set.mem_ofPred_eq, mem_coe]
    constructor
    · intro hr
      exact (hmemB x).2 ⟨mem_coe.1 (by rw [hsq] at hx; exact hx), hehs ▸ (reaches_of_arc N eh).trans hr⟩
    · intro hx'
      exact reaches_target_of_unique_out hehu ((hmemB x).1 hx').2 (hleaf x)
  have halt := NMSC.cut_alternatives hN hθ hρ s hcut
  refine ⟨s, mem_treesOn.2 hsq, hcut, by rw [← hsq]; exact networkClass_eq_tree hN hcut, ?_, halt, fun hnull => ?_⟩
  · refine one_sixth_le_nmscCF hN hBin hLevel hθ hρ hab hA hh₂ hba hbb (fun z hz hza hzb => hnotb z hz (by simp [hza, hzb]))
      fun x hx y hy hxy hxA hyA => ?_
    exact hblock x (hsq ▸ hx) y (hsq ▸ hy) hxy (hnotb x hx hxA) (hnotb y hy hyA)
  · have hsum : ∑ r ∈ treesOn q, nmscCF N θ ρ r = 1 :=
      QuartetTests.sum_displayCF_treesOn (isDist_geneTreeDist hN hθ hρ) (TINNiK.displaysOne_nmsc hN) hq
    rcases cf_trichotomy hq hsum with huni | ⟨s', hs', hstrict⟩ | ⟨hno, -⟩
    · exact Or.inr huni
    · left
      have hst : s'.taxa = s.taxa := (mem_treesOn.1 hs').trans hsq.symm
      by_cases hss : s' = s
      · rw [← hss]
        exact hstrict.1
      · exfalso
        have h₁ : s' ∈ s.alternatives := QuartetTree.mem_alternatives.2 ⟨hst, hss⟩
        obtain ⟨r₁, r₂, hne₂, ha⟩ := QuartetTests.QuartetTree.exists_alternatives s
        have hmem₁ : r₁ ∈ s.alternatives := by rw [ha]; simp
        have hmem₂ : r₂ ∈ s.alternatives := by rw [ha]; simp
        have key : ∀ u ∈ s.alternatives, u ≠ s' → False := fun u hu hne' =>
          (hstrict.1 u (QuartetTree.mem_alternatives.2
            ⟨(QuartetTree.mem_alternatives.1 hu).1.trans hst.symm, hne'⟩)).ne (halt u hu s' h₁)
        by_cases h' : r₁ = s'
        · exact key r₂ hmem₂ fun he => hne₂ (h'.trans he.symm)
        · exact key r₁ hmem₁ h'
    · exact absurd hnull hno

end External.AllmanBanosRhodes2019
