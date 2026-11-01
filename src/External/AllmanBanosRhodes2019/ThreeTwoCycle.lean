module

public import ECToBlob.Remark52
public import External.AllmanBanosRhodes2019.Proposition9

/-!
# A `3₂`-cycle at the centroid: Theorem 36 of NANUQ as printed fails

The network `N₃` on the taxa `Fin 4` (`0, 1, 2, 3` for `a, b, c, d`) has vertices `r, u, v, h, w` and the taxa, and arcs
`r → u`, `r → v`, `u → c`, `v → d`, `u → h`, `v → h`, `h → w`, `w → a`, `w → b`. It is binary and level-1. Its induced
unrooted network is that of Figure 5 (L) of the source: with the root suppressed, a cycle `u, v, h` of three edges, with
two taxa below the reticulation.

## Main results

* `nmscCF_N₃`: its concordance factors from the definition of the NMSC, at any `ρ`, by the chain of
  `src/ECToBlob/Remark52.lean`, with two new steps: `stepOf_three` for three lineages on an arc, and `stepOf_cherry`.
* `nmscCF_N₃_abcd`, `nmscCF_N₃_acbd`, `nmscCF_N₃_adbc`: at `ρ = 0` they are the source's formula, `figure5CFab`,
  `figure5CFac`, with `x₃` for the edge `u v` of the unrooted network. The source takes the formula from its references.
* `isBinary_N₃`, `isLevelOne_N₃`, `hasThreeTwoCycle_N₃`, `inducedCutSplit_N₃`.
* `centroid_N₃`: at the parameters of `figure5_centroid`, all positive lengths, the concordance factors are `1/3`.
* `not_theorem36AsPrinted_N₃`: there the hypothesis of Theorem 36 as printed holds, and its conclusion fails at the level
  of the distance.
* `isT1Strict_N₃`, `theorem36_N₃`: at the source's sufficient condition, the arc below the reticulation of length at
  least `log (5/4)`, the corrected theorem applies.
-/

@[expose] public noncomputable section

open Phylogenetics Phylogenetics.RootedNetwork Phylogenetics.NMSC Finset
open ECToBlob.Remark52
open scoped Classical

namespace External.AllmanBanosRhodes2019.ThreeTwo

/-! ### A forest injected at a child of the root -/

section Generic

variable {V E X : Type*} [Fintype V] [Fintype E] [Fintype X] [DecidableEq X]
variable {N : RootedNetwork V E X} {θ : MetricData E} {ρ : ℝ}

variable (N) in
/-- The forest `F` injected at `u`, and `G` at the root. -/
def twoInj (u : V) (F G : Finset (Finset X)) : V → Finset (Finset X) :=
  fun x => if x = u then F else if x = N.root then G else ∅

omit [Fintype V] [Fintype E] [Fintype X] [DecidableEq X] in
theorem twoInj_left (u : V) (F G : Finset (Finset X)) : twoInj N u F G u = F := by
  simp [twoInj]

omit [Fintype V] [Fintype E] [Fintype X] [DecidableEq X] in
theorem twoInj_root {u : V} (hu : u ≠ N.root) (F G : Finset (Finset X)) : twoInj N u F G N.root = G := by
  simp [twoInj, hu.symm]

omit [Fintype V] [Fintype E] [Fintype X] [DecidableEq X] in
theorem twoInj_other {u x : V} (h₁ : x ≠ u) (h₂ : x ≠ N.root) (F G : Finset (Finset X)) :
    twoInj N u F G x = ∅ := by
  simp [twoInj, h₁, h₂]

omit [Fintype V] [Fintype E] [Fintype X] in
theorem validInj_twoInj {u : V} (hu : u ≠ N.root) {F G : Finset (Finset X)} (hF : IsGoodForest F)
    (hG : IsGoodForest G) (hdisj : Disjoint (lineages F) (lineages G)) : ValidInj (twoInj N u F G) := by
  refine ⟨fun x => ?_, fun x y hxy => ?_⟩
  · unfold twoInj
    split_ifs
    · exact hF
    · exact hG
    · exact isGoodForest_empty
  · have hval : ∀ x, x = u ∨ x = N.root ∨ twoInj N u F G x = ∅ := fun x => by
      by_cases h₁ : x = u
      · exact Or.inl h₁
      by_cases h₂ : x = N.root
      · exact Or.inr (Or.inl h₂)
      · exact Or.inr (Or.inr (twoInj_other h₁ h₂ F G))
    rcases hval x with rfl | rfl | hx
    · rcases hval y with rfl | rfl | hy
      · exact absurd rfl hxy
      · rw [twoInj_left, twoInj_root hu]
        exact hdisj
      · rw [hy]
        simp
    · rcases hval y with rfl | rfl | hy
      · rw [twoInj_left, twoInj_root hu]
        exact hdisj.symm
      · exact absurd rfl hxy
      · rw [hy]
        simp
    · rw [hx]
      simp

/-- **The chain at a child `u` of the root, by the process with forests injected at `u` and the root.** -/
theorem stepOf_eq_cherryMass (hN : N.IsPhylogenetic) (hθ : N.IsNormalized θ) (hρ : 0 ≤ ρ) {e : E} {u : V}
    (hs : N.graph.source e = N.root) (ht : N.graph.target e = u) (hu : ∀ f, N.graph.target f = u → f = e)
    {F G : Finset (Finset X)} (hF : IsGoodForest F) (hG : IsGoodForest G)
    (hdisj : Disjoint (lineages F) (lineages G)) (r : QuartetTree X) :
    stepOf N θ ρ u F (fun t => rootMass r (t e ∪ G)) = cherryMass N θ ρ (twoInj N u F G) r := by
  have hur : u ≠ N.root := fun h => target_ne_root hN e (ht.trans h)
  have hinj := validInj_twoInj (N := N) hur hF hG hdisj
  set D : Finset V := (univ.erase N.root).erase u with hD
  have hmemD : ∀ x, x ∈ D ↔ x ≠ u ∧ x ≠ N.root := fun x => by simp [hD]
  have hup : ∀ f, N.graph.source f = u → N.graph.target f ≠ u := fun f hf h =>
    not_reaches_target_source hN.acyclic f (by rw [hf, h]; exact .refl)
  have hdown : DownClosed N D := by
    intro f hf
    rw [hmemD] at hf ⊢
    refine ⟨fun h => ?_, target_ne_root hN f⟩
    have := hu f h
    rw [this, hs] at hf
    exact hf.2 rfl
  have hch : ∀ f, N.graph.source f = u → N.graph.target f ∈ D := fun f hf =>
    (hmemD _).2 ⟨hup f hf, target_ne_root hN f⟩
  rw [cherryMass_eq_sum_rootMass]
  have hmean := meanOn_of_forall_ne (N := N) (θ := θ) (ρ := ρ) hN (twoInj N u F G) (D := insert u D)
    (fun x => by
      rw [mem_insert, hmemD]
      by_cases h : x = u
      · simp [h, hur]
      · simp [h])
    (fun top => rootMass r (arriving N (twoInj N u F G) top N.root))
  rw [← hmean, meanOn_insert hdown (by simp [hmemD]) hch]
  refine (meanOn_eq_const hN hθ hρ hinj hdown (by simp [hmemD]) fun bot top hw => ?_).symm
  have hFr := frontier_of_prod_ne_zero hN hinj hdown hw
  have htop : ∀ f, N.graph.target f ∈ D → top f = ∅ := by
    intro f hf
    by_contra hne
    obtain ⟨A, hA⟩ := nonempty_iff_ne_empty.2 hne
    obtain ⟨x, hx⟩ := (hFr.good_top f hf).1.1 A hA
    obtain ⟨y, hy, hxy⟩ := hFr.below f hf x (mem_lineages.2 ⟨A, hA, hx⟩)
    obtain ⟨hf₁, hf₂⟩ := (hmemD _).1 hf
    by_cases hyu : y = u
    · subst hyu
      rcases Relation.ReflTransGen.cases_tail hy with h' | ⟨c, hc, g, hg₁, hg₂⟩
      · exact hf₁ h'.symm
      · have := hu g hg₂
        rw [this, hs] at hg₁
        exact hf₂ (TOBQMC.Level1.eq_root_of_reaches_root hN (hg₁ ▸ hc))
    · by_cases hyr : y = N.root
      · subst hyr
        exact hf₂ (TOBQMC.Level1.eq_root_of_reaches_root hN hy)
      · rw [twoInj_other hyu hyr] at hxy
        simp at hxy
  have harr : arriving N (twoInj N u F G) top u = F := by
    rw [arriving_eq_biUnion (S := univ.filter fun f => N.graph.source f = u) (fun f => by simp), twoInj_left]
    refine union_eq_left.2 ?_
    intro A hA
    obtain ⟨f, hf, hAf⟩ := mem_biUnion.1 hA
    rw [htop f (hch f (mem_filter.1 hf).2)] at hAf
    simp at hAf
  have hroot : ∀ t : E → Finset (Finset X),
      arriving N (twoInj N u F G) (ow (arcsInto N u) top t) N.root = t e ∪ G := by
    intro t
    rw [arriving_eq_biUnion (S := univ.filter fun f => N.graph.source f = N.root) (fun f => by simp), twoInj_root hur]
    have heS : e ∈ univ.filter fun f => N.graph.source f = N.root := by simp [hs]
    have hbi : (univ.filter fun f => N.graph.source f = N.root).biUnion (ow (arcsInto N u) top t) = t e := by
      ext A
      constructor
      · intro hA
        obtain ⟨f, hf, hAf⟩ := mem_biUnion.1 hA
        by_cases hfe : f = e
        · rw [hfe, ow_of_mem (mem_arcsInto.2 ht)] at hAf
          exact hAf
        · have hnot : f ∉ arcsInto N u := fun h => hfe (hu f (mem_arcsInto.1 h))
          rw [ow_of_notMem hnot] at hAf
          have hft : N.graph.target f ∈ D := (hmemD _).2 ⟨fun h => hnot (mem_arcsInto.2 h), target_ne_root hN f⟩
          rw [htop f hft] at hAf
          simp at hAf
      · intro hA
        refine mem_biUnion.2 ⟨e, heS, ?_⟩
        rw [ow_of_mem (mem_arcsInto.2 ht)]
        exact hA
    rw [hbi, union_comm]
  unfold stepKernel
  rw [harr]
  congr 1
  funext t
  exact congrArg (rootMass r) (hroot t)

/-- Three singleton lineages at a child of the root, with the fourth at the root: the three quartet trees are equally
likely. -/
theorem stepOf_three (hN : N.IsPhylogenetic) (hθ : N.IsMetric θ) (hρ : 0 ≤ ρ ∧ ρ ≤ 1) {e : E} {u : V}
    (hs : N.graph.source e = N.root) (ht : N.graph.target e = u) (hu : ∀ f, N.graph.target f = u → f = e)
    {Y : Finset X} (hY : #Y = 4) {x : X} (hx : x ∈ Y) {r : QuartetTree X} (hr : r ∈ treesOn Y) :
    stepOf N θ ρ u ((Y.erase x).image fun z => ({z} : Finset X)) (fun t => rootMass r (t e ∪ {{x}})) = 1 / 3 := by
  have hur : u ≠ N.root := fun h => target_ne_root hN e (ht.trans h)
  have hdisj : Disjoint (lineages ((Y.erase x).image fun z => ({z} : Finset X))) (lineages {{x}}) := by
    rw [lineages_image_singleton]
    have : lineages ({{x}} : Finset (Finset X)) = {x} := by simp [lineages]
    rw [this]
    simp
  have hsing : IsGoodForest ({{x}} : Finset (Finset X)) := by
    have := isGoodForest_singletons ({x} : Finset X)
    rwa [image_singleton] at this
  rw [stepOf_eq_cherryMass hN hθ.isNormalized hρ.1 hs ht hu (isGoodForest_singletons _) hsing hdisj]
  refine cherryMass_eq_third hN hθ hρ (validInj_twoInj hur (isGoodForest_singletons _) hsing hdisj) hY
    (fun z => ?_) hx (fun y hy z hz hya hza => ?_) hr
  · constructor
    · rintro ⟨w, hw⟩
      by_cases h₁ : w = u
      · rw [h₁, twoInj_left, lineages_image_singleton] at hw
        exact (mem_erase.1 hw).2
      by_cases h₂ : w = N.root
      · rw [h₂, twoInj_root hur] at hw
        have : z = x := by simpa [lineages] using hw
        rwa [this]
      · rw [twoInj_other h₁ h₂] at hw
        simp at hw
    · intro hz'
      by_cases hzx : z = x
      · refine ⟨N.root, ?_⟩
        rw [twoInj_root hur, hzx]
        simp [lineages]
      · refine ⟨u, ?_⟩
        rw [twoInj_left, lineages_image_singleton]
        exact mem_erase.2 ⟨hzx, hz'⟩
  · funext w
    unfold relabelInj twoInj
    split_ifs
    · exact relabelFamily_swap_singletons (mem_erase.2 ⟨hya, hy⟩) (mem_erase.2 ⟨hza, hz⟩)
    · refine relabelFamily_eq_self fun A hA => ?_
      rw [mem_singleton] at hA
      subst hA
      simp [Equiv.swap_apply_of_ne_of_ne (Ne.symm hya) (Ne.symm hza)]
    · exact relabelFamily_empty _

/-- A cherry at a child of the root decides the quartet trees. -/
theorem stepOf_cherry (hN : N.IsPhylogenetic) (hθ : N.IsMetric θ) (hρ : 0 ≤ ρ ∧ ρ ≤ 1) {e : E} {u : V}
    (hs : N.graph.source e = N.root) (ht : N.graph.target e = u) (hu : ∀ f, N.graph.target f = u → f = e)
    {F G : Finset (Finset X)} (hF : IsGoodForest F) (hG : IsGoodForest G)
    (hdisj : Disjoint (lineages F) (lineages G)) {C : Finset X} (hC : C ∈ F) (hC2 : #C = 2)
    {r : QuartetTree X} (hCr : C ⊆ r.taxa) :
    stepOf N θ ρ u F (fun t => rootMass r (t e ∪ G)) = if C ∈ r.val then 1 else 0 := by
  have hur : u ≠ N.root := fun h => target_ne_root hN e (ht.trans h)
  rw [stepOf_eq_cherryMass hN hθ.isNormalized hρ.1 hs ht hu hF hG hdisj]
  exact cherryMass_of_mem hN hθ hρ (validInj_twoInj hur hF hG hdisj) (v := u) (by rwa [twoInj_left]) hC2 hCr

end Generic

/-! ### The network -/

/-- The vertices of `N₃`. -/
inductive V₃ | r | u | v | h | w | a | b | c | d
  deriving DecidableEq

instance : Fintype V₃ := ⟨{.r, .u, .v, .h, .w, .a, .b, .c, .d}, fun x => by cases x <;> decide⟩

/-- The arcs of `N₃`: `ru`, `rv` leave the root, `uh`, `vh` enter the reticulation, and `c`, `d`, `a`, `b` enter the
leaves. -/
inductive E₃ | ru | rv | c | d | uh | vh | hw | a | b
  deriving DecidableEq

instance : Fintype E₃ := ⟨{.ru, .rv, .c, .d, .uh, .vh, .hw, .a, .b}, fun x => by cases x <;> decide⟩

/-- **The network**: a binary level-1 network whose induced unrooted network, with the root suppressed, has a
`3₂`-cycle. -/
def N₃ : RootedNetwork V₃ E₃ (Fin 4) where
  graph :=
    { source := fun
        | .ru => .r | .rv => .r | .c => .u | .d => .v | .uh => .u | .vh => .v | .hw => .h | .a => .w | .b => .w
      target := fun
        | .ru => .u | .rv => .v | .c => .c | .d => .d | .uh => .h | .vh => .h | .hw => .w | .a => .a | .b => .b }
  root := .r
  leaf := ![.a, .b, .c, .d]

theorem isPhylogenetic_N₃ : N₃.IsPhylogenetic := by
  refine isPhylogenetic_of_rank (fun | .r => 0 | .u => 1 | .v => 1 | .h => 2 | .w => 3 | _ => 4)
    (fun e => by cases e <;> decide) (fun e => by cases e <;> decide) ?_ ?_ (fun x => ?_)
    (fun x e => ?_) (fun y hy => ?_)
  · intro y hy
    cases y
    · exact absurd rfl hy
    · exact ⟨.ru, rfl⟩
    · exact ⟨.rv, rfl⟩
    · exact ⟨.uh, rfl⟩
    · exact ⟨.hw, rfl⟩
    · exact ⟨.a, rfl⟩
    · exact ⟨.b, rfl⟩
    · exact ⟨.c, rfl⟩
    · exact ⟨.d, rfl⟩
  · decide
  · fin_cases x
    · exact ⟨.a, rfl, fun f hf => by cases f <;> first | rfl | exact absurd hf (by decide)⟩
    · exact ⟨.b, rfl, fun f hf => by cases f <;> first | rfl | exact absurd hf (by decide)⟩
    · exact ⟨.c, rfl, fun f hf => by cases f <;> first | rfl | exact absurd hf (by decide)⟩
    · exact ⟨.d, rfl, fun f hf => by cases f <;> first | rfl | exact absurd hf (by decide)⟩
  · fin_cases x <;> cases e <;> decide
  · cases y
    · exact ⟨.ru, rfl⟩
    · exact ⟨.c, rfl⟩
    · exact ⟨.d, rfl⟩
    · exact ⟨.hw, rfl⟩
    · exact ⟨.a, rfl⟩
    · exact absurd rfl (hy 0)
    · exact absurd rfl (hy 1)
    · exact absurd rfl (hy 2)
    · exact absurd rfl (hy 3)

theorem target₃_u {f : E₃} : N₃.graph.target f = .u → f = .ru := by cases f <;> decide
theorem target₃_v {f : E₃} : N₃.graph.target f = .v → f = .rv := by cases f <;> decide
theorem target₃_h (f : E₃) : N₃.graph.target f = .h → f = .uh ∨ f = .vh := by cases f <;> decide
theorem target₃_w {f : E₃} : N₃.graph.target f = .w → f = .hw := by cases f <;> decide

/-! ### The chain -/

section Chain

variable {θ : MetricData E₃} {ρ : ℝ}

local notation "inj₃" => taxaInj N₃ (univ : Finset (Fin 4))

theorem arriving₃_root (top : E₃ → Finset (Finset (Fin 4))) :
    arriving N₃ inj₃ top N₃.root = top .ru ∪ top .rv := by
  rw [arriving_eq_biUnion (S := {.ru, .rv}) (fun e => by cases e <;> decide), taxaInj_eq_empty (by decide)]
  simp [biUnion_insert]

theorem arriving₃_u (top : E₃ → Finset (Finset (Fin 4))) : arriving N₃ inj₃ top .u = top .c ∪ top .uh := by
  rw [arriving_eq_biUnion (S := {.c, .uh}) (fun e => by cases e <;> decide), taxaInj_eq_empty (by decide)]
  simp [biUnion_insert]

theorem arriving₃_v (top : E₃ → Finset (Finset (Fin 4))) : arriving N₃ inj₃ top .v = top .d ∪ top .vh := by
  rw [arriving_eq_biUnion (S := {.d, .vh}) (fun e => by cases e <;> decide), taxaInj_eq_empty (by decide)]
  simp [biUnion_insert]

theorem arriving₃_h (top : E₃ → Finset (Finset (Fin 4))) : arriving N₃ inj₃ top .h = top .hw := by
  rw [arriving_eq_biUnion (S := {.hw}) (fun e => by cases e <;> decide), taxaInj_eq_empty (by decide)]
  simp

theorem arriving₃_w (top : E₃ → Finset (Finset (Fin 4))) : arriving N₃ inj₃ top .w = top .a ∪ top .b := by
  rw [arriving_eq_biUnion (S := {.a, .b}) (fun e => by cases e <;> decide), taxaInj_eq_empty (by decide)]
  simp [biUnion_insert]

/-- The forest at the root gives the mass of the quartet tree `r`. -/
def φ₃ (r : QuartetTree (Fin 4)) (top : E₃ → Finset (Finset (Fin 4))) : ℝ :=
  rootMass r (arriving N₃ inj₃ top N₃.root)

/-- The chain at `u`. -/
abbrev κu (θ : MetricData E₃) (ρ : ℝ) (r : QuartetTree (Fin 4)) := stepKernel N₃ θ ρ inj₃ .u (φ₃ r)

/-- The chain at `v`. -/
abbrev κv (θ : MetricData E₃) (ρ : ℝ) (r : QuartetTree (Fin 4)) := stepKernel N₃ θ ρ inj₃ .v (κu θ ρ r)

/-- The chain at the reticulation. -/
abbrev κh (θ : MetricData E₃) (ρ : ℝ) (r : QuartetTree (Fin 4)) := stepKernel N₃ θ ρ inj₃ .h (κv θ ρ r)

/-- The chain at `w`. -/
abbrev κw (θ : MetricData E₃) (ρ : ℝ) (r : QuartetTree (Fin 4)) := stepKernel N₃ θ ρ inj₃ .w (κh θ ρ r)

theorem ru_mem : E₃.ru ∈ arcsInto N₃ V₃.u := mem_arcsInto.2 rfl
theorem rv_mem : E₃.rv ∈ arcsInto N₃ V₃.v := mem_arcsInto.2 rfl
theorem uh_mem : E₃.uh ∈ arcsInto N₃ V₃.h := mem_arcsInto.2 rfl
theorem vh_mem : E₃.vh ∈ arcsInto N₃ V₃.h := mem_arcsInto.2 rfl
theorem hw_mem : E₃.hw ∈ arcsInto N₃ V₃.w := mem_arcsInto.2 rfl

/-- The chain at `u` as a step from the forest arriving there. -/
theorem κu_eq (r : QuartetTree (Fin 4)) (top : E₃ → Finset (Finset (Fin 4))) :
    κu θ ρ r top = stepOf N₃ θ ρ .u (top .c ∪ top .uh) fun t => rootMass r (t .ru ∪ top .rv) := by
  unfold κu stepKernel
  rw [arriving₃_u]
  congr 1
  funext t
  unfold φ₃
  rw [arriving₃_root, ow_of_mem ru_mem, ow_of_notMem (f := E₃.rv) (by rw [mem_arcsInto]; decide)]

/-- The chain at `u`, from a forest with at most one root. -/
theorem κu_det (hθ : N₃.IsMetric θ) (hρ : 0 ≤ ρ) (r : QuartetTree (Fin 4)) (top : E₃ → Finset (Finset (Fin 4)))
    {F : Finset (Finset (Fin 4))} (h : top .c ∪ top .uh = F) (hF : IsForest F) (hr : #(roots F) ≤ 1) :
    κu θ ρ r top = rootMass r (F ∪ top .rv) := by
  rw [κu_eq, h]
  exact stepOf_unique_det (N := N₃) (θ := θ) (e := E₃.ru) hρ rfl (fun f => target₃_u)
    (hθ.2.2.1 E₃.ru (isTreeArc_of_unique fun f => target₃_u)) hF hr
    (fun t => rootMass r (t .ru ∪ top .rv)) fun t t' htt => by rw [htt _ ru_mem]

/-- The chain at `u`, from two singleton lineages. -/
theorem κu_two (hθ : N₃.IsMetric θ) (hρ : 0 ≤ ρ) (r : QuartetTree (Fin 4)) (top : E₃ → Finset (Finset (Fin 4)))
    {P : Finset (Fin 4)} (hP : #P = 2) (h : top .c ∪ top .uh = P.image fun x => ({x} : Finset (Fin 4))) :
    κu θ ρ r top = Real.exp (-θ.length .ru) * rootMass r ((P.image fun x => ({x} : Finset (Fin 4))) ∪ top .rv) +
      (1 - Real.exp (-θ.length .ru)) *
        rootMass r (insert P (P.image fun x => ({x} : Finset (Fin 4))) ∪ top .rv) := by
  rw [κu_eq, h]
  exact stepOf_unique_two (N := N₃) (θ := θ) (e := E₃.ru) hρ rfl (fun f => target₃_u)
    (hθ.2.2.1 E₃.ru (isTreeArc_of_unique fun f => target₃_u)) hP
    (fun t => rootMass r (t .ru ∪ top .rv)) fun t t' htt => by rw [htt _ ru_mem]

/-- The chain at `v` as a step from the forest arriving there. -/
theorem κv_eq (r : QuartetTree (Fin 4)) (top : E₃ → Finset (Finset (Fin 4))) :
    κv θ ρ r top = stepOf N₃ θ ρ .v (top .d ∪ top .vh) fun t => κu θ ρ r (ow (arcsInto N₃ .v) top t) := by
  unfold κv stepKernel
  rw [arriving₃_v]

/-- The forests at the arcs not entering `v` are kept. -/
theorem ow_v_c (top t : E₃ → Finset (Finset (Fin 4))) : ow (arcsInto N₃ .v) top t .c = top .c :=
  ow_of_notMem (f := E₃.c) (by rw [mem_arcsInto]; decide) _ _

theorem ow_v_uh (top t : E₃ → Finset (Finset (Fin 4))) : ow (arcsInto N₃ .v) top t .uh = top .uh :=
  ow_of_notMem (f := E₃.uh) (by rw [mem_arcsInto]; decide) _ _

theorem ow_v_rv (top t : E₃ → Finset (Finset (Fin 4))) : ow (arcsInto N₃ .v) top t .rv = t .rv :=
  ow_of_mem rv_mem _ _

/-- The chain at `v`, from a forest with at most one root. -/
theorem κv_det (hθ : N₃.IsMetric θ) (hρ : 0 ≤ ρ) (r : QuartetTree (Fin 4)) (top : E₃ → Finset (Finset (Fin 4)))
    {F : Finset (Finset (Fin 4))} (h : top .d ∪ top .vh = F) (hF : IsForest F) (hr : #(roots F) ≤ 1) :
    κv θ ρ r top = κu θ ρ r (ow (arcsInto N₃ .v) top fun _ => F) := by
  rw [κv_eq, h]
  exact stepOf_unique_det (N := N₃) (θ := θ) (e := E₃.rv) hρ rfl (fun f => target₃_v)
    (hθ.2.2.1 E₃.rv (isTreeArc_of_unique fun f => target₃_v)) hF hr
    (fun t => κu θ ρ r (ow (arcsInto N₃ .v) top t)) (ow_dep (arcsInto N₃ .v) top (κu θ ρ r))

/-- The chain at `v`, from two singleton lineages. -/
theorem κv_two (hθ : N₃.IsMetric θ) (hρ : 0 ≤ ρ) (r : QuartetTree (Fin 4)) (top : E₃ → Finset (Finset (Fin 4)))
    {P : Finset (Fin 4)} (hP : #P = 2) (h : top .d ∪ top .vh = P.image fun x => ({x} : Finset (Fin 4))) :
    κv θ ρ r top = Real.exp (-θ.length .rv) *
        κu θ ρ r (ow (arcsInto N₃ .v) top fun _ => P.image fun x => ({x} : Finset (Fin 4))) +
      (1 - Real.exp (-θ.length .rv)) *
        κu θ ρ r (ow (arcsInto N₃ .v) top fun _ => insert P (P.image fun x => ({x} : Finset (Fin 4)))) := by
  rw [κv_eq, h]
  exact stepOf_unique_two (N := N₃) (θ := θ) (e := E₃.rv) hρ rfl (fun f => target₃_v)
    (hθ.2.2.1 E₃.rv (isTreeArc_of_unique fun f => target₃_v)) hP
    (fun t => κu θ ρ r (ow (arcsInto N₃ .v) top t)) (ow_dep (arcsInto N₃ .v) top (κu θ ρ r))

theorem isGoodForest_d : IsGoodForest ({{3}} : Finset (Finset (Fin 4))) := by
  unfold IsGoodForest IsForest IsBinaryForest
  decide

theorem isGoodForest_c : IsGoodForest ({{2}} : Finset (Finset (Fin 4))) := by
  unfold IsGoodForest IsForest IsBinaryForest
  decide

/-- Both lineages `a`, `b` at `u`, uncoalesced: all three trees are equally likely. -/
theorem κv_both_u (hθ : N₃.IsMetric θ) (hρ : 0 ≤ ρ ∧ ρ ≤ 1) (r : QuartetTree (Fin 4))
    (top : E₃ → Finset (Finset (Fin 4))) (hc : top .c = {{2}}) (hd : top .d = {{3}}) (h₁ : top .uh = Fab)
    (h₂ : top .vh = ∅) : κv θ ρ r top = 1 / 3 := by
  rw [κv_det hθ hρ.1 r top (F := {{3}}) (by rw [hd, h₂]; decide) (isForest_singleton_singleton 3)
    (by rw [roots_singleton_singleton]; simp), κu_eq, ow_v_c, ow_v_uh, ow_v_rv, hc, h₁]
  have e : ({{2}} : Finset (Finset (Fin 4))) ∪ Fab =
      (((univ : Finset (Fin 4)).erase 3).image fun z => ({z} : Finset (Fin 4))) := by decide
  rw [e]
  exact stepOf_three isPhylogenetic_N₃ hθ hρ (e := E₃.ru) rfl rfl (fun f => target₃_u) (Y := univ) rfl (mem_univ 3)
    (by rw [mem_treesOn, taxa_eq_univ])

/-- Both lineages `a`, `b` at `v`, uncoalesced. -/
theorem κv_both_v (hθ : N₃.IsMetric θ) (hρ : 0 ≤ ρ ∧ ρ ≤ 1) (r : QuartetTree (Fin 4))
    (top : E₃ → Finset (Finset (Fin 4))) (hc : top .c = {{2}}) (hd : top .d = {{3}}) (h₁ : top .uh = ∅)
    (h₂ : top .vh = Fab) : κv θ ρ r top = 1 / 3 := by
  rw [κv_eq, hd, h₂]
  have hu : ∀ t : E₃ → Finset (Finset (Fin 4)), κu θ ρ r (ow (arcsInto N₃ .v) top t) = rootMass r (t .rv ∪ {{2}}) := by
    intro t
    rw [κu_det hθ hρ.1 r _ (F := {{2}}) (by rw [ow_v_c, ow_v_uh, hc, h₁]; decide)
      (isForest_singleton_singleton 2) (by rw [roots_singleton_singleton]; simp), ow_v_rv, union_comm]
  simp only [hu]
  have e : ({{3}} : Finset (Finset (Fin 4))) ∪ Fab =
      (((univ : Finset (Fin 4)).erase 2).image fun z => ({z} : Finset (Fin 4))) := by decide
  rw [e]
  exact stepOf_three isPhylogenetic_N₃ hθ hρ (e := E₃.rv) rfl rfl (fun f => target₃_v) (Y := univ) rfl (mem_univ 2)
    (by rw [mem_treesOn, taxa_eq_univ])

/-- The chain at `u` when it has only the lineage of `c`, from the top of `rv`. -/
private theorem κu_after_v (hθ : N₃.IsMetric θ) (hρ : 0 ≤ ρ) (r : QuartetTree (Fin 4))
    (top : E₃ → Finset (Finset (Fin 4))) (hc : top .c = {{2}}) (h₁ : top .uh = ∅) (t : E₃ → Finset (Finset (Fin 4))) :
    κu θ ρ r (ow (arcsInto N₃ .v) top t) = rootMass r (t .rv ∪ {{2}}) := by
  rw [κu_det hθ hρ r _ (F := {{2}}) (by rw [ow_v_c, ow_v_uh, hc, h₁]; decide)
    (isForest_singleton_singleton 2) (by rw [roots_singleton_singleton]; simp), ow_v_rv, union_comm]

/-- `a`, `b` coalesced, at `u`. -/
theorem κv_cherry_u (hθ : N₃.IsMetric θ) (hρ : 0 ≤ ρ ∧ ρ ≤ 1) (r : QuartetTree (Fin 4))
    (top : E₃ → Finset (Finset (Fin 4))) (hc : top .c = {{2}}) (hd : top .d = {{3}}) (h₁ : top .uh = Cab)
    (h₂ : top .vh = ∅) : κv θ ρ r top = if ({0, 1} : Finset (Fin 4)) ∈ r.val then 1 else 0 := by
  rw [κv_det hθ hρ.1 r top (F := {{3}}) (by rw [hd, h₂]; decide) (isForest_singleton_singleton 3)
    (by rw [roots_singleton_singleton]; simp), κu_eq, ow_v_c, ow_v_uh, ow_v_rv, hc, h₁]
  exact stepOf_cherry isPhylogenetic_N₃ hθ hρ (e := E₃.ru) rfl rfl (fun f => target₃_u)
    (by unfold IsGoodForest IsForest IsBinaryForest; decide) isGoodForest_d (by decide) (by decide) (by decide)
    (by rw [taxa_eq_univ]; exact subset_univ _)

/-- `a`, `b` coalesced, at `v`. -/
theorem κv_cherry_v (hθ : N₃.IsMetric θ) (hρ : 0 ≤ ρ ∧ ρ ≤ 1) (r : QuartetTree (Fin 4))
    (top : E₃ → Finset (Finset (Fin 4))) (hc : top .c = {{2}}) (hd : top .d = {{3}}) (h₁ : top .uh = ∅)
    (h₂ : top .vh = Cab) : κv θ ρ r top = if ({0, 1} : Finset (Fin 4)) ∈ r.val then 1 else 0 := by
  rw [κv_eq, hd, h₂]
  simp only [κu_after_v hθ hρ.1 r top hc h₁]
  exact stepOf_cherry isPhylogenetic_N₃ hθ hρ (e := E₃.rv) rfl rfl (fun f => target₃_v)
    (by unfold IsGoodForest IsForest IsBinaryForest; decide) isGoodForest_c (by decide) (by decide) (by decide)
    (by rw [taxa_eq_univ]; exact subset_univ _)

theorem mem_val_compl (r : QuartetTree (Fin 4)) {B C : Finset (Fin 4)} (h : univ \ B = C) (hB : B ∈ r.val) :
    C ∈ r.val := by
  have := r.sdiff_mem hB
  rwa [taxa_eq_univ, h] at this

/-- The product of the exponentials of the two arcs at the root: the length of the edge `u v` of the unrooted network.
-/
def x₃ (θ : MetricData E₃) : ℝ := Real.exp (-θ.length .ru) * Real.exp (-θ.length .rv)

/-- The forests in the case of a split, and the masses at the root, for cherries `C`, `C'` in the two parts. -/
private theorem split_value (hθ : N₃.IsMetric θ) (hρ : 0 ≤ ρ ∧ ρ ≤ 1) (r : QuartetTree (Fin 4))
    {C C' : Finset (Fin 4)} (hCC : univ \ C = C') (hC2 : #C = 2) (hC'2 : #C' = 2)
    (hS : (C.image fun x => ({x} : Finset (Fin 4))) ∪ (C'.image fun x => ({x} : Finset (Fin 4))) = Fall)
    (hg₁ : IsGoodForest (insert C (C.image (fun x => ({x} : Finset (Fin 4)))) ∪ (C'.image fun x => ({x} : Finset (Fin 4)))))
    (hg₂ : IsGoodForest ((C.image fun x => ({x} : Finset (Fin 4))) ∪ insert C' (C'.image fun x => ({x} : Finset (Fin 4)))))
    (hg₃ : IsGoodForest (insert C (C.image (fun x => ({x} : Finset (Fin 4)))) ∪ insert C' (C'.image fun x => ({x} : Finset (Fin 4)))))
    (xu xv : ℝ) :
    xv * (xu * rootMass r ((C.image fun x => ({x} : Finset (Fin 4))) ∪ (C'.image fun x => ({x} : Finset (Fin 4)))) +
        (1 - xu) * rootMass r (insert C (C.image fun x => ({x} : Finset (Fin 4))) ∪ (C'.image fun x => ({x} : Finset (Fin 4))))) +
      (1 - xv) * (xu * rootMass r ((C.image fun x => ({x} : Finset (Fin 4))) ∪ insert C' (C'.image fun x => ({x} : Finset (Fin 4)))) +
        (1 - xu) * rootMass r (insert C (C.image fun x => ({x} : Finset (Fin 4))) ∪ insert C' (C'.image fun x => ({x} : Finset (Fin 4))))) =
      xu * xv * (1 / 3) + (1 - xu * xv) * if C ∈ r.val then 1 else 0 := by
  have hN := isPhylogenetic_N₃
  have htaxa : ∀ D : Finset (Fin 4), D ⊆ r.taxa := fun D => by
    rw [taxa_eq_univ]
    exact subset_univ _
  have hiff : C' ∈ r.val ↔ C ∈ r.val := by
    refine ⟨mem_val_compl r ?_, mem_val_compl r hCC⟩
    rw [← hCC, sdiff_sdiff_right_self, inf_eq_inter, univ_inter]
  rw [hS, rootMass_all hN hθ hρ,
    rootMass_of_mem hN hθ hρ hg₁ (C := C) (mem_union_left _ (mem_insert_self _ _)) hC2 (htaxa _),
    rootMass_of_mem hN hθ hρ hg₂ (C := C') (mem_union_right _ (mem_insert_self _ _)) hC'2 (htaxa _),
    rootMass_of_mem hN hθ hρ hg₃ (C := C) (mem_union_left _ (mem_insert_self _ _)) hC2 (htaxa _)]
  simp only [hiff]
  split_ifs <;> ring

/-- `a` at `u`, `b` at `v`: they meet `c` and `d`. -/
theorem κv_split₁ (hθ : N₃.IsMetric θ) (hρ : 0 ≤ ρ ∧ ρ ≤ 1) (r : QuartetTree (Fin 4))
    (top : E₃ → Finset (Finset (Fin 4))) (hc : top .c = {{2}}) (hd : top .d = {{3}}) (h₁ : top .uh = {{0}})
    (h₂ : top .vh = {{1}}) :
    κv θ ρ r top = x₃ θ * (1 / 3) + (1 - x₃ θ) * if ({0, 2} : Finset (Fin 4)) ∈ r.val then 1 else 0 := by
  have hu : ∀ F : Finset (Finset (Fin 4)), κu θ ρ r (ow (arcsInto N₃ .v) top fun _ => F) =
      Real.exp (-θ.length .ru) * rootMass r ((({0, 2} : Finset (Fin 4)).image fun x => ({x} : Finset (Fin 4))) ∪ F) +
        (1 - Real.exp (-θ.length .ru)) *
          rootMass r (insert ({0, 2} : Finset (Fin 4)) (({0, 2} : Finset (Fin 4)).image fun x => ({x} : Finset (Fin 4))) ∪ F) := by
    intro F
    rw [κu_two hθ hρ.1 r _ (P := {0, 2}) (by decide) (by rw [ow_v_c, ow_v_uh, hc, h₁]; decide), ow_v_rv]
  rw [κv_two hθ hρ.1 r top (P := {1, 3}) (by decide) (by rw [hd, h₂]; decide), hu, hu]
  have := split_value hθ hρ r (C := {0, 2}) (C' := {1, 3}) (by decide) (by decide) (by decide) (by decide)
    (by unfold IsGoodForest IsForest IsBinaryForest; decide)
    (by unfold IsGoodForest IsForest IsBinaryForest; decide)
    (by unfold IsGoodForest IsForest IsBinaryForest; decide)
    (Real.exp (-θ.length .ru)) (Real.exp (-θ.length .rv))
  unfold x₃
  rw [← this]

/-- `b` at `u`, `a` at `v`. -/
theorem κv_split₂ (hθ : N₃.IsMetric θ) (hρ : 0 ≤ ρ ∧ ρ ≤ 1) (r : QuartetTree (Fin 4))
    (top : E₃ → Finset (Finset (Fin 4))) (hc : top .c = {{2}}) (hd : top .d = {{3}}) (h₁ : top .uh = {{1}})
    (h₂ : top .vh = {{0}}) :
    κv θ ρ r top = x₃ θ * (1 / 3) + (1 - x₃ θ) * if ({0, 3} : Finset (Fin 4)) ∈ r.val then 1 else 0 := by
  have hu : ∀ F : Finset (Finset (Fin 4)), κu θ ρ r (ow (arcsInto N₃ .v) top fun _ => F) =
      Real.exp (-θ.length .ru) * rootMass r (({1, 2} : Finset (Fin 4)).image (fun x => ({x} : Finset (Fin 4))) ∪ F) +
        (1 - Real.exp (-θ.length .ru)) *
          rootMass r (insert ({1, 2} : Finset (Fin 4)) (({1, 2} : Finset (Fin 4)).image fun x => ({x} : Finset (Fin 4))) ∪ F) := by
    intro F
    rw [κu_two hθ hρ.1 r _ (P := {1, 2}) (by decide) (by rw [ow_v_c, ow_v_uh, hc, h₁]; decide), ow_v_rv]
  rw [κv_two hθ hρ.1 r top (P := {0, 3}) (by decide) (by rw [hd, h₂]; decide), hu, hu]
  have := split_value hθ hρ r (C := {1, 2}) (C' := {0, 3}) (by decide) (by decide) (by decide) (by decide)
    (by unfold IsGoodForest IsForest IsBinaryForest; decide)
    (by unfold IsGoodForest IsForest IsBinaryForest; decide)
    (by unfold IsGoodForest IsForest IsBinaryForest; decide)
    (Real.exp (-θ.length .ru)) (Real.exp (-θ.length .rv))
  have hiff : ({1, 2} : Finset (Fin 4)) ∈ r.val ↔ ({0, 3} : Finset (Fin 4)) ∈ r.val :=
    ⟨mem_val_compl r (by decide), mem_val_compl r (by decide)⟩
  simp only [hiff] at this
  unfold x₃
  rw [← this]

/-! ### The reticulation -/

theorem ow_h_c (top t : E₃ → Finset (Finset (Fin 4))) : ow (arcsInto N₃ .h) top t .c = top .c :=
  ow_of_notMem (f := E₃.c) (by rw [mem_arcsInto]; decide) _ _

theorem ow_h_d (top t : E₃ → Finset (Finset (Fin 4))) : ow (arcsInto N₃ .h) top t .d = top .d :=
  ow_of_notMem (f := E₃.d) (by rw [mem_arcsInto]; decide) _ _

theorem ow_h_uh (top : E₃ → Finset (Finset (Fin 4))) (A B : Finset (Finset (Fin 4))) :
    ow (arcsInto N₃ .h) top (pairFn .uh A .vh B) .uh = A := by
  rw [ow_of_mem uh_mem, pairFn_left]

theorem ow_h_vh (top : E₃ → Finset (Finset (Fin 4))) (A B : Finset (Finset (Fin 4))) :
    ow (arcsInto N₃ .h) top (pairFn .uh A .vh B) .vh = B := by
  rw [ow_of_mem vh_mem, pairFn_right (by decide)]

/-- The cherry `a b` reaches the reticulation: it goes one way as one lineage, and decides the trees. -/
theorem κh_cherry (hθ : N₃.IsMetric θ) (hρ : 0 ≤ ρ ∧ ρ ≤ 1) (r : QuartetTree (Fin 4))
    (top : E₃ → Finset (Finset (Fin 4))) (hc : top .c = {{2}}) (hd : top .d = {{3}}) (h : top .hw = Cab) :
    κh θ ρ r top = if ({0, 1} : Finset (Fin 4)) ∈ r.val then 1 else 0 := by
  have hs : θ.inheritance .uh + θ.inheritance .vh = 1 :=
    inheritance_add_eq_one hθ.isNormalized (k₁ := E₃.uh) (k₂ := E₃.vh) (v := V₃.h) rfl rfl (by decide) target₃_h
  have hstep := stepOf_two_one (N := N₃) (θ := θ) (ρ := ρ) (v := V₃.h) (k₁ := E₃.uh) (k₂ := E₃.vh) rfl rfl
    (by decide) target₃_h (F := Cab) (A := {0, 1}) (by unfold IsForest; decide) (by decide)
    (fun t => κv θ ρ r (ow (arcsInto N₃ .h) top t)) (ow_dep (arcsInto N₃ .h) top (κv θ ρ r))
  unfold κh stepKernel
  rw [arriving₃_h, h, hstep,
    κv_cherry_u hθ hρ r _ (by rw [ow_h_c, hc]) (by rw [ow_h_d, hd]) (ow_h_uh _ _ _) (ow_h_vh _ _ _),
    κv_cherry_v hθ hρ r _ (by rw [ow_h_c, hc]) (by rw [ow_h_d, hd]) (ow_h_uh _ _ _) (ow_h_vh _ _ _)]
  split_ifs <;> linarith

/-- The two lineages `a`, `b` reach the reticulation apart. -/
theorem κh_two (hθ : N₃.IsMetric θ) (hρ : 0 ≤ ρ ∧ ρ ≤ 1) (r : QuartetTree (Fin 4))
    (top : E₃ → Finset (Finset (Fin 4))) (hc : top .c = {{2}}) (hd : top .d = {{3}}) (h : top .hw = Fab) :
    κh θ ρ r top =
      θ.inheritance .uh * ((1 - ρ) * θ.inheritance .uh + ρ) *
          (Real.exp (-θ.length .uh) * (1 / 3) + (1 - Real.exp (-θ.length .uh)) *
            if ({0, 1} : Finset (Fin 4)) ∈ r.val then 1 else 0) +
        (1 - ρ) * θ.inheritance .uh * θ.inheritance .vh *
          (x₃ θ * (1 / 3) + (1 - x₃ θ) * if ({0, 2} : Finset (Fin 4)) ∈ r.val then 1 else 0) +
        ((1 - ρ) * θ.inheritance .vh * θ.inheritance .uh *
            (x₃ θ * (1 / 3) + (1 - x₃ θ) * if ({0, 3} : Finset (Fin 4)) ∈ r.val then 1 else 0) +
          θ.inheritance .vh * ((1 - ρ) * θ.inheritance .vh + ρ) *
            (Real.exp (-θ.length .vh) * (1 / 3) + (1 - Real.exp (-θ.length .vh)) *
              if ({0, 1} : Finset (Fin 4)) ∈ r.val then 1 else 0)) := by
  have hstep := stepOf_two_two (N := N₃) (θ := θ) (ρ := ρ) (v := V₃.h) (k₁ := E₃.uh) (k₂ := E₃.vh) rfl rfl
    (by decide) target₃_h (x := (0 : Fin 4)) (y := 1) (by decide)
    (fun t => κv θ ρ r (ow (arcsInto N₃ .h) top t)) (ow_dep (arcsInto N₃ .h) top (κv θ ρ r))
  unfold κh stepKernel
  rw [arriving₃_h, h, hstep,
    κv_both_u hθ hρ r _ (by rw [ow_h_c, hc]) (by rw [ow_h_d, hd]) (ow_h_uh _ _ _) (ow_h_vh _ _ _),
    κv_cherry_u hθ hρ r _ (by rw [ow_h_c, hc]) (by rw [ow_h_d, hd]) (ow_h_uh _ _ _) (ow_h_vh _ _ _),
    κv_split₁ hθ hρ r _ (by rw [ow_h_c, hc]) (by rw [ow_h_d, hd]) (ow_h_uh _ _ _) (ow_h_vh _ _ _),
    κv_split₂ hθ hρ r _ (by rw [ow_h_c, hc]) (by rw [ow_h_d, hd]) (ow_h_uh _ _ _) (ow_h_vh _ _ _),
    κv_both_v hθ hρ r _ (by rw [ow_h_c, hc]) (by rw [ow_h_d, hd]) (ow_h_uh _ _ _) (ow_h_vh _ _ _),
    κv_cherry_v hθ hρ r _ (by rw [ow_h_c, hc]) (by rw [ow_h_d, hd]) (ow_h_uh _ _ _) (ow_h_vh _ _ _)]

/-- The whole chain, from the lineages at the top of the arcs entering the leaves. -/
theorem κw_eq (hθ : N₃.IsMetric θ) (hρ : 0 ≤ ρ ∧ ρ ≤ 1) (r : QuartetTree (Fin 4))
    (top : E₃ → Finset (Finset (Fin 4))) (ha : top .a = {{0}}) (hb : top .b = {{1}}) (hc : top .c = {{2}})
    (hd : top .d = {{3}}) :
    κw θ ρ r top = Real.exp (-θ.length .hw) * (
      θ.inheritance .uh * ((1 - ρ) * θ.inheritance .uh + ρ) *
          (Real.exp (-θ.length .uh) * (1 / 3) + (1 - Real.exp (-θ.length .uh)) *
            if ({0, 1} : Finset (Fin 4)) ∈ r.val then 1 else 0) +
        (1 - ρ) * θ.inheritance .uh * θ.inheritance .vh *
          (x₃ θ * (1 / 3) + (1 - x₃ θ) * if ({0, 2} : Finset (Fin 4)) ∈ r.val then 1 else 0) +
        ((1 - ρ) * θ.inheritance .vh * θ.inheritance .uh *
            (x₃ θ * (1 / 3) + (1 - x₃ θ) * if ({0, 3} : Finset (Fin 4)) ∈ r.val then 1 else 0) +
          θ.inheritance .vh * ((1 - ρ) * θ.inheritance .vh + ρ) *
            (Real.exp (-θ.length .vh) * (1 / 3) + (1 - Real.exp (-θ.length .vh)) *
              if ({0, 1} : Finset (Fin 4)) ∈ r.val then 1 else 0))) +
      (1 - Real.exp (-θ.length .hw)) * if ({0, 1} : Finset (Fin 4)) ∈ r.val then 1 else 0 := by
  have hstep := stepOf_unique_two (N := N₃) (θ := θ) (ρ := ρ) (v := V₃.w) (e := E₃.hw) hρ.1 rfl (fun f => target₃_w)
    (hθ.2.2.1 E₃.hw (isTreeArc_of_unique fun f => target₃_w)) (P := {0, 1}) (by decide)
    (fun t => κh θ ρ r (ow (arcsInto N₃ .w) top t)) (ow_dep (arcsInto N₃ .w) top (κh θ ρ r))
  have hkeep : ∀ (f : E₃), f ≠ E₃.hw → ∀ t : E₃ → Finset (Finset (Fin 4)), ow (arcsInto N₃ .w) top t f = top f := by
    intro f hf t
    refine ow_of_notMem ?_ _ _
    rw [mem_arcsInto]
    intro h
    exact hf (target₃_w h)
  unfold κw stepKernel
  rw [arriving₃_w, ha, hb, show ({{0}} : Finset (Finset (Fin 4))) ∪ {{1}} = Fab by decide, hstep,
    κh_two hθ hρ r _ (by rw [hkeep _ (by decide), hc]) (by rw [hkeep _ (by decide), hd]) (ow_of_mem hw_mem _ _),
    κh_cherry hθ hρ r _ (by rw [hkeep _ (by decide), hc]) (by rw [hkeep _ (by decide), hd]) (ow_of_mem hw_mem _ _)]

/-- **The concordance factors of `N₃`, by the chain of the NMSC**, at inheritance correlation `ρ`. -/
theorem nmscCF_N₃ (hθ : N₃.IsMetric θ) (hρ : 0 ≤ ρ ∧ ρ ≤ 1) (r : QuartetTree (Fin 4)) :
    nmscCF N₃ θ ρ r = Real.exp (-θ.length .hw) * (
      θ.inheritance .uh * ((1 - ρ) * θ.inheritance .uh + ρ) *
          (Real.exp (-θ.length .uh) * (1 / 3) + (1 - Real.exp (-θ.length .uh)) *
            if ({0, 1} : Finset (Fin 4)) ∈ r.val then 1 else 0) +
        (1 - ρ) * θ.inheritance .uh * θ.inheritance .vh *
          (x₃ θ * (1 / 3) + (1 - x₃ θ) * if ({0, 2} : Finset (Fin 4)) ∈ r.val then 1 else 0) +
        ((1 - ρ) * θ.inheritance .vh * θ.inheritance .uh *
            (x₃ θ * (1 / 3) + (1 - x₃ θ) * if ({0, 3} : Finset (Fin 4)) ∈ r.val then 1 else 0) +
          θ.inheritance .vh * ((1 - ρ) * θ.inheritance .vh + ρ) *
            (Real.exp (-θ.length .vh) * (1 / 3) + (1 - Real.exp (-θ.length .vh)) *
              if ({0, 1} : Finset (Fin 4)) ∈ r.val then 1 else 0))) +
      (1 - Real.exp (-θ.length .hw)) * if ({0, 1} : Finset (Fin 4)) ∈ r.val then 1 else 0 := by
  have hN := isPhylogenetic_N₃
  rw [nmscCF_eq_cherryMass hN hθ hρ r, taxa_eq_univ, cherryMass_eq_sum_rootMass]
  have hmean := meanOn_of_forall_ne (N := N₃) (θ := θ) (ρ := ρ) hN inj₃
    (D := insert V₃.u (insert V₃.v (insert V₃.h (insert V₃.w {V₃.a, V₃.b, V₃.c, V₃.d})))) (fun y => by
      cases y <;> decide) (φ₃ r)
  unfold φ₃ at hmean
  rw [← hmean]
  change meanOn N₃ θ ρ inj₃ _ (φ₃ r) = _
  rw [meanOn_insert (fun e => by cases e <;> decide) (by decide) (fun e => by cases e <;> decide),
    meanOn_insert (fun e => by cases e <;> decide) (by decide) (fun e => by cases e <;> decide),
    meanOn_insert (fun e => by cases e <;> decide) (by decide) (fun e => by cases e <;> decide),
    meanOn_insert (fun e => by cases e <;> decide) (by decide) (fun e => by cases e <;> decide)]
  refine meanOn_eq_const hN hθ.isNormalized hρ.1 (validInj_taxaInj univ)
    (fun e => by cases e <;> decide) (by decide) fun bot top h => ?_
  exact κw_eq hθ hρ r top
    (top_eq_of_leaf hN 0 (fun f => by cases f <;> decide) rfl (fun e => by cases e <;> decide)
      (by decide) h)
    (top_eq_of_leaf hN 1 (fun f => by cases f <;> decide) rfl (fun e => by cases e <;> decide)
      (by decide) h)
    (top_eq_of_leaf hN 2 (fun f => by cases f <;> decide) rfl (fun e => by cases e <;> decide)
      (by decide) h)
    (top_eq_of_leaf hN 3 (fun f => by cases f <;> decide) rfl (fun e => by cases e <;> decide)
      (by decide) h)

/-- **The source's formula for the first entry**, derived from the definition of the NMSC: `figure5CFab` of
`NANUQ.lean`, with `γ` the inheritance of the arc from `v`, `x₁` for the arc below the reticulation, `x₂`, `x₄` for
the hybrid arcs and `x₃` for the edge `u v` of the unrooted network. -/
theorem nmscCF_N₃_abcd (hθ : N₃.IsMetric θ) :
    nmscCF N₃ θ 0 abcd = figure5CFab (θ.inheritance .vh) (Real.exp (-θ.length .hw)) (Real.exp (-θ.length .uh)) (x₃ θ)
      (Real.exp (-θ.length .vh)) := by
  have hs : θ.inheritance .uh = 1 - θ.inheritance .vh := by
    have := inheritance_add_eq_one hθ.isNormalized (k₁ := E₃.uh) (k₂ := E₃.vh) (v := V₃.h) rfl rfl (by decide) target₃_h
    linarith
  have h₁ : ({0, 1} : Finset (Fin 4)) ∈ abcd.val := by decide
  have h₂ : ({0, 2} : Finset (Fin 4)) ∉ abcd.val := by decide
  have h₃ : ({0, 3} : Finset (Fin 4)) ∉ abcd.val := by decide
  rw [nmscCF_N₃ hθ ⟨le_rfl, zero_le_one⟩, ite_eq_left h₁, ite_eq_right h₂, ite_eq_right h₃, hs]
  unfold figure5CFab
  ring

/-- The source's formula for the second entry. -/
theorem nmscCF_N₃_acbd (hθ : N₃.IsMetric θ) :
    nmscCF N₃ θ 0 acbd = figure5CFac (θ.inheritance .vh) (Real.exp (-θ.length .hw)) (Real.exp (-θ.length .uh)) (x₃ θ)
      (Real.exp (-θ.length .vh)) := by
  have hs : θ.inheritance .uh = 1 - θ.inheritance .vh := by
    have := inheritance_add_eq_one hθ.isNormalized (k₁ := E₃.uh) (k₂ := E₃.vh) (v := V₃.h) rfl rfl (by decide) target₃_h
    linarith
  have h₁ : ({0, 1} : Finset (Fin 4)) ∉ acbd.val := by decide
  have h₂ : ({0, 2} : Finset (Fin 4)) ∈ acbd.val := by decide
  have h₃ : ({0, 3} : Finset (Fin 4)) ∉ acbd.val := by decide
  rw [nmscCF_N₃ hθ ⟨le_rfl, zero_le_one⟩, ite_eq_right h₁, ite_eq_left h₂, ite_eq_right h₃, hs]
  unfold figure5CFac
  ring

/-- The source's formula for the third entry. -/
theorem nmscCF_N₃_adbc (hθ : N₃.IsMetric θ) :
    nmscCF N₃ θ 0 adbc = figure5CFac (θ.inheritance .vh) (Real.exp (-θ.length .hw)) (Real.exp (-θ.length .uh)) (x₃ θ)
      (Real.exp (-θ.length .vh)) := by
  have hs : θ.inheritance .uh = 1 - θ.inheritance .vh := by
    have := inheritance_add_eq_one hθ.isNormalized (k₁ := E₃.uh) (k₂ := E₃.vh) (v := V₃.h) rfl rfl (by decide) target₃_h
    linarith
  have h₁ : ({0, 1} : Finset (Fin 4)) ∉ adbc.val := by decide
  have h₂ : ({0, 2} : Finset (Fin 4)) ∉ adbc.val := by decide
  have h₃ : ({0, 3} : Finset (Fin 4)) ∈ adbc.val := by decide
  rw [nmscCF_N₃ hθ ⟨le_rfl, zero_le_one⟩, ite_eq_right h₁, ite_eq_right h₂, ite_eq_left h₃, hs]
  unfold figure5CFac
  ring

end Chain

/-! ### The network is binary and level-1, with a `3₂`-cycle -/

theorem indegree_of {y : V₃} {S : Finset E₃} (h : ∀ e, N₃.graph.target e = y ↔ e ∈ S) : N₃.graph.indegree y = #S := by
  rw [indegree_eq_card]
  congr 1
  ext e
  rw [mem_arcsInto, h]

theorem outdegree_of {y : V₃} {S : Finset E₃} (h : ∀ e, N₃.graph.source e = y ↔ e ∈ S) : N₃.graph.outdegree y = #S := by
  unfold DirectedMultigraph.outdegree
  rw [← Set.ncard_coe_finset]
  congr 1
  ext e
  simp [h]

theorem indegree_h : N₃.graph.indegree .h = 2 := by
  rw [indegree_of (S := {.uh, .vh}) (fun e => by cases e <;> decide)]
  rfl

/-- `N₃` is binary. -/
theorem isBinary_N₃ : N₃.IsBinary := by
  refine ⟨?_, fun y hy hne => ?_⟩
  · change N₃.graph.outdegree .r = 2
    rw [outdegree_of (S := {.ru, .rv}) (fun e => by cases e <;> decide)]
    rfl
  · cases y
    · exact absurd rfl hy
    · rw [indegree_of (S := {.ru}) (fun e => by cases e <;> decide),
        outdegree_of (S := {.c, .uh}) (fun e => by cases e <;> decide)]
      rfl
    · rw [indegree_of (S := {.rv}) (fun e => by cases e <;> decide),
        outdegree_of (S := {.d, .vh}) (fun e => by cases e <;> decide)]
      rfl
    · rw [indegree_of (S := {.uh, .vh}) (fun e => by cases e <;> decide),
        outdegree_of (S := {.hw}) (fun e => by cases e <;> decide)]
      rfl
    · rw [indegree_of (S := {.hw}) (fun e => by cases e <;> decide),
        outdegree_of (S := {.a, .b}) (fun e => by cases e <;> decide)]
      rfl
    · exact absurd (outdegree_of (S := ∅) (fun e => by cases e <;> decide)) hne
    · exact absurd (outdegree_of (S := ∅) (fun e => by cases e <;> decide)) hne
    · exact absurd (outdegree_of (S := ∅) (fun e => by cases e <;> decide)) hne
    · exact absurd (outdegree_of (S := ∅) (fun e => by cases e <;> decide)) hne

/-- Only the two arcs into the reticulation are hybrid. -/
theorem eq_of_isHybridArc {e : E₃} (h : N₃.IsHybridArc e) : e = .uh ∨ e = .vh := by
  cases e
  all_goals first
    | exact Or.inl rfl
    | exact Or.inr rfl
    | exact absurd h (not_isHybridArc_of_isTreeArc (isTreeArc_of_unique fun f hf => by
        cases f <;> first | rfl | exact absurd hf (by decide)))

/-- `N₃` is level-1: its only reticulation has two parents. -/
theorem isLevelOne_N₃ : IsLevelOne N₃ := by
  intro y
  set A := univ.filter fun e => N₃.IsHybridArc e ∧ N₃.graph.blobSetoid y (N₃.graph.source e) ∧
    N₃.graph.blobSetoid y (N₃.graph.target e) with hA
  set B := univ.filter fun z => 2 ≤ N₃.graph.indegree z ∧ N₃.graph.blobSetoid y z with hB
  by_cases hh : N₃.graph.blobSetoid y .h
  · have hAc : #A ≤ 2 := by
      have hsub : A ⊆ {E₃.uh, E₃.vh} := fun e he => by
        have := eq_of_isHybridArc (mem_filter.1 he).2.1
        simpa using this
      exact (card_le_card hsub).trans (by decide)
    have hBc : 1 ≤ #B :=
      card_pos.2 ⟨.h, mem_filter.2 ⟨mem_univ _, by rw [indegree_h], hh⟩⟩
    have h₁ : (#A : ℤ) ≤ 2 := by exact_mod_cast hAc
    have h₂ : (1 : ℤ) ≤ #B := by exact_mod_cast hBc
    linarith
  · have hAe : A = ∅ := by
      refine filter_false_of_mem ?_
      rintro e - ⟨hy₁, -, hy₂⟩
      rcases eq_of_isHybridArc hy₁ with rfl | rfl <;> exact hh hy₂
    rw [hAe]
    simp only [card_empty, Nat.cast_zero]
    have : (0 : ℤ) ≤ #B := by positivity
    linarith

/-- `N₃` has a cut edge with `a, b` on one side and `c, d` on the other: the child arc of the reticulation. -/
theorem hasCutSplit_N₃ : N₃.HasCutSplit (({0, 1} : Finset (Fin 4)) : Set (Fin 4)) := by
  refine ⟨.hw, {y | y = .w ∨ y = .a ∨ y = .b}, fun f => ?_, ?_⟩
  · cases f <;> simp [DirectedMultigraph.Crosses, N₃]
  · ext x
    fin_cases x <;> simp [N₃]

/-- The induced network on all four taxa has the cut-edge split `ab|cd`. -/
theorem inducedCutSplit_N₃ : InducedCutSplit N₃ abcd := by
  refine ⟨{0, 1}, by simp [abcd], ?_⟩
  have := (hasCutSplit_iff_hasCutSplitOn_univ isPhylogenetic_N₃ _).1 hasCutSplit_N₃
  rwa [taxa_eq_univ, coe_univ]

/-- An arc into the reticulation is on the cycle. -/
theorem not_isBridge_uh : ¬ N₃.graph.underlying.IsBridge .uh := by
  rw [DirectedMultigraph.isBridge_iff]
  rintro ⟨S, hS⟩
  have c₁ := (hS .uh).2 rfl
  have c₂ : ¬ N₃.graph.Crosses .ru S := fun h => by cases (hS _).1 h
  have c₃ : ¬ N₃.graph.Crosses .rv S := fun h => by cases (hS _).1 h
  have c₄ : ¬ N₃.graph.Crosses .vh S := fun h => by cases (hS _).1 h
  simp only [DirectedMultigraph.Crosses, N₃] at c₁ c₂ c₃ c₄
  tauto

theorem sameBlob_h_u : N₃.graph.blobSetoid .h .u :=
  Relation.ReflTransGen.single ⟨.uh, not_isBridge_uh, Or.inr ⟨rfl, rfl⟩⟩

theorem not_isBridge_vh : ¬ N₃.graph.underlying.IsBridge .vh := by
  rw [DirectedMultigraph.isBridge_iff]
  rintro ⟨S, hS⟩
  have c₁ := (hS .vh).2 rfl
  have c₂ : ¬ N₃.graph.Crosses .ru S := fun h => by cases (hS _).1 h
  have c₃ : ¬ N₃.graph.Crosses .rv S := fun h => by cases (hS _).1 h
  have c₄ : ¬ N₃.graph.Crosses .uh S := fun h => by cases (hS _).1 h
  simp only [DirectedMultigraph.Crosses, N₃] at c₁ c₂ c₃ c₄
  tauto

theorem sameBlob_h_v : N₃.graph.blobSetoid .h .v :=
  Relation.ReflTransGen.single ⟨.vh, not_isBridge_vh, Or.inr ⟨rfl, rfl⟩⟩

/-- What the reticulation reaches. -/
theorem reaches_h {y : V₃} (h : N₃.graph.Reaches .h y) : y = .h ∨ y = .w ∨ y = .a ∨ y = .b := by
  induction h with
  | refl => exact Or.inl rfl
  | tail _ hstep ih =>
    obtain ⟨e, he₁, he₂⟩ := hstep
    subst he₂
    rcases ih with rfl | rfl | rfl | rfl <;> cases e <;> first | decide | exact absurd he₁ (by decide)

/-- A walk outside the blob from the leaf `c` stays there. -/
theorem blockWalk_c {z : V₃} (h : TOBQMC.Level1.BlockWalk N₃ .h .c z) : z = .c := by
  induction h with
  | refl => rfl
  | tail _ hstep ih =>
    subst ih
    obtain ⟨-, hz, e, he⟩ := hstep
    rcases he with ⟨he, -⟩ | ⟨he₁, he₂⟩
    · cases e <;> exact absurd he (by decide)
    · cases e <;> first
        | exact absurd he₂ (by decide)
        | exact absurd (he₁ ▸ sameBlob_h_u) hz

/-- A walk outside the blob from the leaf `d` stays there. -/
theorem blockWalk_d {z : V₃} (h : TOBQMC.Level1.BlockWalk N₃ .h .d z) : z = .d := by
  induction h with
  | refl => rfl
  | tail _ hstep ih =>
    subst ih
    obtain ⟨-, hz, e, he⟩ := hstep
    rcases he with ⟨he, -⟩ | ⟨he₁, he₂⟩
    · cases e <;> exact absurd he (by decide)
    · cases e <;> first
        | exact absurd he₂ (by decide)
        | exact absurd (he₁ ▸ sameBlob_h_v) hz

/-- **`N₃` has a `3₂`-cycle.** -/
theorem hasThreeTwoCycle_N₃ : HasThreeTwoCycle N₃ univ := by
  have hn : ∀ x : Fin 4, N₃.graph.Reaches .h (N₃.leaf x) ↔ x = 0 ∨ x = 1 := by
    intro x
    constructor
    · intro h
      have := reaches_h h
      fin_cases x
      · exact Or.inl rfl
      · exact Or.inr rfl
      · simp [N₃] at this
      · simp [N₃] at this
    · have hw : N₃.graph.Reaches .h .w := .single ⟨.hw, rfl, rfl⟩
      rintro (rfl | rfl)
      · exact hw.tail ⟨.a, rfl, rfl⟩
      · exact hw.tail ⟨.b, rfl, rfl⟩
  refine ⟨.h, by rw [indegree_h], ?_, fun x _ y _ hxy hx hy hw => ?_⟩
  · have : (univ.filter fun x => N₃.graph.Reaches .h (N₃.leaf x)) = {0, 1} := by
      ext x
      simp [hn]
    rw [this]
    rfl
  · have hxc : x = 2 ∨ x = 3 := by
      rw [hn] at hx
      fin_cases x <;> simp at hx ⊢
    have hyc : y = 2 ∨ y = 3 := by
      rw [hn] at hy
      fin_cases y <;> simp at hy ⊢
    rcases hxc with rfl | rfl <;> rcases hyc with rfl | rfl
    · exact hxy rfl
    · exact absurd (blockWalk_c hw) (by decide)
    · exact absurd (blockWalk_d hw) (by decide)
    · exact hxy rfl

/-! ### The parameters -/

/-- The parameters of `figure5_centroid`. All lengths are positive. -/
def metric₃ : MetricData E₃ where
  length := fun
    | .ru => Real.log (4 / 3)
    | .rv => Real.log (3 / 2)
    | .uh => Real.log (10 / 9)
    | .vh => Real.log (10 / 9)
    | .hw => Real.log (43 / 40)
    | _ => 1
  inheritance := fun
    | .uh => 1 / 2
    | .vh => 1 / 2
    | _ => 1

theorem isMetric_metric₃ : N₃.IsMetric metric₃ := by
  have hne : ∀ e, N₃.graph.target e = .h → ¬ N₃.IsTreeArc e := fun e he hte => by
    unfold RootedNetwork.IsTreeArc at hte
    rw [he, indegree_h] at hte
    omega
  have hlog : ∀ {a : ℝ}, 1 < a → 0 < Real.log a := fun h => Real.log_pos h
  refine ⟨fun e he => ?_, fun e _ => ?_, fun e he => ?_, fun e _ => ?_, fun y hy => ?_⟩
  · cases e
    · exact hlog (by norm_num)
    · exact hlog (by norm_num)
    · exact one_pos
    · exact one_pos
    · exact absurd he (hne _ rfl)
    · exact absurd he (hne _ rfl)
    · exact hlog (by norm_num)
    · exact one_pos
    · exact one_pos
  · cases e
    · exact (hlog (by norm_num)).le
    · exact (hlog (by norm_num)).le
    · exact zero_le_one
    · exact zero_le_one
    · exact (hlog (by norm_num)).le
    · exact (hlog (by norm_num)).le
    · exact (hlog (by norm_num)).le
    · exact zero_le_one
    · exact zero_le_one
  · cases e
    · rfl
    · rfl
    · rfl
    · rfl
    · exact absurd he (hne _ rfl)
    · exact absurd he (hne _ rfl)
    · rfl
    · rfl
    · rfl
  · cases e
    · exact one_pos
    · exact one_pos
    · exact one_pos
    · exact one_pos
    · exact one_div_pos.2 two_pos
    · exact one_div_pos.2 two_pos
    · exact one_pos
    · exact one_pos
    · exact one_pos
  · rw [indegree_eq_card] at hy
    obtain ⟨f, hf, g, hg, hfg⟩ := one_lt_card.1 hy
    have key : ∀ f g : E₃, f ≠ g → N₃.graph.target f = N₃.graph.target g → N₃.graph.target f = .h := by decide
    have hy' : y = .h := (mem_arcsInto.1 hf).symm.trans (key f g hfg ((mem_arcsInto.1 hf).trans (mem_arcsInto.1 hg).symm))
    subst hy'
    rw [sum_ite_target_pair _ (v := V₃.h) (k₁ := E₃.uh) (k₂ := E₃.vh) rfl rfl (by decide) target₃_h]
    change (1 / 2 : ℝ) + 1 / 2 = 1
    norm_num

private theorem exp_neg_log {a : ℝ} (ha : 0 < a) : Real.exp (-Real.log a) = a⁻¹ := by
  rw [Real.exp_neg, Real.exp_log ha]

/-- The quartet trees on `Fin 4`. -/
theorem quartet_cases (r : QuartetTree (Fin 4)) : r = abcd ∨ r = acbd ∨ r = adbc := by
  have hne₁ : abcd ≠ acbd := fun h => by
    have := congrArg Subtype.val h
    revert this
    decide
  have hne₂ : abcd ≠ adbc := fun h => by
    have := congrArg Subtype.val h
    revert this
    decide
  have hne₃ : acbd ≠ adbc := fun h => by
    have := congrArg Subtype.val h
    revert this
    decide
  have hsub : ({abcd, acbd, adbc} : Finset (QuartetTree (Fin 4))) ⊆ treesOn univ := fun s _ =>
    mem_treesOn.2 (taxa_eq_univ s)
  have hcard : #({abcd, acbd, adbc} : Finset (QuartetTree (Fin 4))) = 3 := by
    rw [card_insert_of_notMem (by simp [hne₁, hne₂]), card_pair hne₃]
  have heq := eq_of_subset_of_card_le hsub (by rw [hcard, card_treesOn (by decide)])
  have hr : r ∈ treesOn (univ : Finset (Fin 4)) := mem_treesOn.2 (taxa_eq_univ r)
  rw [← heq] at hr
  simpa using hr

/-- **A binary level-1 network with a `3₂`-cycle at the centroid**, at positive branch lengths, from the definition of
the NMSC. -/
theorem centroid_N₃ (r : QuartetTree (Fin 4)) : nmscCF N₃ metric₃ 0 r = 1 / 3 := by
  have hθ := isMetric_metric₃
  have h₁ : Real.exp (-metric₃.length .hw) = 40 / 43 := by
    change Real.exp (-Real.log (43 / 40)) = _
    rw [exp_neg_log (by norm_num)]
    norm_num
  have h₂ : Real.exp (-metric₃.length .uh) = 9 / 10 := by
    change Real.exp (-Real.log (10 / 9)) = _
    rw [exp_neg_log (by norm_num)]
    norm_num
  have h₄ : Real.exp (-metric₃.length .vh) = 9 / 10 := by
    change Real.exp (-Real.log (10 / 9)) = _
    rw [exp_neg_log (by norm_num)]
    norm_num
  have h₃ : x₃ metric₃ = 1 / 2 := by
    change Real.exp (-Real.log (4 / 3)) * Real.exp (-Real.log (3 / 2)) = _
    rw [exp_neg_log (by norm_num), exp_neg_log (by norm_num)]
    norm_num
  have hγ : metric₃.inheritance .vh = 1 / 2 := rfl
  obtain ⟨hab, hac⟩ := figure5_centroid
  rcases quartet_cases r with rfl | rfl | rfl
  · rw [nmscCF_N₃_abcd hθ, h₁, h₂, h₃, h₄, hγ]
    exact hab
  · rw [nmscCF_N₃_acbd hθ, h₁, h₂, h₃, h₄, hγ]
    exact hac
  · rw [nmscCF_N₃_adbc hθ, h₁, h₂, h₃, h₄, hγ]
    exact hac

/-- The hypothesis of Theorem 36 as printed holds at these parameters: Definition 8 calls the centroid tree-like. -/
theorem threeTwoTreelike_metric₃ : ThreeTwoTreelike N₃ (nmscCF N₃ metric₃ 0) := by
  intro q hq _
  obtain ⟨s, hs⟩ : (treesOn q).Nonempty := by
    rw [← card_pos, card_treesOn hq]
    norm_num
  exact ⟨s, hs, fun r _ => ((centroid_N₃ r).trans (centroid_N₃ s).symm).le,
    fun r _ r' _ => (centroid_N₃ r).trans (centroid_N₃ r').symm⟩

theorem not_noCentroidCF_metric₃ : ¬ TINNiK.NoCentroidCF (nmscCF N₃ metric₃ 0) :=
  fun h => h univ (by decide) fun r _ => centroid_N₃ r

theorem isTreelike_N₃ {q : Finset (Fin 4)} (hq : #q = 4) : IsTreelike N₃ q := by
  have hu : q = univ := eq_univ_of_card q (by simpa using hq)
  subst hu
  exact ⟨abcd, mem_treesOn.2 (taxa_eq_univ _), inducedCutSplit_N₃⟩

/-- On the network the class of the four taxa is the tree `ab|cd`; by the concordance factors (`cfClass_metric₃`), it is
the star tree. The law of the counts depends only on the concordance factors, and the network with its taxa relabelled
has the same ones and another class, so no function of the counts returns the class of both. That last remark is not
formalized. -/
theorem networkClass_N₃ : networkClass N₃ univ = .tree abcd := by
  have hex : ∃ s ∈ treesOn (univ : Finset (Fin 4)), InducedCutSplit N₃ s :=
    ⟨abcd, mem_treesOn.2 (taxa_eq_univ _), inducedCutSplit_N₃⟩
  unfold networkClass
  rw [dite_eq_left hex]
  congr 1
  exact AllmanEtAl2023.inducedCutSplit_unique isPhylogenetic_N₃ hex.choose_spec.2 inducedCutSplit_N₃
    ((taxa_eq_univ _).trans (taxa_eq_univ _).symm)

theorem cfClass_metric₃ : cfClass (nmscCF N₃ metric₃ 0) univ = .star :=
  cfClass_eq_star fun r _ => centroid_N₃ r

/-- **Theorem 36 of NANUQ as printed fails**, at the level of the quartet distance, which is where its proof places
the claim, on the binary level-1 network `N₃` (`isBinary_N₃`, `isLevelOne_N₃`, `hasThreeTwoCycle_N₃`) at the
parameters `metric₃`, where the printed hypothesis holds (`threeTwoTreelike_metric₃`). For every sequence `α_m` and
every `0 < β < 1`, the probability that the computed distance agrees with the theoretical one does not tend to one. -/
theorem not_theorem36AsPrinted_N₃ : ¬ Theorem36AsPrinted N₃ :=
  not_theorem36AsPrinted isPhylogenetic_N₃ (fun _ hq hnt => absurd (isTreelike_N₃ hq) hnt) isMetric_metric₃
    threeTwoTreelike_metric₃ not_noCentroidCF_metric₃

/-! ### The theorem applies at the source's sufficient condition -/

/-- **The source's sufficient condition on `N₃`** (Proposition 10, and the note after the proof of Theorem 36): when
the arc below the reticulation has `x₁ ≤ 4/5`, that is, length at least `log (5/4)`, the concordance factor is
strictly on the half-line of `ab|cd`. -/
theorem isT1Strict_N₃ {θ : MetricData E₃} (hθ : N₃.IsMetric θ) (hx : Real.exp (-θ.length .hw) ≤ 4 / 5) :
    IsT1Strict (nmscCF N₃ θ 0) abcd := by
  have hybrid : ∀ {e : E₃}, N₃.graph.target e = .h → 0 ≤ θ.length e := fun he =>
    hθ.2.1 _ (by unfold RootedNetwork.IsHybridArc; rw [he, indegree_h])
  have tree : ∀ {e : E₃}, (∀ f, N₃.graph.target f = N₃.graph.target e → f = e) → 0 < θ.length e := fun hu =>
    hθ.1 _ (isTreeArc_of_unique hu)
  have hle : ∀ {t : ℝ}, 0 ≤ t → Real.exp (-t) ≤ 1 := fun ht => Real.exp_le_one_iff.2 (by linarith)
  have hru : 0 < θ.length .ru := tree fun f hf => by cases f <;> first | rfl | exact absurd hf (by decide)
  have hrv : 0 < θ.length .rv := tree fun f hf => by cases f <;> first | rfl | exact absurd hf (by decide)
  have hx₃ : 0 < x₃ θ := mul_pos (Real.exp_pos _) (Real.exp_pos _)
  have hx₃' : x₃ θ ≤ 1 := by
    have := mul_le_mul (hle hru.le) (hle hrv.le) (Real.exp_pos _).le zero_le_one
    rwa [one_mul] at this
  have hlt := figure5_lt (γ := θ.inheritance .vh) (Real.exp_pos (-θ.length .hw)).le hx
    (hle (hybrid (e := E₃.uh) rfl)) hx₃ hx₃' (hle (hybrid (e := E₃.vh) rfl))
  have hab := nmscCF_N₃_abcd hθ
  have hac := nmscCF_N₃_acbd hθ
  have had := nmscCF_N₃_adbc hθ
  have halt : ∀ r ∈ abcd.alternatives, nmscCF N₃ θ 0 r = nmscCF N₃ θ 0 acbd := by
    intro r hr
    rcases quartet_cases r with rfl | rfl | rfl
    · exact absurd rfl (QuartetTree.mem_alternatives.1 hr).2
    · rfl
    · rw [had, hac]
  refine ⟨fun r hr => ?_, fun r hr r' hr' => (halt r hr).trans (halt r' hr').symm⟩
  rw [halt r hr, hac, hab]
  exact hlt

/-- **Theorem 36 on `N₃`**, at the source's sufficient condition: the corrected hypotheses hold, and the conclusion.
-/
theorem theorem36_N₃ {θ : MetricData E₃} (hθ : N₃.IsMetric θ) (hx : Real.exp (-θ.length .hw) ≤ 4 / 5) :
    ∃ α : ℕ → ℝ, (∀ m, 0 < α m) ∧ (∀ m, 1 ≤ m → α m < 1) ∧ Filter.Tendsto α Filter.atTop (nhds 0) ∧
      ∀ β : ℝ, 0 < β → β < 1 → ∀ mlT mlC : (QuartetTree (Fin 4) → ℝ) → Finset (Fin 4) → QuartetTree (Fin 4),
        IsMaxCountSelection mlT → IsMinCountSelection mlC →
        Filter.Tendsto (fun m => iidProb (geneTreeDist N₃ θ 0) m fun ω =>
          (∀ q : Finset (Fin 4), #q = 4 →
            classify mlT mlC (α m) β (quartetCount unroot ω) q = networkClass N₃ q) ∧
          nanuqDistance (classify mlT mlC (α m) β (quartetCount unroot ω)) = networkDistance N₃)
          Filter.atTop (nhds 1) := by
  have hstrict := isT1Strict_N₃ hθ hx
  have hmem : abcd ∈ treesOn (univ : Finset (Fin 4)) := mem_treesOn.2 (taxa_eq_univ _)
  refine theorem36 isPhylogenetic_N₃ isBinary_N₃ isLevelOne_N₃ hθ (fun q hq _ => ?_) (fun q hq hall => ?_)
  · have hu : q = univ := eq_univ_of_card q (by simpa using hq)
    subst hu
    exact ⟨abcd, hmem, QuartetTests.IsT1Null.of_isT1Strict hstrict⟩
  · have hu : q = univ := eq_univ_of_card q (by simpa using hq)
    subst hu
    obtain ⟨r₁, r₂, -, ha⟩ := QuartetTests.QuartetTree.exists_alternatives abcd
    have hr : r₁ ∈ abcd.alternatives := by rw [ha]; simp
    exact (hstrict.1 r₁ hr).ne ((hall r₁ (mem_treesOn.2 (taxa_eq_univ _))).trans (hall abcd hmem).symm)

end External.AllmanBanosRhodes2019.ThreeTwo
