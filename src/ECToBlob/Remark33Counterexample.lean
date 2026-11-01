module

public import Basic.Defs
public import Phylogenetics.NMSC.DisplayedTreeModel
public import TOBQMC.Level1Blobs
public import ECToBlob.Remark33
public import ECToBlob.Remark52

/-!
# ECToBlob Remark 3.3: "no anomalous quartets" has to be strict

Remark 3.3 says that the NMSC with independent or correlated inheritance satisfies (3.1) "provided the network has no
anomalous quartets and that cut edges (which are necessarily tree edges) have positive lengths [8]". Definition 2 of
[8] (Ané, Fogg, Allman, Baños, Rhodes 2024) calls a 4-taxon binary network of class 1 anomalous if `P(T₁ | N) < 1/3`.
This file gives a network on four taxa with a 3₂-cycle, at valid parameters with a cut edge of positive length, with
`p_ab|cd = p_ac|bd = p_ad|bc = 1/3`. It is not anomalous in that sense, (3.1) fails, and so does the conclusion of
Theorem 3.1: all three binary trees are optimal.

The claim holds with the definition of TINNiK ([5] of the paper, `notes/tinnik/readable.txt`, line 144): "An anomalous
quartet {a,b,c,d} is one whose CF is ab|cd cut of the form (p, q, q) with q ≥ 1/3", for which `q = 1/3` is anomalous. The
paper's use agrees with it: "the inequality uses the no-anomalous quartets assumption" (line 722, of the strict (5.2)), and
without it "the correct quartet topology need not be indicated by the largest entry of the expected CF" (lines 1459-1460).
So does Definition 1 of TOB-QMC, with strict inequalities. The Lean definitions `TOBQMC.IsTQuartetNonanomalous` and
`NoAnomalousQuartets` are of this kind.

## The network

`cycleNet`: the root `r` has children `x`, `y`; `x` has children `h` and the taxon `c`; `y` has children `h` and the
taxon `d`; the reticulation `h` has one child `u`, by the cut edge `e`; and `u` has children `a`, `b`. It is binary. Its
semidirected form is the 3₂-cycle of Figure 3 of [8], whose tree edge has length `s₀ = s₁ + s₂` here.

## Main results

* `nmscCF_cycleNet_abcd`: the concordance factor of `ab|cd`, for all valid parameters and all `ρ`, as in Example 1 of [8]:
  `(1 - e^{-t}) + e^{-t} (P₁ (1 - 2/3 e^{-ℓ₁}) + P₂ (1 - 2/3 e^{-ℓ₂}) + 2/3 Q e^{-(s₁ + s₂)})`, with
  `P_j = γ_j ((1 - ρ) γ_j + ρ)` and `Q = (1 - ρ) γ₁ γ₂`.
* `isMetric_tieMetric`, `nmscCF_tieMetric`: at the parameters `tieMetric`, with hybrid arcs of length `0` and
  `t = log (1 + (1 - ρ) γ₁ γ₂ (1 - e^{-(s₁ + s₂)}))`, all three concordance factors are `1/3`, for any `0 ≤ ρ < 1`.
* `remark3_3_strict`: the counterexample to the non-strict reading.
-/

@[expose] public noncomputable section

open Phylogenetics Phylogenetics.RootedNetwork Phylogenetics.NMSC Finset Filter Topology
open ECToBlob.Remark52
open scoped Classical

namespace ECToBlob.Remark33Counterexample

/-- The vertices of the network: `h` is the reticulation. -/
inductive V₃ | r | x | y | h | u | a | b | c | d
  deriving DecidableEq

instance : Fintype V₃ := ⟨{.r, .x, .y, .h, .u, .a, .b, .c, .d}, fun v => by cases v <;> decide⟩

/-- The arcs of the network: `hx`, `hy` enter `h`, and `e` is the cut edge. -/
inductive E₃ | rx | ry | hx | hy | xc | yd | cut | ua | ub
  deriving DecidableEq

instance : Fintype E₃ := ⟨{.rx, .ry, .hx, .hy, .xc, .yd, .cut, .ua, .ub}, fun v => by cases v <;> decide⟩

/-- **The network with a 3₂-cycle.** -/
def cycleNet : RootedNetwork V₃ E₃ (Fin 4) where
  graph :=
    { source := fun
        | .rx => .r | .ry => .r | .hx => .x | .hy => .y | .xc => .x | .yd => .y | .cut => .h | .ua => .u
        | .ub => .u
      target := fun
        | .rx => .x | .ry => .y | .hx => .h | .hy => .h | .xc => .c | .yd => .d | .cut => .u | .ua => .a
        | .ub => .b }
  root := .r
  leaf := ![.a, .b, .c, .d]

/-- It is a phylogenetic network. -/
theorem isPhylogenetic_cycleNet : cycleNet.IsPhylogenetic := by
  refine isPhylogenetic_of_rank (fun | .r => 0 | .x => 1 | .y => 1 | .h => 2 | .u => 3 | _ => 4)
    (fun f => by cases f <;> decide)
    (fun f => by cases f <;> decide) (fun v hv => ?_) ?_ (fun x => ?_) (fun x f => ?_) (fun v hv => ?_)
  · cases v
    · exact absurd rfl hv
    · exact ⟨.rx, rfl⟩
    · exact ⟨.ry, rfl⟩
    · exact ⟨.hx, rfl⟩
    · exact ⟨.cut, rfl⟩
    · exact ⟨.ua, rfl⟩
    · exact ⟨.ub, rfl⟩
    · exact ⟨.xc, rfl⟩
    · exact ⟨.yd, rfl⟩
  · decide
  · fin_cases x
    · exact ⟨.ua, rfl, fun f hf => by cases f <;> first | rfl | exact absurd hf (by decide)⟩
    · exact ⟨.ub, rfl, fun f hf => by cases f <;> first | rfl | exact absurd hf (by decide)⟩
    · exact ⟨.xc, rfl, fun f hf => by cases f <;> first | rfl | exact absurd hf (by decide)⟩
    · exact ⟨.yd, rfl, fun f hf => by cases f <;> first | rfl | exact absurd hf (by decide)⟩
  · fin_cases x <;> cases f <;> decide
  · cases v
    · exact ⟨.rx, rfl⟩
    · exact ⟨.hx, rfl⟩
    · exact ⟨.hy, rfl⟩
    · exact ⟨.cut, rfl⟩
    · exact ⟨.ua, rfl⟩
    · exact absurd rfl (hv 0)
    · exact absurd rfl (hv 1)
    · exact absurd rfl (hv 2)
    · exact absurd rfl (hv 3)

/-- The arc `e` is a cut edge, with `a`, `b` on one side. -/
theorem hasCutSplit_cycleNet : cycleNet.HasCutSplit (({0, 1} : Finset (Fin 4)) : Set (Fin 4)) := by
  refine ⟨.cut, {v | v = .u ∨ v = .a ∨ v = .b}, fun f => ?_, ?_⟩
  · cases f <;> simp [DirectedMultigraph.Crosses, cycleNet]
  · ext x
    fin_cases x <;> simp [cycleNet]

theorem isBridge_e : cycleNet.graph.underlying.IsBridge .cut := by
  refine (DirectedMultigraph.isBridge_iff _ _).2 ⟨{v | v = .u ∨ v = .a ∨ v = .b}, fun f => ?_⟩
  cases f <;> simp [DirectedMultigraph.Crosses, cycleNet]

/-- The tree of blobs displays `ab|cd`. -/
theorem displays_treeOfBlobs_abcd : Displays (treeOfBlobs cycleNet) abcd := by
  refine ⟨{0, 1}, mem_filter.2 ⟨mem_univ _, by decide, by decide, hasCutSplit_cycleNet⟩, ?_⟩
  rw [taxa_eq_univ, inter_univ]
  simp [abcd]

theorem inducedCutSplit_abcd : InducedCutSplit cycleNet abcd :=
  inducedCutSplit_of_displays_treeOfBlobs isPhylogenetic_cycleNet displays_treeOfBlobs_abcd

/-- The degree of a vertex, by counting. -/
private theorem ncard_filter {α : Type*} [Fintype α] (p : α → Prop) [DecidablePred p] :
    {a | p a}.ncard = #(univ.filter p) := by
  rw [← Set.ncard_coe_finset]
  congr 1
  ext a
  simp

/-- The network is binary, as Definition 2 of [8] asks. -/
theorem isBinary_cycleNet : cycleNet.IsBinary := by
  refine ⟨?_, fun v hv hout => ?_⟩
  · unfold DirectedMultigraph.outdegree
    rw [ncard_filter]
    decide
  · unfold DirectedMultigraph.outdegree at hout
    unfold DirectedMultigraph.indegree DirectedMultigraph.outdegree
    rw [ncard_filter] at hout
    rw [ncard_filter, ncard_filter]
    revert hv hout
    cases v <;> decide

/-! ### Where the lineages go -/

section Chain

variable {θ : MetricData E₃} {ρ : ℝ}

local notation "inj₃" => taxaInj cycleNet (univ : Finset (Fin 4))

/-- The vertices below the cycle. -/
abbrev D₂ : Finset V₃ := {.h, .u, .a, .b, .c, .d}

/-- The forests `F` at `x` and `G` at `y`. -/
def twoInj (F G : Finset (Finset (Fin 4))) : V₃ → Finset (Finset (Fin 4)) := fun
  | .x => F
  | .y => G
  | _ => ∅

theorem validInj_twoInj {F G : Finset (Finset (Fin 4))} (hF : IsGoodForest F) (hG : IsGoodForest G)
    (hd : Disjoint (lineages F) (lineages G)) : ValidInj (twoInj F G) := by
  refine ⟨fun v => ?_, fun p v huv => ?_⟩
  · cases v <;> first | exact hF | exact hG | exact isGoodForest_empty
  · cases p <;> cases v <;> first
      | exact absurd rfl huv
      | exact hd
      | exact hd.symm
      | simp [twoInj]

/-- A filter of all the elements, for any instance. -/
private theorem filter_eq_of {α : Type*} [Fintype α] {p : α → Prop} (inst : DecidablePred p) {S : Finset α}
    (h : ∀ a, p a ↔ a ∈ S) : @Finset.filter α p inst univ = S := by
  ext a
  rw [mem_filter, h]
  simp

/-- The lineages in `D₂` lifted to `x` and `y`. -/
theorem liftSet_D₂ (τ : E₃ → Finset (Finset (Fin 4))) :
    liftSet cycleNet D₂ inj₃ τ = twoInj (τ .hx ∪ τ .xc) (τ .hy ∪ τ .yd) := by
  funext v
  unfold liftSet
  cases v
  · rw [ite_eq_right (by decide), taxaInj_eq_empty (by decide),
      filter_eq_of _ (S := ∅) fun f => by cases f <;> decide]
    simp [twoInj]
  · rw [ite_eq_right (by decide), taxaInj_eq_empty (by decide),
      filter_eq_of _ (S := {.hx, .xc}) fun f => by cases f <;> decide]
    simp [twoInj, biUnion_insert]
  · rw [ite_eq_right (by decide), taxaInj_eq_empty (by decide),
      filter_eq_of _ (S := {.hy, .yd}) fun f => by cases f <;> decide]
    simp [twoInj, biUnion_insert]
  all_goals rw [ite_eq_left (by decide)]; rfl

/-- The Markov property as a mean. -/
theorem cherryMass_eq_meanOn_lift {V E X : Type*} [Fintype V] [Fintype E] [Fintype X] [DecidableEq X]
    {N : RootedNetwork V E X} {θ : MetricData E} {ρ : ℝ} (hN : N.IsPhylogenetic) (hθ : N.IsNormalized θ)
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

theorem target_u {f : E₃} : cycleNet.graph.target f = .u → f = .cut := by
  cases f <;> decide

theorem target_x {f : E₃} : cycleNet.graph.target f = .x → f = .rx := by
  cases f <;> decide

theorem target_y {f : E₃} : cycleNet.graph.target f = .y → f = .ry := by
  cases f <;> decide

theorem target_h (f : E₃) : cycleNet.graph.target f = .h → f = .hx ∨ f = .hy := by
  cases f <;> decide

theorem arriving_u (top : E₃ → Finset (Finset (Fin 4))) : arriving cycleNet inj₃ top .u = top .ua ∪ top .ub := by
  rw [arriving_eq_biUnion (S := {.ua, .ub}) (fun f => by cases f <;> decide),
    taxaInj_eq_empty (by decide)]
  simp [biUnion_insert]

theorem arriving_h (top : E₃ → Finset (Finset (Fin 4))) : arriving cycleNet inj₃ top .h = top .cut := by
  rw [arriving_eq_biUnion (S := {.cut}) (fun f => by cases f <;> decide),
    taxaInj_eq_empty (by decide)]
  simp

theorem step_u (hθ : cycleNet.IsMetric θ) (hρ : 0 ≤ ρ) (Φ : (E₃ → Finset (Finset (Fin 4))) → ℝ)
    (top : E₃ → Finset (Finset (Fin 4))) (h : top .ua ∪ top .ub = Fab) :
    stepKernel cycleNet θ ρ inj₃ .u Φ top =
      Real.exp (-θ.length .cut) * Φ (ow (arcsInto cycleNet .u) top fun _ => Fab) +
        (1 - Real.exp (-θ.length .cut)) * Φ (ow (arcsInto cycleNet .u) top fun _ => Cab) := by
  unfold stepKernel
  rw [arriving_u, h]
  exact stepOf_unique_two (N := cycleNet) (θ := θ) (e := E₃.cut) hρ rfl (fun f => target_u)
    (hθ.2.2.1 E₃.cut (isTreeArc_of_unique fun f => target_u)) (P := {0, 1}) rfl
    (fun t => Φ (ow (arcsInto cycleNet .u) top t)) (ow_dep (arcsInto cycleNet .u) top Φ)

theorem step_h_two (Ψ : (E₃ → Finset (Finset (Fin 4))) → ℝ) (top : E₃ → Finset (Finset (Fin 4)))
    (h : top .cut = Fab) :
    stepKernel cycleNet θ ρ inj₃ .h Ψ top =
      θ.inheritance .hx * ((1 - ρ) * θ.inheritance .hx + ρ) *
          (Real.exp (-θ.length .hx) * Ψ (ow (arcsInto cycleNet .h) top (pairFn .hx Fab .hy ∅)) +
            (1 - Real.exp (-θ.length .hx)) * Ψ (ow (arcsInto cycleNet .h) top (pairFn .hx Cab .hy ∅))) +
        (1 - ρ) * θ.inheritance .hx * θ.inheritance .hy *
          Ψ (ow (arcsInto cycleNet .h) top (pairFn .hx {{0}} .hy {{1}})) +
        ((1 - ρ) * θ.inheritance .hy * θ.inheritance .hx *
            Ψ (ow (arcsInto cycleNet .h) top (pairFn .hx {{1}} .hy {{0}})) +
          θ.inheritance .hy * ((1 - ρ) * θ.inheritance .hy + ρ) *
            (Real.exp (-θ.length .hy) * Ψ (ow (arcsInto cycleNet .h) top (pairFn .hx ∅ .hy Fab)) +
              (1 - Real.exp (-θ.length .hy)) *
                Ψ (ow (arcsInto cycleNet .h) top (pairFn .hx ∅ .hy Cab)))) := by
  unfold stepKernel
  rw [arriving_h, h]
  exact stepOf_two_two (N := cycleNet) (θ := θ) (ρ := ρ) (k₁ := E₃.hx) (k₂ := E₃.hy) rfl rfl (by decide) target_h
    (x := 0) (y := 1) (by decide) (fun t => Ψ (ow (arcsInto cycleNet .h) top t))
    (ow_dep (arcsInto cycleNet .h) top Ψ)

theorem roots_Cab : roots Cab = {{0, 1}} := by
  ext A
  rw [mem_roots, mem_singleton]
  constructor
  · rintro ⟨hA, hmax⟩
    by_contra hne
    have hsub : A ⊆ {0, 1} := by
      revert hA
      revert A
      decide
    exact hne (hmax _ (mem_insert_self _ _) hsub).symm
  · rintro rfl
    refine ⟨mem_insert_self _ _, fun C hC hsub => ?_⟩
    revert C
    decide

theorem isForest_Cab : IsForest Cab := by
  unfold IsForest
  decide

theorem step_h_one (Ψ : (E₃ → Finset (Finset (Fin 4))) → ℝ) (top : E₃ → Finset (Finset (Fin 4)))
    (h : top .cut = Cab) :
    stepKernel cycleNet θ ρ inj₃ .h Ψ top =
      θ.inheritance .hx * Ψ (ow (arcsInto cycleNet .h) top (pairFn .hx Cab .hy ∅)) +
        θ.inheritance .hy * Ψ (ow (arcsInto cycleNet .h) top (pairFn .hx ∅ .hy Cab)) := by
  unfold stepKernel
  rw [arriving_h, h]
  exact stepOf_two_one (N := cycleNet) (θ := θ) (k₁ := E₃.hx) (k₂ := E₃.hy) rfl rfl (by decide) target_h
    isForest_Cab roots_Cab (fun t => Ψ (ow (arcsInto cycleNet .h) top t))
    (ow_dep (arcsInto cycleNet .h) top Ψ)

theorem arriving_x (L : V₃ → Finset (Finset (Fin 4))) (top : E₃ → Finset (Finset (Fin 4))) :
    arriving cycleNet L top .x = L .x ∪ (top .hx ∪ top .xc) := by
  rw [arriving_eq_biUnion (S := {.hx, .xc}) (fun f => by cases f <;> decide)]
  simp [biUnion_insert]

theorem arriving_y (L : V₃ → Finset (Finset (Fin 4))) (top : E₃ → Finset (Finset (Fin 4))) :
    arriving cycleNet L top .y = L .y ∪ (top .hy ∪ top .yd) := by
  rw [arriving_eq_biUnion (S := {.hy, .yd}) (fun f => by cases f <;> decide)]
  simp [biUnion_insert]

theorem arriving_r (L : V₃ → Finset (Finset (Fin 4))) (top : E₃ → Finset (Finset (Fin 4))) :
    arriving cycleNet L top cycleNet.root = L .r ∪ (top .rx ∪ top .ry) := by
  rw [arriving_eq_biUnion (S := {.rx, .ry}) (fun f => by cases f <;> decide)]
  simp [biUnion_insert]
  rfl

/-- **Two lineages at `x` and two at `y`, none from one cherry of `r`**: they reach the root apart with probability
`e^{-s₁} e^{-s₂}`, and if not, a cherry that is not one of `r` decides. -/
theorem cherryMass_twoInj_split (hθ : cycleNet.IsMetric θ) (hρ : 0 ≤ ρ ∧ ρ ≤ 1) {i j : Fin 4}
    (hi : #({i, 2} : Finset (Fin 4)) = 2) (hj : #({j, 3} : Finset (Fin 4)) = 2)
    (hd : Disjoint (lineages (({i, 2} : Finset (Fin 4)).image fun x => ({x} : Finset (Fin 4))))
      (lineages (({j, 3} : Finset (Fin 4)).image fun x => ({x} : Finset (Fin 4)))))
    (hall : (({i, 2} : Finset (Fin 4)).image fun x => ({x} : Finset (Fin 4))) ∪
      (({j, 3} : Finset (Fin 4)).image fun x => ({x} : Finset (Fin 4))) = Fall)
    (hg₁ : IsGoodForest (insert ({i, 2} : Finset (Fin 4)) (({i, 2} : Finset (Fin 4)).image fun x => ({x} : Finset (Fin 4))) ∪
      (({j, 3} : Finset (Fin 4)).image fun x => ({x} : Finset (Fin 4)))))
    (hg₂ : IsGoodForest ((({i, 2} : Finset (Fin 4)).image fun x => ({x} : Finset (Fin 4))) ∪
      insert ({j, 3} : Finset (Fin 4)) (({j, 3} : Finset (Fin 4)).image fun x => ({x} : Finset (Fin 4)))))
    (hg₃ : IsGoodForest (insert ({i, 2} : Finset (Fin 4)) (({i, 2} : Finset (Fin 4)).image fun x => ({x} : Finset (Fin 4))) ∪
      insert ({j, 3} : Finset (Fin 4)) (({j, 3} : Finset (Fin 4)).image fun x => ({x} : Finset (Fin 4)))))
    (hn₁ : ({i, 2} : Finset (Fin 4)) ∉ abcd.val) (hn₂ : ({j, 3} : Finset (Fin 4)) ∉ abcd.val) :
    cherryMass cycleNet θ ρ (twoInj (({i, 2} : Finset (Fin 4)).image fun x => ({x} : Finset (Fin 4)))
      (({j, 3} : Finset (Fin 4)).image fun x => ({x} : Finset (Fin 4)))) abcd =
      Real.exp (-θ.length .rx) * Real.exp (-θ.length .ry) * (1 / 3) := by
  have hN := isPhylogenetic_cycleNet
  set Fx : Finset (Finset (Fin 4)) := ({i, 2} : Finset (Fin 4)).image fun x => ({x} : Finset (Fin 4)) with hFx
  set Fy : Finset (Finset (Fin 4)) := ({j, 3} : Finset (Fin 4)).image fun x => ({x} : Finset (Fin 4)) with hFy
  have hv : ValidInj (twoInj Fx Fy) :=
    validInj_twoInj (isGoodForest_singletons _) (isGoodForest_singletons _) hd
  rw [cherryMass_eq_sum_rootMass]
  have hmean := meanOn_of_forall_ne (N := cycleNet) (θ := θ) (ρ := ρ) hN (twoInj Fx Fy)
    (D := insert V₃.x (insert V₃.y D₂)) (fun v => by cases v <;> decide)
    (fun top => rootMass abcd (arriving cycleNet (twoInj Fx Fy) top cycleNet.root))
  rw [← hmean, meanOn_insert (fun f => by cases f <;> decide) (by decide) (fun f => by cases f <;> decide),
    meanOn_insert (fun f => by cases f <;> decide) (by decide) (fun f => by cases f <;> decide)]
  refine meanOn_eq_const hN hθ.isNormalized hρ.1 hv (fun f => by cases f <;> decide) (by decide)
    fun bot top h => ?_
  have hemp : ∀ f, cycleNet.graph.target f ∈ D₂ → top f = ∅ := fun f hf =>
    top_eq_empty_of_inj_empty hN (fun f => by cases f <;> decide) hv
      (fun w hw => by cases w <;> first | rfl | exact absurd hw (by decide)) h hf
  have hrx : ∀ τ : E₃ → Finset (Finset (Fin 4)), rootMass abcd
      (arriving cycleNet (twoInj Fx Fy) τ cycleNet.root) = rootMass abcd (τ .rx ∪ τ .ry) := fun τ => by
    rw [arriving_r]
    simp [twoInj]
  have hinhx : θ.inheritance .rx = 1 := hθ.2.2.1 .rx (isTreeArc_of_unique fun f => target_x)
  have hinhy : θ.inheritance .ry = 1 := hθ.2.2.1 .ry (isTreeArc_of_unique fun f => target_y)
  have hstepx : ∀ (Φ : (E₃ → Finset (Finset (Fin 4))) → ℝ) (t : E₃ → Finset (Finset (Fin 4))),
      t .hx = ∅ → t .xc = ∅ → stepKernel cycleNet θ ρ (twoInj Fx Fy) .x Φ t =
        Real.exp (-θ.length .rx) * Φ (ow (arcsInto cycleNet .x) t fun _ => Fx) +
          (1 - Real.exp (-θ.length .rx)) * Φ (ow (arcsInto cycleNet .x) t fun _ => insert {i, 2} Fx) := by
    intro Φ t h₁ h₂
    unfold stepKernel
    rw [arriving_x, h₁, h₂]
    simp only [twoInj, union_empty]
    exact stepOf_unique_two (N := cycleNet) (θ := θ) (e := E₃.rx) hρ.1 rfl (fun f => target_x) hinhx
      (P := {i, 2}) hi (fun t' => Φ (ow (arcsInto cycleNet .x) t t')) (ow_dep (arcsInto cycleNet .x) t Φ)
  have hstepy : ∀ (Φ : (E₃ → Finset (Finset (Fin 4))) → ℝ) (t : E₃ → Finset (Finset (Fin 4))),
      t .hy = ∅ → t .yd = ∅ → stepKernel cycleNet θ ρ (twoInj Fx Fy) .y Φ t =
        Real.exp (-θ.length .ry) * Φ (ow (arcsInto cycleNet .y) t fun _ => Fy) +
          (1 - Real.exp (-θ.length .ry)) * Φ (ow (arcsInto cycleNet .y) t fun _ => insert {j, 3} Fy) := by
    intro Φ t h₁ h₂
    unfold stepKernel
    rw [arriving_y, h₁, h₂]
    simp only [twoInj, union_empty]
    exact stepOf_unique_two (N := cycleNet) (θ := θ) (e := E₃.ry) hρ.1 rfl (fun f => target_y) hinhy
      (P := {j, 3}) hj (fun t' => Φ (ow (arcsInto cycleNet .y) t t')) (ow_dep (arcsInto cycleNet .y) t Φ)
  have hyin : ∀ T, ow (arcsInto cycleNet .y) top T .hx = top .hx ∧ ow (arcsInto cycleNet .y) top T .xc = top .xc := fun T =>
    ⟨ow_of_notMem (by rw [mem_arcsInto]; decide) _ _, ow_of_notMem (by rw [mem_arcsInto]; decide) _ _⟩
  rw [hstepy _ top (hemp _ (by decide)) (hemp _ (by decide)),
    hstepx _ _ (by rw [(hyin _).1]; exact hemp _ (by decide)) (by rw [(hyin _).2]; exact hemp _ (by decide)),
    hstepx _ _ (by rw [(hyin _).1]; exact hemp _ (by decide)) (by rw [(hyin _).2]; exact hemp _ (by decide))]
  simp only [hrx]
  have hval : ∀ (A B : Finset (Finset (Fin 4))) (T : E₃ → Finset (Finset (Fin 4))) (t : E₃ → Finset (Finset (Fin 4))),
      (∀ f, T f = A) → (∀ f, t f = B) →
      rootMass abcd (ow (arcsInto cycleNet .x) (ow (arcsInto cycleNet .y) top t) T .rx ∪
        ow (arcsInto cycleNet .x) (ow (arcsInto cycleNet .y) top t) T .ry) = rootMass abcd (A ∪ B) := by
    intro A B T t hT ht
    have h₁ : E₃.rx ∈ arcsInto cycleNet .x := mem_arcsInto.2 rfl
    have h₂ : E₃.ry ∈ arcsInto cycleNet .y := mem_arcsInto.2 rfl
    have h₃ : E₃.ry ∉ arcsInto cycleNet .x := by
      rw [mem_arcsInto]
      decide
    rw [ow_of_mem h₁, ow_of_notMem h₃, ow_of_mem h₂, hT, ht]
  rw [hval Fx Fy _ _ (fun _ => rfl) (fun _ => rfl), hval (insert {i, 2} Fx) Fy _ _ (fun _ => rfl) (fun _ => rfl),
    hval Fx (insert {j, 3} Fy) _ _ (fun _ => rfl) (fun _ => rfl),
    hval (insert {i, 2} Fx) (insert {j, 3} Fy) _ _ (fun _ => rfl) (fun _ => rfl)]
  have hsub : ∀ C : Finset (Fin 4), C ⊆ abcd.taxa := fun C => by
    rw [taxa_eq_univ]
    exact subset_univ _
  rw [hall, rootMass_all hN hθ hρ,
    rootMass_of_mem hN hθ hρ hg₁ (C := {i, 2}) (mem_union_left _ (mem_insert_self _ _)) hi (hsub _),
    rootMass_of_mem hN hθ hρ hg₂ (C := {j, 3}) (mem_union_right _ (mem_insert_self _ _)) hj (hsub _),
    rootMass_of_mem hN hθ hρ hg₃ (C := {i, 2}) (mem_union_left _ (mem_insert_self _ _)) hi (hsub _),
    ite_eq_right hn₁, ite_eq_right hn₂]
  ring

/-- Three lineages at `x`. -/
theorem cherryMass_three_x (hθ : cycleNet.IsMetric θ) (hρ : 0 ≤ ρ ∧ ρ ≤ 1) :
    cherryMass cycleNet θ ρ (twoInj (Fab ∪ {{2}}) (∅ ∪ {{3}})) abcd = 1 / 3 := by
  have heq : twoInj (Fab ∪ {{2}}) (∅ ∪ {{3}}) = placeInj univ ![V₃.x, .x, .x, .y] := by
    funext v
    unfold placeInj
    cases v
    · rw [filter_eq_of _ (S := ∅) fun a => by fin_cases a <;> decide]; rfl
    · rw [filter_eq_of _ (S := {0, 1, 2}) fun a => by fin_cases a <;> decide]; decide
    · rw [filter_eq_of _ (S := {3}) fun a => by fin_cases a <;> decide]; decide
    all_goals rw [filter_eq_of _ (S := ∅) fun a => by fin_cases a <;> decide]; rfl
  rw [heq]
  exact cherryMass_placeInj_eq_third isPhylogenetic_cycleNet hθ hρ (q := univ) rfl (a := 3) (mem_univ _)
    (v := .x) (fun a _ ha => by fin_cases a <;> first | rfl | exact absurd rfl ha)
    (by rw [mem_treesOn, taxa_eq_univ])

/-- Three lineages at `y`. -/
theorem cherryMass_three_y (hθ : cycleNet.IsMetric θ) (hρ : 0 ≤ ρ ∧ ρ ≤ 1) :
    cherryMass cycleNet θ ρ (twoInj (∅ ∪ {{2}}) (Fab ∪ {{3}})) abcd = 1 / 3 := by
  have heq : twoInj (∅ ∪ {{2}}) (Fab ∪ {{3}}) = placeInj univ ![V₃.y, .y, .x, .y] := by
    funext v
    unfold placeInj
    cases v
    · rw [filter_eq_of _ (S := ∅) fun a => by fin_cases a <;> decide]; rfl
    · rw [filter_eq_of _ (S := {2}) fun a => by fin_cases a <;> decide]; decide
    · rw [filter_eq_of _ (S := {0, 1, 3}) fun a => by fin_cases a <;> decide]; decide
    all_goals rw [filter_eq_of _ (S := ∅) fun a => by fin_cases a <;> decide]; rfl
  rw [heq]
  exact cherryMass_placeInj_eq_third isPhylogenetic_cycleNet hθ hρ (q := univ) rfl (a := 2) (mem_univ _)
    (v := .y) (fun a _ ha => by fin_cases a <;> first | rfl | exact absurd rfl ha)
    (by rw [mem_treesOn, taxa_eq_univ])

/-- The cherry of `a`, `b` decides. -/
theorem cherryMass_cherry {F G : Finset (Finset (Fin 4))} (hθ : cycleNet.IsMetric θ) (hρ : 0 ≤ ρ ∧ ρ ≤ 1)
    (hF : IsGoodForest F) (hG : IsGoodForest G) (hd : Disjoint (lineages F) (lineages G))
    (hC : ({0, 1} : Finset (Fin 4)) ∈ F ∨ ({0, 1} : Finset (Fin 4)) ∈ G) :
    cherryMass cycleNet θ ρ (twoInj F G) abcd = 1 := by
  have hv := validInj_twoInj hF hG hd
  have hsub : ({0, 1} : Finset (Fin 4)) ⊆ abcd.taxa := by
    rw [taxa_eq_univ]
    exact subset_univ _
  have hm : ({0, 1} : Finset (Fin 4)) ∈ abcd.val := by decide
  rcases hC with hC | hC
  · rw [cherryMass_of_mem isPhylogenetic_cycleNet hθ hρ hv (v := .x) hC rfl hsub, ite_eq_left hm]
  · rw [cherryMass_of_mem isPhylogenetic_cycleNet hθ hρ hv (v := .y) hC rfl hsub, ite_eq_left hm]

/-- **The concordance factor of `ab|cd`**, as in Example 1 of [8]. -/
theorem nmscCF_cycleNet_abcd (hθ : cycleNet.IsMetric θ) (hρ : 0 ≤ ρ ∧ ρ ≤ 1) :
    nmscCF cycleNet θ ρ abcd =
      (1 - Real.exp (-θ.length .cut)) + Real.exp (-θ.length .cut) *
        (θ.inheritance .hx * ((1 - ρ) * θ.inheritance .hx + ρ) * (1 - 2 / 3 * Real.exp (-θ.length .hx)) +
          θ.inheritance .hy * ((1 - ρ) * θ.inheritance .hy + ρ) * (1 - 2 / 3 * Real.exp (-θ.length .hy)) +
          2 / 3 * ((1 - ρ) * θ.inheritance .hx * θ.inheritance .hy) *
            (Real.exp (-θ.length .rx) * Real.exp (-θ.length .ry))) := by
  have hN := isPhylogenetic_cycleNet
  have hs : θ.inheritance .hx + θ.inheritance .hy = 1 :=
    inheritance_add_eq_one hθ.isNormalized (k₁ := E₃.hx) (k₂ := E₃.hy) (v := V₃.h) rfl rfl (by decide) target_h
  rw [nmscCF_eq_cherryMass hN hθ hρ abcd, taxa_eq_univ,
    cherryMass_eq_meanOn_lift hN hθ.isNormalized hρ.1 (validInj_taxaInj univ) (D := D₂)
      (fun f => by cases f <;> decide) (by decide) abcd]
  unfold D₂
  rw [meanOn_insert (fun f => by cases f <;> decide) (by decide) (fun f => by cases f <;> decide),
    meanOn_insert (fun f => by cases f <;> decide) (by decide) (fun f => by cases f <;> decide)]
  refine meanOn_eq_const hN hθ.isNormalized hρ.1 (validInj_taxaInj univ)
    (fun f => by cases f <;> decide) (by decide) fun bot top h => ?_
  have hua := top_eq_of_leaf hN 0 (p := E₃.ua) (fun f => by cases f <;> decide) rfl
    (fun f => by cases f <;> decide) (by decide) h
  have hub := top_eq_of_leaf hN 1 (p := E₃.ub) (fun f => by cases f <;> decide) rfl
    (fun f => by cases f <;> decide) (by decide) h
  have hxc := top_eq_of_leaf hN 2 (p := E₃.xc) (fun f => by cases f <;> decide) rfl
    (fun f => by cases f <;> decide) (by decide) h
  have hyd := top_eq_of_leaf hN 3 (p := E₃.yd) (fun f => by cases f <;> decide) rfl
    (fun f => by cases f <;> decide) (by decide) h
  have hcutm : E₃.cut ∈ arcsInto cycleNet .u := mem_arcsInto.2 rfl
  have hΨ : ∀ (A B : Finset (Finset (Fin 4))) (T : E₃ → Finset (Finset (Fin 4))),
      cherryMass cycleNet θ ρ (liftSet cycleNet {.h, .u, .a, .b, .c, .d} inj₃
        (ow (arcsInto cycleNet .h) (ow (arcsInto cycleNet .u) top T) (pairFn .hx A .hy B))) abcd =
      cherryMass cycleNet θ ρ (twoInj (A ∪ {{2}}) (B ∪ {{3}})) abcd := by
    intro A B T
    have h₁ : E₃.hx ∈ arcsInto cycleNet .h := mem_arcsInto.2 rfl
    have h₂ : E₃.hy ∈ arcsInto cycleNet .h := mem_arcsInto.2 rfl
    have h₃ : E₃.xc ∉ arcsInto cycleNet .h := by rw [mem_arcsInto]; decide
    have h₄ : E₃.yd ∉ arcsInto cycleNet .h := by rw [mem_arcsInto]; decide
    have h₅ : E₃.xc ∉ arcsInto cycleNet .u := by rw [mem_arcsInto]; decide
    have h₆ : E₃.yd ∉ arcsInto cycleNet .u := by rw [mem_arcsInto]; decide
    have hl := liftSet_D₂ (ow (arcsInto cycleNet .h) (ow (arcsInto cycleNet .u) top T) (pairFn .hx A .hy B))
    unfold D₂ at hl
    rw [hl, ow_of_mem h₁, ow_of_mem h₂, ow_of_notMem h₃, ow_of_notMem h₄, ow_of_notMem h₅, ow_of_notMem h₆,
      pairFn_left, pairFn_right (by decide), hxc, hyd]
  have hτ : ∀ T : E₃ → Finset (Finset (Fin 4)), ow (arcsInto cycleNet .u) top T .cut = T .cut := fun T =>
    ow_of_mem hcutm _ _
  rw [step_u hθ hρ.1 _ top (by rw [hua, hub]; decide), step_h_two _ _ (hτ _), step_h_one _ _ (hτ _)]
  simp only [hΨ]
  have hE : ∀ {i j : Fin 4}, (i, j) = (0, 1) ∨ (i, j) = (1, 0) →
      cherryMass cycleNet θ ρ (twoInj ({{i}} ∪ {{2}}) ({{j}} ∪ {{3}})) abcd =
        Real.exp (-θ.length .rx) * Real.exp (-θ.length .ry) * (1 / 3) := by
    rintro i j (h' | h') <;> obtain ⟨rfl, rfl⟩ := Prod.mk.inj h'
    · have e₁ : ({{0}} ∪ {{2}} : Finset (Finset (Fin 4))) = ({0, 2} : Finset (Fin 4)).image fun x => ({x} : Finset (Fin 4)) := by decide
      have e₂ : ({{1}} ∪ {{3}} : Finset (Finset (Fin 4))) = ({1, 3} : Finset (Fin 4)).image fun x => ({x} : Finset (Fin 4)) := by decide
      rw [e₁, e₂]
      refine cherryMass_twoInj_split hθ hρ (by decide) (by decide) (by decide) (by decide) ?_ ?_ ?_ (by decide) (by decide)
      all_goals (unfold IsGoodForest IsForest IsBinaryForest; decide)
    · have e₁ : ({{1}} ∪ {{2}} : Finset (Finset (Fin 4))) = ({1, 2} : Finset (Fin 4)).image fun x => ({x} : Finset (Fin 4)) := by decide
      have e₂ : ({{0}} ∪ {{3}} : Finset (Finset (Fin 4))) = ({0, 3} : Finset (Fin 4)).image fun x => ({x} : Finset (Fin 4)) := by decide
      rw [e₁, e₂]
      refine cherryMass_twoInj_split hθ hρ (by decide) (by decide) (by decide) (by decide) ?_ ?_ ?_ (by decide) (by decide)
      all_goals (unfold IsGoodForest IsForest IsBinaryForest; decide)
  have hC₁ : cherryMass cycleNet θ ρ (twoInj (Cab ∪ {{2}}) (∅ ∪ {{3}})) abcd = 1 :=
    cherryMass_cherry hθ hρ (by unfold IsGoodForest IsForest IsBinaryForest; decide)
      (by unfold IsGoodForest IsForest IsBinaryForest; decide) (by decide) (Or.inl (by decide))
  have hC₂ : cherryMass cycleNet θ ρ (twoInj (∅ ∪ {{2}}) (Cab ∪ {{3}})) abcd = 1 :=
    cherryMass_cherry hθ hρ (by unfold IsGoodForest IsForest IsBinaryForest; decide)
      (by unfold IsGoodForest IsForest IsBinaryForest; decide) (by decide) (Or.inr (by decide))
  rw [cherryMass_three_x hθ hρ, cherryMass_three_y hθ hρ, hC₁, hC₂, hE (Or.inl rfl), hE (Or.inr rfl)]
  have e : θ.inheritance .hy = 1 - θ.inheritance .hx := by linarith
  rw [e]
  ring

end Chain

/-! ### The point where all three concordance factors are `1/3` -/

section Tie

variable {ρ γ s₁ s₂ : ℝ}

/-- The parameters of the tie: length `0` on the hybrid arcs, `s₁`, `s₂` on the arcs from the root, and on the cut
edge the length where the concordance factor of `ab|cd` is `1/3`. -/
def tieMetric (ρ γ s₁ s₂ : ℝ) : MetricData E₃ where
  length := fun
    | .rx => s₁
    | .ry => s₂
    | .hx => 0
    | .hy => 0
    | .cut => Real.log (1 + (1 - ρ) * γ * (1 - γ) * (1 - Real.exp (-(s₁ + s₂))))
    | _ => 1
  inheritance := fun
    | .hx => γ
    | .hy => 1 - γ
    | _ => 1

/-- The quantity `(1 - ρ) γ₁ γ₂ (1 - e^{-s₀})`, which makes the cut edge positive. -/
theorem tie_pos (hρ₁ : ρ < 1) (hγ₀ : 0 < γ) (hγ₁ : γ < 1) (hs₁ : 0 < s₁) (hs₂ : 0 < s₂) :
    0 < (1 - ρ) * γ * (1 - γ) * (1 - Real.exp (-(s₁ + s₂))) := by
  have h : Real.exp (-(s₁ + s₂)) < 1 := Real.exp_lt_one_iff.2 (by linarith)
  have h₁ : 0 < 1 - ρ := by linarith
  have h₂ : 0 < 1 - γ := by linarith
  have h₃ : 0 < 1 - Real.exp (-(s₁ + s₂)) := by linarith
  positivity

theorem indegree_cycleNet (v : V₃) :
    cycleNet.graph.indegree v = match v with
      | .r => 0
      | .h => 2
      | _ => 1 := by
  unfold DirectedMultigraph.indegree
  rw [ncard_filter]
  cases v <;> decide

/-- **The parameters of the tie are valid.** -/
theorem isMetric_tieMetric (hρ₁ : ρ < 1) (hγ₀ : 0 < γ) (hγ₁ : γ < 1) (hs₁ : 0 < s₁) (hs₂ : 0 < s₂) :
    cycleNet.IsMetric (tieMetric ρ γ s₁ s₂) := by
  have hcut : 0 < Real.log (1 + (1 - ρ) * γ * (1 - γ) * (1 - Real.exp (-(s₁ + s₂)))) :=
    Real.log_pos (by linarith [tie_pos hρ₁ hγ₀ hγ₁ hs₁ hs₂])
  have hnt : ∀ f, cycleNet.IsTreeArc f → f ≠ .hx ∧ f ≠ .hy := by
    rintro f hf
    unfold RootedNetwork.IsTreeArc at hf
    rw [indegree_cycleNet] at hf
    constructor <;> rintro rfl <;> exact absurd hf (by decide)
  have hth : ∀ f, cycleNet.IsHybridArc f → f = .hx ∨ f = .hy := by
    rintro f hf
    unfold RootedNetwork.IsHybridArc at hf
    rw [indegree_cycleNet] at hf
    revert hf
    cases f <;> decide
  refine ⟨fun f hf => ?_, fun f hf => ?_, fun f hf => ?_, fun f hf => ?_, fun v hv => ?_⟩
  · obtain ⟨h₁, h₂⟩ := hnt f hf
    cases f
    · exact hs₁
    · exact hs₂
    · exact absurd rfl h₁
    · exact absurd rfl h₂
    · exact one_pos
    · exact one_pos
    · exact hcut
    · exact one_pos
    · exact one_pos
  · rcases hth f hf with rfl | rfl <;> exact le_rfl
  · obtain ⟨h₁, h₂⟩ := hnt f hf
    cases f <;> first | rfl | exact absurd rfl h₁ | exact absurd rfl h₂
  · rcases hth f hf with rfl | rfl
    · exact hγ₀
    · exact sub_pos.2 hγ₁
  · rw [indegree_cycleNet] at hv
    have hvh : v = .h := by
      revert hv
      cases v <;> decide
    subst hvh
    rw [sum_ite_target_pair _ (v := V₃.h) (k₁ := E₃.hx) (k₂ := E₃.hy) rfl rfl (by decide) target_h]
    change γ + (1 - γ) = 1
    ring

/-- **At the parameters of the tie, the concordance factor of `ab|cd` is `1/3`.** -/
theorem nmscCF_tieMetric_abcd (hρ₀ : 0 ≤ ρ) (hρ₁ : ρ < 1) (hγ₀ : 0 < γ) (hγ₁ : γ < 1) (hs₁ : 0 < s₁) (hs₂ : 0 < s₂) :
    nmscCF cycleNet (tieMetric ρ γ s₁ s₂) ρ abcd = 1 / 3 := by
  rw [nmscCF_cycleNet_abcd (isMetric_tieMetric hρ₁ hγ₀ hγ₁ hs₁ hs₂) ⟨hρ₀, hρ₁.le⟩]
  set Q := (1 - ρ) * γ * (1 - γ) * (1 - Real.exp (-(s₁ + s₂))) with hQ
  have hQp : 0 < Q := tie_pos hρ₁ hγ₀ hγ₁ hs₁ hs₂
  have h1Q : 0 < 1 + Q := by linarith
  have hcut : Real.exp (-(tieMetric ρ γ s₁ s₂).length .cut) = (1 + Q)⁻¹ := by
    change Real.exp (-Real.log (1 + Q)) = _
    rw [Real.exp_neg, Real.exp_log h1Q]
  have hx : Real.exp (-(tieMetric ρ γ s₁ s₂).length .hx) = 1 := by
    change Real.exp (-0) = 1
    simp
  have hy : Real.exp (-(tieMetric ρ γ s₁ s₂).length .hy) = 1 := by
    change Real.exp (-0) = 1
    simp
  have hee : Real.exp (-(tieMetric ρ γ s₁ s₂).length .rx) * Real.exp (-(tieMetric ρ γ s₁ s₂).length .ry) =
      Real.exp (-(s₁ + s₂)) := by
    change Real.exp (-s₁) * Real.exp (-s₂) = _
    rw [← Real.exp_add]
    congr 1
    ring
  have hγx : (tieMetric ρ γ s₁ s₂).inheritance .hx = γ := rfl
  have hγy : (tieMetric ρ γ s₁ s₂).inheritance .hy = 1 - γ := rfl
  rw [hcut, hx, hy, hee, hγx, hγy]
  field_simp
  rw [hQ]
  ring

/-- **At the parameters of the tie, all three concordance factors are `1/3`.** -/
theorem nmscCF_tieMetric (hρ₀ : 0 ≤ ρ) (hρ₁ : ρ < 1) (hγ₀ : 0 < γ) (hγ₁ : γ < 1) (hs₁ : 0 < s₁) (hs₂ : 0 < s₂)
    (r : QuartetTree (Fin 4)) : nmscCF cycleNet (tieMetric ρ γ s₁ s₂) ρ r = 1 / 3 := by
  by_cases hr : r = abcd
  · rw [hr]
    exact nmscCF_tieMetric_abcd hρ₀ hρ₁ hγ₀ hγ₁ hs₁ hs₂
  · have hm : r ∈ abcd.alternatives := QuartetTree.mem_alternatives.2
      ⟨by rw [taxa_eq_univ, taxa_eq_univ], hr⟩
    rw [nmscCF_alternative_eq isPhylogenetic_cycleNet (isMetric_tieMetric hρ₁ hγ₀ hγ₁ hs₁ hs₂).isWeakMetric
      ⟨hρ₀, hρ₁.le⟩ inducedCutSplit_abcd hm, nmscCF_tieMetric_abcd hρ₀ hρ₁ hγ₀ hγ₁ hs₁ hs₂]
    norm_num

end Tie

/-! ### All the binary trees tie -/

section Trees

/-- The rooted tree on `Fin 4` with the root split `P | Pᶜ`. -/
def quartetHierarchy (P : Finset (Fin 4)) : Finset (Finset (Fin 4)) :=
  {univ, {0}, {1}, {2}, {3}, P, Pᶜ}

theorem isBinaryTree_quartet {P : Finset (Fin 4)} (hP : P = {0, 1} ∨ P = {0, 2} ∨ P = {0, 3}) :
    IsBinaryTree (unroot (quartetHierarchy P)) := by
  refine ⟨_, ?_, rfl, ?_⟩
  · unfold IsHierarchy quartetHierarchy
    rcases hP with rfl | rfl | rfl <;> decide
  · unfold quartetHierarchy
    rcases hP with rfl | rfl | rfl <;> decide

theorem displays_quartet {P : Finset (Fin 4)} (hP : P = {0, 1} ∨ P = {0, 2} ∨ P = {0, 3})
    {s : QuartetTree (Fin 4)} (hs : P ∈ s.val) : Displays (unroot (quartetHierarchy P)) s := by
  refine ⟨P, ?_, ?_⟩
  · refine mem_unroot.2 (Or.inl ⟨?_, ?_⟩)
    · simp [quartetHierarchy]
    · rcases hP with rfl | rfl | rfl <;> decide
  · rw [taxa_eq_univ, inter_univ]
    exact hs

/-- When all weights are `1/3`, a tree has score at most `1/3`, the score of one displaying a quartet tree. -/
theorem quartetScore_of_third {p : QuartetTree (Fin 4) → ℝ} (hp : ∀ r, p r = 1 / 3) {T : Finset (Finset (Fin 4))}
    (hT : IsUnrootedTree T) :
    quartetSupport p T ≤ 1 / 3 ∧ ∀ s, Displays T s → quartetSupport p T = 1 / 3 := by
  have hval : ∀ s, Displays T s → quartetSupport p T = 1 / 3 := by
    intro s hs
    unfold quartetSupport
    rw [Finset.sum_eq_single s]
    · rw [ite_eq_left hs, hp]
    · intro r _ hne
      exact ite_eq_right fun hd => hne (hT.displays_unique hd hs (by rw [taxa_eq_univ, taxa_eq_univ]))
    · exact fun h => absurd (mem_univ _) h
  refine ⟨?_, hval⟩
  by_cases hex : ∃ s, Displays T s
  · obtain ⟨s, hs⟩ := hex
    exact (hval s hs).le
  · push Not at hex
    unfold quartetSupport
    rw [Finset.sum_eq_zero fun s _ => ite_eq_right (hex s)]
    norm_num

end Trees

/-- **Remark 3.3 needs the strict reading of "no anomalous quartets"** (`ecto:rem3_3`). For any `0 ≤ ρ < 1`, `0 < γ < 1`,
`s₁, s₂ > 0`, the binary network `cycleNet` at the valid parameters `tieMetric ρ γ s₁ s₂` has a cut edge, of positive
length, separating `a, b` from `c, d`, and all three concordance factors are `1/3`. So

* it has no anomaly in the sense of Definition 2 of [8], `P(T₁ | N) < 1/3`: the concordance factor of `ab|cd` is `1/3`,
  and so Definition 1 of [8] is not met either, no displayed tree being less probable than another tree;
* equation (3.1) fails for `ab|cd`;
* the conclusion of Theorem 3.1 fails: the binary tree `ac|bd` maximizes the score, as all three binary trees do, and
  it is not a resolution of the tree of blobs. -/
theorem remark3_3_strict {ρ γ s₁ s₂ : ℝ} (hρ₀ : 0 ≤ ρ) (hρ₁ : ρ < 1) (hγ₀ : 0 < γ) (hγ₁ : γ < 1) (hs₁ : 0 < s₁)
    (hs₂ : 0 < s₂) :
    cycleNet.IsPhylogenetic ∧ cycleNet.IsBinary ∧ cycleNet.IsMetric (tieMetric ρ γ s₁ s₂) ∧
      cycleNet.graph.underlying.IsBridge .cut ∧ 0 < (tieMetric ρ γ s₁ s₂).length .cut ∧
      Displays (treeOfBlobs cycleNet) abcd ∧
      (∀ r, nmscCF cycleNet (tieMetric ρ γ s₁ s₂) ρ r = 1 / 3) ∧
      ¬ nmscCF cycleNet (tieMetric ρ γ s₁ s₂) ρ abcd < 1 / 3 ∧
      ¬ TOBQMC.IsTQuartetNonanomalous cycleNet (nmscCF cycleNet (tieMetric ρ γ s₁ s₂) ρ) ∧
      (∀ P, (P = {0, 1} ∨ P = {0, 2} ∨ P = {0, 3}) → IsBinaryTree (unroot (quartetHierarchy P)) ∧
        ∀ T', IsUnrootedTree T' → quartetSupport (nmscCF cycleNet (tieMetric ρ γ s₁ s₂) ρ) T' ≤
          quartetSupport (nmscCF cycleNet (tieMetric ρ γ s₁ s₂) ρ) (unroot (quartetHierarchy P))) ∧
      ∃ T, IsBinaryTree T ∧ IsUnrootedTree T ∧
        (∀ T', IsUnrootedTree T' → quartetSupport (nmscCF cycleNet (tieMetric ρ γ s₁ s₂) ρ) T' ≤
          quartetSupport (nmscCF cycleNet (tieMetric ρ γ s₁ s₂) ρ) T) ∧ ¬ treeOfBlobs cycleNet ⊆ T := by
  have hθ := isMetric_tieMetric hρ₁ hγ₀ hγ₁ hs₁ hs₂
  have hp := nmscCF_tieMetric hρ₀ hρ₁ hγ₀ hγ₁ hs₁ hs₂
  have hU : ∀ {P : Finset (Fin 4)}, (P = {0, 1} ∨ P = {0, 2} ∨ P = {0, 3}) → IsUnrootedTree (unroot (quartetHierarchy P)) :=
    fun hP => by
      obtain ⟨H, hH, hu, -⟩ := isBinaryTree_quartet hP
      exact ⟨H, hH, hu⟩
  have hmem : ∀ {P : Finset (Fin 4)}, (P = {0, 1} ∨ P = {0, 2} ∨ P = {0, 3}) →
      ∃ s : QuartetTree (Fin 4), P ∈ s.val := by
    rintro P (rfl | rfl | rfl)
    · exact ⟨abcd, by decide⟩
    · exact ⟨acbd, by decide⟩
    · exact ⟨adbc, by decide⟩
  have hmax : ∀ {P : Finset (Fin 4)}, (P = {0, 1} ∨ P = {0, 2} ∨ P = {0, 3}) → ∀ T', IsUnrootedTree T' →
      quartetSupport (nmscCF cycleNet (tieMetric ρ γ s₁ s₂) ρ) T' ≤
        quartetSupport (nmscCF cycleNet (tieMetric ρ γ s₁ s₂) ρ) (unroot (quartetHierarchy P)) := by
    intro P hP T' hT'
    obtain ⟨s, hs⟩ := hmem hP
    rw [(quartetScore_of_third hp (hU hP)).2 s (displays_quartet hP hs)]
    exact (quartetScore_of_third hp hT').1
  refine ⟨isPhylogenetic_cycleNet, isBinary_cycleNet, hθ, isBridge_e,
    hθ.1 .cut (isTreeArc_of_isBridge isPhylogenetic_cycleNet isBridge_e), displays_treeOfBlobs_abcd, hp, ?_, ?_,
    fun P hP => ⟨isBinaryTree_quartet hP, hmax hP⟩, _, isBinaryTree_quartet (P := {0, 2}) (Or.inr (Or.inl rfl)),
    hU (Or.inr (Or.inl rfl)), hmax (Or.inr (Or.inl rfl)), fun hsub => ?_⟩
  · rw [hp]
    norm_num
  · intro hano
    have hm : acbd ∈ abcd.alternatives := QuartetTree.mem_alternatives.2
      ⟨by rw [taxa_eq_univ, taxa_eq_univ], by decide⟩
    have := hano abcd displays_treeOfBlobs_abcd acbd hm
    rw [hp, hp] at this
    exact lt_irrefl _ this
  · have h₁ : Displays (unroot (quartetHierarchy {0, 2})) abcd := displays_treeOfBlobs_abcd.mono hsub
    have h₂ : Displays (unroot (quartetHierarchy {0, 2})) acbd :=
      displays_quartet (Or.inr (Or.inl rfl)) (by decide)
    have := (hU (Or.inr (Or.inl rfl))).displays_unique h₁ h₂ (by rw [taxa_eq_univ, taxa_eq_univ])
    exact absurd this (by decide)

end ECToBlob.Remark33Counterexample
