module

public import ECToBlob.Remark52Networks
public import Basic.Defs
public import Phylogenetics.NMSC.Analytic
public import Phylogenetics.NMSC.Level1.Arms
public import Phylogenetics.NMSC.TreeCF
public import Phylogenetics.NMSC.Witness

/-!
# ECToBlob Remark 5.2: the degree condition of Proposition 5.1 cannot be dropped

Remark 5.2 (`ecto:remark5_2`) and the caption of Figure 1: `N₁`, `N₂` satisfy (5.2) for `ab|cd` with no cut edge for
that split, and their blobs can be replaced by an edge of length `t₀ > 0`, which gives the tree `N₀` with identical
quartet concordance factors. The networks are in `src/ECToBlob/Remark52Networks.lean`.

The paper gives no computation for `N₂`, and cites Ané et al. 2024, Example 1 for `N₁`. Here all three follow one
computation, the chain of the network multispecies coalescent from the root down, in `src/Basic/NMSCChain.lean`. Unlike a mixture
over the corners of the inheritance (`nmscCF_withPair`), this stays at valid parameters.

## Main results

Writing `cfOf P` for the concordance factors `1/3 + 2/3 P` on `ab|cd` and `(1 - P)/3` on the other two trees:

* `nmscCF_N₀`: `cfOf (1 - exp (-t₀))`.
* `nmscCF_N₁`: `cfOf (coalescence₁ θ ρ)`, with
  `P = γ ((1 - ρ) γ + ρ) (1 - exp (-t₁)) + (1 - γ) ((1 - ρ) (1 - γ) + ρ) (1 - exp (-t₂))`.
* `nmscCF_N₂`: `cfOf (γ₁ γ₂ (1 - exp (-t)))`, for all `ρ` and all lengths of the hybrid arcs.
* `isT1Strict_N₁`, `isT1Strict_N₂`: (5.2) for `ab|cd`; for `N₁` under `t₁ > 0 ∨ t₂ > 0`, and at `t₁ = t₂ = 0` the
  concordance factors are uniform (`nmscCF_N₁_of_length_zero`).
* `nmscCF_N₂_eq_N₀`, `exists_N₀_of_N₂`, `exists_N₀_of_N₁`: the replacement by an edge of positive length.
* `isMetric_metric₁`, `isMetric_metric₂`, `isMetric_metric₀`, `nmscCF_metric₁`, `nmscCF_metric₂`, `nmscCF_metric₀`: the
  parameters of the figure.
* `remark5_2_N₁`, `remark5_2_N₂`, `remark5_2`: the generic clause of Proposition 5.1 fails on a set of positive measure.
* `star_fails_N₁`: at `t₁ = t₂ = 0`, an atom of the measure of §5.1, `N₁` also fails the converse of the star clause.
-/

@[expose] public noncomputable section

open Phylogenetics Phylogenetics.RootedNetwork Phylogenetics.NMSC Phylogenetics.NMSC.Chain Finset MeasureTheory
open scoped Classical

namespace ECToBlob.Remark52

export Phylogenetics.FinFour (Fab Cab Fall)

/-! ### The concordance factors on `Fin 4` -/

/-- A filter of all the elements, by the elements. -/
theorem filter_eq_finset {α : Type*} [Fintype α] {p : α → Prop} [DecidablePred p] {S : Finset α}
    (h : ∀ a, p a ↔ a ∈ S) : univ.filter p = S := by
  ext a
  rw [mem_filter, h]
  simp

/-- The concordance factors that a coalescence of `c` and `d` with probability `P` gives. -/
def cfOf (P : ℝ) (r : QuartetTree (Fin 4)) : ℝ :=
  if ({2, 3} : Finset (Fin 4)) ∈ r.val then 1 / 3 + 2 / 3 * P else (1 - P) / 3

/-- The lineages of `c`, `d` before they coalesce. -/
abbrev Fcd : Finset (Finset (Fin 4)) := ({2, 3} : Finset (Fin 4)).image fun x => ({x} : Finset (Fin 4))

theorem isGoodForest_cherry : IsGoodForest (insert ({2, 3} : Finset (Fin 4)) Fall) := by
  unfold IsGoodForest IsForest IsBinaryForest
  decide

section RootValues

variable {V E : Type*} [Fintype V] [Fintype E] {N : RootedNetwork V E (Fin 4)} {θ : MetricData E} {ρ : ℝ}

theorem rootMass_all (hN : N.IsPhylogenetic) (hθ : N.IsMetric θ) (hρ : 0 ≤ ρ ∧ ρ ≤ 1)
    (r : QuartetTree (Fin 4)) : rootMass r Fall = 1 / 3 :=
  rootMass_singletons hN hθ hρ (q := univ) rfl (by rw [mem_treesOn, taxa_eq_univ])

theorem rootMass_cherry (hN : N.IsPhylogenetic) (hθ : N.IsMetric θ) (hρ : 0 ≤ ρ ∧ ρ ≤ 1)
    (r : QuartetTree (Fin 4)) :
    rootMass r (insert ({2, 3} : Finset (Fin 4)) Fall) =
      if ({2, 3} : Finset (Fin 4)) ∈ r.val then 1 else 0 :=
  rootMass_of_mem hN hθ hρ isGoodForest_cherry (mem_insert_self _ _) rfl
    (by rw [taxa_eq_univ]; exact subset_univ _)

end RootValues

/-! ### The network `N₂` -/

section N2

variable {θ : MetricData E₂} {ρ : ℝ}

local notation "inj₂" => taxaInj N₂ (univ : Finset (Fin 4))

theorem arriving₂_root (top : E₂ → Finset (Finset (Fin 4))) :
    arriving N₂ inj₂ top N₂.root = top .a ∪ (top .b ∪ (top .Y ∪ (top .rc ∪ top .rd))) := by
  rw [arriving_eq_biUnion (S := {.a, .b, .Y, .rc, .rd}) (fun e => by cases e <;> decide),
    taxaInj_eq_empty (by decide)]
  simp [biUnion_insert]

theorem arriving₂_Y (top : E₂ → Finset (Finset (Fin 4))) :
    arriving N₂ inj₂ top .Y = top .yc ∪ top .yd := by
  rw [arriving_eq_biUnion (S := {.yc, .yd}) (fun e => by cases e <;> decide),
    taxaInj_eq_empty (by decide)]
  simp [biUnion_insert]

theorem arriving₂_hc (top : E₂ → Finset (Finset (Fin 4))) :
    arriving N₂ inj₂ top .hc = top .c := by
  rw [arriving_eq_biUnion (S := {.c}) (fun e => by cases e <;> decide),
    taxaInj_eq_empty (by decide)]
  simp

theorem arriving₂_hd (top : E₂ → Finset (Finset (Fin 4))) :
    arriving N₂ inj₂ top .hd = top .d := by
  rw [arriving_eq_biUnion (S := {.d}) (fun e => by cases e <;> decide),
    taxaInj_eq_empty (by decide)]
  simp

/-- The forest at the root gives the mass of the quartet tree `r`. -/
def φ₂ (r : QuartetTree (Fin 4)) (top : E₂ → Finset (Finset (Fin 4))) : ℝ :=
  rootMass r (arriving N₂ inj₂ top N₂.root)

theorem target₂_Y {f : E₂} : N₂.graph.target f = .Y → f = .Y := by
  cases f <;> decide

theorem target₂_hc (f : E₂) : N₂.graph.target f = .hc → f = .yc ∨ f = .rc := by
  cases f <;> decide

theorem target₂_hd (f : E₂) : N₂.graph.target f = .hd → f = .yd ∨ f = .rd := by
  cases f <;> decide

/-- The chain at `Y`, from a forest with at most one root. -/
theorem step₂_Y_det (hθ : N₂.IsMetric θ) (hρ : 0 ≤ ρ) (φ : (E₂ → Finset (Finset (Fin 4))) → ℝ)
    (top : E₂ → Finset (Finset (Fin 4))) {F : Finset (Finset (Fin 4))}
    (h : top .yc ∪ top .yd = F) (hF : IsForest F) (hr : #(roots F) ≤ 1) :
    stepKernel N₂ θ ρ inj₂ .Y φ top = φ (ow (arcsInto N₂ .Y) top fun _ => F) := by
  unfold stepKernel
  rw [arriving₂_Y, h]
  exact stepOf_unique_det (N := N₂) (θ := θ) (e := E₂.Y) hρ rfl (fun f => target₂_Y)
    (hθ.2.2.1 E₂.Y (isTreeArc_of_unique fun f => target₂_Y)) hF hr
    (fun t => φ (ow (arcsInto N₂ .Y) top t)) (ow_dep (arcsInto N₂ .Y) top φ)

/-- The chain at `Y`, from the two lineages `c`, `d`. -/
theorem step₂_Y_two (hθ : N₂.IsMetric θ) (hρ : 0 ≤ ρ) (φ : (E₂ → Finset (Finset (Fin 4))) → ℝ)
    (top : E₂ → Finset (Finset (Fin 4))) (h : top .yc ∪ top .yd = Fcd) :
    stepKernel N₂ θ ρ inj₂ .Y φ top =
      Real.exp (-θ.length .Y) * φ (ow (arcsInto N₂ .Y) top fun _ => Fcd) +
        (1 - Real.exp (-θ.length .Y)) *
          φ (ow (arcsInto N₂ .Y) top fun _ => insert {2, 3} Fcd) := by
  unfold stepKernel
  rw [arriving₂_Y, h]
  exact stepOf_unique_two (N := N₂) (θ := θ) (e := E₂.Y) hρ rfl (fun f => target₂_Y)
    (hθ.2.2.1 E₂.Y (isTreeArc_of_unique fun f => target₂_Y)) (P := {2, 3}) rfl
    (fun t => φ (ow (arcsInto N₂ .Y) top t)) (ow_dep (arcsInto N₂ .Y) top φ)

/-- The chain at the reticulation above `c`. -/
theorem step₂_hc (φ : (E₂ → Finset (Finset (Fin 4))) → ℝ) (top : E₂ → Finset (Finset (Fin 4)))
    (h : top .c = {{2}}) :
    stepKernel N₂ θ ρ inj₂ .hc φ top =
      θ.inheritance .yc * φ (ow (arcsInto N₂ .hc) top (pairFn .yc {{2}} .rc ∅)) +
        θ.inheritance .rc * φ (ow (arcsInto N₂ .hc) top (pairFn .yc ∅ .rc {{2}})) := by
  unfold stepKernel
  rw [arriving₂_hc, h]
  exact stepOf_two_one (N := N₂) (θ := θ) (k₁ := E₂.yc) (k₂ := E₂.rc) rfl rfl (by decide) target₂_hc
    (isForest_singleton_singleton 2) (roots_singleton_singleton 2)
    (fun t => φ (ow (arcsInto N₂ .hc) top t)) (ow_dep (arcsInto N₂ .hc) top φ)

/-- The chain at the reticulation above `d`. -/
theorem step₂_hd (φ : (E₂ → Finset (Finset (Fin 4))) → ℝ) (top : E₂ → Finset (Finset (Fin 4)))
    (h : top .d = {{3}}) :
    stepKernel N₂ θ ρ inj₂ .hd φ top =
      θ.inheritance .yd * φ (ow (arcsInto N₂ .hd) top (pairFn .yd {{3}} .rd ∅)) +
        θ.inheritance .rd * φ (ow (arcsInto N₂ .hd) top (pairFn .yd ∅ .rd {{3}})) := by
  unfold stepKernel
  rw [arriving₂_hd, h]
  exact stepOf_two_one (N := N₂) (θ := θ) (k₁ := E₂.yd) (k₂ := E₂.rd) rfl rfl (by decide) target₂_hd
    (isForest_singleton_singleton 3) (roots_singleton_singleton 3)
    (fun t => φ (ow (arcsInto N₂ .hd) top t)) (ow_dep (arcsInto N₂ .hd) top φ)

theorem Y_mem_arcsInto : E₂.Y ∈ arcsInto N₂ V₂.Y := mem_arcsInto.2 rfl

theorem φ₂_eq (r : QuartetTree (Fin 4)) (top : E₂ → Finset (Finset (Fin 4))) :
    φ₂ r top = rootMass r (top .a ∪ (top .b ∪ (top .Y ∪ (top .rc ∪ top .rd)))) := by
  unfold φ₂
  rw [arriving₂_root]

/-- The chain at `Y` when the lineages of `c`, `d` both go through it. -/
theorem κ₂_Y_two (hθ : N₂.IsMetric θ) (hρ : 0 ≤ ρ ∧ ρ ≤ 1) (r : QuartetTree (Fin 4))
    (top : E₂ → Finset (Finset (Fin 4))) (ha : top .a = {{0}}) (hb : top .b = {{1}})
    (h₁ : top .yc = {{2}}) (h₂ : top .yd = {{3}}) (h₃ : top .rc = ∅) (h₄ : top .rd = ∅) :
    stepKernel N₂ θ ρ inj₂ .Y (φ₂ r) top =
      Real.exp (-θ.length .Y) * (1 / 3) + (1 - Real.exp (-θ.length .Y)) *
        if ({2, 3} : Finset (Fin 4)) ∈ r.val then 1 else 0 := by
  rw [step₂_Y_two hθ hρ.1 _ top (by rw [h₁, h₂]; decide), φ₂_eq, φ₂_eq,
    ow_of_notMem (f := E₂.a) (by rw [mem_arcsInto]; decide),
    ow_of_notMem (f := E₂.b) (by rw [mem_arcsInto]; decide),
    ow_of_notMem (f := E₂.rc) (by rw [mem_arcsInto]; decide),
    ow_of_notMem (f := E₂.rd) (by rw [mem_arcsInto]; decide),
    ow_of_notMem (f := E₂.a) (by rw [mem_arcsInto]; decide),
    ow_of_notMem (f := E₂.b) (by rw [mem_arcsInto]; decide),
    ow_of_notMem (f := E₂.rc) (by rw [mem_arcsInto]; decide),
    ow_of_notMem (f := E₂.rd) (by rw [mem_arcsInto]; decide),
    ow_of_mem Y_mem_arcsInto, ow_of_mem Y_mem_arcsInto, ha, hb, h₃, h₄]
  have e₁ : ({{0}} : Finset (Finset (Fin 4))) ∪ ({{1}} ∪ (Fcd ∪ (∅ ∪ ∅))) = Fall := by decide
  have e₂ : ({{0}} : Finset (Finset (Fin 4))) ∪ ({{1}} ∪ (insert {2, 3} Fcd ∪ (∅ ∪ ∅))) =
      insert {2, 3} Fall := by decide
  rw [e₁, e₂, rootMass_all isPhylogenetic_N₂ hθ hρ, rootMass_cherry isPhylogenetic_N₂ hθ hρ]

/-- The chain at `Y` when one or none of the lineages of `c`, `d` goes through it: all four reach the
root apart. -/
theorem κ₂_Y_det (hθ : N₂.IsMetric θ) (hρ : 0 ≤ ρ ∧ ρ ≤ 1) (r : QuartetTree (Fin 4))
    (top : E₂ → Finset (Finset (Fin 4))) {F : Finset (Finset (Fin 4))}
    (h : top .yc ∪ top .yd = F) (hF : IsForest F) (hr : #(roots F) ≤ 1)
    (hall : top .a ∪ (top .b ∪ (F ∪ (top .rc ∪ top .rd))) = Fall) :
    stepKernel N₂ θ ρ inj₂ .Y (φ₂ r) top = 1 / 3 := by
  rw [step₂_Y_det hθ hρ.1 _ top h hF hr, φ₂_eq,
    ow_of_notMem (f := E₂.a) (by rw [mem_arcsInto]; decide),
    ow_of_notMem (f := E₂.b) (by rw [mem_arcsInto]; decide),
    ow_of_notMem (f := E₂.rc) (by rw [mem_arcsInto]; decide),
    ow_of_notMem (f := E₂.rd) (by rw [mem_arcsInto]; decide),
    ow_of_mem Y_mem_arcsInto, hall, rootMass_all isPhylogenetic_N₂ hθ hρ]

/-- The whole chain of `N₂` from the lineages at the top of the arcs entering the leaves. -/
theorem κ₂_hc (hθ : N₂.IsMetric θ) (hρ : 0 ≤ ρ ∧ ρ ≤ 1) (r : QuartetTree (Fin 4))
    (top : E₂ → Finset (Finset (Fin 4))) (ha : top .a = {{0}}) (hb : top .b = {{1}})
    (hc : top .c = {{2}}) (hd : top .d = {{3}}) :
    stepKernel N₂ θ ρ inj₂ .hc (stepKernel N₂ θ ρ inj₂ .hd (stepKernel N₂ θ ρ inj₂ .Y (φ₂ r))) top =
      cfOf (θ.inheritance .yc * θ.inheritance .yd * (1 - Real.exp (-θ.length .Y))) r := by
  have hs₁ : θ.inheritance .yc + θ.inheritance .rc = 1 :=
    inheritance_add_eq_one hθ.isNormalized (k₁ := E₂.yc) (k₂ := E₂.rc) (v := V₂.hc) rfl rfl
      (by decide) target₂_hc
  have hs₂ : θ.inheritance .yd + θ.inheritance .rd = 1 :=
    inheritance_add_eq_one hθ.isNormalized (k₁ := E₂.yd) (k₂ := E₂.rd) (v := V₂.hd) rfl rfl
      (by decide) target₂_hd
  rw [step₂_hc _ top hc, step₂_hd _ _ (by simp [ow, overwrite, N₂, hd]),
    step₂_hd _ _ (by simp [ow, overwrite, N₂, hd]),
    κ₂_Y_two hθ hρ r _ (by simp [ow, overwrite, N₂, ha]) (by simp [ow, overwrite, N₂, hb])
      (by simp [ow, overwrite, N₂, pairFn]) (by simp [ow, overwrite, N₂, pairFn])
      (by simp [ow, overwrite, N₂, pairFn]) (by simp [ow, overwrite, N₂, pairFn]),
    κ₂_Y_det hθ hρ r _ (F := {{2}}) (by simp [ow, overwrite, N₂, pairFn])
      (isForest_singleton_singleton 2) (by rw [roots_singleton_singleton]; simp)
      (by simp [ow, overwrite, N₂, pairFn, ha, hb]; decide),
    κ₂_Y_det hθ hρ r _ (F := {{3}}) (by simp [ow, overwrite, N₂, pairFn])
      (isForest_singleton_singleton 3) (by rw [roots_singleton_singleton]; simp)
      (by simp [ow, overwrite, N₂, pairFn, ha, hb]; decide),
    κ₂_Y_det hθ hρ r _ (F := ∅) (by simp [ow, overwrite, N₂, pairFn])
      isForest_empty_and_roots.1 isForest_empty_and_roots.2
      (by simp [ow, overwrite, N₂, pairFn, ha, hb]; decide)]
  have e₁ : θ.inheritance .rc = 1 - θ.inheritance .yc := by linarith
  have e₂ : θ.inheritance .rd = 1 - θ.inheritance .yd := by linarith
  rw [e₁, e₂]
  unfold cfOf
  split_ifs <;> ring

/-- **The concordance factors of `N₂`** (Figure 1, Remark 5.2). With `P = γ₁ γ₂ (1 - exp (-t))`, the tree `ab|cd`
has concordance factor `1/3 + 2/3 P`, and each other has `(1 - P)/3`, for every `ρ`: no two lineages go through one
reticulation, and the lengths of the hybrid arcs do not matter. -/
theorem nmscCF_N₂ (hθ : N₂.IsMetric θ) (hρ : 0 ≤ ρ ∧ ρ ≤ 1) (r : QuartetTree (Fin 4)) :
    nmscCF N₂ θ ρ r =
      cfOf (θ.inheritance .yc * θ.inheritance .yd * (1 - Real.exp (-θ.length .Y))) r := by
  have hN := isPhylogenetic_N₂
  rw [nmscCF_eq_cherryMass hN hθ hρ r, taxa_eq_univ, cherryMass_eq_sum_rootMass]
  have hmean := meanOn_of_forall_ne (N := N₂) (θ := θ) (ρ := ρ) hN inj₂
    (D := insert V₂.Y (insert V₂.hd (insert V₂.hc {V₂.a, V₂.b, V₂.c, V₂.d}))) (fun v => by
      cases v <;> decide) (φ₂ r)
  unfold φ₂ at hmean
  rw [← hmean]
  change meanOn N₂ θ ρ inj₂ _ (φ₂ r) = _
  rw [meanOn_insert (fun e => by cases e <;> decide) (by decide) (fun e => by cases e <;> decide),
    meanOn_insert (fun e => by cases e <;> decide) (by decide) (fun e => by cases e <;> decide),
    meanOn_insert (fun e => by cases e <;> decide) (by decide) (fun e => by cases e <;> decide)]
  refine meanOn_eq_const hN hθ.isNormalized hρ.1 (validInj_taxaInj univ)
    (fun e => by cases e <;> decide) (by decide) fun bot top h => ?_
  exact κ₂_hc hθ hρ r top
    (top_eq_of_leaf hN 0 (fun f => by cases f <;> decide) rfl (fun e => by cases e <;> decide)
      (by decide) h)
    (top_eq_of_leaf hN 1 (fun f => by cases f <;> decide) rfl (fun e => by cases e <;> decide)
      (by decide) h)
    (top_eq_of_leaf hN 2 (fun f => by cases f <;> decide) rfl (fun e => by cases e <;> decide)
      (by decide) h)
    (top_eq_of_leaf hN 3 (fun f => by cases f <;> decide) rfl (fun e => by cases e <;> decide)
      (by decide) h)

end N2

/-! ### The network `N₀` -/

section N0

variable {θ : MetricData E₀} {ρ : ℝ}

local notation "inj₀" => taxaInj N₀ (univ : Finset (Fin 4))

theorem arriving₀_root (top : E₀ → Finset (Finset (Fin 4))) :
    arriving N₀ inj₀ top N₀.root = top .a ∪ (top .b ∪ top .w) := by
  rw [arriving_eq_biUnion (S := {.a, .b, .w}) (fun e => by cases e <;> decide),
    taxaInj_eq_empty (by decide)]
  simp [biUnion_insert]

theorem arriving₀_w (top : E₀ → Finset (Finset (Fin 4))) :
    arriving N₀ inj₀ top .w = top .c ∪ top .d := by
  rw [arriving_eq_biUnion (S := {.c, .d}) (fun e => by cases e <;> decide),
    taxaInj_eq_empty (by decide)]
  simp [biUnion_insert]

/-- The forest at the root gives the mass of the quartet tree `r`. -/
def φ₀ (r : QuartetTree (Fin 4)) (top : E₀ → Finset (Finset (Fin 4))) : ℝ :=
  rootMass r (arriving N₀ inj₀ top N₀.root)

theorem target₀_w {f : E₀} : N₀.graph.target f = .w → f = .w := by
  cases f <;> decide

theorem w_mem_arcsInto : E₀.w ∈ arcsInto N₀ V₀.w := mem_arcsInto.2 rfl

/-- The chain of `N₀`. -/
theorem κ₀_w (hθ : N₀.IsMetric θ) (hρ : 0 ≤ ρ ∧ ρ ≤ 1) (r : QuartetTree (Fin 4))
    (top : E₀ → Finset (Finset (Fin 4))) (ha : top .a = {{0}}) (hb : top .b = {{1}})
    (hc : top .c = {{2}}) (hd : top .d = {{3}}) :
    stepKernel N₀ θ ρ inj₀ .w (φ₀ r) top = cfOf (1 - Real.exp (-θ.length .w)) r := by
  have h : stepKernel N₀ θ ρ inj₀ .w (φ₀ r) top =
      Real.exp (-θ.length .w) * φ₀ r (ow (arcsInto N₀ .w) top fun _ => Fcd) +
        (1 - Real.exp (-θ.length .w)) *
          φ₀ r (ow (arcsInto N₀ .w) top fun _ => insert {2, 3} Fcd) := by
    unfold stepKernel
    rw [arriving₀_w, hc, hd, show ({{2}} : Finset (Finset (Fin 4))) ∪ {{3}} = Fcd by decide]
    exact stepOf_unique_two (N := N₀) (θ := θ) (e := E₀.w) hρ.1 rfl (fun f => target₀_w)
      (hθ.2.2.1 E₀.w (isTreeArc_of_unique fun f => target₀_w)) (P := {2, 3}) rfl
      (fun t => φ₀ r (ow (arcsInto N₀ .w) top t)) (ow_dep (arcsInto N₀ .w) top (φ₀ r))
  have e₁ : ({{0}} : Finset (Finset (Fin 4))) ∪ ({{1}} ∪ Fcd) = Fall := by decide
  have e₂ : ({{0}} : Finset (Finset (Fin 4))) ∪ ({{1}} ∪ insert {2, 3} Fcd) = insert {2, 3} Fall := by
    decide
  rw [h]
  unfold φ₀
  rw [arriving₀_root, arriving₀_root,
    ow_of_notMem (f := E₀.a) (by rw [mem_arcsInto]; decide),
    ow_of_notMem (f := E₀.b) (by rw [mem_arcsInto]; decide),
    ow_of_notMem (f := E₀.a) (by rw [mem_arcsInto]; decide),
    ow_of_notMem (f := E₀.b) (by rw [mem_arcsInto]; decide),
    ow_of_mem w_mem_arcsInto, ow_of_mem w_mem_arcsInto, ha, hb, e₁, e₂,
    rootMass_all isPhylogenetic_N₀ hθ hρ, rootMass_cherry isPhylogenetic_N₀ hθ hρ]
  unfold cfOf
  split_ifs <;> ring

/-- **The concordance factors of `N₀`** (Figure 1): the tree with an internal arc of length `t₀`. -/
theorem nmscCF_N₀ (hθ : N₀.IsMetric θ) (hρ : 0 ≤ ρ ∧ ρ ≤ 1) (r : QuartetTree (Fin 4)) :
    nmscCF N₀ θ ρ r = cfOf (1 - Real.exp (-θ.length .w)) r := by
  have hN := isPhylogenetic_N₀
  rw [nmscCF_eq_cherryMass hN hθ hρ r, taxa_eq_univ, cherryMass_eq_sum_rootMass]
  have hmean := meanOn_of_forall_ne (N := N₀) (θ := θ) (ρ := ρ) hN inj₀
    (D := insert V₀.w {V₀.a, V₀.b, V₀.c, V₀.d}) (fun v => by cases v <;> decide) (φ₀ r)
  unfold φ₀ at hmean
  rw [← hmean]
  change meanOn N₀ θ ρ inj₀ _ (φ₀ r) = _
  rw [meanOn_insert (fun e => by cases e <;> decide) (by decide) (fun e => by cases e <;> decide)]
  refine meanOn_eq_const hN hθ.isNormalized hρ.1 (validInj_taxaInj univ)
    (fun e => by cases e <;> decide) (by decide) fun bot top h => ?_
  exact κ₀_w hθ hρ r top
    (top_eq_of_leaf hN 0 (fun f => by cases f <;> decide) rfl (fun e => by cases e <;> decide)
      (by decide) h)
    (top_eq_of_leaf hN 1 (fun f => by cases f <;> decide) rfl (fun e => by cases e <;> decide)
      (by decide) h)
    (top_eq_of_leaf hN 2 (fun f => by cases f <;> decide) rfl (fun e => by cases e <;> decide)
      (by decide) h)
    (top_eq_of_leaf hN 3 (fun f => by cases f <;> decide) rfl (fun e => by cases e <;> decide)
      (by decide) h)

end N0

/-! ### The network `N₁` -/

section N1

variable {θ : MetricData E₁} {ρ : ℝ}

local notation "inj₁" => taxaInj N₁ (univ : Finset (Fin 4))

theorem arriving₁_root (top : E₁ → Finset (Finset (Fin 4))) :
    arriving N₁ inj₁ top N₁.root = top .a ∪ (top .b ∪ (top .e₁ ∪ top .e₂)) := by
  rw [arriving_eq_biUnion (S := {.a, .b, .e₁, .e₂}) (fun e => by cases e <;> decide),
    taxaInj_eq_empty (by decide)]
  simp [biUnion_insert]

theorem arriving₁_w (top : E₁ → Finset (Finset (Fin 4))) :
    arriving N₁ inj₁ top .w = top .c ∪ top .d := by
  rw [arriving_eq_biUnion (S := {.c, .d}) (fun e => by cases e <;> decide),
    taxaInj_eq_empty (by decide)]
  simp [biUnion_insert]

/-- The forest at the root gives the mass of the quartet tree `r`. -/
def φ₁ (r : QuartetTree (Fin 4)) (top : E₁ → Finset (Finset (Fin 4))) : ℝ :=
  rootMass r (arriving N₁ inj₁ top N₁.root)

theorem target₁_w (f : E₁) : N₁.graph.target f = .w → f = .e₁ ∨ f = .e₂ := by
  cases f <;> decide

theorem e₁_mem_arcsInto : E₁.e₁ ∈ arcsInto N₁ V₀.w := mem_arcsInto.2 rfl

theorem e₂_mem_arcsInto : E₁.e₂ ∈ arcsInto N₁ V₀.w := mem_arcsInto.2 rfl

/-- The probability that the lineages of `c`, `d` coalesce in `N₁`, at inheritance correlation `ρ`. For `ρ = 0`
it is `γ² (1 - exp (-t₁)) + (1 - γ)² (1 - exp (-t₂))`. -/
def coalescence₁ (θ : MetricData E₁) (ρ : ℝ) : ℝ :=
  θ.inheritance .e₁ * ((1 - ρ) * θ.inheritance .e₁ + ρ) * (1 - Real.exp (-θ.length .e₁)) +
    θ.inheritance .e₂ * ((1 - ρ) * θ.inheritance .e₂ + ρ) * (1 - Real.exp (-θ.length .e₂))

/-- The chain of `N₁`. -/
theorem κ₁_w (hθ : N₁.IsMetric θ) (hρ : 0 ≤ ρ ∧ ρ ≤ 1) (r : QuartetTree (Fin 4))
    (top : E₁ → Finset (Finset (Fin 4))) (ha : top .a = {{0}}) (hb : top .b = {{1}})
    (hc : top .c = {{2}}) (hd : top .d = {{3}}) :
    stepKernel N₁ θ ρ inj₁ .w (φ₁ r) top = cfOf (coalescence₁ θ ρ) r := by
  have hs : θ.inheritance .e₁ + θ.inheritance .e₂ = 1 :=
    inheritance_add_eq_one hθ.isNormalized (k₁ := E₁.e₁) (k₂ := E₁.e₂) (v := V₀.w) rfl rfl
      (by decide) target₁_w
  have hval : ∀ t : E₁ → Finset (Finset (Fin 4)), φ₁ r (ow (arcsInto N₁ .w) top t) =
      rootMass r ({{0}} ∪ ({{1}} ∪ (t .e₁ ∪ t .e₂))) := fun t => by
    unfold φ₁
    rw [arriving₁_root, ow_of_notMem (f := E₁.a) (by rw [mem_arcsInto]; decide),
      ow_of_notMem (f := E₁.b) (by rw [mem_arcsInto]; decide), ow_of_mem e₁_mem_arcsInto,
      ow_of_mem e₂_mem_arcsInto, ha, hb]
  have h := stepOf_two_two (N := N₁) (θ := θ) (ρ := ρ) (v := V₀.w) (k₁ := E₁.e₁) (k₂ := E₁.e₂)
    rfl rfl (by decide) target₁_w (x := (2 : Fin 4)) (y := 3) (by decide)
    (fun t => φ₁ r (ow (arcsInto N₁ .w) top t)) (ow_dep (arcsInto N₁ .w) top (φ₁ r))
  have hF : ({{2}} : Finset (Finset (Fin 4))) ∪ {{3}} = Fcd := by decide
  unfold stepKernel
  rw [arriving₁_w, hc, hd, hF]
  refine h.trans ?_
  simp only [hval, pairFn_left, pairFn_right (show E₁.e₁ ≠ E₁.e₂ by decide)]
  have e₁ : ({{0}} : Finset (Finset (Fin 4))) ∪ ({{1}} ∪ (Fcd ∪ ∅)) = Fall := by decide
  have e₂ : ({{0}} : Finset (Finset (Fin 4))) ∪ ({{1}} ∪ (∅ ∪ Fcd)) = Fall := by decide
  have e₃ : ({{0}} : Finset (Finset (Fin 4))) ∪ ({{1}} ∪ ({{2}} ∪ {{3}})) = Fall := by decide
  have e₄ : ({{0}} : Finset (Finset (Fin 4))) ∪ ({{1}} ∪ ({{3}} ∪ {{2}})) = Fall := by decide
  have e₅ : ({{0}} : Finset (Finset (Fin 4))) ∪ ({{1}} ∪ (insert {2, 3} Fcd ∪ ∅)) =
      insert {2, 3} Fall := by decide
  have e₆ : ({{0}} : Finset (Finset (Fin 4))) ∪ ({{1}} ∪ (∅ ∪ insert {2, 3} Fcd)) =
      insert {2, 3} Fall := by decide
  rw [e₁, e₂, e₃, e₄, e₅, e₆, rootMass_all isPhylogenetic_N₁ hθ hρ,
    rootMass_cherry isPhylogenetic_N₁ hθ hρ]
  have hγ : θ.inheritance .e₂ = 1 - θ.inheritance .e₁ := by linarith
  unfold cfOf coalescence₁
  rw [hγ]
  split_ifs <;> ring

/-- **The concordance factors of `N₁`** (Figure 1; Ané et al. 2024, Example 1): the tree `ab|cd` has concordance
factor `1/3 + 2/3 P`, and each other has `(1 - P)/3`, where `P = coalescence₁ θ ρ` depends on `ρ`, since two
lineages go through the reticulation. -/
theorem nmscCF_N₁ (hθ : N₁.IsMetric θ) (hρ : 0 ≤ ρ ∧ ρ ≤ 1) (r : QuartetTree (Fin 4)) :
    nmscCF N₁ θ ρ r = cfOf (coalescence₁ θ ρ) r := by
  have hN := isPhylogenetic_N₁
  rw [nmscCF_eq_cherryMass hN hθ hρ r, taxa_eq_univ, cherryMass_eq_sum_rootMass]
  have hmean := meanOn_of_forall_ne (N := N₁) (θ := θ) (ρ := ρ) hN inj₁
    (D := insert V₀.w {V₀.a, V₀.b, V₀.c, V₀.d}) (fun v => by cases v <;> decide) (φ₁ r)
  unfold φ₁ at hmean
  rw [← hmean]
  change meanOn N₁ θ ρ inj₁ _ (φ₁ r) = _
  rw [meanOn_insert (fun e => by cases e <;> decide) (by decide) (fun e => by cases e <;> decide)]
  refine meanOn_eq_const hN hθ.isNormalized hρ.1 (validInj_taxaInj univ)
    (fun e => by cases e <;> decide) (by decide) fun bot top h => ?_
  exact κ₁_w hθ hρ r top
    (top_eq_of_leaf hN 0 (fun f => by cases f <;> decide) rfl (fun e => by cases e <;> decide)
      (by decide) h)
    (top_eq_of_leaf hN 1 (fun f => by cases f <;> decide) rfl (fun e => by cases e <;> decide)
      (by decide) h)
    (top_eq_of_leaf hN 2 (fun f => by cases f <;> decide) rfl (fun e => by cases e <;> decide)
      (by decide) h)
    (top_eq_of_leaf hN 3 (fun f => by cases f <;> decide) rfl (fun e => by cases e <;> decide)
      (by decide) h)

end N1

/-! ### The form of the concordance factors -/

theorem cfOf_values (P : ℝ) :
    cfOf P abcd = 1 / 3 + 2 / 3 * P ∧ cfOf P acbd = (1 - P) / 3 ∧ cfOf P adbc = (1 - P) / 3 := by
  have h₁ : ({2, 3} : Finset (Fin 4)) ∈ abcd.val := by decide
  have h₂ : ({2, 3} : Finset (Fin 4)) ∉ acbd.val := by decide
  have h₃ : ({2, 3} : Finset (Fin 4)) ∉ adbc.val := by decide
  unfold cfOf
  rw [ite_eq_left h₁, ite_eq_right h₂, ite_eq_right h₃]
  exact ⟨rfl, rfl, rfl⟩

/-- A coalescence of positive probability gives (5.2) for `ab|cd`. -/
theorem isT1Strict_cfOf {P : ℝ} (hP : 0 < P) : IsT1Strict (cfOf P) abcd := by
  have hmem : ({2, 3} : Finset (Fin 4)) ∈ abcd.val := by decide
  have halt : ∀ r ∈ abcd.alternatives, cfOf P r = (1 - P) / 3 := fun r hr => by
    obtain ⟨hrt, hne⟩ := QuartetTree.mem_alternatives.1 hr
    unfold cfOf
    exact ite_eq_right fun h => hne (QuartetTree.eq_of_taxa_eq_of_mem hrt h hmem)
  refine ⟨fun r hr => ?_, fun r hr r' hr' => ?_⟩
  · rw [halt r hr, (cfOf_values P).1]
    linarith
  · rw [halt r hr, halt r' hr']

/-- Without coalescence the concordance factors are uniform. -/
theorem cfOf_zero (r : QuartetTree (Fin 4)) : cfOf 0 r = 1 / 3 := by
  unfold cfOf
  split_ifs <;> norm_num

/-! ### Remark 5.2 for `N₂` -/

section Conclusion₂

variable {θ : MetricData E₂} {ρ : ℝ}

theorem inheritance₂_bounds (hθ : N₂.IsMetric θ) :
    0 < θ.inheritance .yc ∧ θ.inheritance .yc < 1 ∧ 0 < θ.inheritance .yd ∧
      θ.inheritance .yd < 1 := by
  have h₁ : θ.inheritance .yc + θ.inheritance .rc = 1 :=
    inheritance_add_eq_one hθ.isNormalized (k₁ := E₂.yc) (k₂ := E₂.rc) (v := V₂.hc) rfl rfl
      (by decide) target₂_hc
  have h₂ : θ.inheritance .yd + θ.inheritance .rd = 1 :=
    inheritance_add_eq_one hθ.isNormalized (k₁ := E₂.yd) (k₂ := E₂.rd) (v := V₂.hd) rfl rfl
      (by decide) target₂_hd
  have hc := inheritance_pos hθ E₂.yc
  have hc' := inheritance_pos hθ E₂.rc
  have hd := inheritance_pos hθ E₂.yd
  have hd' := inheritance_pos hθ E₂.rd
  exact ⟨hc, by linarith, hd, by linarith⟩

/-- The probability `P = γ₁ γ₂ (1 - exp (-t))` that the lineages of `c`, `d` coalesce in `N₂`. -/
def coalescence₂ (θ : MetricData E₂) : ℝ :=
  θ.inheritance .yc * θ.inheritance .yd * (1 - Real.exp (-θ.length .Y))

theorem coalescence₂_bounds (hθ : N₂.IsMetric θ) : 0 < coalescence₂ θ ∧ coalescence₂ θ < 1 := by
  obtain ⟨hc, hc', hd, hd'⟩ := inheritance₂_bounds hθ
  have ht : 0 < θ.length .Y := hθ.1 E₂.Y (isTreeArc_of_unique fun f => target₂_Y)
  have he : Real.exp (-θ.length .Y) < 1 := Real.exp_lt_one_iff.2 (by linarith)
  have he' := Real.exp_pos (-θ.length .Y)
  have h₁ : 0 < θ.inheritance .yc * θ.inheritance .yd := mul_pos hc hd
  have h₂ : θ.inheritance .yc * θ.inheritance .yd < 1 := by nlinarith
  unfold coalescence₂
  refine ⟨mul_pos h₁ (by linarith), ?_⟩
  nlinarith

/-- The three concordance factors of `N₂`. -/
theorem nmscCF_N₂_values (hθ : N₂.IsMetric θ) (hρ : 0 ≤ ρ ∧ ρ ≤ 1) :
    nmscCF N₂ θ ρ abcd = 1 / 3 + 2 / 3 * coalescence₂ θ ∧
      nmscCF N₂ θ ρ acbd = (1 - coalescence₂ θ) / 3 ∧
      nmscCF N₂ θ ρ adbc = (1 - coalescence₂ θ) / 3 := by
  rw [nmscCF_N₂ hθ hρ, nmscCF_N₂ hθ hρ, nmscCF_N₂ hθ hρ]
  exact cfOf_values _

/-- **`N₂` satisfies (5.2) for `ab|cd`** (`ecto:remark5_2`, Figure 1), at all parameters, though it has no cut-edge for
that split. -/
theorem isT1Strict_N₂ (hθ : N₂.IsMetric θ) (hρ : 0 ≤ ρ ∧ ρ ≤ 1) :
    IsT1Strict (nmscCF N₂ θ ρ) abcd := by
  rw [funext (nmscCF_N₂ hθ hρ)]
  exact isT1Strict_cfOf (coalescence₂_bounds hθ).1

end Conclusion₂

/-! ### Replacing a blob by an edge: the parameters of `N₀` -/

theorem target₀_injective : Function.Injective N₀.graph.target := by
  intro f g
  cases f <;> cases g <;> decide

theorem not_isHybridArc_N₀ (e : E₀) : ¬ N₀.IsHybridArc e := by
  have h := not_isHybridArc_of_isTreeArc (N := N₀) (e := e)
    (isTreeArc_of_unique fun f hf => target₀_injective hf)
  exact h

/-- The parameters of `N₀` with length `t` on the internal arc. -/
def metric₀ (t : ℝ) : MetricData E₀ where
  length := fun e => if e = .w then t else 1
  inheritance := fun _ => 1

theorem isMetric_metric₀ {t : ℝ} (ht : 0 < t) : N₀.IsMetric (metric₀ t) := by
  refine ⟨fun e _ => ?_, fun e he => absurd he (not_isHybridArc_N₀ e), fun _ _ => rfl,
    fun e he => absurd he (not_isHybridArc_N₀ e), fun v hv => ?_⟩
  · change 0 < if e = .w then t else 1
    split_ifs
    · exact ht
    · exact one_pos
  · exfalso
    rw [indegree_eq_card] at hv
    obtain ⟨f, hf, g, hg, hne⟩ := one_lt_card.1 hv
    exact hne (target₀_injective ((mem_arcsInto.1 hf).trans (mem_arcsInto.1 hg).symm))

/-- **A blob replaced by an edge**: a probability of coalescence is that of an arc of positive length. -/
theorem exists_metric₀ {P : ℝ} (h₀ : 0 < P) (h₁ : P < 1) :
    ∃ θ₀, N₀.IsMetric θ₀ ∧ 0 < θ₀.length .w ∧ 1 - Real.exp (-θ₀.length .w) = P := by
  have hl : Real.log (1 - P) < 0 := Real.log_neg (by linarith) (by linarith)
  have ht : 0 < -Real.log (1 - P) := by linarith
  refine ⟨metric₀ (-Real.log (1 - P)), isMetric_metric₀ ht, ?_, ?_⟩
  · change 0 < if E₀.w = .w then _ else (1 : ℝ)
    rw [ite_eq_left rfl]
    exact ht
  · change 1 - Real.exp (-(if E₀.w = .w then -Real.log (1 - P) else 1)) = P
    rw [ite_eq_left rfl, neg_neg, Real.exp_log (by linarith)]
    ring

/-- The concordance factors of `N₀` by the probability of coalescence on its internal arc. -/
theorem nmscCF_N₀_values {θ : MetricData E₀} {ρ : ℝ} (hθ : N₀.IsMetric θ) (hρ : 0 ≤ ρ ∧ ρ ≤ 1) :
    nmscCF N₀ θ ρ abcd = 1 / 3 + 2 / 3 * (1 - Real.exp (-θ.length .w)) ∧
      nmscCF N₀ θ ρ acbd = (1 - (1 - Real.exp (-θ.length .w))) / 3 ∧
      nmscCF N₀ θ ρ adbc = (1 - (1 - Real.exp (-θ.length .w))) / 3 := by
  rw [nmscCF_N₀ hθ hρ, nmscCF_N₀ hθ hρ, nmscCF_N₀ hθ hρ]
  exact cfOf_values _

/-- `N₀` satisfies (5.2) for its cut-edge split `ab|cd`, its internal arc being a tree arc. -/
theorem isT1Strict_N₀ {θ : MetricData E₀} {ρ : ℝ} (hθ : N₀.IsMetric θ) (hρ : 0 ≤ ρ ∧ ρ ≤ 1) :
    IsT1Strict (nmscCF N₀ θ ρ) abcd := by
  have ht : 0 < θ.length .w := hθ.1 E₀.w (isTreeArc_of_unique fun f => target₀_w)
  have he : Real.exp (-θ.length .w) < 1 := Real.exp_lt_one_iff.2 (by linarith)
  rw [funext (nmscCF_N₀ hθ hρ)]
  exact isT1Strict_cfOf (by linarith)

/-- **`N₂` and `N₀` have the same quartet concordance factors** (Figure 1) when
`1 - exp (-t₀) = γ₁ γ₂ (1 - exp (-t))`. -/
theorem nmscCF_N₂_eq_N₀ {θ₂ : MetricData E₂} {θ₀ : MetricData E₀} {ρ ρ₀ : ℝ} (hθ₂ : N₂.IsMetric θ₂)
    (hθ₀ : N₀.IsMetric θ₀) (hρ : 0 ≤ ρ ∧ ρ ≤ 1) (hρ₀ : 0 ≤ ρ₀ ∧ ρ₀ ≤ 1)
    (h : 1 - Real.exp (-θ₀.length .w) =
      θ₂.inheritance .yc * θ₂.inheritance .yd * (1 - Real.exp (-θ₂.length .Y)))
    (r : QuartetTree (Fin 4)) : nmscCF N₂ θ₂ ρ r = nmscCF N₀ θ₀ ρ₀ r := by
  rw [nmscCF_N₂ hθ₂ hρ, nmscCF_N₀ hθ₀ hρ₀, h]

/-- **The blob of `N₂` can be replaced by an edge of positive length** (`ecto:remark5_2`). -/
theorem exists_N₀_of_N₂ {θ₂ : MetricData E₂} (hθ₂ : N₂.IsMetric θ₂) :
    ∃ θ₀, N₀.IsMetric θ₀ ∧ 0 < θ₀.length .w ∧
      1 - Real.exp (-θ₀.length .w) =
        θ₂.inheritance .yc * θ₂.inheritance .yd * (1 - Real.exp (-θ₂.length .Y)) ∧
      ∀ ρ ρ₀ : ℝ, (0 ≤ ρ ∧ ρ ≤ 1) → (0 ≤ ρ₀ ∧ ρ₀ ≤ 1) → ∀ r, nmscCF N₂ θ₂ ρ r = nmscCF N₀ θ₀ ρ₀ r := by
  obtain ⟨h₀, h₁⟩ := coalescence₂_bounds hθ₂
  obtain ⟨θ₀, hm, hp, he⟩ := exists_metric₀ h₀ h₁
  exact ⟨θ₀, hm, hp, he, fun ρ ρ₀ hρ hρ₀ r => nmscCF_N₂_eq_N₀ hθ₂ hm hρ hρ₀ he r⟩

/-! ### Remark 5.2 for `N₁` -/

section Conclusion₁

variable {θ : MetricData E₁} {ρ : ℝ}

theorem inheritance₁_bounds (hθ : N₁.IsMetric θ) :
    0 < θ.inheritance .e₁ ∧ 0 < θ.inheritance .e₂ ∧ θ.inheritance .e₁ + θ.inheritance .e₂ = 1 :=
  ⟨inheritance_pos hθ _, inheritance_pos hθ _,
    inheritance_add_eq_one hθ.isNormalized (k₁ := E₁.e₁) (k₂ := E₁.e₂) (v := V₀.w) rfl rfl
      (by decide) target₁_w⟩

theorem length₁_nonneg (hθ : N₁.IsMetric θ) : 0 ≤ θ.length .e₁ ∧ 0 ≤ θ.length .e₂ :=
  ⟨length_nonneg hθ _, length_nonneg hθ _⟩

/-- The weight of both lineages on a parent. -/
theorem weight_pos {γ : ℝ} (hγ : 0 < γ) (hρ : 0 ≤ ρ ∧ ρ ≤ 1) : 0 < γ * ((1 - ρ) * γ + ρ) := by
  refine mul_pos hγ ?_
  rcases hρ.1.eq_or_lt with h | h
  · rw [← h]
    simpa using hγ
  · have := mul_nonneg (sub_nonneg.2 hρ.2) hγ.le
    linarith

/-- `P > 0` if `t₁ > 0` or `t₂ > 0`, and always `P < 1`. -/
theorem coalescence₁_bounds (hθ : N₁.IsMetric θ) (hρ : 0 ≤ ρ ∧ ρ ≤ 1) :
    0 ≤ coalescence₁ θ ρ ∧ coalescence₁ θ ρ < 1 ∧
      (0 < coalescence₁ θ ρ ↔ 0 < θ.length .e₁ ∨ 0 < θ.length .e₂) := by
  obtain ⟨hγ₁, hγ₂, hs⟩ := inheritance₁_bounds hθ
  obtain ⟨ht₁, ht₂⟩ := length₁_nonneg hθ
  have hw₁ := weight_pos hγ₁ hρ
  have hw₂ := weight_pos hγ₂ hρ
  have hsum : θ.inheritance .e₁ * ((1 - ρ) * θ.inheritance .e₁ + ρ) +
      θ.inheritance .e₂ * ((1 - ρ) * θ.inheritance .e₂ + ρ) ≤ 1 := by
    have hγ : θ.inheritance .e₂ = 1 - θ.inheritance .e₁ := by linarith
    have h1 := mul_nonneg (sub_nonneg.2 hρ.2) (mul_pos hγ₁ hγ₂).le
    rw [hγ] at h1 ⊢
    nlinarith
  have he₁ := Real.exp_pos (-θ.length .e₁)
  have he₂ := Real.exp_pos (-θ.length .e₂)
  have hl₁ : Real.exp (-θ.length .e₁) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
  have hl₂ : Real.exp (-θ.length .e₂) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
  have hn₁ : 0 ≤ 1 - Real.exp (-θ.length .e₁) := by linarith
  have hn₂ : 0 ≤ 1 - Real.exp (-θ.length .e₂) := by linarith
  have hu₁ := mul_nonneg hw₁.le hn₁
  have hu₂ := mul_nonneg hw₂.le hn₂
  unfold coalescence₁
  refine ⟨by linarith, by nlinarith, ⟨fun h => ?_, ?_⟩⟩
  · by_contra hcon
    push Not at hcon
    have e₁ : θ.length .e₁ = 0 := le_antisymm hcon.1 ht₁
    have e₂ : θ.length .e₂ = 0 := le_antisymm hcon.2 ht₂
    rw [e₁, e₂] at h
    simp at h
  · rintro (h | h)
    · have hp : 0 < 1 - Real.exp (-θ.length .e₁) := by
        have := Real.exp_lt_one_iff.2 (by linarith : -θ.length .e₁ < 0)
        linarith
      have := mul_pos hw₁ hp
      linarith
    · have hp : 0 < 1 - Real.exp (-θ.length .e₂) := by
        have := Real.exp_lt_one_iff.2 (by linarith : -θ.length .e₂ < 0)
        linarith
      have := mul_pos hw₂ hp
      linarith

/-- The three concordance factors of `N₁`. -/
theorem nmscCF_N₁_values (hθ : N₁.IsMetric θ) (hρ : 0 ≤ ρ ∧ ρ ≤ 1) :
    nmscCF N₁ θ ρ abcd = 1 / 3 + 2 / 3 * coalescence₁ θ ρ ∧
      nmscCF N₁ θ ρ acbd = (1 - coalescence₁ θ ρ) / 3 ∧
      nmscCF N₁ θ ρ adbc = (1 - coalescence₁ θ ρ) / 3 := by
  rw [nmscCF_N₁ hθ hρ, nmscCF_N₁ hθ hρ, nmscCF_N₁ hθ hρ]
  exact cfOf_values _

/-- **`N₁` satisfies (5.2) for `ab|cd`** (`ecto:remark5_2`, Figure 1) if `t₁ > 0` or `t₂ > 0`, though it has no
cut edge for that split. -/
theorem isT1Strict_N₁ (hθ : N₁.IsMetric θ) (hρ : 0 ≤ ρ ∧ ρ ≤ 1)
    (ht : 0 < θ.length .e₁ ∨ 0 < θ.length .e₂) : IsT1Strict (nmscCF N₁ θ ρ) abcd := by
  rw [funext (nmscCF_N₁ hθ hρ)]
  exact isT1Strict_cfOf ((coalescence₁_bounds hθ hρ).2.2.2 ht)

/-- At `t₁ = t₂ = 0` the concordance factors of `N₁` are uniform, so the condition of the caption of Figure 1 is
needed. -/
theorem nmscCF_N₁_of_length_zero (hθ : N₁.IsMetric θ) (hρ : 0 ≤ ρ ∧ ρ ≤ 1) (h₁ : θ.length .e₁ = 0)
    (h₂ : θ.length .e₂ = 0) (r : QuartetTree (Fin 4)) : nmscCF N₁ θ ρ r = 1 / 3 := by
  have hz : coalescence₁ θ ρ = 0 := by
    unfold coalescence₁
    rw [h₁, h₂]
    simp
  rw [nmscCF_N₁ hθ hρ, hz, cfOf_zero]

/-- **The blob of `N₁` can be replaced by an edge of positive length** (`ecto:remark5_2`; Ané et al. 2024,
Example 1), of a length that depends on `ρ`. -/
theorem exists_N₀_of_N₁ (hθ : N₁.IsMetric θ) (hρ : 0 ≤ ρ ∧ ρ ≤ 1)
    (ht : 0 < θ.length .e₁ ∨ 0 < θ.length .e₂) :
    ∃ θ₀, N₀.IsMetric θ₀ ∧ 0 < θ₀.length .w ∧ 1 - Real.exp (-θ₀.length .w) = coalescence₁ θ ρ ∧
      ∀ ρ₀ : ℝ, (0 ≤ ρ₀ ∧ ρ₀ ≤ 1) → ∀ r, nmscCF N₁ θ ρ r = nmscCF N₀ θ₀ ρ₀ r := by
  obtain ⟨-, h₁, h₂⟩ := coalescence₁_bounds hθ hρ
  obtain ⟨θ₀, hm, hp, he⟩ := exists_metric₀ (h₂.2 ht) h₁
  refine ⟨θ₀, hm, hp, he, fun ρ₀ hρ₀ r => ?_⟩
  rw [nmscCF_N₁ hθ hρ, nmscCF_N₀ hm hρ₀, he]

end Conclusion₁

/-- At `ρ = 0`: `P = γ² (1 - exp (-t₁)) + (1 - γ)² (1 - exp (-t₂))`. -/
theorem coalescence₁_rho_zero (θ : MetricData E₁) :
    coalescence₁ θ 0 = θ.inheritance .e₁ ^ 2 * (1 - Real.exp (-θ.length .e₁)) +
      θ.inheritance .e₂ ^ 2 * (1 - Real.exp (-θ.length .e₂)) := by
  unfold coalescence₁
  ring

/-- At `ρ = 1`: `P = γ (1 - exp (-t₁)) + (1 - γ) (1 - exp (-t₂))`: the lineages take one parent. -/
theorem coalescence₁_rho_one (θ : MetricData E₁) :
    coalescence₁ θ 1 = θ.inheritance .e₁ * (1 - Real.exp (-θ.length .e₁)) +
      θ.inheritance .e₂ * (1 - Real.exp (-θ.length .e₂)) := by
  unfold coalescence₁
  ring

/-! ### The parameters of Figure 1 -/

/-- The parameters of `N₁` as in Figure 1, with length `1` on the pendant arcs. -/
def metric₁ (t₁ t₂ γ : ℝ) : MetricData E₁ where
  length := fun
    | .e₁ => t₁
    | .e₂ => t₂
    | _ => 1
  inheritance := fun
    | .e₁ => γ
    | .e₂ => 1 - γ
    | _ => 1

theorem indegree₁_w : N₁.graph.indegree .w = 2 := by
  rw [indegree_eq_card]
  have : arcsInto N₁ V₀.w = {.e₁, .e₂} := by
    ext e
    rw [mem_arcsInto]
    cases e <;> decide
  rw [this]
  rfl

theorem isMetric_metric₁ {t₁ t₂ γ : ℝ} (h₁ : 0 ≤ t₁) (h₂ : 0 ≤ t₂) (h₃ : 0 < γ) (h₄ : γ < 1) :
    N₁.IsMetric (metric₁ t₁ t₂ γ) := by
  have hne : ∀ e, N₁.graph.target e = .w → ¬ N₁.IsTreeArc e := fun e he ht => by
    unfold RootedNetwork.IsTreeArc at ht
    rw [he, indegree₁_w] at ht
    omega
  refine ⟨fun e he => ?_, fun e _ => ?_, fun e he => ?_, fun e _ => ?_, fun v hv => ?_⟩
  · cases e
    · exact one_pos
    · exact one_pos
    · exact absurd he (hne _ rfl)
    · exact absurd he (hne _ rfl)
    · exact one_pos
    · exact one_pos
  · cases e
    · exact zero_le_one
    · exact zero_le_one
    · exact h₁
    · exact h₂
    · exact zero_le_one
    · exact zero_le_one
  · cases e
    · rfl
    · rfl
    · exact absurd he (hne _ rfl)
    · exact absurd he (hne _ rfl)
    · rfl
    · rfl
  · cases e
    · exact one_pos
    · exact one_pos
    · exact h₃
    · exact sub_pos.2 h₄
    · exact one_pos
    · exact one_pos
  · rw [indegree_eq_card] at hv
    obtain ⟨f, hf, g, hg, hfg⟩ := one_lt_card.1 hv
    have key : ∀ f g : E₁, f ≠ g → N₁.graph.target f = N₁.graph.target g →
        N₁.graph.target f = .w := by decide
    have hv' : v = .w := (mem_arcsInto.1 hf).symm.trans
      (key f g hfg ((mem_arcsInto.1 hf).trans (mem_arcsInto.1 hg).symm))
    subst hv'
    rw [sum_ite_target_pair _ (v := V₀.w) (k₁ := E₁.e₁) (k₂ := E₁.e₂) rfl rfl (by decide) target₁_w]
    change γ + (1 - γ) = 1
    ring

/-- The parameters of `N₂` as in Figure 1, with length `1` on the pendant arcs and `s` on the hybrid arcs,
which do not matter. -/
def metric₂ (t γ₁ γ₂ s : ℝ) : MetricData E₂ where
  length := fun
    | .Y => t
    | .yc | .rc | .yd | .rd => s
    | _ => 1
  inheritance := fun
    | .yc => γ₁
    | .rc => 1 - γ₁
    | .yd => γ₂
    | .rd => 1 - γ₂
    | _ => 1

theorem indegree₂_hc : N₂.graph.indegree .hc = 2 := by
  rw [indegree_eq_card]
  have : arcsInto N₂ V₂.hc = {.yc, .rc} := by
    ext e
    rw [mem_arcsInto]
    cases e <;> decide
  rw [this]
  rfl

theorem indegree₂_hd : N₂.graph.indegree .hd = 2 := by
  rw [indegree_eq_card]
  have : arcsInto N₂ V₂.hd = {.yd, .rd} := by
    ext e
    rw [mem_arcsInto]
    cases e <;> decide
  rw [this]
  rfl

theorem isMetric_metric₂ {t γ₁ γ₂ s : ℝ} (ht : 0 < t) (h₁ : 0 < γ₁) (h₁' : γ₁ < 1) (h₂ : 0 < γ₂)
    (h₂' : γ₂ < 1) (hs : 0 ≤ s) : N₂.IsMetric (metric₂ t γ₁ γ₂ s) := by
  have hne : ∀ e, N₂.graph.target e = .hc ∨ N₂.graph.target e = .hd → ¬ N₂.IsTreeArc e :=
    fun e he hte => by
      unfold RootedNetwork.IsTreeArc at hte
      rcases he with he | he
      · rw [he, indegree₂_hc] at hte
        omega
      · rw [he, indegree₂_hd] at hte
        omega
  refine ⟨fun e he => ?_, fun e _ => ?_, fun e he => ?_, fun e _ => ?_, fun v hv => ?_⟩
  · cases e
    · exact one_pos
    · exact one_pos
    · exact ht
    · exact absurd he (hne _ (Or.inl rfl))
    · exact absurd he (hne _ (Or.inl rfl))
    · exact absurd he (hne _ (Or.inr rfl))
    · exact absurd he (hne _ (Or.inr rfl))
    · exact one_pos
    · exact one_pos
  · cases e
    · exact zero_le_one
    · exact zero_le_one
    · exact ht.le
    · exact hs
    · exact hs
    · exact hs
    · exact hs
    · exact zero_le_one
    · exact zero_le_one
  · cases e
    · rfl
    · rfl
    · rfl
    · exact absurd he (hne _ (Or.inl rfl))
    · exact absurd he (hne _ (Or.inl rfl))
    · exact absurd he (hne _ (Or.inr rfl))
    · exact absurd he (hne _ (Or.inr rfl))
    · rfl
    · rfl
  · cases e
    · exact one_pos
    · exact one_pos
    · exact one_pos
    · exact h₁
    · exact sub_pos.2 h₁'
    · exact h₂
    · exact sub_pos.2 h₂'
    · exact one_pos
    · exact one_pos
  · rw [indegree_eq_card] at hv
    obtain ⟨f, hf, g, hg, hfg⟩ := one_lt_card.1 hv
    have key : ∀ f g : E₂, f ≠ g → N₂.graph.target f = N₂.graph.target g →
        N₂.graph.target f = .hc ∨ N₂.graph.target f = .hd := by decide
    rcases key f g hfg ((mem_arcsInto.1 hf).trans (mem_arcsInto.1 hg).symm) with h | h
    · have hv' : v = .hc := (mem_arcsInto.1 hf).symm.trans h
      subst hv'
      rw [sum_ite_target_pair _ (v := V₂.hc) (k₁ := E₂.yc) (k₂ := E₂.rc) rfl rfl (by decide) target₂_hc]
      change γ₁ + (1 - γ₁) = 1
      ring
    · have hv' : v = .hd := (mem_arcsInto.1 hf).symm.trans h
      subst hv'
      rw [sum_ite_target_pair _ (v := V₂.hd) (k₁ := E₂.yd) (k₂ := E₂.rd) rfl rfl (by decide) target₂_hd]
      change γ₂ + (1 - γ₂) = 1
      ring

/-- **Figure 1 for `N₂`**, at the parameters of the figure. -/
theorem nmscCF_metric₂ {t γ₁ γ₂ s ρ : ℝ} (ht : 0 < t) (h₁ : 0 < γ₁) (h₁' : γ₁ < 1) (h₂ : 0 < γ₂)
    (h₂' : γ₂ < 1) (hs : 0 ≤ s) (hρ : 0 ≤ ρ ∧ ρ ≤ 1) (r : QuartetTree (Fin 4)) :
    nmscCF N₂ (metric₂ t γ₁ γ₂ s) ρ r = cfOf (γ₁ * γ₂ * (1 - Real.exp (-t))) r :=
  nmscCF_N₂ (isMetric_metric₂ ht h₁ h₁' h₂ h₂' hs) hρ r

/-- **Figure 1 for `N₁`**, at the parameters of the figure. -/
theorem nmscCF_metric₁ {t₁ t₂ γ ρ : ℝ} (h₁ : 0 ≤ t₁) (h₂ : 0 ≤ t₂) (h₃ : 0 < γ) (h₄ : γ < 1)
    (hρ : 0 ≤ ρ ∧ ρ ≤ 1) (r : QuartetTree (Fin 4)) :
    nmscCF N₁ (metric₁ t₁ t₂ γ) ρ r =
      cfOf (γ * ((1 - ρ) * γ + ρ) * (1 - Real.exp (-t₁)) +
        (1 - γ) * ((1 - ρ) * (1 - γ) + ρ) * (1 - Real.exp (-t₂))) r :=
  nmscCF_N₁ (isMetric_metric₁ h₁ h₂ h₃ h₄) hρ r

/-- **Figure 1 for `N₀`**, at the parameters of the figure. -/
theorem nmscCF_metric₀ {t ρ : ℝ} (ht : 0 < t) (hρ : 0 ≤ ρ ∧ ρ ≤ 1) (r : QuartetTree (Fin 4)) :
    nmscCF N₀ (metric₀ t) ρ r = cfOf (1 - Real.exp (-t)) r :=
  nmscCF_N₀ (isMetric_metric₀ ht) hρ r

/-! ### The measure of §5.1 -/

section Measure

variable {V E X : Type*} [Fintype V] [Fintype E] {N : RootedNetwork V E X}

omit [Fintype V] in
/-- The coordinates of the numerical parameters give valid parameters, for reticulations with two
parents. -/
theorem isMetric_coordMetric (hdeg : ∀ v, N.graph.indegree v ≤ 2) {d : V → E}
    (hd : IsParentChoice N d) {ℓ g : E → ℝ} (hℓ : ∀ e, 0 < ℓ e) (hg : ∀ e, 0 < g e ∧ g e < 1) :
    N.IsMetric (coordMetric N d ℓ g) := by
  refine ⟨fun e _ => hℓ e, fun e _ => (hℓ e).le, fun e he => coordMetric_inheritance_of_isTreeArc he,
    fun e he => ?_, fun v hv => sum_coordMetric_inheritance hd hv⟩
  by_cases hde : e = d (N.graph.target e)
  · rw [coordMetric_inheritance_of_eq he hde, sub_pos]
    set T := univ.filter (fun f => N.graph.target f = N.graph.target e ∧ f ≠ e) with hT
    have hcard : #T ≤ 1 := by
      have hsub : T ⊆ (arcsInto N (N.graph.target e)).erase e := fun f hf => by
        obtain ⟨h₁, h₂⟩ := (mem_filter.1 hf).2
        exact mem_erase.2 ⟨h₂, mem_arcsInto.2 h₁⟩
      have h₁ := card_le_card hsub
      rw [card_erase_of_mem (mem_arcsInto.2 rfl), ← indegree_eq_card] at h₁
      have h₂ := hdeg (N.graph.target e)
      omega
    rcases T.eq_empty_or_nonempty with h | ⟨f, hf⟩
    · rw [h, sum_empty]
      exact one_pos
    · have hTf : T = {f} := by
        refine eq_singleton_iff_unique_mem.2 ⟨hf, fun h hh => card_le_one.1 hcard h hh f hf⟩
      rw [hTf, sum_singleton]
      exact (hg f).2
  · rw [coordMetric_inheritance_of_ne he hde]
    exact (hg e).1

omit [Fintype V] [Fintype E] in
/-- Each factor of the measure of §5.1 on lengths charges `(1, 2)`. -/
theorem lengthMeasure_Ioo_ne_zero (hybrid : Prop) : lengthMeasure hybrid (Set.Ioo (1 : ℝ) 2) ≠ 0 := by
  have hvol : ∀ S : Set ℝ, Set.Ioo (1 : ℝ) 2 ⊆ S → (volume.restrict S) (Set.Ioo (1 : ℝ) 2) ≠ 0 := by
    intro S hS
    rw [Measure.restrict_apply measurableSet_Ioo, Set.inter_eq_left.2 hS, Real.volume_Ioo]
    norm_num
  unfold lengthMeasure
  split_ifs
  · rw [Measure.add_apply]
    exact fun h => hvol _ (fun x hx => by
      have := hx.1
      exact Set.mem_Ici.2 (by linarith)) (add_eq_zero.1 h).2
  · exact hvol _ fun x hx => by
      have := hx.1
      exact Set.mem_Ioi.2 (by linarith)

omit [Fintype V] in
/-- **A set of parameters containing all valid parameters with positive lengths is not null**, for the
measure of §5.1, when reticulations have two parents. -/
theorem not_isNullParams_of_forall (hN : N.IsPhylogenetic) (hdeg : ∀ v, N.graph.indegree v ≤ 2)
    {A : Set (MetricData E)} (hA : ∀ θ, N.IsMetric θ → (∀ e, 0 < θ.length e) → θ ∈ A) :
    ¬ IsNullParams N A := by
  intro hnull
  have hE : Nonempty E := nonempty_arcs hN
  obtain ⟨d, hd⟩ : ∃ d : V → E, IsParentChoice N d := by
    have h : ∀ v, ∃ e, 2 ≤ N.graph.indegree v → N.graph.target e = v := by
      intro v
      by_cases hv : 2 ≤ N.graph.indegree v
      · rw [indegree_eq_card] at hv
        obtain ⟨e, he⟩ : (arcsInto N v).Nonempty := card_pos.1 (by omega)
        exact ⟨e, fun _ => mem_arcsInto.1 he⟩
      · exact ⟨Classical.arbitrary E, fun h => absurd h hv⟩
    exact Classical.axiomOfChoice h
  have h0 := hnull d hd
  have hbox : (Set.pi Set.univ fun _ : E => Set.Ioo (1 : ℝ) 2) ×ˢ
      (Set.pi Set.univ fun _ : E => Set.Ioo (0 : ℝ) 1) ⊆
      {x : (E → ℝ) × (E → ℝ) | N.IsMetric (coordMetric N d x.1 x.2) ∧
        coordMetric N d x.1 x.2 ∈ A} := by
    rintro ⟨ℓ, g⟩ ⟨hℓ, hg⟩
    have hℓ' : ∀ e, 0 < ℓ e := fun e => by
      have := (hℓ e (Set.mem_univ e)).1
      linarith
    have hg' : ∀ e, 0 < g e ∧ g e < 1 := fun e => hg e (Set.mem_univ e)
    have hm := isMetric_coordMetric hdeg hd hℓ' hg'
    exact ⟨hm, hA _ hm hℓ'⟩
  have hz := measure_mono_null hbox h0
  rw [Measure.prod_prod, Measure.pi_pi, Measure.pi_pi, mul_eq_zero, prod_eq_zero_iff,
    prod_eq_zero_iff] at hz
  rcases hz with ⟨e, -, he⟩ | ⟨e, -, he⟩
  · exact lengthMeasure_Ioo_ne_zero _ he
  · rw [Measure.restrict_apply measurableSet_Ioo, Set.inter_self, Real.volume_Ioo] at he
    norm_num at he

end Measure

/-! ### Remark 5.2 -/

/-- Two parents at most in `N₁`. -/
theorem indegree_N₁ (v : V₀) : N₁.graph.indegree v ≤ 2 := by
  rw [indegree_eq_card]
  by_contra h
  obtain ⟨f, hf, g, hg, k, hk, h₁, h₂, h₃⟩ := two_lt_card.1 (not_le.1 h)
  rw [mem_arcsInto] at hf hg hk
  have key : ∀ f g k : E₁, N₁.graph.target f = N₁.graph.target g →
      N₁.graph.target g = N₁.graph.target k → f = g ∨ f = k ∨ g = k := by decide
  rcases key f g k (hf.trans hg.symm) (hg.trans hk.symm) with h' | h' | h'
  · exact h₁ h'
  · exact h₂ h'
  · exact h₃ h'

/-- Two parents at most in `N₂`. -/
theorem indegree_N₂ (v : V₂) : N₂.graph.indegree v ≤ 2 := by
  rw [indegree_eq_card]
  by_contra h
  obtain ⟨f, hf, g, hg, k, hk, h₁, h₂, h₃⟩ := two_lt_card.1 (not_le.1 h)
  rw [mem_arcsInto] at hf hg hk
  have key : ∀ f g k : E₂, N₂.graph.target f = N₂.graph.target g →
      N₂.graph.target g = N₂.graph.target k → f = g ∨ f = k ∨ g = k := by decide
  rcases key f g k (hf.trans hg.symm) (hg.trans hk.symm) with h' | h' | h'
  · exact h₁ h'
  · exact h₂ h'
  · exact h₃ h'

/-- **Remark 5.2 for `N₁`** (`ecto:remark5_2`), at any inheritance correlation: the parameters with no anomalous
quartets where a converse of Assumption 1 fails are not a null set. `N₁` has no cut edge for `ab|cd`, and (5.2) holds as
soon as `t₁ > 0` or `t₂ > 0`. -/
theorem not_isNullParams_N₁ {ρ : ℝ} (hρ : 0 ≤ ρ ∧ ρ ≤ 1) :
    ¬ IsNullParams N₁ {θ | N₁.IsMetric θ ∧ NoAnomalousQuartets N₁ (nmscCF N₁ θ ρ) ∧
      ¬ Assumption1Converse N₁ (nmscCF N₁ θ ρ)} :=
  not_isNullParams_of_forall isPhylogenetic_N₁ indegree_N₁ fun _ hθ hℓ =>
    ⟨hθ, fun s hs => absurd hs (not_inducedCutSplit_N₁ s), fun hc =>
      hc.t1 abcd (not_inducedCutSplit_N₁ _) (isT1Strict_N₁ hθ hρ (Or.inl (hℓ _)))⟩

/-- **Remark 5.2 for `N₂`** (`ecto:remark5_2`), at any inheritance correlation: a converse of Assumption 1 fails at
all valid parameters, and there are no anomalous quartets. `N₂` has no cut edge for `ab|cd`, and (5.2) holds. -/
theorem not_isNullParams_N₂ {ρ : ℝ} (hρ : 0 ≤ ρ ∧ ρ ≤ 1) :
    ¬ IsNullParams N₂ {θ | N₂.IsMetric θ ∧ NoAnomalousQuartets N₂ (nmscCF N₂ θ ρ) ∧
      ¬ Assumption1Converse N₂ (nmscCF N₂ θ ρ)} :=
  not_isNullParams_of_forall isPhylogenetic_N₂ indegree_N₂ fun _ hθ _ =>
    ⟨hθ, fun s hs => absurd hs (not_inducedCutSplit_N₂ s), fun hc =>
      hc.t1 abcd (not_inducedCutSplit_N₂ _) (isT1Strict_N₂ hθ hρ)⟩

/-- **Remark 5.2 for `N₁`**, in the form of the generic clause of `proposition5_1`, which fails. -/
theorem remark5_2_N₁ :
    ¬ IsNullParams N₁ {θ | N₁.IsMetric θ ∧ NoAnomalousQuartets N₁ (nmscCF N₁ θ 0) ∧
      ¬ Assumption1Converse N₁ (nmscCF N₁ θ 0)} :=
  not_isNullParams_N₁ ⟨le_rfl, zero_le_one⟩

/-- **Remark 5.2 for `N₂`**, in the form of the generic clause of `proposition5_1`, which fails. -/
theorem remark5_2_N₂ :
    ¬ IsNullParams N₂ {θ | N₂.IsMetric θ ∧ NoAnomalousQuartets N₂ (nmscCF N₂ θ 0) ∧
      ¬ Assumption1Converse N₂ (nmscCF N₂ θ 0)} :=
  not_isNullParams_N₂ ⟨le_rfl, zero_le_one⟩

/-- **Remark 5.2** (`ecto:remark5_2`). `N₁` and `N₂` are phylogenetic networks with a blob containing a vertex of
degree `> 3` and no non-trivial cut edge, for which the generic clause of Proposition 5.1 fails: so the hypothesis
`BlobDegreeAtMostThree` of `proposition5_1` cannot be dropped. Indeed (5.2) holds for `ab|cd`, and each blob can be
replaced by an edge of positive length, as in `exists_N₀_of_N₁` and `exists_N₀_of_N₂`. -/
theorem remark5_2 :
    (N₁.IsPhylogenetic ∧ ¬ BlobDegreeAtMostThree N₁ ∧ (∀ s, ¬ InducedCutSplit N₁ s) ∧
      ¬ IsNullParams N₁ {θ | N₁.IsMetric θ ∧ NoAnomalousQuartets N₁ (nmscCF N₁ θ 0) ∧
        ¬ Assumption1Converse N₁ (nmscCF N₁ θ 0)}) ∧
    (N₂.IsPhylogenetic ∧ ¬ BlobDegreeAtMostThree N₂ ∧ (∀ s, ¬ InducedCutSplit N₂ s) ∧
      ¬ IsNullParams N₂ {θ | N₂.IsMetric θ ∧ NoAnomalousQuartets N₂ (nmscCF N₂ θ 0) ∧
        ¬ Assumption1Converse N₂ (nmscCF N₂ θ 0)}) :=
  ⟨⟨isPhylogenetic_N₁, not_blobDegreeAtMostThree_N₁, not_inducedCutSplit_N₁, remark5_2_N₁⟩,
    isPhylogenetic_N₂, not_blobDegreeAtMostThree_N₂, not_inducedCutSplit_N₂, remark5_2_N₂⟩

/-! ### The boundary `t₁ = t₂ = 0` of `N₁` -/

/-- The cut for the taxon `c` in `N₁` is its pendant arc. -/
private theorem eq_c_of_cut {e : E₁} {S : Set V₀} (hS : ∀ f, N₁.graph.Crosses f S ↔ f = e)
    (hc : V₀.c ∈ S) (ha : V₀.a ∉ S) (hb : V₀.b ∉ S) : e = .c := by
  have hu : ∀ f g : E₁, f ≠ g → ¬ (N₁.graph.Crosses f S ∧ N₁.graph.Crosses g S) := fun f g hne h =>
    hne (((hS f).1 h.1).trans ((hS g).1 h.2).symm)
  have hr : V₀.r ∉ S := fun hr => hu .a .b (by decide) ⟨Or.inl ⟨hr, ha⟩, Or.inl ⟨hr, hb⟩⟩
  have hw : V₀.w ∉ S := fun hw => hu .e₁ .e₂ (by decide) ⟨Or.inr ⟨hw, hr⟩, Or.inr ⟨hw, hr⟩⟩
  exact ((hS .c).1 (Or.inr ⟨hc, hw⟩)).symm

/-- The cut for the taxon `a` in `N₁` is its pendant arc. -/
private theorem eq_a_of_cut {e : E₁} {S : Set V₀} (hS : ∀ f, N₁.graph.Crosses f S ↔ f = e)
    (ha : V₀.a ∈ S) (hc : V₀.c ∉ S) (hd : V₀.d ∉ S) : e = .a := by
  have hu : ∀ f g : E₁, f ≠ g → ¬ (N₁.graph.Crosses f S ∧ N₁.graph.Crosses g S) := fun f g hne h =>
    hne (((hS f).1 h.1).trans ((hS g).1 h.2).symm)
  have hr : V₀.r ∉ S := by
    intro hr
    by_cases hw : V₀.w ∈ S
    · exact hu .c .d (by decide) ⟨Or.inl ⟨hw, hc⟩, Or.inl ⟨hw, hd⟩⟩
    · exact hu .e₁ .e₂ (by decide) ⟨Or.inl ⟨hr, hw⟩, Or.inl ⟨hr, hw⟩⟩
  exact ((hS .a).1 (Or.inr ⟨ha, hr⟩)).symm

/-- `N₁` has no trivial 4-blob: no vertex is on the pendant arcs of both `a` and `c`. -/
theorem not_hasTrivialFourBlob_N₁ : ¬ HasTrivialFourBlob N₁ univ := by
  have hall : ∀ f, f ∈ N₁.ancestralArcs ((univ : Finset (Fin 4)) : Set (Fin 4)) := fun f => by
    obtain ⟨x, hx⟩ := exists_reaches_leaf isPhylogenetic_N₁ (N₁.graph.target f)
    exact ⟨x, by simp, hx⟩
  rintro ⟨v, hv⟩
  obtain ⟨e, -, S, hS, hl, -, he⟩ := hv 2 (mem_univ _)
  obtain ⟨e', -, S', hS', hl', -, he'⟩ := hv 0 (mem_univ _)
  have hS₁ : ∀ f, N₁.graph.Crosses f S ↔ f = e := fun f => hS f (hall f)
  have hS₂ : ∀ f, N₁.graph.Crosses f S' ↔ f = e' := fun f => hS' f (hall f)
  have h₁ : e = .c := eq_c_of_cut hS₁ ((hl 2 (mem_univ _)).2 rfl)
    (fun h => absurd ((hl 0 (mem_univ _)).1 h) (by decide))
    (fun h => absurd ((hl 1 (mem_univ _)).1 h) (by decide))
  have h₂ : e' = .a := eq_a_of_cut hS₂ ((hl' 0 (mem_univ _)).2 rfl)
    (fun h => absurd ((hl' 2 (mem_univ _)).1 h) (by decide))
    (fun h => absurd ((hl' 3 (mem_univ _)).1 h) (by decide))
  subst h₁ h₂
  have hv₁ : v = .w ∨ v = .c := by
    rcases he with h | h
    · exact Or.inl h.symm
    · exact Or.inr h.symm
  have hv₂ : v = .r ∨ v = .a := by
    rcases he' with h | h
    · exact Or.inl h.symm
    · exact Or.inr h.symm
  rcases hv₁ with rfl | rfl <;> rcases hv₂ with h | h <;> cases h

/-- **The boundary of Figure 1's condition on `N₁`.** At `t₁ = t₂ = 0`, an atom of the measure of §5.1, the concordance
factors of `N₁` are uniform with no trivial 4-blob, so the star clause of a converse of Assumption 1 fails too. -/
theorem star_fails_N₁ {θ : MetricData E₁} {ρ : ℝ} (hθ : N₁.IsMetric θ) (hρ : 0 ≤ ρ ∧ ρ ≤ 1)
    (h₁ : θ.length .e₁ = 0) (h₂ : θ.length .e₂ = 0) : ¬ Assumption1Converse N₁ (nmscCF N₁ θ ρ) :=
  fun hc => hc.star univ rfl not_hasTrivialFourBlob_N₁ fun r _ => nmscCF_N₁_of_length_zero hθ hρ h₁ h₂ r

end ECToBlob.Remark52
