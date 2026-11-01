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
computation, the chain of the network multispecies coalescent from the root down. `Phylogenetics/NMSC/Marginal.lean`
sums out the arcs entering the topmost vertex of a set closed under children, against a function of the forests at the
tops (`card_sq_mul_sum_insert`). In normalized form this is `meanOn_insert`, with `stepKernel` the function of the
forests that remains. At a vertex the forest is a small explicit one, and the kernel is explicit:

* one parent: `stepOf_unique_det` for at most one root, `stepOf_unique_two` for two singleton lineages;
* two parents: `stepOf_two_one` for one root, `stepOf_two_two` for two singleton lineages, where the urn of the
  inheritance correlation `ρ` appears.

At the root, `rootMass_singletons` and `rootMass_of_mem` give `1/3` and the decision by a cherry, from
`cherryMass_hubInj_eq_third` and `cherryMass_of_mem`. Unlike a mixture over the corners of the inheritance
(`nmscCF_withPair`), this stays at valid parameters.

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

open Phylogenetics Phylogenetics.RootedNetwork Phylogenetics.NMSC Finset MeasureTheory
open scoped Classical

namespace ECToBlob.Remark52

/-! ### The chain along the network, from the root down -/

section Chain

variable {V E X : Type*} [Fintype V] [Fintype E] [Fintype X] [DecidableEq X]
variable {N : RootedNetwork V E X} {θ : MetricData E} {ρ : ℝ}

/-- The mass of the quartet tree `r` from the forest `F` arriving at the root. -/
def rootMass (r : QuartetTree X) (F : Finset (Finset X)) : ℝ :=
  ∑ H, if ∃ B ∈ r.val, B ∈ H then kingmanAbsorption F H else 0

/-- The mass of a quartet tree, against the forest arriving at the root. -/
theorem cherryMass_eq_sum_rootMass (inj : V → Finset (Finset X)) (r : QuartetTree X) :
    cherryMass N θ ρ inj r = ∑ bot : E → Finset (Finset X), ∑ top : E → Finset (Finset X),
      (∏ v ∈ univ.erase N.root, vertexWeight N θ ρ inj v bot top) *
        rootMass r (arriving N inj top N.root) := by
  unfold cherryMass injDist injWeight rootMass
  have h : ∀ H : Finset (Finset X), (if ∃ B ∈ r.val, B ∈ H then
        ∑ bot : E → Finset (Finset X), ∑ top : E → Finset (Finset X),
          (∏ v ∈ univ.erase N.root, vertexWeight N θ ρ inj v bot top) *
            kingmanAbsorption (arriving N inj top N.root) H else 0) =
      ∑ bot : E → Finset (Finset X), ∑ top : E → Finset (Finset X),
        (∏ v ∈ univ.erase N.root, vertexWeight N θ ρ inj v bot top) *
          (if ∃ B ∈ r.val, B ∈ H then kingmanAbsorption (arriving N inj top N.root) H else 0) := by
    intro H
    split_ifs <;> simp
  simp only [h]
  rw [sum_comm]
  refine sum_congr rfl fun bot _ => ?_
  rw [sum_comm]
  refine sum_congr rfl fun top _ => ?_
  rw [mul_sum]

variable (N) in
/-- The forest `F` injected at the root. -/
def atRoot (F : Finset (Finset X)) : V → Finset (Finset X) := fun v => if v = N.root then F else ∅

omit [Fintype V] [Fintype E] [Fintype X] in
theorem validInj_atRoot {F : Finset (Finset X)} (hF : IsGoodForest F) : ValidInj (atRoot N F) := by
  refine ⟨fun v => ?_, fun u v huv => disjoint_left.2 fun x hxu hxv => ?_⟩
  · unfold atRoot
    split_ifs
    · exact hF
    · exact isGoodForest_empty
  · by_cases hu : u = N.root
    · have hv : v ≠ N.root := fun h => huv (hu.trans h.symm)
      simp [atRoot, hv] at hxv
    · simp [atRoot, hu] at hxu

/-- With the forest `F` injected at the root, the arcs below carry nothing. -/
theorem injDist_atRoot (hN : N.IsPhylogenetic) (hθ : N.IsNormalized θ) (hρ : 0 ≤ ρ)
    {F : Finset (Finset X)} (hF : IsGoodForest F) (H : Finset (Finset X)) :
    injDist N θ ρ (atRoot N F) H = kingmanAbsorption F H := by
  have hv := validInj_atRoot (N := N) hF
  have hmass := sum_sum_injWeight_weak (θ := θ) (ρ := ρ) hN hθ hρ hv
  unfold injDist
  calc _ = ∑ bot : E → Finset (Finset X), ∑ top : E → Finset (Finset X),
        injWeight N θ ρ (atRoot N F) bot top * kingmanAbsorption F H := by
        refine sum_congr rfl fun bot _ => sum_congr rfl fun top _ => ?_
        by_cases hw : injWeight N θ ρ (atRoot N F) bot top = 0
        · simp [hw]
        have hD := downClosed_erase_root (N := N) hN
        have hFr := frontier_of_prod_ne_zero hN hv hD hw
        have htop : ∀ e, top e = ∅ := fun e => by
          by_contra hne
          obtain ⟨A, hA⟩ := nonempty_iff_ne_empty.2 hne
          have het : N.graph.target e ∈ univ.erase N.root :=
            mem_erase.2 ⟨target_ne_root hN e, mem_univ _⟩
          obtain ⟨x, hx⟩ := (hFr.good_top e het).1.1 A hA
          obtain ⟨u, hu, hxu⟩ := hFr.below e het x (mem_lineages.2 ⟨A, hA, hx⟩)
          by_cases hur : u = N.root
          · exact root_notMem_belowSet hN e (mem_belowSet.2 (hur ▸ hu))
          · simp [atRoot, hur] at hxu
        have harr : arriving N (atRoot N F) top N.root = F := by
          unfold arriving atRoot
          simp [htop]
        rw [harr]
      _ = _ := by
        simp only [← sum_mul]
        rw [hmass, one_mul]

/-- The mass from the forest at the root is that of the process with the forest injected there. -/
theorem rootMass_eq_cherryMass (hN : N.IsPhylogenetic) (hθ : N.IsNormalized θ) (hρ : 0 ≤ ρ)
    {F : Finset (Finset X)} (hF : IsGoodForest F) (r : QuartetTree X) :
    rootMass r F = cherryMass N θ ρ (atRoot N F) r := by
  unfold rootMass cherryMass
  simp only [injDist_atRoot hN hθ hρ hF]

/-- A cherry at the root decides the quartet trees. -/
theorem rootMass_of_mem (hN : N.IsPhylogenetic) (hθ : N.IsMetric θ) (hρ : 0 ≤ ρ ∧ ρ ≤ 1)
    {F : Finset (Finset X)} (hF : IsGoodForest F) {C : Finset X} (hC : C ∈ F) (hC2 : #C = 2)
    {r : QuartetTree X} (hCr : C ⊆ r.taxa) : rootMass r F = if C ∈ r.val then 1 else 0 := by
  rw [rootMass_eq_cherryMass hN hθ.isNormalized hρ.1 hF]
  refine cherryMass_of_mem hN hθ hρ (validInj_atRoot hF) (v := N.root) ?_ hC2 hCr
  simpa [atRoot] using hC

/-- Four singletons at the root make the quartet trees equally likely. -/
theorem rootMass_singletons (hN : N.IsPhylogenetic) (hθ : N.IsMetric θ) (hρ : 0 ≤ ρ ∧ ρ ≤ 1)
    {q : Finset X} (hq : #q = 4) {r : QuartetTree X} (hr : r ∈ treesOn q) :
    rootMass r (q.image fun x => ({x} : Finset X)) = 1 / 3 := by
  rw [rootMass_eq_cherryMass hN hθ.isNormalized hρ.1 (isGoodForest_singletons q)]
  have hhub : hubInj N q q N.root = atRoot N (q.image fun x => ({x} : Finset X)) := by
    funext u
    unfold hubInj atRoot
    have : taxaInj N (q \ q) u = ∅ := by
      simp [taxaInj]
    rw [this, empty_union]
  rw [← hhub]
  obtain ⟨a, ha⟩ : q.Nonempty := card_pos.1 (by omega)
  exact cherryMass_hubInj_eq_third hN hθ hρ hq Subset.rfl N.root ha (fun x hx _ => hx) hr

local notation "𝔅" => ((Fintype.card (Finset (Finset X)) : ℕ) : ℝ)

variable (N θ ρ) in
/-- The mean of `φ` under the part of the process on a set `D` closed under children. -/
def meanOn (inj : V → Finset (Finset X)) (D : Finset V) (φ : (E → Finset (Finset X)) → ℝ) : ℝ :=
  (𝔅 ^ #(univ.filter fun e => N.graph.target e ∈ D)) ^ 2 *
      (∑ bot : E → Finset (Finset X), ∑ top : E → Finset (Finset X),
        (∏ u ∈ D, vertexWeight N θ ρ inj u bot top) * φ top) / (𝔅 ^ Fintype.card E) ^ 2

variable (N θ ρ) in
/-- One step of the chain at the vertex `v`, from the forest `F` arriving there, normalized. -/
def stepOf (v : V) (F : Finset (Finset X)) (ψ : (E → Finset (Finset X)) → ℝ) : ℝ :=
  vertexKernel N θ ρ v F ψ / (𝔅 ^ #(arcsInto N v)ᶜ) ^ 2

/-- `overwrite`, with its instance of decidable equality fixed. -/
def ow (S : Finset E) (top t : E → Finset (Finset X)) : E → Finset (Finset X) := overwrite S top t

omit [Fintype V] [Fintype E] [Fintype X] [DecidableEq X] in
theorem ow_of_mem {S : Finset E} {f : E} (hf : f ∈ S) (top t : E → Finset (Finset X)) :
    ow S top t f = t f :=
  overwrite_of_mem hf _ _

omit [Fintype V] [Fintype E] [Fintype X] [DecidableEq X] in
theorem ow_of_notMem {S : Finset E} {f : E} (hf : f ∉ S) (top t : E → Finset (Finset X)) :
    ow S top t f = top f :=
  overwrite_of_notMem hf _ _

variable (N θ ρ) in
/-- The function `φ` of the forests at the top of the arcs, with the arcs entering `v` integrated
out. -/
def stepKernel (inj : V → Finset (Finset X)) (v : V) (φ : (E → Finset (Finset X)) → ℝ)
    (top : E → Finset (Finset X)) : ℝ :=
  stepOf N θ ρ v (arriving N inj top v) fun t => φ (ow (arcsInto N v) top t)

omit [DecidableEq X] in
theorem card_forests_pos : (0 : ℝ) < 𝔅 := by exact_mod_cast Fintype.card_pos

/-- All the vertices but the root: the sum over the histories. -/
theorem meanOn_of_forall_ne (hN : N.IsPhylogenetic) (inj : V → Finset (Finset X)) {D : Finset V}
    (hD : ∀ v, v ∈ D ↔ v ≠ N.root) (φ : (E → Finset (Finset X)) → ℝ) :
    meanOn N θ ρ inj D φ =
      ∑ bot : E → Finset (Finset X), ∑ top : E → Finset (Finset X),
        (∏ u ∈ univ.erase N.root, vertexWeight N θ ρ inj u bot top) * φ top := by
  have hDe : D = univ.erase N.root := by
    ext v
    simp [hD]
  have hall : (univ.filter fun f => N.graph.target f ∈ D) = univ :=
    filter_true_of_mem fun f _ => (hD _).2 (target_ne_root hN f)
  unfold meanOn
  rw [hall, card_univ, mul_comm, mul_div_assoc, div_self, mul_one, hDe]
  exact pow_ne_zero _ (pow_ne_zero _ card_forests_pos.ne')

omit [Fintype V] in
/-- **One step of the chain**: the topmost vertex of `insert v D` is integrated out. -/
theorem meanOn_insert_aux {inj : V → Finset (Finset X)} {D : Finset V} (hD : DownClosed N D) {v : V}
    (hvD : v ∉ D) (hch : ∀ e, N.graph.source e = v → N.graph.target e ∈ D)
    (φ : (E → Finset (Finset X)) → ℝ) :
    meanOn N θ ρ inj (insert v D) φ = meanOn N θ ρ inj D (stepKernel N θ ρ inj v φ) := by
  have hB := card_forests_pos (X := X)
  set c : ℝ := (𝔅 ^ #(arcsInto N v)ᶜ) ^ 2 with hc
  have hc0 : c ≠ 0 := pow_ne_zero _ (pow_ne_zero _ hB.ne')
  have hstep := card_sq_mul_sum_insert (θ := θ) (ρ := ρ) (inj := inj) hD hvD hch φ
  have hker : ∑ bot : E → Finset (Finset X), ∑ top : E → Finset (Finset X),
        (∏ u ∈ D, vertexWeight N θ ρ inj u bot top) *
          vertexKernel N θ ρ v (arriving N inj top v)
            (fun t => φ (overwrite (arcsInto N v) top t)) =
      c * ∑ bot : E → Finset (Finset X), ∑ top : E → Finset (Finset X),
        (∏ u ∈ D, vertexWeight N θ ρ inj u bot top) * stepKernel N θ ρ inj v φ top := by
    rw [mul_sum]
    refine sum_congr rfl fun bot _ => ?_
    rw [mul_sum]
    refine sum_congr rfl fun top _ => ?_
    unfold stepKernel stepOf ow
    rw [← hc]
    field_simp
  have hcard : #(univ.filter fun e => N.graph.target e ∈ insert v D) =
      #(univ.filter fun e => N.graph.target e ∈ D) + #(arcsInto N v) := by
    have := card_filter_target_mem (N := N) (W := insert v D) (v := v) (mem_insert_self _ _)
    rwa [erase_insert hvD] at this
  rw [hker, card_fun_arcs (N := N) (X := X) v] at hstep
  unfold meanOn
  rw [hcard, pow_add]
  congr 1
  set Z := ∑ bot : E → Finset (Finset X), ∑ top : E → Finset (Finset X),
    (∏ u ∈ insert v D, vertexWeight N θ ρ inj u bot top) * φ top
  set Z' := ∑ bot : E → Finset (Finset X), ∑ top : E → Finset (Finset X),
    (∏ u ∈ D, vertexWeight N θ ρ inj u bot top) * stepKernel N θ ρ inj v φ top
  have hZ : (𝔅 ^ #(arcsInto N v)) ^ 2 * Z = Z' := by
    refine mul_left_cancel₀ hc0 ?_
    rw [← hstep, hc]
    ring
  rw [← hZ]
  ring

omit [Fintype V] in
/-- **One step of the chain**, for any instance of decidable equality on the vertices. -/
theorem meanOn_insert [DecidableEq V] {inj : V → Finset (Finset X)} {D : Finset V}
    (hD : DownClosed N D) {v : V} (hvD : v ∉ D)
    (hch : ∀ e, N.graph.source e = v → N.graph.target e ∈ D) (φ : (E → Finset (Finset X)) → ℝ) :
    meanOn N θ ρ inj (insert v D) φ = meanOn N θ ρ inj D (stepKernel N θ ρ inj v φ) := by
  rw [← meanOn_insert_aux hD hvD hch φ]
  congr 1
  ext u
  simp

/-- The mean of a function which is constant on the histories of nonzero weight. -/
theorem meanOn_eq_const (hN : N.IsPhylogenetic) (hθ : N.IsNormalized θ) (hρ : 0 ≤ ρ)
    {inj : V → Finset (Finset X)} (hinj : ValidInj inj) {D : Finset V} (hD : DownClosed N D)
    (hroot : N.root ∉ D) {φ : (E → Finset (Finset X)) → ℝ} {c : ℝ}
    (h : ∀ bot top : E → Finset (Finset X),
      ∏ u ∈ D, vertexWeight N θ ρ inj u bot top ≠ 0 → φ top = c) :
    meanOn N θ ρ inj D φ = c := by
  have hB := card_forests_pos (X := X)
  have hmass := sum_sum_prod_vertexWeight_weak (θ := θ) (ρ := ρ) hN hθ hρ hinj hD hroot
  have hsum : ∑ bot : E → Finset (Finset X), ∑ top : E → Finset (Finset X),
        (∏ u ∈ D, vertexWeight N θ ρ inj u bot top) * φ top =
      c * ∑ bot : E → Finset (Finset X), ∑ top : E → Finset (Finset X),
        ∏ u ∈ D, vertexWeight N θ ρ inj u bot top := by
    rw [mul_sum]
    refine sum_congr rfl fun bot _ => ?_
    rw [mul_sum]
    refine sum_congr rfl fun top _ => ?_
    by_cases hw : ∏ u ∈ D, vertexWeight N θ ρ inj u bot top = 0
    · simp [hw]
    · rw [h bot top hw, mul_comm]
  unfold meanOn
  rw [hsum]
  have hne : (𝔅 ^ Fintype.card E) ^ 2 ≠ 0 := pow_ne_zero _ (pow_ne_zero _ hB.ne')
  rw [div_eq_iff hne, mul_left_comm, hmass]

/-! ### Forests of singletons along an arc -/

omit [Fintype X] in
theorem roots_singletons [Fintype X] (T : Finset X) :
    roots (T.image fun x => ({x} : Finset X)) = T.image fun x => ({x} : Finset X) := by
  refine filter_true_of_mem fun A hA B hB hAB => ?_
  obtain ⟨x, -, rfl⟩ := mem_image.1 hA
  obtain ⟨y, -, rfl⟩ := mem_image.1 hB
  rw [singleton_subset_singleton] at hAB
  rw [hAB]

/-- **Two singleton lineages along an arc**: they coalesce with probability `1 - exp (-t)`. -/
theorem kingmanTransition_singletons {P : Finset X} (hP : #P = 2) (t : ℝ) (G : Finset (Finset X)) :
    kingmanTransition t (P.image fun x => ({x} : Finset X)) G =
      (if G = P.image fun x => ({x} : Finset X) then Real.exp (-t) else 0) +
        if G = insert P (P.image fun x => ({x} : Finset X)) then 1 - Real.exp (-t) else 0 := by
  set F : Finset (Finset X) := P.image fun x => ({x} : Finset X) with hF
  have hgood : IsGoodForest F := isGoodForest_singletons P
  have hlin : lineages F = P := lineages_image_singleton P
  have hcard1 : ∀ A ∈ F, #A = 1 := by
    intro A hA
    obtain ⟨x, -, rfl⟩ := mem_image.1 hA
    exact card_singleton x
  have hPF : P ∉ F := fun h => by
    have := hcard1 P h
    omega
  have hne : F ≠ insert P F := fun h => hPF (h ▸ mem_insert_self P F)
  have hcardF : #(roots F) = 2 := by
    rw [hF, roots_singletons, card_image_of_injective _ singleton_injective, hP]
  by_cases hGF : G = F
  · subst hGF
    rw [ite_eq_left rfl, ite_eq_right hne, add_zero, kingmanTransition_apply_self hgood.1, hcardF]
    norm_num
  by_cases hGi : G = insert P F
  · subst hGi
    rw [ite_eq_right hGF, ite_eq_left rfl, zero_add]
    exact kingmanTransition_singletons_cherry hP t
  rw [ite_eq_right hGF, ite_eq_right hGi, add_zero]
  by_contra hG
  obtain ⟨hgG, hsub, hlG⟩ := kingmanTransition_support_good hgood hG
  rw [hlin] at hlG
  by_cases h2 : ∃ C ∈ G, #C = 2
  · obtain ⟨C, hC, hC2⟩ := h2
    have hCP : C = P := eq_of_subset_of_card_le
      (fun x hx => hlG ▸ mem_lineages.2 ⟨C, hC, hx⟩) (by rw [hP, hC2])
    refine hGi (Subset.antisymm (fun A hA => ?_) (insert_subset (hCP ▸ hC) hsub))
    have hAP : A ⊆ P := fun x hx => hlG ▸ mem_lineages.2 ⟨A, hA, hx⟩
    by_cases hAc : #A = 2
    · rw [eq_of_subset_of_card_le hAP (by rw [hP, hAc])]
      exact mem_insert_self _ _
    · have hApos := (hgG.1.1 A hA).card_pos
      have hle := card_le_card hAP
      obtain ⟨x, rfl⟩ := card_eq_one.1 (by omega : #A = 1)
      refine mem_insert_of_mem (mem_image.2 ⟨x, ?_, rfl⟩)
      exact hAP (mem_singleton_self x)
  · have := hgG.eq_singletons h2
    rw [hlG] at this
    exact hGF this

/-- A forest with at most one root stays along the arcs of `S`. -/
theorem sum_prod_kingman_det (S : Finset E) (ℓ : E → ℝ) {b : E → Finset (Finset X)}
    (hb : ∀ f ∈ S, IsForest (b f) ∧ #(roots (b f)) ≤ 1) (Θ : (E → Finset (Finset X)) → ℝ)
    (hΘ : ∀ t t', (∀ f ∈ S, t f = t' f) → Θ t = Θ t') :
    ∑ t : E → Finset (Finset X), (∏ f ∈ S, kingmanTransition (ℓ f) (b f) (t f)) * Θ t =
      Θ b * 𝔅 ^ #Sᶜ := by
  rw [← sum_ite_forall_mul S b Θ hΘ]
  refine sum_congr rfl fun t _ => ?_
  have h : ∏ f ∈ S, kingmanTransition (ℓ f) (b f) (t f) =
      if ∀ f ∈ S, t f = b f then 1 else 0 := by
    rw [prod_congr rfl fun f hf =>
      kingmanTransition_of_card_roots_le_one (hb f hf).1 (hb f hf).2 (ℓ f) (t f), prod_ite_zero]
    simp
  rw [h]
  split_ifs <;> simp

/-- Two singleton lineages on the arc `f₀` of `S`, and forests with at most one root on the others. -/
theorem sum_prod_kingman_two {S : Finset E} (ℓ : E → ℝ) {b : E → Finset (Finset X)} {f₀ : E}
    (hf₀ : f₀ ∈ S) {P : Finset X} (hP : #P = 2) (hb₀ : b f₀ = P.image fun x => ({x} : Finset X))
    (hb : ∀ f ∈ S, f ≠ f₀ → IsForest (b f) ∧ #(roots (b f)) ≤ 1)
    (Θ : (E → Finset (Finset X)) → ℝ) (hΘ : ∀ t t', (∀ f ∈ S, t f = t' f) → Θ t = Θ t') :
    ∑ t : E → Finset (Finset X), (∏ f ∈ S, kingmanTransition (ℓ f) (b f) (t f)) * Θ t =
      (Real.exp (-ℓ f₀) * Θ b + (1 - Real.exp (-ℓ f₀)) *
        Θ (Function.update b f₀ (insert P (P.image fun x => ({x} : Finset X))))) * 𝔅 ^ #Sᶜ := by
  set F : Finset (Finset X) := P.image fun x => ({x} : Finset X) with hF
  set b' := Function.update b f₀ (insert P F) with hb'
  have hR : ∀ t : E → Finset (Finset X), (∏ f ∈ S.erase f₀, kingmanTransition (ℓ f) (b f) (t f)) =
      if ∀ f ∈ S.erase f₀, t f = b f then 1 else 0 := fun t => by
    rw [prod_congr rfl fun f hf =>
      kingmanTransition_of_card_roots_le_one (hb f (mem_of_mem_erase hf) (ne_of_mem_erase hf)).1
        (hb f (mem_of_mem_erase hf) (ne_of_mem_erase hf)).2 (ℓ f) (t f), prod_ite_zero]
    simp
  have hpt : ∀ t : E → Finset (Finset X),
      (∏ f ∈ S, kingmanTransition (ℓ f) (b f) (t f)) * Θ t =
        Real.exp (-ℓ f₀) * (if ∀ f ∈ S, t f = b f then Θ t else 0) +
          (1 - Real.exp (-ℓ f₀)) * (if ∀ f ∈ S, t f = b' f then Θ t else 0) := by
    intro t
    rw [← mul_prod_erase S _ hf₀, hR, hb₀, kingmanTransition_singletons hP]
    have hiff : ∀ c : E → Finset (Finset X), (∀ f ∈ S, f ≠ f₀ → c f = b f) →
        ((∀ f ∈ S, t f = c f) ↔ t f₀ = c f₀ ∧ ∀ f ∈ S.erase f₀, t f = b f) := by
      intro c hc
      constructor
      · intro h
        refine ⟨h f₀ hf₀, fun f hf => ?_⟩
        rw [h f (mem_of_mem_erase hf), hc f (mem_of_mem_erase hf) (ne_of_mem_erase hf)]
      · rintro ⟨h₁, h₂⟩ f hf
        by_cases hff : f = f₀
        · rw [hff, h₁]
        · rw [h₂ f (mem_erase.2 ⟨hff, hf⟩), hc f hf hff]
    rw [if_congr (hiff b fun _ _ _ => rfl) rfl rfl,
      if_congr (hiff b' fun f _ hff => Function.update_of_ne hff _ _) rfl rfl]
    have hb'0 : b' f₀ = insert P F := Function.update_self _ _ _
    rw [hb₀, hb'0]
    by_cases h₁ : ∀ f ∈ S.erase f₀, t f = b f
    · have h₂ : ∀ c, (t f₀ = c ∧ ∀ f ∈ S.erase f₀, t f = b f) ↔ t f₀ = c := fun c => and_iff_left h₁
      simp only [ite_eq_left h₁, h₂]
      split_ifs <;> ring
    · have h₂ : ∀ c, ¬ (t f₀ = c ∧ ∀ f ∈ S.erase f₀, t f = b f) := fun c h => h₁ h.2
      simp only [ite_eq_right h₁, ite_eq_right (h₂ _)]
      ring
  simp only [hpt]
  rw [sum_add_distrib, ← mul_sum, ← mul_sum, sum_ite_forall_mul S b Θ hΘ,
    sum_ite_forall_mul S b' Θ hΘ]
  ring

/-! ### The allocation at a vertex -/

omit [Fintype V] in
/-- The chain at a vertex, as a sum over the assignments of the roots. -/
theorem stepOf_eq_sum (v : V) (F : Finset (Finset X)) (ψ : (E → Finset (Finset X)) → ℝ) :
    stepOf N θ ρ v F ψ = ∑ a : {A // A ∈ roots F} → {e // N.graph.target e = v},
      allocationWeight ρ (fun e : {e // N.graph.target e = v} => θ.inheritance e.val) a *
        ((∑ t : E → Finset (Finset X),
          (∏ f ∈ arcsInto N v, kingmanTransition (θ.length f) (assignedForest N F v a f) (t f)) *
            ψ t) / 𝔅 ^ #(arcsInto N v)ᶜ) := by
  have hB := card_forests_pos (X := X)
  unfold stepOf
  rw [vertexKernel_eq_sum, sum_div]
  refine sum_congr rfl fun a _ => ?_
  field_simp

omit [Fintype V] [Fintype E] [Fintype X] [DecidableEq X] in
/-- The weight of all lineages on a parent of inheritance one. -/
theorem allocationWeight_const_one {R P : Type*} [Fintype R] [Fintype P] [DecidableEq P]
    (hρ : 0 ≤ ρ) {γ : P → ℝ} {e : P} (he : γ e = 1) : allocationWeight ρ γ (fun _ : R => e) = 1 := by
  rcases isEmpty_or_nonempty R with hR | hR
  · simp [allocationWeight]
  · exact allocationWeight_const_eq_one hρ he

omit [Fintype V] [Fintype E] in
/-- All the roots on the parent `p`: all the forest is on it. -/
theorem assignedForest_const_self (F : Finset (Finset X)) {v : V}
    (p : {e // N.graph.target e = v}) : assignedForest N F v (fun _ => p) p.val = F := by
  obtain ⟨e, he⟩ := p
  simp only [assignedForest, he, ↓reduceDIte, filter_true]
  ext A
  rw [mem_forestBelow]
  constructor
  · exact fun h => h.1
  · intro hA
    obtain ⟨R, hR, hAR⟩ := exists_mem_roots_subset hA
    exact ⟨hA, R, mem_image.2 ⟨⟨R, hR⟩, mem_univ _, rfl⟩, hAR⟩

omit [Fintype V] [Fintype E] in
/-- All the roots on the parent `p`: nothing on the other arcs. -/
theorem assignedForest_const_ne (F : Finset (Finset X)) {v : V}
    (p : {e // N.graph.target e = v}) {f : E} (hf : f ≠ p.val) :
    assignedForest N F v (fun _ => p) f = ∅ := by
  unfold assignedForest
  split_ifs with h
  · have hfil : (univ.filter fun _ : {A // A ∈ roots F} => p = ⟨f, h⟩) = ∅ :=
      filter_false_of_mem fun _ _ h' => hf (congrArg Subtype.val h').symm
    rw [hfil, image_empty]
    ext A
    simp [mem_forestBelow]
  · rfl

omit [Fintype V] [Fintype E] in
theorem roots_singleton_singleton (x : X) : roots ({{x}} : Finset (Finset X)) = {{x}} := by
  have h := roots_singletons ({x} : Finset X)
  rwa [image_singleton] at h

omit [Fintype V] [Fintype E] [Fintype X] in
theorem isForest_singleton_singleton (x : X) : IsForest ({{x}} : Finset (Finset X)) := by
  have h := isGoodForest_singletons ({x} : Finset X)
  rw [image_singleton] at h
  exact h.1

omit [Fintype V] [Fintype E] in
theorem isForest_empty_and_roots :
    IsForest (∅ : Finset (Finset X)) ∧ #(roots (∅ : Finset (Finset X))) ≤ 1 :=
  ⟨isForest_empty, by simp [roots]⟩

/-! ### A vertex with one parent -/

omit [Fintype V] in
/-- **A vertex with one parent**, and a forest with at most one root. -/
theorem stepOf_unique_det (hρ : 0 ≤ ρ) {v : V} {e : E} (he : N.graph.target e = v)
    (hu : ∀ f, N.graph.target f = v → f = e) (hγ : θ.inheritance e = 1)
    {F : Finset (Finset X)} (hF : IsForest F) (hr : #(roots F) ≤ 1)
    (ψ : (E → Finset (Finset X)) → ℝ)
    (hψ : ∀ t t', (∀ f ∈ arcsInto N v, t f = t' f) → ψ t = ψ t') :
    stepOf N θ ρ v F ψ = ψ fun _ => F := by
  have hB := card_forests_pos (X := X)
  set p : {e // N.graph.target e = v} := ⟨e, he⟩ with hp
  rw [stepOf_eq_sum, Fintype.sum_eq_single (fun _ => p)
    fun a ha => absurd (funext fun r => Subtype.ext (hu _ (a r).property)) ha]
  rw [allocationWeight_const_one hρ (γ := fun e : {e // N.graph.target e = v} => θ.inheritance e.val)
    hγ, one_mul]
  have hbe : ∀ f ∈ arcsInto N v, assignedForest N F v (fun _ => p) f = F := fun f hf => by
    rw [hu f (mem_arcsInto.1 hf)]
    exact assignedForest_const_self F p
  rw [sum_prod_kingman_det _ _ (fun f hf => by rw [hbe f hf]; exact ⟨hF, hr⟩) ψ hψ,
    mul_div_assoc, div_self (pow_ne_zero _ hB.ne'), mul_one]
  exact hψ _ _ hbe

omit [Fintype V] in
/-- **A vertex with one parent**, and two singleton lineages. -/
theorem stepOf_unique_two (hρ : 0 ≤ ρ) {v : V} {e : E} (he : N.graph.target e = v)
    (hu : ∀ f, N.graph.target f = v → f = e) (hγ : θ.inheritance e = 1)
    {P : Finset X} (hP : #P = 2) (ψ : (E → Finset (Finset X)) → ℝ)
    (hψ : ∀ t t', (∀ f ∈ arcsInto N v, t f = t' f) → ψ t = ψ t') :
    stepOf N θ ρ v (P.image fun x => ({x} : Finset X)) ψ =
      Real.exp (-θ.length e) * ψ (fun _ => P.image fun x => ({x} : Finset X)) +
        (1 - Real.exp (-θ.length e)) *
          ψ fun _ => insert P (P.image fun x => ({x} : Finset X)) := by
  have hB := card_forests_pos (X := X)
  set F : Finset (Finset X) := P.image fun x => ({x} : Finset X) with hF
  set p : {e // N.graph.target e = v} := ⟨e, he⟩ with hp
  rw [stepOf_eq_sum, Fintype.sum_eq_single (fun _ => p)
    fun a ha => absurd (funext fun r => Subtype.ext (hu _ (a r).property)) ha]
  rw [allocationWeight_const_one hρ (γ := fun e : {e // N.graph.target e = v} => θ.inheritance e.val)
    hγ, one_mul]
  have hbe : ∀ f ∈ arcsInto N v, assignedForest N F v (fun _ => p) f = F := fun f hf => by
    rw [hu f (mem_arcsInto.1 hf)]
    exact assignedForest_const_self F p
  have heS : e ∈ arcsInto N v := mem_arcsInto.2 he
  rw [sum_prod_kingman_two _ heS hP (hbe e heS)
    (fun f hf hne => absurd (hu f (mem_arcsInto.1 hf)) hne) ψ hψ,
    mul_div_assoc, div_self (pow_ne_zero _ hB.ne'), mul_one]
  congr 2
  · exact hψ _ _ hbe
  · refine hψ _ _ fun f hf => ?_
    rw [hu f (mem_arcsInto.1 hf), Function.update_self]

/-! ### A vertex with two parents -/

/-- The forests `A`, `B` on the arcs `k₁`, `k₂`. -/
def pairFn (k₁ : E) (A : Finset (Finset X)) (k₂ : E) (B : Finset (Finset X)) :
    E → Finset (Finset X) :=
  fun f => if f = k₁ then A else if f = k₂ then B else ∅

omit [Fintype V] [Fintype E] [Fintype X] [DecidableEq X] in
theorem pairFn_left (k₁ : E) (A : Finset (Finset X)) (k₂ : E) (B : Finset (Finset X)) :
    pairFn k₁ A k₂ B k₁ = A := by
  simp [pairFn]

omit [Fintype V] [Fintype E] [Fintype X] [DecidableEq X] in
theorem pairFn_right {k₁ k₂ : E} (hk : k₁ ≠ k₂) (A B : Finset (Finset X)) :
    pairFn k₁ A k₂ B k₂ = B := by
  simp [pairFn, hk.symm]

/-- The forests of the arcs entering `v`, from an assignment of the roots to the two parents. -/
theorem sum_div_det {S : Finset E} (ℓ : E → ℝ) {b : E → Finset (Finset X)}
    (hb : ∀ f ∈ S, IsForest (b f) ∧ #(roots (b f)) ≤ 1) (Θ : (E → Finset (Finset X)) → ℝ)
    (hΘ : ∀ t t', (∀ f ∈ S, t f = t' f) → Θ t = Θ t') :
    (∑ t : E → Finset (Finset X), (∏ f ∈ S, kingmanTransition (ℓ f) (b f) (t f)) * Θ t) / 𝔅 ^ #Sᶜ =
      Θ b := by
  rw [sum_prod_kingman_det S ℓ hb Θ hΘ, mul_div_assoc, div_self (pow_ne_zero _ card_forests_pos.ne'),
    mul_one]

omit [Fintype V] [Fintype E] [Fintype X] [DecidableEq X] in
/-- The assignments of one lineage to two parents. -/
theorem sum_assign_one {R P : Type*} [Subsingleton R] [Fintype (R → P)] (r₀ : R) {p₁ p₂ : P}
    (hne : p₁ ≠ p₂) (hP : ∀ p, p = p₁ ∨ p = p₂) (g : (R → P) → ℝ) :
    ∑ a, g a = g (fun _ => p₁) + g fun _ => p₂ := by
  refine Fintype.sum_eq_add _ _ (fun h => hne (congrFun h r₀)) ?_
  rintro a ⟨ha₁, ha₂⟩
  exfalso
  rcases hP (a r₀) with h | h
  · exact ha₁ (funext fun r => by rw [Subsingleton.elim r r₀, h])
  · exact ha₂ (funext fun r => by rw [Subsingleton.elim r r₀, h])

omit [Fintype V] [Fintype E] [Fintype X] [DecidableEq X] in
/-- One lineage takes a parent with its inheritance. -/
theorem allocationWeight_one {R P : Type*} [Fintype R] [Subsingleton R] [Fintype P] [DecidableEq P]
    (r₀ : R) {γ : P → ℝ} (p : P) : allocationWeight ρ γ (fun _ : R => p) = γ p := by
  have : Nonempty R := ⟨r₀⟩
  have hcard : Fintype.card R = 1 := Fintype.card_eq_one_iff.2 ⟨r₀, fun r => Subsingleton.elim r r₀⟩
  rw [allocationWeight_const, hcard]
  simp

omit [Fintype V] in
/-- The forests on the parents when all the roots of `F`, with at most one root, take the parent `k₁`
or `k₂`. -/
theorem forall_assigned_const {v : V} {k₁ k₂ : E} (hu : ∀ f, N.graph.target f = v → f = k₁ ∨ f = k₂)
    (hk : k₁ ≠ k₂) {F : Finset (Finset X)} (h₁ : N.graph.target k₁ = v) (h₂ : N.graph.target k₂ = v) :
    (∀ f ∈ arcsInto N v, assignedForest N F v (fun _ => ⟨k₁, h₁⟩) f = pairFn k₁ F k₂ ∅ f) ∧
      ∀ f ∈ arcsInto N v, assignedForest N F v (fun _ => ⟨k₂, h₂⟩) f = pairFn k₁ ∅ k₂ F f := by
  constructor
  · intro f hf
    rcases hu f (mem_arcsInto.1 hf) with rfl | rfl
    · rw [pairFn_left]
      exact assignedForest_const_self _ ⟨_, h₁⟩
    · rw [pairFn_right hk]
      exact assignedForest_const_ne _ ⟨_, h₁⟩ hk.symm
  · intro f hf
    rcases hu f (mem_arcsInto.1 hf) with rfl | rfl
    · rw [pairFn_left]
      exact assignedForest_const_ne _ ⟨_, h₂⟩ hk
    · rw [pairFn_right hk]
      exact assignedForest_const_self _ ⟨_, h₂⟩

omit [Fintype V] in
/-- **A vertex with two parents**, and one root. -/
theorem stepOf_two_one {v : V} {k₁ k₂ : E} (h₁ : N.graph.target k₁ = v)
    (h₂ : N.graph.target k₂ = v) (hk : k₁ ≠ k₂) (hu : ∀ f, N.graph.target f = v → f = k₁ ∨ f = k₂)
    {F : Finset (Finset X)} (hF : IsForest F) {A : Finset X} (hA : roots F = {A})
    (ψ : (E → Finset (Finset X)) → ℝ)
    (hψ : ∀ t t', (∀ f ∈ arcsInto N v, t f = t' f) → ψ t = ψ t') :
    stepOf N θ ρ v F ψ = θ.inheritance k₁ * ψ (pairFn k₁ F k₂ ∅) +
      θ.inheritance k₂ * ψ (pairFn k₁ ∅ k₂ F) := by
  have hmem : A ∈ roots F := by simp [hA]
  have hsub : Subsingleton {A // A ∈ roots F} := ⟨fun a b => Subtype.ext (by
    have ha : a.val ∈ ({A} : Finset (Finset X)) := hA ▸ a.property
    have hb : b.val ∈ ({A} : Finset (Finset X)) := hA ▸ b.property
    rw [mem_singleton.1 ha, mem_singleton.1 hb])⟩
  let r₀ : {A // A ∈ roots F} := ⟨A, hmem⟩
  have hne : (⟨k₁, h₁⟩ : {e // N.graph.target e = v}) ≠ ⟨k₂, h₂⟩ := fun h =>
    hk (congrArg Subtype.val h)
  have hP : ∀ p : {e // N.graph.target e = v}, p = ⟨k₁, h₁⟩ ∨ p = ⟨k₂, h₂⟩ := fun p =>
    (hu _ p.property).imp (fun h => Subtype.ext h) fun h => Subtype.ext h
  obtain ⟨hb₁, hb₂⟩ := forall_assigned_const (F := F) hu hk h₁ h₂
  have hcr : IsForest F ∧ #(roots F) ≤ 1 := ⟨hF, by simp [hA]⟩
  rw [stepOf_eq_sum, sum_assign_one r₀ hne hP, allocationWeight_one r₀, allocationWeight_one r₀]
  rw [sum_div_det _ (fun f hf => ?_) ψ hψ, sum_div_det _ (fun f hf => ?_) ψ hψ, hψ _ _ hb₁,
    hψ _ _ hb₂]
  · rw [hb₂ f hf]
    rcases hu f (mem_arcsInto.1 hf) with rfl | rfl
    · rw [pairFn_left]
      exact isForest_empty_and_roots
    · rw [pairFn_right hk]
      exact hcr
  · rw [hb₁ f hf]
    rcases hu f (mem_arcsInto.1 hf) with rfl | rfl
    · rw [pairFn_left]
      exact hcr
    · rw [pairFn_right hk]
      exact isForest_empty_and_roots

omit [Fintype V] [Fintype E] [Fintype X] [DecidableEq X] in
/-- Two lineages on different parents. -/
theorem allocationWeight_two_distinct {R P : Type*} [Fintype R] [Fintype P] [DecidableEq P]
    {γ : P → ℝ} {a : R → P} {r₁ r₂ : R} (hr : r₁ ≠ r₂) (hR : ∀ r, r = r₁ ∨ r = r₂)
    (ha : a r₁ ≠ a r₂) : allocationWeight ρ γ a = (1 - ρ) * γ (a r₁) * γ (a r₂) := by
  have hcard : Fintype.card R = 2 := by
    rw [← card_univ]
    exact card_eq_two.2 ⟨r₁, r₂, hr, by
      ext r
      simpa using hR r⟩
  have him : univ.image a = {a r₁, a r₂} := by
    ext p
    simp only [mem_image, mem_univ, true_and, mem_insert, mem_singleton]
    constructor
    · rintro ⟨r, rfl⟩
      rcases hR r with rfl | rfl <;> simp
    · rintro (rfl | rfl)
      · exact ⟨r₁, rfl⟩
      · exact ⟨r₂, rfl⟩
  have hfib₁ : #(univ.filter fun r => a r = a r₁) = 1 := by
    rw [card_eq_one]
    refine ⟨r₁, ?_⟩
    ext r
    simp only [mem_filter, mem_univ, true_and, mem_singleton]
    constructor
    · intro h
      rcases hR r with rfl | rfl
      · rfl
      · exact absurd h.symm ha
    · rintro rfl
      rfl
  have hfib₂ : #(univ.filter fun r => a r = a r₂) = 1 := by
    rw [card_eq_one]
    refine ⟨r₂, ?_⟩
    ext r
    simp only [mem_filter, mem_univ, true_and, mem_singleton]
    constructor
    · intro h
      rcases hR r with rfl | rfl
      · exact absurd h ha
      · rfl
    · rintro rfl
      rfl
  unfold allocationWeight
  rw [him, prod_pair ha, card_pair ha, hfib₁, hfib₂, hcard]
  simp
  ring

omit [Fintype V] [Fintype E] [Fintype X] [DecidableEq X] in
/-- Two lineages on one parent. -/
theorem allocationWeight_two_const {R P : Type*} [Fintype R] [Nonempty R] [Fintype P] [DecidableEq P]
    {γ : P → ℝ} (hcard : Fintype.card R = 2) (e : P) :
    allocationWeight ρ γ (fun _ : R => e) = γ e * ((1 - ρ) * γ e + ρ) := by
  rw [allocationWeight_const, hcard]
  simp

omit [Fintype V] [Fintype E] [Fintype X] [DecidableEq X] in
/-- The assignments of two lineages to two parents. -/
theorem sum_assign_two {R P : Type*} [DecidableEq R] [Fintype (R → P)] [Fintype P] {r₁ r₂ : R}
    (hr : r₁ ≠ r₂)
    (hR : ∀ r, r = r₁ ∨ r = r₂) {p₁ p₂ : P} (hne : p₁ ≠ p₂) (hP : ∀ p, p = p₁ ∨ p = p₂)
    (g : (R → P) → ℝ) :
    ∑ a, g a = g (fun r => if r = r₁ then p₁ else p₁) + g (fun r => if r = r₁ then p₁ else p₂) +
      (g (fun r => if r = r₁ then p₂ else p₁) + g fun r => if r = r₁ then p₂ else p₂) := by
  let e : P × P ≃ (R → P) :=
    { toFun := fun pq r => if r = r₁ then pq.1 else pq.2
      invFun := fun a => (a r₁, a r₂)
      left_inv := fun ⟨p, q⟩ => by simp [hr.symm]
      right_inv := fun a => funext fun r => by
        rcases hR r with rfl | rfl
        · simp
        · simp [hr.symm] }
  have hs : ∀ h : P → ℝ, ∑ p, h p = h p₁ + h p₂ := fun h =>
    Fintype.sum_eq_add p₁ p₂ hne fun p hp => (hP p).elim (fun h' => absurd h' hp.1)
      fun h' => absurd h' hp.2
  rw [← e.sum_comp g, Fintype.sum_prod_type]
  simp only [hs]
  rfl

omit [Fintype X] [DecidableEq X] in
theorem forestBelow_image_singleton [Fintype X] [DecidableEq X] {P : Finset X} {z : X} (hz : z ∈ P) :
    forestBelow (P.image fun x => ({x} : Finset X)) {{z}} = {{z}} := by
  ext B
  rw [mem_forestBelow, mem_singleton]
  constructor
  · rintro ⟨hB, C, hC, hBC⟩
    obtain ⟨w, -, rfl⟩ := mem_image.1 hB
    rw [mem_singleton.1 hC, singleton_subset_singleton] at hBC
    rw [hBC]
  · rintro rfl
    exact ⟨mem_image_of_mem _ hz, {z}, mem_singleton_self _, Subset.rfl⟩

omit [Fintype V] [Fintype E] in
/-- The lineage `x`, with root `rx`, takes the parent `k`. -/
theorem assignedForest_split {v : V} {k : E} (hk : N.graph.target k = v) {P : Finset X} {x : X}
    (hx : x ∈ P) {R : Finset (Finset X)} (hRP : R = P.image fun x => ({x} : Finset X))
    (a : {A // A ∈ roots R} → {e // N.graph.target e = v}) (rx : {A // A ∈ roots R})
    (hrx : rx.val = {x}) (h : ∀ r, a r = ⟨k, hk⟩ ↔ r = rx) :
    assignedForest N R v a k = {{x}} := by
  subst hRP
  simp only [assignedForest, hk, ↓reduceDIte]
  have hfil : (univ.filter fun r => a r = ⟨k, hk⟩) = {rx} := by
    ext r
    simp [h]
  rw [hfil, image_singleton, hrx]
  exact forestBelow_image_singleton hx

omit [Fintype V] in
/-- **A vertex with two parents**, and two singleton lineages. -/
theorem stepOf_two_two {v : V} {k₁ k₂ : E} (h₁ : N.graph.target k₁ = v)
    (h₂ : N.graph.target k₂ = v) (hk : k₁ ≠ k₂) (hu : ∀ f, N.graph.target f = v → f = k₁ ∨ f = k₂)
    {x y : X} (hxy : x ≠ y) (ψ : (E → Finset (Finset X)) → ℝ)
    (hψ : ∀ t t', (∀ f ∈ arcsInto N v, t f = t' f) → ψ t = ψ t') :
    stepOf N θ ρ v (({x, y} : Finset X).image fun x => ({x} : Finset X)) ψ =
      θ.inheritance k₁ * ((1 - ρ) * θ.inheritance k₁ + ρ) *
          (Real.exp (-θ.length k₁) *
              ψ (pairFn k₁ (({x, y} : Finset X).image fun x => ({x} : Finset X)) k₂ ∅) +
            (1 - Real.exp (-θ.length k₁)) *
              ψ (pairFn k₁ (insert {x, y} (({x, y} : Finset X).image fun x => ({x} : Finset X))) k₂ ∅)) +
        (1 - ρ) * θ.inheritance k₁ * θ.inheritance k₂ * ψ (pairFn k₁ {{x}} k₂ {{y}}) +
        ((1 - ρ) * θ.inheritance k₂ * θ.inheritance k₁ * ψ (pairFn k₁ {{y}} k₂ {{x}}) +
          θ.inheritance k₂ * ((1 - ρ) * θ.inheritance k₂ + ρ) *
            (Real.exp (-θ.length k₂) *
                ψ (pairFn k₁ ∅ k₂ (({x, y} : Finset X).image fun x => ({x} : Finset X))) +
              (1 - Real.exp (-θ.length k₂)) *
                ψ (pairFn k₁ ∅ k₂
                  (insert {x, y} (({x, y} : Finset X).image fun x => ({x} : Finset X)))))) := by
  have hB := card_forests_pos (X := X)
  have hPc : #({x, y} : Finset X) = 2 := card_pair hxy
  generalize hF : (({x, y} : Finset X).image fun x => ({x} : Finset X)) = F
  have hroots : roots F = F := by
    rw [← hF]
    exact roots_singletons _
  have hmx : ({x} : Finset X) ∈ roots F := by
    rw [hroots, ← hF]
    simp
  have hmy : ({y} : Finset X) ∈ roots F := by
    rw [hroots, ← hF]
    simp
  let rx : {A // A ∈ roots F} := ⟨{x}, hmx⟩
  let ry : {A // A ∈ roots F} := ⟨{y}, hmy⟩
  have hrne : rx ≠ ry := fun h => hxy (singleton_injective (congrArg Subtype.val h))
  have hR : ∀ r : {A // A ∈ roots F}, r = rx ∨ r = ry := by
    rintro ⟨A, hA⟩
    have hA' : A ∈ F := roots_subset F hA
    rw [← hF] at hA'
    obtain ⟨z, hz, rfl⟩ := mem_image.1 hA'
    rcases mem_insert.1 hz with rfl | hz
    · exact Or.inl rfl
    · obtain rfl := mem_singleton.1 hz
      exact Or.inr rfl
  have hcard : Fintype.card {A // A ∈ roots F} = 2 := by
    rw [← card_univ]
    exact card_eq_two.2 ⟨rx, ry, hrne, by
      ext r
      simpa using hR r⟩
  have hNe : Nonempty {A // A ∈ roots F} := ⟨rx⟩
  set p₁ : {e // N.graph.target e = v} := ⟨k₁, h₁⟩ with hp₁
  set p₂ : {e // N.graph.target e = v} := ⟨k₂, h₂⟩ with hp₂
  have hne : p₁ ≠ p₂ := fun h => hk (congrArg Subtype.val h)
  have hP : ∀ p : {e // N.graph.target e = v}, p = p₁ ∨ p = p₂ := fun p =>
    (hu _ p.property).imp (fun h => Subtype.ext h) fun h => Subtype.ext h
  obtain ⟨hb₁, hb₂⟩ := forall_assigned_const (F := F) hu hk h₁ h₂
  have hS₁ : k₁ ∈ arcsInto N v := mem_arcsInto.2 h₁
  have hS₂ : k₂ ∈ arcsInto N v := mem_arcsInto.2 h₂
  have hc₁ := sum_prod_kingman_two (S := arcsInto N v) θ.length (f₀ := k₁) hS₁ hPc
    (b := assignedForest N F v fun _ => p₁)
    ((assignedForest_const_self F p₁).trans hF.symm)
    (fun f hf hne' => by
      rw [hb₁ f hf]
      rcases hu f (mem_arcsInto.1 hf) with rfl | rfl
      · exact absurd rfl hne'
      · rw [pairFn_right hk]
        exact isForest_empty_and_roots) ψ hψ
  have hc₂ := sum_prod_kingman_two (S := arcsInto N v) θ.length (f₀ := k₂) hS₂ hPc
    (b := assignedForest N F v fun _ => p₂)
    ((assignedForest_const_self F p₂).trans hF.symm)
    (fun f hf hne' => by
      rw [hb₂ f hf]
      rcases hu f (mem_arcsInto.1 hf) with rfl | rfl
      · rw [pairFn_left]
        exact isForest_empty_and_roots
      · exact absurd rfl hne') ψ hψ
  rw [hF] at hc₁ hc₂
  have hS1 : ∀ z, IsForest ({{z}} : Finset (Finset X)) ∧ #(roots ({{z}} : Finset (Finset X))) ≤ 1 :=
    fun z => by
      have h := roots_singletons ({z} : Finset X)
      have h' := isGoodForest_singletons ({z} : Finset X)
      rw [image_singleton] at h h'
      rw [h]
      exact ⟨h'.1, by simp⟩
  -- the two lineages on different parents
  have hsplit : ∀ (p q : {e // N.graph.target e = v}) (u w : X) (ru rw : {A // A ∈ roots F}),
      ru.val = {u} → rw.val = {w} → u ∈ ({x, y} : Finset X) → w ∈ ({x, y} : Finset X) → ru ≠ rw →
      (∀ r, r = ru ∨ r = rw) → p ≠ q →
      (∀ (a : {A // A ∈ roots F} → {e // N.graph.target e = v}), a ru = p → a rw = q →
        assignedForest N F v a p.val = {{u}} ∧ assignedForest N F v a q.val = {{w}}) := by
    intro p q u w ru rw hu' hw' hux hwx hne' hall hpq a hap haq
    constructor
    · refine assignedForest_split p.property hux hF.symm a ru hu' fun r => ?_
      constructor
      · intro h
        rcases hall r with h' | h'
        · exact h'
        · exfalso
          rw [h', haq] at h
          exact hpq h.symm
      · rintro rfl
        exact hap
    · refine assignedForest_split q.property hwx hF.symm a rw hw' fun r => ?_
      constructor
      · intro h
        rcases hall r with h' | h'
        · exfalso
          rw [h', hap] at h
          exact hpq h
        · exact h'
      · rintro rfl
        exact haq
  have hallxy : ∀ r, r = ry ∨ r = rx := fun r => (hR r).symm
  rw [stepOf_eq_sum, sum_assign_two hrne hR hne hP]
  simp only [ite_self]
  rw [allocationWeight_two_const hcard, allocationWeight_two_const hcard,
    allocationWeight_two_distinct hrne hR (by simpa [hrne.symm] using hne),
    allocationWeight_two_distinct hrne hR (by simpa [hrne.symm] using hne.symm)]
  simp only [ite_true, ite_eq_right hrne.symm]
  have h₁₂ := hsplit p₁ p₂ x y rx ry rfl rfl (by simp) (by simp) hrne hR hne
    (fun r => if r = rx then p₁ else p₂) (by simp) (by simp [hrne.symm])
  have h₂₁ := hsplit p₂ p₁ x y rx ry rfl rfl (by simp) (by simp) hrne hR hne.symm
    (fun r => if r = rx then p₂ else p₁) (by simp) (by simp [hrne.symm])
  have hv₁₂ : ∀ f ∈ arcsInto N v, assignedForest N F v (fun r => if r = rx then p₁ else p₂) f =
      pairFn k₁ {{x}} k₂ {{y}} f := fun f hf => by
    rcases hu f (mem_arcsInto.1 hf) with rfl | rfl
    · rw [pairFn_left]
      exact h₁₂.1
    · rw [pairFn_right hk]
      exact h₁₂.2
  have hv₂₁ : ∀ f ∈ arcsInto N v, assignedForest N F v (fun r => if r = rx then p₂ else p₁) f =
      pairFn k₁ {{y}} k₂ {{x}} f := fun f hf => by
    rcases hu f (mem_arcsInto.1 hf) with rfl | rfl
    · rw [pairFn_left]
      exact h₂₁.2
    · rw [pairFn_right hk]
      exact h₂₁.1
  have e₁ : ψ (Function.update (assignedForest N F v fun _ => p₁) k₁ (insert {x, y} F)) =
      ψ (pairFn k₁ (insert {x, y} F) k₂ ∅) := hψ _ _ fun f hf => by
    rcases hu f (mem_arcsInto.1 hf) with rfl | rfl
    · rw [pairFn_left, Function.update_self]
    · rw [pairFn_right hk, Function.update_of_ne hk.symm]
      exact assignedForest_const_ne _ p₁ hk.symm
  have e₂ : ψ (Function.update (assignedForest N F v fun _ => p₂) k₂ (insert {x, y} F)) =
      ψ (pairFn k₁ ∅ k₂ (insert {x, y} F)) := hψ _ _ fun f hf => by
    rcases hu f (mem_arcsInto.1 hf) with rfl | rfl
    · rw [pairFn_left, Function.update_of_ne hk]
      exact assignedForest_const_ne _ p₂ hk
    · rw [pairFn_right hk, Function.update_self]
  have d₁₂ := sum_div_det (S := arcsInto N v) θ.length
    (b := assignedForest N F v fun r => if r = rx then p₁ else p₂) (fun f hf => by
      rw [hv₁₂ f hf]
      rcases hu f (mem_arcsInto.1 hf) with rfl | rfl
      · rw [pairFn_left]
        exact hS1 x
      · rw [pairFn_right hk]
        exact hS1 y) ψ hψ
  have d₂₁ := sum_div_det (S := arcsInto N v) θ.length
    (b := assignedForest N F v fun r => if r = rx then p₂ else p₁) (fun f hf => by
      rw [hv₂₁ f hf]
      rcases hu f (mem_arcsInto.1 hf) with rfl | rfl
      · rw [pairFn_left]
        exact hS1 y
      · rw [pairFn_right hk]
        exact hS1 x) ψ hψ
  rw [d₁₂, d₂₁, hc₁, hc₂, mul_div_assoc, mul_div_assoc, div_self (pow_ne_zero _ hB.ne'), mul_one,
    mul_one, hψ _ _ hb₁, hψ _ _ hb₂, hψ _ _ hv₁₂, hψ _ _ hv₂₁, e₁, e₂]

/-! ### The chain on a function of the forests -/

omit [Fintype V] [Fintype E] [Fintype X] [DecidableEq X] in
/-- A function of the overwritten forests depends on the coordinates in `S`. -/
theorem ow_dep (S : Finset E) (top : E → Finset (Finset X)) (φ : (E → Finset (Finset X)) → ℝ)
    (t t' : E → Finset (Finset X)) (h : ∀ f ∈ S, t f = t' f) : φ (ow S top t) = φ (ow S top t') := by
  congr 1
  funext f
  by_cases hf : f ∈ S
  · rw [ow_of_mem hf, ow_of_mem hf, h f hf]
  · rw [ow_of_notMem hf, ow_of_notMem hf]

omit [Fintype V] in
/-- The taxa at their leaves: the forest arriving at a leaf with no children is its singleton. -/
theorem arriving_leaf (hN : N.IsPhylogenetic) (x : X) (hs : ∀ e, N.graph.source e ≠ N.leaf x)
    (top : E → Finset (Finset X)) : arriving N (taxaInj N univ) top (N.leaf x) = {{x}} := by
  have hF : (univ.filter fun e => N.graph.source e = N.leaf x) = ∅ :=
    filter_false_of_mem fun e _ => hs e
  have hT : taxaInj N univ (N.leaf x) = {{x}} := by
    unfold taxaInj
    have : (univ.filter fun z => z ∈ univ ∧ N.leaf z = N.leaf x) = {x} := by
      ext z
      simp [hN.leaf_injective.eq_iff]
    rw [this, image_singleton]
  unfold arriving
  rw [hF, hT]
  simp

omit [Fintype V] in
/-- On a history of nonzero weight, the forest at the top of the parent of a leaf is the singleton of
its taxon. -/
theorem top_eq_of_leaf (hN : N.IsPhylogenetic) {D : Finset V} (x : X) {p : E}
    (hu : ∀ f, N.graph.target f = N.leaf x → f = p) (hp : N.graph.target p = N.leaf x)
    (hs : ∀ e, N.graph.source e ≠ N.leaf x) (hmem : N.leaf x ∈ D) {bot top : E → Finset (Finset X)}
    (h : ∏ u ∈ D, vertexWeight N θ ρ (taxaInj N univ) u bot top ≠ 0) : top p = {{x}} := by
  have hw := prod_ne_zero_iff.1 h _ hmem
  have harr := arriving_leaf hN x hs top
  have hsing := isGoodForest_singletons ({x} : Finset X)
  rw [image_singleton] at hsing
  have hg : IsGoodForest (arriving N (taxaInj N univ) top (N.leaf x)) := by
    rw [harr]
    exact hsing
  obtain ⟨hgood, -, hmem'⟩ := good_of_vertexWeight_ne_zero hg hw
  have hgt := (hgood p hp).2
  have hlin : lineages (top p) = {x} := by
    ext z
    have hz := hmem' z
    rw [harr] at hz
    have hr : z ∈ lineages ({{x}} : Finset (Finset X)) ↔ z ∈ ({x} : Finset X) := by
      simp
    constructor
    · intro hzp
      exact hr.1 (hz.1 ⟨p, hp, hzp⟩)
    · intro hzx
      obtain ⟨e, he, hze⟩ := hz.2 (hr.2 hzx)
      rw [hu e he] at hze
      exact hze
  have hno2 : ¬ ∃ C ∈ top p, #C = 2 := by
    rintro ⟨C, hC, hC2⟩
    have hsub : C ⊆ {x} := fun z hz => hlin ▸ mem_lineages.2 ⟨C, hC, hz⟩
    have := card_le_card hsub
    rw [hC2, card_singleton] at this
    omega
  have := hgt.eq_singletons hno2
  rwa [hlin, image_singleton] at this

omit [Fintype V] [Fintype E] in
/-- No lineage is injected at an internal vertex. -/
theorem taxaInj_eq_empty {v : V} (h : ∀ x, N.leaf x ≠ v) : taxaInj N univ v = ∅ := by
  unfold taxaInj
  rw [image_eq_empty]
  exact filter_false_of_mem fun x _ hx => h x hx.2

omit [Fintype V] [Fintype X] in
/-- The forest arriving at an internal vertex with the given child arcs. -/
theorem arriving_eq_biUnion {inj : V → Finset (Finset X)} {v : V} {S : Finset E}
    (hS : ∀ e, N.graph.source e = v ↔ e ∈ S) (top : E → Finset (Finset X)) :
    arriving N inj top v = inj v ∪ S.biUnion top := by
  unfold arriving
  congr 2
  ext e
  simp [hS]

omit [Fintype V] [Fintype X] [DecidableEq X] in
/-- An arc that is the only parent of its target is a tree arc. -/
theorem isTreeArc_of_unique {e : E} (hu : ∀ f, N.graph.target f = N.graph.target e → f = e) :
    N.IsTreeArc e := by
  unfold RootedNetwork.IsTreeArc
  rw [indegree_eq_card, card_eq_one]
  refine ⟨e, ?_⟩
  ext f
  rw [mem_arcsInto, mem_singleton]
  exact ⟨hu f, fun h => h ▸ rfl⟩

omit [Fintype V] [Fintype X] [DecidableEq X] in
/-- The sum over the two parents of a reticulation. -/
theorem sum_ite_target_pair (γ : E → ℝ) {v : V} {k₁ k₂ : E}
    (h₁ : N.graph.target k₁ = v) (h₂ : N.graph.target k₂ = v) (hk : k₁ ≠ k₂)
    (hu : ∀ f, N.graph.target f = v → f = k₁ ∨ f = k₂) :
    (∑ e, if N.graph.target e = v then γ e else 0) = γ k₁ + γ k₂ := by
  rw [sum_eq_add k₁ k₂ hk]
  · simp only [h₁, h₂, ↓reduceIte]
  · rintro f - ⟨hf₁, hf₂⟩
    refine ite_eq_right fun hf => ?_
    exact (hu f hf).elim (fun h' => absurd h' hf₁) fun h' => absurd h' hf₂
  · exact fun h' => absurd (mem_univ _) h'
  · exact fun h' => absurd (mem_univ _) h'

omit [Fintype V] [Fintype X] [DecidableEq X] in
/-- The two parents of a reticulation have total inheritance one. -/
theorem inheritance_add_eq_one (hθ : N.IsNormalized θ) {v : V} {k₁ k₂ : E}
    (h₁ : N.graph.target k₁ = v) (h₂ : N.graph.target k₂ = v) (hk : k₁ ≠ k₂)
    (hu : ∀ f, N.graph.target f = v → f = k₁ ∨ f = k₂) :
    θ.inheritance k₁ + θ.inheritance k₂ = 1 := by
  have hdeg : 2 ≤ N.graph.indegree v := by
    rw [indegree_eq_card]
    exact one_lt_card.2 ⟨k₁, mem_arcsInto.2 h₁, k₂, mem_arcsInto.2 h₂, hk⟩
  rw [← sum_ite_target_pair θ.inheritance h₁ h₂ hk hu]
  exact hθ.2 v hdeg

end Chain

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

/-- The lineages of `a`, `b` before they coalesce. -/
abbrev Fab : Finset (Finset (Fin 4)) := ({0, 1} : Finset (Fin 4)).image fun x => ({x} : Finset (Fin 4))

/-- The lineages of `a`, `b` after they coalesce. -/
abbrev Cab : Finset (Finset (Fin 4)) := insert ({0, 1} : Finset (Fin 4)) Fab

/-- The lineages of `c`, `d` before they coalesce. -/
abbrev Fcd : Finset (Finset (Fin 4)) := ({2, 3} : Finset (Fin 4)).image fun x => ({x} : Finset (Fin 4))

/-- All the lineages at the root. -/
abbrev Fall : Finset (Finset (Fin 4)) := (univ : Finset (Fin 4)).image fun x => ({x} : Finset (Fin 4))

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
