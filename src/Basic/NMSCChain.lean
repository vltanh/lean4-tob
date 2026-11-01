module

public import Phylogenetics.NMSC.Analytic
public import Phylogenetics.NMSC.Level1.Arms
public import Phylogenetics.NMSC.TreeCF
public import Phylogenetics.NMSC.Witness
public import Phylogenetics.NMSC.DisplayedTreeModel

/-!
# The chain of the network multispecies coalescent, on a concrete network

Computing concordance factors on a concrete network by following the coalescent from the root down, with no mixture over the corners of the inheritance, so at valid parameters.
`Phylogenetics/NMSC/Marginal.lean` sums out the arcs entering the topmost vertex of a set closed under children, against a function of the forests at the tops (`card_sq_mul_sum_insert`). In normalized form this is
`meanOn_insert`, with `stepKernel` the function of the forests that remains. At a vertex the forest is a small explicit one, and the kernel is explicit:

* one parent: `stepOf_unique_det` for at most one root, `stepOf_unique_two` for two singleton lineages;
* two parents: `stepOf_two_one` for one root, `stepOf_two_two` for two singleton lineages, where the urn of the
  inheritance correlation `ρ` appears.

At the root, `rootMass_singletons` and `rootMass_of_mem` give `1/3` and the decision by a cherry, from
`cherryMass_hubInj_eq_third` and `cherryMass_of_mem`. `cherryMass_eq_meanOn_lift` starts the computation.

`RootedNetwork.isPhylogenetic_of_rank` gives the laws of a phylogenetic network on a concrete graph, from a rank function.

These results do not depend on any paper here. ECToBlob's Remarks 3.3 and 5.2, NANUQ's counterexamples and the examples of Allman et al. 2023 use them. They belong in the library `Phylogenetics`.
-/

@[expose] public noncomputable section

open Phylogenetics Phylogenetics.RootedNetwork Phylogenetics.NMSC Finset MeasureTheory
open scoped Classical

namespace Phylogenetics.RootedNetwork

variable {V E X : Type*} [Fintype V] [Fintype E] [Fintype X]

/-- The laws of a phylogenetic network, from a rank function that increases along the arcs. -/
theorem isPhylogenetic_of_rank {N : RootedNetwork V E X} (rank : V → ℕ)
    (hrank : ∀ e, rank (N.graph.source e) < rank (N.graph.target e))
    (h0 : ∀ e, N.graph.target e ≠ N.root)
    (h1 : ∀ v, v ≠ N.root → ∃ e, N.graph.target e = v)
    (hinj : Function.Injective N.leaf)
    (hleaf : ∀ x, ∃ e, N.graph.target e = N.leaf x ∧ ∀ f, N.graph.target f = N.leaf x → f = e)
    (hs : ∀ x e, N.graph.source e ≠ N.leaf x)
    (hint : ∀ v, (∀ x, N.leaf x ≠ v) → ∃ e, N.graph.source e = v) : N.IsPhylogenetic := by
  have hreach : ∀ n v, rank v = n → N.graph.Reaches N.root v := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro v hv
      by_cases hvr : v = N.root
      · exact hvr ▸ .refl
      · obtain ⟨e, he⟩ := h1 v hvr
        have hlt := hrank e
        rw [he, hv] at hlt
        exact (ih _ hlt _ rfl).tail ⟨e, rfl, he⟩
  have hTrans : ∀ u v, Relation.TransGen N.graph.Adj u v → rank u < rank v := by
    intro u v h
    induction h with
    | single h =>
      obtain ⟨e, rfl, rfl⟩ := h
      exact hrank e
    | tail _ h ih =>
      obtain ⟨e, rfl, rfl⟩ := h
      exact ih.trans (hrank e)
  refine ⟨inferInstance, inferInstance, inferInstance, fun v h => lt_irrefl _ (hTrans _ _ h),
    fun v => hreach _ v rfl, ?_, ?_, hinj, ?_, ?_⟩
  · unfold DirectedMultigraph.indegree
    rw [Set.ncard_eq_zero (Set.toFinite _)]
    exact Set.eq_empty_of_forall_notMem fun e he => h0 e he
  · intro v hv
    obtain ⟨e, he⟩ := h1 v hv
    unfold DirectedMultigraph.indegree
    exact (Set.ncard_pos (Set.toFinite _)).2 ⟨e, he⟩
  · intro x
    obtain ⟨e, he, hu⟩ := hleaf x
    unfold DirectedMultigraph.indegree
    rw [Set.ncard_eq_one]
    exact ⟨e, Set.ext fun f => ⟨fun hf => hu f hf, fun hf => by rw [Set.mem_singleton_iff.1 hf]; exact he⟩⟩
  · intro v
    unfold DirectedMultigraph.outdegree
    rw [Set.ncard_eq_zero (Set.toFinite _)]
    constructor
    · intro h
      by_contra hne
      push Not at hne
      obtain ⟨e, he⟩ := hint v hne
      have : e ∈ {e | N.graph.source e = v} := he
      rw [h] at this
      exact this
    · rintro ⟨x, rfl⟩
      exact Set.eq_empty_of_forall_notMem fun e he => hs x e he

end Phylogenetics.RootedNetwork

namespace Phylogenetics.NMSC.Chain

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

/-- The Markov property as a mean. -/
theorem cherryMass_eq_meanOn_lift (hN : N.IsPhylogenetic) (hθ : N.IsNormalized θ) (hρ : 0 ≤ ρ)
    {inj : V → Finset (Finset X)} (hinj : ValidInj inj) {D : Finset V} (hD : DownClosed N D)
    (hroot : N.root ∉ D) (r : QuartetTree X) :
    cherryMass N θ ρ inj r = meanOn N θ ρ inj D fun top => cherryMass N θ ρ (liftSet N D inj top) r := by
  have hB : (0 : ℝ) < ((Fintype.card (Finset (Finset X)) : ℕ) : ℝ) := by exact_mod_cast Fintype.card_pos
  have hM := setMass_mul_cherryMass hN hθ hρ hinj hD hroot r
  have hpos := setMass_pos (X := X) (N := N) D
  unfold meanOn
  rw [← hM]
  unfold setMass arcsIn
  field_simp

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

end Phylogenetics.NMSC.Chain
