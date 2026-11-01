module

public import Phylogenetics.NMSC.Witness
public import Phylogenetics.NMSC.InducedSuppress

/-!
# Comparisons along the chain of the network multispecies coalescent

`historyWeight` is the law of a Markov chain up a network, one vertex at a time (`Phylogenetics.NMSC.card_sq_mul_sum_insert`). Here a function `φ` of the forests at the tops of the arcs is compared along this chain: `stageMass D φ` is the mean of `φ` after
the vertices of a set `D` closed under children, up to the constant `(|forests| ^ |E|) ^ 2`. If the kernel at a vertex `v` lifts `φ` to `φ'` on every history of nonzero weight, then `stageMass D φ ≤ stageMass (insert v D) φ'`: `stageMass_le_insert`; and if it takes `φ'` to `φ`, they are
equal: `stageMass_eq_insert`.

* The kernel at one vertex: `vertexKernel_overwrite_eq`, for a function of the next state that is constant on it; `vertexKernel_one_arc`, at a vertex of one parent arc; `kernel_two_arcs_eq`, at correlation `0`, for two lineages at a vertex of two parent arcs of inheritance `1/2`.
* At the root: `fullMass`, the mean of a function over the whole process, and `absVal r F`, the probability that the forest `F` arriving at the root gives a gene tree with a cherry of `r` (`cherryMass_eq_fullMass`).
* `fullMass_automorphism`: the mean under an automorphism of the network that permutes the lineages.
-/

@[expose] public noncomputable section

open Phylogenetics Phylogenetics.RootedNetwork Phylogenetics.NMSC Finset
open scoped Classical

namespace AllmanEtAl2023.KernelBounds

variable {V E X : Type*} [Fintype V] [Fintype E] [Fintype X] [DecidableEq X]
variable {N : RootedNetwork V E X} {θ : MetricData E} {ρ : ℝ}

variable (N θ ρ) in
/-- The mean of `φ` after the vertices `D`, up to the constant `(|forests| ^ |E|) ^ 2`. -/
def stageMass (inj : V → Finset (Finset X)) (D : Finset V) (φ : (E → Finset (Finset X)) → ℝ) : ℝ :=
  ((Fintype.card (Finset (Finset X)) : ℝ) ^ #(univ.filter fun e => N.graph.target e ∈ D)) ^ 2 *
    ∑ bot : E → Finset (Finset X), ∑ top : E → Finset (Finset X),
      (∏ u ∈ D, vertexWeight N θ ρ inj u bot top) * φ top

/-- The mean of a constant. -/
theorem stageMass_const (hN : N.IsPhylogenetic) (hθ : N.IsNormalized θ) (hρ : 0 ≤ ρ)
    {inj : V → Finset (Finset X)} (hinj : ValidInj inj) {D : Finset V} (hD : DownClosed N D) (hroot : N.root ∉ D)
    (c : ℝ) :
    stageMass N θ ρ inj D (fun _ => c) = c * ((Fintype.card (Finset (Finset X)) : ℝ) ^ Fintype.card E) ^ 2 := by
  have h := sum_sum_prod_vertexWeight_weak (θ := θ) (ρ := ρ) hN hθ hρ hinj hD hroot
  unfold stageMass
  simp only [← sum_mul]
  rw [← h]
  ring

omit [Fintype V] in
/-- The mean is homogeneous. -/
theorem stageMass_const_mul (inj : V → Finset (Finset X)) (D : Finset V) (q : ℝ) (φ : (E → Finset (Finset X)) → ℝ) :
    stageMass N θ ρ inj D (fun t => q * φ t) = q * stageMass N θ ρ inj D φ := by
  unfold stageMass
  simp only [mul_sum]
  refine sum_congr rfl fun bot _ => sum_congr rfl fun top _ => ?_
  ring

omit [Fintype V] in
/-- **One step of the chain.** If the kernel at `v` lifts `φ` to `φ'` on the histories of nonzero weight, the mean of `φ` after `D` is at most that of `φ'` after
`insert v D`. -/
theorem stageMass_le_insert (hθ : N.IsWeakMetric θ) (hρ : 0 ≤ ρ ∧ ρ ≤ 1) {inj : V → Finset (Finset X)} {D : Finset V}
    (hD : DownClosed N D) {v : V} (hvD : v ∉ D) (hch : ∀ e, N.graph.source e = v → N.graph.target e ∈ D)
    {φ φ' : (E → Finset (Finset X)) → ℝ}
    (hκ : ∀ bot top : E → Finset (Finset X), ∏ u ∈ D, vertexWeight N θ ρ inj u bot top ≠ 0 →
      φ top * ((Fintype.card (Finset (Finset X)) : ℝ) ^ #(arcsInto N v)ᶜ) ^ 2 ≤
        vertexKernel N θ ρ v (arriving N inj top v) fun t => φ' (overwrite (arcsInto N v) top t)) :
    stageMass N θ ρ inj D φ ≤ stageMass N θ ρ inj (insert v D) φ' := by
  have hB : (0 : ℝ) < Fintype.card (Finset (Finset X)) := by exact_mod_cast Fintype.card_pos
  set B : ℝ := (Fintype.card (Finset (Finset X)) : ℝ) with hBdef
  have hstep := card_sq_mul_sum_insert (θ := θ) (ρ := ρ) (inj := inj) hD hvD hch φ'
  set S := ∑ bot : E → Finset (Finset X), ∑ top : E → Finset (Finset X),
    (∏ u ∈ D, vertexWeight N θ ρ inj u bot top) * φ top with hS
  set S' := ∑ bot : E → Finset (Finset X), ∑ top : E → Finset (Finset X),
    (∏ u ∈ insert v D, vertexWeight N θ ρ inj u bot top) * φ' top with hS'
  have hM : (Fintype.card (E → Finset (Finset X)) : ℝ) = B ^ #(arcsInto N v) * B ^ #(arcsInto N v)ᶜ :=
    card_fun_arcs (N := N) v
  set A := B ^ #(arcsInto N v) with hA
  set C := B ^ #(arcsInto N v)ᶜ with hC
  have h1 : C ^ 2 * S ≤ ∑ bot : E → Finset (Finset X), ∑ top : E → Finset (Finset X),
      (∏ u ∈ D, vertexWeight N θ ρ inj u bot top) *
        vertexKernel N θ ρ v (arriving N inj top v) (fun t => φ' (overwrite (arcsInto N v) top t)) := by
    rw [hS, mul_sum]
    refine sum_le_sum fun bot _ => ?_
    rw [mul_sum]
    refine sum_le_sum fun top _ => ?_
    by_cases hg : ∏ u ∈ D, vertexWeight N θ ρ inj u bot top = 0
    · simp [hg]
    · calc C ^ 2 * ((∏ u ∈ D, vertexWeight N θ ρ inj u bot top) * φ top)
          = (∏ u ∈ D, vertexWeight N θ ρ inj u bot top) * (φ top * C ^ 2) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left (hκ bot top hg)
            (prod_nonneg fun u _ => vertexWeight_nonneg_weak hθ hρ inj u bot top)
  rw [← hstep, hM] at h1
  have hC0 : 0 < C ^ 2 := by positivity
  have h2 : S ≤ A ^ 2 * S' := by
    refine le_of_mul_le_mul_left ?_ hC0
    calc C ^ 2 * S ≤ _ := h1
      _ = C ^ 2 * (A ^ 2 * S') := by ring
  have hcard : #(univ.filter fun e => N.graph.target e ∈ insert v D) =
      #(univ.filter fun e => N.graph.target e ∈ D) + #(arcsInto N v) := by
    have := card_filter_target_mem (N := N) (W := insert v D) (v := v) (mem_insert_self _ _)
    rwa [erase_insert hvD] at this
  unfold stageMass
  rw [hcard, pow_add]
  calc (B ^ #(univ.filter fun e => N.graph.target e ∈ D)) ^ 2 * S
      ≤ (B ^ #(univ.filter fun e => N.graph.target e ∈ D)) ^ 2 * (A ^ 2 * S') :=
        mul_le_mul_of_nonneg_left h2 (by positivity)
    _ = _ := by ring

/-! ### The kernel at one vertex -/

omit [Fintype V] in
/-- The kernel at a vertex is monotone. -/
theorem vertexKernel_mono (hθ : N.IsWeakMetric θ) (hρ : 0 ≤ ρ ∧ ρ ≤ 1) (v : V) (F : Finset (Finset X))
    {ψ ψ' : (E → Finset (Finset X)) → ℝ}
    (h : ∀ b t : E → Finset (Finset X), allocationFactor N θ ρ F v b ≠ 0 →
      ∏ f ∈ arcsInto N v, kingmanTransition (θ.length f) (b f) (t f) ≠ 0 → ψ t ≤ ψ' t) :
    vertexKernel N θ ρ v F ψ ≤ vertexKernel N θ ρ v F ψ' := by
  unfold vertexKernel
  refine sum_le_sum fun b _ => ?_
  by_cases hb : allocationFactor N θ ρ F v b = 0
  · simp [hb]
  refine mul_le_mul_of_nonneg_left (sum_le_sum fun t _ => ?_) (allocationFactor_nonneg_weak hθ hρ F v b)
  by_cases ht : ∏ f ∈ arcsInto N v, kingmanTransition (θ.length f) (b f) (t f) = 0
  · simp [ht]
  · exact mul_le_mul_of_nonneg_left (h b t hb ht) (prod_nonneg fun e _ => kingmanTransition_nonneg (hθ.1 e) _ _)

omit [Fintype V] in
/-- A lower bound of the test function on the support bounds the kernel. -/
theorem le_vertexKernel (hN : N.IsPhylogenetic) (hθ : N.IsWeakMetric θ) (hρ : 0 ≤ ρ ∧ ρ ≤ 1) {v : V}
    (hv : v ≠ N.root) {F : Finset (Finset X)} (hF : IsForest F) {ψ : (E → Finset (Finset X)) → ℝ} {c : ℝ}
    (h : ∀ b t : E → Finset (Finset X), allocationFactor N θ ρ F v b ≠ 0 →
      ∏ f ∈ arcsInto N v, kingmanTransition (θ.length f) (b f) (t f) ≠ 0 → c ≤ ψ t) :
    c * ((Fintype.card (Finset (Finset X)) : ℝ) ^ #(arcsInto N v)ᶜ) ^ 2 ≤ vertexKernel N θ ρ v F ψ := by
  rw [← vertexKernel_const hN hθ.isNormalized hρ.1 hv hF c]
  exact vertexKernel_mono hθ hρ v F h

/-- Two distinct roots `{a}`, `{b}` and the arcs into `v`. -/
theorem roots_pair {a b : X} (hab : a ≠ b) : roots ({{a}, {b}} : Finset (Finset X)) = {{a}, {b}} := by
  ext A
  simp only [mem_roots, mem_insert, mem_singleton]
  constructor
  · exact fun h => h.1
  · refine fun h => ⟨h, fun B hB hAB => ?_⟩
    rcases h with rfl | rfl <;> rcases hB with rfl | rfl
    · rfl
    · exact absurd (singleton_subset_singleton.1 hAB) hab
    · exact absurd (singleton_subset_singleton.1 hAB) hab.symm
    · rfl

omit [Fintype X] in
/-- The forest `{{a}, {b}}` does not have the cluster `{a, b}`. -/
theorem pair_notMem_pair' {a b : X} (hab : a ≠ b) : ({a, b} : Finset X) ∉ ({{a}, {b}} : Finset (Finset X)) := by
  simp only [mem_insert, mem_singleton, not_or]
  constructor
  · intro h
    have : b ∈ ({a} : Finset X) := h ▸ (by simp)
    exact hab (mem_singleton.1 this).symm
  · intro h
    have : a ∈ ({b} : Finset X) := h ▸ (by simp)
    exact hab (mem_singleton.1 this)

omit [Fintype X] in
/-- The forest `{{a}, {b}}` is a good forest. -/
theorem isGoodForest_pair {a b : X} : IsGoodForest ({{a}, {b}} : Finset (Finset X)) := by
  have := isGoodForest_singletons (L := X) ({a, b} : Finset X)
  convert this using 1
  ext A
  simp only [mem_insert, mem_singleton, mem_image]
  constructor
  · rintro (rfl | rfl)
    · exact ⟨a, Or.inl rfl, rfl⟩
    · exact ⟨b, Or.inr rfl, rfl⟩
  · rintro ⟨x, (rfl | rfl), rfl⟩
    · exact Or.inl rfl
    · exact Or.inr rfl

omit [Fintype X] in
/-- A forest on two lineages that have not merged. -/
theorem eq_pair_of_lineages {F : Finset (Finset X)} (hF : IsGoodForest F) {a b : X} (hab : a ≠ b)
    (hlin : lineages F = {a, b}) (hnot : ({a, b} : Finset X) ∉ F) : F = {{a}, {b}} := by
  have hcard : #({a, b} : Finset X) = 2 := card_pair hab
  ext A
  simp only [mem_insert, mem_singleton]
  constructor
  · intro hA
    have h1 := card_eq_one_of_mem_of_notMem hF.1 hlin hcard hnot hA
    obtain ⟨x, rfl⟩ := card_eq_one.1 h1
    have hx : x ∈ lineages F := mem_lineages.2 ⟨_, hA, mem_singleton_self x⟩
    rw [hlin] at hx
    rcases mem_insert.1 hx with rfl | hx
    · exact Or.inl rfl
    · rw [mem_singleton.1 hx]
      exact Or.inr rfl
  · have hmem : ∀ x ∈ ({a, b} : Finset X), ({x} : Finset X) ∈ F := fun x hx => by
      rw [← hlin] at hx
      obtain ⟨B, hB, hxB⟩ := mem_lineages.1 hx
      exact hF.singleton_mem hB hxB
    rintro (rfl | rfl)
    · exact hmem _ (by simp)
    · exact hmem _ (by simp)

omit [Fintype V] in
/-- The chain at a vertex with a test function that fixes the forest at the top of one arc entering `v`. -/
theorem sum_prod_kingman_mul_ite {v : V} {e : E} (he : N.graph.target e = v) {b : E → Finset (Finset X)}
    (hb : ∀ f ∈ arcsInto N v, IsForest (b f)) (G : Finset (Finset X)) :
    ∑ t : E → Finset (Finset X),
        (∏ f ∈ arcsInto N v, kingmanTransition (θ.length f) (b f) (t f)) * (if t e = G then 1 else 0) =
      kingmanTransition (θ.length e) (b e) G * (Fintype.card (Finset (Finset X)) : ℝ) ^ #(arcsInto N v)ᶜ := by
  have heS : e ∈ arcsInto N v := mem_arcsInto.2 he
  have hinner := sum_prod_mem (arcsInto N v) (fun f τ =>
    kingmanTransition (θ.length f) (b f) τ * if f = e then (if τ = G then (1 : ℝ) else 0) else 1)
  have hprod : ∀ t : E → Finset (Finset X),
      ∏ f ∈ arcsInto N v, (kingmanTransition (θ.length f) (b f) (t f) *
          if f = e then (if t f = G then (1 : ℝ) else 0) else 1) =
        (∏ f ∈ arcsInto N v, kingmanTransition (θ.length f) (b f) (t f)) *
          if t e = G then 1 else 0 := fun t => by
    rw [prod_mul_distrib, prod_ite_eq' _ e, ite_eq_left heS]
  simp only [hprod] at hinner
  rw [hinner, prod_eq_single_of_mem e heS fun f hf hfe => by
    simp only [hfe, ↓reduceIte, mul_one]
    exact kingmanTransition_sum (hb f hf) _]
  simp

omit [Fintype V] [Fintype E] in
/-- An assignment of all roots to `e` puts the forest at the bottom of `e`. -/
theorem assignedForest_of_forall {F : Finset (Finset X)} {v : V} {e : E} (he : N.graph.target e = v)
    {a' : {A // A ∈ roots F} → {e // N.graph.target e = v}} (h : ∀ r, a' r = ⟨e, he⟩) :
    assignedForest N F v a' e = F := by
  simp only [assignedForest, he, ↓reduceDIte]
  have hfil : (univ.filter fun r => a' r = ⟨e, he⟩) = univ := filter_true_of_mem fun r _ => h r
  rw [hfil]
  ext A
  rw [mem_forestBelow]
  constructor
  · exact fun h => h.1
  · intro hA
    obtain ⟨R, hR, hAR⟩ := exists_mem_roots_subset hA
    exact ⟨hA, R, mem_image.2 ⟨⟨R, hR⟩, mem_univ _, rfl⟩, hAR⟩

omit [Fintype V] in
/-- The kernel from an assignment has total mass one, up to the number of values of the other arcs. -/
theorem sum_prod_kingman_assigned {F : Finset (Finset X)} (hF : IsForest F) {v : V}
    (a' : {A // A ∈ roots F} → {e // N.graph.target e = v}) :
    ∑ t : E → Finset (Finset X), ∏ f ∈ arcsInto N v, kingmanTransition (θ.length f) (assignedForest N F v a' f) (t f) =
      (Fintype.card (Finset (Finset X)) : ℝ) ^ #(arcsInto N v)ᶜ :=
  sum_prod_of_sum_eq_one _ _ fun f _ => kingmanTransition_sum (isForest_assignedForest hF v a' f) _

/-! ### Equalities -/

omit [Fintype V] in
/-- **One step of the chain, as an equality.** If the kernel at `v` takes `φ'` to `φ` on the histories of nonzero weight, the mean of `φ` after `D` is that of `φ'` after `insert v D`. -/
theorem stageMass_eq_insert {inj : V → Finset (Finset X)} {D : Finset V} (hD : DownClosed N D) {v : V} (hvD : v ∉ D)
    (hch : ∀ e, N.graph.source e = v → N.graph.target e ∈ D) {φ φ' : (E → Finset (Finset X)) → ℝ}
    (hκ : ∀ bot top : E → Finset (Finset X), ∏ u ∈ D, vertexWeight N θ ρ inj u bot top ≠ 0 →
      φ top * ((Fintype.card (Finset (Finset X)) : ℝ) ^ #(arcsInto N v)ᶜ) ^ 2 =
        vertexKernel N θ ρ v (arriving N inj top v) fun t => φ' (overwrite (arcsInto N v) top t)) :
    stageMass N θ ρ inj D φ = stageMass N θ ρ inj (insert v D) φ' := by
  have hB : (0 : ℝ) < Fintype.card (Finset (Finset X)) := by exact_mod_cast Fintype.card_pos
  set B : ℝ := (Fintype.card (Finset (Finset X)) : ℝ) with hBdef
  have hstep := card_sq_mul_sum_insert (θ := θ) (ρ := ρ) (inj := inj) hD hvD hch φ'
  set S := ∑ bot : E → Finset (Finset X), ∑ top : E → Finset (Finset X),
    (∏ u ∈ D, vertexWeight N θ ρ inj u bot top) * φ top with hS
  set S' := ∑ bot : E → Finset (Finset X), ∑ top : E → Finset (Finset X),
    (∏ u ∈ insert v D, vertexWeight N θ ρ inj u bot top) * φ' top with hS'
  have hM : (Fintype.card (E → Finset (Finset X)) : ℝ) = B ^ #(arcsInto N v) * B ^ #(arcsInto N v)ᶜ :=
    card_fun_arcs (N := N) v
  set A := B ^ #(arcsInto N v) with hA
  set C := B ^ #(arcsInto N v)ᶜ with hC
  have h1 : C ^ 2 * S = ∑ bot : E → Finset (Finset X), ∑ top : E → Finset (Finset X),
      (∏ u ∈ D, vertexWeight N θ ρ inj u bot top) *
        vertexKernel N θ ρ v (arriving N inj top v) (fun t => φ' (overwrite (arcsInto N v) top t)) := by
    rw [hS, mul_sum]
    refine sum_congr rfl fun bot _ => ?_
    rw [mul_sum]
    refine sum_congr rfl fun top _ => ?_
    by_cases hg : ∏ u ∈ D, vertexWeight N θ ρ inj u bot top = 0
    · simp [hg]
    · rw [← hκ bot top hg]
      ring
  rw [← hstep, hM] at h1
  have hC0 : C ^ 2 ≠ 0 := by positivity
  have h2 : S = A ^ 2 * S' := by
    refine mul_left_cancel₀ hC0 ?_
    rw [h1]
    ring
  have hcard : #(univ.filter fun e => N.graph.target e ∈ insert v D) =
      #(univ.filter fun e => N.graph.target e ∈ D) + #(arcsInto N v) := by
    have := card_filter_target_mem (N := N) (W := insert v D) (v := v) (mem_insert_self _ _)
    rwa [erase_insert hvD] at this
  unfold stageMass
  rw [hcard, pow_add]
  calc (B ^ #(univ.filter fun e => N.graph.target e ∈ D)) ^ 2 * S
      = (B ^ #(univ.filter fun e => N.graph.target e ∈ D)) ^ 2 * (A ^ 2 * S') := by rw [h2]
    _ = _ := by ring

omit [Fintype V] in
/-- The mean of two functions that agree on the histories of nonzero weight. -/
theorem stageMass_congr {inj : V → Finset (Finset X)} {D : Finset V} {φ φ' : (E → Finset (Finset X)) → ℝ}
    (h : ∀ bot top : E → Finset (Finset X), ∏ u ∈ D, vertexWeight N θ ρ inj u bot top ≠ 0 → φ top = φ' top) :
    stageMass N θ ρ inj D φ = stageMass N θ ρ inj D φ' := by
  unfold stageMass
  congr 1
  refine sum_congr rfl fun bot _ => sum_congr rfl fun top _ => ?_
  by_cases hg : ∏ u ∈ D, vertexWeight N θ ρ inj u bot top = 0
  · simp [hg]
  · rw [h bot top hg]

omit [Fintype V] in
/-- The mean of a finite sum. -/
theorem stageMass_sum {ι : Type*} (inj : V → Finset (Finset X)) (D : Finset V) (s : Finset ι)
    (φ : ι → (E → Finset (Finset X)) → ℝ) :
    stageMass N θ ρ inj D (fun t => ∑ i ∈ s, φ i t) = ∑ i ∈ s, stageMass N θ ρ inj D (φ i) := by
  unfold stageMass
  simp only [mul_sum]
  exact (sum_congr rfl fun bot _ => sum_comm).trans sum_comm

/-- The mean after `W₂` of a function of the forests after `W₁`, for `W₁ ⊆ W₂`, is the mean after `W₁`. -/
theorem stageMass_marginal (hN : N.IsPhylogenetic) (hθ : N.IsNormalized θ) (hρ : 0 ≤ ρ)
    {inj : V → Finset (Finset X)} (hinj : ValidInj inj) {W₁ W₂ : Finset V}
    (hW₁ : DownClosed N W₁) (hW₂ : DownClosed N W₂) (hsub : W₁ ⊆ W₂) (hroot : N.root ∉ W₂)
    (φ : (E → Finset (Finset X)) → ℝ) (hφ : ∀ t t', (∀ f, N.graph.target f ∈ W₁ → t f = t' f) → φ t = φ t') :
    stageMass N θ ρ inj W₂ φ = stageMass N θ ρ inj W₁ φ :=
  sum_mul_marginal hN hθ hρ hinj hW₁ hW₂ hsub hroot φ hφ

omit [Fintype V] in
/-- A cluster arriving at `v` is at the top of an arc entering `v`, on a history of nonzero weight. -/
theorem exists_mem_top_of_vertexWeight_ne_zero {inj : V → Finset (Finset X)} {v : V} {bot top : E → Finset (Finset X)}
    (hg : IsGoodForest (arriving N inj top v)) (hw : vertexWeight N θ ρ inj v bot top ≠ 0) {C : Finset X}
    (hC : C ∈ arriving N inj top v) : ∃ e, N.graph.target e = v ∧ C ∈ top e := by
  obtain ⟨hgood, -, -⟩ := good_of_vertexWeight_ne_zero hg hw
  obtain ⟨a, ha⟩ := exists_assignment (left_ne_zero_of_mul hw)
  obtain ⟨R, hR, hCR⟩ := exists_mem_roots_subset hC
  let r : {A // A ∈ roots (arriving N inj top v)} := ⟨R, hR⟩
  have hft : N.graph.target (a r).val = v := (a r).property
  have hCb : C ∈ bot (a r).val := by
    rw [ha (a r), mem_forestBelow]
    exact ⟨hC, R, mem_image.2 ⟨r, mem_filter.2 ⟨mem_univ _, rfl⟩, rfl⟩, hCR⟩
  have hK : kingmanTransition (θ.length (a r).val) (bot (a r).val) (top (a r).val) ≠ 0 :=
    prod_ne_zero_iff.1 (right_ne_zero_of_mul hw) _ (mem_arcsInto.2 hft)
  exact ⟨_, hft, (kingmanTransition_support_good (hgood _ hft).1 hK).2.1 hCb⟩

/-- **The kernel at `v` of a function of the next state, which is constant on it.** -/
theorem vertexKernel_overwrite_eq (hN : N.IsPhylogenetic) (hθ : N.IsWeakMetric θ) (hρ : 0 ≤ ρ ∧ ρ ≤ 1)
    {inj : V → Finset (Finset X)} (hinj : ValidInj inj) {D : Finset V} (hD : DownClosed N D) {v : V} (hvD : v ∉ D)
    (hv : v ≠ N.root) (hch : ∀ e, N.graph.source e = v → N.graph.target e ∈ D) {bot top : E → Finset (Finset X)}
    (hw : ∏ u ∈ D, vertexWeight N θ ρ inj u bot top ≠ 0) {c : ℝ} {φ' : (E → Finset (Finset X)) → ℝ}
    (h : ∀ bot' top' : E → Finset (Finset X), (∀ f, N.graph.target f ≠ v → top' f = top f) →
      (∀ x, (∃ e, N.graph.target e = v ∧ x ∈ lineages (top' e)) ↔ x ∈ lineages (arriving N inj top v)) →
      (∀ C ∈ arriving N inj top v, ∃ e, N.graph.target e = v ∧ C ∈ top' e) →
      Frontier N inj (insert v D) bot' top' → φ' top' = c) :
    c * ((Fintype.card (Finset (Finset X)) : ℝ) ^ #(arcsInto N v)ᶜ) ^ 2 =
      vertexKernel N θ ρ v (arriving N inj top v) fun t => φ' (overwrite (arcsInto N v) top t) := by
  have hF := frontier_of_prod_ne_zero hN hinj hD hw
  have hg := hF.good_arriving hinj hvD hch
  have hsupp : ∀ b t : E → Finset (Finset X), allocationFactor N θ ρ (arriving N inj top v) v b ≠ 0 →
      ∏ f ∈ arcsInto N v, kingmanTransition (θ.length f) (b f) (t f) ≠ 0 →
        φ' (overwrite (arcsInto N v) top t) = c := by
    intro b t hb ht
    set bot' := overwrite (arcsInto N v) bot b with hbot'
    set top' := overwrite (arcsInto N v) top t with htop'
    have harr : arriving N inj top' v = arriving N inj top v := arriving_overwrite hvD hch top t
    have hw' : vertexWeight N θ ρ inj v bot' top' ≠ 0 := by
      unfold vertexWeight
      rw [harr, allocationFactor_congr (bot' := b) fun e he => overwrite_of_mem (mem_arcsInto.2 he) _ _]
      refine mul_ne_zero hb ?_
      have : ∏ e ∈ arcsInto N v, kingmanTransition (θ.length e) (bot' e) (top' e) =
          ∏ f ∈ arcsInto N v, kingmanTransition (θ.length f) (b f) (t f) :=
        prod_congr rfl fun e he => by rw [hbot', htop', overwrite_of_mem he, overwrite_of_mem he]
      rw [this]
      exact ht
    have hprod : ∏ u ∈ D, vertexWeight N θ ρ inj u bot' top' ≠ 0 := by
      rw [hbot', htop', prod_vertexWeight_overwrite_top hD hvD, prod_vertexWeight_overwrite_bot hvD]
      exact hw
    have hF' := frontier_of_prod_ne_zero hN hinj hD hprod
    have hg' := hF'.good_arriving hinj hvD hch
    obtain ⟨-, -, hmem⟩ := good_of_vertexWeight_ne_zero hg' hw'
    refine h bot' top' (fun f hf => overwrite_of_notMem (fun hfS => hf (mem_arcsInto.1 hfS)) _ _)
      (fun x => by rw [← harr]; exact hmem x) (fun C hC => ?_) (hF'.insert hN hinj hD hvD hch hw')
    exact exists_mem_top_of_vertexWeight_ne_zero hg' hw' (by rw [harr]; exact hC)
  refine le_antisymm (le_vertexKernel hN hθ hρ hv hg.1 fun b t hb ht => (hsupp b t hb ht).ge) ?_
  rw [← vertexKernel_const hN hθ.isNormalized hρ.1 hv hg.1 c]
  exact vertexKernel_mono hθ hρ v _ fun b t hb ht => (hsupp b t hb ht).le

omit [Fintype V] in
/-- **The kernel at a vertex with one parent arc, of inheritance one**, on a function of the forest at its top. -/
theorem vertexKernel_one_arc (hρ : 0 ≤ ρ) {v : V} {e : E} (he : N.graph.target e = v)
    (hall : ∀ f, N.graph.target f = v → f = e) (hγ : θ.inheritance e = 1) {F : Finset (Finset X)} (hF : F.Nonempty)
    (g : Finset (Finset X) → ℝ) :
    vertexKernel N θ ρ v F (fun t => g (t e)) =
      (∑ G, kingmanTransition (θ.length e) F G * g G) * ((Fintype.card (Finset (Finset X)) : ℝ) ^ #(arcsInto N v)ᶜ) ^ 2 := by
  rw [vertexKernel_eq_sum]
  obtain ⟨A, hA⟩ := hF
  obtain ⟨R, hR, -⟩ := exists_mem_roots_subset hA
  have hne : Nonempty {A // A ∈ roots F} := ⟨⟨R, hR⟩⟩
  set e' : {e // N.graph.target e = v} := ⟨e, he⟩ with he'
  have hsub : ∀ a' : {A // A ∈ roots F} → {e // N.graph.target e = v}, ∀ r, a' r = e' := fun a' r =>
    Subtype.ext (hall _ (a' r).property)
  rw [sum_eq_single (fun _ => e') (fun a' _ ha' => absurd (funext (hsub a')) ha')
    (fun h => absurd (mem_univ _) h)]
  rw [allocationWeight_const_eq_one hρ (γ := fun e : {e // N.graph.target e = v} => θ.inheritance e.val) hγ, one_mul]
  have hS : arcsInto N v = {e} := by
    ext f
    simp only [mem_arcsInto, mem_singleton]
    exact ⟨hall f, fun h => h ▸ he⟩
  have hb : assignedForest N F v (fun _ => e') e = F := assignedForest_of_forall he fun _ => rfl
  have h1 := sum_prod_mem ({e} : Finset E) (fun _ τ => kingmanTransition (θ.length e) F τ * g τ)
  simp only [prod_singleton] at h1
  rw [hS]
  simp only [prod_singleton, hb]
  rw [h1, sq]
  ring

omit [Fintype V] [Fintype E] in
/-- Two lineages `a`, `b` that haven't merged: a forest reached from `{{a}, {b}}` is itself, or has the cluster `{a, b}`. -/
theorem eq_or_eq_insert_of_kingman_ne_zero {a b : X} (hab : a ≠ b) {t : ℝ} {G : Finset (Finset X)}
    (hK : kingmanTransition t ({{a}, {b}} : Finset (Finset X)) G ≠ 0) :
    G = {{a}, {b}} ∨ G = insert {a, b} {{a}, {b}} := by
  obtain ⟨hgood, hsub, hlin⟩ := kingmanTransition_support_good isGoodForest_pair hK
  have hA : ∀ A ∈ G, A = {a} ∨ A = {b} ∨ A = {a, b} := by
    intro A hA
    have h1 : A ⊆ {a, b} := by
      intro x hx
      have : x ∈ lineages G := mem_lineages.2 ⟨A, hA, hx⟩
      rw [hlin] at this
      obtain ⟨B, hB, hxB⟩ := mem_lineages.1 this
      simp only [mem_insert, mem_singleton] at hB ⊢
      rcases hB with rfl | rfl
      · exact Or.inl (mem_singleton.1 hxB)
      · exact Or.inr (mem_singleton.1 hxB)
    obtain ⟨y, hy⟩ := hgood.1.1 A hA
    have hmemA : ∀ x ∈ A, x = a ∨ x = b := fun x hx => by simpa using h1 hx
    by_cases ha : a ∈ A
    · by_cases hb : b ∈ A
      · refine Or.inr (Or.inr (Subset.antisymm h1 ?_))
        intro x hx
        rcases mem_insert.1 hx with rfl | hx
        · exact ha
        · rw [mem_singleton.1 hx]
          exact hb
      · refine Or.inl (ext fun x => ?_)
        simp only [mem_singleton]
        constructor
        · intro hx
          rcases hmemA x hx with rfl | rfl
          · rfl
          · exact absurd hx hb
        · rintro rfl
          exact ha
    · refine Or.inr (Or.inl (ext fun x => ?_))
      simp only [mem_singleton]
      constructor
      · intro hx
        rcases hmemA x hx with rfl | rfl
        · exact absurd hx ha
        · rfl
      · rintro rfl
        rcases hmemA y hy with rfl | rfl
        · exact absurd hy ha
        · exact hy
  by_cases hmem : ({a, b} : Finset X) ∈ G
  · refine Or.inr (Subset.antisymm (fun A hAG => ?_) (insert_subset hmem hsub))
    simp only [mem_insert, mem_singleton]
    rcases hA A hAG with h | h | h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
    · exact Or.inl h
  · refine Or.inl (Subset.antisymm (fun A hAG => ?_) hsub)
    simp only [mem_insert, mem_singleton]
    rcases hA A hAG with h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · exact absurd (h ▸ hAG) hmem

/-- The chain on two lineages `a`, `b`: they merge with probability `1 - exp (-t)`. -/
theorem sum_kingman_pair {a b : X} (hab : a ≠ b) (t : ℝ) (g : Finset (Finset X) → ℝ) :
    ∑ G, kingmanTransition t ({{a}, {b}} : Finset (Finset X)) G * g G =
      Real.exp (-t) * g {{a}, {b}} + (1 - Real.exp (-t)) * g (insert {a, b} {{a}, {b}}) := by
  set F : Finset (Finset X) := {{a}, {b}} with hF
  have hgood : IsGoodForest F := isGoodForest_pair
  have hne : insert {a, b} F ≠ F := by
    intro h
    have : ({a, b} : Finset X) ∈ F := h ▸ mem_insert_self _ _
    exact pair_notMem_pair' hab this
  have hself : kingmanTransition t F F = Real.exp (-t) := by
    rw [kingmanTransition_apply_self hgood.1, roots_pair hab, card_pair (by simpa using hab)]
    simp
  have hsum := kingmanTransition_sum hgood.1 t
  have hsupp : ∀ G ∈ univ, G ≠ F → G ≠ insert {a, b} F → kingmanTransition t F G = 0 := fun G _ h1 h2 => by
    by_contra hK
    rcases eq_or_eq_insert_of_kingman_ne_zero hab hK with h | h
    · exact h1 h
    · exact h2 h
  rw [sum_eq_add F (insert {a, b} F) hne.symm (fun G hG h => by rw [hsupp G hG h.1 h.2, zero_mul])
    (fun h => absurd (mem_univ _) h) (fun h => absurd (mem_univ _) h)]
  rw [sum_eq_add F (insert {a, b} F) hne.symm (fun G hG h => hsupp G hG h.1 h.2)
    (fun h => absurd (mem_univ _) h) (fun h => absurd (mem_univ _) h)] at hsum
  have hK2 : kingmanTransition t F (insert {a, b} F) = 1 - Real.exp (-t) := by linarith
  rw [hself, hK2]

omit [Fintype V] in
/-- The term of an assignment in the kernel, on a function constant on its support. -/
theorem sum_prod_kingman_mul_of_support {F : Finset (Finset X)} (hF : IsForest F) {v : V}
    (a' : {A // A ∈ roots F} → {e // N.graph.target e = v}) {ψ : (E → Finset (Finset X)) → ℝ} {c : ℝ}
    (h : ∀ t : E → Finset (Finset X),
      ∏ f ∈ arcsInto N v, kingmanTransition (θ.length f) (assignedForest N F v a' f) (t f) ≠ 0 → ψ t = c) :
    ∑ t : E → Finset (Finset X),
        (∏ f ∈ arcsInto N v, kingmanTransition (θ.length f) (assignedForest N F v a' f) (t f)) * ψ t =
      c * (Fintype.card (Finset (Finset X)) : ℝ) ^ #(arcsInto N v)ᶜ := by
  rw [← sum_prod_kingman_assigned (θ := θ) hF a', mul_sum]
  refine sum_congr rfl fun t _ => ?_
  by_cases ht : ∏ f ∈ arcsInto N v, kingmanTransition (θ.length f) (assignedForest N F v a' f) (t f) = 0
  · simp [ht]
  · rw [h t ht, mul_comm]

omit [Fintype V] in
/-- **Two arcs into `v`**, of inheritance `1/2`, at correlation `0`, exactly: the lineages `a`, `b` take different arcs with probability `1/4` each way; and one arc `eᵢ`, along which they stay apart with probability
`exp (-(length of eᵢ))`, with probability `1/4` each. The values are those of the test function on the forests that can arise. -/
theorem kernel_two_arcs_eq {v : V} {e₁ e₂ : E} (hne : e₁ ≠ e₂) (h₁ : N.graph.target e₁ = v)
    (h₂ : N.graph.target e₂ = v) (hall : ∀ e, N.graph.target e = v → e = e₁ ∨ e = e₂) (hγ₁ : θ.inheritance e₁ = 1 / 2)
    (hγ₂ : θ.inheritance e₂ = 1 / 2) {a b : X} (hab : a ≠ b) {ψ : (E → Finset (Finset X)) → ℝ} {d₁ d₂ u₁ u₂ w₁ w₂ : ℝ}
    (hd₁ : ∀ t : E → Finset (Finset X), t e₁ = {{a}} → t e₂ = {{b}} → ψ t = d₁)
    (hd₂ : ∀ t : E → Finset (Finset X), t e₁ = {{b}} → t e₂ = {{a}} → ψ t = d₂)
    (hu₁ : ∀ t : E → Finset (Finset X), t e₁ = {{a}, {b}} → t e₂ = ∅ → ψ t = u₁)
    (hw₁ : ∀ t : E → Finset (Finset X), t e₁ = insert {a, b} {{a}, {b}} → t e₂ = ∅ → ψ t = w₁)
    (hu₂ : ∀ t : E → Finset (Finset X), t e₂ = {{a}, {b}} → t e₁ = ∅ → ψ t = u₂)
    (hw₂ : ∀ t : E → Finset (Finset X), t e₂ = insert {a, b} {{a}, {b}} → t e₁ = ∅ → ψ t = w₂) :
    vertexKernel N θ 0 v {{a}, {b}} ψ =
      (1 / 4 * (d₁ + d₂) + 1 / 4 * (Real.exp (-θ.length e₁) * u₁ + (1 - Real.exp (-θ.length e₁)) * w₁) +
        1 / 4 * (Real.exp (-θ.length e₂) * u₂ + (1 - Real.exp (-θ.length e₂)) * w₂)) *
        ((Fintype.card (Finset (Finset X)) : ℝ) ^ #(arcsInto N v)ᶜ) ^ 2 := by
  rw [vertexKernel_eq_sum]
  set F : Finset (Finset X) := {{a}, {b}} with hFdef
  have hg : IsGoodForest F := isGoodForest_pair
  have hroots : roots F = F := roots_pair hab
  have hcard : #F = 2 := card_pair (by simpa using hab)
  have hself : ∀ (e : E), kingmanTransition (θ.length e) F F = Real.exp (-θ.length e) := fun e => by
    rw [kingmanTransition_apply_self hg.1, hroots, hcard]
    simp
  let ra : {A // A ∈ roots F} := ⟨{a}, by rw [hroots, hFdef]; simp⟩
  let rb : {A // A ∈ roots F} := ⟨{b}, by rw [hroots, hFdef]; simp⟩
  have hrne : ra ≠ rb := fun h => hab (singleton_injective (congrArg Subtype.val h))
  have hR : ∀ r : {A // A ∈ roots F}, r = ra ∨ r = rb := fun r => by
    have h : (r : Finset X) ∈ ({{a}, {b}} : Finset (Finset X)) := roots_subset F r.property
    rw [mem_insert, mem_singleton] at h
    rcases h with h | h
    · exact Or.inl (Subtype.ext h)
    · exact Or.inr (Subtype.ext h)
  let p₁ : {e // N.graph.target e = v} := ⟨e₁, h₁⟩
  let p₂ : {e // N.graph.target e = v} := ⟨e₂, h₂⟩
  have hpne : p₁ ≠ p₂ := fun h => hne (congrArg Subtype.val h)
  have hP : ∀ p : {e // N.graph.target e = v}, p = p₁ ∨ p = p₂ := fun p => by
    rcases hall _ p.property with h | h
    · exact Or.inl (Subtype.ext h)
    · exact Or.inr (Subtype.ext h)
  have hγ : ∀ p : {e // N.graph.target e = v}, θ.inheritance p.val = 1 / 2 := fun p => by
    rcases hall _ p.property with h | h
    · rw [h, hγ₁]
    · rw [h, hγ₂]
  have huniv : (univ : Finset {A // A ∈ roots F}) = {ra, rb} := by
    ext r
    simp only [mem_univ, mem_insert, mem_singleton, true_iff]
    exact hR r
  have hW : ∀ a' : {A // A ∈ roots F} → {e // N.graph.target e = v},
      allocationWeight 0 (fun e : {e // N.graph.target e = v} => θ.inheritance e.val) a' = 1 / 4 := fun a' => by
    rw [allocationWeight_rho_zero, huniv, prod_pair hrne, hγ, hγ]
    norm_num
  simp only [hW]
  set C : ℝ := (Fintype.card (Finset (Finset X)) : ℝ) ^ #(arcsInto N v)ᶜ with hC
  let asg : {e // N.graph.target e = v} → {e // N.graph.target e = v} → {A // A ∈ roots F} → {e // N.graph.target e = v} :=
    fun x y r => if r = ra then x else y
  have hasga : ∀ x y, asg x y ra = x := fun x y => by simp [asg]
  have hasgb : ∀ x y, asg x y rb = y := fun x y => by simp [asg, hrne.symm]
  have hne1 : ∀ {x y x' y'}, x ≠ x' → asg x y ≠ asg x' y' := fun h heq => h (by
    have := congrFun heq ra
    rwa [hasga, hasga] at this)
  have hne2 : ∀ {x y x' y'}, y ≠ y' → asg x y ≠ asg x' y' := fun h heq => h (by
    have := congrFun heq rb
    rwa [hasgb, hasgb] at this)
  have hasg : ∀ a' : {A // A ∈ roots F} → {e // N.graph.target e = v}, a' = asg (a' ra) (a' rb) := fun a' => by
    funext r
    rcases hR r with rfl | rfl
    · rw [hasga]
    · rw [hasgb]
  have hunivA : (univ : Finset ({A // A ∈ roots F} → {e // N.graph.target e = v})) =
      {asg p₁ p₂, asg p₂ p₁, asg p₁ p₁, asg p₂ p₂} := by
    ext a'
    simp only [mem_univ, mem_insert, mem_singleton, true_iff]
    rw [hasg a']
    rcases hP (a' ra) with h | h <;> rcases hP (a' rb) with h' | h' <;> rw [h, h'] <;> simp
  rw [hunivA, sum_insert (by simp [hne1 hpne, hne2 hpne.symm]), sum_insert (by simp [hne1 hpne.symm, hne2 hpne]),
    sum_pair (hne1 hpne)]
  -- the assignments that split the two lineages
  have hleft : ∀ x y : {e // N.graph.target e = v}, x ≠ y → assignedForest N F v (asg x y) x.val = {{a}} := by
    intro x y hxy
    simp only [assignedForest, x.property, ↓reduceDIte]
    have hfil : (univ.filter fun r => asg x y r = x) = {ra} := by
      ext r
      simp only [mem_filter, mem_univ, true_and, mem_singleton]
      constructor
      · intro hr
        rcases hR r with rfl | rfl
        · rfl
        · rw [hasgb] at hr
          exact absurd hr.symm hxy
      · rintro rfl
        exact hasga x y
    rw [hfil]
    ext A
    simp only [mem_forestBelow, image_singleton, mem_singleton, exists_eq_left, hFdef, mem_insert, ra]
    constructor
    · rintro ⟨rfl | rfl, h⟩
      · rfl
      · exact absurd (singleton_subset_singleton.1 h) hab.symm
    · rintro rfl
      exact ⟨Or.inl rfl, Subset.refl _⟩
  have hright : ∀ x y : {e // N.graph.target e = v}, x ≠ y → assignedForest N F v (asg x y) y.val = {{b}} := by
    intro x y hxy
    simp only [assignedForest, y.property, ↓reduceDIte]
    have hfil : (univ.filter fun r => asg x y r = y) = {rb} := by
      ext r
      simp only [mem_filter, mem_univ, true_and, mem_singleton]
      constructor
      · intro hr
        rcases hR r with rfl | rfl
        · rw [hasga] at hr
          exact absurd hr hxy
        · rfl
      · rintro rfl
        exact hasgb x y
    rw [hfil]
    ext A
    simp only [mem_forestBelow, image_singleton, mem_singleton, exists_eq_left, hFdef, mem_insert, rb]
    constructor
    · rintro ⟨rfl | rfl, h⟩
      · exact absurd (singleton_subset_singleton.1 h) hab
      · rfl
    · rintro rfl
      exact ⟨Or.inr rfl, Subset.refl _⟩
  have hsingle : ∀ {x : X} {t : ℝ} {G : Finset (Finset X)}, kingmanTransition t ({{x}} : Finset (Finset X)) G ≠ 0 → G = {{x}} := by
    intro x t G hK
    have hf : IsForest ({{x}} : Finset (Finset X)) := by
      refine ⟨fun A hA => ?_, fun A hA B hB => ?_⟩
      · rw [mem_singleton.1 hA]
        exact singleton_nonempty x
      · rw [mem_singleton.1 hA, mem_singleton.1 hB]
        exact Or.inl (Subset.refl _)
    have hr : #(roots ({{x}} : Finset (Finset X))) ≤ 1 :=
      (card_le_card (roots_subset _)).trans (by simp)
    rw [kingmanTransition_of_card_roots_le_one hf hr] at hK
    by_contra hne
    exact hK (ite_eq_right hne)
  have hsplit : ∀ x y : {e // N.graph.target e = v}, x ≠ y → ∀ t : E → Finset (Finset X),
      ∏ f ∈ arcsInto N v, kingmanTransition (θ.length f) (assignedForest N F v (asg x y) f) (t f) ≠ 0 →
        t x.val = {{a}} ∧ t y.val = {{b}} := by
    intro x y hxy t ht
    have h1 := prod_ne_zero_iff.1 ht x.val (mem_arcsInto.2 x.property)
    have h2 := prod_ne_zero_iff.1 ht y.val (mem_arcsInto.2 y.property)
    rw [hleft x y hxy] at h1
    rw [hright x y hxy] at h2
    exact ⟨hsingle h1, hsingle h2⟩
  have hT₁ := sum_prod_kingman_mul_of_support (θ := θ) (ψ := ψ) (c := d₁) hg.1 (asg p₁ p₂) fun t ht => by
    obtain ⟨h1, h2⟩ := hsplit p₁ p₂ hpne t ht
    exact hd₁ t h1 h2
  have hT₂ := sum_prod_kingman_mul_of_support (θ := θ) (ψ := ψ) (c := d₂) hg.1 (asg p₂ p₁) fun t ht => by
    obtain ⟨h1, h2⟩ := hsplit p₂ p₁ hpne.symm t ht
    exact hd₂ t h2 h1
  -- the assignments that keep them together
  have hsame : ∀ {e e' : E} (he : N.graph.target e = v) (he' : N.graph.target e' = v), e ≠ e' → ∀ {u w : ℝ},
      (∀ t : E → Finset (Finset X), t e = F → t e' = ∅ → ψ t = u) →
      (∀ t : E → Finset (Finset X), t e = insert {a, b} F → t e' = ∅ → ψ t = w) →
      ∑ t : E → Finset (Finset X),
          (∏ f ∈ arcsInto N v, kingmanTransition (θ.length f) (assignedForest N F v (asg ⟨e, he⟩ ⟨e, he⟩) f) (t f)) * ψ t =
        (Real.exp (-θ.length e) * u + (1 - Real.exp (-θ.length e)) * w) * C := by
    intro e e' he he' hee' u w hu hw
    have hforall : ∀ r, asg ⟨e, he⟩ ⟨e, he⟩ r = ⟨e, he⟩ := fun r => by simp [asg]
    have hbe : assignedForest N F v (asg ⟨e, he⟩ ⟨e, he⟩) e = F := assignedForest_of_forall he hforall
    have hbe' : assignedForest N F v (asg ⟨e, he⟩ ⟨e, he⟩) e' = ∅ := by
      simp only [assignedForest, he', ↓reduceDIte]
      have hfil : (univ.filter fun r => asg ⟨e, he⟩ ⟨e, he⟩ r = ⟨e', he'⟩) = ∅ :=
        filter_false_of_mem fun r _ h => hee' (congrArg Subtype.val ((hforall r).symm.trans h))
      rw [hfil, image_empty]
      ext A
      simp [mem_forestBelow]
    have hpt : ∀ t : E → Finset (Finset X),
        (∏ f ∈ arcsInto N v, kingmanTransition (θ.length f) (assignedForest N F v (asg ⟨e, he⟩ ⟨e, he⟩) f) (t f)) * ψ t =
          (∏ f ∈ arcsInto N v, kingmanTransition (θ.length f) (assignedForest N F v (asg ⟨e, he⟩ ⟨e, he⟩) f) (t f)) *
              (u - w) * (if t e = F then 1 else 0) +
            (∏ f ∈ arcsInto N v, kingmanTransition (θ.length f) (assignedForest N F v (asg ⟨e, he⟩ ⟨e, he⟩) f) (t f)) * w := by
      intro t
      by_cases ht : ∏ f ∈ arcsInto N v, kingmanTransition (θ.length f) (assignedForest N F v (asg ⟨e, he⟩ ⟨e, he⟩) f) (t f) = 0
      · simp [ht]
      · have h1 := prod_ne_zero_iff.1 ht e (mem_arcsInto.2 he)
        have h2 := prod_ne_zero_iff.1 ht e' (mem_arcsInto.2 he')
        rw [hbe] at h1
        rw [hbe'] at h2
        have ht' : t e' = ∅ := eq_empty_of_kingmanTransition_empty_ne_zero h2
        rcases eq_or_eq_insert_of_kingman_ne_zero hab h1 with h3 | h3
        · rw [hu t h3 ht', ite_eq_left h3]
          ring
        · have hne' : t e ≠ F := fun h4 => by
            have : ({a, b} : Finset X) ∈ t e := h3 ▸ mem_insert_self _ _
            rw [h4] at this
            exact pair_notMem_pair' hab this
          rw [hw t h3 ht', ite_eq_right hne']
          ring
    simp only [hpt]
    rw [sum_add_distrib, ← sum_mul, sum_prod_kingman_assigned hg.1]
    have h3 := sum_prod_kingman_mul_ite (θ := θ) he (b := assignedForest N F v (asg ⟨e, he⟩ ⟨e, he⟩))
      (fun f _ => isForest_assignedForest hg.1 v _ f) F
    rw [hbe, hself] at h3
    have h4 : ∑ t : E → Finset (Finset X),
        (∏ f ∈ arcsInto N v, kingmanTransition (θ.length f) (assignedForest N F v (asg ⟨e, he⟩ ⟨e, he⟩) f) (t f)) *
          (u - w) * (if t e = F then 1 else 0) =
        (u - w) * (Real.exp (-θ.length e) * C) := by
      rw [← h3, mul_sum]
      refine sum_congr rfl fun t _ => ?_
      ring
    rw [h4]
    ring
  have hT₃ := hsame h₁ h₂ hne hu₁ hw₁
  have hT₄ := hsame h₂ h₁ hne.symm hu₂ hw₂
  change _ + (_ + (1 / 4 * ((∑ t, (∏ f ∈ arcsInto N v, kingmanTransition (θ.length f) (assignedForest N F v (asg ⟨e₁, h₁⟩ ⟨e₁, h₁⟩) f) (t f)) * ψ t) * C) +
    1 / 4 * ((∑ t, (∏ f ∈ arcsInto N v, kingmanTransition (θ.length f) (assignedForest N F v (asg ⟨e₂, h₂⟩ ⟨e₂, h₂⟩) f) (t f)) * ψ t) * C))) = _
  rw [hT₁, hT₂, hT₃, hT₄]
  ring

/-! ### At the root -/

/-- The probability that a forest arriving at the root gives a gene tree with a cherry of `r`. -/
def absVal (r : QuartetTree X) (F : Finset (Finset X)) : ℝ :=
  ∑ H, if ∃ B ∈ r.val, B ∈ H then kingmanAbsorption F H else 0

variable (N θ ρ) in
/-- The mean of a function of the forests of all arcs. -/
def fullMass (inj : V → Finset (Finset X)) (φ : (E → Finset (Finset X)) → ℝ) : ℝ :=
  ∑ bot : E → Finset (Finset X), ∑ top : E → Finset (Finset X), injWeight N θ ρ inj bot top * φ top

omit [Fintype X] in
theorem absVal_nonneg [Fintype X] (r : QuartetTree X) {F : Finset (Finset X)} (hF : IsForest F) : 0 ≤ absVal r F :=
  sum_nonneg fun H _ => by
    split_ifs
    · exact kingmanAbsorption_nonneg hF H
    · exact le_rfl

omit [Fintype X] in
theorem absVal_le_one [Fintype X] (r : QuartetTree X) {F : Finset (Finset X)} (hF : IsForest F) : absVal r F ≤ 1 := by
  rw [← kingmanAbsorption_sum hF]
  refine sum_le_sum fun H _ => ?_
  split_ifs
  · exact le_rfl
  · exact kingmanAbsorption_nonneg hF H

/-- After all vertices below the root, the mean is against the weights of the histories. -/
theorem stageMass_top (hN : N.IsPhylogenetic) (inj : V → Finset (Finset X)) (φ : (E → Finset (Finset X)) → ℝ) :
    stageMass N θ ρ inj (univ.erase N.root) φ =
      ((Fintype.card (Finset (Finset X)) : ℝ) ^ Fintype.card E) ^ 2 * fullMass N θ ρ inj φ := by
  have hall : (univ.filter fun f => N.graph.target f ∈ univ.erase N.root) = univ :=
    filter_true_of_mem fun f _ => mem_erase.2 ⟨target_ne_root hN f, mem_univ _⟩
  unfold stageMass
  rw [hall, card_univ]
  rfl

/-- The mass of a quartet tree is the mean of `absVal` of the forest at the root. -/
theorem cherryMass_eq_fullMass (inj : V → Finset (Finset X)) (r : QuartetTree X) :
    cherryMass N θ ρ inj r = fullMass N θ ρ inj fun top => absVal r (arriving N inj top N.root) := by
  unfold cherryMass injDist fullMass absVal
  have hH : ∀ H : Finset (Finset X), (if ∃ B ∈ r.val, B ∈ H then
        ∑ bot : E → Finset (Finset X), ∑ top : E → Finset (Finset X),
          injWeight N θ ρ inj bot top * kingmanAbsorption (arriving N inj top N.root) H else 0) =
      ∑ bot : E → Finset (Finset X), ∑ top : E → Finset (Finset X),
        injWeight N θ ρ inj bot top *
          if ∃ B ∈ r.val, B ∈ H then kingmanAbsorption (arriving N inj top N.root) H else 0 := by
    intro H
    split_ifs <;> simp
  simp only [hH]
  rw [sum_comm]
  refine sum_congr rfl fun bot _ => ?_
  rw [sum_comm]
  refine sum_congr rfl fun top _ => ?_
  rw [mul_sum]

/-- The mean is additive. -/
theorem fullMass_add (inj : V → Finset (Finset X)) (φ φ' : (E → Finset (Finset X)) → ℝ) :
    fullMass N θ ρ inj (fun t => φ t + φ' t) = fullMass N θ ρ inj φ + fullMass N θ ρ inj φ' := by
  unfold fullMass
  simp only [mul_add, sum_add_distrib]

/-- The mean of a finite sum. -/
theorem fullMass_sum {ι : Type*} (inj : V → Finset (Finset X)) (s : Finset ι) (φ : ι → (E → Finset (Finset X)) → ℝ) :
    fullMass N θ ρ inj (fun t => ∑ i ∈ s, φ i t) = ∑ i ∈ s, fullMass N θ ρ inj (φ i) := by
  unfold fullMass
  simp only [mul_sum]
  exact (sum_congr rfl fun bot _ => sum_comm).trans sum_comm

/-- Two functions that agree on the histories of nonzero weight have the same mean. -/
theorem fullMass_congr {inj : V → Finset (Finset X)} {φ φ' : (E → Finset (Finset X)) → ℝ}
    (h : ∀ bot top : E → Finset (Finset X), injWeight N θ ρ inj bot top ≠ 0 → φ top = φ' top) :
    fullMass N θ ρ inj φ = fullMass N θ ρ inj φ' := by
  unfold fullMass
  refine sum_congr rfl fun bot _ => sum_congr rfl fun top _ => ?_
  by_cases hw : injWeight N θ ρ inj bot top = 0
  · simp [hw]
  · rw [h bot top hw]

/-- The mean is monotone. -/
theorem fullMass_mono (hθ : N.IsWeakMetric θ) (hρ : 0 ≤ ρ ∧ ρ ≤ 1) {inj : V → Finset (Finset X)} {φ φ' : (E → Finset (Finset X)) → ℝ}
    (h : ∀ bot top : E → Finset (Finset X), injWeight N θ ρ inj bot top ≠ 0 → φ top ≤ φ' top) :
    fullMass N θ ρ inj φ ≤ fullMass N θ ρ inj φ' := by
  unfold fullMass
  refine sum_le_sum fun bot _ => sum_le_sum fun top _ => ?_
  by_cases hw : injWeight N θ ρ inj bot top = 0
  · simp [hw]
  · exact mul_le_mul_of_nonneg_left (h bot top hw) (injWeight_nonneg_weak hθ hρ inj bot top)

/-- The mean of one is one. -/
theorem fullMass_one (hN : N.IsPhylogenetic) (hθ : N.IsNormalized θ) (hρ : 0 ≤ ρ) {inj : V → Finset (Finset X)} (hinj : ValidInj inj) :
    fullMass N θ ρ inj (fun _ => 1) = 1 := by
  unfold fullMass
  simp only [mul_one]
  exact sum_sum_injWeight_weak hN hθ hρ hinj

/-! ### Automorphisms of a network -/

section Automorphism

variable {fV : V ≃ V} {fE : E ≃ E} {π : Equiv.Perm X}

omit [Fintype V] [Fintype X] in
/-- The forest arriving at a vertex, under an automorphism of the network that permutes the lineages. -/
theorem arriving_automorphism {inj : V → Finset (Finset X)} (hs : ∀ e, N.graph.source (fE e) = fV (N.graph.source e))
    (hinj : ∀ v, inj (fV v) = relabelFamily π (inj v)) (top : E → Finset (Finset X)) (v : V) :
    arriving N inj (fun e => relabelFamily π (top (fE.symm e))) (fV v) = relabelFamily π (arriving N inj top v) := by
  unfold arriving
  rw [relabelFamily_union, relabelFamily_biUnion, hinj]
  congr 1
  ext A
  simp only [mem_biUnion, mem_filter, mem_univ, true_and]
  constructor
  · rintro ⟨e, he, hA⟩
    obtain ⟨e, rfl⟩ := fE.surjective e
    rw [hs] at he
    rw [fE.symm_apply_apply] at hA
    exact ⟨e, fV.injective he, hA⟩
  · rintro ⟨e, he, hA⟩
    exact ⟨fE e, by rw [hs, he], by rwa [fE.symm_apply_apply]⟩

/-- **The weight of a history under an automorphism of the network** that permutes the lineages. -/
theorem injWeight_automorphism {inj : V → Finset (Finset X)} (hs : ∀ e, N.graph.source (fE e) = fV (N.graph.source e))
    (ht : ∀ e, N.graph.target (fE e) = fV (N.graph.target e)) (hroot : fV N.root = N.root)
    (hlen : ∀ e, θ.length (fE e) = θ.length e) (hinh : ∀ e, θ.inheritance (fE e) = θ.inheritance e)
    (hinj : ∀ v, inj (fV v) = relabelFamily π (inj v)) (bot top : E → Finset (Finset X)) :
    injWeight N θ ρ inj (fun e => relabelFamily π (bot (fE.symm e))) (fun e => relabelFamily π (top (fE.symm e))) =
      injWeight N θ ρ inj bot top := by
  unfold injWeight
  have hfin : univ.erase N.root = (univ.erase N.root).map fV.toEmbedding := by
    ext v
    obtain ⟨v, rfl⟩ := fV.surjective v
    simp only [mem_erase, mem_univ, and_true, mem_map, Equiv.coe_toEmbedding]
    constructor
    · intro h
      exact ⟨v, fun h' => h (by rw [h', hroot]), rfl⟩
    · rintro ⟨w, hw, hwv⟩
      rw [← hwv]
      exact fun h => hw (fV.injective (h.trans hroot.symm))
  conv_lhs => rw [hfin, prod_map]
  refine prod_congr rfl fun v _ => ?_
  change vertexWeight N θ ρ inj (fV v) _ _ = _
  rw [← vertexWeight_relabel π inj v bot top]
  unfold vertexWeight
  have hinto : arcsInto N (fV v) = (arcsInto N v).map fE.toEmbedding := by
    ext e
    obtain ⟨e, rfl⟩ := fE.surjective e
    simp [ht]
  rw [arriving_automorphism hs hinj, hinto, prod_map, arriving_relabel]
  congr 1
  · refine allocationFactor_eq_of_equiv (fE.subtypeEquiv (fun e => by rw [ht, fV.injective.eq_iff])) (Equiv.refl _)
      (fun e => (hinh e.1).symm) fun a e => ?_
    change _ ↔ relabelFamily π (bot (fE.symm (fE e.1))) = _
    rw [fE.symm_apply_apply]
    exact Iff.rfl
  · refine prod_congr rfl fun e _ => ?_
    change kingmanTransition (θ.length (fE e)) (relabelFamily π (bot (fE.symm (fE e)))) (relabelFamily π (top (fE.symm (fE e)))) = _
    rw [fE.symm_apply_apply, hlen]

/-- **The mean under an automorphism of the network.** -/
theorem fullMass_automorphism {inj : V → Finset (Finset X)} (hs : ∀ e, N.graph.source (fE e) = fV (N.graph.source e))
    (ht : ∀ e, N.graph.target (fE e) = fV (N.graph.target e)) (hroot : fV N.root = N.root)
    (hlen : ∀ e, θ.length (fE e) = θ.length e) (hinh : ∀ e, θ.inheritance (fE e) = θ.inheritance e)
    (hinj : ∀ v, inj (fV v) = relabelFamily π (inj v)) (φ : (E → Finset (Finset X)) → ℝ) :
    fullMass N θ ρ inj (fun t => φ fun e => relabelFamily π (t (fE.symm e))) = fullMass N θ ρ inj φ := by
  unfold fullMass
  symm
  calc ∑ bot : E → Finset (Finset X), ∑ top : E → Finset (Finset X), injWeight N θ ρ inj bot top * φ top
      = ∑ bot : E → Finset (Finset X), ∑ top : E → Finset (Finset X),
          injWeight N θ ρ inj (fun e => relabelFamily π (bot (fE.symm e))) (fun e => relabelFamily π (top (fE.symm e))) *
            φ fun e => relabelFamily π (top (fE.symm e)) := by
        rw [← (Equiv.arrowCongr fE (relabelFamilyEquiv π)).sum_comp]
        refine sum_congr rfl fun bot _ => ?_
        rw [← (Equiv.arrowCongr fE (relabelFamilyEquiv π)).sum_comp]
        rfl
    _ = _ := by
        refine sum_congr rfl fun bot _ => sum_congr rfl fun top _ => ?_
        rw [injWeight_automorphism hs ht hroot hlen hinh hinj]

omit [Fintype V] [Fintype E] in
/-- `absVal` under a permutation of the lineages. -/
theorem absVal_relabel (π : Equiv.Perm X) (r : QuartetTree X) (F : Finset (Finset X)) :
    absVal (relabelQuartet π r) (relabelFamily π F) = absVal r F := by
  unfold absVal
  rw [← (relabelFamilyEquiv π).sum_comp]
  refine sum_congr rfl fun H _ => ?_
  have hc : (∃ B ∈ (relabelQuartet π r).val, B ∈ relabelFamily π H) ↔ ∃ B ∈ r.val, B ∈ H := by
    constructor
    · rintro ⟨B, hB, hBH⟩
      obtain ⟨A, hA, rfl⟩ := mem_image.1 hB
      exact ⟨A, hA, map_mem_relabelFamily.1 hBH⟩
    · rintro ⟨A, hA, hAH⟩
      exact ⟨A.map π.toEmbedding, mem_image_of_mem _ hA, map_mem_relabelFamily.2 hAH⟩
  simp only [relabelFamilyEquiv_apply, hc, kingmanAbsorption_relabelFamily]

end Automorphism

end AllmanEtAl2023.KernelBounds
