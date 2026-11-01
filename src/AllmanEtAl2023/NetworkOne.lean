module

public import AllmanEtAl2023.TreeBlobs
public import AllmanEtAl2023.NetworkNkExact

/-!
# Allman, Baños, Mitchell, Rhodes 2023: the range `(1/6, 1)` on a level-1 network, cited from Baños (2019)

"If `𝒩⁺` is level-1, then Baños (2019) showed `CF_{ab|cd}` may take on any value in `(1/6, 1)`" (before Proposition 1), of the first entry of `CF_abcd` on a 4-taxon network whose reduced unrooted tree of blobs is `ab|cd`, for all numerical parameters. Baños's Proposition 7, read in PMC6344282, is: on a metric unrooted level-1 quartet network with a `3₂`-cycle, a cycle of three edges with the two taxa `a`, `b` below its hybrid node, `CF` lies in the set `x > 1/6, y = z` or its permutations, and every point of that set arises. His proof computes the `CF` on a network with only that cycle, and reduces the other networks to convex sums of these.

Here the computation is on that network, `𝒩(1)⁺`, by the chain of `NetworkNkExact` with all parameters free: the arcs `arcL`, `arcR` from the path to the hybrid node have free lengths and inheritance `γ`, `1 - γ`.

* `kernel_two_arcs_gamma`: the kernel at a hybrid node on two lineages, for any `γ`. `KernelBounds.kernel_two_arcs_eq` is `γ = 1/2`.
* `nmscCF_one`: **the first entry on `𝒩(1)⁺`, for all parameters**: `1 - p + p (γ² (1 - (2/3) x) + (1 - γ)² (1 - (2/3) x') + (2/3) γ (1 - γ) y)`, with `p`, `x`, `x'`, `y` the `exp (-length)` of the stem, of the two hybrid arcs, and of the arc of the path.
* `isLevelOne_one`: `𝒩(1)⁺` is level-1, in the library's sense.
* `banos_range`: **the range is exactly `(1/6, 1)`** over all parameters on `𝒩(1)⁺`.

The bound `x > 1/6` on every level-1 network is Baños's further claim, by his reduction, and isn't proved here: Allman et al. cite the values, which this module gives.
-/

@[expose] public noncomputable section

open Phylogenetics Phylogenetics.RootedNetwork Phylogenetics.NMSC Finset AllmanEtAl2023.KernelBounds
open scoped Classical

namespace AllmanEtAl2023.KernelBounds

section TwoArcs

variable {V E X : Type*} [Fintype V] [Fintype E] [Fintype X] [DecidableEq X] {N : RootedNetwork V E X} {θ : MetricData E}

omit [Fintype V] in
/-- **The kernel at a hybrid node on two lineages, for any inheritance**: the lineages `a`, `b` take different arcs with probability `γ γ'` each way, and one arc `eᵢ`, along which they stay apart with probability `exp (-(length of eᵢ))`, with probability `γ²` or `γ'²`. -/
theorem kernel_two_arcs_gamma {v : V} {e₁ e₂ : E} (hne : e₁ ≠ e₂) (h₁ : N.graph.target e₁ = v)
    (h₂ : N.graph.target e₂ = v) (hall : ∀ e, N.graph.target e = v → e = e₁ ∨ e = e₂) {γ γ' : ℝ} (hγ₁ : θ.inheritance e₁ = γ)
    (hγ₂ : θ.inheritance e₂ = γ') {a b : X} (hab : a ≠ b) {ψ : (E → Finset (Finset X)) → ℝ} {d₁ d₂ u₁ u₂ w₁ w₂ : ℝ}
    (hd₁ : ∀ t : E → Finset (Finset X), t e₁ = {{a}} → t e₂ = {{b}} → ψ t = d₁)
    (hd₂ : ∀ t : E → Finset (Finset X), t e₁ = {{b}} → t e₂ = {{a}} → ψ t = d₂)
    (hu₁ : ∀ t : E → Finset (Finset X), t e₁ = {{a}, {b}} → t e₂ = ∅ → ψ t = u₁)
    (hw₁ : ∀ t : E → Finset (Finset X), t e₁ = insert {a, b} {{a}, {b}} → t e₂ = ∅ → ψ t = w₁)
    (hu₂ : ∀ t : E → Finset (Finset X), t e₂ = {{a}, {b}} → t e₁ = ∅ → ψ t = u₂)
    (hw₂ : ∀ t : E → Finset (Finset X), t e₂ = insert {a, b} {{a}, {b}} → t e₁ = ∅ → ψ t = w₂) :
    vertexKernel N θ 0 v {{a}, {b}} ψ =
      (γ * γ' * d₁ + γ' * γ * d₂ + γ * γ * (Real.exp (-θ.length e₁) * u₁ + (1 - Real.exp (-θ.length e₁)) * w₁) +
        γ' * γ' * (Real.exp (-θ.length e₂) * u₂ + (1 - Real.exp (-θ.length e₂)) * w₂)) *
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
  have huniv : (univ : Finset {A // A ∈ roots F}) = {ra, rb} := by
    ext r
    simp only [mem_univ, mem_insert, mem_singleton, true_iff]
    exact hR r
  set C : ℝ := (Fintype.card (Finset (Finset X)) : ℝ) ^ #(arcsInto N v)ᶜ with hC
  let asg : {e // N.graph.target e = v} → {e // N.graph.target e = v} → {A // A ∈ roots F} → {e // N.graph.target e = v} :=
    fun x y r => if r = ra then x else y
  have hasga : ∀ x y, asg x y ra = x := fun x y => by simp [asg]
  have hasgb : ∀ x y, asg x y rb = y := fun x y => by simp [asg, hrne.symm]
  have hW : ∀ x y : {e // N.graph.target e = v}, allocationWeight 0 (fun e : {e // N.graph.target e = v} => θ.inheritance e.val) (asg x y) = θ.inheritance x.val * θ.inheritance y.val := fun x y => by
    rw [allocationWeight_rho_zero, huniv, prod_pair hrne, hasga, hasgb]
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
    sum_pair (hne1 hpne), hW, hW, hW, hW]
  have hi₁ : θ.inheritance p₁.val = γ := hγ₁
  have hi₂ : θ.inheritance p₂.val = γ' := hγ₂
  rw [hi₁, hi₂]
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
  change _ + (_ + (γ * γ * ((∑ t, (∏ f ∈ arcsInto N v, kingmanTransition (θ.length f) (assignedForest N F v (asg ⟨e₁, h₁⟩ ⟨e₁, h₁⟩) f) (t f)) * ψ t) * C) +
    γ' * γ' * ((∑ t, (∏ f ∈ arcsInto N v, kingmanTransition (θ.length f) (assignedForest N F v (asg ⟨e₂, h₂⟩ ⟨e₂, h₂⟩) f) (t f)) * ψ t) * C))) = _
  rw [hT₁, hT₂, hT₃, hT₄]
  ring

end TwoArcs

end AllmanEtAl2023.KernelBounds

namespace AllmanEtAl2023.NetworkNk

variable {X : Type*} [Fintype X] [DecidableEq X] {a b c d : X}

/-- The hybrid arc from the node 2 to the node 1 of the inverted subtree of `𝒩(1)⁺`. -/
abbrev arcL : Edge 1 := .tree ⟨0, by norm_num⟩

/-- The hybrid arc from the node 3 to the node 1. -/
abbrev arcR : Edge 1 := .tree ⟨1, by norm_num⟩

/-- The arc of the path, from the node 3 to the node 2. -/
abbrev arcS : Edge 1 := .step ⟨0, by norm_num⟩

theorem outTree_two : (outTree 2 : Edge 1) = arcL := outTree_of_two_le (by norm_num) (by norm_num)

theorem outTree_three : (outTree 3 : Edge 1) = arcR := outTree_of_two_le (by norm_num) (by norm_num)

theorem outPath_two : (outPath 2 : Edge 1) = .bottomTaxon := outPath_self

theorem outPath_three : (outPath 3 : Edge 1) = arcS := outPath_of_lt (by norm_num) (by norm_num)

theorem pathIn_two : (pathIn 2 : Edge 1) = arcS := by
  simp [pathIn]

theorem pathIn_three : (pathIn 3 : Edge 1) = .rootTop := by
  simp [pathIn]

/-! ### The values on the path -/

/-- The value of the forests `A`, `B` on the two hybrid arcs: along the arc of the path, of length `M`, and then to the root, of length `T`. -/
def valOne (c d : X) (M T : ℝ) (r : QuartetTree X) (A B : Finset (Finset X)) : ℝ :=
  ∑ G, kingmanTransition M (A ∪ {{c}}) G * ∑ H, kingmanTransition T (B ∪ G) H * absVal r (H ∪ {{d}})

section Values

variable (hd : ({a, b, c, d} : Finset X).card = 4) (hX : Fintype.card X = 4) {M T : ℝ}
include hd

theorem valOne_same_left (hX : Fintype.card X = 4) (hT : 0 < M + T) : valOne c d M T (quartetTree a b c d hd) {{a}, {b}} ∅ = 1 / 3 := by
  unfold valOne
  simp only [empty_union]
  rw [sum_kingman_comp, union_comm, value_same hd hX hT]

theorem valOne_coal_left : valOne c d M T (quartetTree a b c d hd) (insert {a, b} {{a}, {b}}) ∅ = 1 := by
  unfold valOne
  simp only [empty_union]
  rw [sum_kingman_comp, union_comm, value_coal hd]

theorem valOne_same_right (hX : Fintype.card X = 4) (hT : 0 < T) : valOne c d M T (quartetTree a b c d hd) ∅ {{a}, {b}} = 1 / 3 := by
  unfold valOne
  rw [empty_union, sum_kingman_singleton, union_comm, value_same hd hX hT]

theorem valOne_coal_right : valOne c d M T (quartetTree a b c d hd) ∅ (insert {a, b} {{a}, {b}}) = 1 := by
  unfold valOne
  rw [empty_union, sum_kingman_singleton, union_comm, value_coal hd]

theorem valOne_split (hX : Fintype.card X = 4) {x y : X} (hxy : (x = a ∧ y = b) ∨ (x = b ∧ y = a)) (hd' : ({c, x, y, d} : Finset X).card = 4) (hM : 0 < M) (hT : 0 < T) :
    valOne c d M T (quartetTree a b c d hd) {{x}} {{y}} = Real.exp (-M) / 3 := by
  have h := nmscCF_species_first hd hX hxy hd' hM hT
  rw [nmscCF_treeMetric hd' hX hM hT] at h
  rw [← h]
  unfold valOne
  have hset : ({{x}} ∪ {{c}} : Finset (Finset X)) = {{c}, {x}} := by
    ext A
    simp only [mem_union, mem_insert, mem_singleton]
    tauto
  rw [hset]
  simp only [union_comm ({{y}} : Finset (Finset X))]

end Values

omit [Fintype X] in
/-- A good forest of two lineages with their cluster. -/
theorem eq_insert_of_lineages {F : Finset (Finset X)} (hgood : IsGoodForest F) (hab : a ≠ b) (hlow : lineages F = {a, b}) (hc : ({a, b} : Finset X) ∈ F) :
    F = insert {a, b} {{a}, {b}} := by
  ext B
  simp only [mem_insert, mem_singleton]
  constructor
  · intro hB
    have hsub : B ⊆ {a, b} := hlow ▸ subset_lineages hB
    by_cases hcard : 2 ≤ #B
    · left
      exact Finset.eq_of_subset_of_card_le hsub (by rw [card_pair hab]; exact hcard)
    · have hne := hgood.1.1 B hB
      have h1 : #B = 1 := by
        have := Finset.card_pos.2 hne
        omega
      obtain ⟨z, rfl⟩ := Finset.card_eq_one.1 h1
      have hz := hsub (mem_singleton_self z)
      simp only [mem_insert, mem_singleton] at hz
      rcases hz with rfl | rfl
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr rfl)
  · have hpre : ∀ {z : X}, z ∈ ({a, b} : Finset X) → ({z} : Finset X) ∈ F := by
      intro z hz
      obtain ⟨C, hC, hzC⟩ := mem_lineages.1 (hlow ▸ hz : z ∈ lineages F)
      exact IsGoodForest.singleton_mem hgood hC hzC
    rintro (rfl | rfl | rfl)
    · exact hc
    · exact hpre (by simp)
    · exact hpre (by simp)

/-! ### The parameters -/

section Params

variable (hd : ({a, b, c, d} : Finset X).card = 4) (hX : Fintype.card X = 4) {θ : MetricData (Edge 1)} (hθ : (networkNk 1 a b c d).IsMetric θ)

include hd hX in
theorem isTreeArc_one {e : Edge 1} (he : ∀ m, e ≠ .tree m) : (networkNk 1 a b c d).IsTreeArc e := by
  have hP := isPhylogenetic_networkNk (k := 1) (a := a) (b := b) (c := c) (d := d) hd hX
  have h1 := hP.nonroot_indegree _ (NMSC.target_ne_root hP e)
  have h2 : ¬ (networkNk 1 a b c d).IsHybridArc e := fun h => by
    obtain ⟨m, rfl⟩ := (isHybridArc_iff hd hX e).1 h
    exact he m rfl
  unfold IsHybridArc at h2
  unfold IsTreeArc
  omega

include hd hX in
theorem isHybridArc_one (m : Fin (2 ^ (1 + 1) - 2)) : (networkNk 1 a b c d).IsHybridArc (.tree m) :=
  (isHybridArc_iff hd hX _).2 ⟨m, rfl⟩

omit [Fintype X] [DecidableEq X] in
theorem target_arc_eq (m : Fin (2 ^ (1 + 1) - 2)) : (networkNk 1 a b c d).graph.target (.tree m) = heapNode 1 le_rfl (by norm_num) := by
  rw [target_tree]
  congr 1
  have := m.2
  norm_num at this
  omega

omit [Fintype X] [DecidableEq X] in
theorem target_one_iff (e : Edge 1) : (networkNk 1 a b c d).graph.target e = heapNode 1 le_rfl (by norm_num) ↔ e = arcL ∨ e = arcR :=
  target_eq_inner_iff (h₂ := by norm_num) le_rfl e

include hd hX hθ in
/-- The inheritance of the two hybrid arcs add to one. -/
theorem inheritance_add : θ.inheritance arcL + θ.inheritance arcR = 1 := by
  have hin : 2 ≤ (networkNk 1 a b c d).graph.indegree (heapNode 1 le_rfl (by norm_num)) := by
    have h := isHybridArc_one (a := a) (b := b) (c := c) (d := d) hd hX ⟨0, by norm_num⟩
    unfold IsHybridArc at h
    rwa [target_arc_eq] at h
  have hsum := hθ.2.2.2.2 _ hin
  have hset : (univ.filter fun e : Edge 1 => (networkNk 1 a b c d).graph.target e = heapNode 1 le_rfl (by norm_num)) = {arcL, arcR} := by
    ext e
    simp only [mem_filter, mem_univ, true_and, mem_insert, mem_singleton]
    exact target_one_iff e
  rw [← sum_filter, hset, sum_pair (by simp [arcL, arcR])] at hsum
  exact hsum

end Params

/-! ### The chain -/

section Chain

variable (hd : ({a, b, c, d} : Finset X).card = 4) (hX : Fintype.card X = 4) {θ : MetricData (Edge 1)} (hθ : (networkNk 1 a b c d).IsMetric θ)

/-- **The first entry on `𝒩(1)⁺`.** -/
def firstOne (θ : MetricData (Edge 1)) : ℝ :=
  1 - Real.exp (-θ.length .stem) + Real.exp (-θ.length .stem) *
    (θ.inheritance arcL * θ.inheritance arcL * (1 - 2 / 3 * Real.exp (-θ.length arcL)) +
      θ.inheritance arcR * θ.inheritance arcR * (1 - 2 / 3 * Real.exp (-θ.length arcR)) +
        2 / 3 * (θ.inheritance arcL * θ.inheritance arcR) * Real.exp (-θ.length arcS))

include hd hX hθ in
/-- **The first entry of `CF_abcd` on `𝒩(1)⁺`, for all parameters.** The lineages of `a`, `b` coalesce on the stem, or reach the hybrid node. Then both take one hybrid arc, with probability `γ²` or `(1 - γ)²`, where they coalesce, or reach the path together, and then three lineages meet: `1 / 3`. Or they take different arcs, with probability `2 γ (1 - γ)`, and the lower one must not coalesce with `c` along the arc of the path, and then three lineages meet. Expanded, with `γ² + (1 - γ)² + 2 γ (1 - γ) = 1`, this is equation (9) of Baños (2019). -/
theorem nmscCF_one : nmscCF (networkNk 1 a b c d) θ 0 (quartetTree a b c d hd) = firstOne θ := by
  obtain ⟨hab, hac, had, hbc, hbd, hcd⟩ := ne_of_card_four hd
  have hN := isPhylogenetic_networkNk (k := 1) (a := a) (b := b) (c := c) (d := d) hd hX
  have hw := hθ.isWeakMetric
  have hρ : (0 : ℝ) ≤ 0 ∧ (0 : ℝ) ≤ 1 := ⟨le_rfl, zero_le_one⟩
  have hinj := validInj_injNk (k := 1) (a := a) (b := b) (c := c) (d := d)
  have htaxa : (quartetTree a b c d hd).taxa = univ := eq_univ_of_card _ ((quartetTree a b c d hd).card_taxa.trans hX.symm)
  set r := quartetTree a b c d hd with hr
  set M := θ.length arcS with hM
  set T := θ.length .rootTop with hTdef
  have hposT : 0 < T := hθ.1 _ (isTreeArc_one hd hX (by simp))
  have hposM : 0 < M := hθ.1 _ (isTreeArc_one hd hX (by simp))
  have hin1 : ∀ {e : Edge 1}, (∀ m, e ≠ .tree m) → θ.inheritance e = 1 := fun he => hθ.2.2.1 _ (isTreeArc_one hd hX he)
  set γ := θ.inheritance arcL with hγ
  set γ' := θ.inheritance arcR with hγ'
  set R : Finset (Finset X) → ℝ := fun F => absVal r (F ∪ {{d}}) with hR
  -- the forests above the node 3
  set φ₃ : (Edge 1 → Finset (Finset X)) → ℝ := fun top => R (top .rootTop) with hφ₃
  set φ₂ : (Edge 1 → Finset (Finset X)) → ℝ := fun top => ∑ H, kingmanTransition T (top arcR ∪ top arcS) H * R H with hφ₂
  set φ₁ : (Edge 1 → Finset (Finset X)) → ℝ := fun top => valOne c d M T r (top arcL) (top arcR) with hφ₁
  set X₀ : ℝ := γ * γ' * (Real.exp (-M) / 3) + γ' * γ * (Real.exp (-M) / 3) + γ * γ * (Real.exp (-θ.length arcL) * (1 / 3) + (1 - Real.exp (-θ.length arcL)) * 1) +
    γ' * γ' * (Real.exp (-θ.length arcR) * (1 / 3) + (1 - Real.exp (-θ.length arcR)) * 1) with hX₀
  set φ₀ : (Edge 1 → Finset (Finset X)) → ℝ := fun top => if ({a, b} : Finset X) ∈ top .stem then 1 else X₀ with hφ₀
  have hh1 : (1 : ℕ) + 1 < 2 ^ (1 + 1) := by norm_num
  -- the node 3
  have h₃₃ : (2 : ℕ) + 1 < 2 ^ (1 + 1) := by norm_num
  have hstep₃ : stageMass (networkNk 1 a b c d) θ 0 (injNk 1 a b c d) (stg 1 2) φ₂ = stageMass (networkNk 1 a b c d) θ 0 (injNk 1 a b c d) (stg 1 3) φ₃ := by
    rw [show (3 : ℕ) = 2 + 1 from rfl, ← insert_heapNode_stg h₃₃]
    refine stageMass_eq_insert (downClosed_stg 2) (heapNode_notMem_stg h₃₃) (target_mem_stg_of_source_eq h₃₃) fun bot top hwt => ?_
    have hF := frontier_of_prod_ne_zero hN hinj (downClosed_stg 2) hwt
    have hin : ∀ f : Edge 1, (networkNk 1 a b c d).graph.target f = heapNode (2 + 1) (by omega) h₃₃ ↔ f = .rootTop := fun f => by
      rw [← pathIn_three]
      exact target_eq_path_iff (by omega) (by norm_num) h₃₃ f
    have harr : arriving (networkNk 1 a b c d) (injNk 1 a b c d) top (heapNode (2 + 1) (by omega) h₃₃) = top arcR ∪ top arcS := by
      rw [arriving_path (by omega) (by norm_num) h₃₃, show (2 + 1 : ℕ) = 3 from rfl, outTree_three, outPath_three]
    have hne : (arriving (networkNk 1 a b c d) (injNk 1 a b c d) top (heapNode (2 + 1) (by omega) h₃₃)).Nonempty := by
      obtain ⟨g, hg, hcg⟩ := exists_out_c hd (by norm_num) h₃₃ hF
      obtain ⟨A, hA, -⟩ := mem_lineages.1 ((mem_lineages_arriving _ top _ c).2 (Or.inr ⟨g, hg, hcg⟩))
      exact ⟨A, hA⟩
    have hmem : (Edge.rootTop : Edge 1) ∈ arcsInto (networkNk 1 a b c d) (heapNode (2 + 1) (by omega) h₃₃) := mem_arcsInto.2 ((hin _).2 rfl)
    have hψ : (fun t => φ₃ (overwrite (arcsInto (networkNk 1 a b c d) (heapNode (2 + 1) (by omega) h₃₃)) top t)) = fun t => R (t .rootTop) := by
      funext t
      simp only [hφ₃]
      rw [overwrite_of_mem hmem]
    rw [hψ, vertexKernel_one_arc (N := networkNk 1 a b c d) (θ := θ) (ρ := 0) (e := Edge.rootTop) le_rfl ((hin _).2 rfl) (fun f hf => (hin f).1 hf) (hin1 (by simp)) hne R, harr]
  -- the node 2
  have h₃₂ : (1 : ℕ) + 1 < 2 ^ (1 + 1) := by norm_num
  have hstep₂ : stageMass (networkNk 1 a b c d) θ 0 (injNk 1 a b c d) (stg 1 1) φ₁ = stageMass (networkNk 1 a b c d) θ 0 (injNk 1 a b c d) (stg 1 2) φ₂ := by
    rw [show (2 : ℕ) = 1 + 1 from rfl, ← insert_heapNode_stg h₃₂]
    refine stageMass_eq_insert (downClosed_stg 1) (heapNode_notMem_stg h₃₂) (target_mem_stg_of_source_eq h₃₂) fun bot top hwt => ?_
    have hF := frontier_of_prod_ne_zero hN hinj (downClosed_stg 1) hwt
    have hin : ∀ f : Edge 1, (networkNk 1 a b c d).graph.target f = heapNode (1 + 1) (by omega) h₃₂ ↔ f = arcS := fun f => by
      rw [← pathIn_two]
      exact target_eq_path_iff (by omega) (by norm_num) h₃₂ f
    have hbt : top .bottomTaxon = {{c}} := top_bottomTaxon hd (by norm_num) hF
    have harr : arriving (networkNk 1 a b c d) (injNk 1 a b c d) top (heapNode (1 + 1) (by omega) h₃₂) = top arcL ∪ {{c}} := by
      rw [arriving_path (by omega) (by norm_num) h₃₂, show (1 + 1 : ℕ) = 2 from rfl, outTree_two, outPath_two, hbt]
    have hne : (arriving (networkNk 1 a b c d) (injNk 1 a b c d) top (heapNode (1 + 1) (by omega) h₃₂)).Nonempty := by
      rw [harr]
      exact ⟨{c}, by simp⟩
    have hmem : (arcS : Edge 1) ∈ arcsInto (networkNk 1 a b c d) (heapNode (1 + 1) (by omega) h₃₂) := mem_arcsInto.2 ((hin _).2 rfl)
    have hnot : (arcR : Edge 1) ∉ arcsInto (networkNk 1 a b c d) (heapNode (1 + 1) (by omega) h₃₂) := by
      intro h
      have := (hin _).1 (mem_arcsInto.1 h)
      simp [arcR, arcS] at this
    have hψ : (fun t => φ₂ (overwrite (arcsInto (networkNk 1 a b c d) (heapNode (1 + 1) (by omega) h₃₂)) top t)) =
        fun t => (fun G => ∑ H, kingmanTransition T (top arcR ∪ G) H * R H) (t arcS) := by
      funext t
      simp only [hφ₂]
      rw [overwrite_of_mem hmem, overwrite_of_notMem hnot]
    rw [hψ, vertexKernel_one_arc (N := networkNk 1 a b c d) (θ := θ) (ρ := 0) (e := arcS) le_rfl ((hin _).2 rfl) (fun f hf => (hin f).1 hf) (hin1 (by simp)) hne (fun G => ∑ H, kingmanTransition T (top arcR ∪ G) H * R H), harr]
    rfl
  -- the hybrid node
  have h₃₁ : (0 : ℕ) + 1 < 2 ^ (1 + 1) := by norm_num
  have h₂₁ : (0 : ℕ) + 1 < 2 ^ 1 := by norm_num
  have hstep₁ : stageMass (networkNk 1 a b c d) θ 0 (injNk 1 a b c d) (stg 1 0) φ₀ = stageMass (networkNk 1 a b c d) θ 0 (injNk 1 a b c d) (stg 1 1) φ₁ := by
    change _ = stageMass (networkNk 1 a b c d) θ 0 (injNk 1 a b c d) (stg 1 (0 + 1)) φ₁
    rw [← insert_heapNode_stg h₃₁]
    refine stageMass_eq_insert (downClosed_stg 0) (heapNode_notMem_stg h₃₁) (target_mem_stg_of_source_eq h₃₁) fun bot top hwt => ?_
    have hF := frontier_of_prod_ne_zero hN hinj (downClosed_stg 0) hwt
    set v : Vertex 1 X := heapNode (0 + 1) (by omega) h₃₁ with hv
    have hL : (networkNk 1 a b c d).graph.target arcL = v := (target_one_iff arcL).2 (Or.inl rfl)
    have hR' : (networkNk 1 a b c d).graph.target arcR = v := (target_one_iff arcR).2 (Or.inr rfl)
    have hin : ∀ e, (networkNk 1 a b c d).graph.target e = v → e = arcL ∨ e = arcR := fun e he => (target_one_iff e).1 he
    have harr : arriving (networkNk 1 a b c d) (injNk 1 a b c d) top v = top .stem := by
      rw [hv, arriving_inner (by omega) h₂₁ h₃₁, show (outTree (0 + 1) : Edge 1) = .stem from outTree_one]
    have hfrS : Fr 0 (Edge.stem : Edge 1) := ⟨by simp [tgtRk], by simp [srcRk]⟩
    have hgoodS : IsGoodForest (top .stem) := hF.good_top _ (by
      rw [mem_stg, rk_target]
      exact hfrS.1)
    -- the lineages on the stem
    have hbelow : ∀ {e : Edge 1} {y x : X}, (networkNk 1 a b c d).graph.target e = .taxon y → x ∈ lineages (top e) → x = y := by
      intro e y x he hx
      obtain ⟨u, hu, hxu⟩ := hF.below e (by rw [he]; simp [rk]) x hx
      rw [he] at hu
      have h1 := eq_of_taxon_reaches hu
      have h2 := (mem_lineages_taxaInj.1 hxu).2
      rw [h1] at h2
      exact Vertex.taxon.inj h2
    have honstem : ∀ {x : X}, x ≠ c → x ≠ d → x ∈ lineages (top .stem) := by
      intro x hxc hxd
      obtain ⟨f, ⟨hf₁, hf₂⟩, hx⟩ := exists_fr hF x
      cases f with
      | rootTaxon => exact absurd (hbelow rfl hx) hxd
      | rootTop =>
        simp only [tgtRk] at hf₁
        norm_num at hf₁
      | step t =>
        simp only [tgtRk] at hf₁
        norm_num at hf₁
      | bottomTaxon => exact absurd (hbelow rfl hx) hxc
      | tree m =>
        simp only [tgtRk] at hf₁
        have := m.2
        omega
      | stem => exact hx
      | cherryLeft =>
        simp only [srcRk] at hf₂
        omega
      | cherryRight =>
        simp only [srcRk] at hf₂
        omega
    have hlow : lineages (top .stem) = {a, b} := by
      ext x
      simp only [mem_insert, mem_singleton]
      constructor
      · intro hx
        exact IsLow.of_reaches (reaches_of_mem hF hfrS.1 hx) (by trivial)
      · rintro (rfl | rfl)
        · exact honstem hac had
        · exact honstem hbc hbd
    rw [harr]
    by_cases hc : ({a, b} : Finset X) ∈ top .stem
    · -- coalesced on the stem
      have hφ : φ₀ top = 1 := ite_eq_left hc
      rw [hφ, one_mul]
      have hD := downClosed_stg (k := 1) (a := a) (b := b) (c := c) (d := d) 0
      have hrv : v ≠ (networkNk 1 a b c d).root := (root_ne_heapNode).symm
      have key := vertexKernel_overwrite_eq (N := networkNk 1 a b c d) (θ := θ) (ρ := 0) (inj := injNk 1 a b c d) hN hw hρ hinj hD (heapNode_notMem_stg h₃₁) hrv (target_mem_stg_of_source_eq h₃₁) hwt (c := 1) (φ' := φ₁) ?_
      · rw [harr] at key
        rw [← one_mul (_ ^ 2 : ℝ), ← key]
      intro bot' top' htop' hmem hclust hF'
      rw [insert_heapNode_stg h₃₁] at hF'
      rw [harr] at hmem hclust
      obtain ⟨e, he, habe⟩ := hclust _ hc
      have hgoodL : IsGoodForest (top' arcL) := hF'.good_top _ (by
        rw [mem_stg, rk_target]
        simp [tgtRk])
      have hgoodR : IsGoodForest (top' arcR) := hF'.good_top _ (by
        rw [mem_stg, rk_target]
        simp [tgtRk])
      have hfrL : Fr 1 (arcL : Edge 1) := ⟨by simp [tgtRk], by simp [srcRk]⟩
      have hfrR : Fr 1 (arcR : Edge 1) := ⟨by simp [tgtRk], by simp [srcRk]⟩
      have hneLR : (arcL : Edge 1) ≠ arcR := by simp [arcL, arcR]
      have hsubL : ∀ x, x ∈ lineages (top' arcL) → x = a ∨ x = b := fun x hx => by
        have := (hmem x).1 ⟨_, hL, hx⟩
        rw [hlow] at this
        simpa using this
      have hsubR : ∀ x, x ∈ lineages (top' arcR) → x = a ∨ x = b := fun x hx => by
        have := (hmem x).1 ⟨_, hR', hx⟩
        rw [hlow] at this
        simpa using this
      rcases hin e he with rfl | rfl
      · have hlin : lineages (top' arcL) = {a, b} := by
          ext x
          simp only [mem_insert, mem_singleton]
          refine ⟨hsubL x, ?_⟩
          rintro (rfl | rfl) <;> exact mem_lineages.2 ⟨_, habe, by simp⟩
        have hemp : top' arcR = ∅ := by
          refine eq_empty_of_lineages hgoodR.1 (eq_empty_of_forall_notMem fun x hx => ?_)
          have hxL : x ∈ lineages (top' arcL) := by
            rw [hlin]
            rcases hsubR x hx with rfl | rfl <;> simp
          exact hneLR (eq_of_fr hF' hfrL hfrR hxL hx)
        change valOne c d M T r (top' arcL) (top' arcR) = 1
        rw [eq_insert_of_lineages hgoodL hab hlin habe, hemp]
        exact valOne_coal_left hd
      · have hlin : lineages (top' arcR) = {a, b} := by
          ext x
          simp only [mem_insert, mem_singleton]
          refine ⟨hsubR x, ?_⟩
          rintro (rfl | rfl) <;> exact mem_lineages.2 ⟨_, habe, by simp⟩
        have hemp : top' arcL = ∅ := by
          refine eq_empty_of_lineages hgoodL.1 (eq_empty_of_forall_notMem fun x hx => ?_)
          have hxR : x ∈ lineages (top' arcR) := by
            rw [hlin]
            rcases hsubL x hx with rfl | rfl <;> simp
          exact hneLR (eq_of_fr hF' hfrL hfrR hx hxR)
        change valOne c d M T r (top' arcL) (top' arcR) = 1
        rw [eq_insert_of_lineages hgoodR hab hlin habe, hemp]
        exact valOne_coal_right hd
    · -- apart on the stem
      have hpair := KernelBounds.eq_pair_of_lineages hgoodS hab hlow hc
      have hφ : φ₀ top = X₀ := ite_eq_right hc
      rw [hφ, hpair]
      have hmemL : (arcL : Edge 1) ∈ arcsInto (networkNk 1 a b c d) v := mem_arcsInto.2 hL
      have hmemR : (arcR : Edge 1) ∈ arcsInto (networkNk 1 a b c d) v := mem_arcsInto.2 hR'
      have hvals : ∀ t, φ₁ (overwrite (arcsInto (networkNk 1 a b c d) v) top t) = valOne c d M T r (t arcL) (t arcR) := fun t => by
        simp only [hφ₁]
        rw [overwrite_of_mem hmemL, overwrite_of_mem hmemR]
      rw [KernelBounds.kernel_two_arcs_gamma (by simp [arcL, arcR]) hL hR' hin rfl rfl hab (d₁ := Real.exp (-M) / 3) (d₂ := Real.exp (-M) / 3) (u₁ := 1 / 3) (w₁ := 1) (u₂ := 1 / 3) (w₂ := 1)]
      · intro t h1 h2
        rw [hvals, h1, h2]
        exact valOne_split hd hX (Or.inl ⟨rfl, rfl⟩) (card_species_ab hd) hposM hposT
      · intro t h1 h2
        rw [hvals, h1, h2]
        exact valOne_split hd hX (Or.inr ⟨rfl, rfl⟩) (card_species_ba hd) hposM hposT
      · intro t h1 h2
        rw [hvals, h1, h2]
        exact valOne_same_left hd hX (by linarith)
      · intro t h1 h2
        rw [hvals, h1, h2]
        exact valOne_coal_left hd
      · intro t h1 h2
        rw [hvals, h1, h2]
        exact valOne_same_right hd hX hposT
      · intro t h1 h2
        rw [hvals, h1, h2]
        exact valOne_coal_right hd
  -- the cherry
  set W : ℝ := Real.exp (-θ.length .stem) * X₀ + (1 - Real.exp (-θ.length .stem)) * 1 with hW
  have hstep₀ : stageMass (networkNk 1 a b c d) θ 0 (injNk 1 a b c d) (stgT 1) (fun _ => W) = stageMass (networkNk 1 a b c d) θ 0 (injNk 1 a b c d) (stg 1 0) φ₀ := by
    rw [← insert_cherry_stgT]
    refine stageMass_eq_insert downClosed_stgT (by simp [rk]) (fun e he => ?_) fun bot top hwt => ?_
    · have h1 := rk_target_lt_rk_source (a := a) (b := b) (c := c) (d := d) e
      rw [he] at h1
      have h2 : rk (Vertex.cherry : Vertex 1 X) = 1 := rfl
      rw [mem_stgT]
      omega
    · rw [arriving_cherry hd hX hwt]
      have hmem : (Edge.stem : Edge 1) ∈ arcsInto (networkNk 1 a b c d) Vertex.cherry := mem_arcsInto.2 rfl
      have hψ : (fun t => φ₀ (overwrite (arcsInto (networkNk 1 a b c d) Vertex.cherry) top t)) = fun t => (fun G => if ({a, b} : Finset X) ∈ G then (1 : ℝ) else X₀) (t .stem) := by
        funext t
        simp only [hφ₀]
        rw [overwrite_of_mem hmem]
      rw [hψ, vertexKernel_one_arc (N := networkNk 1 a b c d) (θ := θ) (ρ := 0) (v := Vertex.cherry) (e := Edge.stem) (F := {{a}, {b}}) le_rfl rfl eq_stem_of_target_eq_cherry (hin1 (by simp)) ⟨{a}, by simp⟩ (fun G => if ({a, b} : Finset X) ∈ G then (1 : ℝ) else X₀), sum_kingman_pair hab]
      have h1 : ({a, b} : Finset X) ∉ ({{a}, {b}} : Finset (Finset X)) := pair_notMem_pair hab
      simp only [h1, ↓reduceIte, mem_insert_self]
      rfl
  -- at the root
  have hend : stageMass (networkNk 1 a b c d) θ 0 (injNk 1 a b c d) (stg 1 3) φ₃ =
      stageMass (networkNk 1 a b c d) θ 0 (injNk 1 a b c d) (stg 1 3) (fun top => absVal r (arriving (networkNk 1 a b c d) (injNk 1 a b c d) top .root)) := by
    refine stageMass_congr fun bot top hwt => ?_
    have hF := frontier_of_prod_ne_zero hN hinj (downClosed_stg 3) hwt
    rw [arriving_root, top_rootTaxon hd hF, union_comm]
  have htop := stageMass_top (N := networkNk 1 a b c d) (θ := θ) (ρ := 0) hN (injNk 1 a b c d)
    (fun top => absVal r (arriving (networkNk 1 a b c d) (injNk 1 a b c d) top .root))
  have hstg : (univ.erase (networkNk 1 a b c d).root) = stg 1 3 := stg_top.symm
  rw [hstg, ← hend, ← hstep₃, ← hstep₂, ← hstep₁, ← hstep₀, stageMass_const hN hw.isNormalized le_rfl hinj downClosed_stgT root_notMem_stgT] at htop
  have hZ0 : ((Fintype.card (Finset (Finset X)) : ℝ) ^ Fintype.card (Edge 1)) ^ 2 ≠ 0 := by
    have : (0 : ℝ) < Fintype.card (Finset (Finset X)) := by exact_mod_cast Fintype.card_pos
    positivity
  rw [nmscCF_eq_cherryMass_weak hN hw.isNormalized le_rfl, htaxa, cherryMass_eq_fullMass]
  refine (mul_left_cancel₀ hZ0 (htop.symm.trans (mul_comm _ _))).trans ?_
  rw [hW, hX₀, firstOne]
  simp only [← hγ, ← hγ', ← hM]
  ring

end Chain

/-! ### The range -/

section Range

variable (hd : ({a, b, c, d} : Finset X).card = 4) (hX : Fintype.card X = 4)

include hd hX in
/-- **`𝒩(1)⁺` is level-1**, in the library's sense: its one hybrid node is the node 1 of the inverted subtree. -/
theorem isLevelOne_one : (networkNk 1 a b c d).IsLevelOne := by
  refine BlobStructure.isLevelOne_of_unique_hybrid (h := heapNode 1 le_rfl (by norm_num)) (fun u hu => ?_) ?_
  · obtain ⟨e, he⟩ : ({e | (networkNk 1 a b c d).graph.target e = u} : Set (Edge 1)).Nonempty := by
      refine Set.nonempty_of_ncard_ne_zero ?_
      have : (networkNk 1 a b c d).graph.indegree u = ({e | (networkNk 1 a b c d).graph.target e = u} : Set (Edge 1)).ncard := rfl
      omega
    have he' : (networkNk 1 a b c d).graph.target e = u := he
    have hhy : (networkNk 1 a b c d).IsHybridArc e := by
      unfold IsHybridArc
      rwa [he']
    obtain ⟨m, rfl⟩ := (isHybridArc_iff hd hX e).1 hhy
    rw [← he']
    exact target_arc_eq m
  · have hsub : ({e | (networkNk 1 a b c d).graph.target e = heapNode 1 le_rfl (by norm_num)} : Set (Edge 1)) ⊆ {arcL, arcR} := fun e he => (target_one_iff e).1 he
    have h1 := Set.ncard_le_ncard hsub (Set.toFinite _)
    rw [Set.ncard_pair (by simp [arcL, arcR])] at h1
    exact h1

/-- The parameters of the family that reaches every value: hybrid arcs of length 0, each with inheritance `1/2`. -/
def metricOne (ε M : ℝ) : MetricData (Edge 1) where
  length
    | .stem => ε
    | .step _ => M
    | .tree _ => 0
    | _ => 1
  inheritance
    | .tree _ => 1 / 2
    | _ => 1

include hd hX in
theorem isMetric_metricOne {ε M : ℝ} (hε : 0 < ε) (hM : 0 < M) : (networkNk 1 a b c d).IsMetric (metricOne ε M) := by
  have hm := isMetric_metricNk (k := 1) (ε := 1) (M := 1) hd hX one_pos one_pos
  have hinh : ∀ e : Edge 1, (metricOne ε M).inheritance e = (metricNk 1 1 1).inheritance e := by
    intro e
    cases e <;> rfl
  have hnot : ∀ {e : Edge 1}, (networkNk 1 a b c d).IsTreeArc e → ∀ m, e ≠ .tree m := by
    rintro e he m rfl
    have h := isHybridArc_one (a := a) (b := b) (c := c) (d := d) hd hX m
    unfold IsHybridArc at h
    unfold IsTreeArc at he
    omega
  refine ⟨fun e he => ?_, fun e _ => ?_, fun e he => ?_, fun e he => ?_, fun v hv => ?_⟩
  · cases e with
    | stem => exact hε
    | step t => exact hM
    | tree m => exact absurd rfl (hnot he m)
    | _ => exact one_pos
  · cases e with
    | stem => exact hε.le
    | step t => exact hM.le
    | tree m => exact le_rfl
    | _ => exact zero_le_one
  · rw [hinh]
    exact hm.2.2.1 e he
  · rw [hinh]
    exact hm.2.2.2.1 e he
  · rw [← hm.2.2.2.2 v hv]
    exact Finset.sum_congr rfl fun e _ => by rw [hinh]

/-- The value on the family. -/
theorem firstOne_metricOne (ε M : ℝ) : firstOne (metricOne ε M) = 1 - Real.exp (-ε) * (5 / 6 - Real.exp (-M) / 6) := by
  have h1 : (metricOne ε M).inheritance arcL = 1 / 2 := rfl
  have h2 : (metricOne ε M).inheritance arcR = 1 / 2 := rfl
  have h3 : (metricOne ε M).length arcL = 0 := rfl
  have h4 : (metricOne ε M).length arcR = 0 := rfl
  have h5 : (metricOne ε M).length arcS = M := rfl
  have h6 : (metricOne ε M).length .stem = ε := rfl
  rw [firstOne, h1, h2, h3, h4, h5, h6, neg_zero, Real.exp_zero]
  ring

include hd hX in
/-- **The bounds on `𝒩(1)⁺`**: for all parameters, the first entry is in `(1/6, 1)`. -/
theorem firstOne_bounds {θ : MetricData (Edge 1)} (hθ : (networkNk 1 a b c d).IsMetric θ) : 1 / 6 < firstOne θ ∧ firstOne θ < 1 := by
  have hsum := inheritance_add hd hX hθ
  have hγ₁ : 0 < θ.inheritance arcL := hθ.2.2.2.1 _ (isHybridArc_one hd hX _)
  have hγ₂ : 0 < θ.inheritance arcR := hθ.2.2.2.1 _ (isHybridArc_one hd hX _)
  have hl₁ : 0 ≤ θ.length arcL := hθ.2.1 _ (isHybridArc_one hd hX _)
  have hl₂ : 0 ≤ θ.length arcR := hθ.2.1 _ (isHybridArc_one hd hX _)
  have hlS : 0 < θ.length arcS := hθ.1 _ (isTreeArc_one hd hX (by simp))
  have hlε : 0 < θ.length .stem := hθ.1 _ (isTreeArc_one hd hX (by simp))
  have hx₁ := Real.exp_pos (-θ.length arcL)
  have hx₂ := Real.exp_pos (-θ.length arcR)
  have hy := Real.exp_pos (-θ.length arcS)
  have hp := Real.exp_pos (-θ.length .stem)
  have hx₁' : Real.exp (-θ.length arcL) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
  have hx₂' : Real.exp (-θ.length arcR) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
  have hy' : Real.exp (-θ.length arcS) < 1 := Real.exp_lt_one_iff.2 (by linarith)
  have hp' : Real.exp (-θ.length .stem) < 1 := Real.exp_lt_one_iff.2 (by linarith)
  unfold firstOne
  generalize θ.inheritance arcL = γ at *
  generalize θ.inheritance arcR = γ' at *
  generalize Real.exp (-θ.length arcL) = x₁ at *
  generalize Real.exp (-θ.length arcR) = x₂ at *
  generalize Real.exp (-θ.length arcS) = y at *
  generalize Real.exp (-θ.length .stem) = p at *
  have hg : 0 < γ * γ' := mul_pos hγ₁ hγ₂
  have hAl : γ * γ * (1 / 3) ≤ γ * γ * (1 - 2 / 3 * x₁) := mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  have hAu : γ * γ * (1 - 2 / 3 * x₁) < γ * γ := by
    have : 0 < γ * γ * x₁ := by positivity
    nlinarith
  have hBl : γ' * γ' * (1 / 3) ≤ γ' * γ' * (1 - 2 / 3 * x₂) := mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  have hBu : γ' * γ' * (1 - 2 / 3 * x₂) < γ' * γ' := by
    have : 0 < γ' * γ' * x₂ := by positivity
    nlinarith
  have hCl : 0 < 2 / 3 * (γ * γ') * y := by positivity
  have hCu : 2 / 3 * (γ * γ') * y < 2 * (γ * γ') := by nlinarith
  have hγγ : γ' = 1 - γ := by linarith
  subst hγγ
  set W := γ * γ * (1 - 2 / 3 * x₁) + (1 - γ) * (1 - γ) * (1 - 2 / 3 * x₂) + 2 / 3 * (γ * (1 - γ)) * y with hW
  have hW₁ : 1 / 6 < W := by nlinarith [sq_nonneg (2 * γ - 1)]
  have hW₂ : W < 1 := by nlinarith
  constructor
  · nlinarith [mul_pos (sub_pos.2 hp') (sub_pos.2 hW₂)]
  · nlinarith [mul_pos hp (sub_pos.2 hW₂)]

include hd hX in
/-- **"If `𝒩⁺` is level-1, then Baños (2019) showed `CF_{ab|cd}` may take on any value in `(1/6, 1)`"** (`a:claim:banos-range`, before Proposition 1). `𝒩(1)⁺` is level-1, with `T_rd(𝒩⁻) = ab|cd`, and the values of the first entry of its `CF`, over all numerical parameters, are exactly `(1/6, 1)`. Each value is on the line: the `CF` is `(v, (1 - v)/2, (1 - v)/2)`. Baños's further bound on all level-1 networks, by his reduction to convex sums, isn't proved here. -/
theorem banos_range :
    (networkNk 1 a b c d).IsLevelOne ∧ (Trd (isBinaryNetwork_networkNk 1 hd hX) (nontrivial_of_card_four hX)).HasQuartetTopology a b c d ∧
      {v | ∃ θ, (networkNk 1 a b c d).IsMetric θ ∧ nmscCF (networkNk 1 a b c d) θ 0 (quartetTree a b c d hd) = v} = Set.Ioo (1 / 6) 1 ∧
      ∀ v ∈ Set.Ioo (1 / 6 : ℝ) 1, ∃ θ, (networkNk 1 a b c d).IsMetric θ ∧ cfTriple (networkNk 1 a b c d) θ a b c d hd = (v, (1 - v) / 2, (1 - v) / 2) := by
  have hex : ∀ v ∈ Set.Ioo (1 / 6 : ℝ) 1, ∃ θ, (networkNk 1 a b c d).IsMetric θ ∧ nmscCF (networkNk 1 a b c d) θ 0 (quartetTree a b c d hd) = v := by
    rintro v ⟨h1, h2⟩
    set y : ℝ := min (1 / 2) ((6 * v - 1) / 2) with hy
    have hy0 : 0 < y := lt_min (by norm_num) (by linarith)
    have hy1 : y < 1 := lt_of_le_of_lt (min_le_left _ _) (by norm_num)
    have hy2 : y ≤ (6 * v - 1) / 2 := min_le_right _ _
    set D : ℝ := 5 / 6 - y / 6 with hD
    have hDpos : 0 < D := by rw [hD]; linarith
    have hlt : 1 - v < D := by rw [hD]; linarith
    set p : ℝ := (1 - v) / D with hp
    have hp0 : 0 < p := div_pos (by linarith) hDpos
    have hp1 : p < 1 := (div_lt_one hDpos).2 hlt
    have hε : 0 < -Real.log p := by linarith [Real.log_neg hp0 hp1]
    have hM : 0 < -Real.log y := by linarith [Real.log_neg hy0 hy1]
    refine ⟨metricOne (-Real.log p) (-Real.log y), isMetric_metricOne hd hX hε hM, ?_⟩
    rw [nmscCF_one hd hX (isMetric_metricOne hd hX hε hM), firstOne_metricOne, neg_neg, neg_neg, Real.exp_log hp0, Real.exp_log hy0]
    have : p * D = 1 - v := by
      rw [hp]
      field_simp
    rw [hD] at this
    linarith
  refine ⟨isLevelOne_one hd hX, hasQuartetTopology_networkNk 1 hd hX, ?_, fun v hv => ?_⟩
  · ext v
    constructor
    · rintro ⟨θ, hθ, rfl⟩
      rw [nmscCF_one hd hX hθ]
      exact firstOne_bounds hd hX hθ
    · exact hex v
  · obtain ⟨θ, hθ, hF⟩ := hex v hv
    refine ⟨θ, hθ, ?_⟩
    obtain ⟨p', q', heq, -, -, -, -, hsum⟩ := proposition1 (isBinaryNetwork_networkNk 1 hd hX) hX hd (hasQuartetTopology_networkNk 1 hd hX) hθ
    have hp : p' = v := by
      have h1 : (cfTriple (networkNk 1 a b c d) θ a b c d hd).1 = v := hF
      rw [heq] at h1
      exact h1
    have hq : q' = (1 - v) / 2 := by
      rw [hp] at hsum
      linarith
    rw [heq, hp, hq]

end Range

end AllmanEtAl2023.NetworkNk
