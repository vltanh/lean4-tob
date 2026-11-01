module

public import AllmanEtAl2023.Proposition1

/-!
# Allman, Baños, Mitchell, Rhodes 2023: the distance between blobs is not identifiable

"For example, on the 4-taxon network in Fig. 6 if the length of the edge between the blobs is held fixed but `k` or `M` varied, the `CF` varies over a line segment. This segment overlaps a similarly constructed segment
of `CF`s for a nearby value `ε′ ≈ ε`. Thus the distance between blobs cannot be identified in this 4-taxon case." (Section 5.)

The edge between the blobs of `𝒩(k)⁺` is the stem, of length `ε`. On one topological network `𝒩(k)⁺`, so with one tree of blobs, of topology `ab|cd`:

* at `M = 0`, where the parameters are on the boundary, a weak metric, the first entry of the `CF` is at least `(1 - exp (-3)) / 3`: the three lineages of `a`, `b`, `c` meet on the arc from the root, of length 1, or `a`, `b` have coalesced
  (`cf_first_ge`).
* at large `M` the first entry is at most `(1 - α) + exp (-M)` (`cf_first_le`).
* the first entry is continuous in `M`, so it takes all values between; the `CF` is on the line `(v, (1 - v)/2, (1 - v)/2)` (`exists_M_of_value`). This is the segment.
* `1 - α` is continuous in `ε`, so for `ε₀` small, `k ≥ 2`, and all `ε′` near `ε₀`, the segments of `ε₀` and of `ε′` share a nondegenerate segment: `blobDistance_not_identifiable`.

Two points on the paper's sentences. "`k` or `M` varied" is loose: `k` is discrete, so only `M` gives a segment. And the bounds here need `1 - α < (1 - exp (-3)) / 3`, so `k ≥ 2` and `ε₀` small; the paper's example is `k = 3` in Fig. 6, with no value of `ε`. For `k = 1` the
segments do exist, by a finer computation (the first entry at `M = 0` and its limit at `M = ∞` differ by `p (1 - p) / 6`), which isn't formalized here.
-/

@[expose] public noncomputable section

open Phylogenetics Phylogenetics.RootedNetwork Phylogenetics.NMSC Finset Filter Topology AllmanEtAl2023.KernelBounds
open scoped Classical

namespace AllmanEtAl2023.InPassing

open AllmanEtAl2023.NetworkNk

variable {X : Type*} [Fintype X] [DecidableEq X] {k : ℕ} {a b c d : X}

/-! ### Three lineages along an arc -/

omit [Fintype X] in
theorem kingmanTransition_relabel_sum [Fintype X] {F : Finset (Finset X)} (π : Equiv.Perm X) (hF : relabelFamily π F = F) (t : ℝ) (C : Finset X) :
    ∑ G, kingmanTransition t F G * (if C.map π.toEmbedding ∈ G then 1 else 0) = ∑ G, kingmanTransition t F G * (if C ∈ G then 1 else 0) := by
  rw [← (relabelFamilyEquiv π).sum_comp]
  refine sum_congr rfl fun G _ => ?_
  simp only [relabelFamilyEquiv_apply]
  have h1 : kingmanTransition t F (relabelFamily π G) = kingmanTransition t F G := by
    conv_lhs => rw [← hF]
    exact kingmanTransition_relabelFamily π t F G
  rw [h1]
  simp only [map_mem_relabelFamily]

/-- **Three lineages along an arc**: the first coalescence is of each pair with probability `1/3`. -/
theorem le_sum_kingman_three {a b c : X} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) {t : ℝ} (ht : 0 ≤ t) :
    (1 - Real.exp (-(3 * t))) / 3 ≤
      ∑ G, kingmanTransition t (({a, b, c} : Finset X).image fun x => ({x} : Finset X)) G * (if ({a, b} : Finset X) ∈ G then 1 else 0) := by
  set S : Finset (Finset X) := ({a, b, c} : Finset X).image fun x => ({x} : Finset X) with hS
  have hgood : IsGoodForest S := isGoodForest_singletons _
  have hlin : lineages S = {a, b, c} := lineages_image_singleton _
  have hsing : ∀ {x : X}, x ∈ ({a, b, c} : Finset X) → ({x} : Finset X) ∈ S := fun hx => mem_image_of_mem _ hx
  have hcard3 : #({a, b, c} : Finset X) = 3 := by
    rw [card_insert_of_notMem (by simp [hab, hac]), card_pair hbc]
  have hroots : roots S = S := by
    refine filter_true_of_mem fun A hA B hB hAB => ?_
    obtain ⟨x, -, rfl⟩ := mem_image.1 hA
    obtain ⟨y, -, rfl⟩ := mem_image.1 hB
    rw [singleton_subset_singleton] at hAB
    rw [hAB]
  have hself : kingmanTransition t S S = Real.exp (-(3 * t)) := by
    rw [kingmanTransition_apply_self hgood.1, hroots, hS, card_image_of_injective _ singleton_injective, hcard3]
    norm_num
  -- the symmetries of the three lineages
  have hfix : ∀ π : Equiv.Perm X, (∀ x ∈ ({a, b, c} : Finset X), π x ∈ ({a, b, c} : Finset X)) → relabelFamily π S = S := by
    intro π hπ
    refine Finset.eq_of_subset_of_card_le ?_ ?_
    · intro A hA
      obtain ⟨B, hB, rfl⟩ := mem_image.1 hA
      obtain ⟨x, hx, rfl⟩ := mem_image.1 hB
      simp only [map_singleton, Equiv.coe_toEmbedding]
      exact hsing (hπ x hx)
    · rw [card_relabelFamily]
  have h13 : ∑ G, kingmanTransition t S G * (if ({a, c} : Finset X) ∈ G then 1 else 0) =
      ∑ G, kingmanTransition t S G * (if ({a, b} : Finset X) ∈ G then 1 else 0) := by
    have hπ : ({a, b} : Finset X).map (Equiv.swap b c).toEmbedding = {a, c} := by
      ext z
      simp only [Finset.mem_map, mem_insert, mem_singleton, Equiv.coe_toEmbedding]
      constructor
      · rintro ⟨y, rfl | rfl, rfl⟩
        · rw [Equiv.swap_apply_of_ne_of_ne hab hac]
          exact Or.inl rfl
        · rw [Equiv.swap_apply_left]
          exact Or.inr rfl
      · rintro (rfl | rfl)
        · exact ⟨z, Or.inl rfl, Equiv.swap_apply_of_ne_of_ne hab hac⟩
        · exact ⟨b, Or.inr rfl, Equiv.swap_apply_left _ _⟩
    rw [← hπ]
    refine kingmanTransition_relabel_sum _ (hfix _ fun x hx => ?_) t _
    simp only [mem_insert, mem_singleton] at hx ⊢
    rcases hx with rfl | rfl | rfl
    · rw [Equiv.swap_apply_of_ne_of_ne hab hac]
      exact Or.inl rfl
    · rw [Equiv.swap_apply_left]
      exact Or.inr (Or.inr rfl)
    · rw [Equiv.swap_apply_right]
      exact Or.inr (Or.inl rfl)
  have h23 : ∑ G, kingmanTransition t S G * (if ({b, c} : Finset X) ∈ G then 1 else 0) =
      ∑ G, kingmanTransition t S G * (if ({a, b} : Finset X) ∈ G then 1 else 0) := by
    have hπ : ({a, b} : Finset X).map (Equiv.swap a c).toEmbedding = {b, c} := by
      ext z
      simp only [Finset.mem_map, mem_insert, mem_singleton, Equiv.coe_toEmbedding]
      constructor
      · rintro ⟨y, rfl | rfl, rfl⟩
        · rw [Equiv.swap_apply_left]
          exact Or.inr rfl
        · rw [Equiv.swap_apply_of_ne_of_ne hab.symm hbc]
          exact Or.inl rfl
      · rintro (rfl | rfl)
        · exact ⟨z, Or.inr rfl, Equiv.swap_apply_of_ne_of_ne hab.symm hbc⟩
        · exact ⟨a, Or.inl rfl, Equiv.swap_apply_left _ _⟩
    rw [← hπ]
    refine kingmanTransition_relabel_sum _ (hfix _ fun x hx => ?_) t _
    simp only [mem_insert, mem_singleton] at hx ⊢
    rcases hx with rfl | rfl | rfl
    · rw [Equiv.swap_apply_left]
      exact Or.inr (Or.inr rfl)
    · rw [Equiv.swap_apply_of_ne_of_ne hab.symm hbc]
      exact Or.inr (Or.inl rfl)
    · rw [Equiv.swap_apply_right]
      exact Or.inl rfl
  -- a forest other than `S` has one of the pairs
  have hcover : ∀ G, kingmanTransition t S G * (if G = S then 0 else 1) ≤
      kingmanTransition t S G * (if ({a, b} : Finset X) ∈ G then 1 else 0) +
        kingmanTransition t S G * (if ({a, c} : Finset X) ∈ G then 1 else 0) +
          kingmanTransition t S G * (if ({b, c} : Finset X) ∈ G then 1 else 0) := by
    intro G
    have hnn := kingmanTransition_nonneg ht S G
    by_cases hK : kingmanTransition t S G = 0
    · simp [hK]
    obtain ⟨hG, hSG, hlG⟩ := kingmanTransition_support_good hgood hK
    by_cases hGS : G = S
    · rw [ite_eq_left hGS, mul_zero]
      refine add_nonneg (add_nonneg ?_ ?_) ?_ <;> refine mul_nonneg hnn ?_ <;> split_ifs <;> norm_num
    · rw [ite_eq_right hGS, mul_one]
      -- a cluster of two
      have hex : ∃ C ∈ G, #C = 2 := by
        by_contra hno
        have := hG.eq_singletons hno
        rw [hlG, hlin] at this
        exact hGS this
      obtain ⟨C, hC, hC2⟩ := hex
      have hsub : C ⊆ {a, b, c} := by
        rw [← hlin, ← hlG]
        exact subset_lineages hC
      have hcases : C = {a, b} ∨ C = {a, c} ∨ C = {b, c} := by
        obtain ⟨x, y, hxy, rfl⟩ := card_eq_two.1 hC2
        have hx : x ∈ ({a, b, c} : Finset X) := hsub (by simp)
        have hy : y ∈ ({a, b, c} : Finset X) := hsub (by simp)
        simp only [mem_insert, mem_singleton] at hx hy
        rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl <;> first
          | exact absurd rfl hxy
          | exact Or.inl rfl
          | exact Or.inr (Or.inl rfl)
          | exact Or.inr (Or.inr rfl)
          | exact Or.inl (pair_comm _ _)
          | exact Or.inr (Or.inl (pair_comm _ _))
          | exact Or.inr (Or.inr (pair_comm _ _))
      have h0 : ∀ D : Finset X, 0 ≤ kingmanTransition t S G * (if D ∈ G then (1 : ℝ) else 0) := fun D => by
        refine mul_nonneg hnn ?_
        split_ifs <;> norm_num
      rcases hcases with rfl | rfl | rfl
      · rw [ite_eq_left hC, mul_one]
        linarith [h0 {a, c}, h0 {b, c}]
      · rw [ite_eq_left hC, mul_one]
        linarith [h0 {a, b}, h0 {b, c}]
      · rw [ite_eq_left hC, mul_one]
        linarith [h0 {a, b}, h0 {a, c}]
  have hsum := sum_le_sum fun G (_ : G ∈ (univ : Finset (Finset (Finset X)))) => hcover G
  simp only [sum_add_distrib] at hsum
  rw [h13, h23] at hsum
  have hone : ∑ G, kingmanTransition t S G * (if G = S then 0 else 1) = 1 - Real.exp (-(3 * t)) := by
    have h1 := kingmanTransition_sum hgood.1 t
    have h2 : ∀ G, kingmanTransition t S G * (if G = S then 0 else 1) = kingmanTransition t S G - if G = S then kingmanTransition t S G else 0 := by
      intro G
      split_ifs <;> ring
    simp only [h2]
    rw [sum_sub_distrib, h1, sum_ite_eq' univ S, ite_eq_left (mem_univ S), hself]
  linarith

/-! ### The parameters at `M = 0` -/

omit [Fintype X] [DecidableEq X] in
theorem metricNk_inheritance (ε M ε' M' : ℝ) : (metricNk k ε M).inheritance = (metricNk k ε' M').inheritance := by
  funext e
  cases e <;> rfl

theorem isWeakMetric_metricNk (hd : ({a, b, c, d} : Finset X).card = 4) (hX : Fintype.card X = 4) {ε M : ℝ} (hε : 0 ≤ ε) (hM : 0 ≤ M) :
    (networkNk k a b c d).IsWeakMetric (metricNk k ε M) := by
  have hpow : (0 : ℝ) ≤ 2 ^ k - 1 := sub_nonneg.2 (one_le_pow₀ (by norm_num))
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hn := (isMetric_metricNk (k := k) (ε := 1) (M := 1) hd hX one_pos one_pos).isNormalized
  refine ⟨fun e => ?_, fun e _ => ?_, fun e he => ?_, fun v hv => ?_⟩
  · cases e with
    | rootTaxon => simp only [metricNk]; positivity
    | rootTop => simp [metricNk]
    | step t => exact hM
    | bottomTaxon => simp only [metricNk]; positivity
    | tree m =>
      simp only [metricNk]
      split_ifs <;> positivity
    | stem => exact hε
    | cherryLeft => simp [metricNk]
    | cherryRight => simp [metricNk]
  · cases e with
    | tree m => simp [metricNk]
    | _ => simp [metricNk]
  · rw [metricNk_inheritance ε M 1 1]
    exact hn.1 e he
  · rw [metricNk_inheritance ε M 1 1]
    exact hn.2 v hv

/-! ### The first entry at `M = 0` -/

section Boundary

variable (hd : ({a, b, c, d} : Finset X).card = 4) (hX : Fintype.card X = 4) {ε : ℝ} (hε : 0 < ε)

include hd hX in
/-- **At `M = 0`, the lineage of `c` stays alone on the path below the top**: the arcs of the path have length 0. -/
theorem eq_singleton_of_mem_frontPath {n : ℕ} (hn₀ : 2 ^ k - 1 ≤ n) (hn : n + 1 < 2 ^ (k + 1)) {bot top : Edge k → Finset (Finset X)}
    (hw : ∏ u ∈ stg k n, vertexWeight (networkNk k a b c d) (metricNk k ε 0) 0 (injNk k a b c d) u bot top ≠ 0) {C : Finset X}
    (hC : C ∈ top (frontPath n)) (hcC : c ∈ C) : C = {c} := by
  obtain ⟨hab, hac, had, hbc, hbd, hcd⟩ := ne_of_card_four hd
  have hN := isPhylogenetic_networkNk (k := k) hd hX
  have hinj := validInj_injNk (k := k) (a := a) (b := b) (c := c) (d := d)
  have h1k := one_le_two_pow_k k
  induction n, hn₀ using Nat.le_induction generalizing C with
  | base =>
    have hF := frontier_of_prod_ne_zero hN hinj (downClosed_stg _) hw
    rw [frontPath_start, top_bottomTaxon hd (by omega) hF] at hC
    exact mem_singleton.1 hC
  | succ n hn' ih =>
    have h₃ : n + 1 < 2 ^ (k + 1) := by omega
    have hn₁ : 2 ^ k ≤ n + 1 := by omega
    have hw' : ∏ u ∈ stg k n, vertexWeight (networkNk k a b c d) (metricNk k ε 0) 0 (injNk k a b c d) u bot top ≠ 0 :=
      prod_ne_zero_iff.2 fun u hu => prod_ne_zero_iff.1 hw u (by
        rw [mem_stg] at hu ⊢
        omega)
    have hF := frontier_of_prod_ne_zero hN hinj (downClosed_stg _) hw'
    have hv : vertexWeight (networkNk k a b c d) (metricNk k ε 0) 0 (injNk k a b c d) (heapNode (n + 1) (by omega) h₃) bot top ≠ 0 :=
      prod_ne_zero_iff.1 hw _ (by rw [mem_stg, rk_heapNode])
    have hin : (networkNk k a b c d).graph.target (pathIn (n + 1)) = heapNode (n + 1) (by omega) h₃ :=
      (target_eq_path_iff (by omega) hn₁ h₃ _).2 rfl
    have hK : kingmanTransition ((metricNk k ε 0).length (pathIn (n + 1))) (bot (pathIn (n + 1))) (top (pathIn (n + 1))) ≠ 0 :=
      prod_ne_zero_iff.1 (right_ne_zero_of_mul hv) _ (mem_arcsInto.2 hin)
    rw [length_pathIn hn₁ h₃, ite_eq_right (by omega), kingmanTransition_zero, Matrix.one_apply] at hK
    have htb : bot (pathIn (n + 1)) = top (pathIn (n + 1)) := by
      by_contra hne
      exact hK (ite_eq_right hne)
    rw [frontPath_succ hn₁, ← htb] at hC
    obtain ⟨a', ha'⟩ := exists_assignment (left_ne_zero_of_mul hv)
    have hCF := (mem_forestBelow.1 ((ha' ⟨pathIn (n + 1), hin⟩) ▸ hC)).1
    rw [arriving_path (by omega) hn₁ h₃, mem_union, outPath_eq_frontPath hn₁ h₃] at hCF
    rcases hCF with hCF | hCF
    · exfalso
      have hsrc := (source_eq_path_iff (a := a) (b := b) (c := c) (d := d) (by omega) hn₁ h₃ (outTree (n + 1))).2 (Or.inl rfl)
      rcases IsLow.of_reaches (reaches_of_mem hF (fr_of_source_eq h₃ hsrc).1 (mem_lineages.2 ⟨C, hCF, hcC⟩)) (isLow_target_outTree h₃) with h | h
      · exact hac h.symm
      · exact hbc h.symm
    · exact ih h₃ hw' hCF hcC

include hd hX in
/-- **At `M = 0`, three lineages meet on the arc from the root**, or `a` and `b` have coalesced. -/
theorem le_sum_kingman_top {bot top : Edge k → Finset (Finset X)}
    (hw : ∏ u ∈ stg k (2 ^ (k + 1) - 2), vertexWeight (networkNk k a b c d) (metricNk k ε 0) 0 (injNk k a b c d) u bot top ≠ 0)
    (h₃ : 2 ^ (k + 1) - 2 + 1 < 2 ^ (k + 1)) :
    (1 - Real.exp (-3)) / 3 ≤
      ∑ G, kingmanTransition 1 (arriving (networkNk k a b c d) (injNk k a b c d) top (heapNode (2 ^ (k + 1) - 2 + 1) (by omega) h₃)) G *
        (if ({a, b} : Finset X) ∈ G then 1 else 0) := by
  obtain ⟨hab, hac, had, hbc, hbd, hcd⟩ := ne_of_card_four hd
  have hN := isPhylogenetic_networkNk (k := k) hd hX
  have hinj := validInj_injNk (k := k) (a := a) (b := b) (c := c) (d := d)
  have h1k := one_le_two_pow_k k
  have h2k := two_pow_succ_eq k
  have hF := frontier_of_prod_ne_zero hN hinj (downClosed_stg _) hw
  set n₁ := 2 ^ (k + 1) - 2 with hn₁
  have hk₁ : 2 ^ k ≤ n₁ + 1 := by omega
  set F := arriving (networkNk k a b c d) (injNk k a b c d) top (heapNode (n₁ + 1) (by omega) h₃) with hF'
  have hgood : IsGoodForest F := hF.good_arriving hinj (heapNode_notMem_stg h₃) (target_mem_stg_of_source_eq h₃)
  -- the lineages at the node
  have hsource : ∀ {f : Edge k}, Fr n₁ f → (networkNk k a b c d).graph.source f = heapNode (n₁ + 1) (by omega) h₃ ∨ f = .rootTaxon := by
    intro f hf
    by_cases h : srcRk f = n₁ + 2
    · exact Or.inl (eq_heapNode_of_rk h₃ ((rk_source f).trans h))
    · refine Or.inr ?_
      obtain ⟨hf₁, hf₂⟩ := hf
      cases f with
      | rootTaxon => rfl
      | rootTop =>
        simp only [tgtRk] at hf₁
        omega
      | step t =>
        have := t.2
        simp only [srcRk] at hf₂ h
        omega
      | bottomTaxon =>
        simp only [srcRk] at hf₂ h
        omega
      | tree m =>
        have := m.2
        simp only [srcRk] at hf₂ h
        omega
      | stem =>
        simp only [srcRk] at hf₂ h
        omega
      | cherryLeft =>
        simp only [srcRk] at hf₂ h
        omega
      | cherryRight =>
        simp only [srcRk] at hf₂ h
        omega
  have hd_root : top .rootTaxon = {{d}} := top_rootTaxon hd hF
  have hmem_of : ∀ {x : X}, x ≠ d → x ∈ lineages F := by
    intro x hx
    obtain ⟨f, hf, hxf⟩ := exists_fr hF x
    rcases hsource hf with h | rfl
    · exact (mem_lineages_arriving _ top _ x).2 (Or.inr ⟨f, h, hxf⟩)
    · rw [hd_root] at hxf
      simp only [lineages_singleton, mem_singleton] at hxf
      exact absurd hxf hx
  have hd_not : d ∉ lineages F := by
    intro hx
    obtain ⟨g, hg, hxg⟩ := exists_out_of_mem_arriving hx
    have hfr : Fr n₁ (Edge.rootTaxon : Edge k) := ⟨by simp [tgtRk], by
      simp only [srcRk]
      omega⟩
    have h1 := eq_of_fr hF (fr_of_source_eq h₃ hg) hfr hxg (by rw [hd_root]; simp)
    rw [h1] at hg
    exact root_ne_heapNode hg
  have hlin : lineages F = {a, b, c} := by
    ext x
    simp only [mem_insert, mem_singleton]
    have hall : x = a ∨ x = b ∨ x = c ∨ x = d := by
      have hu : ({a, b, c, d} : Finset X) = univ := eq_univ_of_card _ (by rw [hd, hX])
      have := mem_univ x
      rw [← hu] at this
      simpa using this
    constructor
    · intro hx
      rcases hall with rfl | rfl | rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr rfl)
      · exact absurd hx hd_not
    · rintro (rfl | rfl | rfl)
      · exact hmem_of had
      · exact hmem_of hbd
      · exact hmem_of hcd
  -- the lineage of `c` is alone
  have hc_alone : ∀ C ∈ F, c ∈ C → C = {c} := by
    intro C hC hcC
    rw [hF', arriving_path (by omega) hk₁ h₃, mem_union, outPath_eq_frontPath hk₁ h₃] at hC
    rcases hC with hC | hC
    · exfalso
      have hsrc := (source_eq_path_iff (a := a) (b := b) (c := c) (d := d) (by omega) hk₁ h₃ (outTree (n₁ + 1))).2 (Or.inl rfl)
      rcases IsLow.of_reaches (reaches_of_mem hF (fr_of_source_eq h₃ hsrc).1 (mem_lineages.2 ⟨C, hC, hcC⟩)) (isLow_target_outTree h₃) with h | h
      · exact hac h.symm
      · exact hbc h.symm
    · exact eq_singleton_of_mem_frontPath hd hX (by omega) h₃ hw hC hcC
  by_cases hab_mem : ({a, b} : Finset X) ∈ F
  · -- `a`, `b` have coalesced
    have hone : ∑ G, kingmanTransition 1 F G * (if ({a, b} : Finset X) ∈ G then 1 else 0) = 1 := by
      refine Eq.trans (sum_congr rfl fun G _ => ?_) (kingmanTransition_sum hgood.1 1)
      by_cases hK : kingmanTransition 1 F G = 0
      · simp [hK]
      · rw [ite_eq_left ((kingmanTransition_support_good hgood hK).2.1 hab_mem), mul_one]
    rw [hone]
    have := Real.exp_pos (-3 : ℝ)
    linarith
  · have hno : ¬ ∃ C ∈ F, #C = 2 := by
      rintro ⟨C, hC, hC2⟩
      have hsub : C ⊆ {a, b, c} := hlin ▸ subset_lineages hC
      by_cases hcC : c ∈ C
      · rw [hc_alone C hC hcC] at hC2
        simp at hC2
      · have hsub2 : C ⊆ {a, b} := fun x hx => by
          have := hsub hx
          simp only [mem_insert, mem_singleton] at this ⊢
          rcases this with h | h | h
          · exact Or.inl h
          · exact Or.inr h
          · exact absurd (h ▸ hx) hcC
        have heq : C = {a, b} := Finset.eq_of_subset_of_card_le hsub2 (by rw [hC2, card_pair hab])
        exact hab_mem (heq ▸ hC)
    have hFeq := hgood.eq_singletons hno
    rw [hlin] at hFeq
    rw [hFeq]
    have := le_sum_kingman_three hab hac hbc (t := 1) zero_le_one
    rwa [mul_one] at this

include hd hX hε in
/-- **The first entry of the `CF` at `M = 0`** is at least `(1 - exp (-3)) / 3`. -/
theorem cf_first_ge :
    (1 - Real.exp (-3)) / 3 ≤ (cfTriple (networkNk k a b c d) (metricNk k ε 0) a b c d hd).1 := by
  obtain ⟨hab, hac, had, hbc, hbd, hcd⟩ := ne_of_card_four hd
  have hN := isPhylogenetic_networkNk (k := k) hd hX
  have hθ : (networkNk k a b c d).IsWeakMetric (metricNk k ε 0) := isWeakMetric_metricNk hd hX hε.le le_rfl
  have hρ : (0 : ℝ) ≤ 0 ∧ (0 : ℝ) ≤ 1 := ⟨le_rfl, zero_le_one⟩
  have hinj := validInj_injNk (k := k) (a := a) (b := b) (c := c) (d := d)
  have h1k := one_le_two_pow_k k
  have h2k := two_pow_succ_eq k
  have h₃ : 2 ^ (k + 1) - 2 + 1 < 2 ^ (k + 1) := by omega
  set c₀ : ℝ := (1 - Real.exp (-3)) / 3 with hc₀
  -- the last step of the chain
  have hstep : stageMass (networkNk k a b c d) (metricNk k ε 0) 0 (injNk k a b c d) (stg k (2 ^ (k + 1) - 2)) (fun _ => c₀) ≤
      stageMass (networkNk k a b c d) (metricNk k ε 0) 0 (injNk k a b c d) (stg k (2 ^ (k + 1) - 2 + 1))
        (fun top => if ({a, b} : Finset X) ∈ top .rootTop then 1 else 0) := by
    rw [← insert_heapNode_stg h₃]
    refine stageMass_le_insert hθ hρ (downClosed_stg _) (heapNode_notMem_stg h₃) (target_mem_stg_of_source_eq h₃) fun bot top hw => ?_
    have hF := frontier_of_prod_ne_zero hN hinj (downClosed_stg _) hw
    have hn₁ : 2 ^ k ≤ 2 ^ (k + 1) - 2 + 1 := by omega
    have hpath : (pathIn (2 ^ (k + 1) - 2 + 1) : Edge k) = .rootTop := by
      simp only [pathIn]
      rw [dite_eq_right (by omega)]
    have hin : ∀ f : Edge k, (networkNk k a b c d).graph.target f = heapNode (2 ^ (k + 1) - 2 + 1) (by omega) h₃ ↔ f = .rootTop := by
      intro f
      rw [← hpath]
      exact target_eq_path_iff (by omega) hn₁ h₃ f
    have hmem : (Edge.rootTop : Edge k) ∈ arcsInto (networkNk k a b c d) (heapNode (2 ^ (k + 1) - 2 + 1) (by omega) h₃) := mem_arcsInto.2 ((hin _).2 rfl)
    have hψ : (fun t => if ({a, b} : Finset X) ∈ overwrite (arcsInto (networkNk k a b c d) (heapNode (2 ^ (k + 1) - 2 + 1) (by omega) h₃)) top t .rootTop then (1 : ℝ) else 0) =
        fun t => (fun G => if ({a, b} : Finset X) ∈ G then (1 : ℝ) else 0) (t .rootTop) := by
      funext t
      rw [overwrite_of_mem hmem]
    have hne : (arriving (networkNk k a b c d) (injNk k a b c d) top (heapNode (2 ^ (k + 1) - 2 + 1) (by omega) h₃)).Nonempty := by
      obtain ⟨g, hg, hcg⟩ := exists_out_c hd hn₁ h₃ hF
      obtain ⟨A, hA, -⟩ := mem_lineages.1 ((mem_lineages_arriving _ top _ c).2 (Or.inr ⟨g, hg, hcg⟩))
      exact ⟨A, hA⟩
    have key := vertexKernel_one_arc (N := networkNk k a b c d) (θ := metricNk k ε 0) (ρ := 0) (e := Edge.rootTop) le_rfl ((hin _).2 rfl)
      (fun f hf => (hin f).1 hf) rfl hne (fun G => if ({a, b} : Finset X) ∈ G then (1 : ℝ) else 0)
    rw [hψ, key]
    refine mul_le_mul_of_nonneg_right (le_sum_kingman_top hd hX hw h₃) (by positivity)
  have hconst := stageMass_const (N := networkNk k a b c d) (θ := metricNk k ε 0) (ρ := 0) hN hθ.isNormalized le_rfl hinj
    (downClosed_stg (2 ^ (k + 1) - 2)) (root_notMem_stg (by omega)) c₀
  have hstg : (univ.erase (networkNk k a b c d).root) = stg k (2 ^ (k + 1) - 2 + 1) := by
    rw [show 2 ^ (k + 1) - 2 + 1 = 2 ^ (k + 1) - 1 by omega]
    exact stg_top.symm
  have htop := stageMass_top (N := networkNk k a b c d) (θ := metricNk k ε 0) (ρ := 0) hN (injNk k a b c d)
    (fun top => if ({a, b} : Finset X) ∈ top .rootTop then 1 else 0)
  rw [hstg] at htop
  rw [hconst, htop] at hstep
  have hZ0 : 0 < ((Fintype.card (Finset (Finset X)) : ℝ) ^ Fintype.card (Edge k)) ^ 2 := by
    have : (0 : ℝ) < Fintype.card (Finset (Finset X)) := by exact_mod_cast Fintype.card_pos
    positivity
  have hmass : c₀ ≤ fullMass (networkNk k a b c d) (metricNk k ε 0) 0 (injNk k a b c d)
      (fun top => if ({a, b} : Finset X) ∈ top .rootTop then 1 else 0) := by
    refine le_of_mul_le_mul_left ?_ hZ0
    rw [mul_comm]
    exact hstep
  refine hmass.trans ?_
  have htaxa : (quartetTree a b c d hd).taxa = univ := eq_univ_of_card _ ((quartetTree a b c d hd).card_taxa.trans hX.symm)
  change _ ≤ nmscCF _ _ 0 _
  rw [nmscCF_eq_cherryMass_weak hN hθ.isNormalized le_rfl, htaxa, cherryMass_eq_fullMass]
  refine fullMass_mono hθ hρ fun bot top hw => ?_
  have hgood := (good_arriving_root hN hinj hw).1
  split_ifs with hE
  · -- the cluster `{a, b}` is in every gene tree
    have hmemF : ({a, b} : Finset X) ∈ arriving (networkNk k a b c d) (taxaInj (networkNk k a b c d) univ) top (networkNk k a b c d).root := by
      have := arriving_root (a := a) (b := b) (c := c) (d := d) top
      rw [show (networkNk k a b c d).root = Vertex.root from rfl]
      change _ ∈ arriving (networkNk k a b c d) (injNk k a b c d) top Vertex.root
      rw [this]
      exact mem_union_right _ hE
    have hval : absVal (quartetTree a b c d hd) (arriving (networkNk k a b c d) (taxaInj (networkNk k a b c d) univ) top (networkNk k a b c d).root) = 1 := by
      unfold absVal
      rw [← kingmanAbsorption_sum hgood.1]
      refine sum_congr rfl fun H _ => ?_
      by_cases hA : kingmanAbsorption (arriving (networkNk k a b c d) (injNk k a b c d) top (networkNk k a b c d).root) H = 0
      · simp only [injNk] at hA
        simp [hA]
      · refine ite_eq_left ⟨{a, b}, ?_, (kingmanAbsorption_support_good hgood hA).2.1 hmemF⟩
        simp [quartetTree]
    exact hval.ge
  · exact absVal_nonneg _ hgood.1

end Boundary

/-! ### The segment -/

section Segment

variable (hd : ({a, b, c, d} : Finset X).card = 4) (hX : Fintype.card X = 4)

/-- `CF_{ab|cd}` is continuous in `M`. -/
theorem continuous_cf_first_M (k : ℕ) (a b c d : X) (h : ({a, b, c, d} : Finset X).card = 4) (ε : ℝ) :
    Continuous fun M => (cfTriple (networkNk k a b c d) (metricNk k ε M) a b c d h).1 := by
  refine continuousOn_univ.1 (AnalyticOnNhd.continuousOn (analyticOnNhd_nmscCF (networkNk k a b c d)
    (θ := fun M : ℝ => metricNk k ε M) 0 (fun e => ?_) (fun e => analyticOnNhd_const) _))
  have haff : ∀ u v : ℝ, AnalyticOnNhd ℝ (fun x : ℝ => u + v * x) Set.univ := fun u v =>
    analyticOnNhd_const.add (analyticOnNhd_const.mul analyticOnNhd_id)
  cases e with
  | rootTaxon =>
    refine (haff (2 + (k + 1) * ε) (2 ^ k - 1)).congr isOpen_univ fun x _ => ?_
    simp only [metricNk]
  | rootTop => exact analyticOnNhd_const
  | step t => exact analyticOnNhd_id
  | bottomTaxon => exact analyticOnNhd_const
  | tree m =>
    simp only [metricNk]
    split_ifs
    · exact analyticOnNhd_const
    · exact haff ε _
  | stem => exact analyticOnNhd_const
  | cherryLeft => exact analyticOnNhd_const
  | cherryRight => exact analyticOnNhd_const

/-- **"The `CF` varies over a line segment"**: as `M` varies at fixed `k`, `ε`, the first entries form an interval, and by Proposition 1 the `CF`s are on the line `(v, (1 - v)/2, (1 - v)/2)`. -/
theorem isPreconnected_cf_first (k : ℕ) (a b c d : X) (h : ({a, b, c, d} : Finset X).card = 4) (ε : ℝ) :
    IsPreconnected ((fun M => (cfTriple (networkNk k a b c d) (metricNk k ε M) a b c d h).1) '' Set.Ioi 0) :=
  isPreconnected_Ioi.image _ (continuous_cf_first_M k a b c d h ε).continuousOn

include hd hX in
/-- A `CF` of `𝒩(k)⁺` with first entry `v` is on the line. -/
theorem cfTriple_eq_of_first {ε M : ℝ} (hε : 0 < ε) (hM : 0 < M) {v : ℝ}
    (hv : (cfTriple (networkNk k a b c d) (metricNk k ε M) a b c d hd).1 = v) :
    cfTriple (networkNk k a b c d) (metricNk k ε M) a b c d hd = (v, (1 - v) / 2, (1 - v) / 2) := by
  obtain ⟨p', q', heq, -, -, -, -, hsum⟩ := proposition1 (isBinaryNetwork_networkNk k hd hX) hX hd
    (hasQuartetTopology_networkNk k hd hX) (isMetric_metricNk hd hX hε hM)
  have hp' : p' = v := by
    rw [heq] at hv
    exact hv
  have hq' : q' = (1 - v) / 2 := by
    rw [hp'] at hsum
    linarith
  rw [heq, hp', hq']

include hd hX in
/-- **The segment of `ε`**: every value between `1 - α` and `(1 - exp (-3)) / 3` is the first entry of a `CF` of `𝒩(k)⁺` at `ε`, for some `M > 0`. -/
theorem exists_M_of_value {ε : ℝ} (hε : 0 < ε) {v : ℝ} (h1 : 1 - alpha k ε < v) (h2 : v < (1 - Real.exp (-3)) / 3) :
    ∃ M : ℝ, 0 < M ∧ cfTriple (networkNk k a b c d) (metricNk k ε M) a b c d hd = (v, (1 - v) / 2, (1 - v) / 2) := by
  obtain ⟨M₁, hM₁, hM₁pos⟩ := ((Real.tendsto_exp_neg_atTop_nhds_zero.eventually (gt_mem_nhds (sub_pos.2 h1))).and
    (eventually_gt_atTop 0)).exists
  have hF₁ : (cfTriple (networkNk k a b c d) (metricNk k ε M₁) a b c d hd).1 ≤ v := by
    have := cf_first_le k hd hX hε hM₁pos
    linarith
  have hF₀ := cf_first_ge (k := k) hd hX hε
  obtain ⟨M, ⟨hM0, -⟩, hFM⟩ := intermediate_value_Icc' hM₁pos.le (continuous_cf_first_M k a b c d hd ε).continuousOn ⟨hF₁, h2.le.trans hF₀⟩
  have hFM' : (cfTriple (networkNk k a b c d) (metricNk k ε M) a b c d hd).1 = v := hFM
  have hMpos : 0 < M := by
    refine lt_of_le_of_ne hM0 ?_
    rintro rfl
    rw [hFM'] at hF₀
    linarith
  exact ⟨M, hMpos, cfTriple_eq_of_first hd hX hε hMpos hFM'⟩

end Segment

omit [Fintype X] [DecidableEq X] in
theorem continuous_alpha (k : ℕ) : Continuous fun ε => alpha k ε := by
  unfold alpha
  fun_prop

omit [Fintype X] [DecidableEq X] in
theorem alpha_two_le {k : ℕ} (hk : 2 ≤ k) (ε : ℝ) : alpha 2 ε ≤ alpha k ε :=
  sum_le_sum_of_subset_of_nonneg (Finset.Icc_subset_Icc_right hk) fun _ _ _ => by positivity

/-- **"Thus the distance between blobs cannot be identified in this 4-taxon case"** (`a:claim:blob-distance`, in Section 5). On one topological network `𝒩(k)⁺`, for `k ≥ 2`, whose tree of blobs has the topology `ab|cd`, the edge between the blobs being the stem of
length `ε`: for `ε₀` small and for all `ε′` near `ε₀`, "this segment overlaps a similarly constructed segment of `CF`s": a nondegenerate segment `[q₁, q₂]` of first entries arises at `ε₀` and at `ε′`. Here `M` varies; see the module docstring on the
quantifiers. -/
theorem blobDistance_not_identifiable {a b c d : X} (h : ({a, b, c, d} : Finset X).card = 4) (hX : Fintype.card X = 4) :
    ∃ ε₁ : ℝ, 0 < ε₁ ∧ ∀ k, 2 ≤ k → ∀ ε₀ : ℝ, 0 < ε₀ → ε₀ < ε₁ →
      (Trd (isBinaryNetwork_networkNk k h hX) (nontrivial_of_card_four hX)).HasQuartetTopology a b c d ∧
      ∃ q₁ q₂ : ℝ, q₁ < q₂ ∧ ∀ᶠ ε' in 𝓝 ε₀, 0 < ε' ∧ ∀ v ∈ Set.Icc q₁ q₂, ∃ M M' : ℝ, 0 < M ∧ 0 < M' ∧
        cfTriple (networkNk k a b c d) (metricNk k ε₀ M) a b c d h = (v, (1 - v) / 2, (1 - v) / 2) ∧
        cfTriple (networkNk k a b c d) (metricNk k ε' M') a b c d h = (v, (1 - v) / 2, (1 - v) / 2) := by
  set c₀ : ℝ := (1 - Real.exp (-3)) / 3 with hc₀
  -- small `ε`: `1 - α` is below `(1 - exp (-3)) / 3`
  have hexp : Real.exp (-3) < 1 / 4 := by
    have h4 : (3 : ℝ) + 1 < Real.exp 3 := Real.add_one_lt_exp (by norm_num)
    rw [Real.exp_neg, inv_eq_one_div]
    exact one_div_lt_one_div_of_lt (by norm_num) (by linarith)
  have hval : (1 : ℝ) - c₀ < alpha 2 0 := by
    have : alpha 2 0 = 3 / 4 := by
      unfold alpha
      rw [show Finset.Icc 1 2 = {1, 2} from rfl, Finset.sum_pair (by norm_num)]
      simp only [neg_zero, Real.exp_zero]
      norm_num
    rw [this, hc₀]
    linarith
  obtain ⟨ε₁, hε₁, hsmall⟩ := Metric.eventually_nhds_iff.1 ((continuous_alpha 2).continuousAt.eventually (lt_mem_nhds hval))
  refine ⟨ε₁, hε₁, fun k hk ε₀ hε₀ hlt => ⟨hasQuartetTopology_networkNk k h hX, ?_⟩⟩
  have hgap : 1 - alpha k ε₀ < c₀ := by
    have h1 : (1 : ℝ) - c₀ < alpha 2 ε₀ := hsmall (by
      rw [Real.dist_eq, sub_zero, abs_of_pos hε₀]
      exact hlt)
    have h2 := alpha_two_le hk ε₀
    linarith
  set u : ℝ := 1 - alpha k ε₀ with hu
  refine ⟨u + (c₀ - u) / 3, u + 2 * (c₀ - u) / 3, by linarith, ?_⟩
  have hnear : ∀ᶠ ε' in 𝓝 ε₀, 1 - alpha k ε' < u + (c₀ - u) / 3 :=
    ((continuous_const.sub (continuous_alpha k)).continuousAt (x := ε₀)).eventually (gt_mem_nhds (by
      change 1 - alpha k ε₀ < _
      linarith))
  filter_upwards [hnear, lt_mem_nhds hε₀] with ε' hε'near hε'pos
  refine ⟨hε'pos, fun v hv => ?_⟩
  obtain ⟨M, hM, heq⟩ := exists_M_of_value (k := k) h hX hε₀ (v := v) (by linarith [hv.1]) (by linarith [hv.2])
  obtain ⟨M', hM', heq'⟩ := exists_M_of_value (k := k) h hX hε'pos (v := v) (by linarith [hv.1]) (by linarith [hv.2])
  exact ⟨M, M', hM, hM', heq, heq'⟩

end AllmanEtAl2023.InPassing
