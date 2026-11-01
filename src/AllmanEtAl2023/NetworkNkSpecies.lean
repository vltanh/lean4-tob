module

public import AllmanEtAl2023.NetworkNkCF

/-!
# Allman, Baños, Mitchell, Rhodes 2023: `CF₁` from species trees, in the proof of Proposition 1

"To compute `CF₁`, note that the conditioning ensures that all coalescent events that can occur will have the same probability that they would if they instead occurred on a species tree with topology `(((c, a), b), d)` or a species tree
with topology `(((c, b), a), d)`, with each of these trees having equal probability. Moreover on these trees the length of the edge ancestral only to the cherry is `mM` for some `m ∈ {1, 2, …, 2^k − 1}`."

The two lineages of `a`, `b` have reached two arcs `outTree (2^k + i)`, `outTree (2^k + j)` of the inverted subtree, `i < j`, at height `1 + (k + 1)ε` (`ArrAt`). Above that:

* on the path they meet the lineage of `c`, in a schedule `B`, which `pv` runs: along the path, the coalescent runs for the length of each arc. This is the identity of the kernel above the stage, `xi_step` at one node, and `fullMass_event` on the whole path.
* by the semigroup property of Kingman's coalescent, that is a coalescent for the time `(j - i) M` on the lower lineage and `c`, then one on the three lineages, then the population above the root (`pv_top`).
* that is the concordance factor on the species tree `𝒩(0)⁺` on the taxa `c, x, y, d`, whose stem has length `(j - i) M` (`nmscCF_treeMetric`). The two are put together in `fullMass_arrAt`.
-/

@[expose] public noncomputable section

open Phylogenetics Phylogenetics.RootedNetwork Phylogenetics.NMSC Finset AllmanEtAl2023.KernelBounds
open scoped Classical

namespace AllmanEtAl2023.NetworkNk

variable {X : Type*} [Fintype X] [DecidableEq X] {k : ℕ} {a b c d : X}

/-! ### Forests with one lineage, and Kingman's coalescent on composites -/

omit [Fintype X] in
/-- A forest on one lineage. -/
theorem eq_singleton_of_lineages {F : Finset (Finset X)} (hF : IsForest F) {x : X} (h : lineages F = {x}) : F = {{x}} := by
  ext A
  simp only [mem_singleton]
  constructor
  · intro hA
    obtain ⟨y, hy⟩ := hF.1 A hA
    have hsub : A ⊆ {x} := h ▸ subset_lineages hA
    have hyx : y = x := mem_singleton.1 (hsub hy)
    subst hyx
    exact Subset.antisymm hsub (singleton_subset_iff.2 hy)
  · rintro rfl
    have hx : x ∈ lineages F := by
      rw [h]
      exact mem_singleton_self x
    obtain ⟨A, hA, hxA⟩ := mem_lineages.1 hx
    have hsub : A ⊆ {x} := h ▸ subset_lineages hA
    have : A = {x} := Subset.antisymm hsub (singleton_subset_iff.2 hxA)
    exact this ▸ hA

omit [Fintype X] in
/-- A forest on no lineage. -/
theorem eq_empty_of_lineages {F : Finset (Finset X)} (hF : IsForest F) (h : lineages F = ∅) : F = ∅ := by
  refine eq_empty_of_forall_notMem fun A hA => ?_
  obtain ⟨y, hy⟩ := hF.1 A hA
  have : y ∈ lineages F := mem_lineages.2 ⟨A, hA, hy⟩
  rw [h] at this
  exact absurd this (notMem_empty y)

/-- The semigroup property of Kingman's coalescent. -/
theorem sum_kingman_comp (s t : ℝ) (F : Finset (Finset X)) (g : Finset (Finset X) → ℝ) :
    ∑ G, kingmanTransition s F G * ∑ H, kingmanTransition t G H * g H = ∑ H, kingmanTransition (s + t) F H * g H := by
  rw [kingmanTransition_add]
  simp only [Matrix.mul_apply, mul_sum, sum_mul]
  rw [sum_comm]
  refine sum_congr rfl fun H _ => sum_congr rfl fun G _ => ?_
  ring

theorem sum_kingman_zero (F : Finset (Finset X)) (g : Finset (Finset X) → ℝ) :
    ∑ G, kingmanTransition 0 F G * g G = g F := by
  rw [kingmanTransition_zero]
  simp [Matrix.one_apply]

/-- One lineage doesn't change along an arc. -/
theorem sum_kingman_singleton (t : ℝ) (x : X) (g : Finset (Finset X) → ℝ) :
    ∑ G, kingmanTransition t ({{x}} : Finset (Finset X)) G * g G = g {{x}} := by
  have hf : IsForest ({{x}} : Finset (Finset X)) := by
    refine ⟨fun A hA => ?_, fun A hA B hB => ?_⟩
    · rw [mem_singleton.1 hA]
      exact singleton_nonempty x
    · rw [mem_singleton.1 hA, mem_singleton.1 hB]
      exact Or.inl (Subset.refl _)
  have hr : #(roots ({{x}} : Finset (Finset X))) ≤ 1 :=
    (card_le_card (roots_subset _)).trans (by simp)
  simp only [kingmanTransition_of_card_roots_le_one hf hr]
  simp

/-! ### The arcs at a 'leaf', and at the root -/

omit [Fintype X] [DecidableEq X] in
theorem source_eq_root_iff (e : Edge k) : (networkNk k a b c d).graph.source e = .root ↔ e = .rootTaxon ∨ e = .rootTop := by
  cases e <;> simp [source_step, source_bottomTaxon, source_tree, source_stem, heapNode]

omit [Fintype X] [DecidableEq X] in
theorem outTree_ne_of_lt {m m' : ℕ} (hm : 2 ≤ m) (hm' : 2 ≤ m') (hlt : m < 2 ^ (k + 1)) (hlt' : m' < 2 ^ (k + 1)) (hne : m ≠ m') :
    (outTree m : Edge k) ≠ outTree m' := by
  rw [outTree_of_two_le hm hlt, outTree_of_two_le hm' hlt']
  simp only [ne_eq, Edge.tree.injEq, Fin.mk.injEq]
  omega

/-- A node on the path: the forest arriving there is the union of those at the top of the two arcs leaving it. -/
theorem arriving_path {m : ℕ} (h₁ : 1 ≤ m) (h₂ : 2 ^ k ≤ m) (h₃ : m < 2 ^ (k + 1)) (top : Edge k → Finset (Finset X)) :
    arriving (networkNk k a b c d) (injNk k a b c d) top (heapNode m h₁ h₃) = top (outTree m) ∪ top (outPath m) := by
  unfold arriving
  have h4 : injNk k a b c d (heapNode m h₁ h₃) = ∅ := by
    refine eq_empty_of_forall_notMem fun A hA => ?_
    obtain ⟨x, hx, -⟩ := mem_image.1 hA
    have := (mem_filter.1 hx).2.2
    simp [networkNk] at this
  have h5 : (univ.filter fun e => (networkNk k a b c d).graph.source e = heapNode m h₁ h₃) = {outTree m, outPath m} := by
    ext e
    simp only [mem_filter, mem_univ, true_and, mem_insert, mem_singleton]
    exact source_eq_path_iff h₁ h₂ h₃ e
  rw [h4, h5, biUnion_insert, singleton_biUnion, empty_union]

/-- The forest arriving at the root. -/
theorem arriving_root (top : Edge k → Finset (Finset X)) :
    arriving (networkNk k a b c d) (injNk k a b c d) top .root = top .rootTaxon ∪ top .rootTop := by
  unfold arriving
  have h4 : injNk k a b c d .root = ∅ := by
    refine eq_empty_of_forall_notMem fun A hA => ?_
    obtain ⟨x, hx, -⟩ := mem_image.1 hA
    have := (mem_filter.1 hx).2.2
    simp [networkNk] at this
  have h5 : (univ.filter fun e => (networkNk k a b c d).graph.source e = .root) = {Edge.rootTaxon, Edge.rootTop} := by
    ext e
    simp only [mem_filter, mem_univ, true_and, mem_insert, mem_singleton]
    exact source_eq_root_iff e
  rw [h4, h5, biUnion_insert, singleton_biUnion, empty_union]

variable (hd : ({a, b, c, d} : Finset X).card = 4)
include hd

/-- The lineage of `d` is alone on its arc. -/
theorem top_rootTaxon {n : ℕ} {bot top : Edge k → Finset (Finset X)}
    (hF : Frontier (networkNk k a b c d) (injNk k a b c d) (stg k n) bot top) : top .rootTaxon = {{d}} := by
  obtain ⟨hab, hac, had, hbc, hbd, hcd⟩ := ne_of_card_four hd
  have hfr : tgtRk (Edge.rootTaxon : Edge k) ≤ n + 1 := by simp [tgtRk]
  refine eq_singleton_of_lineages (hF.good_top _ (by rw [mem_stg, rk_target]; exact hfr)).1 ?_
  ext x
  simp only [mem_singleton]
  constructor
  · intro hx
    exact (Vertex.taxon.inj (eq_of_taxon_reaches (reaches_of_mem hF hfr hx))).symm ▸ rfl
  · rintro rfl
    obtain ⟨f, hf, hx⟩ := exists_fr hF x
    rcases eq_of_reaches_taxon_d had hbd hcd (reaches_of_mem hF hf.1 hx) with h | h
    · rcases (target_eq_taxon_iff f x).1 h with ⟨-, h'⟩ | ⟨-, h'⟩ | ⟨-, h'⟩ | ⟨rfl, -⟩
      · exact absurd h' had
      · exact absurd h' hbd
      · exact absurd h' hcd
      · exact hx
    · exact absurd h (target_ne_root f)

/-- The lineage of `c` is alone on its arc, below the path. -/
theorem top_bottomTaxon {n : ℕ} (hn : n < 2 ^ k) {bot top : Edge k → Finset (Finset X)}
    (hF : Frontier (networkNk k a b c d) (injNk k a b c d) (stg k n) bot top) : top .bottomTaxon = {{c}} := by
  obtain ⟨hab, hac, had, hbc, hbd, hcd⟩ := ne_of_card_four hd
  have hfr : tgtRk (Edge.bottomTaxon : Edge k) ≤ n + 1 := by simp [tgtRk]
  have h2k := two_pow_succ_eq k
  refine eq_singleton_of_lineages (hF.good_top _ (by rw [mem_stg, rk_target]; exact hfr)).1 ?_
  ext x
  simp only [mem_singleton]
  constructor
  · intro hx
    exact (Vertex.taxon.inj (eq_of_taxon_reaches (reaches_of_mem hF hfr hx))).symm ▸ rfl
  · rintro rfl
    obtain ⟨f, hf, hx⟩ := exists_fr hF x
    have hr := reaches_of_mem hF hf.1 hx
    have hlow : IsLow a b ((networkNk k a b x d).graph.target f) → False := fun hl => by
      rcases IsLow.of_reaches (c := x) (d := d) hr hl with h | h
      · exact hac h.symm
      · exact hbc h.symm
    obtain ⟨hf₁, hf₂⟩ := hf
    cases f with
    | rootTaxon => exact absurd (Vertex.taxon.inj (eq_of_taxon_reaches hr)) hcd
    | rootTop =>
      simp only [tgtRk] at hf₁
      omega
    | step t =>
      simp only [tgtRk] at hf₁
      omega
    | bottomTaxon => exact hx
    | tree m => exact (hlow (isLow_target_tree m)).elim
    | stem => exact (hlow trivial).elim
    | cherryLeft => exact absurd (Vertex.taxon.inj (eq_of_taxon_reaches hr)) hac.symm
    | cherryRight => exact absurd (Vertex.taxon.inj (eq_of_taxon_reaches hr)) hbc.symm

/-- The lineage of `c` arrives at the 'leaf' that a stage reaches. -/
theorem exists_out_c {n : ℕ} (hn₁ : 2 ^ k ≤ n + 1) (h₃ : n + 1 < 2 ^ (k + 1)) {bot top : Edge k → Finset (Finset X)}
    (hF : Frontier (networkNk k a b c d) (injNk k a b c d) (stg k n) bot top) :
    ∃ g : Edge k, (networkNk k a b c d).graph.source g = heapNode (n + 1) (by omega) h₃ ∧ c ∈ lineages (top g) := by
  obtain ⟨hab, hac, had, hbc, hbd, hcd⟩ := ne_of_card_four hd
  obtain ⟨f, hf, hx⟩ := exists_fr hF c
  have hr := reaches_of_mem hF hf.1 hx
  have hlow : IsLow a b ((networkNk k a b c d).graph.target f) → False := fun hl => by
    rcases IsLow.of_reaches hr hl with h | h
    · exact hac h.symm
    · exact hbc h.symm
  obtain ⟨hf₁, hf₂⟩ := hf
  cases f with
  | rootTaxon => exact absurd (Vertex.taxon.inj (eq_of_taxon_reaches hr)) hcd
  | rootTop =>
    simp only [tgtRk] at hf₁
    omega
  | step t =>
    simp only [tgtRk, srcRk] at hf₁ hf₂
    refine ⟨.step t, ?_, hx⟩
    rw [source_step, heapNode_inj]
    omega
  | bottomTaxon =>
    simp only [srcRk] at hf₂
    refine ⟨.bottomTaxon, ?_, hx⟩
    rw [source_bottomTaxon, heapNode_inj]
    omega
  | tree m => exact (hlow (isLow_target_tree m)).elim
  | stem => exact (hlow trivial).elim
  | cherryLeft => exact absurd (Vertex.taxon.inj (eq_of_taxon_reaches hr)) hac.symm
  | cherryRight => exact absurd (Vertex.taxon.inj (eq_of_taxon_reaches hr)) hbc.symm

omit hd

/-! ### The species trees -/

/-- **The parameters of a species tree** `𝒩(0)⁺`: the stem, the edge ancestral only to the cherry, has length `L₁`, and the edge above it length `L₂`. The pendant edges have length 1. -/
def treeMetric (L₁ L₂ : ℝ) : MetricData (Edge 0) where
  length
    | .stem => L₁
    | .rootTop => L₂
    | _ => 1
  inheritance _ := 1

variable (hd : ({a, b, c, d} : Finset X).card = 4) (hX : Fintype.card X = 4)
include hd hX

/-- The parameters of a species tree are valid. -/
theorem isMetric_treeMetric {L₁ L₂ : ℝ} (h₁ : 0 < L₁) (h₂ : 0 < L₂) : (networkNk 0 a b c d).IsMetric (treeMetric L₁ L₂) := by
  have hm := isMetric_metricNk (k := 0) (ε := 1) (M := 1) hd hX one_pos one_pos
  have hinh : ∀ e : Edge 0, (treeMetric L₁ L₂).inheritance e = (metricNk 0 1 1).inheritance e := by
    intro e
    cases e with
    | tree m => exact m.elim0
    | _ => rfl
  refine ⟨fun e _ => ?_, fun e _ => ?_, fun e he => ?_, fun e _ => ?_, fun v hv => ?_⟩
  · cases e with
    | stem => exact h₁
    | rootTop => exact h₂
    | _ => exact one_pos
  · cases e with
    | stem => exact h₁.le
    | rootTop => exact h₂.le
    | _ => exact zero_le_one
  · rfl
  · exact one_pos
  · rw [← hm.2.2.2.2 v hv]
    exact sum_congr rfl fun e _ => by rw [hinh]

/-- **The concordance factor on a species tree**: the lineages of `a` and `b` coalesce for the time `L₁`, then that of `c` joins them for the time `L₂`, and that of `d` above the root. -/
theorem nmscCF_treeMetric {L₁ L₂ : ℝ} (h₁ : 0 < L₁) (h₂ : 0 < L₂) (r : QuartetTree X) :
    nmscCF (networkNk 0 a b c d) (treeMetric L₁ L₂) 0 r =
      ∑ G, kingmanTransition L₁ ({{a}, {b}} : Finset (Finset X)) G *
        ∑ H, kingmanTransition L₂ (G ∪ {{c}}) H * absVal r (H ∪ {{d}}) := by
  obtain ⟨hab, hac, had, hbc, hbd, hcd⟩ := ne_of_card_four hd
  have hN := isPhylogenetic_networkNk (k := 0) hd hX
  have hmetric := isMetric_treeMetric (a := a) (b := b) (c := c) (d := d) hd hX h₁ h₂
  have hθ := hmetric.isWeakMetric
  have hinj := validInj_injNk (k := 0) (a := a) (b := b) (c := c) (d := d)
  have htaxa : r.taxa = univ := eq_univ_of_card _ (r.card_taxa.trans hX.symm)
  rw [nmscCF_eq_cherryMass_weak hN hθ.isNormalized le_rfl, htaxa, cherryMass_eq_fullMass]
  set Z : ℝ := ((Fintype.card (Finset (Finset X)) : ℝ) ^ Fintype.card (Edge 0)) ^ 2 with hZ
  have hZ0 : Z ≠ 0 := by
    have : (0 : ℝ) < Fintype.card (Finset (Finset X)) := by exact_mod_cast Fintype.card_pos
    positivity
  set W : ℝ := ∑ G, kingmanTransition L₁ ({{a}, {b}} : Finset (Finset X)) G *
    ∑ H, kingmanTransition L₂ (G ∪ {{c}}) H * absVal r (H ∪ {{d}}) with hW
  -- from the taxa to the cherry
  have hstep₀ : stageMass (networkNk 0 a b c d) (treeMetric L₁ L₂) 0 (injNk 0 a b c d) (stgT 0) (fun _ => W) =
      stageMass (networkNk 0 a b c d) (treeMetric L₁ L₂) 0 (injNk 0 a b c d) (stg 0 0)
        (fun top => ∑ H, kingmanTransition L₂ (top .stem ∪ {{c}}) H * absVal r (H ∪ {{d}})) := by
    rw [← insert_cherry_stgT]
    refine stageMass_eq_insert downClosed_stgT (by simp [rk]) (fun e he => ?_) fun bot top hw => ?_
    · have h1 := rk_target_lt_rk_source (a := a) (b := b) (c := c) (d := d) e
      rw [he] at h1
      have h2 : rk (Vertex.cherry : Vertex 0 X) = 1 := rfl
      rw [mem_stgT]
      omega
    · rw [arriving_cherry hd hX hw]
      have hmem : (Edge.stem : Edge 0) ∈ arcsInto (networkNk 0 a b c d) Vertex.cherry := mem_arcsInto.2 rfl
      have hψ : (fun t => ∑ H, kingmanTransition L₂ (overwrite (arcsInto (networkNk 0 a b c d) Vertex.cherry) top t .stem ∪ {{c}}) H * absVal r (H ∪ {{d}})) =
          fun t => (fun G => ∑ H, kingmanTransition L₂ (G ∪ {{c}}) H * absVal r (H ∪ {{d}})) (t .stem) := by
        funext t
        rw [overwrite_of_mem hmem]
      have key := vertexKernel_one_arc (N := networkNk 0 a b c d) (θ := treeMetric L₁ L₂) (ρ := 0) (v := Vertex.cherry) (e := Edge.stem)
        (F := {{a}, {b}}) le_rfl rfl eq_stem_of_target_eq_cherry rfl ⟨{a}, by simp⟩ (fun G => ∑ H, kingmanTransition L₂ (G ∪ {{c}}) H * absVal r (H ∪ {{d}}))
      rw [hψ, key]
      rfl
  -- from the cherry to the node of the path
  have h₃ : 0 + 1 < 2 ^ (0 + 1) := by norm_num
  have hstep₁ : stageMass (networkNk 0 a b c d) (treeMetric L₁ L₂) 0 (injNk 0 a b c d) (stg 0 0)
        (fun top => ∑ H, kingmanTransition L₂ (top .stem ∪ {{c}}) H * absVal r (H ∪ {{d}})) =
      stageMass (networkNk 0 a b c d) (treeMetric L₁ L₂) 0 (injNk 0 a b c d) (stg 0 1)
        (fun top => absVal r (top .rootTop ∪ {{d}})) := by
    rw [← insert_heapNode_stg h₃]
    refine stageMass_eq_insert (downClosed_stg 0) (heapNode_notMem_stg h₃) (target_mem_stg_of_source_eq h₃) fun bot top hw => ?_
    have hF := frontier_of_prod_ne_zero hN hinj (downClosed_stg 0) hw
    have hin : ∀ f : Edge 0, (networkNk 0 a b c d).graph.target f = heapNode (0 + 1) (by omega) h₃ ↔ f = pathIn (0 + 1) :=
      target_eq_path_iff (by omega) (by simp) h₃
    have hpath : (pathIn (0 + 1) : Edge 0) = .rootTop := by
      simp [pathIn]
    rw [hpath] at hin
    have harr : arriving (networkNk 0 a b c d) (injNk 0 a b c d) top (heapNode (0 + 1) (by omega) h₃) = top .stem ∪ {{c}} := by
      rw [arriving_path (by omega) (by simp) h₃, ← top_bottomTaxon hd (by simp) hF]
      rw [show (outTree (0 + 1) : Edge 0) = .stem from outTree_one]
      rw [show (outPath (0 + 1) : Edge 0) = .bottomTaxon from outPath_self]
    have hmem : (Edge.rootTop : Edge 0) ∈ arcsInto (networkNk 0 a b c d) (heapNode (0 + 1) (by omega) h₃) := mem_arcsInto.2 ((hin _).2 rfl)
    have hψ : (fun t => absVal r (overwrite (arcsInto (networkNk 0 a b c d) (heapNode (0 + 1) (by omega) h₃)) top t .rootTop ∪ {{d}})) =
        fun t => (fun G => absVal r (G ∪ {{d}})) (t .rootTop) := by
      funext t
      rw [overwrite_of_mem hmem]
    have key := vertexKernel_one_arc (N := networkNk 0 a b c d) (θ := treeMetric L₁ L₂) (ρ := 0) (e := Edge.rootTop) (F := top .stem ∪ {{c}})
      le_rfl ((hin _).2 rfl) (fun f hf => (hin f).1 hf) rfl ⟨{c}, by simp⟩ (fun G => absVal r (G ∪ {{d}}))
    rw [harr, hψ, key]
    rfl
  -- at the root
  have hend : stageMass (networkNk 0 a b c d) (treeMetric L₁ L₂) 0 (injNk 0 a b c d) (stg 0 1)
        (fun top => absVal r (top .rootTop ∪ {{d}})) =
      stageMass (networkNk 0 a b c d) (treeMetric L₁ L₂) 0 (injNk 0 a b c d) (stg 0 1)
        (fun top => absVal r (arriving (networkNk 0 a b c d) (injNk 0 a b c d) top .root)) := by
    refine stageMass_congr fun bot top hw => ?_
    have hF := frontier_of_prod_ne_zero hN hinj (downClosed_stg 1) hw
    rw [arriving_root, top_rootTaxon hd hF, union_comm]
  have htop := stageMass_top (N := networkNk 0 a b c d) (θ := treeMetric L₁ L₂) (ρ := 0) hN (injNk 0 a b c d)
    (fun top => absVal r (arriving (networkNk 0 a b c d) (injNk 0 a b c d) top .root))
  have hstg : (univ.erase (networkNk 0 a b c d).root) = stg 0 1 := stg_top.symm
  rw [hstg, ← hend, ← hstep₁, ← hstep₀, stageMass_const hN hθ.isNormalized le_rfl hinj downClosed_stgT root_notMem_stgT] at htop
  exact mul_left_cancel₀ hZ0 (htop.symm.trans (mul_comm _ _))

omit hd hX

/-! ### The kernel above the stage -/

/-- The chain up the path: with `s` nodes left, a forest `F` on the path takes the arrivals `B (s - 1)` at the next node, and goes along its arc, of length `1` at the top of the path and `M` below it. Then `R` of the forest at the top. -/
def pv (B : ℕ → Finset (Finset X)) (R : Finset (Finset X) → ℝ) (M : ℝ) : ℕ → Finset (Finset X) → ℝ
  | 0, F => R F
  | s + 1, F => ∑ G, kingmanTransition (if s = 0 then 1 else M) (F ∪ B s) G * pv B R M s G

/-- The arc of the path that leaves the stage `n`, at the 'leaves' and above: to `c` at the lowest, then a step, and at the top the arc from the root. -/
def frontPath (n : ℕ) : Edge k := if n < 2 ^ k then .bottomTaxon else pathIn n

theorem outPath_eq_frontPath {n : ℕ} (hn₁ : 2 ^ k ≤ n + 1) (h₃ : n + 1 < 2 ^ (k + 1)) : (outPath (n + 1) : Edge k) = frontPath n := by
  have h2k := two_pow_succ_eq k
  rcases Nat.lt_or_ge n (2 ^ k) with h | h
  · obtain h' : n + 1 = 2 ^ k := by omega
    rw [h', outPath_self]
    simp only [frontPath]
    rw [ite_eq_left h]
  · simp only [frontPath]
    rw [ite_eq_right (by omega), outPath_of_lt (by omega) h₃]
    simp only [pathIn]
    rw [dite_eq_left (by omega)]
    simp only [Edge.step.injEq, Fin.mk.injEq]
    omega

theorem frontPath_succ {n : ℕ} (hn₁ : 2 ^ k ≤ n + 1) : (frontPath (n + 1) : Edge k) = pathIn (n + 1) := by
  simp only [frontPath]
  rw [ite_eq_right (by omega)]

theorem frontPath_top : (frontPath (2 ^ (k + 1) - 1) : Edge k) = .rootTop := by
  have h2k := two_pow_succ_eq k
  have h1k := one_le_two_pow_k k
  simp only [frontPath, pathIn]
  rw [ite_eq_right (by omega), dite_eq_right (by omega)]

theorem frontPath_start : (frontPath (2 ^ k - 1) : Edge k) = .bottomTaxon := by
  have h1k := one_le_two_pow_k k
  simp only [frontPath]
  rw [ite_eq_left (by omega)]

/-- The length of an arc of the path. -/
theorem length_pathIn {n : ℕ} {ε M : ℝ} (hn₁ : 2 ^ k ≤ n + 1) (h₃ : n + 1 < 2 ^ (k + 1)) :
    (metricNk k ε M).length (pathIn (n + 1)) = if 2 ^ (k + 1) - 1 - (n + 1) = 0 then 1 else M := by
  have h2k := two_pow_succ_eq k
  simp only [pathIn]
  by_cases h : n + 1 - 2 ^ k < 2 ^ k - 1
  · rw [dite_eq_left h, ite_eq_right (by omega)]
    rfl
  · rw [dite_eq_right h, ite_eq_left (by omega)]
    rfl

/-- The potential above the stage, on the event `E`. -/
def Xi (E : (Edge k → Finset (Finset X)) → Prop) (B : ℕ → Finset (Finset X)) (R : Finset (Finset X) → ℝ) (M : ℝ) (n : ℕ)
    (top : Edge k → Finset (Finset X)) : ℝ :=
  if E top then pv B R M (2 ^ (k + 1) - 1 - n) (top (frontPath n)) else 0

variable (hd : ({a, b, c, d} : Finset X).card = 4) (hX : Fintype.card X = 4) {ε M : ℝ} (hε : 0 < ε) (hM : 0 < M)

include hd hX in
/-- **The kernel above the stage, at one node of the path.** On the event `E`, the arrivals at each node are as in the schedule `B`; the arc of the path takes the rest. -/
theorem xi_step {E : (Edge k → Finset (Finset X)) → Prop} {B : ℕ → Finset (Finset X)} {R : Finset (Finset X) → ℝ}
    (hE : ∀ t t' : Edge k → Finset (Finset X), (∀ f, tgtRk f ≤ 2 ^ k → t f = t' f) → (E t ↔ E t'))
    (hB : ∀ bot top : Edge k → Finset (Finset X),
      ∏ u ∈ stg k (2 ^ k - 1), vertexWeight (networkNk k a b c d) (metricNk k ε M) 0 (injNk k a b c d) u bot top ≠ 0 → E top →
        ∀ n', 2 ^ k ≤ n' → n' < 2 ^ (k + 1) → top (outTree n') = B (2 ^ (k + 1) - 1 - n'))
    {n : ℕ} (hn₁ : 2 ^ k ≤ n + 1) (h₃ : n + 1 < 2 ^ (k + 1)) (bot top : Edge k → Finset (Finset X))
    (hw : ∏ u ∈ stg k n, vertexWeight (networkNk k a b c d) (metricNk k ε M) 0 (injNk k a b c d) u bot top ≠ 0) :
    Xi E B R M n top *
        ((Fintype.card (Finset (Finset X)) : ℝ) ^ #(arcsInto (networkNk k a b c d) (heapNode (n + 1) (by omega) h₃))ᶜ) ^ 2 =
      vertexKernel (networkNk k a b c d) (metricNk k ε M) 0 (heapNode (n + 1) (by omega) h₃)
        (arriving (networkNk k a b c d) (injNk k a b c d) top (heapNode (n + 1) (by omega) h₃)) fun t =>
          Xi E B R M (n + 1) (overwrite (arcsInto (networkNk k a b c d) (heapNode (n + 1) (by omega) h₃)) top t) := by
  have hN := isPhylogenetic_networkNk (k := k) hd hX
  have hinj := validInj_injNk (k := k) (a := a) (b := b) (c := c) (d := d)
  have h1k := one_le_two_pow_k k
  set v : Vertex k X := heapNode (n + 1) (by omega) h₃ with hv
  set S := arcsInto (networkNk k a b c d) v with hS
  have hF := frontier_of_prod_ne_zero hN hinj (downClosed_stg n) hw
  have hE' : ∀ t' : Edge k → Finset (Finset X), E (overwrite S top t') ↔ E top := fun t' =>
    hE _ _ fun f hf => overwrite_of_notMem (fun h => by
      have h1 : tgtRk f = n + 2 := by
        rw [← rk_target (a := a) (b := b) (c := c) (d := d), mem_arcsInto.1 h, hv, rk_heapNode]
      omega) _ _
  by_cases hEt : E top
  · have hs : 2 ^ (k + 1) - 1 - n = (2 ^ (k + 1) - 1 - (n + 1)) + 1 := by omega
    set s' := 2 ^ (k + 1) - 1 - (n + 1) with hs'
    have hprev : ∏ u ∈ stg k (2 ^ k - 1), vertexWeight (networkNk k a b c d) (metricNk k ε M) 0 (injNk k a b c d) u bot top ≠ 0 :=
      prod_ne_zero_iff.2 fun u hu => prod_ne_zero_iff.1 hw u (by
        rw [mem_stg] at hu ⊢
        omega)
    have harr : arriving (networkNk k a b c d) (injNk k a b c d) top v = top (frontPath n) ∪ B s' := by
      rw [hv, arriving_path (by omega) hn₁ h₃, hB bot top hprev hEt (n + 1) hn₁ h₃, outPath_eq_frontPath hn₁ h₃, union_comm]
    have hne : (arriving (networkNk k a b c d) (injNk k a b c d) top v).Nonempty := by
      obtain ⟨g, hg, hcg⟩ := exists_out_c hd hn₁ h₃ hF
      obtain ⟨A, hA, -⟩ := mem_lineages.1 ((mem_lineages_arriving _ top v c).2 (Or.inr ⟨g, hg, hcg⟩))
      exact ⟨A, hA⟩
    have hin : ∀ f : Edge k, (networkNk k a b c d).graph.target f = v ↔ f = pathIn (n + 1) := target_eq_path_iff (by omega) hn₁ h₃
    have hpS : (pathIn (n + 1) : Edge k) ∈ S := mem_arcsInto.2 ((hin _).2 rfl)
    have hγ : (metricNk k ε M).inheritance (pathIn (n + 1)) = 1 := by
      simp only [pathIn]
      split_ifs <;> rfl
    have hψ : (fun t => Xi E B R M (n + 1) (overwrite S top t)) = fun t => (pv B R M s') (t (pathIn (n + 1))) := by
      funext t
      unfold Xi
      rw [ite_eq_left ((hE' t).2 hEt), frontPath_succ hn₁, overwrite_of_mem hpS]
    have key := vertexKernel_one_arc (N := networkNk k a b c d) (θ := metricNk k ε M) (ρ := 0) (e := pathIn (n + 1)) le_rfl ((hin _).2 rfl)
      (fun f hf => (hin f).1 hf) hγ hne (pv B R M s')
    rw [hψ, key, harr, length_pathIn hn₁ h₃]
    unfold Xi
    rw [ite_eq_left hEt, hs]
    rfl
  · have hzero : (fun t => Xi E B R M (n + 1) (overwrite S top t)) = fun _ => 0 := by
      funext t
      unfold Xi
      rw [ite_eq_right (fun h => hEt ((hE' t).1 h))]
    rw [hzero]
    unfold Xi
    rw [ite_eq_right hEt, zero_mul]
    simp [vertexKernel]

include hd hX hε hM in
/-- **The identity of the kernel above the stage**: on the event `E`, the mass of a quartet tree is the probability of `E`, times the chain up the path from the lineage of `c`. -/
theorem fullMass_event {E : (Edge k → Finset (Finset X)) → Prop} {B : ℕ → Finset (Finset X)} (r : QuartetTree X)
    (hE : ∀ t t' : Edge k → Finset (Finset X), (∀ f, tgtRk f ≤ 2 ^ k → t f = t' f) → (E t ↔ E t'))
    (hB : ∀ bot top : Edge k → Finset (Finset X),
      ∏ u ∈ stg k (2 ^ k - 1), vertexWeight (networkNk k a b c d) (metricNk k ε M) 0 (injNk k a b c d) u bot top ≠ 0 → E top →
        ∀ n', 2 ^ k ≤ n' → n' < 2 ^ (k + 1) → top (outTree n') = B (2 ^ (k + 1) - 1 - n')) :
    fullMass (networkNk k a b c d) (metricNk k ε M) 0 (injNk k a b c d)
        (fun top => (if E top then 1 else 0) * absVal r (arriving (networkNk k a b c d) (injNk k a b c d) top .root)) =
      pv B (fun F => absVal r (F ∪ {{d}})) M (2 ^ k) {{c}} *
        fullMass (networkNk k a b c d) (metricNk k ε M) 0 (injNk k a b c d) (fun top => if E top then 1 else 0) := by
  have hN := isPhylogenetic_networkNk (k := k) hd hX
  have hθ : (networkNk k a b c d).IsWeakMetric (metricNk k ε M) := (isMetric_metricNk hd hX hε hM).isWeakMetric
  have hinj := validInj_injNk (k := k) (a := a) (b := b) (c := c) (d := d)
  have h1k := one_le_two_pow_k k
  have h2k := two_pow_succ_eq k
  set R : Finset (Finset X) → ℝ := fun F => absVal r (F ∪ {{d}}) with hR
  -- up the path
  have hchain : ∀ j, 2 ^ k - 1 ≤ j → j < 2 ^ (k + 1) →
      stageMass (networkNk k a b c d) (metricNk k ε M) 0 (injNk k a b c d) (stg k (2 ^ k - 1)) (Xi E B R M (2 ^ k - 1)) =
        stageMass (networkNk k a b c d) (metricNk k ε M) 0 (injNk k a b c d) (stg k j) (Xi E B R M j) := by
    intro j hj
    induction j, hj using Nat.le_induction with
    | base => exact fun _ => rfl
    | succ j hj ih =>
      intro hj'
      refine (ih (by omega)).trans ?_
      rw [← insert_heapNode_stg hj']
      exact stageMass_eq_insert (downClosed_stg j) (heapNode_notMem_stg hj') (target_mem_stg_of_source_eq hj')
        (xi_step hd hX hE hB (by omega) hj')
  have hstg : (univ.erase (networkNk k a b c d).root) = stg k (2 ^ (k + 1) - 1) := stg_top.symm
  have htop₁ := stageMass_top (N := networkNk k a b c d) (θ := metricNk k ε M) (ρ := 0) hN (injNk k a b c d)
    (fun top => (if E top then 1 else 0) * absVal r (arriving (networkNk k a b c d) (injNk k a b c d) top .root))
  have htop₂ := stageMass_top (N := networkNk k a b c d) (θ := metricNk k ε M) (ρ := 0) hN (injNk k a b c d)
    (fun top => if E top then 1 else 0)
  rw [hstg] at htop₁ htop₂
  -- at the root
  have hend : stageMass (networkNk k a b c d) (metricNk k ε M) 0 (injNk k a b c d) (stg k (2 ^ (k + 1) - 1)) (Xi E B R M (2 ^ (k + 1) - 1)) =
      stageMass (networkNk k a b c d) (metricNk k ε M) 0 (injNk k a b c d) (stg k (2 ^ (k + 1) - 1))
        (fun top => (if E top then 1 else 0) * absVal r (arriving (networkNk k a b c d) (injNk k a b c d) top .root)) := by
    refine stageMass_congr fun bot top hw => ?_
    have hF := frontier_of_prod_ne_zero hN hinj (downClosed_stg _) hw
    unfold Xi
    rw [Nat.sub_self, frontPath_top, arriving_root, top_rootTaxon hd hF, union_comm]
    split_ifs
    · rw [one_mul]
      rfl
    · rw [zero_mul]
  -- at the stage
  have hstart : stageMass (networkNk k a b c d) (metricNk k ε M) 0 (injNk k a b c d) (stg k (2 ^ k - 1)) (Xi E B R M (2 ^ k - 1)) =
      pv B R M (2 ^ k) {{c}} * stageMass (networkNk k a b c d) (metricNk k ε M) 0 (injNk k a b c d) (stg k (2 ^ k - 1))
        (fun top => if E top then 1 else 0) := by
    rw [← stageMass_const_mul]
    refine stageMass_congr fun bot top hw => ?_
    have hF := frontier_of_prod_ne_zero hN hinj (downClosed_stg _) hw
    unfold Xi
    rw [frontPath_start, top_bottomTaxon hd (by omega) hF, show 2 ^ (k + 1) - 1 - (2 ^ k - 1) = 2 ^ k by omega]
    split_ifs
    · rw [mul_one]
    · rw [mul_zero]
  have hmarg : stageMass (networkNk k a b c d) (metricNk k ε M) 0 (injNk k a b c d) (stg k (2 ^ (k + 1) - 1))
        (fun top => if E top then 1 else 0) =
      stageMass (networkNk k a b c d) (metricNk k ε M) 0 (injNk k a b c d) (stg k (2 ^ k - 1)) (fun top => if E top then 1 else 0) := by
    refine stageMass_marginal hN hθ.isNormalized le_rfl hinj (downClosed_stg _) (downClosed_stg _) (fun u hu => ?_) (root_notMem_stg (by omega)) _ fun t t' h => ?_
    · rw [mem_stg] at hu ⊢
      omega
    · have : E t ↔ E t' := hE t t' fun f hf => h f (by
        rw [mem_stg, rk_target]
        omega)
      simp only [this]
  have hZ0 : ((Fintype.card (Finset (Finset X)) : ℝ) ^ Fintype.card (Edge k)) ^ 2 ≠ 0 := by
    have : (0 : ℝ) < Fintype.card (Finset (Finset X)) := by exact_mod_cast Fintype.card_pos
    positivity
  refine mul_left_cancel₀ hZ0 ?_
  rw [← htop₁, ← hend, ← hchain _ (by omega) (by omega), hstart, ← hmarg, htop₂]
  ring

/-! ### The chain up the path, on two arrivals -/

section Schedule

variable {R : Finset (Finset X) → ℝ} {x y : X}

/-- The time above an arrival with `s` nodes left. -/
def pathTime (M : ℝ) : ℕ → ℝ
  | 0 => 0
  | s + 1 => (if s = 0 then 1 else M) + pathTime M s

omit [Fintype X] [DecidableEq X] in
theorem pathTime_pos {M : ℝ} (hM : 0 < M) (s : ℕ) : 0 < pathTime M (s + 1) := by
  induction s with
  | zero => simp [pathTime]
  | succ s ih =>
    rw [pathTime, ite_eq_right (by omega)]
    exact add_pos hM ih

/-- The arrivals of two lineages. -/
def arrivals (x y : X) (sx sy : ℕ) (s : ℕ) : Finset (Finset X) :=
  if s = sy then {{y}} else if s = sx then {{x}} else ∅

/-- Above the arrivals, Kingman's coalescent runs for the time left. -/
theorem pv_above {sx sy : ℕ} (hsy : sy < sx) (M : ℝ) (s : ℕ) (hs : s ≤ sy) (F : Finset (Finset X)) :
    pv (arrivals x y sx sy) R M s F = ∑ H, kingmanTransition (pathTime M s) F H * R H := by
  induction s generalizing F with
  | zero =>
    simp only [pv, pathTime]
    rw [sum_kingman_zero]
  | succ s ih =>
    have harr : arrivals x y sx sy s = ∅ := by
      unfold arrivals
      rw [ite_eq_right (by omega), ite_eq_right (by omega)]
    simp only [pv, pathTime, harr, union_empty]
    simp only [ih (by omega)]
    rw [sum_kingman_comp]

/-- At the upper arrival. -/
theorem pv_upper {sx sy : ℕ} (hsy : sy < sx) (M : ℝ) (F : Finset (Finset X)) :
    pv (arrivals x y sx sy) R M (sy + 1) F = ∑ H, kingmanTransition (pathTime M (sy + 1)) (F ∪ {{y}}) H * R H := by
  have harr : arrivals x y sx sy sy = {{y}} := by
    unfold arrivals
    rw [ite_eq_left rfl]
  simp only [pv, pathTime, harr]
  simp only [pv_above hsy M sy le_rfl]
  rw [sum_kingman_comp]

/-- Between the arrivals, Kingman's coalescent runs on the lower lineage and `c`. -/
theorem pv_middle {sx sy : ℕ} (hsy : sy < sx) (M : ℝ) (r : ℕ) (hr : sy + 1 + r ≤ sx) (F : Finset (Finset X)) :
    pv (arrivals x y sx sy) R M (sy + 1 + r) F =
      ∑ G, kingmanTransition (r * M) F G * ∑ H, kingmanTransition (pathTime M (sy + 1)) (G ∪ {{y}}) H * R H := by
  induction r generalizing F with
  | zero =>
    simp only [Nat.add_zero, Nat.cast_zero, zero_mul]
    rw [pv_upper hsy, sum_kingman_zero]
  | succ r ih =>
    have harr : arrivals x y sx sy (sy + 1 + r) = ∅ := by
      unfold arrivals
      rw [ite_eq_right (by omega), ite_eq_right (by omega)]
    rw [show sy + 1 + (r + 1) = (sy + 1 + r) + 1 by omega]
    simp only [pv, harr, union_empty]
    rw [ite_eq_right (by omega)]
    simp only [ih (by omega)]
    have hlen : M + (r : ℝ) * M = ((r + 1 : ℕ) : ℝ) * M := by
      push_cast
      ring
    rw [sum_kingman_comp, hlen]

/-- At the lower arrival, and below: the two coalescents of the species tree, on the lineage of `c`. -/
theorem pv_top {sx sy : ℕ} (hsy : sy < sx) (M : ℝ) (r : ℕ) (c : X) :
    pv (arrivals x y sx sy) R M (sx + 1 + r) {{c}} =
      ∑ G, kingmanTransition (((sx - sy : ℕ) : ℝ) * M) ({{c}, {x}} : Finset (Finset X)) G *
        ∑ H, kingmanTransition (pathTime M (sy + 1)) (G ∪ {{y}}) H * R H := by
  induction r with
  | zero =>
    have harr : arrivals x y sx sy sx = {{x}} := by
      unfold arrivals
      rw [ite_eq_right (by omega), ite_eq_left rfl]
    simp only [pv, harr]
    rw [ite_eq_right (by omega)]
    have hmid : ∀ G, pv (arrivals x y sx sy) R M sx G =
        ∑ G', kingmanTransition (((sx - sy - 1 : ℕ) : ℝ) * M) G G' * ∑ H, kingmanTransition (pathTime M (sy + 1)) (G' ∪ {{y}}) H * R H := by
      intro G
      have := pv_middle (R := R) (x := x) (y := y) hsy M (sx - sy - 1) (by omega) G
      rwa [show sy + 1 + (sx - sy - 1) = sx by omega] at this
    simp only [hmid]
    have hlen : M + ((sx - sy - 1 : ℕ) : ℝ) * M = ((sx - sy : ℕ) : ℝ) * M := by
      have h1 : ((sx - sy : ℕ) : ℝ) = ((sx - sy - 1 : ℕ) : ℝ) + 1 := by
        rw [← Nat.cast_add_one]
        congr 1
        omega
      rw [h1]
      ring
    rw [sum_kingman_comp, hlen, show ({{c}} ∪ {{x}} : Finset (Finset X)) = {{c}, {x}} from rfl]
  | succ r ih =>
    have harr : arrivals x y sx sy (sx + 1 + r) = ∅ := by
      unfold arrivals
      rw [ite_eq_right (by omega), ite_eq_right (by omega)]
    rw [show sx + 1 + (r + 1) = (sx + 1 + r) + 1 by omega]
    simp only [pv, harr, union_empty]
    rw [sum_kingman_singleton, ih]

end Schedule

end AllmanEtAl2023.NetworkNk
