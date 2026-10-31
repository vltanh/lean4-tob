module

public import Basic.Phylogenetics.NMSC.Basic
public import Basic.Probability.QuartetLimits
public import External.AllmanEtAl2023.Basic
public import External.AllmanEtAl2023.Theorem1
public import External.Rhodes2020.Theorem2
public import TINNiK.Statistics.AppendixC

/-!
# TINNiK: consistency of the algorithm

The count of Step 3(a)(i) (E29 of the report), and Theorem 4. Theorem 4 takes the CF-detectability of 4-blobs from
`External.AllmanEtAl2023.corollary1` (TINNiK's Theorem 1 on the induced 4-taxon networks, proved in
`External/AllmanEtAl2023/Theorem1.lean`), and excludes the centroid by the analytic argument of the paper
(`isGenericNull_centroid`). Theorem 2 and the combinatorial part of Theorem 3 are proved in
`External/AllmanEtAl2023/Basic.lean`.
-/

@[expose] public noncomputable section

open Phylogenetics Phylogenetics.RootedNetwork Finset Filter Topology
open scoped Classical

namespace TINNiK

variable {V E X : Type*} [Fintype X] [DecidableEq X]

/-- The count of Step 3(a)(i) of the B-quartet Inference Algorithm, corrected (E29 of the report): a
4-taxon set has exactly `4 (N - 4)` others sharing exactly three of its taxa. The printed `4(N - 1)` is
a misprint. -/
theorem card_sharing_three {q : Finset X} (hq : q.card = 4) :
    (univ.filter fun t : Finset X => t.card = 4 ∧ (t ∩ q).card = 3).card = 4 * (Fintype.card X - 4) := by
  have himg : (univ.filter fun t : Finset X => t.card = 4 ∧ (t ∩ q).card = 3) =
      (q ×ˢ qᶜ).image (fun p : X × X => insert p.2 (q.erase p.1)) := by
    ext t
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image, Finset.mem_product,
      Finset.mem_compl, Prod.exists]
    constructor
    · rintro ⟨ht, hi⟩
      have h1 : (t \ q).card = 1 := by
        have := Finset.card_inter_add_card_sdiff t q
        omega
      have h2 : (q \ t).card = 1 := by
        have := Finset.card_inter_add_card_sdiff q t
        rw [Finset.inter_comm] at this
        omega
      obtain ⟨v, hv⟩ := Finset.card_eq_one.mp h1
      obtain ⟨u, hu⟩ := Finset.card_eq_one.mp h2
      have hvm : v ∈ t \ q := by simp [hv]
      have hum : u ∈ q \ t := by simp [hu]
      refine ⟨u, v, ⟨(Finset.mem_sdiff.mp hum).1, (Finset.mem_sdiff.mp hvm).2⟩, ?_⟩
      ext x
      simp only [Finset.mem_insert, Finset.mem_erase]
      constructor
      · rintro (rfl | ⟨hxu, hxq⟩)
        · exact (Finset.mem_sdiff.mp hvm).1
        · by_contra hxt
          have : x ∈ q \ t := Finset.mem_sdiff.mpr ⟨hxq, hxt⟩
          rw [hu] at this
          exact hxu (Finset.mem_singleton.mp this)
      · intro hxt
        by_cases hxq : x ∈ q
        · refine Or.inr ⟨fun h => ?_, hxq⟩
          exact (Finset.mem_sdiff.mp hum).2 (h ▸ hxt)
        · have : x ∈ t \ q := Finset.mem_sdiff.mpr ⟨hxt, hxq⟩
          rw [hv] at this
          exact Or.inl (Finset.mem_singleton.mp this)
    · rintro ⟨u, v, ⟨hu, hv⟩, rfl⟩
      have hve : v ∉ q.erase u := fun h => hv (Finset.mem_of_mem_erase h)
      refine ⟨?_, ?_⟩
      · rw [Finset.card_insert_of_notMem hve, Finset.card_erase_of_mem hu, hq]
      · have : insert v (q.erase u) ∩ q = q.erase u := by
          ext x
          simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_erase]
          constructor
          · rintro ⟨rfl | h, hx⟩
            · exact absurd hx hv
            · exact h
          · intro h
            exact ⟨Or.inr h, h.2⟩
        rw [this, Finset.card_erase_of_mem hu, hq]
  rw [himg, Finset.card_image_of_injOn, Finset.card_product, Finset.card_compl, hq]
  rintro ⟨u, v⟩ h ⟨u', v'⟩ h' heq
  simp only [Finset.mem_coe, Finset.mem_product, Finset.mem_compl] at h h'
  simp only at heq
  have hvv : v = v' := by
    have : v ∈ insert v' (q.erase u') := heq ▸ Finset.mem_insert_self v _
    rcases Finset.mem_insert.mp this with h1 | h1
    · exact h1
    · exact absurd (Finset.mem_of_mem_erase h1) h.2
  subst hvv
  have huu : u = u' := by
    by_contra hne
    have h1 : u ∈ insert v (q.erase u') :=
      Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨hne, h.1⟩)
    rw [← heq] at h1
    rcases Finset.mem_insert.mp h1 with h2 | h2
    · exact h.2 (h2 ▸ h.1)
    · exact Finset.notMem_erase u q h2
  rw [huu]

omit [Fintype X] in
/-- `BInferred` holds only of 4-taxon sets. -/
private theorem card_of_bInferred {B₀ : Set (Finset X)} {τ : Set (QuartetTree X)}
    (hB₀ : ∀ q ∈ B₀, q.card = 4) {q : Finset X} (h : BInferred B₀ τ q) : q.card = 4 := by
  have key : ∀ {a b c d e : X} {q : Finset X}, ({a, b, c, d, e} : Finset X).card = 5 →
      q ∈ ({{a, b, c, e}, {a, b, d, e}, {a, c, d, e}} : Finset (Finset X)) → q.card = 4 := by
    intro a b c d e q h5 hq
    obtain ⟨hab, hac, had, hae, hbc, hbd, hbe, hcd, hce, hde⟩ :=
      External.AllmanEtAl2023.ne_of_card_five h5
    simp only [Finset.mem_insert, Finset.mem_singleton] at hq
    rcases hq with rfl | rfl | rfl
    · exact TreeMetric.card_four_of_ne hab hac hae hbc hbe hce
    · exact TreeMetric.card_four_of_ne hab had hae hbd hbe hde
    · exact TreeMetric.card_four_of_ne hac had hae hcd hce hde
  induction h with
  | base q hq => exact hB₀ q hq
  | ruleB a b c d e t q h5 _ _ _ _ hq _ _ _ => exact key h5 hq
  | ruleT a b c d e s q h5 _ _ _ _ _ hq _ _ => exact key h5 hq

/-- The quartet distance depends only on the 4-taxon sets in its first argument. -/
private theorem quartetDistance_congr {Bq Bq' : Set (Finset X)} {τ τ' : Set (QuartetTree X)}
    (h1 : ∀ q : Finset X, q.card = 4 → (q ∈ Bq ↔ q ∈ Bq')) (h2 : τ = τ') :
    quartetDistance Bq τ = quartetDistance Bq' τ' := by
  subst h2
  funext x y
  unfold quartetDistance
  by_cases hxy : x = y
  · simp [hxy]
  · simp only [hxy, ↓reduceIte]
    have : (univ.filter fun q : Finset X =>
        q.card = 4 ∧ x ∈ q ∧ y ∈ q ∧ (q ∈ Bq ∨ ∃ s ∈ τ, s.taxa = q ∧ Separated s x y)) =
        univ.filter fun q : Finset X =>
        q.card = 4 ∧ x ∈ q ∧ y ∈ q ∧ (q ∈ Bq' ∨ ∃ s ∈ τ, s.taxa = q ∧ Separated s x y) := by
      refine Finset.filter_congr fun q _ => ?_
      constructor
      · rintro ⟨h4, hx, hy, h⟩
        exact ⟨h4, hx, hy, h.imp_left (h1 q h4).mp⟩
      · rintro ⟨h4, hx, hy, h⟩
        exact ⟨h4, hx, hy, h.imp_left (h1 q h4).mpr⟩
    rw [this]

/-- The deterministic part of Theorem 4: from correct answers on all 4-taxon sets the algorithm returns
the tree of blobs. The closure identifies the B-quartets (`closure_complete`, `closure_sound`); the
quartet distance is then the tree metric of the quartet metrization of the tree of blobs (Rhodes 2020,
Theorem 2); an exact tree builder returns it; and the internal branches of length at least `2` survive
the cutoff `δ < 2`. -/
private theorem tinnik_eq_of_tests {V E : Type*} {N : RootedNetwork V E X} (hN : N.IsPhylogenetic)
    (hX : 4 ≤ Fintype.card X) {ml : (QuartetTree X → ℝ) → Finset X → QuartetTree X} {a β δ : ℝ}
    (hδ₂ : δ < 2) {M : TreeBuilder X} (hM : IsExactBuilder M) {c : QuartetTree X → ℝ}
    (hB : testedB ml a β c = {q | q.card = 4 ∧ ¬ IsTreelike N q})
    (hT : testedT ml a β c = {s | InducedCutSplit N s}) :
    tinnik ml a β δ M c = treeOfBlobs N := by
  have hne : Nonempty X := Fintype.card_pos_iff.mp (by omega)
  have hTB : IsUnrootedTree (treeOfBlobs N) := treeOfBlobs_isUnrootedTree hN
  -- the closure is the set of B-quartets
  have hBset : {q | BInferred {q' : Finset X | q'.card = 4 ∧ ¬ IsTreelike N q'}
      {s | InducedCutSplit N s} q} = {q | q.card = 4 ∧ IsBQuartet N q} := by
    ext q
    simp only [Set.mem_ofPred_eq]
    constructor
    · intro h
      exact ⟨card_of_bInferred (B₀ := {q' | q'.card = 4 ∧ ¬ IsTreelike N q'}) (fun q hq => hq.1) h,
        External.AllmanEtAl2023.closure_sound hN h⟩
    · rintro ⟨h4, h⟩
      exact External.AllmanEtAl2023.closure_complete hN h4 h
  have hτ : {s : QuartetTree X | s ∈ {s | InducedCutSplit N s} ∧
      s.taxa ∉ {q | q.card = 4 ∧ IsBQuartet N q}} = {s | Displays (treeOfBlobs N) s} := by
    ext s
    simp only [Set.mem_ofPred_eq, External.AllmanEtAl2023.displays_treeOfBlobs_iff hN s,
      QuartetTree.card_taxa, true_and]
  have hdist : quartetDistance {q | q.card = 4 ∧ IsBQuartet N q}
      {s | Displays (treeOfBlobs N) s} =
      treeMetric (treeOfBlobs N) (External.Rhodes2020.quartetWeight (treeOfBlobs N)) := by
    funext x y
    by_cases hxy : x = y
    · subst hxy
      simp only [quartetDistance, ↓reduceIte, treeMetric]
      refine (Finset.sum_eq_zero fun A hA => ?_).symm
      have := Finset.mem_filter.mp hA
      exact absurd this.2.1 this.2.2
    · rw [External.Rhodes2020.theorem2 hTB hX hxy]
      exact congrFun (congrFun (quartetDistance_congr (fun q h4 => by
        simp only [Set.mem_ofPred_eq, h4, true_and]; rfl) rfl) x) y
  have hw : ∀ A ∈ treeOfBlobs N, 0 < External.Rhodes2020.quartetWeight (treeOfBlobs N) A ∧
      External.Rhodes2020.quartetWeight (treeOfBlobs N) Aᶜ =
        External.Rhodes2020.quartetWeight (treeOfBlobs N) A := fun A hA =>
    ⟨lt_of_lt_of_le two_pos (External.Rhodes2020.quartetWeight_ge_two hTB hX hA),
      External.Rhodes2020.quartetWeight_compl _ _⟩
  obtain ⟨h0, h1, h2, h3⟩ := hM _ _ hTB hw
  simp only [tinnik]
  rw [hB, hT, hBset, hτ, hdist]
  have hX2 : 2 ≤ Fintype.card X := by omega
  have hTfam := (isUnrootedTree_iff hX2 _).mp hTB
  have hbuilt := (isUnrootedTree_iff hX2 _).mp h0
  ext A
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨hA, hor⟩
    by_contra hnA
    rcases hor with hor | ⟨-, hpos⟩
    · -- a side of a tree that is not internal is a singleton or the complement of one
      apply hnA
      have hne := hbuilt.nonempty A hA
      have hne' := hbuilt.compl_nonempty A hA
      simp only [internalSides, Finset.mem_filter, not_and_or, not_le] at hor
      rcases hor with hor | hor | hor
      · exact absurd hA hor
      · obtain ⟨x, rfl⟩ := Finset.card_eq_one.mp
          (le_antisymm (by omega) (Finset.card_pos.mpr hne))
        exact hTfam.singleton_mem x
      · obtain ⟨x, hx⟩ := Finset.card_eq_one.mp
          (le_antisymm (by omega) (Finset.card_pos.mpr hne'))
        have := hTfam.compl_mem _ (hTfam.singleton_mem x)
        rwa [← hx, compl_compl] at this
    · exact absurd hpos (not_lt.mpr (h3 A hA hnA))
  · intro hA
    refine ⟨h1 hA, Or.inr ?_⟩
    rw [h2 A hA]
    have h2le := External.Rhodes2020.quartetWeight_ge_two hTB hX hA
    exact ⟨hδ₂.le.trans h2le, lt_of_lt_of_le two_pos h2le⟩

/-- The answers wanted on a set of four taxa: the star test rejects; a cut-edge split on the induced
network is the maximum likelihood topology, and the cut test does not reject it; and without a
cut-edge split the cut test rejects. -/
private def QGood {V E : Type*} (N : RootedNetwork V E X)
    (ml : (QuartetTree X → ℝ) → Finset X → QuartetTree X) (β a : ℝ) (c : QuartetTree X → ℝ)
    (q : Finset X) : Prop :=
  starPValue .lrt c q < β ∧ (∀ s ∈ treesOn q, InducedCutSplit N s → ml c q = s ∧ a ≤ cutPValue c s) ∧
    (¬ IsTreelike N q → cutPValue c (ml c q) < a)

/-- The tests are right when they are right on each set of four taxa. -/
private theorem tests_of_qGood {V E : Type*} {N : RootedNetwork V E X} {ml : (QuartetTree X → ℝ) → Finset X → QuartetTree X}
    {β a : ℝ} {c : QuartetTree X → ℝ} (h : ∀ q : Finset X, q.card = 4 → QGood N ml β a c q) :
    testedB ml a β c = {q | q.card = 4 ∧ ¬ IsTreelike N q} ∧
      testedT ml a β c = {s | InducedCutSplit N s} := by
  have hB : testedB ml a β c = {q | q.card = 4 ∧ ¬ IsTreelike N q} := by
    ext q
    simp only [testedB, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨h4, hor⟩
      obtain ⟨h1, h2, -⟩ := h q h4
      refine ⟨h4, ?_⟩
      rintro ⟨s, hs, hcs⟩
      obtain ⟨h3, h5⟩ := h2 s hs hcs
      rcases hor with hor | hor
      · exact absurd h1 (not_lt.mpr hor)
      · rw [h3] at hor
        exact absurd hor (not_lt.mpr h5)
    · rintro ⟨h4, hnt⟩
      exact ⟨h4, Or.inr ((h q h4).2.2 hnt)⟩
  refine ⟨hB, ?_⟩
  ext s
  simp only [testedT, Set.mem_ofPred_eq, hB]
  have hsmem : s ∈ treesOn s.taxa := Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩
  constructor
  · rintro ⟨hn, hs⟩
    have htl : IsTreelike N s.taxa := by
      by_contra hnt
      exact hn ⟨QuartetTree.card_taxa s, hnt⟩
    obtain ⟨s₀, hs₀, hc₀⟩ := htl
    obtain ⟨h1, -⟩ := (h s.taxa (QuartetTree.card_taxa s)).2.1 s₀ hs₀ hc₀
    rw [hs, h1]
    exact hc₀
  · intro hc
    exact ⟨fun hn => hn.2 ⟨s, hsmem, hc⟩,
      ((h s.taxa (QuartetTree.card_taxa s)).2.1 s hsmem hc).1.symm⟩

/-- If two events have probability tending to one, so does their intersection. -/
theorem tendsto_iidProb_and {Γ : Type*} [Fintype Γ] {dist : Γ → ℝ} (hd : IsDist dist)
    {P Q : (n : ℕ) → (Fin n → Γ) → Prop}
    (hP : Tendsto (fun n => iidProb dist n (P n)) atTop (𝓝 1))
    (hQ : Tendsto (fun n => iidProb dist n (Q n)) atTop (𝓝 1)) :
    Tendsto (fun n => iidProb dist n fun ω => P n ω ∧ Q n ω) atTop (𝓝 1) := by
  have h := tendsto_iidProb_forall hd (ι := Bool) (fun b n ω => if b = true then P n ω else Q n ω)
    (by intro b; cases b <;> simpa)
  refine tendsto_iidProb_of_imp hd (Eventually.of_forall fun n ω hω => ?_) h
  exact ⟨by simpa using hω true, by simpa using hω false⟩

/-- Gene trees under the NMSC are binary, so they display one quartet tree on each set of four taxa. -/
private theorem displaysOne_nmsc {V E : Type*} [Fintype V] [Fintype E] [Nonempty X]
    {N : RootedNetwork V E X} (hN : N.IsPhylogenetic) {θ : MetricData E} {ρ : ℝ} :
    QuartetTests.DisplaysOne (geneTreeDist N θ ρ) (unroot (L := X)) := by
  intro g hg q hq
  obtain ⟨hH, hbin⟩ := geneTreeDist_support hN hg
  have hbt : IsBinaryTree (unroot g) := ⟨g, hH, rfl, hbin⟩
  obtain ⟨s, hs, hd⟩ := hbt.exists_displays hq
  refine ⟨s, ⟨hs, hd⟩, fun s' h' => ?_⟩
  exact IsUnrootedTree.displays_unique ⟨g, hH, rfl⟩ h'.2 hd
    (by rw [(Finset.mem_filter.mp h'.1).2, (Finset.mem_filter.mp hs).2])

/-- Levels with `log α_m / m → 0` are eventually above the `χ²₁` tail at `m d`. -/
private theorem eventually_chiSqOneTail_le {α : ℕ → ℝ} (hα : ∀ m, 0 < α m)
    (hαlog : Tendsto (fun m : ℕ => Real.log (α m) / m) atTop (𝓝 0)) {d : ℝ} (hd : 0 < d) :
    ∀ᶠ n : ℕ in atTop, chiSqOneTail (n * d) ≤ α n := by
  have h1 : ∀ᶠ n : ℕ in atTop, -(d / 2) < Real.log (α n) / n :=
    hαlog.eventually (lt_mem_nhds (by linarith))
  filter_upwards [h1, eventually_gt_atTop 0] with n hn hn0
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn0
  have ht : (0 : ℝ) ≤ n * d := by positivity
  have h2 : chiSqOneTail (n * d) ≤ chiSqTwoTail (n * d) :=
    (QuartetTests.chiSqOneTail_le_t1Tail 0 _).trans (QuartetTests.t1Tail_le_chiSqTwoTail le_rfl ht)
  refine h2.trans ?_
  rw [chiSqTwoTail, ← Real.le_log_iff_exp_le (hα n)]
  have := (lt_div_iff₀ hn').mp hn
  linarith

/-- Step 2a of the algorithm: for any `β > 0` the star test rejects a concordance factor off the
centroid, with probability tending to one. -/
private theorem tendsto_star {Γ : Type*} [Fintype Γ] {dist : Γ → ℝ} {sides : Γ → Finset (Finset X)}
    (hd : IsDist dist) (hs : QuartetTests.DisplaysOne dist sides) {q : Finset X} (hq : q.card = 4)
    (h : ¬ ∀ r ∈ treesOn q, displayCF dist sides r = 1 / 3) {β : ℝ} (hβ : 0 < β) :
    Tendsto (fun n => iidProb dist n fun ω => starPValue .lrt (quartetCount sides ω) q < β)
      atTop (𝓝 1) := by
  have h0 := QuartetTests.starStat_growth .lrt hd hs hq h (b := fun _ => -2 * Real.log β)
    (tendsto_const_div_atTop_nhds_zero_nat _)
  refine tendsto_iidProb_of_imp hd (Eventually.of_forall fun n ω hω => ?_) h0
  have he : Real.exp (-(-2 * Real.log β) / 2) = β := by
    rw [show -(-2 * Real.log β) / 2 = Real.log β by ring, Real.exp_log hβ]
  rw [he] at hω
  exact hω

/-- At a strictly cut CF the maximum likelihood topology is the cut split, and the cut test does not reject. -/
private theorem tendsto_good_cut {V E : Type*} [Fintype V] [Fintype E] [Nonempty X]
    {N : RootedNetwork V E X} (hN : N.IsPhylogenetic) {θ : MetricData E} (hθ : N.IsMetric θ)
    {ρ : ℝ} (hρ : 0 ≤ ρ ∧ ρ ≤ 1) {α : ℕ → ℝ} (hα₀ : Tendsto α atTop (𝓝 0))
    {ml : (QuartetTree X → ℝ) → Finset X → QuartetTree X}
    (hml : IsMLSelection ml) {s₀ : QuartetTree X}
    (hc : External.AllmanEtAl2023.IsStrictlyCut (nmscCF N θ ρ) s₀) :
    Tendsto (fun m => iidProb (geneTreeDist N θ ρ) m fun ω =>
      ml (quartetCount unroot ω) s₀.taxa = s₀ ∧
        α m ≤ cutPValue (quartetCount unroot ω) s₀) atTop (𝓝 1) := by
  have hd : IsDist (geneTreeDist N θ ρ) :=
    ⟨geneTreeDist_nonneg hN hθ hρ, sum_geneTreeDist hN hθ hρ⟩
  have hs := displaysOne_nmsc (θ := θ) (ρ := ρ) hN
  obtain ⟨hcne, hceq⟩ := hc
  have hq := QuartetTree.card_taxa s₀
  have hs₀ : s₀ ∈ treesOn s₀.taxa := Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩
  have hnull := QuartetTests.cutTest_null hd hs (s := s₀) hcne hceq
    (fun r _ => nmscCF_pos hN hθ hρ r) hα₀
  refine tendsto_iidProb_of_imp hd (Eventually.of_forall fun m ω hω => ?_) hnull
  obtain ⟨h2, h3⟩ := hω
  refine ⟨?_, h3⟩
  obtain ⟨hm1, hm2⟩ := hml (quartetCount unroot ω) s₀.taxa hq
  by_contra hneq
  have halt : ml (quartetCount unroot ω) s₀.taxa ∈ s₀.alternatives :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hm1).2, hneq⟩
  exact absurd (hm2 s₀ hs₀) (not_le.mpr (h2 _ halt))

/-- The cut test rejects at the levels `α`, with probability tending to one, on the 4-taxon sets with
no cut-edge split on their induced network. -/
def Rejects {V E : Type*} [Fintype V] [Fintype E] (N : RootedNetwork V E X) (θ : MetricData E) (ρ : ℝ)
    (α : ℕ → ℝ) : Prop :=
  ∀ q : Finset X, q.card = 4 → ¬ IsTreelike N q →
    Tendsto (fun m => iidProb (geneTreeDist N θ ρ) m fun ω =>
      ∀ s ∈ treesOn q, cutPValue (quartetCount unroot ω) s < α m) atTop (𝓝 1)

/-- At a non-cut CF, levels `α_m` with `log(1/α_m) = o(m)` eventually exceed `P(χ²₁ > m d)`, where the cut
test's p-value lies, so the cut test rejects at them. -/
private theorem tendsto_cut_rejects {V E : Type*} [Fintype V] [Fintype E] {N : RootedNetwork V E X}
    {θ : MetricData E} {ρ : ℝ} (hd : IsDist (geneTreeDist N θ ρ)) {α : ℕ → ℝ} (hα : ∀ m, 0 < α m)
    (hαlog : Tendsto (fun m : ℕ => Real.log (α m) / m) atTop (𝓝 0)) {q : Finset X} (hq : q.card = 4)
    (hnc : External.AllmanEtAl2023.IsNonCut (nmscCF N θ ρ) q) :
    Tendsto (fun m => iidProb (geneTreeDist N θ ρ) m fun ω =>
      ∀ s ∈ treesOn q, cutPValue (quartetCount unroot ω) s < α m) atTop (𝓝 1) := by
  obtain ⟨d, hd0, halt⟩ := QuartetTests.cutTest_alternative hd hq hnc
  exact tendsto_iidProb_of_imp hd
    ((eventually_chiSqOneTail_le hα hαlog hd0).mono fun m hm ω hω s hs => (hω s hs).trans_le hm) halt

/-- The concordance factors are off the centroid on each set of four taxa. -/
def NoCentroidCF (p : QuartetTree X → ℝ) : Prop :=
  ∀ q : Finset X, q.card = 4 → ¬ ∀ r ∈ treesOn q, p r = 1 / 3

/-- CF-detectability excludes the centroid: strictly cut and non-cut CFs each have two different entries. So
the paper's separate step for the centroid (`isGenericNull_centroid`) is redundant, as Section 11 of the
report records. -/
theorem noCentroidCF_of_cfDetectable {V E : Type*} {N : RootedNetwork V E X}
    {p : QuartetTree X → ℝ} (hdet : External.AllmanEtAl2023.CFDetectable N p) : NoCentroidCF p := by
  intro q hq hall
  by_cases htl : IsTreelike N q
  · obtain ⟨s, hs, hc⟩ := htl
    obtain ⟨r, hr⟩ := Finset.card_pos.mp
      (by rw [QuartetTree.card_alternatives]; norm_num : 0 < s.alternatives.card)
    have hrq : r ∈ treesOn q :=
      mem_treesOn.2 ((QuartetTree.mem_alternatives.1 hr).1.trans (mem_treesOn.1 hs))
    exact (hdet.cut s hc).1 r hr ((hall r hrq).trans (hall s hs).symm)
  · obtain ⟨r, hr, r', hr', hrr⟩ := Finset.one_lt_card.mp
      (by rw [card_treesOn hq]; norm_num : 1 < (treesOn q).card)
    exact hdet.blob q hq htl r hr r' hr' hrr ((hall r hr).trans (hall r' hr').symm)

omit [Fintype X] [DecidableEq X] in
/-- The deletion that leaves each vertex exactly one parent. Off it, the inheritance probabilities of
`External.AllmanEtAl2023.deletionMetric` are all `0` or `1`. -/
private theorem exists_isDeletion_unique_parent {V E : Type*} [Fintype E] {N : RootedNetwork V E X}
    (hN : N.IsPhylogenetic) : ∃ D : Set E, N.IsDeletion D ∧
      ∀ f g, f ∉ D → g ∉ D → N.graph.target f = N.graph.target g → f = g := by
  have hex : ∀ v : V, ∃ g : Option E, ∀ f, N.graph.target f = v →
      ∃ f', g = some f' ∧ N.graph.target f' = v := by
    intro v
    by_cases h : ∃ f, N.graph.target f = v
    · obtain ⟨f, hf⟩ := h
      exact ⟨some f, fun _ _ => ⟨f, rfl, hf⟩⟩
    · exact ⟨none, fun f hf => absurd ⟨f, hf⟩ h⟩
  choose c hc using hex
  refine ⟨{f | N.IsHybridArc f ∧ c (N.graph.target f) ≠ some f}, ⟨fun e he => he.1, fun v hv => ?_⟩,
    fun f g hf hg hfg => ?_⟩
  · obtain ⟨f, hf⟩ := (N.graph.one_le_indegree_iff v).mp (hN.nonroot_indegree v hv)
    obtain ⟨f', hc', hf'⟩ := hc v f hf
    exact ⟨f', fun h => h.2 (by rw [hf', hc']), hf'⟩
  · by_cases hh : N.IsHybridArc f
    · have hg' : N.IsHybridArc g := by
        unfold IsHybridArc at hh ⊢
        rwa [← hfg]
      have h₁ : c (N.graph.target f) = some f := by
        by_contra h
        exact hf ⟨hh, h⟩
      have h₂ : c (N.graph.target g) = some g := by
        by_contra h
        exact hg ⟨hg', h⟩
      rw [hfg, h₂] at h₁
      exact (Option.some.inj h₁).symm
    · have hc1 : (NMSC.arcsInto N (N.graph.target f)).card ≤ 1 := by
        rw [← NMSC.indegree_eq_card]
        unfold IsHybridArc at hh
        omega
      exact Finset.card_le_one.1 hc1 _ (NMSC.mem_arcsInto.2 rfl) _ (NMSC.mem_arcsInto.2 hfg.symm)

/-- **The centroid is excluded for generic parameters**, as the paper does before its Theorem 4
(`notes/tinnik/readable.txt`, line 206): no induced 4-taxon network has `CF = (1/3, 1/3, 1/3)`. With a 4-blob
this follows from the non-cut CF of TINNiK's Theorem 1. Without one, at hybridization parameters `0` or `1` the
network is a resolved tree off the deleted arcs, whose CF is off the centroid: with long arcs, the CF of the
cut split is more than `3/4`. Analyticity then gives the inequality for generic parameters.

This step is redundant, as Section 11 of the report records: `noCentroidCF_of_cfDetectable` derives the same
exclusion, at given parameters, from CF-detectability. `theorem4` uses this step, since the paper does. -/
theorem isGenericNull_centroid [Fintype V] [Fintype E] {N : RootedNetwork V E X}
    (hN : N.IsPhylogenetic) (hBin : N.IsBinary) :
    External.AllmanEtAl2023.IsGenericNull N {θ | N.IsMetric θ ∧ ¬ NoCentroidCF (nmscCF N θ 0)} := by
  have key : ∀ q : {q : Finset X // q.card = 4}, External.AllmanEtAl2023.IsGenericNull N
      {θ | N.IsMetric θ ∧ ∀ r ∈ treesOn q.val, nmscCF N θ 0 r = 1 / 3} := by
    rintro ⟨q, hq⟩
    obtain ⟨r, hr, r', hr', hrr⟩ := Finset.one_lt_card.mp
      (by rw [card_treesOn hq]; norm_num : 1 < (treesOn q).card)
    by_cases htl : IsTreelike N q
    · obtain ⟨s, hs, hc⟩ := htl
      obtain ⟨D, hD, -⟩ := exists_isDeletion_unique_parent hN
      obtain ⟨e, he⟩ := External.AllmanEtAl2023.exists_splitOffAt_of_inducedCutSplit hN hc
      have hlt := External.AllmanEtAl2023.three_quarters_lt_nmscCF hN hD (ℓ := fun _ => 3)
        (fun _ => by norm_num) rfl (he.mono (Set.empty_subset D))
      have hne : nmscCF N (External.AllmanEtAl2023.deletionMetric N D fun _ => 3) 0 s ≠ 1 / 3 := by
        intro h
        rw [h] at hlt
        norm_num at hlt
      refine (External.AllmanEtAl2023.isGenericNull_of_analyticOnNhd
        (F := fun θ => nmscCF N θ 0 s - 1 / 3)
        (fun d => (analyticOnNhd_nmscCF_coordMetric N d 0 s).sub analyticOnNhd_const)
        (External.AllmanEtAl2023.isNormalized_deletionMetric hN hD _) (sub_ne_zero.2 hne)).mono ?_
      exact fun θ hθ => ⟨hθ.1, sub_eq_zero.2 (hθ.2 s hs)⟩
    · exact (External.AllmanEtAl2023.isGenericNull_not_isNonCut hN hBin hq htl).mono fun θ hθ =>
        ⟨hθ.1, fun hnc => hnc r hr r' hr' hrr ((hθ.2 r hr).trans (hθ.2 r' hr').symm)⟩
  refine (External.AllmanEtAl2023.IsGenericNull.iUnion key).mono ?_
  rintro θ ⟨hθ, hnot⟩
  unfold NoCentroidCF at hnot
  push Not at hnot
  obtain ⟨q, hq, hall⟩ := hnot
  exact Set.mem_iUnion.2 ⟨⟨q, hq⟩, hθ, hall⟩

/-- On each set of four taxa, the tests give the wanted answers with probability tending to one: Step 2a at a
CF off the centroid, and the cut test by CF-detectability. -/
private theorem tendsto_qGood {V E : Type*} [Fintype V] [Fintype E] {N : RootedNetwork V E X}
    (hN : N.IsPhylogenetic) (hX : 4 ≤ Fintype.card X) {θ : MetricData E} (hθ : N.IsMetric θ)
    {ρ : ℝ} (hρ : 0 ≤ ρ ∧ ρ ≤ 1) (hdet : External.AllmanEtAl2023.CFDetectable N (nmscCF N θ ρ))
    (hcen : NoCentroidCF (nmscCF N θ ρ))
    {α : ℕ → ℝ} (hα₀ : Tendsto α atTop (𝓝 0)) (hrej : Rejects N θ ρ α)
    {β : ℝ} (hβ : 0 < β) {ml : (QuartetTree X → ℝ) → Finset X → QuartetTree X}
    (hml : IsMLSelection ml) {q : Finset X} (hq : q.card = 4) :
    Tendsto (fun m => iidProb (geneTreeDist N θ ρ) m fun ω =>
      QGood N ml β (α m) (quartetCount unroot ω) q) atTop (𝓝 1) := by
  have hne : Nonempty X := Fintype.card_pos_iff.mp (by omega)
  have hd : IsDist (geneTreeDist N θ ρ) :=
    ⟨geneTreeDist_nonneg hN hθ hρ, sum_geneTreeDist hN hθ hρ⟩
  have hcases : Tendsto (fun m => iidProb (geneTreeDist N θ ρ) m fun ω =>
      (∀ s ∈ treesOn q, InducedCutSplit N s →
        ml (quartetCount unroot ω) q = s ∧ α m ≤ cutPValue (quartetCount unroot ω) s) ∧
      (¬ IsTreelike N q → cutPValue (quartetCount unroot ω) (ml (quartetCount unroot ω) q) < α m))
      atTop (𝓝 1) := by
    by_cases htl : IsTreelike N q
    · -- a cut-edge split on the induced network: the cut test does not reject
      obtain ⟨s₀, hs₀, hc₀⟩ := htl
      have hst : s₀.taxa = q := (Finset.mem_filter.mp hs₀).2
      subst hst
      refine tendsto_iidProb_of_imp hd (Eventually.of_forall fun m ω hω => ?_)
        (tendsto_good_cut hN hθ hρ hα₀ hml (hdet.cut s₀ hc₀))
      refine ⟨fun s hsq hcs => ?_, fun hnt => absurd ⟨s₀, hs₀, hc₀⟩ hnt⟩
      have hss : s = s₀ := External.AllmanEtAl2023.inducedCutSplit_unique hN hcs hc₀
        (Finset.mem_filter.mp hsq).2
      subst hss
      exact hω
    · -- no cut-edge split: the cut test rejects, in particular at the maximum likelihood topology
      refine tendsto_iidProb_of_imp hd (Eventually.of_forall fun m ω hω => ?_) (hrej q hq htl)
      exact ⟨fun s hsq hcs => absurd ⟨s, hsq, hcs⟩ htl,
        fun _ => hω _ (hml (quartetCount unroot ω) q hq).1⟩
  exact tendsto_iidProb_and hd
    (tendsto_star hd (displaysOne_nmsc hN) hq (hcen q hq) hβ) hcases

/-- **The test-correctness step of the proof of Theorem 4**, for any inheritance correlation `ρ`: at
parameters satisfying CF-detectability and off the centroid, for levels `α_m → 0` at which the cut test
rejects on the sets with no cut-edge split, and any `β > 0`, TINNiK's hypothesis tests return the correct
answer on all 4-taxon sets with probability tending to one. -/
theorem tests_correct_of_noCentroidCF {V E : Type*} [Fintype V] [Fintype E] {N : RootedNetwork V E X}
    (hN : N.IsPhylogenetic) (hX : 4 ≤ Fintype.card X) {θ : MetricData E} (hθ : N.IsMetric θ)
    {ρ : ℝ} (hρ : 0 ≤ ρ ∧ ρ ≤ 1) (hdet : External.AllmanEtAl2023.CFDetectable N (nmscCF N θ ρ))
    (hcen : NoCentroidCF (nmscCF N θ ρ))
    {α : ℕ → ℝ} (hα₀ : Tendsto α atTop (𝓝 0)) (hrej : Rejects N θ ρ α)
    {β : ℝ} (hβ : 0 < β) {ml : (QuartetTree X → ℝ) → Finset X → QuartetTree X}
    (hml : IsMLSelection ml) :
    Tendsto (fun m => iidProb (geneTreeDist N θ ρ) m fun ω =>
      testedB ml (α m) β (quartetCount unroot ω) = {q | q.card = 4 ∧ ¬ IsTreelike N q} ∧
        testedT ml (α m) β (quartetCount unroot ω) = {s | InducedCutSplit N s}) atTop (𝓝 1) := by
  have hne : Nonempty X := Fintype.card_pos_iff.mp (by omega)
  have hd : IsDist (geneTreeDist N θ ρ) :=
    ⟨geneTreeDist_nonneg hN hθ hρ, sum_geneTreeDist hN hθ hρ⟩
  have hall := tendsto_iidProb_forall hd (ι := {q : Finset X // q.card = 4})
    (fun q m ω => QGood N ml β (α m) (quartetCount unroot ω) q.val)
    (fun q => tendsto_qGood hN hX hθ hρ hdet hcen hα₀ hrej hβ hml q.property)
  refine tendsto_iidProb_of_imp hd (Eventually.of_forall fun m ω hω => ?_) hall
  exact tests_of_qGood fun q hq => hω ⟨q, hq⟩

/-- `tests_correct_of_noCentroidCF` at parameters satisfying CF-detectability alone, which excludes the
centroid (`noCentroidCF_of_cfDetectable`). This is what TOB-QMC §4.3 cites from TINNiK's Theorem 4. -/
theorem tests_correct {V E : Type*} [Fintype V] [Fintype E] {N : RootedNetwork V E X}
    (hN : N.IsPhylogenetic) (hX : 4 ≤ Fintype.card X) {θ : MetricData E} (hθ : N.IsMetric θ)
    {ρ : ℝ} (hρ : 0 ≤ ρ ∧ ρ ≤ 1) (hdet : External.AllmanEtAl2023.CFDetectable N (nmscCF N θ ρ))
    {α : ℕ → ℝ} (hα₀ : Tendsto α atTop (𝓝 0)) (hrej : Rejects N θ ρ α)
    {β : ℝ} (hβ : 0 < β) {ml : (QuartetTree X → ℝ) → Finset X → QuartetTree X}
    (hml : IsMLSelection ml) :
    Tendsto (fun m => iidProb (geneTreeDist N θ ρ) m fun ω =>
      testedB ml (α m) β (quartetCount unroot ω) = {q | q.card = 4 ∧ ¬ IsTreelike N q} ∧
        testedT ml (α m) β (quartetCount unroot ω) = {s | InducedCutSplit N s}) atTop (𝓝 1) :=
  tests_correct_of_noCentroidCF hN hX hθ hρ hdet (noCentroidCF_of_cfDetectable hdet) hα₀ hrej hβ hml

/-- **Theorem 4** at given parameters (`tinnik:theorem4`). If the NMSC's concordance factors at the
parameters `θ` of a rooted binary network satisfy CF-detectability on all induced 4-taxon networks, and are
off the centroid on all of them, then for levels `α_m → 0` of the cut test at which it rejects on the sets with
no cut-edge split, for any `β > 0` and
`δ < 2`, any exact distance-based tree building method and any selection of maximum likelihood topologies,
the TINNiK algorithm on `m` independent gene trees infers the tree of blobs with probability tending to one.

The proof follows the paper: on an event of probability tending to one the star test rejects on all
4-taxon sets, and the cut test rejects exactly on the sets with no cut-edge split on their induced network,
whose maximum likelihood topology is otherwise that split; the rule's closure then gives the B-quartets
and the quartet distance is the quartet metrization of the tree of blobs, which has branches of length at
least `2`, so that the cutoff `δ` has no effect.

The hypothesis that the CFs are off the centroid is the paper's, proved for generic parameters by
`isGenericNull_centroid`. It is redundant, as Section 11 of the report records: CF-detectability already gives it,
since a strictly cut CF has two different entries, and so does a non-cut one (`noCentroidCF_of_cfDetectable`).

Departure from the paper, repairing E33 of the report: under the alternative, the paper's limit "the test
distribution converges to `χ²₁`" gives no comparison at the growing cutoffs `m d / 2`, so the test distribution is
compared pointwise with that of `Z²` (`QuartetTests.cutTail_le_chiSqOneTail`, used in
`QuartetTests.cutTest_alternative`). The paper's "without loss of generality on the vertical line" hides that the
fitted line is random: `QuartetTests.cutTest_alternative` takes the least limit over the three lines. Under the null
the proof follows the paper, reading `μ₀ → ∞` as `|μ₀| → ∞`, since anomalous strictly cut CFs have `μ₀ → -∞`: the test
distribution at the estimated parameter tends to `χ²₁`, so the p-value is asymptotically uniform and the test does
not reject at levels `α_m → 0` (`QuartetTests.cutTest_null`). -/
theorem theorem4_of_rejects [Fintype V] [Fintype E] {N : RootedNetwork V E X}
    (hN : N.IsPhylogenetic) (hX : 4 ≤ Fintype.card X) {θ : MetricData E}
    (hθ : N.IsMetric θ) (hdet : External.AllmanEtAl2023.CFDetectable N (nmscCF N θ 0))
    (hcen : NoCentroidCF (nmscCF N θ 0))
    {α : ℕ → ℝ} (hα₀ : Tendsto α atTop (𝓝 0)) (hrej : Rejects N θ 0 α)
    {β δ : ℝ} (hβ : 0 < β) (hδ₂ : δ < 2) {M : TreeBuilder X} (hM : IsExactBuilder M)
    {ml : (QuartetTree X → ℝ) → Finset X → QuartetTree X} (hml : IsMLSelection ml) :
    Tendsto (fun m => iidProb (geneTreeDist N θ 0) m fun ω =>
      tinnik ml (α m) β δ M (quartetCount unroot ω) = treeOfBlobs N) atTop (𝓝 1) := by
  have hne : Nonempty X := Fintype.card_pos_iff.mp (by omega)
  have hρ : (0 : ℝ) ≤ 0 ∧ (0 : ℝ) ≤ 1 := ⟨le_rfl, zero_le_one⟩
  have hd : IsDist (geneTreeDist N θ 0) :=
    ⟨geneTreeDist_nonneg hN hθ hρ, sum_geneTreeDist hN hθ hρ⟩
  exact tendsto_iidProb_of_imp hd
    (Eventually.of_forall fun m ω hω => tinnik_eq_of_tests hN hX hδ₂ hM hω.1 hω.2)
    (tests_correct_of_noCentroidCF hN hX hθ hρ hdet hcen hα₀ hrej hβ hml)

/-- Levels with `log(1/α_m) = o(m)` make the cut test reject on the sets with no cut-edge split. -/
theorem rejects_of_log [Fintype V] [Fintype E] [Nonempty X] {N : RootedNetwork V E X} (hN : N.IsPhylogenetic)
    {θ : MetricData E} (hθ : N.IsMetric θ) {ρ : ℝ} (hρ : 0 ≤ ρ ∧ ρ ≤ 1)
    (hdet : External.AllmanEtAl2023.CFDetectable N (nmscCF N θ ρ))
    {α : ℕ → ℝ} (hα : ∀ m, 0 < α m) (hαlog : Tendsto (fun m : ℕ => Real.log (α m) / m) atTop (𝓝 0)) :
    Rejects N θ ρ α := fun _ hq htl =>
  tendsto_cut_rejects ⟨geneTreeDist_nonneg hN hθ hρ, sum_geneTreeDist hN hθ hρ⟩ hα hαlog hq (hdet.blob _ hq htl)

/-- `P(χ²₁ > m d)` tends to zero, for `d > 0`. -/
private theorem tendsto_chiSqOneTail_mul {d : ℝ} (hd : 0 < d) :
    Tendsto (fun m : ℕ => chiSqOneTail (m * d)) atTop (𝓝 0) := by
  have h1 : Tendsto (fun m : ℕ => (m : ℝ) * d / 2) atTop atTop :=
    (tendsto_natCast_atTop_atTop.atTop_mul_const hd).atTop_div_const (by norm_num)
  have h : Tendsto (fun m : ℕ => Real.exp (-((m : ℝ) * d) / 2)) atTop (𝓝 0) := by
    refine (Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp h1)).congr fun m => ?_
    simp [neg_div]
  refine squeeze_zero (fun m => QuartetTests.chiSqOneTail_nonneg _) (fun m => ?_) h
  exact QuartetTests.chiSqOneTail_le_chiSqTwoTail (by positivity)

/-- **The levels of the paper's proof of Theorem 4.** For each 4-taxon set `q` with no cut-edge split, with
`d_q` the limit there of the least statistic, let `α'_m(q) = P(χ²₁ > m d_q)`, and let `α_m` be the maximum of the
`α'_m(q)`, with `P(χ²₁ > m)` added so that the maximum is over a nonempty set. The paper's cutoff is `m d/2`, whose
`d/2` is the `d` here (`QuartetTests.cutTest_alternative`). -/
theorem exists_levels [Fintype V] [Fintype E] [Nonempty X] {N : RootedNetwork V E X} (hN : N.IsPhylogenetic)
    {θ : MetricData E} (hθ : N.IsMetric θ) {ρ : ℝ} (hρ : 0 ≤ ρ ∧ ρ ≤ 1)
    (hdet : External.AllmanEtAl2023.CFDetectable N (nmscCF N θ ρ)) :
    ∃ α : ℕ → ℝ, Tendsto α atTop (𝓝 0) ∧ (∀ m, 0 < α m) ∧ Rejects N θ ρ α := by
  have hd : IsDist (geneTreeDist N θ ρ) :=
    ⟨geneTreeDist_nonneg hN hθ hρ, sum_geneTreeDist hN hθ hρ⟩
  classical
  let Q : Finset (Finset X) := univ.filter fun q => q.card = 4 ∧ ¬ IsTreelike N q
  have hex : ∀ q : Finset X, ∃ d : ℝ, 0 < d ∧ (q ∈ Q → Tendsto (fun n : ℕ =>
      iidProb (geneTreeDist N θ ρ) n fun ω =>
        ∀ s ∈ treesOn q, cutPValue (quartetCount unroot ω) s < chiSqOneTail (n * d)) atTop (𝓝 1)) := by
    intro q
    by_cases hq : q ∈ Q
    · obtain ⟨hq4, hnt⟩ := (mem_filter.mp hq).2
      obtain ⟨d, hd0, h⟩ := QuartetTests.cutTest_alternative hd hq4 (hdet.blob q hq4 hnt)
      exact ⟨d, hd0, fun _ => h⟩
    · exact ⟨1, one_pos, fun h => absurd h hq⟩
  choose d hd0 hdq using hex
  let α : ℕ → ℝ := fun m => Q.fold max (chiSqOneTail (m * 1)) fun q => chiSqOneTail (m * d q)
  have hle : ∀ m : ℕ, ∀ q ∈ Q, chiSqOneTail (m * d q) ≤ α m := fun m q hq =>
    (Finset.le_fold_max _).mpr (Or.inr ⟨q, hq, le_rfl⟩)
  have hbase : ∀ m : ℕ, chiSqOneTail (m * 1) ≤ α m := fun m =>
    (Finset.le_fold_max _).mpr (Or.inl le_rfl)
  refine ⟨α, ?_, fun m => (QuartetTests.chiSqOneTail_pos _).trans_le (hbase m), ?_⟩
  · have hsum : Tendsto (fun m : ℕ => chiSqOneTail (m * 1) + ∑ q ∈ Q, chiSqOneTail (m * d q)) atTop (𝓝 0) := by
      have := (tendsto_chiSqOneTail_mul (one_pos)).add
        (tendsto_finsetSum Q fun q _ => tendsto_chiSqOneTail_mul (hd0 q))
      simpa using this
    refine squeeze_zero (fun m => (QuartetTests.chiSqOneTail_nonneg _).trans (hbase m)) (fun m => ?_) hsum
    refine Finset.fold_max_le _ |>.mpr ⟨?_, fun q hq => ?_⟩
    · exact le_add_of_nonneg_right (Finset.sum_nonneg fun _ _ => QuartetTests.chiSqOneTail_nonneg _)
    · exact (Finset.single_le_sum (f := fun q => chiSqOneTail (m * d q))
        (fun _ _ => QuartetTests.chiSqOneTail_nonneg _) hq).trans
        (le_add_of_nonneg_left (QuartetTests.chiSqOneTail_nonneg _))
  · intro q hq4 hnt
    have hq : q ∈ Q := mem_filter.mpr ⟨mem_univ _, hq4, hnt⟩
    exact tendsto_iidProb_of_imp hd
      (Eventually.of_forall fun m ω hω s hs => (hω s hs).trans_le (hle m q hq)) (hdq q hq)

/-- **Theorem 4** (`tinnik:theorem4`). For generic numerical parameters on a binary network there is a
sequence `α_m → 0` such that for any `β > 0` and `2 > δ ≥ 0`, the TINNiK algorithm using the cut test on
`m` independent gene trees from the NMSC infers the tree of blobs with probability tending to one. The
sequence is the paper's (`exists_levels`), built from the limits `d` of the statistics. The generic parameters
are the paper's: those with CF-detectability on all induced 4-taxon networks
(`External.AllmanEtAl2023.corollary1`, TINNiK's Theorem 1) and no centroid CF (`isGenericNull_centroid`). That
`N` is binary is used by these two results, through `External.AllmanEtAl2023.exists_reduction`, and `0 ≤ δ` is
not used. -/
theorem theorem4 [Fintype V] [Fintype E] {N : RootedNetwork V E X}
    (hN : N.IsPhylogenetic) (hX : 4 ≤ Fintype.card X) (hBin : N.IsBinary) :
    ∃ A : Set (MetricData E), External.AllmanEtAl2023.IsGenericNull N A ∧
      ∀ θ, N.IsMetric θ → θ ∉ A →
        ∃ α : ℕ → ℝ, Tendsto α atTop (𝓝 0) ∧ (∀ m, 0 < α m) ∧
          ∀ (β δ : ℝ), 0 < β → 0 ≤ δ → δ < 2 →
          ∀ (M : TreeBuilder X), IsExactBuilder M →
          ∀ (ml : (QuartetTree X → ℝ) → Finset X → QuartetTree X), IsMLSelection ml →
            Tendsto (fun m => iidProb (geneTreeDist N θ 0) m fun ω =>
              tinnik ml (α m) β δ M (quartetCount unroot ω) = treeOfBlobs N) atTop (𝓝 1) := by
  have hne : Nonempty X := Fintype.card_pos_iff.mp (by omega)
  refine ⟨{θ | N.IsMetric θ ∧ ¬ External.AllmanEtAl2023.CFDetectable N (nmscCF N θ 0)} ∪
      {θ | N.IsMetric θ ∧ ¬ NoCentroidCF (nmscCF N θ 0)},
    (External.AllmanEtAl2023.corollary1 hN hBin).union (isGenericNull_centroid hN hBin),
    fun θ hθ hA => ?_⟩
  have hdet : External.AllmanEtAl2023.CFDetectable N (nmscCF N θ 0) := by
    by_contra hn
    exact hA (Or.inl ⟨hθ, hn⟩)
  have hcen : NoCentroidCF (nmscCF N θ 0) := by
    by_contra hn
    exact hA (Or.inr ⟨hθ, hn⟩)
  obtain ⟨α, hα₀, hαpos, hrej⟩ := exists_levels hN hθ ⟨le_rfl, zero_le_one⟩ hdet
  exact ⟨α, hα₀, hαpos, fun β δ hβ _ hδ₂ M hM ml hml =>
    theorem4_of_rejects hN hX hθ hdet hcen hα₀ hrej hβ hδ₂ hM hml⟩

/-- Theorem 4 with one sequence of levels for all networks and parameters: the upper tail of `χ²₁` at `log m`.
This is stronger than the statement of the paper, whose `α_m` depends on the unknown limits `d`. ECToBlob's
Remark 8.3 points this out. -/
theorem theorem4_explicit [Fintype V] [Fintype E] {N : RootedNetwork V E X}
    (hN : N.IsPhylogenetic) (hX : 4 ≤ Fintype.card X) {θ : MetricData E} (hθ : N.IsMetric θ)
    (hdet : External.AllmanEtAl2023.CFDetectable N (nmscCF N θ 0)) {β δ : ℝ} (hβ : 0 < β) (hδ₂ : δ < 2)
    {M : TreeBuilder X} (hM : IsExactBuilder M)
    {ml : (QuartetTree X → ℝ) → Finset X → QuartetTree X} (hml : IsMLSelection ml) :
    Tendsto (fun m : ℕ => iidProb (geneTreeDist N θ 0) m fun ω =>
      tinnik ml (chiSqOneTail (Real.log m)) β δ M (quartetCount unroot ω) = treeOfBlobs N)
      atTop (𝓝 1) := by
  have hne : Nonempty X := Fintype.card_pos_iff.mp (by omega)
  exact theorem4_of_rejects hN hX hθ hdet (noCentroidCF_of_cfDetectable hdet)
    QuartetTests.tendsto_chiSqOneTail_log
    (rejects_of_log hN hθ ⟨le_rfl, zero_le_one⟩ hdet (fun _ => QuartetTests.chiSqOneTail_pos _)
      QuartetTests.tendsto_log_chiSqOneTail_log) hβ hδ₂ hM hml

end TINNiK
