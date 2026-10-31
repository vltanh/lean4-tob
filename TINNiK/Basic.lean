module

public import Basic.Phylogenetics.NMSC.Basic
public import Basic.Probability.QuartetLimits
public import External.AllmanEtAl2023.Basic
public import External.Rhodes2020.Theorem2
public import TINNiK.Statistics.AppendixC

/-!
# TINNiK: consistency of the algorithm

Definition 6 for quartet concordance factors, the count of Step 3(a)(i) (E8 of the report), and
Theorem 4. Theorem 4 takes the CF-detectability of 4-blobs from the literature
(`External.AllmanEtAl2023.Corollary1`, TINNiK's Theorem 1 on the induced 4-taxon networks), so it is
conditional on that result. Theorem 2 and the combinatorial part of Theorem 3 are proved in
`External/AllmanEtAl2023/Basic.lean`.
-/

@[expose] public noncomputable section

open Phylogenetics Phylogenetics.RootedNetwork Finset Filter Topology
open scoped Classical

namespace TINNiK

variable {V E X : Type*} [Fintype X] [DecidableEq X]

/-- The count of Step 3(a)(i) of the B-quartet Inference Algorithm, corrected (E8 of the report): a
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

/-- At a strictly cut CF the star test rejects, the maximum likelihood topology is the cut split, and the
cut test does not reject. A strictly cut CF is off the centroid, without genericity (departure from the
paper's proof of Theorem 4; see `theorem4_of_detectable`). -/
private theorem tendsto_good_cut {V E : Type*} [Fintype V] [Fintype E] [Nonempty X]
    {N : RootedNetwork V E X} (hN : N.IsPhylogenetic) {θ : MetricData E} (hθ : N.IsMetric θ)
    {ρ : ℝ} (hρ : 0 ≤ ρ ∧ ρ ≤ 1) {α : ℕ → ℝ} (hα₀ : Tendsto α atTop (𝓝 0))
    {β : ℝ} (hβ : 0 < β) {ml : (QuartetTree X → ℝ) → Finset X → QuartetTree X}
    (hml : IsMLSelection ml) {s₀ : QuartetTree X}
    (hc : External.AllmanEtAl2023.IsStrictlyCut (nmscCF N θ ρ) s₀) :
    Tendsto (fun m => iidProb (geneTreeDist N θ ρ) m fun ω =>
      starPValue .lrt (quartetCount unroot ω) s₀.taxa < β ∧
        ml (quartetCount unroot ω) s₀.taxa = s₀ ∧
        α m ≤ cutPValue (quartetCount unroot ω) s₀) atTop (𝓝 1) := by
  have hd : IsDist (geneTreeDist N θ ρ) :=
    ⟨geneTreeDist_nonneg hN hθ hρ, sum_geneTreeDist hN hθ hρ⟩
  have hs := displaysOne_nmsc (θ := θ) (ρ := ρ) hN
  obtain ⟨hcne, hceq⟩ := hc
  have hq := QuartetTree.card_taxa s₀
  have hs₀ : s₀ ∈ treesOn s₀.taxa := Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩
  have hcentroid : ¬ ∀ r ∈ treesOn s₀.taxa, displayCF (geneTreeDist N θ ρ) unroot r = 1 / 3 := by
    intro hall
    obtain ⟨r, hr⟩ := Finset.card_pos.mp
      (by rw [QuartetTree.card_alternatives]; norm_num : 0 < s₀.alternatives.card)
    obtain ⟨-, hrt, -⟩ := Finset.mem_filter.mp hr
    refine hcne r hr ?_
    have h1 := hall r (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hrt⟩)
    have h2 := hall s₀ hs₀
    exact h1.trans h2.symm
  have hnull := QuartetTests.cutTest_null hd hs (s := s₀) hcne hceq
    (fun r _ => nmscCF_pos hN hθ hρ r) hα₀
  refine tendsto_iidProb_of_imp hd (Eventually.of_forall fun m ω hω => ?_)
    (tendsto_iidProb_and hd (tendsto_star hd hs hq hcentroid hβ) hnull)
  obtain ⟨h1, h2, h3⟩ := hω
  refine ⟨h1, ?_, h3⟩
  obtain ⟨hm1, hm2⟩ := hml (quartetCount unroot ω) s₀.taxa hq
  by_contra hneq
  have halt : ml (quartetCount unroot ω) s₀.taxa ∈ s₀.alternatives :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hm1).2, hneq⟩
  exact absurd (hm2 s₀ hs₀) (not_le.mpr (h2 _ halt))

/-- At a non-cut CF the star test rejects, and the cut test rejects at the maximum likelihood topology. -/
private theorem tendsto_good_blob {V E : Type*} [Fintype V] [Fintype E] [Nonempty X]
    {N : RootedNetwork V E X} (hN : N.IsPhylogenetic) {θ : MetricData E} (hθ : N.IsMetric θ)
    {ρ : ℝ} (hρ : 0 ≤ ρ ∧ ρ ≤ 1) {α : ℕ → ℝ} (hα : ∀ m, 0 < α m)
    (hαlog : Tendsto (fun m : ℕ => Real.log (α m) / m) atTop (𝓝 0))
    {β : ℝ} (hβ : 0 < β) {ml : (QuartetTree X → ℝ) → Finset X → QuartetTree X}
    (hml : IsMLSelection ml) {q : Finset X} (hq : q.card = 4)
    (hnc : External.AllmanEtAl2023.IsNonCut (nmscCF N θ ρ) q) :
    Tendsto (fun m => iidProb (geneTreeDist N θ ρ) m fun ω =>
      starPValue .lrt (quartetCount unroot ω) q < β ∧
        cutPValue (quartetCount unroot ω) (ml (quartetCount unroot ω) q) < α m) atTop (𝓝 1) := by
  have hd : IsDist (geneTreeDist N θ ρ) :=
    ⟨geneTreeDist_nonneg hN hθ hρ, sum_geneTreeDist hN hθ hρ⟩
  have hs := displaysOne_nmsc (θ := θ) (ρ := ρ) hN
  have hcentroid : ¬ ∀ r ∈ treesOn q, displayCF (geneTreeDist N θ ρ) unroot r = 1 / 3 := by
    intro hall
    obtain ⟨r, hr, r', hr', hrr⟩ := Finset.one_lt_card.mp
      (by rw [card_treesOn hq]; norm_num : 1 < (treesOn q).card)
    exact hnc r hr r' hr' hrr ((hall r hr).trans (hall r' hr').symm)
  obtain ⟨d, hd0, halt⟩ := QuartetTests.cutTest_alternative hd hq hnc
  refine tendsto_iidProb_of_imp hd
    ((eventually_chiSqOneTail_le hα hαlog hd0).mono fun m hm ω hω => ?_)
    (tendsto_iidProb_and hd (tendsto_star hd hs hq hcentroid hβ) halt)
  obtain ⟨h1, h2⟩ := hω
  exact ⟨h1, (h2 _ (hml (quartetCount unroot ω) q hq).1).trans_le hm⟩

/-- At a strictly cut CF, the tests do not judge the taxa a B-quartet, with probability tending to one. -/
theorem tendsto_not_testedB {V E : Type*} [Fintype V] [Fintype E] [Nonempty X]
    {N : RootedNetwork V E X} (hN : N.IsPhylogenetic) {θ : MetricData E} (hθ : N.IsMetric θ)
    {ρ : ℝ} (hρ : 0 ≤ ρ ∧ ρ ≤ 1) {α : ℕ → ℝ} (hα₀ : Tendsto α atTop (𝓝 0))
    {β : ℝ} (hβ : 0 < β) {ml : (QuartetTree X → ℝ) → Finset X → QuartetTree X}
    (hml : IsMLSelection ml) {s₀ : QuartetTree X}
    (hc : External.AllmanEtAl2023.IsStrictlyCut (nmscCF N θ ρ) s₀) :
    Tendsto (fun m => iidProb (geneTreeDist N θ ρ) m fun ω =>
      s₀.taxa ∉ testedB ml (α m) β (quartetCount unroot ω)) atTop (𝓝 1) := by
  have hd : IsDist (geneTreeDist N θ ρ) :=
    ⟨geneTreeDist_nonneg hN hθ hρ, sum_geneTreeDist hN hθ hρ⟩
  refine tendsto_iidProb_of_imp hd (Eventually.of_forall fun m ω hω hB => ?_)
    (tendsto_good_cut hN hθ hρ hα₀ hβ hml hc)
  obtain ⟨h1, h2, h3⟩ := hω
  rcases hB.2 with h | h
  · exact absurd h (not_le.mpr h1)
  · rw [h2] at h
    exact absurd h (not_lt.mpr h3)

/-- At a non-cut CF, the tests judge the taxa a B-quartet, with probability tending to one. -/
theorem tendsto_testedB {V E : Type*} [Fintype V] [Fintype E] [Nonempty X]
    {N : RootedNetwork V E X} (hN : N.IsPhylogenetic) {θ : MetricData E} (hθ : N.IsMetric θ)
    {ρ : ℝ} (hρ : 0 ≤ ρ ∧ ρ ≤ 1) {α : ℕ → ℝ} (hα : ∀ m, 0 < α m)
    (hαlog : Tendsto (fun m : ℕ => Real.log (α m) / m) atTop (𝓝 0))
    {β : ℝ} (hβ : 0 < β) {ml : (QuartetTree X → ℝ) → Finset X → QuartetTree X}
    (hml : IsMLSelection ml) {q : Finset X} (hq : q.card = 4)
    (hnc : External.AllmanEtAl2023.IsNonCut (nmscCF N θ ρ) q) :
    Tendsto (fun m => iidProb (geneTreeDist N θ ρ) m fun ω =>
      q ∈ testedB ml (α m) β (quartetCount unroot ω)) atTop (𝓝 1) := by
  have hd : IsDist (geneTreeDist N θ ρ) :=
    ⟨geneTreeDist_nonneg hN hθ hρ, sum_geneTreeDist hN hθ hρ⟩
  exact tendsto_iidProb_of_imp hd (Eventually.of_forall fun m ω hω => ⟨hq, Or.inr hω.2⟩)
    (tendsto_good_blob hN hθ hρ hα hαlog hβ hml hq hnc)

/-- On each set of four taxa, the tests give the wanted answers with probability tending to one. -/
private theorem tendsto_qGood {V E : Type*} [Fintype V] [Fintype E] {N : RootedNetwork V E X}
    (hN : N.IsPhylogenetic) (hX : 4 ≤ Fintype.card X) {θ : MetricData E} (hθ : N.IsMetric θ)
    {ρ : ℝ} (hρ : 0 ≤ ρ ∧ ρ ≤ 1) (hdet : External.AllmanEtAl2023.CFDetectable N (nmscCF N θ ρ))
    {α : ℕ → ℝ} (hα : ∀ m, 0 < α m) (hα₀ : Tendsto α atTop (𝓝 0))
    (hαlog : Tendsto (fun m : ℕ => Real.log (α m) / m) atTop (𝓝 0))
    {β : ℝ} (hβ : 0 < β) {ml : (QuartetTree X → ℝ) → Finset X → QuartetTree X}
    (hml : IsMLSelection ml) {q : Finset X} (hq : q.card = 4) :
    Tendsto (fun m => iidProb (geneTreeDist N θ ρ) m fun ω =>
      QGood N ml β (α m) (quartetCount unroot ω) q) atTop (𝓝 1) := by
  have hne : Nonempty X := Fintype.card_pos_iff.mp (by omega)
  have hd : IsDist (geneTreeDist N θ ρ) :=
    ⟨geneTreeDist_nonneg hN hθ hρ, sum_geneTreeDist hN hθ hρ⟩
  by_cases htl : IsTreelike N q
  · -- a cut-edge split on the induced network: the cut test does not reject
    obtain ⟨s₀, hs₀, hc₀⟩ := htl
    have hst : s₀.taxa = q := (Finset.mem_filter.mp hs₀).2
    subst hst
    refine tendsto_iidProb_of_imp hd (Eventually.of_forall fun m ω hω => ?_)
      (tendsto_good_cut hN hθ hρ hα₀ hβ hml (hdet.cut s₀ hc₀))
    obtain ⟨h1, h2, h3⟩ := hω
    refine ⟨h1, fun s hsq hcs => ?_, fun hnt => absurd ⟨s₀, hs₀, hc₀⟩ hnt⟩
    have hss : s = s₀ := External.AllmanEtAl2023.inducedCutSplit_unique hN hcs hc₀
      (Finset.mem_filter.mp hsq).2
    subst hss
    exact ⟨h2, h3⟩
  · -- no cut-edge split: the cut test rejects
    refine tendsto_iidProb_of_imp hd (Eventually.of_forall fun m ω hω => ?_)
      (tendsto_good_blob hN hθ hρ hα hαlog hβ hml hq (hdet.blob q hq htl))
    obtain ⟨h1, h2⟩ := hω
    exact ⟨h1, fun s hsq hcs => absurd ⟨s, hsq, hcs⟩ htl, fun _ => h2⟩

/-- **The test-correctness step of the proof of Theorem 4**, for any inheritance correlation `ρ`: at
parameters satisfying CF-detectability, for levels `α_m → 0` with `log(1/α_m) = o(m)` and any `β > 0`, TINNiK's
hypothesis tests return the correct answer on all 4-taxon sets with probability tending to one. This is
what TOB-QMC §4.3 cites from TINNiK's Theorem 4. -/
theorem tests_correct {V E : Type*} [Fintype V] [Fintype E] {N : RootedNetwork V E X}
    (hN : N.IsPhylogenetic) (hX : 4 ≤ Fintype.card X) {θ : MetricData E} (hθ : N.IsMetric θ)
    {ρ : ℝ} (hρ : 0 ≤ ρ ∧ ρ ≤ 1) (hdet : External.AllmanEtAl2023.CFDetectable N (nmscCF N θ ρ))
    {α : ℕ → ℝ} (hα : ∀ m, 0 < α m) (hα₀ : Tendsto α atTop (𝓝 0))
    (hαlog : Tendsto (fun m : ℕ => Real.log (α m) / m) atTop (𝓝 0))
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
    (fun q => tendsto_qGood hN hX hθ hρ hdet hα hα₀ hαlog hβ hml q.property)
  refine tendsto_iidProb_of_imp hd (Eventually.of_forall fun m ω hω => ?_) hall
  exact tests_of_qGood fun q hq => hω ⟨q, hq⟩

/-- **Theorem 4** at given parameters (`tinnik:theorem4`). If the NMSC's concordance factors at the
parameters `θ` of a rooted binary network satisfy CF-detectability on all induced 4-taxon networks, then
for levels `α_m → 0` of the cut test with `log(1/α_m) = o(m)`, for any `β > 0` and `0 ≤ δ < 2`, any exact
distance-based tree building method and any selection of maximum likelihood topologies, the
TINNiK algorithm on `m` independent gene trees infers the tree of blobs with probability tending to
one.

The proof follows the paper: on an event of probability tending to one the star test rejects on all
4-taxon sets, and the cut test rejects exactly on the sets with no cut-edge split on their induced network,
whose maximum likelihood topology is otherwise that split; the rule's closure then gives the B-quartets
and the quartet distance is the quartet metrization of the tree of blobs, which has branches of length at
least `2`, so that the cutoff `δ` has no effect.

Departure from the paper: the paper gets `CF ≠ (1/3, 1/3, 1/3)` by a further genericity argument using the
analyticity of the NMSC parametrization, which this project does not build. It is not needed:
CF-detectability already gives it, since a strictly cut CF has two different entries, and so does a non-cut
one.

The paper's comparison of the test distribution with `χ²₁` at the growing cutoffs `m d / 2` does not
follow from weak convergence (E10 of the report), and it says `μ₀ → ∞` where anomalous strictly cut CFs
have `μ₀ → -∞`. It is repaired in `QuartetTests.cutTest_alternative`, by the pointwise domination of the
test distribution by `Z²`, and in `QuartetTests.cutTest_null`. -/
theorem theorem4_of_detectable [Fintype V] [Fintype E] {N : RootedNetwork V E X}
    (hN : N.IsPhylogenetic) (hX : 4 ≤ Fintype.card X) {θ : MetricData E}
    (hθ : N.IsMetric θ) (hdet : External.AllmanEtAl2023.CFDetectable N (nmscCF N θ 0))
    {α : ℕ → ℝ} (hα : ∀ m, 0 < α m) (hα₀ : Tendsto α atTop (𝓝 0))
    (hαlog : Tendsto (fun m : ℕ => Real.log (α m) / m) atTop (𝓝 0))
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
    (tests_correct hN hX hθ hρ hdet hα hα₀ hαlog hβ hml)

/-- **Theorem 4** (`tinnik:theorem4`), conditional on CF-detectability for generic parameters
(`External.AllmanEtAl2023.Corollary1`). For generic numerical parameters on a binary network there is a
sequence `α_m → 0` such that for any `β > 0` and `2 > δ ≥ 0`, the TINNiK algorithm using the cut test on
`m` independent gene trees from the NMSC infers the tree of blobs with probability tending to one.

The sequence `α_m` is the upper tail of `χ²₁` at `log m`, which does not depend on the network or the
parameters: this is stronger than the statement of the paper, whose `α_m` is built from the unknown limits
`d` of the statistics. ECToBlob's Remark 8.3 makes the same observation. That `N` is binary is needed only
for the hypothesis `Corollary1` to hold, not by this proof. -/
theorem theorem4 [Fintype V] [Fintype E] {N : RootedNetwork V E X}
    (hN : N.IsPhylogenetic) (hX : 4 ≤ Fintype.card X)
    (hCor : External.AllmanEtAl2023.Corollary1 N) :
    ∃ A : Set (MetricData E), External.AllmanEtAl2023.IsGenericNull N A ∧
      ∀ θ, N.IsMetric θ → θ ∉ A →
        ∃ α : ℕ → ℝ, Tendsto α atTop (𝓝 0) ∧ (∀ m, 0 < α m) ∧
          ∀ (β δ : ℝ), 0 < β → 0 ≤ δ → δ < 2 →
          ∀ (M : TreeBuilder X), IsExactBuilder M →
          ∀ (ml : (QuartetTree X → ℝ) → Finset X → QuartetTree X), IsMLSelection ml →
            Tendsto (fun m => iidProb (geneTreeDist N θ 0) m fun ω =>
              tinnik ml (α m) β δ M (quartetCount unroot ω) = treeOfBlobs N) atTop (𝓝 1) := by
  refine ⟨{θ | N.IsMetric θ ∧ ¬ External.AllmanEtAl2023.CFDetectable N (nmscCF N θ 0)}, hCor,
    fun θ hθ hA => ?_⟩
  have hdet : External.AllmanEtAl2023.CFDetectable N (nmscCF N θ 0) := by
    by_contra hn
    exact hA ⟨hθ, hn⟩
  refine ⟨fun m => chiSqOneTail (Real.log m), QuartetTests.tendsto_chiSqOneTail_log,
    fun m => QuartetTests.chiSqOneTail_pos _, fun β δ hβ hδ hδ₂ M hM ml hml => ?_⟩
  exact theorem4_of_detectable hN hX hθ hdet (fun m => QuartetTests.chiSqOneTail_pos _)
    QuartetTests.tendsto_chiSqOneTail_log QuartetTests.tendsto_log_chiSqOneTail_log hβ hδ₂ hM hml

end TINNiK
