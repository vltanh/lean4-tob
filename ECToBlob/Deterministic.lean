module

public import Basic.Phylogenetics.PendantCuts
public import ECToBlob.FalseEdge
public import ECToBlob.Section5
public import ECToBlob.Section6

/-!
# ECToBlob §8: the deterministic core of the proof of Theorem 8.2

If the combined tests behave as the proof of Theorem 8.2 says they do on a table `c` of quartet
counts, then the algorithm outputs the tree of blobs. The conditions on the table (`Run`) are per
quartet, not per run of the algorithm, so one event covers all the possible intermediate trees.

The steps are those of the paper's proof, with the corrections listed at `ECToBlob.theorem8_2`:

* Step 3 keeps the edges of the tree of blobs, and each edge it keeps has a nonuniform quartet
  (`Run.treeOfBlobs_subset_afterStar`, `Run.exists_not_uniform`);
* a false edge that Step 3 keeps has a quartet off the T1 null, in the multipartition of `T₀`, so in
  the quartets of all types (`Run.exists_not_t1Null`), and is rejected (`Run.edgeT1P_lt`), while an
  edge of the tree of blobs is not rejected (`Run.edgeT1P_gt`). Hence Step 7 contracts only false
  edges as long as there are any (`Run.treeOfBlobs_subset_contractStep`);
* the overall p-value rejects exactly the trees with a false edge (`Run.treeT1P_lt`,
  `Run.treeT1P_gt`), so both selection rules select the first tree without one, which is the tree of
  blobs.

API: `CombineBounds`, `T1Null`, `Run`, `ectoblob_eq_treeOfBlobs`, `exists_combineBounds`.
-/

@[expose] public noncomputable section

open Phylogenetics Phylogenetics.RootedNetwork Finset Filter Topology
open scoped Classical

namespace ECToBlob.Deterministic

open ECToBlob.FalseEdge

variable {V E X : Type*} [Fintype X] [DecidableEq X]

/-- The T1 null hypothesis `p_s ≥ p_{s'} = p_{s''}` at the quartet tree `s`. -/
def T1Null (p : QuartetTree X → ℝ) (s : QuartetTree X) : Prop :=
  (∀ r ∈ s.alternatives, p r ≤ p s) ∧ ∀ r ∈ s.alternatives, ∀ r' ∈ s.alternatives, p r = p r'

/-- What the combined p-values do at a level `τ`, for multisets of p-values with at most `K`
elements: one p-value below `η` rejects, and all p-values above `τ` do not reject. For the Cauchy
combinations the p-values must stay below `1 - δ`. -/
structure CombineBounds (m : TestCorrection) (K : ℕ) (δ τ η : ℝ) : Prop where
  lt : ∀ P : Multiset ℝ, (∀ x ∈ P, 0 ≤ x ∧ x ≤ 1) → Multiset.card P ≤ K → (∃ x ∈ P, x < η) →
    ((m = .cauchy ∨ m = .cbc) → ∀ x ∈ P, x ≤ 1 - δ) → combineP m P < τ
  gt : ∀ P : Multiset ℝ, (∀ x ∈ P, 0 ≤ x ∧ x ≤ 1) → (∀ x ∈ P, τ < x) →
    ((m = .cauchy ∨ m = .cbc) → ∀ x ∈ P, x ≤ 1 - δ) → τ < combineP m P

theorem CombineBounds.gt_map {m : TestCorrection} {K : ℕ} {δ τ η : ℝ}
    (h : CombineBounds m K δ τ η) {ι : Type*} (Q : Finset ι) (f : ι → ℝ)
    (h01 : ∀ s ∈ Q, 0 ≤ f s ∧ f s ≤ 1) (hgt : ∀ s ∈ Q, τ < f s)
    (hle : (m = .cauchy ∨ m = .cbc) → ∀ s ∈ Q, f s ≤ 1 - δ) : τ < combineP m (Q.val.map f) := by
  refine h.gt _ ?_ ?_ ?_
  · intro x hx
    obtain ⟨s, hs, rfl⟩ := Multiset.mem_map.1 hx
    exact h01 s hs
  · intro x hx
    obtain ⟨s, hs, rfl⟩ := Multiset.mem_map.1 hx
    exact hgt s hs
  · intro hm x hx
    obtain ⟨s, hs, rfl⟩ := Multiset.mem_map.1 hx
    exact hle hm s hs

theorem CombineBounds.lt_map {m : TestCorrection} {K : ℕ} {δ τ η : ℝ}
    (h : CombineBounds m K δ τ η) {ι : Type*} [Fintype ι] (hK : Fintype.card ι ≤ K) (Q : Finset ι)
    (f : ι → ℝ) (h01 : ∀ s ∈ Q, 0 ≤ f s ∧ f s ≤ 1) (hlt : ∃ s ∈ Q, f s < η)
    (hle : (m = .cauchy ∨ m = .cbc) → ∀ s ∈ Q, f s ≤ 1 - δ) : combineP m (Q.val.map f) < τ := by
  refine h.lt _ ?_ ?_ ?_ ?_
  · intro x hx
    obtain ⟨s, hs, rfl⟩ := Multiset.mem_map.1 hx
    exact h01 s hs
  · rw [Multiset.card_map]
    exact (Finset.card_le_univ Q).trans hK
  · obtain ⟨s, hs, hsη⟩ := hlt
    exact ⟨f s, Multiset.mem_map_of_mem _ hs, hsη⟩
  · intro hm x hx
    obtain ⟨s, hs, rfl⟩ := Multiset.mem_map.1 hx
    exact hle hm s hs

/-- A run of the algorithm on a table `c` on which every test behaves as it should. -/
structure Run (N : RootedNetwork V E X) (p : QuartetTree X → ℝ) (T₀ : Finset (Finset X))
    (o : ECToBlobOptions) (α β δ ηα ηβ : ℝ) (c : QuartetTree X → ℝ) : Prop where
  phylo : N.IsPhylogenetic
  forward : Assumption1Forward N p
  converse : Assumption1Converse N p
  sum : ∀ s : QuartetTree X, ∑ r ∈ treesOn s.taxa, p r = 1
  resolution : IsResolutionOf T₀ (treeOfBlobs N)
  comb_α : CombineBounds o.testCo (Fintype.card (QuartetTree X)) δ α ηα
  comb_β : CombineBounds o.testCo (Fintype.card (QuartetTree X)) δ β ηβ
  star_mem : ∀ q : Finset X, q.card = 4 →
    0 ≤ starPValue o.starTest c q ∧ starPValue o.starTest c q ≤ 1
  t1_mem : ∀ s : QuartetTree X, 0 ≤ t1PValue c s ∧ t1PValue c s ≤ 1
  star_null : ∀ q : Finset X, q.card = 4 → IsUniformOn p q → β < starPValue o.starTest c q
  star_alt : ∀ q : Finset X, q.card = 4 → ¬ IsUniformOn p q → starPValue o.starTest c q < ηβ
  t1_null : ∀ s : QuartetTree X, T1Null p s → α < t1PValue c s
  t1_alt : ∀ s : QuartetTree X, ¬ T1Null p s → t1PValue c s < ηα
  star_le : (o.testCo = .cauchy ∨ o.testCo = .cbc) → ∀ q : Finset X, q.card = 4 →
    starPValue o.starTest c q ≤ 1 - δ
  t1_le : (o.testCo = .cauchy ∨ o.testCo = .cbc) → ∀ s : QuartetTree X, t1PValue c s ≤ 1 - δ

/-! ### Trees and sides -/

omit [DecidableEq X] in
theorem nonempty_of_mem_tree [DecidableEq X] {T : Finset (Finset X)} (hT : IsUnrootedTree T)
    {A : Finset X} (hA : A ∈ T) : A.Nonempty ∧ Aᶜ.Nonempty := by
  obtain ⟨H, hH, rfl⟩ := hT
  have hne : ∀ B ∈ H, B ≠ univ → B.Nonempty ∧ Bᶜ.Nonempty := by
    intro B hB hBu
    refine ⟨hH.2.2.1 B hB, ?_⟩
    rwa [Finset.nonempty_iff_ne_empty, Ne, Finset.compl_eq_empty_iff]
  simp only [unroot, mem_union, mem_erase, mem_image] at hA
  rcases hA with ⟨hAu, hAH⟩ | ⟨B, ⟨hBu, hBH⟩, rfl⟩
  · exact hne A hAH hAu
  · obtain ⟨h₁, h₂⟩ := hne B hBH hBu
    exact ⟨h₂, by simpa using h₁⟩

/-- The tree of blobs is closed under complements. -/
theorem compl_mem_treeOfBlobs {N : RootedNetwork V E X} {A : Finset X} (hA : A ∈ treeOfBlobs N) :
    Aᶜ ∈ treeOfBlobs N := by
  obtain ⟨_, h₁, h₂, h₃⟩ := mem_filter.1 hA
  refine mem_filter.2 ⟨mem_univ _, h₂, by simpa using h₁, ?_⟩
  rw [Finset.coe_compl]
  exact (hasCutSplit_compl N _).2 h₃

/-- The pendant edges of a tree are in the tree of blobs. -/
theorem mem_treeOfBlobs_of_not_internal {N : RootedNetwork V E X} (hN : N.IsPhylogenetic)
    {A : Finset X} (h₁ : A.Nonempty) (h₂ : Aᶜ.Nonempty) (h : ¬ (2 ≤ A.card ∧ 2 ≤ Aᶜ.card)) :
    A ∈ treeOfBlobs N := by
  have hcard₁ : 0 < A.card := Finset.card_pos.2 h₁
  have hcard₂ : 0 < Aᶜ.card := Finset.card_pos.2 h₂
  by_cases hA : A.card = 1
  · obtain ⟨x, rfl⟩ := Finset.card_eq_one.1 hA
    refine mem_filter.2 ⟨mem_univ _, h₁, h₂, ?_⟩
    rw [Finset.coe_singleton]
    exact hasSingletonCut N hN x
  · have hA' : Aᶜ.card = 1 := by omega
    obtain ⟨x, hx⟩ := Finset.card_eq_one.1 hA'
    have : Aᶜ ∈ treeOfBlobs N := by
      refine mem_filter.2 ⟨mem_univ _, h₂, by simpa using h₁, ?_⟩
      rw [hx, Finset.coe_singleton]
      exact hasSingletonCut N hN x
    simpa using compl_mem_treeOfBlobs this

/-- A side of the tree of blobs is a cut split of the network induced on each quartet it resolves.
-/
theorem inducedCutSplit_of_mem {N : RootedNetwork V E X} (hN : N.IsPhylogenetic) {A : Finset X}
    (hA : A ∈ treeOfBlobs N) {s : QuartetTree X} (hs : A ∩ s.taxa ∈ s.val) :
    InducedCutSplit N s := by
  obtain ⟨_, _, _, hcut⟩ := mem_filter.1 hA
  refine ⟨_, hs, ?_⟩
  have hcard₂ : (A ∩ s.taxa).card = 2 := s.2.2.1 _ hs
  have hcard₄ : s.taxa.card = 4 := s.card_taxa
  have hne₁ : ((s.taxa : Set X) ∩ (A : Set X)).Nonempty := by
    obtain ⟨x, hx⟩ : (A ∩ s.taxa).Nonempty := Finset.card_pos.1 (by omega)
    exact ⟨x, by simpa [and_comm] using hx⟩
  have hne₂ : ((s.taxa : Set X) \ (A : Set X)).Nonempty := by
    have : (s.taxa \ A).Nonempty := by
      by_contra hemp
      rw [Finset.not_nonempty_iff_eq_empty, Finset.sdiff_eq_empty_iff_subset] at hemp
      rw [Finset.inter_eq_right.2 hemp] at hcard₂
      omega
    obtain ⟨x, hx⟩ := this
    exact ⟨x, by simpa using hx⟩
  refine (hasCutSplitOn_congr ?_).1 (hcut.hasCutSplitOn hN hne₁ hne₂)
  ext x
  simp only [Set.mem_inter_iff, Finset.mem_coe, mem_inter]
  tauto

/-! ### Facts about concordance factors -/

/-- A quartet tree is one of the trees on its taxa. -/
theorem mem_treesOn_taxa (s : QuartetTree X) : s ∈ treesOn s.taxa := by
  simp [treesOn]

omit [DecidableEq X] in
theorem T1Null_of_strict [DecidableEq X] {p : QuartetTree X → ℝ} {s : QuartetTree X}
    (h : IsT1Strict p s) : T1Null p s :=
  ⟨fun r hr => (h.1 r hr).le, h.2⟩

theorem not_uniform_of_strict {p : QuartetTree X → ℝ} {s : QuartetTree X} (h : IsT1Strict p s) :
    ¬ IsUniformOn p s.taxa := by
  intro hu
  obtain ⟨r, hr⟩ : s.alternatives.Nonempty := by
    rw [← Finset.card_pos, s.card_alternatives]
    omega
  have hr' := (mem_filter.1 hr).2
  have h₁ := hu r (by simp [treesOn, hr'.1])
  have h₂ := hu s (mem_treesOn_taxa s)
  have := h.1 r hr
  linarith

/-- A null quartet tree with no strict inequality has equal concordance factors, which sum to one.
-/
theorem not_t1Null {p : QuartetTree X → ℝ} {s : QuartetTree X}
    (hsum : ∑ r ∈ treesOn s.taxa, p r = 1) (h₁ : ¬ IsT1Strict p s) (h₂ : ¬ IsUniformOn p s.taxa) :
    ¬ T1Null p s := by
  rintro ⟨hle, heq⟩
  have hsplit : treesOn s.taxa = insert s s.alternatives := by
    ext r
    simp only [treesOn, QuartetTree.alternatives, mem_filter, mem_univ, true_and, mem_insert]
    constructor
    · intro hr
      by_cases hrs : r = s
      · exact Or.inl hrs
      · exact Or.inr ⟨hr, hrs⟩
    · rintro (rfl | hr)
      · rfl
      · exact hr.1
  have hnot : s ∉ s.alternatives := by simp [QuartetTree.alternatives]
  have hstrict : ¬ ∀ r ∈ s.alternatives, p r < p s := fun h => h₁ ⟨h, heq⟩
  push Not at hstrict
  obtain ⟨r, hr, hrs⟩ := hstrict
  have hrs' : p r = p s := le_antisymm (hle r hr) hrs
  have hall : ∀ r' ∈ s.alternatives, p r' = p s := fun r' hr' => (heq r' hr' r hr).trans hrs'
  have hcard := s.card_alternatives
  have hsum' : p s + ∑ r' ∈ s.alternatives, p r' = 1 := by
    rw [← Finset.sum_insert hnot, ← hsplit]
    exact hsum
  rw [Finset.sum_congr rfl hall, Finset.sum_const, hcard] at hsum'
  simp only [nsmul_eq_mul] at hsum'
  apply h₂
  intro r' hr'
  rw [hsplit, mem_insert] at hr'
  rcases hr' with rfl | hr'
  · push_cast at hsum'
    linarith
  · rw [hall r' hr']
    push_cast at hsum'
    linarith

/-! ### The run -/

section Run

variable {N : RootedNetwork V E X} {p : QuartetTree X → ℝ} {T₀ : Finset (Finset X)}
  {o : ECToBlobOptions} {α β δ ηα ηβ : ℝ} {c : QuartetTree X → ℝ}

theorem Run.nonempty_of_mem (R : Run N p T₀ o α β δ ηα ηβ c) {T : Finset (Finset X)} (hT : T ⊆ T₀)
    {A : Finset X} (hA : A ∈ T) : A.Nonempty ∧ Aᶜ.Nonempty :=
  nonempty_of_mem_tree R.resolution.1 (hT hA)

/-- A quartet of a cut side is under the T1 null. -/
theorem Run.t1Null_of_mem (R : Run N p T₀ o α β δ ηα ηβ c) {A : Finset X}
    (hA : A ∈ treeOfBlobs N) {s : QuartetTree X} (hs : A ∩ s.taxa ∈ s.val) : T1Null p s :=
  T1Null_of_strict (R.forward.t1 s (inducedCutSplit_of_mem R.phylo hA hs))

/-- Combined star p-value: all quartets uniform. -/
theorem Run.edgeStarP_gt (R : Run N p T₀ o α β δ ηα ηβ c) {A : Finset X}
    (h : ∀ s ∈ multipartitionQuartets T₀ A, IsUniformOn p s.taxa) : β < edgeStarP o c T₀ A :=
  R.comb_β.gt_map _ _ (fun s _ => R.star_mem _ s.card_taxa)
    (fun s hs => R.star_null _ s.card_taxa (h s hs)) (fun hm s _ => R.star_le hm _ s.card_taxa)

/-- Combined star p-value: some quartet not uniform. -/
theorem Run.edgeStarP_lt (R : Run N p T₀ o α β δ ηα ηβ c) {A : Finset X}
    (h : ∃ s ∈ multipartitionQuartets T₀ A, ¬ IsUniformOn p s.taxa) : edgeStarP o c T₀ A < β := by
  obtain ⟨s, hs, hu⟩ := h
  exact R.comb_β.lt_map le_rfl _ _ (fun s _ => R.star_mem _ s.card_taxa)
    ⟨s, hs, R.star_alt _ s.card_taxa hu⟩ (fun hm s _ => R.star_le hm _ s.card_taxa)

theorem mem_contractSides {T C : Finset (Finset X)} {A : Finset X} :
    A ∈ contractSides T C ↔ A ∈ T ∧ A ∉ C ∧ Aᶜ ∉ C := by
  simp [contractSides]

theorem mem_internalSides {T : Finset (Finset X)} {A : Finset X} :
    A ∈ internalSides T ↔ A ∈ T ∧ 2 ≤ A.card ∧ 2 ≤ Aᶜ.card := by
  simp [internalSides]

theorem Run.split_family (R : Run N p T₀ o α β δ ηα ηβ c) {A : Finset X}
    (hA : A ∈ internalSides T₀) :
    IsSplitFamily T₀ := by
  obtain ⟨_, h, _⟩ := mem_internalSides.1 hA
  exact (isUnrootedTree_iff (h.trans (Finset.card_le_univ A)) T₀).1 R.resolution.1

/-- Step 3 does not contract an edge of the tree of blobs: its quartets are nonuniform. -/
theorem Run.treeOfBlobs_subset_afterStar (R : Run N p T₀ o α β δ ηα ηβ c) :
    treeOfBlobs N ⊆ afterStar o β c T₀ := by
  have key : ∀ A ∈ treeOfBlobs N,
      A ∉ (internalSides T₀).filter fun A => β < edgeStarP o c T₀ A := by
    intro A hA hmem
    obtain ⟨hint, hβ⟩ := mem_filter.1 hmem
    obtain ⟨_, h₂, h₂'⟩ := mem_internalSides.1 hint
    obtain ⟨s, hs⟩ := exists_mem_multipartitionQuartets (R.split_family hint) h₂ h₂'
    have hA' : A ∩ s.taxa ∈ s.val := (mem_filter.1 (mem_filter.1 hs).1).2
    have hstrict := R.forward.t1 s (inducedCutSplit_of_mem R.phylo hA hA')
    exact absurd hβ (not_lt_of_gt (R.edgeStarP_lt ⟨s, hs, not_uniform_of_strict hstrict⟩))
  intro A hA
  exact mem_contractSides.2 ⟨R.resolution.2 hA, key A hA, key _ (compl_mem_treeOfBlobs hA)⟩

theorem afterStar_subset : afterStar o β c T₀ ⊆ T₀ := Finset.filter_subset _ _

/-- An edge that Step 3 keeps has a nonuniform quartet. -/
theorem Run.exists_not_uniform (R : Run N p T₀ o α β δ ηα ηβ c) {T : Finset (Finset X)}
    (hT : T ⊆ afterStar o β c T₀) {A : Finset X} (hA : A ∈ internalSides T) :
    ∃ s ∈ multipartitionQuartets T₀ A, ¬ IsUniformOn p s.taxa := by
  obtain ⟨hAT, h₂, h₂'⟩ := mem_internalSides.1 hA
  obtain ⟨hAT₀, hnot, _⟩ := mem_contractSides.1 (hT hAT)
  by_contra hcon
  push Not at hcon
  exact hnot (mem_filter.2 ⟨mem_internalSides.2 ⟨hAT₀, h₂, h₂'⟩, R.edgeStarP_gt hcon⟩)

/-- A false edge that Step 3 keeps has a quartet off the T1 null: `falseEdge_witness`, which gives
one neither a cut split nor a trivial 4-blob, so by the converse of Assumption 1 neither (5.2) nor
(5.1). -/
theorem Run.exists_not_t1Null (R : Run N p T₀ o α β δ ηα ηβ c) {T : Finset (Finset X)}
    (hT : T ⊆ afterStar o β c T₀) {A : Finset X} (hA : A ∈ internalSides T)
    (hAB : A ∉ treeOfBlobs N) : ∃ s ∈ multipartitionQuartets T₀ A, ¬ T1Null p s := by
  obtain ⟨hAT, h₂, h₂'⟩ := mem_internalSides.1 hA
  have hAT₀ := afterStar_subset (hT hAT)
  obtain ⟨s₀, hs₀, hu₀⟩ := R.exists_not_uniform hT hA
  obtain ⟨s, hs, hR, hTr⟩ := falseEdge_witness R.phylo R.resolution
    (mem_internalSides.2 ⟨hAT₀, h₂, h₂'⟩) hAB
    ⟨s₀, hs₀, fun htr => hu₀ (R.forward.star _ s₀.card_taxa htr)⟩
  exact ⟨s, hs, not_t1Null (R.sum s) (R.converse.t1 s hR) (R.converse.star _ s.card_taxa hTr)⟩

theorem multipartitionQuartets_subset_edgeQuartets {T : Finset (Finset X)} (hT : T ⊆ T₀)
    (A : Finset X) : multipartitionQuartets T₀ A ⊆ edgeQuartets o T₀ T A := by
  intro s hs
  obtain ⟨h₁, h₂, h₃⟩ := mem_filter.1 hs
  unfold edgeQuartets
  cases o.qType with
  | bi => exact h₁
  | quad => exact hs
  | mul =>
    refine mem_filter.2 ⟨h₁, ?_, ?_⟩
    · rintro ⟨C, hC, hrest⟩
      exact h₂ ⟨C, hT hC, hrest⟩
    · rintro ⟨C, hC, hrest⟩
      exact h₃ ⟨C, hT hC, hrest⟩

theorem mem_of_mem_edgeQuartets {T : Finset (Finset X)} {A : Finset X} {s : QuartetTree X}
    (hs : s ∈ edgeQuartets o T₀ T A) : A ∩ s.taxa ∈ s.val := by
  unfold edgeQuartets at hs
  revert hs
  cases o.qType with
  | bi => exact fun hs => (mem_filter.1 hs).2
  | mul => exact fun hs => (mem_filter.1 (mem_filter.1 hs).1).2
  | quad => exact fun hs => (mem_filter.1 (mem_filter.1 hs).1).2

/-- Edges of the tree of blobs are not rejected. -/
theorem Run.edgeT1P_gt (R : Run N p T₀ o α β δ ηα ηβ c) (T : Finset (Finset X)) {A : Finset X}
    (hA : A ∈ treeOfBlobs N) : α < edgeT1P o c T₀ T A :=
  R.comb_α.gt_map _ _ (fun s _ => R.t1_mem s)
    (fun s hs => R.t1_null s (R.t1Null_of_mem hA (mem_of_mem_edgeQuartets hs)))
    (fun hm s _ => R.t1_le hm s)

/-- False edges are rejected. -/
theorem Run.edgeT1P_lt (R : Run N p T₀ o α β δ ηα ηβ c) {T : Finset (Finset X)}
    (hT : T ⊆ afterStar o β c T₀) {A : Finset X} (hA : A ∈ internalSides T)
    (hAB : A ∉ treeOfBlobs N) : edgeT1P o c T₀ T A < α := by
  obtain ⟨s, hs, hn⟩ := R.exists_not_t1Null hT hA hAB
  exact R.comb_α.lt_map le_rfl _ _ (fun s _ => R.t1_mem s)
    ⟨s, multipartitionQuartets_subset_edgeQuartets (hT.trans afterStar_subset) A hs, R.t1_alt s hn⟩
    (fun hm s _ => R.t1_le hm s)

/-- A tree with a false edge is rejected. -/
theorem Run.treeT1P_lt (R : Run N p T₀ o α β δ ηα ηβ c) {T : Finset (Finset X)}
    (hT : T ⊆ afterStar o β c T₀) {A : Finset X} (hA : A ∈ internalSides T)
    (hAB : A ∉ treeOfBlobs N) : treeT1P o c T < α := by
  obtain ⟨s, hs, hn⟩ := R.exists_not_t1Null hT hA hAB
  refine R.comb_α.lt_map le_rfl _ _ (fun s _ => R.t1_mem s) ⟨s, ?_, R.t1_alt s hn⟩
    (fun hm s _ => R.t1_le hm s)
  exact mem_filter.2
    ⟨mem_univ _, A, (mem_internalSides.1 hA).1, (mem_filter.1 (mem_filter.1 hs).1).2⟩

/-- A tree without false edges is not rejected. -/
theorem Run.treeT1P_gt (R : Run N p T₀ o α β δ ηα ηβ c) {T : Finset (Finset X)}
    (hT : T ⊆ treeOfBlobs N) : α < treeT1P o c T := by
  refine R.comb_α.gt_map _ _ (fun s _ => R.t1_mem s) ?_ (fun hm s _ => R.t1_le hm s)
  intro s hs
  obtain ⟨A, hA, hAs⟩ := (mem_filter.1 hs).2
  exact R.t1_null s (R.t1Null_of_mem (hT hA) hAs)

theorem contractStep_subset (T : Finset (Finset X)) : contractStep o c T₀ T ⊆ T :=
  Finset.filter_subset _ _

/-- Step 7 keeps the edges of the tree of blobs as long as there is a false edge. -/
theorem Run.treeOfBlobs_subset_contractStep (R : Run N p T₀ o α β δ ηα ηβ c)
    {T : Finset (Finset X)} (hT : T ⊆ afterStar o β c T₀) (hB : treeOfBlobs N ⊆ T) {F : Finset X}
    (hF : F ∈ internalSides T) (hFB : F ∉ treeOfBlobs N) :
    treeOfBlobs N ⊆ contractStep o c T₀ T := by
  have key : ∀ A ∈ treeOfBlobs N, A ∉ (internalSides T).filter fun A =>
      ∀ B ∈ internalSides T, edgeT1P o c T₀ T A ≤ edgeT1P o c T₀ T B := by
    intro A hA hmem
    have h₀ := (mem_filter.1 hmem).2 F hF
    have h₁ := R.edgeT1P_gt T hA
    have h₂ := R.edgeT1P_lt hT hF hFB
    linarith
  intro A hA
  exact mem_contractSides.2 ⟨hB hA, key A hA, key _ (compl_mem_treeOfBlobs hA)⟩

/-- Step 7 contracts an edge. -/
theorem contractStep_ssubset {T : Finset (Finset X)} (h : (internalSides T).Nonempty) :
    contractStep o c T₀ T ⊂ T := by
  obtain ⟨A, hA, hmin⟩ := Finset.exists_min_image _ (edgeT1P o c T₀ T) h
  rw [Finset.ssubset_iff_of_subset (contractStep_subset T)]
  exact ⟨A, (mem_internalSides.1 hA).1,
    fun hmem => (mem_contractSides.1 hmem).2.1 (mem_filter.2 ⟨hA, hmin⟩)⟩

theorem treeSeq_succ (i : ℕ) :
    treeSeq o β c T₀ (i + 1) = contractStep o c T₀ (treeSeq o β c T₀ i) :=
  Function.iterate_succ_apply' _ _ _

theorem treeSeq_anti {i j : ℕ} (h : i ≤ j) : treeSeq o β c T₀ j ⊆ treeSeq o β c T₀ i := by
  induction j, h using Nat.le_induction with
  | base => exact subset_rfl
  | succ j _ ih =>
    rw [treeSeq_succ]
    exact (contractStep_subset _).trans ih

theorem treeSeq_subset_afterStar (i : ℕ) : treeSeq o β c T₀ i ⊆ afterStar o β c T₀ :=
  treeSeq_anti (Nat.zero_le i)

/-- The sequence of trees reaches a star tree. -/
theorem exists_internalSides_eq_empty : ∃ i, internalSides (treeSeq o β c T₀ i) = ∅ := by
  by_contra hcon
  push Not at hcon
  have hcard : ∀ i, (treeSeq o β c T₀ i).card + i ≤ (treeSeq o β c T₀ 0).card := by
    intro i
    induction i with
    | zero => omega
    | succ i ih =>
      rw [treeSeq_succ]
      have := Finset.card_lt_card
        (contractStep_ssubset (o := o) (c := c) (T₀ := T₀) (hcon i))
      omega
  have := hcard ((treeSeq o β c T₀ 0).card + 1)
  omega

/-- **The deterministic core of Theorem 8.2.** On a table on which every test behaves as it should,
the algorithm outputs the tree of blobs. -/
theorem ectoblob_eq_treeOfBlobs (R : Run N p T₀ o α β δ ηα ηβ c) :
    ectoblob o α β c T₀ = treeOfBlobs N := by
  have hex : ∃ i, ¬ ∃ A ∈ internalSides (treeSeq o β c T₀ i), A ∉ treeOfBlobs N := by
    obtain ⟨i, hi⟩ := exists_internalSides_eq_empty (o := o) (β := β) (c := c) (T₀ := T₀)
    exact ⟨i, by simp [hi]⟩
  let i₀ := Nat.find hex
  have hspec : ¬ ∃ A ∈ internalSides (treeSeq o β c T₀ i₀), A ∉ treeOfBlobs N := Nat.find_spec hex
  have hbefore : ∀ i, i < i₀ → ∃ A ∈ internalSides (treeSeq o β c T₀ i), A ∉ treeOfBlobs N :=
    fun i hi => not_not.1 (Nat.find_min hex hi)
  have hsub : ∀ i, i ≤ i₀ → treeOfBlobs N ⊆ treeSeq o β c T₀ i := by
    intro i
    induction i with
    | zero => exact fun _ => R.treeOfBlobs_subset_afterStar
    | succ i ih =>
      intro hi
      obtain ⟨F, hF, hFB⟩ := hbefore i (by omega)
      rw [treeSeq_succ]
      exact R.treeOfBlobs_subset_contractStep (treeSeq_subset_afterStar i) (ih (by omega)) hF hFB
  have hsub₀ : treeSeq o β c T₀ i₀ ⊆ T₀ := (treeSeq_subset_afterStar i₀).trans afterStar_subset
  have heq : treeSeq o β c T₀ i₀ = treeOfBlobs N := by
    refine Finset.Subset.antisymm ?_ (hsub i₀ le_rfl)
    intro A hA
    by_contra hAB
    by_cases hint : 2 ≤ A.card ∧ 2 ≤ Aᶜ.card
    · exact hspec ⟨A, mem_internalSides.2 ⟨hA, hint⟩, hAB⟩
    · obtain ⟨h₁, h₂⟩ := R.nonempty_of_mem hsub₀ hA
      exact hAB (mem_treeOfBlobs_of_not_internal R.phylo h₁ h₂ hint)
  have hle : ∀ i, i₀ ≤ i → treeSeq o β c T₀ i ⊆ treeOfBlobs N := fun i hi => by
    rw [← heq]
    exact treeSeq_anti hi
  have hlt : ∀ i, i < i₀ → treeT1P o c (treeSeq o β c T₀ i) < α := by
    intro i hi
    obtain ⟨F, hF, hFB⟩ := hbefore i hi
    exact R.treeT1P_lt (treeSeq_subset_afterStar i) hF hFB
  have hgt : ∀ i, i₀ ≤ i → α < treeT1P o c (treeSeq o β c T₀ i) := fun i hi =>
    R.treeT1P_gt (hle i hi)
  have hlast : i₀ ≤ lastIteration o β c T₀ := by
    have hmem : lastIteration o β c T₀ ∈ {i | internalSides (treeSeq o β c T₀ i) = ∅} :=
      Nat.sInf_mem exists_internalSides_eq_empty
    refine Nat.find_min' hex ?_
    have hmem' : internalSides (treeSeq o β c T₀ (lastIteration o β c T₀)) = ∅ := hmem
    simp [hmem']
  have hsel : selectedIteration o α β c T₀ = i₀ := by
    cases hr : o.rule with
    | early =>
      simp only [selectedIteration, hr]
      refine IsLeast.csInf_eq ⟨⟨hlast, (hgt i₀ le_rfl).le⟩, ?_⟩
      rintro i ⟨_, hi⟩
      by_contra hcon
      exact absurd hi (not_le_of_gt (hlt i (by omega)))
    | late =>
      simp only [selectedIteration, hr]
      split_ifs with h
      · obtain ⟨i, _, hi⟩ := h
        have hipos : i < i₀ := by
          by_contra hcon
          exact absurd hi (not_lt_of_gt (hgt i (by omega)))
        have hset : IsGreatest {i | i ≤ lastIteration o β c T₀ ∧
            treeT1P o c (treeSeq o β c T₀ i) < α} (i₀ - 1) := by
          refine ⟨⟨by omega, hlt _ (by omega)⟩, ?_⟩
          rintro j ⟨hj, hjα⟩
          by_contra hcon
          exact absurd hjα (not_lt_of_gt (hgt j (by omega)))
        rw [hset.csSup_eq]
        omega
      · push Not at h
        by_contra hcon
        exact absurd (hlt 0 (by omega)) (not_lt_of_ge (h 0 (Nat.zero_le _)))
  rw [ectoblob, hsel]
  exact heq

end Run

/-! ### The combination bounds from Lemma 6.1 -/

/-- The level `τ` and the threshold `η` of `CombineBounds`, from Lemma 6.1. The threshold is a
constant times the level: the bound `B(K, η, 1 - δ)` is equivalent to a constant times `K η` as `η →
0`, so with a small constant it is below `τ`. (The paper's proof takes `B(K, η_n, 1 - δ) ∼ β_n`,
which does not give `B(K, η_n, 1 - δ) < β_n`: slack is needed.) For Bonferroni and BBC, whose
p-values may equal `1` at a degenerate null, this is the bound of `combineP_le_two_mul` with no
condition on the maximum. -/
theorem exists_combineBounds (m : TestCorrection) (K : ℕ) {δ : ℝ} (hδ : 0 < δ) (hδ' : δ < 1) :
    ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ᶠ τ in 𝓝[>] (0 : ℝ), CombineBounds m K δ τ (c₀ * τ) := by
  obtain ⟨B, hB, hk, hη, hD, hasym⟩ := lemma6_1_part1 m
  have hK' : 1 ≤ max K 1 := le_max_right _ _
  have hKK : K ≤ max K 1 := le_max_left _ _
  have hK'R : (1 : ℝ) ≤ (max K 1 : ℕ) := by exact_mod_cast hK'
  have hc : 1 ≤ boundConstant m := by cases m <;> simp [boundConstant]
  set v : ℝ := boundConstant m * ((max K 1 : ℕ) : ℝ) with hv
  have hv1 : ((max K 1 : ℕ) : ℝ) ≤ v := by
    rw [hv]
    nlinarith
  have hv0 : 0 < v := by linarith
  have hc₀ : 0 < 1 / (4 * v) := by positivity
  have hev : ∀ᶠ η in 𝓝[>] (0 : ℝ), B (max K 1) η (1 - δ) ≤ 2 * (v * η) := by
    have h := (hasym (max K 1) (1 - δ) hK' (by linarith) (by linarith)).isLittleO.def one_pos
    filter_upwards [h, self_mem_nhdsWithin] with η hη₁ hηpos
    have hpos : 0 < boundConstant m * ((max K 1 : ℕ) : ℝ) * η := mul_pos hv0 hηpos
    simp only [Pi.sub_apply, Real.norm_eq_abs, one_mul] at hη₁
    rw [abs_of_pos hpos] at hη₁
    have := (abs_le.1 hη₁).2
    have hvη : v * η = boundConstant m * ((max K 1 : ℕ) : ℝ) * η := rfl
    linarith
  have htend : Tendsto (fun τ : ℝ => 1 / (4 * v) * τ) (𝓝[>] 0) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · have : Tendsto (fun τ : ℝ => 1 / (4 * v) * τ) (𝓝 0) (𝓝 (1 / (4 * v) * 0)) :=
        (continuous_const.mul continuous_id).tendsto 0
      rw [mul_zero] at this
      exact this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with τ hτ
      exact mul_pos hc₀ hτ
  have hsmall : ∀ᶠ τ in 𝓝[>] (0 : ℝ), 1 / (4 * v) * τ < 1 - δ := by
    have : ∀ᶠ η in 𝓝[>] (0 : ℝ), η < 1 - δ :=
      eventually_of_mem (Ioo_mem_nhdsGT (by linarith)) fun _ h => h.2
    exact htend.eventually this
  refine ⟨1 / (4 * v), hc₀, ?_⟩
  have hτ1 : ∀ᶠ τ in 𝓝[>] (0 : ℝ), τ < 1 :=
    eventually_of_mem (Ioo_mem_nhdsGT one_pos) fun _ h => h.2
  filter_upwards [htend.eventually hev, hsmall, self_mem_nhdsWithin, hτ1] with τ hτB hτη hτpos hτone
  have hτpos' : 0 < τ := hτpos
  have hηval : 2 * (v * (1 / (4 * v) * τ)) = τ / 2 := by
    field_simp
    ring
  refine ⟨?_, ?_⟩
  · -- one p-value below the threshold rejects
    intro P h01 hcard ⟨x, hx, hxη⟩ hle
    have hP : P ≠ 0 := by
      rintro rfl
      simp at hx
    have hmin₀ : 0 ≤ minP P := minP_nonneg fun p hp => (h01 p hp).1
    have hminη : minP P < 1 / (4 * v) * τ := (minP_le_of_mem hx).trans_lt hxη
    have hcard₁ : 1 ≤ Multiset.card P := Multiset.card_pos.2 hP
    have hbon : (m = .bon ∨ m = .bbc) → combineP m P < τ := by
      intro hm
      have h₁ := combineP_le_two_mul hm hP fun p hp => (h01 p hp).1
      have hcardR : ((Multiset.card P : ℕ) : ℝ) ≤ v :=
        le_trans (by exact_mod_cast hcard.trans hKK) hv1
      have h₂ : 2 * ((Multiset.card P : ℕ) : ℝ) * minP P ≤ 2 * (v * (1 / (4 * v) * τ)) := by
        have := mul_le_mul hcardR hminη.le hmin₀ hv0.le
        linarith
      rw [hηval] at h₂
      linarith
    have hcauchy : (m = .cauchy ∨ m = .cbc) → combineP m P < τ := by
      intro hm
      have hle' := hle hm
      have hP01 : ∀ p ∈ P, 0 ≤ p ∧ p < 1 := fun p hp =>
        ⟨(h01 p hp).1, (hle' p hp).trans_lt (by linarith)⟩
      have hmax₁ : maxP P ≤ 1 - δ := maxP_le_iff.2 ⟨by linarith, hle'⟩
      have hmax₀ := maxP_nonneg P
      have h₁ := hB P hP hP01
      have h₂ := hD _ (minP P) (maxP P) (1 - δ) hcard₁ hmin₀
        ((minP_le_of_mem hx).trans (le_maxP_of_mem hx)) hmax₁ (by linarith)
      have h₃ := hη _ (minP P) (1 / (4 * v) * τ) (1 - δ) hcard₁ hmin₀ hminη.le hτη.le (by linarith)
      have h₄ := hk _ (max K 1) (1 / (4 * v) * τ) (1 - δ) hcard₁ (hcard.trans hKK)
        (mul_pos hc₀ hτpos).le hτη.le (by linarith)
      rw [hηval] at hτB
      linarith
    cases m with
    | bon => exact hbon (Or.inl rfl)
    | bbc => exact hbon (Or.inr rfl)
    | cauchy => exact hcauchy (Or.inl rfl)
    | cbc => exact hcauchy (Or.inr rfl)
  · -- all p-values above the level do not reject
    intro P h01 hgt hle
    by_cases hP : P = 0
    · subst hP
      simpa [combineP] using hτone
    have hτmin : τ < minP P := hgt _ (minP_mem hP fun p hp => (h01 p hp).2)
    have hbon : (m = .bon ∨ m = .bbc) → τ < combineP m P := fun _ =>
      hτmin.trans_le (minP_le_combineP m hP h01)
    have hcauchy : (m = .cauchy ∨ m = .cbc) → τ < combineP m P := fun hm =>
      hτmin.trans_le (lemma6_1_part2 m P hP fun p hp =>
        ⟨(h01 p hp).1, (hle hm p hp).trans_lt (by linarith)⟩)
    cases m with
    | bon => exact hbon (Or.inl rfl)
    | bbc => exact hbon (Or.inr rfl)
    | cauchy => exact hcauchy (Or.inl rfl)
    | cbc => exact hcauchy (Or.inr rfl)

end ECToBlob.Deterministic
