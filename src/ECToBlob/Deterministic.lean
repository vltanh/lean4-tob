module

public import Basic.Defs
public import Basic.InducedSplits
public import Phylogenetics.Network.Cuts
public import Basic.Testing.Combining
public import Basic.Testing.Defs
public import Phylogenetics.Tree.Splits
public import ECToBlob.FalseEdge
public import ECToBlob.Section5
public import ECToBlob.Section6

/-!
# ECToBlob §8: the deterministic core of the proof of Theorem 8.2

The paper's proof of Theorem 8.2 shows that, with high probability, "all the various combination
tests computed by the algorithm correctly indicate whether edges of `T₀` should be contracted or
not" (the paper's text, line 1056). Here is what it does with that: if all these tests
come out right on a table `c` of quartet counts (`Run`, with one test per edge, `TestCorrect`), then
the algorithm outputs the tree of blobs. `src/ECToBlob/Section8.lean` proves that this holds with high
probability, test by test.

The steps are those of the end of the paper's proof (lines 1123-1158), with the corrections listed
at `ECToBlob.theorem8_2`:

* Step 3 keeps the edges of the tree of blobs, and each edge it keeps has a nonuniform quartet
  (`Run.treeOfBlobs_subset_afterStar`, `Run.exists_not_uniform`);
* "by Corollaries 4.2 and 4.3, `S^a(e)` is empty exactly when `e` is a cut-edge" (lines 1126-1127):
  the quartets of a cut edge are under the T1 null (`Run.t1Null_of_mem`), and a false edge that Step
  3 keeps has a quartet off the T1 null (`Run.exists_not_t1Null`). So it is rejected
  (`Run.edgeT1P_lt`), while an edge of the tree of blobs is not (`Run.edgeT1P_gt`). Hence Step 7
  contracts only false edges as long as there are any (`Run.treeOfBlobs_subset_contractStep`);
* the overall p-value rejects exactly the trees with a false edge (`Run.treeT1P_lt`,
  `Run.treeT1P_gt`), so both selection rules select the first tree without one, which is the tree of
  blobs.

API: `CombineBounds`, `IsT1Null`, `TestCorrect`, `Run`, `ectoblob_eq_treeOfBlobs`,
`exists_combineBounds`.
-/

@[expose] public noncomputable section

open Phylogenetics Phylogenetics.RootedNetwork Finset Filter Topology
open scoped Classical

namespace ECToBlob.Deterministic

open ECToBlob.FalseEdge

variable {V E X : Type*} [Fintype X] [DecidableEq X]

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
    (h : CombineBounds m K δ τ η) {ι : Type*} (Q : Finset ι) (hK : Q.card ≤ K) (f : ι → ℝ)
    (h01 : ∀ s ∈ Q, 0 ≤ f s ∧ f s ≤ 1) (hlt : ∃ s ∈ Q, f s < η)
    (hle : (m = .cauchy ∨ m = .cbc) → ∀ s ∈ Q, f s ≤ 1 - δ) : combineP m (Q.val.map f) < τ := by
  refine h.lt _ ?_ ?_ ?_ ?_
  · intro x hx
    obtain ⟨s, hs, rfl⟩ := Multiset.mem_map.1 hx
    exact h01 s hs
  · rw [Multiset.card_map]
    exact hK
  · obtain ⟨s, hs, hsη⟩ := hlt
    exact ⟨f s, Multiset.mem_map_of_mem _ hs, hsη⟩
  · intro hm x hx
    obtain ⟨s, hs, rfl⟩ := Multiset.mem_map.1 hx
    exact hle hm s hs

/-- A combined test comes out right on a table of counts ("correctly indicate", line 1056). Here `Q`
is its set of quartets, `Null` the null hypothesis on a quartet, `x` the combined p-value and `τ`
the level: the test does not reject if the null holds on all of `Q`, and it rejects if `S^a = {s ∈ Q
| ¬ Null s}` is not empty. -/
def TestCorrect (Null : QuartetTree X → Prop) (Q : Finset (QuartetTree X)) (τ x : ℝ) : Prop :=
  ((∀ s ∈ Q, Null s) → τ < x) ∧ ((∃ s ∈ Q, ¬ Null s) → x < τ)

/-- A run of the algorithm on a table `c` on which every test comes out right, for a network and
concordance factors `p` meeting Assumption 1: each star test of Step 3, one per edge of `T₀`; each
T1 test of Step 6, one per pair of a possible current tree `T` and an edge of `T`; and each overall
test of Steps 4 and 8, one per possible current tree. For the type `mul` the quartets of an edge
depend on the current tree, which is random (E16), so the T1 tests are indexed by all subsets of
`T₀`, which include its contractions. -/
structure Run (N : RootedNetwork V E X) (p : QuartetTree X → ℝ) (T₀ : Finset (Finset X))
    (o : ECToBlobOptions) (α β : ℝ) (c : QuartetTree X → ℝ) : Prop where
  phylo : N.IsPhylogenetic
  forward : Assumption1Forward N p
  converse : Assumption1Converse N p
  sum : ∀ s : QuartetTree X, ∑ r ∈ treesOn s.taxa, p r = 1
  resolution : IsResolutionOf T₀ (treeOfBlobs N)
  star : ∀ A ∈ internalSides T₀, TestCorrect (fun s => IsUniformOn p s.taxa)
    (multipartitionQuartets T₀ A) β (edgeStarP o c T₀ A)
  t1 : ∀ T ⊆ T₀, ∀ A ∈ internalSides T, TestCorrect (IsT1Null p) (edgeQuartets o T₀ T A) α
    (edgeT1P o c T₀ T A)
  tree : ∀ T ⊆ T₀, TestCorrect (IsT1Null p) (univ.filter fun s => Displays T s) α (treeT1P o c T)

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

/-! ### Facts about concordance factors -/

/-- A quartet tree is one of the trees on its taxa. -/
theorem mem_treesOn_taxa (s : QuartetTree X) : s ∈ treesOn s.taxa := by
  simp [treesOn]

omit [DecidableEq X] in
theorem isT1Null_of_strict [DecidableEq X] {p : QuartetTree X → ℝ} {s : QuartetTree X}
    (h : IsT1Strict p s) : IsT1Null p s :=
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
    ¬ IsT1Null p s := by
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
  {o : ECToBlobOptions} {α β : ℝ} {c : QuartetTree X → ℝ}

theorem Run.nonempty_of_mem (R : Run N p T₀ o α β c) {T : Finset (Finset X)} (hT : T ⊆ T₀)
    {A : Finset X} (hA : A ∈ T) : A.Nonempty ∧ Aᶜ.Nonempty :=
  nonempty_of_mem_tree R.resolution.1 (hT hA)

/-- A quartet of a cut side is under the T1 null. -/
theorem Run.t1Null_of_mem (R : Run N p T₀ o α β c) {A : Finset X}
    (hA : A ∈ treeOfBlobs N) {s : QuartetTree X} (hs : A ∩ s.taxa ∈ s.val) : IsT1Null p s :=
  isT1Null_of_strict (R.forward.t1 s (inducedCutSplit_of_mem R.phylo hA hs))

/-- Combined star p-value: all quartets uniform (lines 1064-1082). -/
theorem Run.edgeStarP_gt (R : Run N p T₀ o α β c) {A : Finset X} (hA : A ∈ internalSides T₀)
    (h : ∀ s ∈ multipartitionQuartets T₀ A, IsUniformOn p s.taxa) : β < edgeStarP o c T₀ A :=
  (R.star A hA).1 h

/-- Combined star p-value: some quartet not uniform (lines 1083-1116). -/
theorem Run.edgeStarP_lt (R : Run N p T₀ o α β c) {A : Finset X} (hA : A ∈ internalSides T₀)
    (h : ∃ s ∈ multipartitionQuartets T₀ A, ¬ IsUniformOn p s.taxa) : edgeStarP o c T₀ A < β :=
  (R.star A hA).2 h

theorem mem_contractSides {T C : Finset (Finset X)} {A : Finset X} :
    A ∈ contractSides T C ↔ A ∈ T ∧ A ∉ C ∧ Aᶜ ∉ C := by
  simp [contractSides]

theorem mem_internalSides {T : Finset (Finset X)} {A : Finset X} :
    A ∈ internalSides T ↔ A ∈ T ∧ 2 ≤ A.card ∧ 2 ≤ Aᶜ.card := by
  simp [internalSides]

theorem Run.split_family (R : Run N p T₀ o α β c) {A : Finset X}
    (hA : A ∈ internalSides T₀) :
    IsSplitFamily T₀ := by
  obtain ⟨_, h, _⟩ := mem_internalSides.1 hA
  exact (isUnrootedTree_iff (h.trans (Finset.card_le_univ A)) T₀).1 R.resolution.1

/-- Step 3 does not contract an edge of the tree of blobs: its quartets are nonuniform. -/
theorem Run.treeOfBlobs_subset_afterStar (R : Run N p T₀ o α β c) :
    treeOfBlobs N ⊆ afterStar o β c T₀ := by
  have key : ∀ A ∈ treeOfBlobs N,
      A ∉ (internalSides T₀).filter fun A => β < edgeStarP o c T₀ A := by
    intro A hA hmem
    obtain ⟨hint, hβ⟩ := mem_filter.1 hmem
    obtain ⟨_, h₂, h₂'⟩ := mem_internalSides.1 hint
    obtain ⟨s, hs⟩ := exists_mem_multipartitionQuartets (R.split_family hint) h₂ h₂'
    have hA' : A ∩ s.taxa ∈ s.val := (mem_filter.1 (mem_filter.1 hs).1).2
    have hstrict := R.forward.t1 s (inducedCutSplit_of_mem R.phylo hA hA')
    exact absurd hβ (not_lt_of_gt (R.edgeStarP_lt hint ⟨s, hs, not_uniform_of_strict hstrict⟩))
  intro A hA
  exact mem_contractSides.2 ⟨R.resolution.2 hA, key A hA, key _ (compl_mem_treeOfBlobs hA)⟩

theorem afterStar_subset : afterStar o β c T₀ ⊆ T₀ := Finset.filter_subset _ _

/-- An edge that Step 3 keeps has a nonuniform quartet. -/
theorem Run.exists_not_uniform (R : Run N p T₀ o α β c) {T : Finset (Finset X)}
    (hT : T ⊆ afterStar o β c T₀) {A : Finset X} (hA : A ∈ internalSides T) :
    ∃ s ∈ multipartitionQuartets T₀ A, ¬ IsUniformOn p s.taxa := by
  obtain ⟨hAT, h₂, h₂'⟩ := mem_internalSides.1 hA
  obtain ⟨hAT₀, hnot, _⟩ := mem_contractSides.1 (hT hAT)
  by_contra hcon
  push Not at hcon
  have hint := mem_internalSides.2 ⟨hAT₀, h₂, h₂'⟩
  exact hnot (mem_filter.2 ⟨hint, R.edgeStarP_gt hint hcon⟩)

/-- Step 7 contracts within a tree: contracting internal edges of a tree leaves a tree. -/
theorem isSplitFamily_contractSides {T C : Finset (Finset X)} (hT : IsSplitFamily T)
    (hC : C ⊆ internalSides T) : IsSplitFamily (contractSides T C) := by
  have hint : ∀ {A : Finset X}, A ∈ C → 2 ≤ A.card ∧ 2 ≤ Aᶜ.card := fun hA =>
    (mem_internalSides.1 (hC hA)).2
  refine ⟨fun A hA => hT.nonempty A (mem_contractSides.1 hA).1,
    fun A hA => hT.compl_nonempty A (mem_contractSides.1 hA).1, fun A hA => ?_, fun x => ?_,
    fun A hA B hB => hT.compatible A (mem_contractSides.1 hA).1 B (mem_contractSides.1 hB).1⟩
  · obtain ⟨h₁, h₂, h₃⟩ := mem_contractSides.1 hA
    exact mem_contractSides.2 ⟨hT.compl_mem A h₁, h₃, by rwa [compl_compl]⟩
  · refine mem_contractSides.2 ⟨hT.singleton_mem x, fun h => ?_, fun h => ?_⟩
    · have := (hint h).1
      simp at this
    · have := (hint h).2
      simp at this

theorem isSplitFamily_afterStar (hT₀ : IsSplitFamily T₀) : IsSplitFamily (afterStar o β c T₀) :=
  isSplitFamily_contractSides hT₀ (Finset.filter_subset _ _)

theorem isSplitFamily_contractStep {T : Finset (Finset X)} (hT : IsSplitFamily T) :
    IsSplitFamily (contractStep o c T₀ T) :=
  isSplitFamily_contractSides hT (Finset.filter_subset _ _)

/-- Corollary 4.2 for the quartets `S_bi(e)` of a false edge: one of them is not a cut split of its
induced network. -/
theorem exists_not_inducedCutSplit_bipartition (hN : N.IsPhylogenetic) {A : Finset X}
    (hA : 2 ≤ A.card) (hA' : 2 ≤ Aᶜ.card) (hcut : ¬ N.HasCutSplit (A : Set X)) :
    ∃ s ∈ bipartitionQuartets A, ¬ InducedCutSplit N s := by
  obtain ⟨a₁, ha₁⟩ : A.Nonempty := Finset.card_pos.1 (by omega)
  obtain ⟨b₁, hb₁⟩ : Aᶜ.Nonempty := Finset.card_pos.1 (by omega)
  rcases corollary4_2 hN A hA hA' with h | h
  · exact absurd h hcut
  obtain ⟨a₂, ha₂, b₂, hb₂, hane, hbne, hbad⟩ := h a₁ ha₁ b₁ hb₁
  have hb₁' := mem_compl.1 hb₁
  have hb₂' := mem_compl.1 hb₂
  have hc : ({a₁, a₂, b₁, b₂} : Finset X).card = 4 :=
    TreeMetric.card_four_of_ne hane.symm (fun h => hb₁' (h ▸ ha₁)) (fun h => hb₂' (h ▸ ha₁))
      (fun h => hb₁' (h ▸ ha₂)) (fun h => hb₂' (h ▸ ha₂)) hbne.symm
  refine ⟨quartetTree a₁ a₂ b₁ b₂ hc, mem_filter.2 ⟨mem_univ _, ?_⟩,
    fun hr => hbad (hasCutSplitOn_of_inducedCutSplit hc hr)⟩
  rw [taxa_quartetTree, inter_four ha₁ ha₂ hb₁' hb₂']
  simp [quartetTree]

/-- Corollary 4.3 for the quartets `S_mul(e)` of a false edge of a tree: one of them is not a cut
split of its induced network. -/
theorem exists_not_inducedCutSplit_multipartition (hN : N.IsPhylogenetic) {T : Finset (Finset X)}
    (hT : IsSplitFamily T) {A : Finset X} (hA : 2 ≤ A.card) (hA' : 2 ≤ Aᶜ.card)
    (hcut : ¬ N.HasCutSplit (A : Set X)) :
    ∃ s ∈ multipartitionQuartets T A, ¬ InducedCutSplit N s := by
  obtain ⟨a, ha, b, hb, c, hc, d, hd, hab, hcd, hbad⟩ := exists_cut_witness hN hT hA hA' hcut
  have hc' := mem_compl.1 hc
  have hd' := mem_compl.1 hd
  have hcard : ({a, b, c, d} : Finset X).card = 4 :=
    TreeMetric.card_four_of_ne hab.1 (fun h => hc' (h ▸ ha)) (fun h => hd' (h ▸ ha))
      (fun h => hc' (h ▸ hb)) (fun h => hd' (h ▸ hb)) hcd.1
  exact ⟨_, quartetTree_mem hcard ha hb hc' hd' hab hcd,
    fun hr => hbad (hasCutSplitOn_of_inducedCutSplit hcard hr)⟩

/-- "By Corollaries 4.2 and 4.3" (line 1126): at a false edge, the quartets of the chosen type, at
any stage, include one that is not a cut split of its induced network. Corollary 4.2 for the type
`bi`, Corollary 4.3 at the current tree for `mul`, and at `T₀` for `quad`. -/
theorem exists_not_inducedCutSplit_edgeQuartets (hN : N.IsPhylogenetic) {T : Finset (Finset X)}
    (hT₀ : IsSplitFamily T₀) (hT : IsSplitFamily T) {A : Finset X} (hA : 2 ≤ A.card)
    (hA' : 2 ≤ Aᶜ.card) (hcut : ¬ N.HasCutSplit (A : Set X)) :
    ∃ s ∈ edgeQuartets o T₀ T A, ¬ InducedCutSplit N s := by
  unfold edgeQuartets
  cases o.qType with
  | bi => exact exists_not_inducedCutSplit_bipartition hN hA hA' hcut
  | mul => exact exists_not_inducedCutSplit_multipartition hN hT hA hA' hcut
  | quad => exact exists_not_inducedCutSplit_multipartition hN hT₀ hA hA' hcut

/-- An internal edge of a tree that is not in the tree of blobs is not a cut edge. -/
theorem not_hasCutSplit_of_notMem {A : Finset X} (hA : 2 ≤ A.card)
    (hA' : 2 ≤ Aᶜ.card) (hAB : A ∉ treeOfBlobs N) : ¬ N.HasCutSplit (A : Set X) := fun h =>
  hAB (mem_filter.2 ⟨mem_univ _, Finset.card_pos.1 (by omega), Finset.card_pos.1 (by omega), h⟩)

/-- A set `Q` of quartets of a false edge that Step 3 keeps, containing a quartet `s` that is not a
cut split (the paper's witness, from Corollaries 4.2 and 4.3), and containing the multipartition of
`T₀`, has a quartet off the T1 null.

If `s` has no trivial 4-blob, this is `s`, by the converse of Assumption 1: this is the paper's
argument. If `s` has a trivial 4-blob, then the T1 null holds on it, at the centroid, and it does
not witness anything: this is the gap of the paper's proof (E12). In that case the witness comes
from `falseEdge_witness`, which applies since Step 3 kept the edge. -/
theorem Run.exists_not_t1Null_of_witness (R : Run N p T₀ o α β c) {T : Finset (Finset X)}
    (hT : T ⊆ afterStar o β c T₀) {A : Finset X} (hA : A ∈ internalSides T)
    (hAB : A ∉ treeOfBlobs N) {Q : Finset (QuartetTree X)} (hQ : multipartitionQuartets T₀ A ⊆ Q)
    (hw : ∃ s ∈ Q, ¬ InducedCutSplit N s) : ∃ s ∈ Q, ¬ IsT1Null p s := by
  obtain ⟨s, hs, hR⟩ := hw
  by_cases htr : HasTrivialFourBlob N s.taxa
  · -- the gap: the paper's witness is on the T1 null
    obtain ⟨hAT, h₂, h₂'⟩ := mem_internalSides.1 hA
    obtain ⟨s₀, hs₀, hu₀⟩ := R.exists_not_uniform hT hA
    obtain ⟨s', hs', hR', hTr'⟩ := falseEdge_witness R.phylo R.resolution
      (mem_internalSides.2 ⟨afterStar_subset (hT hAT), h₂, h₂'⟩) hAB
      ⟨s₀, hs₀, fun htr => hu₀ (R.forward.star _ s₀.card_taxa htr)⟩
    exact ⟨s', hQ hs', not_t1Null (R.sum s') (R.converse.t1 s' hR')
      (R.converse.star _ s'.card_taxa hTr')⟩
  · -- the paper's argument: the witness is off the T1 null
    exact ⟨s, hs, not_t1Null (R.sum s) (R.converse.t1 s hR) (R.converse.star _ s.card_taxa htr)⟩

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

/-- A set of quartets displayed by a tree has at most `C(s,4)` elements, one for each set of four
taxa, for `s` the number of taxa: the paper's bound (lines 1107 and 1154-1155). -/
theorem card_le_choose_of_displays {T : Finset (Finset X)} (hT : IsUnrootedTree T)
    {Q : Finset (QuartetTree X)} (hQ : ∀ s ∈ Q, Displays T s) :
    Q.card ≤ (Fintype.card X).choose 4 := by
  rw [← Finset.card_univ, ← Finset.card_powersetCard]
  refine Finset.card_le_card_of_injOn (fun s => s.taxa) (fun s _ => ?_) fun s hs s' hs' h => ?_
  · exact Finset.mem_coe.2 (Finset.mem_powersetCard.2 ⟨Finset.subset_univ _, s.card_taxa⟩)
  · exact hT.displays_unique (hQ s hs) (hQ s' hs') h

/-- The size of the quartets of an edge of `T₀`, for the star test. -/
theorem card_multipartitionQuartets_le (hT₀ : IsUnrootedTree T₀) {A : Finset X} (hA : A ∈ T₀) :
    (multipartitionQuartets T₀ A).card ≤ (Fintype.card X).choose 4 :=
  card_le_choose_of_displays hT₀ fun _ hs => ⟨A, hA, (mem_filter.1 (mem_filter.1 hs).1).2⟩

/-- The size of the quartets of an edge of a contraction of `T₀`, for the T1 test. -/
theorem card_edgeQuartets_le (hT₀ : IsUnrootedTree T₀) {T : Finset (Finset X)} (hT : T ⊆ T₀)
    {A : Finset X} (hA : A ∈ T) : (edgeQuartets o T₀ T A).card ≤ (Fintype.card X).choose 4 :=
  card_le_choose_of_displays hT₀ fun _ hs => ⟨A, hT hA, mem_of_mem_edgeQuartets hs⟩

/-- The size of the quartets of a contraction of `T₀`, for the overall p-value. -/
theorem card_displays_le (hT₀ : IsUnrootedTree T₀) {T : Finset (Finset X)} (hT : T ⊆ T₀) :
    (univ.filter fun s => Displays T s).card ≤ (Fintype.card X).choose 4 :=
  card_le_choose_of_displays hT₀ fun _ hs => by
    obtain ⟨A, hA, hAs⟩ := (mem_filter.1 hs).2
    exact ⟨A, hT hA, hAs⟩

/-- A false edge that Step 3 keeps has a quartet of the chosen type off the T1 null: `S^a(e)` is not
empty (lines 1125-1127). -/
theorem Run.exists_not_t1Null (R : Run N p T₀ o α β c) {T : Finset (Finset X)}
    (hT : T ⊆ afterStar o β c T₀) (hTs : IsSplitFamily T) {A : Finset X} (hA : A ∈ internalSides T)
    (hAB : A ∉ treeOfBlobs N) : ∃ s ∈ edgeQuartets o T₀ T A, ¬ IsT1Null p s := by
  obtain ⟨hAT, h₂, h₂'⟩ := mem_internalSides.1 hA
  refine R.exists_not_t1Null_of_witness hT hA hAB
    (multipartitionQuartets_subset_edgeQuartets (hT.trans afterStar_subset) A) ?_
  exact exists_not_inducedCutSplit_edgeQuartets R.phylo
    (R.split_family (mem_internalSides.2 ⟨afterStar_subset (hT hAT), h₂, h₂'⟩)) hTs h₂ h₂'
    (not_hasCutSplit_of_notMem h₂ h₂' hAB)

/-- Edges of the tree of blobs are not rejected: `S^a(e)` is empty. -/
theorem Run.edgeT1P_gt (R : Run N p T₀ o α β c) {T : Finset (Finset X)} (hT : T ⊆ T₀) {A : Finset X}
    (hAi : A ∈ internalSides T) (hA : A ∈ treeOfBlobs N) : α < edgeT1P o c T₀ T A :=
  (R.t1 T hT A hAi).1 fun _ hs => R.t1Null_of_mem hA (mem_of_mem_edgeQuartets hs)

/-- False edges are rejected: `S^a(e)` is not empty. -/
theorem Run.edgeT1P_lt (R : Run N p T₀ o α β c) {T : Finset (Finset X)}
    (hT : T ⊆ afterStar o β c T₀) (hTs : IsSplitFamily T) {A : Finset X} (hA : A ∈ internalSides T)
    (hAB : A ∉ treeOfBlobs N) : edgeT1P o c T₀ T A < α :=
  (R.t1 T (hT.trans afterStar_subset) A hA).2 (R.exists_not_t1Null hT hTs hA hAB)

/-- A tree with a false edge is rejected (lines 1151-1158). The overall p-value combines the T1
tests on `∪_{e ∈ T_k} S_bi(e)`, so the paper's witness at the false edge comes from Corollary 4.2.
-/
theorem Run.treeT1P_lt (R : Run N p T₀ o α β c) {T : Finset (Finset X)}
    (hT : T ⊆ afterStar o β c T₀) {A : Finset X} (hA : A ∈ internalSides T)
    (hAB : A ∉ treeOfBlobs N) : treeT1P o c T < α := by
  obtain ⟨hAT, h₂, h₂'⟩ := mem_internalSides.1 hA
  obtain ⟨s, hs, hn⟩ := R.exists_not_t1Null_of_witness hT hA hAB (Finset.filter_subset _ _)
    (exists_not_inducedCutSplit_bipartition R.phylo h₂ h₂' (not_hasCutSplit_of_notMem h₂ h₂' hAB))
  exact (R.tree T (hT.trans afterStar_subset)).2
    ⟨s, mem_filter.2 ⟨mem_univ _, A, hAT, (mem_filter.1 hs).2⟩, hn⟩

/-- A tree without false edges is not rejected. -/
theorem Run.treeT1P_gt (R : Run N p T₀ o α β c) {T : Finset (Finset X)}
    (hT : T ⊆ treeOfBlobs N) : α < treeT1P o c T := by
  refine (R.tree T (hT.trans R.resolution.2)).1 fun s hs => ?_
  obtain ⟨A, hA, hAs⟩ := (mem_filter.1 hs).2
  exact R.t1Null_of_mem (hT hA) hAs

theorem contractStep_subset (T : Finset (Finset X)) : contractStep o c T₀ T ⊆ T :=
  Finset.filter_subset _ _

/-- Step 7 keeps the edges of the tree of blobs as long as there is a false edge. -/
theorem Run.treeOfBlobs_subset_contractStep (R : Run N p T₀ o α β c)
    {T : Finset (Finset X)} (hT : T ⊆ afterStar o β c T₀) (hTs : IsSplitFamily T)
    (hB : treeOfBlobs N ⊆ T) {F : Finset X} (hF : F ∈ internalSides T) (hFB : F ∉ treeOfBlobs N) :
    treeOfBlobs N ⊆ contractStep o c T₀ T := by
  have key : ∀ A ∈ treeOfBlobs N, A ∉ (internalSides T).filter fun A =>
      ∀ B ∈ internalSides T, edgeT1P o c T₀ T A ≤ edgeT1P o c T₀ T B := by
    intro A hA hmem
    obtain ⟨hAi, h₀⟩ := mem_filter.1 hmem
    have h₁ := R.edgeT1P_gt (hT.trans afterStar_subset) hAi hA
    have h₂ := R.edgeT1P_lt hT hTs hF hFB
    linarith [h₀ F hF]
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

theorem isSplitFamily_treeSeq (hT₀ : IsSplitFamily T₀) (i : ℕ) :
    IsSplitFamily (treeSeq o β c T₀ i) := by
  induction i with
  | zero => exact isSplitFamily_afterStar hT₀
  | succ i ih =>
    rw [treeSeq_succ]
    exact isSplitFamily_contractStep ih

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

/-- **The deterministic core of Theorem 8.2.** On a table on which every test comes out right, the
algorithm outputs the tree of blobs (the end of the paper's proof, lines 1133-1158). -/
theorem ectoblob_eq_treeOfBlobs (R : Run N p T₀ o α β c) :
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
      have hF₀ : F ∈ internalSides T₀ := by
        obtain ⟨h₁, h₂⟩ := mem_internalSides.1 hF
        exact mem_internalSides.2 ⟨afterStar_subset (treeSeq_subset_afterStar i h₁), h₂⟩
      rw [treeSeq_succ]
      exact R.treeOfBlobs_subset_contractStep (treeSeq_subset_afterStar i)
        (isSplitFamily_treeSeq (R.split_family hF₀) i) (ih (by omega)) hF hFB
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
