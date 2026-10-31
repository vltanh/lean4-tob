module

public import Basic.Phylogenetics.TreeSplice
public import Basic.Probability.IID
public import Basic.Analysis.FiniteOptimization
public import Mathlib.Order.Filter.AtTopBot.Basic

/-!
# ECToBlob §3: resolving the tree of blobs

Lemma 3.5, Theorem 3.1, Remark 3.2, Corollary 3.6, and the objective decompositions (3.2) and (3.3).
Equation (3.3) as printed overcounts quartets (E1 of the report): `equation3_3` is the repaired
identity, with the weights by block sizes, and the proof of Theorem 3.1 follows the paper's route
with these weights. The splice of the local maximizers into the tree of blobs is the construction of
`Basic/Phylogenetics/TreeSplice.lean`.
-/

@[expose] public noncomputable section

open Phylogenetics Phylogenetics.RootedNetwork Finset Filter Topology
open scoped Classical

namespace ECToBlob

variable {V E X : Type*} [Fintype X] [DecidableEq X] {N : RootedNetwork V E X}


/-- **Lemma 3.5** (`ecto:lem3_5`). If `x₀` simultaneously maximizes each of the `fᵢ`, it maximizes
their sum, and every maximizer of the sum maximizes each of the `fᵢ`. -/
theorem lemma3_5 {ι U : Type*} (t : Finset ι) (f : ι → U → ℝ) (x₀ : U)
    (h : ∀ i ∈ t, ∀ x, f i x ≤ f i x₀) :
    (∀ x, ∑ i ∈ t, f i x ≤ ∑ i ∈ t, f i x₀) ∧
      ∀ x₁, (∀ x, ∑ i ∈ t, f i x ≤ ∑ i ∈ t, f i x₁) → ∀ i ∈ t, ∀ x, f i x ≤ f i x₁ := by
  refine ⟨fun x => sum_le_sum fun i hi => h i hi x, fun x₁ hx₁ i hi x => ?_⟩
  by_contra hlt
  have h₁ : f i x₁ < f i x₀ := lt_of_lt_of_le (not_le.1 hlt) (h i hi x)
  exact absurd (hx₁ x₀) (not_le.2 (sum_lt_sum (fun j hj => h j hj x₁) ⟨i, hi, h₁⟩))

/-- The part `f_R` of the objective from the 4-taxon sets that the tree `TB` resolves. -/
def resolvedPart (TB : Finset (Finset X)) (w : QuartetTree X → ℝ) (T : Finset (Finset X)) : ℝ :=
  ∑ s, if (∃ r ∈ treesOn s.taxa, Displays TB r) ∧ Displays T s then w s else 0

/-- The part `f_m` of the objective from the 4-taxon sets with centre the multifurcation `P`. -/
def starPart (P : Finset (Finset X)) (w : QuartetTree X → ℝ) (T : Finset (Finset X)) : ℝ :=
  ∑ s, if InDistinctBlocks P s.taxa ∧ Displays T s then w s else 0

/-- **Equation (3.2)** (`ecto:eq3_2`): the objective is `f_R + ∑_m f_m`. -/
theorem equation3_2 {TB : Finset (Finset X)} (hTB : IsUnrootedTree TB) (w : QuartetTree X → ℝ)
    (T : Finset (Finset X)) :
    quartetScore w T = resolvedPart TB w T + ∑ P ∈ multifurcations TB, starPart P w T := by
  have hc : ∑ P ∈ multifurcations TB, starPart P w T =
      ∑ s, ∑ P ∈ multifurcations TB, if InDistinctBlocks P s.taxa ∧ Displays T s then w s else 0 := by
    simp only [starPart]
    exact sum_comm
  rw [hc, resolvedPart, ← sum_add_distrib]
  refine sum_congr rfl fun s _ => ?_
  by_cases hD : Displays T s
  · by_cases hR : ∃ r ∈ treesOn s.taxa, Displays TB r
    · have hzero : ∀ P ∈ multifurcations TB,
          (if InDistinctBlocks P s.taxa ∧ Displays T s then w s else 0) = 0 := by
        intro P hP
        refine ite_eq_right fun h => ?_
        obtain ⟨r, hr, hdr⟩ := hR
        have hr' := mem_treesOn.1 hr
        exact not_displays_of_inDistinctBlocks (mem_multifurcations.1 hP).1
          (s := r) (hr' ▸ h.1) hdr
      rw [sum_eq_zero hzero]
      simp only [hD, hR, and_self, ↓reduceIte, add_zero]
    · have hstar : ∀ r ∈ treesOn s.taxa, ¬ Displays TB r := fun r hr h => hR ⟨r, hr, h⟩
      obtain ⟨P₀, ⟨hP₀, hI⟩, huniq⟩ := existsUnique_center hTB s.card_taxa hstar
      rw [sum_eq_single_of_mem P₀ hP₀ fun P hP hne =>
        ite_eq_right fun h => hne (huniq P ⟨hP, h.1⟩)]
      simp only [hD, hR, hI, and_self, false_and, ↓reduceIte, zero_add]
  · rw [sum_eq_zero fun P _ => ite_eq_right fun h => hD h.2]
    simp only [hD, and_false, ↓reduceIte, add_zero]

/-- The weight of a quartet tree in the repaired (3.3): the product of the sizes of the blocks of `P`
meeting its taxa. -/
def blockWeight (P : Finset (Finset X)) (s : QuartetTree X) : ℝ :=
  ∏ B ∈ P.filter fun B => (B ∩ s.taxa).Nonempty, (B.card : ℝ)

/-- Counting the representative tuples containing the taxa of a quartet tree in distinct blocks. -/
theorem card_rep_mul_blockWeight {P : Finset (Finset X)}
    (hdisj : ∀ B ∈ P, ∀ C ∈ P, B ≠ C → Disjoint B C)
    (hcover : P.sup id = univ) {s : QuartetTree X} (hI : InDistinctBlocks P s.taxa) :
    (((univ : Finset ({B // B ∈ P} → X)).filter
        (fun x => (∀ B, x B ∈ B.val) ∧ s.taxa ⊆ univ.image x)).card : ℝ) * blockWeight P s =
      ∏ B ∈ P, (B.card : ℝ) := by
  set q := s.taxa with hq
  let F : (b : {B // B ∈ P}) → Finset X := fun b =>
    if (b.val ∩ q).Nonempty then b.val ∩ q else b.val
  have hfil : (univ : Finset ({B // B ∈ P} → X)).filter
      (fun x => (∀ B, x B ∈ B.val) ∧ q ⊆ univ.image x) = Fintype.piFinset F := by
    ext x
    simp only [mem_filter, mem_univ, true_and, Fintype.mem_piFinset]
    constructor
    · rintro ⟨hrep, hsub⟩ b
      by_cases hb : (b.val ∩ q).Nonempty
      · simp only [F, ite_eq_left hb]
        obtain ⟨y, hy⟩ := hb
        obtain ⟨hyb, hyq⟩ := mem_inter.1 hy
        obtain ⟨c, -, rfl⟩ := mem_image.1 (hsub hyq)
        have : c = b := block_eq_of_mem hdisj (hrep c) hyb
        exact this ▸ hy
      · simp only [F, ite_eq_right hb]
        exact hrep b
    · intro h
      have hrep : ∀ b, x b ∈ b.val := by
        intro b
        have := h b
        by_cases hb : (b.val ∩ q).Nonempty
        · simp only [F, ite_eq_left hb] at this
          exact (mem_inter.1 this).1
        · simpa only [F, ite_eq_right hb] using this
      refine ⟨hrep, fun y hy => ?_⟩
      obtain ⟨b, hb⟩ := exists_block hcover y
      have hne' : (b.val ∩ q).Nonempty := ⟨y, mem_inter.2 ⟨hb, hy⟩⟩
      have hxb := h b
      simp only [F, ite_eq_left hne'] at hxb
      have : x b = y := card_le_one.1 (hI b.val b.property) _ hxb _ (mem_inter.2 ⟨hb, hy⟩)
      exact mem_image.2 ⟨b, mem_univ b, this⟩
  rw [hfil, Fintype.card_piFinset, blockWeight, prod_filter]
  push_cast
  have hcoe : ∏ b : {B // B ∈ P}, ((F b).card : ℝ) =
      ∏ B ∈ P, ((if (B ∩ q).Nonempty then B ∩ q else B).card : ℝ) :=
    prod_coe_sort P fun B => ((if (B ∩ q).Nonempty then B ∩ q else B).card : ℝ)
  rw [hcoe, ← prod_mul_distrib]
  refine prod_congr rfl fun B hB => ?_
  by_cases hb : (B ∩ q).Nonempty
  · have h1 : (B ∩ q).card = 1 := le_antisymm (hI B hB) (card_pos.2 hb)
    rw [ite_eq_left hb, ite_eq_left hb, h1]
    simp
  · rw [ite_eq_right hb, ite_eq_right hb, mul_one]

/-- **Equation (3.3)** (`ecto:eq3_3`), repaired (E1 of the report). The printed identity repeats a
quartet once for each choice of representatives of the blocks it does not use. Weighted by the
block sizes and divided by the product of all block sizes, the representative sum is `f_m`. A
representative tuple `x` chooses a taxon in each block. The `X_i` of the paper partition the taxa:
without `hcover`, a quartet with a taxon in no block counts on the left only. -/
theorem equation3_3 {P : Finset (Finset X)} (hdisj : ∀ B ∈ P, ∀ C ∈ P, B ≠ C → Disjoint B C)
    (hne : ∀ B ∈ P, B.Nonempty) (hcover : P.sup id = univ) (w : QuartetTree X → ℝ)
    (T : Finset (Finset X)) :
    (∏ B ∈ P, (B.card : ℝ)) * starPart P w T =
      ∑ x ∈ (univ : Finset ({B // B ∈ P} → X)).filter (fun x => ∀ B, x B ∈ B.val),
        ∑ s, if InDistinctBlocks P s.taxa ∧ Displays T s ∧ s.taxa ⊆ univ.image x then
            blockWeight P s * w s else 0 := by
  rw [sum_comm, starPart, mul_sum]
  refine sum_congr rfl fun s _ => ?_
  by_cases hID : InDistinctBlocks P s.taxa ∧ Displays T s
  · rw [ite_eq_left hID]
    have hstep : ∀ x : {B // B ∈ P} → X,
        (if InDistinctBlocks P s.taxa ∧ Displays T s ∧ s.taxa ⊆ univ.image x then
          blockWeight P s * w s else 0) =
        if s.taxa ⊆ univ.image x then blockWeight P s * w s else 0 := by
      intro x
      by_cases hc : s.taxa ⊆ univ.image x
      · rw [ite_eq_left ⟨hID.1, hID.2, hc⟩, ite_eq_left hc]
      · rw [ite_eq_right fun h => hc h.2.2, ite_eq_right hc]
    simp only [hstep]
    rw [← sum_filter, filter_filter, sum_const, nsmul_eq_mul, ← mul_assoc,
      card_rep_mul_blockWeight hdisj hcover hID.1]
  · rw [ite_eq_right hID, mul_zero]
    exact (sum_eq_zero fun x _ => ite_eq_right fun h => hID ⟨h.1, h.2.1⟩).symm

/-! ### The part `f_R`: maximizers display the resolved quartets of the tree of blobs -/

/-- `f_R` grouped by the quartet tree of `TB` on each resolved set of four taxa. -/
theorem resolvedPart_eq_sum {TB : Finset (Finset X)} (hTB : IsUnrootedTree TB)
    (w : QuartetTree X → ℝ) (T : Finset (Finset X)) :
    resolvedPart TB w T = ∑ r ∈ univ.filter (Displays TB),
      ∑ s ∈ treesOn r.taxa, if Displays T s then w s else 0 := by
  unfold resolvedPart
  refine (sum_congr rfl fun s _ => ?_ :
    _ = ∑ s : QuartetTree X, ∑ r ∈ univ.filter (Displays TB),
      if s ∈ treesOn r.taxa then (if Displays T s then w s else 0) else 0).trans ?_
  · by_cases hR : ∃ r ∈ treesOn s.taxa, Displays TB r
    · obtain ⟨r₀, hr₀, hd₀⟩ := id hR
      have hrs : r₀.taxa = s.taxa := mem_treesOn.1 hr₀
      rw [sum_eq_single_of_mem r₀ (mem_filter.2 ⟨mem_univ _, hd₀⟩)]
      · have hmem : s ∈ treesOn r₀.taxa := mem_treesOn.2 hrs.symm
        simp only [hR, hmem, true_and, ↓reduceIte]
      · intro r hr hne
        refine ite_eq_right fun hs => absurd ?_ hne
        exact hTB.displays_unique (mem_filter.1 hr).2 hd₀ ((mem_treesOn.1 hs).symm.trans hrs.symm)
    · rw [sum_eq_zero]
      · simp only [hR, false_and, ↓reduceIte]
      · intro r hr
        refine ite_eq_right fun hs => hR ⟨r, ?_, (mem_filter.1 hr).2⟩
        exact mem_treesOn.2 (mem_treesOn.1 hs).symm
  · rw [sum_comm]
    refine sum_congr rfl fun r _ => ?_
    rw [sum_ite_mem, univ_inter]

/-- The contribution of a set of four taxa that `TB` resolves into `r`. -/
theorem sum_treesOn_eq_of_displays {T : Finset (Finset X)} (hT : IsUnrootedTree T)
    (p : QuartetTree X → ℝ) {r : QuartetTree X} (hr : Displays T r) :
    (∑ s ∈ treesOn r.taxa, if Displays T s then p s else 0) = p r := by
  rw [sum_eq_single_of_mem r (mem_treesOn.2 rfl), ite_eq_left hr]
  intro s hs hne
  exact ite_eq_right fun h => hne (hT.displays_unique h hr (mem_treesOn.1 hs))

theorem sum_treesOn_lt_of_not_displays {T : Finset (Finset X)} (hT : IsUnrootedTree T)
    {p : QuartetTree X → ℝ} (hp : ∀ s, 0 ≤ p s) {r : QuartetTree X}
    (hr : ∀ r' ∈ r.alternatives, p r' < p r) (hnot : ¬ Displays T r) :
    (∑ s ∈ treesOn r.taxa, if Displays T s then p s else 0) < p r := by
  by_cases hex : ∃ s ∈ treesOn r.taxa, Displays T s
  · obtain ⟨s, hs, hds⟩ := hex
    have hsr : s.taxa = r.taxa := mem_treesOn.1 hs
    rw [sum_eq_single_of_mem s hs, ite_eq_left hds]
    · refine hr s (QuartetTree.mem_alternatives.2 ⟨hsr, ?_⟩)
      rintro rfl
      exact hnot hds
    · intro s' hs' hne
      exact ite_eq_right fun h => hne (hT.displays_unique h hds
        ((mem_treesOn.1 hs').trans hsr.symm))
  · rw [sum_eq_zero fun s hs => ite_eq_right fun h => hex ⟨s, hs, h⟩]
    obtain ⟨r', hr'⟩ := card_pos.1 (by rw [r.card_alternatives]; omega : 0 < r.alternatives.card)
    exact lt_of_le_of_lt (hp r') (hr r' hr')

/-- The value of `f_R` on the trees resolving `TB`. -/
theorem resolvedPart_eq_of_subset {TB T : Finset (Finset X)} (hTB : IsUnrootedTree TB)
    (hT : IsUnrootedTree T) (h : TB ⊆ T) (p : QuartetTree X → ℝ) :
    resolvedPart TB p T = quartetScore p TB := by
  rw [resolvedPart_eq_sum hTB, quartetScore, ← sum_filter]
  exact sum_congr rfl fun r hr =>
    sum_treesOn_eq_of_displays hT p ((mem_filter.1 hr).2.mono h)

/-- `TB` and its resolutions maximize `f_R`: each resolved quartet gives its largest weight. -/
theorem resolvedPart_le {TB T : Finset (Finset X)} (hTB : IsUnrootedTree TB)
    (hT : IsUnrootedTree T) {p : QuartetTree X → ℝ} (hp : ∀ s, 0 ≤ p s)
    (h₁ : ∀ s, Displays TB s → ∀ r ∈ s.alternatives, p r < p s) :
    resolvedPart TB p T ≤ quartetScore p TB := by
  rw [resolvedPart_eq_sum hTB, quartetScore, ← sum_filter]
  refine sum_le_sum fun r hr => ?_
  by_cases hd : Displays T r
  · exact (sum_treesOn_eq_of_displays hT p hd).le
  · exact (sum_treesOn_lt_of_not_displays hT hp (h₁ r (mem_filter.1 hr).2) hd).le

/-- Every maximizer of `f_R` displays the resolved quartets of `TB`. -/
theorem displays_of_le_resolvedPart {TB T : Finset (Finset X)} (hTB : IsUnrootedTree TB)
    (hT : IsUnrootedTree T) {p : QuartetTree X → ℝ} (hp : ∀ s, 0 ≤ p s)
    (h₁ : ∀ s, Displays TB s → ∀ r ∈ s.alternatives, p r < p s)
    (h : quartetScore p TB ≤ resolvedPart TB p T) {r : QuartetTree X} (hr : Displays TB r) :
    Displays T r := by
  by_contra hnot
  rw [resolvedPart_eq_sum hTB, quartetScore, ← sum_filter] at h
  refine absurd h (not_le.2 (sum_lt_sum (fun r' hr' => ?_) ⟨r, mem_filter.2 ⟨mem_univ _, hr⟩,
    sum_treesOn_lt_of_not_displays hT hp (h₁ r hr) hnot⟩))
  by_cases hd : Displays T r'
  · exact (sum_treesOn_eq_of_displays hT p hd).le
  · exact (sum_treesOn_lt_of_not_displays hT hp (h₁ r' (mem_filter.1 hr').2) hd).le

/-! ### The part `f_m`: the objective on the blocks -/

/-- The weight of the local objective `f̃_m` on the blocks: the product of the sizes of the four
blocks. -/
def blockSizeProd {P : Finset (Finset X)} (s₀ : QuartetTree {B // B ∈ P}) : ℝ :=
  ∏ b ∈ s₀.taxa, (b.val.card : ℝ)

theorem blockWeight_map {P : Finset (Finset X)} (hd : ∀ B ∈ P, ∀ C ∈ P, B ≠ C → Disjoint B C)
    {x : {B // B ∈ P} → X} (hx : IsRepTuple P x) (s₀ : QuartetTree {B // B ∈ P}) :
    blockWeight P (s₀.map (hx.injective hd)) = blockSizeProd s₀ := by
  have hfil : (P.filter fun B => (B ∩ (s₀.map (hx.injective hd)).taxa).Nonempty) =
      s₀.taxa.image Subtype.val := by
    ext B
    simp only [mem_filter, mem_image, QuartetTree.map_taxa]
    constructor
    · rintro ⟨hB, y, hy⟩
      obtain ⟨hyB, hyt⟩ := mem_inter.1 hy
      obtain ⟨b, hb, rfl⟩ := mem_image.1 hyt
      have : b = ⟨B, hB⟩ := block_eq_of_mem hd (hx b) hyB
      exact ⟨b, hb, by rw [this]⟩
    · rintro ⟨b, hb, rfl⟩
      exact ⟨b.property, x b, mem_inter.2 ⟨hx b, mem_image_of_mem _ hb⟩⟩
  rw [blockWeight, hfil, prod_image fun a _ b _ h => Subtype.ext h, blockSizeProd]

/-- The inner sum of the repaired (3.3), at the representative tuple `x`. -/
def innerSum (P : Finset (Finset X)) (w : QuartetTree X → ℝ) (T : Finset (Finset X))
    (x : {B // B ∈ P} → X) : ℝ :=
  ∑ s, if InDistinctBlocks P s.taxa ∧ Displays T s ∧ s.taxa ⊆ univ.image x then
    blockWeight P s * w s else 0

/-- The local objective `f̃_m` on the blocks of `P`: the weight of a quartet tree is the
product of the sizes of the four blocks times its probability, read at any representatives. -/
def localWeight {P : Finset (Finset X)} (hd : ∀ B ∈ P, ∀ C ∈ P, B ≠ C → Disjoint B C)
    {x₀ : {B // B ∈ P} → X} (hx₀ : IsRepTuple P x₀) (p : QuartetTree X → ℝ)
    (s₀ : QuartetTree {B // B ∈ P}) : ℝ :=
  blockSizeProd s₀ * p (s₀.map (hx₀.injective hd))

/-- The inner sum of (3.3) at `x` is `f̃_m` of the restriction to `x`. -/
theorem innerSum_eq_quartetScore {P : Finset (Finset X)} {p : QuartetTree X → ℝ}
    (h₂ : CutExchangeable N p) (hd : ∀ B ∈ P, ∀ C ∈ P, B ≠ C → Disjoint B C)
    (hcut : ∀ B ∈ P, N.HasCutSplit (B : Set X)) {x₀ x : {B // B ∈ P} → X}
    (hx₀ : IsRepTuple P x₀) (hx : IsRepTuple P x) (T : Finset (Finset X)) :
    innerSum P p T x = quartetScore (localWeight hd hx₀ p) (pullTree x T) := by
  have hstep : ∀ s : QuartetTree X,
      (if InDistinctBlocks P s.taxa ∧ Displays T s ∧ s.taxa ⊆ univ.image x then
        blockWeight P s * p s else 0) =
      if s.taxa ⊆ univ.image x then (if Displays T s then blockWeight P s * p s else 0) else 0 := by
    intro s
    by_cases hc : s.taxa ⊆ univ.image x
    · have hI := hx.inDistinctBlocks hd hc
      simp only [hI, hc, true_and, and_true, ↓reduceIte]
    · simp only [hc, and_false, ↓reduceIte]
  simp only [innerSum, hstep]
  rw [sum_ite_taxa_subset_image (hx.injective hd), quartetScore]
  refine sum_congr rfl fun s₀ _ => ?_
  simp only [displays_pullTree_iff (hx.injective hd), blockWeight_map hd hx, localWeight,
    map_eq_of_cutExchangeable h₂ hd hcut hx hx₀ s₀]

/-- A tree splicing a maximizer of `f̃_m` at `P` simultaneously maximizes the inner sums of (3.3),
hence `f_m`, by Lemma 3.5. -/
theorem starPart_le_splice {TB : Finset (Finset X)} (hTB : IsUnrootedTree TB)
    {L : Finset (Finset X) → Finset (Finset X)}
    (hL : ∀ P ∈ multifurcations TB, IsBlockFamily P (L P)) {P : Finset (Finset X)}
    (hP : P ∈ multifurcations TB) {p : QuartetTree X → ℝ} (h₂ : CutExchangeable N p)
    (hcut : ∀ B ∈ P, N.HasCutSplit (B : Set X)) (hd : ∀ B ∈ P, ∀ C ∈ P, B ≠ C → Disjoint B C)
    {x₀ : {B // B ∈ P} → X} (hx₀ : IsRepTuple P x₀) {T₀ : Finset (Finset {B // B ∈ P})}
    (hmax : ∀ T', IsUnrootedTree T' →
      quartetScore (localWeight hd hx₀ p) T' ≤ quartetScore (localWeight hd hx₀ p) T₀)
    (hLP : L P = T₀.image (liftBlocks P)) {T' : Finset (Finset X)} (hT' : IsUnrootedTree T') :
    starPart P p T' ≤ starPart P p (splice TB L) := by
  obtain ⟨hV, h4⟩ := mem_multifurcations.1 hP
  have hne : ∀ B ∈ P, B.Nonempty := fun B hB => hTB.nonempty_of_mem (hV.mem B hB)
  have hW : 0 < ∏ B ∈ P, (B.card : ℝ) :=
    prod_pos fun B hB => by exact_mod_cast card_pos.2 (hne B hB)
  have hY : 2 ≤ Fintype.card {B // B ∈ P} := by
    rw [Fintype.card_coe]
    omega
  let Tstar : {T // IsUnrootedTree T} := ⟨splice TB L, splice_isUnrootedTree hTB hL⟩
  let F : ({B // B ∈ P} → X) → {T : Finset (Finset X) // IsUnrootedTree T} → ℝ :=
    fun x T => innerSum P p T.val x
  have hsimul : ∀ x ∈ (univ : Finset ({B // B ∈ P} → X)).filter (fun x => ∀ B, x B ∈ B.val),
      ∀ T, F x T ≤ F x Tstar := by
    intro x hx T
    have hx' : IsRepTuple P x := (mem_filter.1 hx).2
    have hval : F x Tstar = quartetScore (localWeight hd hx₀ p) T₀ := by
      simp only [F, Tstar]
      rw [innerSum_eq_quartetScore h₂ hd hcut hx₀ hx', quartetScore, quartetScore]
      refine sum_congr rfl fun s₀ _ => ?_
      have := (displays_pullTree_iff (T := splice TB L) (hx'.injective hd) s₀).trans
        (displays_splice_map_iff hd hx' hTB hL hP hLP s₀)
      simp only [this]
    rw [hval]
    simp only [F]
    rw [innerSum_eq_quartetScore h₂ hd hcut hx₀ hx']
    exact hmax _ (pullTree_isUnrootedTree (hx'.injective hd) T.property hY)
  have hsum := (lemma3_5 _ F Tstar hsimul).1 ⟨T', hT'⟩
  have h33 := fun T => equation3_3 hd hne hV.cover p T
  have h1 := h33 T'
  have h2 := h33 (splice TB L)
  simp only [F, innerSum, Tstar] at hsum
  rw [← h1, ← h2] at hsum
  exact le_of_mul_le_mul_left hsum hW

/-- **Theorem 3.1** (`ecto:thm3_1`). Consider weights `p` on quartet trees, the probabilities
of a gene tree distribution, such that

1. (`ecto:eq3_1`) if a cut edge of the network separates `a, b` from `c, d`, then
   `p_ab|cd > max(p_ac|bd, p_ad|bc)`;
2. replacing a taxon by one on the same side of a cut edge, with the other three on the other side,
   does not change `p`. By `pendantChainInvariant_cutExchangeable`, this follows from the condition
   as printed, that `p_xy|zw` is determined by the induced network but does not depend on its pendant
   chains of 2-blobs and edges leading to single taxa.

Then every unrooted tree maximizing the sum over its displayed quartet trees of `p` is a resolution
of the tree of blobs. The paper's `p` is a probability; only its nonnegativity is used.

Departure from the paper: since the printed (3.3) overcounts (E1 of the report), the local objective
`f̃_m` is weighted by the product of the sizes of the four blocks (`localWeight`), and (3.3) is
`equation3_3`. The rest is the paper's route: (3.2), the maximizers of `f_R` display the resolved
quartets of the tree of blobs, a spliced tree simultaneously maximizes the inner sums of (3.3), hence
every `f_m` by Lemma 3.5, and `f_R`, hence `f` by Lemma 3.5; every maximizer of `f` maximizes `f_R`. The
paper's closing remark, that every maximizer arises by splicing, is not needed for the conclusion. -/
theorem theorem3_1 (hN : N.IsPhylogenetic) (p : QuartetTree X → ℝ) (hp : ∀ s, 0 ≤ p s)
    (h₁ : ∀ s, Displays (treeOfBlobs N) s → ∀ r ∈ s.alternatives, p r < p s)
    (h₂ : CutExchangeable N p) {T : Finset (Finset X)} (hT : IsUnrootedTree T)
    (hmax : ∀ T', IsUnrootedTree T' → quartetScore p T' ≤ quartetScore p T) :
    treeOfBlobs N ⊆ T := by
  rcases isEmpty_or_nonempty X with hX | hX
  · intro A hA
    obtain ⟨x, -⟩ := (mem_filter.1 hA).2.1
    exact hX.elim x
  set TB := treeOfBlobs N with hTBdef
  have hTB : IsUnrootedTree TB := treeOfBlobs_isUnrootedTree hN
  -- at each multifurcation, a maximizer of the local objective on the blocks
  have hM : ∀ P ∈ multifurcations TB, ∃ L₀, IsBlockFamily P L₀ ∧
      ∀ L : Finset (Finset X) → Finset (Finset X), (∀ P ∈ multifurcations TB, IsBlockFamily P (L P)) →
        L P = L₀ → ∀ T', IsUnrootedTree T' → starPart P p T' ≤ starPart P p (splice TB L) := by
    intro P hP
    obtain ⟨hV, h4⟩ := mem_multifurcations.1 hP
    have hne : ∀ B ∈ P, B.Nonempty := fun B hB => hTB.nonempty_of_mem (hV.mem B hB)
    have hd := hV.pairwiseDisjoint
    have hcut : ∀ B ∈ P, N.HasCutSplit (B : Set X) := fun B hB =>
      (mem_filter.1 (hV.mem B hB)).2.2.2
    have hY : 2 ≤ Fintype.card {B // B ∈ P} := by
      rw [Fintype.card_coe]
      omega
    obtain ⟨x₀, hx₀⟩ := exists_isRepTuple hne
    obtain ⟨T₀, hT₀, hmax₀⟩ := exists_max_quartetScore
      (pullTree_isUnrootedTree (hx₀.injective hd) hTB hY) (localWeight hd hx₀ p)
    refine ⟨T₀.image (liftBlocks P), isBlockFamily_image_liftBlocks hne hd hV.cover hT₀, ?_⟩
    intro L hL hLP T' hT'
    exact starPart_le_splice hTB hL hP h₂ hcut hd hx₀ hmax₀ hLP hT'
  choose! L hLfam hLmax using hM
  -- the spliced tree
  let Tstar : {T // IsUnrootedTree T} := ⟨splice TB L, splice_isUnrootedTree hTB hLfam⟩
  let F : Option (Finset (Finset X)) → {T : Finset (Finset X) // IsUnrootedTree T} → ℝ :=
    fun i T => i.elim (resolvedPart TB p T.val) fun P => starPart P p T.val
  have hparts : ∀ i ∈ insertNone (multifurcations TB), ∀ T, F i T ≤ F i Tstar := by
    intro i hi T
    cases i with
    | none =>
      simp only [F, Option.elim, Tstar]
      rw [resolvedPart_eq_of_subset hTB (splice_isUnrootedTree hTB hLfam) (subset_splice TB L)]
      exact resolvedPart_le hTB T.property hp h₁
    | some P =>
      exact hLmax P (mem_insertNone.1 hi _ rfl) L hLfam rfl T.val T.property
  have hsum : ∀ T : {T : Finset (Finset X) // IsUnrootedTree T},
      ∑ i ∈ insertNone (multifurcations TB), F i T = quartetScore p T.val := by
    intro T
    rw [sum_insertNone, equation3_2 hTB]
    rfl
  have hle := (lemma3_5 _ F Tstar hparts).2 ⟨T, hT⟩
    (fun T' => by rw [hsum, hsum]; exact hmax T'.val T'.property) none
    (mem_insertNone.2 fun a h => absurd h (by simp)) Tstar
  simp only [F, Option.elim, Tstar] at hle
  rw [resolvedPart_eq_of_subset hTB (splice_isUnrootedTree hTB hLfam) (subset_splice TB L)] at hle
  exact subset_of_forall_displays hT hTB fun r hr =>
    displays_of_le_resolvedPart hTB hT hp h₁ hle hr

/-- **Remark 3.2** (`ecto:rem3_2`). If on each set of four taxa the weights are the probabilities of
the three resolved quartet trees, every maximizer is binary: a multifurcation can always be resolved
so as to increase the score. The printed "arbitrarily resolved" is loose when some weights vanish: an
arbitrary resolution need not increase the score, so the proof chooses four blocks and a resolution of
their representatives with positive weight. -/
theorem remark3_2 (p : QuartetTree X → ℝ) (hp : ∀ s, 0 ≤ p s)
    (hsum : ∀ q : Finset X, q.card = 4 → ∑ r ∈ treesOn q, p r = 1) {T : Finset (Finset X)}
    (hT : IsUnrootedTree T)
    (hmax : ∀ T', IsUnrootedTree T' → quartetScore p T' ≤ quartetScore p T) :
    IsBinaryTree T := by
  -- a maximizer has no multifurcation
  have hnoM : ∀ P, ¬ (P ∈ multifurcations T) := by
    intro P hP
    obtain ⟨hV, h4⟩ := mem_multifurcations.1 hP
    have hne : ∀ B ∈ P, B.Nonempty := fun B hB => hT.nonempty_of_mem (hV.mem B hB)
    have hd := hV.pairwiseDisjoint
    obtain ⟨x, hx⟩ := exists_isRepTuple hne
    have hinj := hx.injective hd
    -- four blocks and representatives
    obtain ⟨D, -, hDc⟩ := exists_subset_card_eq (s := (univ : Finset {B // B ∈ P})) (n := 4) (by
      rw [card_univ, Fintype.card_coe]; exact h4)
    have hq : (D.image x).card = 4 := by rw [card_image_of_injective _ hinj, hDc]
    -- some resolution has positive probability
    obtain ⟨r, hr, hpr⟩ : ∃ r ∈ treesOn (D.image x), 0 < p r := by
      by_contra hcon
      push Not at hcon
      have := sum_nonpos hcon
      rw [hsum _ hq] at this
      linarith
    have hrt := mem_treesOn.1 hr
    obtain ⟨r₀, rfl⟩ := QuartetTree.exists_map_eq hinj r (by
      rw [hrt]; exact image_subset_image (subset_univ _))
    have hdist : InDistinctBlocks P (r₀.map hinj).taxa :=
      hx.inDistinctBlocks hd (by rw [hrt]; exact image_subset_image (subset_univ _))
    -- the corresponding split, two blocks versus the rest
    obtain ⟨C₀, hC₀⟩ : ∃ C₀, C₀ ∈ r₀.val := by
      have h2 := r₀.property.1
      exact card_pos.1 (by omega)
    have hCc := r₀.card_of_mem hC₀
    have hCc' := r₀.card_of_mem (r₀.sdiff_mem hC₀)
    have hCne : C₀.Nonempty := card_pos.1 (by omega)
    have hCne' : C₀ᶜ.Nonempty := by
      obtain ⟨c, hc⟩ := card_pos.1 (show 0 < (r₀.taxa \ C₀).card by omega)
      exact ⟨c, mem_compl.2 (mem_sdiff.1 hc).2⟩
    let A := liftBlocks P C₀
    have hAc : Aᶜ = liftBlocks P C₀ᶜ := (liftBlocks_compl hd hV.cover C₀).symm
    let L : Finset (Finset X) → Finset (Finset X) := fun P' => if P' = P then {A, Aᶜ} else ∅
    have hL : ∀ P' ∈ multifurcations T, IsBlockFamily P' (L P') := by
      intro P' _
      by_cases he : P' = P
      · subst he
        have hfam : L P' = {A, Aᶜ} := ite_eq_left rfl
        rw [hfam]
        have hmem : ∀ B ∈ ({A, Aᶜ} : Finset (Finset X)), B = A ∨ B = Aᶜ := by simp
        have hAne : A.Nonempty := liftBlocks_nonempty hne hCne
        have hAne' : Aᶜ.Nonempty := hAc ▸ liftBlocks_nonempty hne hCne'
        refine ⟨?_, ?_, ?_, ?_, ?_⟩
        · intro B hB
          rcases hmem B hB with rfl | rfl
          · exact isBlockUnion_liftBlocks hd C₀
          · rw [hAc]
            exact isBlockUnion_liftBlocks hd _
        · intro B hB
          rcases hmem B hB with rfl | rfl
          · exact hAne
          · exact hAne'
        · intro B hB
          rcases hmem B hB with rfl | rfl
          · exact hAne'
          · rw [compl_compl]
            exact hAne
        · intro B hB
          rcases hmem B hB with rfl | rfl
          · simp
          · simp
        · intro B hB B' hB'
          rcases hmem B hB with rfl | rfl <;> rcases hmem B' hB' with rfl | rfl
          · exact Or.inl (Subset.refl _)
          · exact Or.inr (Or.inr (Or.inl disjoint_compl_right))
          · exact Or.inr (Or.inr (Or.inl disjoint_compl_left))
          · exact Or.inl (Subset.refl _)
      · have hfam : L P' = ∅ := ite_eq_right he
        rw [hfam]
        exact ⟨by simp, by simp, by simp, by simp, by simp⟩
    have hT' := splice_isUnrootedTree hT hL
    have hdisp : Displays (splice T L) (r₀.map hinj) := by
      refine mem_splice.2 (Or.inr ⟨P, hP, ?_⟩) |> fun h => ⟨A, h, ?_⟩
      · simp only [L, ↓reduceIte]
        simp
      · rw [QuartetTree.map_taxa, hx.liftBlocks_inter_image hd, QuartetTree.map_val]
        have : C₀ ∩ r₀.taxa = C₀ := inter_eq_left.2 (r₀.subset_taxa hC₀)
        rw [this]
        exact mem_image_of_mem _ hC₀
    have hnot := not_displays_of_inDistinctBlocks hV hdist
    -- all displayed quartets stay displayed, and `p ≥ 0`: the score increases
    have hlt : quartetScore p T < quartetScore p (splice T L) := by
      refine sum_lt_sum (fun s _ => ?_) ⟨r₀.map hinj, mem_univ _, ?_⟩
      · by_cases hs : Displays T s
        · have := hs.mono (subset_splice T L)
          simp only [hs, this, ↓reduceIte, le_refl]
        · simp only [hs, ↓reduceIte]
          split_ifs
          · exact hp s
          · exact le_refl _
      · simp only [hnot, hdisp, ↓reduceIte]
        exact hpr
    exact absurd (hmax _ hT') (not_le.2 hlt)
  by_cases hX : 2 ≤ Fintype.card X
  · have hSF := hT.isSplitFamily hX
    obtain ⟨r⟩ : Nonempty X := Fintype.card_pos_iff.1 (by omega)
    have hH := rootedAt_isHierarchy hSF r
    have hun := unroot_rootedAt hSF r
    refine ⟨rootedAt T r, hH, hun, fun A hA hA2 => ?_⟩
    apply le_antisymm _ (hH.two_le_card_childClusters hA2)
    by_cases hAu : A = univ
    · -- the root has the children `{r}` and its complement
      subst hAu
      have hsub : childClusters (rootedAt T r) univ ⊆ {{r}, {r}ᶜ} := by
        intro B hB
        obtain ⟨hBH, hBu, hmaxB⟩ := mem_childClusters.1 hB
        rcases mem_rootedAt.1 hBH with rfl | rfl | ⟨hBT, hrB⟩
        · exact absurd hBu (ssubset_irrefl _)
        · simp
        · by_cases he : B = {r}ᶜ
          · simp [he]
          · exfalso
            have hBs : B ⊂ {r}ᶜ := ssubset_of_subset_of_ne (fun y hy => by
              simp only [mem_compl, mem_singleton]
              rintro rfl
              exact hrB hy) he
            refine hmaxB {r}ᶜ (mem_rootedAt.2 (Or.inr (Or.inr
              ⟨hSF.compl_mem _ (hSF.singleton_mem r), by simp⟩))) hBs ?_
            refine ssubset_univ_iff.2 fun h => ?_
            have : r ∈ ({r} : Finset X)ᶜ := h ▸ mem_univ r
            simp at this
      exact (card_le_card hsub).trans card_le_two
    · have hVP := hH.isVertexPartition_insert_compl hA hAu hA2
      rw [hun] at hVP
      have hnot4 : ¬ 4 ≤ (insert Aᶜ (childClusters (rootedAt T r) A)).card := fun h =>
        hnoM _ (mem_multifurcations.2 ⟨hVP, h⟩)
      have := card_le_card (subset_insert Aᶜ (childClusters (rootedAt T r) A))
      have hnotin : Aᶜ ∉ childClusters (rootedAt T r) A := by
        intro h
        obtain ⟨h1, h2, -⟩ := mem_childClusters.1 h
        obtain ⟨y, hy⟩ := hH.2.2.1 _ h1
        exact mem_compl.1 hy (h2.subset hy)
      rw [card_insert_of_notMem hnotin] at hnot4
      omega
  · obtain ⟨H, hH, hu⟩ := hT
    exact ⟨H, hH, hu, fun A _ hA2 => absurd (hA2.trans (card_le_univ A)) hX⟩

/-! ### The literal form of condition 2 -/

/-- The arcs of the network induced on `Y`: those ancestral to `Y` below its LSA. -/
def inducedArcs (N : RootedNetwork V E X) (Y : Set X) : Set E :=
  {e | e ∈ N.ancestralArcs Y ∧ ∃ v, N.IsLeastStableAncestor Y v ∧ N.graph.Reaches v (N.graph.source e)}

/-- `e`, with side `S`, is a cut edge of the network induced on `Y` separating exactly the taxon `x`. -/
def IsPendantCut (N : RootedNetwork V E X) (Y : Set X) (x : X) (e : E) (S : Set V) : Prop :=
  e ∈ inducedArcs N Y ∧ (∀ f ∈ inducedArcs N Y, N.graph.Crosses f S ↔ f = e) ∧
    ∀ y ∈ Y, N.leaf y ∈ S ↔ y = x

/-- The arcs of the induced network on `Y` that are not on the pendant chain leading to a taxon of
`Y`: what remains without the pendant chains of 2-blobs and edges. -/
def coreArcs (N : RootedNetwork V E X) (Y : Set X) : Set E :=
  {f | f ∈ inducedArcs N Y ∧ ¬ ∃ x ∈ Y, ∃ e S, IsPendantCut N Y x e S ∧
    (f = e ∨ (N.graph.source f ∈ S ∧ N.graph.target f ∈ S))}

/-- `v` is the vertex at which the pendant chain of the taxon `x` of `Y` attaches to the rest of the
network induced on `Y`. -/
def AttachesAt (N : RootedNetwork V E X) (Y : Set X) (x : X) (v : V) : Prop :=
  ∃ e S, IsPendantCut N Y x e S ∧ v ∉ S ∧ (N.graph.source e = v ∨ N.graph.target e = v) ∧
    ∀ e' S', IsPendantCut N Y x e' S' → ∀ u ∈ S', N.graph.Reaches N.root u → u ∈ S

/-- Condition 2 of Theorem 3.1 as printed, for a network with fixed numerical parameters: `p_xy|zw`
depends on the induced network on `x, y, z, w` only through what remains without its pendant chains,
and where those chains attach. It is stated for two quartet trees on sets of taxa of the same
network, for which the same arcs carry the same numerical parameters. -/
def PendantChainInvariant (N : RootedNetwork V E X) (p : QuartetTree X → ℝ) : Prop :=
  ∀ (s s' : QuartetTree X) (g : X → X), Set.InjOn g s.taxa →
    s'.val = s.val.image (fun B => B.image g) →
    coreArcs N (s.taxa : Set X) = coreArcs N (s'.taxa : Set X) →
    (∀ x ∈ s.taxa, ∀ v, AttachesAt N (s.taxa : Set X) x v ↔ AttachesAt N (s'.taxa : Set X) (g x) v) →
    p s = p s'

namespace PendantChain

/-! #### The proof of `pendantChainInvariant_cutExchangeable`

Let a cut edge `g` have `a, a'` on the side `Z` and the set `Q` of the other taxa on the other side.
The networks induced on `insert a Q` and on `insert a' Q` have the same vertices outside `Z`, both
contain `g`, and each side of `g` is connected in them. Hence a pendant cut of one gives a pendant cut
of the other, and what `g` leaves on the side of `Q` is the same in both. -/

/-- The vertices of the network induced on `Y`: below its LSA and ancestral to `Y`. -/
def inducedVertices (N : RootedNetwork V E X) (Y : Set X) : Set V :=
  {t | (∃ v, N.IsLeastStableAncestor Y v ∧ N.graph.Reaches v t) ∧
    ∃ y ∈ Y, N.graph.Reaches t (N.leaf y)}

omit [Fintype X] [DecidableEq X] in
theorem mem_inducedArcs_iff {Y : Set X} {e : E} :
    e ∈ inducedArcs N Y ↔
      N.graph.source e ∈ inducedVertices N Y ∧ N.graph.target e ∈ inducedVertices N Y := by
  have hstep : N.graph.Reaches (N.graph.source e) (N.graph.target e) :=
    Relation.ReflTransGen.single ⟨e, rfl, rfl⟩
  constructor
  · rintro ⟨⟨y, hy, hr⟩, v, hv, hs⟩
    exact ⟨⟨⟨v, hv, hs⟩, y, hy, hstep.trans hr⟩, ⟨v, hv, hs.trans hstep⟩, y, hy, hr⟩
  · rintro ⟨⟨⟨v, hv, hs⟩, -⟩, -, y, hy, hr⟩
    exact ⟨⟨y, hy, hr⟩, v, hv, hs⟩

omit [Fintype X] [DecidableEq X] in
theorem crosses_compl {f : E} {S : Set V} : N.graph.Crosses f Sᶜ ↔ N.graph.Crosses f S := by
  simp only [DirectedMultigraph.Crosses, Set.mem_compl_iff, not_not]
  tauto

omit [Fintype X] [DecidableEq X] in
theorem mem_iff_of_not_crosses {f : E} {S : Set V} (h : ¬ N.graph.Crosses f S) :
    N.graph.source f ∈ S ↔ N.graph.target f ∈ S := by
  simp only [DirectedMultigraph.Crosses, not_or, not_and, not_not] at h
  exact ⟨h.1, h.2⟩

omit [Fintype X] [DecidableEq X] in
theorem crosses_congr {f : E} {S S' : Set V} (h₁ : N.graph.source f ∈ S ↔ N.graph.source f ∈ S')
    (h₂ : N.graph.target f ∈ S ↔ N.graph.target f ∈ S') :
    N.graph.Crosses f S ↔ N.graph.Crosses f S' := by
  simp only [DirectedMultigraph.Crosses, h₁, h₂]

section Cut

variable {W : Set V} {g : E}

omit [Fintype X] [DecidableEq X] in
/-- A cut edge whose side `W` avoids the root enters `W`. -/
theorem cut_enter (hN : N.IsPhylogenetic) (hW : ∀ f, N.graph.Crosses f W ↔ f = g)
    (hroot : N.root ∉ W) {t : V} (ht : t ∈ W) :
    N.graph.source g ∉ W ∧ N.graph.target g ∈ W := by
  have key : ∀ v, N.graph.Reaches N.root v → v ∈ W →
      N.graph.source g ∉ W ∧ N.graph.target g ∈ W := by
    intro v hv
    induction hv with
    | refl => exact fun h => absurd h hroot
    | @tail b c hab hbc ih =>
      intro hc
      by_cases hb : b ∈ W
      · exact ih hb
      · obtain ⟨f, hs, ht'⟩ := hbc
        have hf := (hW f).1 (Or.inr ⟨ht' ▸ hc, hs ▸ hb⟩)
        subst hf
        exact ⟨hs ▸ hb, ht' ▸ hc⟩
  exact key t (hN.root_reaches t) ht

omit [Fintype X] [DecidableEq X] in
/-- The side of a cut edge avoiding the root is closed under descent. -/
theorem cut_closed (hN : N.IsPhylogenetic) (hW : ∀ f, N.graph.Crosses f W ↔ f = g)
    (hroot : N.root ∉ W) {p q : V} (hp : p ∈ W) (h : N.graph.Reaches p q) : q ∈ W := by
  induction h with
  | refl => exact hp
  | @tail b c hab hbc ih =>
    obtain ⟨f, hs, ht⟩ := hbc
    by_contra hc
    have hf := (hW f).1 (Or.inl ⟨hs ▸ ih, ht ▸ hc⟩)
    subst hf
    exact (cut_enter hN hW hroot ih).1 (hs ▸ ih)

omit [Fintype X] [DecidableEq X] in
/-- A path entering the side avoiding the root uses the cut edge. -/
theorem cut_entry (hW : ∀ f, N.graph.Crosses f W ↔ f = g)
    {p t : V} (hp : p ∉ W) (h : N.graph.Reaches p t) (ht : t ∈ W) :
    N.graph.Reaches p (N.graph.source g) ∧ N.graph.Reaches (N.graph.target g) t := by
  induction h with
  | refl => exact absurd ht hp
  | @tail b c hab hbc ih =>
    by_cases hb : b ∈ W
    · exact ⟨(ih hb).1, (ih hb).2.tail hbc⟩
    · obtain ⟨f, hs, ht'⟩ := hbc
      have hf := (hW f).1 (Or.inr ⟨ht' ▸ ht, hs ▸ hb⟩)
      subst hf
      exact ⟨hs ▸ hab, ht' ▸ Relation.ReflTransGen.refl⟩

omit [Fintype X] [DecidableEq X] in
/-- A path of `R`, avoiding `v`, into the side `W` has a prefix to the cut edge. -/
theorem avoid_prefix {v : V} (hW : ∀ f, N.graph.Crosses f W ↔ f = g) (hroot : N.root ∉ W) {t : V}
    (h : Relation.ReflTransGen (fun a b => N.graph.Adj a b ∧ a ≠ v ∧ b ≠ v) N.root t) (ht : t ∈ W) :
    Relation.ReflTransGen (fun a b => N.graph.Adj a b ∧ a ≠ v ∧ b ≠ v) N.root (N.graph.source g) ∧
      N.graph.source g ≠ v := by
  induction h with
  | refl => exact absurd ht hroot
  | @tail b c hab hbc ih =>
    by_cases hb : b ∈ W
    · exact ih hb
    · obtain ⟨⟨f, hs, ht'⟩, hne, -⟩ := hbc
      have hf := (hW f).1 (Or.inr ⟨ht' ▸ ht, hs ▸ hb⟩)
      subst hf
      exact ⟨hs ▸ hab, hs ▸ hne⟩

/-- A path inside the side `W` avoids every vertex outside. -/
theorem avoid_in_cut (hN : N.IsPhylogenetic) (hW : ∀ f, N.graph.Crosses f W ↔ f = g)
    (hroot : N.root ∉ W) {v p t : V} (hv : v ∉ W) (hp : p ∈ W) (h : N.graph.Reaches p t) :
    Relation.ReflTransGen (fun a b => N.graph.Adj a b ∧ a ≠ v ∧ b ≠ v) p t := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | @tail b c hab hbc ih =>
    have hb := cut_closed hN hW hroot hp hab
    have hc := cut_closed hN hW hroot hb (Relation.ReflTransGen.single hbc)
    exact ih.tail ⟨hbc, fun e => hv (e ▸ hb), fun e => hv (e ▸ hc)⟩

end Cut

omit [Fintype X] [DecidableEq X] in
/-- A path into a vertex that `v` does not reach avoids `v`. -/
theorem avoid_of_not_reaches {v t u : V} (hnot : ¬ N.graph.Reaches v t) (h : N.graph.Reaches u t) :
    Relation.ReflTransGen (fun a b => N.graph.Adj a b ∧ a ≠ v ∧ b ≠ v) u t := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact Relation.ReflTransGen.refl
  | @head a b hab hbt ih =>
    exact ih.head ⟨hab, fun e => hnot (e ▸ Relation.ReflTransGen.head hab hbt), fun e => hnot (e ▸ hbt)⟩

omit [Fintype X] [DecidableEq X] in
/-- A path from a vertex that does not reach `v` avoids `v`. -/
theorem avoid_of_not_reaches_forward {v t u : V} (hnot : ¬ N.graph.Reaches u v)
    (h : N.graph.Reaches u t) :
    Relation.ReflTransGen (fun a b => N.graph.Adj a b ∧ a ≠ v ∧ b ≠ v) u t := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | @tail b c hab hbc ih =>
    exact ih.tail ⟨hbc, fun e => hnot (e ▸ hab), fun e => hnot (e ▸ hab.tail hbc)⟩

omit [Fintype X] [DecidableEq X] in
/-- A stable ancestor reaches the taxa. -/
theorem stable_reaches (hN : N.IsPhylogenetic) {Y : Set X} {v : V} (hv : N.IsStableAncestor Y v)
    {y : X} (hy : y ∈ Y) : N.graph.Reaches v (N.leaf y) := by
  by_contra hnot
  refine hv y hy ⟨fun e => hnot (e ▸ hN.root_reaches _), fun e => hnot (e ▸ Relation.ReflTransGen.refl),
    avoid_of_not_reaches hnot (hN.root_reaches _)⟩

/-- The least stable ancestor of a nonempty set of taxa exists. -/
theorem exists_leastStableAncestor (hN : N.IsPhylogenetic) {Y : Set X} (hY : Y.Nonempty) :
    ∃ v, N.IsLeastStableAncestor Y v := by
  have : Finite V := hN.finite_vertices
  obtain ⟨y, hy⟩ := hY
  have htotal : ∀ v w, N.IsStableAncestor Y v → N.IsStableAncestor Y w →
      N.graph.Reaches w v ∨ N.graph.Reaches v w := by
    intro v w hv hw
    by_contra hcon
    push Not at hcon
    obtain ⟨h1, h2⟩ := hcon
    refine hw y hy ⟨fun e => h1 (e ▸ hN.root_reaches v), fun e => h2 (e ▸ stable_reaches hN hv hy), ?_⟩
    exact (avoid_of_not_reaches h1 (hN.root_reaches v)).trans
      (avoid_of_not_reaches_forward h2 (stable_reaches hN hv hy))
  let r : V → V → Prop := fun x a => Relation.TransGen N.graph.Adj a x
  have : IsTrans V r := ⟨fun a b c hab hbc => hbc.trans hab⟩
  have : Std.Irrefl r := ⟨fun a h => hN.acyclic a h⟩
  have hwf : WellFounded r := Finite.wellFounded_of_trans_of_irrefl r
  obtain ⟨v, hv, hmin⟩ := hwf.has_min {v | N.IsStableAncestor Y v} ⟨N.root, N.root_isStableAncestor Y⟩
  refine ⟨v, hv, fun w hw => ?_⟩
  rcases htotal v w hv hw with h | h
  · exact h
  · rcases Relation.reflTransGen_iff_eq_or_transGen.1 h with rfl | h'
    · exact Relation.ReflTransGen.refl
    · exact absurd h' (hmin w hw)

omit [Fintype X] [DecidableEq X] in
theorem leastStableAncestor_unique (hN : N.IsPhylogenetic) {Y : Set X} {v w : V}
    (hv : N.IsLeastStableAncestor Y v) (hw : N.IsLeastStableAncestor Y w) : v = w := by
  have h1 := hw.2 v hv.1
  have h2 := hv.2 w hw.1
  rcases Relation.reflTransGen_iff_eq_or_transGen.1 h1 with h | h
  · exact h.symm
  · exact absurd (h.trans_left h2) (hN.acyclic v)

/-- What the proof uses of the network induced on `Y`, with the cut edge `g` of side `Z`. -/
structure SideFacts (N : RootedNetwork V E X) (Y : Set X) (Z : Set V) (g : E) : Prop where
  source_mem : N.graph.source g ∈ inducedVertices N Y
  target_mem : N.graph.target g ∈ inducedVertices N Y
  leaf_mem : ∀ y ∈ Y, N.leaf y ∈ inducedVertices N Y
  conn_in : ∀ S : Set V, (∀ f ∈ inducedArcs N Y, N.graph.source f ∈ Z → N.graph.target f ∈ Z →
      ¬ N.graph.Crosses f S) → ∀ t ∈ inducedVertices N Y, ∀ t' ∈ inducedVertices N Y, t ∈ Z → t' ∈ Z →
      (t ∈ S ↔ t' ∈ S)
  conn_out : ∀ S : Set V, (∀ f ∈ inducedArcs N Y, N.graph.source f ∉ Z → N.graph.target f ∉ Z →
      ¬ N.graph.Crosses f S) → ∀ t ∈ inducedVertices N Y, ∀ t' ∈ inducedVertices N Y, t ∉ Z → t' ∉ Z →
      (t ∈ S ↔ t' ∈ S)

omit [Fintype X] [DecidableEq X] in
theorem SideFacts.compl {Y : Set X} {Z : Set V} {g : E} (h : SideFacts N Y Z g) :
    SideFacts N Y Zᶜ g where
  source_mem := h.source_mem
  target_mem := h.target_mem
  leaf_mem := h.leaf_mem
  conn_in S hS t ht t' ht' h1 h2 :=
    h.conn_out S (fun f hf h3 h4 => hS f hf h3 h4) t ht t' ht' h1 h2
  conn_out S hS t ht t' ht' h1 h2 :=
    h.conn_in S (fun f hf h3 h4 => hS f hf (not_not.2 h3) (not_not.2 h4)) t ht t' ht'
      (not_not.1 h1) (not_not.1 h2)

/-- A stable ancestor outside the side `W` of a cut edge, for a taxon in `W`, reaches the cut edge. -/
theorem stable_reaches_source (hN : N.IsPhylogenetic) {W : Set V} {g : E}
    (hW : ∀ f, N.graph.Crosses f W ↔ f = g) (hroot : N.root ∉ W) {Y : Set X} {v : V}
    (hv : N.IsStableAncestor Y v) {y : X} (hy : y ∈ Y) (hyW : N.leaf y ∈ W) (hvW : v ∉ W) :
    N.graph.Reaches v (N.graph.source g) := by
  by_contra hnot
  have h1 := avoid_of_not_reaches hnot (hN.root_reaches (N.graph.source g))
  have h2 := (cut_entry hW hroot (hN.root_reaches (N.leaf y)) hyW).2
  have hgW := cut_enter hN hW hroot hyW
  have h3 := avoid_in_cut hN hW hroot hvW hgW.2 h2
  refine hv y hy ⟨fun e => hnot (e ▸ hN.root_reaches _), fun e => hvW (e ▸ hyW), h1.trans
    (Relation.ReflTransGen.head ⟨⟨g, rfl, rfl⟩, fun e => hnot (e ▸ Relation.ReflTransGen.refl),
      fun e => hvW (e ▸ hgW.2)⟩ h3)⟩

/-- The facts on the side `W` of the cut edge avoiding the root. -/
theorem sideFacts_of_cut (hN : N.IsPhylogenetic) {W : Set V} {g : E}
    (hW : ∀ f, N.graph.Crosses f W ↔ f = g) (hroot : N.root ∉ W) {Y : Set X} {y₁ y₂ : X}
    (hy₁ : y₁ ∈ Y) (hy₁W : N.leaf y₁ ∈ W) (hy₂ : y₂ ∈ Y) (hy₂W : N.leaf y₂ ∉ W) :
    SideFacts N Y W g := by
  obtain ⟨L, hL⟩ := exists_leastStableAncestor hN ⟨y₁, hy₁⟩
  have hLW : L ∉ W := fun h => hy₂W (cut_closed hN hW hroot h (stable_reaches hN hL.1 hy₂))
  have hstep : N.graph.Reaches (N.graph.source g) (N.graph.target g) :=
    Relation.ReflTransGen.single ⟨g, rfl, rfl⟩
  have hLs := stable_reaches_source hN hW hroot hL.1 hy₁ hy₁W hLW
  have hLt := hLs.trans hstep
  have hty := (cut_entry hW hroot (hN.root_reaches _) hy₁W).2
  have hgW := cut_enter hN hW hroot hy₁W
  have hmemV : ∀ t, N.graph.Reaches L t → (∃ y ∈ Y, N.graph.Reaches t (N.leaf y)) →
      t ∈ inducedVertices N Y := fun t h1 h2 => ⟨⟨L, hL, h1⟩, h2⟩
  have hVL : ∀ t ∈ inducedVertices N Y, N.graph.Reaches L t ∧
      ∃ y ∈ Y, N.graph.Reaches t (N.leaf y) := by
    rintro t ⟨⟨v, hv, hr⟩, h⟩
    exact ⟨leastStableAncestor_unique hN hv hL ▸ hr, h⟩
  refine ⟨hmemV _ hLs ⟨y₁, hy₁, hstep.trans hty⟩, hmemV _ hLt ⟨y₁, hy₁, hty⟩,
    fun y hy => hmemV _ (stable_reaches hN hL.1 hy) ⟨y, hy, Relation.ReflTransGen.refl⟩, ?_, ?_⟩
  · intro S hS
    have key : ∀ u, N.graph.Reaches (N.graph.target g) u →
        (∃ y ∈ Y, N.graph.Reaches u (N.leaf y)) → (u ∈ S ↔ N.graph.target g ∈ S) := by
      intro u hu
      induction hu with
      | refl => exact fun _ => Iff.rfl
      | @tail b c hab hbc ih =>
        rintro ⟨y, hy, hc⟩
        have hb' := ih ⟨y, hy, Relation.ReflTransGen.head hbc hc⟩
        have hbW := cut_closed hN hW hroot hgW.2 hab
        have hcW := cut_closed hN hW hroot hbW (Relation.ReflTransGen.single hbc)
        have hLb := hLt.trans hab
        obtain ⟨f, hs, ht⟩ := id hbc
        have hfI : f ∈ inducedArcs N Y := mem_inducedArcs_iff.2
          ⟨hs ▸ hmemV b hLb ⟨y, hy, Relation.ReflTransGen.head hbc hc⟩,
            ht ▸ hmemV c (hLb.tail hbc) ⟨y, hy, hc⟩⟩
        have hiff := mem_iff_of_not_crosses (hS f hfI (hs ▸ hbW) (ht ▸ hcW))
        rw [hs, ht] at hiff
        exact hiff.symm.trans hb'
    intro t ht t' ht' h1 h2
    exact (key t (cut_entry hW hroot (hN.root_reaches t) h1).2 (hVL t ht).2).trans
      (key t' (cut_entry hW hroot (hN.root_reaches t') h2).2 (hVL t' ht').2).symm
  · intro S hS
    have key : ∀ u, N.graph.Reaches L u → u ∉ W →
        (∃ y ∈ Y, N.graph.Reaches u (N.leaf y)) → (u ∈ S ↔ L ∈ S) := by
      intro u hu
      induction hu with
      | refl => exact fun _ _ => Iff.rfl
      | @tail b c hab hbc ih =>
        rintro hcW ⟨y, hy, hc⟩
        have hbW : b ∉ W := fun h => hcW (cut_closed hN hW hroot h (Relation.ReflTransGen.single hbc))
        have hb' := ih hbW ⟨y, hy, Relation.ReflTransGen.head hbc hc⟩
        obtain ⟨f, hs, ht⟩ := id hbc
        have hfI : f ∈ inducedArcs N Y := mem_inducedArcs_iff.2
          ⟨hs ▸ hmemV b hab ⟨y, hy, Relation.ReflTransGen.head hbc hc⟩,
            ht ▸ hmemV c (hab.tail hbc) ⟨y, hy, hc⟩⟩
        have hiff := mem_iff_of_not_crosses (hS f hfI (hs ▸ hbW) (ht ▸ hcW))
        rw [hs, ht] at hiff
        exact hiff.symm.trans hb'
    intro t ht t' ht' h1 h2
    exact (key t (hVL t ht).1 h1 (hVL t ht).2).trans (key t' (hVL t' ht').1 h2 (hVL t' ht').2).symm

section Exchange

variable {a a' : X} {Q : Set X} {W : Set V} {g : E}

/-- Below the cut edge: the stable ancestors do not see which of the two taxa is below it. -/
theorem stable_insert_of_low (hN : N.IsPhylogenetic) (hW : ∀ f, N.graph.Crosses f W ↔ f = g)
    (hroot : N.root ∉ W) (haW : N.leaf a ∈ W) (ha'W : N.leaf a' ∈ W) {b : X} (hb : b ∈ Q)
    (hbW : N.leaf b ∉ W) {v : V} (hv : N.IsStableAncestor (insert a Q) v) :
    N.IsStableAncestor (insert a' Q) v := by
  intro y hy
  rcases Set.mem_insert_iff.1 hy with rfl | hy
  · rintro ⟨h1, h2, h3⟩
    have hvW : v ∉ W := fun h =>
      hbW (cut_closed hN hW hroot h (stable_reaches hN hv (Set.mem_insert_of_mem _ hb)))
    have hpre := avoid_prefix hW hroot h3 ha'W
    have hg := cut_enter hN hW hroot haW
    have htarget := (cut_entry hW hroot (hN.root_reaches (N.leaf a)) haW).2
    exact hv a (Set.mem_insert _ _) ⟨h1, fun e => hvW (e ▸ haW), hpre.1.trans
      (Relation.ReflTransGen.head ⟨⟨g, rfl, rfl⟩, hpre.2, fun e => hvW (e ▸ hg.2)⟩
        (avoid_in_cut hN hW hroot hvW hg.2 htarget))⟩
  · exact hv y (Set.mem_insert_of_mem _ hy)

theorem inducedVertices_of_low (hN : N.IsPhylogenetic) (hW : ∀ f, N.graph.Crosses f W ↔ f = g)
    (hroot : N.root ∉ W) (haW : N.leaf a ∈ W) (ha'W : N.leaf a' ∈ W) {b : X} (hb : b ∈ Q)
    (hbW : N.leaf b ∉ W) {t : V} (ht : t ∉ W) (h : t ∈ inducedVertices N (insert a Q)) :
    t ∈ inducedVertices N (insert a' Q) := by
  obtain ⟨⟨v, hv, hr⟩, y, hy, hty⟩ := h
  have hLSA : N.IsLeastStableAncestor (insert a' Q) v :=
    ⟨stable_insert_of_low hN hW hroot haW ha'W hb hbW hv.1, fun w hw =>
      hv.2 w (stable_insert_of_low hN hW hroot ha'W haW hb hbW hw)⟩
  refine ⟨⟨v, hLSA, hr⟩, ?_⟩
  rcases Set.mem_insert_iff.1 hy with rfl | hy
  · refine ⟨a', Set.mem_insert _ _, ?_⟩
    exact ((cut_entry hW ht hty haW).1.tail ⟨g, rfl, rfl⟩).trans
      (cut_entry hW hroot (hN.root_reaches _) ha'W).2
  · exact ⟨y, Set.mem_insert_of_mem _ hy, hty⟩

theorem inducedVertices_of_high (hN : N.IsPhylogenetic) (hW : ∀ f, N.graph.Crosses f W ↔ f = g)
    (hroot : N.root ∉ W) (haW : N.leaf a ∉ W) (ha'W : N.leaf a' ∉ W) (hQ : ∀ y ∈ Q, N.leaf y ∈ W)
    {b : X} (hb : b ∈ Q) {t : V} (ht : t ∈ W) (h : t ∈ inducedVertices N (insert a Q)) :
    t ∈ inducedVertices N (insert a' Q) := by
  obtain ⟨-, y, hy, hty⟩ := h
  have hyW := cut_closed hN hW hroot ht hty
  have hyQ : y ∈ Q := by
    rcases Set.mem_insert_iff.1 hy with rfl | hy
    · exact absurd hyW haW
    · exact hy
  obtain ⟨L, hL⟩ := exists_leastStableAncestor hN (Set.insert_nonempty a' Q)
  have hLW : L ∉ W := fun h' =>
    ha'W (cut_closed hN hW hroot h' (stable_reaches hN hL.1 (Set.mem_insert _ _)))
  have hLs := stable_reaches_source hN hW hroot hL.1 (Set.mem_insert_of_mem _ hb) (hQ b hb) hLW
  have hgt := (cut_entry hW hroot (hN.root_reaches t) ht).2
  exact ⟨⟨L, hL, (hLs.tail ⟨g, rfl, rfl⟩).trans hgt⟩, y, Set.mem_insert_of_mem _ hyQ, hty⟩

/-- The induced networks on `insert a Q` and on `insert a' Q`, where the cut edge `g` of side `Z`
has `a, a'` on `Z` and `Q` off it. -/
structure PendantSetting (N : RootedNetwork V E X) (Z : Set V) (g : E) (a a' : X) (Q : Set X) :
    Prop where
  hZ : ∀ f, N.graph.Crosses f Z ↔ f = g
  ha : N.leaf a ∈ Z
  ha' : N.leaf a' ∈ Z
  hQ : ∀ y ∈ Q, N.leaf y ∉ Z
  two : ∃ b ∈ Q, ∃ c ∈ Q, b ≠ c
  facts : SideFacts N (insert a Q) Z g
  facts' : SideFacts N (insert a' Q) Z g
  hV : ∀ t, t ∉ Z → (t ∈ inducedVertices N (insert a Q) ↔ t ∈ inducedVertices N (insert a' Q))

omit [Fintype X] [DecidableEq X] in
theorem PendantSetting.symm {Z : Set V} (h : PendantSetting N Z g a a' Q) :
    PendantSetting N Z g a' a Q :=
  ⟨h.hZ, h.ha', h.ha, h.hQ, h.two, h.facts', h.facts, fun t ht => (h.hV t ht).symm⟩

theorem pendantSetting_of_cut (hN : N.IsPhylogenetic) {Z : Set V}
    (hZ : ∀ f, N.graph.Crosses f Z ↔ f = g) (ha : N.leaf a ∈ Z) (ha' : N.leaf a' ∈ Z)
    (hQ : ∀ y ∈ Q, N.leaf y ∉ Z) (two : ∃ b ∈ Q, ∃ c ∈ Q, b ≠ c) :
    PendantSetting N Z g a a' Q := by
  obtain ⟨b, hb, -⟩ := id two
  by_cases hroot : N.root ∈ Z
  · have hW : ∀ f, N.graph.Crosses f Zᶜ ↔ f = g := fun f => crosses_compl.trans (hZ f)
    have hrW : N.root ∉ Zᶜ := not_not.2 hroot
    have hbW : N.leaf b ∈ Zᶜ := hQ b hb
    have haW : N.leaf a ∉ Zᶜ := not_not.2 ha
    have ha'W : N.leaf a' ∉ Zᶜ := not_not.2 ha'
    have F₁ := sideFacts_of_cut hN hW hrW (Set.mem_insert_of_mem a hb) hbW (Set.mem_insert a Q) haW
    have F₂ := sideFacts_of_cut hN hW hrW (Set.mem_insert_of_mem a' hb) hbW (Set.mem_insert a' Q) ha'W
    have F₁' := F₁.compl
    have F₂' := F₂.compl
    rw [compl_compl] at F₁' F₂'
    exact ⟨hZ, ha, ha', hQ, two, F₁', F₂', fun t ht =>
      ⟨inducedVertices_of_high hN hW hrW haW ha'W hQ hb ht,
        inducedVertices_of_high hN hW hrW ha'W haW hQ hb ht⟩⟩
  · exact ⟨hZ, ha, ha', hQ, two,
      sideFacts_of_cut hN hZ hroot (Set.mem_insert a Q) ha (Set.mem_insert_of_mem a hb) (hQ b hb),
      sideFacts_of_cut hN hZ hroot (Set.mem_insert a' Q) ha' (Set.mem_insert_of_mem a' hb) (hQ b hb),
      fun t ht => ⟨inducedVertices_of_low hN hZ hroot ha ha' hb (hQ b hb) ht,
        inducedVertices_of_low hN hZ hroot ha' ha hb (hQ b hb) ht⟩⟩

omit [Fintype X] [DecidableEq X] in
theorem arc_cases {Z : Set V} (hZ : ∀ f, N.graph.Crosses f Z ↔ f = g) (f : E) :
    f = g ∨ (N.graph.source f ∈ Z ∧ N.graph.target f ∈ Z) ∨
      (N.graph.source f ∉ Z ∧ N.graph.target f ∉ Z) := by
  by_cases h1 : N.graph.source f ∈ Z <;> by_cases h2 : N.graph.target f ∈ Z
  · exact Or.inr (Or.inl ⟨h1, h2⟩)
  · exact Or.inl ((hZ f).1 (Or.inl ⟨h1, h2⟩))
  · exact Or.inl ((hZ f).1 (Or.inr ⟨h2, h1⟩))
  · exact Or.inr (Or.inr ⟨h1, h2⟩)

variable {Z : Set V}

omit [Fintype X] [DecidableEq X] in
theorem PendantSetting.g_mem (hs : PendantSetting N Z g a a' Q) : g ∈ inducedArcs N (insert a Q) :=
  mem_inducedArcs_iff.2 ⟨hs.facts.source_mem, hs.facts.target_mem⟩

omit [Fintype X] [DecidableEq X] in
/-- An arc of the induced network off `Z` is in the other induced network. -/
theorem PendantSetting.mem_arcs_of_off (hs : PendantSetting N Z g a a' Q) {f : E}
    (hf : f ∈ inducedArcs N (insert a Q)) (h₁ : N.graph.source f ∉ Z) (h₂ : N.graph.target f ∉ Z) :
    f ∈ inducedArcs N (insert a' Q) := by
  have := mem_inducedArcs_iff.1 hf
  exact mem_inducedArcs_iff.2 ⟨(hs.hV _ h₁).1 this.1, (hs.hV _ h₂).1 this.2⟩

/-- `Z` is a pendant cut for `a`. -/
theorem PendantSetting.pendant_side (hs : PendantSetting N Z g a a' Q) :
    IsPendantCut N (insert a Q) a g Z := by
  refine ⟨hs.g_mem, fun f _ => hs.hZ f, fun y hy => ?_⟩
  rcases Set.mem_insert_iff.1 hy with rfl | hy
  · exact ⟨fun _ => rfl, fun _ => hs.ha⟩
  · refine ⟨fun h => absurd h (hs.hQ y hy), fun e => absurd (e ▸ hs.ha) (hs.hQ y hy)⟩

/-- A pendant cut for a taxon of `Q` lies off `Z` and is a pendant cut of the other network. -/
theorem pendant_other (hs : PendantSetting N Z g a a' Q) {b : X} {e : E} {S : Set V} (hb : b ∈ Q)
    (h : IsPendantCut N (insert a Q) b e S) :
    IsPendantCut N (insert a' Q) b e (S \ Z) ∧ N.graph.source e ∉ Z ∧ N.graph.target e ∉ Z ∧
      ∀ t ∈ inducedVertices N (insert a Q), t ∈ Z → t ∉ S := by
  obtain ⟨he, hcr, hleaf⟩ := h
  have hbS : N.leaf b ∈ S := (hleaf b (Set.mem_insert_of_mem _ hb)).2 rfl
  obtain ⟨c, hc, hcb⟩ : ∃ c ∈ Q, c ≠ b := by
    obtain ⟨x, hx, y, hy, hxy⟩ := hs.two
    by_cases hxb : x = b
    · exact ⟨y, hy, fun e' => hxy (hxb.trans e'.symm)⟩
    · exact ⟨x, hx, hxb⟩
  have hcS : N.leaf c ∉ S := fun h' => hcb ((hleaf c (Set.mem_insert_of_mem _ hc)).1 h')
  have hab : a ≠ b := fun e' => hs.hQ b hb (e' ▸ hs.ha)
  have haS : N.leaf a ∉ S := fun h' => hab ((hleaf a (Set.mem_insert _ _)).1 h')
  have hout : N.graph.source e ∉ Z ∧ N.graph.target e ∉ Z := by
    by_contra hnot
    have := hs.facts.conn_out S (fun f hf h1 h2 hcross => by
        have hfe := (hcr f hf).1 hcross
        rw [hfe] at h1 h2
        exact hnot ⟨h1, h2⟩) _ (hs.facts.leaf_mem b (Set.mem_insert_of_mem _ hb)) _
      (hs.facts.leaf_mem c (Set.mem_insert_of_mem _ hc)) (hs.hQ b hb) (hs.hQ c hc)
    exact hcS (this.1 hbS)
  have hin : ∀ t ∈ inducedVertices N (insert a Q), t ∈ Z → t ∉ S := fun t ht htZ htS => by
    have := hs.facts.conn_in S (fun f hf h1 h2 hcross => by
        have hfe := (hcr f hf).1 hcross
        rw [hfe] at h1
        exact hout.1 h1) t ht _ (hs.facts.leaf_mem a (Set.mem_insert _ _)) htZ hs.ha
    exact haS (this.1 htS)
  have hgne : g ≠ e := by
    intro hge
    rcases (hs.hZ g).2 rfl with ⟨h1, -⟩ | ⟨h1, -⟩
    · exact hout.1 (hge ▸ h1)
    · exact hout.2 (hge ▸ h1)
  have hgS : N.graph.source g ∉ S ∧ N.graph.target g ∉ S := by
    have hnc : ¬ N.graph.Crosses g S := fun hc' => hgne ((hcr g hs.g_mem).1 hc')
    have hiff := mem_iff_of_not_crosses hnc
    rcases (hs.hZ g).2 rfl with ⟨h1, -⟩ | ⟨h1, -⟩
    · have h2 := hin _ hs.facts.source_mem h1
      exact ⟨h2, fun h' => h2 (hiff.2 h')⟩
    · have h2 := hin _ hs.facts.target_mem h1
      exact ⟨fun h' => h2 (hiff.1 h'), h2⟩
  have hoff : ∀ t, t ∉ Z → (t ∈ S \ Z ↔ t ∈ S) := fun t ht => ⟨fun h' => h'.1, fun h' => ⟨h', ht⟩⟩
  refine ⟨⟨hs.mem_arcs_of_off he hout.1 hout.2, fun f hf => ?_, fun y hy => ?_⟩, hout.1, hout.2, hin⟩
  · rcases arc_cases hs.hZ f with hfg | ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [hfg]
      constructor
      · rintro (⟨h', -⟩ | ⟨h', -⟩)
        · exact absurd h'.1 hgS.1
        · exact absurd h'.1 hgS.2
      · exact fun h' => absurd h' hgne
    · constructor
      · rintro (⟨h', -⟩ | ⟨h', -⟩)
        · exact absurd h1 h'.2
        · exact absurd h2 h'.2
      · exact fun h' => absurd (h' ▸ h1) hout.1
    · exact (crosses_congr (hoff _ h1) (hoff _ h2)).trans
        (hcr f (hs.symm.mem_arcs_of_off hf h1 h2))
  · rcases Set.mem_insert_iff.1 hy with rfl | hy
    · constructor
      · exact fun h' => absurd hs.ha' h'.2
      · exact fun h' => absurd (h' ▸ hs.ha') (hs.hQ _ hb)
    · exact (hoff _ (hs.hQ y hy)).trans (hleaf y (Set.mem_insert_of_mem _ hy))

/-- A pendant cut for `a` gives one for `a'`, with the side `Z` added. -/
theorem pendant_self (hs : PendantSetting N Z g a a' Q) {e : E} {S : Set V}
    (h : IsPendantCut N (insert a Q) a e S) :
    ∃ e', IsPendantCut N (insert a' Q) a' e' (S ∪ Z) ∧
      (¬ (N.graph.source e ∈ Z ∧ N.graph.target e ∈ Z) → e' = e) ∧
      ((N.graph.source e ∈ Z ∧ N.graph.target e ∈ Z) →
        ∀ t ∈ inducedVertices N (insert a Q), t ∉ Z → t ∉ S) := by
  obtain ⟨he, hcr, hleaf⟩ := h
  have haS : N.leaf a ∈ S := (hleaf a (Set.mem_insert _ _)).2 rfl
  have hQS : ∀ y ∈ Q, N.leaf y ∉ S := fun y hy h' =>
    hs.hQ y hy (((hleaf y (Set.mem_insert_of_mem _ hy)).1 h').symm ▸ hs.ha)
  have hgY' : g ∈ inducedArcs N (insert a' Q) := hs.symm.g_mem
  have hleaves : ∀ y ∈ insert a' Q, N.leaf y ∈ S ∪ Z ↔ y = a' := by
    intro y hy
    rcases Set.mem_insert_iff.1 hy with rfl | hy
    · exact ⟨fun _ => rfl, fun _ => Or.inr hs.ha'⟩
    · refine ⟨fun h' => h'.elim (fun h'' => absurd h'' (hQS y hy)) (fun h'' => absurd h'' (hs.hQ y hy)),
        fun e' => absurd (e' ▸ hs.ha') (hs.hQ y hy)⟩
  obtain ⟨b, hb, -⟩ := hs.two
  by_cases hez : N.graph.source e ∈ Z ∧ N.graph.target e ∈ Z
  · have hout : ∀ t ∈ inducedVertices N (insert a Q), t ∉ Z → t ∉ S := fun t ht htZ htS => by
      have := hs.facts.conn_out S (fun f hf h1 h2 hcross => by
          have hfe := (hcr f hf).1 hcross
          rw [hfe] at h1
          exact h1 hez.1) t ht _ (hs.facts.leaf_mem b (Set.mem_insert_of_mem _ hb)) htZ (hs.hQ b hb)
      exact hQS b hb (this.1 htS)
    refine ⟨g, ⟨hgY', fun f hf => ?_, hleaves⟩, fun h' => absurd hez h', fun _ => hout⟩
    rcases arc_cases hs.hZ f with hfg | ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [hfg]
      refine ⟨fun _ => rfl, fun _ => ?_⟩
      rcases (hs.hZ g).2 rfl with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Or.inl ⟨Or.inr h1, fun h' => h'.elim (hout _ hs.facts.target_mem h2) h2⟩
      · exact Or.inr ⟨Or.inr h1, fun h' => h'.elim (hout _ hs.facts.source_mem h2) h2⟩
    · constructor
      · rintro (⟨-, h'⟩ | ⟨-, h'⟩)
        · exact absurd (Or.inr h2) h'
        · exact absurd (Or.inr h1) h'
      · intro hfg
        rw [hfg] at h1 h2
        rcases (hs.hZ g).2 rfl with ⟨-, h'⟩ | ⟨-, h'⟩
        · exact absurd h2 h'
        · exact absurd h1 h'
    · have hfY := hs.symm.mem_arcs_of_off hf h1 h2
      have hfV := mem_inducedArcs_iff.1 hfY
      constructor
      · rintro (⟨h', -⟩ | ⟨h', -⟩)
        · exact absurd h' fun h'' => h''.elim (hout _ hfV.1 h1) h1
        · exact absurd h' fun h'' => h''.elim (hout _ hfV.2 h2) h2
      · intro hfg
        rw [hfg] at h1 h2
        rcases (hs.hZ g).2 rfl with ⟨h', -⟩ | ⟨h', -⟩
        · exact absurd h' h1
        · exact absurd h' h2
  · have hin : ∀ t ∈ inducedVertices N (insert a Q), t ∈ Z → t ∈ S := fun t ht htZ => by
      have := hs.facts.conn_in S (fun f hf h1 h2 hcross => by
          have hfe := (hcr f hf).1 hcross
          rw [hfe] at h1 h2
          exact hez ⟨h1, h2⟩) t ht _ (hs.facts.leaf_mem a (Set.mem_insert _ _)) htZ hs.ha
      exact this.2 haS
    have hcong : ∀ t ∈ inducedVertices N (insert a Q), (t ∈ S ∪ Z ↔ t ∈ S) := fun t ht =>
      ⟨fun h' => h'.elim id (hin t ht), Or.inl⟩
    refine ⟨e, ⟨?_, fun f hf => ?_, hleaves⟩, fun _ => rfl, fun h' => absurd h' hez⟩
    · rcases arc_cases hs.hZ e with heg | h1 | h1
      · exact heg ▸ hgY'
      · exact absurd h1 hez
      · exact hs.mem_arcs_of_off he h1.1 h1.2
    · rcases arc_cases hs.hZ f with hfg | ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [hfg]
        exact (crosses_congr (hcong _ hs.facts.source_mem) (hcong _ hs.facts.target_mem)).trans
          (hcr _ hs.g_mem)
      · constructor
        · rintro (⟨-, h'⟩ | ⟨-, h'⟩)
          · exact absurd (Or.inr h2) h'
          · exact absurd (Or.inr h1) h'
        · intro hfe
          rw [hfe] at h1 h2
          exact absurd ⟨h1, h2⟩ hez
      · have hfY := hs.symm.mem_arcs_of_off hf h1 h2
        have hfV := mem_inducedArcs_iff.1 hfY
        exact (crosses_congr (hcong _ hfV.1) (hcong _ hfV.2)).trans (hcr f hfY)

/-- What remains without the pendant chains is the same in both induced networks. -/
theorem coreArcs_subset (hs : PendantSetting N Z g a a' Q) :
    coreArcs N (insert a Q) ⊆ coreArcs N (insert a' Q) := by
  rintro f ⟨hf, hnot⟩
  have hf' : N.graph.source f ∉ Z ∧ N.graph.target f ∉ Z := by
    rcases arc_cases hs.hZ f with h | h | h
    · exact absurd ⟨a, Set.mem_insert _ _, g, Z, hs.pendant_side, Or.inl h⟩ hnot
    · exact absurd ⟨a, Set.mem_insert _ _, g, Z, hs.pendant_side, Or.inr h⟩ hnot
    · exact h
  have hfV := mem_inducedArcs_iff.1 hf
  refine ⟨hs.mem_arcs_of_off hf hf'.1 hf'.2, ?_⟩
  rintro ⟨x, hx, e, S, hp, hcov⟩
  rcases Set.mem_insert_iff.1 hx with rfl | hx
  · obtain ⟨e', hp', h1, h2⟩ := pendant_self hs.symm hp
    by_cases hez : N.graph.source e ∈ Z ∧ N.graph.target e ∈ Z
    · rcases hcov with h | h
      · exact hf'.1 (h ▸ hez.1)
      · exact h2 hez _ ((hs.hV _ hf'.1).1 hfV.1) hf'.1 h.1
    · rw [h1 hez] at hp'
      exact hnot ⟨a, Set.mem_insert _ _, e, S ∪ Z, hp', hcov.imp id fun h => ⟨Or.inl h.1, Or.inl h.2⟩⟩
  · obtain ⟨hp', -, -, -⟩ := pendant_other hs.symm hx hp
    exact hnot ⟨x, Set.mem_insert_of_mem _ hx, e, S \ Z, hp',
      hcov.imp id fun h => ⟨⟨h.1, hf'.1⟩, ⟨h.2, hf'.2⟩⟩⟩

/-- The attachment point of the chain to `a` is that of the chain to `a'`. -/
theorem attaches_self (hN : N.IsPhylogenetic) (hs : PendantSetting N Z g a a' Q) {v : V}
    (h : AttachesAt N (insert a Q) a v) : AttachesAt N (insert a' Q) a' v := by
  obtain ⟨e, S, hp, hv, hend, htop⟩ := h
  have hZS : Z ⊆ S := fun u hu => htop g Z hs.pendant_side u hu (hN.root_reaches u)
  have hez : ¬ (N.graph.source e ∈ Z ∧ N.graph.target e ∈ Z) := by
    rintro ⟨h1, h2⟩
    rcases (hp.2.1 e hp.1).2 rfl with ⟨-, h'⟩ | ⟨-, h'⟩
    · exact h' (hZS h2)
    · exact h' (hZS h1)
  obtain ⟨e', hp', h1, -⟩ := pendant_self hs hp
  rw [h1 hez, Set.union_eq_left.2 hZS] at hp'
  refine ⟨e, S, hp', hv, hend, fun e₂ S₂ hp₂ u hu _ => ?_⟩
  obtain ⟨e₃, hp₃, -, -⟩ := pendant_self hs.symm hp₂
  exact htop e₃ (S₂ ∪ Z) hp₃ u (Or.inl hu) (hN.root_reaches u)

/-- The attachment point of the chain to a taxon of `Q` is the same in both induced networks. -/
theorem attaches_other (hN : N.IsPhylogenetic) (hs : PendantSetting N Z g a a' Q) {b : X} {v : V}
    (hb : b ∈ Q) (h : AttachesAt N (insert a Q) b v) : AttachesAt N (insert a' Q) b v := by
  obtain ⟨e, S, hp, hv, hend, htop⟩ := h
  obtain ⟨hp', h1, h2, -⟩ := pendant_other hs hb hp
  have hcong : ∀ t ∈ inducedVertices N (insert a' Q),
      (t ∈ (S \ Z) ∪ (inducedVertices N (insert a' Q))ᶜ ↔ t ∈ S \ Z) := fun t ht =>
    ⟨fun h' => h'.elim id fun h'' => absurd ht h'', Or.inl⟩
  have hpS : IsPendantCut N (insert a' Q) b e ((S \ Z) ∪ (inducedVertices N (insert a' Q))ᶜ) := by
    refine ⟨hp'.1, fun f hf => ?_, fun y hy => ?_⟩
    · have hfV := mem_inducedArcs_iff.1 hf
      exact (crosses_congr (hcong _ hfV.1) (hcong _ hfV.2)).trans (hp'.2.1 f hf)
    · exact (hcong _ (hs.facts'.leaf_mem y hy)).trans (hp'.2.2 y hy)
  have heV := mem_inducedArcs_iff.1 hp'.1
  refine ⟨e, _, hpS, ?_, hend, fun e₂ S₂ hp₂ u hu _ => ?_⟩
  · have hvB : v ∈ inducedVertices N (insert a' Q) := by
      rcases hend with h' | h'
      · exact h' ▸ heV.1
      · exact h' ▸ heV.2
    exact fun h' => hv ((hcong v hvB).1 h').1
  · by_cases huB : u ∈ inducedVertices N (insert a' Q)
    · obtain ⟨hp₃, -, -, h₃⟩ := pendant_other hs.symm hb hp₂
      have huZ : u ∉ Z := fun h' => h₃ u huB h' hu
      exact Or.inl ⟨htop e₂ (S₂ \ Z) hp₃ u ⟨hu, huZ⟩ (hN.root_reaches u), huZ⟩
    · exact Or.inr huB

end Exchange

end PendantChain

open PendantChain in
/-- The printed condition 2 implies the form used in `theorem3_1`: if a cut edge groups `a, a'` away
from `b, c, d`, then the induced networks on `a, b, c, d` and on `a', b, c, d` differ only in the
pendant chain to `a` or `a'`. -/
theorem pendantChainInvariant_cutExchangeable (hN : N.IsPhylogenetic) {p : QuartetTree X → ℝ}
    (h : PendantChainInvariant N p) : CutExchangeable N p := by
  intro s s' a a' has ha's hs' ⟨A, hcut, haA, ha'A, hdisj⟩
  obtain ⟨g, Z, hZ, hZA⟩ := hcut
  have hmemZ : ∀ y, N.leaf y ∈ Z ↔ y ∈ A := fun y => by
    have := Set.ext_iff.1 hZA y
    simpa using this
  let G : X → X := Function.update id a a'
  have hGa : G a = a' := by simp [G]
  have hG : ∀ y, y ≠ a → G y = y := fun y hy => by simp [G, Function.update_of_ne hy]
  let Q : Set X := ↑(s.taxa.erase a)
  have hs'val : s'.val = s.val.image fun B => B.image G := by
    rw [hs']
    refine image_congr fun B _ => ?_
    by_cases haB : a ∈ B
    · simp only [haB, ↓reduceIte]
      ext z
      simp only [mem_insert, mem_erase, mem_image]
      constructor
      · rintro (rfl | ⟨hz, hzB⟩)
        · exact ⟨a, haB, hGa⟩
        · exact ⟨z, hzB, hG z hz⟩
      · rintro ⟨y, hy, rfl⟩
        by_cases hya : y = a
        · subst hya
          exact Or.inl hGa
        · rw [hG y hya]
          exact Or.inr ⟨hya, hy⟩
    · simp only [haB, ↓reduceIte]
      ext z
      simp only [mem_image]
      constructor
      · exact fun hz => ⟨z, hz, hG z fun e => haB (e ▸ hz)⟩
      · rintro ⟨y, hy, rfl⟩
        rwa [hG y fun e => haB (e ▸ hy)]
  have htaxa : (s.taxa : Set X) = insert a Q := by
    simp only [Q, coe_erase]
    exact (Set.insert_sdiff_singleton.trans (Set.insert_eq_of_mem has)).symm
  have htaxa' : (s'.taxa : Set X) = insert a' Q := by
    have h1 : s'.taxa = s.taxa.image G := by
      ext y
      simp only [QuartetTree.taxa, hs'val, Finset.mem_sup, id, mem_image]
      constructor
      · rintro ⟨_, ⟨B, hB, rfl⟩, hy⟩
        obtain ⟨z, hz, rfl⟩ := mem_image.1 hy
        exact ⟨z, ⟨B, hB, hz⟩, rfl⟩
      · rintro ⟨z, ⟨B, hB, hz⟩, rfl⟩
        exact ⟨_, ⟨B, hB, rfl⟩, mem_image_of_mem _ hz⟩
    rw [h1]
    ext y
    simp only [coe_image, Set.mem_image, mem_coe, Set.mem_insert_iff, Q, coe_erase, Set.mem_sdiff,
      Set.mem_singleton_iff]
    constructor
    · rintro ⟨z, hz, rfl⟩
      by_cases hza : z = a
      · subst hza
        exact Or.inl hGa
      · rw [hG z hza]
        exact Or.inr ⟨hz, hza⟩
    · rintro (rfl | ⟨hz, hza⟩)
      · exact ⟨a, has, hGa⟩
      · exact ⟨y, hz, hG y hza⟩
  have hQc : (s.taxa.erase a).card = 3 := by
    rw [card_erase_of_mem has, s.card_taxa]
  have hset : PendantSetting N Z g a a' Q := by
    refine pendantSetting_of_cut hN hZ ((hmemZ a).2 haA) ((hmemZ a').2 ha'A) (fun y hy hyZ => ?_) ?_
    · exact disjoint_left.1 hdisj ((hmemZ y).1 hyZ) hy
    · obtain ⟨b, hb, c, hc, hbc⟩ := one_lt_card.1 (by omega : 1 < (s.taxa.erase a).card)
      exact ⟨b, hb, c, hc, hbc⟩
  have hinj : Set.InjOn G s.taxa := by
    intro x hx y hy hxy
    by_cases hxa : x = a
    · by_cases hya : y = a
      · rw [hxa, hya]
      · rw [hxa, hGa, hG y hya] at hxy
        exact absurd (hxy ▸ hy) ha's
    · by_cases hya : y = a
      · rw [hya, hGa, hG x hxa] at hxy
        exact absurd (hxy ▸ hx) ha's
      · rwa [hG x hxa, hG y hya] at hxy
  refine h s s' G hinj hs'val ?_ ?_
  · rw [htaxa, htaxa']
    exact Set.Subset.antisymm (coreArcs_subset hset) (coreArcs_subset hset.symm)
  · intro x hx v
    rw [htaxa, htaxa']
    by_cases hxa : x = a
    · rw [hxa, hGa]
      exact ⟨attaches_self hN hset, attaches_self hN hset.symm⟩
    · rw [hG x hxa]
      have hxQ : x ∈ Q := by
        simp only [Q, coe_erase, Set.mem_sdiff, mem_coe, Set.mem_singleton_iff]
        exact ⟨hx, hxa⟩
      exact ⟨attaches_other hN hset hxQ, attaches_other hN hset.symm hxQ⟩

/-! ### Empirical concordance factors -/

/-- Unrooted gene trees, resolved or not. -/
abbrev UnrootedGeneTree (X : Type*) [Fintype X] [DecidableEq X] :=
  {T : Finset (Finset X) // IsUnrootedTree T}

/-- What a gene tree contributes to the concordance factor of `s` (ECToBlob §2): `1` if it displays
`s`, and `1/3` if it does not resolve the taxa of `s`. -/
def geneContribution (T : Finset (Finset X)) (s : QuartetTree X) : ℝ :=
  if Displays T s then 1 else if ∀ r ∈ treesOn s.taxa, ¬ Displays T r then 1 / 3 else 0

/-- The concordance factor of a distribution on gene trees. -/
def expectedCF (dist : UnrootedGeneTree X → ℝ) (s : QuartetTree X) : ℝ :=
  ∑ G, dist G * geneContribution G.val s

/-- The empirical concordance factor of a sample of gene trees. -/
def empiricalCF {n : ℕ} (ω : Fin n → UnrootedGeneTree X) (s : QuartetTree X) : ℝ :=
  (∑ i, geneContribution (ω i).val s) / n

/-- **Corollary 3.6** (`ecto:cor3_6`). For `n` independent gene trees from a distribution
satisfying the assumptions of Theorem 3.1, with probability tending to one every tree optimal for the
Maximum Quartet Support criterion is a resolution of the tree of blobs.

Departure from the paper: the printed claim that the empirical and expected objectives have the same
optima is too strong when the expected objective has ties (E2 of the report). The containment of the
empirical optima in the expected optima suffices, from the gap to non-maximizers. -/
theorem corollary3_6 (hN : N.IsPhylogenetic) (dist : UnrootedGeneTree X → ℝ)
    (hdist : (∀ G, 0 ≤ dist G) ∧ ∑ G, dist G = 1)
    (h₁ : ∀ s, Displays (treeOfBlobs N) s → ∀ r ∈ s.alternatives, expectedCF dist r < expectedCF dist s)
    (h₂ : CutExchangeable N (expectedCF dist)) :
    Tendsto (fun n => iidProb dist n fun ω =>
      ∀ T, IsUnrootedTree T →
        (∀ T', IsUnrootedTree T' → quartetScore (empiricalCF ω) T' ≤ quartetScore (empiricalCF ω) T) →
        treeOfBlobs N ⊆ T) atTop (𝓝 1) := by
  have hd : IsDist dist := hdist
  have hexp : ∀ s, 0 ≤ expectedCF dist s := fun s => sum_nonneg fun G _ =>
    mul_nonneg (hdist.1 G) (by
      unfold geneContribution
      split_ifs <;> norm_num)
  -- a radius within which the empirical maximizers are expected maximizers (E2 of the report)
  let S : Finset (Finset (Finset X)) := univ.filter fun T => IsUnrootedTree T
  obtain ⟨δ, hδ, hrad⟩ := Finset.exists_pos_radius_isMaxOn S (quartetScore (expectedCF dist))
  let c : ℝ := (Fintype.card (QuartetTree X) : ℝ) + 1
  have hc : 0 < c := by positivity
  have hε : 0 < δ / c := div_pos hδ hc
  -- the empirical concordance factors are uniformly close to the expected ones
  have hev : Tendsto (fun n => iidProb dist n fun ω => ∀ s : QuartetTree X,
      |(∑ i, geneContribution (ω i).val s) / n - ∑ G, dist G * geneContribution G.val s| < δ / c)
      atTop (𝓝 1) :=
    tendsto_iidProb_forall hd _ fun s => iidProb_weak_law hd (fun G => geneContribution G.val s) hε
  refine tendsto_iidProb_of_imp hd (Eventually.of_forall fun n ω hω T hT hTmax => ?_) hev
  have herr : ∀ T ∈ S, |quartetScore (expectedCF dist) T - quartetScore (empiricalCF ω) T| < δ := by
    intro T' _
    have hterm : ∀ s : QuartetTree X,
        |(if Displays T' s then expectedCF dist s else 0) -
          (if Displays T' s then empiricalCF ω s else 0)| ≤ δ / c := by
      intro s
      split_ifs
      · rw [abs_sub_comm]
        exact (hω s).le
      · simpa using hε.le
    calc |quartetScore (expectedCF dist) T' - quartetScore (empiricalCF ω) T'|
        = |∑ s, ((if Displays T' s then expectedCF dist s else 0) -
            (if Displays T' s then empiricalCF ω s else 0))| := by
          rw [quartetScore, quartetScore, sum_sub_distrib]
      _ ≤ ∑ s, |(if Displays T' s then expectedCF dist s else 0) -
            (if Displays T' s then empiricalCF ω s else 0)| := abs_sum_le_sum_abs _ _
      _ ≤ ∑ _s : QuartetTree X, δ / c := sum_le_sum fun s _ => hterm s
      _ = (Fintype.card (QuartetTree X) : ℝ) * (δ / c) := by simp [card_univ]
      _ < δ := by
        have : (Fintype.card (QuartetTree X) : ℝ) < c := by simp [c]
        rw [mul_div_assoc', div_lt_iff₀ hc]
        nlinarith
  have hTS : T ∈ S := mem_filter.2 ⟨mem_univ _, hT⟩
  have hmaxE := hrad (quartetScore (empiricalCF ω)) herr T hTS (fun T' hT' =>
    hTmax T' (mem_filter.1 hT').2)
  exact theorem3_1 hN (expectedCF dist) hexp h₁ h₂ hT fun T' hT' =>
    hmaxE (mem_filter.2 ⟨mem_univ _, hT'⟩)

end ECToBlob
