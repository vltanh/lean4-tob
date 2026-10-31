/-
Adapted from https://github.com/vltanh/lean4-phylogenetics,
commit 06f684e526e276ca2ccf668a1c3a808a2b8c181d.
Licensed under the Apache License, Version 2.0:
https://www.apache.org/licenses/LICENSE-2.0
Exact source regions and adaptations: docs/COALESCENT_SOURCES.md.
-/
module

public import Basic.Phylogenetics.Coalescent.BinaryForest
public import Mathlib.Analysis.Matrix.Normed

/-!
# Lumpability of Kingman's coalescent

[E. S. Allman, J. H. Degnan, J. A. Rhodes, *Identifying the rooted species tree from the
distribution of unrooted gene trees under the coalescent*, J. Math. Biol. 62 (2011) 833–862]

Kingman's coalescent is consistent: restricting a forest to a subset `Z` of the lineages lumps the
chain into Kingman's coalescent on `Z`. The generators intertwine, `Q M = M Q` on the rows of forests,
where `M` is the restriction map: merging two roots that both meet `Z` merges their traces, and the
other merges do not change the restriction.

* `traceForest Z F`: the restriction of a forest to the lineages `Z`, the nonempty traces of its
  clusters, as a forest on the same type of lineages.

## Main results

* `kingmanTransition_trace`, `kingmanAbsorption_trace`, and the form `sum_kingmanTransition_trace`
  tested against a function of the restriction.
* `IsForest.traceForest`, `mem_roots_traceForest`: the roots of a restriction are the traces of the
  roots meeting `Z`.
* `traceForest_forestBelow`: the restriction of the forest below some roots.
-/

@[expose] public section

namespace Phylogenetics

open Finset

variable {L : Type*} [DecidableEq L]

/-- The restriction of a forest to the lineages `Z`: the nonempty traces of its clusters. -/
def traceForest (Z : Finset L) (F : Finset (Finset L)) : Finset (Finset L) :=
  (F.filter fun A => (A ∩ Z).Nonempty).image fun A => A ∩ Z

/-! ### Restricting forests -/

theorem mem_traceForest {Z : Finset L} {F : Finset (Finset L)} {D : Finset L} :
    D ∈ traceForest Z F ↔ ∃ A ∈ F, (A ∩ Z).Nonempty ∧ A ∩ Z = D := by
  unfold traceForest
  simp only [mem_image, mem_filter, and_assoc]

theorem inter_mem_traceForest {Z : Finset L} {F : Finset (Finset L)} {A : Finset L}
    (hA : A ∈ F) (hmeet : (A ∩ Z).Nonempty) : A ∩ Z ∈ traceForest Z F :=
  mem_traceForest.2 ⟨A, hA, hmeet, rfl⟩

private theorem trc_mono (Z : Finset L) {A B : Finset L} (h : A ⊆ B) : A ∩ Z ⊆ B ∩ Z :=
  inter_subset_inter_right h

private theorem trc_disjoint (Z : Finset L) {A B : Finset L} (h : Disjoint A B) :
    Disjoint (A ∩ Z) (B ∩ Z) :=
  h.mono inter_subset_left inter_subset_left

theorem IsForest.traceForest {F : Finset (Finset L)} (hF : IsForest F) (Z : Finset L) :
    IsForest (traceForest Z F) := by
  refine ⟨fun D hD => ?_, fun D hD D' hD' => ?_⟩
  · obtain ⟨A, -, hm, rfl⟩ := mem_traceForest.1 hD
    exact hm
  · obtain ⟨A, hA, -, rfl⟩ := mem_traceForest.1 hD
    obtain ⟨B, hB, -, rfl⟩ := mem_traceForest.1 hD'
    rcases hF.2 A hA B hB with h | h | h
    · exact Or.inl (trc_mono Z h)
    · exact Or.inr (Or.inl (trc_mono Z h))
    · exact Or.inr (Or.inr (trc_disjoint Z h))

/-- A restriction contains no cluster outside `Z`. -/
theorem subset_of_mem_traceForest {Z : Finset L} {F : Finset (Finset L)} {D : Finset L}
    (hD : D ∈ traceForest Z F) : D ⊆ Z := by
  obtain ⟨A, -, -, rfl⟩ := mem_traceForest.1 hD
  exact inter_subset_right

theorem traceForest_union (Z : Finset L) (F G : Finset (Finset L)) :
    traceForest Z (F ∪ G) = traceForest Z F ∪ traceForest Z G := by
  unfold traceForest
  rw [filter_union, image_union]

@[simp] theorem traceForest_empty (Z : Finset L) : traceForest Z (∅ : Finset (Finset L)) = ∅ := by
  simp [traceForest]

theorem traceForest_biUnion {ι : Type*} [DecidableEq ι] (Z : Finset L) (s : Finset ι)
    (f : ι → Finset (Finset L)) :
    traceForest Z (s.biUnion f) = s.biUnion fun i => traceForest Z (f i) := by
  unfold traceForest
  rw [filter_biUnion, biUnion_image]

private theorem trc_insert (Z C : Finset L) (F : Finset (Finset L)) :
    traceForest Z (insert C F) =
      if (C ∩ Z).Nonempty then insert (C ∩ Z) (traceForest Z F) else traceForest Z F := by
  unfold traceForest
  rw [filter_insert]
  split_ifs <;> simp [image_insert]

section Fintype

variable [Fintype L]

/-- The trace is injective on the roots meeting `Z`. -/
theorem IsForest.inter_inj_of_mem_roots {F : Finset (Finset L)} (hF : IsForest F) {Z : Finset L}
    {A B : Finset L} (hA : A ∈ roots F) (hB : B ∈ roots F) (hmeet : (A ∩ Z).Nonempty)
    (h : A ∩ Z = B ∩ Z) : A = B := by
  obtain ⟨l, hl⟩ := hmeet
  have hlB : l ∈ B ∩ Z := h ▸ hl
  exact hF.eq_of_mem_roots_of_mem hA hB (mem_inter.1 hl).1 (mem_inter.1 hlB).1

/-- The roots of the restriction of a forest are the traces of its roots meeting `Z`. -/
theorem mem_roots_traceForest {F : Finset (Finset L)} (hF : IsForest F) {Z : Finset L}
    {D : Finset L} :
    D ∈ roots (traceForest Z F) ↔ ∃ A ∈ roots F, (A ∩ Z).Nonempty ∧ A ∩ Z = D := by
  constructor
  · intro hD
    obtain ⟨hDF, hmax⟩ := mem_roots.1 hD
    obtain ⟨A, hA, hmeet, rfl⟩ := mem_traceForest.1 hDF
    obtain ⟨R, hR, hAR⟩ := exists_mem_roots_subset hA
    have hRmeet : (R ∩ Z).Nonempty := hmeet.mono (trc_mono Z hAR)
    exact ⟨R, hR, hRmeet, hmax _ (inter_mem_traceForest (roots_subset F hR) hRmeet)
      (trc_mono Z hAR)⟩
  · rintro ⟨A, hA, hmeet, rfl⟩
    refine mem_roots.2 ⟨inter_mem_traceForest (roots_subset F hA) hmeet, fun D hD hAD => ?_⟩
    obtain ⟨B, hB, hBmeet, rfl⟩ := mem_traceForest.1 hD
    obtain ⟨R, hR, hBR⟩ := exists_mem_roots_subset hB
    obtain ⟨l, hl⟩ := hmeet
    have hlB : l ∈ B ∩ Z := hAD hl
    have hAR : A = R := hF.eq_of_mem_roots_of_mem hA hR (mem_inter.1 hl).1
      (hBR (mem_inter.1 hlB).1)
    subst hAR
    exact subset_antisymm (trc_mono Z hBR) hAD

/-- The restriction of a merge: merging two roots that both meet `Z` merges their traces; otherwise
the restriction does not change. -/
private theorem trc_merge {F : Finset (Finset L)} (Z : Finset L) {A B : Finset L}
    (hA : A ∈ roots F) (hB : B ∈ roots F) :
    traceForest Z (insert (A ∪ B) F) =
      if (A ∩ Z).Nonempty ∧ (B ∩ Z).Nonempty then
        insert ((A ∩ Z) ∪ (B ∩ Z)) (traceForest Z F)
      else traceForest Z F := by
  rw [trc_insert, union_inter_distrib_right]
  by_cases hAm : (A ∩ Z).Nonempty <;> by_cases hBm : (B ∩ Z).Nonempty
  · have hU : ((A ∩ Z) ∪ (B ∩ Z)).Nonempty := hAm.mono subset_union_left
    rw [ite_eq_left hU, ite_eq_left ⟨hAm, hBm⟩]
  · have hU : ((A ∩ Z) ∪ (B ∩ Z)).Nonempty := hAm.mono subset_union_left
    have hB0 : B ∩ Z = ∅ := not_nonempty_iff_eq_empty.1 hBm
    rw [ite_eq_left hU, ite_eq_right (fun h => hBm h.2), hB0, union_empty]
    exact insert_eq_of_mem (inter_mem_traceForest (roots_subset F hA) hAm)
  · have hU : ((A ∩ Z) ∪ (B ∩ Z)).Nonempty := hBm.mono subset_union_right
    have hA0 : A ∩ Z = ∅ := not_nonempty_iff_eq_empty.1 hAm
    rw [ite_eq_left hU, ite_eq_right (fun h => hAm h.1), hA0, empty_union]
    exact insert_eq_of_mem (inter_mem_traceForest (roots_subset F hB) hBm)
  · have hU : ¬ ((A ∩ Z) ∪ (B ∩ Z)).Nonempty := by
      rw [not_nonempty_iff_eq_empty, not_nonempty_iff_eq_empty.1 hAm,
        not_nonempty_iff_eq_empty.1 hBm, union_empty]
    rw [ite_eq_right hU, ite_eq_right (fun h => hAm h.1)]

/-- The merges of `F` whose restriction differs from the restriction of `F`: the merges of two
roots that both meet `Z`. -/
private theorem trc_mem_merges_ne {F : Finset (Finset L)} (hF : IsForest F) (Z : Finset L)
    {H : Finset (Finset L)} :
    (H ∈ merges F ∧ traceForest Z H ≠ traceForest Z F) ↔
      ∃ A ∈ roots F, ∃ B ∈ roots F, A ≠ B ∧ (A ∩ Z).Nonempty ∧ (B ∩ Z).Nonempty ∧
        H = insert (A ∪ B) F := by
  constructor
  · rintro ⟨hH, hne⟩
    obtain ⟨A, hA, B, hB, hAB, rfl⟩ := mem_merges.1 hH
    rw [trc_merge Z hA hB] at hne
    by_cases h : (A ∩ Z).Nonempty ∧ (B ∩ Z).Nonempty
    · exact ⟨A, hA, B, hB, hAB, h.1, h.2, rfl⟩
    · rw [ite_eq_right h] at hne
      exact absurd rfl hne
  · rintro ⟨A, hA, B, hB, hAB, hAm, hBm, rfl⟩
    refine ⟨mem_merges.2 ⟨A, hA, B, hB, hAB, rfl⟩, ?_⟩
    rw [trc_merge Z hA hB, ite_eq_left ⟨hAm, hBm⟩]
    intro h
    have hrA := (mem_roots_traceForest hF).2 ⟨A, hA, hAm, rfl⟩
    have hrB := (mem_roots_traceForest hF).2 ⟨B, hB, hBm, rfl⟩
    have hne : A ∩ Z ≠ B ∩ Z := fun h' => hAB (hF.inter_inj_of_mem_roots hA hB hAm h')
    exact union_not_mem_of_mem_roots hrA hrB hne (h ▸ mem_insert_self _ _)

/-- The key count behind lumpability: summing a function of the restriction over the merges of
`F` gives the sum over the merges of the restriction, plus the merges that do not change the
restriction. -/
private theorem trc_sum_merges {F : Finset (Finset L)} (hF : IsForest F) (Z : Finset L)
    (u : Finset (Finset L) → ℝ) :
    -((#(roots F)).choose 2 : ℝ) * u (traceForest Z F) +
        ∑ H ∈ merges F, u (traceForest Z H) =
      -((#(roots (traceForest Z F))).choose 2 : ℝ) * u (traceForest Z F) +
        ∑ H' ∈ merges (traceForest Z F), u H' := by
  set rF := traceForest Z F with hrF
  have hrFf : IsForest rF := hF.traceForest Z
  set M₂ := (merges F).filter fun H => traceForest Z H ≠ rF with hM₂
  have hmemM₂ : ∀ H, H ∈ M₂ ↔ (H ∈ merges F ∧ traceForest Z H ≠ traceForest Z F) := fun H => by
    rw [hM₂, mem_filter]
  -- the restriction maps `M₂` onto the merges of `rF`
  have himage : M₂.image (traceForest Z) = merges rF := by
    ext H'
    rw [mem_image]
    constructor
    · rintro ⟨H, hH, rfl⟩
      obtain ⟨A, hA, B, hB, hAB, hAm, hBm, rfl⟩ := (trc_mem_merges_ne hF Z).1 ((hmemM₂ H).1 hH)
      rw [trc_merge Z hA hB, ite_eq_left ⟨hAm, hBm⟩]
      exact mem_merges.2 ⟨_, (mem_roots_traceForest hF).2 ⟨A, hA, hAm, rfl⟩, _,
        (mem_roots_traceForest hF).2 ⟨B, hB, hBm, rfl⟩,
        fun h' => hAB (hF.inter_inj_of_mem_roots hA hB hAm h'), rfl⟩
    · intro hH'
      obtain ⟨A', hA', B', hB', hAB', rfl⟩ := mem_merges.1 hH'
      obtain ⟨A, hA, hAm, rfl⟩ := (mem_roots_traceForest hF).1 hA'
      obtain ⟨B, hB, hBm, rfl⟩ := (mem_roots_traceForest hF).1 hB'
      have hAB : A ≠ B := by
        rintro rfl
        exact hAB' rfl
      refine ⟨insert (A ∪ B) F, (hmemM₂ _).2 ((trc_mem_merges_ne hF Z).2
        ⟨A, hA, B, hB, hAB, hAm, hBm, rfl⟩), ?_⟩
      rw [trc_merge Z hA hB, ite_eq_left ⟨hAm, hBm⟩]
  -- and is injective on `M₂`
  have hinj : Set.InjOn (traceForest Z) (M₂ : Set (Finset (Finset L))) := by
    intro H₁ hH₁ H₂ hH₂ h12
    obtain ⟨A₁, hA₁, B₁, hB₁, hAB₁, hA₁m, hB₁m, rfl⟩ :=
      (trc_mem_merges_ne hF Z).1 ((hmemM₂ _).1 (mem_coe.1 hH₁))
    obtain ⟨A₂, hA₂, B₂, hB₂, hAB₂, hA₂m, hB₂m, rfl⟩ :=
      (trc_mem_merges_ne hF Z).1 ((hmemM₂ _).1 (mem_coe.1 hH₂))
    rw [trc_merge Z hA₁ hB₁, ite_eq_left ⟨hA₁m, hB₁m⟩,
      trc_merge Z hA₂ hB₂, ite_eq_left ⟨hA₂m, hB₂m⟩] at h12
    have hr := fun {A} (hA : A ∈ roots F) (hAm : (A ∩ Z).Nonempty) =>
      (mem_roots_traceForest hF).2 ⟨A, hA, hAm, rfl⟩
    have hU : (A₁ ∩ Z) ∪ (B₁ ∩ Z) = (A₂ ∩ Z) ∪ (B₂ ∩ Z) := by
      have hmem := h12 ▸ mem_insert_self ((A₁ ∩ Z) ∪ (B₁ ∩ Z)) rF
      rcases mem_insert.1 hmem with h | h
      · exact h
      · exact absurd h (union_not_mem_of_mem_roots (hr hA₁ hA₁m) (hr hB₁ hB₁m)
          (fun h' => hAB₁ (hF.inter_inj_of_mem_roots hA₁ hB₁ hA₁m h')))
    -- each of `A₁`, `B₁` is one of `A₂`, `B₂`
    have hin : ∀ {C}, C ∈ roots F → (C ∩ Z).Nonempty →
        C ∩ Z ⊆ (A₂ ∩ Z) ∪ (B₂ ∩ Z) → C = A₂ ∨ C = B₂ := by
      intro C hC hCm hsub
      obtain ⟨l, hl⟩ := hCm
      rcases mem_union.1 (hsub hl) with h | h
      · exact Or.inl (hF.eq_of_mem_roots_of_mem hC hA₂ (mem_inter.1 hl).1 (mem_inter.1 h).1)
      · exact Or.inr (hF.eq_of_mem_roots_of_mem hC hB₂ (mem_inter.1 hl).1 (mem_inter.1 h).1)
    have h1 := hin hA₁ hA₁m (hU ▸ subset_union_left)
    have h2 := hin hB₁ hB₁m (hU ▸ subset_union_right)
    rcases h1 with rfl | rfl <;> rcases h2 with rfl | rfl
    · exact absurd rfl hAB₁
    · rfl
    · rw [union_comm]
    · exact absurd rfl hAB₁
  have hcard₂ : #M₂ = (#(roots rF)).choose 2 := by
    rw [← card_image_of_injOn hinj, himage, hrFf.card_merges]
  have hcard : #((merges F).filter fun H => traceForest Z H = rF) + #M₂ =
      (#(roots F)).choose 2 := by
    rw [hM₂, card_filter_add_card_filter_not, hF.card_merges]
  have hsum : ∑ H ∈ merges F, u (traceForest Z H) =
      #((merges F).filter fun H => traceForest Z H = rF) * u rF + ∑ H' ∈ merges rF, u H' := by
    rw [← sum_filter_add_sum_filter_not (merges F) (fun H => traceForest Z H = rF)]
    congr 1
    · rw [sum_congr rfl fun H hH => by rw [(mem_filter.1 hH).2], sum_const, nsmul_eq_mul]
    · rw [← himage, sum_image hinj]
  rw [hsum]
  have hcard' : ((#((merges F).filter fun H => traceForest Z H = rF) : ℕ) : ℝ) =
      ((#(roots F)).choose 2 : ℝ) - ((#(roots rF)).choose 2 : ℝ) := by
    rw [← hcard, ← hcard₂]
    push_cast
    ring
  rw [hcard']
  ring

/-- Intertwining of the generators: `Q M = M Q` on the rows of forests, tested against `w`. -/
private theorem trc_sum_kingmanGenerator {F : Finset (Finset L)} (hF : IsForest F)
    (Z : Finset L) (w : Finset (Finset L) → ℝ) :
    ∑ G, kingmanGenerator F G * w (traceForest Z G) =
      ∑ G', kingmanGenerator (traceForest Z F) G' * w G' := by
  rw [hF.sum_kingmanGenerator_mul (fun G => w (traceForest Z G)),
    (hF.traceForest Z).sum_kingmanGenerator_mul w]
  exact trc_sum_merges hF Z w

/-- The generator is supported on the forest itself and its merges. -/
private theorem trc_kingmanGenerator_ne_zero {F G : Finset (Finset L)} (hF : IsForest F)
    (h : kingmanGenerator F G ≠ 0) : IsForest G := by
  rw [kingmanGenerator_apply_of_isForest] at h
  split_ifs at h with h1 h2
  · exact h1 ▸ hF
  · exact (hF.of_mem_merges h2).1
  · exact absurd rfl h

private theorem trc_sum_kingmanGenerator_pow (Z : Finset L) (n : ℕ) {F : Finset (Finset L)}
    (hF : IsForest F) (w : Finset (Finset L) → ℝ) :
    ∑ G, (kingmanGenerator ^ n) F G * w (traceForest Z G) =
      ∑ G', (kingmanGenerator ^ n) (traceForest Z F) G' * w G' := by
  induction n generalizing F w with
  | zero =>
    simp only [pow_zero, Matrix.one_apply, ite_mul, one_mul, zero_mul, sum_ite_eq, mem_univ,
      ite_true]
  | succ n ih =>
    set u : Finset (Finset L) → ℝ := fun H' => ∑ G', (kingmanGenerator ^ n) H' G' * w G'
      with hu
    have hstep : ∀ H : Finset (Finset L), kingmanGenerator F H *
        ∑ G, (kingmanGenerator ^ n) H G * w (traceForest Z G) =
          kingmanGenerator F H * u (traceForest Z H) := by
      intro H
      by_cases hQ : kingmanGenerator F H = 0
      · rw [hQ, zero_mul, zero_mul]
      · rw [ih (trc_kingmanGenerator_ne_zero hF hQ) w]
    calc ∑ G, (kingmanGenerator ^ (n + 1)) F G * w (traceForest Z G)
        = ∑ H, kingmanGenerator F H *
            ∑ G, (kingmanGenerator ^ n) H G * w (traceForest Z G) := by
          simp_rw [pow_succ', Matrix.mul_apply, sum_mul]
          rw [sum_comm]
          simp_rw [mul_sum, mul_assoc]
      _ = ∑ H, kingmanGenerator F H * u (traceForest Z H) := sum_congr rfl fun H _ => hstep H
      _ = ∑ H', kingmanGenerator (traceForest Z F) H' * u H' :=
          trc_sum_kingmanGenerator hF Z u
      _ = ∑ G', (kingmanGenerator ^ (n + 1)) (traceForest Z F) G' * w G' := by
          simp_rw [hu, pow_succ', Matrix.mul_apply, sum_mul, mul_sum, mul_assoc]
          rw [sum_comm]

set_option backward.isDefEq.respectTransparency false in
/-- The entries of the exponential of a real matrix are given by the exponential series. -/
private theorem trc_hasSum_exp_apply {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (i j : ι) :
    HasSum (fun n : ℕ => ((n.factorial : ℝ))⁻¹ * (A ^ n) i j) (NormedSpace.exp A i j) := by
  open scoped Matrix.Norms.Operator in
  have h := NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) A
  have h2 := Pi.hasSum.mp (Pi.hasSum.mp h i) j
  simpa using h2

/-- Lumpability of Kingman's coalescent, tested against a function `w` of the restriction. -/
theorem sum_kingmanTransition_trace {F : Finset (Finset L)} (hF : IsForest F)
    (Z : Finset L) (t : ℝ) (w : Finset (Finset L) → ℝ) :
    ∑ G, kingmanTransition t F G * w (traceForest Z G) =
      ∑ G', kingmanTransition t (traceForest Z F) G' * w G' := by
  have h1 : HasSum (fun n : ℕ => ∑ G, ((n.factorial : ℝ))⁻¹ *
      ((t • kingmanGenerator (L := L)) ^ n) F G * w (traceForest Z G))
      (∑ G, kingmanTransition t F G * w (traceForest Z G)) :=
    hasSum_sum fun G _ => (trc_hasSum_exp_apply _ F G).mul_right _
  have h2 : HasSum (fun n : ℕ => ∑ G', ((n.factorial : ℝ))⁻¹ *
      ((t • kingmanGenerator (L := L)) ^ n) (traceForest Z F) G' * w G')
      (∑ G', kingmanTransition t (traceForest Z F) G' * w G') :=
    hasSum_sum fun G' _ => (trc_hasSum_exp_apply _ _ G').mul_right _
  refine h1.unique ?_
  convert h2 using 1
  funext n
  simp_rw [smul_pow, Matrix.smul_apply, smul_eq_mul, mul_assoc, ← mul_sum]
  rw [trc_sum_kingmanGenerator_pow Z n hF w]

/-- **Consistency of Kingman's coalescent** (lumpability). -/
theorem kingmanTransition_trace {F : Finset (Finset L)} (hF : IsForest F) (Z : Finset L) (t : ℝ)
    (G' : Finset (Finset L)) :
    ∑ G, (if traceForest Z G = G' then kingmanTransition t F G else 0) =
      kingmanTransition t (traceForest Z F) G' := by
  have h := sum_kingmanTransition_trace hF Z t fun G'' => if G'' = G' then 1 else 0
  simp only [mul_ite, mul_one, mul_zero, sum_ite_eq', mem_univ, ite_true] at h
  exact h

theorem kingmanAbsorption_trace {F : Finset (Finset L)} (hF : IsForest F) (Z : Finset L)
    (G' : Finset (Finset L)) :
    ∑ G, (if traceForest Z G = G' then kingmanAbsorption F G else 0) =
      kingmanAbsorption (traceForest Z F) G' := by
  have h1 : Filter.Tendsto
      (fun t => ∑ G, (if traceForest Z G = G' then kingmanTransition t F G else 0))
      Filter.atTop
      (nhds (∑ G, (if traceForest Z G = G' then kingmanAbsorption F G else 0))) := by
    refine tendsto_finsetSum _ fun G _ => ?_
    split_ifs
    · exact tendsto_kingmanTransition hF G
    · exact tendsto_const_nhds
  have h2 := tendsto_kingmanTransition (hF.traceForest Z) G'
  simp_rw [kingmanTransition_trace hF Z] at h1
  exact tendsto_nhds_unique h1 h2

/-- The part below some roots, restricted: only the roots meeting `Z` matter. -/
theorem traceForest_forestBelow {F : Finset (Finset L)} (hF : IsForest F) (Z : Finset L)
    {R R' : Finset (Finset L)} (hR : R ⊆ roots F)
    (hR' : ∀ C, C ∈ R' ↔ ∃ A ∈ R, (A ∩ Z).Nonempty ∧ A ∩ Z = C) :
    traceForest Z (forestBelow F R) = forestBelow (traceForest Z F) R' := by
  ext D
  rw [mem_traceForest, mem_forestBelow]
  constructor
  · rintro ⟨A, hA, hm, rfl⟩
    obtain ⟨hAF, C, hC, hAC⟩ := mem_forestBelow.1 hA
    exact ⟨inter_mem_traceForest hAF hm, C ∩ Z, (hR' _).2 ⟨C, hC, hm.mono (trc_mono Z hAC), rfl⟩,
      trc_mono Z hAC⟩
  · rintro ⟨hD, C', hC', hDC'⟩
    obtain ⟨A, hA, hm, rfl⟩ := mem_traceForest.1 hD
    obtain ⟨C, hC, -, rfl⟩ := (hR' _).1 hC'
    refine ⟨A, mem_forestBelow.2 ⟨hA, C, hC, ?_⟩, hm, rfl⟩
    obtain ⟨l, hl⟩ := hm
    have hlC := (mem_inter.1 (hDC' hl)).1
    rcases hF.2 A hA C (roots_subset F (hR hC)) with h | h | h
    · exact h
    · rw [(mem_roots.1 (hR hC)).2 A hA h]
    · exact absurd hlC (disjoint_left.1 h (mem_inter.1 hl).1)

end Fintype

end Phylogenetics
