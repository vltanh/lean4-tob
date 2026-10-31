module

public import Basic.Phylogenetics.TreeSplits

/-!
# Tree metrics through split families

The metric `treeMetric T w` of a split family `T` with positive weights `w`, through the four-point
expression `d(a,c) + d(b,e) - d(a,b) - d(c,e)`. This expression is twice the weight of the splits
`ab|ce` minus twice the weight of the splits `ac|be` (`TreeMetric.fourPoint_treeMetric`). Hence the
quartet trees displayed on `T`, and so `T` and `w`, can be read off from the metric (Buneman 1971).

API (namespace `Phylogenetics.TreeMetric`): `ne_of_card_four`, `card_four_of_ne`,
`exists_eq_quartetTree`, `taxa_quartetTree`, `displays_quartetTree_iff`, `fourPoint_treeMetric`,
`displays_iff_fourPoint`, `exists_pair_not_in_proper`, `eq_of_treeMetric_eq`.
-/

@[expose] public noncomputable section

open Finset
open scoped Classical

namespace Phylogenetics.TreeMetric

variable {X : Type*} [DecidableEq X]

theorem ne_of_card_four {a b c d : X} (h : ({a, b, c, d} : Finset X).card = 4) :
    a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d := by
  have key : ∀ u v w z : X, ({u, v, w, z} : Finset X).card = 4 → u ≠ v := by
    rintro u v w z h rfl
    have : ({u, u, w, z} : Finset X).card ≤ 3 := by
      rw [Finset.insert_idem]; exact Finset.card_le_three
    omega
  refine ⟨key _ _ _ _ h, ?_, ?_, ?_, ?_, ?_⟩
  · apply key a c b d; rw [← h]; congr 1; grind
  · apply key a d b c; rw [← h]; congr 1; grind
  · apply key b c a d; rw [← h]; congr 1; grind
  · apply key b d a c; rw [← h]; congr 1; grind
  · apply key c d a b; rw [← h]; congr 1; grind

theorem card_four_of_ne {a b c d : X} (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c)
    (hbd : b ≠ d) (hcd : c ≠ d) : ({a, b, c, d} : Finset X).card = 4 := by
  rw [card_insert_of_notMem (by simp [*]), card_insert_of_notMem (by simp [*]), card_pair hcd]

section

variable [Fintype X]

omit [Fintype X] in
/-- Every quartet tree is `ab|cd` for four distinct taxa. -/
theorem exists_eq_quartetTree (s : QuartetTree X) :
    ∃ a b c d : X, ∃ h : ({a, b, c, d} : Finset X).card = 4, s = quartetTree a b c d h := by
  obtain ⟨s, h2, hc, hd⟩ := s
  obtain ⟨B, C, hBC, rfl⟩ := Finset.card_eq_two.mp h2
  obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp (hc B (by simp))
  obtain ⟨c, d, hcd, rfl⟩ := Finset.card_eq_two.mp (hc C (by simp))
  have hdis := hd {a, b} (by simp) {c, d} (by simp) hBC
  have hdis' := Finset.disjoint_left.mp hdis
  have : ({a, b, c, d} : Finset X).card = 4 :=
    card_four_of_ne hab (fun h => hdis' (a := a) (by simp) (by simp [h]))
      (fun h => hdis' (a := a) (by simp) (by simp [h]))
      (fun h => hdis' (a := b) (by simp) (by simp [h]))
      (fun h => hdis' (a := b) (by simp) (by simp [h])) hcd
  exact ⟨a, b, c, d, this, rfl⟩

omit [Fintype X] in
@[simp] theorem val_quartetTree {a b c d : X} (h : ({a, b, c, d} : Finset X).card = 4) :
    (quartetTree a b c d h).val = {{a, b}, {c, d}} := rfl

omit [Fintype X] in
@[simp] theorem taxa_quartetTree {a b c d : X} (h : ({a, b, c, d} : Finset X).card = 4) :
    (quartetTree a b c d h).taxa = {a, b, c, d} := by
  simp [QuartetTree.taxa, quartetTree]
  grind

/-- A split family displays `ab|cd` exactly when one of its sides contains `a, b` and not `c, d`. -/
theorem displays_quartetTree_iff {T : Finset (Finset X)} (hT : IsSplitFamily T) {a b c d : X}
    (h : ({a, b, c, d} : Finset X).card = 4) :
    Displays T (quartetTree a b c d h) ↔ ∃ A ∈ T, a ∈ A ∧ b ∈ A ∧ c ∉ A ∧ d ∉ A := by
  obtain ⟨hab, hac, had, hbc, hbd, hcd⟩ := ne_of_card_four h
  constructor
  · rintro ⟨A, hA, hs⟩
    simp only [taxa_quartetTree, val_quartetTree, mem_insert, mem_singleton] at hs
    rcases hs with hs | hs
    · have hmem := fun z => Finset.ext_iff.mp hs z
      simp only [mem_inter, mem_insert, mem_singleton] at hmem
      refine ⟨A, hA, ((hmem a).mpr (Or.inl rfl)).1, ((hmem b).mpr (Or.inr rfl)).1, fun h' => ?_,
        fun h' => ?_⟩
      · rcases (hmem c).mp ⟨h', by simp⟩ with h'' | h''
        · exact hac h''.symm
        · exact hbc h''.symm
      · rcases (hmem d).mp ⟨h', by simp⟩ with h'' | h''
        · exact had h''.symm
        · exact hbd h''.symm
    · have hmem := fun z => Finset.ext_iff.mp hs z
      simp only [mem_inter, mem_insert, mem_singleton] at hmem
      refine ⟨Aᶜ, hT.compl_mem A hA, mem_compl.mpr fun h' => ?_, mem_compl.mpr fun h' => ?_,
        fun h' => mem_compl.mp h' ((hmem c).mpr (Or.inl rfl)).1,
        fun h' => mem_compl.mp h' ((hmem d).mpr (Or.inr rfl)).1⟩
      · rcases (hmem a).mp ⟨h', by simp⟩ with h'' | h''
        · exact hac h''
        · exact had h''
      · rcases (hmem b).mp ⟨h', by simp⟩ with h'' | h''
        · exact hbc h''
        · exact hbd h''
  · rintro ⟨A, hA, ha, hb, hc, hd⟩
    refine ⟨A, hA, ?_⟩
    simp only [taxa_quartetTree, val_quartetTree, mem_insert, mem_singleton]
    left
    ext x
    simp only [mem_inter, mem_insert, mem_singleton]
    constructor
    · rintro ⟨hx, rfl | rfl | rfl | rfl⟩
      · exact Or.inl rfl
      · exact Or.inr rfl
      · exact absurd hx hc
      · exact absurd hx hd
    · rintro (rfl | rfl)
      · exact ⟨ha, Or.inl rfl⟩
      · exact ⟨hb, Or.inr (Or.inl rfl)⟩

omit [Fintype X] in
/-- The quartet tree on a set of four taxa with a given cherry. -/
theorem exists_quartetTree_of_subset {q B : Finset X} (hq : q.card = 4) (hB : B ⊆ q)
    (hB2 : B.card = 2) : ∃ s : QuartetTree X, s.taxa = q ∧ s.val = {B, q \ B} := by
  have hc : (q \ B).card = 2 := by rw [Finset.card_sdiff_of_subset hB]; omega
  have hdis : Disjoint B (q \ B) := Finset.disjoint_sdiff
  have hne : B ≠ q \ B := by
    intro h
    obtain ⟨x, hx⟩ := Finset.card_pos.mp (by omega : 0 < B.card)
    exact Finset.disjoint_left.mp hdis hx (h ▸ hx)
  have hs : IsQuartetTree ({B, q \ B} : Finset (Finset X)) := by
    refine ⟨Finset.card_pair hne, ?_, ?_⟩
    · intro C hC
      simp only [Finset.mem_insert, Finset.mem_singleton] at hC
      rcases hC with rfl | rfl <;> assumption
    · intro C hC D hD hCD
      simp only [Finset.mem_insert, Finset.mem_singleton] at hC hD
      rcases hC with rfl | rfl <;> rcases hD with rfl | rfl
      · exact absurd rfl hCD
      · exact hdis
      · exact hdis.symm
      · exact absurd rfl hCD
  refine ⟨⟨_, hs⟩, ?_, rfl⟩
  simp only [QuartetTree.taxa, Finset.sup_insert, Finset.sup_singleton, id]
  exact Finset.union_sdiff_of_subset hB

omit [Fintype X] in
/-- A quartet tree is determined by its taxa and one cherry. -/
theorem val_eq_of_mem {s : QuartetTree X} {B : Finset X} (hB : B ∈ s.val) :
    s.val = {B, s.taxa \ B} := by
  obtain ⟨a, b, c, d, h, rfl⟩ := exists_eq_quartetTree s
  obtain ⟨hab, hac, had, hbc, hbd, hcd⟩ := ne_of_card_four h
  rw [taxa_quartetTree]
  simp only [val_quartetTree, mem_insert, mem_singleton] at hB ⊢
  rcases hB with rfl | rfl
  · have : ({a, b, c, d} : Finset X) \ {a, b} = {c, d} := by
      ext x
      simp only [mem_sdiff, mem_insert, mem_singleton]
      grind
    rw [this]
  · have : ({a, b, c, d} : Finset X) \ {c, d} = {a, b} := by
      ext x
      simp only [mem_sdiff, mem_insert, mem_singleton]
      grind
    rw [this, Finset.pair_comm]

omit [Fintype X] in
theorem eq_of_mem_of_taxa_eq {s s' : QuartetTree X} {B : Finset X} (hB : B ∈ s.val)
    (hB' : B ∈ s'.val) (h : s.taxa = s'.taxa) : s = s' :=
  Subtype.ext (by rw [val_eq_of_mem hB, val_eq_of_mem hB', h])

omit [Fintype X] in
/-- The other cherry of a quartet tree. -/
theorem sdiff_mem_of_mem {s : QuartetTree X} {B : Finset X} (hB : B ∈ s.val) :
    s.taxa \ B ∈ s.val := by
  rw [val_eq_of_mem hB]
  simp

omit [Fintype X] in
/-- A cherry is a subset of the taxa. -/
theorem subset_taxa_of_mem {s : QuartetTree X} {B : Finset X} (hB : B ∈ s.val) : B ⊆ s.taxa :=
  Finset.le_sup (f := id) hB

omit [Fintype X] in
/-- The count of a predicate on four distinct taxa. -/
theorem card_filter_four {a b c d : X} (h : ({a, b, c, d} : Finset X).card = 4) (P : X → Prop) :
    (({a, b, c, d} : Finset X).filter P).card =
      (if P a then 1 else 0) + (if P b then 1 else 0) + (if P c then 1 else 0) +
        (if P d then 1 else 0) := by
  obtain ⟨hab, hac, had, hbc, hbd, hcd⟩ := ne_of_card_four h
  rw [Finset.card_filter, Finset.sum_insert (by simp [*]), Finset.sum_insert (by simp [*]),
    Finset.sum_pair hcd]
  ring

omit [Fintype X] in
/-- The count of the four distinct taxa in a set. -/
theorem card_inter_four {a b c d : X} (h : ({a, b, c, d} : Finset X).card = 4) (A : Finset X) :
    (A ∩ {a, b, c, d}).card =
      (if a ∈ A then 1 else 0) + (if b ∈ A then 1 else 0) + (if c ∈ A then 1 else 0) +
        (if d ∈ A then 1 else 0) := by
  obtain ⟨hab, hac, had, hbc, hbd, hcd⟩ := ne_of_card_four h
  rw [Finset.inter_comm, ← Finset.filter_mem_eq_inter, Finset.card_filter,
    Finset.sum_insert (by simp [*]), Finset.sum_insert (by simp [*]), Finset.sum_pair hcd]
  ring

/-- A family of sides does not resolve the four taxa `q` exactly when none has two of them. -/
theorem forall_not_displays_iff {T : Finset (Finset X)} {q : Finset X} (hq : q.card = 4) :
    (∀ s ∈ treesOn q, ¬ Displays T s) ↔ ∀ A ∈ T, (A ∩ q).card ≠ 2 := by
  constructor
  · intro h A hA h2
    obtain ⟨s, hst, hsv⟩ := exists_quartetTree_of_subset hq Finset.inter_subset_right h2
    refine h s (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hst⟩) ⟨A, hA, ?_⟩
    rw [hst, hsv]
    simp
  · rintro h s hs ⟨A, hA, hmem⟩
    have hst : s.taxa = q := (Finset.mem_filter.mp hs).2
    rw [hst] at hmem
    exact h A hA (s.2.2.1 _ hmem)

/-- The four-point expression of a dissimilarity. -/
def fourPoint (δ : X → X → ℝ) (a b c e : X) : ℝ := δ a c + δ b e - δ a b - δ c e

/-- The total weight of the sides containing `a, b` and neither of `c, e`. -/
def sideWeight (T : Finset (Finset X)) (w : Finset X → ℝ) (a b c e : X) : ℝ :=
  ∑ C ∈ T.filter (fun C => a ∈ C ∧ b ∈ C ∧ c ∉ C ∧ e ∉ C), w C

/-- The tree metric as a sum over the sides avoiding a chosen taxon, one for each split. -/
theorem treeMetric_eq_sum_avoiding {T : Finset (Finset X)} (hT : IsSplitFamily T)
    {w : Finset X → ℝ} (hw : ∀ A ∈ T, w Aᶜ = w A) (u v r : X) :
    treeMetric T w u v = ∑ C ∈ T.filter (fun C => r ∉ C), if (u ∈ C ↔ v ∈ C) then 0 else w C := by
  have hsplit : ∑ C ∈ T, (if u ∈ C ∧ v ∉ C ∧ r ∈ C then w C else 0) =
      ∑ C ∈ T, (if v ∈ C ∧ u ∉ C ∧ r ∉ C then w C else 0) := by
    refine Finset.sum_nbij' compl compl (fun C hC => hT.compl_mem C hC)
      (fun C hC => hT.compl_mem C hC) (by simp) (by simp) ?_
    intro C hC
    by_cases hu : u ∈ C <;> by_cases hv : v ∈ C <;> by_cases hr : r ∈ C <;> simp [hu, hv, hr, hw C hC]
  have h1 : treeMetric T w u v = ∑ C ∈ T, (if u ∈ C ∧ v ∉ C ∧ r ∉ C then w C else 0) +
      ∑ C ∈ T, (if u ∈ C ∧ v ∉ C ∧ r ∈ C then w C else 0) := by
    rw [treeMetric, Finset.sum_filter, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun C _ => ?_
    by_cases hu : u ∈ C <;> by_cases hv : v ∈ C <;> by_cases hr : r ∈ C <;> simp [hu, hv, hr]
  rw [h1, hsplit, Finset.sum_filter, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun C _ => ?_
  by_cases hu : u ∈ C <;> by_cases hv : v ∈ C <;> by_cases hr : r ∈ C <;> simp [hu, hv, hr]

/-- **The four-point formula.** -/
theorem fourPoint_treeMetric {T : Finset (Finset X)} (hT : IsSplitFamily T)
    {w : Finset X → ℝ} (hw : ∀ A ∈ T, w Aᶜ = w A) (a b c e : X) :
    fourPoint (treeMetric T w) a b c e = 2 * sideWeight T w a b c e - 2 * sideWeight T w a c b e := by
  have hW : ∀ x y z : X, sideWeight T w x y z e =
      ∑ C ∈ T.filter (fun C => e ∉ C), if x ∈ C ∧ y ∈ C ∧ z ∉ C then w C else 0 := by
    intro x y z
    rw [sideWeight, Finset.sum_filter, Finset.sum_filter]
    refine Finset.sum_congr rfl fun C _ => ?_
    by_cases hx : x ∈ C <;> by_cases hy : y ∈ C <;> by_cases hz : z ∈ C <;> by_cases he : e ∈ C <;>
      simp [hx, hy, hz, he]
  rw [fourPoint, treeMetric_eq_sum_avoiding hT hw a c e, treeMetric_eq_sum_avoiding hT hw b e e,
    treeMetric_eq_sum_avoiding hT hw a b e, treeMetric_eq_sum_avoiding hT hw c e e, hW, hW,
    Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib,
    ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun C hC => ?_
  have he : e ∉ C := (Finset.mem_filter.mp hC).2
  by_cases ha : a ∈ C <;> by_cases hb : b ∈ C <;> by_cases hc : c ∈ C <;> simp [ha, hb, hc, he] <;>
    ring

omit [Fintype X] in
theorem sideWeight_nonneg {T : Finset (Finset X)} {w : Finset X → ℝ} (hw : ∀ A ∈ T, 0 < w A)
    (a b c e : X) : 0 ≤ sideWeight T w a b c e :=
  Finset.sum_nonneg fun C hC => (hw C (Finset.mem_filter.mp hC).1).le

/-- The four-point characterization of the quartet trees displayed on a split family. -/
theorem displays_iff_fourPoint {T : Finset (Finset X)} (hT : IsSplitFamily T)
    {w : Finset X → ℝ} (hpos : ∀ A ∈ T, 0 < w A) (hw : ∀ A ∈ T, w Aᶜ = w A) {a b c d : X}
    (h : ({a, b, c, d} : Finset X).card = 4) :
    Displays T (quartetTree a b c d h) ↔ 0 < fourPoint (treeMetric T w) a b c d := by
  rw [displays_quartetTree_iff hT, fourPoint_treeMetric hT hw]
  constructor
  · rintro ⟨A, hA, ha, hb, hc, hd⟩
    have h0 : sideWeight T w a c b d = 0 := by
      refine Finset.sum_eq_zero fun C hC => ?_
      obtain ⟨hCT, haC, hcC, hbC, hdC⟩ := Finset.mem_filter.mp hC
      exfalso
      rcases hT.compatible A hA C hCT with hsub | hsub | hsub | hsub
      · exact hbC (hsub hb)
      · exact hc (hsub hcC)
      · exact Finset.disjoint_left.mp hsub ha haC
      · have : d ∈ A ∪ C := hsub ▸ Finset.mem_univ d
        rcases Finset.mem_union.mp this with h' | h'
        · exact hd h'
        · exact hdC h'
    have hpos' : 0 < sideWeight T w a b c d :=
      lt_of_lt_of_le (hpos A hA) (Finset.single_le_sum (f := w)
        (fun C hC => (hpos C (Finset.mem_filter.mp hC).1).le)
        (Finset.mem_filter.mpr ⟨hA, ha, hb, hc, hd⟩))
    rw [h0]
    linarith
  · intro h'
    have h0 := sideWeight_nonneg hpos a c b d
    have h1 : 0 < sideWeight T w a b c d := by linarith
    obtain ⟨A, hA, -⟩ := Finset.exists_lt_of_sum_lt (s := T.filter
      (fun C => a ∈ C ∧ b ∈ C ∧ c ∉ C ∧ d ∉ C)) (f := fun _ => (0 : ℝ)) (g := w)
      (by simpa [sideWeight] using h1)
    obtain ⟨hAT, hmem⟩ := Finset.mem_filter.mp hA
    exact ⟨A, hAT, hmem⟩

/-- Taxa on either side of a maximal side `C₀` properly inside the side `A` lie in no common side
properly inside `A`. -/
theorem not_mem_proper_of_maximal {T : Finset (Finset X)} (hT : IsSplitFamily T) {A C₀ : Finset X}
    (hA : A ∈ T) (hC₀ : C₀ ∈ T) (hlt : C₀ ⊂ A) (hmax : ∀ C ∈ T, C ⊂ A → C.card ≤ C₀.card) {u z : X}
    (hu : u ∈ C₀) (hzC : z ∉ C₀) : ∀ C ∈ T, C ⊂ A → ¬ (u ∈ C ∧ z ∈ C) := by
  rintro C hC hCA ⟨huC, hzC'⟩
  rcases hT.compatible C hC C₀ hC₀ with hsub | hsub | hsub | hsub
  · exact hzC (hsub hzC')
  · have : C₀ ⊂ C := ⟨hsub, fun h => hzC (h hzC')⟩
    exact absurd (Finset.card_lt_card this) (not_lt.mpr (hmax C hC hCA))
  · exact Finset.disjoint_left.mp hsub huC hu
  · obtain ⟨t, ht⟩ := hT.compl_nonempty A hA
    have ht' : t ∈ C ∪ C₀ := hsub ▸ Finset.mem_univ t
    have : t ∈ A := by
      rcases Finset.mem_union.mp ht' with h' | h'
      · exact hCA.1 h'
      · exact hlt.1 h'
    exact (Finset.mem_compl.mp ht) this

/-- A side `A` has two taxa, possibly equal, in no side properly inside `A`. -/
theorem exists_pair_not_in_proper {T : Finset (Finset X)} (hT : IsSplitFamily T) {A : Finset X}
    (hA : A ∈ T) : ∃ x ∈ A, ∃ x' ∈ A, ∀ C ∈ T, C ⊂ A → ¬ (x ∈ C ∧ x' ∈ C) := by
  by_cases hne : (T.filter fun C => C ⊂ A).Nonempty
  · obtain ⟨C₀, hC₀, hmax⟩ := Finset.exists_max_image _ Finset.card hne
    obtain ⟨hC₀T, hC₀A⟩ := Finset.mem_filter.mp hC₀
    obtain ⟨u, hu⟩ := hT.nonempty C₀ hC₀T
    obtain ⟨z, hz, hzC⟩ := Finset.exists_of_ssubset hC₀A
    exact ⟨u, hC₀A.1 hu, z, hz, not_mem_proper_of_maximal hT hA hC₀T hC₀A
      (fun C hC hCA => hmax C (Finset.mem_filter.mpr ⟨hC, hCA⟩)) hu hzC⟩
  · obtain ⟨x, hx⟩ := hT.nonempty A hA
    refine ⟨x, hx, x, hx, fun C hC hCA => ?_⟩
    exact absurd (Finset.mem_filter.mpr ⟨hC, hCA⟩) (fun h => hne ⟨C, h⟩)

/-- Weights can be read off from the metric. -/
theorem weight_eq_fourPoint {T : Finset (Finset X)} (hT : IsSplitFamily T) {A : Finset X}
    (hA : A ∈ T) : ∃ x x' y y' : X, ∀ {w : Finset X → ℝ}, (∀ A ∈ T, w Aᶜ = w A) →
      fourPoint (treeMetric T w) x x' y y' = 2 * w A := by
  obtain ⟨x, hx, x', hx', hxx⟩ := exists_pair_not_in_proper hT hA
  obtain ⟨y, hy, y', hy', hyy⟩ := exists_pair_not_in_proper hT (hT.compl_mem A hA)
  refine ⟨x, x', y, y', fun {w} hw => ?_⟩
  have hy₀ := Finset.mem_compl.mp hy
  have hy₀' := Finset.mem_compl.mp hy'
  have h0 : sideWeight T w x y x' y' = 0 := by
    refine Finset.sum_eq_zero fun C hC => ?_
    obtain ⟨hCT, hxC, hyC, hxC', hyC'⟩ := Finset.mem_filter.mp hC
    exfalso
    rcases hT.compatible A hA C hCT with hsub | hsub | hsub | hsub
    · exact hxC' (hsub hx')
    · exact hy₀ (hsub hyC)
    · exact Finset.disjoint_left.mp hsub hx hxC
    · have : y' ∈ A ∪ C := hsub ▸ Finset.mem_univ y'
      rcases Finset.mem_union.mp this with h' | h'
      · exact hy₀' h'
      · exact hyC' h'
  have h1 : sideWeight T w x x' y y' = w A := by
    have : T.filter (fun C => x ∈ C ∧ x' ∈ C ∧ y ∉ C ∧ y' ∉ C) = {A} := by
      refine Finset.eq_singleton_iff_unique_mem.mpr
        ⟨Finset.mem_filter.mpr ⟨hA, hx, hx', hy₀, hy₀'⟩, fun C hC => ?_⟩
      obtain ⟨hCT, hxC, hxC', hyC, hyC'⟩ := Finset.mem_filter.mp hC
      rcases hT.compatible A hA C hCT with hsub | hsub | hsub | hsub
      · by_contra hne
        have hlt : Cᶜ ⊂ Aᶜ := by
          refine ⟨Finset.compl_subset_compl.mpr hsub, fun h => hne ?_⟩
          exact Finset.Subset.antisymm (Finset.compl_subset_compl.mp h) hsub
        exact hyy Cᶜ (hT.compl_mem C hCT) hlt
          ⟨Finset.mem_compl.mpr hyC, Finset.mem_compl.mpr hyC'⟩
      · by_contra hne
        exact hxx C hCT ⟨hsub, fun h => hne (Finset.Subset.antisymm hsub h)⟩ ⟨hxC, hxC'⟩
      · exact absurd hxC (Finset.disjoint_left.mp hsub hx)
      · have : y ∈ A ∪ C := hsub ▸ Finset.mem_univ y
        rcases Finset.mem_union.mp this with h' | h'
        · exact absurd h' hy₀
        · exact absurd h' hyC
    rw [sideWeight, this, Finset.sum_singleton]
  rw [fourPoint_treeMetric hT hw, h0, h1]
  ring

/-- **Buneman's theorem**: a tree metric with positive weights determines the tree and its weights. -/
theorem eq_of_treeMetric_eq (hX : 2 ≤ Fintype.card X) {T T' : Finset (Finset X)}
    (hT : IsUnrootedTree T) (hT' : IsUnrootedTree T') {w w' : Finset X → ℝ}
    (hw : ∀ A ∈ T, 0 < w A ∧ w Aᶜ = w A) (hw' : ∀ A ∈ T', 0 < w' A ∧ w' Aᶜ = w' A)
    (h : treeMetric T w = treeMetric T' w') : T = T' ∧ ∀ A ∈ T, w A = w' A := by
  have hS := (isUnrootedTree_iff hX T).mp hT
  have hS' := (isUnrootedTree_iff hX T').mp hT'
  have hdisp : ∀ s : QuartetTree X, Displays T s ↔ Displays T' s := by
    intro s
    obtain ⟨a, b, c, d, hq, rfl⟩ := exists_eq_quartetTree s
    rw [displays_iff_fourPoint hS (fun A hA => (hw A hA).1) (fun A hA => (hw A hA).2),
      displays_iff_fourPoint hS' (fun A hA => (hw' A hA).1) (fun A hA => (hw' A hA).2), h]
  have hTT : T = T' := Finset.Subset.antisymm
    (subset_of_forall_displays hT' hT fun s hs => (hdisp s).mp hs)
    (subset_of_forall_displays hT hT' fun s hs => (hdisp s).mpr hs)
  refine ⟨hTT, fun A hA => ?_⟩
  subst hTT
  obtain ⟨x, x', y, y', hf⟩ := weight_eq_fourPoint hS hA
  have h1 := hf (w := w) fun A hA => (hw A hA).2
  have h2 := hf (w := w') fun A hA => (hw' A hA).2
  rw [h, h2] at h1
  linarith

/-- With fewer than two taxa, the only tree is empty. -/
theorem eq_empty_of_card_lt_two (hX : Fintype.card X < 2) {T : Finset (Finset X)}
    (hT : IsUnrootedTree T) : T = ∅ := by
  obtain ⟨H, ⟨-, -, hne, -⟩, rfl⟩ := hT
  have hsub : Subsingleton X := Fintype.card_le_one_iff_subsingleton.mp (by omega)
  have huniv : ∀ A ∈ H, A = univ := by
    intro A hA
    obtain ⟨x, hx⟩ := hne A hA
    ext y
    simpa [Subsingleton.elim y x] using hx
  have : H.erase univ = ∅ := by
    ext A
    simp only [mem_erase, notMem_empty, iff_false, not_and]
    exact fun h hA => h (huniv A hA)
  simp [unroot, this]

end

end Phylogenetics.TreeMetric
