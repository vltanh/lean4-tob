module

public import External.LegriedEtAl2021.Correlation
public import External.LegriedEtAl2021.Counting

/-!
# The species quartet is the most likely topology

Theorem 1 of Legried, Molloy, Warnow and Roch, equation (5), and its version (7) for the multiple alleles of their Theorem 3: under gene
duplication and loss on a species tree, without incomplete lineage sorting, and for a species quartet `AB|CD`, the topology `ab|cd` of
gene copies is strictly the most likely, both for one copy picked uniformly in each species and for the expected number of choices of
copies.

Both come from `quartet_dom`, for a weight `φ` of the species on the number of copies. The proof is theirs, with `R` the most recent
common ancestor of the four species, or of three of them in a caterpillar, and `I` the number of copies at `R`:

* `expect_bal`, `expect_cat`: the terms of (3), (4), (9), (10), from the classification of tuples of ancestral copies.
* `bal_core`: case (1), a balanced species quartet, (2).
* `cat_core`: case (2), a caterpillar, in their appendix.
* `claim_of_sep`: the law of total probability, by induction along the path from the root to `R`.
* `eq5`, `eq7`: the two forms; `theorem1`: identifiability, on quartets.

Departure from the paper: they fix `R` in the species tree, and condition on the number of copies there. The conditioning is the same
here, one edge at a time: `claim_of_sep`, `catClaim_of_trip` induct on the tree, for a forest of copies at the top of an edge. In the
caterpillar, `D` is fixed at the first speciation below which `A`, `B`, `C` lie, which is the independence they use in Appendix A.3.
-/

@[expose] public noncomputable section

open scoped ENNReal Classical

namespace External.LegriedEtAl2021

variable {X : Type}

/-! ### The terms of the sums -/

section Expansion

variable {I : Type} [Fintype I]

theorem card_forestLeaves (ρ : I → Path) (h : I → Leaves X) (y : X) :
    Multiset.card (forestLeaves ρ h y) = ∑ k, cnt y (h k) := by
  simp [forestLeaves, cnt, Multiset.card_sum]

theorem forestLeaves_eq_zero (ρ : I → Path) {h : I → Leaves X} {y : X} (hz : ∀ k, h k y = 0) : forestLeaves ρ h y = 0 := by
  simp [forestLeaves, hz]

theorem mem_forestLeaves {ρ : I → Path} {h : I → Leaves X} {y : X} {d : Path} (hd : d ∈ forestLeaves ρ h y) :
    ∃ k, ρ k <+: d := by
  simp only [forestLeaves, Multiset.mem_sum, Multiset.mem_map] at hd
  obtain ⟨k, -, q, -, rfl⟩ := hd
  exact ⟨k, List.prefix_append _ _⟩

/-- **The terms of (3) and (4)**: the number of choices of copies with a topology, by the ancestral copies at `R`, when the topology is
determined by these. -/
theorem topo_forest (ρa ρb ρc ρd : I → Path) (A B C D : I → Multiset Path) (pat : Path → Path → Path → Path → Prop)
    (Γ : I → I → I → I → Prop)
    (hΓ : ∀ w x y z a b c d, ρa w <+: a → ρb x <+: b → ρc y <+: c → ρd z <+: d → (pat a b c d ↔ Γ w x y z)) :
    topo pat (∑ w, (A w).map (ρa w ++ ·)) (∑ x, (B x).map (ρb x ++ ·)) (∑ y, (C y).map (ρc y ++ ·)) (∑ z, (D z).map (ρd z ++ ·)) =
      ∑ w, ∑ x, ∑ y, ∑ z, ind (Γ w x y z) * (Multiset.card (A w) : ℝ≥0∞) * (Multiset.card (B x) : ℝ≥0∞) *
        (Multiset.card (C y) : ℝ≥0∞) * (Multiset.card (D z) : ℝ≥0∞) := by
  unfold topo
  simp only [sumMS_forest]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [sumMS_const_of_forall (c := ∑ x, ∑ y, ∑ z, ind (Γ w x y z) * (Multiset.card (B x) : ℝ≥0∞) *
    (Multiset.card (C y) : ℝ≥0∞) * (Multiset.card (D z) : ℝ≥0∞)), Finset.mul_sum]
  · refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun z _ => ?_
    ring
  intro a _
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [sumMS_const_of_forall (c := ∑ y, ∑ z, ind (Γ w x y z) * (Multiset.card (C y) : ℝ≥0∞) * (Multiset.card (D z) : ℝ≥0∞)),
    Finset.mul_sum]
  · refine Finset.sum_congr rfl fun y _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun z _ => ?_
    ring
  intro b _
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [sumMS_const_of_forall (c := ∑ z, ind (Γ w x y z) * (Multiset.card (D z) : ℝ≥0∞)), Finset.mul_sum]
  · refine Finset.sum_congr rfl fun z _ => ?_
    ring
  intro c _
  refine Finset.sum_congr rfl fun z _ => ?_
  rw [sumMS_const_of_forall (c := ind (Γ w x y z)), mul_comm]
  intro d _
  exact ind_congr (hΓ w x y z _ _ _ _ (List.prefix_append _ _) (List.prefix_append _ _) (List.prefix_append _ _)
    (List.prefix_append _ _))

/-- **The terms of (9) and (10)**: the same, with the leaves in `D` fixed. -/
theorem topo_forest_three (ρa ρb ρc : I → Path) (A B C : I → Multiset Path) (Ld : Multiset Path)
    (pat : Path → Path → Path → Path → Prop) (Γ : I → I → I → Path → Prop)
    (hΓ : ∀ w x y a b c d, d ∈ Ld → ρa w <+: a → ρb x <+: b → ρc y <+: c → (pat a b c d ↔ Γ w x y d)) :
    topo pat (∑ w, (A w).map (ρa w ++ ·)) (∑ x, (B x).map (ρb x ++ ·)) (∑ y, (C y).map (ρc y ++ ·)) Ld =
      ∑ w, ∑ x, ∑ y, sumMS Ld (fun d => ind (Γ w x y d)) * (Multiset.card (A w) : ℝ≥0∞) * (Multiset.card (B x) : ℝ≥0∞) *
        (Multiset.card (C y) : ℝ≥0∞) := by
  unfold topo
  simp only [sumMS_forest]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [sumMS_const_of_forall (c := ∑ x, ∑ y, sumMS Ld (fun d => ind (Γ w x y d)) * (Multiset.card (B x) : ℝ≥0∞) *
    (Multiset.card (C y) : ℝ≥0∞)), Finset.mul_sum]
  · refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun y _ => ?_
    ring
  intro a _
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [sumMS_const_of_forall (c := ∑ y, sumMS Ld (fun d => ind (Γ w x y d)) * (Multiset.card (C y) : ℝ≥0∞)), Finset.mul_sum]
  · refine Finset.sum_congr rfl fun y _ => ?_
    ring
  intro b _
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [sumMS_const_of_forall (c := sumMS Ld (fun d => ind (Γ w x y d))), mul_comm]
  intro c _
  unfold sumMS
  refine congrArg _ (Multiset.map_congr rfl fun d hd => ?_)
  exact ind_congr (hΓ w x y _ _ _ d hd (List.prefix_append _ _) (List.prefix_append _ _) (List.prefix_append _ _))

/-- Independence of the two sides of a speciation, in the sums of (3) and (4). -/
theorem expect_sum_four {α β : Type*} (P : PMF α) (Q : PMF β) (γ : I → I → I → I → ℝ≥0∞) (a : I → I → α → ℝ≥0∞)
    (b : I → I → β → ℝ≥0∞) :
    expect P (fun h => expect Q fun h' => ∑ w, ∑ x, ∑ y, ∑ z, γ w x y z * a w x h * b y z h') =
      ∑ w, ∑ x, ∑ y, ∑ z, γ w x y z * expect P (a w x) * expect Q (b y z) := by
  have h₁ : ∀ h, expect Q (fun h' => ∑ w, ∑ x, ∑ y, ∑ z, γ w x y z * a w x h * b y z h') =
      ∑ w, ∑ x, ∑ y, ∑ z, γ w x y z * a w x h * expect Q (b y z) := by
    intro h
    simp only [expect_sum, expect_mul_left]
  simp only [h₁, expect_sum]
  refine Finset.sum_congr rfl fun w _ => Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ =>
    Finset.sum_congr rfl fun z _ => ?_
  rw [expect_mul_right, expect_mul_left]

/-- Independence of the two sides of a speciation, in the sums of (9) and (10). -/
theorem expect_sum_three {α β : Type*} (P : PMF α) (Q : PMF β) (γ : I → I → I → ℝ≥0∞) (a : I → I → α → ℝ≥0∞) (b : I → β → ℝ≥0∞) :
    expect P (fun h => expect Q fun h' => ∑ w, ∑ x, ∑ y, γ w x y * a w x h * b y h') =
      ∑ w, ∑ x, ∑ y, γ w x y * expect P (a w x) * expect Q (b y) := by
  have h₁ : ∀ h, expect Q (fun h' => ∑ w, ∑ x, ∑ y, γ w x y * a w x h * b y h') =
      ∑ w, ∑ x, ∑ y, γ w x y * a w x h * expect Q (b y) := by
    intro h
    simp only [expect_sum, expect_mul_left]
  simp only [h₁, expect_sum]
  refine Finset.sum_congr rfl fun w _ => Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
  rw [expect_mul_right, expect_mul_left]

/-- **The expected statistic, on the copies at `R` of a balanced quartet.** -/
theorem expect_bal (φ : ℕ → ℝ≥0∞) (T₁ T₂ : SpeciesTree X) {A B C D : X} (hA : ¬ T₂.Has A) (hB : ¬ T₂.Has B) (hC : ¬ T₁.Has C)
    (hD : ¬ T₁.Has D) (ρ₁ ρ₂ : I → Path) (pat : Path → Path → Path → Path → Prop) (Γ : I → I → I → I → Prop)
    (hΓ : ∀ w x y z a b c d, ρ₁ w <+: a → ρ₁ x <+: b → ρ₂ y <+: c → ρ₂ z <+: d → (pat a b c d ↔ Γ w x y z)) :
    expect (iid I (geneLaw T₁)) (fun h => expect (iid I (geneLaw T₂)) fun h' =>
      score φ pat ((forestLeaves ρ₁ h + forestLeaves ρ₂ h') A) ((forestLeaves ρ₁ h + forestLeaves ρ₂ h') B)
        ((forestLeaves ρ₁ h + forestLeaves ρ₂ h') C) ((forestLeaves ρ₁ h + forestLeaves ρ₂ h') D)) =
      ∑ w, ∑ x, ∑ y, ∑ z, ind (Γ w x y z) * U φ T₁ A B I w x * U φ T₂ C D I y z := by
  unfold U
  rw [← expect_sum_four]
  refine expect_congr fun h hh => expect_congr fun h' hh' => ?_
  have hA' : (forestLeaves ρ₁ h + forestLeaves ρ₂ h') A = forestLeaves ρ₁ h A := by
    rw [Pi.add_apply, forestLeaves_eq_zero ρ₂ (zero_of_iid hh' hA), add_zero]
  have hB' : (forestLeaves ρ₁ h + forestLeaves ρ₂ h') B = forestLeaves ρ₁ h B := by
    rw [Pi.add_apply, forestLeaves_eq_zero ρ₂ (zero_of_iid hh' hB), add_zero]
  have hC' : (forestLeaves ρ₁ h + forestLeaves ρ₂ h') C = forestLeaves ρ₂ h' C := by
    rw [Pi.add_apply, forestLeaves_eq_zero ρ₁ (zero_of_iid hh hC), zero_add]
  have hD' : (forestLeaves ρ₁ h + forestLeaves ρ₂ h') D = forestLeaves ρ₂ h' D := by
    rw [Pi.add_apply, forestLeaves_eq_zero ρ₁ (zero_of_iid hh hD), zero_add]
  rw [hA', hB', hC', hD']
  unfold score
  rw [card_forestLeaves, card_forestLeaves, card_forestLeaves, card_forestLeaves]
  unfold forestLeaves
  rw [topo_forest ρ₁ ρ₁ ρ₂ ρ₂ _ _ _ _ pat Γ hΓ]
  simp only [Finset.mul_sum, pairW]
  refine Finset.sum_congr rfl fun w _ => Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ =>
    Finset.sum_congr rfl fun z _ => ?_
  simp only [cnt]
  ring

/-- **The expected statistic, on the copies at `R` of a caterpillar.** -/
theorem expect_cat (φ : ℕ → ℝ≥0∞) (T₁ T₂ : SpeciesTree X) {A B C : X} (hA : ¬ T₂.Has A) (hB : ¬ T₂.Has B) (hC : ¬ T₁.Has C)
    (ρ₁ ρ₂ : I → Path) (Ld : Multiset Path) (pat : Path → Path → Path → Path → Prop) (Γ : I → I → I → Path → Prop)
    (hΓ : ∀ w x y a b c d, d ∈ Ld → ρ₁ w <+: a → ρ₁ x <+: b → ρ₂ y <+: c → (pat a b c d ↔ Γ w x y d)) :
    expect (iid I (geneLaw T₁)) (fun h => expect (iid I (geneLaw T₂)) fun h' =>
      score φ pat ((forestLeaves ρ₁ h + forestLeaves ρ₂ h') A) ((forestLeaves ρ₁ h + forestLeaves ρ₂ h') B)
        ((forestLeaves ρ₁ h + forestLeaves ρ₂ h') C) Ld) =
      φ (Multiset.card Ld) * ∑ w, ∑ x, ∑ y, sumMS Ld (fun d => ind (Γ w x y d)) * U φ T₁ A B I w x * V φ T₂ C I y := by
  unfold U V
  rw [← expect_sum_three, ← expect_mul_left]
  refine expect_congr fun h hh => ?_
  rw [← expect_mul_left]
  refine expect_congr fun h' hh' => ?_
  have hA' : (forestLeaves ρ₁ h + forestLeaves ρ₂ h') A = forestLeaves ρ₁ h A := by
    rw [Pi.add_apply, forestLeaves_eq_zero ρ₂ (zero_of_iid hh' hA), add_zero]
  have hB' : (forestLeaves ρ₁ h + forestLeaves ρ₂ h') B = forestLeaves ρ₁ h B := by
    rw [Pi.add_apply, forestLeaves_eq_zero ρ₂ (zero_of_iid hh' hB), add_zero]
  have hC' : (forestLeaves ρ₁ h + forestLeaves ρ₂ h') C = forestLeaves ρ₂ h' C := by
    rw [Pi.add_apply, forestLeaves_eq_zero ρ₁ (zero_of_iid hh hC), zero_add]
  rw [hA', hB', hC']
  unfold score
  rw [card_forestLeaves, card_forestLeaves, card_forestLeaves]
  unfold forestLeaves
  rw [topo_forest_three ρ₁ ρ₁ ρ₂ _ _ _ Ld pat Γ hΓ]
  simp only [Finset.mul_sum, pairW, singleW]
  refine Finset.sum_congr rfl fun w _ => Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
  simp only [cnt]
  ring

end Expansion

/-! ### The classification of the tuples of ancestral copies -/

section Classification

variable {I : Type} {ρ : I → Path} {e : Bool}

/-- The topology `ab|cd` on a balanced quartet, by the ancestral copies at `R`: the cases in the sketch before their Theorem 1, and (3). -/
theorem bal_class_ab (hρ : IsAnti ρ) (w x y z : I) (a b c d : Path) (ha : ρ w ++ [e] <+: a) (hb : ρ x ++ [e] <+: b)
    (hc : ρ y ++ [!e] <+: c) (hd : ρ z ++ [!e] <+: d) :
    Pat a b c d ↔ GammaAB (fun w x y z => Pat (ρ w) (ρ x) (ρ y) (ρ z)) w x y z := by
  have ha' : ρ w <+: a := (List.prefix_append _ _).trans ha
  have hb' : ρ x <+: b := (List.prefix_append _ _).trans hb
  have hc' : ρ y <+: c := (List.prefix_append _ _).trans hc
  have hd' : ρ z <+: d := (List.prefix_append _ _).trans hd
  by_cases h₁ : w = x ∨ y = z
  · exact iff_of_true (bal_ab hρ ha hb hc hd h₁) (Or.inl h₁)
  · push Not at h₁
    have hG : GammaAB (fun w x y z => Pat (ρ w) (ρ x) (ρ y) (ρ z)) w x y z ↔ (Dist w x y z ∧ Pat (ρ w) (ρ x) (ρ y) (ρ z)) := by
      unfold GammaAB
      constructor
      · rintro (h | h)
        · exact (h.elim h₁.1 h₁.2).elim
        · exact h
      · exact Or.inr
    rw [hG]
    by_cases h₂ : w = y ∨ x = z
    · refine iff_of_false (fun h => not_pat_of_pat h (bal_ac hρ ha' hb' hc' hd' h₁.1 h₁.2 h₂)) ?_
      rintro ⟨⟨-, h₃, -, -, h₄, -⟩, -⟩
      exact h₂.elim h₃ h₄
    · by_cases h₃ : w = z ∨ x = y
      · refine iff_of_false (fun h => not_pat_of_pat_ad (bal_ad hρ ha' hb' hc' hd' h₁.1 h₁.2 h₃) h) ?_
        rintro ⟨⟨-, -, h₄, h₅, -, -⟩, -⟩
        exact h₃.elim h₄ h₅
      · push Not at h₂ h₃
        have hDist : Dist w x y z := ⟨h₁.1, h₂.1, h₃.1, h₃.2, h₂.2, h₁.2⟩
        rw [pat_lift hρ h₁.1 h₂.1 h₃.1 h₃.2 h₁.2 ha' hb' hc' hd']
        exact ⟨fun h => ⟨hDist, h⟩, fun h => h.2⟩

/-- The topology `ac|bd` on a balanced quartet, by the ancestral copies at `R`: (4). -/
theorem bal_class_ac (hρ : IsAnti ρ) (w x y z : I) (a b c d : Path) (ha : ρ w ++ [e] <+: a) (hb : ρ x ++ [e] <+: b)
    (hc : ρ y ++ [!e] <+: c) (hd : ρ z ++ [!e] <+: d) :
    Pat a c b d ↔ GammaAC (fun w x y z => Pat (ρ w) (ρ x) (ρ y) (ρ z)) w x y z := by
  have ha' : ρ w <+: a := (List.prefix_append _ _).trans ha
  have hb' : ρ x <+: b := (List.prefix_append _ _).trans hb
  have hc' : ρ y <+: c := (List.prefix_append _ _).trans hc
  have hd' : ρ z <+: d := (List.prefix_append _ _).trans hd
  by_cases h₁ : w = x ∨ y = z
  · refine iff_of_false (not_pat_of_pat (bal_ab hρ ha hb hc hd h₁)) ?_
    rintro (⟨h₂, h₃, -⟩ | ⟨⟨h₂, -, -, -, -, h₃⟩, -⟩) <;> exact h₁.elim h₂ h₃
  · push Not at h₁
    by_cases h₂ : w = y ∨ x = z
    · exact iff_of_true (bal_ac hρ ha' hb' hc' hd' h₁.1 h₁.2 h₂) (Or.inl ⟨h₁.1, h₁.2, h₂⟩)
    · have hG : GammaAC (fun w x y z => Pat (ρ w) (ρ x) (ρ y) (ρ z)) w x y z ↔
          (Dist w x y z ∧ Pat (ρ w) (ρ y) (ρ x) (ρ z)) := by
        unfold GammaAC
        constructor
        · rintro (h | h)
          · exact (h₂ h.2.2).elim
          · exact h
        · exact Or.inr
      rw [hG]
      by_cases h₃ : w = z ∨ x = y
      · refine iff_of_false (not_pat_of_pat_ad' (bal_ad hρ ha' hb' hc' hd' h₁.1 h₁.2 h₃)) ?_
        rintro ⟨⟨-, -, h₄, h₅, -, -⟩, -⟩
        exact h₃.elim h₄ h₅
      · push Not at h₂ h₃
        have hDist : Dist w x y z := ⟨h₁.1, h₂.1, h₃.1, h₃.2, h₂.2, h₁.2⟩
        rw [pat_lift hρ h₂.1 h₁.1 h₃.1 h₃.2.symm h₂.2 ha' hc' hb' hd']
        exact ⟨fun h => ⟨hDist, h⟩, fun h => h.2⟩

/-- The topology `ab|cd` on a caterpillar, by the ancestral copies at `R`: (9). -/
theorem cat_class_ab (hρ : IsAnti ρ) (w x y : I) (a b c d : Path) (hdρ : ∀ j, ¬ ρ j <+: d) (ha : ρ w ++ [e] <+: a)
    (hb : ρ x ++ [e] <+: b) (hc : ρ y ++ [!e] <+: c) :
    Pat a b c d ↔ CatAB (fun w x y d => Pat (ρ w) (ρ x) (ρ y) d) w x y d := by
  have ha' : ρ w <+: a := (List.prefix_append _ _).trans ha
  have hb' : ρ x <+: b := (List.prefix_append _ _).trans hb
  have hc' : ρ y <+: c := (List.prefix_append _ _).trans hc
  by_cases h₁ : w = x
  · exact iff_of_true (cat_ab hρ hdρ ha hb hc h₁) (Or.inl h₁)
  · have hG : CatAB (fun w x y d => Pat (ρ w) (ρ x) (ρ y) d) w x y d ↔ (Dist3 w x y ∧ Pat (ρ w) (ρ x) (ρ y) d) := by
      unfold CatAB
      simp [h₁]
    rw [hG]
    by_cases h₂ : y = w
    · refine iff_of_false (fun h => not_pat_of_pat h (cat_ac hρ hdρ ha' hb' hc' h₁ h₂)) ?_
      rintro ⟨⟨-, h₃, -⟩, -⟩
      exact h₃ h₂.symm
    · by_cases h₃ : y = x
      · refine iff_of_false (fun h => not_pat_of_pat_ad (cat_ad hρ hdρ ha' hb' hc' h₁ h₃) h) ?_
        rintro ⟨⟨-, -, h₄⟩, -⟩
        exact h₄ h₃.symm
      · have hDist : Dist3 w x y := ⟨h₁, Ne.symm h₂, Ne.symm h₃⟩
        rw [pat_lift_three hρ h₁ (Ne.symm h₂) (Ne.symm h₃) hdρ ha' hb' hc']
        exact ⟨fun h => ⟨hDist, h⟩, fun h => h.2⟩

/-- The topology `ac|bd` on a caterpillar, by the ancestral copies at `R`: (10). -/
theorem cat_class_ac (hρ : IsAnti ρ) (w x y : I) (a b c d : Path) (hdρ : ∀ j, ¬ ρ j <+: d) (ha : ρ w ++ [e] <+: a)
    (hb : ρ x ++ [e] <+: b) (hc : ρ y ++ [!e] <+: c) :
    Pat a c b d ↔ CatAC (fun w x y d => Pat (ρ w) (ρ x) (ρ y) d) w x y d := by
  have ha' : ρ w <+: a := (List.prefix_append _ _).trans ha
  have hb' : ρ x <+: b := (List.prefix_append _ _).trans hb
  have hc' : ρ y <+: c := (List.prefix_append _ _).trans hc
  by_cases h₁ : w = x
  · refine iff_of_false (not_pat_of_pat (cat_ab hρ hdρ ha hb hc h₁)) ?_
    rintro (⟨h₂, -⟩ | ⟨⟨h₂, -, -⟩, -⟩) <;> exact h₂ h₁
  · by_cases h₂ : y = w
    · exact iff_of_true (cat_ac hρ hdρ ha' hb' hc' h₁ h₂) (Or.inl ⟨h₁, h₂⟩)
    · have hG : CatAC (fun w x y d => Pat (ρ w) (ρ x) (ρ y) d) w x y d ↔ (Dist3 w x y ∧ Pat (ρ w) (ρ y) (ρ x) d) := by
        unfold CatAC
        simp [h₂]
      rw [hG]
      by_cases h₃ : y = x
      · refine iff_of_false (not_pat_of_pat_ad' (cat_ad hρ hdρ ha' hb' hc' h₁ h₃)) ?_
        rintro ⟨⟨-, -, h₄⟩, -⟩
        exact h₄ h₃.symm
      · have hDist : Dist3 w x y := ⟨h₁, Ne.symm h₂, Ne.symm h₃⟩
        rw [pat_lift_three hρ (Ne.symm h₂) h₁ h₃ hdρ ha' hc' hb']
        exact ⟨fun h => ⟨hDist, h⟩, fun h => h.2⟩

end Classification

/-! ### The two cases at `R` -/

section Core

variable {I : Type} [Fintype I]

/-- **Case (1) of Theorem 1, a balanced species quartet, on the copies at `R`**: (2). -/
theorem bal_core (φ : ℕ → ℝ≥0∞) {T₁ T₂ : SpeciesTree X} {A B C D : X} (hT₁ : T₁.Nodup) (hT₂ : T₂.Nodup) (hAB : A ≠ B)
    (hCD : C ≠ D) (hA₁ : T₁.Has A) (hB₁ : T₁.Has B) (hC₂ : T₂.Has C) (hD₂ : T₂.Has D) (hA : ¬ T₂.Has A) (hB : ¬ T₂.Has B)
    (hC : ¬ T₁.Has C) (hD : ¬ T₁.Has D) {ρ : I → Path} (hρ : IsAnti ρ) (e : Bool) :
    PDom
      (expect (iid I (geneLaw T₁)) fun h => expect (iid I (geneLaw T₂)) fun h' =>
        Alt φ A B C D (forestLeaves (fun k => ρ k ++ [e]) h + forestLeaves (fun k => ρ k ++ [!e]) h'))
      (expect (iid I (geneLaw T₁)) fun h => expect (iid I (geneLaw T₂)) fun h' =>
        Sc φ A B C D (forestLeaves (fun k => ρ k ++ [e]) h + forestLeaves (fun k => ρ k ++ [!e]) h'))
      (expect (iid I (geneLaw T₁)) fun h => expect (iid I (geneLaw T₂)) fun h' =>
        Tot φ A B C D (forestLeaves (fun k => ρ k ++ [e]) h + forestLeaves (fun k => ρ k ++ [!e]) h')) := by
  have hU₁ := exch_U φ hAB T₁ hT₁ hA₁ hB₁
  have hU₂ := exch_U φ hCD T₂ hT₂ hC₂ hD₂
  simp only [Alt, Sc, Tot]
  rw [expect_bal φ T₁ T₂ hA hB hC hD _ _ _ (GammaAC fun w x y z => Pat (ρ w) (ρ x) (ρ y) (ρ z))
      (fun w x y z a b c d ha hb hc hd => bal_class_ac hρ w x y z a b c d ha hb hc hd),
    expect_bal φ T₁ T₂ hA hB hC hD _ _ _ (GammaAB fun w x y z => Pat (ρ w) (ρ x) (ρ y) (ρ z))
      (fun w x y z a b c d ha hb hc hd => bal_class_ab hρ w x y z a b c d ha hb hc hd),
    expect_bal φ T₁ T₂ hA hB hC hD _ _ _ (fun _ _ _ _ => True) (fun _ _ _ _ _ _ _ _ _ _ _ _ => Iff.rfl)]
  have h₁ : ∀ w x, U φ T₁ A B I w x = tw _ _ w x := fun w x => hU₁.eq_ite w x
  have h₂ : ∀ y z, U φ T₂ C D I y z = tw _ _ y z := fun y z => hU₂.eq_ite y z
  simp only [h₁, h₂]
  exact bal_algebra (hU₁.off_le_on _) (hU₂.off_le_on _) _

/-- **Case (2) of Theorem 1, a caterpillar, on the copies at `R`**, with the leaves in `D` fixed. -/
theorem cat_core (φ : ℕ → ℝ≥0∞) {T₁ T₂ : SpeciesTree X} {A B C : X} (hT₁ : T₁.Nodup) (hAB : A ≠ B) (hA₁ : T₁.Has A)
    (hB₁ : T₁.Has B) (hA : ¬ T₂.Has A) (hB : ¬ T₂.Has B) (hC : ¬ T₁.Has C) {ρ : I → Path} (hρ : IsAnti ρ) (e : Bool)
    (Ld : Multiset Path) (hLd : ∀ d ∈ Ld, ∀ j, ¬ ρ j <+: d) :
    PDom
      (expect (iid I (geneLaw T₁)) fun h => expect (iid I (geneLaw T₂)) fun h' =>
        score φ (fun a b c d => Pat a c b d)
          ((forestLeaves (fun k => ρ k ++ [e]) h + forestLeaves (fun k => ρ k ++ [!e]) h') A)
          ((forestLeaves (fun k => ρ k ++ [e]) h + forestLeaves (fun k => ρ k ++ [!e]) h') B)
          ((forestLeaves (fun k => ρ k ++ [e]) h + forestLeaves (fun k => ρ k ++ [!e]) h') C) Ld)
      (expect (iid I (geneLaw T₁)) fun h => expect (iid I (geneLaw T₂)) fun h' =>
        score φ Pat
          ((forestLeaves (fun k => ρ k ++ [e]) h + forestLeaves (fun k => ρ k ++ [!e]) h') A)
          ((forestLeaves (fun k => ρ k ++ [e]) h + forestLeaves (fun k => ρ k ++ [!e]) h') B)
          ((forestLeaves (fun k => ρ k ++ [e]) h + forestLeaves (fun k => ρ k ++ [!e]) h') C) Ld)
      (expect (iid I (geneLaw T₁)) fun h => expect (iid I (geneLaw T₂)) fun h' =>
        score φ (fun _ _ _ _ => True)
          ((forestLeaves (fun k => ρ k ++ [e]) h + forestLeaves (fun k => ρ k ++ [!e]) h') A)
          ((forestLeaves (fun k => ρ k ++ [e]) h + forestLeaves (fun k => ρ k ++ [!e]) h') B)
          ((forestLeaves (fun k => ρ k ++ [e]) h + forestLeaves (fun k => ρ k ++ [!e]) h') C) Ld) := by
  have hU₁ := exch_U φ hAB T₁ hT₁ hA₁ hB₁
  rw [expect_cat φ T₁ T₂ hA hB hC _ _ Ld _ (CatAC fun w x y d => Pat (ρ w) (ρ x) (ρ y) d)
      (fun w x y a b c d hd ha hb hc => cat_class_ac hρ w x y a b c d (hLd d hd) ha hb hc),
    expect_cat φ T₁ T₂ hA hB hC _ _ Ld _ (CatAB fun w x y d => Pat (ρ w) (ρ x) (ρ y) d)
      (fun w x y a b c d hd ha hb hc => cat_class_ab hρ w x y a b c d (hLd d hd) ha hb hc),
    expect_cat φ T₁ T₂ hA hB hC _ _ Ld _ (fun _ _ _ _ => True) (fun _ _ _ _ _ _ _ _ _ _ _ => Iff.rfl)]
  have h₁ : ∀ w x, U φ T₁ A B I w x = tw _ _ w x := fun w x => hU₁.eq_ite w x
  obtain ⟨c, hc⟩ : ∃ c, ∀ y : I, V φ T₂ C I y = c := by
    by_cases hI : Nonempty I
    · exact ⟨V φ T₂ C I hI.some, fun y => V_eq φ T₂ C y _⟩
    · exact ⟨0, fun y => (hI ⟨y⟩).elim⟩
  simp only [h₁, hc]
  exact (cat_algebra (hU₁.off_le_on _) Ld _).mul_left _

end Core

/-! ### The law of total probability: down the species tree -/

section Claims

variable {K : PMF Shape} {l r : SpeciesTree X}

/-- **The recursion of the process, on a forest.** -/
theorem expect_forest_node (K : PMF Shape) (l r : SpeciesTree X) (e : Bool) {J : Type} [Fintype J] (ρ : J → Path)
    (f : Leaves X → ℝ≥0∞) :
    expect (iid J (geneLaw (.node K l r))) (fun g => f (forestLeaves ρ g)) =
      expect (iid J K) fun s =>
        expect (iid (Slots s) (geneLaw (child l r e))) fun h =>
          expect (iid (Slots s) (geneLaw (child l r (!e)))) fun h' =>
            f (forestLeaves (fun k => slot ρ s k ++ [e]) h + forestLeaves (fun k => slot ρ s k ++ [!e]) h') := by
  rw [expect_iid_node K l r e]
  simp only [forestLeaves_glueSide]

/-- The comparison for a forest of copies. -/
def Claim (φ : ℕ → ℝ≥0∞) (T : SpeciesTree X) (A B C D : X) : Prop :=
  ∀ (J : Type) [Fintype J] (ρ : J → Path), IsAnti ρ →
    PDom (expect (iid J (geneLaw T)) fun g => Alt φ A B C D (forestLeaves ρ g))
      (expect (iid J (geneLaw T)) fun g => Sc φ A B C D (forestLeaves ρ g))
      (expect (iid J (geneLaw T)) fun g => Tot φ A B C D (forestLeaves ρ g))

/-- The comparison for a forest of copies, with the leaves in `D` fixed, below none of the roots of the forest. -/
def CatClaim (φ : ℕ → ℝ≥0∞) (T : SpeciesTree X) (A B C : X) : Prop :=
  ∀ (J : Type) [Fintype J] (ρ : J → Path), IsAnti ρ → ∀ Ld : Multiset Path, (∀ d ∈ Ld, ∀ j, ¬ ρ j <+: d) →
    PDom (expect (iid J (geneLaw T)) fun g => score φ (fun a b c d => Pat a c b d) (forestLeaves ρ g A) (forestLeaves ρ g B)
        (forestLeaves ρ g C) Ld)
      (expect (iid J (geneLaw T)) fun g => score φ Pat (forestLeaves ρ g A) (forestLeaves ρ g B) (forestLeaves ρ g C) Ld)
      (expect (iid J (geneLaw T)) fun g => score φ (fun _ _ _ _ => True) (forestLeaves ρ g A) (forestLeaves ρ g B)
        (forestLeaves ρ g C) Ld)

theorem not_prefix_slot {J : Type} {ρ : J → Path} {s : J → Shape} {d : Path} (h : ∀ j, ¬ ρ j <+: d) (k : Slots s) :
    ¬ slot ρ s k <+: d := fun h' => h k.1 ((List.prefix_append _ _).trans h')

theorem side_eq_not {e e' : Bool} (h : e' ≠ e) : e' = !e := by
  cases e <;> cases e' <;> simp_all

/-- The side of a speciation with the cluster. -/
theorem exists_side_of_mem_clusters {K : PMF Shape} {l r : SpeciesTree X} {S : Set X}
    (hS : S ∈ (SpeciesTree.node K l r).clusters) {C : X} (hC : (SpeciesTree.node K l r).Has C) (hCS : C ∉ S) :
    ∃ e, S ∈ (child l r e).clusters := by
  simp only [SpeciesTree.clusters, Set.mem_union, Set.mem_singleton_iff] at hS
  rcases hS with (rfl | hS) | hS
  · exact (hCS hC).elim
  · exact ⟨false, hS⟩
  · exact ⟨true, hS⟩

theorem not_mem_leaf_clusters {K : PMF Shape} {x : X} {S : Set X} (hS : S ∈ (SpeciesTree.leaf K x).clusters) {C : X}
    (hC : (SpeciesTree.leaf K x).Has C) (hCS : C ∉ S) : False := by
  simp only [SpeciesTree.clusters, Set.mem_singleton_iff] at hS
  subst hS
  exact hCS hC

/-- **A caterpillar, from the top of an edge above `R`.** -/
theorem catClaim_of_trip (φ : ℕ → ℝ≥0∞) {A B C : X} (hAB : A ≠ B) (T : SpeciesTree X) (hT : T.Nodup) (hTr : T.Trip A B C)
    (hC : T.Has C) : CatClaim φ T A B C := by
  induction T with
  | leaf K x =>
    obtain ⟨S, hS, -, -, hCS⟩ := hTr
    exact (not_mem_leaf_clusters hS hC hCS).elim
  | node K l r ihl ihr =>
    obtain ⟨S, hS, hAS, hBS, hCS⟩ := hTr
    obtain ⟨e, hSe⟩ := exists_side_of_mem_clusters hS hC hCS
    have hA' := SpeciesTree.has_of_mem_cluster hSe hAS
    have hB' := SpeciesTree.has_of_mem_cluster hSe hBS
    have hAn := not_has_child_not hT hA'
    have hBn := not_has_child_not hT hB'
    have hTe : (child l r e).Nodup := by
      cases e
      · exact hT.1
      · exact hT.2.1
    intro J _ ρ hρ Ld hLd
    rw [expect_forest_node K l r e ρ fun L => score φ (fun a b c d => Pat a c b d) (L A) (L B) (L C) Ld,
      expect_forest_node K l r e ρ fun L => score φ Pat (L A) (L B) (L C) Ld,
      expect_forest_node K l r e ρ fun L => score φ (fun _ _ _ _ => True) (L A) (L B) (L C) Ld]
    refine PDom.expect (fun s _ => ?_) (fun s _ => expect_mono fun h _ => expect_mono fun h' _ =>
      score_mono (fun _ _ _ _ _ => trivial) _ _ _ _ _)
    by_cases hCe : (child l r e).Has C
    · -- the three species below one side: go down
      have hIH : CatClaim φ (child l r e) A B C := by
        cases e
        · exact ihl hT.1 ⟨S, hSe, hAS, hBS, hCS⟩ hCe
        · exact ihr hT.2.1 ⟨S, hSe, hAS, hBS, hCS⟩ hCe
      have hCn := not_has_child_not hT hCe
      have hred : ∀ pat : Path → Path → Path → Path → Prop,
          (expect (iid (Slots s) (geneLaw (child l r e))) fun h => expect (iid (Slots s) (geneLaw (child l r (!e)))) fun h' =>
            score φ pat
              ((forestLeaves (fun k => slot ρ s k ++ [e]) h + forestLeaves (fun k => slot ρ s k ++ [!e]) h') A)
              ((forestLeaves (fun k => slot ρ s k ++ [e]) h + forestLeaves (fun k => slot ρ s k ++ [!e]) h') B)
              ((forestLeaves (fun k => slot ρ s k ++ [e]) h + forestLeaves (fun k => slot ρ s k ++ [!e]) h') C) Ld) =
          expect (iid (Slots s) (geneLaw (child l r e))) fun h =>
            score φ pat (forestLeaves (fun k => slot ρ s k ++ [e]) h A) (forestLeaves (fun k => slot ρ s k ++ [e]) h B)
              (forestLeaves (fun k => slot ρ s k ++ [e]) h C) Ld := by
        intro pat
        refine expect_congr fun h _ => ?_
        rw [expect_congr (g := fun _ => score φ pat (forestLeaves (fun k => slot ρ s k ++ [e]) h A)
          (forestLeaves (fun k => slot ρ s k ++ [e]) h B) (forestLeaves (fun k => slot ρ s k ++ [e]) h C) Ld), expect_const]
        intro h' hh'
        simp only [Pi.add_apply, forestLeaves_eq_zero _ (zero_of_iid hh' hAn), forestLeaves_eq_zero _ (zero_of_iid hh' hBn),
          forestLeaves_eq_zero _ (zero_of_iid hh' hCn), add_zero]
      rw [hred, hred, hred]
      exact hIH (Slots s) _ ((isAnti_slot hρ s).append_singleton e) Ld fun d hd k h' =>
        not_prefix_slot (hLd d hd) k ((List.prefix_append _ _).trans h')
    · -- `R` is here
      exact cat_core φ hTe hAB hA' hB' hAn hBn hCe (isAnti_slot hρ s) e Ld fun d hd k => not_prefix_slot (hLd d hd) k

/-- **A balanced species quartet, at the top of the edge above `R`.** -/
theorem claim_bal (φ : ℕ → ℝ≥0∞) (hT : (SpeciesTree.node K l r).Nodup) {A B C D : X} (hAB : A ≠ B) (hCD : C ≠ D) {e : Bool}
    (hA : (child l r e).Has A) (hB : (child l r e).Has B) (hC : (child l r (!e)).Has C) (hD : (child l r (!e)).Has D) :
    Claim φ (.node K l r) A B C D := by
  have hTe : (child l r e).Nodup := by
    cases e
    · exact hT.1
    · exact hT.2.1
  have hTe' : (child l r (!e)).Nodup := by
    cases e
    · exact hT.2.1
    · exact hT.1
  have hnot : ∀ {y : X}, (child l r (!e)).Has y → ¬ (child l r e).Has y := by
    intro y hy
    have := not_has_child_not (e := !e) hT hy
    rwa [Bool.not_not] at this
  intro J _ ρ hρ
  rw [expect_forest_node K l r e ρ (Alt φ A B C D), expect_forest_node K l r e ρ (Sc φ A B C D),
    expect_forest_node K l r e ρ (Tot φ A B C D)]
  refine PDom.expect (fun s _ => ?_) (fun s _ => expect_mono fun h _ => expect_mono fun h' _ => Alt_le_Tot _ _ _ _ _ _)
  exact bal_core φ hTe hTe' hAB hCD hA hB hC hD (not_has_child_not hT hA) (not_has_child_not hT hB) (hnot hC) (hnot hD)
    (isAnti_slot hρ s) e

/-- **A caterpillar, at the first speciation below which `A`, `B`, `C` lie and `D` doesn't**: from here `D` is fixed. -/
theorem claim_cat (φ : ℕ → ℝ≥0∞) (hT : (SpeciesTree.node K l r).Nodup) {A B C D : X} (hAB : A ≠ B) {e : Bool}
    (hA : (child l r e).Has A) (hB : (child l r e).Has B) (hC : (child l r e).Has C) (hD : (child l r (!e)).Has D)
    (hTr : (child l r e).Trip A B C) : Claim φ (.node K l r) A B C D := by
  have hTe : (child l r e).Nodup := by
    cases e
    · exact hT.1
    · exact hT.2.1
  have hDn : ¬ (child l r e).Has D := by
    have := not_has_child_not (e := !e) hT hD
    rwa [Bool.not_not] at this
  have hAn := not_has_child_not hT hA
  have hBn := not_has_child_not hT hB
  have hCn := not_has_child_not hT hC
  have hCl := catClaim_of_trip φ hAB (child l r e) hTe hTr hC
  intro J _ ρ hρ
  rw [expect_forest_node K l r e ρ (Alt φ A B C D), expect_forest_node K l r e ρ (Sc φ A B C D),
    expect_forest_node K l r e ρ (Tot φ A B C D)]
  refine PDom.expect (fun s _ => ?_) (fun s _ => expect_mono fun h _ => expect_mono fun h' _ => Alt_le_Tot _ _ _ _ _ _)
  have hred : ∀ pat : Path → Path → Path → Path → Prop,
      (expect (iid (Slots s) (geneLaw (child l r e))) fun h => expect (iid (Slots s) (geneLaw (child l r (!e)))) fun h' =>
        score φ pat
          ((forestLeaves (fun k => slot ρ s k ++ [e]) h + forestLeaves (fun k => slot ρ s k ++ [!e]) h') A)
          ((forestLeaves (fun k => slot ρ s k ++ [e]) h + forestLeaves (fun k => slot ρ s k ++ [!e]) h') B)
          ((forestLeaves (fun k => slot ρ s k ++ [e]) h + forestLeaves (fun k => slot ρ s k ++ [!e]) h') C)
          ((forestLeaves (fun k => slot ρ s k ++ [e]) h + forestLeaves (fun k => slot ρ s k ++ [!e]) h') D)) =
      expect (iid (Slots s) (geneLaw (child l r (!e)))) fun h' => expect (iid (Slots s) (geneLaw (child l r e))) fun h =>
        score φ pat (forestLeaves (fun k => slot ρ s k ++ [e]) h A) (forestLeaves (fun k => slot ρ s k ++ [e]) h B)
          (forestLeaves (fun k => slot ρ s k ++ [e]) h C) (forestLeaves (fun k => slot ρ s k ++ [!e]) h' D) := by
    intro pat
    conv_rhs => rw [expect_comm]
    refine expect_congr fun h hh => expect_congr fun h' hh' => ?_
    simp only [Pi.add_apply, forestLeaves_eq_zero _ (zero_of_iid hh' hAn), forestLeaves_eq_zero _ (zero_of_iid hh' hBn),
      forestLeaves_eq_zero _ (zero_of_iid hh' hCn), forestLeaves_eq_zero _ (zero_of_iid hh hDn), add_zero, zero_add]
  simp only [Alt, Sc, Tot]
  rw [hred, hred, hred]
  refine PDom.expect (fun h' _ => ?_) (fun h' _ => expect_mono fun h _ => score_mono (fun _ _ _ _ _ => trivial) _ _ _ _ _)
  refine hCl (Slots s) _ ((isAnti_slot hρ s).append_singleton e) _ fun d hd k hk => ?_
  obtain ⟨k', hk'⟩ := mem_forestLeaves hd
  exact not_side_prefix (isAnti_slot hρ s) (e := e) (e' := !e) (by simp) hk hk'

/-! ### Symmetries of the statistic -/

theorem sumMS_comm (M N : Multiset Path) (f : Path → Path → ℝ≥0∞) :
    sumMS M (fun a => sumMS N fun b => f a b) = sumMS N fun b => sumMS M fun a => f a b :=
  Multiset.sum_map_sum_map M N

theorem topo_swap_left (pat : Path → Path → Path → Path → Prop) (La Lb Lc Ld : Multiset Path) :
    topo pat La Lb Lc Ld = topo (fun b a c d => pat a b c d) Lb La Lc Ld := by
  unfold topo
  rw [sumMS_comm]

theorem topo_swap_right (pat : Path → Path → Path → Path → Prop) (La Lb Lc Ld : Multiset Path) :
    topo pat La Lb Lc Ld = topo (fun a b d c => pat a b c d) La Lb Ld Lc := by
  unfold topo
  refine congrArg _ (funext fun a => congrArg _ (funext fun b => ?_))
  rw [sumMS_comm]

theorem topo_swap_pair (pat : Path → Path → Path → Path → Prop) (La Lb Lc Ld : Multiset Path) :
    topo pat La Lb Lc Ld = topo (fun c d a b => pat a b c d) Lc Ld La Lb := by
  unfold topo
  have h₁ : (fun a => sumMS Lb fun b => sumMS Lc fun c => sumMS Ld fun d => ind (pat a b c d)) =
      fun a => sumMS Lc fun c => sumMS Lb fun b => sumMS Ld fun d => ind (pat a b c d) := by
    funext a
    rw [sumMS_comm]
  rw [h₁, sumMS_comm]
  refine congrArg _ (funext fun c => ?_)
  have h₂ : (fun a => sumMS Lb fun b => sumMS Ld fun d => ind (pat a b c d)) =
      fun a => sumMS Ld fun d => sumMS Lb fun b => ind (pat a b c d) := by
    funext a
    rw [sumMS_comm]
  rw [h₂, sumMS_comm]

theorem score_swap_left (φ : ℕ → ℝ≥0∞) (pat : Path → Path → Path → Path → Prop) (La Lb Lc Ld : Multiset Path) :
    score φ pat La Lb Lc Ld = score φ (fun b a c d => pat a b c d) Lb La Lc Ld := by
  unfold score
  rw [topo_swap_left]
  ring

theorem score_swap_right (φ : ℕ → ℝ≥0∞) (pat : Path → Path → Path → Path → Prop) (La Lb Lc Ld : Multiset Path) :
    score φ pat La Lb Lc Ld = score φ (fun a b d c => pat a b c d) La Lb Ld Lc := by
  unfold score
  rw [topo_swap_right]
  ring

theorem score_swap_pair (φ : ℕ → ℝ≥0∞) (pat : Path → Path → Path → Path → Prop) (La Lb Lc Ld : Multiset Path) :
    score φ pat La Lb Lc Ld = score φ (fun c d a b => pat a b c d) Lc Ld La Lb := by
  unfold score
  rw [topo_swap_pair]
  ring

/-- The same topology, on other species' names. -/
theorem score_congr_pat {φ : ℕ → ℝ≥0∞} {pat pat' : Path → Path → Path → Path → Prop} (h : ∀ a b c d, pat a b c d ↔ pat' a b c d)
    (La Lb Lc Ld : Multiset Path) : score φ pat La Lb Lc Ld = score φ pat' La Lb Lc Ld := by
  have : pat = pat' := by
    funext a b c d
    exact propext (h a b c d)
  rw [this]

theorem Sc_swap_both (φ : ℕ → ℝ≥0∞) (A B C D : X) (L : Leaves X) : Sc φ B A D C L = Sc φ A B C D L := by
  unfold Sc
  rw [score_swap_left φ Pat (L A), score_swap_right φ (fun b a c d => Pat a b c d) (L B)]
  exact score_congr_pat (fun a b c d => pat_swap_left.trans pat_swap_right) _ _ _ _

theorem Alt_swap_both (φ : ℕ → ℝ≥0∞) (A B C D : X) (L : Leaves X) : Alt φ B A D C L = Alt φ A B C D L := by
  unfold Alt
  rw [score_swap_left φ (fun a b c d => Pat a c b d) (L A),
    score_swap_right φ (fun b a c d => Pat a c b d) (L B)]
  exact score_congr_pat (fun a b c d => pat_swap_pair) _ _ _ _

theorem Tot_swap_both (φ : ℕ → ℝ≥0∞) (A B C D : X) (L : Leaves X) : Tot φ B A D C L = Tot φ A B C D L := by
  unfold Tot
  rw [score_swap_left φ (fun _ _ _ _ => True) (L A), score_swap_right φ (fun _ _ _ _ => True) (L B)]

theorem Sc_swap_pair (φ : ℕ → ℝ≥0∞) (A B C D : X) (L : Leaves X) : Sc φ C D A B L = Sc φ A B C D L := by
  unfold Sc
  rw [score_swap_pair φ Pat (L A)]
  exact score_congr_pat (fun a b c d => pat_swap_pair) _ _ _ _

theorem Alt_swap_pair (φ : ℕ → ℝ≥0∞) (A B C D : X) (L : Leaves X) : Alt φ C D A B L = Alt φ A B C D L := by
  unfold Alt
  rw [score_swap_pair φ (fun a b c d => Pat a c b d) (L A)]
  exact score_congr_pat (fun a b c d => pat_swap_left.trans pat_swap_right) _ _ _ _

theorem Tot_swap_pair (φ : ℕ → ℝ≥0∞) (A B C D : X) (L : Leaves X) : Tot φ C D A B L = Tot φ A B C D L := by
  unfold Tot
  rw [score_swap_pair φ (fun _ _ _ _ => True) (L A)]

theorem Claim.swap_both {φ : ℕ → ℝ≥0∞} {T : SpeciesTree X} {A B C D : X} (h : Claim φ T B A D C) : Claim φ T A B C D := by
  intro J _ ρ hρ
  simpa only [Sc_swap_both, Alt_swap_both, Tot_swap_both] using h J ρ hρ

theorem Claim.swap_pair {φ : ℕ → ℝ≥0∞} {T : SpeciesTree X} {A B C D : X} (h : Claim φ T C D A B) : Claim φ T A B C D := by
  intro J _ ρ hρ
  simpa only [Sc_swap_pair, Alt_swap_pair, Tot_swap_pair] using h J ρ hρ

/-! ### Down the species tree -/

/-- All four species below one side of a speciation: go down. -/
theorem claim_node_child (φ : ℕ → ℝ≥0∞) (hT : (SpeciesTree.node K l r).Nodup) {A B C D : X} {e : Bool}
    (hA : (child l r e).Has A) (hB : (child l r e).Has B) (hC : (child l r e).Has C) (hD : (child l r e).Has D)
    (hIH : Claim φ (child l r e) A B C D) : Claim φ (.node K l r) A B C D := by
  have hAn := not_has_child_not hT hA
  have hBn := not_has_child_not hT hB
  have hCn := not_has_child_not hT hC
  have hDn := not_has_child_not hT hD
  intro J _ ρ hρ
  rw [expect_forest_node K l r e ρ (Alt φ A B C D), expect_forest_node K l r e ρ (Sc φ A B C D),
    expect_forest_node K l r e ρ (Tot φ A B C D)]
  refine PDom.expect (fun s _ => ?_) (fun s _ => expect_mono fun h _ => expect_mono fun h' _ => Alt_le_Tot _ _ _ _ _ _)
  have hred : ∀ pat : Path → Path → Path → Path → Prop,
      (expect (iid (Slots s) (geneLaw (child l r e))) fun h => expect (iid (Slots s) (geneLaw (child l r (!e)))) fun h' =>
        score φ pat
          ((forestLeaves (fun k => slot ρ s k ++ [e]) h + forestLeaves (fun k => slot ρ s k ++ [!e]) h') A)
          ((forestLeaves (fun k => slot ρ s k ++ [e]) h + forestLeaves (fun k => slot ρ s k ++ [!e]) h') B)
          ((forestLeaves (fun k => slot ρ s k ++ [e]) h + forestLeaves (fun k => slot ρ s k ++ [!e]) h') C)
          ((forestLeaves (fun k => slot ρ s k ++ [e]) h + forestLeaves (fun k => slot ρ s k ++ [!e]) h') D)) =
      expect (iid (Slots s) (geneLaw (child l r e))) fun h =>
        score φ pat (forestLeaves (fun k => slot ρ s k ++ [e]) h A) (forestLeaves (fun k => slot ρ s k ++ [e]) h B)
          (forestLeaves (fun k => slot ρ s k ++ [e]) h C) (forestLeaves (fun k => slot ρ s k ++ [e]) h D) := by
    intro pat
    refine expect_congr fun h _ => ?_
    rw [expect_congr (g := fun _ => score φ pat (forestLeaves (fun k => slot ρ s k ++ [e]) h A)
      (forestLeaves (fun k => slot ρ s k ++ [e]) h B) (forestLeaves (fun k => slot ρ s k ++ [e]) h C)
      (forestLeaves (fun k => slot ρ s k ++ [e]) h D)), expect_const]
    intro h' hh'
    simp only [Pi.add_apply, forestLeaves_eq_zero _ (zero_of_iid hh' hAn), forestLeaves_eq_zero _ (zero_of_iid hh' hBn),
      forestLeaves_eq_zero _ (zero_of_iid hh' hCn), forestLeaves_eq_zero _ (zero_of_iid hh' hDn), add_zero]
  simp only [Alt, Sc, Tot]
  rw [hred, hred, hred]
  exact hIH (Slots s) _ ((isAnti_slot hρ s).append_singleton e)

/-- **The species tree displays `AB|CD` by a cluster with `A`, `B`: the comparison holds.** -/
theorem claim_of_sep (φ : ℕ → ℝ≥0∞) {A B C D : X} (hAB : A ≠ B) (hCD : C ≠ D) (T : SpeciesTree X) (hT : T.Nodup)
    (hC : T.Has C) (hD : T.Has D) (hS : T.Sep A B C D) : Claim φ T A B C D := by
  induction T with
  | leaf K x =>
    obtain ⟨S, hS, -, -, hCS, -⟩ := hS
    exact (not_mem_leaf_clusters hS hC hCS).elim
  | node K l r ihl ihr =>
    obtain ⟨S, hS, hAS, hBS, hCS, hDS⟩ := hS
    obtain ⟨e, hSe⟩ := exists_side_of_mem_clusters hS hC hCS
    have hA' := SpeciesTree.has_of_mem_cluster hSe hAS
    have hB' := SpeciesTree.has_of_mem_cluster hSe hBS
    obtain ⟨e₃, hC'⟩ := has_child_or hC
    obtain ⟨e₄, hD'⟩ := has_child_or hD
    by_cases h₃ : e₃ = e <;> by_cases h₄ : e₄ = e
    · rw [h₃] at hC'
      rw [h₄] at hD'
      refine claim_node_child φ hT hA' hB' hC' hD' ?_
      cases e
      · exact ihl hT.1 hC' hD' ⟨S, hSe, hAS, hBS, hCS, hDS⟩
      · exact ihr hT.2.1 hC' hD' ⟨S, hSe, hAS, hBS, hCS, hDS⟩
    · rw [h₃] at hC'
      rw [side_eq_not h₄] at hD'
      exact claim_cat φ hT hAB hA' hB' hC' hD' ⟨S, hSe, hAS, hBS, hCS⟩
    · rw [h₄] at hD'
      rw [side_eq_not h₃] at hC'
      exact Claim.swap_both (claim_cat φ hT hAB.symm hB' hA' hD' hC' ⟨S, hSe, hBS, hAS, hDS⟩)
    · rw [side_eq_not h₃] at hC'
      rw [side_eq_not h₄] at hD'
      exact claim_bal φ hT hAB hCD hA' hB' hC' hD'

theorem expect_iid_unit {α : Type} (p : PMF α) (F : (Unit → α) → ℝ≥0∞) :
    expect (iid Unit p) F = expect p fun a => F fun _ => a := by
  unfold expect
  rw [← (Equiv.funUnique Unit α).symm.tsum_eq]
  refine tsum_congr fun a => ?_
  congr 1
  simp [piLaw_apply]

theorem forestLeaves_unit (L : Leaves X) : forestLeaves (fun _ : Unit => ([] : Path)) (fun _ => L) = L := by
  funext y
  simp [forestLeaves]

/-- **The statistics compare on the gene tree of one copy at the top of the root edge.** -/
theorem dom_of_claim {φ : ℕ → ℝ≥0∞} {T : SpeciesTree X} {A B C D : X} (h : Claim φ T A B C D) :
    PDom (expect (geneLaw T) (Alt φ A B C D)) (expect (geneLaw T) (Sc φ A B C D)) (expect (geneLaw T) (Tot φ A B C D)) := by
  have h₁ := h Unit (fun _ => []) fun _ _ _ => rfl
  simpa only [expect_iid_unit, forestLeaves_unit] using h₁

theorem SpeciesTree.Sep.swap_left {T : SpeciesTree X} {A B C D : X} (h : T.Sep A B C D) : T.Sep B A C D := by
  obtain ⟨S, hS, h₁, h₂, h₃⟩ := h
  exact ⟨S, hS, h₂, h₁, h₃⟩

theorem SpeciesTree.Sep.swap_right {T : SpeciesTree X} {A B C D : X} (h : T.Sep A B C D) : T.Sep A B D C := by
  obtain ⟨S, hS, h₁, h₂, h₃, h₄⟩ := h
  exact ⟨S, hS, h₁, h₂, h₄, h₃⟩

theorem claim_of_isQuartet (φ : ℕ → ℝ≥0∞) {T : SpeciesTree X} (hT : T.Nodup) {A B C D : X} (hAB : A ≠ B) (hCD : C ≠ D)
    (hA : T.Has A) (hB : T.Has B) (hC : T.Has C) (hD : T.Has D) (hq : T.IsQuartet A B C D) : Claim φ T A B C D := by
  rcases hq with h | h
  · exact claim_of_sep φ hAB hCD T hT hC hD h
  · exact Claim.swap_pair (claim_of_sep φ hCD hAB T hT hA hB h)

/-- The statistic for the topology `ad|bc`. -/
def Alt₂ (φ : ℕ → ℝ≥0∞) (A B C D : X) (L : Leaves X) : ℝ≥0∞ :=
  score φ (fun a b c d => Pat a d b c) (L A) (L B) (L C) (L D)

theorem Alt_swap_left (φ : ℕ → ℝ≥0∞) (A B C D : X) (L : Leaves X) : Alt φ B A C D L = Alt₂ φ A B C D L := by
  unfold Alt Alt₂
  rw [score_swap_left φ (fun a b c d => Pat a d b c) (L A)]
  exact score_congr_pat (fun a b c d => pat_swap_pair) _ _ _ _

theorem Sc_swap_left (φ : ℕ → ℝ≥0∞) (A B C D : X) (L : Leaves X) : Sc φ B A C D L = Sc φ A B C D L := by
  unfold Sc
  rw [score_swap_left φ Pat (L A)]
  exact score_congr_pat (fun a b c d => pat_swap_left) _ _ _ _

theorem Tot_swap_left (φ : ℕ → ℝ≥0∞) (A B C D : X) (L : Leaves X) : Tot φ B A C D L = Tot φ A B C D L := by
  unfold Tot
  rw [score_swap_left φ (fun _ _ _ _ => True) (L A)]

/-- **Equations (5) and (7) together** (`ext:legried_quartet`). Let `T` be a species tree with every species at one leaf, with a law on
shapes for each edge, and `AB|CD` a quartet it displays. Let `φ` weigh the species by their number of copies. Then the expected
statistic of `ab|cd` is at least those of `ac|bd` and `ad|bc`, strictly when the expected total is positive and finite. -/
theorem quartet_dom (φ : ℕ → ℝ≥0∞) {T : SpeciesTree X} (hT : T.Nodup) {A B C D : X} (hAB : A ≠ B) (hCD : C ≠ D)
    (hA : T.Has A) (hB : T.Has B) (hC : T.Has C) (hD : T.Has D) (hq : T.IsQuartet A B C D) :
    PDom (expect (geneLaw T) (Alt φ A B C D)) (expect (geneLaw T) (Sc φ A B C D)) (expect (geneLaw T) (Tot φ A B C D)) ∧
      PDom (expect (geneLaw T) (Alt₂ φ A B C D)) (expect (geneLaw T) (Sc φ A B C D)) (expect (geneLaw T) (Tot φ A B C D)) := by
  refine ⟨dom_of_claim (claim_of_isQuartet φ hT hAB hCD hA hB hC hD hq), ?_⟩
  have hq' : T.IsQuartet B A C D := by
    rcases hq with h | h
    · exact Or.inl h.swap_left
    · exact Or.inr h.swap_right
  have h := dom_of_claim (claim_of_isQuartet φ hT hAB.symm hCD hB hA hC hD hq')
  have e₁ : Alt φ B A C D = Alt₂ φ A B C D := funext (Alt_swap_left φ A B C D)
  have e₂ : Sc φ B A C D = Sc φ A B C D := funext (Sc_swap_left φ A B C D)
  have e₃ : Tot φ B A C D = Tot φ A B C D := funext (Tot_swap_left φ A B C D)
  rwa [e₁, e₂, e₃] at h

end Claims

/-! ### The two forms of the theorem -/

section Results

/-- The weight of a uniform pick of one copy in a species with `n` copies. -/
def pickWeight (n : ℕ) : ℝ≥0∞ := (n : ℝ≥0∞)⁻¹

/-- All four species have a copy. -/
def Present (A B C D : X) (L : Leaves X) : Prop := L A ≠ 0 ∧ L B ≠ 0 ∧ L C ≠ 0 ∧ L D ≠ 0

theorem sumMS_const (M : Multiset Path) (c : ℝ≥0∞) : sumMS M (fun _ => c) = (Multiset.card M : ℝ≥0∞) * c :=
  sumMS_const_of_forall fun _ _ => rfl

/-- All choices of copies. -/
theorem topo_true (La Lb Lc Ld : Multiset Path) :
    topo (fun _ _ _ _ => True) La Lb Lc Ld =
      (Multiset.card La : ℝ≥0∞) * (Multiset.card Lb : ℝ≥0∞) * (Multiset.card Lc : ℝ≥0∞) * (Multiset.card Ld : ℝ≥0∞) := by
  unfold topo
  simp only [ind_true trivial, sumMS_const]
  ring

theorem inv_mul_card_of_ne {M : Multiset Path} (hM : M ≠ 0) :
    ((Multiset.card M : ℝ≥0∞))⁻¹ * (Multiset.card M : ℝ≥0∞) = 1 := by
  refine ENNReal.inv_mul_cancel ?_ (ENNReal.natCast_ne_top _)
  simpa using hM

/-- With the weight of a uniform pick, the total is the indicator that all four species have a copy. -/
theorem Tot_pick (A B C D : X) (L : Leaves X) : Tot pickWeight A B C D L = ind (Present A B C D L) := by
  unfold Tot score
  rw [topo_true]
  simp only [pickWeight]
  by_cases hP : Present A B C D L
  · obtain ⟨h₁, h₂, h₃, h₄⟩ := hP
    rw [ind_true ⟨h₁, h₂, h₃, h₄⟩]
    calc _ = (((Multiset.card (L A) : ℝ≥0∞))⁻¹ * (Multiset.card (L A) : ℝ≥0∞)) *
          (((Multiset.card (L B) : ℝ≥0∞))⁻¹ * (Multiset.card (L B) : ℝ≥0∞)) *
          (((Multiset.card (L C) : ℝ≥0∞))⁻¹ * (Multiset.card (L C) : ℝ≥0∞)) *
          (((Multiset.card (L D) : ℝ≥0∞))⁻¹ * (Multiset.card (L D) : ℝ≥0∞)) := by ring
      _ = 1 := by
        rw [inv_mul_card_of_ne h₁, inv_mul_card_of_ne h₂, inv_mul_card_of_ne h₃, inv_mul_card_of_ne h₄]
        simp
  · rw [ind_false hP]
    have h0 : (Multiset.card (L A) : ℝ≥0∞) * (Multiset.card (L B) : ℝ≥0∞) * (Multiset.card (L C) : ℝ≥0∞) *
        (Multiset.card (L D) : ℝ≥0∞) = 0 := by
      by_contra hne
      refine hP ?_
      simp only [mul_eq_zero, not_or, Nat.cast_eq_zero, Multiset.card_eq_zero] at hne
      exact ⟨hne.1.1.1, hne.1.1.2, hne.1.2, hne.2⟩
    rw [h0, mul_zero]

/-- **The probability of a topology of four gene copies**, picked independently and uniformly in the four species, given that all four
species have a copy. -/
def probTopology (T : SpeciesTree X) (pat : Path → Path → Path → Path → Prop) (A B C D : X) : ℝ≥0∞ :=
  expect (geneLaw T) (fun L => score pickWeight pat (L A) (L B) (L C) (L D)) / expect (geneLaw T) (fun L => ind (Present A B C D L))

theorem expect_ind_le_one (p : PMF (Leaves X)) (P : Leaves X → Prop) : expect p (fun L => ind (P L)) ≤ 1 := by
  calc expect p (fun L => ind (P L)) ≤ expect p (fun _ => 1) := expect_mono fun L _ => ind_le_one _
    _ = 1 := expect_const _ _

theorem div_lt_div_of_lt {x y c : ℝ≥0∞} (h : x < y) (hc : c ≠ 0) (hc' : c ≠ ⊤) : x / c < y / c := by
  rw [div_eq_mul_inv, div_eq_mul_inv, mul_comm x, mul_comm y]
  exact (ENNReal.mul_lt_mul_iff_right (ENNReal.inv_ne_zero.2 hc') (ENNReal.inv_ne_top.2 hc)).2 h

/-- **Equation (5) in the proof of Theorem 1** (`ext:legried_eq5`). Under gene duplication and loss on a species tree, without
incomplete lineage sorting, with `AB|CD` a quartet of the species tree, and one gene copy picked uniformly in each species, given that
all four species have a copy, the topology `ab|cd` is strictly more likely than `ac|bd` and `ad|bc`. This needs that all four have a copy
with positive probability, for the conditioning to make sense. -/
theorem eq5 {T : SpeciesTree X} (hT : T.Nodup) {A B C D : X} (hAB : A ≠ B) (hCD : C ≠ D) (hA : T.Has A) (hB : T.Has B)
    (hC : T.Has C) (hD : T.Has D) (hq : T.IsQuartet A B C D)
    (hpos : 0 < expect (geneLaw T) fun L => ind (Present A B C D L)) :
    probTopology T (fun a b c d => Pat a c b d) A B C D < probTopology T Pat A B C D ∧
      probTopology T (fun a b c d => Pat a d b c) A B C D < probTopology T Pat A B C D := by
  obtain ⟨h₁, h₂⟩ := quartet_dom pickWeight hT hAB hCD hA hB hC hD hq
  have ht : expect (geneLaw T) (Tot pickWeight A B C D) = expect (geneLaw T) fun L => ind (Present A B C D L) :=
    congrArg _ (funext (Tot_pick A B C D))
  have hfin : (expect (geneLaw T) fun L => ind (Present A B C D L)) < ⊤ := (expect_ind_le_one _ _).trans_lt ENNReal.one_lt_top
  rw [ht] at h₁ h₂
  exact ⟨div_lt_div_of_lt (h₁.2 hpos hfin) hpos.ne' hfin.ne, div_lt_div_of_lt (h₂.2 hpos hfin) hpos.ne' hfin.ne⟩

/-- The number of choices of one copy in each species with a topology. -/
def numTopology (pat : Path → Path → Path → Path → Prop) (A B C D : X) (L : Leaves X) : ℝ≥0∞ :=
  topo pat (L A) (L B) (L C) (L D)

/-- The number of choices of one copy in each species. -/
def numChoices (A B C D : X) (L : Leaves X) : ℝ≥0∞ :=
  (Multiset.card (L A) : ℝ≥0∞) * (Multiset.card (L B) : ℝ≥0∞) * (Multiset.card (L C) : ℝ≥0∞) * (Multiset.card (L D) : ℝ≥0∞)

theorem score_one (pat : Path → Path → Path → Path → Prop) (La Lb Lc Ld : Multiset Path) :
    score (fun _ => 1) pat La Lb Lc Ld = topo pat La Lb Lc Ld := by
  simp [score]

/-- **Equation (7) in the proof of Theorem 3** (`ext:legried_eq7`). The same with all gene copies treated as multiple alleles: the
expected number of choices of one copy in each species with the topology `ab|cd` is strictly larger than for `ac|bd`, `ad|bc`. This needs
that the expected number of choices is positive and finite, which they don't state: it holds for a birth-death process at positive
rates, whose moments are finite. -/
theorem eq7 {T : SpeciesTree X} (hT : T.Nodup) {A B C D : X} (hAB : A ≠ B) (hCD : C ≠ D) (hA : T.Has A) (hB : T.Has B)
    (hC : T.Has C) (hD : T.Has D) (hq : T.IsQuartet A B C D) (hpos : 0 < expect (geneLaw T) (numChoices A B C D))
    (hfin : expect (geneLaw T) (numChoices A B C D) < ⊤) :
    expect (geneLaw T) (numTopology (fun a b c d => Pat a c b d) A B C D) < expect (geneLaw T) (numTopology Pat A B C D) ∧
      expect (geneLaw T) (numTopology (fun a b c d => Pat a d b c) A B C D) < expect (geneLaw T) (numTopology Pat A B C D) := by
  obtain ⟨h₁, h₂⟩ := quartet_dom (fun _ => 1) hT hAB hCD hA hB hC hD hq
  have ht : Tot (fun _ => 1) A B C D = numChoices A B C D := by
    funext L
    simp only [Tot, numChoices, score_one, topo_true]
  have hS : Sc (fun _ => 1) A B C D = numTopology Pat A B C D := by
    funext L
    simp only [Sc, numTopology, score_one]
  have hAl : Alt (fun _ => 1) A B C D = numTopology (fun a b c d => Pat a c b d) A B C D := by
    funext L
    simp only [Alt, numTopology, score_one]
  have hAl₂ : Alt₂ (fun _ => 1) A B C D = numTopology (fun a b c d => Pat a d b c) A B C D := by
    funext L
    simp only [Alt₂, numTopology, score_one]
  rw [ht, hS, hAl] at h₁
  rw [ht, hS, hAl₂] at h₂
  exact ⟨h₁.2 hpos hfin, h₂.2 hpos hfin⟩

/-! ### Identifiability -/

theorem SpeciesTree.self_mem_clusters (T : SpeciesTree X) : {y | T.Has y} ∈ T.clusters := by
  cases T with
  | leaf K x => exact Set.mem_singleton _
  | node K l r => exact Or.inl (Or.inl rfl)

theorem mem_clusters_node_of_child {K : PMF Shape} {l r : SpeciesTree X} {e : Bool} {S : Set X}
    (hS : S ∈ (child l r e).clusters) : S ∈ (SpeciesTree.node K l r).clusters := by
  cases e
  · exact Or.inl (Or.inr hS)
  · exact Or.inr hS

/-- **Among three species of a rooted binary tree, a cluster holds two of them and not the third.** -/
theorem trip_trichotomy {A B C : X} (hAB : A ≠ B) (T : SpeciesTree X) (hT : T.Nodup)
    (hA : T.Has A) (hB : T.Has B) (hC : T.Has C) : T.Trip A B C ∨ T.Trip A C B ∨ T.Trip B C A := by
  induction T with
  | leaf K x => exact absurd ((show A = x from hA).trans (show B = x from hB).symm) hAB
  | node K l r ihl ihr =>
    obtain ⟨e, hA'⟩ := has_child_or hA
    obtain ⟨e₂, hB'⟩ := has_child_or hB
    obtain ⟨e₃, hC'⟩ := has_child_or hC
    have hS : ∀ {e : Bool}, {y | (child l r e).Has y} ∈ (SpeciesTree.node K l r).clusters := fun {e} =>
      mem_clusters_node_of_child (SpeciesTree.self_mem_clusters _)
    have hup : ∀ {e : Bool} {x y z : X}, (child l r e).Trip x y z → (SpeciesTree.node K l r).Trip x y z := by
      rintro e x y z ⟨S, hSe, h⟩
      exact ⟨S, mem_clusters_node_of_child hSe, h⟩
    by_cases h₂ : e₂ = e <;> by_cases h₃ : e₃ = e
    · rw [h₂] at hB'
      rw [h₃] at hC'
      have hIH : (child l r e).Trip A B C ∨ (child l r e).Trip A C B ∨ (child l r e).Trip B C A := by
        cases e
        · exact ihl hT.1 hA' hB' hC'
        · exact ihr hT.2.1 hA' hB' hC'
      exact hIH.elim (fun h => Or.inl (hup h)) fun h => Or.inr (h.elim (fun h => Or.inl (hup h)) fun h => Or.inr (hup h))
    · rw [h₂] at hB'
      rw [side_eq_not h₃] at hC'
      have hC'' : ¬ (child l r e).Has C := by
        have := not_has_child_not (e := !e) hT hC'
        rwa [Bool.not_not] at this
      exact Or.inl ⟨_, hS, hA', hB', hC''⟩
    · rw [h₃] at hC'
      rw [side_eq_not h₂] at hB'
      have hB'' : ¬ (child l r e).Has B := by
        have := not_has_child_not (e := !e) hT hB'
        rwa [Bool.not_not] at this
      exact Or.inr (Or.inl ⟨_, hS, hA', hC', hB''⟩)
    · rw [side_eq_not h₂] at hB'
      rw [side_eq_not h₃] at hC'
      exact Or.inr (Or.inr ⟨_, hS, hB', hC', not_has_child_not hT hA'⟩)

/-- **A rooted binary species tree displays one of the three quartets on four of its species.** -/
theorem quartet_trichotomy {A B C D : X} (hAB : A ≠ B) (hAC : A ≠ C) (hBC : B ≠ C) (T : SpeciesTree X) (hT : T.Nodup) (hA : T.Has A) (hB : T.Has B) (hC : T.Has C) (hD : T.Has D) :
    T.IsQuartet A B C D ∨ T.IsQuartet A C B D ∨ T.IsQuartet A D B C := by
  induction T with
  | leaf K x => exact absurd ((show A = x from hA).trans (show B = x from hB).symm) hAB
  | node K l r ihl ihr =>
    obtain ⟨e, hA'⟩ := has_child_or hA
    obtain ⟨e₂, hB'⟩ := has_child_or hB
    obtain ⟨e₃, hC'⟩ := has_child_or hC
    obtain ⟨e₄, hD'⟩ := has_child_or hD
    have hS : ∀ {e : Bool}, {y | (child l r e).Has y} ∈ (SpeciesTree.node K l r).clusters := fun {e} =>
      mem_clusters_node_of_child (SpeciesTree.self_mem_clusters _)
    have hnot : ∀ {y : X}, (child l r (!e)).Has y → ¬ (child l r e).Has y := by
      intro y hy
      have := not_has_child_not (e := !e) hT hy
      rwa [Bool.not_not] at this
    have hnot' : ∀ {y : X}, (child l r e).Has y → ¬ (child l r (!e)).Has y := fun hy => not_has_child_not hT hy
    -- a cluster on one side, with the fourth species on the other
    have hsep : ∀ {e' : Bool} {x y z w : X}, (child l r e').Trip x y z → (child l r (!e')).Has w →
        (SpeciesTree.node K l r).Sep x y z w := by
      rintro e' x y z w ⟨S, hSe, h₁, h₂, h₃⟩ hw
      refine ⟨S, mem_clusters_node_of_child hSe, h₁, h₂, h₃, fun h₄ => ?_⟩
      have := not_has_child_not (e := !e') hT hw
      rw [Bool.not_not] at this
      exact this (SpeciesTree.has_of_mem_cluster hSe h₄)
    have hTe : ∀ e' : Bool, (child l r e').Nodup := by
      intro e'
      cases e'
      · exact hT.1
      · exact hT.2.1
    by_cases h₂ : e₂ = e <;> by_cases h₃ : e₃ = e <;> by_cases h₄ : e₄ = e
    · rw [h₂] at hB'
      rw [h₃] at hC'
      rw [h₄] at hD'
      have hup : ∀ {x y z w : X}, (child l r e).Sep x y z w → (SpeciesTree.node K l r).Sep x y z w := by
        rintro x y z w ⟨S, hSe, h⟩
        exact ⟨S, mem_clusters_node_of_child hSe, h⟩
      have hIH : (child l r e).IsQuartet A B C D ∨ (child l r e).IsQuartet A C B D ∨ (child l r e).IsQuartet A D B C := by
        cases e
        · exact ihl hT.1 hA' hB' hC' hD'
        · exact ihr hT.2.1 hA' hB' hC' hD'
      rcases hIH with h | h | h
      · exact Or.inl (h.imp hup hup)
      · exact Or.inr (Or.inl (h.imp hup hup))
      · exact Or.inr (Or.inr (h.imp hup hup))
    · -- alone: `D`
      rw [h₂] at hB'
      rw [h₃] at hC'
      rw [side_eq_not h₄] at hD'
      rcases trip_trichotomy hAB _ (hTe e) hA' hB' hC' with h | h | h
      · exact Or.inl (Or.inl (hsep h hD'))
      · exact Or.inr (Or.inl (Or.inl (hsep h hD')))
      · exact Or.inr (Or.inr (Or.inr (hsep h hD')))
    · -- alone: `C`
      rw [h₂] at hB'
      rw [h₄] at hD'
      rw [side_eq_not h₃] at hC'
      rcases trip_trichotomy hAB _ (hTe e) hA' hB' hD' with h | h | h
      · exact Or.inl (Or.inl (hsep h hC').swap_right)
      · exact Or.inr (Or.inr (Or.inl (hsep h hC')))
      · exact Or.inr (Or.inl (Or.inr (hsep h hC')))
    · -- `AB|CD`
      rw [h₂] at hB'
      rw [side_eq_not h₃] at hC'
      rw [side_eq_not h₄] at hD'
      exact Or.inl (Or.inl ⟨_, hS, hA', hB', hnot hC', hnot hD'⟩)
    · -- alone: `B`
      rw [h₃] at hC'
      rw [h₄] at hD'
      rw [side_eq_not h₂] at hB'
      rcases trip_trichotomy hAC _ (hTe e) hA' hC' hD' with h | h | h
      · exact Or.inr (Or.inl (Or.inl (hsep h hB').swap_right))
      · exact Or.inr (Or.inr (Or.inl (hsep h hB').swap_right))
      · exact Or.inl (Or.inr (hsep h hB'))
    · -- `AC|BD`
      rw [h₃] at hC'
      rw [side_eq_not h₂] at hB'
      rw [side_eq_not h₄] at hD'
      exact Or.inr (Or.inl (Or.inl ⟨_, hS, hA', hC', hnot hB', hnot hD'⟩))
    · -- `AD|BC`
      rw [h₄] at hD'
      rw [side_eq_not h₂] at hB'
      rw [side_eq_not h₃] at hC'
      exact Or.inr (Or.inr (Or.inl ⟨_, hS, hA', hD', hnot hB', hnot hC'⟩))
    · -- alone: `A`
      rw [side_eq_not h₂] at hB'
      rw [side_eq_not h₃] at hC'
      rw [side_eq_not h₄] at hD'
      have hA'' : (child l r (!(!e))).Has A := by rwa [Bool.not_not]
      rcases trip_trichotomy hBC _ (hTe (!e)) hB' hC' hD' with h | h | h
      · exact Or.inr (Or.inr (Or.inr (hsep h hA'').swap_right))
      · exact Or.inr (Or.inl (Or.inr (hsep h hA'').swap_right))
      · exact Or.inl (Or.inr (hsep h hA'').swap_right)

theorem topo_swap_mid (pat : Path → Path → Path → Path → Prop) (La Lb Lc Ld : Multiset Path) :
    topo pat La Lb Lc Ld = topo (fun a c b d => pat a b c d) La Lc Lb Ld := by
  unfold topo
  refine congrArg _ (funext fun a => ?_)
  rw [sumMS_comm]

theorem score_swap_mid (φ : ℕ → ℝ≥0∞) (pat : Path → Path → Path → Path → Prop) (La Lb Lc Ld : Multiset Path) :
    score φ pat La Lb Lc Ld = score φ (fun a c b d => pat a b c d) La Lc Lb Ld := by
  unfold score
  rw [topo_swap_mid]
  ring

/-- Two species trees with the same probabilities of topologies can't display `AB|CD` and `AC|BD`. -/
theorem not_isQuartet_of_same {T T' : SpeciesTree X} (hT : T.Nodup) (hT' : T'.Nodup) {A B C D : X} (hAB : A ≠ B) (hAC : A ≠ C)
    (hBD : B ≠ D) (hCD : C ≠ D) (hA : T.Has A) (hB : T.Has B) (hC : T.Has C) (hD : T.Has D) (hA' : T'.Has A) (hB' : T'.Has B)
    (hC' : T'.Has C) (hD' : T'.Has D) (hSc : expect (geneLaw T) (Sc pickWeight A B C D) = expect (geneLaw T') (Sc pickWeight A B C D))
    (hAlt : expect (geneLaw T) (Alt pickWeight A B C D) = expect (geneLaw T') (Alt pickWeight A B C D))
    (hpos : 0 < expect (geneLaw T) fun L => ind (Present A B C D L)) (hq : T.IsQuartet A B C D) : ¬ T'.IsQuartet A C B D := by
  intro hq'
  have h₁ := (quartet_dom pickWeight hT hAB hCD hA hB hC hD hq).1
  have h₂ := (quartet_dom pickWeight hT' hAC hBD hA' hC' hB' hD' hq').1
  have ht : expect (geneLaw T) (Tot pickWeight A B C D) = expect (geneLaw T) fun L => ind (Present A B C D L) :=
    congrArg _ (funext (Tot_pick A B C D))
  have hfin : (expect (geneLaw T) fun L => ind (Present A B C D L)) < ⊤ := (expect_ind_le_one _ _).trans_lt ENNReal.one_lt_top
  rw [ht] at h₁
  have hlt := h₁.2 hpos hfin
  have e₁ : Alt pickWeight A C B D = Sc pickWeight A B C D := by
    funext L
    unfold Alt Sc
    exact (score_swap_mid pickWeight Pat _ _ _ _).symm
  have e₂ : Sc pickWeight A C B D = Alt pickWeight A B C D := by
    funext L
    unfold Alt Sc
    exact score_swap_mid pickWeight (fun a b c d => Pat a c b d) _ _ _ _ |>.symm
  rw [e₁, e₂] at h₂
  rw [hSc, hAlt] at hlt
  exact absurd h₂.1 (not_le.2 hlt)

/-- **Theorem 1 of Legried, Molloy, Warnow and Roch** (`ext:legried_thm1`): "Let `T` be a species tree with `n ≥ 4` leaves. Then `T`,
without its root, is identifiable from the distribution of MUL-trees under the GDL model over `T`", on quartets. If two species trees on
the same species give the same probabilities of topologies on four gene copies picked uniformly, and all four species have a copy with
positive probability, then the unrooted trees display the same quartets, and so they agree, by the fact that a tree is defined by its
quartets that they cite and we don't restate. These probabilities are determined by the distribution of the unrooted MUL-tree. -/
theorem theorem1 {T T' : SpeciesTree X} (hT : T.Nodup) (hT' : T'.Nodup) {A B C D : X} (hAB : A ≠ B) (hAC : A ≠ C) (hAD : A ≠ D)
    (hBC : B ≠ C) (hBD : B ≠ D) (hCD : C ≠ D) (hA : T.Has A) (hB : T.Has B) (hC : T.Has C) (hD : T.Has D) (hA' : T'.Has A)
    (hB' : T'.Has B) (hC' : T'.Has C) (hD' : T'.Has D)
    (hSc : expect (geneLaw T) (Sc pickWeight A B C D) = expect (geneLaw T') (Sc pickWeight A B C D))
    (hAlt : expect (geneLaw T) (Alt pickWeight A B C D) = expect (geneLaw T') (Alt pickWeight A B C D))
    (hAlt₂ : expect (geneLaw T) (Alt₂ pickWeight A B C D) = expect (geneLaw T') (Alt₂ pickWeight A B C D))
    (hpos : 0 < expect (geneLaw T) fun L => ind (Present A B C D L)) (hq : T.IsQuartet A B C D) : T'.IsQuartet A B C D := by
  rcases quartet_trichotomy hAB hAC hBC T' hT' hA' hB' hC' hD' with h | h | h
  · exact h
  · exact (not_isQuartet_of_same hT hT' hAB hAC hBD hCD hA hB hC hD hA' hB' hC' hD' hSc hAlt hpos hq h).elim
  · -- the case `AD|BC` is the last one, for the species `B, A, C, D`
    have e₁ : ∀ S : SpeciesTree X, expect (geneLaw S) (Sc pickWeight B A C D) = expect (geneLaw S) (Sc pickWeight A B C D) := fun S =>
      congrArg _ (funext (Sc_swap_left pickWeight A B C D))
    have e₂ : ∀ S : SpeciesTree X, expect (geneLaw S) (Alt pickWeight B A C D) = expect (geneLaw S) (Alt₂ pickWeight A B C D) := fun S =>
      congrArg _ (funext (Alt_swap_left pickWeight A B C D))
    have hP : ∀ L : Leaves X, ind (Present B A C D L) = ind (Present A B C D L) := by
      intro L
      refine ind_congr ?_
      unfold Present
      tauto
    have hpos' : 0 < expect (geneLaw T) fun L => ind (Present B A C D L) := by
      simpa only [hP] using hpos
    have hq₁ : T.IsQuartet B A C D := by
      rcases hq with h' | h'
      · exact Or.inl h'.swap_left
      · exact Or.inr h'.swap_right
    have hq₂ : T'.IsQuartet B C A D := by
      rcases h with h' | h'
      · exact Or.inr h'
      · exact Or.inl h'
    exact (not_isQuartet_of_same hT hT' hAB.symm hBC hAD hCD hB hA hC hD hB' hA' hC' hD' (by rw [e₁, e₁, hSc]) (by rw [e₂, e₂, hAlt₂])
      hpos' hq₁ hq₂).elim

/-- **A mixture of species trees**: if the gene family first picks a species tree at random, and all of those display `AB|CD`, the
statistics compare in the same way. -/
theorem mixture_dom {ι : Type*} (φ : ℕ → ℝ≥0∞) (ν : PMF ι) (T : ι → SpeciesTree X) {A B C D : X} (hAB : A ≠ B) (hCD : C ≠ D)
    (h : ∀ i, ν i ≠ 0 → (T i).Nodup ∧ (T i).Has A ∧ (T i).Has B ∧ (T i).Has C ∧ (T i).Has D ∧ (T i).IsQuartet A B C D) :
    PDom (expect (ν.bind fun i => geneLaw (T i)) (Alt φ A B C D)) (expect (ν.bind fun i => geneLaw (T i)) (Sc φ A B C D))
        (expect (ν.bind fun i => geneLaw (T i)) (Tot φ A B C D)) ∧
      PDom (expect (ν.bind fun i => geneLaw (T i)) (Alt₂ φ A B C D)) (expect (ν.bind fun i => geneLaw (T i)) (Sc φ A B C D))
        (expect (ν.bind fun i => geneLaw (T i)) (Tot φ A B C D)) := by
  simp only [expect_bind]
  have hdom := fun i (hi : ν i ≠ 0) =>
    quartet_dom φ (h i hi).1 hAB hCD (h i hi).2.1 (h i hi).2.2.1 (h i hi).2.2.2.1 (h i hi).2.2.2.2.1 (h i hi).2.2.2.2.2
  refine ⟨PDom.expect (fun i hi => (hdom i hi).1) fun i _ => expect_mono fun L _ => Alt_le_Tot _ _ _ _ _ _,
    PDom.expect (fun i hi => (hdom i hi).2) fun i _ => expect_mono fun L _ => score_mono (fun _ _ _ _ _ => trivial) _ _ _ _ _⟩

/-! ### Positive probabilities -/

/-- The shape of a copy that goes through an edge unchanged. -/
def Shape.one : Shape := ⟨{[]}, by
  intro p hp q hq _
  rw [Finset.mem_singleton] at hp hq
  rw [hp, hq]⟩

/-- On each edge, a gene copy goes through with no duplication and no loss with positive probability, as under a birth-death process. -/
def SpeciesTree.Survives : SpeciesTree X → Prop
  | .leaf K _ => K Shape.one ≠ 0
  | .node K l r => K Shape.one ≠ 0 ∧ l.Survives ∧ r.Survives

/-- A gene tree with a copy in every species has positive probability. -/
theorem exists_geneLaw_ne_zero (T : SpeciesTree X) (hT : T.Survives) : ∃ L, geneLaw T L ≠ 0 ∧ ∀ y, T.Has y → L y ≠ 0 := by
  induction T with
  | leaf K x =>
    refine ⟨fun y => if y = x then Shape.one.copies.val else 0, ?_, fun y hy => ?_⟩
    · refine (PMF.mem_support_iff _ _).1 ((PMF.mem_support_bind_iff _ _ _).2 ⟨Shape.one, (PMF.mem_support_iff _ _).2 hT, ?_⟩)
      exact (PMF.mem_support_pure_iff _ _).2 rfl
    · have hyx : y = x := hy
      simp [hyx, Shape.one]
  | node K l r ihl ihr =>
    obtain ⟨Ll, hLl, hl⟩ := ihl hT.2.1
    obtain ⟨Lr, hLr, hr⟩ := ihr hT.2.2
    refine ⟨glue Shape.one (fun _ => Ll) (fun _ => Lr), ?_, fun y hy => ?_⟩
    · refine (PMF.mem_support_iff _ _).1 ((PMF.mem_support_bind_iff _ _ _).2 ⟨Shape.one, (PMF.mem_support_iff _ _).2 hT.1, ?_⟩)
      refine (PMF.mem_support_bind_iff _ _ _).2 ⟨fun _ => Ll, (PMF.mem_support_iff _ _).2 ?_, ?_⟩
      · rw [piLaw_apply]
        exact Finset.prod_ne_zero_iff.2 fun _ _ => hLl
      refine (PMF.mem_support_bind_iff _ _ _).2 ⟨fun _ => Lr, (PMF.mem_support_iff _ _).2 ?_, ?_⟩
      · rw [piLaw_apply]
        exact Finset.prod_ne_zero_iff.2 fun _ _ => hLr
      exact (PMF.mem_support_pure_iff _ _).2 rfl
    · have hcard : Multiset.card (glue Shape.one (fun _ => Ll) (fun _ => Lr) y) =
          Multiset.card (Ll y) + Multiset.card (Lr y) := by
        have h1 : Shape.one.copies.card = 1 := rfl
        simp [glue, forestLeaves, Multiset.card_sum, h1]
      intro h0
      rw [h0] at hcard
      simp only [Multiset.card_zero] at hcard
      rcases hy with hy | hy
      · exact hl y hy (Multiset.card_eq_zero.1 (by omega))
      · exact hr y hy (Multiset.card_eq_zero.1 (by omega))

theorem expect_pos_of {α : Type*} {p : PMF α} {f : α → ℝ≥0∞} {a : α} (ha : p a ≠ 0) (hf : f a ≠ 0) : 0 < expect p f := by
  rw [pos_iff_ne_zero]
  intro h
  unfold expect at h
  exact (mul_ne_zero ha hf) (ENNReal.tsum_eq_zero.1 h a)

/-- All four species have a copy with positive probability, on a tree where a copy can go through each edge. -/
theorem present_pos {T : SpeciesTree X} (hS : T.Survives) {A B C D : X} (hA : T.Has A) (hB : T.Has B) (hC : T.Has C) (hD : T.Has D) :
    0 < expect (geneLaw T) fun L => ind (Present A B C D L) := by
  obtain ⟨L, hL, h⟩ := exists_geneLaw_ne_zero T hS
  refine expect_pos_of hL ?_
  rw [ind_true ⟨h A hA, h B hB, h C hC, h D hD⟩]
  exact one_ne_zero

/-- The number of choices is positive in expectation, on a tree where a copy can go through each edge. -/
theorem numChoices_pos {T : SpeciesTree X} (hS : T.Survives) {A B C D : X} (hA : T.Has A) (hB : T.Has B) (hC : T.Has C) (hD : T.Has D) :
    0 < expect (geneLaw T) (numChoices A B C D) := by
  obtain ⟨L, hL, h⟩ := exists_geneLaw_ne_zero T hS
  refine expect_pos_of hL ?_
  have hne : ∀ y, T.Has y → (Multiset.card (L y) : ℝ≥0∞) ≠ 0 := fun y hy => by
    simpa using h y hy
  simp only [numChoices]
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero (hne A hA) (hne B hB)) (hne C hC)) (hne D hD)

end Results

end External.LegriedEtAl2021
