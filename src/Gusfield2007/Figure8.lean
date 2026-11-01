module

public import Gusfield2007.Components
public import External.HudsonKaplan1985.Bound

/-!
# Gusfield et al. 2007, Figures 8 and 9: the numbers

- Line 612: `R(M(C_k)) ≥ 2`, which the paper obtains from the program multicross.pl. Here by the search of `Gusfield2007.LabelSearch`, and in fact `R(M(C_k)) = 2`.
- Figure 9, with three recombination nodes, and `R(M) = 3`. The paper needs `≤` only.
- The numbers for `R¹`, which the paper doesn't state: `R¹(M(C_k)) = 3` and `R¹(M) = 6`, by the Hudson-Kaplan bound and a network.
- Also `R_{00000}(M(C_k)) ≤ 2` and `R¹_{00000}(M(C_k)) ≤ 3`, for `F`.
-/

@[expose] public section

open scoped Classical

namespace Gusfield2007

/-- The sites of `C₁`. -/
def fig8Sites₁ : Fin 5 → Fin 10 := Fin.castLE (by decide)

/-- The sites of `C₂`. -/
def fig8Sites₂ : Fin 5 → Fin 10 := Fin.natAdd 5

theorem fig8Sites₁_strictMono : StrictMono fig8Sites₁ := fun a b h => by
  revert a b
  decide

theorem fig8Sites₂_strictMono : StrictMono fig8Sites₂ := fun a b h => by
  revert a b
  decide

theorem fig8Sites₁_range : Set.range fig8Sites₁ = fig8C₁ := Set.ext fun i => by
  change (∃ a, fig8Sites₁ a = i) ↔ i.val < 5
  revert i
  decide

theorem fig8Sites₂_range : Set.range fig8Sites₂ = fig8C₂ := Set.ext fun i => by
  change (∃ a, fig8Sites₂ a = i) ↔ 5 ≤ i.val
  revert i
  decide

/-! ### The components -/

/-- A network for `M(C₁)`, `M(C₂)`, which are the same matrix, with root `00000` and three single crossovers. -/
def fig8CompSingleNet : NetSpec 5 16 18 :=
  ⟨[0, 0, 1, 2, 4, 1, 2, 3, 6, 3, 5, 0, 2, 6, 7, 4, 5, 8],
   [1, 2, 3, 4, 5, 6, 6, 7, 7, 8, 8, 9, 10, 11, 12, 13, 14, 15],
   [0, 1, 2, 3, 4],
   [0, 1, 2, 5, 10, 26, 3, 7, 29, 0, 2, 3, 7, 10, 26, 29]⟩

theorem fig8CompSingleNet_valid : fig8CompSingleNet.Valid := by decide +kernel

theorem fig8CompSingleNet_single : fig8CompSingleNet.SingleCheck := by decide +kernel

theorem fig8CompSingleNet_recombs : fig8CompSingleNet.recombs = 3 := by decide +kernel

/-- A network for `M(C₁)`, `M(C₂)`, with root `00000` and two recombination nodes. -/
def fig8CompMultipleNet : NetSpec 5 15 16 :=
  ⟨[0, 1, 1, 2, 3, 0, 4, 5, 6, 0, 1, 2, 4, 3, 5, 7],
   [1, 2, 3, 4, 5, 6, 6, 7, 7, 8, 9, 10, 11, 12, 13, 14],
   [1, 0, 3, 2, 4],
   [0, 2, 3, 10, 7, 26, 5, 29, 0, 2, 3, 7, 10, 26, 29]⟩

theorem fig8CompMultipleNet_valid : fig8CompMultipleNet.Valid := by decide +kernel

theorem fig8CompMultipleNet_recombs : fig8CompMultipleNet.recombs = 2 := by decide +kernel

/-- The codes of the rows of `M(C₁)`, `M(C₂)`. -/
def fig8CompCodes : List ℕ := [0, 2, 3, 7, 10, 26, 29]

/-- **Line 612**, the fact checked by multicross.pl in the paper: no network for `M(C_k)` has only one recombination node. -/
theorem fig8Comp_check : LabelSearch.check 5 fig8CompCodes 1 = false := by decide +kernel

/-- `R(M(C₁)) = 2` (line 612, for `≥`). -/
theorem fig8_R_multiple₁ : R .multiple (restrictRows fig8C₁ fig8) = 2 := by
  rw [R_restrictRows fig8Sites₁ fig8Sites₁_strictMono fig8Sites₁_range]
  exact R_eq_of_spec (s := fig8CompMultipleNet) (k := 1) fig8CompMultipleNet_valid (by decide +kernel) trivial fig8CompMultipleNet_recombs (Mc := fig8CompCodes) (by decide +kernel) fig8Comp_check

/-- `R(M(C₂)) = 2` (line 612, for `≥`). -/
theorem fig8_R_multiple₂ : R .multiple (restrictRows fig8C₂ fig8) = 2 := by
  rw [R_restrictRows fig8Sites₂ fig8Sites₂_strictMono fig8Sites₂_range]
  exact R_eq_of_spec (s := fig8CompMultipleNet) (k := 1) fig8CompMultipleNet_valid (by decide +kernel) trivial fig8CompMultipleNet_recombs (Mc := fig8CompCodes) (by decide +kernel) fig8Comp_check

/-- The Hudson-Kaplan bound on `M(C_k)`: the pairs of sites `(1, 2)`, `(2, 3)`, `(3, 4)`. -/
theorem fig8Comp_three_le {f : Fin 5 → Fin 10}
    (hinc : Incompatible (fig8.image fun r => r ∘ f) 0 1 ∧ Incompatible (fig8.image fun r => r ∘ f) 1 2 ∧ Incompatible (fig8.image fun r => r ∘ f) 2 3) :
    3 ≤ R .single (fig8.image fun r => r ∘ f) := by
  have hcard : (({(0, 1), (1, 2), (2, 3)} : Finset (Fin 5 × Fin 5))).card = 3 := by decide
  rw [← hcard]
  refine HudsonKaplan1985.card_le_R _ _ (fun p hp => ?_) (fun p hp q hq hne => ?_)
  · rcases Finset.mem_insert.1 hp with rfl | hp
    · exact ⟨by decide, hinc.1⟩
    · rcases Finset.mem_insert.1 hp with rfl | hp
      · exact ⟨by decide, hinc.2.1⟩
      · rw [Finset.mem_singleton.1 hp]
        exact ⟨by decide, hinc.2.2⟩
  · revert hne
    revert q p
    decide

theorem fig8Inc₁ : Incompatible (fig8.image fun r => r ∘ fig8Sites₁) 0 1 ∧ Incompatible (fig8.image fun r => r ∘ fig8Sites₁) 1 2 ∧ Incompatible (fig8.image fun r => r ∘ fig8Sites₁) 2 3 := by
  unfold Incompatible
  decide +kernel

theorem fig8Inc₂ : Incompatible (fig8.image fun r => r ∘ fig8Sites₂) 0 1 ∧ Incompatible (fig8.image fun r => r ∘ fig8Sites₂) 1 2 ∧ Incompatible (fig8.image fun r => r ∘ fig8Sites₂) 2 3 := by
  unfold Incompatible
  decide +kernel

/-- `R¹(M(C₁)) = 3`. Not in the paper. -/
theorem fig8_R_single₁ : R .single (restrictRows fig8C₁ fig8) = 3 := by
  rw [R_restrictRows fig8Sites₁ fig8Sites₁_strictMono fig8Sites₁_range]
  have h₁ := NetSpec.R_le (M := fig8.image fun r => r ∘ fig8Sites₁) fig8CompSingleNet_valid (by decide +kernel)
    (NetSpec.obeys_single_toNetwork _ fig8CompSingleNet_single)
  rw [fig8CompSingleNet_recombs] at h₁
  have h₂ := fig8Comp_three_le fig8Inc₁
  omega

/-- `R¹(M(C₂)) = 3`. Not in the paper. -/
theorem fig8_R_single₂ : R .single (restrictRows fig8C₂ fig8) = 3 := by
  rw [R_restrictRows fig8Sites₂ fig8Sites₂_strictMono fig8Sites₂_range]
  have h₁ := NetSpec.R_le (M := fig8.image fun r => r ∘ fig8Sites₂) fig8CompSingleNet_valid (by decide +kernel)
    (NetSpec.obeys_single_toNetwork _ fig8CompSingleNet_single)
  rw [fig8CompSingleNet_recombs] at h₁
  have h₂ := fig8Comp_three_le fig8Inc₂
  omega

/-- `R_{00000}(M(C₁)) ≤ 2`, for `F`. -/
theorem fig8_RS_multiple₁ : RS .multiple (fig8C₁.domRestrict fun _ => false) (restrictRows fig8C₁ fig8) ≤ 2 := by
  rw [RS_restrictRows fig8Sites₁ fig8Sites₁_strictMono fig8Sites₁_range, ← fig8CompMultipleNet_recombs]
  exact NetSpec.RS_le (c := .multiple) fig8CompMultipleNet_valid (by decide +kernel) trivial (by decide +kernel)

/-- `R_{00000}(M(C₂)) ≤ 2`, for `F`. -/
theorem fig8_RS_multiple₂ : RS .multiple (fig8C₂.domRestrict fun _ => false) (restrictRows fig8C₂ fig8) ≤ 2 := by
  rw [RS_restrictRows fig8Sites₂ fig8Sites₂_strictMono fig8Sites₂_range, ← fig8CompMultipleNet_recombs]
  exact NetSpec.RS_le (c := .multiple) fig8CompMultipleNet_valid (by decide +kernel) trivial (by decide +kernel)

/-- `R¹_{00000}(M(C₁)) ≤ 3`, for `F¹`. -/
theorem fig8_RS_single₁ : RS .single (fig8C₁.domRestrict fun _ => false) (restrictRows fig8C₁ fig8) ≤ 3 := by
  rw [RS_restrictRows fig8Sites₁ fig8Sites₁_strictMono fig8Sites₁_range, ← fig8CompSingleNet_recombs]
  exact NetSpec.RS_le fig8CompSingleNet_valid (by decide +kernel) (NetSpec.obeys_single_toNetwork _ fig8CompSingleNet_single) (by decide +kernel)

/-- `R¹_{00000}(M(C₂)) ≤ 3`, for `F¹`. -/
theorem fig8_RS_single₂ : RS .single (fig8C₂.domRestrict fun _ => false) (restrictRows fig8C₂ fig8) ≤ 3 := by
  rw [RS_restrictRows fig8Sites₂ fig8Sites₂_strictMono fig8Sites₂_range, ← fig8CompSingleNet_recombs]
  exact NetSpec.RS_le fig8CompSingleNet_valid (by decide +kernel) (NetSpec.obeys_single_toNetwork _ fig8CompSingleNet_single) (by decide +kernel)

/-! ### The whole matrix -/

/-- Figure 9, as lists: the nodes `x`, `y`, `z` of the paper are the vertices `12`, `13`, `14`. -/
def figure9Spec : NetSpec 10 28 30 :=
  ⟨[0, 1, 2, 3, 2, 5, 1, 7, 8, 7, 10, 4, 9, 6, 12, 11, 12, 0, 2, 3, 4, 5, 6, 13, 7, 8, 9, 10, 11, 14],
   [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 12, 13, 13, 14, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27],
   [2, 1, 3, 4, 5, 7, 6, 8, 9, 10],
   [0, 0, 2, 3, 7, 10, 26, 64, 96, 224, 320, 832, 165, 29, 928, 0, 2, 3, 7, 10, 26, 29, 64, 96, 224, 320, 832, 928]⟩

theorem figure9Spec_valid : figure9Spec.Valid := by decide +kernel

theorem figure9Spec_derives : figure9Spec.DerivesCheck fig8 := by decide +kernel

theorem figure9Spec_recombs : figure9Spec.recombs = 3 := by decide +kernel

theorem figure9Spec_root : figure9Spec.label 0 = fun _ => false := by decide +kernel

/-- The number of changes of parent along the sites. -/
def parentChanges {m : ℕ} (o : Fin m → Bool) : ℕ :=
  ((List.range m).filter fun i => if h : i + 1 < m then o ⟨i, by omega⟩ != o ⟨i + 1, h⟩ else false).length

/-- `q` is a recombinant of `p`, `p'` with `k` crossovers. -/
def HasCrossovers {m : ℕ} (k : ℕ) (p p' q : Fin m → Bool) : Prop :=
  ∃ o : Fin m → Bool, (∀ i, q i = if o i then p i else p' i) ∧ parentChanges o = k

/-- A statement about all the sequences is one about their codes. -/
theorem forall_of_codes {m : ℕ} {P : (Fin m → Bool) → Prop} (h : ∀ x ∈ List.range (2 ^ m), P (LabelSearch.dec x)) (o : Fin m → Bool) : P o := by
  have := h (LabelSearch.code o) (List.mem_range.2 (LabelSearch.code_lt o))
  rwa [LabelSearch.dec_code] at this

/-- The least number of crossovers of a recombinant of `p`, `p'`, for the figure: `k` crossovers are enough, and fewer aren't. -/
theorem hasCrossovers_of_codes {m k : ℕ} {p p' q : Fin m → Bool} (x : ℕ)
    (h₁ : (∀ i, q i = if (LabelSearch.dec x : Fin m → Bool) i then p i else p' i) ∧ parentChanges (LabelSearch.dec x : Fin m → Bool) = k)
    (h₂ : ∀ y ∈ List.range (2 ^ m), (∀ i, q i = if (LabelSearch.dec y : Fin m → Bool) i then p i else p' i) → k ≤ parentChanges (LabelSearch.dec y : Fin m → Bool)) :
    HasCrossovers k p p' q ∧ ∀ j < k, ¬ HasCrossovers j p p' q := by
  refine ⟨⟨_, h₁⟩, ?_⟩
  rintro j hj ⟨o, ho, rfl⟩
  have := forall_of_codes (P := fun o => (∀ i, q i = if o i then p i else p' i) → k ≤ parentChanges o) h₂ o ho
  omega

/-- The caption of Figure 9: "the recombination event at node `y` uses only a single-crossover, while multiple-crossovers are used at nodes `x` and `z`". The counts are 5, 1, 2; the paper doesn't state them. -/
theorem figure9_crossovers :
    (HasCrossovers 5 (figure9Spec.label 4) (figure9Spec.label 9) (figure9Spec.label 12) ∧ ∀ j < 5, ¬ HasCrossovers j (figure9Spec.label 4) (figure9Spec.label 9) (figure9Spec.label 12)) ∧
    (HasCrossovers 1 (figure9Spec.label 6) (figure9Spec.label 12) (figure9Spec.label 13) ∧ ∀ j < 1, ¬ HasCrossovers j (figure9Spec.label 6) (figure9Spec.label 12) (figure9Spec.label 13)) ∧
    (HasCrossovers 2 (figure9Spec.label 11) (figure9Spec.label 12) (figure9Spec.label 14) ∧ ∀ j < 2, ¬ HasCrossovers j (figure9Spec.label 11) (figure9Spec.label 12) (figure9Spec.label 14)) :=
  ⟨hasCrossovers_of_codes 69 (by decide +kernel) (by decide +kernel), hasCrossovers_of_codes 1016 (by decide +kernel) (by decide +kernel),
    hasCrossovers_of_codes 775 (by decide +kernel) (by decide +kernel)⟩

/-- The codes of the rows of Figure 8. -/
def fig8Codes : List ℕ := [0, 2, 3, 7, 10, 26, 29, 64, 96, 224, 320, 832, 928]

theorem fig8Codes_codesOf : CodesOf fig8 fig8Codes := by decide +kernel

theorem fig8_check : LabelSearch.check 10 fig8Codes 2 = false := by decide +kernel

/-- `R(M) = 3`. The paper needs `≤` only (line 612). -/
theorem fig8_R_multiple : R .multiple fig8 = 3 :=
  R_eq_of_spec (s := figure9Spec) (k := 2) figure9Spec_valid figure9Spec_derives trivial figure9Spec_recombs fig8Codes_codesOf fig8_check

/-- A network for the matrix of Figure 8 with six single crossovers: the two components on their own. -/
def fig8SingleNet : NetSpec 10 30 35 :=
  ⟨[0, 0, 1, 2, 4, 1, 2, 3, 6, 3, 5, 0, 0, 9, 10, 12, 9, 10, 11, 14, 11, 13, 0, 2, 6, 7, 4, 5, 8, 10, 14, 15, 12, 13, 16],
   [1, 2, 3, 4, 5, 6, 6, 7, 7, 8, 8, 9, 10, 11, 12, 13, 14, 14, 15, 15, 16, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29],
   [0, 1, 2, 3, 4, 11, 12, 13, 14, 15],
   [0, 1, 2, 5, 10, 26, 3, 7, 29, 32, 64, 160, 320, 832, 96, 224, 928, 0, 2, 3, 7, 10, 26, 29, 64, 96, 224, 320, 832, 928]⟩

theorem fig8SingleNet_valid : fig8SingleNet.Valid := by decide +kernel

theorem fig8SingleNet_derives : fig8SingleNet.DerivesCheck fig8 := by decide +kernel

theorem fig8SingleNet_single : fig8SingleNet.SingleCheck := by decide +kernel

theorem fig8SingleNet_recombs : fig8SingleNet.recombs = 6 := by decide +kernel

theorem fig8Inc : ∀ p ∈ ({(0, 1), (1, 2), (2, 3), (5, 6), (6, 7), (7, 8)} : Finset (Fin 10 × Fin 10)), p.1 < p.2 ∧ Incompatible fig8 p.1 p.2 := by
  unfold Incompatible
  decide +kernel

/-- `R¹(M) = 6`, for the matrix of Figure 8. The paper doesn't state this number. The Hudson-Kaplan bound is tight on it: the components are spatially disjoint. -/
theorem fig8_R_single : R .single fig8 = 6 := by
  have h₁ := NetSpec.R_le fig8SingleNet_valid fig8SingleNet_derives (NetSpec.obeys_single_toNetwork _ fig8SingleNet_single)
  rw [fig8SingleNet_recombs] at h₁
  have h₂ := HudsonKaplan1985.card_le_R fig8 ({(0, 1), (1, 2), (2, 3), (5, 6), (6, 7), (7, 8)} : Finset (Fin 10 × Fin 10)) fig8Inc (by decide +kernel)
  have hcard : (({(0, 1), (1, 2), (2, 3), (5, 6), (6, 7), (7, 8)} : Finset (Fin 10 × Fin 10))).card = 6 := by decide
  omega

end Gusfield2007
