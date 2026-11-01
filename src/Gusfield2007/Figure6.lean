module

public import Gusfield2007.Components
public import External.HudsonKaplan1985.Bound

/-!
# Gusfield et al. 2007, Figures 6 and 7: the numbers

- Line 594: `R¹(M(C_k)) = 2`, the lower bound by the Hudson-Kaplan bound, and Figure 7, a network with three recombination nodes.
- `R¹(M) = 3`, which the paper doesn't state: it needs `R¹(M) ≤ 3` only. By the composite bound `Gen.split`: a single crossover breaks the sites `1, 2, 3, 4` or the sites `4, 5, 6`, and not both. The first set needs two
  recombinations, by the search, and the second one needs one.
- `R(M(C_k)) = 1` and `R(M) = 2`, which the paper doesn't state either.
-/

@[expose] public section

open scoped Classical

namespace Gusfield2007

/-- The sites of `C₁`: `2, 3, 5` of the paper. -/
def fig6Sites₁ : Fin 3 → Fin 6 := fun a => Fin.ofNat 6 ([1, 2, 4].getD a 0)

/-- The sites of `C₂`: `1, 4, 6` of the paper. -/
def fig6Sites₂ : Fin 3 → Fin 6 := fun a => Fin.ofNat 6 ([0, 3, 5].getD a 0)

theorem fig6Sites₁_strictMono : StrictMono fig6Sites₁ := fun a b h => by
  revert a b
  decide

theorem fig6Sites₂_strictMono : StrictMono fig6Sites₂ := fun a b h => by
  revert a b
  decide

theorem fig6Sites₁_range : Set.range fig6Sites₁ = fig6C₁ := Set.ext fun i => by
  change (∃ a, fig6Sites₁ a = i) ↔ (i = 1 ∨ i = 2 ∨ i = 4)
  revert i
  decide

theorem fig6Sites₂_range : Set.range fig6Sites₂ = fig6C₂ := Set.ext fun i => by
  change (∃ a, fig6Sites₂ a = i) ↔ (i = 0 ∨ i = 3 ∨ i = 5)
  revert i
  decide

/-- A network for `M(C₁)`, `M(C₂)`, which are the same matrix, with root `000` and two single crossovers. -/
def fig6CompSingleNet : NetSpec 3 10 11 :=
  ⟨[0, 0, 1, 1, 2, 3, 4, 2, 5, 3, 0],
   [1, 2, 3, 4, 4, 5, 5, 6, 7, 8, 9],
   [0, 1, 2],
   [0, 1, 2, 5, 3, 7, 2, 7, 5, 0]⟩

theorem fig6CompSingleNet_valid : fig6CompSingleNet.Valid := by decide +kernel

theorem fig6CompSingleNet_single : fig6CompSingleNet.SingleCheck := by decide +kernel

theorem fig6CompSingleNet_recombs : fig6CompSingleNet.recombs = 2 := by decide +kernel

/-- A network for `M(C₁)`, `M(C₂)`, with root `000` and one recombination node. -/
def fig6CompMultipleNet : NetSpec 3 9 9 :=
  ⟨[0, 0, 1, 2, 3, 2, 4, 3, 0],
   [1, 2, 3, 4, 4, 5, 6, 7, 8],
   [0, 1, 2],
   [0, 1, 2, 5, 7, 2, 7, 5, 0]⟩

theorem fig6CompMultipleNet_valid : fig6CompMultipleNet.Valid := by decide +kernel

theorem fig6CompMultipleNet_recombs : fig6CompMultipleNet.recombs = 1 := by decide +kernel

/-- The codes of the rows of `M(C₁)`, `M(C₂)`. -/
def fig6CompCodes : List ℕ := [2, 7, 5, 0]

theorem fig6Comp_check : LabelSearch.check 3 fig6CompCodes 0 = false := by decide +kernel

/-- **Line 594**: the Hudson-Kaplan bound on the matrix `M(C_k)`, whose first and second, and second and third, sites are incompatible. -/
theorem fig6Comp_two_le {f : Fin 3 → Fin 6}
    (hinc : Incompatible (fig6.image fun r => r ∘ f) 0 1 ∧ Incompatible (fig6.image fun r => r ∘ f) 1 2) :
    2 ≤ R .single (fig6.image fun r => r ∘ f) := by
  have hcard : (({(0, 1), (1, 2)} : Finset (Fin 3 × Fin 3))).card = 2 := by decide
  rw [← hcard]
  refine HudsonKaplan1985.card_le_R _ _ (fun p hp => ?_) (fun p hp q hq hne => ?_)
  · rcases Finset.mem_insert.1 hp with rfl | hp
    · exact ⟨by decide, hinc.1⟩
    · rw [Finset.mem_singleton.1 hp]
      exact ⟨by decide, hinc.2⟩
  · revert hne
    revert q p
    decide

theorem fig6Inc₁ : Incompatible (fig6.image fun r => r ∘ fig6Sites₁) 0 1 ∧ Incompatible (fig6.image fun r => r ∘ fig6Sites₁) 1 2 := by
  unfold Incompatible
  decide +kernel

theorem fig6Inc₂ : Incompatible (fig6.image fun r => r ∘ fig6Sites₂) 0 1 ∧ Incompatible (fig6.image fun r => r ∘ fig6Sites₂) 1 2 := by
  unfold Incompatible
  decide +kernel

/-- `R¹(M(C₁)) = 2`: "In fact, `R¹(M(C₁)) = R¹(M(C₂)) = 2`" (line 594). -/
theorem fig6_R_single₁ : R .single (restrictRows fig6C₁ fig6) = 2 := by
  rw [R_restrictRows fig6Sites₁ fig6Sites₁_strictMono fig6Sites₁_range]
  have h₁ := NetSpec.R_le (M := fig6.image fun r => r ∘ fig6Sites₁) fig6CompSingleNet_valid (by decide +kernel)
    (NetSpec.obeys_single_toNetwork _ fig6CompSingleNet_single)
  rw [fig6CompSingleNet_recombs] at h₁
  have h₂ := fig6Comp_two_le fig6Inc₁
  omega

/-- `R¹(M(C₂)) = 2`: "In fact, `R¹(M(C₁)) = R¹(M(C₂)) = 2`" (line 594). -/
theorem fig6_R_single₂ : R .single (restrictRows fig6C₂ fig6) = 2 := by
  rw [R_restrictRows fig6Sites₂ fig6Sites₂_strictMono fig6Sites₂_range]
  have h₁ := NetSpec.R_le (M := fig6.image fun r => r ∘ fig6Sites₂) fig6CompSingleNet_valid (by decide +kernel)
    (NetSpec.obeys_single_toNetwork _ fig6CompSingleNet_single)
  rw [fig6CompSingleNet_recombs] at h₁
  have h₂ := fig6Comp_two_le fig6Inc₂
  omega

/-- `R(M(C₁)) = 1`. Not in the paper. -/
theorem fig6_R_multiple₁ : R .multiple (restrictRows fig6C₁ fig6) = 1 := by
  rw [R_restrictRows fig6Sites₁ fig6Sites₁_strictMono fig6Sites₁_range]
  exact R_eq_of_spec (s := fig6CompMultipleNet) (k := 0) fig6CompMultipleNet_valid (by decide +kernel) trivial fig6CompMultipleNet_recombs (Mc := fig6CompCodes) (by decide +kernel) fig6Comp_check

/-- `R(M(C₂)) = 1`. Not in the paper. -/
theorem fig6_R_multiple₂ : R .multiple (restrictRows fig6C₂ fig6) = 1 := by
  rw [R_restrictRows fig6Sites₂ fig6Sites₂_strictMono fig6Sites₂_range]
  exact R_eq_of_spec (s := fig6CompMultipleNet) (k := 0) fig6CompMultipleNet_valid (by decide +kernel) trivial fig6CompMultipleNet_recombs (Mc := fig6CompCodes) (by decide +kernel) fig6Comp_check

/-- `R¹_{000}(M(C₁)) ≤ 2`, for `F¹`. -/
theorem fig6_RS_single₁ : RS .single (fig6C₁.domRestrict fun _ => false) (restrictRows fig6C₁ fig6) ≤ 2 := by
  rw [RS_restrictRows fig6Sites₁ fig6Sites₁_strictMono fig6Sites₁_range, ← fig6CompSingleNet_recombs]
  exact NetSpec.RS_le fig6CompSingleNet_valid (by decide +kernel) (NetSpec.obeys_single_toNetwork _ fig6CompSingleNet_single) (by decide +kernel)

/-- `R¹_{000}(M(C₂)) ≤ 2`, for `F¹`. -/
theorem fig6_RS_single₂ : RS .single (fig6C₂.domRestrict fun _ => false) (restrictRows fig6C₂ fig6) ≤ 2 := by
  rw [RS_restrictRows fig6Sites₂ fig6Sites₂_strictMono fig6Sites₂_range, ← fig6CompSingleNet_recombs]
  exact NetSpec.RS_le fig6CompSingleNet_valid (by decide +kernel) (NetSpec.obeys_single_toNetwork _ fig6CompSingleNet_single) (by decide +kernel)

/-- `R_{000}(M(C₁)) ≤ 1`, for `F`. -/
theorem fig6_RS_multiple₁ : RS .multiple (fig6C₁.domRestrict fun _ => false) (restrictRows fig6C₁ fig6) ≤ 1 := by
  rw [RS_restrictRows fig6Sites₁ fig6Sites₁_strictMono fig6Sites₁_range, ← fig6CompMultipleNet_recombs]
  exact NetSpec.RS_le (c := .multiple) fig6CompMultipleNet_valid (by decide +kernel) trivial (by decide +kernel)

/-- `R_{000}(M(C₂)) ≤ 1`, for `F`. -/
theorem fig6_RS_multiple₂ : RS .multiple (fig6C₂.domRestrict fun _ => false) (restrictRows fig6C₂ fig6) ≤ 1 := by
  rw [RS_restrictRows fig6Sites₂ fig6Sites₂_strictMono fig6Sites₂_range, ← fig6CompMultipleNet_recombs]
  exact NetSpec.RS_le (c := .multiple) fig6CompMultipleNet_valid (by decide +kernel) trivial (by decide +kernel)

/-! ### The whole matrix -/

/-- Figure 7, as lists: the network of the paper, with the sequence `100010` at the first recombination node (line 608). -/
def figure7Spec : NetSpec 6 16 18 :=
  ⟨[0, 0, 1, 2, 4, 3, 3, 4, 6, 5, 5, 7, 1, 6, 8, 2, 7, 9],
   [1, 2, 3, 4, 5, 5, 6, 7, 8, 8, 9, 9, 10, 11, 12, 13, 14, 15],
   [3, 6, 0, 1, 2, 7],
   [0, 4, 8, 20, 9, 17, 22, 41, 18, 33, 4, 22, 18, 8, 41, 33]⟩

theorem figure7Spec_valid : figure7Spec.Valid := by decide +kernel

theorem figure7Spec_derives : figure7Spec.DerivesCheck fig6 := by decide +kernel

theorem figure7Spec_single : figure7Spec.SingleCheck := by decide +kernel

theorem figure7Spec_recombs : figure7Spec.recombs = 3 := by decide +kernel

theorem figure7Spec_root : figure7Spec.label 0 = fun _ => false := by decide +kernel

/-- A network for Figure 6 with two recombination nodes. It isn't in the paper. -/
def fig6MultipleNet : NetSpec 6 15 16 :=
  ⟨[0, 0, 1, 2, 3, 5, 0, 6, 3, 4, 0, 4, 8, 7, 6, 5],
   [1, 2, 3, 4, 5, 6, 7, 7, 8, 8, 9, 10, 11, 12, 13, 14],
   [0, 1, 2, 5, 3, 4],
   [4, 5, 6, 1, 22, 33, 41, 8, 18, 4, 22, 18, 8, 41, 33]⟩

theorem fig6MultipleNet_valid : fig6MultipleNet.Valid := by decide +kernel

theorem fig6MultipleNet_derives : fig6MultipleNet.DerivesCheck fig6 := by decide +kernel

theorem fig6MultipleNet_recombs : fig6MultipleNet.recombs = 2 := by decide +kernel

/-- The sites `1, 2, 3, 4` of the paper. -/
def fig6Left : Fin 4 → Fin 6 := Fin.castLE (by decide)

/-- The sites `4, 5, 6` of the paper. -/
def fig6Right : Fin 3 → Fin 6 := Fin.natAdd 3

theorem fig6Left_strictMono : StrictMono fig6Left := fun a b h => by
  revert a b
  decide

theorem fig6Right_strictMono : StrictMono fig6Right := fun a b h => by
  revert a b
  decide

theorem fig6Left_le_right (a : Fin 4) (b : Fin 3) : fig6Left a ≤ fig6Right b := by
  revert a b
  decide

/-- The codes of the rows on the sites `1, 2, 3, 4`. -/
def fig6LeftCodes : List ℕ := [4, 6, 2, 8, 9, 1]

/-- The codes of the rows on the sites `4, 5, 6`. -/
def fig6RightCodes : List ℕ := [0, 2, 1, 5, 4]

theorem fig6LeftCodes_codesOf : CodesOf (fig6.image fun r => r ∘ fig6Left) fig6LeftCodes := by decide +kernel

theorem fig6RightCodes_codesOf : CodesOf (fig6.image fun r => r ∘ fig6Right) fig6RightCodes := by decide +kernel

theorem fig6Left_check : LabelSearch.check 4 fig6LeftCodes 1 = false := by decide +kernel

theorem fig6Right_check : LabelSearch.check 3 fig6RightCodes 0 = false := by decide +kernel

/-- `Finset.image_subset_image` with two instances. -/
theorem image_subset_image_of_inst {α β : Type*} (i₁ i₂ : DecidableEq β) (f : α → β) {M A : Finset α} (h : M ⊆ A) :
    @Finset.image _ _ i₁ f M ⊆ @Finset.image _ _ i₂ f A := by
  intro r hr
  obtain ⟨x, hx, rfl⟩ := (@Finset.mem_image _ _ i₁ _ _ _).1 hr
  exact (@Finset.mem_image _ _ i₂ _ _ _).2 ⟨x, h hx, rfl⟩

/-- The labels of a network deriving `M` contain `M`. -/
theorem rows_subset_of_derives {ι V E : Type*} {N : Network ι V E} {M A : Finset (ι → Bool)} (hd : N.Derives M) (hlab : ∀ v, N.label v ∈ A) : M ⊆ A := fun r hr => by
  obtain ⟨v, -, rfl⟩ := hd.surjOn hr
  exact hlab v

/-- A network with the rows of Figure 6 among its labels, in the single-crossover model, has at least three recombination nodes: the composite bound. -/
theorem fig6_three_le_of_labels {a b : ℕ} (N : Network (Fin 6) (Fin a) (Fin b)) (hc : N.Obeys .single) (hl : ∀ r ∈ fig6, ∃ v, N.label v = r) :
    3 ≤ N.recombCount := by
  obtain ⟨A, U, hg, hlab⟩ := N.exists_gen hc
  obtain ⟨r₁, r₂, hle, h₁, h₂⟩ := hg.split fig6Left_strictMono fig6Right_strictMono fig6Left_le_right
  have hsub : fig6 ⊆ A := fun r hr => by
    obtain ⟨v, rfl⟩ := hl r hr
    exact hlab v
  have hl := h₁.lt_of_check (M := fig6.image fun r => r ∘ fig6Left) (image_subset_image_of_inst _ _ _ hsub) fig6LeftCodes_codesOf fig6Left_check
  have hr := h₂.lt_of_check (M := fig6.image fun r => r ∘ fig6Right) (image_subset_image_of_inst _ _ _ hsub) fig6RightCodes_codesOf fig6Right_check
  omega

/-- A network for Figure 6 in the single-crossover model has at least three recombination nodes. -/
theorem fig6_three_le_recombCount {a b : ℕ} (N : Network (Fin 6) (Fin a) (Fin b)) (hc : N.Obeys .single) (hd : N.Derives fig6) :
    3 ≤ N.recombCount :=
  fig6_three_le_of_labels N hc fun r hr => by
    obtain ⟨v, -, hv⟩ := hd.surjOn hr
    exact ⟨v, hv⟩

/-- A network for Figure 6 has at least two recombination nodes, in any model. -/
theorem fig6_two_le_recombCount {a b : ℕ} {c : Crossover} (N : Network (Fin 6) (Fin a) (Fin b)) (hc : N.Obeys c) (hd : N.Derives fig6) :
    2 ≤ N.recombCount := by
  obtain ⟨A, U, hg, hlab⟩ := N.exists_gen hc
  obtain ⟨r', hle, h₁⟩ := hg.toMultiple.restrict fig6Left_strictMono.injective
  have hsub := rows_subset_of_derives hd hlab
  have hl := h₁.lt_of_check (M := fig6.image fun r => r ∘ fig6Left) (image_subset_image_of_inst _ _ _ hsub) fig6LeftCodes_codesOf fig6Left_check
  omega

/-- `R¹(M) = 3`. The paper needs `≤` only (line 594). -/
theorem fig6_R_single : R .single fig6 = 3 := by
  have h₁ := NetSpec.R_le figure7Spec_valid figure7Spec_derives (NetSpec.obeys_single_toNetwork _ figure7Spec_single)
  rw [figure7Spec_recombs] at h₁
  have hne : {k | ∃ (a b : ℕ) (N : Network (Fin 6) (Fin a) (Fin b)), N.Obeys .single ∧ N.Derives fig6 ∧ N.recombCount = k}.Nonempty :=
    ⟨_, _, _, NetSpec.toNetwork figure7Spec_valid, NetSpec.obeys_single_toNetwork _ figure7Spec_single, NetSpec.derives_toNetwork _ figure7Spec_derives, rfl⟩
  obtain ⟨a, b, N, h₂, h₃, h₄⟩ := Nat.sInf_mem hne
  have := fig6_three_le_recombCount N h₂ h₃
  rw [h₄] at this
  exact le_antisymm h₁ this

/-- `R(M) = 2`. Not in the paper. -/
theorem fig6_R_multiple : R .multiple fig6 = 2 := by
  have h₁ := NetSpec.R_le (c := .multiple) fig6MultipleNet_valid fig6MultipleNet_derives trivial
  rw [fig6MultipleNet_recombs] at h₁
  have hne : {k | ∃ (a b : ℕ) (N : Network (Fin 6) (Fin a) (Fin b)), N.Obeys .multiple ∧ N.Derives fig6 ∧ N.recombCount = k}.Nonempty :=
    ⟨_, _, _, NetSpec.toNetwork fig6MultipleNet_valid, trivial, NetSpec.derives_toNetwork _ fig6MultipleNet_derives, rfl⟩
  obtain ⟨a, b, N, h₂, h₃, h₄⟩ := Nat.sInf_mem hne
  have := fig6_two_le_recombCount N h₂ h₃
  rw [h₄] at this
  exact le_antisymm h₁ this

/-! ### Figure 7 with another root -/

/-- Figure 7's topology with the root relabelled `001100`: the arcs out of the root have the sites `4` and `3`, in place of `3` and `4`. -/
def figure7RerootedSpec : NetSpec 6 16 18 :=
  ⟨[0, 0, 1, 2, 4, 3, 3, 4, 6, 5, 5, 7, 1, 6, 8, 2, 7, 9],
   [1, 2, 3, 4, 5, 5, 6, 7, 8, 8, 9, 9, 10, 11, 12, 13, 14, 15],
   [3, 6, 1, 0, 2, 7],
   [12, 4, 8, 20, 9, 17, 22, 41, 18, 33, 4, 22, 18, 8, 41, 33]⟩

theorem figure7RerootedSpec_valid : figure7RerootedSpec.Valid := by decide +kernel

theorem figure7RerootedSpec_derives : figure7RerootedSpec.DerivesCheck fig6 := by decide +kernel

theorem figure7RerootedSpec_single : figure7RerootedSpec.SingleCheck := by decide +kernel

theorem figure7RerootedSpec_recombs : figure7RerootedSpec.recombs = 3 := by decide +kernel

/-- The sequence `001100`. -/
def fig6Root : Fin 6 → Bool := ofBits [0, 0, 1, 1, 0, 0]

theorem figure7RerootedSpec_root : figure7RerootedSpec.label 0 = fig6Root := by decide +kernel

/-- `R¹_S(M) = 3` for `S = 001100`. -/
theorem fig6_RS_rerooted : RS .single fig6Root fig6 = 3 := by
  have h₁ := NetSpec.RS_le figure7RerootedSpec_valid figure7RerootedSpec_derives (NetSpec.obeys_single_toNetwork _ figure7RerootedSpec_single) figure7RerootedSpec_root
  rw [figure7RerootedSpec_recombs] at h₁
  have hne : {k | ∃ (a b : ℕ) (N : Network (Fin 6) (Fin a) (Fin b)), N.Obeys .single ∧ N.Derives fig6 ∧ N.ancestral = fig6Root ∧ N.recombCount = k}.Nonempty :=
    ⟨_, _, _, NetSpec.toNetwork figure7RerootedSpec_valid, NetSpec.obeys_single_toNetwork _ figure7RerootedSpec_single, NetSpec.derives_toNetwork _ figure7RerootedSpec_derives, figure7RerootedSpec_root, rfl⟩
  obtain ⟨a, b, N, h₂, h₃, -, h₅⟩ := Nat.sInf_mem hne
  have := fig6_three_le_recombCount N h₂ h₃
  rw [h₅] at this
  exact le_antisymm h₁ this

/-! ### Line 608 -/

/-- The sequence `100010` that the first recombination of Figure 7 creates (line 608). -/
def fig6Recomb : Fin 6 → Bool := ofBits [1, 0, 0, 0, 1, 0]

/-- "The first recombination creates the sequence `100010`" (line 608): vertex `5` of `figure7Spec`, the vertices being numbered so that arcs go up. -/
theorem figure7Spec_first_recomb : figure7Spec.IsRec 5 ∧ figure7Spec.label 5 = fig6Recomb ∧ ∀ v : Fin 16, v < 5 → ¬ figure7Spec.IsRec v := by
  decide +kernel

/-- `M + S`, with `S = 000000`, computably. -/
def fig6WithRoot : Finset (Fin 6 → Bool) := insert (fun _ => false) fig6

theorem addRow_fig6_eq : addRow fig6 (fun _ => false) = fig6WithRoot := by
  ext r
  rw [mem_addRow, fig6WithRoot, Finset.mem_insert]

/-- Figure 7 with a leaf `000000` at the root: a network for `M + S`. -/
def figure7WithRootSpec : NetSpec 6 17 19 :=
  ⟨[0, 0, 1, 2, 4, 3, 3, 4, 6, 5, 5, 7, 1, 6, 8, 2, 7, 9, 0],
   [1, 2, 3, 4, 5, 5, 6, 7, 8, 8, 9, 9, 10, 11, 12, 13, 14, 15, 16],
   [3, 6, 0, 1, 2, 7],
   [0, 4, 8, 20, 9, 17, 22, 41, 18, 33, 4, 22, 18, 8, 41, 33, 0]⟩

theorem figure7WithRootSpec_valid : figure7WithRootSpec.Valid := by decide +kernel

theorem figure7WithRootSpec_derives : figure7WithRootSpec.DerivesCheck fig6WithRoot := by decide +kernel

theorem figure7WithRootSpec_single : figure7WithRootSpec.SingleCheck := by decide +kernel

theorem figure7WithRootSpec_recombs : figure7WithRootSpec.recombs = 3 := by decide +kernel

/-- `R¹(M + S) = 3`, with `S = 000000`. -/
theorem fig6WithRoot_R : R .single (addRow fig6 fun _ => false) = 3 := by
  rw [addRow_fig6_eq]
  have h₁ := NetSpec.R_le figure7WithRootSpec_valid figure7WithRootSpec_derives (NetSpec.obeys_single_toNetwork _ figure7WithRootSpec_single)
  rw [figure7WithRootSpec_recombs] at h₁
  have hne : {k | ∃ (a b : ℕ) (N : Network (Fin 6) (Fin a) (Fin b)), N.Obeys .single ∧ N.Derives fig6WithRoot ∧ N.recombCount = k}.Nonempty :=
    ⟨_, _, _, NetSpec.toNetwork figure7WithRootSpec_valid, NetSpec.obeys_single_toNetwork _ figure7WithRootSpec_single,
      NetSpec.derives_toNetwork _ figure7WithRootSpec_derives, rfl⟩
  obtain ⟨a, b, N, h₂, h₃, h₄⟩ := Nat.sInf_mem hne
  have h₅ := fig6_three_le_of_labels N h₂ fun r hr => by
    obtain ⟨v, -, hv⟩ := h₃.surjOn (show r ∈ (fig6WithRoot : Set _) from Finset.mem_coe.2 (Finset.mem_insert_of_mem hr))
    exact ⟨v, hv⟩
  rw [h₄] at h₅
  exact le_antisymm h₁ h₅

/-- `R¹_S(M) = 3`, with `S = 000000`. -/
theorem fig6_RS_zero : RS .single (fun _ => false) fig6 = 3 := by
  have h₁ := NetSpec.RS_le figure7Spec_valid figure7Spec_derives (NetSpec.obeys_single_toNetwork _ figure7Spec_single) figure7Spec_root
  rw [figure7Spec_recombs] at h₁
  have hne : {k | ∃ (a b : ℕ) (N : Network (Fin 6) (Fin a) (Fin b)), N.Obeys .single ∧ N.Derives fig6 ∧ N.ancestral = (fun _ => false) ∧ N.recombCount = k}.Nonempty :=
    ⟨_, _, _, NetSpec.toNetwork figure7Spec_valid, NetSpec.obeys_single_toNetwork _ figure7Spec_single, NetSpec.derives_toNetwork _ figure7Spec_derives, figure7Spec_root, rfl⟩
  obtain ⟨a, b, N, h₂, h₃, -, h₅⟩ := Nat.sInf_mem hne
  have := fig6_three_le_recombCount N h₂ h₃
  rw [h₅] at this
  exact le_antisymm h₁ this

/-- `H(M + S) = 7 - 4 - 1 = 2`, with `S = 000000`: the columns of `M + S` are `u, x, y, v, x, u`. -/
theorem fig6_haplotypeBound_addRow : haplotypeBound (addRow fig6 fun _ => false) = 2 := by
  rw [addRow_fig6_eq, haplotypeBound, distinctColumns_eq (M := fig6WithRoot) {0, 1, 2, 3} (by decide +kernel) (by decide +kernel)]
  have hcard : fig6WithRoot.card = 7 := by decide +kernel
  rw [hcard]
  decide

/-- `H(M(C₁)) = 4 - 2 - 1 = 1`. -/
theorem fig6_haplotypeBound₁ : haplotypeBound (restrictRows fig6C₁ fig6) = 1 := by
  have hcols : distinctColumns (restrictRows fig6C₁ fig6) = 2 := by
    refine distinctColumns_restrictRows_eq_two (a := 1) (b := 2) (Or.inl rfl) (Or.inr (Or.inl rfl)) (fun i hi => ?_) (by decide +kernel)
    change i = 1 ∨ i = 2 ∨ i = 4 at hi
    revert hi
    revert i
    decide +kernel
  have hcard : (fig6.image fun r => r ∘ fig6Sites₁).card = 4 := by decide +kernel
  rw [haplotypeBound, hcols, card_restrictRows fig6Sites₁ fig6Sites₁_strictMono fig6Sites₁_range, hcard]
  decide

/-- `H(M(C₂)) = 4 - 2 - 1 = 1`. -/
theorem fig6_haplotypeBound₂ : haplotypeBound (restrictRows fig6C₂ fig6) = 1 := by
  have hcols : distinctColumns (restrictRows fig6C₂ fig6) = 2 := by
    refine distinctColumns_restrictRows_eq_two (a := 0) (b := 3) (Or.inl rfl) (Or.inr (Or.inl rfl)) (fun i hi => ?_) (by decide +kernel)
    change i = 0 ∨ i = 3 ∨ i = 5 at hi
    revert hi
    revert i
    decide +kernel
  have hcard : (fig6.image fun r => r ∘ fig6Sites₂).card = 4 := by decide +kernel
  rw [haplotypeBound, hcols, card_restrictRows fig6Sites₂ fig6Sites₂_strictMono fig6Sites₂_range, hcard]
  decide

/-- `S(C₁) = 000` is a row of `M(C₁)`, the restriction of the row `000100`. -/
theorem fig6_root_mem₁ : (fig6C₁.domRestrict fun _ => false) ∈ restrictRows fig6C₁ fig6 := by
  refine mem_restrictRows.2 ⟨ofBits [0, 0, 0, 1, 0, 0], by decide +kernel, funext fun i => ?_⟩
  obtain ⟨i, hi⟩ := i
  change i = 1 ∨ i = 2 ∨ i = 4 at hi
  rcases hi with rfl | rfl | rfl <;> rfl

/-- `S(C₂) = 000` is a row of `M(C₂)`, the restriction of the row `001000`. -/
theorem fig6_root_mem₂ : (fig6C₂.domRestrict fun _ => false) ∈ restrictRows fig6C₂ fig6 := by
  refine mem_restrictRows.2 ⟨ofBits [0, 0, 1, 0, 0, 0], by decide +kernel, funext fun i => ?_⟩
  obtain ⟨i, hi⟩ := i
  change i = 0 ∨ i = 3 ∨ i = 5 at hi
  rcases hi with rfl | rfl | rfl <;> rfl

end Gusfield2007
