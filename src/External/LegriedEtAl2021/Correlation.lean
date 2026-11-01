module

public import External.LegriedEtAl2021.Model

/-!
# The positive correlation of the ancestral copies of two species

Lemma 1 and Lemma 2 of Legried, Molloy, Warnow and Roch. Take an i.i.d. family of gene copies, indexed by `J`, at a vertex of the species
tree above `A`, `B`, and let `A_j`, `B_j` be the numbers of leaves in `A`, `B` descending from `j`. Then the expectation of
`A_w B_x φ(Σ A) φ(Σ B)` depends only on whether `w = x`, and is larger when `w = x`. This is both lemmas at once: Lemma 1 for
`φ n = 1 / n`, where this expectation is the probability that the copies picked in `A`, `B` descend from `w`, `x`, and Lemma 2 for
`φ n = 1`, where it is `E[A_w B_x]`.

Their proof conditions on the numbers `N_j` of copies at the most recent common ancestor of `A`, `B` descending from `j`, then uses
that the two picks are independent, proportional to `N_j`, and that `Σ N_j N_k ≤ Σ N_j²`. Here this is done one edge at a time in
`step_le`, along the path from the vertex to that ancestor; at the ancestor itself, `exch_V_mul` is the independence.
-/

@[expose] public noncomputable section

open scoped ENNReal Classical

namespace External.LegriedEtAl2021

variable {X : Type}

/-- The number of leaves of a gene tree in a species. -/
def cnt (y : X) (g : Leaves X) : ℕ := Multiset.card (g y)

/-- The weighted number of pairs of leaves in `A`, `B` with ancestral copies `w`, `x`, in a family of gene trees. -/
def pairW (φ : ℕ → ℝ≥0∞) (A B : X) {J : Type} [Fintype J] (g : J → Leaves X) (w x : J) : ℝ≥0∞ :=
  (cnt A (g w) : ℝ≥0∞) * cnt B (g x) * φ (∑ k, cnt A (g k)) * φ (∑ k, cnt B (g k))

/-- The expectation of `A_w B_x φ(Σ A) φ(Σ B)`, in an i.i.d. family indexed by `J` (their `X⁼`, `X^≠`). -/
def U (φ : ℕ → ℝ≥0∞) (T : SpeciesTree X) (A B : X) (J : Type) [Fintype J] (w x : J) : ℝ≥0∞ :=
  expect (iid J (geneLaw T)) fun g => pairW φ A B g w x

/-- The weighted number of leaves in `C` with ancestral copy `y`. -/
def singleW (φ : ℕ → ℝ≥0∞) (C : X) {J : Type} [Fintype J] (g : J → Leaves X) (y : J) : ℝ≥0∞ :=
  (cnt C (g y) : ℝ≥0∞) * φ (∑ k, cnt C (g k))

/-- The expectation of `C_y φ(Σ C)`, in an i.i.d. family indexed by `J`. -/
def V (φ : ℕ → ℝ≥0∞) (T : SpeciesTree X) (C : X) (J : Type) [Fintype J] (y : J) : ℝ≥0∞ :=
  expect (iid J (geneLaw T)) fun g => singleW φ C g y

section Exchangeability

variable {J J' : Type} [Fintype J] [Fintype J']

theorem U_equiv (φ : ℕ → ℝ≥0∞) (T : SpeciesTree X) (A B : X) (e : J ≃ J') (w x : J) :
    U φ T A B J w x = U φ T A B J' (e w) (e x) := by
  unfold U
  rw [expect_iid_equiv e]
  refine congrArg _ (funext fun g => ?_)
  have h : ∀ y : X, ∑ k, cnt y (g (e.symm k)) = ∑ k, cnt y (g k) := fun y =>
    Equiv.sum_comp e.symm fun k => cnt y (g k)
  simp [pairW, h]

theorem V_equiv (φ : ℕ → ℝ≥0∞) (T : SpeciesTree X) (C : X) (e : J ≃ J') (y : J) :
    V φ T C J y = V φ T C J' (e y) := by
  unfold V
  rw [expect_iid_equiv e]
  refine congrArg _ (funext fun g => ?_)
  have h : ∑ k, cnt C (g (e.symm k)) = ∑ k, cnt C (g k) := Equiv.sum_comp e.symm fun k => cnt C (g k)
  simp [singleW, h]

/-- **By symmetry, the copies are alike.** -/
theorem V_eq (φ : ℕ → ℝ≥0∞) (T : SpeciesTree X) (C : X) (y y' : J) : V φ T C J y = V φ T C J y' := by
  have h := V_equiv φ T C (Equiv.swap y y') y
  rwa [Equiv.swap_apply_left] at h

/-- Any two pairs of distinct elements, of sets of the same size, correspond. -/
theorem exists_equiv_pair (hcard : Fintype.card J = Fintype.card J') {w x : J} {w' x' : J'} (hwx : w ≠ x) (hwx' : w' ≠ x') :
    ∃ e : J ≃ J', e w = w' ∧ e x = x' := by
  let e₀ : J ≃ J' := Fintype.equivOfCardEq hcard
  let e₁ : J ≃ J' := e₀.trans (Equiv.swap (e₀ w) w')
  have h₁ : e₁ w = w' := by simp [e₁]
  have hne : e₁ x ≠ w' := fun h => hwx (e₁.injective (h.trans h₁.symm)).symm
  refine ⟨e₁.trans (Equiv.swap (e₁ x) x'), ?_, ?_⟩
  · simp only [Equiv.trans_apply]
    rw [h₁]
    exact Equiv.swap_apply_of_ne_of_ne hne.symm hwx'
  · simp

/-- Any two elements, of sets of the same size, correspond. -/
theorem exists_equiv_one (hcard : Fintype.card J = Fintype.card J') (w : J) (w' : J') :
    ∃ e : J ≃ J', e w = w' := by
  let e₀ : J ≃ J' := Fintype.equivOfCardEq hcard
  exact ⟨e₀.trans (Equiv.swap (e₀ w) w'), by simp⟩

end Exchangeability

section Table

/-- **A table on finite sets, invariant by symmetry, with larger values on the diagonal.** -/
structure Exch (τ : ∀ (J : Type) [Fintype J], J → J → ℝ≥0∞) : Prop where
  /-- Reindexing keeps the values. -/
  equiv : ∀ (J J' : Type) [Fintype J] [Fintype J'] (e : J ≃ J') (w x : J), τ J w x = τ J' (e w) (e x)
  /-- The diagonal dominates. -/
  le : ∀ (J : Type) [Fintype J] (w x : J), τ J w x ≤ τ J w w

variable {τ : ∀ (J : Type) [Fintype J], J → J → ℝ≥0∞}

/-- The value of a table off the diagonal, on a set of size `n`. -/
def offVal (τ : ∀ (J : Type) [Fintype J], J → J → ℝ≥0∞) (n : ℕ) : ℝ≥0∞ :=
  if h : 2 ≤ n then τ (Fin n) ⟨0, by omega⟩ ⟨1, by omega⟩ else 0

/-- The value of a table on the diagonal, on a set of size `n`. -/
def onVal (τ : ∀ (J : Type) [Fintype J], J → J → ℝ≥0∞) (n : ℕ) : ℝ≥0∞ :=
  if h : 1 ≤ n then τ (Fin n) ⟨0, by omega⟩ ⟨0, by omega⟩ else 0

theorem Exch.off_eq (h : Exch τ) {J : Type} [Fintype J] {w x : J} (hwx : w ≠ x) :
    τ J w x = offVal τ (Fintype.card J) := by
  have hc : 2 ≤ Fintype.card J := Fintype.one_lt_card_iff.2 ⟨w, x, hwx⟩
  unfold offVal
  simp only [hc, ↓reduceDIte]
  obtain ⟨e, he₁, he₂⟩ := exists_equiv_pair (J' := Fin (Fintype.card J)) (by simp) hwx
    (w' := ⟨0, by omega⟩) (x' := ⟨1, by omega⟩) (by simp [Fin.ext_iff])
  rw [h.equiv J _ e, he₁, he₂]

theorem Exch.on_eq (h : Exch τ) {J : Type} [Fintype J] (w : J) : τ J w w = onVal τ (Fintype.card J) := by
  have hc : 1 ≤ Fintype.card J := Fintype.card_pos_iff.2 ⟨w⟩
  unfold onVal
  simp only [hc, ↓reduceDIte]
  obtain ⟨e, he₁⟩ := exists_equiv_one (J' := Fin (Fintype.card J)) (by simp) w (w' := ⟨0, by omega⟩)
  rw [h.equiv J _ e, he₁]

theorem Exch.off_le_on (h : Exch τ) (n : ℕ) : offVal τ n ≤ onVal τ n := by
  unfold offVal onVal
  by_cases hn : 2 ≤ n
  · have hn' : 1 ≤ n := by omega
    simp only [hn, hn', ↓reduceDIte]
    exact h.le _ _ _
  · simp only [hn, ↓reduceDIte]
    exact zero_le

/-- **The table has one value on the diagonal, and another off it.** -/
theorem Exch.eq_ite (h : Exch τ) {J : Type} [Fintype J] (w x : J) :
    τ J w x = if w = x then onVal τ (Fintype.card J) else offVal τ (Fintype.card J) := by
  by_cases hwx : w = x
  · subst hwx
    simp only [↓reduceIte]
    exact h.on_eq w
  · rw [ite_eq_right_iff.2 fun h' => absurd h' hwx, h.off_eq hwx]

/-- The number of copies at the bottom of an edge. -/
theorem card_slots {J : Type} [Fintype J] (s : J → Shape) :
    Fintype.card (Slots s) = ∑ j, (s j).copies.card := by
  rw [Fintype.card_sigma]
  simp

/-- **The step of Lemmas 1 and 2 along an edge**: with `N_j` copies at the bottom descending from the copy `j`, a table on the bottom
gives, in expectation, `E[N_w N_x τ₁] ≤ E[N_w² τ₁]`, where `τ₁` is the value off the diagonal, by Cauchy-Schwarz and
`E[N_w² τ₁] = E[N_x² τ₁]`. -/
theorem step_le (h : Exch τ) (K : PMF Shape) {J : Type} [Fintype J] (w x : J) :
    expect (iid J K) (fun s => ∑ k : (s w).copies, ∑ ℓ : (s x).copies, τ (Slots s) ⟨w, k⟩ ⟨x, ℓ⟩) ≤
      expect (iid J K) fun s => ∑ k : (s w).copies, ∑ ℓ : (s w).copies, τ (Slots s) ⟨w, k⟩ ⟨w, ℓ⟩ := by
  by_cases hwx : w = x
  · subst hwx
    exact le_rfl
  let N : (J → Shape) → J → ℝ≥0∞ := fun s j => ((s j).copies.card : ℝ≥0∞)
  let g : (J → Shape) → ℝ≥0∞ := fun s => offVal τ (Fintype.card (Slots s))
  have hL : ∀ s : J → Shape, ∑ k : (s w).copies, ∑ ℓ : (s x).copies, τ (Slots s) ⟨w, k⟩ ⟨x, ℓ⟩ = N s w * N s x * g s := by
    intro s
    have : ∀ (k : (s w).copies) (ℓ : (s x).copies), τ (Slots s) ⟨w, k⟩ ⟨x, ℓ⟩ = g s := fun k ℓ =>
      h.off_eq fun he => hwx (congrArg Sigma.fst he)
    simp [this, N, mul_assoc]
  have hR : ∀ s : J → Shape, N s w * N s w * g s ≤ ∑ k : (s w).copies, ∑ ℓ : (s w).copies, τ (Slots s) ⟨w, k⟩ ⟨w, ℓ⟩ := by
    intro s
    have hle : ∀ (k ℓ : (s w).copies), g s ≤ τ (Slots s) ⟨w, k⟩ ⟨w, ℓ⟩ := by
      intro k ℓ
      rw [h.eq_ite]
      split_ifs
      · exact h.off_le_on _
      · exact le_rfl
    calc N s w * N s w * g s = ∑ _k : (s w).copies, ∑ _ℓ : (s w).copies, g s := by simp [N, mul_assoc]
      _ ≤ _ := Finset.sum_le_sum fun k _ => Finset.sum_le_sum fun ℓ _ => hle k ℓ
  have hsym : expect (iid J K) (fun s => N s x * N s x * g s) = expect (iid J K) fun s => N s w * N s w * g s := by
    rw [expect_iid_equiv (Equiv.swap w x) K (fun s => N s w * N s w * g s)]
    refine congrArg _ (funext fun s => ?_)
    have hg : g (s ∘ (Equiv.swap w x)) = g s := by
      simp only [g, card_slots]
      congr 1
      exact Equiv.sum_comp (Equiv.swap w x) fun j => (s j).copies.card
    simp [N, hg]
  have hkey : ∀ s : J → Shape, 2 * (N s w * N s x * g s) ≤ N s w * N s w * g s + N s x * N s x * g s := by
    intro s
    have hn : 2 * (((s w).copies.card : ℝ≥0∞) * (s x).copies.card) ≤
        ((s w).copies.card : ℝ≥0∞) * (s w).copies.card + ((s x).copies.card : ℝ≥0∞) * (s x).copies.card := by
      have h' : 2 * ((s w).copies.card * (s x).copies.card) ≤
          (s w).copies.card * (s w).copies.card + (s x).copies.card * (s x).copies.card := by
        nlinarith [sq_nonneg ((s w).copies.card - (s x).copies.card : ℤ), Nat.zero_le (s w).copies.card,
          (by
            have := two_mul_le_add_sq ((s w).copies.card : ℤ) ((s x).copies.card : ℤ)
            nlinarith : (2 * ((s w).copies.card * (s x).copies.card : ℤ) ≤
              (s w).copies.card * (s w).copies.card + (s x).copies.card * (s x).copies.card))]
      exact_mod_cast h'
    calc 2 * (N s w * N s x * g s) = (2 * (N s w * N s x)) * g s := by ring
      _ ≤ (N s w * N s w + N s x * N s x) * g s := by gcongr
      _ = _ := by ring
  have hmain : expect (iid J K) (fun s => N s w * N s x * g s) ≤ expect (iid J K) fun s => N s w * N s w * g s := by
    have h₂ : 2 * expect (iid J K) (fun s => N s w * N s x * g s) ≤ 2 * expect (iid J K) fun s => N s w * N s w * g s := by
      rw [← expect_mul_left]
      refine (expect_mono fun s _ => hkey s).trans ?_
      rw [expect_add, hsym, two_mul]
    exact (ENNReal.mul_le_mul_iff_right (by simp) (by simp)).1 h₂
  simp only [hL]
  exact hmain.trans (expect_mono fun s _ => hR s)

end Table

section Node

variable {J : Type} [Fintype J] {K : PMF Shape} {l r : SpeciesTree X}

theorem cnt_glueSide_left {s : Shape} {e : Bool} {h h' : s.copies → Leaves X} {A : X} (hz : ∀ w, h' w A = 0) :
    cnt A (glueSide e s h h') = ∑ w, cnt A (h w) := by
  simp [cnt, glueSide, forestLeaves, hz, Multiset.card_sum]

theorem cnt_glueSide_right {s : Shape} {e : Bool} {h h' : s.copies → Leaves X} {A : X} (hz : ∀ w, h w A = 0) :
    cnt A (glueSide e s h h') = ∑ w, cnt A (h' w) := by
  simp [cnt, glueSide, forestLeaves, hz, Multiset.card_sum]

/-- On gene trees of a family, no leaf in a species elsewhere. -/
theorem zero_of_iid {T : SpeciesTree X} {I : Type} [Fintype I] {h : I → Leaves X} (hh : iid I (geneLaw T) h ≠ 0)
    {y : X} (hy : ¬ T.Has y) (k : I) : h k y = 0 :=
  eq_zero_of_geneLaw_ne_zero T (piLaw_ne_zero hh k) hy

/-- **The recursion, with `A`, `B` on one side of the speciation.** -/
theorem U_node_same (φ : ℕ → ℝ≥0∞) {A B : X} (hT : (SpeciesTree.node K l r).Nodup) {e : Bool} (hA : (child l r e).Has A)
    (hB : (child l r e).Has B) (w x : J) :
    U φ (.node K l r) A B J w x = expect (iid J K) fun s =>
      ∑ k : (s w).copies, ∑ ℓ : (s x).copies, U φ (child l r e) A B (Slots s) ⟨w, k⟩ ⟨x, ℓ⟩ := by
  unfold U
  rw [expect_iid_node K l r e]
  refine congrArg _ (funext fun s => ?_)
  simp only [← expect_sum]
  refine expect_congr fun h _ => ?_
  rw [expect_congr (g := fun _ => ∑ k : (s w).copies, ∑ ℓ : (s x).copies, pairW φ A B h ⟨w, k⟩ ⟨x, ℓ⟩), expect_const]
  intro h' hh'
  have hzA := zero_of_iid hh' (not_has_child_not hT hA)
  have hzB := zero_of_iid hh' (not_has_child_not hT hB)
  have h₁ : ∀ j, cnt A (glueSide e (s j) (fun w => h ⟨j, w⟩) (fun w => h' ⟨j, w⟩)) = ∑ w : (s j).copies, cnt A (h ⟨j, w⟩) :=
    fun j => cnt_glueSide_left fun w => hzA _
  have h₂ : ∀ j, cnt B (glueSide e (s j) (fun w => h ⟨j, w⟩) (fun w => h' ⟨j, w⟩)) = ∑ w : (s j).copies, cnt B (h ⟨j, w⟩) :=
    fun j => cnt_glueSide_left fun w => hzB _
  have h₃ : ∀ y : X, ∑ j, ∑ w : (s j).copies, cnt y (h ⟨j, w⟩) = ∑ k : Slots s, cnt y (h k) := fun y =>
    (Fintype.sum_sigma fun k : Slots s => cnt y (h k)).symm
  simp only [pairW, h₁, h₂, h₃, Nat.cast_sum]
  rw [Finset.sum_mul_sum, Finset.sum_mul, Finset.sum_mul]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.sum_mul, Finset.sum_mul]

/-- The weight of a family of gene trees below a speciation, with `A`, `B` on two sides. -/
theorem pairW_glueSide_diff (φ : ℕ → ℝ≥0∞) {A B : X} {e : Bool} (s : J → Shape) (h h' : Slots s → Leaves X)
    (hzA : ∀ k, h' k A = 0) (hzB : ∀ k, h k B = 0) (w x : J) :
    pairW φ A B (fun j => glueSide e (s j) (fun w => h ⟨j, w⟩) (fun w => h' ⟨j, w⟩)) w x =
      ∑ k : (s w).copies, ∑ ℓ : (s x).copies, singleW φ A h ⟨w, k⟩ * singleW φ B h' ⟨x, ℓ⟩ := by
  have h₁ : ∀ j, cnt A (glueSide e (s j) (fun w => h ⟨j, w⟩) (fun w => h' ⟨j, w⟩)) = ∑ w : (s j).copies, cnt A (h ⟨j, w⟩) :=
    fun j => cnt_glueSide_left fun w => hzA _
  have h₂ : ∀ j, cnt B (glueSide e (s j) (fun w => h ⟨j, w⟩) (fun w => h' ⟨j, w⟩)) = ∑ w : (s j).copies, cnt B (h' ⟨j, w⟩) :=
    fun j => cnt_glueSide_right fun w => hzB _
  have h₃ : ∀ (y : X) (f : Slots s → Leaves X), ∑ j, ∑ w : (s j).copies, cnt y (f ⟨j, w⟩) = ∑ k : Slots s, cnt y (f k) :=
    fun y f => (Fintype.sum_sigma fun k : Slots s => cnt y (f k)).symm
  simp only [pairW, singleW, h₁, h₂, h₃, Nat.cast_sum]
  rw [Finset.sum_mul_sum, Finset.sum_mul, Finset.sum_mul]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.sum_mul, Finset.sum_mul]
  refine Finset.sum_congr rfl fun ℓ _ => ?_
  ring

/-- Independence, for two finite sums. -/
theorem expect_sum_sum_mul {α β : Type*} {I I' : Type*} [Fintype I] [Fintype I'] (P : PMF α) (Q : PMF β)
    (a : I → α → ℝ≥0∞) (b : I' → β → ℝ≥0∞) :
    expect P (fun h => expect Q fun h' => ∑ k, ∑ ℓ, a k h * b ℓ h') = ∑ k, ∑ ℓ, expect P (a k) * expect Q (b ℓ) := by
  have h₄ : ∀ h, expect Q (fun h' => ∑ k, ∑ ℓ, a k h * b ℓ h') = ∑ k, ∑ ℓ, a k h * expect Q (b ℓ) := by
    intro h
    rw [expect_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [expect_sum]
    refine Finset.sum_congr rfl fun ℓ _ => ?_
    rw [expect_mul_left]
  simp only [h₄]
  rw [expect_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [expect_sum]
  refine Finset.sum_congr rfl fun ℓ _ => ?_
  rw [expect_mul_right]

/-- **The recursion, with `A`, `B` on two sides of the speciation.** -/
theorem U_node_diff (φ : ℕ → ℝ≥0∞) {A B : X} (hT : (SpeciesTree.node K l r).Nodup) {e : Bool} (hA : (child l r e).Has A)
    (hB : (child l r (!e)).Has B) (w x : J) :
    U φ (.node K l r) A B J w x = expect (iid J K) fun s =>
      ∑ k : (s w).copies, ∑ ℓ : (s x).copies, V φ (child l r e) A (Slots s) ⟨w, k⟩ * V φ (child l r (!e)) B (Slots s) ⟨x, ℓ⟩ := by
  unfold U
  rw [expect_iid_node K l r e]
  refine congrArg _ (funext fun s => ?_)
  have hB' : ¬ (child l r e).Has B := by
    have := not_has_child_not (e := !e) hT hB
    rwa [Bool.not_not] at this
  unfold V
  rw [← expect_sum_sum_mul]
  refine expect_congr fun h hh => expect_congr fun h' hh' => ?_
  exact pairW_glueSide_diff φ s h h' (zero_of_iid hh' (not_has_child_not hT hA)) (zero_of_iid hh hB') w x

/-- At the most recent common ancestor of `A`, `B`, the table is a product, the same everywhere. -/
theorem exch_V_mul (φ : ℕ → ℝ≥0∞) (T T' : SpeciesTree X) (A B : X) :
    Exch fun J _ k ℓ => V φ T A J k * V φ T' B J ℓ := by
  refine ⟨fun J J' _ _ e w x => ?_, fun J _ w x => ?_⟩
  · rw [V_equiv φ T A e w, V_equiv φ T' B e x]
  · rw [V_eq φ T' B x w]

/-- **Lemmas 1 and 2** (`ext:legried_lem1`, `ext:legried_lem2`). The expectation of `A_w B_x φ(Σ A) φ(Σ B)` has one value on `w = x`,
another off it, and the first is at least the second, for two species below the vertex. -/
theorem exch_U (φ : ℕ → ℝ≥0∞) {A B : X} (hAB : A ≠ B) (T : SpeciesTree X) (hT : T.Nodup) (hA : T.Has A) (hB : T.Has B) :
    Exch fun J _ w x => U φ T A B J w x := by
  induction T with
  | leaf K y => exact absurd ((show A = y from hA).trans (show B = y from hB).symm) hAB
  | node K l r ihl ihr =>
    refine ⟨fun J J' _ _ e w x => U_equiv φ _ A B e w x, fun J _ w x => ?_⟩
    obtain ⟨eA, hA'⟩ := has_child_or hA
    obtain ⟨eB, hB'⟩ := has_child_or hB
    by_cases heq : eA = eB
    · subst heq
      have hE : Exch fun J _ w x => U φ (child l r eA) A B J w x := by
        cases eA
        · exact ihl hT.1 hA' hB'
        · exact ihr hT.2.1 hA' hB'
      rw [U_node_same φ hT hA' hB', U_node_same φ hT hA' hB']
      exact step_le hE K w x
    · have hB'' : (child l r (!eA)).Has B := by
        have : eB = !eA := by cases eA <;> cases eB <;> simp_all
        rwa [← this]
      rw [U_node_diff φ hT hA' hB'', U_node_diff φ hT hA' hB'']
      exact step_le (exch_V_mul φ _ _ A B) K w x

end Node

end External.LegriedEtAl2021
