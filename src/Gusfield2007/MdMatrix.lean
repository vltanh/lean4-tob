module

public import Gusfield2007.Examples
public import Gusfield2007.Components
public import Gusfield2007.Mosaic
public import External.HudsonKaplan1985.Bound

/-!
# Gusfield et al. 2007, Theorem 11: the matrix `M_d`

`M_d` has the six rows of Figure 6, repeated `d` times: its column `j` is the column `j % 6` of Figure 6. So it has two connected components (line 641), and `R¹(M_d(C_k)) = 2d` (line 643): `≥` by the Hudson-Kaplan bound, and `≤` by the network of
`Gusfield2007.Mosaic`.
-/

@[expose] public section

open scoped Classical

namespace Gusfield2007

variable {d : ℕ}

/-- The column of Figure 6 that the column `j` of `M_d` repeats. -/
def mod6 (j : Fin (6 * d)) : Fin 6 := ⟨j.val % 6, Nat.mod_lt _ (by decide)⟩

/-- The entry of Figure 6. -/
def fig6Entry (t s : Fin 6) : Bool := (ofBits (fig6Table.getD t.val []) : Fin 6 → Bool) s

theorem mem_Md {r : Fin (6 * d) → Bool} : r ∈ Md d ↔ ∃ t : Fin 6, r = fun j => fig6Entry t (mod6 j) := by
  unfold Md
  rw [Finset.mem_image]
  constructor
  · rintro ⟨t, -, rfl⟩
    exact ⟨t, rfl⟩
  · rintro ⟨t, rfl⟩
    exact ⟨t, by simp, rfl⟩

/-- A site of `M_d` of a given type, in the first copy. -/
def firstSite (hd : 0 < d) (s : Fin 6) : Fin (6 * d) := ⟨s.val, Nat.lt_of_lt_of_le s.2 (Nat.le_mul_of_pos_right 6 hd)⟩

theorem mod6_firstSite (hd : 0 < d) (s : Fin 6) : mod6 (firstSite hd s) = s :=
  Fin.ext (Nat.mod_eq_of_lt s.2)

theorem Md_nonempty : (Md d).Nonempty := ⟨_, mem_Md.2 ⟨0, rfl⟩⟩

/-- Incompatibility in `M_d` is incompatibility in Figure 6. -/
theorem incompatible_Md_iff (i j : Fin (6 * d)) : Incompatible (Md d) i j ↔ ∀ a b : Bool, ∃ t : Fin 6, fig6Entry t (mod6 i) = a ∧ fig6Entry t (mod6 j) = b := by
  constructor
  · intro h a b
    obtain ⟨r, hr, h₁, h₂⟩ := h a b
    obtain ⟨t, rfl⟩ := mem_Md.1 hr
    exact ⟨t, h₁, h₂⟩
  · intro h a b
    obtain ⟨t, h₁, h₂⟩ := h a b
    exact ⟨_, mem_Md.2 ⟨t, rfl⟩, h₁, h₂⟩

/-- The types of column of Figure 6 and the pairs that are incompatible. -/
theorem fig6Entry_incompatible : ∀ s s' : Fin 6, (∀ a b : Bool, ∃ t : Fin 6, fig6Entry t s = a ∧ fig6Entry t s' = b) →
    ((s.val = 1 ∨ s.val = 2 ∨ s.val = 4) ↔ (s'.val = 1 ∨ s'.val = 2 ∨ s'.val = 4)) := by
  decide +kernel

theorem fig6Entry_incompatible₁ : ∀ a b : Bool, ∃ t : Fin 6, fig6Entry t 1 = a ∧ fig6Entry t 2 = b := by decide +kernel
theorem fig6Entry_incompatible₂ : ∀ a b : Bool, ∃ t : Fin 6, fig6Entry t 2 = a ∧ fig6Entry t 4 = b := by decide +kernel
theorem fig6Entry_incompatible₃ : ∀ a b : Bool, ∃ t : Fin 6, fig6Entry t 0 = a ∧ fig6Entry t 3 = b := by decide +kernel
theorem fig6Entry_incompatible₄ : ∀ a b : Bool, ∃ t : Fin 6, fig6Entry t 3 = a ∧ fig6Entry t 5 = b := by decide +kernel

theorem fig6Entry_nonconstant : ∀ s : Fin 6, ∃ t t' : Fin 6, fig6Entry t s ≠ fig6Entry t' s := by decide +kernel

theorem Md_noConstantColumn : NoConstantColumn (Md d) := fun i => by
  obtain ⟨t, t', h⟩ := fig6Entry_nonconstant (mod6 i)
  exact ⟨_, mem_Md.2 ⟨t, rfl⟩, _, mem_Md.2 ⟨t', rfl⟩, h⟩

theorem MdC₁_compl : (MdC₁ d)ᶜ = MdC₂ d := Set.ext fun j => by
  change ¬ (j.val % 6 = 1 ∨ j.val % 6 = 2 ∨ j.val % 6 = 4) ↔ (j.val % 6 = 0 ∨ j.val % 6 = 3 ∨ j.val % 6 = 5)
  omega

/-- **Line 641**: the two components of `G(M_d)`: "the first only containing columns of type `x` or `y`, and the second only containing columns of type `u` or `v`". -/
theorem Md_reachable (i j : Fin (6 * d)) : (incompatGraph (Md d)).Reachable i j ↔ (i ∈ MdC₁ d ↔ j ∈ MdC₁ d) := by
  have hd : 0 < d := by
    have := i.2
    omega
  refine reachable_iff_of_adj _ (fun i j hij => ?_) (a := firstSite hd 2) (b := firstSite hd 3) (fun i hi => ?_) (fun i hi => ?_) i j
  · exact fig6Entry_incompatible _ _ ((incompatible_Md_iff i j).1 hij)
  · have hadj : ∀ i : Fin (6 * d), (i.val % 6 = 1 ∨ i.val % 6 = 4) → (incompatGraph (Md d)).Adj i (firstSite hd 2) := fun i hi => by
      refine (incompatible_Md_iff _ _).2 ?_
      rw [mod6_firstSite]
      have hm : mod6 i = 1 ∨ mod6 i = 4 := by
        rcases hi with hi | hi
        · exact Or.inl (Fin.ext hi)
        · exact Or.inr (Fin.ext hi)
      rcases hm with hm | hm
      · rw [hm]
        exact fig6Entry_incompatible₁
      · rw [hm]
        intro a b
        obtain ⟨t, h₁, h₂⟩ := fig6Entry_incompatible₂ b a
        exact ⟨t, h₂, h₁⟩
    rcases hi with hi | hi | hi
    · exact (hadj i (Or.inl hi)).reachable
    · have h₁ : (incompatGraph (Md d)).Adj i (firstSite hd 1) := by
        refine (incompatible_Md_iff _ _).2 ?_
        rw [mod6_firstSite]
        have hm : mod6 i = 2 := Fin.ext hi
        rw [hm]
        intro a b
        obtain ⟨t, h₁, h₂⟩ := fig6Entry_incompatible₁ b a
        exact ⟨t, h₂, h₁⟩
      exact h₁.reachable.trans (hadj _ (Or.inl (congrArg Fin.val (mod6_firstSite hd 1)))).reachable
    · exact (hadj i (Or.inr hi)).reachable
  · have hi' : i.val % 6 = 0 ∨ i.val % 6 = 3 ∨ i.val % 6 = 5 := by
      change ¬ (i.val % 6 = 1 ∨ i.val % 6 = 2 ∨ i.val % 6 = 4) at hi
      omega
    have hadj : ∀ i : Fin (6 * d), (i.val % 6 = 0 ∨ i.val % 6 = 5) → (incompatGraph (Md d)).Adj i (firstSite hd 3) := fun i hi => by
      refine (incompatible_Md_iff _ _).2 ?_
      rw [mod6_firstSite]
      have hm : mod6 i = 0 ∨ mod6 i = 5 := by
        rcases hi with hi | hi
        · exact Or.inl (Fin.ext hi)
        · exact Or.inr (Fin.ext hi)
      rcases hm with hm | hm
      · rw [hm]
        exact fig6Entry_incompatible₃
      · rw [hm]
        intro a b
        obtain ⟨t, h₁, h₂⟩ := fig6Entry_incompatible₄ b a
        exact ⟨t, h₂, h₁⟩
    rcases hi' with hi' | hi' | hi'
    · exact (hadj i (Or.inl hi')).reachable
    · have h₁ : (incompatGraph (Md d)).Adj i (firstSite hd 0) := by
        refine (incompatible_Md_iff _ _).2 ?_
        rw [mod6_firstSite]
        have hm : mod6 i = 3 := Fin.ext hi'
        rw [hm]
        intro a b
        obtain ⟨t, h₁, h₂⟩ := fig6Entry_incompatible₃ b a
        exact ⟨t, h₂, h₁⟩
      exact h₁.reachable.trans (hadj _ (Or.inl (congrArg Fin.val (mod6_firstSite hd 0)))).reachable
    · exact (hadj i (Or.inr hi')).reachable

/-! ### One component -/

/-- The data of a component of `G(M_d)`: the three types of column in one copy of Figure 6, the first and the third being the same column of Figure 6, and incompatible with the second. -/
structure CompData (o₁ o₂ o₃ : Fin 6) : Prop where
  lt₁ : o₁ < o₂
  lt₂ : o₂ < o₃
  same : ∀ t, fig6Entry t o₁ = fig6Entry t o₃
  inc : ∀ a b : Bool, ∃ t : Fin 6, fig6Entry t o₁ = a ∧ fig6Entry t o₂ = b

theorem compData₁ : CompData 1 2 4 := by
  refine ⟨by decide, by decide, by decide +kernel, by decide +kernel⟩

theorem compData₂ : CompData 0 3 5 := by
  refine ⟨by decide, by decide, by decide +kernel, by decide +kernel⟩

/-- The sites of a component. -/
def compSet (d : ℕ) (o₁ o₂ o₃ : Fin 6) : Set (Fin (6 * d)) := {j | j.val % 6 = o₁ ∨ j.val % 6 = o₂ ∨ j.val % 6 = o₃}

/-- The segment of a site, in `R_single_le_of_mosaic`: all the columns of the same type in a row are in one segment. -/
def compSeg (o₁ o₂ : Fin 6) (j : Fin (6 * d)) : ℕ :=
  2 * (j.val / 6) + (if j.val % 6 = o₁ then 0 else if j.val % 6 = o₂ then 1 else 2)

variable {o₁ o₂ o₃ : Fin 6}

theorem compSeg_mono (h : CompData o₁ o₂ o₃) : Monotone fun j : compSet d o₁ o₂ o₃ => compSeg o₁ o₂ j.1 := by
  intro a b hab
  have hab' : a.1.val ≤ b.1.val := hab
  have h₁ := h.lt₁
  have h₂ := h.lt₂
  have h₃ := o₃.2
  have ha := a.2
  have hb := b.2
  change a.1.val % 6 = o₁ ∨ a.1.val % 6 = o₂ ∨ a.1.val % 6 = o₃ at ha
  change b.1.val % 6 = o₁ ∨ b.1.val % 6 = o₂ ∨ b.1.val % 6 = o₃ at hb
  rw [Fin.lt_def] at h₁ h₂
  simp only [compSeg]
  have e₁ := Nat.div_add_mod a.1.val 6
  have e₂ := Nat.div_add_mod b.1.val 6
  split_ifs <;> omega

theorem compSeg_le (j : compSet d o₁ o₂ o₃) : compSeg o₁ o₂ j.1 ≤ 2 * d := by
  have hj := j.1.2
  have hdiv : j.1.val / 6 < d := Nat.div_lt_of_lt_mul hj
  simp only [compSeg]
  split_ifs <;> omega

/-- The rows of `M_d(C)`. -/
theorem mem_restrictRows_comp (h : CompData o₁ o₂ o₃) (r : compSet d o₁ o₂ o₃ → Bool) :
    r ∈ restrictRows (compSet d o₁ o₂ o₃) (Md d) ↔ r = (fun _ => false) ∨
      r = Mosaic.parity (fun j : compSet d o₁ o₂ o₃ => compSeg o₁ o₂ j.1) 0 ∨
      r = Mosaic.parity (fun j : compSet d o₁ o₂ o₃ => compSeg o₁ o₂ j.1) 1 ∨ r = fun _ => true := by
  have hne := h.lt₁.ne
  have hne' : o₁.val ≠ o₂.val := fun h' => hne (Fin.ext h')
  have hne₃ : o₃.val ≠ o₂.val := fun h' => h.lt₂.ne (Fin.ext h'.symm)
  have hneq : o₃.val ≠ o₁.val := fun h' => by
    have := Fin.lt_def.1 (h.lt₁.trans h.lt₂)
    omega
  -- The parity of the segment is the type of the column.
  have hpar : ∀ j : compSet d o₁ o₂ o₃, (compSeg o₁ o₂ j.1 % 2 = 1 ↔ j.1.val % 6 = o₂) := fun j => by
    have hj := j.2
    change j.1.val % 6 = o₁ ∨ j.1.val % 6 = o₂ ∨ j.1.val % 6 = o₃ at hj
    simp only [compSeg]
    split_ifs <;> omega
  have hmod : ∀ j : compSet d o₁ o₂ o₃, mod6 j.1 = o₁ ∨ mod6 j.1 = o₂ ∨ mod6 j.1 = o₃ := fun j => by
    rcases j.2 with hj | hj | hj
    · exact Or.inl (Fin.ext hj)
    · exact Or.inr (Or.inl (Fin.ext hj))
    · exact Or.inr (Or.inr (Fin.ext hj))
  have hval : ∀ (t : Fin 6) (j : compSet d o₁ o₂ o₃), fig6Entry t (mod6 j.1) = if compSeg o₁ o₂ j.1 % 2 = 1 then fig6Entry t o₂ else fig6Entry t o₁ := fun t j => by
    by_cases hj : compSeg o₁ o₂ j.1 % 2 = 1
    · have : mod6 j.1 = o₂ := Fin.ext ((hpar j).1 hj)
      simp only [hj, ↓reduceIte, this]
    · simp only [hj, ↓reduceIte]
      have hne₂ : j.1.val % 6 ≠ o₂ := fun h' => hj ((hpar j).2 h')
      rcases hmod j with h' | h' | h'
      · rw [h']
      · exact absurd (congrArg Fin.val h') hne₂
      · rw [h', h.same]
  have hseg2 : ∀ j : compSet d o₁ o₂ o₃, compSeg o₁ o₂ j.1 % 2 = 0 ∨ compSeg o₁ o₂ j.1 % 2 = 1 := fun j => by omega
  rw [mem_restrictRows]
  constructor
  · rintro ⟨r', hr', rfl⟩
    obtain ⟨t, rfl⟩ := mem_Md.1 hr'
    have hrow : (compSet d o₁ o₂ o₃).domRestrict (fun j => fig6Entry t (mod6 j)) =
        fun j : compSet d o₁ o₂ o₃ => if compSeg o₁ o₂ j.1 % 2 = 1 then fig6Entry t o₂ else fig6Entry t o₁ := by
      funext j
      exact hval t j
    rw [hrow]
    cases h₁ : fig6Entry t o₁ <;> cases h₂ : fig6Entry t o₂
    · left
      funext j
      split_ifs <;> rfl
    · right; right; left
      funext j
      simp only [Mosaic.parity]
      rcases hseg2 j with hj | hj <;> simp [hj]
    · right; left
      funext j
      simp only [Mosaic.parity]
      rcases hseg2 j with hj | hj <;> simp [hj]
    · right; right; right
      funext j
      split_ifs <;> rfl
  · have hrow : ∀ a b : Bool, ∃ r' ∈ Md d, (compSet d o₁ o₂ o₃).domRestrict r' =
        fun j : compSet d o₁ o₂ o₃ => if compSeg o₁ o₂ j.1 % 2 = 1 then b else a := fun a b => by
      obtain ⟨t, h₁, h₂⟩ := h.inc a b
      refine ⟨_, mem_Md.2 ⟨t, rfl⟩, ?_⟩
      funext j
      rw [← h₁, ← h₂]
      exact hval t j
    rintro (rfl | rfl | rfl | rfl)
    · obtain ⟨r', hr', he⟩ := hrow false false
      refine ⟨r', hr', he.trans ?_⟩
      funext j
      split_ifs <;> rfl
    · obtain ⟨r', hr', he⟩ := hrow true false
      refine ⟨r', hr', he.trans ?_⟩
      funext j
      simp only [Mosaic.parity]
      rcases hseg2 j with hj | hj <;> simp [hj]
    · obtain ⟨r', hr', he⟩ := hrow false true
      refine ⟨r', hr', he.trans ?_⟩
      funext j
      simp only [Mosaic.parity]
      rcases hseg2 j with hj | hj <;> simp [hj]
    · obtain ⟨r', hr', he⟩ := hrow true true
      refine ⟨r', hr', he.trans ?_⟩
      funext j
      split_ifs <;> rfl

/-- The upper bound: the network of `Gusfield2007.Mosaic`. -/
theorem R_comp_le (h : CompData o₁ o₂ o₃) : R .single (restrictRows (compSet d o₁ o₂ o₃) (Md d)) ≤ 2 * d := by
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · have : IsEmpty (compSet 0 o₁ o₂ o₃) := ⟨fun j => absurd j.1.2 (by simp)⟩
    have hne : (restrictRows (compSet 0 o₁ o₂ o₃) (Md 0)).Nonempty := by
      obtain ⟨r, hr⟩ := Md_nonempty (d := 0)
      exact ⟨_, mem_restrictRows.2 ⟨r, hr, rfl⟩⟩
    rw [R_eq_zero_of_isEmpty _ _ hne]
  · have hsite : ∀ o, (o = o₁ ∨ o = o₂ ∨ o = o₃) → (firstSite hd o) ∈ compSet d o₁ o₂ o₃ := fun o ho => by
      have hm : (firstSite hd o).val % 6 = o.val := Nat.mod_eq_of_lt o.2
      change (firstSite hd o).val % 6 = o₁ ∨ (firstSite hd o).val % 6 = o₂ ∨ (firstSite hd o).val % 6 = o₃
      rw [hm]
      rcases ho with rfl | rfl | rfl <;> simp
    have hlt₂ := Fin.lt_def.1 h.lt₁
    have hdiv : ∀ o : Fin 6, (firstSite hd o).val / 6 = 0 := fun o => Nat.div_eq_of_lt o.2
    have hmod : ∀ o : Fin 6, (firstSite hd o).val % 6 = o.val := fun o => Nat.mod_eq_of_lt o.2
    refine R_single_le_of_mosaic _ (compSeg_mono h) (n := 2 * d) (by omega) compSeg_le (i₀ := ⟨firstSite hd o₁, hsite _ (Or.inl rfl)⟩)
      (i₁ := ⟨firstSite hd o₂, hsite _ (Or.inr (Or.inl rfl))⟩) ?_ ?_ (mem_restrictRows_comp h)
    · simp [compSeg, hdiv, hmod]
    · have : o₂.val ≠ o₁.val := by omega
      simp [compSeg, hdiv, hmod, this]

theorem compSet₁ (d : ℕ) : MdC₁ d = compSet d 1 2 4 := rfl

theorem compSet₂ (d : ℕ) : MdC₂ d = compSet d 0 3 5 := rfl

/-- The left end of the `n`-th pair of the Hudson-Kaplan bound. -/
def compLeft (o₁ o₂ : Fin 6) (n : ℕ) : ℕ := 6 * (n / 2) + (if n % 2 = 0 then o₁.val else o₂.val)

/-- The right end of the `n`-th pair of the Hudson-Kaplan bound. -/
def compRight (o₂ o₃ : Fin 6) (n : ℕ) : ℕ := 6 * (n / 2) + (if n % 2 = 0 then o₂.val else o₃.val)

theorem compLeft_lt (o₁ o₂ : Fin 6) {n : ℕ} (hn : n < 2 * d) : compLeft o₁ o₂ n < 6 * d := by
  have h₁ := o₁.2
  have h₂ := o₂.2
  simp only [compLeft]
  split_ifs <;> omega

theorem compRight_lt (o₂ o₃ : Fin 6) {n : ℕ} (hn : n < 2 * d) : compRight o₂ o₃ n < 6 * d := by
  have h₁ := o₂.2
  have h₂ := o₃.2
  simp only [compRight]
  split_ifs <;> omega

theorem compLeft_mod (o₁ o₂ : Fin 6) (n : ℕ) : compLeft o₁ o₂ n % 6 = if n % 2 = 0 then o₁.val else o₂.val := by
  have h₁ := o₁.2
  have h₂ := o₂.2
  simp only [compLeft]
  split_ifs <;> omega

theorem compRight_mod (o₂ o₃ : Fin 6) (n : ℕ) : compRight o₂ o₃ n % 6 = if n % 2 = 0 then o₂.val else o₃.val := by
  have h₁ := o₂.2
  have h₂ := o₃.2
  simp only [compRight]
  split_ifs <;> omega

/-- The `n`-th pair of the Hudson-Kaplan bound. -/
def compPair (d : ℕ) (o₁ o₂ o₃ : Fin 6) (n : Fin (2 * d)) : compSet d o₁ o₂ o₃ × compSet d o₁ o₂ o₃ :=
  (⟨⟨compLeft o₁ o₂ n, compLeft_lt o₁ o₂ n.2⟩, by
      change compLeft o₁ o₂ n % 6 = o₁ ∨ compLeft o₁ o₂ n % 6 = o₂ ∨ compLeft o₁ o₂ n % 6 = o₃
      rw [compLeft_mod]
      split_ifs <;> simp⟩,
    ⟨⟨compRight o₂ o₃ n, compRight_lt o₂ o₃ n.2⟩, by
      change compRight o₂ o₃ n % 6 = o₁ ∨ compRight o₂ o₃ n % 6 = o₂ ∨ compRight o₂ o₃ n % 6 = o₃
      rw [compRight_mod]
      split_ifs <;> simp⟩)

/-- Incompatible columns of `M` are incompatible in `M(C)`. -/
theorem incompatible_restrictRows {ι : Type*} {M : Finset (ι → Bool)} {C : Set ι} {i j : C} (h : Incompatible M i.1 j.1) : Incompatible (restrictRows C M) i j := fun a b => by
  obtain ⟨r, hr, h₁, h₂⟩ := h a b
  exact ⟨_, mem_restrictRows.2 ⟨r, hr, rfl⟩, h₁, h₂⟩

/-- **Line 643**: the lower bound, by the Hudson-Kaplan bound: between two consecutive columns of different types, one recombination. -/
theorem le_R_comp (h : CompData o₁ o₂ o₃) : 2 * d ≤ R .single (restrictRows (compSet d o₁ o₂ o₃) (Md d)) := by
  have hl₁ := Fin.lt_def.1 h.lt₁
  have hl₂ := Fin.lt_def.1 h.lt₂
  have h₃ := o₃.2
  have hinj : Function.Injective (compPair d o₁ o₂ o₃) := fun a b hab => by
    have h₁ : compLeft o₁ o₂ a.val = compLeft o₁ o₂ b.val := congrArg (fun p => p.1.1.val) hab
    have h₂ : compRight o₂ o₃ a.val = compRight o₂ o₃ b.val := congrArg (fun p => p.2.1.val) hab
    refine Fin.ext ?_
    simp only [compLeft, compRight] at h₁ h₂
    split_ifs at h₁ h₂ <;> omega
  have hcard : (Finset.univ.image (compPair d o₁ o₂ o₃)).card = 2 * d := by
    rw [Finset.card_image_of_injective _ hinj]
    simp
  rw [← hcard]
  refine HudsonKaplan1985.card_le_R _ _ (fun p hp => ?_) (fun p hp q hq hne => ?_)
  · obtain ⟨n, -, rfl⟩ := Finset.mem_image.1 hp
    refine ⟨?_, incompatible_restrictRows ?_⟩
    · change compLeft o₁ o₂ n < compRight o₂ o₃ n
      simp only [compLeft, compRight]
      split_ifs <;> omega
    · refine (incompatible_Md_iff _ _).2 fun a b => ?_
      have hm₁ : mod6 (compPair d o₁ o₂ o₃ n).1.1 = if n.val % 2 = 0 then o₁ else o₂ := by
        refine Fin.ext ?_
        change compLeft o₁ o₂ n % 6 = _
        rw [compLeft_mod]
        split_ifs <;> rfl
      have hm₂ : mod6 (compPair d o₁ o₂ o₃ n).2.1 = if n.val % 2 = 0 then o₂ else o₃ := by
        refine Fin.ext ?_
        change compRight o₂ o₃ n % 6 = _
        rw [compRight_mod]
        split_ifs <;> rfl
      rw [hm₁, hm₂]
      split_ifs
      · exact h.inc a b
      · obtain ⟨t, h₁, h₂⟩ := h.inc b a
        exact ⟨t, h₂, h.same t ▸ h₁⟩
  · obtain ⟨a, -, rfl⟩ := Finset.mem_image.1 hp
    obtain ⟨b, -, rfl⟩ := Finset.mem_image.1 hq
    have hab : a.val ≠ b.val := fun h' => hne (by rw [Fin.ext h'])
    have key : ∀ x y : ℕ, x < y → compRight o₂ o₃ x ≤ compLeft o₁ o₂ y := fun x y hxy => by
      simp only [compLeft, compRight]
      split_ifs <;> omega
    rcases lt_or_gt_of_ne hab with hlt | hlt
    · exact Or.inl (key _ _ hlt)
    · exact Or.inr (key _ _ hlt)

/-- `R¹(M_d(C)) = 2d`, for each of the two components (line 643). -/
theorem R_comp_eq (h : CompData o₁ o₂ o₃) : R .single (restrictRows (compSet d o₁ o₂ o₃) (Md d)) = 2 * d :=
  le_antisymm (R_comp_le h) (le_R_comp h)

end Gusfield2007
