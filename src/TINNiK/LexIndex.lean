module

public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.Finset.Sort
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Ring

/-!
# TINNiK: the index of a set of four taxa

TINNiK's text (line 162): the sets of four taxa are ordered lexicographically, "In lex order, the index for a particular set of 4 taxa is given by the formula (Corollary 3.22, [34])
`ρ(n₁, n₂, n₃, n₄) = C(N, 4) - ∑_{i=1}^4 C(N - n_i, 5 - i)`. [...] Tabulating all binomial coefficients that might be needed in the formula in advance, so they are computed only once, requires time `O(N)`. After this, however, the index for any set of 4 taxa can be
computed in time `O(1)`."

* `rho`: the formula; `rho_lt_rho`: it increases along the lexicographic order; `rho_first`, `rho_last`, `one_le_rho`, `rho_le_choose`: its range.
* `image_rho_words`: **it is the index**: a bijection from the sets of four taxa to `[1, C(N, 4)]`, increasing, hence the rank in lex order. [34] was not read: this proves the formula directly.
* `card_table`, `rho_reads`: the table of `5 (N + 1)` binomial coefficients, each a sum of two others by Pascal's rule, and the five entries that the formula reads.
-/

@[expose] public noncomputable section

open Finset
open scoped Classical

namespace TINNiK

/-- The formula for the index of the set `{a, b, c, d}`, `1 ≤ a < b < c < d ≤ N`. -/
def rho (N a b c d : ℕ) : ℕ :=
  N.choose 4 - ((N - a).choose 4 + (N - b).choose 3 + (N - c).choose 2 + (N - d).choose 1)

/-- The sum subtracted in the formula. -/
def rhoSum (N a b c d : ℕ) : ℕ := (N - a).choose 4 + (N - b).choose 3 + (N - c).choose 2 + (N - d).choose 1

/-- Pascal's rule, down to the last term: `C(x + 4, 4) = C(x + 3, 4) + C(x + 2, 3) + C(x + 1, 2) + C(x, 1) + 1`. -/
theorem choose_four_eq (x : ℕ) :
    (x + 4).choose 4 = (x + 3).choose 4 + (x + 2).choose 3 + (x + 1).choose 2 + x.choose 1 + 1 := by
  have h₁ : (x + 4).choose 4 = (x + 3).choose 3 + (x + 3).choose 4 := Nat.choose_succ_succ (x + 3) 3
  have h₂ : (x + 3).choose 3 = (x + 2).choose 2 + (x + 2).choose 3 := Nat.choose_succ_succ (x + 2) 2
  have h₃ : (x + 2).choose 2 = (x + 1).choose 1 + (x + 1).choose 2 := Nat.choose_succ_succ (x + 1) 1
  have h₄ : (x + 1).choose 1 = x + 1 := Nat.choose_one_right _
  have h₅ : x.choose 1 = x := Nat.choose_one_right _
  omega

/-- `C(x + 3, 3) = C(x + 2, 3) + C(x + 1, 2) + C(x, 1) + 1`. -/
theorem choose_three_eq (x : ℕ) : (x + 3).choose 3 = (x + 2).choose 3 + (x + 1).choose 2 + x.choose 1 + 1 := by
  have h₂ : (x + 3).choose 3 = (x + 2).choose 2 + (x + 2).choose 3 := Nat.choose_succ_succ (x + 2) 2
  have h₃ : (x + 2).choose 2 = (x + 1).choose 1 + (x + 1).choose 2 := Nat.choose_succ_succ (x + 1) 1
  have h₄ : (x + 1).choose 1 = x + 1 := Nat.choose_one_right _
  have h₅ : x.choose 1 = x := Nat.choose_one_right _
  omega

/-- `C(x + 2, 2) = C(x + 1, 2) + C(x, 1) + 1`. -/
theorem choose_two_eq (x : ℕ) : (x + 2).choose 2 = (x + 1).choose 2 + x.choose 1 + 1 := by
  have h₃ : (x + 2).choose 2 = (x + 1).choose 1 + (x + 1).choose 2 := Nat.choose_succ_succ (x + 1) 1
  have h₄ : (x + 1).choose 1 = x + 1 := Nat.choose_one_right _
  have h₅ : x.choose 1 = x := Nat.choose_one_right _
  omega

/-- The lexicographic order on words. -/
def LexLT (w w' : ℕ × ℕ × ℕ × ℕ) : Prop :=
  w.1 < w'.1 ∨ (w.1 = w'.1 ∧ (w.2.1 < w'.2.1 ∨ (w.2.1 = w'.2.1 ∧ (w.2.2.1 < w'.2.2.1 ∨ (w.2.2.1 = w'.2.2.1 ∧ w.2.2.2 < w'.2.2.2)))))

/-- A word: `1 ≤ a < b < c < d ≤ N`. -/
def IsWord (N : ℕ) (w : ℕ × ℕ × ℕ × ℕ) : Prop := 1 ≤ w.1 ∧ w.1 < w.2.1 ∧ w.2.1 < w.2.2.1 ∧ w.2.2.1 < w.2.2.2 ∧ w.2.2.2 ≤ N

/-- **The formula's sum decreases along the lexicographic order.** -/
theorem rhoSum_lt_rhoSum {N : ℕ} {w w' : ℕ × ℕ × ℕ × ℕ} (hw : IsWord N w) (hw' : IsWord N w') (h : LexLT w w') :
    rhoSum N w'.1 w'.2.1 w'.2.2.1 w'.2.2.2 < rhoSum N w.1 w.2.1 w.2.2.1 w.2.2.2 := by
  obtain ⟨a, b, c, d⟩ := w
  obtain ⟨a', b', c', d'⟩ := w'
  simp only [IsWord, LexLT, rhoSum] at hw hw' h ⊢
  obtain ⟨h₁, h₂, h₃, h₄, h₅⟩ := hw
  obtain ⟨h₁', h₂', h₃', h₄', h₅'⟩ := hw'
  have mono : ∀ {x y k : ℕ}, x ≤ y → x.choose k ≤ y.choose k := fun h => Nat.choose_le_choose _ h
  rcases h with h | ⟨rfl, h | ⟨rfl, h | ⟨rfl, h⟩⟩⟩
  · -- the first entry differs
    obtain ⟨x, hx⟩ : ∃ x, N - a = x + 4 := ⟨N - a - 4, by omega⟩
    have e := choose_four_eq x
    have m₁ : (N - a').choose 4 ≤ (x + 3).choose 4 := mono (by omega)
    have m₂ : (N - b').choose 3 ≤ (x + 2).choose 3 := mono (by omega)
    have m₃ : (N - c').choose 2 ≤ (x + 1).choose 2 := mono (by omega)
    have m₄ : (N - d').choose 1 ≤ x.choose 1 := mono (by omega)
    rw [hx]
    omega
  · obtain ⟨x, hx⟩ : ∃ x, N - b = x + 3 := ⟨N - b - 3, by omega⟩
    have e := choose_three_eq x
    have m₂ : (N - b').choose 3 ≤ (x + 2).choose 3 := mono (by omega)
    have m₃ : (N - c').choose 2 ≤ (x + 1).choose 2 := mono (by omega)
    have m₄ : (N - d').choose 1 ≤ x.choose 1 := mono (by omega)
    rw [hx]
    omega
  · obtain ⟨x, hx⟩ : ∃ x, N - c = x + 2 := ⟨N - c - 2, by omega⟩
    have e := choose_two_eq x
    have m₃ : (N - c').choose 2 ≤ (x + 1).choose 2 := mono (by omega)
    have m₄ : (N - d').choose 1 ≤ x.choose 1 := mono (by omega)
    rw [hx]
    omega
  · have m₄ : (N - d').choose 1 < (N - d).choose 1 := by
      rw [Nat.choose_one_right, Nat.choose_one_right]
      omega
    omega

/-- The first word has index `1`. -/
theorem rhoSum_first {N : ℕ} (hN : 4 ≤ N) : rhoSum N 1 2 3 4 + 1 = N.choose 4 := by
  obtain ⟨x, rfl⟩ : ∃ x, N = x + 4 := ⟨N - 4, by omega⟩
  have e := choose_four_eq x
  simp only [rhoSum, show x + 4 - 1 = x + 3 by omega, show x + 4 - 2 = x + 2 by omega, show x + 4 - 3 = x + 1 by omega,
    show x + 4 - 4 = x by omega]
  omega

theorem rho_first {N : ℕ} (hN : 4 ≤ N) : rho N 1 2 3 4 = 1 := by
  have := rhoSum_first hN
  unfold rhoSum at this
  unfold rho
  omega

/-- The last word has index `C(N, 4)`. -/
theorem rho_last {N : ℕ} (hN : 4 ≤ N) : rho N (N - 3) (N - 2) (N - 1) N = N.choose 4 := by
  simp only [rho, show N - (N - 3) = 3 by omega, show N - (N - 2) = 2 by omega, show N - (N - 1) = 1 by omega, Nat.sub_self]
  simp

/-- `rhoSum` of a word is below `C(N, 4)`, so the subtraction in the formula is a true one. -/
theorem rhoSum_lt_choose {N : ℕ} {w : ℕ × ℕ × ℕ × ℕ} (hw : IsWord N w) : rhoSum N w.1 w.2.1 w.2.2.1 w.2.2.2 < N.choose 4 := by
  have hN : 4 ≤ N := by
    obtain ⟨h₁, h₂, h₃, h₄, h₅⟩ := hw
    omega
  have hfirst := rhoSum_first hN
  by_cases he : w = (1, 2, 3, 4)
  · subst he
    simp only
    omega
  · have hlex : LexLT (1, 2, 3, 4) w := by
      obtain ⟨a, b, c, d⟩ := w
      simp only [IsWord] at hw
      simp only [LexLT, Prod.mk.injEq, not_and] at he ⊢
      omega
    have h1 : IsWord N (1, 2, 3, 4) := by
      simp only [IsWord]
      omega
    have := rhoSum_lt_rhoSum h1 hw hlex
    simp only at this
    omega

theorem one_le_rho {N : ℕ} {w : ℕ × ℕ × ℕ × ℕ} (hw : IsWord N w) : 1 ≤ rho N w.1 w.2.1 w.2.2.1 w.2.2.2 := by
  have := rhoSum_lt_choose hw
  unfold rhoSum at this
  unfold rho
  omega

theorem rho_le_choose (N a b c d : ℕ) : rho N a b c d ≤ N.choose 4 := Nat.sub_le _ _

/-- **The formula increases along the lexicographic order.** -/
theorem rho_lt_rho {N : ℕ} {w w' : ℕ × ℕ × ℕ × ℕ} (hw : IsWord N w) (hw' : IsWord N w') (h : LexLT w w') :
    rho N w.1 w.2.1 w.2.2.1 w.2.2.2 < rho N w'.1 w'.2.1 w'.2.2.1 w'.2.2.2 := by
  have h₁ := rhoSum_lt_rhoSum hw hw' h
  have h₂ := rhoSum_lt_choose hw
  unfold rhoSum at h₁ h₂
  unfold rho
  omega

/-- Distinct words are comparable. -/
theorem lexLT_or_of_ne {w w' : ℕ × ℕ × ℕ × ℕ} (h : w ≠ w') : LexLT w w' ∨ LexLT w' w := by
  obtain ⟨a, b, c, d⟩ := w
  obtain ⟨a', b', c', d'⟩ := w'
  simp only [LexLT, ne_eq, Prod.mk.injEq, not_and] at h ⊢
  omega

/-- The set of a word. -/
def wordSet (w : ℕ × ℕ × ℕ × ℕ) : Finset ℕ := {w.1, w.2.1, w.2.2.1, w.2.2.2}

/-- The words on `{1, ..., N}`. -/
def words (N : ℕ) : Finset (ℕ × ℕ × ℕ × ℕ) :=
  (Icc 1 N ×ˢ Icc 1 N ×ˢ Icc 1 N ×ˢ Icc 1 N).filter (IsWord N)

theorem mem_words {N : ℕ} {w : ℕ × ℕ × ℕ × ℕ} : w ∈ words N ↔ IsWord N w := by
  obtain ⟨a, b, c, d⟩ := w
  simp only [words, mem_filter, mem_product, mem_Icc, IsWord]
  constructor
  · exact fun h => h.2
  · intro h
    refine ⟨?_, h⟩
    omega

/-- **The words are the sets of four taxa**: there are `C(N, 4)`. -/
theorem card_words (N : ℕ) : (words N).card = N.choose 4 := by
  have hc : ((Icc 1 N).powersetCard 4).card = N.choose 4 := by
    rw [card_powersetCard, Nat.card_Icc]
    simp
  rw [← hc]
  refine card_nbij wordSet ?_ ?_ ?_
  · intro w hw
    have hw' := mem_words.1 (mem_coe.1 hw)
    obtain ⟨a, b, c, d⟩ := w
    simp only [IsWord] at hw'
    refine mem_coe.2 (mem_powersetCard.2 ⟨?_, ?_⟩)
    · intro x hx
      simp only [wordSet, mem_insert, mem_singleton] at hx
      rw [mem_Icc]
      omega
    · simp only [wordSet]
      rw [card_insert_of_notMem, card_insert_of_notMem, card_insert_of_notMem, card_singleton]
      all_goals simp only [mem_insert, mem_singleton]
      all_goals omega
  · intro w hw w' hw' h
    have h₁ := mem_words.1 (mem_coe.1 hw)
    have h₂ := mem_words.1 (mem_coe.1 hw')
    obtain ⟨a, b, c, d⟩ := w
    obtain ⟨a', b', c', d'⟩ := w'
    simp only [IsWord] at h₁ h₂
    have hm : ∀ x, x ∈ wordSet (a, b, c, d) ↔ x ∈ wordSet (a', b', c', d') := fun x => by rw [h]
    simp only [wordSet, mem_insert, mem_singleton] at hm
    have ha := (hm a).1 (by simp)
    have hb := (hm b).1 (by simp)
    have hc' := (hm c).1 (by simp)
    have hd := (hm d).1 (by simp)
    have ha' := (hm a').2 (by simp)
    have hb' := (hm b').2 (by simp)
    have hc'' := (hm c').2 (by simp)
    have hd' := (hm d').2 (by simp)
    simp only [Prod.mk.injEq]
    omega
  · intro s hs
    obtain ⟨hsub, hcard⟩ := mem_powersetCard.1 (mem_coe.1 hs)
    let e := s.orderEmbOfFin hcard
    have hmem : ∀ i, e i ∈ Icc 1 N := fun i => hsub (s.orderEmbOfFin_mem hcard i)
    have hlt : ∀ {i j : Fin 4}, i < j → e i < e j := fun h => e.strictMono h
    refine ⟨(e 0, e 1, e 2, e 3), mem_coe.2 (mem_words.2 ?_), ?_⟩
    · have h₀ := mem_Icc.1 (hmem 0)
      have h₃ := mem_Icc.1 (hmem 3)
      exact ⟨h₀.1, hlt (by decide), hlt (by decide), hlt (by decide), h₃.2⟩
    · have himg := s.image_orderEmbOfFin_univ hcard
      refine Eq.trans ?_ himg
      ext x
      simp only [wordSet, mem_insert, mem_singleton, mem_image, mem_univ, true_and]
      constructor
      · rintro (rfl | rfl | rfl | rfl)
        · exact ⟨0, rfl⟩
        · exact ⟨1, rfl⟩
        · exact ⟨2, rfl⟩
        · exact ⟨3, rfl⟩
      · rintro ⟨i, rfl⟩
        fin_cases i
        · exact Or.inl rfl
        · exact Or.inr (Or.inl rfl)
        · exact Or.inr (Or.inr (Or.inl rfl))
        · exact Or.inr (Or.inr (Or.inr rfl))

/-- **The formula is the index** (TINNiK's text, line 162): it maps the sets of four taxa onto `[1, C(N, 4)]`, one-to-one, and in the lexicographic order (`rho_lt_rho`). So it is the position in that order. -/
theorem image_rho_words (N : ℕ) : (words N).image (fun w => rho N w.1 w.2.1 w.2.2.1 w.2.2.2) = Icc 1 (N.choose 4) := by
  have hinj : Set.InjOn (fun w : ℕ × ℕ × ℕ × ℕ => rho N w.1 w.2.1 w.2.2.1 w.2.2.2) (words N : Set (ℕ × ℕ × ℕ × ℕ)) := by
    intro w hw w' hw' h
    by_contra hne
    have h₁ := mem_words.1 (mem_coe.1 hw)
    have h₂ := mem_words.1 (mem_coe.1 hw')
    rcases lexLT_or_of_ne hne with hl | hl
    · exact absurd h (rho_lt_rho h₁ h₂ hl).ne
    · exact absurd h.symm (rho_lt_rho h₂ h₁ hl).ne
  refine eq_of_subset_of_card_le (fun x hx => ?_) ?_
  · obtain ⟨w, hw, rfl⟩ := mem_image.1 hx
    exact mem_Icc.2 ⟨one_le_rho (mem_words.1 hw), rho_le_choose _ _ _ _ _⟩
  · rw [card_image_of_injOn hinj, card_words, Nat.card_Icc]
    simp

/-- The table of binomial coefficients that the formula reads: `C(x, k)` for `x ≤ N`, `k ≤ 4`. -/
def binomialIndices (N : ℕ) : Finset (ℕ × ℕ) := range (N + 1) ×ˢ range 5

/-- **"Tabulating all binomial coefficients that might be needed in the formula in advance [...] requires time `O(N)`"**: `5 (N + 1)` entries, each the sum of two others by Pascal's rule (`Nat.choose_succ_succ`). -/
theorem card_binomialIndices (N : ℕ) : (binomialIndices N).card = 5 * (N + 1) := by
  simp [binomialIndices, mul_comm]

/-- The entries of the table that the formula reads. -/
def rhoReads (N a b c d : ℕ) : List (ℕ × ℕ) := [(N, 4), (N - a, 4), (N - b, 3), (N - c, 2), (N - d, 1)]

/-- **"After this, however, the index for any set of 4 taxa can be computed in time `O(1)`"**: five entries of the table. -/
theorem rho_reads (N a b c d : ℕ) :
    (rhoReads N a b c d).length = 5 ∧ ∀ r ∈ rhoReads N a b c d, r ∈ binomialIndices N := by
  refine ⟨rfl, fun r hr => ?_⟩
  simp only [rhoReads, List.mem_cons, List.not_mem_nil, or_false] at hr
  simp only [binomialIndices, mem_product, mem_range]
  rcases hr with rfl | rfl | rfl | rfl | rfl <;> simp <;> omega

end TINNiK
