module

public import External.MyersGriffiths2003.Algorithm1
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Dedup
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
public import Mathlib.Data.List.Range

/-!
# The algorithm of Hudson and Kaplan for `R_M`

Hudson and Kaplan 1985, Appendix 2 (p. 162), as a function of the matrix `D = (d(i, j))`. "To each nonzero element `d(i, j)` of `D` above the diagonal we associate the open interval `(i, j)` and form a list of these intervals ordered so that the starting points of the intervals are not decreasing." Then two deletions:

* "those that completely contain other intervals" (`deleteContaining`);
* "let `(i₁, j₁)` be the first interval that is not disjoint from all of the others. All intervals `(m, n)` such that `i₁ < m < j₁` are then deleted. Next, let `(i₂, j₂)` be the first interval with `i₂ ≥ j₁` such that `(i₂, j₂)` is not disjoint from all of the remaining intervals and delete all intervals whose first component is `< j₂` and `> i₂`. This process is continued until it is not possible to find an interval that has a nonempty intersection with some other interval on the list" (`sweep`).

"At this point all of the intervals are disjoint, and to each interval we must assign at least one recombination event. Hence, `R_M` equals the final number of intervals on the list." The value `R_M` is defined on p. 152 as "the minimum number of recombination events in the history of the sample which is consistent with the structure of `D`".

The sites are numbered from `0`, and from `1` in the source, as in `External.MyersGriffiths2003.Algorithm1`. "Consistent with the structure of `D`" is the integer program of Myers and Griffiths with `B_ij = d(i, j)`: at least one event in `(i, j)` when `d(i, j) = 1`, which is how they read this source (p. 378). What's proved:

* the final list is a sublist of the first, so it has pairs of sites with `d(i, j) = 1`, and its intervals are disjoint (`finalList_disjoint`): the source's claim;
* its length is the minimum, for the whole region and for the region up to any site (`hudsonKaplan_isOptimalValue`, `isOptimalValue_countUpTo`): the source's "hence", whose step the source leaves out, which is that each interval has a right endpoint hitting every interval deleted on its account (`exists_pierce`);
* no disjoint family of the first list is larger (`card_le_hudsonKaplan`), which the source doesn't state;
* it's the value of Algorithm 1 of Myers and Griffiths (`hudsonKaplan_eq_algorithm1`), and "the right endpoints of the disjoint intervals remaining in Hudson and Kaplan's method correspond exactly to the only nonzero values for `r_k`" of the vector from the top row (`rStarVec_ne_zero_iff`), as Myers and Griffiths say on p. 378-379;
* the eight cases of the source's Figure 1 (`figure1`), and "increasing `S` cannot decrease `R_M`" (`hudsonKaplan_comp_le`).

`External.HudsonKaplan1985.AlgorithmBound` has the value on a sample of sequences, as a lower bound on `R¹`.
-/

@[expose] public section

namespace HudsonKaplan1985

open Finset MyersGriffiths2003

/-! ### The function -/

/-- The list of Appendix 2: the open intervals `(i, j)` for the nonzero `d(i, j)` above the diagonal, on the sites `0, ..., S - 1`, with the starting points not decreasing. -/
def intervalList (S : ℕ) (d : ℕ → ℕ → Bool) : List (ℕ × ℕ) :=
  (List.range S).flatMap fun i => ((List.range S).filter fun j => decide (i < j) && d i j).map fun j => (i, j)

/-- The first deletion: "those that completely contain other intervals. For example, if `(i, j)` and `(m, n)` are on the list, and `m ≤ i < j ≤ n`, then `(m, n)` is deleted". -/
def deleteContaining (L : List (ℕ × ℕ)) : List (ℕ × ℕ) :=
  L.filter fun p => !L.any fun q => decide (q ≠ p) && decide (p.1 ≤ q.1) && decide (q.2 ≤ p.2)

/-- The open intervals `p` and `q`, which aren't empty, have a nonempty intersection. -/
def Meets (p q : ℕ × ℕ) : Prop := p.1 < q.2 ∧ q.1 < p.2

instance (p q : ℕ × ℕ) : Decidable (Meets p q) := inferInstanceAs (Decidable (_ ∧ _))

/-- "The first interval with `i ≥ a` such that it is not disjoint from all of the remaining intervals." The first time, `a` is `0`, so that it says nothing. -/
def firstMeeting (a : ℕ) (L : List (ℕ × ℕ)) : Option (ℕ × ℕ) :=
  L.find? fun p => decide (a ≤ p.1) && L.any fun q => decide (q ≠ p) && decide (Meets p q)

/-- "Delete all intervals whose first component is `< j` and `> i`". -/
def deleteStarts (p : ℕ × ℕ) (L : List (ℕ × ℕ)) : List (ℕ × ℕ) :=
  L.filter fun q => !(decide (p.1 < q.1) && decide (q.1 < p.2))

/-- The second deletion, by rounds, with a bound on their number: "this process is continued until it is not possible to find an interval that has a nonempty intersection with some other interval on the list". The number of intervals is enough (`sweep_length`). -/
def sweep : ℕ → ℕ → List (ℕ × ℕ) → List (ℕ × ℕ)
  | 0, _, L => L
  | n + 1, a, L =>
    match firstMeeting a L with
    | none => L
    | some p => sweep n p.2 (deleteStarts p L)

/-- **The final list of intervals of Appendix 2** (`ext:hk_final_list`). -/
def finalList (S : ℕ) (d : ℕ → ℕ → Bool) : List (ℕ × ℕ) :=
  sweep (deleteContaining (intervalList S d)).length 0 (deleteContaining (intervalList S d))

/-- **`R_M`, as computed by Appendix 2** (`ext:hk_algorithm`): "`R_M` equals the final number of intervals on the list". It's a computable function of `D`: `decide` evaluates it. -/
def hudsonKaplan (S : ℕ) (d : ℕ → ℕ → Bool) : ℕ := (finalList S d).length

/-- The local bounds of the four-gamete test, in the system of Myers and Griffiths: "`B_ij = 1` if sites `i` and `j` are incompatible ... and `B_ij = 0` otherwise". -/
def incompatBounds (d : ℕ → ℕ → Bool) : ℕ → ℕ → ℕ := fun i j => if d i j then 1 else 0

/-- The matrix `D` of a sample of sequences on the sites `0, ..., S - 1`: "`d(i, j) = 1` if all four gametes involving sites `i` and `j` are present in the sample; otherwise `d(i, j) = 0`". -/
def fourGamete {S : ℕ} (M : Finset (Fin S → Bool)) (i j : ℕ) : Bool :=
  if h : i < S ∧ j < S then decide (∀ a b : Bool, ∃ r ∈ M, r ⟨i, h.1⟩ = a ∧ r ⟨j, h.2⟩ = b) else false

/-! ### The first list -/

variable {S : ℕ} {d : ℕ → ℕ → Bool}

theorem mem_intervalList {p : ℕ × ℕ} : p ∈ intervalList S d ↔ p.1 < p.2 ∧ p.2 < S ∧ d p.1 p.2 = true := by
  obtain ⟨i, j⟩ := p
  simp only [intervalList, List.mem_flatMap, List.mem_range, List.mem_map, List.mem_filter, Bool.and_eq_true, decide_eq_true_eq,
    Prod.mk.injEq]
  constructor
  · rintro ⟨a, -, b, ⟨hb, hab, hd⟩, rfl, rfl⟩
    exact ⟨hab, hb, hd⟩
  · rintro ⟨hij, hj, hd⟩
    exact ⟨i, hij.trans hj, j, ⟨hj, hij, hd⟩, rfl, rfl⟩

/-- The first list is ordered by starting point, then by end point. -/
theorem intervalList_pairwise : (intervalList S d).Pairwise fun p q => p.1 < q.1 ∨ (p.1 = q.1 ∧ p.2 < q.2) := by
  rw [intervalList, List.pairwise_flatMap]
  refine ⟨fun i _ => ?_, ?_⟩
  · rw [List.pairwise_map]
    refine List.Pairwise.filter _ ?_
    refine List.pairwise_lt_range.imp fun h => Or.inr ⟨rfl, h⟩
  · refine List.pairwise_lt_range.imp fun {a b} hab x hx y hy => ?_
    obtain ⟨_, -, rfl⟩ := List.mem_map.1 hx
    obtain ⟨_, -, rfl⟩ := List.mem_map.1 hy
    exact Or.inl hab

/-! ### Lists with both ends increasing -/

/-- The state of the list after the first deletion: the intervals aren't empty, and both ends are strictly increasing. -/
structure Good (L : List (ℕ × ℕ)) : Prop where
  pos : ∀ p ∈ L, p.1 < p.2
  sorted : L.Pairwise fun p q => p.1 < q.1 ∧ p.2 < q.2

theorem Good.filter {L : List (ℕ × ℕ)} (h : Good L) (f : ℕ × ℕ → Bool) : Good (L.filter f) :=
  ⟨fun p hp => h.pos p (List.mem_of_mem_filter hp), h.sorted.filter f⟩

theorem Good.trichotomy {L : List (ℕ × ℕ)} (h : Good L) {p q : ℕ × ℕ} (hp : p ∈ L) (hq : q ∈ L) :
    p = q ∨ (p.1 < q.1 ∧ p.2 < q.2) ∨ (q.1 < p.1 ∧ q.2 < p.2) := by
  have hs := h.sorted
  clear h
  induction L with
  | nil => simp at hp
  | cons a L ih =>
    rw [List.pairwise_cons] at hs
    rcases List.mem_cons.1 hp with rfl | hp'
    · rcases List.mem_cons.1 hq with rfl | hq'
      · exact Or.inl rfl
      · exact Or.inr (Or.inl (hs.1 q hq'))
    · rcases List.mem_cons.1 hq with rfl | hq'
      · exact Or.inr (Or.inr (hs.1 p hp'))
      · exact ih hp' hq' hs.2

theorem deleteContaining_sublist (L : List (ℕ × ℕ)) : (deleteContaining L).Sublist L := List.filter_sublist

theorem mem_deleteContaining {L : List (ℕ × ℕ)} {p : ℕ × ℕ} :
    p ∈ deleteContaining L ↔ p ∈ L ∧ ∀ q ∈ L, q ≠ p → ¬ (p.1 ≤ q.1 ∧ q.2 ≤ p.2) := by
  simp only [deleteContaining, List.mem_filter, Bool.not_eq_true', List.any_eq_false, Bool.and_eq_true, decide_eq_true_eq, not_and, and_imp]

/-- After the first deletion, both ends increase. -/
theorem good_deleteContaining (S : ℕ) (d : ℕ → ℕ → Bool) : Good (deleteContaining (intervalList S d)) := by
  refine ⟨fun p hp => (mem_intervalList.1 (mem_deleteContaining.1 hp).1).1, ?_⟩
  refine List.Pairwise.imp_of_mem (R := fun p q => p.1 < q.1 ∨ (p.1 = q.1 ∧ p.2 < q.2)) (fun {p q} hp hq h => ?_)
    (intervalList_pairwise.filter _)
  have hp' := mem_deleteContaining.1 hp
  have hq' := mem_deleteContaining.1 hq
  rcases h with h | ⟨h₁, h₂⟩
  · refine ⟨h, ?_⟩
    by_contra hc
    refine hp'.2 q hq'.1 ?_ ⟨h.le, not_lt.1 hc⟩
    rintro rfl
    exact lt_irrefl _ h
  · exfalso
    refine hq'.2 p hp'.1 ?_ ⟨h₁.ge, h₂.le⟩
    rintro rfl
    exact lt_irrefl _ h₂

/-- An interval of the first list contains one that stays after the first deletion. -/
theorem exists_mem_deleteContaining {L : List (ℕ × ℕ)} (hpos : ∀ p ∈ L, p.1 < p.2) {q : ℕ × ℕ} (hq : q ∈ L) :
    ∃ p ∈ deleteContaining L, q.1 ≤ p.1 ∧ p.2 ≤ q.2 := by
  induction hn : q.2 - q.1 using Nat.strong_induction_on generalizing q with
  | _ n ih =>
    by_cases hmin : q ∈ deleteContaining L
    · exact ⟨q, hmin, le_rfl, le_rfl⟩
    · have hex : ∃ q' ∈ L, q' ≠ q ∧ q.1 ≤ q'.1 ∧ q'.2 ≤ q.2 := by
        by_contra hno
        push Not at hno
        refine hmin (mem_deleteContaining.2 ⟨hq, fun q' hq' hne hc => ?_⟩)
        exact absurd hc.2 (not_le.2 (hno q' hq' hne hc.1))
      obtain ⟨q', hq', hne, h₁, h₂⟩ := hex
      have hlen : q'.2 - q'.1 < n := by
        have hq'pos := hpos q' hq'
        have hqne : q'.1 ≠ q.1 ∨ q'.2 ≠ q.2 := by
          by_contra hc
          push Not at hc
          exact hne (Prod.ext hc.1 hc.2)
        omega
      obtain ⟨p, hp, h₃, h₄⟩ := ih _ hlen hq' rfl
      exact ⟨p, hp, h₁.trans h₃, h₄.trans h₂⟩

/-! ### One round of the second deletion -/

theorem Meets.symm {p q : ℕ × ℕ} (h : Meets p q) : Meets q p := ⟨h.2, h.1⟩

theorem deleteStarts_sublist (p : ℕ × ℕ) (L : List (ℕ × ℕ)) : (deleteStarts p L).Sublist L := List.filter_sublist

theorem mem_deleteStarts {p q : ℕ × ℕ} {L : List (ℕ × ℕ)} : q ∈ deleteStarts p L ↔ q ∈ L ∧ ¬ (p.1 < q.1 ∧ q.1 < p.2) := by
  simp only [deleteStarts, List.mem_filter, Bool.not_eq_true', Bool.and_eq_false_iff, decide_eq_false_iff_not, not_and_or]

theorem firstMeeting_eq_none {a : ℕ} {L : List (ℕ × ℕ)} (h : firstMeeting a L = none) :
    ∀ p ∈ L, a ≤ p.1 → ∀ q ∈ L, q ≠ p → ¬ Meets p q := by
  intro p hp ha q hq hne hm
  refine List.find?_eq_none.1 h p hp ?_
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.any_eq_true]
  exact ⟨ha, q, hq, hne, hm⟩

theorem firstMeeting_eq_some {a : ℕ} {L : List (ℕ × ℕ)} {p : ℕ × ℕ} (h : firstMeeting a L = some p) :
    p ∈ L ∧ a ≤ p.1 ∧ (∃ q ∈ L, q ≠ p ∧ Meets p q) ∧ ∃ as bs, L = as ++ p :: bs ∧ ∀ r ∈ as, a ≤ r.1 → ∀ q ∈ L, q ≠ r → ¬ Meets r q := by
  obtain ⟨h₁, as, bs, rfl, h₂⟩ := List.find?_eq_some_iff_append.1 h
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.any_eq_true] at h₁
  refine ⟨by simp, h₁.1, h₁.2, as, bs, rfl, fun r hr ha q hq hne hm => ?_⟩
  have := h₂ r hr
  simp only [Bool.not_eq_true', Bool.and_eq_false_iff, decide_eq_false_iff_not, List.any_eq_false] at this
  rcases this with h₃ | h₃
  · exact h₃ ha
  · have h₄ := h₃ q hq
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h₄
    exact h₄ ⟨hne, hm⟩

/-- What a list has before the sweep has reached the point `a`: the intervals starting before `a` meet no other. -/
def Swept (a : ℕ) (L : List (ℕ × ℕ)) : Prop := ∀ r ∈ L, r.1 < a → ∀ q ∈ L, q ≠ r → ¬ Meets r q

/-- One round: the first interval that meets another keeps its place, the list gets shorter, and what starts before its end point now meets nothing. -/
theorem step_spec {a : ℕ} {L : List (ℕ × ℕ)} {p : ℕ × ℕ} (hg : Good L) (hs : Swept a L) (h : firstMeeting a L = some p) :
    p ∈ deleteStarts p L ∧ (deleteStarts p L).length < L.length ∧ Swept p.2 (deleteStarts p L) := by
  obtain ⟨hp, hap, ⟨q₀, hq₀, hne₀, hm₀⟩, as, bs, hL, hfirst⟩ := firstMeeting_eq_some h
  have hsorted := hg.sorted
  rw [hL, List.pairwise_append, List.pairwise_cons] at hsorted
  have hpas : ∀ r ∈ as, r.1 < p.1 := fun r hr => (hsorted.2.2 r hr p (by simp)).1
  have hpbs : ∀ r ∈ bs, p.1 < r.1 := fun r hr => (hsorted.2.1.1 r hr).1
  -- An interval starting before `p` meets nothing.
  have hbefore : ∀ r ∈ L, r.1 < p.1 → ∀ q ∈ L, q ≠ r → ¬ Meets r q := by
    intro r hr hrp q hq hne
    by_cases hra : a ≤ r.1
    · have hras : r ∈ as := by
        rw [hL] at hr
        rcases List.mem_append.1 hr with h₁ | h₁
        · exact h₁
        · rcases List.mem_cons.1 h₁ with rfl | h₂
          · exact absurd hrp (lt_irrefl _)
          · exact absurd (hpbs r h₂) (not_lt.2 hrp.le)
      exact hfirst r hras hra q hq hne
    · exact hs r hr (not_le.1 hra) q hq hne
  -- An interval meeting `p` other than `p` starts after it.
  have hafter : ∀ q ∈ L, q ≠ p → Meets p q → p.1 < q.1 := by
    intro q hq hne hm
    by_contra hc
    rcases (not_lt.1 hc).eq_or_lt with heq | hlt
    · rcases hg.trichotomy hp hq with h₁ | h₁ | h₁
      · exact hne h₁.symm
      · omega
      · omega
    · exact hbefore q hq hlt p hp hne.symm hm.symm
  refine ⟨mem_deleteStarts.2 ⟨hp, fun h₁ => lt_irrefl _ h₁.1⟩, ?_, ?_⟩
  · refine List.length_filter_lt_length_iff_exists.2 ⟨q₀, hq₀, ?_⟩
    simp only [Bool.not_eq_true', Bool.and_eq_false_iff, decide_eq_false_iff_not, not_or, not_not]
    exact ⟨hafter q₀ hq₀ hne₀ hm₀, hm₀.2⟩
  · intro r hr hrp q hq hne hm
    obtain ⟨hr₁, hr₂⟩ := mem_deleteStarts.1 hr
    obtain ⟨hq₁, hq₂⟩ := mem_deleteStarts.1 hq
    rcases lt_trichotomy r.1 p.1 with hlt | heq | hgt
    · exact hbefore r hr₁ hlt q hq₁ hne hm
    · -- `r` is `p`.
      have hrpe : r = p := by
        rcases hg.trichotomy hr₁ hp with h₁ | h₁ | h₁
        · exact h₁
        · omega
        · omega
      subst hrpe
      rcases lt_trichotomy q.1 r.1 with h₁ | h₁ | h₁
      · exact hbefore q hq₁ h₁ r hp hne.symm hm.symm
      · rcases hg.trichotomy hq₁ hp with h₂ | h₂ | h₂
        · exact hne h₂
        · omega
        · omega
      · exact hq₂ ⟨h₁, hm.2⟩
    · exact hr₂ ⟨hgt, hrp⟩

/-- The list of a sweep is a sublist of what it starts with. -/
theorem sweep_sublist (n a : ℕ) (L : List (ℕ × ℕ)) : (sweep n a L).Sublist L := by
  induction n generalizing a L with
  | zero => exact List.Sublist.refl L
  | succ n ih =>
    unfold sweep
    split
    · exact List.Sublist.refl L
    · exact (ih _ _).trans (deleteStarts_sublist _ _)

/-- What starts before `a` is never deleted. -/
theorem mem_sweep_of_lt {n a : ℕ} {L : List (ℕ × ℕ)} (hg : Good L) {r : ℕ × ℕ} (hr : r ∈ L) (hra : r.1 < a) : r ∈ sweep n a L := by
  induction n generalizing a L with
  | zero => exact hr
  | succ n ih =>
    unfold sweep
    split
    · exact hr
    · rename_i p hsome
      obtain ⟨hp, hap, -⟩ := firstMeeting_eq_some hsome
      refine ih (hg.filter _) (mem_deleteStarts.2 ⟨hr, fun h => ?_⟩) ?_
      · omega
      · have := hg.pos p hp
        omega

/-- **Every interval has the right end point of a final one in it.** "To each interval we must assign at least one recombination event": what makes that a bound from above is that a final interval's event, put next to its right end point, also serves the intervals deleted on its account. The source leaves this step out. -/
theorem exists_pierce_sweep {n a : ℕ} {L : List (ℕ × ℕ)} (hg : Good L) {r : ℕ × ℕ} (hr : r ∈ L) :
    ∃ p ∈ sweep n a L, r.1 < p.2 ∧ p.2 ≤ r.2 := by
  induction n generalizing a L with
  | zero => exact ⟨r, hr, hg.pos r hr, le_rfl⟩
  | succ n ih =>
    unfold sweep
    split
    · exact ⟨r, hr, hg.pos r hr, le_rfl⟩
    · rename_i p hsome
      obtain ⟨hp, hap, -⟩ := firstMeeting_eq_some hsome
      by_cases hdel : p.1 < r.1 ∧ r.1 < p.2
      · refine ⟨p, mem_sweep_of_lt (hg.filter _) (mem_deleteStarts.2 ⟨hp, fun h => lt_irrefl _ h.1⟩) (hg.pos p hp), hdel.2, ?_⟩
        rcases hg.trichotomy hp hr with h₁ | h₁ | h₁
        · rw [h₁]
        · exact h₁.2.le
        · omega
      · exact ih (hg.filter _) (mem_deleteStarts.2 ⟨hr, hdel⟩)

/-- With enough rounds, the final intervals are disjoint. -/
theorem sweep_disjoint {n a : ℕ} {L : List (ℕ × ℕ)} (hg : Good L) (hs : Swept a L) (hn : L.length ≤ n) :
    ∀ p ∈ sweep n a L, ∀ q ∈ sweep n a L, q ≠ p → ¬ Meets p q := by
  induction n generalizing a L with
  | zero =>
    have : L = [] := List.length_eq_zero_iff.1 (by omega)
    subst this
    simp [sweep]
  | succ n ih =>
    unfold sweep
    split
    · rename_i hnone
      intro p hp q hq hne
      by_cases ha : a ≤ p.1
      · exact firstMeeting_eq_none hnone p hp ha q hq hne
      · exact hs p hp (not_le.1 ha) q hq hne
    · rename_i p hsome
      obtain ⟨-, hlt, hsw⟩ := step_spec hg hs hsome
      exact ih (hg.filter _) hsw (by omega)

theorem sweep_length {n a : ℕ} {L : List (ℕ × ℕ)} : (sweep n a L).length ≤ L.length := (sweep_sublist n a L).length_le

/-! ### The final list -/

/-- The final list has intervals of the first list. -/
theorem finalList_subset : ∀ p ∈ finalList S d, p ∈ intervalList S d := fun _ hp =>
  (deleteContaining_sublist _).subset ((sweep_sublist _ _ _).subset hp)

/-- **"At this point all of the intervals are disjoint"** (`ext:hk_disjoint`): open intervals, which can share an end point. -/
theorem finalList_disjoint : ∀ p ∈ finalList S d, ∀ q ∈ finalList S d, q ≠ p → p.2 ≤ q.1 ∨ q.2 ≤ p.1 := by
  intro p hp q hq hne
  have := sweep_disjoint (good_deleteContaining S d) (a := 0) (fun r _ h => absurd h (Nat.not_lt_zero _)) le_rfl p hp q hq hne
  unfold Meets at this
  omega

/-- Each interval of the first list has the right end point of a final interval in it, in the sense that the gap just before that point is in it. -/
theorem exists_pierce {q : ℕ × ℕ} (hq : q ∈ intervalList S d) : ∃ p ∈ finalList S d, q.1 < p.2 ∧ p.2 ≤ q.2 := by
  obtain ⟨q', hq', h₁, h₂⟩ := exists_mem_deleteContaining (L := intervalList S d) (fun p hp => (mem_intervalList.1 hp).1) hq
  obtain ⟨p, hp, h₃, h₄⟩ := exists_pierce_sweep (n := (deleteContaining (intervalList S d)).length) (a := 0) (good_deleteContaining S d) hq'
  exact ⟨p, hp, by omega, h₄.trans h₂⟩

theorem finalList_nodup (S : ℕ) (d : ℕ → ℕ → Bool) : (finalList S d).Nodup := by
  have hg : Good (finalList S d) := ⟨fun p hp => (mem_intervalList.1 (finalList_subset p hp)).1,
    List.Pairwise.sublist (sweep_sublist _ _ _) (good_deleteContaining S d).sorted⟩
  exact hg.sorted.imp fun h heq => by
    rw [heq] at h
    exact lt_irrefl _ h.1

/-! ### The minimum -/

/-- The number of final intervals with right end point at or before `k`. -/
def countUpTo (S : ℕ) (d : ℕ → ℕ → Bool) (k : ℕ) : ℕ := (finalList S d).countP fun p => decide (p.2 ≤ k)

/-- The placement of events: one just before the right end point of each final interval. -/
def eventVector (S : ℕ) (d : ℕ → ℕ → Bool) (l : ℕ) : ℕ := (finalList S d).countP fun p => decide (p.2 - 1 = l)

/-- The events of `eventVector` before `k`. -/
theorem sum_countP (F : List (ℕ × ℕ)) (hF : ∀ p ∈ F, 1 ≤ p.2) (k : ℕ) :
    ∑ l ∈ range k, F.countP (fun p => decide (p.2 - 1 = l)) = F.countP fun p => decide (p.2 ≤ k) := by
  induction F with
  | nil => simp
  | cons a F ih =>
    have ih' := ih fun p hp => hF p (List.mem_cons_of_mem _ hp)
    have ha := hF a List.mem_cons_self
    simp only [List.countP_cons, sum_add_distrib, ih', add_right_inj]
    have hsum : ∑ l ∈ range k, (if decide (a.2 - 1 = l) = true then 1 else 0) = if a.2 - 1 ∈ range k then 1 else 0 := by
      simp only [decide_eq_true_eq]
      exact sum_ite_eq (range k) (a.2 - 1) fun _ => 1
    rw [hsum]
    simp only [mem_range, decide_eq_true_eq]
    congr 1
    apply propext
    omega

theorem sum_eventVector (k : ℕ) : ∑ l ∈ range k, eventVector S d l = countUpTo S d k :=
  sum_countP _ (fun p hp => by have := (mem_intervalList.1 (finalList_subset p hp)).1; omega) k

/-- The placement satisfies the four-gamete bounds. -/
theorem eventVector_feasible : Feasible S (incompatBounds d) (eventVector S d) := by
  intro i j hij hj
  unfold incompatBounds
  split_ifs with hd
  · have hq : (i, j) ∈ intervalList S d := mem_intervalList.2 ⟨hij, hj, hd⟩
    obtain ⟨p, hp, h₁, h₂⟩ := exists_pierce hq
    simp only at h₁ h₂
    have hl : p.2 - 1 ∈ Ico i j := mem_Ico.2 ⟨by omega, by omega⟩
    refine le_trans ?_ (single_le_sum (f := eventVector S d) (fun _ _ => Nat.zero_le _) hl)
    exact List.countP_pos_iff.2 ⟨p, hp, by simp⟩
  · exact Nat.zero_le _

/-- **Disjoint intervals need separate events** ("to each interval we must assign at least one recombination event"). A family of pairwise disjoint intervals, in the region up to `k`, each with at least one event, has at most as many elements as there are events before `k`. -/
theorem card_le_sum_of_disjoint {P : Finset (ℕ × ℕ)} {r : ℕ → ℕ} {k : ℕ} (hk : ∀ p ∈ P, p.2 ≤ k) (h₁ : ∀ p ∈ P, 1 ≤ ∑ l ∈ Ico p.1 p.2, r l)
    (hdisj : ∀ p ∈ P, ∀ q ∈ P, q ≠ p → p.2 ≤ q.1 ∨ q.2 ≤ p.1) : P.card ≤ ∑ l ∈ range k, r l := by
  have hpd : (P : Set (ℕ × ℕ)).PairwiseDisjoint fun p => Ico p.1 p.2 := by
    intro p hp q hq hne
    refine disjoint_left.2 fun x hx hx' => ?_
    obtain ⟨hx₁, hx₂⟩ := mem_Ico.1 hx
    obtain ⟨hx₃, hx₄⟩ := mem_Ico.1 hx'
    have := hdisj p hp q hq (Ne.symm hne)
    omega
  calc P.card = ∑ _p ∈ P, 1 := by simp
    _ ≤ ∑ p ∈ P, ∑ l ∈ Ico p.1 p.2, r l := sum_le_sum h₁
    _ = ∑ l ∈ P.biUnion (fun p => Ico p.1 p.2), r l := (sum_biUnion hpd).symm
    _ ≤ ∑ l ∈ range k, r l := by
      refine sum_le_sum_of_subset fun x hx => ?_
      obtain ⟨p, hp, hxp⟩ := mem_biUnion.1 hx
      exact mem_range.2 ((mem_Ico.1 hxp).2.trans_le (hk p hp))

/-- The filtered final list, as a finite set. -/
theorem countUpTo_eq_card (k : ℕ) : countUpTo S d k = ((finalList S d).filter fun p => decide (p.2 ≤ k)).toFinset.card := by
  rw [List.toFinset_card_of_nodup ((finalList_nodup S d).filter _)]
  exact List.countP_eq_length_filter

/-- **The minimum of events in the region up to any site** (`ext:hk_optimal_region`): the number of final intervals in that region. -/
theorem isOptimalValue_countUpTo : ∀ k, IsOptimalValue S (incompatBounds d) 0 k (countUpTo S d k) := by
  intro k
  refine ⟨⟨eventVector S d, eventVector_feasible, ?_⟩, ?_⟩
  · change ∑ l ∈ Ico 0 k, eventVector S d l = _
    rw [Nat.Ico_zero_eq_range, sum_eventVector]
  · rintro _ ⟨r, hr, rfl⟩
    change _ ≤ ∑ l ∈ Ico 0 k, r l
    rw [Nat.Ico_zero_eq_range, countUpTo_eq_card]
    refine card_le_sum_of_disjoint (fun p hp => ?_) (fun p hp => ?_) (fun p hp q hq hne => ?_)
    · have := (List.mem_filter.1 (List.mem_toFinset.1 hp)).2
      simpa using this
    · have hp' := mem_intervalList.1 (finalList_subset p (List.mem_filter.1 (List.mem_toFinset.1 hp)).1)
      have := hr p.1 p.2 hp'.1 hp'.2.1
      unfold incompatBounds at this
      rwa [ite_eq_left hp'.2.2] at this
    · exact finalList_disjoint p (List.mem_filter.1 (List.mem_toFinset.1 hp)).1 q (List.mem_filter.1 (List.mem_toFinset.1 hq)).1 hne

theorem countUpTo_eq_length {k : ℕ} (hk : S ≤ k + 1) : countUpTo S d k = hudsonKaplan S d := by
  unfold countUpTo hudsonKaplan
  rw [List.countP_eq_length_filter, List.filter_eq_self.2]
  intro p hp
  have := (mem_intervalList.1 (finalList_subset p hp)).2.1
  simp only [decide_eq_true_eq]
  omega

/-- **`R_M` equals the final number of intervals on the list** (`ext:hk_optimal`): the length of the final list is "the minimum number of recombination events in the history of the sample which is consistent with the structure of `D`". -/
theorem hudsonKaplan_isOptimalValue (hS : 0 < S) : IsOptimalValue S (incompatBounds d) 0 (S - 1) (hudsonKaplan S d) := by
  have := isOptimalValue_countUpTo (S := S) (d := d) (S - 1)
  rwa [countUpTo_eq_length (by omega)] at this

/-- **The two methods lead to the same bound** (`ext:hk_eq_mg`; Myers and Griffiths 2003, p. 378): with the bounds of the four-gamete test, the value of Algorithm 1 is the number of intervals on Hudson and Kaplan's list. -/
theorem hudsonKaplan_eq_algorithm1 (hS : 0 < S) : hudsonKaplan S d = algorithm1 (incompatBounds d) S 0 (S - 1) :=
  (hudsonKaplan_isOptimalValue hS).unique (algorithm1_isOptimalValue _ (Nat.zero_le _) (by omega))

/-- The top row of Algorithm 1, with the bounds of the four-gamete test, counts the final intervals. -/
theorem algorithm1_eq_countUpTo {k : ℕ} (hk : k < S) : algorithm1 (incompatBounds d) S 0 k = countUpTo S d k :=
  (algorithm1_isOptimalValue _ (Nat.zero_le _) hk).unique (isOptimalValue_countUpTo k)

/-- The vector from the top row counts the final intervals with a given right end point. -/
theorem rStarVec_eq_countP {k : ℕ} (hk : k + 1 < S) :
    rStarVec (incompatBounds d) k = (finalList S d).countP fun p => decide (p.2 = k + 1) := by
  rw [rStarVec_eq_sub _ hk, algorithm1_eq_countUpTo hk, algorithm1_eq_countUpTo (Nat.lt_of_succ_lt hk)]
  have h₁ : countUpTo S d (k + 1) = countUpTo S d k + eventVector S d k := by
    rw [← sum_eventVector, ← sum_eventVector, sum_range_succ]
  rw [h₁, Nat.add_sub_cancel_left]
  unfold eventVector
  refine List.countP_congr fun p hp => ?_
  have := (mem_intervalList.1 (finalList_subset p hp)).1
  simp only [decide_eq_true_eq]
  omega

/-- **The right end points** (`ext:mg_right_endpoints`; Myers and Griffiths 2003, pp. 378-379): "the right endpoints of the disjoint intervals remaining in Hudson and Kaplan's method correspond exactly to the only nonzero values for `r_k` obtained in evaluating the particular optimal solution from the top row". -/
theorem rStarVec_ne_zero_iff {k : ℕ} (hk : k + 1 < S) : rStarVec (incompatBounds d) k ≠ 0 ↔ ∃ p ∈ finalList S d, p.2 = k + 1 := by
  rw [rStarVec_eq_countP hk, ← Nat.pos_iff_ne_zero, List.countP_pos_iff]
  simp only [decide_eq_true_eq]

/-- **The final list is a largest disjoint family** (`ext:hk_maximal`). No set of pairwise disjoint intervals with `d(i, j) = 1` is larger. The source doesn't say this, and it follows from what it says, once `R_M` is the minimum. -/
theorem card_le_hudsonKaplan (hS : 0 < S) {P : Finset (ℕ × ℕ)} (hP : ∀ p ∈ P, p ∈ intervalList S d)
    (hdisj : ∀ p ∈ P, ∀ q ∈ P, q ≠ p → p.2 ≤ q.1 ∨ q.2 ≤ p.1) : P.card ≤ hudsonKaplan S d := by
  rw [← countUpTo_eq_length (k := S - 1) (by omega), ← sum_eventVector]
  refine card_le_sum_of_disjoint (fun p hp => ?_) (fun p hp => ?_) hdisj
  · have := (mem_intervalList.1 (hP p hp)).2.1
    omega
  · have hp' := mem_intervalList.1 (hP p hp)
    have := eventVector_feasible (S := S) (d := d) p.1 p.2 hp'.1 hp'.2.1
    unfold incompatBounds at this
    rwa [ite_eq_left hp'.2.2] at this

/-- **"It is clear from the definition of `R_M` that increasing `S` cannot decrease `R_M`"** (`ext:hk_monotone`, p. 153): `R_M` of a subset of the sites is at most that of the sites. -/
theorem hudsonKaplan_comp_le {S' : ℕ} (hS : 0 < S) {f : ℕ → ℕ} (hf : StrictMono f) (hfS : ∀ i, i < S' → f i < S) :
    hudsonKaplan S' (fun i j => d (f i) (f j)) ≤ hudsonKaplan S d := by
  set F := finalList S' (fun i j => d (f i) (f j)) with hF
  have hinj : Function.Injective fun p : ℕ × ℕ => (f p.1, f p.2) := fun p q h => by
    simp only [Prod.mk.injEq] at h
    exact Prod.ext (hf.injective h.1) (hf.injective h.2)
  have hcard : (F.toFinset.image fun p : ℕ × ℕ => (f p.1, f p.2)).card = hudsonKaplan S' (fun i j => d (f i) (f j)) := by
    rw [card_image_of_injective _ hinj, List.toFinset_card_of_nodup (finalList_nodup _ _)]
    rfl
  rw [← hcard]
  refine card_le_hudsonKaplan hS (fun p hp => ?_) (fun p hp q hq hne => ?_)
  · obtain ⟨a, ha, rfl⟩ := mem_image.1 hp
    have ha' := mem_intervalList.1 (finalList_subset a (List.mem_toFinset.1 ha))
    exact mem_intervalList.2 ⟨hf ha'.1, hfS _ ha'.2.1, ha'.2.2⟩
  · obtain ⟨a, ha, rfl⟩ := mem_image.1 hp
    obtain ⟨b, hb, rfl⟩ := mem_image.1 hq
    have hab : b ≠ a := fun h => hne (by rw [h])
    rcases finalList_disjoint a (List.mem_toFinset.1 ha) b (List.mem_toFinset.1 hb) hab with h | h
    · exact Or.inl (hf.monotone h)
    · exact Or.inr (hf.monotone h)

/-! ### Figure 1 of the source -/

/-- The matrix `D` on three sites, from `d(1, 2)`, `d(1, 3)`, `d(2, 3)`. -/
def threeSites (a b c : Bool) : ℕ → ℕ → Bool := fun i j =>
  if i = 0 ∧ j = 1 then a else if i = 0 ∧ j = 2 then b else if i = 1 ∧ j = 2 then c else false

/-- **Figure 1** (`ext:hk_figure1`). "In case (1) there is no evidence of recombination and, therefore, `R_M = 0`. For cases (2) through (6) only one event is needed ...; for cases (7) and (8) two recombination events are required." The cases (7), (8) are those with `d(1, 2) = d(2, 3) = 1`. -/
theorem figure1 (a b c : Bool) :
    hudsonKaplan 3 (threeSites a b c) = if a && c then 2 else if a || b || c then 1 else 0 := by
  revert a b c
  decide +kernel

end HudsonKaplan1985
