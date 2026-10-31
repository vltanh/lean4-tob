module

public import TOBQMC.Consistency

/-!
# TOB-QMC §4.3: the bipartition search (Algorithm 2) combined with 3-fix-1-alter

TOB-QMC (`notes/paper2025/v5.txt`, embedded lines 616-623): "This motivated us to implement a 3f1a-like algorithm that
tests taxa around the induced bipartition [...] until a predetermined number of tests have been performed (see
Algorithm 2 in the Supplement). [...] Lastly, we note that combining the bipartition search heuristic with 3f1a yields
a consistent method for level-1 networks and does not increase time complexity."

## The search

Algorithm 2 (`notes/paper2025/tob-qmc_supp.txt`, lines 654-676) is written out as a function, with its "random" picks
a parameter `pick`, its tie-breaking at the `argmin` a parameter `argmin`, and its iteration limit a parameter
`limit`: `neighbours` is lines 7-9, `repeatLoop` lines 6-13, `whileLoop` lines 4-14, `bipartitionSearch` the whole,
`SearchOut.pValue` line 15. The counter `i` is the printed one, and `SearchOut.restarts` counts the executions of line
5.

Three repairs of the printed pseudocode, none affecting the claim:

* On a repeat of line 6 the tuple `(a₁, a₂, b₁, b₂)` must be the current `qmin`; the printed text never reassigns it,
  and if it stayed fixed, the second pass would find nothing new and the loop would be vacuous. Here it is `qmin`.
* With `|A| = |B| = 2` (so `n = 4`), `N` is empty, line 10 has no minimizer, and `i` never grows, so line 4 never
  exits as printed. Here the search stops after testing the one quartet.
* Line 12 needs the p-value of the tuple picked at line 5, so that tuple is tested too, and `i` does not count it.

## The test count

`i` may pass the limit by the last `|N|`, and the tests at line 5 are not in `i`: `SearchOut.card_testedSets_le` says
the search calls the test on at most `2 * limit + 2 * (n - 4)` four-taxon sets, more exactly `i + restarts` times,
with `i ≤ limit + 2 * (n - 4)` and `restarts ≤ limit`. Hence `(n - 3) + 2 * limit + 2 * (n - 4)` per edge together
with 3f1a (`card_threeFixOneAlter_union_testedSets_le`).

## Consistency

* A true edge is not contracted by anything the search adds: every 4-taxon set around the bipartition of a cut edge is
  treelike (`Level1.isTreelike_of_hasCutSplit`, Lemma 2), even if it draws two taxa from a block of the
  multipartition.
* A false edge is contracted because of the disjoint cover: Theorem 2 (`contractSides_cover_union_eq`).
* The search alone gives no such guarantee, and it plays no part in the proof beyond this: it only adds rejections,
  and they are right.

So `consistency_search` holds for all picks, and so does `consistency_threeFixOneAlter_search` with the cover of 3f1a.
-/

@[expose] public noncomputable section

open Phylogenetics Phylogenetics.RootedNetwork Finset Filter Topology
open scoped Classical

namespace TOBQMC

variable {V E X : Type*}

/-- The tuple `(a₁, a₂, b₁, b₂)` of Algorithm 2. -/
abbrev SearchTuple (X : Type*) := X × X × X × X

namespace SearchTuple

variable [DecidableEq X]

/-- The four-taxon set of a tuple. -/
def taxa (t : SearchTuple X) : Finset X := {t.1, t.2.1, t.2.2.1, t.2.2.2}

/-- Line 5: `a₁, a₂` in `A` and `b₁, b₂` in its complement, each pair distinct. -/
structure IsAround (A : Finset X) (t : SearchTuple X) : Prop where
  a₁_mem : t.1 ∈ A
  a₂_mem : t.2.1 ∈ A
  a_ne : t.1 ≠ t.2.1
  b₁_notMem : t.2.2.1 ∉ A
  b₂_notMem : t.2.2.2 ∉ A
  b_ne : t.2.2.1 ≠ t.2.2.2

omit [DecidableEq X] in
/-- The two pairs of a tuple have no common taxon. -/
theorem IsAround.card_taxa [DecidableEq X] {A : Finset X} {t : SearchTuple X} (h : t.IsAround A) : t.taxa.card = 4 := by
  obtain ⟨a₁, a₂, b₁, b₂⟩ := t
  obtain ⟨h₁, h₂, ha, h₃, h₄, hb⟩ := h
  simp only at h₁ h₂ ha h₃ h₄ hb
  have h13 : a₁ ≠ b₁ := fun h => h₃ (h ▸ h₁)
  have h14 : a₁ ≠ b₂ := fun h => h₄ (h ▸ h₁)
  have h23 : a₂ ≠ b₁ := fun h => h₃ (h ▸ h₂)
  have h24 : a₂ ≠ b₂ := fun h => h₄ (h ▸ h₂)
  simp [taxa, ha, h13, h14, h23, h24, hb]

end SearchTuple

variable [Fintype X] [DecidableEq X]

/-- Lines 7-9: the tuples `N` tested from `(a₁, a₂, b₁, b₂)`. -/
def neighbours (A : Finset X) (t : SearchTuple X) : Finset (SearchTuple X) :=
  ((A \ {t.1, t.2.1}).biUnion fun a' => {(a', t.1, t.2.2.1, t.2.2.2), (a', t.2.1, t.2.2.1, t.2.2.2)}) ∪
    ((Aᶜ \ {t.2.2.1, t.2.2.2}).biUnion fun b' => {(t.1, t.2.1, b', t.2.2.1), (t.1, t.2.1, b', t.2.2.2)})

/-- A selection of minimizers of `p`: line 10's `argmin`. Ties are not resolved by the paper, and the results hold for
every selection. -/
def IsArgmin (p : SearchTuple X → ℝ) (argmin : Finset (SearchTuple X) → SearchTuple X) : Prop :=
  ∀ S : Finset (SearchTuple X), S.Nonempty → argmin S ∈ S ∧ ∀ t ∈ S, p (argmin S) ≤ p t

omit [Fintype X] [DecidableEq X] in
/-- Every function has a selection of minimizers. -/
theorem exists_isArgmin [Nonempty X] (p : SearchTuple X → ℝ) : ∃ argmin, IsArgmin p argmin := by
  have h : ∀ S : Finset (SearchTuple X), ∃ m : SearchTuple X, S.Nonempty → m ∈ S ∧ ∀ t ∈ S, p m ≤ p t := by
    intro S
    by_cases hS : S.Nonempty
    · obtain ⟨m, hm, hmin⟩ := S.exists_min_image p hS
      exact ⟨m, fun _ => ⟨hm, hmin⟩⟩
    · exact ⟨Classical.arbitrary _, fun h => absurd h hS⟩
  choose argmin hargmin using h
  exact ⟨argmin, fun S hS => hargmin S hS⟩

/-- The state at the exit of the loop of lines 6-13. -/
structure RepeatOut (X : Type*) where
  qmin : SearchTuple X
  i : ℕ
  tested : Finset (SearchTuple X)

/-- Lines 6-13, from the tuple `qmin`, the counter `i` and the tuples `tested` already tested. The body runs at least
once; it repeats when `qmin` was updated and `i` is not above the limit. -/
def repeatLoop (A : Finset X) (p : SearchTuple X → ℝ) (argmin : Finset (SearchTuple X) → SearchTuple X) (limit : ℕ)
    (qmin : SearchTuple X) (i : ℕ) (tested : Finset (SearchTuple X)) : RepeatOut X :=
  if _h : (neighbours A qmin).Nonempty then
    if p (argmin (neighbours A qmin)) < p qmin then
      if i + (neighbours A qmin).card ≤ limit then
        repeatLoop A p argmin limit (argmin (neighbours A qmin)) (i + (neighbours A qmin).card)
          (tested ∪ neighbours A qmin)
      else ⟨argmin (neighbours A qmin), i + (neighbours A qmin).card, tested ∪ neighbours A qmin⟩
    else ⟨qmin, i + (neighbours A qmin).card, tested ∪ neighbours A qmin⟩
  else ⟨qmin, i, tested⟩
termination_by limit + 1 - i
decreasing_by
  have := Finset.card_pos.mpr ‹(neighbours A qmin).Nonempty›
  omega

section Neighbours

variable {A : Finset X} {t : SearchTuple X}

/-- Lines 8-9 keep two taxa on each side: every tuple tested is around the bipartition. -/
theorem SearchTuple.IsAround.neighbours (h : t.IsAround A) {n : SearchTuple X} (hn : n ∈ neighbours A t) :
    n.IsAround A := by
  obtain ⟨a₁, a₂, b₁, b₂⟩ := t
  obtain ⟨h₁, h₂, ha, h₃, h₄, hb⟩ := h
  simp only at h₁ h₂ ha h₃ h₄ hb
  rcases mem_union.mp hn with hn | hn
  · obtain ⟨a', ha', hn⟩ := mem_biUnion.mp hn
    obtain ⟨ha'A, ha'p⟩ := mem_sdiff.mp ha'
    have hne₁ : a' ≠ a₁ := fun h => ha'p (by simp [h])
    have hne₂ : a' ≠ a₂ := fun h => ha'p (by simp [h])
    rcases mem_insert.mp hn with rfl | hn
    · exact ⟨ha'A, h₁, hne₁, h₃, h₄, hb⟩
    · rw [mem_singleton.mp hn]
      exact ⟨ha'A, h₂, hne₂, h₃, h₄, hb⟩
  · obtain ⟨b', hb', hn⟩ := mem_biUnion.mp hn
    obtain ⟨hb'A, hb'p⟩ := mem_sdiff.mp hb'
    have hne₁ : b' ≠ b₁ := fun h => hb'p (by simp [h])
    have hne₂ : b' ≠ b₂ := fun h => hb'p (by simp [h])
    rcases mem_insert.mp hn with rfl | hn
    · exact ⟨h₁, h₂, ha, mem_compl.mp hb'A, h₃, hne₁⟩
    · rw [mem_singleton.mp hn]
      exact ⟨h₁, h₂, ha, mem_compl.mp hb'A, h₄, hne₂⟩

/-- `|N| ≤ 2 (|A| - 2) + 2 (|B| - 2) = 2 (n - 4)`. -/
theorem SearchTuple.IsAround.card_neighbours_le (h : t.IsAround A) :
    (TOBQMC.neighbours A t).card ≤ 2 * (Fintype.card X - 4) := by
  obtain ⟨a₁, a₂, b₁, b₂⟩ := t
  obtain ⟨h₁, h₂, ha, h₃, h₄, hb⟩ := h
  simp only at h₁ h₂ ha h₃ h₄ hb
  have hsubA : ({a₁, a₂} : Finset X) ⊆ A := by
    intro x hx
    rcases mem_insert.mp hx with rfl | hx
    · exact h₁
    · exact mem_singleton.mp hx ▸ h₂
  have hsubB : ({b₁, b₂} : Finset X) ⊆ Aᶜ := by
    intro x hx
    rcases mem_insert.mp hx with rfl | hx
    · exact mem_compl.mpr h₃
    · exact mem_compl.mpr (mem_singleton.mp hx ▸ h₄)
  have hcA := card_le_card hsubA
  have hcB := card_le_card hsubB
  rw [card_pair ha] at hcA
  rw [card_pair hb] at hcB
  have hu₁ := card_biUnion_le_card_mul (A \ {a₁, a₂})
    (fun a' => ({(a', a₁, b₁, b₂), (a', a₂, b₁, b₂)} : Finset (SearchTuple X))) 2 (fun _ _ => card_le_two)
  have hu₂ := card_biUnion_le_card_mul (Aᶜ \ {b₁, b₂})
    (fun b' => ({(a₁, a₂, b', b₁), (a₁, a₂, b', b₂)} : Finset (SearchTuple X))) 2 (fun _ _ => card_le_two)
  rw [card_sdiff_of_subset hsubA, card_pair ha] at hu₁
  rw [card_sdiff_of_subset hsubB, card_pair hb] at hu₂
  have htot := card_add_card_compl A
  refine (card_union_le _ _).trans ?_
  simp only at hu₁ hu₂ ⊢
  omega

omit [Fintype X] in
/-- The set of a tuple is one around the bipartition: two taxa on each side. -/
theorem SearchTuple.IsAround.card_inter_taxa (h : t.IsAround A) : (A ∩ t.taxa).card = 2 := by
  have heq : A ∩ t.taxa = {t.1, t.2.1} := by
    ext x
    simp only [SearchTuple.taxa, mem_inter, mem_insert, mem_singleton]
    constructor
    · rintro ⟨hx, rfl | rfl | rfl | rfl⟩
      · exact Or.inl rfl
      · exact Or.inr rfl
      · exact absurd hx h.b₁_notMem
      · exact absurd hx h.b₂_notMem
    · rintro (rfl | rfl)
      · exact ⟨h.a₁_mem, Or.inl rfl⟩
      · exact ⟨h.a₂_mem, Or.inr (Or.inl rfl)⟩
  rw [heq, card_pair h.a_ne]

/-- A tuple around `A` is a quartet tree of `bipartitionQuartets A`: this is ECToBlob's `Sbi(e)`. -/
theorem SearchTuple.IsAround.exists_mem_bipartitionQuartets (h : t.IsAround A) :
    ∃ s ∈ bipartitionQuartets A, s.taxa = t.taxa := by
  have hc := h.card_taxa
  refine ⟨quartetOfCherry t.taxa (A ∩ t.taxa) hc inter_subset_right h.card_inter_taxa,
    mem_filter.mpr ⟨mem_univ _, ?_⟩, quartetOfCherry_taxa _ _ _ _ _⟩
  simp

/-- The side of an internal edge has a tuple around it. -/
theorem exists_isAround {T : Finset (Finset X)} (hA : A ∈ internalSides T) :
    ∃ t : SearchTuple X, t.IsAround A := by
  obtain ⟨-, h₁, h₂⟩ := mem_filter.mp hA
  obtain ⟨a₁, ha₁, a₂, ha₂, ha⟩ := one_lt_card.mp (by omega : 1 < A.card)
  obtain ⟨b₁, hb₁, b₂, hb₂, hb⟩ := one_lt_card.mp (by omega : 1 < Aᶜ.card)
  exact ⟨(a₁, a₂, b₁, b₂), ha₁, ha₂, ha, mem_compl.mp hb₁, mem_compl.mp hb₂, hb⟩

end Neighbours

section RepeatLoop

variable {A : Finset X} {p : SearchTuple X → ℝ} {argmin : Finset (SearchTuple X) → SearchTuple X} {limit : ℕ}

/-- The counter does not decrease. -/
theorem le_i_repeatLoop (qmin : SearchTuple X) (i : ℕ) (tested : Finset (SearchTuple X)) :
    i ≤ (repeatLoop A p argmin limit qmin i tested).i := by
  fun_induction repeatLoop A p argmin limit qmin i tested
  all_goals try dsimp only
  all_goals omega

/-- With tuples to test, the counter grows. -/
theorem lt_i_repeatLoop {qmin : SearchTuple X} {i : ℕ} (tested : Finset (SearchTuple X))
    (h : (neighbours A qmin).Nonempty) : i < (repeatLoop A p argmin limit qmin i tested).i := by
  have hc := Finset.card_pos.mpr h
  rw [repeatLoop]
  simp only [h, ↓reduceDIte]
  split_ifs
  · exact lt_of_lt_of_le (by omega) (le_i_repeatLoop _ _ _)
  · dsimp only
    omega
  · dsimp only
    omega

/-- Nothing tested is forgotten. -/
theorem subset_tested_repeatLoop (qmin : SearchTuple X) (i : ℕ) (tested : Finset (SearchTuple X)) :
    tested ⊆ (repeatLoop A p argmin limit qmin i tested).tested := by
  fun_induction repeatLoop A p argmin limit qmin i tested
  case case1 ih => exact subset_union_left.trans ih
  case case2 => exact subset_union_left
  case case3 => exact subset_union_left
  case case4 => exact Subset.refl _

/-- Each pass adds at most `|N|` tuples, and adds `|N|` to `i`. -/
theorem card_tested_repeatLoop_le (qmin : SearchTuple X) (i : ℕ) (tested : Finset (SearchTuple X)) :
    (repeatLoop A p argmin limit qmin i tested).tested.card + i ≤
      tested.card + (repeatLoop A p argmin limit qmin i tested).i := by
  fun_induction repeatLoop A p argmin limit qmin i tested
  case case1 qmin i tested _ _ _ ih =>
    have := card_union_le tested (neighbours A qmin)
    omega
  case case2 qmin i tested _ _ _ =>
    have := card_union_le tested (neighbours A qmin)
    dsimp only
    omega
  case case3 qmin i tested _ _ =>
    have := card_union_le tested (neighbours A qmin)
    dsimp only
    omega
  case case4 =>
    exact le_of_eq rfl

/-- From tuples around `A`, the loop stays around `A`. -/
theorem isAround_repeatLoop (hargmin : IsArgmin p argmin) {qmin : SearchTuple X} {i : ℕ}
    {tested : Finset (SearchTuple X)} (hq : qmin.IsAround A) (ht : ∀ t ∈ tested, t.IsAround A) :
    (repeatLoop A p argmin limit qmin i tested).qmin.IsAround A ∧
      ∀ t ∈ (repeatLoop A p argmin limit qmin i tested).tested, t.IsAround A := by
  fun_induction repeatLoop A p argmin limit qmin i tested
  case case1 qmin i tested hne _ _ ih =>
    refine ih (hq.neighbours (hargmin _ hne).1) fun t ht' => ?_
    rcases mem_union.mp ht' with h | h
    · exact ht t h
    · exact hq.neighbours h
  case case2 qmin i tested hne _ _ =>
    refine ⟨hq.neighbours (hargmin _ hne).1, fun t ht' => ?_⟩
    rcases mem_union.mp ht' with h | h
    · exact ht t h
    · exact hq.neighbours h
  case case3 qmin i tested _ _ =>
    refine ⟨hq, fun t ht' => ?_⟩
    rcases mem_union.mp ht' with h | h
    · exact ht t h
    · exact hq.neighbours h
  case case4 => exact ⟨hq, ht⟩

/-- `i` passes the limit by at most the last `|N|`. -/
theorem i_repeatLoop_le (hargmin : IsArgmin p argmin) {qmin : SearchTuple X} {i : ℕ}
    {tested : Finset (SearchTuple X)} (hq : qmin.IsAround A) (hi : i ≤ limit) :
    (repeatLoop A p argmin limit qmin i tested).i ≤ limit + 2 * (Fintype.card X - 4) := by
  fun_induction repeatLoop A p argmin limit qmin i tested
  case case1 qmin i tested hne _ hle ih =>
    exact ih (hq.neighbours (hargmin _ hne).1) hle
  case case2 =>
    have := hq.card_neighbours_le
    dsimp only
    omega
  case case3 =>
    have := hq.card_neighbours_le
    dsimp only
    omega
  case case4 =>
    dsimp only
    omega

/-- **The tuple the loop returns is a minimizer** of everything it tested: line 12 compares the minimizer `qnew` of
`N` with `qmin`. -/
theorem le_of_mem_tested_repeatLoop (hargmin : IsArgmin p argmin) (qmin : SearchTuple X) (i : ℕ)
    (tested : Finset (SearchTuple X)) :
    p (repeatLoop A p argmin limit qmin i tested).qmin ≤ p qmin ∧
      ∀ t ∈ (repeatLoop A p argmin limit qmin i tested).tested,
        t ∈ tested ∨ p (repeatLoop A p argmin limit qmin i tested).qmin ≤ p t := by
  fun_induction repeatLoop A p argmin limit qmin i tested
  case case1 qmin i tested hne hlt _ ih =>
    obtain ⟨ih₁, ih₂⟩ := ih
    refine ⟨ih₁.trans hlt.le, fun t ht => ?_⟩
    rcases ih₂ t ht with h | h
    · rcases mem_union.mp h with h | h
      · exact Or.inl h
      · exact Or.inr (ih₁.trans ((hargmin _ hne).2 t h))
    · exact Or.inr h
  case case2 qmin i tested hne hlt _ =>
    refine ⟨hlt.le, fun t ht => ?_⟩
    rcases mem_union.mp ht with h | h
    · exact Or.inl h
    · exact Or.inr ((hargmin _ hne).2 t h)
  case case3 qmin i tested hne hlt =>
    refine ⟨le_rfl, fun t ht => ?_⟩
    rcases mem_union.mp ht with h | h
    · exact Or.inl h
    · exact Or.inr ((not_lt.mp hlt).trans ((hargmin _ hne).2 t h))
  case case4 => exact ⟨le_rfl, fun t ht => Or.inl ht⟩

/-- The tuple the loop returns has been tested. -/
theorem qmin_mem_tested_repeatLoop (hargmin : IsArgmin p argmin) {qmin : SearchTuple X} {i : ℕ}
    {tested : Finset (SearchTuple X)} (hq : qmin ∈ tested) :
    (repeatLoop A p argmin limit qmin i tested).qmin ∈ (repeatLoop A p argmin limit qmin i tested).tested := by
  fun_induction repeatLoop A p argmin limit qmin i tested
  case case1 qmin i tested hne _ _ ih =>
    exact ih (mem_union_right _ (hargmin _ hne).1)
  case case2 qmin i tested hne _ _ =>
    exact mem_union_right _ (hargmin _ hne).1
  case case3 =>
    exact mem_union_left _ hq
  case case4 => exact hq

end RepeatLoop

/-- Line 14: update `q*`. The empty `q*` of line 2 is `none`. -/
def betterTuple (p : SearchTuple X → ℝ) : Option (SearchTuple X) → SearchTuple X → Option (SearchTuple X)
  | none, q => some q
  | some b, q => if p q < p b then some q else some b

/-- The state at the exit of the loop of lines 4-14. The number of calls of the test is `i + restarts`: line 5's tuple
is tested at each of the `restarts` executions of line 5, for line 12's comparison, and line 11 adds `|N|` to `i` for
the tuples of each pass. -/
structure SearchOut (X : Type*) where
  best : Option (SearchTuple X)
  restarts : ℕ
  i : ℕ
  tested : Finset (SearchTuple X)

/-- Lines 4-14, with the picks of line 5 given by `pick`, numbered from `k`. See the header on the exit for `n = 4`.
-/
def whileLoop (A : Finset X) (p : SearchTuple X → ℝ) (argmin : Finset (SearchTuple X) → SearchTuple X) (limit : ℕ)
    (pick : ℕ → SearchTuple X) (k : ℕ) (best : Option (SearchTuple X)) (i : ℕ) (tested : Finset (SearchTuple X)) :
    SearchOut X :=
  if _hi : i < limit then
    if _h : (neighbours A (pick k)).Nonempty then
      whileLoop A p argmin limit pick (k + 1)
        (betterTuple p best (repeatLoop A p argmin limit (pick k) i (insert (pick k) tested)).qmin)
        (repeatLoop A p argmin limit (pick k) i (insert (pick k) tested)).i
        (repeatLoop A p argmin limit (pick k) i (insert (pick k) tested)).tested
    else ⟨betterTuple p best (pick k), k + 1, i, insert (pick k) tested⟩
  else ⟨best, k, i, tested⟩
termination_by limit - i
decreasing_by
  have := lt_i_repeatLoop (p := p) (argmin := argmin) (limit := limit) (i := i) (insert (pick k) tested) ‹_›
  omega

/-- **Algorithm 2**, a 3f1a-like bipartition search around the side `A`, with test p-values `p`, minimizers `argmin`,
iteration limit `limit` and picks `pick`. -/
def bipartitionSearch (A : Finset X) (p : SearchTuple X → ℝ) (argmin : Finset (SearchTuple X) → SearchTuple X)
    (limit : ℕ) (pick : ℕ → SearchTuple X) : SearchOut X :=
  whileLoop A p argmin limit pick 0 none 0 ∅

/-- Line 15: the p-value of `q*`. With no tests, the value `1`, as line 6 of Algorithm 1 starts from. -/
def SearchOut.pValue (o : SearchOut X) (p : SearchTuple X → ℝ) : ℝ :=
  match o.best with
  | none => 1
  | some q => p q

/-- The four-taxon sets the search tested. -/
def SearchOut.testedSets (o : SearchOut X) : Finset (Finset X) := o.tested.image SearchTuple.taxa

/-- `best` is a minimizer of `p` on `tested`, or nothing was tested. -/
def IsBestOf (p : SearchTuple X → ℝ) (best : Option (SearchTuple X)) (tested : Finset (SearchTuple X)) : Prop :=
  match best with
  | none => tested = ∅
  | some b => b ∈ tested ∧ ∀ t ∈ tested, p b ≤ p t

section WhileLoop

variable {A : Finset X} {p : SearchTuple X → ℝ} {argmin : Finset (SearchTuple X) → SearchTuple X} {limit : ℕ}
  {pick : ℕ → SearchTuple X}

omit [Fintype X] [DecidableEq X] in
/-- Line 14 keeps a minimizer. -/
theorem IsBestOf.betterTuple {best : Option (SearchTuple X)} {T T' : Finset (SearchTuple X)} {q : SearchTuple X}
    (h : IsBestOf p best T) (hq : q ∈ T') (hTT : T ⊆ T') (hmin : ∀ t ∈ T', t ∈ T ∨ p q ≤ p t) :
    IsBestOf p (TOBQMC.betterTuple p best q) T' := by
  cases best with
  | none =>
    have hT : T = ∅ := h
    subst hT
    refine ⟨hq, fun t ht => ?_⟩
    rcases hmin t ht with h' | h'
    · exact absurd h' (notMem_empty t)
    · exact h'
  | some b =>
    obtain ⟨hb, hbmin⟩ : b ∈ T ∧ ∀ t ∈ T, p b ≤ p t := h
    simp only [TOBQMC.betterTuple]
    split_ifs with hlt
    · refine ⟨hq, fun t ht => ?_⟩
      rcases hmin t ht with h' | h'
      · exact hlt.le.trans (hbmin t h')
      · exact h'
    · refine ⟨hTT hb, fun t ht => ?_⟩
      rcases hmin t ht with h' | h'
      · exact hbmin t h'
      · exact (not_lt.mp hlt).trans h'

/-- The picks are around `A`, so all tuples tested are: lines 8-9 keep two taxa on each side. -/
theorem isAround_whileLoop (hargmin : IsArgmin p argmin) (hpick : ∀ k, (pick k).IsAround A) {k : ℕ}
    {best : Option (SearchTuple X)} {i : ℕ} {tested : Finset (SearchTuple X)} (ht : ∀ t ∈ tested, t.IsAround A) :
    ∀ t ∈ (whileLoop A p argmin limit pick k best i tested).tested, t.IsAround A := by
  fun_induction whileLoop A p argmin limit pick k best i tested
  case case1 k best i tested _ _ ih =>
    refine ih (isAround_repeatLoop hargmin (hpick k) ?_).2
    intro t ht'
    rcases mem_insert.mp ht' with rfl | h
    · exact hpick k
    · exact ht t h
  case case2 k best i tested _ _ =>
    intro t ht'
    rcases mem_insert.mp ht' with rfl | h
    · exact hpick k
    · exact ht t h
  case case3 => exact ht

/-- The test count: `|tested| ≤ i + restarts`. -/
theorem card_tested_whileLoop_le (pick : ℕ → SearchTuple X) (k : ℕ) (best : Option (SearchTuple X)) (i : ℕ)
    (tested : Finset (SearchTuple X)) :
    (whileLoop A p argmin limit pick k best i tested).tested.card + i + k ≤
      tested.card + (whileLoop A p argmin limit pick k best i tested).i +
        (whileLoop A p argmin limit pick k best i tested).restarts := by
  fun_induction whileLoop A p argmin limit pick k best i tested
  case case1 k best i tested _ _ ih =>
    have h₁ := card_tested_repeatLoop_le (A := A) (p := p) (argmin := argmin) (limit := limit) (pick k) i
      (insert (pick k) tested)
    have h₂ := card_insert_le (pick k) tested
    omega
  case case2 k best i tested _ _ =>
    have h₂ := card_insert_le (pick k) tested
    dsimp only
    omega
  case case3 =>
    dsimp only
    omega

/-- `i` passes the limit by at most the last `|N|`, and line 5 runs at most `limit` times: each run is at `i < limit`,
and adds to `i`. -/
theorem le_of_whileLoop (hargmin : IsArgmin p argmin) (hpick : ∀ k, (pick k).IsAround A) {k : ℕ}
    {best : Option (SearchTuple X)} {i : ℕ} {tested : Finset (SearchTuple X)}
    (hi : i ≤ limit + 2 * (Fintype.card X - 4)) (hki : k ≤ i) (hk : k ≤ limit) :
    (whileLoop A p argmin limit pick k best i tested).i ≤ limit + 2 * (Fintype.card X - 4) ∧
      (whileLoop A p argmin limit pick k best i tested).restarts ≤ limit := by
  fun_induction whileLoop A p argmin limit pick k best i tested
  case case1 k best i tested hlt hne ih =>
    have hgrow := lt_i_repeatLoop (A := A) (p := p) (argmin := argmin) (limit := limit) (i := i)
      (insert (pick k) tested) hne
    exact ih (i_repeatLoop_le hargmin (hpick k) hlt.le) (by omega) (by omega)
  case case2 =>
    dsimp only
    omega
  case case3 =>
    dsimp only
    omega

/-- **The search returns the minimum of what it tested**: `q*` is a minimizer of the p-values of the tested tuples. -/
theorem isBestOf_whileLoop (hargmin : IsArgmin p argmin) {k : ℕ} {best : Option (SearchTuple X)} {i : ℕ}
    {tested : Finset (SearchTuple X)} (hb : IsBestOf p best tested) :
    IsBestOf p (whileLoop A p argmin limit pick k best i tested).best
      (whileLoop A p argmin limit pick k best i tested).tested := by
  fun_induction whileLoop A p argmin limit pick k best i tested
  case case1 k best i tested _ _ ih =>
    refine ih (hb.betterTuple (qmin_mem_tested_repeatLoop hargmin (mem_insert_self _ _))
      ((subset_insert _ _).trans (subset_tested_repeatLoop _ _ _)) fun t ht => ?_)
    obtain ⟨h₁, h₂⟩ := le_of_mem_tested_repeatLoop (A := A) (limit := limit) hargmin (pick k) i
      (insert (pick k) tested)
    rcases h₂ t ht with h | h
    · rcases mem_insert.mp h with rfl | h
      · exact Or.inr h₁
      · exact Or.inl h
    · exact Or.inr h
  case case2 k best i tested _ _ =>
    refine hb.betterTuple (mem_insert_self _ _) (subset_insert _ _) fun t ht => ?_
    rcases mem_insert.mp ht with rfl | h
    · exact Or.inr le_rfl
    · exact Or.inl h
  case case3 => exact hb

end WhileLoop

section Search

variable {A : Finset X} {p : SearchTuple X → ℝ} {argmin : Finset (SearchTuple X) → SearchTuple X} {limit : ℕ}
  {pick : ℕ → SearchTuple X}

/-- All tuples the search tests are around the bipartition. -/
theorem isAround_bipartitionSearch (hargmin : IsArgmin p argmin) (hpick : ∀ k, (pick k).IsAround A) :
    ∀ t ∈ (bipartitionSearch A p argmin limit pick).tested, t.IsAround A :=
  isAround_whileLoop hargmin hpick (by simp)

/-- The four-taxon sets the search tests have two taxa on each side of the bipartition. -/
theorem card_of_mem_testedSets (hargmin : IsArgmin p argmin) (hpick : ∀ k, (pick k).IsAround A) {Y : Finset X}
    (hY : Y ∈ (bipartitionSearch A p argmin limit pick).testedSets) : Y.card = 4 ∧ (A ∩ Y).card = 2 := by
  obtain ⟨t, ht, rfl⟩ := mem_image.mp hY
  have := isAround_bipartitionSearch hargmin hpick t ht
  exact ⟨this.card_taxa, this.card_inter_taxa⟩

/-- **The test count of the search**: at most `i + restarts` tuples, with `i ≤ limit + 2 (n - 4)` and at most `limit`
tests at line 5. The iteration limit bounds the printed counter `i` only up to the size of the last `N`. -/
theorem SearchOut.counts (hargmin : IsArgmin p argmin) (hpick : ∀ k, (pick k).IsAround A) :
    (bipartitionSearch A p argmin limit pick).tested.card ≤
        (bipartitionSearch A p argmin limit pick).i + (bipartitionSearch A p argmin limit pick).restarts ∧
      (bipartitionSearch A p argmin limit pick).i ≤ limit + 2 * (Fintype.card X - 4) ∧
      (bipartitionSearch A p argmin limit pick).restarts ≤ limit := by
  have h := card_tested_whileLoop_le (A := A) (p := p) (argmin := argmin) (limit := limit) pick 0 none 0 ∅
  obtain ⟨h₁, h₂⟩ := le_of_whileLoop (A := A) (p := p) (limit := limit) (best := none) (tested := ∅) (i := 0) (k := 0)
    hargmin hpick (by omega) (by omega) (by omega)
  simp only [card_empty, add_zero, zero_add] at h
  exact ⟨h, h₁, h₂⟩

/-- At most `2 * limit + 2 * (n - 4)` four-taxon sets are tested by the search. -/
theorem SearchOut.card_testedSets_le (hargmin : IsArgmin p argmin) (hpick : ∀ k, (pick k).IsAround A) :
    (bipartitionSearch A p argmin limit pick).testedSets.card ≤ 2 * limit + 2 * (Fintype.card X - 4) := by
  obtain ⟨h₁, h₂, h₃⟩ := SearchOut.counts (limit := limit) hargmin hpick
  exact card_image_le.trans (by omega)

/-- **The test count per edge**, for `Q` a set of `n - 3` four-taxon sets such as that of 3f1a
(`threeFixOneAlter_isDisjointCover`). -/
theorem card_threeFixOneAlter_union_testedSets_le (hargmin : IsArgmin p argmin) (hpick : ∀ k, (pick k).IsAround A)
    {Q : Finset (Finset X)} (hQ : Q.card = Fintype.card X - 3) :
    (Q ∪ (bipartitionSearch A p argmin limit pick).testedSets).card ≤
      (Fintype.card X - 3) + 2 * limit + 2 * (Fintype.card X - 4) := by
  have := SearchOut.card_testedSets_le (limit := limit) hargmin hpick
  have h := card_union_le Q (bipartitionSearch A p argmin limit pick).testedSets
  omega

/-- The p-value the search returns is below a level exactly when a tested tuple is, at levels at most `1`. -/
theorem pValue_lt_iff (hargmin : IsArgmin p argmin) {α : ℝ} (hα : α ≤ 1) :
    (bipartitionSearch A p argmin limit pick).pValue p < α ↔
      ∃ t ∈ (bipartitionSearch A p argmin limit pick).tested, p t < α := by
  have hb : IsBestOf p (bipartitionSearch A p argmin limit pick).best
      (bipartitionSearch A p argmin limit pick).tested :=
    isBestOf_whileLoop hargmin (best := none) (tested := ∅) rfl
  rw [SearchOut.pValue]
  cases hbest : (bipartitionSearch A p argmin limit pick).best with
  | none =>
    rw [hbest] at hb
    have hT : (bipartitionSearch A p argmin limit pick).tested = ∅ := hb
    rw [hT]
    simp only [notMem_empty, false_and, exists_false, iff_false, not_lt]
    exact hα
  | some b =>
    rw [hbest] at hb
    obtain ⟨hbm, hbmin⟩ : b ∈ (bipartitionSearch A p argmin limit pick).tested ∧ _ := hb
    exact ⟨fun h => ⟨b, hbm, h⟩, fun ⟨t, ht, h⟩ => (hbmin t ht).trans_lt h⟩

end Search

/-! ### Contraction on a cover and on more quartets around the bipartition -/

section Oracle

variable {N : RootedNetwork V E X}

/-- **Theorem 2 with more four-taxon subsets around the bipartition.** Testing a disjoint cover `Q A` at each edge and
also any four-taxon subsets `R A` around the bipartition of the edge, and contracting the edges where the oracle
answers non-treelike on one of them, returns the tree of blobs. A false positive is labelled because of `Q`, by
Theorem 2. A true edge is never labelled: by Lemma 2, all the subsets around its bipartition are treelike, whether or
not they draw from distinct blocks. -/
theorem contractSides_cover_union_eq [Fintype V] [Fintype E] (hN : N.IsPhylogenetic) (hBin : N.IsBinary)
    (hLevel : IsLevelOne N)
    {B : Finset (Finset X)} (hB : IsUnrootedTree B) (hTB : treeOfBlobs N ⊆ B)
    (Q R : Finset X → Finset (Finset X)) (hQ : ∀ A ∈ internalSides B, IsDisjointCover B A (Q A))
    (hR : ∀ A ∈ internalSides B, ∀ Y ∈ R A, Y.card = 4 ∧ (A ∩ Y).card = 2) :
    contractSides B ((internalSides B).filter fun A => ∃ Y ∈ Q A ∪ R A, ¬ IsTreelike N Y) = treeOfBlobs N := by
  have h2 := theorem2 hN hBin hLevel hB hTB Q hQ
  -- a true edge is not labelled
  have htrue : ∀ A ∈ treeOfBlobs N, A ∉ (internalSides B).filter fun A => ∃ Y ∈ Q A ∪ R A, ¬ IsTreelike N Y := by
    intro A hAT hC
    obtain ⟨hint, Y, hY, hnt⟩ := mem_filter.mp hC
    have hA := (mem_filter.mp hAT).2.2.2
    rcases mem_union.mp hY with hY | hY
    · obtain ⟨s, hs, rfl⟩ := (hQ A hint).around Y hY
      have hbi := (mem_filter.mp (mem_filter.mp hs).1).2
      exact hnt (Level1.isTreelike_of_hasCutSplit hN hA (QuartetTree.card_taxa s) (s.2.2.1 _ hbi))
    · obtain ⟨hc, hc'⟩ := hR A hint Y hY
      exact hnt (Level1.isTreelike_of_hasCutSplit hN hA hc hc')
  have hsub : (internalSides B).filter (fun A => ∃ Y ∈ Q A, ¬ IsTreelike N Y) ⊆
      (internalSides B).filter fun A => ∃ Y ∈ Q A ∪ R A, ¬ IsTreelike N Y := by
    intro A hA
    obtain ⟨hint, Y, hY, hnt⟩ := mem_filter.mp hA
    exact mem_filter.mpr ⟨hint, Y, mem_union_left _ hY, hnt⟩
  ext A
  rw [← h2]
  simp only [contractSides, mem_filter (s := B)]
  constructor
  · rintro ⟨hAB, h₁, h₂⟩
    exact ⟨hAB, fun h => h₁ (hsub h), fun h => h₂ (hsub h)⟩
  · intro h
    have hAT : A ∈ treeOfBlobs N := by
      rw [← h2]
      simp only [contractSides, mem_filter (s := B)]
      exact h
    exact ⟨h.1, htrue A hAT, htrue _ (Level1.mem_treeOfBlobs_compl hAT)⟩

end Oracle

/-! ### The tests -/

/-- `α ≤ 1`: the minimum of a multiset, with `1` for the empty one, is below `α` when a member is. -/
theorem minP_lt_iff {α : ℝ} (hα : α ≤ 1) {P : Multiset ℝ} : minP P < α ↔ ∃ x ∈ P, x < α := by
  induction P using Multiset.induction_on with
  | empty => simpa [minP] using hα
  | cons x P ih =>
    simp only [minP] at ih ⊢
    rw [Multiset.fold_cons_left, min_lt_iff, ih]
    simp only [Multiset.mem_cons, exists_eq_or_imp]

/-- The p-value with which the tests of TINNiK's algorithm (Step 2, `testedB`) judge a four-taxon set: `0` when the
star test does not reject at level `β`, and the p-value of the cut test otherwise. At a level `α > 0` of the cut test,
it is below `α` exactly when the set is judged non-treelike (`judgedP_lt_iff`).

This reads the tests as `TOBQMC.tobqmc` does, TOB-QMC §4.3's "TINNiK's hypothesis tests". The implementation described
at embedded lines 133-137 instead keeps the p-value of the treelikeness test and applies the star test to the
minimizer alone; the T3 test is not treated. -/
def judgedP (ml : (QuartetTree X → ℝ) → Finset X → QuartetTree X) (β : ℝ) (c : QuartetTree X → ℝ) (Y : Finset X) : ℝ :=
  if β ≤ starPValue .lrt c Y then 0 else cutPValue c (ml c Y)

/-- The p-value is below `α` exactly when the tests judge the set non-treelike. -/
theorem judgedP_lt_iff {ml : (QuartetTree X → ℝ) → Finset X → QuartetTree X} {α β : ℝ} {c : QuartetTree X → ℝ}
    {Y : Finset X} (hα : 0 < α) (hY : Y.card = 4) : judgedP ml β c Y < α ↔ Y ∈ testedB ml α β c := by
  simp only [judgedP, testedB, Set.mem_ofPred_eq, hY, true_and]
  by_cases h : β ≤ starPValue .lrt c Y
  · simp [h, hα]
  · simp [h]

/-- **The p-value of an edge**: the minimum of Algorithm 1's over the disjoint cover `Q` and of Algorithm 2's. -/
def edgeP (ml : (QuartetTree X → ℝ) → Finset X → QuartetTree X) (β : ℝ) (c : QuartetTree X → ℝ)
    (Q : Finset (Finset X)) (o : SearchOut X) : ℝ :=
  min (minP (Q.val.map (judgedP ml β c))) (o.pValue fun t => judgedP ml β c t.taxa)

/-- The p-value of an edge is below a level exactly when one of the four-taxon sets tested has its p-value below that
level, at levels at most `1`. So it is the minimum over the cover and over the sets the search tested. -/
theorem edgeP_lt_iff {ml : (QuartetTree X → ℝ) → Finset X → QuartetTree X} {α β : ℝ} {c : QuartetTree X → ℝ}
    {Q : Finset (Finset X)} {A : Finset X} {argmin : Finset (SearchTuple X) → SearchTuple X} {limit : ℕ}
    {pick : ℕ → SearchTuple X} (hargmin : IsArgmin (fun t => judgedP ml β c t.taxa) argmin) (hα : α ≤ 1) :
    edgeP ml β c Q (bipartitionSearch A (fun t => judgedP ml β c t.taxa) argmin limit pick) < α ↔
      ∃ Y ∈ Q ∪ (bipartitionSearch A (fun t => judgedP ml β c t.taxa) argmin limit pick).testedSets,
        judgedP ml β c Y < α := by
  rw [edgeP, min_lt_iff, minP_lt_iff hα, pValue_lt_iff hargmin hα]
  simp only [Multiset.mem_map, mem_val, SearchOut.testedSets, mem_union, mem_image]
  constructor
  · rintro (⟨x, ⟨Y, hY, rfl⟩, hx⟩ | ⟨t, ht, hx⟩)
    · exact ⟨Y, Or.inl hY, hx⟩
    · exact ⟨t.taxa, Or.inr ⟨t, ht, rfl⟩, hx⟩
  · rintro ⟨Y, hY | ⟨t, ht, rfl⟩, hx⟩
    · exact Or.inl ⟨_, ⟨Y, hY, rfl⟩, hx⟩
    · exact Or.inr ⟨t, ht, hx⟩

/-- The method with any further four-taxon sets `R` around the bipartitions: from the tree `B`, contract the edges
where the tests judge a set of the cover `Q` or of `R` non-treelike. -/
def tobqmcAround (ml : (QuartetTree X → ℝ) → Finset X → QuartetTree X) (α β : ℝ) (c : QuartetTree X → ℝ)
    (B : Finset (Finset X)) (Q R : Finset X → Finset (Finset X)) : Finset (Finset X) :=
  contractSides B ((internalSides B).filter fun A => ∃ Y ∈ Q A ∪ R A, Y ∈ testedB ml α β c)

/-- **The combination of §4.3**: from the tree `B`, contract the edges whose p-value `edgeP`, the minimum over the
disjoint cover `Q` and over Algorithm 2 with limit `limit` and picks `pick`, is below `α`. -/
def tobqmcSearch (ml : (QuartetTree X → ℝ) → Finset X → QuartetTree X) (α β : ℝ) (c : QuartetTree X → ℝ)
    (B : Finset (Finset X)) (Q : Finset X → Finset (Finset X))
    (argmin : (SearchTuple X → ℝ) → Finset (SearchTuple X) → SearchTuple X) (limit : ℕ)
    (pick : Finset X → ℕ → SearchTuple X) : Finset (Finset X) :=
  contractSides B ((internalSides B).filter fun A =>
    edgeP ml β c (Q A) (bipartitionSearch A (fun t => judgedP ml β c t.taxa)
      (argmin fun t => judgedP ml β c t.taxa) limit (pick A)) < α)

/-! ### Consistency -/

/-- **Consistency with further four-taxon sets around the bipartitions**, under the hypotheses of
`TOBQMC.consistency`, for any selection `R` of four-taxon sets around the bipartitions, possibly depending on the
data. The levels are those of `TOBQMC.consistency`'s proof. On the event that the tests are correct on all four-taxon
sets (`TINNiK.tests_correct`) and that the solution refines the tree of blobs, the method is the oracle's, and
`contractSides_cover_union_eq` applies. That the solution refines the tree of blobs comes from `TOBQMC.consistency`
itself, whose output is contained in the solution. -/
theorem consistency_around [Fintype V] [Fintype E] {N : RootedNetwork V E X} {θ : MetricData E} {ρ : ℝ}
    (hStd : StandardAssumptions N θ ρ) (hLevel : IsLevelOne N)
    (hNon : IsTQuartetNonanomalous N (nmscCF N θ ρ))
    (hBlob : ∀ q : Finset X, q.card = 4 → ¬ IsTreelike N q →
      External.AllmanEtAl2023.IsNonCut (nmscCF N θ ρ) q) (hX : 4 ≤ Fintype.card X) :
    ∃ α : ℕ → ℝ, Tendsto α atTop (𝓝 0) ∧ (∀ k, 0 < α k) ∧
      ∀ (β : ℝ), 0 < β →
      ∀ (ml : (QuartetTree X → ℝ) → Finset X → QuartetTree X), IsMLSelection ml →
      ∀ (solve : (QuartetTree X → ℝ) → Finset (Finset X)), (∀ c, IsWQCOptimal c (solve c)) →
      ∀ (cover : Finset (Finset X) → Finset X → Finset (Finset X)),
        (∀ B, IsBinaryTree B → ∀ A ∈ internalSides B, IsDisjointCover B A (cover B A)) →
      ∀ (R : (QuartetTree X → ℝ) → Finset (Finset X) → Finset X → Finset (Finset X)),
        (∀ c B, IsBinaryTree B → ∀ A ∈ internalSides B, ∀ Y ∈ R c B A, Y.card = 4 ∧ (A ∩ Y).card = 2) →
        Tendsto (fun k => iidProb (geneTreeDist N θ ρ) k fun ω =>
          tobqmcAround ml (α k) β (quartetCount unroot ω) (solve (quartetCount unroot ω))
            (cover (solve (quartetCount unroot ω))) (R (quartetCount unroot ω) (solve (quartetCount unroot ω))) =
              treeOfBlobs N) atTop (𝓝 1) := by
  have hN := hStd.phylogenetic
  have hne : Nonempty X := Fintype.card_pos_iff.mp (by omega)
  have hd : IsDist (geneTreeDist N θ ρ) :=
    ⟨geneTreeDist_nonneg hN hStd.metric hStd.rho, sum_geneTreeDist hN hStd.metric hStd.rho⟩
  have hdet := Level1.cfDetectable hStd hLevel hNon hBlob
  obtain ⟨α, hα₀, hαpos, hrej⟩ := TINNiK.exists_levels hN hStd.metric hStd.rho hdet
  obtain ⟨α', -, -, hcons⟩ := consistency hStd hLevel hNon hBlob hX
  refine ⟨α, hα₀, hαpos, fun β hβ ml hml solve hsolve cover hcover R hR => ?_⟩
  have htests := TINNiK.tests_correct hN hX hStd.metric hStd.rho hdet hα₀ hrej hβ hml
  refine tendsto_iidProb_of_imp hd (Eventually.of_forall fun k ω hω => ?_)
    (TINNiK.tendsto_iidProb_and hd htests (hcons β hβ ml hml solve hsolve cover hcover))
  obtain ⟨⟨hB, -⟩, hout⟩ := hω
  obtain ⟨hbin, -⟩ := hsolve (quartetCount unroot ω)
  have hTB : treeOfBlobs N ⊆ solve (quartetCount unroot ω) := by
    rw [← hout]
    exact filter_subset _ _
  have hBu : IsUnrootedTree (solve (quartetCount unroot ω)) := by
    obtain ⟨H, hH, hu, -⟩ := hbin
    exact ⟨H, hH, hu⟩
  have hcov := hcover _ hbin
  have hRR := hR (quartetCount unroot ω) _ hbin
  rw [← contractSides_cover_union_eq hN hStd.binary hLevel hBu hTB _ _ hcov hRR, tobqmcAround]
  congr 1
  refine Finset.filter_congr fun A hA => exists_congr fun Y => and_congr_right fun hY => ?_
  have hc : Y.card = 4 := by
    rcases mem_union.mp hY with hY | hY
    · obtain ⟨s, -, rfl⟩ := (hcov A hA).around Y hY
      exact QuartetTree.card_taxa s
    · exact (hRR A hA Y hY).1
  rw [hB]
  exact ⟨fun h => h.2, fun h => ⟨hc, h⟩⟩

/-- **The claim of TOB-QMC at embedded lines 622-623** on consistency (`tob2025:consistency`, as extended there):
combining the bipartition search with a disjoint cover, the p-value of each edge being the minimum over the cover and
over the four-taxon sets the search tested, is consistent for level-1 networks. The hypotheses are those of
`TOBQMC.consistency`; the iteration limit and the picks of Algorithm 2 are arbitrary, its picks being around the
bipartition, and may depend on the data. -/
theorem consistency_search [Fintype V] [Fintype E] {N : RootedNetwork V E X} {θ : MetricData E} {ρ : ℝ}
    (hStd : StandardAssumptions N θ ρ) (hLevel : IsLevelOne N)
    (hNon : IsTQuartetNonanomalous N (nmscCF N θ ρ))
    (hBlob : ∀ q : Finset X, q.card = 4 → ¬ IsTreelike N q →
      External.AllmanEtAl2023.IsNonCut (nmscCF N θ ρ) q) (hX : 4 ≤ Fintype.card X) :
    ∃ α : ℕ → ℝ, Tendsto α atTop (𝓝 0) ∧ (∀ k, 0 < α k) ∧
      ∀ (β : ℝ), 0 < β →
      ∀ (ml : (QuartetTree X → ℝ) → Finset X → QuartetTree X), IsMLSelection ml →
      ∀ (solve : (QuartetTree X → ℝ) → Finset (Finset X)), (∀ c, IsWQCOptimal c (solve c)) →
      ∀ (cover : Finset (Finset X) → Finset X → Finset (Finset X)),
        (∀ B, IsBinaryTree B → ∀ A ∈ internalSides B, IsDisjointCover B A (cover B A)) →
      ∀ (argmin : (SearchTuple X → ℝ) → Finset (SearchTuple X) → SearchTuple X), (∀ p, IsArgmin p (argmin p)) →
      ∀ (limit : ℕ) (pick : (QuartetTree X → ℝ) → Finset (Finset X) → Finset X → ℕ → SearchTuple X),
        (∀ c B, IsBinaryTree B → ∀ A ∈ internalSides B, ∀ i, (pick c B A i).IsAround A) →
        Tendsto (fun k => iidProb (geneTreeDist N θ ρ) k fun ω =>
          tobqmcSearch ml (α k) β (quartetCount unroot ω) (solve (quartetCount unroot ω))
            (cover (solve (quartetCount unroot ω))) argmin limit
            (pick (quartetCount unroot ω) (solve (quartetCount unroot ω))) = treeOfBlobs N) atTop (𝓝 1) := by
  have hN := hStd.phylogenetic
  have hne : Nonempty X := Fintype.card_pos_iff.mp (by omega)
  have hd : IsDist (geneTreeDist N θ ρ) :=
    ⟨geneTreeDist_nonneg hN hStd.metric hStd.rho, sum_geneTreeDist hN hStd.metric hStd.rho⟩
  obtain ⟨α, hα₀, hαpos, h⟩ := consistency_around hStd hLevel hNon hBlob hX
  refine ⟨α, hα₀, hαpos, fun β hβ ml hml solve hsolve cover hcover argmin hargmin limit pick hpick => ?_⟩
  let R : (QuartetTree X → ℝ) → Finset (Finset X) → Finset X → Finset (Finset X) := fun c B A =>
    (bipartitionSearch A (fun t => judgedP ml β c t.taxa) (argmin fun t => judgedP ml β c t.taxa) limit
      (pick c B A)).testedSets
  have hR : ∀ c B, IsBinaryTree B → ∀ A ∈ internalSides B, ∀ Y ∈ R c B A, Y.card = 4 ∧ (A ∩ Y).card = 2 :=
    fun c B hB A hA Y hY => card_of_mem_testedSets (hargmin _) (hpick c B hB A hA) hY
  refine tendsto_iidProb_of_imp hd ?_ (h β hβ ml hml solve hsolve cover hcover R hR)
  filter_upwards [hα₀.eventually (gt_mem_nhds (zero_lt_one' ℝ))] with k hk ω hω
  rw [← hω, tobqmcSearch, tobqmcAround]
  congr 1
  refine Finset.filter_congr fun A hA => ?_
  rw [edgeP_lt_iff (hargmin _) hk.le]
  obtain ⟨hbin, -⟩ := hsolve (quartetCount unroot ω)
  refine exists_congr fun Y => and_congr_right fun hY => judgedP_lt_iff (hαpos k) ?_
  rcases mem_union.mp hY with hY | hY
  · obtain ⟨s, -, rfl⟩ := (hcover _ hbin A hA).around Y hY
    exact QuartetTree.card_taxa s
  · exact (hR _ _ hbin A hA Y hY).1

/-- **Consistency with 3f1a itself**: the cover is the one of Algorithm 1, on the blocks `P B A` of the
quadripartition of the edge with side `A` of `B`, with anchors `z B A`. It has `n - 3` subsets
(`threeFixOneAlter_isDisjointCover`), so the number of four-taxon subsets per edge is at most `(n - 3) + 2 * limit + 2
* (n - 4)` (`card_threeFixOneAlter_union_testedSets_le`). -/
theorem consistency_threeFixOneAlter_search [Fintype V] [Fintype E] {N : RootedNetwork V E X} {θ : MetricData E} {ρ : ℝ}
    (hStd : StandardAssumptions N θ ρ) (hLevel : IsLevelOne N)
    (hNon : IsTQuartetNonanomalous N (nmscCF N θ ρ))
    (hBlob : ∀ q : Finset X, q.card = 4 → ¬ IsTreelike N q →
      External.AllmanEtAl2023.IsNonCut (nmscCF N θ ρ) q) (hX : 4 ≤ Fintype.card X) :
    ∃ α : ℕ → ℝ, Tendsto α atTop (𝓝 0) ∧ (∀ k, 0 < α k) ∧
      ∀ (β : ℝ), 0 < β →
      ∀ (ml : (QuartetTree X → ℝ) → Finset X → QuartetTree X), IsMLSelection ml →
      ∀ (solve : (QuartetTree X → ℝ) → Finset (Finset X)), (∀ c, IsWQCOptimal c (solve c)) →
      ∀ (P : Finset (Finset X) → Finset X → Fin 4 → Finset X) (z : Finset (Finset X) → Finset X → Fin 4 → X),
        (∀ B, IsBinaryTree B → ∀ A ∈ internalSides B,
          (∀ i j, i ≠ j → Disjoint (P B A i) (P B A j)) ∧ univ.biUnion (P B A) = univ ∧
            P B A 0 ∪ P B A 1 = A ∧ (∀ i, P B A i ∈ B) ∧ ∀ i, z B A i ∈ P B A i) →
      ∀ (argmin : (SearchTuple X → ℝ) → Finset (SearchTuple X) → SearchTuple X), (∀ p, IsArgmin p (argmin p)) →
      ∀ (limit : ℕ) (pick : (QuartetTree X → ℝ) → Finset (Finset X) → Finset X → ℕ → SearchTuple X),
        (∀ c B, IsBinaryTree B → ∀ A ∈ internalSides B, ∀ i, (pick c B A i).IsAround A) →
        Tendsto (fun k => iidProb (geneTreeDist N θ ρ) k fun ω =>
          tobqmcSearch ml (α k) β (quartetCount unroot ω) (solve (quartetCount unroot ω))
            (fun A => threeFixOneAlter (P (solve (quartetCount unroot ω)) A) (z (solve (quartetCount unroot ω)) A))
            argmin limit (pick (quartetCount unroot ω) (solve (quartetCount unroot ω))) = treeOfBlobs N)
          atTop (𝓝 1) := by
  obtain ⟨α, hα₀, hαpos, h⟩ := consistency_search hStd hLevel hNon hBlob hX
  refine ⟨α, hα₀, hαpos, fun β hβ ml hml solve hsolve P z hPz argmin hargmin limit pick hpick => ?_⟩
  refine h β hβ ml hml solve hsolve (fun B A => threeFixOneAlter (P B A) (z B A)) (fun B hB A hA => ?_) argmin hargmin
    limit pick hpick
  obtain ⟨h₁, h₂, h₃, h₄, h₅⟩ := hPz B hB A hA
  exact (threeFixOneAlter_isDisjointCover hB hA (P B A) h₁ h₂ h₃ h₄ (z B A) h₅).1

end TOBQMC
