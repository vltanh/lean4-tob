module

public import AllmanEtAl2023.Basic
public import Basic.Defs
public import Basic.Testing.Defs
public import Phylogenetics.Tree.Splits
public import TINNiK.Basic

/-!
# TINNiK: operation counts

The running times of TINNiK (`notes/tinnik/readable.txt`, lines 180 and 196). No machine model is used: each theorem
counts the objects that a step enumerates, and says what each one costs in the paper's terms; the bounds are explicit.

## The B-quartet Inference Algorithm

Step 3 of the algorithm (line 176) is written out as a function, with the lists `L₁`, `L₂` of the printed text and
with counters: `compareStep` is the body of Step 3(a)(i), `visitStep` the loop (i), `passStep` the loop (a),
`inferLoop` the return of (b), and `bQuartetInference` the whole. Its output is the closure the library calls
`BInferred` (`mem_bQuartetInference_iff`, `setOf_bInferred_eq_bQuartetInference`), which is the paper's statement:
"The algorithm eventually considers every pair of B-quartets sharing three taxa, since any time a new one is
discovered it is compared to all quartets that share three taxa with it. If one of these is a not-yet-inferred
B-quartet, then this pair will be compared again later, once that quartet is inferred as a B-quartet." That sentence
is `IsClosedOn.visit`, which also needs the case where the third B-quartet of the rule appears after the comparison of
the pair: then it is compared with one of the pair, and the other is among its `otherSets`.

The counters are exact: each B-quartet is compared with the `4 (N - 4)` sets sharing three taxa with it
(`card_sharing_three`, E29 of the report), once (`count_bQuartetInference`), so at most `4 (N - 4) C(N, 4)`
comparisons (`count_bQuartetInference_le`), in at most `C(N, 4) + 1` passes (`passes_bQuartetInference_le`).

## The steps of TINNiK

Step 1 `O(mN⁴)`: `card_tabulation`. Step 2 `O(N⁵)`: `sum_step2_statistics` and the above. Step 3 `O(N⁴)`:
`sum_distance_incidences`, with `card_fourSets_superset` per pair of taxa. Step 4 `O(N³)`: `tinnikOperations_le` takes
`nj ≤ c N³` as a hypothesis. Step 5 `O(N)`: `card_le_of_isUnrootedTree`. Combined, `O((m + N) N⁴)`:
`tinnikOperations_le`.
-/

@[expose] public noncomputable section

open Phylogenetics Finset
open scoped Classical

namespace TINNiK

variable {X : Type*} [Fintype X] [DecidableEq X]

/-! ### The B-quartet Inference Algorithm, Step 3 -/

/-- The sets of four taxa sharing exactly three taxa with `q`: Step 3(a)(i)'s loop. By `card_sharing_three`, there are
`4 (N - 4)` of them. -/
def sharingThree (q : Finset X) : Finset (Finset X) :=
  univ.filter fun t => t.card = 4 ∧ (t ∩ q).card = 3

/-- For sets `x = {a, b, c, d}` and `y = {a, b, c, e}` sharing three taxa, the sets `{a, b, d, e}`, `{a, c, d, e}`,
`{b, c, d, e}` of Step 3(a)(i)(α): the four-subsets of `x ∪ y` other than `x` and `y`. -/
def otherSets (x y : Finset X) : Finset (Finset X) :=
  (x ∩ y).image fun z => (x ∪ y).erase z

/-- Step 3(a)(i)(β): a quartet tree inferred at Step 2(c), on one of `otherSets x y`, that separates the taxa in which
`x` and `y` differ. These are the printed `ea|bd, eb|ad, ea|cd, ec|ad, eb|cd, ec|bd`. -/
def HasSeparatingTree (τ : Set (QuartetTree X)) (x y : Finset X) : Prop :=
  ∃ s ∈ τ, s.taxa ∈ otherSets x y ∧ ∀ a ∈ x \ y, ∀ e ∈ y \ x, Separated s a e

/-- The state of Step 3: the vector `B`, the list `L₂`, and the number `count` of executions of the body of Step
3(a)(i). -/
structure InferState (X : Type*) where
  B : Finset (Finset X)
  L₂ : List (Finset X)
  count : ℕ

/-- The body of Step 3(a)(i): comparison of the set `x` with a set `y` sharing three taxa. If `y` is a known
B-quartet, and (α) one of `otherSets x y` is, or (β) a separating quartet tree was inferred, then (γ) designate
`otherSets x y`, and store the new ones in `L₂`. -/
def compareStep (τ : Set (QuartetTree X)) (x : Finset X) (σ : InferState X) (y : Finset X) : InferState X :=
  if y ∈ σ.B ∧ ((otherSets x y ∩ σ.B).Nonempty ∨ HasSeparatingTree τ x y) then
    ⟨σ.B ∪ otherSets x y, σ.L₂ ++ (otherSets x y \ σ.B).toList, σ.count + 1⟩
  else ⟨σ.B, σ.L₂, σ.count + 1⟩

/-- Step 3(a)(i): the loop over the sets sharing three taxa with `x`. -/
def visitStep (τ : Set (QuartetTree X)) (σ : InferState X) (x : Finset X) : InferState X :=
  (sharingThree x).toList.foldl (compareStep τ x) σ

/-- Step 3(a): the loop over the entries of `L₁`. -/
def passStep (τ : Set (QuartetTree X)) (L₁ : List (Finset X)) (σ : InferState X) : InferState X :=
  L₁.foldl (visitStep τ) σ

/-! #### Invariants of a pass -/

omit [Fintype X] [DecidableEq X] in
/-- An invariant of a fold. -/
theorem foldl_induction {α β : Type*} {f : α → β → α} {P : α → Prop} {l : List β}
    (hf : ∀ a, ∀ b ∈ l, P a → P (f a b)) {a : α} (h : P a) : P (l.foldl f a) := by
  induction l generalizing a with
  | nil => exact h
  | cons b l ih =>
    exact ih (fun a' b' hb' => hf a' b' (List.mem_cons_of_mem _ hb')) (hf a b List.mem_cons_self h)

/-- What a pass from the vector `B₀` keeps: `L₂` lists without repetition exactly the sets added to `B₀`. -/
structure PassInv (B₀ : Finset (Finset X)) (σ : InferState X) : Prop where
  subset : B₀ ⊆ σ.B
  mem_iff : ∀ t, t ∈ σ.B ↔ t ∈ B₀ ∨ t ∈ σ.L₂
  nodup : σ.L₂.Nodup
  notMem : ∀ t ∈ σ.L₂, t ∉ B₀

variable {τ : Set (QuartetTree X)}

omit [Fintype X] [DecidableEq X] in
theorem PassInv.init (B₀ : Finset (Finset X)) (n : ℕ) : PassInv B₀ ⟨B₀, [], n⟩ :=
  ⟨Subset.refl _, by simp, List.nodup_nil, by simp⟩

omit [Fintype X] in
theorem PassInv.compareStep {B₀ : Finset (Finset X)} {σ : InferState X} (h : PassInv B₀ σ) (x y : Finset X) :
    PassInv B₀ (TINNiK.compareStep τ x σ y) := by
  unfold TINNiK.compareStep
  split_ifs
  · refine ⟨h.subset.trans subset_union_left, fun t => ?_, ?_, ?_⟩
    · simp only [mem_union, List.mem_append, mem_toList, mem_sdiff]
      have := h.mem_iff t
      tauto
    · refine List.nodup_append.mpr ⟨h.nodup, nodup_toList _, ?_⟩
      intro a ha b hb hab
      subst hab
      exact (mem_sdiff.mp (mem_toList.mp hb)).2 ((h.mem_iff a).mpr (Or.inr ha))
    · intro t ht
      rcases List.mem_append.mp ht with ht | ht
      · exact h.notMem t ht
      · exact fun hB => (mem_sdiff.mp (mem_toList.mp ht)).2 (h.subset hB)
  · exact ⟨h.subset, h.mem_iff, h.nodup, h.notMem⟩

theorem PassInv.visitStep {B₀ : Finset (Finset X)} {σ : InferState X} (h : PassInv B₀ σ) (x : Finset X) :
    PassInv B₀ (TINNiK.visitStep τ σ x) :=
  foldl_induction (fun _ y _ ha => ha.compareStep x y) h

theorem PassInv.passStep {B₀ : Finset (Finset X)} {σ : InferState X} (h : PassInv B₀ σ) (L₁ : List (Finset X)) :
    PassInv B₀ (TINNiK.passStep τ L₁ σ) :=
  foldl_induction (fun _ x _ ha => ha.visitStep x) h

omit [Fintype X] in
theorem subset_B_compareStep (x y : Finset X) (σ : InferState X) : σ.B ⊆ (compareStep τ x σ y).B := by
  unfold compareStep
  split_ifs
  · exact subset_union_left
  · exact Subset.refl _

theorem subset_B_visitStep (x : Finset X) (σ : InferState X) : σ.B ⊆ (visitStep τ σ x).B :=
  foldl_induction (P := fun a : InferState X => σ.B ⊆ a.B)
    (fun a y _ ha => ha.trans (subset_B_compareStep x y a)) (Subset.refl _)

theorem subset_B_passStep (L₁ : List (Finset X)) (σ : InferState X) : σ.B ⊆ (passStep τ L₁ σ).B :=
  foldl_induction (P := fun a : InferState X => σ.B ⊆ a.B)
    (fun a x _ ha => ha.trans (subset_B_visitStep x a)) (Subset.refl _)

/-- The output of Step 3: the vector `B`, the number `count` of executions of the body of Step 3(a)(i), and the number
`passes` of executions of Step 3(a). -/
structure InferOut (X : Type*) where
  B : Finset (Finset X)
  count : ℕ
  passes : ℕ

/-- Step 3: run a pass over `L₁`, and (b) if `L₂` is not empty, store it into `L₁` and go on. -/
def inferLoop (τ : Set (QuartetTree X)) (L₁ : List (Finset X)) (B : Finset (Finset X)) (count passes : ℕ) :
    InferOut X :=
  if _h : (passStep τ L₁ ⟨B, [], count⟩).L₂ = [] then
    ⟨(passStep τ L₁ ⟨B, [], count⟩).B, (passStep τ L₁ ⟨B, [], count⟩).count, passes + 1⟩
  else
    inferLoop τ (passStep τ L₁ ⟨B, [], count⟩).L₂ (passStep τ L₁ ⟨B, [], count⟩).B
      (passStep τ L₁ ⟨B, [], count⟩).count (passes + 1)
termination_by (univ \ B).card
decreasing_by
  have hinv := (PassInv.init B count).passStep (τ := τ) L₁
  obtain ⟨t, ht⟩ := List.exists_mem_of_ne_nil _ ‹_›
  refine card_lt_card ⟨sdiff_subset_sdiff (Subset.refl _) hinv.subset, fun hsub => ?_⟩
  have htB := hinv.notMem t ht
  have htm : t ∈ (passStep τ L₁ ⟨B, [], count⟩).B := (hinv.mem_iff t).mpr (Or.inr ht)
  exact (mem_sdiff.mp (hsub (mem_sdiff.mpr ⟨mem_univ t, htB⟩))).2 htm

/-- **The B-quartet Inference Algorithm**, Step 3 (TINNiK, `notes/tinnik/readable.txt`, line 176), from the sets `B₀`
judged B-quartets at Step 2 and the quartet trees `τ` of Step 2(c). It returns the vector `B` and the numbers of
executions of the body of Step 3(a)(i), and of Step 3(a). -/
def bQuartetInference (B₀ : Finset (Finset X)) (τ : Set (QuartetTree X)) : InferOut X :=
  inferLoop τ B₀.toList B₀ 0 0

/-! #### The sets `otherSets` -/

section Others

variable {x y : Finset X}

omit [Fintype X] in
theorem mem_otherSets_iff (hx : x.card = 4) (hy : y.card = 4) (h3 : (x ∩ y).card = 3) {r : Finset X} :
    r ∈ otherSets x y ↔ r ⊆ x ∪ y ∧ r.card = 4 ∧ r ≠ x ∧ r ≠ y := by
  have h5 : (x ∪ y).card = 5 := by
    have := card_union_add_card_inter x y
    omega
  constructor
  · intro hr
    obtain ⟨z, hz, rfl⟩ := mem_image.mp hr
    obtain ⟨hzx, hzy⟩ := mem_inter.mp hz
    have hzu : z ∈ x ∪ y := mem_union_left _ hzx
    refine ⟨erase_subset _ _, by rw [card_erase_of_mem hzu, h5], ?_, ?_⟩
    · exact fun h => notMem_erase z (x ∪ y) (by rw [h]; exact hzx)
    · exact fun h => notMem_erase z (x ∪ y) (by rw [h]; exact hzy)
  · rintro ⟨hsub, hc, hrx, hry⟩
    have h1 : ((x ∪ y) \ r).card = 1 := by rw [card_sdiff_of_subset hsub, h5, hc]
    obtain ⟨z, hz⟩ := card_eq_one.mp h1
    have hzm : z ∈ (x ∪ y) \ r := hz ▸ mem_singleton_self z
    obtain ⟨hzu, hzr⟩ := mem_sdiff.mp hzm
    have hsubr : ∀ w, w ∈ x ∪ y → w ≠ z → w ∈ r := by
      intro w hw hne
      by_contra hwr
      have : w ∈ (x ∪ y) \ r := mem_sdiff.mpr ⟨hw, hwr⟩
      rw [hz] at this
      exact hne (mem_singleton.mp this)
    have hzx : z ∈ x := by
      by_contra hzx
      refine hrx (eq_of_subset_of_card_le (fun w hw => ?_) (by omega)).symm
      exact hsubr w (mem_union_left _ hw) fun h => hzx (h ▸ hw)
    have hzy : z ∈ y := by
      by_contra hzy
      refine hry (eq_of_subset_of_card_le (fun w hw => ?_) (by omega)).symm
      exact hsubr w (mem_union_right _ hw) fun h => hzy (h ▸ hw)
    refine mem_image.mpr ⟨z, mem_inter.mpr ⟨hzx, hzy⟩, ?_⟩
    ext w
    simp only [mem_erase]
    constructor
    · rintro ⟨hne, hw⟩
      exact hsubr w hw hne
    · intro hw
      exact ⟨fun h => hzr (h ▸ hw), hsub hw⟩

omit [Fintype X] in
theorem otherSets_comm (x y : Finset X) : otherSets x y = otherSets y x := by
  simp only [otherSets, inter_comm, union_comm]

omit [Fintype X] in
theorem hasSeparatingTree_comm {x y : Finset X} (h : HasSeparatingTree τ x y) : HasSeparatingTree τ y x := by
  obtain ⟨s, hs, ht, hsep⟩ := h
  refine ⟨s, hs, otherSets_comm x y ▸ ht, fun a ha e he => ?_⟩
  obtain ⟨h₁, h₂, h₃⟩ := hsep e he a ha
  exact ⟨h₂, h₁, fun B hB hc => h₃ B hB ⟨hc.2, hc.1⟩⟩

omit [Fintype X] in
/-- Two sets with labels as in the rule `BInferred`. -/
theorem labels_of_card_five {a b c d e : X} (h5 : ({a, b, c, d, e} : Finset X).card = 5) :
    (({a, b, c, d} : Finset X) ∩ {b, c, d, e}) = {b, c, d} ∧
      ({a, b, c, d} : Finset X) \ {b, c, d, e} = {a} ∧ ({b, c, d, e} : Finset X) \ {a, b, c, d} = {e} ∧
      otherSets ({a, b, c, d} : Finset X) {b, c, d, e} = {{a, b, c, e}, {a, b, d, e}, {a, c, d, e}} := by
  obtain ⟨hab, hac, had, hae, hbc, hbd, hbe, hcd, hce, hde⟩ := AllmanEtAl2023.ne_of_card_five h5
  have hi : (({a, b, c, d} : Finset X) ∩ {b, c, d, e}) = {b, c, d} := by
    ext w
    simp only [mem_inter, mem_insert, mem_singleton]
    grind
  have hun : ({a, b, c, d} : Finset X) ∪ {b, c, d, e} = {a, b, c, d, e} := by
    ext w
    simp only [mem_union, mem_insert, mem_singleton]
    grind
  refine ⟨hi, ?_, ?_, ?_⟩
  · ext w
    simp only [mem_sdiff, mem_insert, mem_singleton]
    grind
  · ext w
    simp only [mem_sdiff, mem_insert, mem_singleton]
    grind
  · rw [otherSets, hi, hun]
    ext r
    simp only [mem_image, mem_insert, mem_singleton]
    have hb' : ({a, b, c, d, e} : Finset X).erase b = {a, c, d, e} := by
      ext w
      simp only [mem_erase, mem_insert, mem_singleton]
      grind
    have hc' : ({a, b, c, d, e} : Finset X).erase c = {a, b, d, e} := by
      ext w
      simp only [mem_erase, mem_insert, mem_singleton]
      grind
    have hd' : ({a, b, c, d, e} : Finset X).erase d = {a, b, c, e} := by
      ext w
      simp only [mem_erase, mem_insert, mem_singleton]
      grind
    constructor
    · rintro ⟨z, (rfl | rfl | rfl), rfl⟩
      · exact Or.inr (Or.inr hb')
      · exact Or.inr (Or.inl hc')
      · exact Or.inl hd'
    · rintro (rfl | rfl | rfl)
      · exact ⟨d, Or.inr (Or.inr rfl), hd'⟩
      · exact ⟨c, Or.inr (Or.inl rfl), hc'⟩
      · exact ⟨b, Or.inl rfl, hb'⟩

omit [Fintype X] in
/-- The labels of two sets sharing three taxa, as in the rule `BInferred`. -/
theorem exists_labels (hx : x.card = 4) (hy : y.card = 4) (h3 : (x ∩ y).card = 3) :
    ∃ a b c d e : X, x = {a, b, c, d} ∧ y = {b, c, d, e} ∧ ({a, b, c, d, e} : Finset X).card = 5 := by
  obtain ⟨b, c, d, hbc, hbd, hcd, hi⟩ := card_eq_three.mp h3
  have hxd : (x \ y).card = 1 := by
    have := card_inter_add_card_sdiff x y
    omega
  have hyd : (y \ x).card = 1 := by
    have := card_inter_add_card_sdiff y x
    rw [inter_comm] at this
    omega
  obtain ⟨a, ha⟩ := card_eq_one.mp hxd
  obtain ⟨e, he⟩ := card_eq_one.mp hyd
  have ham : a ∈ x \ y := ha ▸ mem_singleton_self a
  have hem : e ∈ y \ x := he ▸ mem_singleton_self e
  obtain ⟨hax, hay⟩ := mem_sdiff.mp ham
  obtain ⟨hey, hex⟩ := mem_sdiff.mp hem
  have hin : ∀ w, w = b ∨ w = c ∨ w = d ↔ w ∈ x ∧ w ∈ y := by
    intro w
    rw [← mem_inter, hi]
    simp
  have hbm := (hin b).mp (Or.inl rfl)
  have hcm := (hin c).mp (Or.inr (Or.inl rfl))
  have hdm := (hin d).mp (Or.inr (Or.inr rfl))
  have hab : a ≠ b := fun h => hay (h ▸ hbm.2)
  have hac : a ≠ c := fun h => hay (h ▸ hcm.2)
  have had : a ≠ d := fun h => hay (h ▸ hdm.2)
  have hae : a ≠ e := fun h => hex (h ▸ hax)
  have hbe : b ≠ e := fun h => hex (h ▸ hbm.1)
  have hce : c ≠ e := fun h => hex (h ▸ hcm.1)
  have hde : d ≠ e := fun h => hex (h ▸ hdm.1)
  have hxeq : x = {a, b, c, d} := by
    ext w
    simp only [mem_insert, mem_singleton]
    constructor
    · intro hw
      by_cases hwy : w ∈ y
      · have := (hin w).mpr ⟨hw, hwy⟩
        tauto
      · have : w ∈ x \ y := mem_sdiff.mpr ⟨hw, hwy⟩
        rw [ha] at this
        exact Or.inl (mem_singleton.mp this)
    · rintro (rfl | rfl | rfl | rfl)
      · exact hax
      · exact hbm.1
      · exact hcm.1
      · exact hdm.1
  have hyeq : y = {b, c, d, e} := by
    ext w
    simp only [mem_insert, mem_singleton]
    constructor
    · intro hw
      by_cases hwx : w ∈ x
      · have := (hin w).mpr ⟨hwx, hw⟩
        tauto
      · have : w ∈ y \ x := mem_sdiff.mpr ⟨hw, hwx⟩
        rw [he] at this
        have := mem_singleton.mp this
        tauto
    · rintro (rfl | rfl | rfl | rfl)
      · exact hbm.2
      · exact hcm.2
      · exact hdm.2
      · exact hey
  refine ⟨a, b, c, d, e, hxeq, hyeq, ?_⟩
  simp [hab, hac, had, hae, hbc, hbd, hbe, hcd, hce, hde]

end Others

/-! #### The algorithm computes the closure `BInferred` -/

section Correct

variable {B₀ : Finset (Finset X)} {x y : Finset X} {σ : InferState X}

theorem mem_sharingThree : y ∈ sharingThree x ↔ y.card = 4 ∧ (y ∩ x).card = 3 := by
  simp [sharingThree]

/-- `compareStep` keeps sets of four taxa. -/
theorem four_compareStep (hx : x.card = 4) (hy : y ∈ sharingThree x) (h : ∀ q ∈ σ.B, q.card = 4) :
    ∀ q ∈ (compareStep τ x σ y).B, q.card = 4 := by
  unfold compareStep
  split_ifs
  · intro q hq
    rcases mem_union.mp hq with hq | hq
    · exact h q hq
    · obtain ⟨hyc, h3⟩ := mem_sharingThree.mp hy
      exact ((mem_otherSets_iff hx hyc (by rwa [inter_comm])).mp hq).2.1
  · exact h

theorem four_visitStep (hx : x.card = 4) (h : ∀ q ∈ σ.B, q.card = 4) : ∀ q ∈ (visitStep τ σ x).B, q.card = 4 :=
  foldl_induction (P := fun a : InferState X => ∀ q ∈ a.B, q.card = 4)
    (fun _ _ hy ha => four_compareStep hx (mem_toList.mp hy) ha) h

/-- Everything `compareStep` designates is inferred by the rule of `BInferred`. -/
theorem sound_compareStep (hx : x ∈ σ.B) (hy : y ∈ sharingThree x) (hf : ∀ q ∈ σ.B, q.card = 4)
    (hs : ∀ q ∈ σ.B, BInferred (B₀ : Set (Finset X)) τ q) :
    ∀ q ∈ (compareStep τ x σ y).B, BInferred (B₀ : Set (Finset X)) τ q := by
  unfold compareStep
  split_ifs with hc
  · intro q hq
    rcases mem_union.mp hq with hq | hq
    · exact hs q hq
    · obtain ⟨hyc, h3⟩ := mem_sharingThree.mp hy
      obtain ⟨a, b, c, d, e, rfl, rfl, h5⟩ := exists_labels (hf x hx) hyc (by rwa [inter_comm])
      obtain ⟨-, hxd, hyd, hoth⟩ := labels_of_card_five h5
      rw [hoth] at hq
      rcases hc.2 with ⟨r, hr⟩ | ⟨s, hsτ, hst, hsep⟩
      · obtain ⟨hr₁, hr₂⟩ := mem_inter.mp hr
        rw [hoth] at hr₁
        exact BInferred.ruleB a b c d e r q h5 (hs _ hx) (hs _ hc.1) hr₁ (hs r hr₂) hq
      · rw [hoth] at hst
        exact BInferred.ruleT a b c d e s q h5 (hs _ hx) (hs _ hc.1) hsτ hst
          (hsep a (by rw [hxd]; exact mem_singleton_self a) e (by rw [hyd]; exact mem_singleton_self e)) hq
  · exact hs

theorem sound_visitStep (hx : x ∈ σ.B) (hf : ∀ q ∈ σ.B, q.card = 4)
    (hs : ∀ q ∈ σ.B, BInferred (B₀ : Set (Finset X)) τ q) :
    ∀ q ∈ (visitStep τ σ x).B, BInferred (B₀ : Set (Finset X)) τ q := by
  have hxc := hf x hx
  have := foldl_induction (l := (sharingThree x).toList) (f := compareStep τ x)
    (P := fun a : InferState X => x ∈ a.B ∧ (∀ q ∈ a.B, q.card = 4) ∧ ∀ q ∈ a.B, BInferred (B₀ : Set (Finset X)) τ q)
    (fun a y hy ha => ⟨subset_B_compareStep x y a ha.1, four_compareStep hxc (mem_toList.mp hy) ha.2.1,
      sound_compareStep ha.1 (mem_toList.mp hy) ha.2.1 ha.2.2⟩) (a := σ) ⟨hx, hf, hs⟩
  exact this.2.2

omit [Fintype X] in
/-- Number of bodies in a loop of Step 3(a)(i). -/
theorem count_foldl_compareStep (l : List (Finset X)) (σ : InferState X) :
    (l.foldl (compareStep τ x) σ).count = σ.count + l.length := by
  induction l generalizing σ with
  | nil => rfl
  | cons y l ih =>
    have hc : (compareStep τ x σ y).count = σ.count + 1 := by
      unfold compareStep
      split_ifs <;> rfl
    rw [List.foldl_cons, ih, hc, List.length_cons]
    omega

/-- The sets sharing three taxa with a set of four: `4 (N - 4)`. -/
theorem card_sharingThree (hx : x.card = 4) : (sharingThree x).card = 4 * (Fintype.card X - 4) :=
  card_sharing_three hx

/-- The loop of Step 3(a)(i) executes its body `4 (N - 4)` times. -/
theorem count_visitStep (hx : x.card = 4) (σ : InferState X) :
    (visitStep τ σ x).count = σ.count + 4 * (Fintype.card X - 4) := by
  rw [visitStep, count_foldl_compareStep, length_toList, card_sharingThree hx]

/-- A pass executes the body `4 (N - 4)` times per entry of `L₁`. -/
theorem count_passStep {L₁ : List (Finset X)} (hL : ∀ x ∈ L₁, x.card = 4) (σ : InferState X) :
    (passStep τ L₁ σ).count = σ.count + 4 * (Fintype.card X - 4) * L₁.length := by
  induction L₁ generalizing σ with
  | nil => simp [passStep]
  | cons x L ih =>
    have h := ih (fun z hz => hL z (List.mem_cons_of_mem _ hz)) (visitStep τ σ x)
    rw [count_visitStep (hL x List.mem_cons_self)] at h
    simp only [passStep, List.foldl_cons] at h ⊢
    rw [h, List.length_cons, Nat.mul_add]
    omega

/-- Pairs of sets of `Done` sharing three taxa have had their comparison, up to `B`: if one of `otherSets` is in
`Done`, or a separating tree exists, then all of `otherSets` are in `B`. -/
def IsClosedOn (τ : Set (QuartetTree X)) (Done B : Finset (Finset X)) : Prop :=
  ∀ q ∈ Done, ∀ t ∈ Done, (q ∩ t).card = 3 → ((∃ r ∈ otherSets q t, r ∈ Done) ∨ HasSeparatingTree τ q t) →
    otherSets q t ⊆ B

omit [Fintype X] in
/-- The loop of Step 3(a)(i) only adds to `B`. -/
theorem subset_B_foldl (l : List (Finset X)) (σ : InferState X) : σ.B ⊆ (l.foldl (compareStep τ x) σ).B :=
  foldl_induction (P := fun a : InferState X => σ.B ⊆ a.B)
    (fun a y _ ha => ha.trans (subset_B_compareStep x y a)) (Subset.refl _)

omit [Fintype X] in
/-- The body fires at `y` in the loop of Step 3(a)(i), if it can. -/
theorem otherSets_subset_foldl {l : List (Finset X)} (hy : y ∈ l) (hyB : y ∈ σ.B)
    (hc : (∃ r ∈ otherSets x y, r ∈ σ.B) ∨ HasSeparatingTree τ x y) :
    otherSets x y ⊆ (l.foldl (compareStep τ x) σ).B := by
  induction l generalizing σ with
  | nil => exact absurd hy List.not_mem_nil
  | cons z l ih =>
    rw [List.foldl_cons]
    rcases List.mem_cons.mp hy with rfl | hy
    · refine Subset.trans ?_ (subset_B_foldl l _)
      have hfire : y ∈ σ.B ∧ ((otherSets x y ∩ σ.B).Nonempty ∨ HasSeparatingTree τ x y) := by
        refine ⟨hyB, ?_⟩
        rcases hc with ⟨r, hr, hrm⟩ | hc
        · exact Or.inl ⟨r, mem_inter.mpr ⟨hr, hrm⟩⟩
        · exact Or.inr hc
      unfold compareStep
      split_ifs
      exact subset_union_right
    · refine ih hy (subset_B_compareStep x z σ hyB) ?_
      rcases hc with ⟨r, hr, hrm⟩ | hc
      · exact Or.inl ⟨r, hr, subset_B_compareStep x z σ hrm⟩
      · exact Or.inr hc

/-- The comparison at `y` has been made once `x` is visited. -/
theorem otherSets_subset_visitStep (hy : y ∈ sharingThree x) (hyB : y ∈ σ.B)
    (hc : (∃ r ∈ otherSets x y, r ∈ σ.B) ∨ HasSeparatingTree τ x y) : otherSets x y ⊆ (visitStep τ σ x).B :=
  otherSets_subset_foldl (mem_toList.mpr hy) hyB hc

/-- **Why the loop reaches every pair**, TINNiK after the algorithm: "any time a new one is discovered it is compared
to all quartets that share three taxa with it. If one of these is a not-yet-inferred B-quartet, then this pair will be
compared again later". After visiting `x`, the pairs with `x` have had their comparison; a pair `q, t` of earlier sets
with `x` among their `otherSets` has its other sets designated because `x` was compared with `q`, and `t` is among
`otherSets x q`. -/
theorem IsClosedOn.visitStep {Done : Finset (Finset X)} (hcl : IsClosedOn τ Done σ.B) (hDone : Done ⊆ σ.B)
    (hx : x ∈ σ.B) (hf : ∀ q ∈ σ.B, q.card = 4) : IsClosedOn τ (insert x Done) (TINNiK.visitStep τ σ x).B := by
  have hsub := subset_B_visitStep (τ := τ) x σ
  have hxc := hf x hx
  -- a member of `insert x Done` among `otherSets x t` is in `Done`
  have hpair : ∀ t ∈ Done, (x ∩ t).card = 3 →
      ((∃ r ∈ otherSets x t, r ∈ insert x Done) ∨ HasSeparatingTree τ x t) →
      otherSets x t ⊆ (TINNiK.visitStep τ σ x).B := by
    intro t ht h3 hc
    have htc := hf t (hDone ht)
    refine otherSets_subset_visitStep (mem_sharingThree.mpr ⟨htc, by rwa [inter_comm]⟩) (hDone ht) ?_
    rcases hc with ⟨r, hr, hrm⟩ | hc
    · rcases mem_insert.mp hrm with rfl | hrD
      · exact absurd rfl ((mem_otherSets_iff hxc htc h3).mp hr).2.2.1
      · exact Or.inl ⟨r, hr, hDone hrD⟩
    · exact Or.inr hc
  intro q hq t ht h3 hc
  rcases mem_insert.mp hq with hqx | hq
  · rcases mem_insert.mp ht with htx | ht
    · rw [hqx, htx, inter_self, hxc] at h3
      omega
    · rw [hqx] at h3 hc ⊢
      exact hpair t ht h3 hc
  · have hqc := hf q (hDone hq)
    rcases mem_insert.mp ht with htx | ht
    · rw [htx] at h3 hc ⊢
      rw [otherSets_comm]
      refine hpair q hq (by rwa [inter_comm]) ?_
      rcases hc with ⟨r, hr, hrm⟩ | hc
      · exact Or.inl ⟨r, otherSets_comm q _ ▸ hr, hrm⟩
      · exact Or.inr (hasSeparatingTree_comm hc)
    · have htc := hf t (hDone ht)
      rcases hc with ⟨r, hr, hrm⟩ | hc
      · rcases mem_insert.mp hrm with hrx | hrD
        · -- `x` is among `otherSets q t`
          rw [hrx] at hr
          obtain ⟨z, hz, hze⟩ := mem_image.mp hr
          obtain ⟨hzq, hzt⟩ := mem_inter.mp hz
          obtain ⟨hxsub, -, hxq, hxt⟩ := (mem_otherSets_iff hqc htc h3).mp hr
          have hqx : (x ∩ q) = q.erase z := by
            ext w
            rw [← hze]
            simp only [mem_inter, mem_erase, mem_union]
            tauto
          have hxq3 : (x ∩ q).card = 3 := by
            rw [hqx, card_erase_of_mem hzq, hqc]
          have hun : x ∪ q = q ∪ t := by
            ext w
            rw [← hze]
            simp only [mem_union, mem_erase]
            constructor
            · tauto
            · intro hw
              by_cases hwz : w = z
              · exact Or.inr (hwz ▸ hzq)
              · exact Or.inl ⟨hwz, hw⟩
          have htq : t ≠ q := by
            rintro rfl
            rw [inter_self, hqc] at h3
            omega
          have hto : t ∈ otherSets x q :=
            (mem_otherSets_iff hxc hqc hxq3).mpr ⟨hun ▸ subset_union_right, htc, hxt.symm, htq⟩
          have hfire := otherSets_subset_visitStep (τ := τ) (x := x) (y := q) (σ := σ)
            (mem_sharingThree.mpr ⟨hqc, by rwa [inter_comm]⟩) (hDone hq) (Or.inl ⟨t, hto, hDone ht⟩)
          intro w hw
          obtain ⟨hwsub, hwc, hwq, hwt⟩ := (mem_otherSets_iff hqc htc h3).mp hw
          by_cases hwx : w = x
          · exact hsub (hwx ▸ hx)
          · exact hfire ((mem_otherSets_iff hxc hqc hxq3).mpr ⟨hun ▸ hwsub, hwc, hwx, hwq⟩)
        · exact (hcl q hq t ht h3 (Or.inl ⟨r, hr, hrD⟩)).trans hsub
      · exact (hcl q hq t ht h3 (Or.inr hc)).trans hsub

/-- A pass over `L₁` extends the closed sets by `L₁`. -/
theorem IsClosedOn.passStep {L₁ : List (Finset X)} {Done : Finset (Finset X)} (hcl : IsClosedOn τ Done σ.B)
    (hDone : Done ⊆ σ.B) (hL : ∀ x ∈ L₁, x ∈ σ.B) (hf : ∀ q ∈ σ.B, q.card = 4) :
    IsClosedOn τ (Done ∪ L₁.toFinset) (TINNiK.passStep τ L₁ σ).B := by
  induction L₁ generalizing Done σ with
  | nil =>
    simpa [TINNiK.passStep] using hcl
  | cons x L ih =>
    have hx : x ∈ σ.B := hL x List.mem_cons_self
    have h := ih (Done := insert x Done) (σ := TINNiK.visitStep τ σ x) (hcl.visitStep hDone hx hf)
      (insert_subset (subset_B_visitStep x σ hx) (hDone.trans (subset_B_visitStep x σ)))
      (fun z hz => subset_B_visitStep x σ (hL z (List.mem_cons_of_mem _ hz))) (four_visitStep (hf x hx) hf)
    have heq : Done ∪ (x :: L).toFinset = insert x Done ∪ L.toFinset := by
      ext w
      simp only [mem_union, List.mem_toFinset, List.mem_cons, mem_insert]
      tauto
    rw [heq]
    exact h

theorem four_passStep {L₁ : List (Finset X)} (hL : ∀ x ∈ L₁, x ∈ σ.B) (hf : ∀ q ∈ σ.B, q.card = 4) :
    ∀ q ∈ (passStep τ L₁ σ).B, q.card = 4 := by
  induction L₁ generalizing σ with
  | nil => exact hf
  | cons x L ih =>
    have hx : x ∈ σ.B := hL x List.mem_cons_self
    exact ih (σ := visitStep τ σ x) (fun z hz => subset_B_visitStep x σ (hL z (List.mem_cons_of_mem _ hz)))
      (four_visitStep (hf x hx) hf)

theorem sound_passStep {L₁ : List (Finset X)} (hL : ∀ x ∈ L₁, x ∈ σ.B) (hf : ∀ q ∈ σ.B, q.card = 4)
    (hs : ∀ q ∈ σ.B, BInferred (B₀ : Set (Finset X)) τ q) :
    ∀ q ∈ (passStep τ L₁ σ).B, BInferred (B₀ : Set (Finset X)) τ q := by
  induction L₁ generalizing σ with
  | nil => exact hs
  | cons x L ih =>
    have hx : x ∈ σ.B := hL x List.mem_cons_self
    exact ih (σ := visitStep τ σ x) (fun z hz => subset_B_visitStep x σ (hL z (List.mem_cons_of_mem _ hz)))
      (four_visitStep (hf x hx) hf) (sound_visitStep hx hf hs)

/-- The invariant of the loop of Step 3: `Done` have been visited, `L₁` are waiting, and they make up `B`. -/
theorem inferLoop_spec (L₁ : List (Finset X)) (B : Finset (Finset X)) (count passes : ℕ) (Done : Finset (Finset X))
    (hB : B = Done ∪ L₁.toFinset) (hdis : Disjoint Done L₁.toFinset) (hnd : L₁.Nodup) (hf : ∀ q ∈ B, q.card = 4)
    (hs : ∀ q ∈ B, BInferred (B₀ : Set (Finset X)) τ q) (hcl : IsClosedOn τ Done B)
    (hc : count = 4 * (Fintype.card X - 4) * Done.card) (hp : passes ≤ Done.card) :
    B ⊆ (inferLoop τ L₁ B count passes).B ∧
      IsClosedOn τ (inferLoop τ L₁ B count passes).B (inferLoop τ L₁ B count passes).B ∧
      (∀ q ∈ (inferLoop τ L₁ B count passes).B, BInferred (B₀ : Set (Finset X)) τ q) ∧
      (∀ q ∈ (inferLoop τ L₁ B count passes).B, q.card = 4) ∧
      (inferLoop τ L₁ B count passes).count = 4 * (Fintype.card X - 4) * (inferLoop τ L₁ B count passes).B.card ∧
      (inferLoop τ L₁ B count passes).passes ≤ (inferLoop τ L₁ B count passes).B.card + 1 := by
  have hstep : ∀ {L₁ : List (Finset X)} {B : Finset (Finset X)} {count : ℕ} {Done : Finset (Finset X)},
      B = Done ∪ L₁.toFinset → Disjoint Done L₁.toFinset → L₁.Nodup → (∀ q ∈ B, q.card = 4) →
      (∀ q ∈ B, BInferred (B₀ : Set (Finset X)) τ q) → IsClosedOn τ Done B →
      count = 4 * (Fintype.card X - 4) * Done.card →
      IsClosedOn τ (Done ∪ L₁.toFinset) (passStep τ L₁ ⟨B, [], count⟩).B ∧
      (∀ q ∈ (passStep τ L₁ ⟨B, [], count⟩).B, q.card = 4) ∧
      (∀ q ∈ (passStep τ L₁ ⟨B, [], count⟩).B, BInferred (B₀ : Set (Finset X)) τ q) ∧
      (passStep τ L₁ ⟨B, [], count⟩).count = 4 * (Fintype.card X - 4) * (Done ∪ L₁.toFinset).card := by
    intro L₁ B count Done hB hdis hnd hf hs hcl hc
    have hLB : ∀ x ∈ L₁, x ∈ B := fun x hx => hB ▸ mem_union_right _ (List.mem_toFinset.mpr hx)
    have hDB : Done ⊆ B := hB ▸ subset_union_left
    refine ⟨IsClosedOn.passStep (σ := ⟨B, [], count⟩) hcl hDB hLB hf, four_passStep (σ := ⟨B, [], count⟩) hLB hf,
      sound_passStep (σ := ⟨B, [], count⟩) hLB hf hs, ?_⟩
    rw [count_passStep (fun x hx => hf x (hLB x hx)), card_union_of_disjoint hdis,
      List.toFinset_card_of_nodup hnd, Nat.mul_add]
    simp only [hc]
  fun_induction inferLoop τ L₁ B count passes generalizing Done
  case case1 L₁ B count passes hL =>
    obtain ⟨h₁, h₂, h₃, h₄⟩ := hstep hB hdis hnd hf hs hcl hc
    have hinv := (PassInv.init B count).passStep (τ := τ) L₁
    have hBeq : (passStep τ L₁ ⟨B, [], count⟩).B = B := by
      ext t
      rw [hinv.mem_iff t, hL]
      simp
    have hDB : Done.card ≤ B.card := card_le_card (hB ▸ subset_union_left)
    rw [← hB, hBeq] at h₁
    rw [hBeq] at h₂ h₃
    rw [← hB] at h₄
    dsimp only
    rw [hBeq]
    exact ⟨Subset.refl _, h₁, h₃, h₂, h₄, by omega⟩
  case case2 L₁ B count passes hL ih =>
    obtain ⟨h₁, h₂, h₃, h₄⟩ := hstep hB hdis hnd hf hs hcl hc
    have hinv := (PassInv.init B count).passStep (τ := τ) L₁
    have hB' : (passStep τ L₁ ⟨B, [], count⟩).B =
        (Done ∪ L₁.toFinset) ∪ (passStep τ L₁ ⟨B, [], count⟩).L₂.toFinset := by
      ext t
      rw [hinv.mem_iff t, ← hB, mem_union, List.mem_toFinset]
    have hdis' : Disjoint (Done ∪ L₁.toFinset) (passStep τ L₁ ⟨B, [], count⟩).L₂.toFinset := by
      rw [← hB, disjoint_right]
      exact fun t ht => hinv.notMem t (List.mem_toFinset.mp ht)
    have hLne : L₁ ≠ [] := by
      rintro rfl
      exact hL rfl
    have hp' : passes + 1 ≤ (Done ∪ L₁.toFinset).card := by
      rw [card_union_of_disjoint hdis, List.toFinset_card_of_nodup hnd]
      have := List.length_pos_of_ne_nil hLne
      omega
    obtain ⟨i₁, i₂, i₃, i₄, i₅, i₆⟩ := ih (Done := Done ∪ L₁.toFinset) hB' hdis' hinv.nodup h₂ h₃ h₁ h₄ hp'
    exact ⟨hinv.subset.trans i₁, i₂, i₃, i₄, i₅, i₆⟩

/-- The start of the loop. -/
theorem bQuartetInference_spec (hB₀ : ∀ q ∈ B₀, q.card = 4) (τ : Set (QuartetTree X)) :
    B₀ ⊆ (bQuartetInference B₀ τ).B ∧
      IsClosedOn τ (bQuartetInference B₀ τ).B (bQuartetInference B₀ τ).B ∧
      (∀ q ∈ (bQuartetInference B₀ τ).B, BInferred (B₀ : Set (Finset X)) τ q) ∧
      (∀ q ∈ (bQuartetInference B₀ τ).B, q.card = 4) ∧
      (bQuartetInference B₀ τ).count = 4 * (Fintype.card X - 4) * (bQuartetInference B₀ τ).B.card ∧
      (bQuartetInference B₀ τ).passes ≤ (bQuartetInference B₀ τ).B.card + 1 :=
  inferLoop_spec B₀.toList B₀ 0 0 ∅ (by simp) (by simp) (nodup_toList _) hB₀ (fun _ hq => BInferred.base _ hq)
    (fun _ hq => absurd hq (notMem_empty _)) (by simp) (by simp)

/-- **The output of the algorithm is the closure of `BInferred`**, as the docstring of `BInferred` says of the
worklist of the printed algorithm. -/
theorem mem_bQuartetInference_iff (hB₀ : ∀ q ∈ B₀, q.card = 4) (τ : Set (QuartetTree X)) {q : Finset X} :
    q ∈ (bQuartetInference B₀ τ).B ↔ BInferred (B₀ : Set (Finset X)) τ q := by
  obtain ⟨hsub, hcl, hsound, -, -, -⟩ := bQuartetInference_spec hB₀ τ
  refine ⟨hsound q, fun h => ?_⟩
  have hthree : ∀ {a b c d e : X}, ({a, b, c, d, e} : Finset X).card = 5 →
      (({a, b, c, d} : Finset X) ∩ {b, c, d, e}).card = 3 := by
    intro a b c d e h5
    obtain ⟨hi, -, -, -⟩ := labels_of_card_five h5
    obtain ⟨-, -, -, -, hbc, hbd, -, hcd, -, -⟩ := AllmanEtAl2023.ne_of_card_five h5
    rw [hi]
    simp [hbc, hbd, hcd]
  induction h with
  | base q hq => exact hsub hq
  | ruleB a b c d e t q h5 _ _ ht _ hq ih₁ ih₂ ih₃ =>
    obtain ⟨-, -, -, hoth⟩ := labels_of_card_five h5
    refine hcl _ ih₁ _ ih₂ (hthree h5) (Or.inl ⟨t, hoth ▸ ht, ih₃⟩) (hoth ▸ hq)
  | ruleT a b c d e s q h5 _ _ hs hst hsep hq ih₁ ih₂ =>
    obtain ⟨-, hxd, hyd, hoth⟩ := labels_of_card_five h5
    refine hcl _ ih₁ _ ih₂ (hthree h5) (Or.inr ⟨s, hs, hoth ▸ hst, fun a' ha' e' he' => ?_⟩) (hoth ▸ hq)
    rw [hxd] at ha'
    rw [hyd] at he'
    rw [mem_singleton.mp ha', mem_singleton.mp he']
    exact hsep

/-- **The count of the printed algorithm**, TINNiK after the algorithm: "there can be at most `C(N, 4)` B-quartets
that can appear in the lists L through all passes through step 3a, and each is compared in step 3(a)i to `O(N)` other
sets of 4-taxa". Exactly: each B-quartet is compared with the `4 (N - 4)` sets sharing three taxa with it, once. -/
theorem count_bQuartetInference (hB₀ : ∀ q ∈ B₀, q.card = 4) (τ : Set (QuartetTree X)) :
    (bQuartetInference B₀ τ).count = 4 * (Fintype.card X - 4) * (bQuartetInference B₀ τ).B.card :=
  (bQuartetInference_spec hB₀ τ).2.2.2.2.1

omit [DecidableEq X] in
/-- The B-quartets are at most `C(N, 4)`. -/
theorem card_le_choose_of_forall_card {S : Finset (Finset X)} (hS : ∀ q ∈ S, q.card = 4) :
    S.card ≤ (Fintype.card X).choose 4 := by
  have : S ⊆ powersetCard 4 univ := fun q hq => mem_powersetCard.mpr ⟨subset_univ q, hS q hq⟩
  simpa [card_powersetCard] using card_le_card this

/-- All passes of Step 3 execute the body of Step 3(a)(i) at most `4 (N - 4) C(N, 4)` times: the paper's `O(N⁵)`. -/
theorem count_bQuartetInference_le (hB₀ : ∀ q ∈ B₀, q.card = 4) (τ : Set (QuartetTree X)) :
    (bQuartetInference B₀ τ).count ≤ 4 * (Fintype.card X - 4) * (Fintype.card X).choose 4 := by
  rw [count_bQuartetInference hB₀]
  exact Nat.mul_le_mul_left _ (card_le_choose_of_forall_card (bQuartetInference_spec hB₀ τ).2.2.2.1)

/-- Step 3(a) runs at most `C(N, 4) + 1` times: each pass but the last has entries, and these are not repeated. -/
theorem passes_bQuartetInference_le (hB₀ : ∀ q ∈ B₀, q.card = 4) (τ : Set (QuartetTree X)) :
    (bQuartetInference B₀ τ).passes ≤ (Fintype.card X).choose 4 + 1 :=
  (bQuartetInference_spec hB₀ τ).2.2.2.2.2.trans
    (Nat.add_le_add_right (card_le_choose_of_forall_card (bQuartetInference_spec hB₀ τ).2.2.2.1) 1)

variable {ml : (QuartetTree X → ℝ) → Finset X → QuartetTree X} {α β : ℝ} {c : QuartetTree X → ℝ}

/-- The B-quartets of the algorithm `TINNiK`, as the printed algorithm finds them. -/
theorem setOf_bInferred_eq_bQuartetInference :
    {q | BInferred (testedB ml α β c) (testedT ml α β c) q} =
      ((bQuartetInference (univ.filter (· ∈ testedB ml α β c)) (testedT ml α β c)).B : Set (Finset X)) := by
  have hco : ((univ.filter (· ∈ testedB ml α β c) : Finset (Finset X)) : Set (Finset X)) = testedB ml α β c := by
    ext q
    simp
  ext q
  rw [mem_coe, mem_bQuartetInference_iff (fun q hq => (mem_filter.mp hq).2.1), hco]
  rfl

end Correct

/-! ### Trees: how many splits -/

section Trees

variable {H : Finset (Finset X)}

/-- The clusters other than the root are the children of the clusters, each of one. -/
theorem sum_card_childClusters (hH : IsHierarchy H) : ∑ A ∈ H, (childClusters H A).card + 1 = H.card := by
  have hunion : H.biUnion (childClusters H) = H.erase univ := by
    ext C
    simp only [mem_biUnion, mem_erase]
    constructor
    · rintro ⟨A, -, hC⟩
      obtain ⟨hCH, hCA, -⟩ := mem_childClusters.mp hC
      exact ⟨fun h => (h ▸ hCA).2 (subset_univ A), hCH⟩
    · rintro ⟨hCu, hCH⟩
      exact ⟨_, hH.parentCluster_mem hCH hCu, hH.mem_childClusters_parentCluster hCH hCu⟩
  have hdis : ∀ A ∈ H, ∀ A' ∈ H, A ≠ A' → Disjoint (childClusters H A) (childClusters H A') := by
    intro A hA A' hA' hne
    rw [disjoint_left]
    intro C hC hC'
    exact hne ((hH.parentCluster_eq_of_mem_childClusters hA hC).symm.trans
      (hH.parentCluster_eq_of_mem_childClusters hA' hC'))
  have hcard := card_biUnion hdis
  rw [hunion, card_erase_of_mem hH.1] at hcard
  have := card_pos.mpr ⟨_, hH.1⟩
  omega

omit [DecidableEq X] in
/-- The clusters of one taxon are `N` many. -/
theorem card_filter_not_two_le (hH : IsHierarchy H) : (H.filter fun A => ¬ 2 ≤ A.card).card = Fintype.card X := by
  have heq : (H.filter fun A => ¬ 2 ≤ A.card) = univ.image fun x : X => ({x} : Finset X) := by
    ext A
    simp only [mem_filter, mem_image, mem_univ, true_and]
    constructor
    · rintro ⟨hA, h2⟩
      have hpos := card_pos.mpr (hH.2.2.1 A hA)
      obtain ⟨x, rfl⟩ := card_eq_one.mp (by omega : A.card = 1)
      exact ⟨x, rfl⟩
    · rintro ⟨x, rfl⟩
      exact ⟨hH.2.1 x, by simp⟩
  rw [heq, card_image_of_injective _ singleton_injective, card_univ]

/-- A hierarchy has at most `N - 1` clusters of at least two taxa. -/
theorem card_filter_two_le_add_one_le (hH : IsHierarchy H) :
    (H.filter fun A => 2 ≤ A.card).card + 1 ≤ Fintype.card X := by
  have hsum := sum_card_childClusters hH
  have htot := card_filter_add_card_filter_not (s := H) (fun A : Finset X => 2 ≤ A.card)
  rw [card_filter_not_two_le hH] at htot
  have hle : 2 * (H.filter fun A => 2 ≤ A.card).card ≤ ∑ A ∈ H, (childClusters H A).card := by
    calc 2 * (H.filter fun A => 2 ≤ A.card).card = ∑ _A ∈ H.filter (fun A => 2 ≤ A.card), 2 := by
          rw [sum_const, smul_eq_mul, mul_comm]
      _ ≤ ∑ A ∈ H.filter (fun A => 2 ≤ A.card), (childClusters H A).card :=
          sum_le_sum fun A hA => hH.two_le_card_childClusters (mem_filter.mp hA).2
      _ ≤ ∑ A ∈ H, (childClusters H A).card := sum_le_sum_of_subset (filter_subset _ _)
  omega

/-- A hierarchy has at most `2 N - 1` clusters. -/
theorem card_add_one_le_of_isHierarchy (hH : IsHierarchy H) : H.card + 1 ≤ 2 * Fintype.card X := by
  have htot := card_filter_add_card_filter_not (s := H) (fun A : Finset X => 2 ≤ A.card)
  rw [card_filter_not_two_le hH] at htot
  have := card_filter_two_le_add_one_le hH
  omega

/-- **A tree on `N` taxa has at most `4 N - 4` sides of splits**, so at most `2 N - 2` edges. -/
theorem card_le_of_isUnrootedTree {T : Finset (Finset X)} (hT : IsUnrootedTree T) :
    T.card ≤ 4 * Fintype.card X - 4 := by
  obtain ⟨H, hH, rfl⟩ := hT
  have h₁ := card_add_one_le_of_isHierarchy hH
  have h₂ : (unroot H).card ≤ 2 * (H.erase univ).card := by
    refine (card_union_le _ _).trans ?_
    have := card_image_le (s := H.erase univ) (f := compl)
    omega
  rw [card_erase_of_mem hH.1] at h₂
  omega

end Trees

/-! ### The steps of TINNiK -/

section Steps

omit [DecidableEq X] in
variable (X) in
/-- The sets of four taxa. -/
theorem card_fourSets : (univ.filter fun q : Finset X => q.card = 4).card = (Fintype.card X).choose 4 := by
  have : (univ.filter fun q : Finset X => q.card = 4) = powersetCard 4 univ := by
    ext q
    simp [mem_powersetCard]
  rw [this, card_powersetCard, card_univ]

variable (X) in
/-- The quartet trees: three on each set of four taxa. -/
theorem card_quartetTree : Fintype.card (QuartetTree X) = 3 * (Fintype.card X).choose 4 := by
  rw [← card_univ, card_eq_sum_card_fiberwise (f := QuartetTree.taxa) (t := univ.filter fun q : Finset X => q.card = 4)
    (fun s _ => mem_filter.mpr ⟨mem_univ _, s.card_taxa⟩)]
  have hfib : ∀ q ∈ univ.filter (fun q : Finset X => q.card = 4),
      (univ.filter fun s : QuartetTree X => s.taxa = q).card = 3 :=
    fun q hq => card_treesOn (mem_filter.mp hq).2
  rw [sum_congr rfl hfib, sum_const, card_fourSets, smul_eq_mul, mul_comm]

variable (X) in
/-- **Step 1 of TINNiK**, "tabulate all qcCFs for the taxon set `X` across all gene trees": `O(mN⁴)`. Counted: the
evaluations of `Displays (sides (ω i)) s` in the table `quartetCount sides ω s`, for all quartet trees `s` and all `m`
gene trees. Each is one look-up per gene tree, given the look-up on one gene tree in constant time, as the paper takes
it. -/
theorem card_tabulation (m : ℕ) :
    (univ : Finset (QuartetTree X × Fin m)).card = 3 * (Fintype.card X).choose 4 * m := by
  simp [card_quartetTree]

variable (X) in
/-- **Step 2 of the B-quartet Inference Algorithm**, the hypothesis tests. Counted: the statistics that `testedB` and
`testedT` evaluate, one `starStat` and the three `lineStat` of each set of four taxa, from which `cutStat`, `ml` and
`cutPValue` come. -/
theorem sum_step2_statistics :
    ∑ q ∈ univ.filter (fun q : Finset X => q.card = 4), (1 + (treesOn q).card) = 4 * (Fintype.card X).choose 4 := by
  have h : ∀ q ∈ univ.filter (fun q : Finset X => q.card = 4), 1 + (treesOn q).card = 4 :=
    fun q hq => by rw [card_treesOn (mem_filter.mp hq).2]
  rw [sum_congr rfl h, sum_const, card_fourSets, smul_eq_mul, mul_comm]

/-- The sets of four taxa containing two given taxa: the sets that `quartetDistance` looks at, for one pair of taxa.
-/
theorem card_fourSets_superset {p : Finset X} (hp : p.card = 2) :
    (univ.filter fun q : Finset X => q.card = 4 ∧ p ⊆ q).card = (Fintype.card X - 2).choose 2 := by
  have hcompl : pᶜ.card = Fintype.card X - 2 := by rw [card_compl, hp]
  rw [← hcompl, ← card_powersetCard]
  refine card_nbij' (fun q => q \ p) (fun r => r ∪ p) ?_ ?_ ?_ ?_
  · intro q hq
    obtain ⟨-, hq4, hpq⟩ := mem_filter.mp hq
    refine mem_powersetCard.mpr ⟨fun x hx => mem_compl.mpr (mem_sdiff.mp hx).2, ?_⟩
    rw [card_sdiff_of_subset hpq, hq4, hp]
  · intro r hr
    obtain ⟨hsub, hc⟩ := mem_powersetCard.mp hr
    refine mem_filter.mpr ⟨mem_univ _, ?_, subset_union_right⟩
    rw [card_union_of_disjoint, hc, hp]
    exact disjoint_left.mpr fun x hx hxp => (mem_compl.mp (hsub hx)) hxp
  · intro q hq
    exact sdiff_union_of_subset (mem_filter.mp hq).2.2
  · intro r hr
    have hsub := (mem_powersetCard.mp hr).1
    ext x
    simp only [mem_sdiff, mem_union]
    constructor
    · rintro ⟨h | h, hn⟩
      · exact h
      · exact absurd h hn
    · exact fun hx => ⟨Or.inl hx, mem_compl.mp (hsub hx)⟩

/-- **Step 3 of TINNiK**, the quartet distance: `O(N⁴)`. Counted: the pairs of a pair of taxa and a set of four taxa
containing it. Each is a look-up in `B` or `τ` and an update of `quartetDistance`. There are `6 C(N, 4)`, as each set
has six pairs. -/
theorem sum_distance_incidences :
    ∑ p ∈ univ.filter (fun p : Finset X => p.card = 2), (univ.filter fun q : Finset X => q.card = 4 ∧ p ⊆ q).card =
      6 * (Fintype.card X).choose 4 := by
  have hp : (univ.filter fun p : Finset X => p.card = 2).card = (Fintype.card X).choose 2 := by
    have : (univ.filter fun p : Finset X => p.card = 2) = powersetCard 2 univ := by
      ext q
      simp [mem_powersetCard]
    rw [this, card_powersetCard, card_univ]
  rw [sum_congr rfl fun p hp => card_fourSets_superset (mem_filter.mp hp).2, sum_const, hp, smul_eq_mul]
  have h := Nat.choose_mul (n := Fintype.card X) (k := 4) (s := 2) (by norm_num)
  have h42 : Nat.choose 4 2 = 6 := by decide
  rw [h42, show (4 : ℕ) - 2 = 2 from rfl] at h
  rw [← h, mul_comm]

/-- The operations that TINNiK's five steps perform, on `N` taxa and `m` gene trees, with a method of `nj` operations
in its Step 4. Step 1: `card_tabulation`. Step 2: `sum_step2_statistics`, then for Step 3 of the inference at most
`13` reads or updates of the table in each of the `4 (N - 4) C(N, 4)` bodies (`compareStep`,
`count_bQuartetInference_le`: `y`; three others; six quartet trees; three updates), and one per pass
(`passes_bQuartetInference_le`). Step 3: `sum_distance_incidences`. Step 5: one per side of a split of the tree
returned (`card_le_of_isUnrootedTree`). -/
def tinnikOperations (N m nj : ℕ) : ℕ :=
  3 * N.choose 4 * m + 4 * N.choose 4 + 13 * (4 * (N - 4) * N.choose 4) + (N.choose 4 + 1) + 6 * N.choose 4 + nj +
    (4 * N - 4)

/-- **TINNiK's time, as printed: "the computational times for steps 1–5 using NJ in step 4 are, respectively,
`O(mN⁴)`, `O(N⁵)`, `O(N⁴)`, `O(N³)`, `O(N)`, for a combined `O((m + N) N⁴)`"** (`notes/tinnik/readable.txt`, line
196), with `nj ≤ c N³` for NJ. -/
theorem tinnikOperations_le {N m nj c : ℕ} (hN : 1 ≤ N) (hnj : nj ≤ c * N ^ 3) :
    tinnikOperations N m nj ≤ (68 + c) * ((m + N) * N ^ 4) := by
  have hC : N.choose 4 ≤ N ^ 4 := Nat.choose_le_pow N 4
  have hP : 1 ≤ N ^ 4 := Nat.one_le_pow _ _ hN
  have hsub : (N - 4) * N.choose 4 ≤ N * N ^ 4 := Nat.mul_le_mul (Nat.sub_le _ _) hC
  have hPQ : N ^ 4 ≤ N * N ^ 4 := Nat.le_mul_of_pos_left _ hN
  have hNQ : N ≤ N * N ^ 4 := Nat.le_mul_of_pos_right _ hP
  have hN3 : N ^ 3 ≤ N * N ^ 4 := by
    calc N ^ 3 ≤ N ^ 5 := Nat.pow_le_pow_right hN (by norm_num)
      _ = N * N ^ 4 := by ring
  have h1 : N.choose 4 * m ≤ N ^ 4 * m := Nat.mul_le_mul_right _ hC
  have h2 : nj ≤ c * (N * N ^ 4) := hnj.trans (Nat.mul_le_mul_left _ hN3)
  have hexp : (68 + c) * ((m + N) * N ^ 4) =
      68 * (N ^ 4 * m) + 68 * (N * N ^ 4) + c * (N ^ 4 * m) + c * (N * N ^ 4) := by
    ring
  rw [hexp]
  have hsmall : 4 * N - 4 ≤ 4 * (N * N ^ 4) := by omega
  simp only [tinnikOperations]
  have hmul : 13 * (4 * (N - 4) * N.choose 4) = 52 * ((N - 4) * N.choose 4) := by ring
  rw [hmul]
  have hc3 : 3 * N.choose 4 * m = 3 * (N.choose 4 * m) := by ring
  rw [hc3]
  have hnn : 0 ≤ c * (N ^ 4 * m) := Nat.zero_le _
  omega

end Steps

end TINNiK
