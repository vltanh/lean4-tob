module

public import Gusfield2007.Basic

/-!
# Gusfield et al. 2007, Section 3.1: the structure of `M`

Dominant classes and characters: Lemma 1, Theorem 2, Corollary 1, Lemma 2.
-/

@[expose] public section

open scoped Classical

namespace Gusfield2007

variable {ι : Type*}

/-- The statement of the definition (line 200): `(a, b)` are dominant for `i`, `i'` when, with `X = {r | r i = a}` and
`Y = {r | r i' = !b}`, we have `Y ⊆ X`, or equivalently `X̄ ⊆ Ȳ`. The bridge between `IsDominantPair` and classes. -/
theorem isDominantPair_iff (M : Finset (ι → Bool)) (i i' : ι) (a b : Bool) :
    IsDominantPair M i i' a b ↔ ∀ r ∈ M, r i' = !b → r i = a := by
  refine forall₂_congr fun r _ => ?_
  cases h : r i' <;> cases b <;> simp

/-- **Line 200** (`g:compatible_dominant`). Sites that aren't incompatible have dominant characters: "one class of the `i`
bipartition must strictly contain one class of the `i'` bipartition". -/
theorem exists_isDominantPair (M : Finset (ι → Bool)) {i i' : ι} (h : ¬ Incompatible M i i') :
    ∃ a b, IsDominantPair M i i' a b := by
  unfold Incompatible at h
  push Not at h
  obtain ⟨a, b, h⟩ := h
  refine ⟨!a, !b, fun r hr => ?_⟩
  by_cases h₁ : r i = a
  · right
    have := h r hr h₁
    cases hb : r i' <;> cases b <;> simp_all
  · left
    cases hb : r i <;> cases a <;> simp_all

/-- **Lemma 1** (`g:lem1`). Let `i` be a site out of the connected component `C'` of `G(M)`, and `i'`, `j'` sites of `C'`. "The
dominant class of `i` with respect to the pair `i, j'` is the dominant class of `i` with respect to the pair `i, i'`"
(line 206). The class of `i` is the state `a`.

The printed proof has a misprint at line 210: "`Y ∩ W̄ = ∅`, and `i` and `k'` can't be incompatible" should read `i'` and `k'`:
`i` and `k'` are in different components, and it's the incompatibility of `i'` and `k'` that's contradicted. -/
theorem lemma1 (M : Finset (ι → Bool)) {i i' j' : ι} (hi : ¬ (incompatGraph M).Reachable i i')
    (hj : (incompatGraph M).Reachable i' j') {a b : Bool} (h : IsDominantPair M i i' a b) :
    ∃ b', IsDominantPair M i j' a b' := by
  rw [SimpleGraph.reachable_iff_reflTransGen] at hj
  induction hj with
  | refl => exact ⟨b, h⟩
  | @tail u k hu hadj ih =>
    obtain ⟨b₁, hb₁⟩ := ih
    have hreach : (incompatGraph M).Reachable i' k :=
      ((SimpleGraph.reachable_iff_reflTransGen _ _).2 hu).trans hadj.reachable
    have hik : ¬ Incompatible M i k := fun hinc =>
      hi ((SimpleGraph.Adj.reachable (G := incompatGraph M) hinc).trans hreach.symm)
    obtain ⟨a₂, b₂, hd⟩ := exists_isDominantPair M hik
    by_cases ha : a₂ = a
    · exact ⟨b₂, ha ▸ hd⟩
    · exfalso
      obtain ⟨r, hr, h₁, h₂⟩ := hadj (!b₁) (!b₂)
      have hri : r i = a := (hb₁ r hr).resolve_right (by simp [h₁])
      rcases hd r hr with h₃ | h₃
      · exact ha (h₃.symm.trans hri)
      · simp [h₂] at h₃

/-- **Line 212** (`g:dom_exists`). "With respect to the `(C, C')` pair of connected components, each site in `C ∪ C'` has a well-defined
dominant class". -/
theorem exists_isDominantFor (M : Finset (ι → Bool)) {c c' : (incompatGraph M).ConnectedComponent} (hc : c ≠ c') :
    ∃ d d', IsDominantFor M c.supp c'.supp d d' := by
  sorry

/-- **Lines 200, 212** (`g:dom_unique`). The dominant characters are unique, under the standing assumption, unless both components are
trivial (where line 202 allows a choice for identical sites). -/
theorem isDominantFor_unique {M : Finset (ι → Bool)} (hC : NoConstantColumn M)
    {c c' : (incompatGraph M).ConnectedComponent} (hc : c ≠ c') (hnt : c.supp.Nontrivial ∨ c'.supp.Nontrivial)
    {d₁ d₂ : c.supp → Bool} {d₁' d₂' : c'.supp → Bool} (h₁ : IsDominantFor M c.supp c'.supp d₁ d₁')
    (h₂ : IsDominantFor M c.supp c'.supp d₂ d₂') : d₁ = d₂ ∧ d₁' = d₂' := by
  sorry

/-- **Theorem 2** (`g:thm2`). "Every row in `D[C, C']` has the same sequence in `M(C')`. In particular, in each row of
`D[C, C']`, every site `i' ∈ C'` has the dominant character with respect to `(C, C')`. Similarly, every row in `D[C', C]`
has the same sequence in `M(C)`" (line 227). Here `C`, `C'` are distinct connected components of `G(M)`. -/
theorem theorem2 (M : Finset (ι → Bool)) {c c' : (incompatGraph M).ConnectedComponent} (hc : c ≠ c') :
    (∃ d d', IsDominantFor M c.supp c'.supp d d') ∧
      ∀ d d', IsDominantFor M c.supp c'.supp d d' →
        (∀ r ∈ dominatedRows M c.supp d, c'.supp.domRestrict r = d') ∧
          ∀ r ∈ dominatedRows M c'.supp d', c.supp.domRestrict r = d := by
  refine ⟨exists_isDominantFor M hc, fun d d' h => ⟨fun r hr => ?_, fun r hr => ?_⟩⟩
  · obtain ⟨hrM, i, hi⟩ := Finset.mem_filter.1 hr
    funext i'
    exact (h i i' r hrM).resolve_left hi
  · obtain ⟨hrM, i', hi'⟩ := Finset.mem_filter.1 hr
    funext i
    exact (h i i' r hrM).resolve_right hi'

/-- **Line 229** (`g:dom_mem`). "We can define the dominant sequence in `M(C)` with respect to `(C, C')` as the sequence in
`M(C)` where each site has the dominant character": it is indeed a sequence of `M(C)`. -/
theorem dominant_mem_restrictRows {M : Finset (ι → Bool)} (hC : NoConstantColumn M)
    {c c' : (incompatGraph M).ConnectedComponent} (hc : c ≠ c') {d : c.supp → Bool} {d' : c'.supp → Bool}
    (h : IsDominantFor M c.supp c'.supp d d') : d ∈ restrictRows c.supp M := by
  sorry

/-- **Corollary 1** (`g:cor1`). "There is no row in `M` which (w.r.t. `(C, C')`) contains both a non-dominant sequence in
`M(C)` and a non-dominant sequence in `M(C')`" (line 233). -/
theorem corollary1 (M : Finset (ι → Bool)) {c c' : (incompatGraph M).ConnectedComponent} (hc : c ≠ c')
    {d : c.supp → Bool} {d' : c'.supp → Bool} (h : IsDominantFor M c.supp c'.supp d d') {r : ι → Bool} (hr : r ∈ M) :
    c.supp.domRestrict r = d ∨ c'.supp.domRestrict r = d' := by
  by_cases hd : c.supp.domRestrict r = d
  · exact Or.inl hd
  · right
    have : ∃ i : c.supp, r i ≠ d i := by
      by_contra hne
      push Not at hne
      exact hd (funext hne)
    exact ((theorem2 M hc).2 d d' h).1 r (Finset.mem_filter.2 ⟨hr, this⟩)

/-- **Line 237** (`g:three_pairs`). "There must be exactly three distinct pairs of binary characters in columns `i`, `i'`",
for sites in two distinct non-trivial components. -/
theorem ncard_pairs_eq_three (M : Finset (ι → Bool)) {c c' : (incompatGraph M).ConnectedComponent} (hc : c ≠ c')
    (hnt : c.supp.Nontrivial) (hnt' : c'.supp.Nontrivial) {i i' : ι} (hi : i ∈ c.supp) (hi' : i' ∈ c'.supp) :
    ((fun r : ι → Bool => (r i, r i')) '' (M : Set (ι → Bool))).ncard = 3 := by
  sorry

/-- **Lemma 2** (`g:lem2`). "Suppose `C` and `C'` are non-trivial components of `G(M)`. If we add new sequences to `M` which
do not create any incompatibilities between sites in different components of `G(M)`, then with respect to `(C, C')`, the
dominant sequences of `C` and `C'` remain unchanged" (line 241). -/
theorem lemma2 {M M' : Finset (ι → Bool)} (hM : M ⊆ M')
    (hnew : ∀ i j, Incompatible M' i j → (incompatGraph M).Reachable i j)
    {c c' : (incompatGraph M).ConnectedComponent} (hc : c ≠ c') (hnt : c.supp.Nontrivial) (hnt' : c'.supp.Nontrivial)
    {d : c.supp → Bool} {d' : c'.supp → Bool} (h : IsDominantFor M c.supp c'.supp d d') :
    IsDominantFor M' c.supp c'.supp d d' := by
  sorry

end Gusfield2007
