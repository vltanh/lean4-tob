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

The printed proof has two misprints at line 210: "`Y ∩ W̄ = ∅`, and `i` and `k'` can't be incompatible" should read `i'` and `k'`:
`i` and `k'` are in different components, and it's the incompatibility of `i'` and `k'` that's contradicted. And "`W̄ ⊃ Y`, and
`W ∩ Y̅ = ∅`" should read `W ∩ Y = ∅`. -/
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

/-- A site of a non-trivial component is incompatible with some site. -/
theorem exists_incompatible_of_nontrivial {M : Finset (ι → Bool)} {c : (incompatGraph M).ConnectedComponent}
    (hc : c.supp.Nontrivial) {i : ι} (hi : i ∈ c.supp) : ∃ k, Incompatible M i k := by
  obtain ⟨j, hj, hij⟩ := hc.exists_ne i
  exact exists_adj_of_reachable (SimpleGraph.ConnectedComponent.exact (hi.trans hj.symm)) hij.symm

/-- A column that is incompatible with a column has both states. -/
theorem Incompatible.exists_ne {M : Finset (ι → Bool)} {i k : ι} (h : Incompatible M i k) :
    ∃ r ∈ M, ∃ r' ∈ M, r i ≠ r' i := by
  obtain ⟨r, hr, h₁, -⟩ := h true true
  obtain ⟨r', hr', h₂, -⟩ := h false true
  exact ⟨r, hr, r', hr', by simp [h₁, h₂]⟩

/-- Identical or complementary columns have the same incompatibilities: "for otherwise sites `i` and `i'` would have
exactly the same incompatibilities and so be in the same connected component" (line 200). -/
theorem Incompatible.of_iff {M : Finset (ι → Bool)} {i i' k : ι} {a b : Bool}
    (h : ∀ r ∈ M, r i = a ↔ r i' = b) (hk : Incompatible M i k) : Incompatible M i' k := by
  intro s t
  obtain ⟨r, hr, h₁, h₂⟩ := hk (if s = b then a else !a) t
  refine ⟨r, hr, ?_, h₂⟩
  by_cases hs : s = b
  · rw [hs]
    exact (h r hr).1 (by simpa [hs] using h₁)
  · have hne : r i ≠ a := by
      rw [h₁]
      simp [hs]
    have hb : r i' ≠ b := fun hb => hne ((h r hr).2 hb)
    cases hs' : s <;> cases hb' : b <;> cases hr' : r i' <;> simp_all

/-- **Lines 200, 202.** The dominant pair of two sites is unique when their columns have both states, the sites are in
different components, and one of them is incompatible with some site: the bipartitions are then not identical. -/
theorem IsDominantPair.eq {M : Finset (ι → Bool)} {i i' : ι} (hnr : ¬ (incompatGraph M).Reachable i i')
    (hi : ∃ r ∈ M, ∃ r' ∈ M, r i ≠ r' i) (hi' : ∃ r ∈ M, ∃ r' ∈ M, r i' ≠ r' i')
    (hk : (∃ k, Incompatible M i k) ∨ ∃ k, Incompatible M i' k) {a b a' b' : Bool}
    (h₁ : IsDominantPair M i i' a b) (h₂ : IsDominantPair M i i' a' b') : a = a' ∧ b = b' := by
  by_cases ha : a = a'
  · refine ⟨ha, ?_⟩
    by_contra hb
    subst ha
    obtain ⟨r, hr, r', hr', hne⟩ := hi
    have key : ∀ s ∈ M, s i = a := by
      intro s hs
      rcases h₁ s hs with h | h
      · exact h
      · rcases h₂ s hs with h' | h'
        · exact h'
        · exact absurd (h.symm.trans h') hb
    exact hne ((key r hr).trans (key r' hr').symm)
  · exfalso
    by_cases hb : b = b'
    · subst hb
      obtain ⟨r, hr, r', hr', hne⟩ := hi'
      have key : ∀ s ∈ M, s i' = b := by
        intro s hs
        rcases h₁ s hs with h | h
        · rcases h₂ s hs with h' | h'
          · exact absurd (h.symm.trans h') ha
          · exact h'
        · exact h
      exact hne ((key r hr).trans (key r' hr').symm)
    · have hiff : ∀ r ∈ M, r i = a ↔ r i' = b' := by
        intro r hr
        constructor
        · intro h
          rcases h₂ r hr with h' | h'
          · exact absurd (h.symm.trans h') ha
          · exact h'
        · intro h
          rcases h₁ r hr with h' | h'
          · exact h'
          · exact absurd (h'.symm.trans h) hb
      have hiff' : ∀ r ∈ M, r i' = b' ↔ r i = a := fun r hr => (hiff r hr).symm
      rcases hk with ⟨k, hk⟩ | ⟨k, hk⟩
      · have : Incompatible M i' k := Incompatible.of_iff hiff hk
        have h₃ : (incompatGraph M).Adj i k := hk
        have h₄ : (incompatGraph M).Adj i' k := this
        exact hnr (h₃.reachable.trans h₄.reachable.symm)
      · have : Incompatible M i k := Incompatible.of_iff hiff' hk
        have h₃ : (incompatGraph M).Adj i k := this
        have h₄ : (incompatGraph M).Adj i' k := hk
        exact hnr (h₃.reachable.trans h₄.reachable.symm)

/-- `IsDominantPair` read from the other site. -/
theorem IsDominantPair.symm {M : Finset (ι → Bool)} {i i' : ι} {a b : Bool} (h : IsDominantPair M i i' a b) :
    IsDominantPair M i' i b a := fun r hr => (h r hr).symm

/-- Sites of two distinct components aren't reachable from each other. -/
theorem not_reachable_of_ne {M : Finset (ι → Bool)} {c c' : (incompatGraph M).ConnectedComponent} (hc : c ≠ c')
    {i i' : ι} (hi : i ∈ c.supp) (hi' : i' ∈ c'.supp) : ¬ (incompatGraph M).Reachable i i' := fun h =>
  hc (by rw [← (SimpleGraph.ConnectedComponent.mem_supp_iff _ _).1 hi,
    ← (SimpleGraph.ConnectedComponent.mem_supp_iff _ _).1 hi']; exact SimpleGraph.ConnectedComponent.sound h)

/-- **Line 212** (`g:dom_exists`). "With respect to the `(C, C')` pair of connected components, each site in `C ∪ C'` has a well-defined
dominant class". As in the paper, by Lemma 1, in both directions, and the uniqueness of the dominant pair where a component is
non-trivial; a choice is needed only when a component is trivial (line 202), and is made at one fixed pair of sites. -/
theorem exists_isDominantFor (M : Finset (ι → Bool)) {c c' : (incompatGraph M).ConnectedComponent} (hc : c ≠ c') :
    ∃ d d', IsDominantFor M c.supp c'.supp d d' := by
  obtain ⟨i₀, hi₀⟩ := c.nonempty_supp
  obtain ⟨j₀, hj₀⟩ := c'.nonempty_supp
  have hnr : ∀ {i i'}, i ∈ c.supp → i' ∈ c'.supp → ¬ (incompatGraph M).Reachable i i' :=
    fun hi hi' => not_reachable_of_ne hc hi hi'
  have hreach : ∀ {c'' : (incompatGraph M).ConnectedComponent} {i i'}, i ∈ c''.supp → i' ∈ c''.supp →
      (incompatGraph M).Reachable i i' := fun hi hi' =>
    SimpleGraph.ConnectedComponent.exact (hi.trans hi'.symm)
  obtain ⟨a₀, b₀, h₀⟩ := exists_isDominantPair M (fun h => hnr hi₀ hj₀ (SimpleGraph.Adj.reachable (G := incompatGraph M) h))
  -- Lemma 1, moving the site of `C'` with the site `i₀` fixed
  have h₁ : ∀ j : c'.supp, ∃ b, (j.1 = j₀ → b = b₀) ∧ IsDominantPair M i₀ j a₀ b := by
    intro j
    by_cases hj : j.1 = j₀
    · exact ⟨b₀, fun _ => rfl, hj ▸ h₀⟩
    · obtain ⟨b, hb⟩ := lemma1 M (hnr hi₀ hj₀) (hreach hj₀ j.2) h₀
      exact ⟨b, fun h => absurd h hj, hb⟩
  -- Lemma 1, moving the site of `C` with the site `j₀` fixed
  have h₂ : ∀ i : c.supp, ∃ a, (i.1 = i₀ → a = a₀) ∧ IsDominantPair M i j₀ a b₀ := by
    intro i
    by_cases hi : i.1 = i₀
    · exact ⟨a₀, fun _ => rfl, hi ▸ h₀⟩
    · obtain ⟨a, ha⟩ := lemma1 M (fun h => hnr hi₀ hj₀ h.symm) (hreach hi₀ i.2) h₀.symm
      exact ⟨a, fun h => absurd h hi, ha.symm⟩
  choose d' hd'₀ hd' using h₁
  choose d hd₀ hd using h₂
  refine ⟨d, d', fun i j => ?_⟩
  by_cases hi : i.1 = i₀
  · rw [hd₀ i hi, hi]
    exact hd' j
  by_cases hj : j.1 = j₀
  · rw [hd'₀ j hj, hj]
    exact hd i
  -- both components have two sites, so the dominant pair of `i`, `j` is unique
  have hnc : (c.supp).Nontrivial := ⟨i, i.2, i₀, hi₀, hi⟩
  have hnc' : (c'.supp).Nontrivial := ⟨j, j.2, j₀, hj₀, hj⟩
  obtain ⟨k, hk⟩ := exists_incompatible_of_nontrivial hnc i.2
  obtain ⟨k', hk'⟩ := exists_incompatible_of_nontrivial hnc' j.2
  -- Lemma 1, from `i, j₀` to `i, j`, gives the state of `i`; from `i₀, j` to `i, j` gives the state of `j`
  obtain ⟨b, hb⟩ := lemma1 M (hnr i.2 hj₀) (hreach hj₀ j.2) (hd i)
  obtain ⟨a, ha⟩ := lemma1 M (fun h => hnr hi₀ j.2 h.symm) (hreach hi₀ i.2) (hd' j).symm
  obtain ⟨-, h₄⟩ := IsDominantPair.eq (hnr i.2 j.2) hk.exists_ne hk'.exists_ne (Or.inl ⟨k, hk⟩) hb ha.symm
  rw [← h₄]
  exact hb

/-- **Lines 200, 212** (`g:dom_unique`). The dominant characters are unique, under the standing assumption, unless both components are
trivial (where line 202 allows a choice for identical sites). The dominance is given here for all pairs of sites, so what's needed
is that of line 200 for one pair (`IsDominantPair.eq`): Lemma 1 is what gives the dominance for all pairs, in `exists_isDominantFor`. -/
theorem isDominantFor_unique {M : Finset (ι → Bool)} (hC : NoConstantColumn M)
    {c c' : (incompatGraph M).ConnectedComponent} (hc : c ≠ c') (hnt : c.supp.Nontrivial ∨ c'.supp.Nontrivial)
    {d₁ d₂ : c.supp → Bool} {d₁' d₂' : c'.supp → Bool} (h₁ : IsDominantFor M c.supp c'.supp d₁ d₁')
    (h₂ : IsDominantFor M c.supp c'.supp d₂ d₂') : d₁ = d₂ ∧ d₁' = d₂' := by
  have key : ∀ (i : c.supp) (j : c'.supp), d₁ i = d₂ i ∧ d₁' j = d₂' j := fun i j => by
    refine IsDominantPair.eq (not_reachable_of_ne hc i.2 j.2) (hC i) (hC j) ?_ (h₁ i j) (h₂ i j)
    rcases hnt with hnt | hnt
    · exact Or.inl (exists_incompatible_of_nontrivial hnt i.2)
    · exact Or.inr (exists_incompatible_of_nontrivial hnt j.2)
  obtain ⟨i₀, hi₀⟩ := c.nonempty_supp
  obtain ⟨j₀, hj₀⟩ := c'.nonempty_supp
  exact ⟨funext fun i => (key i ⟨j₀, hj₀⟩).1, funext fun j => (key ⟨i₀, hi₀⟩ j).2⟩

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
  obtain ⟨j₀, hj₀⟩ := c'.nonempty_supp
  -- a row with the dominated character at `j₀`, which exists since the column isn't constant
  have hex : ∃ r ∈ M, r j₀ ≠ d' ⟨j₀, hj₀⟩ := by
    obtain ⟨r, hr, r', hr', hne⟩ := hC j₀
    by_cases hd : r j₀ = d' ⟨j₀, hj₀⟩
    · exact ⟨r', hr', fun hd' => hne (hd.trans hd'.symm)⟩
    · exact ⟨r, hr, hd⟩
  obtain ⟨r, hr, hne⟩ := hex
  have hmem : r ∈ dominatedRows M c'.supp d' := Finset.mem_filter.2 ⟨hr, ⟨j₀, hj₀⟩, hne⟩
  exact mem_restrictRows.2 ⟨r, hr, ((theorem2 M hc).2 d d' h).2 r hmem⟩

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
  have hnr := not_reachable_of_ne hc hi hi'
  obtain ⟨k, hk⟩ := exists_incompatible_of_nontrivial hnt hi
  obtain ⟨k', hk'⟩ := exists_incompatible_of_nontrivial hnt' hi'
  -- not incompatible: a pair is missing
  have hni : ¬ Incompatible M i i' := fun h => hnr (SimpleGraph.Adj.reachable (G := incompatGraph M) h)
  have hmissing : ∃ a b, ∀ r ∈ M, ¬ (r i = a ∧ r i' = b) := by
    unfold Incompatible at hni
    push Not at hni
    obtain ⟨a, b, h⟩ := hni
    exact ⟨a, b, fun r hr ⟨h₁, h₂⟩ => h r hr h₁ h₂⟩
  obtain ⟨a, b, hab⟩ := hmissing
  have hdom : ∀ {a b : Bool}, (∀ r ∈ M, ¬ (r i = a ∧ r i' = b)) → IsDominantPair M i i' (!a) (!b) := by
    intro a b h r hr
    by_cases h₁ : r i = a
    · right
      have h₂ : r i' ≠ b := fun h₂ => h r hr ⟨h₁, h₂⟩
      cases hb : r i' <;> cases b <;> simp_all
    · left
      cases ha : r i <;> cases a <;> simp_all
  -- the set of pairs is the complement of the missing pair: a second missing pair contradicts uniqueness
  have hset : (fun r : ι → Bool => (r i, r i')) '' (M : Set (ι → Bool)) = {(a, b)}ᶜ := by
    ext ⟨s, t⟩
    constructor
    · rintro ⟨r, hr, hrr⟩
      simp only [Prod.mk.injEq] at hrr
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff, Prod.mk.injEq]
      rintro ⟨rfl, rfl⟩
      exact hab r hr hrr
    · intro hst
      by_contra hno
      have hmiss : ∀ r ∈ M, ¬ (r i = s ∧ r i' = t) := fun r hr h =>
        hno ⟨r, hr, by simp [h.1, h.2]⟩
      obtain ⟨h₁, h₂⟩ := IsDominantPair.eq hnr hk.exists_ne hk'.exists_ne (Or.inl ⟨k, hk⟩) (hdom hab) (hdom hmiss)
      apply hst
      simp only [Set.mem_singleton_iff, Prod.mk.injEq]
      exact ⟨by simpa using h₁.symm, by simpa using h₂.symm⟩
  rw [hset, Set.ncard_compl, Set.ncard_singleton]
  simp

/-- `IsDominantPair` in terms of the pairs of a column. -/
theorem isDominantPair_of_pairs {M M' : Finset (ι → Bool)} {i i' : ι} {a b : Bool}
    (h : (fun r : ι → Bool => (r i, r i')) '' (M' : Set (ι → Bool)) ⊆ (fun r : ι → Bool => (r i, r i')) '' (M : Set (ι → Bool)))
    (hd : IsDominantPair M i i' a b) : IsDominantPair M' i i' a b := by
  intro r hr
  obtain ⟨s, hs, hsr⟩ := h ⟨r, hr, rfl⟩
  simp only [Prod.mk.injEq] at hsr
  rw [← hsr.1, ← hsr.2]
  exact hd s hs

/-- **Lemma 2** (`g:lem2`). "Suppose `C` and `C'` are non-trivial components of `G(M)`. If we add new sequences to `M` which
do not create any incompatibilities between sites in different components of `G(M)`, then with respect to `(C, C')`, the
dominant sequences of `C` and `C'` remain unchanged" (line 241). -/
theorem lemma2 {M M' : Finset (ι → Bool)} (hM : M ⊆ M')
    (hnew : ∀ i j, Incompatible M' i j → (incompatGraph M).Reachable i j)
    {c c' : (incompatGraph M).ConnectedComponent} (hc : c ≠ c') (hnt : c.supp.Nontrivial) (hnt' : c'.supp.Nontrivial)
    {d : c.supp → Bool} {d' : c'.supp → Bool} (h : IsDominantFor M c.supp c'.supp d d') :
    IsDominantFor M' c.supp c'.supp d d' := by
  intro i i'
  have hnr := not_reachable_of_ne hc i.2 i'.2
  -- the pairs of `M` are three, by line 237; `M'` has them and misses one, since `i`, `i'` aren't incompatible in it
  have hthree := ncard_pairs_eq_three M hc hnt hnt' i.2 i'.2
  have hsub : (fun r : ι → Bool => (r i, r i')) '' (M : Set (ι → Bool)) ⊆
      (fun r : ι → Bool => (r i, r i')) '' (M' : Set (ι → Bool)) :=
    Set.image_mono (by exact_mod_cast hM)
  have hni : ¬ Incompatible M' i i' := fun hi => hnr (hnew _ _ hi)
  have hle : ((fun r : ι → Bool => (r i, r i')) '' (M' : Set (ι → Bool))).ncard ≤ 3 := by
    unfold Incompatible at hni
    push Not at hni
    obtain ⟨a, b, hab⟩ := hni
    have hs : (fun r : ι → Bool => (r i, r i')) '' (M' : Set (ι → Bool)) ⊆ {(a, b)}ᶜ := by
      rintro _ ⟨r, hr, rfl⟩
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff, Prod.mk.injEq]
      exact fun ⟨h₁, h₂⟩ => hab r hr h₁ h₂
    calc _ ≤ ({(a, b)}ᶜ : Set (Bool × Bool)).ncard := Set.ncard_le_ncard hs (Set.toFinite _)
      _ = 3 := by rw [Set.ncard_compl, Set.ncard_singleton]; simp
  have heq : (fun r : ι → Bool => (r i, r i')) '' (M : Set (ι → Bool)) =
      (fun r : ι → Bool => (r i, r i')) '' (M' : Set (ι → Bool)) :=
    Set.eq_of_subset_of_ncard_le hsub (hle.trans hthree.ge) (Set.toFinite _)
  exact isDominantPair_of_pairs heq.ge (h i i')

end Gusfield2007
