module

public import External.LegriedEtAl2021.Theorem1
public import Phylogenetics.Network.OfHierarchy
public import Phylogenetics.Network.Quartets
public import Phylogenetics.Tree.Splits

/-!
# From addresses and species trees to `QuartetTree` and `RootedNetwork`

The model of `External.LegriedEtAl2021.Model` reads topologies from addresses, by `Pat`, and species quartets from clusters, by
`SpeciesTree.IsQuartet`. This file connects both to the library.

**The topology of leaves.**

* `pat_trichotomy`: on four leaves, none above another, one of the three topologies holds. With `not_pat_of_pat`, exactly one.
* `not_prefix_of_geneLaw`: in a gene tree, a leaf in one species is not above a leaf in another.
* `sum_probTopology`: so the three probabilities of topologies sum to one.
* `pickTree`, `displays_pickTree_iff`: one copy in each species gives an unrooted tree on the species, in the sense of the library, which
  displays a quartet tree exactly when `Pat` holds.

**The species tree.**

* `clustersF`, `isHierarchy_clustersF`: its clusters are a hierarchy, and `speciesNetwork` is the library's network of this hierarchy, a tree.
* `treeOfBlobs_speciesNetwork`, `displays_treeOfBlobs_iff`: its tree of blobs displays a quartet tree exactly when `SpeciesTree.IsQuartet`
  holds. So the species tree's quartets are the cut edges in (3.1).

**The probabilities on quartet trees.**

* `quartetP`: the probability of a quartet tree, for a uniform pick of one copy per species. `quartetP_quartetTree` gives it on `ab|cd`,
  whichever way the quartet tree is written; `sum_treesOn_quartetP` says that it sums to one on four taxa.
* `quartetP_lt`: (3.1), in the form of the hypothesis of ECToBlob's Theorem 3.1.
-/

@[expose] public noncomputable section

open scoped ENNReal Classical
open Phylogenetics Finset

namespace External.LegriedEtAl2021

/-! ### The topologies of four leaves are exhaustive -/

/-- Neither address is above the other. -/
def NP (a b : Path) : Prop := ¬ a <+: b ∧ ¬ b <+: a

theorem NP.symm {a b : Path} (h : NP a b) : NP b a := ⟨h.2, h.1⟩

theorem cons_prefix_cons_self {x : Bool} {r l : Path} (h : r <+: l) : (x :: r) <+: (x :: l) :=
  List.cons_prefix_cons.2 ⟨rfl, h⟩

theorem not_cons_prefix_self {x : Bool} {r l : Path} (h : ¬ r <+: l) : ¬ (x :: r) <+: (x :: l) :=
  fun h' => h (List.cons_prefix_cons.1 h').2

theorem not_cons_prefix_of_ne {x y : Bool} (h : x ≠ y) (r l : Path) : ¬ (x :: r) <+: (y :: l) :=
  fun h' => h (List.cons_prefix_cons.1 h').1

theorem NP.tail {x : Bool} {a b : Path} (h : NP (x :: a) (x :: b)) : NP a b :=
  ⟨fun h' => h.1 (cons_prefix_cons_self h'), fun h' => h.2 (cons_prefix_cons_self h')⟩

theorem singleton_prefix_cons (x : Bool) (l : Path) : [x] <+: (x :: l) := cons_prefix_cons_self List.nil_prefix

theorem bool_eq_of_ne {x y z : Bool} (hy : y ≠ x) (hz : z ≠ x) : y = z := by
  cases x <;> cases y <;> cases z <;> simp_all

/-- Among three leaves, none above another, a vertex is above two of them and not the third. -/
theorem trip_path {a b c : Path} (hab : NP a b) (hac : NP a c) (hbc : NP b c) :
    (∃ r, r <+: a ∧ r <+: b ∧ ¬ r <+: c) ∨ (∃ r, r <+: a ∧ r <+: c ∧ ¬ r <+: b) ∨ (∃ r, r <+: b ∧ r <+: c ∧ ¬ r <+: a) := by
  induction a generalizing b c with
  | nil => exact absurd List.nil_prefix hab.1
  | cons x a ih =>
    cases b with
    | nil => exact absurd List.nil_prefix hab.2
    | cons y b =>
      cases c with
      | nil => exact absurd List.nil_prefix hac.2
      | cons z c =>
        by_cases hy : y = x <;> by_cases hz : z = x
        · subst y z
          rcases ih hab.tail hac.tail hbc.tail with ⟨r, h₁, h₂, h₃⟩ | ⟨r, h₁, h₂, h₃⟩ | ⟨r, h₁, h₂, h₃⟩
          · exact Or.inl ⟨x :: r, cons_prefix_cons_self h₁, cons_prefix_cons_self h₂, not_cons_prefix_self h₃⟩
          · exact Or.inr (Or.inl ⟨x :: r, cons_prefix_cons_self h₁, cons_prefix_cons_self h₂, not_cons_prefix_self h₃⟩)
          · exact Or.inr (Or.inr ⟨x :: r, cons_prefix_cons_self h₁, cons_prefix_cons_self h₂, not_cons_prefix_self h₃⟩)
        · subst y
          exact Or.inl ⟨[x], singleton_prefix_cons _ _, singleton_prefix_cons _ _, not_cons_prefix_of_ne (Ne.symm hz) _ _⟩
        · subst z
          exact Or.inr (Or.inl ⟨[x], singleton_prefix_cons _ _, singleton_prefix_cons _ _, not_cons_prefix_of_ne (Ne.symm hy) _ _⟩)
        · have hyz := bool_eq_of_ne hy hz
          subst z
          exact Or.inr (Or.inr ⟨[y], singleton_prefix_cons _ _, singleton_prefix_cons _ _, not_cons_prefix_of_ne hy _ _⟩)

/-- **On four leaves, none above another, one of the three topologies holds.** -/
theorem pat_trichotomy {a b c d : Path} (hab : NP a b) (hac : NP a c) (had : NP a d) (hbc : NP b c) (hbd : NP b d) (hcd : NP c d) :
    Pat a b c d ∨ Pat a c b d ∨ Pat a d b c := by
  induction a generalizing b c d with
  | nil => exact absurd List.nil_prefix hab.1
  | cons x a ih =>
    cases b with
    | nil => exact absurd List.nil_prefix hab.2
    | cons y b =>
      cases c with
      | nil => exact absurd List.nil_prefix hac.2
      | cons z c =>
        cases d with
        | nil => exact absurd List.nil_prefix had.2
        | cons w d =>
          have P : ∀ {r l : Path}, r <+: l → (x :: r) <+: (x :: l) := fun h => cons_prefix_cons_self h
          have Q : ∀ {r l : Path}, ¬ r <+: l → ¬ (x :: r) <+: (x :: l) := fun h => not_cons_prefix_self h
          by_cases hy : y = x <;> by_cases hz : z = x <;> by_cases hw : w = x
          · subst y z w
            rcases ih hab.tail hac.tail had.tail hbc.tail hbd.tail hcd.tail with ⟨r, h | h⟩ | ⟨r, h | h⟩ | ⟨r, h | h⟩
            · exact Or.inl ⟨x :: r, Or.inl ⟨P h.1, P h.2.1, Q h.2.2.1, Q h.2.2.2⟩⟩
            · exact Or.inl ⟨x :: r, Or.inr ⟨P h.1, P h.2.1, Q h.2.2.1, Q h.2.2.2⟩⟩
            · exact Or.inr (Or.inl ⟨x :: r, Or.inl ⟨P h.1, P h.2.1, Q h.2.2.1, Q h.2.2.2⟩⟩)
            · exact Or.inr (Or.inl ⟨x :: r, Or.inr ⟨P h.1, P h.2.1, Q h.2.2.1, Q h.2.2.2⟩⟩)
            · exact Or.inr (Or.inr ⟨x :: r, Or.inl ⟨P h.1, P h.2.1, Q h.2.2.1, Q h.2.2.2⟩⟩)
            · exact Or.inr (Or.inr ⟨x :: r, Or.inr ⟨P h.1, P h.2.1, Q h.2.2.1, Q h.2.2.2⟩⟩)
          · -- alone: `d`
            subst y z
            have N := not_cons_prefix_of_ne (x := x) (y := w) (Ne.symm hw)
            rcases trip_path hab.tail hac.tail hbc.tail with ⟨r, h₁, h₂, h₃⟩ | ⟨r, h₁, h₂, h₃⟩ | ⟨r, h₁, h₂, h₃⟩
            · exact Or.inl ⟨x :: r, Or.inl ⟨P h₁, P h₂, Q h₃, N _ _⟩⟩
            · exact Or.inr (Or.inl ⟨x :: r, Or.inl ⟨P h₁, P h₂, Q h₃, N _ _⟩⟩)
            · exact Or.inr (Or.inr ⟨x :: r, Or.inr ⟨P h₁, P h₂, Q h₃, N _ _⟩⟩)
          · -- alone: `c`
            subst y w
            have N := not_cons_prefix_of_ne (x := x) (y := z) (Ne.symm hz)
            rcases trip_path hab.tail had.tail hbd.tail with ⟨r, h₁, h₂, h₃⟩ | ⟨r, h₁, h₂, h₃⟩ | ⟨r, h₁, h₂, h₃⟩
            · exact Or.inl ⟨x :: r, Or.inl ⟨P h₁, P h₂, N _ _, Q h₃⟩⟩
            · exact Or.inr (Or.inr ⟨x :: r, Or.inl ⟨P h₁, P h₂, Q h₃, N _ _⟩⟩)
            · exact Or.inr (Or.inl ⟨x :: r, Or.inr ⟨P h₁, P h₂, Q h₃, N _ _⟩⟩)
          · -- `ab|cd`
            subst y
            have hzw := bool_eq_of_ne hz hw
            subst w
            exact Or.inl ⟨[x], Or.inl ⟨singleton_prefix_cons _ _, singleton_prefix_cons _ _, not_cons_prefix_of_ne (Ne.symm hz) _ _,
              not_cons_prefix_of_ne (Ne.symm hz) _ _⟩⟩
          · -- alone: `b`
            subst z w
            have N := not_cons_prefix_of_ne (x := x) (y := y) (Ne.symm hy)
            rcases trip_path hac.tail had.tail hcd.tail with ⟨r, h₁, h₂, h₃⟩ | ⟨r, h₁, h₂, h₃⟩ | ⟨r, h₁, h₂, h₃⟩
            · exact Or.inr (Or.inl ⟨x :: r, Or.inl ⟨P h₁, P h₂, N _ _, Q h₃⟩⟩)
            · exact Or.inr (Or.inr ⟨x :: r, Or.inl ⟨P h₁, P h₂, N _ _, Q h₃⟩⟩)
            · exact Or.inl ⟨x :: r, Or.inr ⟨P h₁, P h₂, Q h₃, N _ _⟩⟩
          · -- `ac|bd`
            subst z
            have hyw := bool_eq_of_ne hy hw
            subst w
            exact Or.inr (Or.inl ⟨[x], Or.inl ⟨singleton_prefix_cons _ _, singleton_prefix_cons _ _, not_cons_prefix_of_ne (Ne.symm hy) _ _,
              not_cons_prefix_of_ne (Ne.symm hy) _ _⟩⟩)
          · -- `ad|bc`
            subst w
            have hyz := bool_eq_of_ne hy hz
            subst z
            exact Or.inr (Or.inr ⟨[x], Or.inl ⟨singleton_prefix_cons _ _, singleton_prefix_cons _ _, not_cons_prefix_of_ne (Ne.symm hy) _ _,
              not_cons_prefix_of_ne (Ne.symm hy) _ _⟩⟩)
          · -- alone: `a`
            have hyz := bool_eq_of_ne hy hz
            have hyw := bool_eq_of_ne hy hw
            subst z w
            have N := not_cons_prefix_of_ne (x := y) (y := x) hy
            have P' : ∀ {r l : Path}, r <+: l → (y :: r) <+: (y :: l) := fun h => cons_prefix_cons_self h
            have Q' : ∀ {r l : Path}, ¬ r <+: l → ¬ (y :: r) <+: (y :: l) := fun h => not_cons_prefix_self h
            rcases trip_path hbc.tail hbd.tail hcd.tail with ⟨r, h₁, h₂, h₃⟩ | ⟨r, h₁, h₂, h₃⟩ | ⟨r, h₁, h₂, h₃⟩
            · exact Or.inr (Or.inr ⟨y :: r, Or.inr ⟨P' h₁, P' h₂, N _ _, Q' h₃⟩⟩)
            · exact Or.inr (Or.inl ⟨y :: r, Or.inr ⟨P' h₁, P' h₂, N _ _, Q' h₃⟩⟩)
            · exact Or.inl ⟨y :: r, Or.inr ⟨P' h₁, P' h₂, N _ _, Q' h₃⟩⟩

/-- On four leaves, none above another, exactly one of the three topologies holds. -/
theorem ind_pat_sum {a b c d : Path} (hab : NP a b) (hac : NP a c) (had : NP a d) (hbc : NP b c) (hbd : NP b d) (hcd : NP c d) :
    ind (Pat a b c d) + ind (Pat a c b d) + ind (Pat a d b c) = ind True := by
  rw [ind_true trivial]
  rcases pat_trichotomy hab hac had hbc hbd hcd with h | h | h
  · rw [ind_true h, ind_false (not_pat_of_pat h), ind_false fun h' => not_pat_of_pat_ad h' h]
    simp
  · rw [ind_true h, ind_false fun h' => not_pat_of_pat h' h, ind_false fun h' => not_pat_of_pat_ad' h' h]
    simp
  · rw [ind_true h, ind_false (not_pat_of_pat_ad h), ind_false (not_pat_of_pat_ad' h)]
    simp

/-! ### The leaves of a gene tree -/

variable {X : Type}

theorem mem_forestLeaves_iff {J : Type} [Fintype J] {ρ : J → Path} {g : J → Leaves X} {y : X} {d : Path} :
    d ∈ forestLeaves ρ g y ↔ ∃ j, ∃ q ∈ g j y, d = ρ j ++ q := by
  simp only [forestLeaves, Multiset.mem_sum, Multiset.mem_map, Finset.mem_univ, true_and]
  exact exists_congr fun j => exists_congr fun q => and_congr_right fun _ => eq_comm

/-- **In a gene tree, a leaf in one species is not above a leaf in another.** -/
theorem not_prefix_of_geneLaw (T : SpeciesTree X) {L : Leaves X} (hL : geneLaw T L ≠ 0) {A B : X} (hAB : A ≠ B) {a b : Path}
    (ha : a ∈ L A) (hb : b ∈ L B) : ¬ a <+: b := by
  induction T generalizing L a b with
  | leaf K x =>
    obtain ⟨s, -, hs⟩ := (PMF.mem_support_bind_iff _ _ _).1 ((PMF.mem_support_iff _ _).2 hL)
    have hLs := (PMF.mem_support_pure_iff _ _).1 hs
    subst hLs
    by_cases hA : A = x
    · have hB : B ≠ x := fun h => hAB (hA.trans h.symm)
      simp [hB] at hb
    · simp [hA] at ha
  | node K l r ihl ihr =>
    obtain ⟨s, -, hs⟩ := (PMF.mem_support_bind_iff _ _ _).1 ((PMF.mem_support_iff _ _).2 hL)
    obtain ⟨gl, hgl, hs⟩ := (PMF.mem_support_bind_iff _ _ _).1 hs
    obtain ⟨gr, hgr, hs⟩ := (PMF.mem_support_bind_iff _ _ _).1 hs
    have hLs := (PMF.mem_support_pure_iff _ _).1 hs
    subst hLs
    have hgl' := (PMF.mem_support_iff _ _).1 hgl
    have hgr' := (PMF.mem_support_iff _ _).1 hgr
    -- the shape of a leaf: `w ++ [e] ++ q`
    have hform : ∀ {y : X} {d : Path}, d ∈ glue s gl gr y → ∃ w : s.copies, ∃ e : Bool, ∃ q,
        d = (w.1 ++ [e]) ++ q ∧ ((e = false ∧ q ∈ gl w y) ∨ (e = true ∧ q ∈ gr w y)) := by
      intro y d hd
      rcases Multiset.mem_add.1 hd with h | h
      · obtain ⟨w, q, hq, rfl⟩ := mem_forestLeaves_iff.1 h
        exact ⟨w, false, q, rfl, Or.inl ⟨rfl, hq⟩⟩
      · obtain ⟨w, q, hq, rfl⟩ := mem_forestLeaves_iff.1 h
        exact ⟨w, true, q, rfl, Or.inr ⟨rfl, hq⟩⟩
    obtain ⟨w, e, q, rfl, hq⟩ := hform ha
    obtain ⟨w', e', q', rfl, hq'⟩ := hform hb
    intro hpre
    have hw : w.1 <+: (w'.1 ++ [e']) ++ q' := (List.prefix_append _ _ |>.trans (List.prefix_append _ _)).trans hpre
    have hw' : w'.1 <+: (w'.1 ++ [e']) ++ q' := List.prefix_append _ _ |>.trans (List.prefix_append _ _)
    have hww : w = w' := by
      rcases List.prefix_or_prefix_of_prefix hw hw' with h | h
      · exact Subtype.ext (s.anti _ w.2 _ w'.2 h)
      · exact (Subtype.ext (s.anti _ w'.2 _ w.2 h)).symm
    subst hww
    have htail : (e :: q) <+: (e' :: q') := by
      have h₂ : w.1 ++ (e :: q) <+: w.1 ++ (e' :: q') := by simpa [List.append_assoc] using hpre
      exact (List.prefix_append_right_inj _).1 h₂
    obtain ⟨hee, hqq⟩ := List.cons_prefix_cons.1 htail
    rcases hq with ⟨he, hq⟩ | ⟨he, hq⟩ <;> rcases hq' with ⟨he', hq'⟩ | ⟨he', hq'⟩
    · exact ihl (piLaw_ne_zero hgl' w) hq hq' hqq
    · rw [he, he'] at hee
      exact absurd hee (by decide)
    · rw [he, he'] at hee
      exact absurd hee (by decide)
    · exact ihr (piLaw_ne_zero hgr' w) hq hq' hqq

theorem NP_of_geneLaw (T : SpeciesTree X) {L : Leaves X} (hL : geneLaw T L ≠ 0) {A B : X} (hAB : A ≠ B) {a b : Path}
    (ha : a ∈ L A) (hb : b ∈ L B) : NP a b :=
  ⟨not_prefix_of_geneLaw T hL hAB ha hb, not_prefix_of_geneLaw T hL hAB.symm hb ha⟩

theorem sumMS_congr_mem {M : Multiset Path} {h h' : Path → ℝ≥0∞} (hh : ∀ a ∈ M, h a = h' a) : sumMS M h = sumMS M h' := by
  unfold sumMS
  rw [Multiset.map_congr rfl hh]

/-- On the leaves of a gene tree, the three statistics sum to the total. -/
theorem score_sum_of_geneLaw (φ : ℕ → ℝ≥0∞) (T : SpeciesTree X) {L : Leaves X} (hL : geneLaw T L ≠ 0) {A B C D : X} (hAB : A ≠ B)
    (hAC : A ≠ C) (hAD : A ≠ D) (hBC : B ≠ C) (hBD : B ≠ D) (hCD : C ≠ D) :
    Sc φ A B C D L + Alt φ A B C D L + Alt₂ φ A B C D L = Tot φ A B C D L := by
  have htopo : topo Pat (L A) (L B) (L C) (L D) + topo (fun a b c d => Pat a c b d) (L A) (L B) (L C) (L D) +
      topo (fun a b c d => Pat a d b c) (L A) (L B) (L C) (L D) = topo (fun _ _ _ _ => True) (L A) (L B) (L C) (L D) := by
    unfold topo
    simp only [← sumMS_add_fun]
    refine sumMS_congr_mem fun a ha => sumMS_congr_mem fun b hb => sumMS_congr_mem fun c hc => sumMS_congr_mem fun d hd => ?_
    exact ind_pat_sum (NP_of_geneLaw T hL hAB ha hb) (NP_of_geneLaw T hL hAC ha hc) (NP_of_geneLaw T hL hAD ha hd)
      (NP_of_geneLaw T hL hBC hb hc) (NP_of_geneLaw T hL hBD hb hd) (NP_of_geneLaw T hL hCD hc hd)
  simp only [Sc, Alt, Alt₂, Tot, score]
  rw [← htopo]
  ring

/-- **The three probabilities of topologies sum to one**, given that all four species have a copy with positive probability. -/
theorem sum_probTopology {T : SpeciesTree X} {A B C D : X} (hAB : A ≠ B) (hAC : A ≠ C) (hAD : A ≠ D) (hBC : B ≠ C) (hBD : B ≠ D)
    (hCD : C ≠ D) (hpos : 0 < expect (geneLaw T) fun L => ind (Present A B C D L)) :
    probTopology T Pat A B C D + probTopology T (fun a b c d => Pat a c b d) A B C D +
      probTopology T (fun a b c d => Pat a d b c) A B C D = 1 := by
  have hfin : (expect (geneLaw T) fun L => ind (Present A B C D L)) ≠ ⊤ :=
    ((expect_ind_le_one _ _).trans_lt ENNReal.one_lt_top).ne
  have hsum : expect (geneLaw T) (Sc pickWeight A B C D) + expect (geneLaw T) (Alt pickWeight A B C D) +
      expect (geneLaw T) (Alt₂ pickWeight A B C D) = expect (geneLaw T) fun L => ind (Present A B C D L) := by
    rw [← expect_add, ← expect_add]
    refine expect_congr fun L hL => ?_
    rw [score_sum_of_geneLaw pickWeight T hL hAB hAC hAD hBC hBD hCD, Tot_pick]
  unfold probTopology
  rw [ENNReal.div_add_div_same, ENNReal.div_add_div_same]
  change (expect (geneLaw T) (Sc pickWeight A B C D) + expect (geneLaw T) (Alt pickWeight A B C D) +
      expect (geneLaw T) (Alt₂ pickWeight A B C D)) / _ = 1
  rw [hsum]
  exact ENNReal.div_self hpos.ne' hfin

/-! ### Displays, on a family of clusters -/

section Displays

variable {Y : Type} [Fintype Y] [DecidableEq Y]

/-- **The unrooted tree of a family of clusters displays `ab|cd`** when a cluster holds two of them and not the other two. -/
theorem displays_unroot_iff {H : Finset (Finset Y)} {a b c d : Y} (h : ({a, b, c, d} : Finset Y).card = 4) :
    Displays (unroot H) (quartetTree a b c d h) ↔
      ∃ F ∈ H, (a ∈ F ∧ b ∈ F ∧ c ∉ F ∧ d ∉ F) ∨ (c ∈ F ∧ d ∈ F ∧ a ∉ F ∧ b ∉ F) := by
  obtain ⟨hab, hac, had, hbc, hbd, hcd⟩ := ne_of_card_four h
  -- the intersection with the four taxa
  have hab' : ∀ A : Finset Y, A ∩ {a, b, c, d} = {a, b} ↔ (a ∈ A ∧ b ∈ A ∧ c ∉ A ∧ d ∉ A) := by
    intro A
    constructor
    · intro hA
      have hm : ∀ x, x ∈ A ∧ x ∈ ({a, b, c, d} : Finset Y) ↔ x ∈ ({a, b} : Finset Y) := fun x => by rw [← mem_inter, hA]
      have h₁ := hm a
      have h₂ := hm b
      have h₃ := hm c
      have h₄ := hm d
      simp only [mem_insert, mem_singleton, true_or, or_true, and_true, hac.symm, hbc.symm, had.symm, hbd.symm, or_self, iff_false,
        iff_true] at h₁ h₂ h₃ h₄
      exact ⟨h₁, h₂, h₃, h₄⟩
    · rintro ⟨h₁, h₂, h₃, h₄⟩
      ext x
      simp only [mem_inter, mem_insert, mem_singleton]
      constructor
      · rintro ⟨hx, rfl | rfl | rfl | rfl⟩
        · exact Or.inl rfl
        · exact Or.inr rfl
        · exact absurd hx h₃
        · exact absurd hx h₄
      · rintro (rfl | rfl)
        · exact ⟨h₁, Or.inl rfl⟩
        · exact ⟨h₂, Or.inr (Or.inl rfl)⟩
  have hcd' : ∀ A : Finset Y, A ∩ {a, b, c, d} = {c, d} ↔ (c ∈ A ∧ d ∈ A ∧ a ∉ A ∧ b ∉ A) := by
    intro A
    constructor
    · intro hA
      have hm : ∀ x, x ∈ A ∧ x ∈ ({a, b, c, d} : Finset Y) ↔ x ∈ ({c, d} : Finset Y) := fun x => by rw [← mem_inter, hA]
      have h₁ := hm a
      have h₂ := hm b
      have h₃ := hm c
      have h₄ := hm d
      simp only [mem_insert, mem_singleton, true_or, or_true, and_true, hac, hbc, had, hbd, or_self, iff_false,
        iff_true] at h₁ h₂ h₃ h₄
      exact ⟨h₃, h₄, h₁, h₂⟩
    · rintro ⟨h₁, h₂, h₃, h₄⟩
      ext x
      simp only [mem_inter, mem_insert, mem_singleton]
      constructor
      · rintro ⟨hx, rfl | rfl | rfl | rfl⟩
        · exact absurd hx h₃
        · exact absurd hx h₄
        · exact Or.inl rfl
        · exact Or.inr rfl
      · rintro (rfl | rfl)
        · exact ⟨h₁, Or.inr (Or.inr (Or.inl rfl))⟩
        · exact ⟨h₂, Or.inr (Or.inr (Or.inr rfl))⟩
  have hne : ∀ {A : Finset Y} {x : Y}, x ∉ A → A ≠ univ := fun hx hA => hx (hA ▸ mem_univ _)
  unfold Displays
  simp only [quartetTree_taxa, quartetTree_val, mem_insert, mem_singleton, hab', hcd']
  constructor
  · rintro ⟨A, hA, hs⟩
    rcases mem_unroot.1 hA with ⟨hF, -⟩ | ⟨hF, -⟩
    · exact ⟨A, hF, hs⟩
    · refine ⟨Aᶜ, hF, ?_⟩
      simp only [mem_compl, not_not]
      rcases hs with ⟨h₁, h₂, h₃, h₄⟩ | ⟨h₁, h₂, h₃, h₄⟩
      · exact Or.inr ⟨h₃, h₄, h₁, h₂⟩
      · exact Or.inl ⟨h₃, h₄, h₁, h₂⟩
  · rintro ⟨F, hF, hs⟩
    refine ⟨F, mem_unroot.2 (Or.inl ⟨hF, ?_⟩), hs⟩
    rcases hs with ⟨-, -, h₃, -⟩ | ⟨-, -, h₃, -⟩
    · exact hne h₃
    · exact hne h₃

/-- The clusters of a pick of one copy in each species: the species below each vertex. -/
def pickClusters (ℓ : Y → Path) : Finset (Finset Y) :=
  insert univ ((univ.biUnion fun x => (ℓ x).inits.toFinset).image fun r => univ.filter fun y => r <+: ℓ y)

theorem mem_pickClusters_of_prefix (ℓ : Y → Path) {r : Path} {x : Y} (h : r <+: ℓ x) :
    (univ.filter fun y => r <+: ℓ y) ∈ pickClusters ℓ := by
  refine mem_insert_of_mem (mem_image.2 ⟨r, mem_biUnion.2 ⟨x, mem_univ _, ?_⟩, rfl⟩)
  exact List.mem_toFinset.2 (List.mem_inits _ _ |>.2 h)

/-- **One copy in each species, none above another, gives a hierarchy on the species.** -/
theorem isHierarchy_pickClusters [Nonempty Y] {ℓ : Y → Path} (hℓ : IsAnti ℓ) : IsHierarchy (pickClusters ℓ) := by
  have hmem : ∀ A ∈ pickClusters ℓ, A = univ ∨ ∃ r x, r <+: ℓ x ∧ A = univ.filter fun y => r <+: ℓ y := by
    intro A hA
    rcases mem_insert.1 hA with rfl | hA
    · exact Or.inl rfl
    · obtain ⟨r, hr, rfl⟩ := mem_image.1 hA
      obtain ⟨x, -, hx⟩ := mem_biUnion.1 hr
      exact Or.inr ⟨r, x, (List.mem_inits _ _).1 (List.mem_toFinset.1 hx), rfl⟩
  refine ⟨mem_insert_self _ _, fun x => ?_, fun A hA => ?_, fun A hA B hB => ?_⟩
  · have hc := mem_pickClusters_of_prefix ℓ (List.prefix_refl (ℓ x))
    have heq : (univ.filter fun y => ℓ x <+: ℓ y) = {x} := by
      ext y
      simp only [mem_filter, mem_univ, true_and, mem_singleton]
      exact ⟨fun h => (hℓ x y h).symm, fun h => h ▸ List.prefix_refl _⟩
    rwa [heq] at hc
  · rcases hmem A hA with rfl | ⟨r, x, hr, rfl⟩
    · exact univ_nonempty
    · exact ⟨x, mem_filter.2 ⟨mem_univ _, hr⟩⟩
  · rcases hmem A hA with rfl | ⟨r, x, -, rfl⟩
    · exact Or.inr (Or.inl (subset_univ _))
    · rcases hmem B hB with rfl | ⟨r', x', -, rfl⟩
      · exact Or.inl (subset_univ _)
      · by_cases hd : Disjoint (univ.filter fun y => r <+: ℓ y) (univ.filter fun y => r' <+: ℓ y)
        · exact Or.inr (Or.inr hd)
        · obtain ⟨z, hz, hz'⟩ := not_disjoint_iff.1 hd
          rcases List.prefix_or_prefix_of_prefix (mem_filter.1 hz).2 (mem_filter.1 hz').2 with h | h
          · refine Or.inr (Or.inl fun y hy => mem_filter.2 ⟨mem_univ _, h.trans (mem_filter.1 hy).2⟩)
          · exact Or.inl fun y hy => mem_filter.2 ⟨mem_univ _, h.trans (mem_filter.1 hy).2⟩

/-- **The unrooted tree of a pick of one copy in each species**, in the sense of the library. -/
def pickTree (ℓ : Y → Path) : Finset (Finset Y) := unroot (pickClusters ℓ)

theorem isUnrootedTree_pickTree [Nonempty Y] {ℓ : Y → Path} (hℓ : IsAnti ℓ) : IsUnrootedTree (pickTree ℓ) :=
  ⟨_, isHierarchy_pickClusters hℓ, rfl⟩

/-- **The bridge for gene trees.** The unrooted tree of a pick of one copy in each species displays `ab|cd` exactly when the copies have
the topology `Pat`. -/
theorem displays_pickTree_iff {ℓ : Y → Path} {a b c d : Y} (h : ({a, b, c, d} : Finset Y).card = 4) :
    Displays (pickTree ℓ) (quartetTree a b c d h) ↔ Pat (ℓ a) (ℓ b) (ℓ c) (ℓ d) := by
  unfold pickTree
  rw [displays_unroot_iff]
  constructor
  · rintro ⟨F, hF, hs⟩
    rcases mem_insert.1 hF with rfl | hF
    · simp at hs
    · obtain ⟨r, -, rfl⟩ := mem_image.1 hF
      simp only [mem_filter, mem_univ, true_and] at hs
      exact ⟨r, hs⟩
  · rintro ⟨r, ⟨h₁, h₂, h₃, h₄⟩ | ⟨h₁, h₂, h₃, h₄⟩⟩
    · exact ⟨_, mem_pickClusters_of_prefix ℓ h₁, Or.inl (by simpa using ⟨h₁, h₂, h₃, h₄⟩)⟩
    · exact ⟨_, mem_pickClusters_of_prefix ℓ h₁, Or.inr (by simpa using ⟨h₁, h₂, h₃, h₄⟩)⟩

/-! ### The species tree as a network -/

/-- The species below a vertex, as a finite set. -/
def taxaF : SpeciesTree Y → Finset Y
  | .leaf _ x => {x}
  | .node _ l r => taxaF l ∪ taxaF r

omit [Fintype Y] in
theorem mem_taxaF {T : SpeciesTree Y} {y : Y} : y ∈ taxaF T ↔ T.Has y := by
  induction T with
  | leaf K x => simp [taxaF, SpeciesTree.Has]
  | node K l r ihl ihr => simp [taxaF, SpeciesTree.Has, ihl, ihr]

/-- The clusters of a species tree, as a finite set. -/
def clustersF : SpeciesTree Y → Finset (Finset Y)
  | .leaf _ x => {{x}}
  | .node _ l r => insert (taxaF l ∪ taxaF r) (clustersF l ∪ clustersF r)

omit [Fintype Y] in
theorem coe_taxaF (T : SpeciesTree Y) : (taxaF T : Set Y) = {y | T.Has y} := by
  ext y
  simp [mem_taxaF]

omit [Fintype Y] in
/-- **The clusters as a finite set are the clusters of the species tree.** -/
theorem mem_clustersF {T : SpeciesTree Y} {A : Finset Y} : A ∈ clustersF T ↔ (A : Set Y) ∈ T.clusters := by
  induction T with
  | leaf K x =>
    simp only [clustersF, mem_singleton, SpeciesTree.clusters, Set.mem_singleton_iff]
    rw [show {y | (SpeciesTree.leaf K x).Has y} = (({x} : Finset Y) : Set Y) from (coe_taxaF _).symm]
    exact Finset.coe_inj.symm
  | node K l r ihl ihr =>
    simp only [clustersF, mem_insert, mem_union, SpeciesTree.clusters, Set.mem_union, Set.mem_singleton_iff, ihl, ihr]
    rw [show {y | (SpeciesTree.node K l r).Has y} = ((taxaF l ∪ taxaF r : Finset Y) : Set Y) from (coe_taxaF (.node K l r)).symm,
      Finset.coe_inj, or_assoc]

omit [Fintype Y] in
theorem subset_taxaF_of_mem {T : SpeciesTree Y} {A : Finset Y} (h : A ∈ clustersF T) : A ⊆ taxaF T := fun y hy =>
  mem_taxaF.2 (SpeciesTree.has_of_mem_cluster (mem_clustersF.1 h) (by simpa using hy))

omit [Fintype Y] in
theorem taxaF_mem_clustersF (T : SpeciesTree Y) : taxaF T ∈ clustersF T := by
  cases T with
  | leaf K x => simp [clustersF, taxaF]
  | node K l r => simp [clustersF, taxaF]

omit [Fintype Y] in
theorem singleton_mem_clustersF {T : SpeciesTree Y} {x : Y} (h : T.Has x) : {x} ∈ clustersF T := by
  induction T with
  | leaf K z =>
    have hxz : x = z := h
    simp [clustersF, hxz]
  | node K l r ihl ihr =>
    rcases h with h | h
    · exact mem_insert_of_mem (mem_union_left _ (ihl h))
    · exact mem_insert_of_mem (mem_union_right _ (ihr h))

omit [Fintype Y] in
theorem nonempty_taxaF (T : SpeciesTree Y) : (taxaF T).Nonempty := by
  induction T with
  | leaf K x => simp [taxaF]
  | node K l r ihl _ => exact ihl.mono subset_union_left

omit [Fintype Y] in
theorem nonempty_of_mem_clustersF {T : SpeciesTree Y} {A : Finset Y} (h : A ∈ clustersF T) : A.Nonempty := by
  induction T with
  | leaf K x =>
    rw [mem_singleton.1 h]
    simp
  | node K l r ihl ihr =>
    rcases mem_insert.1 h with rfl | h
    · exact (nonempty_taxaF l).mono subset_union_left
    · rcases mem_union.1 h with h | h
      · exact ihl h
      · exact ihr h

omit [Fintype Y] in
theorem laminar_clustersF {T : SpeciesTree Y} (hT : T.Nodup) {A B : Finset Y} (hA : A ∈ clustersF T) (hB : B ∈ clustersF T) :
    A ⊆ B ∨ B ⊆ A ∨ Disjoint A B := by
  induction T with
  | leaf K x =>
    rw [mem_singleton.1 hA, mem_singleton.1 hB]
    exact Or.inl subset_rfl
  | node K l r ihl ihr =>
    have htop : ∀ {C : Finset Y}, C ∈ clustersF (.node K l r) → C ⊆ taxaF l ∪ taxaF r := fun h => subset_taxaF_of_mem h
    rcases mem_insert.1 hA with rfl | hA'
    · exact Or.inr (Or.inl (htop hB))
    · rcases mem_insert.1 hB with rfl | hB'
      · exact Or.inl (htop hA)
      · have hdis : ∀ {C E : Finset Y}, C ∈ clustersF l → E ∈ clustersF r → Disjoint C E := by
          intro C E hC hE
          refine Finset.disjoint_left.2 fun y hy hy' => ?_
          exact hT.2.2 y (mem_taxaF.1 (subset_taxaF_of_mem hC hy)) (mem_taxaF.1 (subset_taxaF_of_mem hE hy'))
        rcases mem_union.1 hA' with hA₁ | hA₁ <;> rcases mem_union.1 hB' with hB₁ | hB₁
        · exact ihl hT.1 hA₁ hB₁
        · exact Or.inr (Or.inr (hdis hA₁ hB₁))
        · exact Or.inr (Or.inr (hdis hB₁ hA₁).symm)
        · exact ihr hT.2.1 hA₁ hB₁

/-- **The clusters of a species tree on all the species are a hierarchy.** -/
theorem isHierarchy_clustersF {T : SpeciesTree Y} (hT : T.Nodup) (hall : ∀ x, T.Has x) : IsHierarchy (clustersF T) := by
  have huniv : taxaF T = univ := Finset.eq_univ_of_forall fun x => mem_taxaF.2 (hall x)
  exact ⟨huniv ▸ taxaF_mem_clustersF T, fun x => singleton_mem_clustersF (hall x), fun A hA => nonempty_of_mem_clustersF hA,
    fun A hA B hB => laminar_clustersF hT hA hB⟩

/-- **The species tree as a network**: the library's network of the hierarchy of its clusters, a tree. -/
abbrev speciesNetwork (T : SpeciesTree Y) (hT : T.Nodup) (hall : ∀ x, T.Has x) :=
  hierarchyNetwork (clustersF T) (isHierarchy_clustersF hT hall)

/-- **The tree of blobs of the species network is the unrooted species tree**: on a tree, every edge is a cut edge. -/
theorem treeOfBlobs_speciesNetwork {T : SpeciesTree Y} (hT : T.Nodup) (hall : ∀ x, T.Has x) :
    treeOfBlobs (speciesNetwork T hT hall) = unroot (clustersF T) := by
  ext A
  unfold treeOfBlobs
  simp only [mem_filter, mem_univ, true_and]
  rw [hierarchyNetwork_hasCutSplit_iff]
  constructor
  · exact fun h => h.2.2
  · intro h
    refine ⟨?_, ?_, h⟩
    · rcases mem_unroot.1 h with ⟨hA, -⟩ | ⟨-, hne⟩
      · exact nonempty_of_mem_clustersF hA
      · by_contra he
        rw [Finset.not_nonempty_iff_eq_empty] at he
        exact hne (by rw [he, compl_empty])
    · rcases mem_unroot.1 h with ⟨-, hne⟩ | ⟨hA, -⟩
      · by_contra he
        rw [Finset.not_nonempty_iff_eq_empty] at he
        exact hne (by rw [← compl_compl A, he, compl_empty])
      · exact nonempty_of_mem_clustersF hA

/-- **The bridge for species trees.** The tree of blobs of the species network displays `AB|CD` exactly when the species tree has an edge
separating `A`, `B` from `C`, `D`. So `SpeciesTree.IsQuartet` is the hypothesis of (3.1). -/
theorem displays_treeOfBlobs_iff {T : SpeciesTree Y} (hT : T.Nodup) (hall : ∀ x, T.Has x) {A B C D : Y}
    (h : ({A, B, C, D} : Finset Y).card = 4) :
    Displays (treeOfBlobs (speciesNetwork T hT hall)) (quartetTree A B C D h) ↔ T.IsQuartet A B C D := by
  rw [treeOfBlobs_speciesNetwork, displays_unroot_iff]
  constructor
  · rintro ⟨F, hF, hs | hs⟩
    · exact Or.inl ⟨F, mem_clustersF.1 hF, by simpa using hs⟩
    · exact Or.inr ⟨F, mem_clustersF.1 hF, by simpa using hs⟩
  · have hco : ∀ {S : Set Y}, S ∈ T.clusters → ∃ F ∈ clustersF T, (F : Set Y) = S := by
      intro S hS
      have hsub : S ⊆ {y | T.Has y} := fun y hy => SpeciesTree.has_of_mem_cluster hS hy
      have hfin : S.Finite := Set.toFinite _
      refine ⟨hfin.toFinset, mem_clustersF.2 (by simpa using hS), by simp⟩
    rintro (⟨S, hS, h₁, h₂, h₃, h₄⟩ | ⟨S, hS, h₁, h₂, h₃, h₄⟩)
    · obtain ⟨F, hF, rfl⟩ := hco hS
      exact ⟨F, hF, Or.inl (by simpa using ⟨h₁, h₂, h₃, h₄⟩)⟩
    · obtain ⟨F, hF, rfl⟩ := hco hS
      exact ⟨F, hF, Or.inr (by simpa using ⟨h₁, h₂, h₃, h₄⟩)⟩

/-! ### The probabilities on quartet trees -/

omit [Fintype Y] in
theorem exists_eq_quartetTree (s : QuartetTree Y) : ∃ a b c d, ∃ h : ({a, b, c, d} : Finset Y).card = 4, s = quartetTree a b c d h := by
  obtain ⟨B, C, hs, hB, hC, hd, ht⟩ := s.exists_eq_pair
  obtain ⟨a, b, -, rfl⟩ := card_eq_two.1 hB
  obtain ⟨c, d, -, rfl⟩ := card_eq_two.1 hC
  have hc : ({a, b, c, d} : Finset Y).card = 4 := by
    have h₁ := s.card_taxa
    rw [ht] at h₁
    rw [← h₁]
    congr 1
    ext x
    simp only [mem_insert, mem_singleton, mem_union]
    tauto
  exact ⟨a, b, c, d, hc, Subtype.ext hs⟩

/-- **The probability of a quartet tree**, for a uniform pick of one gene copy in each of its species, given that they all have one. -/
def quartetP (T : SpeciesTree Y) (s : QuartetTree Y) : ℝ :=
  (probTopology T Pat (exists_eq_quartetTree s).choose (exists_eq_quartetTree s).choose_spec.choose
    (exists_eq_quartetTree s).choose_spec.choose_spec.choose (exists_eq_quartetTree s).choose_spec.choose_spec.choose_spec.choose).toReal

omit [Fintype Y] [DecidableEq Y] in
theorem probTopology_swap_left (T : SpeciesTree Y) (A B C D : Y) : probTopology T Pat B A C D = probTopology T Pat A B C D := by
  unfold probTopology
  have h₁ : (fun L : Leaves Y => score pickWeight Pat (L B) (L A) (L C) (L D)) = Sc pickWeight B A C D := rfl
  have h₂ : (fun L : Leaves Y => score pickWeight Pat (L A) (L B) (L C) (L D)) = Sc pickWeight A B C D := rfl
  rw [h₁, h₂, funext (Sc_swap_left pickWeight A B C D)]
  congr 2
  funext L
  refine ind_congr ?_
  unfold Present
  tauto

omit [Fintype Y] [DecidableEq Y] in
theorem probTopology_swap_pair (T : SpeciesTree Y) (A B C D : Y) : probTopology T Pat C D A B = probTopology T Pat A B C D := by
  unfold probTopology
  have h₁ : (fun L : Leaves Y => score pickWeight Pat (L C) (L D) (L A) (L B)) = Sc pickWeight C D A B := rfl
  have h₂ : (fun L : Leaves Y => score pickWeight Pat (L A) (L B) (L C) (L D)) = Sc pickWeight A B C D := rfl
  rw [h₁, h₂, funext (Sc_swap_pair pickWeight A B C D)]
  congr 2
  funext L
  refine ind_congr ?_
  unfold Present
  tauto

omit [Fintype Y] [DecidableEq Y] in
theorem probTopology_swap_right (T : SpeciesTree Y) (A B C D : Y) : probTopology T Pat A B D C = probTopology T Pat A B C D := by
  rw [← probTopology_swap_pair T A B D C, probTopology_swap_left T C D A B, probTopology_swap_pair T A B C D]

omit [Fintype Y] in
/-- **The probability doesn't depend on how the quartet tree is written.** -/
theorem probTopology_congr (T : SpeciesTree Y) {a b c d a' b' c' d' : Y} {h : ({a, b, c, d} : Finset Y).card = 4}
    {h' : ({a', b', c', d'} : Finset Y).card = 4} (he : quartetTree a b c d h = quartetTree a' b' c' d' h') :
    probTopology T Pat a b c d = probTopology T Pat a' b' c' d' := by
  obtain ⟨hab, hac, had, hbc, hbd, hcd⟩ := ne_of_card_four h
  have hval : ({{a, b}, {c, d}} : Finset (Finset Y)) = {{a', b'}, {c', d'}} := congrArg Subtype.val he
  have hne : ({a, b} : Finset Y) ≠ {c, d} := by
    intro hh
    have : a ∈ ({c, d} : Finset Y) := hh ▸ (by simp)
    simp only [mem_insert, mem_singleton] at this
    tauto
  have hpairs : (({a, b} : Finset Y) = {a', b'} ∧ ({c, d} : Finset Y) = {c', d'}) ∨
      (({a, b} : Finset Y) = {c', d'} ∧ ({c, d} : Finset Y) = {a', b'}) := by
    have h₁ : ({a, b} : Finset Y) ∈ ({{a', b'}, {c', d'}} : Finset (Finset Y)) := hval ▸ (by simp)
    have h₂ : ({c, d} : Finset Y) ∈ ({{a', b'}, {c', d'}} : Finset (Finset Y)) := hval ▸ (by simp)
    simp only [mem_insert, mem_singleton] at h₁ h₂
    rcases h₁ with h₁ | h₁ <;> rcases h₂ with h₂ | h₂
    · exact absurd (h₁.trans h₂.symm) hne
    · exact Or.inl ⟨h₁, h₂⟩
    · exact Or.inr ⟨h₁, h₂⟩
    · exact absurd (h₁.trans h₂.symm) hne
  have hsw : ∀ {p q p' q' : Y}, ({p, q} : Finset Y) = {p', q'} → (p = p' ∧ q = q') ∨ (p = q' ∧ q = p') := by
    intro p q p' q' hh
    have h₁ : p ∈ ({p', q'} : Finset Y) := hh ▸ (by simp)
    have h₂ : q ∈ ({p', q'} : Finset Y) := hh ▸ (by simp)
    have h₃ : p' ∈ ({p, q} : Finset Y) := hh ▸ (by simp)
    have h₄ : q' ∈ ({p, q} : Finset Y) := hh ▸ (by simp)
    simp only [mem_insert, mem_singleton] at h₁ h₂ h₃ h₄
    grind
  rcases hpairs with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
  · rcases hsw h₁ with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rcases hsw h₂ with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rfl
    · exact (probTopology_swap_right T a b c d).symm
    · exact (probTopology_swap_left T a b c d).symm
    · rw [probTopology_swap_left T a b d c, probTopology_swap_right T a b c d]
  · rcases hsw h₁ with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rcases hsw h₂ with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact (probTopology_swap_pair T a b c d).symm
    · rw [probTopology_swap_left T c d a b, probTopology_swap_pair T a b c d]
    · rw [probTopology_swap_right T c d a b, probTopology_swap_pair T a b c d]
    · rw [probTopology_swap_left T c d b a, probTopology_swap_right T c d a b, probTopology_swap_pair T a b c d]

omit [Fintype Y] in
/-- **The probability of `ab|cd`.** -/
theorem quartetP_quartetTree (T : SpeciesTree Y) {a b c d : Y} (h : ({a, b, c, d} : Finset Y).card = 4) :
    quartetP T (quartetTree a b c d h) = (probTopology T Pat a b c d).toReal := by
  unfold quartetP
  obtain ⟨_, he⟩ := (exists_eq_quartetTree (quartetTree a b c d h)).choose_spec.choose_spec.choose_spec.choose_spec
  rw [← probTopology_congr T he]

omit [Fintype Y] [DecidableEq Y] in
theorem score_alt_eq (L : Leaves Y) (A B C D : Y) :
    score pickWeight Pat (L A) (L C) (L B) (L D) = score pickWeight (fun a b c d => Pat a c b d) (L A) (L B) (L C) (L D) :=
  (score_swap_mid pickWeight (fun a b c d => Pat a c b d) _ _ _ _).symm

omit [Fintype Y] [DecidableEq Y] in
theorem score_alt₂_eq (L : Leaves Y) (A B C D : Y) :
    score pickWeight Pat (L A) (L D) (L B) (L C) = score pickWeight (fun a b c d => Pat a d b c) (L A) (L B) (L C) (L D) := by
  rw [score_swap_mid pickWeight (fun a b c d => Pat a d b c) (L A) (L B) (L C) (L D),
    score_swap_right pickWeight (fun a c b d => Pat a d b c) (L A) (L C) (L B) (L D),
    score_swap_mid pickWeight (fun a c d b => Pat a d b c) (L A) (L C) (L D) (L B),
    score_swap_right pickWeight (fun a d c b => Pat a d b c) (L A) (L D) (L C) (L B)]

omit [Fintype Y] [DecidableEq Y] in
theorem probTopology_alt (T : SpeciesTree Y) (A B C D : Y) :
    probTopology T Pat A C B D = probTopology T (fun a b c d => Pat a c b d) A B C D := by
  unfold probTopology
  simp only [score_alt_eq]
  congr 2
  funext L
  refine ind_congr ?_
  unfold Present
  tauto

omit [Fintype Y] [DecidableEq Y] in
theorem probTopology_alt₂ (T : SpeciesTree Y) (A B C D : Y) :
    probTopology T Pat A D B C = probTopology T (fun a b c d => Pat a d b c) A B C D := by
  unfold probTopology
  simp only [score_alt₂_eq]
  congr 2
  funext L
  refine ind_congr ?_
  unfold Present
  tauto

/-- The three quartet trees on four taxa. -/
theorem treesOn_eq {a b c d : Y} (h : ({a, b, c, d} : Finset Y).card = 4) (h₁ : ({a, c, b, d} : Finset Y).card = 4)
    (h₂ : ({a, d, b, c} : Finset Y).card = 4) :
    treesOn ({a, b, c, d} : Finset Y) = {quartetTree a b c d h, quartetTree a c b d h₁, quartetTree a d b c h₂} ∧
      quartetTree a b c d h ≠ quartetTree a c b d h₁ ∧ quartetTree a b c d h ≠ quartetTree a d b c h₂ ∧
      quartetTree a c b d h₁ ≠ quartetTree a d b c h₂ := by
  obtain ⟨hab, hac, had, hbc, hbd, hcd⟩ := ne_of_card_four h
  have hnot : ∀ {u v p q : Y}, u ≠ p → u ≠ q → ({u, v} : Finset Y) ≠ {p, q} := by
    intro u v p q h₁ h₂ he
    have : u ∈ ({p, q} : Finset Y) := he ▸ (by simp)
    simp only [mem_insert, mem_singleton] at this
    tauto
  have hnot' : ∀ {u v p q : Y}, v ≠ p → v ≠ q → ({u, v} : Finset Y) ≠ {p, q} := by
    intro u v p q h₁ h₂ he
    have : v ∈ ({p, q} : Finset Y) := he ▸ (by simp)
    simp only [mem_insert, mem_singleton] at this
    tauto
  have hne₁ : quartetTree a b c d h ≠ quartetTree a c b d h₁ := by
    intro he
    have hv : ({a, b} : Finset Y) ∈ (quartetTree a c b d h₁).val := by
      rw [← he]
      simp
    simp only [quartetTree_val, mem_insert, mem_singleton] at hv
    rcases hv with hv | hv
    · exact hnot' hab.symm hbc hv
    · exact hnot (u := a) (v := b) (p := b) (q := d) hab had hv
  have hne₂ : quartetTree a b c d h ≠ quartetTree a d b c h₂ := by
    intro he
    have hv : ({a, b} : Finset Y) ∈ (quartetTree a d b c h₂).val := by
      rw [← he]
      simp
    simp only [quartetTree_val, mem_insert, mem_singleton] at hv
    rcases hv with hv | hv
    · exact hnot' hab.symm hbd hv
    · exact hnot hab hac hv
  have hne₃ : quartetTree a c b d h₁ ≠ quartetTree a d b c h₂ := by
    intro he
    have hv : ({a, c} : Finset Y) ∈ (quartetTree a d b c h₂).val := by
      rw [← he]
      simp
    simp only [quartetTree_val, mem_insert, mem_singleton] at hv
    rcases hv with hv | hv
    · exact hnot' hac.symm hcd hv
    · exact hnot hab hac hv
  refine ⟨?_, hne₁, hne₂, hne₃⟩
  symm
  refine Finset.eq_of_subset_of_card_le ?_ ?_
  · intro r hr
    simp only [mem_insert, mem_singleton] at hr
    rw [mem_treesOn]
    rcases hr with rfl | rfl | rfl
    · exact quartetTree_taxa _ _ _ _ _
    · rw [quartetTree_taxa]
      ext x
      simp only [mem_insert, mem_singleton]
      tauto
    · rw [quartetTree_taxa]
      ext x
      simp only [mem_insert, mem_singleton]
      tauto
  · rw [card_treesOn h, Finset.card_eq_three.2 ⟨_, _, _, hne₁, hne₂, hne₃, rfl⟩]

omit [Fintype Y] in
theorem card_rearrange {a b c d : Y} (h : ({a, b, c, d} : Finset Y).card = 4) :
    ({a, c, b, d} : Finset Y).card = 4 ∧ ({a, d, b, c} : Finset Y).card = 4 := by
  constructor
  · rw [← h]
    congr 1
    ext x
    simp only [mem_insert, mem_singleton]
    tauto
  · rw [← h]
    congr 1
    ext x
    simp only [mem_insert, mem_singleton]
    tauto

omit [Fintype Y] in
/-- The probability of a topology is finite, on four species with a positive probability of having copies. -/
theorem probTopology_ne_top {T : SpeciesTree Y} {a b c d : Y} (h : ({a, b, c, d} : Finset Y).card = 4)
    (hpos : 0 < expect (geneLaw T) fun L => ind (Present a b c d L)) :
    probTopology T Pat a b c d ≠ ⊤ ∧ probTopology T (fun a b c d => Pat a c b d) a b c d ≠ ⊤ ∧
      probTopology T (fun a b c d => Pat a d b c) a b c d ≠ ⊤ := by
  obtain ⟨hab, hac, had, hbc, hbd, hcd⟩ := ne_of_card_four h
  have hsum := sum_probTopology (T := T) hab hac had hbc hbd hcd hpos
  refine ⟨?_, ?_, ?_⟩
  · intro ht
    rw [ht] at hsum
    simp at hsum
  · intro ht
    rw [ht] at hsum
    simp at hsum
  · intro ht
    rw [ht] at hsum
    simp at hsum

/-- **The probabilities of the three quartet trees on four species sum to one**, on a species tree on all the species where a copy can go
through each edge. -/
theorem sum_treesOn_quartetP {T : SpeciesTree Y} (hS : T.Survives) (hall : ∀ x, T.Has x) {q : Finset Y} (hq : q.card = 4) :
    ∑ r ∈ treesOn q, quartetP T r = 1 := by
  obtain ⟨s₀, hs₀⟩ : (treesOn q).Nonempty := Finset.card_pos.1 (by rw [card_treesOn hq]; norm_num)
  obtain ⟨a, b, c, d, h, rfl⟩ := exists_eq_quartetTree s₀
  have hqe : q = {a, b, c, d} := by
    rw [← mem_treesOn.1 hs₀, quartetTree_taxa]
  subst hqe
  obtain ⟨hab, hac, had, hbc, hbd, hcd⟩ := ne_of_card_four h
  obtain ⟨h₁, h₂⟩ := card_rearrange h
  obtain ⟨he, hne₁, hne₂, hne₃⟩ := treesOn_eq h h₁ h₂
  have hpos := present_pos hS (hall a) (hall b) (hall c) (hall d)
  obtain ⟨hf₁, hf₂, hf₃⟩ := probTopology_ne_top h hpos
  have hsum := sum_probTopology (T := T) hab hac had hbc hbd hcd hpos
  rw [he, Finset.sum_insert (by simp [hne₁, hne₂]), Finset.sum_pair hne₃, quartetP_quartetTree, quartetP_quartetTree,
    quartetP_quartetTree, probTopology_alt T a b c d, probTopology_alt₂ T a b c d, ← add_assoc, ← ENNReal.toReal_add hf₁ hf₂,
    ← ENNReal.toReal_add (ENNReal.add_ne_top.2 ⟨hf₁, hf₂⟩) hf₃, hsum]
  rfl

/-- **(3.1) on a species tree, as the hypothesis of ECToBlob's Theorem 3.1** (`ext:legried_eq5_quartet`). If the tree of blobs of the species
network displays `s`, then the probability of `s`, for a uniform pick of one copy per species, exceeds those of its alternatives. -/
theorem quartetP_lt {T : SpeciesTree Y} (hT : T.Nodup) (hall : ∀ x, T.Has x) (hS : T.Survives) {s r : QuartetTree Y}
    (hs : Displays (treeOfBlobs (speciesNetwork T hT hall)) s) (hr : r ∈ s.alternatives) : quartetP T r < quartetP T s := by
  obtain ⟨a, b, c, d, h, rfl⟩ := exists_eq_quartetTree s
  obtain ⟨hab, -, -, -, -, hcd⟩ := ne_of_card_four h
  have hq := (displays_treeOfBlobs_iff hT hall h).1 hs
  have hpos := present_pos hS (hall a) (hall b) (hall c) (hall d)
  obtain ⟨hlt₁, hlt₂⟩ := eq5 hT hab hcd (hall a) (hall b) (hall c) (hall d) hq hpos
  obtain ⟨hf₁, hf₂, hf₃⟩ := probTopology_ne_top h hpos
  obtain ⟨h₁, h₂⟩ := card_rearrange h
  obtain ⟨he, -, -, -⟩ := treesOn_eq h h₁ h₂
  obtain ⟨hrt, hrs⟩ := QuartetTree.mem_alternatives.1 hr
  have hrm : r ∈ treesOn ({a, b, c, d} : Finset Y) := mem_treesOn.2 (hrt.trans (quartetTree_taxa _ _ _ _ _))
  rw [he] at hrm
  simp only [mem_insert, mem_singleton] at hrm
  rcases hrm with rfl | rfl | rfl
  · exact absurd rfl hrs
  · rw [quartetP_quartetTree, quartetP_quartetTree, probTopology_alt T a b c d]
    exact (ENNReal.toReal_lt_toReal hf₂ hf₁).2 hlt₁
  · rw [quartetP_quartetTree, quartetP_quartetTree, probTopology_alt₂ T a b c d]
    exact (ENNReal.toReal_lt_toReal hf₃ hf₁).2 hlt₂

end Displays

end External.LegriedEtAl2021
