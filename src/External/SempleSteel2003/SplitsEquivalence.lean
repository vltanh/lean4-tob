module

public import External.SempleSteel2003.Support
public import Mathlib.Data.Fintype.Lattice

/-!
# The Splits Equivalence Theorem (Semple, Steel 2003, Theorem 3.1.4)

See the `README.md` of this directory. The book wasn't read, and the proofs are standard arguments.

* Existence: root the splits at an element `x₀` of `X`. The sides not containing `x₀` are a laminar family, whose graph
  (`External/SempleSteel2003/Support.lean`) is the `X`-tree.
* Uniqueness: a node `w` of an `X`-tree orients every split, towards `w` (`orient`). The orientations of the nodes are exactly the
  consistent orientations of the splits (`exists_orient_eq`), which depend only on the splits; two nodes are adjacent exactly
  when their orientations differ in one split (`orient_adj`).
-/

@[expose] public section

open scoped Classical

namespace SempleSteel2003

variable {X W W' : Type*}

/-- An `X`-tree: a tree with a map from `X` to its vertices, where every vertex of degree at most two is labelled. -/
structure IsXTree (T : SimpleGraph W) (φ : X → W) : Prop where
  isTree : T.IsTree
  labelled : ∀ v, (T.neighborSet v).ncard ≤ 2 → v ∈ Set.range φ

/-- The side of the split of the edge `e` containing `x`. -/
def edgeSide (T : SimpleGraph W) (φ : X → W) (e : Sym2 W) (x : X) : Set X :=
  {y | (T.deleteEdges {e}).Reachable (φ x) (φ y)}

/-- The split system `Σ(T)`, as the family of sides of the splits of the edges. -/
def splitSides (T : SimpleGraph W) (φ : X → W) : Set (Set X) :=
  {A | ∃ e ∈ T.edgeSet, ∃ x, A = edgeSide T φ e x}

/-- A collection of `X`-splits, as the family of their sides: both sides are nonempty. -/
def IsSplitSystem (F : Set (Set X)) : Prop :=
  ∀ A ∈ F, A.Nonempty ∧ Aᶜ.Nonempty ∧ Aᶜ ∈ F

/-- The splits are pairwise compatible: for any two, one of the four intersections of their sides is empty. -/
def PairwiseCompatible (F : Set (Set X)) : Prop :=
  ∀ A ∈ F, ∀ B ∈ F, A ∩ B = ∅ ∨ A ∩ Bᶜ = ∅ ∨ Aᶜ ∩ B = ∅ ∨ Aᶜ ∩ Bᶜ = ∅

section Sides

variable {T : SimpleGraph W} {φ : X → W}

/-- The side of the edge `e` containing the node `w`, on `X`. -/
def sideOf (T : SimpleGraph W) (φ : X → W) (e : Sym2 W) (w : W) : Set X :=
  {y | (T.deleteEdges {e}).Reachable w (φ y)}

theorem edgeSide_eq_sideOf (e : Sym2 W) (x : X) : edgeSide T φ e x = sideOf T φ e (φ x) := rfl

theorem sideOf_eq_of_reachable {e : Sym2 W} {u v : W} (h : (T.deleteEdges {e}).Reachable u v) :
    sideOf T φ e u = sideOf T φ e v := by
  ext y
  exact ⟨fun hy => h.symm.trans hy, fun hy => h.trans hy⟩

/-- For three nodes and an edge of a tree, two of them are on one side. -/
theorem reachable_of_three (hT : T.IsTree) {e : Sym2 W} (he : e ∈ T.edgeSet) (u v z : W) :
    (T.deleteEdges {e}).Reachable u v ∨ (T.deleteEdges {e}).Reachable u z ∨ (T.deleteEdges {e}).Reachable v z := by
  induction e using Sym2.ind with
  | _ a b =>
    rcases reachable_deleteEdges_or hT.1 a b u with h₁ | h₁ <;> rcases reachable_deleteEdges_or hT.1 a b v with h₂ | h₂ <;>
      rcases reachable_deleteEdges_or hT.1 a b z with h₃ | h₃
    · exact Or.inl (h₁.symm.trans h₂)
    · exact Or.inl (h₁.symm.trans h₂)
    · exact Or.inr (Or.inl (h₁.symm.trans h₃))
    · exact Or.inr (Or.inr (h₂.symm.trans h₃))
    · exact Or.inr (Or.inr (h₂.symm.trans h₃))
    · exact Or.inr (Or.inl (h₁.symm.trans h₃))
    · exact Or.inl (h₁.symm.trans h₂)
    · exact Or.inl (h₁.symm.trans h₂)

/-- Nodes on different sides of an edge of a tree have complementary sides. -/
theorem sideOf_compl (hT : T.IsTree) {e : Sym2 W} (he : e ∈ T.edgeSet) {u v : W} (h : ¬ (T.deleteEdges {e}).Reachable u v) :
    (sideOf T φ e u)ᶜ = sideOf T φ e v := by
  ext y
  constructor
  · intro hy
    rcases reachable_of_three hT he u v (φ y) with h' | h' | h'
    · exact absurd h' h
    · exact absurd h' hy
    · exact h'
  · intro hy hy'
    exact h (hy'.trans (Set.mem_ofPred.1 hy).symm)

end Sides

section Labels

variable [Finite W] {T : SimpleGraph W} {φ : X → W}

/-- **Each branch at an edge has a label.** Going down the branch, a node with no further branching has degree at most two. -/
theorem exists_label_branch (hX : IsXTree T φ) {a b : W} (hab : T.Adj a b) :
    ∃ x, (T.deleteEdges {s(a, b)}).Reachable b (φ x) := by
  induction hn : {y | (T.deleteEdges {s(a, b)}).Reachable b y}.ncard using Nat.strong_induction_on generalizing a b with
  | _ n ih =>
    by_cases hb : (T.neighborSet b).ncard ≤ 2
    · obtain ⟨x, hx⟩ := hX.labelled b hb
      exact ⟨x, by rw [hx]⟩
    · have hone : 1 < (T.neighborSet b).ncard := by omega
      obtain ⟨b', hb', hne⟩ := Set.exists_ne_of_one_lt_ncard hone a
      have hbb' : T.Adj b b' := hb'
      have hnr : ¬ (T.deleteEdges {s(b, b')}).Reachable b' b := fun h =>
        not_reachable_deleteEdges hX.isTree.2 hbb' h.symm
      have hstep : (T.deleteEdges {s(a, b)}).Adj b b' := by
        refine deleteEdges_adj_of_ne hbb' fun he => ?_
        rcases Sym2.eq_iff.1 he with ⟨h₁, -⟩ | ⟨-, h₂⟩
        · exact hab.ne h₁.symm
        · exact hne h₂
      have hsub : ∀ {y}, (T.deleteEdges {s(b, b')}).Reachable b' y → (T.deleteEdges {s(a, b)}).Reachable b y := fun hy =>
        hstep.reachable.trans (reachable_deleteEdges_of_not_reachable (c := b) (by simp) hnr hy)
      have hlt : {y | (T.deleteEdges {s(b, b')}).Reachable b' y}.ncard < n := by
        rw [← hn]
        refine Set.ncard_lt_ncard ⟨fun y hy => hsub hy, fun h => ?_⟩ (Set.toFinite _)
        exact hnr (h (show (T.deleteEdges {s(a, b)}).Reachable b b from .refl _))
      obtain ⟨x, hx⟩ := ih _ hlt hbb' rfl
      exact ⟨x, hsub hx⟩

omit [Finite W] in
/-- The branches at a node are disjoint. -/
theorem not_reachable_branch (hT : T.IsTree) {w n n' y : W} (hn : T.Adj w n) (hn' : T.Adj w n') (hne : n ≠ n')
    (hy : (T.deleteEdges {s(w, n)}).Reachable n y) : ¬ (T.deleteEdges {s(w, n')}).Reachable n' y := by
  intro hy'
  have hnr : ¬ (T.deleteEdges {s(w, n')}).Reachable n' w := fun h =>
    not_reachable_deleteEdges hT.2 hn' h.symm
  have h₁ : (T.deleteEdges {s(w, n)}).Reachable n' y :=
    reachable_deleteEdges_of_not_reachable (c := w) (by simp) hnr hy'
  have hstep : (T.deleteEdges {s(w, n)}).Adj w n' := by
    refine deleteEdges_adj_of_ne hn' fun he => ?_
    rcases Sym2.eq_iff.1 he with ⟨-, h₂⟩ | ⟨h₂, -⟩
    · exact hne h₂.symm
    · exact hn.ne h₂
  exact not_reachable_deleteEdges hT.2 hn (hstep.reachable.trans (h₁.trans hy.symm))

/-- **Any two sides at a node have a common label.** A node of degree at most two is labelled. Otherwise, it has three branches,
and the two edges are in at most two of them, or at their edges to the node; the third branch has a label. -/
theorem exists_label_both (hX : IsXTree T φ) (w : W) {e e' : Sym2 W} (he : e ∈ T.edgeSet) (he' : e' ∈ T.edgeSet) :
    ∃ x, (T.deleteEdges {e}).Reachable w (φ x) ∧ (T.deleteEdges {e'}).Reachable w (φ x) := by
  classical
  by_cases hw : (T.neighborSet w).ncard ≤ 2
  · obtain ⟨x, hx⟩ := hX.labelled w hw
    exact ⟨x, by rw [hx], by rw [hx]⟩
  obtain ⟨n₁, n₂, n₃, h₁, h₂, h₃, h₁₂, h₁₃, h₂₃⟩ := Set.two_lt_ncard_iff (Set.toFinite _) |>.1 (by omega : 2 < (T.neighborSet w).ncard)
  have h₁' : T.Adj w n₁ := h₁
  have h₂' : T.Adj w n₂ := h₂
  have h₃' : T.Adj w n₃ := h₃
  have hT := hX.isTree
  -- an end of each edge other than `w`
  have hend : ∀ {f : Sym2 W}, f ∈ T.edgeSet → ∃ c ∈ f, c ≠ w := by
    intro f hf
    induction f using Sym2.ind with
    | _ a b =>
      have hab : T.Adj a b := hf
      by_cases ha : a = w
      · exact ⟨b, by simp, fun hb => hab.ne (ha.trans hb.symm)⟩
      · exact ⟨a, by simp, ha⟩
  obtain ⟨c, hc, hcw⟩ := hend he
  obtain ⟨c', hc', hcw'⟩ := hend he'
  -- a branch that holds neither
  have hbr : ∃ n, T.Adj w n ∧ ¬ (T.deleteEdges {s(w, n)}).Reachable n c ∧ ¬ (T.deleteEdges {s(w, n)}).Reachable n c' := by
    by_contra hno
    push Not at hno
    have d₁₂ := fun y => not_reachable_branch (y := y) hT h₁' h₂' h₁₂
    have d₁₃ := fun y => not_reachable_branch (y := y) hT h₁' h₃' h₁₃
    have d₂₃ := fun y => not_reachable_branch (y := y) hT h₂' h₃' h₂₃
    have k₁ := hno n₁ h₁'
    have k₂ := hno n₂ h₂'
    have k₃ := hno n₃ h₃'
    by_cases p₁ : (T.deleteEdges {s(w, n₁)}).Reachable n₁ c
    · by_cases p₂ : (T.deleteEdges {s(w, n₂)}).Reachable n₂ c
      · exact d₁₂ c p₁ p₂
      · have q₂ := k₂ p₂
        by_cases p₃ : (T.deleteEdges {s(w, n₃)}).Reachable n₃ c
        · exact d₁₃ c p₁ p₃
        · exact d₂₃ c' q₂ (k₃ p₃)
    · have q₁ := k₁ p₁
      by_cases p₂ : (T.deleteEdges {s(w, n₂)}).Reachable n₂ c
      · by_cases p₃ : (T.deleteEdges {s(w, n₃)}).Reachable n₃ c
        · exact d₂₃ c p₂ p₃
        · exact d₁₃ c' q₁ (k₃ p₃)
      · exact d₁₂ c' q₁ (k₂ p₂)
  obtain ⟨n, hn, hnc, hnc'⟩ := hbr
  obtain ⟨x, hx⟩ := exists_label_branch hX hn
  have key : ∀ {f : Sym2 W} {d : W}, d ∈ f → d ≠ w → ¬ (T.deleteEdges {s(w, n)}).Reachable n d →
      (T.deleteEdges {f}).Reachable w (φ x) := by
    intro f d hd hdw hnd
    have hstep : (T.deleteEdges {f}).Adj w n := by
      refine deleteEdges_adj_of_ne hn fun hf => ?_
      rw [← hf, Sym2.mem_iff] at hd
      rcases hd with rfl | rfl
      · exact hdw rfl
      · exact hnd (.refl _)
    exact hstep.reachable.trans (reachable_deleteEdges_of_not_reachable hd hnd hx)
  exact ⟨x, key hc hcw hnc, key hc' hcw' hnc'⟩

/-- The orientation of the splits towards the node `w`. -/
def orient (T : SimpleGraph W) (φ : X → W) (w : W) : Set (Set X) := {A | ∃ e ∈ T.edgeSet, A = sideOf T φ e w}

omit [Finite W] in
theorem sideOf_mem_orient {e : Sym2 W} (he : e ∈ T.edgeSet) (w : W) : sideOf T φ e w ∈ orient T φ w := ⟨e, he, rfl⟩

theorem orient_subset (hX : IsXTree T φ) (w : W) : orient T φ w ⊆ splitSides T φ := by
  rintro _ ⟨e, he, rfl⟩
  obtain ⟨x, hx, -⟩ := exists_label_both hX w he he
  exact ⟨e, he, x, sideOf_eq_of_reachable hx⟩

theorem orient_inter (hX : IsXTree T φ) (w : W) {A B : Set X} (hA : A ∈ orient T φ w) (hB : B ∈ orient T φ w) :
    (A ∩ B).Nonempty := by
  obtain ⟨e, he, rfl⟩ := hA
  obtain ⟨e', he', rfl⟩ := hB
  obtain ⟨x, h₁, h₂⟩ := exists_label_both hX w he he'
  exact ⟨x, h₁, h₂⟩

theorem not_compl_mem_orient (hX : IsXTree T φ) (w : W) {A : Set X} (hA : A ∈ orient T φ w) : Aᶜ ∉ orient T φ w := fun hc => by
  obtain ⟨x, h₁, h₂⟩ := orient_inter hX w hA hc
  exact h₂ h₁

omit [Finite W] in
theorem orient_total (hX : IsXTree T φ) (w : W) {A : Set X} (hA : A ∈ splitSides T φ) :
    A ∈ orient T φ w ∨ Aᶜ ∈ orient T φ w := by
  obtain ⟨e, he, x, rfl⟩ := hA
  by_cases h : (T.deleteEdges {e}).Reachable w (φ x)
  · left
    rw [edgeSide_eq_sideOf, ← sideOf_eq_of_reachable h]
    exact sideOf_mem_orient he w
  · right
    rw [edgeSide_eq_sideOf, sideOf_compl hX.isTree he (fun h' => h h'.symm)]
    exact sideOf_mem_orient he w

/-- **A consistent orientation is that of a node.** At a node with the fewest edges oriented away from it, an edge oriented away
gives a neighbour with fewer: the edge at the node towards it is also oriented away, or the two chosen sides would be disjoint. -/
theorem exists_orient_eq (hX : IsXTree T φ) {O : Set (Set X)} (hsub : O ⊆ splitSides T φ)
    (hinter : ∀ A ∈ O, ∀ B ∈ O, (A ∩ B).Nonempty) (htotal : ∀ A ∈ splitSides T φ, A ∈ O ∨ Aᶜ ∈ O) :
    ∃ w, orient T φ w = O := by
  classical
  have hT := hX.isTree
  have : Nonempty W := hT.1.nonempty
  let bad : W → Set (Sym2 W) := fun w => {e | e ∈ T.edgeSet ∧ sideOf T φ e w ∉ O}
  obtain ⟨w, hw⟩ := Finite.exists_min fun w => (bad w).ncard
  -- each side at a node is one of the splits
  have hside : ∀ {e} (_ : e ∈ T.edgeSet) (u : W), sideOf T φ e u ∈ splitSides T φ := fun he u =>
    orient_subset hX u (sideOf_mem_orient he u)
  have hflip : ∀ {u n : W}, T.Adj u n → sideOf T φ s(u, n) u ∉ O → sideOf T φ s(u, n) n ∈ O := by
    intro u n hadj hb
    have hs := htotal _ (hside (e := s(u, n)) hadj u)
    rw [sideOf_compl hT hadj (not_reachable_deleteEdges hT.2 hadj)] at hs
    exact hs.resolve_left hb
  -- the step: from a bad edge at `w`, a bad edge out of `w`
  have hstep : ∀ {e}, e ∈ bad w → ∃ n, T.Adj w n ∧ s(w, n) ∈ bad w := by
    intro e heb
    obtain ⟨he, hbad⟩ := heb
    -- name the end of `e` on the side of `w`
    obtain ⟨a, b, rfl, hab, haw⟩ : ∃ a b, e = s(a, b) ∧ T.Adj a b ∧ (T.deleteEdges {e}).Reachable a w := by
      induction e using Sym2.ind with
      | _ a b =>
        have hab : T.Adj a b := he
        rcases reachable_deleteEdges_or hT.1 a b w with h | h
        · exact ⟨a, b, rfl, hab, h⟩
        · exact ⟨b, a, Sym2.eq_swap, hab.symm, h⟩
    by_cases hwa : w = a
    · subst hwa
      exact ⟨b, hab, he, hbad⟩
    · obtain ⟨n, hn, hna⟩ := exists_adj_reachable_deleteEdges hT.1 hwa
      refine ⟨n, hn, hn, fun hin => ?_⟩
      have hab' := not_reachable_deleteEdges hT.2 hab
      have hbO : sideOf T φ s(a, b) b ∈ O := by
        have := hflip hab (by rwa [sideOf_eq_of_reachable haw])
        exact this
      obtain ⟨x, hx₁, hx₂⟩ := hinter _ hin _ hbO
      -- `w` isn't on the side of `b`, so what's on the side of `b` is connected to `b` without `wn`
      have hbw : ¬ (T.deleteEdges {s(a, b)}).Reachable b w := fun h => hab' (haw.trans h.symm)
      have h₁ : (T.deleteEdges {s(w, n)}).Reachable b (φ x) :=
        reachable_deleteEdges_of_not_reachable (c := w) (by simp) hbw hx₂
      have hne : s(a, b) ≠ s(w, n) := by
        intro heq
        rcases Sym2.eq_iff.1 heq with ⟨h₂, -⟩ | ⟨-, h₂⟩
        · exact hwa h₂.symm
        · exact hbw (by rw [h₂])
      have h₂ : (T.deleteEdges {s(w, n)}).Adj a b := deleteEdges_adj_of_ne hab hne
      exact not_reachable_deleteEdges hT.2 hn ((show (T.deleteEdges {s(w, n)}).Reachable w (φ x) from hx₁).trans
        (h₁.symm.trans (h₂.reachable.symm.trans hna.symm)))
  have hempty : ∀ e, e ∉ bad w := by
    intro e he
    obtain ⟨n, hn, hb⟩ := hstep he
    have hlt : (bad n).ncard < (bad w).ncard := by
      refine Set.ncard_lt_ncard ⟨?_, fun hsub' => ?_⟩ (Set.toFinite _)
      · rintro f ⟨hf, hfb⟩
        refine ⟨hf, fun hfO => hfb ?_⟩
        by_cases hfe : f = s(w, n)
        · subst hfe
          exact hflip hn hb.2
        · rw [← sideOf_eq_of_reachable (deleteEdges_adj_of_ne hn (Ne.symm hfe)).reachable]
          exact hfO
      · exact (hsub' hb).2 (hflip hn hb.2)
    exact absurd (hw n) (not_le.2 hlt)
  refine ⟨w, Set.Subset.antisymm ?_ fun A hA => ?_⟩
  · rintro _ ⟨e, he, rfl⟩
    by_contra hno
    exact hempty e ⟨he, hno⟩
  · rcases orient_total hX w (hsub hA) with h | h
    · exact h
    · exfalso
      obtain ⟨e, he, heq⟩ := h
      have hmem : Aᶜ ∈ O := by
        rw [heq]
        by_contra hno
        exact hempty e ⟨he, hno⟩
      obtain ⟨x, h₁, h₂⟩ := hinter A hA _ hmem
      exact h₂ h₁

/-- Distinct nodes have distinct orientations. -/
theorem orient_injective (hX : IsXTree T φ) {u v : W} (h : orient T φ u = orient T φ v) : u = v := by
  by_contra hne
  have hT := hX.isTree
  obtain ⟨n, hn, hnv⟩ := exists_adj_reachable_deleteEdges hT.1 hne
  have hnr := not_reachable_deleteEdges hT.2 hn
  have huv : ¬ (T.deleteEdges {s(u, n)}).Reachable u v := fun h' => hnr (h'.trans hnv.symm)
  have h₁ : sideOf T φ s(u, n) u ∈ orient T φ v := h ▸ sideOf_mem_orient hn u
  have h₂ : (sideOf T φ s(u, n) u)ᶜ ∈ orient T φ v := by
    rw [sideOf_compl hT hn huv]
    exact sideOf_mem_orient hn v
  exact not_compl_mem_orient hX v h₁ h₂

variable [Finite W'] {T' : SimpleGraph W'} {φ' : X → W'}

/-- **Adjacent nodes go to adjacent nodes.** The orientations of adjacent nodes differ in one split only. If the images weren't
adjacent, two edges between them would have that one split, and a node between these two edges would contradict
`exists_label_both`. -/
theorem orient_adj (hX : IsXTree T φ) (hX' : IsXTree T' φ') {f : W → W'} (hf : ∀ w, orient T' φ' (f w) = orient T φ w) {u v : W}
    (huv : T.Adj u v) : T'.Adj (f u) (f v) := by
  have hT := hX.isTree
  have hT' := hX'.isTree
  by_contra hna
  have hne : f u ≠ f v := fun h => huv.ne (orient_injective hX (by rw [← hf, ← hf, h]))
  -- an edge between the images has the side `sideOf s(u, v) u`
  have key : ∀ {e'}, e' ∈ T'.edgeSet → ¬ (T'.deleteEdges {e'}).Reachable (f u) (f v) →
      sideOf T' φ' e' (f u) = sideOf T φ s(u, v) u := by
    intro e' he' hsep
    have h₁ : sideOf T' φ' e' (f u) ∈ orient T φ u := hf u ▸ sideOf_mem_orient he' (f u)
    have h₂ : (sideOf T' φ' e' (f u))ᶜ ∈ orient T φ v := by
      rw [sideOf_compl hT' he' hsep]
      exact hf v ▸ sideOf_mem_orient he' (f v)
    obtain ⟨d, hd, hdeq⟩ := h₁
    by_cases hde : d = s(u, v)
    · rw [hdeq, hde]
    · exfalso
      have h₃ : sideOf T φ d u ∈ orient T φ v := by
        rw [sideOf_eq_of_reachable (deleteEdges_adj_of_ne huv (Ne.symm hde)).reachable]
        exact sideOf_mem_orient hd v
      rw [← hdeq] at h₃
      exact not_compl_mem_orient hX v h₃ h₂
  obtain ⟨n₁, hn₁, hn₁v⟩ := exists_adj_reachable_deleteEdges hT'.1 hne
  have hn₁ne : n₁ ≠ f v := fun h => hna (h ▸ hn₁)
  obtain ⟨n₂, hn₂, hn₂v⟩ := exists_adj_reachable_deleteEdges hT'.1 hn₁ne
  have hb₁ := not_reachable_deleteEdges hT'.2 hn₁
  have hb₂ := not_reachable_deleteEdges hT'.2 hn₂
  have hn₂u : n₂ ≠ f u := by
    rintro rfl
    rw [Sym2.eq_swap] at hn₂v
    exact hb₁ (hn₂v.trans hn₁v.symm)
  have hee : s(f u, n₁) ≠ s(n₁, n₂) := by
    intro heq
    rcases Sym2.eq_iff.1 heq with ⟨h₁, -⟩ | ⟨h₁, -⟩
    · exact hn₁.ne h₁
    · exact hn₂u h₁.symm
  have hstep : (T'.deleteEdges {s(n₁, n₂)}).Adj (f u) n₁ := deleteEdges_adj_of_ne hn₁ hee
  have hsep₁ : ¬ (T'.deleteEdges {s(f u, n₁)}).Reachable (f u) (f v) := fun h => hb₁ (h.trans hn₁v.symm)
  have hsep₂ : ¬ (T'.deleteEdges {s(n₁, n₂)}).Reachable (f u) (f v) := fun h =>
    hb₂ (hstep.reachable.symm.trans (h.trans hn₂v.symm))
  have k₁ := key hn₁ hsep₁
  have k₂ := key hn₂ hsep₂
  -- the node between the two edges
  obtain ⟨x, hx₁, hx₂⟩ := exists_label_both hX' n₁ (e := s(f u, n₁)) (e' := s(n₁, n₂)) hn₁ hn₂
  have hx₃ : x ∈ sideOf T' φ' s(n₁, n₂) (f u) := hstep.reachable.trans hx₂
  have hx₄ : x ∉ sideOf T' φ' s(f u, n₁) (f u) := by
    intro h
    exact hb₁ ((show (T'.deleteEdges {s(f u, n₁)}).Reachable (f u) (φ' x) from h).trans
      (show (T'.deleteEdges {s(f u, n₁)}).Reachable n₁ (φ' x) from hx₁).symm)
  rw [k₁] at hx₄
  rw [k₂] at hx₃
  exact hx₄ hx₃

/-- The orientation of a labelled node depends on the splits only. -/
theorem orient_label (hX : IsXTree T φ) (x : X) : orient T φ (φ x) = {A | A ∈ splitSides T φ ∧ x ∈ A} := by
  ext A
  constructor
  · intro hA
    refine ⟨orient_subset hX _ hA, ?_⟩
    obtain ⟨e, -, rfl⟩ := hA
    exact SimpleGraph.Reachable.refl _
  · rintro ⟨⟨e, he, y, rfl⟩, hx⟩
    rw [edgeSide_eq_sideOf, sideOf_eq_of_reachable (show (T.deleteEdges {e}).Reachable (φ y) (φ x) from hx)]
    exact sideOf_mem_orient he _

end Labels

section Transport

variable {T : SimpleGraph W} {T' : SimpleGraph W'} {φ : X → W}

/-- An isomorphism carries an `X`-tree to an `X`-tree with the same split system. -/
theorem IsXTree.map (hX : IsXTree T φ) (f : T ≃g T') : IsXTree T' (f ∘ φ) := by
  refine ⟨f.isTree_iff.1 hX.isTree, fun v hv => ?_⟩
  have hn : (T.neighborSet (f.symm v)).ncard = (T'.neighborSet v).ncard := by
    rw [← ncard_neighborSet_iso f, RelIso.apply_symm_apply]
  obtain ⟨x, hx⟩ := hX.labelled (f.symm v) (hn ▸ hv)
  exact ⟨x, by simp [hx]⟩

theorem splitSides_map (f : T ≃g T') : splitSides T' (f ∘ φ) = splitSides T φ := by
  have hside : ∀ e x, edgeSide T' (f ∘ φ) (e.map f) x = edgeSide T φ e x := by
    intro e x
    ext y
    exact reachable_deleteEdges_iso f e (φ x) (φ y)
  ext A
  constructor
  · rintro ⟨e', he', x, rfl⟩
    have hmap : e' = (e'.map f.symm).map f := by
      rw [Sym2.map_map]
      simp
    have hmem : e'.map f.symm ∈ T.edgeSet := by
      induction e' using Sym2.ind with
      | _ a b =>
        have h : T'.Adj a b := he'
        rw [Sym2.map_mk, SimpleGraph.mem_edgeSet, ← f.map_adj_iff]
        simpa using h
    exact ⟨_, hmem, x, by rw [← hside, ← hmap]⟩
  · rintro ⟨e, he, x, rfl⟩
    refine ⟨e.map f, ?_, x, (hside e x).symm⟩
    induction e using Sym2.ind with
    | _ a b =>
      have h : T.Adj a b := he
      rw [Sym2.map_mk, SimpleGraph.mem_edgeSet, f.map_adj_iff]
      exact h

end Transport

section Existence

variable {F : Set (Set X)} [Finite X] [Nonempty X]

/-- The sides not containing `x₀`. -/
def rootedSides (F : Set (Set X)) (x₀ : X) : Set (Set X) := {A | A ∈ F ∧ x₀ ∉ A}

omit [Finite X] [Nonempty X] in
theorem rootedSides_isLaminar (hF : IsSplitSystem F) (hc : PairwiseCompatible F) (x₀ : X) : IsLaminar (rootedSides F x₀) where
  nonempty A hA := (hF A hA.1).1
  comparable A hA B hB := by
    rcases hc A hA.1 B hB.1 with h | h | h | h
    · exact Or.inl (Set.disjoint_iff_inter_eq_empty.2 h)
    · refine Or.inr (Or.inl fun x hx => ?_)
      by_contra hxB
      exact (Set.eq_empty_iff_forall_notMem.1 h x) ⟨hx, hxB⟩
    · refine Or.inr (Or.inr fun x hx => ?_)
      by_contra hxA
      exact (Set.eq_empty_iff_forall_notMem.1 h x) ⟨hxA, hx⟩
    · exact absurd ⟨hA.2, hB.2⟩ (Set.eq_empty_iff_forall_notMem.1 h x₀)

theorem lam_isXTree {L : Set (Set X)} (hL : IsLaminar L) {x₀ : X} (hx₀ : ∀ A ∈ L, x₀ ∉ A) : IsXTree (lamGraph L) hL.label := by
  refine ⟨lamGraph_isTree hL, fun v hv => ?_⟩
  by_contra hno
  -- `v` isn't the root, which is the label of `x₀`
  have hroot : hL.label x₀ = lamRoot L := by
    apply Subtype.ext
    rcases (hL.label x₀).2 with hA | hA
    · exact absurd (hL.mem_label x₀) (hx₀ _ hA)
    · exact hA
  have hvr : v ≠ lamRoot L := fun h => hno ⟨x₀, by rw [hroot, h]⟩
  obtain ⟨p, hp⟩ := exists_covBy_of_ne_root hvr
  -- a child below each element of `v`
  have hchild : ∀ x ∈ v.1, ∃ c, c ⋖ v ∧ x ∈ c.1 := by
    intro x hx
    have hle : hL.label x ≤ v := hL.label_le_iff.2 hx
    have hlt : hL.label x < v := lt_of_le_of_ne hle fun h => hno ⟨x, h⟩
    obtain ⟨c, hc₁, hc₂⟩ := exists_le_covBy_of_lt hlt
    exact ⟨c, hc₂, mem_of_le hc₁ (hL.mem_label x)⟩
  obtain ⟨x, hx⟩ := hL.node_nonempty v
  obtain ⟨c₁, hc₁, hxc₁⟩ := hchild x hx
  -- `c₁` is strictly below `v`: there's an element of `v` off it
  obtain ⟨y, hy, hyc⟩ : ∃ y ∈ v.1, y ∉ c₁.1 := by
    by_contra hall
    push Not at hall
    exact hc₁.lt.not_ge (Subtype.coe_le_coe.1 hall)
  obtain ⟨c₂, hc₂, hyc₂⟩ := hchild y hy
  have hne₁₂ : c₁ ≠ c₂ := fun h => hyc (h ▸ hyc₂)
  have hthree : 2 < ((lamGraph L).neighborSet v).ncard := by
    refine Set.two_lt_ncard_iff (Set.toFinite _) |>.2 ⟨p, c₁, c₂, lamGraph_adj.2 (Or.inl hp), lamGraph_adj.2 (Or.inr hc₁),
      lamGraph_adj.2 (Or.inr hc₂), ?_, ?_, hne₁₂⟩
    · rintro rfl
      exact hp.lt.not_gt hc₁.lt
    · rintro rfl
      exact hp.lt.not_gt hc₂.lt
  omega

theorem lam_edgeSide {L : Set (Set X)} (hL : IsLaminar L) {a b : LamNode L} (hab : a ⋖ b) (x : X) :
    edgeSide (lamGraph L) hL.label s(a, b) x = if x ∈ a.1 then a.1 else a.1ᶜ := by
  ext y
  change ((lamGraph L).deleteEdges {s(a, b)}).Reachable _ _ ↔ _
  rw [lam_reachable_deleteEdges_iff hL hab, hL.label_le_iff, hL.label_le_iff]
  by_cases hx : x ∈ a.1
  · simp [hx]
  · simp [hx]

theorem lam_splitSides (hF : IsSplitSystem F) (hc : PairwiseCompatible F) (x₀ : X) :
    splitSides (lamGraph (rootedSides F x₀)) (rootedSides_isLaminar hF hc x₀).label = F := by
  have hL := rootedSides_isLaminar hF hc x₀
  ext A
  constructor
  · rintro ⟨e, he, x, rfl⟩
    induction e using Sym2.ind with
    | _ a b =>
      -- the lower end of the edge is a side
      have key : ∀ {a b : LamNode (rootedSides F x₀)}, a ⋖ b → a.1 ∈ F := by
        intro a b hab
        rcases a with ⟨a, ha | rfl⟩
        · exact ha.1
        · exact absurd (le_lamRoot b) hab.lt.not_ge
      have hadj := lamGraph_adj.1 (show (lamGraph (rootedSides F x₀)).Adj a b from he)
      rcases hadj with h | h
      · rw [lam_edgeSide hL h]
        split_ifs
        · exact key h
        · exact (hF _ (key h)).2.2
      · rw [Sym2.eq_swap, lam_edgeSide hL h]
        split_ifs
        · exact key h
        · exact (hF _ (key h)).2.2
  · intro hA
    -- a side, from the node of the side without `x₀`
    have key : ∀ {B : Set X}, B ∈ F → x₀ ∉ B → ∀ x, ∃ e ∈ (lamGraph (rootedSides F x₀)).edgeSet,
        edgeSide (lamGraph (rootedSides F x₀)) hL.label e x = if x ∈ B then B else Bᶜ := by
      intro B hB hxB x
      let a : LamNode (rootedSides F x₀) := ⟨B, Or.inl ⟨hB, hxB⟩⟩
      have ha : a ≠ lamRoot (rootedSides F x₀) := fun h => hxB (by
        have : B = Set.univ := congrArg Subtype.val h
        rw [this]; exact Set.mem_univ _)
      obtain ⟨b, hb⟩ := exists_covBy_of_ne_root ha
      exact ⟨s(a, b), lamGraph_adj.2 (Or.inl hb), lam_edgeSide hL hb x⟩
    by_cases hx : x₀ ∈ A
    · obtain ⟨e, he, heq⟩ := key (hF A hA).2.2 (fun h => h hx) x₀
      refine ⟨e, he, x₀, ?_⟩
      rw [heq]
      simp [hx]
    · obtain ⟨y, hy⟩ := (hF A hA).1
      obtain ⟨e, he, heq⟩ := key hA hx y
      refine ⟨e, he, y, ?_⟩
      rw [heq]
      simp [hy]

end Existence

/-- **The Splits Equivalence Theorem** (`ext:splits_equivalence`), existence (Semple, Steel 2003, Theorem 3.1.4). -/
theorem exists_xTree_iff [Finite X] [Nonempty X] {F : Set (Set X)} (hF : IsSplitSystem F) :
    PairwiseCompatible F ↔ ∃ (n : ℕ) (T : SimpleGraph (Fin n)) (φ : X → Fin n), IsXTree T φ ∧ splitSides T φ = F := by
  constructor
  · intro hc
    obtain ⟨x₀⟩ := ‹Nonempty X›
    have hL := rootedSides_isLaminar hF hc x₀
    have hx₀ : ∀ A ∈ rootedSides F x₀, x₀ ∉ A := fun A hA => hA.2
    obtain ⟨n, T', ⟨f⟩⟩ := exists_iso_fin (lamGraph (rootedSides F x₀))
    exact ⟨n, T', f ∘ hL.label, (lam_isXTree hL hx₀).map f, (splitSides_map f).trans (lam_splitSides hF hc x₀)⟩
  · rintro ⟨n, T, φ, hX, rfl⟩ A ⟨e, he, x, rfl⟩ B ⟨e', he', y, rfl⟩
    have hT := hX.isTree
    induction e using Sym2.ind with
    | _ a b =>
    induction e' using Sym2.ind with
    | _ c d =>
    obtain ⟨u, v, t, t', hee, huv, hff, htt, hfar⟩ := exists_far_sides hT (show T.Adj a b from he) (show T.Adj c d from he')
    rw [edgeSide_eq_sideOf, edgeSide_eq_sideOf]
    -- each side is one of the two named, or the complement
    have hA : sideOf T φ s(a, b) (φ x) = sideOf T φ s(a, b) u ∨ sideOf T φ s(a, b) (φ x) = (sideOf T φ s(a, b) u)ᶜ := by
      by_cases h : (T.deleteEdges {s(a, b)}).Reachable u (φ x)
      · exact Or.inl (sideOf_eq_of_reachable h).symm
      · exact Or.inr (sideOf_compl hT he h).symm
    have hB : sideOf T φ s(c, d) (φ y) = sideOf T φ s(c, d) t ∨ sideOf T φ s(c, d) (φ y) = (sideOf T φ s(c, d) t)ᶜ := by
      by_cases h : (T.deleteEdges {s(c, d)}).Reachable t (φ y)
      · exact Or.inl (sideOf_eq_of_reachable h).symm
      · exact Or.inr (sideOf_compl hT he' h).symm
    have hdisj : sideOf T φ s(a, b) u ∩ sideOf T φ s(c, d) t = ∅ := by
      refine Set.eq_empty_iff_forall_notMem.2 fun z hz => ?_
      exact hfar _ ⟨hz.1, hz.2⟩
    rcases hA with hA | hA <;> rcases hB with hB | hB <;> rw [hA, hB]
    · exact Or.inl hdisj
    · right; left; simpa using hdisj
    · right; right; left; simpa using hdisj
    · right; right; right; simpa using hdisj

/-- **The Splits Equivalence Theorem** (`ext:splits_equivalence`), uniqueness (Semple, Steel 2003, Theorem 3.1.4). -/
theorem xTree_unique [Finite X] [Nonempty X] [Finite W] [Finite W'] {T : SimpleGraph W} {T' : SimpleGraph W'}
    {φ : X → W} {φ' : X → W'} (hT : IsXTree T φ) (hT' : IsXTree T' φ') (h : splitSides T φ = splitSides T' φ') :
    ∃ f : T ≃g T', ∀ x, f (φ x) = φ' x := by
  have hex : ∀ w, ∃ w', orient T' φ' w' = orient T φ w := fun w =>
    exists_orient_eq hT' (h ▸ orient_subset hT w) (fun A hA B hB => orient_inter hT w hA hB)
      (fun A hA => orient_total hT w (h ▸ hA))
  have hex' : ∀ w', ∃ w, orient T φ w = orient T' φ' w' := fun w' =>
    exists_orient_eq hT (h.symm ▸ orient_subset hT' w') (fun A hA B hB => orient_inter hT' w' hA hB)
      (fun A hA => orient_total hT' w' (h.symm ▸ hA))
  choose f hf using hex
  choose g hg using hex'
  have hgf : ∀ w, g (f w) = w := fun w => orient_injective hT (by rw [hg, hf])
  have hfg : ∀ w', f (g w') = w' := fun w' => orient_injective hT' (by rw [hf, hg])
  refine ⟨{ toFun := f, invFun := g, left_inv := hgf, right_inv := hfg, map_rel_iff' := ?_ }, fun x => ?_⟩
  · intro u v
    constructor
    · intro hadj
      have := orient_adj hT' hT hg hadj
      simpa [hgf] using this
    · exact orient_adj hT hT' hf
  · refine orient_injective hT' ?_
    change orient T' φ' (f (φ x)) = _
    rw [hf, orient_label hT, orient_label hT', h]

end SempleSteel2003
