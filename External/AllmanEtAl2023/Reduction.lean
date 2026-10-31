module

public import Basic.Phylogenetics.DeletedArcs
public import Basic.Phylogenetics.TreeMetric

/-!
# Allman, Baños, Mitchell, Rhodes 2023, Theorem 1(b): the graph side

The source proves part (b) of its Theorem 1 at boundary parameters: an inheritance probability `0`
deletes a hybrid arc. This file is the part of that proof about graphs. It reads the network off a set
`D` of deleted arcs (`Basic/Phylogenetics/DeletedArcs.lean`). Its result, `exists_reduction`: a 4-set
`q` that is not treelike has a set `D` and a reticulation
`h` with exactly two parents `k₁`, `k₂` off `D` and exactly one taxon `a` of `q` below it, such that
deleting either parent gives a cut split, and the two splits differ.

The steps, in the source's order (`notes/sources/allman2023.txt`, lines 145-149):

1. `IsTreelikeOff`, which is `IsTreelike` at `D = ∅` (`isTreelikeOff_empty_iff`).
2. If no vertex ancestral to `q` off `D` is a reticulation, a tree on four taxa has a `2|2` arc
   (`isTreelikeOff_or_starOff`).
3. Otherwise take a lowest reticulation `h`, with parents `k₁`, `k₂`; while deleting one leaves `q`
   non-treelike, delete it (the source's "set `γᵢ = 0`"; `exists_reduction_aux`, by induction).
4. If both deletions give cut splits, the vertices ancestral to `q` below `h` form a tree. If it had
   two taxa of `q`, some arc in it would separate `2|2` off `D`, so exactly one taxon `a` is below `h`
   (`isTreelikeOff_or_starOff` again).
5. The two splits differ, the source's contradiction argument (`IsLowPair.exists_splitOffAt`).

The non-binary variant that ECToBlob's adaptation needs is `exists_reduction_of_blobDegree`: only the
two uses of the degrees differ, and they are the hypotheses of `exists_reduction_aux`.
-/

@[expose] public noncomputable section

open Phylogenetics Phylogenetics.RootedNetwork Finset
open scoped Classical

namespace External.AllmanEtAl2023

variable {V E X : Type*} {N : RootedNetwork V E X} {D : Set E}

/-! ### The source's contradiction, in one network -/

/-- If `e'` dominates `a` and `e`, above `e'`, dominates a taxon `b` below `e'`, then `e` dominates
`a`: a path to `a` avoiding `e` would reach `e'`, and continue to `b`. -/
theorem dominatesOff_of_above (hN : N.IsPhylogenetic) {e e' : E} {a b : X}
    (he'a : N.DominatesOff D e' a) (heb : N.DominatesOff D e b) (he'b : N.IsBelowOff D e' b)
    (hord : N.ReachesOff D (N.graph.target e) (N.graph.source e')) : N.DominatesOff D e a := by
  intro hr
  rcases hr.split e' with hl | ⟨hp, he', -⟩
  · exact he'a (hl.mono (Set.insert_subset_insert (Set.subset_insert _ _)))
  · have h₁ : N.ReachesOff (insert e D) N.root (N.graph.target e') :=
      (hp.mono (Set.subset_insert _ _)).tail_arc he'
    have h₂ : N.ReachesOff (insert e D) (N.graph.target e') (N.leaf b) :=
      ReachesOff.insert_of_target_reaches hN.acyclic (hord.tail_arc he'b.1) he'b.2
    exact heb (h₁.trans h₂)

/-- The case of the source's contradiction with the two cut edges of opposite directions. Let `e'`
dominate `a` and `b`, with `c` not below it, and let `c` be below `e`, with `b` not below it. Then `a`
is not below `e`: a path from `e` to `a` either avoids `e'`, and then `e'` is above `e` and so above
`c`, or it passes `e'`, and then `b` is below `e`. -/
theorem not_isBelowOff_of_opposite (hN : N.IsPhylogenetic) (hD : N.IsDeletion D) {e e' : E}
    {a b c : X} (he'a : N.DominatesOff D e' a) (he'c : ¬ N.IsBelowOff D e' c)
    (he'b : N.IsBelowOff D e' b) (hec : N.IsBelowOff D e c) (heb : ¬ N.IsBelowOff D e b) :
    ¬ N.IsBelowOff D e a := by
  rintro ⟨he, hr⟩
  rcases hr.split e' with hl | ⟨hp, he', -⟩
  · have hne : e ≠ e' := by
      rintro rfl
      exact he'c hec
    rcases (hD.root_reachesOff hN (N.graph.source e)).split e' with hp' | ⟨-, he'', hr'⟩
    · exact he'a ((hp'.tail_arc (by simp [hne, he])).trans hl)
    · exact he'c ⟨he'', (hr'.tail_arc he).trans hec.2⟩
  · exact heb ⟨he, ((hp.mono (Set.subset_insert _ _)).tail_arc he').trans he'b.2⟩

/-! ### The source's contradiction, over both deletions -/

/-- The situation of the source's last step: two parents `k₁ ≠ k₂` off the deletion `D` of a vertex
below which, of the taxa `Y`, at most `a` lies. -/
structure IsLowPair (N : RootedNetwork V E X) (D : Set E) (k₁ k₂ : E) (a : X) (Y : Set X) : Prop where
  phylogenetic : N.IsPhylogenetic
  deletion : N.IsDeletion D
  ne : k₁ ≠ k₂
  target_eq : N.graph.target k₁ = N.graph.target k₂
  notMem₁ : k₁ ∉ D
  notMem₂ : k₂ ∉ D
  not_reaches : ∀ x ∈ Y, x ≠ a → ¬ N.ReachesOff D (N.graph.target k₁) (N.leaf x)

namespace IsLowPair

variable {k₁ k₂ e e' : E} {a b c x : X} {Y P Q : Set X}

theorem symm (hL : IsLowPair N D k₁ k₂ a Y) : IsLowPair N D k₂ k₁ a Y where
  phylogenetic := hL.phylogenetic
  deletion := hL.deletion
  ne := hL.ne.symm
  target_eq := hL.target_eq.symm
  notMem₁ := hL.notMem₂
  notMem₂ := hL.notMem₁
  not_reaches x hx hxa := hL.target_eq ▸ hL.not_reaches x hx hxa

theorem isDeletion_insert_left (hL : IsLowPair N D k₁ k₂ a Y) : N.IsDeletion (insert k₁ D) :=
  hL.deletion.insert hL.phylogenetic hL.ne hL.target_eq hL.notMem₂

theorem dominatesOff_left_iff (hL : IsLowPair N D k₁ k₂ a Y) (hx : x ∈ Y) (hxa : x ≠ a) :
    N.DominatesOff (insert k₁ D) e x ↔ N.DominatesOff D e x :=
  dominatesOff_insert_iff (hL.not_reaches x hx hxa)

theorem isBelowOff_left_iff (hL : IsLowPair N D k₁ k₂ a Y) (hx : x ∈ Y) (hxa : x ≠ a) :
    N.IsBelowOff (insert k₁ D) e x ↔ N.IsBelowOff D e x :=
  isBelowOff_insert_iff (hL.not_reaches x hx hxa)

theorem ne_of_isBelowOff (hL : IsLowPair N D k₁ k₂ a Y) (hb : N.IsBelowOff D e x) (hx : x ∈ Y)
    (hxa : x ≠ a) : e ≠ k₁ ∧ e ≠ k₂ := by
  constructor
  · rintro rfl
    exact hL.not_reaches x hx hxa hb.2
  · rintro rfl
    exact hL.symm.not_reaches x hx hxa hb.2

/-- A taxon other than `a` does not see which of `k₁`, `k₂` is deleted. -/
theorem dominatesOff_swap (hL : IsLowPair N D k₁ k₂ a Y) (hx : x ∈ Y) (hxa : x ≠ a)
    (h : N.DominatesOff (insert k₁ D) e x) : N.DominatesOff (insert k₂ D) e x :=
  (hL.symm.dominatesOff_left_iff hx hxa).mpr ((hL.dominatesOff_left_iff hx hxa).mp h)

/-- A taxon other than `a` does not see which of `k₁`, `k₂` is deleted. -/
theorem not_isBelowOff_swap (hL : IsLowPair N D k₁ k₂ a Y) (hx : x ∈ Y) (hxa : x ≠ a)
    (h : ¬ N.IsBelowOff (insert k₁ D) e x) : ¬ N.IsBelowOff (insert k₂ D) e x := fun h' =>
  h ((hL.isBelowOff_left_iff hx hxa).mpr ((hL.symm.isBelowOff_left_iff hx hxa).mp h'))

/-- The end of the source's contradiction: an arc that induces a split both when `k₁` and when `k₂` is
deleted induces it in the network itself. Every path uses at most one of `k₁`, `k₂`. -/
theorem separatesOff_of_both (hL : IsLowPair N D k₁ k₂ a Y) (he : e ≠ k₁ ∧ e ≠ k₂)
    (h₁ : N.SeparatesOff (insert k₁ D) e P Q) (h₂ : N.SeparatesOff (insert k₂ D) e P Q) :
    N.SeparatesOff D e P Q := by
  refine ⟨fun x hx => ?_, fun x hx => ?_⟩
  · exact dominatesOff_of_insert_of_insert hL.phylogenetic.acyclic hL.ne hL.target_eq
      (h₁.1 x hx) (h₂.1 x hx)
  · exact not_isBelowOff_of_insert_of_insert hL.phylogenetic.acyclic hL.ne hL.target_eq he.1 he.2
      (h₁.2 x hx) (h₂.2 x hx)

/-- A path off `D` that ends above a taxon other than `a` does not use `k₁`. -/
theorem reachesOff_insert (hL : IsLowPair N D k₁ k₂ a Y) (hx : x ∈ Y) (hxa : x ≠ a) {u w : V}
    (h : N.ReachesOff D u w) (hw : N.ReachesOff D w (N.leaf x)) : N.ReachesOff (insert k₁ D) u w :=
  h.insert_of_not_reaches fun h' => hL.not_reaches x hx hxa (h'.trans hw)

/-- Both cut edges dominate the side of `a`, and `e` is the one above: `e` is the nearer of the two to
the blob of `b` and the other side. -/
theorem separatesOff_upper (hL : IsLowPair N D k₁ k₂ a Y) (hP : P ⊆ Y) (hQ : Q ⊆ Y) (hb : b ∈ P)
    (hba : b ≠ a) (hQa : a ∉ Q) (hs : N.SeparatesOff (insert k₂ D) e P Q)
    (hs' : N.SeparatesOff (insert k₁ D) e' P Q)
    (hord : N.ReachesOff D (N.graph.target e) (N.graph.source e')) : N.SeparatesOff D e P Q := by
  have hN := hL.phylogenetic
  have heb : N.DominatesOff (insert k₁ D) e b := hL.symm.dominatesOff_swap (hP hb) hba (hs.1 b hb)
  have he'b : N.IsBelowOff (insert k₁ D) e' b := (hs'.1 b hb).isBelowOff hN hL.isDeletion_insert_left
  have hne := hL.ne_of_isBelowOff ((hL.dominatesOff_left_iff (hP hb) hba).mp heb |>.isBelowOff hN
    hL.deletion) (hP hb) hba
  refine hL.separatesOff_of_both hne ⟨fun x hx => ?_, fun x hx => ?_⟩ hs
  · by_cases hxa : x = a
    · subst hxa
      refine dominatesOff_of_above hN (hs'.1 x hx) heb he'b ?_
      refine hL.reachesOff_insert (hP hb) hba hord ?_
      have he' : e' ∉ D := fun h => he'b.1 (Set.mem_insert_of_mem _ h)
      exact ReachesOff.head_arc he' (he'b.2.mono (Set.subset_insert _ _))
    · exact hL.symm.dominatesOff_swap (hP hx) hxa (hs.1 x hx)
  · have hxa : x ≠ a := fun h => hQa (h ▸ hx)
    exact hL.symm.not_isBelowOff_swap (hQ hx) hxa (hs.2 x hx)

/-- Both cut edges dominate the side away from `a`, and `e` is the one below: again `e` is the nearer
of the two to the blob. -/
theorem separatesOff_lower (hL : IsLowPair N D k₁ k₂ a Y) (hP : P ⊆ Y) (hQ : Q ⊆ Y) (hc : c ∈ P)
    (hPa : a ∉ P) (hs : N.SeparatesOff (insert k₁ D) e P Q)
    (hs' : N.SeparatesOff (insert k₂ D) e' P Q)
    (hord : N.ReachesOff D (N.graph.target e') (N.graph.source e)) : N.SeparatesOff D e P Q := by
  have hN := hL.phylogenetic
  have hca : c ≠ a := fun h => hPa (h ▸ hc)
  have hec : N.IsBelowOff D e c :=
    ((hL.dominatesOff_left_iff (hP hc) hca).mp (hs.1 c hc)).isBelowOff hN hL.deletion
  have he'c : N.IsBelowOff (insert k₂ D) e' c :=
    (hs'.1 c hc).isBelowOff hN hL.symm.isDeletion_insert_left
  have hne := hL.ne_of_isBelowOff hec (hP hc) hca
  refine hL.separatesOff_of_both hne hs ⟨fun x hx => ?_, fun x hx => ?_⟩
  · exact hL.dominatesOff_swap (hP hx) (fun h => hPa (h ▸ hx)) (hs.1 x hx)
  · by_cases hxa : x = a
    · subst hxa
      rintro ⟨he, hr⟩
      refine hs'.2 x hx ⟨he'c.1, ?_⟩
      have h₁ : N.ReachesOff (insert k₂ D) (N.graph.target e') (N.graph.source e) :=
        hL.symm.reachesOff_insert (hP hc) hca hord
          (ReachesOff.head_arc hec.1 hec.2)
      exact (h₁.tail_arc he).trans hr
    · exact hL.not_isBelowOff_swap (hQ hx) hxa (hs.2 x hx)

/-- The cut edge `e`, when `k₁` is deleted, dominates the side away from `a`, and the cut edge `e'`,
when `k₂` is deleted, dominates the side of `a`. Then `e` is the one nearer the blob. -/
theorem separatesOff_opposite (hL : IsLowPair N D k₁ k₂ a Y) (hP : P ⊆ Y) (hQ : Q ⊆ Y) (ha : a ∈ Q)
    (hb : b ∈ Q) (hba : b ≠ a) (hc : c ∈ P) (hPa : a ∉ P)
    (hs : N.SeparatesOff (insert k₁ D) e P Q) (hs' : N.SeparatesOff (insert k₂ D) e' Q P) :
    N.SeparatesOff D e P Q := by
  have hN := hL.phylogenetic
  have hca : c ≠ a := fun h => hPa (h ▸ hc)
  have hne := hL.ne_of_isBelowOff
    (((hL.dominatesOff_left_iff (hP hc) hca).mp (hs.1 c hc)).isBelowOff hN hL.deletion) (hP hc) hca
  have hdel₂ := hL.symm.isDeletion_insert_left
  refine hL.separatesOff_of_both hne hs ⟨fun x hx => ?_, fun x hx => ?_⟩
  · exact hL.dominatesOff_swap (hP hx) (fun h => hPa (h ▸ hx)) (hs.1 x hx)
  · by_cases hxa : x = a
    · subst hxa
      exact not_isBelowOff_of_opposite hN hdel₂ (hs'.1 x ha) (hs'.2 c hc)
        ((hs'.1 b hb).isBelowOff hN hdel₂)
        ((hL.dominatesOff_swap (hP hc) hca (hs.1 c hc)).isBelowOff hN hdel₂)
        (hL.not_isBelowOff_swap (hQ hb) hba (hs.2 b hb))
    · exact hL.not_isBelowOff_swap (hQ hx) hxa (hs.2 x hx)

variable [DecidableEq X] {e₁ e₂ : E} {s : QuartetTree X}

/-- **The source's contradiction** (`notes/sources/allman2023.txt`, line 149), in domination language:
if deleting `k₂` and deleting `k₁` give cut arcs `e₁`, `e₂` of the same quartet tree, then an arc induces
it in the network itself.

Of the four taxa `a, b, c, d`, with `a` the taxon below `k₁`, `k₂` and `ab|cd` the split, the
subnetwork `N₃` on `b, c, d` is the part of the network that does not see which arc is deleted
(`dominatesOff_swap`, `not_isBelowOff_swap`). Each `eᵢ` is a cut edge of `N₃` with `b` on one side and
`c, d` on the other, so they lie on the chain of such cut edges, and `a` is attached on the `b`-side of
each. An arc of this chain nearest the blob of `b, c, d` therefore has `a` on the `b`-side in both
deletions (`separatesOff_upper`, `separatesOff_lower`, `separatesOff_opposite`, by the directions of
the two arcs), and every path to `a` uses at most one of `k₁`, `k₂`, so this arc is a cut edge of the
network with the split `ab|cd` (`separatesOff_of_both`).

Departure from the paper: the source takes `e` to be the cut edge of `N₃` incident to the blob on
`b, c, d`. Here `e` is the nearer of `e₁`, `e₂` to that blob. This needs no description of the blob, and
the steps after the choice of `e` are the source's. -/
theorem exists_splitOffAt (hL : IsLowPair N D k₁ k₂ a (s.taxa : Set X)) (ha : a ∈ s.taxa)
    (h₁ : N.SplitOffAt (insert k₂ D) e₁ s) (h₂ : N.SplitOffAt (insert k₁ D) e₂ s) :
    ∃ e, N.SplitOffAt D e s := by
  have hN := hL.phylogenetic
  obtain ⟨P₁, hP₁, hs₁⟩ := h₁
  obtain ⟨P₂, hP₂, hs₂⟩ := h₂
  have hsub : ∀ P ∈ s.val, (P : Set X) ⊆ s.taxa := fun P hP =>
    Finset.coe_subset.mpr (s.subset_taxa hP)
  have hsub' : ∀ P : Finset X, ((s.taxa \ P : Finset X) : Set X) ⊆ s.taxa := fun P =>
    Finset.coe_subset.mpr Finset.sdiff_subset
  have h12 : P₂ = P₁ ∨ P₂ = s.taxa \ P₁ := by
    have := hP₂
    rw [s.eq_pair_of_mem hP₁] at this
    simpa using this
  have hcard : ∀ P ∈ s.val, 1 < P.card := fun P hP => by
    rw [s.card_of_mem hP]
    norm_num
  by_cases ha₁ : a ∈ P₁
  · by_cases ha₂ : a ∈ P₂
    · -- Both cut edges dominate the side of `a`.
      have hP : P₂ = P₁ := by
        rcases h12 with h | h
        · exact h
        · rw [h] at ha₂
          exact absurd ha₁ (Finset.mem_sdiff.mp ha₂).2
      subst hP
      obtain ⟨b, hb, hba⟩ := Finset.exists_mem_ne (hcard _ hP₁) a
      have hb' : b ∈ (P₂ : Set X) := Finset.mem_coe.mpr hb
      have hQa : a ∉ ((s.taxa \ P₂ : Finset X) : Set X) := by simp [ha₁]
      have hbY := hsub _ hP₁ hb'
      have hd₁ : N.DominatesOff D e₁ b :=
        (hL.symm.dominatesOff_left_iff hbY hba).mp (hs₁.1 b hb')
      have hd₂ : N.DominatesOff D e₂ b := (hL.dominatesOff_left_iff hbY hba).mp (hs₂.1 b hb')
      by_cases hne : e₁ = e₂
      · subst hne
        exact ⟨e₁, P₂, hP₁, hL.separatesOff_of_both
          (hL.ne_of_isBelowOff (hd₁.isBelowOff hN hL.deletion) hbY hba) hs₂ hs₁⟩
      · rcases hd₁.reaches_or_reaches hN hL.deletion hd₂ hne with hord | hord
        · exact ⟨e₁, P₂, hP₁,
            hL.separatesOff_upper (hsub _ hP₁) (hsub' _) hb' hba hQa hs₁ hs₂ hord⟩
        · exact ⟨e₂, P₂, hP₁,
            hL.symm.separatesOff_upper (hsub _ hP₁) (hsub' _) hb' hba hQa hs₂ hs₁ hord⟩
    · -- The cut edge of `k₂` deleted dominates the side of `a`, that of `k₁` deleted the other.
      have hP : P₂ = s.taxa \ P₁ := by
        rcases h12 with h | h
        · rw [h] at ha₂
          exact absurd ha₁ ha₂
        · exact h
      have hQ : s.taxa \ P₂ = P₁ := by
        rw [hP, Finset.sdiff_sdiff_eq_self (s.subset_taxa hP₁)]
      obtain ⟨b, hb, hba⟩ := Finset.exists_mem_ne (hcard _ hP₁) a
      obtain ⟨c, hc⟩ := Finset.card_pos.mp (Nat.zero_lt_of_lt (hcard _ hP₂))
      rw [hQ] at hs₂
      have hs₁' : N.SeparatesOff (insert k₂ D) e₁ ((s.taxa \ P₂ : Finset X) : Set X) (P₂ : Set X) := by
        rw [hQ, hP]
        exact hs₁
      refine ⟨e₂, P₂, hP₂, ?_⟩
      rw [hQ]
      exact hL.separatesOff_opposite (hsub _ hP₂) (hsub _ hP₁) (Finset.mem_coe.mpr ha₁)
        (Finset.mem_coe.mpr hb) hba (Finset.mem_coe.mpr hc) (by simpa using ha₂) hs₂
        (by rwa [hQ] at hs₁')
  · by_cases ha₂ : a ∈ P₂
    · -- The cut edge of `k₁` deleted dominates the side of `a`, that of `k₂` deleted the other.
      have hP : P₂ = s.taxa \ P₁ := by
        rcases h12 with h | h
        · rw [h] at ha₂
          exact absurd ha₂ ha₁
        · exact h
      have hQ : s.taxa \ P₁ = P₂ := hP.symm
      have hQ' : s.taxa \ P₂ = P₁ := by
        rw [hP, Finset.sdiff_sdiff_eq_self (s.subset_taxa hP₁)]
      obtain ⟨b, hb, hba⟩ := Finset.exists_mem_ne (hcard _ hP₂) a
      obtain ⟨c, hc⟩ := Finset.card_pos.mp (Nat.zero_lt_of_lt (hcard _ hP₁))
      rw [hQ] at hs₁
      rw [hQ'] at hs₂
      refine ⟨e₁, P₁, hP₁, ?_⟩
      rw [hQ]
      exact hL.symm.separatesOff_opposite (hsub _ hP₁) (hsub _ hP₂) (Finset.mem_coe.mpr ha₂)
        (Finset.mem_coe.mpr hb) hba (Finset.mem_coe.mpr hc) (by simpa using ha₁) hs₁ hs₂
    · -- Both cut edges dominate the side away from `a`.
      have hP : P₂ = P₁ := by
        rcases h12 with h | h
        · exact h
        · refine absurd ?_ ha₂
          rw [h]
          exact Finset.mem_sdiff.mpr ⟨ha, ha₁⟩
      subst hP
      obtain ⟨c, hc⟩ := Finset.card_pos.mp (Nat.zero_lt_of_lt (hcard _ hP₁))
      have hc' : c ∈ (P₂ : Set X) := Finset.mem_coe.mpr hc
      have hPa : a ∉ (P₂ : Set X) := by simpa using ha₁
      have hcY := hsub _ hP₁ hc'
      have hca : c ≠ a := fun h => ha₁ (h ▸ hc)
      have hd₁ : N.DominatesOff D e₁ c :=
        (hL.symm.dominatesOff_left_iff hcY hca).mp (hs₁.1 c hc')
      have hd₂ : N.DominatesOff D e₂ c := (hL.dominatesOff_left_iff hcY hca).mp (hs₂.1 c hc')
      by_cases hne : e₁ = e₂
      · subst hne
        exact ⟨e₁, P₂, hP₁, hL.separatesOff_of_both
          (hL.ne_of_isBelowOff (hd₁.isBelowOff hN hL.deletion) hcY hca) hs₂ hs₁⟩
      · rcases hd₁.reaches_or_reaches hN hL.deletion hd₂ hne with hord | hord
        · exact ⟨e₂, P₂, hP₁,
            hL.separatesOff_lower (hsub _ hP₁) (hsub' _) hc' hPa hs₂ hs₁ hord⟩
        · exact ⟨e₁, P₂, hP₁,
            hL.symm.separatesOff_lower (hsub _ hP₁) (hsub' _) hc' hPa hs₁ hs₂ hord⟩

end IsLowPair

/-! ### Below a lowest reticulation the network is a tree -/

/-- The taxa of `q` below the vertex `w`, off `D`. -/
def taxaBelowOff (N : RootedNetwork V E X) (D : Set E) (q : Finset X) (w : V) : Finset X :=
  q.filter fun x => N.ReachesOff D w (N.leaf x)

theorem mem_taxaBelowOff {q : Finset X} {w : V} {x : X} :
    x ∈ taxaBelowOff N D q w ↔ x ∈ q ∧ N.ReachesOff D w (N.leaf x) := by
  simp [taxaBelowOff]

/-- Below `v`, off `D`, every vertex ancestral to `q` has one parent. -/
def HasUniqueParentsBelow (N : RootedNetwork V E X) (D : Set E) (q : Finset X) (v : V) : Prop :=
  ∀ w, N.ReachesOff D v w → w ≠ v → (taxaBelowOff N D q w).Nonempty →
    ∀ f g, f ∉ D → g ∉ D → N.graph.target f = w → N.graph.target g = w → f = g

/-- Off `D`, an arc into the tree below `v` dominates the taxa of `q` below it: going up from such a
taxon, each vertex has only one parent. -/
theorem dominatesOff_of_uniqueParents (hN : N.IsPhylogenetic) {q : Finset X} {v : V}
    (hT : HasUniqueParentsBelow N D q v) {e : E} (he : e ∉ D)
    (hv : N.ReachesOff D v (N.graph.source e)) {x : X} (hx : x ∈ q)
    (hr : N.ReachesOff D (N.graph.target e) (N.leaf x)) : N.DominatesOff D e x := by
  have hne : ∀ w, N.ReachesOff D (N.graph.target e) w → w ≠ v := by
    rintro w hw rfl
    exact not_reaches_target_source hN.acyclic e (ReachesOff.reaches (hw.trans hv))
  have hv' : N.ReachesOff D v (N.graph.target e) := hv.tail_arc he
  have hnon : ∀ w, N.ReachesOff D w (N.leaf x) → (taxaBelowOff N D q w).Nonempty := fun w hw =>
    ⟨x, mem_taxaBelowOff.mpr ⟨hx, hw⟩⟩
  have hnotin : ∀ {g : E}, g ∉ insert e D → g ≠ e ∧ g ∉ D := fun hg =>
    ⟨fun h => hg (Set.mem_insert_iff.mpr (Or.inl h)), fun h => hg (Set.mem_insert_of_mem _ h)⟩
  have key : ∀ w, N.ReachesOff D (N.graph.target e) w → N.ReachesOff D w (N.leaf x) →
      ¬ N.ReachesOff (insert e D) N.root w := by
    intro w hw
    induction hw with
    | refl =>
      intro hl hav
      obtain ⟨f, hf, hft, -⟩ := hav.exists_last (target_ne_root_of_isPhylogenetic hN e).symm
      obtain ⟨hfe, hfD⟩ := hnotin hf
      exact hfe (hT _ hv' (hne _ .refl) (hnon _ hl) f e hfD he hft rfl)
    | @tail b c hb hbc ih =>
      obtain ⟨f, hf, rfl, rfl⟩ := hbc
      intro hl hav
      obtain ⟨g, hg, hgt, hp⟩ := hav.exists_last (target_ne_root_of_isPhylogenetic hN f).symm
      obtain ⟨-, hgD⟩ := hnotin hg
      have hbf : N.ReachesOff D (N.graph.target e) (N.graph.target f) := ReachesOff.tail_arc hb hf
      have hgf : g = f := hT _ (hv'.trans hbf) (hne _ hbf) (hnon _ hl) g f hgD hf hgt rfl
      subst hgf
      exact ih (ReachesOff.head_arc hf hl) hp
  exact key _ hr .refl

/-- `f` is an arm at the vertex `w` towards the taxon `x` of `q`, off `D`: it leaves `w` with exactly
`x` below it, or it enters `w` with exactly the other taxa of `q` below it. -/
def ArmOff (N : RootedNetwork V E X) (D : Set E) (q : Finset X) (w : V) (x : X) (f : E) : Prop :=
  f ∉ D ∧ ((N.graph.source f = w ∧ ∀ y ∈ q, N.IsBelowOff D f y ↔ y = x) ∨
    (N.graph.target f = w ∧ ∀ y ∈ q, N.IsBelowOff D f y ↔ y ≠ x))

/-- Off `D`, the vertex `w` has an arm towards each taxon of `q`: a multifurcation of degree at least
four. -/
def StarOff (N : RootedNetwork V E X) (D : Set E) (q : Finset X) (w : V) : Prop :=
  ∀ x ∈ q, ∃ f, ArmOff N D q w x f

variable [Fintype X] [DecidableEq X]

/-- **The tree below a vertex** (the source's "the subnetwork below `v` must be a tree"). Take two
or more taxa of `q` below `v`, with one parent at each vertex ancestral to `q` below `v`. The lowest
vertex `w` with at least two taxa of `q` below it has at most one below each child. If it has exactly
two, the arc entering `w` separates `2|2`, so `q` is treelike off `D`. Otherwise `w` is a
multifurcation. A binary tree has none, so this is the source's "a binary tree on 4 taxa has a
`2|2` arc", and its "this tree can only have one leaf". -/
theorem isTreelikeOff_or_starOff (hN : N.IsPhylogenetic) (hD : N.IsDeletion D) {q : Finset X}
    (hq : q.card = 4) {v : V} (hT : HasUniqueParentsBelow N D q v)
    (h2 : 2 ≤ (taxaBelowOff N D q v).card)
    (hv : (taxaBelowOff N D q v).card = 2 →
      ∀ f g, N.graph.source f = v → N.graph.source g = v → f = g) :
    N.IsTreelikeOff D q ∨ ∃ w, StarOff N D q w := by
  obtain ⟨w, ⟨hvw, hw2⟩, hlow⟩ :=
    exists_lowest hN (S := {w | N.ReachesOff D v w ∧ 2 ≤ (taxaBelowOff N D q w).card})
      ⟨v, .refl, h2⟩
  have hchild : ∀ f, f ∉ D → N.graph.source f = w → (taxaBelowOff N D q (N.graph.target f)).card ≤ 1 := by
    intro f hf hs
    by_contra hc
    have hvf : N.ReachesOff D v (N.graph.target f) := (hs ▸ hvw : N.ReachesOff D v _).tail_arc hf
    have hstep : N.graph.Reaches w (N.graph.target f) := .single ⟨f, hs, rfl⟩
    have heq := hlow _ ⟨hvf, by omega⟩ hstep
    exact hN.acyclic w (.single ⟨f, hs, heq⟩)
  have hfirst : ∀ x ∈ taxaBelowOff N D q w,
      ∃ f, f ∉ D ∧ N.graph.source f = w ∧ N.ReachesOff D (N.graph.target f) (N.leaf x) := by
    intro x hx
    obtain ⟨y, hy, hyx⟩ := Finset.exists_mem_ne (by omega : 1 < (taxaBelowOff N D q w).card) x
    refine (mem_taxaBelowOff.mp hx).2.exists_first ?_
    intro hwx
    have hy' := (mem_taxaBelowOff.mp hy).2
    rw [hwx] at hy'
    exact hyx (eq_of_leaf_reachesOff_leaf hN hy')
  rcases (by omega : (taxaBelowOff N D q w).card = 2 ∨ 3 ≤ (taxaBelowOff N D q w).card) with h | h
  · left
    have hwv : v ≠ w := by
      rintro rfl
      obtain ⟨x, y, hxy, hxy'⟩ := Finset.card_eq_two.mp h
      obtain ⟨f, hf, hfs, hfx⟩ := hfirst x (by simp [hxy'])
      obtain ⟨g, hg, hgs, hgy⟩ := hfirst y (by simp [hxy'])
      have hfg := hv h f g hfs hgs
      subst hfg
      have hle := hchild f hf hfs
      have hxm : x ∈ taxaBelowOff N D q (N.graph.target f) :=
        mem_taxaBelowOff.mpr ⟨(mem_taxaBelowOff.mp (by simp [hxy'] : x ∈ taxaBelowOff N D q v)).1, hfx⟩
      have hym : y ∈ taxaBelowOff N D q (N.graph.target f) :=
        mem_taxaBelowOff.mpr ⟨(mem_taxaBelowOff.mp (by simp [hxy'] : y ∈ taxaBelowOff N D q v)).1, hgy⟩
      exact hxy (Finset.card_le_one.mp hle x hxm y hym)
    obtain ⟨e, he, het, hes⟩ := hvw.exists_last hwv
    obtain ⟨s, hst, hsv⟩ := TreeMetric.exists_quartetTree_of_subset (B := taxaBelowOff N D q w) hq
      (Finset.filter_subset _ _) h
    refine ⟨s, mem_treesOn.mpr hst, e, taxaBelowOff N D q w, by simp [hsv], ?_, ?_⟩
    · intro x hx
      have hx' := mem_taxaBelowOff.mp (Finset.mem_coe.mp hx)
      exact dominatesOff_of_uniqueParents hN hT he hes hx'.1 (het ▸ hx'.2)
    · intro x hx hb
      rw [hst, Finset.mem_coe, Finset.mem_sdiff] at hx
      exact hx.2 (mem_taxaBelowOff.mpr ⟨hx.1, het ▸ hb.2⟩)
  · right
    refine ⟨w, fun x hx => ?_⟩
    by_cases hxw : x ∈ taxaBelowOff N D q w
    · obtain ⟨f, hf, hfs, hfx⟩ := hfirst x hxw
      refine ⟨f, hf, Or.inl ⟨hfs, fun y hy => ⟨?_, ?_⟩⟩⟩
      · rintro ⟨-, hr⟩
        exact Finset.card_le_one.mp (hchild f hf hfs) y (mem_taxaBelowOff.mpr ⟨hy, hr⟩) x
          (mem_taxaBelowOff.mpr ⟨hx, hfx⟩)
      · rintro rfl
        exact ⟨hf, hfx⟩
    · have hwr : w ≠ N.root := by
        rintro rfl
        exact hxw (mem_taxaBelowOff.mpr ⟨hx, hD.root_reachesOff hN _⟩)
      obtain ⟨e, he, het⟩ := hD.parent w hwr
      have hsub : taxaBelowOff N D q w ⊆ q.erase x := fun y hy =>
        Finset.mem_erase.mpr ⟨fun hyx => hxw (hyx ▸ hy), (mem_taxaBelowOff.mp hy).1⟩
      have heq : taxaBelowOff N D q w = q.erase x :=
        Finset.eq_of_subset_of_card_le hsub (by rw [Finset.card_erase_of_mem hx]; omega)
      refine ⟨e, he, Or.inr ⟨het, fun y hy => ⟨?_, ?_⟩⟩⟩
      · rintro ⟨-, hr⟩ rfl
        exact hxw (mem_taxaBelowOff.mpr ⟨hx, het ▸ hr⟩)
      · intro hyx
        have hm : y ∈ taxaBelowOff N D q w := by
          rw [heq]
          exact Finset.mem_erase.mpr ⟨hyx, hy⟩
        exact ⟨he, het ▸ (mem_taxaBelowOff.mp hm).2⟩

/-- Domination language for `IsTreelike`, `hasCutSplitOn_iff_separates`: step 1 of the proof. -/
theorem isTreelikeOff_empty_iff (hN : N.IsPhylogenetic) {q : Finset X} :
    N.IsTreelikeOff ∅ q ↔ IsTreelike N q := by
  have hsep : ∀ {e : E} {P Q : Set X}, N.SeparatesOff ∅ e P Q ↔ N.Separates e P Q := by
    intro e P Q
    simp only [SeparatesOff, Separates, dominatesOff_empty_iff, isBelowOff_empty_iff]
  have hinter : ∀ (s : QuartetTree X) (P : Finset X), P ∈ s.val →
      (s.taxa : Set X) ∩ P = P := fun s P hP =>
    Set.inter_eq_right.mpr (Finset.coe_subset.mpr (s.subset_taxa hP))
  have hdiff : ∀ (s : QuartetTree X) (P : Finset X),
      (s.taxa : Set X) \ P = ((s.taxa \ P : Finset X) : Set X) := fun s P => by simp
  constructor
  · rintro ⟨s, hs, e, P, hP, hsp⟩
    refine ⟨s, hs, P, hP, (hasCutSplitOn_iff_separates hN _ _).mpr ⟨e, Or.inl ?_⟩⟩
    rw [hinter s P hP, hdiff]
    exact ⟨Finset.card_pos.mp (by rw [s.card_of_mem hP]; norm_num), hsep.mp hsp⟩
  · rintro ⟨s, hs, P, hP, hcut⟩
    obtain ⟨e, ⟨-, hsp⟩ | ⟨-, hsp⟩⟩ := (hasCutSplitOn_iff_separates hN _ _).mp hcut
    · rw [hinter s P hP, hdiff] at hsp
      exact ⟨s, hs, e, P, hP, hsep.mpr hsp⟩
    · rw [hinter s P hP, hdiff] at hsp
      refine ⟨s, hs, e, s.taxa \ P, s.sdiff_mem hP, ?_⟩
      rw [Finset.sdiff_sdiff_eq_self (s.subset_taxa hP)]
      exact hsep.mpr hsp

/-! ### The reduction -/

/-- **The reduction**, under the two uses of the degrees: a reticulation has two parents and one
child (`hRet`), and no multifurcation arises off a deletion (`hStar`). By induction on `D`, as in the
source: take a lowest reticulation ancestral to `q`, and delete a parent while `q` stays non-treelike.

Departure from the paper: the source first sets the lengths of the arcs of 2-blobs to zero, and repeats
this after each deletion, so that the lowest reticulation is in the 4-blob and the only non-leaf blob is
the 4-blob. Domination sees through 2-blobs, so this step is not needed: a reticulation in a 2-blob
is deleted like any other (the 4-set stays non-treelike), and steps 4 and 5 use only domination. The
recursion runs on the set `D`, which grows at each deletion, rather than on the number of
reticulations; the deletions are the source's. -/
theorem exists_reduction_aux (hN : N.IsPhylogenetic)
    (hRet : ∀ v, 2 ≤ N.graph.indegree v → N.graph.indegree v = 2 ∧ N.graph.outdegree v = 1)
    {q : Finset X} (hq : q.card = 4)
    (hStar : ∀ (D : Set E) (w : V), N.IsDeletion D → ¬ StarOff N D q w) (D : Set E) :
    N.IsDeletion D → ¬ N.IsTreelikeOff D q →
    ∃ (D : Set E) (k₁ k₂ : E) (a : X) (s₁ s₂ : QuartetTree X) (e₁ e₂ : E),
      N.IsDeletion D ∧ k₁ ≠ k₂ ∧ N.graph.target k₁ = N.graph.target k₂ ∧ k₁ ∉ D ∧ k₂ ∉ D ∧
      (∀ f, N.graph.target f = N.graph.target k₁ → f ∉ D → f = k₁ ∨ f = k₂) ∧
      a ∈ q ∧ N.ReachesOff D (N.graph.target k₁) (N.leaf a) ∧
      (∀ x ∈ q, x ≠ a → ¬ N.ReachesOff D (N.graph.target k₁) (N.leaf x)) ∧
      s₁ ∈ treesOn q ∧ s₂ ∈ treesOn q ∧ s₁ ≠ s₂ ∧
      N.SplitOffAt (insert k₂ D) e₁ s₁ ∧ N.SplitOffAt (insert k₁ D) e₂ s₂ := by
  have : Finite E := hN.finite_arcs
  induction D using WellFoundedGT.induction with
  | _ D ih =>
    intro hD hnt
    have hroot : taxaBelowOff N D q N.root = q :=
      Finset.filter_true_of_mem fun x _ => hD.root_reachesOff hN (N.leaf x)
    by_cases hex : ∃ w, (taxaBelowOff N D q w).Nonempty ∧ ∃ k₁ k₂, k₁ ≠ k₂ ∧ k₁ ∉ D ∧ k₂ ∉ D ∧
        N.graph.target k₁ = w ∧ N.graph.target k₂ = w
    · -- Step 3: a lowest reticulation.
      obtain ⟨h, ⟨hhT, k₁, k₂, hk, hk₁, hk₂, ht₁, ht₂⟩, hlow⟩ := exists_lowest hN (S := {w |
        (taxaBelowOff N D q w).Nonempty ∧ ∃ k₁ k₂, k₁ ≠ k₂ ∧ k₁ ∉ D ∧ k₂ ∉ D ∧
          N.graph.target k₁ = w ∧ N.graph.target k₂ = w}) hex
      have ht : N.graph.target k₁ = N.graph.target k₂ := ht₁.trans ht₂.symm
      by_cases h₁ : N.IsTreelikeOff (insert k₁ D) q
      · by_cases h₂ : N.IsTreelikeOff (insert k₂ D) q
        · -- Step 4: exactly one taxon of `q` is below `h`.
          have hdeg := hRet h (by
            have hfin : {e | N.graph.target e = h}.Finite := Set.toFinite _
            exact (Set.one_lt_ncard_iff hfin).mpr ⟨k₁, k₂, ht₁, ht₂, hk⟩)
          have hcard : (taxaBelowOff N D q h).card ≤ 1 := by
            by_contra hc
            have hT : HasUniqueParentsBelow N D q h := by
              intro w hw hwh hnon f g hf hg hfw hgw
              by_contra hfg
              exact hwh (hlow w ⟨hnon, f, g, hfg, hf, hg, hfw, hgw⟩ hw.reaches)
            have hv : (taxaBelowOff N D q h).card = 2 →
                ∀ f g, N.graph.source f = h → N.graph.source g = h → f = g := by
              intro _ f g hf hg
              obtain ⟨e, he⟩ := (N.graph.outdegree_eq_one_iff h).mp hdeg.2
              rw [(he f).mp hf, (he g).mp hg]
            rcases isTreelikeOff_or_starOff hN hD hq hT (by omega) hv with hl | ⟨w, hw⟩
            · exact hnt hl
            · exact hStar D w hD hw
          obtain ⟨a, ha⟩ := Finset.card_eq_one.mp
            (le_antisymm hcard (Finset.card_pos.mpr hhT))
          have hamem : a ∈ taxaBelowOff N D q h := by simp [ha]
          have hnot : ∀ x ∈ q, x ≠ a → ¬ N.ReachesOff D h (N.leaf x) := fun x hx hxa hr => by
            have hm : x ∈ taxaBelowOff N D q h := mem_taxaBelowOff.mpr ⟨hx, hr⟩
            rw [ha, Finset.mem_singleton] at hm
            exact hxa hm
          obtain ⟨s₂, hs₂, e₂, hs₂'⟩ := h₁
          obtain ⟨s₁, hs₁, e₁, hs₁'⟩ := h₂
          refine ⟨D, k₁, k₂, a, s₁, s₂, e₁, e₂, hD, hk, ht, hk₁, hk₂, ?_,
            (mem_taxaBelowOff.mp hamem).1, ht₁ ▸ (mem_taxaBelowOff.mp hamem).2,
            fun x hx hxa => ht₁ ▸ hnot x hx hxa, hs₁, hs₂, ?_, hs₁', hs₂'⟩
          · -- `h` has only the parents `k₁`, `k₂`.
            intro f hf _
            by_contra hne
            push Not at hne
            have hgt : 2 < N.graph.indegree h :=
              (Set.two_lt_ncard_iff (Set.toFinite _)).mpr
                ⟨k₁, k₂, f, ht₁, ht₂, hf.trans ht₁, hk, hne.1.symm, hne.2.symm⟩
            omega
          · -- Step 5: the two splits differ.
            rintro rfl
            have hta : s₁.taxa = q := mem_treesOn.mp hs₁
            have hL : IsLowPair N D k₁ k₂ a (s₁.taxa : Set X) :=
              { phylogenetic := hN
                deletion := hD
                ne := hk
                target_eq := ht
                notMem₁ := hk₁
                notMem₂ := hk₂
                not_reaches := fun x hx hxa => ht₁ ▸ hnot x (hta ▸ Finset.mem_coe.mp hx) hxa }
            obtain ⟨e, he⟩ := hL.exists_splitOffAt (hta ▸ (mem_taxaBelowOff.mp hamem).1) hs₁' hs₂'
            exact hnt ⟨s₁, hs₁, e, he⟩
        · exact ih (insert k₂ D) (Set.ssubset_insert hk₂)
            (hD.insert hN hk.symm ht.symm hk₁) h₂
      · exact ih (insert k₁ D) (Set.ssubset_insert hk₁) (hD.insert hN hk ht hk₂) h₁
    · -- Step 2: no reticulation, so the ancestors of `q` form a tree.
      exfalso
      have hT : HasUniqueParentsBelow N D q N.root := by
        intro w _ _ hnon f g hf hg hfw hgw
        by_contra hfg
        exact hex ⟨w, hnon, f, g, hfg, hf, hg, hfw, hgw⟩
      rcases isTreelikeOff_or_starOff hN hD hq hT (by rw [hroot]; omega)
        (by rw [hroot]; omega) with hl | ⟨w, hw⟩
      · exact hnt hl
      · exact hStar D w hD hw

omit [Fintype X] in
/-- A vertex with an arm towards each of four taxa has degree at least four. -/
theorem StarOff.four_le_degree (hN : N.IsPhylogenetic) {q : Finset X} (hq : q.card = 4) {w : V}
    (h : StarOff N D q w) : 4 ≤ N.graph.indegree w + N.graph.outdegree w := by
  have : Finite E := hN.finite_arcs
  obtain ⟨x₀, hx₀⟩ := Finset.card_pos.mp (by omega : 0 < q.card)
  have : Nonempty E := (h x₀ hx₀).elim fun f _ => ⟨f⟩
  choose! f hf using h
  have hinj : Set.InjOn f q := by
    intro x hx y hy hxy
    by_contra hne
    have hx : x ∈ q := Finset.mem_coe.mp hx
    have hy : y ∈ q := Finset.mem_coe.mp hy
    obtain ⟨u, hu, huxy⟩ := Finset.exists_mem_notMem_of_card_lt_card
      (s := {x, y}) (t := q) (by
        rw [hq]
        exact lt_of_le_of_lt Finset.card_le_two (by norm_num))
    have hux : u ≠ x := fun h => huxy (by simp [h])
    have huy : u ≠ y := fun h => huxy (by simp [h])
    obtain ⟨-, hx'⟩ := hf x hx
    obtain ⟨-, hy'⟩ := hf y hy
    rw [hxy] at hx'
    rcases hx' with ⟨-, hx'⟩ | ⟨-, hx'⟩ <;> rcases hy' with ⟨-, hy'⟩ | ⟨-, hy'⟩
    · exact hne ((hy' x hx).mp ((hx' x hx).mpr rfl))
    · exact hux ((hx' u hu).mp ((hy' u hu).mpr huy))
    · exact huy ((hy' u hu).mp ((hx' u hu).mpr hux))
    · exact (hx' x hx).mp ((hy' x hx).mpr hne) rfl
  have hcard : (f '' (q : Set X)).ncard = 4 := by
    rw [hinj.ncard_image, Set.ncard_coe_finset, hq]
  have hsub : f '' (q : Set X) ⊆ {e | N.graph.target e = w} ∪ {e | N.graph.source e = w} := by
    rintro _ ⟨x, hx, rfl⟩
    rcases (hf x hx).2 with ⟨hs, -⟩ | ⟨ht, -⟩
    · exact Or.inr hs
    · exact Or.inl ht
  calc 4 = (f '' (q : Set X)).ncard := hcard.symm
    _ ≤ ({e | N.graph.target e = w} ∪ {e | N.graph.source e = w}).ncard :=
        Set.ncard_le_ncard hsub (Set.toFinite _)
    _ ≤ _ := Set.ncard_union_le _ _

/-- **The graph side of part (b) of Theorem 1 of Allman et al. 2023**
(`notes/sources/allman2023.txt`, lines 145-149). For a binary network and a 4-set `q` that is not
treelike, there are a deletion `D` of hybrid arcs and a reticulation with exactly two parents `k₁`, `k₂`
off `D` and exactly one taxon `a` of `q` below it, such that deleting `k₂` gives a cut arc `e₁` of a
quartet tree `s₁` on `q`, deleting `k₁` gives a cut arc `e₂` of a quartet tree `s₂` on `q`, and
`s₁ ≠ s₂`. See `exists_reduction_aux` for the proof and the departures from the source. -/
theorem exists_reduction (hN : N.IsPhylogenetic) (hBin : N.IsBinary) {q : Finset X} (hq : q.card = 4)
    (hnt : ¬ IsTreelike N q) :
    ∃ (D : Set E) (k₁ k₂ : E) (a : X) (s₁ s₂ : QuartetTree X) (e₁ e₂ : E),
      N.IsDeletion D ∧ k₁ ≠ k₂ ∧ N.graph.target k₁ = N.graph.target k₂ ∧ k₁ ∉ D ∧ k₂ ∉ D ∧
      (∀ f, N.graph.target f = N.graph.target k₁ → f ∉ D → f = k₁ ∨ f = k₂) ∧
      a ∈ q ∧ N.ReachesOff D (N.graph.target k₁) (N.leaf a) ∧
      (∀ x ∈ q, x ≠ a → ¬ N.ReachesOff D (N.graph.target k₁) (N.leaf x)) ∧
      s₁ ∈ treesOn q ∧ s₂ ∈ treesOn q ∧ s₁ ≠ s₂ ∧
      N.SplitOffAt (insert k₂ D) e₁ s₁ ∧ N.SplitOffAt (insert k₁ D) e₂ s₂ :=
  exists_reduction_aux hN
    (fun v h2 => indegree_eq_two_of_degree_le_three hN h2 (degree_le_three_of_isBinary hN hBin v)) hq
    (fun _ w _ hw => by
      have h₁ := hw.four_le_degree hN hq
      have h₂ := degree_le_three_of_isBinary hN hBin w
      omega)
    ∅ (isDeletion_empty hN) fun h => hnt ((isTreelikeOff_empty_iff hN).mp h)

/-! ### The non-binary variant, for ECToBlob's adaptation -/

omit [Fintype X] [DecidableEq X] in
/-- Under the degree condition of ECToBlob's Proposition 5.1, a reticulation has degree at most
three, since it lies in a non-trivial blob. -/
theorem degree_le_three_of_two_le_indegree (hN : N.IsPhylogenetic)
    (hdeg : ∀ v w : V, v ≠ w → TOBQMC.SameBlob N v w →
      N.graph.indegree v + N.graph.outdegree v ≤ 3) {v : V} (h2 : 2 ≤ N.graph.indegree v) :
    N.graph.indegree v + N.graph.outdegree v ≤ 3 := by
  have : Finite E := hN.finite_arcs
  obtain ⟨f, g, hf, hg, hne⟩ := (Set.one_lt_ncard_iff (Set.toFinite _)).mp h2
  have hf' : N.graph.target f = v := hf
  have hg' : N.graph.target g = v := hg
  refine hdeg v (N.graph.source f) ?_ (.single ⟨f, not_isBridge_of_two_parents hN hne
    (hf'.trans hg'.symm), Or.inr ⟨rfl, hf'⟩⟩)
  rintro rfl
  exact hN.acyclic _ (.single ⟨f, rfl, hf'⟩)

omit [Fintype X] in
/-- Under the degree condition of ECToBlob's Proposition 5.1, a multifurcation off a deletion is a
trivial 4-blob of the network itself: its vertex has degree at least four, so it lies in no non-trivial
blob, so its arcs are bridges, and a bridge has the same taxa on each side as off `D`. -/
theorem hasTrivialFourBlob_of_starOff (hN : N.IsPhylogenetic)
    (hdeg : ∀ v w : V, v ≠ w → TOBQMC.SameBlob N v w →
      N.graph.indegree v + N.graph.outdegree v ≤ 3) (hD : N.IsDeletion D) {q : Finset X}
    (hq : q.card = 4) {w : V} (hw : StarOff N D q w) : HasTrivialFourBlob N q := by
  have h4 := hw.four_le_degree hN hq
  have hA := hN.acyclic
  refine ⟨w, fun x hx => ?_⟩
  obtain ⟨f, hf, harm⟩ := hw x hx
  have hbr : TOBQMC.IsBridge N f := by
    by_contra hnb
    rcases harm with ⟨hs, -⟩ | ⟨ht, -⟩
    · have hne : w ≠ N.graph.target f := by
        rintro rfl
        exact hA _ (.single ⟨f, hs, rfl⟩)
      have := hdeg w _ hne (.single ⟨f, hnb, Or.inl ⟨hs, rfl⟩⟩)
      omega
    · have hne : w ≠ N.graph.source f := by
        rintro rfl
        exact hA _ (.single ⟨f, rfl, ht⟩)
      have := hdeg w _ hne (.single ⟨f, hnb, Or.inr ⟨rfl, ht⟩⟩)
      omega
  obtain ⟨S₀, hS₀⟩ := hbr
  obtain ⟨S, hS, hwS⟩ : ∃ S : Set V, (∀ g, N.graph.Crosses g S ↔ g = f) ∧ w ∉ S := by
    by_cases hw0 : w ∈ S₀
    · exact ⟨S₀ᶜ, fun g => (N.graph.crosses_compl g S₀).trans (hS₀ g), by simpa using hw0⟩
    · exact ⟨S₀, hS₀, hw0⟩
  have hc := (hS f).mpr rfl
  -- A taxon not below `f` is on the side of the source of `f`, one below it on the side of the target.
  have hrs : N.ReachesOff (insert f D) N.root (N.graph.source f) :=
    (hD.root_reachesOff hN _).insert_of_not_reaches fun h =>
      not_reaches_target_source hA f (ReachesOff.reaches h)
  have hnb : ∀ y, ¬ N.IsBelowOff D f y → (N.leaf y ∈ S ↔ N.graph.source f ∈ S) := by
    intro y hy
    rcases (hD.root_reachesOff hN (N.leaf y)).split f with hl | ⟨-, he, hr⟩
    · exact (mem_iff_mem_of_reachesOff_insert hS hl).symm.trans
        (mem_iff_mem_of_reachesOff_insert hS hrs)
    · exact absurd ⟨he, hr⟩ hy
  have hbl : ∀ y, N.IsBelowOff D f y → (N.leaf y ∈ S ↔ N.graph.target f ∈ S) := fun y hy =>
    (mem_iff_mem_of_reachesOff_insert hS
      (ReachesOff.insert_of_target_reaches hA .refl hy.2)).symm
  rcases harm with ⟨hs, harm⟩ | ⟨ht, harm⟩
  · have htS : N.graph.target f ∈ S := by
      rcases hc with ⟨h, -⟩ | ⟨h, -⟩
      · exact absurd (hs ▸ h) hwS
      · exact h
    refine ⟨f, ⟨x, hx, ((harm x hx).mpr rfl).2.reaches⟩, S, fun g _ => hS g, fun y hy => ⟨?_, ?_⟩,
      hwS, Or.inl hs⟩
    · intro hyS
      by_contra hyx
      exact hwS (hs ▸ (hnb y fun h => hyx ((harm y hy).mp h)).mp hyS)
    · rintro rfl
      exact (hbl y ((harm y hy).mpr rfl)).mpr htS
  · have hsS : N.graph.source f ∈ S := by
      rcases hc with ⟨h, -⟩ | ⟨h, -⟩
      · exact h
      · exact absurd (ht ▸ h) hwS
    obtain ⟨y₀, hy₀, hy₀x⟩ := Finset.exists_mem_ne (by omega : 1 < q.card) x
    refine ⟨f, ⟨y₀, hy₀, ((harm y₀ hy₀).mpr hy₀x).2.reaches⟩, S, fun g _ => hS g,
      fun y hy => ⟨?_, ?_⟩, hwS, Or.inr ht⟩
    · intro hyS
      by_contra hyx
      exact hwS (ht ▸ (hbl y ((harm y hy).mpr hyx)).mp hyS)
    · rintro rfl
      exact (hnb y fun h => (harm y hy).mp h rfl).mpr hsS

omit [Fintype X] in
/-- A cut arc off a deletion can be moved down to a tree arc of the network, with the same split: a
hybrid arc of the network enters a reticulation, whose one child arc dominates the same taxa. -/
theorem exists_isTreeArc_of_splitOffAt (hN : N.IsPhylogenetic) (hD : N.IsDeletion D)
    (hRet : ∀ v, 2 ≤ N.graph.indegree v → N.graph.indegree v = 2 ∧ N.graph.outdegree v = 1)
    {e : E} {s : QuartetTree X} (h : N.SplitOffAt D e s) :
    ∃ e', N.IsTreeArc e' ∧ N.SplitOffAt D e' s := by
  have : Finite E := hN.finite_arcs
  suffices H : ∀ (v : V) (e : E), N.graph.target e = v → N.SplitOffAt D e s →
      ∃ e', N.IsTreeArc e' ∧ N.SplitOffAt D e' s from H _ e rfl h
  intro v
  induction v using (wellFounded_transGen_adj_flip hN).induction with
  | _ v ih =>
    intro e hev hsplit
    by_cases htree : N.IsTreeArc e
    · exact ⟨e, htree, hsplit⟩
    have h2 : 2 ≤ N.graph.indegree (N.graph.target e) := by
      have h1 := (N.graph.one_le_indegree_iff (N.graph.target e)).mpr ⟨e, rfl⟩
      have h3 : N.graph.indegree (N.graph.target e) ≠ 1 := htree
      omega
    obtain ⟨e', he'⟩ := (N.graph.outdegree_eq_one_iff _).mp (hRet _ h2).2
    have hes : N.graph.source e' = N.graph.target e := (he' e').mpr rfl
    have hleaf : ∀ y, N.graph.target e ≠ N.leaf y := fun y hy => by
      have := hN.leaf_indegree y
      rw [← hy] at this
      omega
    obtain ⟨P, hP, hsep⟩ := hsplit
    obtain ⟨x, hx⟩ := Finset.card_pos.mp (by rw [s.card_of_mem hP]; norm_num : 0 < P.card)
    have hbx := (hsep.1 x (Finset.mem_coe.mpr hx)).isBelowOff hN hD
    obtain ⟨g, hg, hgs, -⟩ := hbx.2.exists_first (hleaf x)
    have he'D : e' ∉ D := (he' g).mp hgs ▸ hg
    refine ih (N.graph.target e') (hev ▸ .single ⟨e', hes, rfl⟩) e' rfl ⟨P, hP, ?_, ?_⟩
    · intro y hy hav
      rcases hav.split e with hl | ⟨-, -, hr⟩
      · refine hsep.1 y hy (hl.mono ?_)
        exact Set.insert_subset_insert (Set.subset_insert _ _)
      · obtain ⟨g', hg', hg's, -⟩ := hr.exists_first (hleaf y)
        exact hg' (Set.mem_insert_iff.mpr (Or.inl ((he' g').mp hg's)))
    · rintro y hy ⟨-, hr⟩
      exact hsep.2 y hy ⟨hbx.1, hes ▸ ReachesOff.head_arc he'D hr⟩

/-- **The reduction for ECToBlob's adaptation of Theorem 1 of Allman et al. 2023**
(`ECToBlob.adaptedAllmanTheorem1`). For a network whose vertices in non-trivial blobs have degree at
most three (`hdeg`, which is `ECToBlob.BlobDegreeAtMostThree N`) and a 4-set `q` that is neither
treelike nor a trivial 4-blob, the conclusion of `exists_reduction` holds, with cut arcs `e₁`, `e₂` that
are tree arcs of the network, so that their lengths are free positive parameters on every face of
ECToBlob's measure. -/
theorem exists_reduction_of_blobDegree (hN : N.IsPhylogenetic)
    (hdeg : ∀ v w : V, v ≠ w → TOBQMC.SameBlob N v w →
      N.graph.indegree v + N.graph.outdegree v ≤ 3) {q : Finset X} (hq : q.card = 4)
    (hnt : ¬ IsTreelike N q) (htr : ¬ HasTrivialFourBlob N q) :
    ∃ (D : Set E) (k₁ k₂ : E) (a : X) (s₁ s₂ : QuartetTree X) (e₁ e₂ : E),
      N.IsDeletion D ∧ k₁ ≠ k₂ ∧ N.graph.target k₁ = N.graph.target k₂ ∧ k₁ ∉ D ∧ k₂ ∉ D ∧
      (∀ f, N.graph.target f = N.graph.target k₁ → f ∉ D → f = k₁ ∨ f = k₂) ∧
      a ∈ q ∧ N.ReachesOff D (N.graph.target k₁) (N.leaf a) ∧
      (∀ x ∈ q, x ≠ a → ¬ N.ReachesOff D (N.graph.target k₁) (N.leaf x)) ∧
      s₁ ∈ treesOn q ∧ s₂ ∈ treesOn q ∧ s₁ ≠ s₂ ∧
      N.SplitOffAt (insert k₂ D) e₁ s₁ ∧ N.SplitOffAt (insert k₁ D) e₂ s₂ ∧
      N.IsTreeArc e₁ ∧ N.IsTreeArc e₂ := by
  have hRet : ∀ v, 2 ≤ N.graph.indegree v →
      N.graph.indegree v = 2 ∧ N.graph.outdegree v = 1 := fun v h2 =>
    indegree_eq_two_of_degree_le_three hN h2 (degree_le_three_of_two_le_indegree hN hdeg h2)
  obtain ⟨D, k₁, k₂, a, s₁, s₂, e₁, e₂, hD, hk, ht, hk₁, hk₂, hpar, ha, hra, hnot, hs₁, hs₂, hss,
      hsp₁, hsp₂⟩ := exists_reduction_aux hN hRet hq
    (fun D w hD hw => htr (hasTrivialFourBlob_of_starOff hN hdeg hD hq hw))
    ∅ (isDeletion_empty hN) fun h => hnt ((isTreelikeOff_empty_iff hN).mp h)
  obtain ⟨e₁', he₁', hsp₁'⟩ := exists_isTreeArc_of_splitOffAt hN
    (hD.insert hN hk.symm ht.symm hk₁) hRet hsp₁
  obtain ⟨e₂', he₂', hsp₂'⟩ := exists_isTreeArc_of_splitOffAt hN
    (hD.insert hN hk ht hk₂) hRet hsp₂
  exact ⟨D, k₁, k₂, a, s₁, s₂, e₁', e₂', hD, hk, ht, hk₁, hk₂, hpar, ha, hra, hnot, hs₁, hs₂, hss,
    hsp₁', hsp₂', he₁', he₂'⟩

end External.AllmanEtAl2023
