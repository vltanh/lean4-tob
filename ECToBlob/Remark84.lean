module

public import ECToBlob.Section8

/-!
# ECToBlob Remark 8.4: an input tree that is not a resolution of the tree of blobs

Remark 8.4 of the paper (`notes/paper2026/paper.txt`, lines 1183-1187): "If ECToBlob is given an
input tree `T0` that is not a resolution of the tree of blobs, the argument above indicates it would
still contract any edges of `T0` that do not define cut-edge splits in the true network. That is,
asymptotically it should return a 'coarsened' version of the tree of blobs, so that the cut edges in
its output still represent cut edges of the network, although the network's cut edges absent from
`T0` remain absent."

So the output should be `T₀ ∩ T_B(N)`, for an arbitrary unrooted tree `T₀`. This file proves:

* for a binary network the Remark holds, by the argument of the proof of Theorem 8.2
  (`remark8_4`, `remark8_4_generic`, and `remark8_4_of_noTrivial` for a network with no trivial
  4-blob on four taxa);
* for a non-binary network the Remark is false (`Counterexample.not_remark8_4`): on the tree
  `((0,1),2,3,4)` with a polytomy, and the binary `T₀` with cherries `02` and `34`, the false edge
  `34|012` has all its quartets under the T1 null, one of them not uniform, so neither the star test
  nor the T1 test contracts it;
* for every network and every `T₀`, what the algorithm tends to is `limitTree N T₀`
  (`tendsto_ectoblob_limitTree`), for all quartet types, corrections and selection rules. It
  contains the cut edges of `T₀` (`inter_treeOfBlobs_subset_limitTree`), so these do remain; all its
  edges are compatible with the tree of blobs (`limitTree_compatible`); and a false edge in it needs a
  cut edge missing from `T₀`, inside one of its sides (`exists_missed_cut_of_mem_limitTree`). When the
  limit tree is `T₀ ∩ T_B(N)` is `limitTree_eq_inter_iff`, with the sufficient conditions
  `limitTree_eq_inter_of_noTrivial`, `limitTree_eq_inter_of_blocks` and `limitTree_eq_treeOfBlobs`.

What makes the limit independent of the quartet type and of the stage is the quartet rule for the T1
null (`NullOn.rule`): if `pr|ab` and `qr|ab` are each a cut split or a trivial 4-blob, then so is
`pq|ab`. Hence, at an edge of a tree, the T1 null on the quartets of the multipartition gives the T1
null on all the quartets of the bipartition (`forall_bipartition_of_forall_multipartition`).

The end of the proof of Theorem 8.2 is restated for any target tree, any edge p-values and any overall
p-values: `IsLimit`, `IsLimit.outputBy_eq`. `ECToBlob/Remarks.lean` uses it for the variants of §10.

API: `limitTree`, `CoarseRun`, `IsLimit`, `outputBy`, `edgeTestP`, `treeTestP`, `NullOn`,
`IsNullQuartet`.
-/

@[expose] public noncomputable section

open Phylogenetics Phylogenetics.RootedNetwork Finset Filter Topology
open scoped Classical

namespace ECToBlob.Coarsening

open ECToBlob.FalseEdge ECToBlob.Deterministic

variable {V E X : Type*} {N : RootedNetwork V E X}

/-! ### Part 1: the T1 null on a network

#### Hubs and trivial 4-blobs -/

/-- The bridge entering a hub dominates the hub. -/
theorem not_avoidingReach_of_enters (hN : N.IsPhylogenetic) {q : Finset X} {v : V} {x y : X} {e : E}
    (he : Enters N q v x e) (hy : y ∈ q) (hyx : y ≠ x) : ¬ N.AvoidingReach e N.root v := fun h => by
  refine he.2.1 y hy hyx (h.trans ?_)
  rw [← he.1]
  exact avoidingReach_of_target_reaches hN.acyclic .refl (isBelow_of_dominates hN (he.2.1 y hy hyx))

/-- The converse of `FalseEdge.exists_isHub`: a hub gives a trivial 4-blob. -/
theorem hasTrivialFourBlob_of_isHub (hN : N.IsPhylogenetic) {q : Finset X} (hq : 1 < q.card) {v : V}
    (hv : IsHub N q v) : HasTrivialFourBlob N q := by
  refine ⟨v, fun x hx => ?_⟩
  obtain ⟨e, he | he⟩ := hv x hx
  · -- the bridge leaves `v`
    have hY : ∀ y ∈ (q : Set X), N.Dominates e y ∨ ¬ N.IsBelow e y := fun y hy => by
      by_cases hyx : y = x
      · exact Or.inl (hyx ▸ he.2.1)
      · exact Or.inr (he.2.2 y hy hyx)
    obtain ⟨hanc, hc⟩ := crosses_domSet_iff hN (Y := (q : Set X)) (by simpa using hx) he.2.1 hY
    refine ⟨e, hanc, N.domSet e, hc, fun y hy => ⟨fun h => ?_, ?_⟩, ?_, Or.inl he.1⟩
    · by_contra hyx
      exact he.2.2 y hy hyx (isBelow_of_dominates hN h)
    · rintro rfl
      exact he.2.1
    · intro hmem
      exact hmem (he.1 ▸ avoidingReach_of_reaches_source hN.acyclic (hN.root_reaches _) .refl)
  · -- the bridge enters `v`
    obtain ⟨y₀, hy₀, hy₀x⟩ := Finset.exists_mem_ne hq x
    have hY : ∀ y ∈ (q : Set X), N.Dominates e y ∨ ¬ N.IsBelow e y := fun y hy => by
      by_cases hyx : y = x
      · exact Or.inr (hyx ▸ he.2.2)
      · exact Or.inl (he.2.1 y hy hyx)
    obtain ⟨hanc, hc⟩ := crosses_domSet_iff hN (Y := (q : Set X)) (by simpa using hy₀)
      (he.2.1 y₀ hy₀ hy₀x) hY
    refine ⟨e, hanc, (N.domSet e)ᶜ, fun f hf => (N.graph.crosses_compl f _).trans (hc f hf),
      fun y hy => ⟨fun h => ?_, ?_⟩, ?_, Or.inr he.1⟩
    · by_contra hyx
      exact h (he.2.1 y hy hyx)
    · rintro rfl hd
      exact he.2.2 (isBelow_of_dominates hN hd)
    · intro hmem
      exact hmem (not_avoidingReach_of_enters hN he hy₀ hy₀x)

/-- Two arcs leaving a vertex: what the second dominates is not below the first. -/
theorem not_isBelow_of_leaving (hN : N.IsPhylogenetic) {v : V} {e f : E} {y : X}
    (he : N.graph.source e = v) (hf : N.graph.source f = v) (hef : e ≠ f)
    (hd : N.Dominates f y) : ¬ N.IsBelow e y := by
  intro hb
  have hroot : N.AvoidingReach f N.root v := by
    rw [← hf]
    exact avoidingReach_of_reaches_source hN.acyclic (hN.root_reaches _) .refl
  rcases reaches_split f hb with h | ⟨h, _⟩
  · exact hd ((hroot.tail ⟨e, hef, he, rfl⟩).trans h)
  · refine not_reaches_target_source hN e ?_
    rw [he, ← hf]
    exact h

/-- An arc dominating a vertex dominates what an arc leaving the vertex dominates. -/
theorem dominates_of_leaving {v : V} {g f : E} {y : X} (hg : ¬ N.AvoidingReach g N.root v)
    (hf : N.graph.source f = v) (hd : N.Dominates f y) : N.Dominates g y := by
  intro h
  rcases avoiding_split g f h with h' | ⟨h', _⟩
  · exact hd h'
  · exact hg (hf ▸ h')

/-- What is not below the target of an arc entering `v` is not below an arc leaving `v`. -/
theorem not_isBelow_of_entering {v : V} {g f : E} {y : X} (hg : N.graph.target g = v)
    (hf : N.graph.source f = v) (hy : ¬ N.IsBelow g y) : ¬ N.IsBelow f y := fun h => by
  refine hy ?_
  show N.graph.Reaches _ _
  rw [hg, ← hf]
  exact (reaches_arc f).trans h

/-- **Replacing a taxon of a hub.** Let `v` be the hub of `{p, r, a, b}`, and suppose that a taxon
`x` attaches to `v` by a bridge relative to `p, a, b`. Then `v` is the hub of `{p, x, a, b}`. -/
theorem isHub_replace [DecidableEq X] (hN : N.IsPhylogenetic) {p r a b x : X} {v : V}
    (hpr : p ≠ r) (hpa : p ≠ a) (hpb : p ≠ b) (hra : r ≠ a) (hrb : r ≠ b) (hab : a ≠ b)
    (hxp : x ≠ p) (hxa : x ≠ a) (hxb : x ≠ b)
    (hv : IsHub N {p, r, a, b} v)
    (hx : ∃ f, (N.graph.source f = v ∧ N.Dominates f x ∧ ¬ N.IsBelow f p ∧ ¬ N.IsBelow f a ∧
        ¬ N.IsBelow f b) ∨
      (N.graph.target f = v ∧ ¬ N.IsBelow f x ∧ N.Dominates f p ∧ N.Dominates f a ∧
        N.Dominates f b)) :
    IsHub N {p, x, a, b} v := by
  obtain ⟨f, hf⟩ := hx
  -- the bridge of a taxon `y` of `p, a, b`
  have key : ∀ y, (y = p ∨ y = a ∨ y = b) → ∃ e, Leaves N {p, x, a, b} v y e ∨
      Enters N {p, x, a, b} v y e := by
    intro y hy
    have hyq : y ∈ ({p, r, a, b} : Finset X) := by
      rcases hy with rfl | rfl | rfl <;> simp
    have hyr : y ≠ r := by
      rcases hy with rfl | rfl | rfl
      · exact hpr
      · exact hra.symm
      · exact hrb.symm
    have hyx : y ≠ x := by
      rcases hy with rfl | rfl | rfl
      · exact hxp.symm
      · exact hxa.symm
      · exact hxb.symm
    obtain ⟨e, he | he⟩ := hv y hyq
    · refine ⟨e, Or.inl ⟨he.1, he.2.1, fun z hz hzy => ?_⟩⟩
      simp only [mem_insert, mem_singleton] at hz
      rcases hz with rfl | rfl | rfl | rfl
      · exact he.2.2 _ (by simp) hzy
      · -- the taxon `x` is not below the bridge of `y`
        rcases hf with ⟨hfs, hfd, hfn⟩ | ⟨hft, hfn, _⟩
        · have hef : e ≠ f := by
            rintro rfl
            rcases hy with rfl | rfl | rfl
            · exact hfn.1 (isBelow_of_dominates hN he.2.1)
            · exact hfn.2.1 (isBelow_of_dominates hN he.2.1)
            · exact hfn.2.2 (isBelow_of_dominates hN he.2.1)
          exact not_isBelow_of_leaving hN he.1 hfs hef hfd
        · exact not_isBelow_of_entering hft he.1 hfn
      · exact he.2.2 _ (by simp) hzy
      · exact he.2.2 _ (by simp) hzy
    · refine ⟨e, Or.inr ⟨he.1, fun z hz hzy => ?_, he.2.2⟩⟩
      simp only [mem_insert, mem_singleton] at hz
      rcases hz with rfl | rfl | rfl | rfl
      · exact he.2.1 _ (by simp) hzy
      · -- the bridge of `y` enters `v`, and dominates `x`
        rcases hf with ⟨hfs, hfd, _⟩ | ⟨hft, _, hfp, hfa, hfb⟩
        · exact dominates_of_leaving (not_avoidingReach_of_enters hN he (y := r) (by simp) hyr.symm) hfs
            hfd
        · -- two bridges entering `v` are impossible
          exfalso
          have hef : e = f := by
            have hdz : ∃ w, N.Dominates e w ∧ N.Dominates f w := by
              rcases hy with rfl | rfl | rfl
              · exact ⟨a, he.2.1 a (by simp) hpa.symm, hfa⟩
              · exact ⟨p, he.2.1 p (by simp) hpa, hfp⟩
              · exact ⟨p, he.2.1 p (by simp) hpb, hfp⟩
            obtain ⟨w, h₁, h₂⟩ := hdz
            rcases dominates_comparable hN h₁ h₂ with h | h | h
            · exact h
            · exact absurd (by rw [hft, ← he.1]; exact h) (not_reaches_target_source hN f)
            · exact absurd (by rw [he.1, ← hft]; exact h) (not_reaches_target_source hN e)
          subst hef
          rcases hy with rfl | rfl | rfl
          · exact he.2.2 (isBelow_of_dominates hN hfp)
          · exact he.2.2 (isBelow_of_dominates hN hfa)
          · exact he.2.2 (isBelow_of_dominates hN hfb)
      · exact he.2.1 _ (by simp) hzy
      · exact he.2.1 _ (by simp) hzy
  intro z hz
  simp only [mem_insert, mem_singleton] at hz
  rcases hz with rfl | rfl | rfl | rfl
  · exact key _ (Or.inl rfl)
  · refine ⟨f, ?_⟩
    rcases hf with ⟨hfs, hfd, h₁, h₂, h₃⟩ | ⟨hft, hfn, h₁, h₂, h₃⟩
    · refine Or.inl ⟨hfs, hfd, fun y hy hyz => ?_⟩
      simp only [mem_insert, mem_singleton] at hy
      rcases hy with rfl | rfl | rfl | rfl
      · exact h₁
      · exact absurd rfl hyz
      · exact h₂
      · exact h₃
    · refine Or.inr ⟨hft, fun y hy hyz => ?_, hfn⟩
      simp only [mem_insert, mem_singleton] at hy
      rcases hy with rfl | rfl | rfl | rfl
      · exact h₁
      · exact absurd rfl hyz
      · exact h₂
      · exact h₃
  · exact key _ (Or.inr (Or.inl rfl))
  · exact key _ (Or.inr (Or.inr rfl))

/-! #### The quartet rule for the T1 null -/

section Rule

variable [DecidableEq X]

/-- A cut split and a hub on the same quartet are impossible. -/
theorem not_isHub_of_rdom (hN : N.IsPhylogenetic) {a b c d : X} {v : V}
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hcd : c ≠ d)
    (hv : IsHub N {a, b, c, d} v) (hr : RDom N a b c d) : False := by
  have ma : a ∈ ({a, b, c, d} : Finset X) := by simp
  have mb : b ∈ ({a, b, c, d} : Finset X) := by simp
  have mc : c ∈ ({a, b, c, d} : Finset X) := by simp
  have md : d ∈ ({a, b, c, d} : Finset X) := by simp
  obtain ⟨g, ⟨g₁, g₂, g₃, g₄⟩ | ⟨g₁, g₂, g₃, g₄⟩⟩ := hr
  · have hg := reaches_hub_of_dominates hN hv ma mb mc hab hac hbc g₁ g₂
    rcases exists_leaves hN hv mc md ma hcd hac.symm had.symm with ⟨f, hf⟩ | ⟨f, hf⟩
    · exact g₃ (hf.isBelow_of_reaches hN hg)
    · exact g₄ (hf.isBelow_of_reaches hN hg)
  · have hg := reaches_hub_of_dominates hN hv mc md ma hcd hac.symm had.symm g₁ g₂
    rcases exists_leaves hN hv ma mb mc hab hac hbc with ⟨f, hf⟩ | ⟨f, hf⟩
    · exact g₃ (hf.isBelow_of_reaches hN hg)
    · exact g₄ (hf.isBelow_of_reaches hN hg)

omit [DecidableEq X] in
/-- A quartet has at most one cut split. -/
theorem not_rdom_of_rdom (hN : N.IsPhylogenetic) {p q r s : X}
    (h₁ : RDom N p q r s) (h₂ : RDom N p r q s) : False := by
  have key : ∀ {g g' : E} {x y z : X}, N.Dominates g x → N.Dominates g' x → N.Dominates g y →
      N.Dominates g' z → ¬ N.IsBelow g z → ¬ N.IsBelow g' y → False := by
    intro g g' x y z hgx hgx' hgy hgz hn hn'
    rcases dominates_comparable hN hgx hgx' with h | h | h
    · subst h
      exact hn (isBelow_of_dominates hN hgz)
    · exact hn (isBelow_of_dominates hN (dominates_of_above hN h hgx hgx' hgz))
    · exact hn' (isBelow_of_dominates hN (dominates_of_above hN h hgx' hgx hgy))
  obtain ⟨g, ⟨g₁, g₂, g₃, g₄⟩ | ⟨g₁, g₂, g₃, g₄⟩⟩ := h₁ <;>
    obtain ⟨g', ⟨g₁', g₂', g₃', g₄'⟩ | ⟨g₁', g₂', g₃', g₄'⟩⟩ := h₂
  · exact key g₁ g₁' g₂ g₂' g₃ g₃'
  · exact key g₂ g₁' g₁ g₂' g₄ g₃'
  · exact key g₁ g₂' g₂ g₁' g₃ g₄'
  · exact key g₂ g₂' g₁ g₁' g₄ g₄'

/-- Two hubs with three common taxa: the fifth taxon replaces the third, or the two taxa form a
cut split. -/
theorem nullOn_of_two_hubs (hN : N.IsPhylogenetic) {p q r a b : X} (hpq : p ≠ q) (hpr : p ≠ r)
    (hpa : p ≠ a) (hpb : p ≠ b) (hqr : q ≠ r) (hqa : q ≠ a) (hqb : q ≠ b) (hra : r ≠ a)
    (hrb : r ≠ b) (hab : a ≠ b) (h₁ : HasTrivialFourBlob N {p, r, a, b})
    (h₂ : HasTrivialFourBlob N {q, r, a, b}) :
    HasTrivialFourBlob N {p, q, a, b} ∨ RDom N p q a b := by
  have hc₁ : 1 < ({p, r, a, b} : Finset X).card := by
    rw [card_four_of_ne hpr hpa hpb hra hrb hab]; omega
  have hc₂ : 1 < ({q, r, a, b} : Finset X).card := by
    rw [card_four_of_ne hqr hqa hqb hra hrb hab]; omega
  have hc : 1 < ({p, q, a, b} : Finset X).card := by
    rw [card_four_of_ne hpq hpa hpb hqa hqb hab]; omega
  obtain ⟨v, hv⟩ := exists_isHub hN hc₁ h₁
  obtain ⟨u, hu⟩ := exists_isHub hN hc₂ h₂
  have huv : u = v := isHub_unique hN hv hu (t₁ := r) (t₂ := a) (t₃ := b) (by simp) (by simp)
    (by simp) (by simp) (by simp) (by simp) hra hrb hab
  subst huv
  have hub : IsHub N {p, q, a, b} u → HasTrivialFourBlob N {p, q, a, b} ∨ RDom N p q a b :=
    fun h => Or.inl (hasTrivialFourBlob_of_isHub hN hc h)
  obtain ⟨e, he | he⟩ := hv p (by simp) <;> obtain ⟨f, hf | hf⟩ := hu q (by simp)
  · -- both bridges leave the hub
    by_cases hef : f = e
    · subst hef
      exact Or.inr ⟨f, Or.inl ⟨he.2.1, hf.2.1, hf.2.2 a (by simp) hqa.symm,
        hf.2.2 b (by simp) hqb.symm⟩⟩
    · exact hub (isHub_replace hN hpr hpa hpb hra hrb hab hpq.symm hqa hqb hv ⟨f, Or.inl
        ⟨hf.1, hf.2.1, not_isBelow_of_leaving hN hf.1 he.1 hef he.2.1, hf.2.2 a (by simp) hqa.symm,
          hf.2.2 b (by simp) hqb.symm⟩⟩)
  · -- the bridge of `q` enters the hub
    exact hub (isHub_replace hN hpr hpa hpb hra hrb hab hpq.symm hqa hqb hv ⟨f, Or.inr
      ⟨hf.1, hf.2.2, dominates_of_leaving
        (not_avoidingReach_of_enters hN hf (y := r) (by simp) hqr.symm) he.1 he.2.1,
        hf.2.1 a (by simp) hqa.symm, hf.2.1 b (by simp) hqb.symm⟩⟩)
  · -- the bridge of `p` enters the hub
    exact hub (isHub_replace hN hpr hpa hpb hra hrb hab hpq.symm hqa hqb hv ⟨f, Or.inl
      ⟨hf.1, hf.2.1, not_isBelow_of_entering he.1 hf.1 he.2.2, hf.2.2 a (by simp) hqa.symm,
        hf.2.2 b (by simp) hqb.symm⟩⟩)
  · -- both enter the hub: they are one arc, which gives a cut split
    have hef : e = f := by
      rcases dominates_comparable hN (he.2.1 r (by simp) hpr.symm) (hf.2.1 r (by simp) hqr.symm) with
        h | h | h
      · exact h
      · exact absurd (by rw [hf.1, ← he.1]; exact h) (not_reaches_target_source hN f)
      · exact absurd (by rw [he.1, ← hf.1]; exact h) (not_reaches_target_source hN e)
    subst hef
    exact Or.inr ⟨e, Or.inr ⟨he.2.1 a (by simp) hpa.symm, he.2.1 b (by simp) hpb.symm, he.2.2,
      hf.2.2⟩⟩

/-- A hub and a cut split on adjacent quartets: the taxon on the side of the cut replaces the third.
This is the first half of `FalseEdge.false_of_adjacent`. -/
theorem hasTrivialFourBlob_of_hub_rdom (hN : N.IsPhylogenetic) {p q r a b : X} (hpq : p ≠ q)
    (hpa : p ≠ a) (hpb : p ≠ b) (hqr : q ≠ r) (hqa : q ≠ a) (hqb : q ≠ b) (hra : r ≠ a)
    (hrb : r ≠ b) (hab : a ≠ b) (h₁ : HasTrivialFourBlob N {q, r, a, b}) (h₂ : RDom N p r a b) :
    HasTrivialFourBlob N {p, q, a, b} := by
  have hc₁ : 1 < ({q, r, a, b} : Finset X).card := by
    rw [card_four_of_ne hqr hqa hqb hra hrb hab]; omega
  have hc : 1 < ({p, q, a, b} : Finset X).card := by
    rw [card_four_of_ne hpq hpa hpb hqa hqb hab]; omega
  obtain ⟨v, hv⟩ := exists_isHub hN hc₁ h₁
  have ma : a ∈ ({q, r, a, b} : Finset X) := by simp
  have mb : b ∈ ({q, r, a, b} : Finset X) := by simp
  have mr : r ∈ ({q, r, a, b} : Finset X) := by simp
  obtain ⟨e, he | he⟩ := hv r mr
  · -- the bridge towards `r` leaves the hub, and dominates `p`
    have hep : N.Dominates e p := by
      obtain ⟨g, ⟨g₁, g₂, g₃, g₄⟩ | ⟨g₁, g₂, g₃, g₄⟩⟩ := h₂
      · rcases dominates_comparable hN he.2.1 g₂ with h | h | h
        · subst h
          exact g₁
        · exact dominates_of_above hN h he.2.1 g₂ g₁
        · exact absurd (he.1 ▸ h) (not_reaches_hub hN hv ma mb mr hab hra.symm hrb.symm g₃ g₄)
      · exact absurd (he.isBelow_of_reaches hN
          (reaches_hub_of_dominates hN hv ma mb mr hab hra.symm hrb.symm g₁ g₂)) g₄
    have := isHub_replace hN hqr hqa hqb hra hrb hab hpq hpa hpb hv ⟨e, Or.inl
      ⟨he.1, hep, he.2.2 q (by simp) hqr, he.2.2 a ma hra.symm, he.2.2 b mb hrb.symm⟩⟩
    rw [pair_insert_comm] at this
    exact hasTrivialFourBlob_of_isHub hN hc this
  · -- the bridge towards `r` enters the hub, and `p` is not below it
    have hep : ¬ N.IsBelow e p := by
      intro hb'
      have hvb : N.graph.Reaches v (N.leaf p) := by
        rw [← he.1]; exact hb'
      obtain ⟨g, ⟨g₁, g₂, g₃, g₄⟩ | ⟨g₁, g₂, g₃, g₄⟩⟩ := h₂
      · have hng := not_reaches_hub hN hv ma mb mr hab hra.symm hrb.symm g₃ g₄
        have hvg := reaches_source_of_dominates hN hng hvb g₁
        refine he.2.2 ?_
        show N.graph.Reaches _ _
        rw [he.1]
        exact hvg.trans ((reaches_arc g).trans (isBelow_of_dominates hN g₂))
      · exact g₃ ((reaches_hub_of_dominates hN hv ma mb mr hab hra.symm hrb.symm g₁ g₂).trans hvb)
    have := isHub_replace hN hqr hqa hqb hra hrb hab hpq hpa hpb hv ⟨e, Or.inr
      ⟨he.1, hep, he.2.1 q (by simp) hqr, he.2.1 a ma hra.symm, he.2.1 b mb hrb.symm⟩⟩
    rw [pair_insert_comm] at this
    exact hasTrivialFourBlob_of_isHub hN hc this

omit [DecidableEq X] in
/-- What an arc `g₁` dominates, with a taxon `r`, is not below an arc `g₂` that has `r` not below it
and a taxon `a` below it that is not below `g₁`. -/
theorem not_isBelow_of_cross (hN : N.IsPhylogenetic) {g₁ g₂ : E} {x r a : X}
    (hx : N.Dominates g₁ x) (hr : N.Dominates g₁ r) (hr₂ : ¬ N.IsBelow g₂ r)
    (ha : N.IsBelow g₂ a) (ha₁ : ¬ N.IsBelow g₁ a) : ¬ N.IsBelow g₂ x := by
  intro hb
  have hne : g₂ ≠ g₁ := by
    rintro rfl
    exact ha₁ ha
  rcases reaches_split g₁ (hN.root_reaches (N.graph.source g₂)) with h₁ | ⟨_, h₁⟩
  · rcases reaches_split g₁ hb with h₂ | ⟨h₂, _⟩
    · exact hx ((h₁.tail ⟨g₂, hne, rfl, rfl⟩).trans h₂)
    · exact hr₂ (h₂.trans ((reaches_arc g₁).trans (isBelow_of_dominates hN hr)))
  · exact ha₁ (h₁.trans ((reaches_arc g₂).trans ha))

omit [DecidableEq X] in
/-- The quartet rule for cut splits: `pr|ab` and `qr|ab` give `pq|ab`. -/
theorem rdom_rule (hN : N.IsPhylogenetic) {p q r a b : X} (h₁ : RDom N p r a b)
    (h₂ : RDom N q r a b) : RDom N p q a b := by
  obtain ⟨g, ⟨gp, gr, ga, gb⟩ | ⟨ga, gb, gp, gr⟩⟩ := h₁ <;>
    obtain ⟨g', ⟨gq, gr', ga', gb'⟩ | ⟨ga', gb', gq, gr'⟩⟩ := h₂
  · rcases dominates_comparable hN gr gr' with h | h | h
    · subst h
      exact ⟨g, Or.inl ⟨gp, gq, ga, gb⟩⟩
    · exact ⟨g, Or.inl ⟨gp, dominates_of_above hN h gr gr' gq, ga, gb⟩⟩
    · exact ⟨g', Or.inl ⟨dominates_of_above hN h gr' gr gp, gq, ga', gb'⟩⟩
  · exact ⟨g', Or.inr ⟨ga', gb', not_isBelow_of_cross hN gp gr gr'
      (isBelow_of_dominates hN ga') ga, gq⟩⟩
  · exact ⟨g, Or.inr ⟨ga, gb, gp, not_isBelow_of_cross hN gq gr' gr
      (isBelow_of_dominates hN ga) ga'⟩⟩
  · rcases dominates_comparable hN ga ga' with h | h | h
    · subst h
      exact ⟨g, Or.inr ⟨ga, gb, gp, gq⟩⟩
    · exact ⟨g', Or.inr ⟨ga', gb', fun hb => gp (h.trans ((reaches_arc g').trans hb)), gq⟩⟩
    · exact ⟨g, Or.inr ⟨ga, gb, gp, fun hb => gq (h.trans ((reaches_arc g).trans hb))⟩⟩

/-- The T1 null on `x₁x₂|x₃x₄`, in the language of domination: a trivial 4-blob, or the cut split. -/
def NullOn (N : RootedNetwork V E X) (x₁ x₂ x₃ x₄ : X) : Prop :=
  HasTrivialFourBlob N ({x₁, x₂, x₃, x₄} : Finset X) ∨ RDom N x₁ x₂ x₃ x₄

theorem NullOn.symm {x₁ x₂ x₃ x₄ : X} (h : NullOn N x₁ x₂ x₃ x₄) : NullOn N x₃ x₄ x₁ x₂ := by
  rcases h with h | h
  · rw [← insert_pair_comm] at h
    exact Or.inl h
  · exact Or.inr h.symm

/-- **The quartet rule for the T1 null.** If `pr|ab` and `qr|ab` are each a cut split or a trivial
4-blob, then so is `pq|ab`. This is the rule `pr|ab, qr|ab ⟹ pq|ab` for the quartets of a tree, carried
over to the quartets of a network that are under the T1 null, for any network. -/
theorem NullOn.rule (hN : N.IsPhylogenetic) {p q r a b : X} (hpq : p ≠ q) (hpr : p ≠ r)
    (hpa : p ≠ a) (hpb : p ≠ b) (hqr : q ≠ r) (hqa : q ≠ a) (hqb : q ≠ b) (hra : r ≠ a)
    (hrb : r ≠ b) (hab : a ≠ b) (h₁ : NullOn N p r a b) (h₂ : NullOn N q r a b) :
    NullOn N p q a b := by
  rcases h₁ with h₁ | h₁ <;> rcases h₂ with h₂ | h₂
  · exact nullOn_of_two_hubs hN hpq hpr hpa hpb hqr hqa hqb hra hrb hab h₁ h₂
  · have := hasTrivialFourBlob_of_hub_rdom hN hpq.symm hqa hqb hpr hpa hpb hra hrb hab h₁ h₂
    rw [pair_insert_comm] at this
    exact Or.inl this
  · exact Or.inl (hasTrivialFourBlob_of_hub_rdom hN hpq hpa hpb hqr hqa hqb hra hrb hab h₂ h₁)
  · exact Or.inr (rdom_rule hN h₁ h₂)

end Rule

/-! #### From the multipartition to the bipartition -/

section Quartets

variable [Fintype X] [DecidableEq X]

/-- The quartet tree `s` is under the T1 null, in terms of the network: it is a cut split of the
induced network, or the induced network has a trivial 4-blob. -/
def IsNullQuartet (N : RootedNetwork V E X) (s : QuartetTree X) : Prop :=
  InducedCutSplit N s ∨ HasTrivialFourBlob N s.taxa

omit [Fintype X] in
/-- A cut split of an induced network, from the language of domination. -/
theorem inducedCutSplit_of_rdom (hN : N.IsPhylogenetic) {a b c d : X}
    (h : ({a, b, c, d} : Finset X).card = 4) (hr : RDom N a b c d) :
    InducedCutSplit N (quartetTree a b c d h) := by
  obtain ⟨_, hac, had, hbc, hbd, _⟩ := ne_of_card_four h
  refine ⟨{a, b}, by simp [quartetTree], ?_⟩
  rw [taxa_quartetTree, hasCutSplitOn_iff_separates hN]
  have hin : ∀ x, x ∈ ((({a, b, c, d} : Finset X) : Set X) ∩ (({a, b} : Finset X) : Set X)) →
      x = a ∨ x = b := by
    intro x hx
    simpa using hx.2
  have hout : ∀ x, x ∈ ((({a, b, c, d} : Finset X) : Set X) \ (({a, b} : Finset X) : Set X)) →
      x = c ∨ x = d := by
    intro x hx
    have h₁ : x = a ∨ x = b ∨ x = c ∨ x = d := by simpa using hx.1
    have h₂ : ¬ (x = a ∨ x = b) := by simpa using hx.2
    tauto
  obtain ⟨g, ⟨g₁, g₂, g₃, g₄⟩ | ⟨g₁, g₂, g₃, g₄⟩⟩ := hr
  · refine ⟨g, Or.inl ⟨⟨a, by simp, by simp⟩, ?_, ?_⟩⟩
    · intro x hx
      rcases hin x hx with rfl | rfl
      · exact g₁
      · exact g₂
    · intro x hx
      rcases hout x hx with rfl | rfl
      · exact g₃
      · exact g₄
  · refine ⟨g, Or.inr ⟨⟨c, by simp, by simp [hac.symm, hbc.symm]⟩, ?_, ?_⟩⟩
    · intro x hx
      rcases hout x hx with rfl | rfl
      · exact g₁
      · exact g₂
    · intro x hx
      rcases hin x hx with rfl | rfl
      · exact g₃
      · exact g₄

omit [Fintype X] in
/-- The T1 null on a quartet tree is the T1 null on its tuple. -/
theorem isNullQuartet_quartetTree_iff (hN : N.IsPhylogenetic) {a b c d : X}
    (h : ({a, b, c, d} : Finset X).card = 4) :
    IsNullQuartet N (quartetTree a b c d h) ↔ NullOn N a b c d := by
  obtain ⟨_, hac, had, hbc, hbd, _⟩ := ne_of_card_four h
  unfold IsNullQuartet NullOn
  rw [taxa_quartetTree, or_comm]
  refine or_congr Iff.rfl ⟨fun hr => ?_, inducedCutSplit_of_rdom hN h⟩
  exact rdom_of_hasCutSplitOn hN hac had hbc hbd (hasCutSplitOn_of_inducedCutSplit h hr)

/-- At an internal edge of a tree, the T1 null on the quartets of the multipartition gives the T1
null on all the quartets of the bipartition. So the three quartet types agree on whether the T1
null holds on all their quartets, by the quartet rule `NullOn.rule`. -/
theorem nullOn_of_forall_multipartition (hN : N.IsPhylogenetic) {T : Finset (Finset X)}
    (hT : IsSplitFamily T) {A : Finset X} (hA : 2 ≤ A.card) (hA' : 2 ≤ Aᶜ.card)
    (hall : ∀ x₁ x₂ x₃ x₄, x₁ ∈ A → x₂ ∈ A → x₃ ∉ A → x₄ ∉ A → Sep T A x₁ x₂ → Sep T Aᶜ x₃ x₄ →
      NullOn N x₁ x₂ x₃ x₄)
    {a b c d : X} (ha : a ∈ A) (hb : b ∈ A) (hc : c ∉ A) (hd : d ∉ A) (hab : a ≠ b) (hcd : c ≠ d) :
    NullOn N a b c d := by
  have hAu : A ≠ univ := by
    rintro rfl
    simp at hA'
  have hAu' : Aᶜ ≠ univ := by
    intro h
    have : A = ∅ := by simpa using congrArg compl h
    subst this
    simp at hA
  -- a taxon in another block than two given taxa of a side, if these are in one block
  have pivot : ∀ {P : Finset X}, P ≠ univ → 2 ≤ P.card → ∀ {x y : X}, ¬ Sep T P x y → x ≠ y →
      ∃ r ∈ P, Sep T P x r ∧ Sep T P y r := by
    intro P hP hP₂ x y hxy hne
    obtain ⟨u, hu, w, hw, huw⟩ := exists_sep hT hP hP₂
    have hor : ∃ r ∈ P, Sep T P x r := by
      rcases huw.or hT hP x with h | h
      · exact ⟨u, hu, h⟩
      · exact ⟨w, hw, h⟩
    obtain ⟨r, hr, hxr⟩ := hor
    refine ⟨r, hr, hxr, ?_⟩
    rcases hxr.or hT hP y with h | h
    · exact absurd h.symm hxy
    · exact h
  -- first the pairs `c, d` in distinct blocks
  have step₁ : ∀ {a b c d : X}, a ∈ A → b ∈ A → c ∉ A → d ∉ A → a ≠ b → Sep T Aᶜ c d →
      NullOn N a b c d := by
    intro a b c d ha hb hc hd hab hcd
    by_cases hsep : Sep T A a b
    · exact hall a b c d ha hb hc hd hsep hcd
    · obtain ⟨r, hr, har, hbr⟩ := pivot hAu hA hsep hab
      exact NullOn.rule hN hab har.1 (fun h => hc (h ▸ ha)) (fun h => hd (h ▸ ha)) hbr.1
        (fun h => hc (h ▸ hb)) (fun h => hd (h ▸ hb)) (fun h => hc (h ▸ hr))
        (fun h => hd (h ▸ hr)) hcd.1
        (hall a r c d ha hr hc hd har hcd) (hall b r c d hb hr hc hd hbr hcd)
  by_cases hsep : Sep T Aᶜ c d
  · exact step₁ ha hb hc hd hab hsep
  · obtain ⟨r, hr, hcr, hdr⟩ := pivot hAu' hA' hsep hcd
    have hrA : r ∉ A := mem_compl.1 hr
    exact (NullOn.rule hN hcd hcr.1 (fun h => hc (h ▸ ha)) (fun h => hc (h ▸ hb)) hdr.1
      (fun h => hd (h ▸ ha)) (fun h => hd (h ▸ hb)) (fun h => hrA (h ▸ ha))
      (fun h => hrA (h ▸ hb)) hab
      (step₁ ha hb hc hrA hab hcr).symm (step₁ ha hb hd hrA hab hdr).symm).symm

omit [Fintype X] in
theorem mem_multipartitionQuartets_empty [Fintype X] {A : Finset X} {s : QuartetTree X}
    (hs : s ∈ bipartitionQuartets A) : s ∈ multipartitionQuartets (∅ : Finset (Finset X)) A :=
  mem_filter.2 ⟨hs, by simp, by simp⟩

/-- **The quartet types agree on the T1 null.** At an internal edge of a tree `T`, if all the
quartets of the multipartition `S_mul` are under the T1 null, then so are all the quartets of the
bipartition `S_bi`. -/
theorem forall_bipartition_of_forall_multipartition (hN : N.IsPhylogenetic)
    {T : Finset (Finset X)} (hT : IsSplitFamily T) {A : Finset X} (hA : 2 ≤ A.card)
    (hA' : 2 ≤ Aᶜ.card) (h : ∀ s ∈ multipartitionQuartets T A, IsNullQuartet N s) :
    ∀ s ∈ bipartitionQuartets A, IsNullQuartet N s := by
  intro s hs
  obtain ⟨a, b, c, d, hc₄, rfl, ha, hb, hc, hd, hab, hcd⟩ :=
    exists_tuple (mem_multipartitionQuartets_empty hs)
  rw [isNullQuartet_quartetTree_iff hN]
  refine nullOn_of_forall_multipartition hN hT hA hA' (fun x₁ x₂ x₃ x₄ h₁ h₂ h₃ h₄ h₁₂ h₃₄ => ?_)
    ha hb hc hd hab.1 hcd.1
  have h₁₃ : x₁ ≠ x₃ := fun h => h₃ (h ▸ h₁)
  have h₁₄ : x₁ ≠ x₄ := fun h => h₄ (h ▸ h₁)
  have h₂₃ : x₂ ≠ x₃ := fun h => h₃ (h ▸ h₂)
  have h₂₄ : x₂ ≠ x₄ := fun h => h₄ (h ▸ h₂)
  have hc := card_four_of_ne h₁₂.1 h₁₃ h₁₄ h₂₃ h₂₄ h₃₄.1
  exact (isNullQuartet_quartetTree_iff hN hc).1 (h _ (quartetTree_mem hc h₁ h₂ h₃ h₄ h₁₂ h₃₄))

/-! #### Complements of sides -/

theorem compl_inter_taxa_mem {A : Finset X} {s : QuartetTree X} (hs : A ∩ s.taxa ∈ s.val) :
    Aᶜ ∩ s.taxa ∈ s.val := by
  have : Aᶜ ∩ s.taxa = s.taxa \ (A ∩ s.taxa) := by
    ext x
    rw [Finset.mem_sdiff, mem_inter, mem_inter, mem_compl]
    tauto
  rw [this]
  exact s.sdiff_mem hs

theorem bipartitionQuartets_compl (A : Finset X) :
    bipartitionQuartets Aᶜ = bipartitionQuartets A := by
  ext s
  simp only [bipartitionQuartets, mem_filter, mem_univ, true_and]
  refine ⟨fun h => ?_, compl_inter_taxa_mem⟩
  simpa using compl_inter_taxa_mem h

theorem multipartitionQuartets_compl (T : Finset (Finset X)) (A : Finset X) :
    multipartitionQuartets T Aᶜ = multipartitionQuartets T A := by
  ext s
  simp only [multipartitionQuartets, mem_filter, bipartitionQuartets_compl, compl_compl]
  tauto

theorem two_le_card_of_inter_taxa_mem {A : Finset X} {s : QuartetTree X}
    (hs : A ∩ s.taxa ∈ s.val) : 2 ≤ A.card ∧ 2 ≤ Aᶜ.card := by
  have h₁ := s.card_of_mem hs
  have h₂ := s.card_of_mem (compl_inter_taxa_mem hs)
  exact ⟨h₁ ▸ Finset.card_le_card Finset.inter_subset_left,
    h₂ ▸ Finset.card_le_card Finset.inter_subset_left⟩

end Quartets

/-! ### Part 2: the sequence of trees, for any edge p-values and any overall p-values -/

section Sequence

variable {X : Type*} [Fintype X] [DecidableEq X]

/-- Step 7 of the algorithm, for edge p-values `edgeP`. -/
def contractBy (edgeP : Finset (Finset X) → Finset X → ℝ) (T : Finset (Finset X)) :
    Finset (Finset X) :=
  contractSides T ((internalSides T).filter fun A =>
    ∀ B ∈ internalSides T, edgeP T A ≤ edgeP T B)

/-- The sequence of trees, from the tree `T₁` after Step 3. -/
def seqBy (edgeP : Finset (Finset X) → Finset X → ℝ) (T₁ : Finset (Finset X)) (i : ℕ) :
    Finset (Finset X) :=
  (contractBy edgeP)^[i] T₁

/-- The first iteration at which the tree has no internal edges. -/
def lastBy (edgeP : Finset (Finset X) → Finset X → ℝ) (T₁ : Finset (Finset X)) : ℕ :=
  sInf {i | internalSides (seqBy edgeP T₁ i) = ∅}

/-- Step 10 of the algorithm, for overall p-values `treeP`. -/
def selectedBy (rule : SelectionRule) (α : ℝ) (edgeP : Finset (Finset X) → Finset X → ℝ)
    (treeP : Finset (Finset X) → ℝ) (T₁ : Finset (Finset X)) : ℕ :=
  match rule with
  | .early => sInf {i | i ≤ lastBy edgeP T₁ ∧ α ≤ treeP (seqBy edgeP T₁ i)}
  | .late =>
      if ∃ i ≤ lastBy edgeP T₁, treeP (seqBy edgeP T₁ i) < α then
        sSup {i | i ≤ lastBy edgeP T₁ ∧ treeP (seqBy edgeP T₁ i) < α} + 1
      else 0

/-- The output of Steps 4 to 10 of the algorithm. -/
def outputBy (rule : SelectionRule) (α : ℝ) (edgeP : Finset (Finset X) → Finset X → ℝ)
    (treeP : Finset (Finset X) → ℝ) (T₁ : Finset (Finset X)) : Finset (Finset X) :=
  seqBy edgeP T₁ (selectedBy rule α edgeP treeP T₁)

/-- The algorithm of the paper is this one. -/
theorem ectoblob_eq_outputBy (o : ECToBlobOptions) (α β : ℝ) (c : QuartetTree X → ℝ)
    (T₀ : Finset (Finset X)) :
    ectoblob o α β c T₀ =
      outputBy o.rule α (edgeT1P o c T₀) (treeT1P o c) (afterStar o β c T₀) := rfl

/-- What the end of the proof of Theorem 8.2 uses of the p-values (lines 1133-1158), with `G` in the
place of the tree of blobs: the tree `T₁` contains `G`, the edges in `G` are not rejected, and the
others are rejected, by the edge p-values and by the overall p-values alike. -/
structure IsLimit (α : ℝ) (edgeP : Finset (Finset X) → Finset X → ℝ)
    (treeP : Finset (Finset X) → ℝ) (T₁ G : Finset (Finset X)) : Prop where
  subset : G ⊆ T₁
  compl : ∀ A ∈ G, Aᶜ ∈ G
  pendant : ∀ A ∈ T₁, ¬ (2 ≤ A.card ∧ 2 ≤ Aᶜ.card) → A ∈ G
  split : ∀ A ∈ internalSides T₁, IsSplitFamily T₁
  edge_gt : ∀ T ⊆ T₁, ∀ A ∈ internalSides T, A ∈ G → α < edgeP T A
  edge_lt : ∀ T ⊆ T₁, IsSplitFamily T → ∀ A ∈ internalSides T, A ∉ G → edgeP T A < α
  tree_gt : ∀ T ⊆ G, α < treeP T
  tree_lt : ∀ T ⊆ T₁, ∀ A ∈ internalSides T, A ∉ G → treeP T < α

variable {α : ℝ} {edgeP : Finset (Finset X) → Finset X → ℝ} {treeP : Finset (Finset X) → ℝ}
  {T₁ G : Finset (Finset X)}

theorem contractBy_subset (T : Finset (Finset X)) : contractBy edgeP T ⊆ T :=
  Finset.filter_subset _ _

theorem seqBy_succ (i : ℕ) : seqBy edgeP T₁ (i + 1) = contractBy edgeP (seqBy edgeP T₁ i) :=
  Function.iterate_succ_apply' _ _ _

theorem seqBy_anti {i j : ℕ} (h : i ≤ j) : seqBy edgeP T₁ j ⊆ seqBy edgeP T₁ i := by
  induction j, h using Nat.le_induction with
  | base => exact subset_rfl
  | succ j _ ih =>
    rw [seqBy_succ]
    exact (contractBy_subset _).trans ih

theorem seqBy_subset (i : ℕ) : seqBy edgeP T₁ i ⊆ T₁ := seqBy_anti (Nat.zero_le i)

theorem isSplitFamily_seqBy (hT₁ : IsSplitFamily T₁) (i : ℕ) : IsSplitFamily (seqBy edgeP T₁ i) := by
  induction i with
  | zero => exact hT₁
  | succ i ih =>
    rw [seqBy_succ]
    exact isSplitFamily_contractSides ih (Finset.filter_subset _ _)

theorem contractBy_ssubset {T : Finset (Finset X)} (h : (internalSides T).Nonempty) :
    contractBy edgeP T ⊂ T := by
  obtain ⟨A, hA, hmin⟩ := Finset.exists_min_image _ (edgeP T) h
  rw [Finset.ssubset_iff_of_subset (contractBy_subset T)]
  exact ⟨A, (mem_internalSides.1 hA).1,
    fun hmem => (mem_contractSides.1 hmem).2.1 (mem_filter.2 ⟨hA, hmin⟩)⟩

theorem exists_internalSides_seqBy_eq_empty : ∃ i, internalSides (seqBy edgeP T₁ i) = ∅ := by
  by_contra hcon
  push Not at hcon
  have hcard : ∀ i, (seqBy edgeP T₁ i).card + i ≤ (seqBy edgeP T₁ 0).card := by
    intro i
    induction i with
    | zero => omega
    | succ i ih =>
      rw [seqBy_succ]
      have := Finset.card_lt_card (contractBy_ssubset (edgeP := edgeP) (hcon i))
      omega
  have := hcard ((seqBy edgeP T₁ 0).card + 1)
  omega

/-- Step 7 keeps `G` as long as there is an edge off `G`. -/
theorem IsLimit.subset_contractBy (R : IsLimit α edgeP treeP T₁ G) {T : Finset (Finset X)}
    (hT : T ⊆ T₁) (hTs : IsSplitFamily T) (hB : G ⊆ T) {F : Finset X} (hF : F ∈ internalSides T)
    (hFB : F ∉ G) : G ⊆ contractBy edgeP T := by
  have key : ∀ A ∈ G, A ∉ (internalSides T).filter fun A =>
      ∀ B ∈ internalSides T, edgeP T A ≤ edgeP T B := by
    intro A hA hmem
    obtain ⟨hAi, h₀⟩ := mem_filter.1 hmem
    have h₁ := R.edge_gt T hT A hAi hA
    have h₂ := R.edge_lt T hT hTs F hF hFB
    linarith [h₀ F hF]
  intro A hA
  exact mem_contractSides.2 ⟨hB hA, key A hA, key _ (R.compl A hA)⟩

/-- **The end of the proof of Theorem 8.2 (lines 1133-1158), with `G` in the place of the tree of
blobs.** If `G` is the limit of the p-values, then both selection rules output `G`. -/
theorem IsLimit.outputBy_eq (R : IsLimit α edgeP treeP T₁ G) (rule : SelectionRule) :
    outputBy rule α edgeP treeP T₁ = G := by
  have hex : ∃ i, ¬ ∃ A ∈ internalSides (seqBy edgeP T₁ i), A ∉ G := by
    obtain ⟨i, hi⟩ := exists_internalSides_seqBy_eq_empty (edgeP := edgeP) (T₁ := T₁)
    exact ⟨i, by simp [hi]⟩
  let i₀ := Nat.find hex
  have hspec : ¬ ∃ A ∈ internalSides (seqBy edgeP T₁ i₀), A ∉ G := Nat.find_spec hex
  have hbefore : ∀ i, i < i₀ → ∃ A ∈ internalSides (seqBy edgeP T₁ i), A ∉ G :=
    fun i hi => not_not.1 (Nat.find_min hex hi)
  have hsub : ∀ i, i ≤ i₀ → G ⊆ seqBy edgeP T₁ i := by
    intro i
    induction i with
    | zero => exact fun _ => R.subset
    | succ i ih =>
      intro hi
      obtain ⟨F, hF, hFB⟩ := hbefore i (by omega)
      have hF₀ : F ∈ internalSides T₁ := by
        obtain ⟨h₁, h₂⟩ := mem_internalSides.1 hF
        exact mem_internalSides.2 ⟨seqBy_subset i h₁, h₂⟩
      rw [seqBy_succ]
      exact R.subset_contractBy (seqBy_subset i) (isSplitFamily_seqBy (R.split F hF₀) i)
        (ih (by omega)) hF hFB
  have heq : seqBy edgeP T₁ i₀ = G := by
    refine Finset.Subset.antisymm ?_ (hsub i₀ le_rfl)
    intro A hA
    by_contra hAB
    by_cases hint : 2 ≤ A.card ∧ 2 ≤ Aᶜ.card
    · exact hspec ⟨A, mem_internalSides.2 ⟨hA, hint⟩, hAB⟩
    · exact hAB (R.pendant A (seqBy_subset i₀ hA) hint)
  have hle : ∀ i, i₀ ≤ i → seqBy edgeP T₁ i ⊆ G := fun i hi => by
    rw [← heq]
    exact seqBy_anti hi
  have hlt : ∀ i, i < i₀ → treeP (seqBy edgeP T₁ i) < α := by
    intro i hi
    obtain ⟨F, hF, hFB⟩ := hbefore i hi
    exact R.tree_lt _ (seqBy_subset i) F hF hFB
  have hgt : ∀ i, i₀ ≤ i → α < treeP (seqBy edgeP T₁ i) := fun i hi => R.tree_gt _ (hle i hi)
  have hlast : i₀ ≤ lastBy edgeP T₁ := by
    have hmem : lastBy edgeP T₁ ∈ {i | internalSides (seqBy edgeP T₁ i) = ∅} :=
      Nat.sInf_mem exists_internalSides_seqBy_eq_empty
    refine Nat.find_min' hex ?_
    have hmem' : internalSides (seqBy edgeP T₁ (lastBy edgeP T₁)) = ∅ := hmem
    simp [hmem']
  have hsel : selectedBy rule α edgeP treeP T₁ = i₀ := by
    cases rule with
    | early =>
      simp only [selectedBy]
      refine IsLeast.csInf_eq ⟨⟨hlast, (hgt i₀ le_rfl).le⟩, ?_⟩
      rintro i ⟨_, hi⟩
      by_contra hcon
      exact absurd hi (not_le_of_gt (hlt i (by omega)))
    | late =>
      simp only [selectedBy]
      split_ifs with h
      · obtain ⟨i, _, hi⟩ := h
        have hipos : i < i₀ := by
          by_contra hcon
          exact absurd hi (not_lt_of_gt (hgt i (by omega)))
        have hset : IsGreatest {i | i ≤ lastBy edgeP T₁ ∧ treeP (seqBy edgeP T₁ i) < α}
            (i₀ - 1) := by
          refine ⟨⟨by omega, hlt _ (by omega)⟩, ?_⟩
          rintro j ⟨hj, hjα⟩
          by_contra hcon
          exact absurd hjα (not_lt_of_gt (hgt j (by omega)))
        rw [hset.csSup_eq]
        omega
      · push Not at h
        by_contra hcon
        exact absurd (hlt 0 (by omega)) (not_lt_of_ge (h 0 (Nat.zero_le _)))
  rw [outputBy, hsel]
  exact heq

end Sequence

/-! ### Part 3: the limit of the algorithm on an arbitrary tree -/

section Limit

variable {V E X : Type*} [Fintype X] [DecidableEq X] {N : RootedNetwork V E X}

/-- Step 6, for p-values `f` of the quartets: the combined p-value of the edge with side `A` of the
current tree `T`. -/
def edgeTestP (o : ECToBlobOptions) (f : QuartetTree X → ℝ) (T₀ T : Finset (Finset X))
    (A : Finset X) : ℝ :=
  combineP o.testCo ((edgeQuartets o T₀ T A).val.map f)

/-- Steps 4 and 8, for p-values `f` of the quartets: the combined p-value of the tree `T`. -/
def treeTestP (o : ECToBlobOptions) (f : QuartetTree X → ℝ) (T : Finset (Finset X)) : ℝ :=
  combineP o.testCo ((univ.filter fun s => Displays T s).val.map f)

/-- **What the algorithm tends to, on an arbitrary tree `T₀`.** The pendant edges of `T₀`, and its
internal edges that have a quartet of the multipartition with no trivial 4-blob, so that Step 3 does
not contract them, and all of whose quartets are under the T1 null, so that the T1 tests do not
reject them.

It contains the cut edges of `T₀` (`inter_treeOfBlobs_subset_limitTree`). When it has others, Remark
8.4 of the paper fails (`Counterexample.not_remark8_4`). -/
def limitTree (N : RootedNetwork V E X) (T₀ : Finset (Finset X)) : Finset (Finset X) :=
  T₀.filter fun A => ¬ (2 ≤ A.card ∧ 2 ≤ Aᶜ.card) ∨
    ((∃ s ∈ multipartitionQuartets T₀ A, ¬ HasTrivialFourBlob N s.taxa) ∧
      ∀ s ∈ bipartitionQuartets A, IsNullQuartet N s)

theorem mem_limitTree {T₀ : Finset (Finset X)} {A : Finset X} :
    A ∈ limitTree N T₀ ↔ A ∈ T₀ ∧ (¬ (2 ≤ A.card ∧ 2 ≤ Aᶜ.card) ∨
      ((∃ s ∈ multipartitionQuartets T₀ A, ¬ HasTrivialFourBlob N s.taxa) ∧
        ∀ s ∈ bipartitionQuartets A, IsNullQuartet N s)) := by
  simp [limitTree]

theorem limitTree_subset (T₀ : Finset (Finset X)) : limitTree N T₀ ⊆ T₀ := Finset.filter_subset _ _

theorem compl_mem_of_isUnrootedTree {T : Finset (Finset X)} (hT : IsUnrootedTree T) {A : Finset X}
    (hA : A ∈ T) : Aᶜ ∈ T := by
  obtain ⟨H, _, rfl⟩ := hT
  simp only [unroot, mem_union, mem_erase, mem_image] at hA ⊢
  rcases hA with ⟨hAu, hAH⟩ | ⟨B, ⟨hBu, hBH⟩, rfl⟩
  · exact Or.inr ⟨A, ⟨hAu, hAH⟩, rfl⟩
  · rw [compl_compl]
    exact Or.inl ⟨hBu, hBH⟩

theorem compl_mem_limitTree {T₀ : Finset (Finset X)} (hT₀ : IsUnrootedTree T₀) {A : Finset X}
    (hA : A ∈ limitTree N T₀) : Aᶜ ∈ limitTree N T₀ := by
  obtain ⟨h₁, h₂⟩ := mem_limitTree.1 hA
  refine mem_limitTree.2 ⟨compl_mem_of_isUnrootedTree hT₀ h₁, ?_⟩
  rw [multipartitionQuartets_compl, bipartitionQuartets_compl, compl_compl]
  rcases h₂ with h | h
  · exact Or.inl fun h' => h ⟨h'.2, h'.1⟩
  · exact Or.inr h

/-- The split family of an unrooted tree with an internal side. -/
theorem isSplitFamily_of_internal {T : Finset (Finset X)} (hT : IsUnrootedTree T) {A : Finset X}
    (hA : 2 ≤ A.card) : IsSplitFamily T :=
  (isUnrootedTree_iff (hA.trans (Finset.card_le_univ A)) T).1 hT

/-- A run of the algorithm on a table `c` on which every test comes out right: as
`Deterministic.Run`, for an arbitrary tree `T₀`, and for any p-values `f` of the quartets whose tests
have the null hypothesis `Null`, which must be the T1 null of the network. -/
structure CoarseRun (N : RootedNetwork V E X) (p f : QuartetTree X → ℝ)
    (Null : QuartetTree X → Prop) (T₀ : Finset (Finset X)) (o : ECToBlobOptions) (α β : ℝ)
    (c : QuartetTree X → ℝ) : Prop where
  phylo : N.IsPhylogenetic
  isTree : IsUnrootedTree T₀
  null_iff : ∀ s, Null s ↔ IsNullQuartet N s
  uniform_iff : ∀ s : QuartetTree X, IsUniformOn p s.taxa ↔ HasTrivialFourBlob N s.taxa
  star : ∀ A ∈ internalSides T₀, TestCorrect (fun s => IsUniformOn p s.taxa)
    (multipartitionQuartets T₀ A) β (edgeStarP o c T₀ A)
  edge : ∀ T ⊆ T₀, ∀ A ∈ internalSides T, TestCorrect Null (edgeQuartets o T₀ T A) α
    (edgeTestP o f T₀ T A)
  tree : ∀ T ⊆ T₀, TestCorrect Null (univ.filter fun s => Displays T s) α (treeTestP o f T)

section RunLemmas

variable {p f : QuartetTree X → ℝ} {Null : QuartetTree X → Prop} {T₀ : Finset (Finset X)}
  {o : ECToBlobOptions} {α β : ℝ} {c : QuartetTree X → ℝ}

/-- An edge in the limit survives Step 3. -/
theorem CoarseRun.limitTree_subset_afterStar (R : CoarseRun N p f Null T₀ o α β c) :
    limitTree N T₀ ⊆ afterStar o β c T₀ := by
  have key : ∀ A ∈ limitTree N T₀,
      A ∉ (internalSides T₀).filter fun A => β < edgeStarP o c T₀ A := by
    intro A hA hmem
    obtain ⟨hint, hβ⟩ := mem_filter.1 hmem
    obtain ⟨_, h₂⟩ := mem_internalSides.1 hint
    rcases (mem_limitTree.1 hA).2 with h | ⟨⟨s, hs, hn⟩, _⟩
    · exact h h₂
    · exact absurd hβ (not_lt_of_gt ((R.star A hint).2 ⟨s, hs, fun hu => hn ((R.uniform_iff s).1 hu)⟩))
  intro A hA
  exact mem_contractSides.2 ⟨limitTree_subset T₀ hA, key A hA, key _ (compl_mem_limitTree R.isTree hA)⟩

/-- An edge off the limit that survives Step 3 has a quartet of the bipartition off the T1 null. -/
theorem CoarseRun.exists_not_null_bipartition (R : CoarseRun N p f Null T₀ o α β c) {A : Finset X}
    (hA : A ∈ afterStar o β c T₀) (h₂ : 2 ≤ A.card ∧ 2 ≤ Aᶜ.card) (hAL : A ∉ limitTree N T₀) :
    ∃ s ∈ bipartitionQuartets A, ¬ IsNullQuartet N s := by
  obtain ⟨hAT₀, hnot, _⟩ := mem_contractSides.1 hA
  have hint : A ∈ internalSides T₀ := mem_internalSides.2 ⟨hAT₀, h₂⟩
  by_contra hcon
  push Not at hcon
  refine hAL (mem_limitTree.2 ⟨hAT₀, Or.inr ⟨?_, hcon⟩⟩)
  by_contra hall
  push Not at hall
  exact hnot (mem_filter.2 ⟨hint, (R.star A hint).1 fun s hs => (R.uniform_iff s).2 (hall s hs)⟩)

/-- An edge off the limit that survives Step 3 has a quartet of the chosen type off the T1 null,
whichever the type and the stage: the types agree on the T1 null
(`forall_bipartition_of_forall_multipartition`), and the multipartition of `T₀` is in all of them. -/
theorem CoarseRun.exists_not_null_edgeQuartets (R : CoarseRun N p f Null T₀ o α β c)
    {T : Finset (Finset X)} (hT : T ⊆ T₀) {A : Finset X} (hA : A ∈ afterStar o β c T₀)
    (h₂ : 2 ≤ A.card ∧ 2 ≤ Aᶜ.card) (hAL : A ∉ limitTree N T₀) :
    ∃ s ∈ edgeQuartets o T₀ T A, ¬ Null s := by
  obtain ⟨s₀, hs₀, hn₀⟩ := R.exists_not_null_bipartition hA h₂ hAL
  by_contra hcon
  push Not at hcon
  refine hn₀ (forall_bipartition_of_forall_multipartition R.phylo
    (isSplitFamily_of_internal R.isTree h₂.1) h₂.1 h₂.2 (fun s hs => ?_) s₀ hs₀)
  exact (R.null_iff s).1 (hcon s (multipartitionQuartets_subset_edgeQuartets hT A hs))

theorem CoarseRun.isLimit (R : CoarseRun N p f Null T₀ o α β c) :
    IsLimit α (edgeTestP o f T₀) (treeTestP o f) (afterStar o β c T₀) (limitTree N T₀) := by
  have hsub : afterStar o β c T₀ ⊆ T₀ := afterStar_subset
  refine ⟨R.limitTree_subset_afterStar, fun A hA => compl_mem_limitTree R.isTree hA, ?_, ?_, ?_, ?_,
    ?_, ?_⟩
  · intro A hA h
    exact mem_limitTree.2 ⟨hsub hA, Or.inl h⟩
  · intro A hA
    obtain ⟨_, h₂⟩ := mem_internalSides.1 hA
    exact isSplitFamily_afterStar (isSplitFamily_of_internal R.isTree h₂.1)
  · intro T hT A hAi hA
    refine (R.edge T (hT.trans hsub) A hAi).1 fun s hs => (R.null_iff s).2 ?_
    obtain ⟨_, h₂⟩ := mem_internalSides.1 hAi
    rcases (mem_limitTree.1 hA).2 with h | ⟨_, h⟩
    · exact absurd h₂ h
    · exact h s (mem_filter.2 ⟨mem_univ _, mem_of_mem_edgeQuartets hs⟩)
  · intro T hT _ A hAi hA
    obtain ⟨hAT, h₂⟩ := mem_internalSides.1 hAi
    exact (R.edge T (hT.trans hsub) A hAi).2 (R.exists_not_null_edgeQuartets (hT.trans hsub)
      (hT hAT) h₂ hA)
  · intro T hT
    refine (R.tree T (hT.trans (limitTree_subset T₀))).1 fun s hs => (R.null_iff s).2 ?_
    obtain ⟨A, hA, hAs⟩ := (mem_filter.1 hs).2
    rcases (mem_limitTree.1 (hT hA)).2 with h | ⟨_, h⟩
    · exact absurd (two_le_card_of_inter_taxa_mem hAs) h
    · exact h s (mem_filter.2 ⟨mem_univ _, hAs⟩)
  · intro T hT A hAi hA
    obtain ⟨hAT, h₂⟩ := mem_internalSides.1 hAi
    obtain ⟨s, hs, hn⟩ := R.exists_not_null_bipartition (hT hAT) h₂ hA
    exact (R.tree T (hT.trans hsub)).2 ⟨s, mem_filter.2 ⟨mem_univ _, A, hAT, (mem_filter.1 hs).2⟩,
      fun h => hn ((R.null_iff s).1 h)⟩

/-- On a table on which every test comes out right, the algorithm outputs the limit tree, whichever
the quartet type and the selection rule. -/
theorem CoarseRun.outputBy_eq (R : CoarseRun N p f Null T₀ o α β c) :
    outputBy o.rule α (edgeTestP o f T₀) (treeTestP o f) (afterStar o β c T₀) = limitTree N T₀ :=
  R.isLimit.outputBy_eq o.rule

end RunLemmas

/-! #### The T1 null of the concordance factors -/

/-- By both directions of Assumption 1, the T1 null at a quartet tree holds exactly when the quartet
tree is a cut split of the induced network, or this network has a trivial 4-blob. -/
theorem t1Null_iff {p : QuartetTree X → ℝ} (h₁ : Assumption1Forward N p)
    (h₂ : Assumption1Converse N p) (hsum : ∀ s : QuartetTree X, ∑ r ∈ treesOn s.taxa, p r = 1)
    (s : QuartetTree X) : T1Null p s ↔ IsNullQuartet N s := by
  constructor
  · intro hn
    by_contra hcon
    unfold IsNullQuartet at hcon
    push Not at hcon
    exact not_t1Null (hsum s) (h₂.t1 s hcon.1) (h₂.star _ s.card_taxa hcon.2) hn
  · rintro (h | h)
    · exact T1Null_of_strict (h₁.t1 s h)
    · have hu := h₁.star _ s.card_taxa h
      have hmem : ∀ r ∈ s.alternatives, r ∈ treesOn s.taxa := fun r hr => by
        simpa [treesOn] using (mem_filter.1 hr).2.1
      refine ⟨fun r hr => ?_, fun r hr r' hr' => ?_⟩
      · rw [hu r (hmem r hr), hu s (mem_treesOn_taxa s)]
      · rw [hu r (hmem r hr), hu r' (hmem r' hr')]

/-- By both directions of Assumption 1, a set of four taxa has uniform concordance factors exactly
when it has a trivial 4-blob. -/
theorem uniform_iff {p : QuartetTree X → ℝ} (h₁ : Assumption1Forward N p)
    (h₂ : Assumption1Converse N p) (s : QuartetTree X) :
    IsUniformOn p s.taxa ↔ HasTrivialFourBlob N s.taxa :=
  ⟨fun hu => by
    by_contra hn
    exact h₂.star _ s.card_taxa hn hu, h₁.star _ s.card_taxa⟩

/-! #### The theorem -/

section Consistency

variable {V E X : Type*} [Fintype X] [DecidableEq X] {dist : BinaryGeneTree X → ℝ}

/-- All the tests of the algorithm come out right, on an arbitrary tree `T₀`, with probability
`> 1 - ε` for large `n`: the proof of Theorem 8.2 does not use that `T₀` is a resolution, up to the
end, which is deterministic. -/
theorem eventually_tests_correct (hd : IsDist dist) (o : ECToBlobOptions)
    (hpos : (o.testCo = .cauchy ∨ o.testCo = .cbc) →
      ∀ s, IsT1Strict (displayCF dist Subtype.val) s →
        ∀ r ∈ s.alternatives, 0 < displayCF dist Subtype.val r)
    {T₀ : Finset (Finset X)} (hT₀ : IsUnrootedTree T₀) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, 1 - ε < iidProb dist n fun ω =>
      (∀ A ∈ internalSides T₀, TestCorrect
        (fun s => IsUniformOn (displayCF dist Subtype.val) s.taxa) (multipartitionQuartets T₀ A)
        (betaSeq n) (edgeStarP o (quartetCount Subtype.val ω) T₀ A)) ∧
      (∀ T ⊆ T₀, ∀ A ∈ internalSides T, TestCorrect (T1Null (displayCF dist Subtype.val))
        (edgeQuartets o T₀ T A) (alphaSeq n) (edgeT1P o (quartetCount Subtype.val ω) T₀ T A)) ∧
      ∀ T ⊆ T₀, TestCorrect (T1Null (displayCF dist Subtype.val))
        (univ.filter fun s => Displays T s) (alphaSeq n)
        (treeT1P o (quartetCount Subtype.val ω) T) := by
  have hS := eventually_forall_mem hd (internalSides T₀)
    (fun A n ω => TestCorrect
      (fun s => IsUniformOn (displayCF dist Subtype.val) s.taxa) (multipartitionQuartets T₀ A)
      (betaSeq n) (edgeStarP o (quartetCount Subtype.val ω) T₀ A))
    (half_pos hε) fun A hA _ hε' => eventually_star_correct hd o.starTest o.testCo _
      (card_multipartitionQuartets_le hT₀ (Finset.mem_filter.1 hA).1) hε'
  have hT := eventually_t1_all hd o hpos hT₀ (half_pos hε)
  filter_upwards [hS, hT] with n hnS hnT
  exact iidProb_and_gt hd n _ _ hnS hnT

/-- With high probability, the algorithm outputs the limit tree. -/
theorem eventually_ectoblob_eq_limitTree {N : RootedNetwork V E X} (hN : N.IsPhylogenetic)
    (hd : IsDist dist) (h₁ : Assumption1Forward N (displayCF dist Subtype.val))
    (h₂ : Assumption1Converse N (displayCF dist Subtype.val)) (o : ECToBlobOptions)
    (hpos : (o.testCo = .cauchy ∨ o.testCo = .cbc) →
      ∀ s, IsT1Strict (displayCF dist Subtype.val) s →
        ∀ r ∈ s.alternatives, 0 < displayCF dist Subtype.val r)
    {T₀ : Finset (Finset X)} (hT₀ : IsUnrootedTree T₀) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, 1 - ε < iidProb dist n fun ω =>
      ectoblob o (alphaSeq n) (betaSeq n) (quartetCount Subtype.val ω) T₀ = limitTree N T₀ := by
  filter_upwards [eventually_tests_correct hd o hpos hT₀ hε] with n hn
  refine hn.trans_le (iidProb_mono hd fun ω hω => ?_)
  have R : CoarseRun N (displayCF dist Subtype.val)
      (t1PValue (quartetCount Subtype.val ω)) (T1Null (displayCF dist Subtype.val)) T₀ o
      (alphaSeq n) (betaSeq n) (quartetCount Subtype.val ω) :=
    ⟨hN, hT₀, t1Null_iff h₁ h₂ fun s => sum_displayCF_binaryGeneTree hd s.card_taxa,
      uniform_iff h₁ h₂, hω.1, hω.2.1, hω.2.2⟩
  exact R.outputBy_eq

/-- **The limit of ECToBlob on an arbitrary tree.** For any network, any unrooted tree `T₀`, any
variant of the algorithm, and any distribution of binary gene trees whose concordance factors satisfy
both directions of Assumption 1, the output tends in probability to `limitTree N T₀`. The sequences
are those of Theorem 8.2. -/
theorem tendsto_ectoblob_limitTree (N : RootedNetwork V E X) (hN : N.IsPhylogenetic)
    (dist : BinaryGeneTree X → ℝ) (hd : IsDist dist)
    (h₁ : Assumption1Forward N (displayCF dist Subtype.val))
    (h₂ : Assumption1Converse N (displayCF dist Subtype.val)) (T₀ : Finset (Finset X))
    (hT₀ : IsUnrootedTree T₀) (o : ECToBlobOptions)
    (hpos : (o.testCo = .cauchy ∨ o.testCo = .cbc) →
      ∀ s, IsT1Strict (displayCF dist Subtype.val) s →
        ∀ r ∈ s.alternatives, 0 < displayCF dist Subtype.val r) :
    Tendsto (fun n => iidProb dist n fun ω =>
      ectoblob o (alphaSeq n) (betaSeq n) (quartetCount Subtype.val ω) T₀ = limitTree N T₀)
      atTop (𝓝 1) := by
  refine tendsto_order.2 ⟨fun a ha => ?_, fun a ha => ?_⟩
  · filter_upwards [eventually_ectoblob_eq_limitTree hN hd h₁ h₂ o hpos hT₀ (ε := 1 - a)
      (by linarith)] with n hn
    linarith
  · exact Eventually.of_forall fun n => (iidProb_le_one hd n _).trans_lt ha

/-- If the limit tree is not `G`, then the output is `G` with probability tending to zero. -/
theorem tendsto_ectoblob_zero (N : RootedNetwork V E X) (hN : N.IsPhylogenetic)
    (dist : BinaryGeneTree X → ℝ) (hd : IsDist dist)
    (h₁ : Assumption1Forward N (displayCF dist Subtype.val))
    (h₂ : Assumption1Converse N (displayCF dist Subtype.val)) (T₀ : Finset (Finset X))
    (hT₀ : IsUnrootedTree T₀) (o : ECToBlobOptions)
    (hpos : (o.testCo = .cauchy ∨ o.testCo = .cbc) →
      ∀ s, IsT1Strict (displayCF dist Subtype.val) s →
        ∀ r ∈ s.alternatives, 0 < displayCF dist Subtype.val r)
    {G : Finset (Finset X)} (hG : limitTree N T₀ ≠ G) :
    Tendsto (fun n => iidProb dist n fun ω =>
      ectoblob o (alphaSeq n) (betaSeq n) (quartetCount Subtype.val ω) T₀ = G) atTop (𝓝 0) := by
  have hlim := (tendsto_const_nhds (x := (1 : ℝ))).sub (tendsto_ectoblob_limitTree N hN dist hd h₁ h₂
    T₀ hT₀ o hpos)
  rw [sub_self] at hlim
  refine squeeze_zero (fun n => iidProb_nonneg hd n _) (fun n => ?_) hlim
  rw [← iidProb_not hd]
  refine iidProb_mono hd fun ω hω hL => hG ?_
  rw [← hL]
  exact hω

end Consistency

/-! ### Part 4: what the limit tree is -/

section Properties

variable {T₀ : Finset (Finset X)}

/-- A cut split of an induced network, in the language of domination. -/
theorem exists_rdom_of_inducedCutSplit (hN : N.IsPhylogenetic) {s : QuartetTree X}
    (h : InducedCutSplit N s) :
    ∃ (a b c d : X) (hc : ({a, b, c, d} : Finset X).card = 4), s = quartetTree a b c d hc ∧
      RDom N a b c d := by
  obtain ⟨B, hB, hcut⟩ := id h
  have hmem : s ∈ bipartitionQuartets B := by
    refine mem_filter.2 ⟨mem_univ _, ?_⟩
    rwa [Finset.inter_eq_left.2 (s.subset_taxa hB)]
  obtain ⟨a, b, c, d, hc, rfl, ha, hb, hc', hd, hab, hcd⟩ :=
    exists_tuple (mem_multipartitionQuartets_empty hmem)
  obtain ⟨_, hac, had, hbc, hbd, _⟩ := ne_of_card_four hc
  exact ⟨a, b, c, d, hc, rfl,
    rdom_of_hasCutSplitOn hN hac had hbc hbd (hasCutSplitOn_of_inducedCutSplit hc h)⟩

/-- A cut split of an induced network excludes a trivial 4-blob. -/
theorem not_hasTrivialFourBlob_of_inducedCutSplit (hN : N.IsPhylogenetic) {s : QuartetTree X}
    (h : InducedCutSplit N s) : ¬ HasTrivialFourBlob N s.taxa := by
  obtain ⟨a, b, c, d, hc, rfl, hr⟩ := exists_rdom_of_inducedCutSplit hN h
  obtain ⟨hab, hac, had, hbc, _, hcd⟩ := ne_of_card_four hc
  rw [taxa_quartetTree]
  intro htr
  obtain ⟨v, hv⟩ := exists_isHub hN (by omega) htr
  exact not_isHub_of_rdom hN hab hac had hbc hcd hv hr

/-- **The cut edges of `T₀` remain.** Step 3 does not contract them, since their quartets are not
uniform, and the T1 tests do not reject them. This holds for every network. -/
theorem inter_treeOfBlobs_subset_limitTree (hN : N.IsPhylogenetic) (hT₀ : IsUnrootedTree T₀) :
    T₀ ∩ treeOfBlobs N ⊆ limitTree N T₀ := by
  intro A hA
  obtain ⟨hAT₀, hAB⟩ := mem_inter.1 hA
  refine mem_limitTree.2 ⟨hAT₀, ?_⟩
  by_cases h₂ : 2 ≤ A.card ∧ 2 ≤ Aᶜ.card
  · refine Or.inr ⟨?_, fun s hs => Or.inl (inducedCutSplit_of_mem hN hAB (mem_filter.1 hs).2)⟩
    obtain ⟨s, hs⟩ := exists_mem_multipartitionQuartets (isSplitFamily_of_internal hT₀ h₂.1) h₂.1 h₂.2
    exact ⟨s, hs, not_hasTrivialFourBlob_of_inducedCutSplit hN
      (inducedCutSplit_of_mem hN hAB (mem_filter.1 (mem_filter.1 hs).1).2)⟩
  · exact Or.inl h₂

/-- A side with all quartets under the T1 null is compatible with each cut side. -/
theorem compatible_of_forall_null (hN : N.IsPhylogenetic) {A D : Finset X}
    (hall : ∀ s ∈ bipartitionQuartets A, IsNullQuartet N s) (hD : D ∈ treeOfBlobs N) :
    A ⊆ D ∨ D ⊆ A ∨ Disjoint A D ∨ A ∪ D = univ := by
  by_contra hcon
  push Not at hcon
  obtain ⟨h₁, h₂, h₃, h₄⟩ := hcon
  obtain ⟨q, hqA, hqD⟩ := Finset.not_subset.1 h₁
  obtain ⟨r, hrD, hrA⟩ := Finset.not_subset.1 h₂
  obtain ⟨p, hpA, hpD⟩ := Finset.not_disjoint_iff.1 h₃
  obtain ⟨t, ht⟩ : ∃ t, t ∉ A ∪ D := by
    by_contra hall'
    push Not at hall'
    exact h₄ (Finset.eq_univ_iff_forall.2 hall')
  obtain ⟨htA, htD⟩ : t ∉ A ∧ t ∉ D := by simpa using ht
  have hpq : p ≠ q := fun h => hqD (h ▸ hpD)
  have hpr : p ≠ r := fun h => hrA (h ▸ hpA)
  have hpt : p ≠ t := fun h => htA (h ▸ hpA)
  have hqr : q ≠ r := fun h => hrA (h ▸ hqA)
  have hqt : q ≠ t := fun h => htA (h ▸ hqA)
  have hrt : r ≠ t := fun h => htD (h ▸ hrD)
  have hc := card_four_of_ne hpq hpr hpt hqr hqt hrt
  have hc' := card_four_of_ne hpr hpq hpt hqr.symm hrt hqt
  -- the quartet of `A` is under the T1 null
  have hmem : quartetTree p q r t hc ∈ bipartitionQuartets A := by
    refine mem_filter.2 ⟨mem_univ _, ?_⟩
    rw [taxa_quartetTree, inter_four hpA hqA hrA htA]
    simp [quartetTree]
  have hnull := (isNullQuartet_quartetTree_iff hN hc).1 (hall _ hmem)
  -- the cut side `D` gives another split on it
  have hrd : RDom N p r q t := by
    have : InducedCutSplit N (quartetTree p r q t hc') := inducedCutSplit_of_mem hN hD (by
      rw [taxa_quartetTree, inter_four hpD hrD hqD htD]
      simp [quartetTree])
    exact rdom_of_hasCutSplitOn hN hpq hpt hqr.symm hrt (hasCutSplitOn_of_inducedCutSplit hc' this)
  rcases hnull with htr | hrd'
  · have hset : ({p, q, r, t} : Finset X) = {p, r, q, t} := by
      ext z
      simp only [mem_insert, mem_singleton]
      tauto
    rw [hset] at htr
    obtain ⟨v, hv⟩ := exists_isHub hN (by omega) htr
    exact not_isHub_of_rdom hN hpr hpq hpt hqr.symm hqt hv hrd
  · exact not_rdom_of_rdom hN hrd' hrd

/-- **The output is compatible with the tree of blobs.** Whatever the network, each edge of the limit
tree is compatible with each cut edge: the false edges in it refine multifurcations of the tree of
blobs. -/
theorem limitTree_compatible (hN : N.IsPhylogenetic) (hT₀ : IsUnrootedTree T₀) {A D : Finset X}
    (hA : A ∈ limitTree N T₀) (hD : D ∈ treeOfBlobs N) :
    A ⊆ D ∨ D ⊆ A ∨ Disjoint A D ∨ A ∪ D = univ := by
  obtain ⟨hAT₀, h⟩ := mem_limitTree.1 hA
  rcases h with h | ⟨_, h⟩
  · have hne := nonempty_of_mem_tree hT₀ hAT₀
    have hc₁ : 0 < A.card := Finset.card_pos.2 hne.1
    have hc₂ : 0 < Aᶜ.card := Finset.card_pos.2 hne.2
    by_cases hc : A.card = 1
    · obtain ⟨x, rfl⟩ := Finset.card_eq_one.1 hc
      by_cases hx : x ∈ D
      · exact Or.inl (Finset.singleton_subset_iff.2 hx)
      · exact Or.inr (Or.inr (Or.inl (Finset.disjoint_singleton_left.2 hx)))
    · have hc' : Aᶜ.card = 1 := by omega
      obtain ⟨x, hx⟩ := Finset.card_eq_one.1 hc'
      by_cases hxD : x ∈ D
      · refine Or.inr (Or.inr (Or.inr ?_))
        rw [Finset.eq_univ_iff_forall]
        intro z
        by_cases hzA : z ∈ A
        · exact mem_union_left _ hzA
        · have : z ∈ Aᶜ := mem_compl.2 hzA
          rw [hx, mem_singleton] at this
          exact mem_union_right _ (this ▸ hxD)
      · refine Or.inr (Or.inl fun z hz => ?_)
        by_contra hzA
        have : z ∈ Aᶜ := mem_compl.2 hzA
        rw [hx, mem_singleton] at this
        exact hxD (this ▸ hz)
  · exact compatible_of_forall_null hN h hD

/-- The exact condition for Remark 8.4 on the pair `N`, `T₀`: each false edge of `T₀` is contracted
by Step 3, since all its quartets of the multipartition have trivial 4-blobs, or it is rejected by the
T1 tests, since it has a quartet off the T1 null. -/
theorem limitTree_eq_inter_iff (hN : N.IsPhylogenetic) (hT₀ : IsUnrootedTree T₀) :
    limitTree N T₀ = T₀ ∩ treeOfBlobs N ↔ ∀ A ∈ internalSides T₀, A ∉ treeOfBlobs N →
      (∀ s ∈ multipartitionQuartets T₀ A, HasTrivialFourBlob N s.taxa) ∨
        ∃ s ∈ bipartitionQuartets A, ¬ IsNullQuartet N s := by
  constructor
  · intro h A hA hAB
    obtain ⟨hAT₀, h₂⟩ := mem_internalSides.1 hA
    by_contra hcon
    push Not at hcon
    obtain ⟨⟨s, hs, hn⟩, hall⟩ := hcon
    have hmem : A ∈ limitTree N T₀ := mem_limitTree.2 ⟨hAT₀, Or.inr ⟨⟨s, hs, hn⟩, hall⟩⟩
    rw [h] at hmem
    exact hAB (mem_inter.1 hmem).2
  · intro h
    refine Finset.Subset.antisymm (fun A hA => ?_) (inter_treeOfBlobs_subset_limitTree hN hT₀)
    obtain ⟨hAT₀, hor⟩ := mem_limitTree.1 hA
    refine mem_inter.2 ⟨hAT₀, ?_⟩
    by_contra hAB
    rcases hor with h₂ | ⟨⟨s, hs, hn⟩, hall⟩
    · have hne := nonempty_of_mem_tree hT₀ hAT₀
      exact hAB (mem_treeOfBlobs_of_not_internal hN hne.1 hne.2 h₂)
    · have h₂ : 2 ≤ A.card ∧ 2 ≤ Aᶜ.card := two_le_card_of_inter_taxa_mem (mem_filter.1 (mem_filter.1 hs).1).2
      rcases h A (mem_internalSides.2 ⟨hAT₀, h₂⟩) hAB with h₁ | ⟨s', hs', hn'⟩
      · exact hn (h₁ s hs)
      · exact hn' (hall s' hs')

/-- A network with no trivial 4-blob has the limit tree of Remark 8.4. -/
theorem limitTree_eq_inter_of_noTrivial (hN : N.IsPhylogenetic) (hT₀ : IsUnrootedTree T₀)
    (hno : ∀ q : Finset X, q.card = 4 → ¬ HasTrivialFourBlob N q) :
    limitTree N T₀ = T₀ ∩ treeOfBlobs N := by
  refine (limitTree_eq_inter_iff hN hT₀).2 fun A hA hAB => Or.inr ?_
  obtain ⟨_, h₂, h₂'⟩ := mem_internalSides.1 hA
  obtain ⟨s, hs, hn⟩ := exists_not_inducedCutSplit_bipartition hN h₂ h₂'
    (not_hasCutSplit_of_notMem h₂ h₂' hAB)
  exact ⟨s, hs, fun h => h.elim hn (hno _ s.card_taxa)⟩

/-- On a resolution of the tree of blobs, the limit tree is the tree of blobs: this is the case of
Theorem 8.2, by the repair of E12. -/
theorem limitTree_eq_treeOfBlobs (hN : N.IsPhylogenetic) (hT₀ : IsResolutionOf T₀ (treeOfBlobs N)) :
    limitTree N T₀ = treeOfBlobs N := by
  have h := (limitTree_eq_inter_iff hN hT₀.1).2 fun A hA hAB => by
    by_cases hall : ∀ s ∈ multipartitionQuartets T₀ A, HasTrivialFourBlob N s.taxa
    · exact Or.inl hall
    · push Not at hall
      obtain ⟨s, hs, hn₁, hn₂⟩ := falseEdge_witness hN hT₀ hA hAB hall
      exact Or.inr ⟨s, (mem_filter.1 hs).1, fun h => h.elim hn₁ hn₂⟩
  rw [h, Finset.inter_eq_right.2 hT₀.2]


/-- Two adjacent quartets under the T1 null, one with a trivial 4-blob and one with a cut split, come
from a cut side: this is the argument of `FalseEdge.false_of_adjacent`, which ends there, since on a
resolution the cut side is an edge of the tree, grouping taxa that lie in distinct blocks. -/
theorem exists_cut_side_of_adjacent (hN : N.IsPhylogenetic) {T : Finset (Finset X)}
    (hT : IsSplitFamily T) {P : Finset X}
    (hall : ∀ x₁ x₂ x₃ x₄, x₁ ∉ P → x₂ ∉ P → x₃ ∈ P → x₄ ∈ P → Sep T Pᶜ x₁ x₂ → Sep T P x₃ x₄ →
      HasTrivialFourBlob N {x₁, x₂, x₃, x₄} ∨ RDom N x₁ x₂ x₃ x₄)
    {a b c d d' : X} (ha : a ∉ P) (hb : b ∉ P) (hc : c ∈ P) (hd : d ∈ P)
    (hab : Sep T Pᶜ a b) (hcd : Sep T P c d)
    (htr : HasTrivialFourBlob N {a, b, c, d}) (hr : RDom N a b c d') :
    ∃ Z ∈ treeOfBlobs N, c ∈ Z ∧ d' ∈ Z ∧ a ∉ Z ∧ d ∉ Z := by
  have hP : P ≠ univ := by
    rintro rfl
    exact ha (mem_univ a)
  have hP' : Pᶜ ≠ univ := by
    intro h
    exact (mem_compl.1 (h ▸ mem_univ c)) hc
  have hac : a ≠ c := fun h => ha (h ▸ hc)
  have had : a ≠ d := fun h => ha (h ▸ hd)
  have hbc : b ≠ c := fun h => hb (h ▸ hc)
  have hbd : b ≠ d := fun h => hb (h ▸ hd)
  have hcard := card_four_of_ne hab.1 hac had hbc hbd hcd.1
  have ma : a ∈ ({a, b, c, d} : Finset X) := by simp
  have mb : b ∈ ({a, b, c, d} : Finset X) := by simp
  have mc : c ∈ ({a, b, c, d} : Finset X) := by simp
  have md : d ∈ ({a, b, c, d} : Finset X) := by simp
  obtain ⟨v, hv⟩ := exists_isHub hN (by omega) htr
  obtain ⟨e, he | he⟩ := hv c mc
  · -- the bridge towards `c` leaves the hub, and dominates `d'`
    have hed' : N.Dominates e d' := by
      obtain ⟨g, ⟨g₁, g₂, g₃, _⟩ | ⟨g₁, g₂, g₃, g₄⟩⟩ := hr
      · exact absurd (he.isBelow_of_reaches hN
          (reaches_hub_of_dominates hN hv ma mb mc hab.1 hac hbc g₁ g₂)) g₃
      · rcases dominates_comparable hN he.2.1 g₁ with h | h | h
        · subst h
          exact g₂
        · exact dominates_of_above hN h he.2.1 g₁ g₂
        · exact absurd (he.1 ▸ h) (not_reaches_hub hN hv ma mb mc hab.1 hac hbc g₃ g₄)
    by_cases hall' : ∀ x, N.IsBelow e x → N.Dominates e x
    · have hcb := isBelow_of_dominates hN he.2.1
      refine ⟨univ.filter fun x => N.IsBelow e x, mem_filter.2 ⟨mem_univ _, ⟨c, by simp [hcb]⟩,
        ⟨a, by simp [he.2.2 a ma hac]⟩, hasCutSplit_below hN hall' hcb⟩, by simp [hcb],
        by simp [isBelow_of_dominates hN hed'], by simp [he.2.2 a ma hac],
        by simp [he.2.2 d md hcd.1.symm]⟩
    · push Not at hall'
      obtain ⟨w, hwb, hwd⟩ := hall'
      have hne : ∀ y ∈ ({a, b, c, d} : Finset X), w ≠ y := by
        rintro _ hy rfl
        by_cases hyc : w = c
        · subst hyc
          exact hwd he.2.1
        · exact he.2.2 w hy hyc hwb
      exact (false_of_isStray hN hT hP hP' hall ha hb hc hd hab hcd hv (hne a ma) (hne b mb)
        (hne c mc) (hne d md) (isStray_of_leaves hN he hwb hwd)).elim
  · -- the bridge towards `c` enters the hub, and `d'` is not below it
    have hvd' : N.graph.target e = v := he.1
    have hed' : ¬ N.IsBelow e d' := by
      intro hb'
      have hvb : N.graph.Reaches v (N.leaf d') := by
        rw [← hvd']; exact hb'
      obtain ⟨g, ⟨g₁, g₂, _, g₄⟩ | ⟨g₁, g₂, g₃, g₄⟩⟩ := hr
      · exact g₄ ((reaches_hub_of_dominates hN hv ma mb mc hab.1 hac hbc g₁ g₂).trans hvb)
      · have hng := not_reaches_hub hN hv ma mb mc hab.1 hac hbc g₃ g₄
        have hvg := reaches_source_of_dominates hN hng hvb g₂
        refine he.2.2 ?_
        show N.graph.Reaches _ _
        rw [hvd']
        exact hvg.trans ((reaches_arc g).trans (isBelow_of_dominates hN g₁))
    by_cases hall' : ∀ x, N.IsBelow e x → N.Dominates e x
    · have hab' := isBelow_of_dominates hN (he.2.1 a ma hac)
      have hdb' := isBelow_of_dominates hN (he.2.1 d md hcd.1.symm)
      have hmem : (univ.filter fun x => N.IsBelow e x) ∈ treeOfBlobs N := mem_filter.2 ⟨mem_univ _,
        ⟨a, by simp [hab']⟩, ⟨c, by simp [he.2.2]⟩, hasCutSplit_below hN hall' hab'⟩
      exact ⟨_, compl_mem_treeOfBlobs hmem, by simp [he.2.2], by simp [hed'], by simp [hab'],
        by simp [hdb']⟩
    · push Not at hall'
      obtain ⟨w, hwb, hwd⟩ := hall'
      have hne : ∀ y ∈ ({a, b, c, d} : Finset X), w ≠ y := by
        rintro _ hy rfl
        by_cases hyc : w = c
        · subst hyc
          exact he.2.2 hwb
        · exact hwd (he.2.1 w hy hyc)
      exact (false_of_isStray hN hT hP hP' hall ha hb hc hd hab hcd hv (hne a ma) (hne b mb)
        (hne c mc) (hne d md)
        (isStray_of_enters hN hv ma mb hac hbc.symm.symm hab.1.symm he hwb hwd)).elim

/-- **What a false edge in the limit requires.** If the limit tree has an edge that is not a cut edge,
then `T₀` misses a cut edge: one side of the false edge properly contains a cut side `D` of the
network, two taxa of which lie in distinct blocks of `T₀` at that side. So `D` is not a side of `T₀`.

The proof is that of `falseEdge_witness`, which ends at the cut side found here. -/
theorem exists_missed_cut_of_mem_limitTree (hN : N.IsPhylogenetic) (hT₀ : IsUnrootedTree T₀)
    {A : Finset X} (hA : A ∈ limitTree N T₀) (hAB : A ∉ treeOfBlobs N) :
    ∃ P, (P = A ∨ P = Aᶜ) ∧ ∃ D ∈ treeOfBlobs N, D ⊂ P ∧ ∃ x ∈ D, ∃ y ∈ D, Sep T₀ P x y := by
  obtain ⟨hAT₀, hor⟩ := mem_limitTree.1 hA
  have hne := nonempty_of_mem_tree hT₀ hAT₀
  rcases hor with h₂ | ⟨⟨s, hs, hns⟩, hnull⟩
  · exact absurd (mem_treeOfBlobs_of_not_internal hN hne.1 hne.2 h₂) hAB
  have h₂ := two_le_card_of_inter_taxa_mem (mem_filter.1 (mem_filter.1 hs).1).2
  have hT := isSplitFamily_of_internal hT₀ h₂.1
  have hAu : A ≠ univ := by
    rintro rfl
    simp at h₂
  have hAu' : Aᶜ ≠ univ := by
    intro h
    have : A = ∅ := by simpa using congrArg compl h
    subst this
    simp at h₂
  have hnotcut := not_hasCutSplit_of_notMem h₂.1 h₂.2 hAB
  -- every quartet of the bipartition is a trivial 4-blob or a cut split
  have hall₀ : ∀ x₁ x₂ x₃ x₄, x₁ ∈ A → x₂ ∈ A → x₃ ∉ A → x₄ ∉ A → Sep T₀ A x₁ x₂ →
      Sep T₀ Aᶜ x₃ x₄ → HasTrivialFourBlob N {x₁, x₂, x₃, x₄} ∨ RDom N x₁ x₂ x₃ x₄ := by
    intro x₁ x₂ x₃ x₄ h₁ h₂' h₃ h₄ h₁₂ h₃₄
    have h₁₃ : x₁ ≠ x₃ := fun h => h₃ (h ▸ h₁)
    have h₁₄ : x₁ ≠ x₄ := fun h => h₄ (h ▸ h₁)
    have h₂₃ : x₂ ≠ x₃ := fun h => h₃ (h ▸ h₂')
    have h₂₄ : x₂ ≠ x₄ := fun h => h₄ (h ▸ h₂')
    have hc := card_four_of_ne h₁₂.1 h₁₃ h₁₄ h₂₃ h₂₄ h₃₄.1
    exact (isNullQuartet_quartetTree_iff hN hc).1
      (hnull _ (mem_filter.1 (quartetTree_mem hc h₁ h₂' h₃ h₄ h₁₂ h₃₄)).1)
  have hallA : ∀ x₁ x₂ x₃ x₄, x₁ ∉ A → x₂ ∉ A → x₃ ∈ A → x₄ ∈ A → Sep T₀ Aᶜ x₁ x₂ → Sep T₀ A x₃ x₄ →
      HasTrivialFourBlob N {x₁, x₂, x₃, x₄} ∨ RDom N x₁ x₂ x₃ x₄ := by
    intro x₁ x₂ x₃ x₄ h₁ h₂' h₃ h₄ h₁₂ h₃₄
    rcases hall₀ x₃ x₄ x₁ x₂ h₃ h₄ h₁ h₂' h₃₄ h₁₂ with h | h
    · rw [insert_pair_comm] at h
      exact Or.inl h
    · exact Or.inr h.symm
  have hallB : ∀ x₁ x₂ x₃ x₄, x₁ ∉ Aᶜ → x₂ ∉ Aᶜ → x₃ ∈ Aᶜ → x₄ ∈ Aᶜ → Sep T₀ Aᶜᶜ x₁ x₂ →
      Sep T₀ Aᶜ x₃ x₄ → HasTrivialFourBlob N {x₁, x₂, x₃, x₄} ∨ RDom N x₁ x₂ x₃ x₄ := by
    intro x₁ x₂ x₃ x₄ h₁ h₂' h₃ h₄ h₁₂ h₃₄
    rw [compl_compl] at h₁₂
    exact hall₀ x₁ x₂ x₃ x₄ (by simpa using h₁) (by simpa using h₂') (mem_compl.1 h₃)
      (mem_compl.1 h₄) h₁₂ h₃₄
  -- the end, on a side `P`
  have finish : ∀ {P : Finset X}, (P = A ∨ P = Aᶜ) → (∀ s ∈ bipartitionQuartets P, IsNullQuartet N s) →
      ∀ {a c d d' : X} {Z : Finset X}, a ∉ P → c ∈ P → d ∈ P → Sep T₀ P c d' → Z ∈ treeOfBlobs N →
      c ∈ Z → d' ∈ Z → a ∉ Z → d ∉ Z →
      ∃ P, (P = A ∨ P = Aᶜ) ∧ ∃ D ∈ treeOfBlobs N, D ⊂ P ∧ ∃ x ∈ D, ∃ y ∈ D, Sep T₀ P x y := by
    intro P hPA hPn a c d d' Z ha hc hd hsep hZ hcZ hd'Z haZ hdZ
    refine ⟨P, hPA, Z, hZ, ?_, c, hcZ, d', hd'Z, hsep⟩
    rcases compatible_of_forall_null hN hPn hZ with h | h | h | h
    · exact absurd (h hd) hdZ
    · exact Finset.ssubset_def.2 ⟨h, fun hPZ => hdZ (hPZ hd)⟩
    · exact absurd hcZ (Finset.disjoint_left.1 h hc)
    · have : a ∈ P ∪ Z := h ▸ mem_univ a
      rcases mem_union.1 this with h' | h'
      · exact absurd h' ha
      · exact absurd h' haZ
  -- a quartet that is a trivial 4-blob, from Corollary 4.3
  obtain ⟨a₀, ha₀, b₀, hb₀, c₀, hc₀, d₀, hd₀, hab₀, hcd₀, hbad⟩ :=
    exists_cut_witness hN hT h₂.1 h₂.2 hnotcut
  have hc₀' := mem_compl.1 hc₀
  have hd₀' := mem_compl.1 hd₀
  have htr₀ : HasTrivialFourBlob N {a₀, b₀, c₀, d₀} := by
    rcases hall₀ a₀ b₀ c₀ d₀ ha₀ hb₀ hc₀' hd₀' hab₀ hcd₀ with h | h
    · exact h
    · have h₁₃ : a₀ ≠ c₀ := fun h => hc₀' (h ▸ ha₀)
      have h₁₄ : a₀ ≠ d₀ := fun h => hd₀' (h ▸ ha₀)
      have h₂₃ : b₀ ≠ c₀ := fun h => hc₀' (h ▸ hb₀)
      have h₂₄ : b₀ ≠ d₀ := fun h => hd₀' (h ▸ hb₀)
      have hc := card_four_of_ne hab₀.1 h₁₃ h₁₄ h₂₃ h₂₄ hcd₀.1
      exact absurd (hasCutSplitOn_of_inducedCutSplit hc (inducedCutSplit_of_rdom hN hc h)) hbad
  -- a quartet that is not, by hypothesis
  obtain ⟨a₁, b₁, c₁, d₁, hc₁, rfl, ha₁, hb₁, hc₁', hd₁', hab₁, hcd₁⟩ := exists_tuple hs
  rw [taxa_quartetTree] at hns
  by_cases hmid : HasTrivialFourBlob N {a₁, b₁, c₀, d₀}
  · -- replacing taxa on the side `Aᶜ`
    obtain ⟨x, hx, y, hy, y', hy', hxy, hxy', hτ, hnτ⟩ := exists_step hT hAu'
      (fun x y => HasTrivialFourBlob N {a₁, b₁, x, y})
      (fun x y h => by rwa [insert_insert_pair_comm] at h) hc₀ hd₀ (mem_compl.2 hc₁')
      (mem_compl.2 hd₁') hcd₀ hcd₁ hmid hns
    have hr :=
      (hall₀ a₁ b₁ x y' ha₁ hb₁ (mem_compl.1 hx) (mem_compl.1 hy') hab₁ hxy').resolve_left hnτ
    obtain ⟨Z, hZ, hxZ, hyZ, haZ, hdZ⟩ := exists_cut_side_of_adjacent hN hT hallB (a := a₁) (b := b₁)
      (by simpa using ha₁) (by simpa using hb₁) hx hy (by rwa [compl_compl]) hxy hτ hr
    exact finish (Or.inr rfl) (by rw [bipartitionQuartets_compl]; exact hnull)
      (by simpa using ha₁) hx hy hxy' hZ hxZ hyZ haZ hdZ
  · -- replacing taxa on the side `A`
    obtain ⟨x, hx, y, hy, y', hy', hxy, hxy', hτ, hnτ⟩ := exists_step hT hAu
      (fun x y => HasTrivialFourBlob N {x, y, c₀, d₀})
      (fun x y h => by rwa [pair_insert_comm] at h) ha₀ hb₀ ha₁ hb₁ hab₀ hab₁ htr₀ hmid
    have hr := (hall₀ x y' c₀ d₀ hx hy' hc₀' hd₀' hxy' hcd₀).resolve_left hnτ
    obtain ⟨Z, hZ, hxZ, hyZ, haZ, hdZ⟩ := exists_cut_side_of_adjacent hN hT hallA (a := c₀) (b := d₀)
      hc₀' hd₀' hx hy hcd₀ hxy (by rw [insert_pair_comm]; exact hτ) hr.symm
    exact finish (Or.inl rfl) hnull hc₀' hx hy hxy' hZ hxZ hyZ haZ hdZ

/-- **A condition on `T₀`.** Remark 8.4 holds for any network, if `T₀` is such that each cut side
inside a side of a false edge of `T₀` lies in one block of `T₀` at that side. On a resolution of the
tree of blobs, the cut side itself is that block. -/
theorem limitTree_eq_inter_of_blocks (hN : N.IsPhylogenetic) (hT₀ : IsUnrootedTree T₀)
    (h : ∀ A ∈ internalSides T₀, A ∉ treeOfBlobs N → ∀ D ∈ treeOfBlobs N, D ⊂ A →
      ∃ C ∈ T₀, C ⊂ A ∧ D ⊆ C) :
    limitTree N T₀ = T₀ ∩ treeOfBlobs N := by
  refine Finset.Subset.antisymm (fun A hA => ?_) (inter_treeOfBlobs_subset_limitTree hN hT₀)
  have hAT₀ := limitTree_subset T₀ hA
  refine mem_inter.2 ⟨hAT₀, ?_⟩
  by_contra hAB
  obtain ⟨P, hP, D, hD, hDP, x, hx, y, hy, hsep⟩ := exists_missed_cut_of_mem_limitTree hN hT₀ hA hAB
  have hne := nonempty_of_mem_tree hT₀ hAT₀
  have hA₂ : 2 ≤ A.card ∧ 2 ≤ Aᶜ.card := by
    by_contra hcon
    exact hAB (mem_treeOfBlobs_of_not_internal hN hne.1 hne.2 hcon)
  have hPi : P ∈ internalSides T₀ ∧ P ∉ treeOfBlobs N := by
    rcases hP with rfl | rfl
    · exact ⟨mem_internalSides.2 ⟨hAT₀, hA₂⟩, hAB⟩
    · refine ⟨mem_internalSides.2 ⟨compl_mem_of_isUnrootedTree hT₀ hAT₀, hA₂.2, by simpa using hA₂.1⟩,
        fun hc => hAB ?_⟩
      simpa using compl_mem_treeOfBlobs hc
  obtain ⟨C, hC, hCP, hDC⟩ := h P hPi.1 hPi.2 D hD hDP
  exact hsep.2 ⟨C, hC, hCP, hDC hx, hDC hy⟩

end Properties


/-! ### Part 5: Remark 8.4 for networks with no trivial 4-blob, by the paper's argument -/

section Binary

omit [Fintype X] in
/-- A binary network has no trivial 4-blob: a hub of four taxa would have four distinct bridges, and
a vertex has degree at most three. -/
theorem not_hasTrivialFourBlob_of_isBinary (hN : N.IsPhylogenetic) (hb : N.IsBinary) {q : Finset X}
    (hq : q.card = 4) : ¬ HasTrivialFourBlob N q := by
  intro htr
  obtain ⟨v, hv⟩ := exists_isHub hN (by omega) htr
  have : Nonempty E := by
    obtain ⟨x, hx⟩ : q.Nonempty := Finset.card_pos.1 (by omega)
    exact ⟨(hv x hx).choose⟩
  choose! e he using hv
  have : Finite E := hN.finite_arcs
  have hinj : Set.InjOn e (q : Set X) := by
    intro x hx y hy hxy
    by_contra hne
    have hx' : x ∈ q := hx
    have hy' : y ∈ q := hy
    rcases he x hx' with h₁ | h₁ <;> rcases he y hy' with h₂ | h₂
    · exact h₁.2.2 y hy' (Ne.symm hne) (hxy ▸ isBelow_of_dominates hN h₂.2.1)
    · refine not_reaches_target_source hN (e y) ?_
      rw [h₂.1, ← hxy, h₁.1]
      exact Relation.ReflTransGen.refl
    · refine not_reaches_target_source hN (e x) ?_
      rw [h₁.1, hxy, h₂.1]
      exact Relation.ReflTransGen.refl
    · exact h₂.2.2 (hxy ▸ isBelow_of_dominates hN (h₁.2.1 y hy' (Ne.symm hne)))
  have hmaps : Set.MapsTo e (q : Set X)
      ({f | N.graph.source f = v} ∪ {f | N.graph.target f = v}) := by
    intro x hx
    rcases he x hx with h | h
    · exact Or.inl h.1
    · exact Or.inr h.1
  have h₄ : 4 ≤ ({f | N.graph.source f = v} ∪ {f | N.graph.target f = v}).ncard := by
    rw [← hq, ← Set.ncard_coe_finset q]
    exact Set.ncard_le_ncard_of_injOn e hmaps hinj (Set.toFinite _)
  have hun := Set.ncard_union_le {f | N.graph.source f = v} {f | N.graph.target f = v}
  have hin : {f | N.graph.target f = v}.ncard = N.graph.indegree v := rfl
  have hout : {f | N.graph.source f = v}.ncard = N.graph.outdegree v := rfl
  by_cases hr : v = N.root
  · subst hr
    have := hN.root_indegree
    have := hb.1
    omega
  · by_cases hz : N.graph.outdegree v = 0
    · obtain ⟨x, rfl⟩ := (hN.leaves v).1 hz
      have := hN.leaf_indegree x
      omega
    · have := hb.2 v hr hz
      omega

variable {p f : QuartetTree X → ℝ} {Null : QuartetTree X → Prop} {T₀ : Finset (Finset X)}
  {o : ECToBlobOptions} {α β : ℝ} {c : QuartetTree X → ℝ}

/-- **The argument of the proof of Theorem 8.2, on a network with no trivial 4-blob.** "By Corollaries
4.2 and 4.3, `S^a(e)` is empty exactly when `e` is a cut-edge" (line 1126): for each quartet type, and
at each stage, a false edge has a quartet that is not a cut split, by
`Deterministic.exists_not_inducedCutSplit_edgeQuartets`, so off the T1 null since it has no trivial
4-blob; and Step 3 keeps the cut edges of `T₀`, which replaces its use of `T_B ⊆ T₀`. -/
theorem CoarseRun.isLimit_inter (R : CoarseRun N p f Null T₀ o α β c)
    (hno : ∀ q : Finset X, q.card = 4 → ¬ HasTrivialFourBlob N q) :
    IsLimit α (edgeTestP o f T₀) (treeTestP o f) (afterStar o β c T₀) (T₀ ∩ treeOfBlobs N) := by
  have hsub : afterStar o β c T₀ ⊆ T₀ := afterStar_subset
  have hnull : ∀ {s : QuartetTree X}, ¬ InducedCutSplit N s → ¬ Null s := fun {s} hn h =>
    ((R.null_iff s).1 h).elim hn (hno _ s.card_taxa)
  have hcompl : ∀ A ∈ T₀ ∩ treeOfBlobs N, Aᶜ ∈ T₀ ∩ treeOfBlobs N := fun A hA =>
    mem_inter.2 ⟨compl_mem_of_isUnrootedTree R.isTree (mem_inter.1 hA).1,
      compl_mem_treeOfBlobs (mem_inter.1 hA).2⟩
  -- Step 3 keeps the cut edges of `T₀`
  have hkey : ∀ A ∈ T₀ ∩ treeOfBlobs N,
      A ∉ (internalSides T₀).filter fun A => β < edgeStarP o c T₀ A := by
    intro A hA hmem
    obtain ⟨hint, hβ⟩ := mem_filter.1 hmem
    obtain ⟨_, h₂, h₂'⟩ := mem_internalSides.1 hint
    obtain ⟨s, hs⟩ := exists_mem_multipartitionQuartets (isSplitFamily_of_internal R.isTree h₂) h₂ h₂'
    have hA' : A ∩ s.taxa ∈ s.val := (mem_filter.1 (mem_filter.1 hs).1).2
    have hcut := inducedCutSplit_of_mem R.phylo (mem_inter.1 hA).2 hA'
    exact absurd hβ (not_lt_of_gt ((R.star A hint).2 ⟨s, hs, fun hu => hno _ s.card_taxa
      ((R.uniform_iff s).1 hu)⟩))
  refine ⟨fun A hA => mem_contractSides.2 ⟨(mem_inter.1 hA).1, hkey A hA, hkey _ (hcompl A hA)⟩,
    hcompl, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro A hA h
    have hne := nonempty_of_mem_tree R.isTree (hsub hA)
    exact mem_inter.2 ⟨hsub hA, mem_treeOfBlobs_of_not_internal R.phylo hne.1 hne.2 h⟩
  · intro A hA
    obtain ⟨_, h₂⟩ := mem_internalSides.1 hA
    exact isSplitFamily_afterStar (isSplitFamily_of_internal R.isTree h₂.1)
  · intro T hT A hAi hA
    exact (R.edge T (hT.trans hsub) A hAi).1 fun s hs => (R.null_iff s).2 (Or.inl
      (inducedCutSplit_of_mem R.phylo (mem_inter.1 hA).2 (mem_of_mem_edgeQuartets hs)))
  · intro T hT hTs A hAi hA
    obtain ⟨hAT, h₂, h₂'⟩ := mem_internalSides.1 hAi
    have hAB : A ∉ treeOfBlobs N := fun h => hA (mem_inter.2 ⟨hsub (hT hAT), h⟩)
    obtain ⟨s, hs, hn⟩ := exists_not_inducedCutSplit_edgeQuartets (o := o) R.phylo
      (isSplitFamily_of_internal R.isTree h₂) hTs h₂ h₂' (not_hasCutSplit_of_notMem h₂ h₂' hAB)
    exact (R.edge T (hT.trans hsub) A hAi).2 ⟨s, hs, hnull hn⟩
  · intro T hT
    refine (R.tree T (hT.trans Finset.inter_subset_left)).1 fun s hs => (R.null_iff s).2 (Or.inl ?_)
    obtain ⟨A, hA, hAs⟩ := (mem_filter.1 hs).2
    exact inducedCutSplit_of_mem R.phylo (mem_inter.1 (hT hA)).2 hAs
  · intro T hT A hAi hA
    obtain ⟨hAT, h₂, h₂'⟩ := mem_internalSides.1 hAi
    have hAB : A ∉ treeOfBlobs N := fun h => hA (mem_inter.2 ⟨hsub (hT hAT), h⟩)
    obtain ⟨s, hs, hn⟩ := exists_not_inducedCutSplit_bipartition R.phylo h₂ h₂'
      (not_hasCutSplit_of_notMem h₂ h₂' hAB)
    exact (R.tree T (hT.trans hsub)).2
      ⟨s, mem_filter.2 ⟨mem_univ _, A, hAT, (mem_filter.1 hs).2⟩, hnull hn⟩

end Binary

section Remark

variable {V E X : Type*} [Fintype X] [DecidableEq X]

/-- **Remark 8.4 for a network with no trivial 4-blob on four taxa**: the T1 null is then exactly the
cut splits, and the argument of Theorem 8.2 applies to an arbitrary tree `T₀`. -/
theorem remark8_4_of_noTrivial (N : RootedNetwork V E X) (hN : N.IsPhylogenetic)
    (hno : ∀ q : Finset X, q.card = 4 → ¬ HasTrivialFourBlob N q)
    (dist : BinaryGeneTree X → ℝ) (hd : IsDist dist)
    (h₁ : Assumption1Forward N (displayCF dist Subtype.val))
    (h₂ : Assumption1Converse N (displayCF dist Subtype.val)) (T₀ : Finset (Finset X))
    (hT₀ : IsUnrootedTree T₀) (o : ECToBlobOptions)
    (hpos : (o.testCo = .cauchy ∨ o.testCo = .cbc) →
      ∀ s, IsT1Strict (displayCF dist Subtype.val) s →
        ∀ r ∈ s.alternatives, 0 < displayCF dist Subtype.val r) :
    Tendsto (fun n => iidProb dist n fun ω =>
      ectoblob o (alphaSeq n) (betaSeq n) (quartetCount Subtype.val ω) T₀ = T₀ ∩ treeOfBlobs N)
      atTop (𝓝 1) := by
  refine tendsto_order.2 ⟨fun a ha => ?_, fun a ha => ?_⟩
  · filter_upwards [eventually_tests_correct hd o hpos hT₀ (ε := 1 - a) (by linarith)] with n hn
    refine (by linarith : a ≤ 1 - (1 - a)).trans_lt (hn.trans_le (iidProb_mono hd fun ω hω => ?_))
    have R : CoarseRun N (displayCF dist Subtype.val)
        (t1PValue (quartetCount Subtype.val ω)) (T1Null (displayCF dist Subtype.val)) T₀ o
        (alphaSeq n) (betaSeq n) (quartetCount Subtype.val ω) :=
      ⟨hN, hT₀, t1Null_iff h₁ h₂ fun s => sum_displayCF_binaryGeneTree hd s.card_taxa,
        uniform_iff h₁ h₂, hω.1, hω.2.1, hω.2.2⟩
    exact (R.isLimit_inter hno).outputBy_eq o.rule
  · exact Eventually.of_forall fun n => (iidProb_le_one hd n _).trans_lt ha

/-- **Remark 8.4 (`ecto:rem8_4`) for binary networks.** For a binary network, every unrooted tree
`T₀`, binary or not, every variant of the algorithm, and every distribution of binary gene trees
whose concordance factors satisfy both directions of Assumption 1, the output on `n` independent gene
trees is `T₀ ∩ T_B(N)` with probability tending to one: the edges of `T₀` that are cut edges of the
network, pendant edges included. The sequences are those of Theorem 8.2, and the hypothesis on
`cauchy` and `cbc` is that of Theorem 8.2 (E11).

For non-binary networks the Remark is false: `Counterexample.not_remark8_4`. -/
theorem remark8_4 (N : RootedNetwork V E X) (hN : N.IsPhylogenetic) (hb : N.IsBinary)
    (dist : BinaryGeneTree X → ℝ) (hd : IsDist dist)
    (h₁ : Assumption1Forward N (displayCF dist Subtype.val))
    (h₂ : Assumption1Converse N (displayCF dist Subtype.val)) (T₀ : Finset (Finset X))
    (hT₀ : IsUnrootedTree T₀) (o : ECToBlobOptions)
    (hpos : (o.testCo = .cauchy ∨ o.testCo = .cbc) →
      ∀ s, IsT1Strict (displayCF dist Subtype.val) s →
        ∀ r ∈ s.alternatives, 0 < displayCF dist Subtype.val r) :
    Tendsto (fun n => iidProb dist n fun ω =>
      ectoblob o (alphaSeq n) (betaSeq n) (quartetCount Subtype.val ω) T₀ = T₀ ∩ treeOfBlobs N)
      atTop (𝓝 1) :=
  remark8_4_of_noTrivial N hN (fun _ hq => not_hasTrivialFourBlob_of_isBinary hN hb hq) dist hd h₁ h₂
    T₀ hT₀ o hpos

end Remark

section Generic

universe u

variable {V E X : Type u} [Fintype V] [Fintype E] [Fintype X] [DecidableEq X]

omit [Fintype V] in
/-- Remark 8.4 for a binary network and a model meeting Assumption 1: the conclusion holds for all
trees and all variants at all valid parameters outside a null set of the measure of §5.1, the one
that Assumption 1 excludes. -/
theorem remark8_4_generic (N : RootedNetwork V E X) (hN : N.IsPhylogenetic) (hb : N.IsBinary)
    (dist : MetricData E → BinaryGeneTree X → ℝ) (hd : ∀ θ, N.IsMetric θ → IsDist (dist θ))
    (hA : Assumption1 N fun θ => displayCF (dist θ) Subtype.val) :
    IsNullParams N {θ | N.IsMetric θ ∧ ¬ ∀ (T₀ : Finset (Finset X)) (o : ECToBlobOptions),
      IsUnrootedTree T₀ →
      ((o.testCo = .cauchy ∨ o.testCo = .cbc) →
        ∀ s, IsT1Strict (displayCF (dist θ) Subtype.val) s →
          ∀ r ∈ s.alternatives, 0 < displayCF (dist θ) Subtype.val r) →
      Tendsto (fun n => iidProb (dist θ) n fun ω =>
        ectoblob o (alphaSeq n) (betaSeq n) (quartetCount Subtype.val ω) T₀ = T₀ ∩ treeOfBlobs N)
        atTop (𝓝 1)} := by
  intro d hd'
  refine MeasureTheory.measure_mono_null ?_ (hA.2 d hd')
  rintro x ⟨hval, hθ, hnot⟩
  refine ⟨hval, hval, fun hconv => hnot fun T₀ o hT₀ hpos => ?_⟩
  exact remark8_4 N hN hb (dist _) (hd _ hval) (hA.1 _ hval) hconv T₀ hT₀ o hpos

omit [Fintype V] in
/-- The limit of the algorithm on an arbitrary tree, for an arbitrary network and a model meeting
Assumption 1, at all valid parameters outside a null set. -/
theorem tendsto_ectoblob_limitTree_generic (N : RootedNetwork V E X) (hN : N.IsPhylogenetic)
    (dist : MetricData E → BinaryGeneTree X → ℝ) (hd : ∀ θ, N.IsMetric θ → IsDist (dist θ))
    (hA : Assumption1 N fun θ => displayCF (dist θ) Subtype.val) :
    IsNullParams N {θ | N.IsMetric θ ∧ ¬ ∀ (T₀ : Finset (Finset X)) (o : ECToBlobOptions),
      IsUnrootedTree T₀ →
      ((o.testCo = .cauchy ∨ o.testCo = .cbc) →
        ∀ s, IsT1Strict (displayCF (dist θ) Subtype.val) s →
          ∀ r ∈ s.alternatives, 0 < displayCF (dist θ) Subtype.val r) →
      Tendsto (fun n => iidProb (dist θ) n fun ω =>
        ectoblob o (alphaSeq n) (betaSeq n) (quartetCount Subtype.val ω) T₀ = limitTree N T₀)
        atTop (𝓝 1)} := by
  intro d hd'
  refine MeasureTheory.measure_mono_null ?_ (hA.2 d hd')
  rintro x ⟨hval, hθ, hnot⟩
  refine ⟨hval, hval, fun hconv => hnot fun T₀ o hT₀ hpos => ?_⟩
  exact tendsto_ectoblob_limitTree N hN (dist _) (hd _ hval) (hA.1 _ hval) hconv T₀ hT₀ o hpos

end Generic


end Limit

/-! ### Part 6: Remark 8.4 is false for non-binary networks -/

namespace Counterexample

/-- The tails of the arcs of the network `((0,1),2,3,4)` with a polytomy at its root: the vertices
`0, …, 4` are the taxa, `5` is the parent of `0` and `1`, and `6` is the root. -/
def src : Fin 6 → Fin 7 := ![6, 6, 6, 6, 5, 5]

/-- The heads of the arcs. -/
def tgt : Fin 6 → Fin 7 := ![5, 2, 3, 4, 0, 1]

/-- The taxa, as vertices. -/
def lf : Fin 5 → Fin 7 := ![0, 1, 2, 3, 4]

/-- The network: a tree on five taxa, with one internal edge, `01|234`, and a polytomy of degree four
at the root. It has no reticulation. -/
def net : RootedNetwork (Fin 7) (Fin 6) (Fin 5) := ⟨⟨src, tgt⟩, 6, lf⟩

/-- The vertices below a vertex. -/
def desc : Fin 7 → Finset (Fin 7) := ![{0}, {1}, {2}, {3}, {4}, {5, 0, 1}, {6, 5, 2, 3, 4, 0, 1}]

theorem reaches_iff {u w : Fin 7} : net.graph.Reaches u w ↔ w ∈ desc u := by
  constructor
  · intro h
    induction h with
    | refl =>
      have key : ∀ u : Fin 7, u ∈ desc u := by decide
      exact key u
    | tail _ hf ih =>
      obtain ⟨f, rfl, rfl⟩ := hf
      have key : ∀ (u : Fin 7) (f : Fin 6), src f ∈ desc u → tgt f ∈ desc u := by decide
      exact key u f ih
  · intro h
    have h₆₅ : net.graph.Reaches 6 5 := .single ⟨0, rfl, rfl⟩
    have h₅₀ : net.graph.Reaches 5 0 := .single ⟨4, rfl, rfl⟩
    have h₅₁ : net.graph.Reaches 5 1 := .single ⟨5, rfl, rfl⟩
    have h₆₂ : net.graph.Reaches 6 2 := .single ⟨1, rfl, rfl⟩
    have h₆₃ : net.graph.Reaches 6 3 := .single ⟨2, rfl, rfl⟩
    have h₆₄ : net.graph.Reaches 6 4 := .single ⟨3, rfl, rfl⟩
    have hsplit : ∀ u w : Fin 7, w ∈ desc u → w = u ∨ (u = 5 ∧ (w = 0 ∨ w = 1)) ∨
        (u = 6 ∧ (w = 5 ∨ w = 2 ∨ w = 3 ∨ w = 4 ∨ w = 0 ∨ w = 1)) := by decide
    rcases hsplit u w h with rfl | ⟨rfl, rfl | rfl⟩ | ⟨rfl, rfl | rfl | rfl | rfl | rfl | rfl⟩
    · exact .refl
    · exact h₅₀
    · exact h₅₁
    · exact h₆₅
    · exact h₆₂
    · exact h₆₃
    · exact h₆₄
    · exact h₆₅.trans h₅₀
    · exact h₆₅.trans h₅₁

theorem indegree_eq (v : Fin 7) : net.graph.indegree v = (univ.filter fun e => tgt e = v).card := by
  have : {e | net.graph.target e = v} = ((univ.filter fun e => tgt e = v : Finset (Fin 6)) : Set _) := by
    ext e
    simp [net]
  unfold DirectedMultigraph.indegree
  rw [this, Set.ncard_coe_finset]

theorem outdegree_eq (v : Fin 7) : net.graph.outdegree v = (univ.filter fun e => src e = v).card := by
  have : {e | net.graph.source e = v} = ((univ.filter fun e => src e = v : Finset (Fin 6)) : Set _) := by
    ext e
    simp [net]
  unfold DirectedMultigraph.outdegree
  rw [this, Set.ncard_coe_finset]

theorem net_isPhylogenetic : net.IsPhylogenetic := by
  have hrank : ∀ u w : Fin 7, net.graph.Adj u w → (![2, 2, 2, 2, 2, 1, 0] : Fin 7 → ℕ) u <
      (![2, 2, 2, 2, 2, 1, 0] : Fin 7 → ℕ) w := by
    rintro _ _ ⟨f, rfl, rfl⟩
    revert f
    decide
  refine ⟨inferInstance, inferInstance, inferInstance, fun v h => ?_, fun v => ?_, ?_, fun v hv => ?_,
    (by decide : Function.Injective lf), fun x => ?_, fun v => ?_⟩
  · have : ∀ w, Relation.TransGen net.graph.Adj v w → (![2, 2, 2, 2, 2, 1, 0] : Fin 7 → ℕ) v <
        (![2, 2, 2, 2, 2, 1, 0] : Fin 7 → ℕ) w := by
      intro w hw
      induction hw with
      | single hw => exact hrank _ _ hw
      | tail _ hw ih => exact ih.trans (hrank _ _ hw)
    exact lt_irrefl _ (this v h)
  · exact reaches_iff.2 (by revert v; decide)
  · rw [indegree_eq]
    decide
  · rw [indegree_eq]
    revert v
    decide
  · rw [indegree_eq]
    revert x
    decide
  · rw [outdegree_eq]
    show _ ↔ ∃ x, lf x = v
    revert v
    decide

/-- The arc `e` has the taxon `x` below it. -/
abbrev below (e : Fin 6) (x : Fin 5) : Prop := lf x ∈ desc (tgt e)

theorem isBelow_iff {e : Fin 6} {x : Fin 5} : net.IsBelow e x ↔ below e x := reaches_iff

/-- An arc dominates the taxa below it, in this tree. -/
theorem dominates_iff {e : Fin 6} {x : Fin 5} : net.Dominates e x ↔ below e x := by
  constructor
  · exact fun h => isBelow_iff.1 (FalseEdge.isBelow_of_dominates net_isPhylogenetic h)
  · intro h ha
    have key : ∀ w, net.AvoidingReach e net.root w → w ∉ desc (tgt e) := by
      intro w hw
      induction hw with
      | refl =>
        have : ∀ e : Fin 6, (6 : Fin 7) ∉ desc (tgt e) := by decide
        exact this e
      | tail _ hf ih =>
        obtain ⟨f, hfe, rfl, rfl⟩ := hf
        have : ∀ (e f : Fin 6), f ≠ e → src f ∉ desc (tgt e) → tgt f ∉ desc (tgt e) := by decide
        exact this e f hfe ih
    exact key _ ha h

/-- `RDom` on this network, in a decidable form. -/
def RDom' (a b c d : Fin 5) : Prop :=
  ∃ g : Fin 6, (below g a ∧ below g b ∧ ¬ below g c ∧ ¬ below g d) ∨
    (below g c ∧ below g d ∧ ¬ below g a ∧ ¬ below g b)

instance (a b c d : Fin 5) : Decidable (RDom' a b c d) :=
  inferInstanceAs (Decidable (∃ g : Fin 6, (below g a ∧ below g b ∧ ¬ below g c ∧ ¬ below g d) ∨
    (below g c ∧ below g d ∧ ¬ below g a ∧ ¬ below g b)))

theorem rdom_iff {a b c d : Fin 5} : RDom net a b c d ↔ RDom' a b c d := by
  simp only [RDom, dominates_iff, isBelow_iff, RDom']

/-- The hub of a set of taxa in distinct subtrees at the root. -/
theorem isHub_root {q : Finset (Fin 5)}
    (h : ∀ x ∈ q, ∃ e : Fin 6, src e = 6 ∧ below e x ∧ ∀ y ∈ q, y ≠ x → ¬ below e y) :
    IsHub net q 6 := by
  intro x hx
  obtain ⟨e, he, hb, hn⟩ := h x hx
  exact ⟨e, Or.inl ⟨he, dominates_iff.2 hb, fun y hy hyx hb' => hn y hy hyx (isBelow_iff.1 hb')⟩⟩

/-- The trivial 4-blobs of the network: the sets of four taxa without both `0` and `1`. -/
theorem hasTrivialFourBlob_iff {q : Finset (Fin 5)} (hq : q.card = 4) :
    HasTrivialFourBlob net q ↔ 0 ∉ q ∨ 1 ∉ q := by
  constructor
  · intro htr
    by_contra hcon
    push Not at hcon
    have hdec : ∀ q : Finset (Fin 5), q.card = 4 → 0 ∈ q → 1 ∈ q → ∃ x y : Fin 5, x ≠ 0 ∧ x ≠ 1 ∧
        y ≠ 0 ∧ y ≠ 1 ∧ x ≠ y ∧ q = {0, 1, x, y} ∧ RDom' 0 1 x y := by decide
    obtain ⟨x, y, hx₀, hx₁, hy₀, hy₁, hxy, rfl, hr⟩ := hdec q hq hcon.1 hcon.2
    obtain ⟨v, hv⟩ := exists_isHub net_isPhylogenetic (by omega) htr
    exact not_isHub_of_rdom net_isPhylogenetic (by decide) hx₀.symm hy₀.symm hx₁.symm hxy hv
      (rdom_iff.2 hr)
  · intro h
    have hdec : ∀ q : Finset (Fin 5), q.card = 4 → (0 ∉ q ∨ 1 ∉ q) →
        ∀ x ∈ q, ∃ e : Fin 6, src e = 6 ∧ below e x ∧ ∀ y ∈ q, y ≠ x → ¬ below e y := by decide
    exact hasTrivialFourBlob_of_isHub net_isPhylogenetic (by omega) (isHub_root (hdec q hq h))

/-! #### The starting tree -/

/-- The rooted tree `((0,2),(1,(3,4)))`. -/
def H₀ : Finset (Finset (Fin 5)) := {univ, {0}, {1}, {2}, {3}, {4}, {0, 2}, {3, 4}, {1, 3, 4}}

/-- The binary tree `T₀` with cherries `02` and `34`, which is not a resolution of the tree of blobs:
the cut edge `01|234` is not in it. -/
def T₀ : Finset (Finset (Fin 5)) := unroot H₀

theorem T₀_isBinaryTree : IsBinaryTree T₀ :=
  ⟨H₀, by unfold IsHierarchy; decide, rfl, by decide⟩

theorem T₀_isUnrootedTree : IsUnrootedTree T₀ :=
  let ⟨H, h₁, h₂, _⟩ := T₀_isBinaryTree
  ⟨H, h₁, h₂⟩

/-- A cut side of this network dominates its taxa, and `3`, `4` have no common arc. -/
theorem notMem_treeOfBlobs : ({3, 4} : Finset (Fin 5)) ∉ treeOfBlobs net := by
  intro h
  obtain ⟨_, _, _, hcut⟩ := mem_filter.1 h
  rw [hasCutSplit_iff_hasCutSplitOn_univ net_isPhylogenetic,
    hasCutSplitOn_iff_separates net_isPhylogenetic] at hcut
  obtain ⟨e, ⟨_, hd, _⟩ | ⟨_, hd, _⟩⟩ := hcut
  · have h₃ := hd 3 (by simp)
    have h₄ := hd 4 (by simp)
    rw [dominates_iff] at h₃ h₄
    have : ∀ e : Fin 6, ¬ (below e 3 ∧ below e 4) := by decide
    exact this e ⟨h₃, h₄⟩
  · have h₀ := hd 0 (by simp)
    have h₂ := hd 2 (by simp)
    rw [dominates_iff] at h₀ h₂
    have : ∀ e : Fin 6, ¬ (below e 0 ∧ below e 2) := by decide
    exact this e ⟨h₀, h₂⟩

/-- All quartets around the edge `34|012` are under the T1 null: `34|01` is a cut split, and the
other two have a trivial 4-blob. -/
theorem forall_null : ∀ s ∈ bipartitionQuartets ({3, 4} : Finset (Fin 5)), IsNullQuartet net s := by
  intro s hs
  obtain ⟨a, b, c, d, hc, rfl, ha, hb, hc', hd, hab, hcd⟩ :=
    exists_tuple (mem_multipartitionQuartets_empty hs)
  rw [isNullQuartet_quartetTree_iff net_isPhylogenetic]
  have hdec : ∀ a b c d : Fin 5, a ∈ ({3, 4} : Finset (Fin 5)) → b ∈ ({3, 4} : Finset (Fin 5)) →
      c ∉ ({3, 4} : Finset (Fin 5)) → d ∉ ({3, 4} : Finset (Fin 5)) → a ≠ b → c ≠ d →
      RDom' a b c d ∨ 0 ∉ ({a, b, c, d} : Finset (Fin 5)) ∨ 1 ∉ ({a, b, c, d} : Finset (Fin 5)) := by
    decide
  rcases hdec a b c d ha hb hc' hd hab.1 hcd.1 with h | h
  · exact Or.inr (rdom_iff.2 h)
  · exact Or.inl ((hasTrivialFourBlob_iff hc).2 h)

/-- The quartet `01|34` of the multipartition at the edge is a cut split, so not uniform: Step 3 does
not contract the edge. Taxa `0` and `1` are in distinct blocks at this edge, since `T₀` misses the
cut edge `01|234`. -/
theorem exists_nontrivial : ∃ s ∈ multipartitionQuartets T₀ ({3, 4} : Finset (Fin 5)),
    ¬ HasTrivialFourBlob net s.taxa := by
  have hc : ({3, 4, 0, 1} : Finset (Fin 5)).card = 4 := by decide
  refine ⟨quartetTree 3 4 0 1 hc, quartetTree_mem hc (by decide) (by decide) (by decide) (by decide)
    ?_ ?_, ?_⟩
  · unfold FalseEdge.Sep T₀ H₀ unroot
    decide
  · unfold FalseEdge.Sep T₀ H₀ unroot
    decide
  · rw [taxa_quartetTree, hasTrivialFourBlob_iff hc]
    decide

/-- **The false edge stays.** -/
theorem mem_limitTree_three_four : ({3, 4} : Finset (Fin 5)) ∈ limitTree net T₀ :=
  mem_limitTree.2 ⟨by unfold T₀ H₀ unroot; decide, Or.inr ⟨exists_nontrivial, forall_null⟩⟩

/-- The other false edge, `02|134`, is contracted, since its quartet `02|13` is off the T1 null. -/
theorem notMem_limitTree_zero_two : ({0, 2} : Finset (Fin 5)) ∉ limitTree net T₀ := by
  intro h
  rcases (mem_limitTree.1 h).2 with h₂ | ⟨_, hall⟩
  · exact h₂ (by decide)
  · have hc : ({0, 2, 1, 3} : Finset (Fin 5)).card = 4 := by decide
    have hmem : quartetTree 0 2 1 3 hc ∈ bipartitionQuartets ({0, 2} : Finset (Fin 5)) := by
      refine mem_filter.2 ⟨mem_univ _, ?_⟩
      rw [taxa_quartetTree]
      simp only [quartetTree_val]
      decide
    rcases (isNullQuartet_quartetTree_iff net_isPhylogenetic hc).1 (hall _ hmem) with h' | h'
    · exact absurd ((hasTrivialFourBlob_iff hc).1 h') (by decide)
    · exact absurd (rdom_iff.1 h') (by decide)

/-- The limit of the algorithm on this tree: the pendant edges and the false edge `34|012`. -/
theorem limitTree_eq : limitTree net T₀ = T₀.filter fun A => A ≠ {0, 2} ∧ A ≠ {1, 3, 4} := by
  ext A
  rw [mem_filter]
  constructor
  · intro hA
    refine ⟨limitTree_subset T₀ hA, ?_, ?_⟩
    · rintro rfl
      exact notMem_limitTree_zero_two hA
    · rintro rfl
      have := compl_mem_limitTree T₀_isUnrootedTree hA
      have he : ({1, 3, 4} : Finset (Fin 5))ᶜ = {0, 2} := by decide
      rw [he] at this
      exact notMem_limitTree_zero_two this
  · rintro ⟨hA, h₁, h₂⟩
    have hdec : ∀ A ∈ T₀, A ≠ {0, 2} → A ≠ {1, 3, 4} → ¬ (2 ≤ A.card ∧ 2 ≤ Aᶜ.card) ∨ A = {3, 4} ∨
        A = {0, 1, 2} := by
      unfold T₀ H₀ unroot
      decide
    rcases hdec A hA h₁ h₂ with h | rfl | rfl
    · exact mem_limitTree.2 ⟨hA, Or.inl h⟩
    · exact mem_limitTree_three_four
    · have := compl_mem_limitTree T₀_isUnrootedTree mem_limitTree_three_four
      have he : ({3, 4} : Finset (Fin 5))ᶜ = {0, 1, 2} := by decide
      rwa [he] at this

/-! #### A law of gene trees -/

/-- The nine gene trees: `((a,b),(c,(d,e)))` for the given `a, b, c, d, e`. They are the three with
cherry `01`, and the six with cherries `0x`, `1z`. -/
def tup : Fin 9 → Fin 5 × Fin 5 × Fin 5 × Fin 5 × Fin 5 :=
  ![(0, 1, 2, 3, 4), (0, 1, 3, 2, 4), (0, 1, 4, 2, 3), (0, 2, 3, 1, 4), (0, 2, 4, 1, 3),
    (0, 3, 2, 1, 4), (0, 3, 4, 1, 2), (0, 4, 2, 1, 3), (0, 4, 3, 1, 2)]

/-- The clusters of these gene trees. -/
def hier (i : Fin 9) : Finset (Finset (Fin 5)) :=
  {univ, {0}, {1}, {2}, {3}, {4}, {(tup i).1, (tup i).2.1}, {(tup i).2.2.2.1, (tup i).2.2.2.2},
    {(tup i).2.2.1, (tup i).2.2.2.1, (tup i).2.2.2.2}}

/-- The gene trees. -/
def gene (i : Fin 9) : BinaryGeneTree (Fin 5) :=
  ⟨unroot (hier i), hier i, by unfold IsHierarchy; revert i; decide, rfl, by revert i; decide⟩

/-- Their weights, in twelfths. -/
def wt : Fin 9 → ℕ := ![2, 2, 2, 1, 1, 1, 1, 1, 1]

/-- The law of the gene trees. -/
def law (g : BinaryGeneTree (Fin 5)) : ℝ := ∑ i, if g = gene i then (wt i : ℝ) / 12 else 0

theorem law_isDist : IsDist law := by
  refine ⟨fun g => Finset.sum_nonneg fun i _ => ?_, ?_⟩
  · split_ifs
    · positivity
    · exact le_rfl
  · unfold law
    rw [Finset.sum_comm]
    simp only [Finset.sum_ite_eq', mem_univ, ite_true]
    rw [← Finset.sum_div, ← Nat.cast_sum]
    have : ∑ i, wt i = 12 := by decide
    rw [this]
    norm_num

/-- The weight of the gene trees displaying the quartet with cherries `B`, `C`. -/
def count (B C : Finset (Fin 5)) : ℕ :=
  ∑ i, wt i * if ∃ A ∈ unroot (hier i), A ∩ (B ∪ C) = B ∨ A ∩ (B ∪ C) = C then 1 else 0

theorem count_eq : ∀ B ∈ powersetCard 2 (univ : Finset (Fin 5)),
    ∀ C ∈ powersetCard 2 (univ : Finset (Fin 5)), Disjoint B C →
      count B C = if B = {0, 1} ∨ C = {0, 1} then 6
        else if ({0, 1} : Finset (Fin 5)) ⊆ B ∪ C then 3 else 4 := by
  decide

/-- The concordance factors of the law: `1/2` on `01|xy`, `1/4` on the two other quartet trees with
these taxa, and `1/3` on the quartet trees whose taxa do not include both `0` and `1`. -/
theorem displayCF_law (s : QuartetTree (Fin 5)) :
    displayCF law Subtype.val s = if ({0, 1} : Finset (Fin 5)) ∈ s.val then 1 / 2
      else if ({0, 1} : Finset (Fin 5)) ⊆ s.taxa then 1 / 4 else 1 / 3 := by
  obtain ⟨B, C, hs, hB, hC, hd, ht⟩ := s.exists_eq_pair
  have hdisp : ∀ i, Displays (gene i).1 s ↔ ∃ A ∈ unroot (hier i), A ∩ (B ∪ C) = B ∨ A ∩ (B ∪ C) = C := by
    intro i
    unfold Displays
    rw [ht, hs]
    simp only [mem_insert, mem_singleton]
    rfl
  have hsum : displayCF law Subtype.val s = (count B C : ℝ) / 12 := by
    unfold displayCF law count
    rw [Nat.cast_sum, Finset.sum_div]
    have hstep : ∀ g : BinaryGeneTree (Fin 5), (if Displays g.1 s then
        ∑ i, (if g = gene i then (wt i : ℝ) / 12 else 0) else 0) =
        ∑ i, if Displays g.1 s then (if g = gene i then (wt i : ℝ) / 12 else 0) else 0 := by
      intro g
      split_ifs <;> simp
    simp only [hstep]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_eq_single (gene i)]
    · simp only [ite_true, hdisp i]
      split_ifs <;> push_cast <;> simp
    · intro g _ hg
      simp [hg]
    · intro h
      exact absurd (mem_univ _) h
  have hc := count_eq B (mem_powersetCard.2 ⟨subset_univ _, hB⟩) C
    (mem_powersetCard.2 ⟨subset_univ _, hC⟩) hd
  have hmem : ({0, 1} : Finset (Fin 5)) ∈ s.val ↔ B = {0, 1} ∨ C = {0, 1} := by
    rw [hs]
    simp only [mem_insert, mem_singleton]
    exact ⟨fun h => h.imp Eq.symm Eq.symm, fun h => h.imp Eq.symm Eq.symm⟩
  rw [hsum, hc, ht]
  by_cases h₁ : B = {0, 1} ∨ C = {0, 1}
  · rw [ite_eq_left h₁, ite_eq_left (hmem.2 h₁)]
    norm_num
  · rw [ite_eq_right h₁, ite_eq_right (fun h => h₁ (hmem.1 h))]
    split_ifs <;> norm_num

theorem displayCF_law_pos (r : QuartetTree (Fin 5)) : 0 < displayCF law Subtype.val r := by
  rw [displayCF_law]
  split_ifs <;> norm_num

/-- Four taxa with `0` and `1`. -/
theorem exists_decomp {q : Finset (Fin 5)} (hq : q.card = 4) (h₀ : 0 ∈ q) (h₁ : 1 ∈ q) :
    ∃ x y : Fin 5, x ≠ 0 ∧ x ≠ 1 ∧ y ≠ 0 ∧ y ≠ 1 ∧ x ≠ y ∧ q = {0, 1, x, y} := by
  have hdec : ∀ q : Finset (Fin 5), q.card = 4 → 0 ∈ q → 1 ∈ q → ∃ x y : Fin 5, x ≠ 0 ∧ x ≠ 1 ∧
      y ≠ 0 ∧ y ≠ 1 ∧ x ≠ y ∧ q = {0, 1, x, y} := by decide
  exact hdec q hq h₀ h₁

/-- The quartet tree `01|xy` has the cut split. -/
theorem rdom_zero_one {x y : Fin 5} (h₁ : x ≠ 0) (h₂ : x ≠ 1) (h₃ : y ≠ 0) (h₄ : y ≠ 1) :
    RDom net 0 1 x y := by
  have hdec : ∀ x y : Fin 5, x ≠ 0 → x ≠ 1 → y ≠ 0 → y ≠ 1 → RDom' 0 1 x y := by decide
  exact rdom_iff.2 (hdec x y h₁ h₂ h₃ h₄)

/-- A cut split of the network on four taxa is `01|xy`. -/
theorem mem_val_of_inducedCutSplit {s : QuartetTree (Fin 5)} (h : InducedCutSplit net s) :
    ({0, 1} : Finset (Fin 5)) ∈ s.val := by
  obtain ⟨a, b, c, d, hc, rfl, hr⟩ := exists_rdom_of_inducedCutSplit net_isPhylogenetic h
  have hdec : ∀ a b c d : Fin 5, ({a, b, c, d} : Finset (Fin 5)).card = 4 → RDom' a b c d →
      ({a, b} : Finset (Fin 5)) = {0, 1} ∨ ({c, d} : Finset (Fin 5)) = {0, 1} := by decide
  rcases hdec a b c d hc (rdom_iff.1 hr) with h' | h'
  · simp [quartetTree, h']
  · simp [quartetTree, h']

/-- The law meets the forward direction of Assumption 1. -/
theorem law_forward : Assumption1Forward net (displayCF law Subtype.val) := by
  refine ⟨fun q hq htr r hr => ?_, fun s hs => ?_⟩
  · have hrq : r.taxa = q := by simpa [treesOn] using hr
    have hn := (hasTrivialFourBlob_iff hq).1 htr
    have hsub : ¬ ({0, 1} : Finset (Fin 5)) ⊆ r.taxa := by
      rw [hrq]
      intro h
      rcases hn with h' | h'
      · exact h' (h (by simp))
      · exact h' (h (by simp))
    have hval : ({0, 1} : Finset (Fin 5)) ∉ r.val := fun h => hsub (r.subset_taxa h)
    rw [displayCF_law, ite_eq_right hval, ite_eq_right hsub]
  · have h₀ := mem_val_of_inducedCutSplit hs
    have halt : ∀ r ∈ s.alternatives, displayCF law Subtype.val r = 1 / 4 := by
      intro r hr
      obtain ⟨hrt, hrs⟩ := QuartetTree.mem_alternatives.1 hr
      rw [displayCF_law, ite_eq_right (fun h => hrs (QuartetTree.eq_of_taxa_eq_of_mem hrt h h₀)),
        ite_eq_left (hrt ▸ s.subset_taxa h₀)]
    have hval : displayCF law Subtype.val s = 1 / 2 := by
      rw [displayCF_law, ite_eq_left h₀]
    refine ⟨fun r hr => ?_, fun r hr r' hr' => ?_⟩
    · rw [halt r hr, hval]
      norm_num
    · rw [halt r hr, halt r' hr']

/-- The law meets the converse direction of Assumption 1. -/
theorem law_converse : Assumption1Converse net (displayCF law Subtype.val) := by
  refine ⟨fun q hq htr hu => ?_, fun s hs hstrict => ?_⟩
  · have hmem : 0 ∈ q ∧ 1 ∈ q := by
      by_contra hcon
      refine htr ((hasTrivialFourBlob_iff hq).2 ?_)
      by_cases h₀ : 0 ∈ q
      · exact Or.inr fun h₁ => hcon ⟨h₀, h₁⟩
      · exact Or.inl h₀
    obtain ⟨x, y, hx₀, hx₁, hy₀, hy₁, hxy, rfl⟩ := exists_decomp hq hmem.1 hmem.2
    have hc : ({0, x, 1, y} : Finset (Fin 5)).card = 4 :=
      card_four_of_ne hx₀.symm (by decide) hy₀.symm hx₁ hxy hy₁.symm
    have ht : (quartetTree 0 x 1 y hc).taxa = {0, 1, x, y} := by
      rw [taxa_quartetTree]
      ext z
      simp only [mem_insert, mem_singleton]
      tauto
    have hval := hu (quartetTree 0 x 1 y hc) (by simp [treesOn, ht])
    rw [displayCF_law, ite_eq_right, ite_eq_left] at hval
    · norm_num at hval
    · rw [ht]
      intro z hz
      simp only [mem_insert, mem_singleton] at hz ⊢
      tauto
    · simp only [quartetTree_val, mem_insert, mem_singleton]
      rintro (h | h)
      · have : (1 : Fin 5) ∈ ({0, x} : Finset (Fin 5)) := h ▸ (by simp)
        simp [hx₁.symm] at this
      · have : (0 : Fin 5) ∈ ({1, y} : Finset (Fin 5)) := h ▸ (by simp)
        simp [hy₀.symm] at this
  · have hne : s.alternatives.Nonempty := by
      rw [← Finset.card_pos, s.card_alternatives]
      omega
    by_cases h₀ : ({0, 1} : Finset (Fin 5)) ∈ s.val
    · -- then `s` is the cut split
      apply hs
      have hmem : s ∈ bipartitionQuartets ({0, 1} : Finset (Fin 5)) := by
        refine mem_filter.2 ⟨mem_univ _, ?_⟩
        rwa [Finset.inter_eq_left.2 (s.subset_taxa h₀)]
      obtain ⟨a, b, c, d, hc, rfl, ha, hb, hc', hd, _, _⟩ :=
        exists_tuple (mem_multipartitionQuartets_empty hmem)
      refine inducedCutSplit_of_rdom net_isPhylogenetic hc ?_
      have hdec : ∀ a b c d : Fin 5, a ∈ ({0, 1} : Finset (Fin 5)) → b ∈ ({0, 1} : Finset (Fin 5)) →
          c ∉ ({0, 1} : Finset (Fin 5)) → d ∉ ({0, 1} : Finset (Fin 5)) → a ≠ b → RDom' a b c d := by
        decide
      exact rdom_iff.2 (hdec a b c d ha hb hc' hd (ne_of_card_four hc).1)
    · by_cases h₁ : ({0, 1} : Finset (Fin 5)) ⊆ s.taxa
      · -- the quartet tree `01|xy` has more weight
        obtain ⟨x, y, hx₀, hx₁, hy₀, hy₁, hxy, htaxa⟩ :=
          exists_decomp s.card_taxa (h₁ (by simp)) (h₁ (by simp))
        have hc : ({0, 1, x, y} : Finset (Fin 5)).card = 4 := htaxa ▸ s.card_taxa
        have hr : quartetTree 0 1 x y hc ∈ s.alternatives := by
          refine QuartetTree.mem_alternatives.2 ⟨by rw [taxa_quartetTree, htaxa], ?_⟩
          rintro h
          apply h₀
          rw [← h]
          simp
        have hlt := hstrict.1 _ hr
        rw [displayCF_law, displayCF_law, ite_eq_right h₀, ite_eq_left h₁, ite_eq_left (by simp)] at hlt
        norm_num at hlt
      · -- all three are at `1/3`
        obtain ⟨r, hr⟩ := hne
        obtain ⟨hrt, _⟩ := QuartetTree.mem_alternatives.1 hr
        have hsub : ¬ ({0, 1} : Finset (Fin 5)) ⊆ r.taxa := hrt ▸ h₁
        have hlt := hstrict.1 _ hr
        rw [displayCF_law, displayCF_law, ite_eq_right h₀, ite_eq_right h₁,
          ite_eq_right (fun h => hsub (r.subset_taxa h)), ite_eq_right hsub] at hlt
        exact lt_irrefl _ hlt

/-- **Remark 8.4 is false for non-binary networks.** The network is the tree `((0,1),2,3,4)`, with a
polytomy of degree four and the cut edge `01|234`. The tree `T₀` is the binary tree with cherries
`02` and `34`. The law of the gene trees has concordance factors `(1/2, 1/4, 1/4)` on the three sets
of four taxa with `0`, `1`, and uniform on the two others, so it meets both directions of Assumption
1, with positive concordance factors, so that all variants of the algorithm apply. (It has the shape
of the multispecies coalescent on this tree.)

The edge `34|012` is not a cut edge. Its three quartets are `34|01`, a cut split, and `34|02`, `34|12`,
which have trivial 4-blobs: all are under the T1 null, and the first is not uniform, since `0`, `1`
are in distinct blocks of `T₀`, which misses the cut edge `01|234`. So neither the star test nor the T1
tests contract the edge, and the algorithm outputs a tree with this false edge, for all variants of the
algorithm: the output is the limit tree, and it is not `T₀ ∩ T_B(N)`. -/
theorem not_remark8_4 :
    net.IsPhylogenetic ∧ ¬ net.IsBinary ∧ IsBinaryTree T₀ ∧ IsDist law ∧
      Assumption1Forward net (displayCF law Subtype.val) ∧
      Assumption1Converse net (displayCF law Subtype.val) ∧
      (∀ r, 0 < displayCF law Subtype.val r) ∧
      ({3, 4} : Finset (Fin 5)) ∈ T₀ ∧ ({3, 4} : Finset (Fin 5)) ∉ treeOfBlobs net ∧
      limitTree net T₀ = (T₀.filter fun A => A ≠ {0, 2} ∧ A ≠ {1, 3, 4}) ∧
      ({3, 4} : Finset (Fin 5)) ∈ limitTree net T₀ ∧
      ∀ o : ECToBlobOptions,
        Tendsto (fun n => iidProb law n fun ω =>
          ectoblob o (alphaSeq n) (betaSeq n) (quartetCount Subtype.val ω) T₀ = limitTree net T₀)
          atTop (𝓝 1) ∧
        Tendsto (fun n => iidProb law n fun ω =>
          ectoblob o (alphaSeq n) (betaSeq n) (quartetCount Subtype.val ω) T₀ =
            T₀ ∩ treeOfBlobs net) atTop (𝓝 0) := by
  refine ⟨net_isPhylogenetic, ?_, T₀_isBinaryTree, law_isDist, law_forward, law_converse,
    displayCF_law_pos, by unfold T₀ H₀ unroot; decide, notMem_treeOfBlobs, limitTree_eq,
    mem_limitTree_three_four, fun o => ⟨?_, ?_⟩⟩
  · rintro ⟨h₁, _⟩
    rw [outdegree_eq] at h₁
    exact absurd h₁ (by decide)
  · exact tendsto_ectoblob_limitTree net net_isPhylogenetic law law_isDist law_forward law_converse
      T₀ T₀_isUnrootedTree o fun _ _ _ r _ => displayCF_law_pos r
  · refine tendsto_ectoblob_zero net net_isPhylogenetic law law_isDist law_forward law_converse T₀
      T₀_isUnrootedTree o (fun _ _ _ r _ => displayCF_law_pos r) fun h => ?_
    have := mem_limitTree_three_four
    rw [h] at this
    exact notMem_treeOfBlobs (mem_inter.1 this).2

end Counterexample

end ECToBlob.Coarsening
