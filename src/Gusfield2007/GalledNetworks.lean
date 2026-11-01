module

public import Gusfield2007.SufficientConditions
public import Mathlib.Data.Fin.VecNotation

/-!
# Gusfield et al. 2007, line 554: non-degenerate galled networks

"One application of Theorem 5 is to the recently introduced non-degenerate galled-networks (Huson and Klopper, 2007). It is easy to prove that for any non-degenerate galled-network `N` for `M`, a pair of sites is incompatible in `L` if and only if it is incompatible in `M`, and therefore `G(L)` and `G(M)` are
identical."

Huson and Klöpper 2007 (RECOMB, LNBI 4453, pp. 211-225) is closed and wasn't read. The definitions here come from what the authors published around it:

* `Network.IsNonDegenerate` is from the authors' errata to that paper, which corrects the definition there, and credits Gusfield with pointing it out;
* `Network.IsGalled` is Definition 1 of Huson, Rupp, Berry, Gambette, Paul 2009, *Computing galled networks from real data* (Bioinformatics 25, PMC2687971), which continues that paper. It may be worded differently in the 2007 paper.

The conjecture of that paper, which line 590 refutes, is in `Gusfield2007.HusonKloepper`, read from the thesis of the second author, whose Section 2.4 also has a galled network, as a "weakly dependent" reticulate network, and its own "degenerated" vertices. These are worded differently from the definitions here, and weren't compared further.

As printed, the sentence is false: the root can give a fourth pair (`galledIncompatPrinted_false`). What's true, and what Theorem 5 needs, has the ancestral sequence: a pair of sites is incompatible in `L` if and only if it is incompatible in `M + S` (`incompatible_labelSet_iff`), so that `G_S(L) = G_S(M)` (`conflictGraph_labelSet_eq`).
-/

@[expose] public noncomputable section

open scoped Classical

namespace Gusfield2007

universe u

namespace Network

variable {ι : Type*} {V : Type*} {E : Type*} (N : Network ι V E)

/-- A tree edge, in the sense of Huson and Klöpper: an arc into a node that isn't a recombination node. Not `IsTreeArc`, which is an arc on no recombination cycle. -/
def IsHKTreeEdge (e : E) : Prop := ¬ N.IsRecomb (N.tgt e)

/-- The undirected graph of the tree edges. -/
def hkTreeGraph : SimpleGraph V :=
  SimpleGraph.fromRel fun a b => ∃ e, N.IsHKTreeEdge e ∧ N.src e = a ∧ N.tgt e = b

/-- A galled network (Huson et al. 2009, Definition 1): "for every reticulation `r` in `N` and every pair of reticulation edges `p` and `q` with target node `r` there exists a tree cycle, that is, an undirected cycle in `N` that passes through `p` followed by `q` and otherwise contains only tree edges". Here: the sources of `p` and `q`
are joined by tree edges. A path of tree edges between them doesn't pass through `r`, as both would be below `r`, so that it closes a cycle with `p` and `q`, and such a cycle is such a path. -/
def IsGalled : Prop :=
  ∀ e f, e ≠ f → N.tgt e = N.tgt f → N.hkTreeGraph.Reachable (N.src e) (N.src f)

/-- A non-degenerate galled network, by the authors' errata: "for every tree edge `e = (u, v)` there exists a directed path of tree edges from `v` to some leaf `w`. Additionally, each tree node is either a leaf or is the source of two or more different tree edges." -/
structure IsNonDegenerate : Prop where
  tree_path : ∀ e, N.IsHKTreeEdge e → ∃ w, N.IsLeaf w ∧
    Relation.ReflTransGen (fun a b => ∃ f, N.IsHKTreeEdge f ∧ N.src f = a ∧ N.tgt f = b) (N.tgt e) w
  branching : ∀ v, ¬ N.IsRecomb v → N.IsLeaf v ∨ ∃ e f, e ≠ f ∧ N.src e = v ∧ N.src f = v ∧ N.IsHKTreeEdge e ∧ N.IsHKTreeEdge f

variable {N}

/-- A label is carried along a tree edge with no site of `i`. -/
theorem label_tgt_of_site_ne {e : E} (he : N.IsHKTreeEdge e) {i : ι} (hi : N.site i ≠ e) : N.label (N.tgt e) i = N.label (N.src e) i := by
  have hl := N.label_tree e (fun f hf => eq_of_not_isRecomb he hf) i
  rwa [ite_eq_right hi] at hl

/-- A node above the arc with `i` still has the state of the root at `i`. -/
theorem label_eq_root_of_src [Finite V] {i : ι} {v : V} (h : N.Reach v (N.src (N.site i))) : N.label v i = N.label N.root i :=
  label_eq_root_of_not_reach .refl fun hr => not_reach_tgt_src (N.site i) (hr.trans h)

/-- **At a node with no recombination**: going down tree edges, avoiding the arcs of `i` and `j`, reaches a leaf with the same states at `i` and `j`. It can be stopped only at a node whose two tree edges are the arcs of `i` and `j`. This node has the states of the root. -/
theorem exists_row_of_not_isRecomb [Finite V] (hnd : N.IsNonDegenerate) {M : Finset (ι → Bool)} (hd : N.Derives M) (i j : ι) (v : V) (hv : ¬ N.IsRecomb v) :
    ∃ r ∈ addRow M N.ancestral, r i = N.label v i ∧ r j = N.label v j := by
  induction v using N.wellFounded_transGen_swap.induction with
  | _ v ih =>
    rcases hnd.branching v hv with hleaf | ⟨e, f, hef, rfl, hf, he₁, hf₁⟩
    · exact ⟨_, mem_addRow.2 (Or.inr (hd.mapsTo hleaf)), rfl, rfl⟩
    · have hdown : ∀ g, N.src g = N.src e → N.IsHKTreeEdge g → N.site i ≠ g → N.site j ≠ g → ∃ r ∈ addRow M N.ancestral, r i = N.label (N.src e) i ∧ r j = N.label (N.src e) j := by
        intro g hg hg₁ hgi hgj
        obtain ⟨r, hr, h₁, h₂⟩ := ih (N.tgt g) (Relation.TransGen.single ⟨g, hg, rfl⟩) hg₁
        rw [label_tgt_of_site_ne hg₁ hgi, hg] at h₁
        rw [label_tgt_of_site_ne hg₁ hgj, hg] at h₂
        exact ⟨r, hr, h₁, h₂⟩
      by_cases h₁ : N.site i ≠ e ∧ N.site j ≠ e
      · exact hdown e rfl he₁ h₁.1 h₁.2
      by_cases h₂ : N.site i ≠ f ∧ N.site j ≠ f
      · exact hdown f hf hf₁ h₂.1 h₂.2
      · have hroot : ∀ s, (N.site s = e ∨ N.site s = f) → N.label (N.src e) s = N.label N.root s := by
          rintro s (hs | hs)
          · exact label_eq_root_of_src (by rw [hs]; exact Relation.ReflTransGen.refl)
          · exact label_eq_root_of_src (by rw [hs, hf]; exact Relation.ReflTransGen.refl)
        have hi : N.site i = e ∨ N.site i = f := by
          by_contra hno
          push Not at hno
          have hj₁ : N.site j = e := by
            by_contra h
            exact h₁ ⟨hno.1, h⟩
          have hj₂ : N.site j = f := by
            by_contra h
            exact h₂ ⟨hno.2, h⟩
          exact hef (hj₁.symm.trans hj₂)
        have hj : N.site j = e ∨ N.site j = f := by
          by_contra hno
          push Not at hno
          have hi₁ : N.site i = e := by
            by_contra h
            exact h₁ ⟨h, hno.1⟩
          have hi₂ : N.site i = f := by
            by_contra h
            exact h₂ ⟨h, hno.2⟩
          exact hef (hi₁.symm.trans hi₂)
        exact ⟨_, mem_addRow.2 (Or.inl rfl), (hroot i hi).symm, (hroot j hj).symm⟩

/-- In a galled network, a recombination node with an arc out has a tree edge out: an arc out of it is a tree edge, or it's on a tree cycle, which leaves it by a tree edge. -/
theorem exists_treeEdge_out (hg : N.IsGalled) {x : V} (hx : N.IsRecomb x) (hl : ¬ N.IsLeaf x) : ∃ d, N.src d = x ∧ N.IsHKTreeEdge d := by
  unfold IsLeaf at hl
  push Not at hl
  obtain ⟨g, rfl⟩ := hl
  by_cases htree : N.IsHKTreeEdge g
  · exact ⟨g, rfl, htree⟩
  · have hrec : N.IsRecomb (N.tgt g) := not_not.1 htree
    obtain ⟨a, b, hab, ha, hb⟩ := hrec
    have hother : ∃ g', g' ≠ g ∧ N.tgt g' = N.tgt g := by
      by_cases hag : a = g
      · exact ⟨b, fun h => hab (hag.trans h.symm), hb⟩
      · exact ⟨a, hag, ha⟩
    obtain ⟨g', hne, hg'⟩ := hother
    have hsrc : N.src g ≠ N.src g' := fun h => hne (N.simple _ _ h.symm hg')
    have key : ∀ {u w : V}, N.hkTreeGraph.Reachable u w → u ≠ w → ∃ c, N.hkTreeGraph.Adj u c := by
      rintro u w ⟨p⟩ huw
      cases p with
      | nil => exact absurd rfl huw
      | cons hadj _ => exact ⟨_, hadj⟩
    obtain ⟨c, -, ⟨d, hd, h₁, -⟩ | ⟨d, hd, -, h₂⟩⟩ := key (hg g g' hne.symm hg'.symm) hsrc
    · exact ⟨d, h₁, hd⟩
    · exact absurd hx (h₂ ▸ hd)

/-- **Every label of a non-degenerate galled network has, at any two sites, the states of a row or of the ancestral sequence.** -/
theorem exists_row_of_galled [Finite V] (hg : N.IsGalled) (hnd : N.IsNonDegenerate) {M : Finset (ι → Bool)} (hd : N.Derives M) (i j : ι) (v : V) :
    ∃ r ∈ addRow M N.ancestral, r i = N.label v i ∧ r j = N.label v j := by
  induction v using N.arc_induction with
  | _ v ih =>
    by_cases hv : N.IsRecomb v
    · by_cases hl : N.IsLeaf v
      · exact ⟨_, mem_addRow.2 (Or.inr (hd.mapsTo hl)), rfl, rfl⟩
      · obtain ⟨d, rfl, hdt⟩ := exists_treeEdge_out hg hv hl
        by_cases hfree : N.site i ≠ d ∧ N.site j ≠ d
        · obtain ⟨r, hr, h₁, h₂⟩ := exists_row_of_not_isRecomb hnd hd i j (N.tgt d) hdt
          rw [label_tgt_of_site_ne hdt hfree.1] at h₁
          rw [label_tgt_of_site_ne hdt hfree.2] at h₂
          exact ⟨r, hr, h₁, h₂⟩
        · -- A site on `d` hasn't mutated above `v`, so that all the parents have the state of `v` there: `v` has the states of the parent that gives the other site.
          obtain ⟨a, b, hab, ha, hb⟩ := hv
          have hparent : ∀ s s', N.site s = d → ∃ p, N.tgt p = N.src d ∧ N.label (N.src p) s = N.label (N.src d) s ∧ N.label (N.src p) s' = N.label (N.src d) s' := by
            intro s s' hs
            have hrootv : N.label (N.src d) s = N.label N.root s := label_eq_root_of_src (by rw [hs]; exact Relation.ReflTransGen.refl)
            have hrootp : ∀ p, N.tgt p = N.src d → N.label (N.src p) s = N.label N.root s := fun p hp =>
              label_eq_root_of_src (by
                rw [hs]
                exact Relation.ReflTransGen.single ⟨p, rfl, hp⟩)
            rcases N.label_recomb a b hab (ha.trans hb.symm) s' with h | h
            · rw [ha] at h
              exact ⟨a, ha, (hrootp a ha).trans hrootv.symm, h.symm⟩
            · rw [ha] at h
              exact ⟨b, hb, (hrootp b hb).trans hrootv.symm, h.symm⟩
          have hor : N.site i = d ∨ N.site j = d := by
            by_contra hno
            push Not at hno
            exact hfree hno
          rcases hor with hs | hs
          · obtain ⟨p, hp, h₁, h₂⟩ := hparent i j hs
            obtain ⟨r, hr, h₃, h₄⟩ := ih p hp
            exact ⟨r, hr, h₃.trans h₁, h₄.trans h₂⟩
          · obtain ⟨p, hp, h₁, h₂⟩ := hparent j i hs
            obtain ⟨r, hr, h₃, h₄⟩ := ih p hp
            exact ⟨r, hr, h₃.trans h₂, h₄.trans h₁⟩
    · exact exists_row_of_not_isRecomb hnd hd i j v hv

end Network

variable {ι : Type u} [LinearOrder ι] [Finite ι] {V E : Type*} [Fintype V] [Finite E]

omit [LinearOrder ι] [Finite ι] [Finite E] in
/-- **Line 554, with the ancestral sequence** (`g:galled_incompat`). "For any non-degenerate galled-network `N` for `M`, a pair of sites is incompatible in `L` if and only if it is incompatible in `M`": true with `M + S` in place of `M`, for `N` with ancestral sequence `S`. The paper gives no proof ("it is easy to prove"). The printed form is false: `galledIncompatPrinted_false`. -/
theorem incompatible_labelSet_iff {M : Finset (ι → Bool)} {S : ι → Bool} (N : Network ι V E) (hg : N.IsGalled) (hnd : N.IsNonDegenerate) (hd : N.Derives M) (hS : N.ancestral = S) (i j : ι) :
    Incompatible N.labelSet i j ↔ Incompatible (addRow M S) i j := by
  constructor
  · intro h a b
    obtain ⟨r, hr, h₁, h₂⟩ := h a b
    obtain ⟨v, -, rfl⟩ := Finset.mem_image.1 hr
    obtain ⟨r', hr', h₃, h₄⟩ := Network.exists_row_of_galled hg hnd hd i j v
    rw [hS] at hr'
    exact ⟨r', hr', h₃.trans h₁, h₄.trans h₂⟩
  · intro h a b
    obtain ⟨r, hr, h₁⟩ := h a b
    exact ⟨r, addRow_subset_labelSet N hd hS hr, h₁⟩

omit [LinearOrder ι] [Finite ι] [Finite E] in
/-- **Line 554, the graphs** (`g:galled_graph`): `G_S(L) = G_S(M)`, for a non-degenerate galled network with ancestral sequence `S`. -/
theorem conflictGraph_labelSet_eq {M : Finset (ι → Bool)} {S : ι → Bool} (N : Network ι V E) (hg : N.IsGalled) (hnd : N.IsNonDegenerate) (hd : N.Derives M) (hS : N.ancestral = S) :
    conflictGraph S N.labelSet = conflictGraph S M := by
  have hmem : S ∈ N.labelSet := addRow_subset_labelSet N hd hS (mem_addRow.2 (Or.inl rfl))
  rw [conflictGraph_eq_of_mem hmem, conflictGraph_eq_incompatGraph_addRow]
  ext i j
  exact incompatible_labelSet_iff N hg hnd hd hS i j

/-- **Line 554, the application of Theorem 5** (`g:galled_thm5`). An optimal network for `M` with ancestral sequence `S` that is a non-degenerate galled network shows that `M` is S-min (respectively S-min-1) decomposable. -/
theorem sMinDecomposable_of_galled {c : Crossover} {M : Finset (ι → Bool)} {S : ι → Bool} (hC : NoConstantColumn M) (N : Network ι V E) (hN : N.IsOptimalRooted c S M)
    (hg : N.IsGalled) (hnd : N.IsNonDegenerate) : SMinDecomposable c S M := by
  refine theorem5 hC N hN ?_
  rw [conflictGraph_labelSet_eq N hg hnd hN.2.1 hN.2.2.1]

omit [LinearOrder ι] [Finite ι] [Finite E] in
/-- Line 554 as printed holds when the ancestral sequence is a row. -/
theorem incompatible_labelSet_iff_of_mem {M : Finset (ι → Bool)} {S : ι → Bool} (N : Network ι V E) (hg : N.IsGalled) (hnd : N.IsNonDegenerate) (hd : N.Derives M) (hS : N.ancestral = S) (hSM : S ∈ M) (i j : ι) :
    Incompatible N.labelSet i j ↔ Incompatible M i j := by
  rw [incompatible_labelSet_iff N hg hnd hd hS, addRow_eq_of_mem hSM]

/-! ### The sentence as printed is false -/

/-- The sentence of line 554, as printed: "for any non-degenerate galled-network `N` for `M`, a pair of sites is incompatible in `L` if and only if it is incompatible in `M`". False: see below. -/
def GalledIncompatPrinted : Prop :=
  ∀ (m a b : ℕ) (M : Finset (Fin m → Bool)) (N : Network (Fin m) (Fin a) (Fin b)), NoConstantColumn M → N.Derives M → N.IsGalled → N.IsNonDegenerate →
    ∀ i j, Incompatible N.labelSet i j ↔ Incompatible M i j

/-- The labels of `galledNet`. -/
def galledLabels : List (List ℕ) :=
  [[0, 0, 0, 0], [1, 0, 0, 0], [0, 1, 0, 0], [1, 0, 0, 0], [1, 0, 1, 0], [0, 1, 0, 0], [0, 1, 0, 1], [1, 1, 0, 0], [1, 1, 0, 0]]

/-- The network of the counterexample. The root `0000` has children `1000` and `0100`, by the first two sites. Each of them has two leaves, a copy of it and one with one more site. The node `1100` is a recombination of the two children, with a leaf. -/
def galledNet : Network (Fin 4) (Fin 9) (Fin 9) where
  src := ![0, 0, 1, 1, 2, 2, 1, 2, 7]
  tgt := ![1, 2, 3, 4, 5, 6, 7, 7, 8]
  root := 0
  site := ![0, 1, 3, 5]
  label := fun v => ofBits (galledLabels.getD v.val [])
  simple := by decide +kernel
  acyclic := Network.acyclic_of_rank (fun v : Fin 9 => v.val) (by decide +kernel)
  root_iff := by decide +kernel
  inDegree_le_two := by decide +kernel
  site_not_recomb := by decide +kernel
  label_tree := by
    have key : ∀ (e : Fin 9) (i : Fin 4), e ≠ 6 → e ≠ 7 →
        (ofBits (galledLabels.getD ((![1, 2, 3, 4, 5, 6, 7, 7, 8] : Fin 9 → Fin 9) e).val []) : Fin 4 → Bool) i =
          if (![0, 1, 3, 5] : Fin 4 → Fin 9) i = e then !(ofBits (galledLabels.getD ((![0, 0, 1, 1, 2, 2, 1, 2, 7] : Fin 9 → Fin 9) e).val []) : Fin 4 → Bool) i
          else (ofBits (galledLabels.getD ((![0, 0, 1, 1, 2, 2, 1, 2, 7] : Fin 9 → Fin 9) e).val []) : Fin 4 → Bool) i := by
      decide +kernel
    intro e he i
    have h₆ : e ≠ 6 := by
      rintro rfl
      exact absurd (he 7 rfl) (by decide)
    have h₇ : e ≠ 7 := by
      rintro rfl
      exact absurd (he 6 rfl) (by decide)
    convert key e i h₆ h₇
  label_recomb := by decide +kernel

/-- The rows of the counterexample. -/
def galledRows : Finset (Fin 4 → Bool) :=
  {ofBits [1, 0, 0, 0], ofBits [1, 0, 1, 0], ofBits [0, 1, 0, 0], ofBits [0, 1, 0, 1], ofBits [1, 1, 0, 0]}

theorem galledNet_isRecomb : ∀ v, galledNet.IsRecomb v ↔ v = 7 := by
  unfold Network.IsRecomb
  decide +kernel

theorem galledNet_isTreeEdge : ∀ e, galledNet.IsHKTreeEdge e ↔ e ≠ 6 ∧ e ≠ 7 := by
  intro e
  unfold Network.IsHKTreeEdge
  rw [galledNet_isRecomb]
  revert e
  decide +kernel

theorem galledNet_isLeaf : ∀ v, galledNet.IsLeaf v ↔ v = 3 ∨ v = 4 ∨ v = 5 ∨ v = 6 ∨ v = 8 := by
  unfold Network.IsLeaf
  decide +kernel

theorem galledNet_derives : galledNet.Derives galledRows := by
  have h₁ : ∀ v : Fin 9, (v = 3 ∨ v = 4 ∨ v = 5 ∨ v = 6 ∨ v = 8) → galledNet.label v ∈ galledRows := by decide +kernel
  have h₂ : ∀ v w : Fin 9, (v = 3 ∨ v = 4 ∨ v = 5 ∨ v = 6 ∨ v = 8) → (w = 3 ∨ w = 4 ∨ w = 5 ∨ w = 6 ∨ w = 8) → galledNet.label v = galledNet.label w → v = w := by decide +kernel
  have h₃ : ∀ r ∈ galledRows, ∃ v : Fin 9, (v = 3 ∨ v = 4 ∨ v = 5 ∨ v = 6 ∨ v = 8) ∧ galledNet.label v = r := by decide +kernel
  refine ⟨fun v hv => h₁ v ((galledNet_isLeaf v).1 hv), fun v hv w hw h => h₂ v w ((galledNet_isLeaf v).1 hv) ((galledNet_isLeaf w).1 hw) h, fun r hr => ?_⟩
  obtain ⟨v, hv, hl⟩ := h₃ r hr
  exact ⟨v, (galledNet_isLeaf v).2 hv, hl⟩

theorem galledNet_isGalled : galledNet.IsGalled := by
  have hpairs : ∀ e f : Fin 9, e ≠ f → galledNet.tgt e = galledNet.tgt f → (e = 6 ∧ f = 7) ∨ (e = 7 ∧ f = 6) := by decide +kernel
  have hadj₁ : galledNet.hkTreeGraph.Adj 1 0 := by
    refine ⟨by decide, Or.inr ⟨0, (galledNet_isTreeEdge 0).2 (by decide), rfl, rfl⟩⟩
  have hadj₂ : galledNet.hkTreeGraph.Adj 0 2 := by
    refine ⟨by decide, Or.inl ⟨1, (galledNet_isTreeEdge 1).2 (by decide), rfl, rfl⟩⟩
  have hr : galledNet.hkTreeGraph.Reachable 1 2 := hadj₁.reachable.trans hadj₂.reachable
  intro e f hne ht
  rcases hpairs e f hne ht with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact hr
  · exact hr.symm

theorem galledNet_isNonDegenerate : galledNet.IsNonDegenerate := by
  refine ⟨fun e he => ?_, fun v hv => ?_⟩
  · have hne := (galledNet_isTreeEdge e).1 he
    have key : ∀ e : Fin 9, e ≠ 6 → e ≠ 7 → e = 0 ∨ e = 1 ∨ (galledNet.tgt e = 3 ∨ galledNet.tgt e = 4 ∨ galledNet.tgt e = 5 ∨ galledNet.tgt e = 6 ∨ galledNet.tgt e = 8) := by
      decide +kernel
    have hcases := key e hne.1 hne.2
    rcases hcases with rfl | rfl | h
    · exact ⟨3, (galledNet_isLeaf 3).2 (by decide), Relation.ReflTransGen.single ⟨2, (galledNet_isTreeEdge 2).2 (by decide), rfl, rfl⟩⟩
    · exact ⟨5, (galledNet_isLeaf 5).2 (by decide), Relation.ReflTransGen.single ⟨4, (galledNet_isTreeEdge 4).2 (by decide), rfl, rfl⟩⟩
    · exact ⟨_, (galledNet_isLeaf _).2 h, Relation.ReflTransGen.refl⟩
  · have hv₇ : v ≠ 7 := fun h => hv ((galledNet_isRecomb v).2 h)
    have key : ∀ v : Fin 9, v ≠ 7 → v = 0 ∨ v = 1 ∨ v = 2 ∨ (v = 3 ∨ v = 4 ∨ v = 5 ∨ v = 6 ∨ v = 8) := by
      decide +kernel
    have hcases := key v hv₇
    rcases hcases with rfl | rfl | rfl | h
    · exact Or.inr ⟨0, 1, by decide, rfl, rfl, (galledNet_isTreeEdge 0).2 (by decide), (galledNet_isTreeEdge 1).2 (by decide)⟩
    · exact Or.inr ⟨2, 3, by decide, rfl, rfl, (galledNet_isTreeEdge 2).2 (by decide), (galledNet_isTreeEdge 3).2 (by decide)⟩
    · exact Or.inr ⟨4, 5, by decide, rfl, rfl, (galledNet_isTreeEdge 4).2 (by decide), (galledNet_isTreeEdge 5).2 (by decide)⟩
    · exact Or.inl ((galledNet_isLeaf v).2 h)

/-- **Counterexample to the sentence of line 554** (`g:galled_false`). `M = {1000, 1010, 0100, 0101, 1100}`, with no constant column, on the non-degenerate galled network `galledNet` with ancestral sequence `0000`. The first two sites are compatible in `M`, which has `10`, `01`, `11` there and not `00`, and incompatible in `L`, which has the root. So `G(L) ≠ G(M)`.
The sentence holds with `M + S` in place of `M` (`incompatible_labelSet_iff`), which is what Theorem 5 needs. It also holds when `S ∈ M` (`incompatible_labelSet_iff_of_mem`). The definitions are those stated at the top of this module, not the text of Huson and Klöpper 2007, which wasn't read. -/
theorem galledIncompatPrinted_false : ¬ GalledIncompatPrinted := by
  intro h
  have hC : NoConstantColumn galledRows := by
    unfold NoConstantColumn
    decide +kernel
  have hiff := h 4 9 9 galledRows galledNet hC galledNet_derives galledNet_isGalled galledNet_isNonDegenerate 0 1
  have hL : Incompatible galledNet.labelSet 0 1 := by
    have hmem : ∀ v, galledNet.label v ∈ galledNet.labelSet := galledNet.label_mem_labelSet
    have hval : ∀ a b : Bool, ∃ v : Fin 9, galledNet.label v 0 = a ∧ galledNet.label v 1 = b := by decide +kernel
    intro a b
    obtain ⟨v, h₁, h₂⟩ := hval a b
    exact ⟨_, hmem v, h₁, h₂⟩
  have hM : ¬ Incompatible galledRows 0 1 := by
    have hno : ∀ r ∈ galledRows, ¬ (r 0 = false ∧ r 1 = false) := by decide +kernel
    intro hi
    obtain ⟨r, hr, h₁, h₂⟩ := hi false false
    exact hno r hr ⟨h₁, h₂⟩
  exact hM (hiff.1 hL)

end Gusfield2007
