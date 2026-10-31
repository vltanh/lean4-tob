module

public import External.AllmanEtAl2023.CutOrder
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Allman, Baños, Mitchell, Rhodes 2023: the tree of blobs of a species network

E. S. Allman, H. Baños, J. D. Mitchell, J. A. Rhodes, *The tree of blobs of a species network:
identifiability under the coalescent*, J. Math. Biol. 86 (2023), 10.

* `theorem2`, the B-quartet inference rule, is proved, from the description of the tree of blobs
  by cut edges.
* `lemma3` and `closure_complete`, the combinatorial content of Theorem 3, are proved: from the
  B-quartets detected on induced 4-taxon networks, the inference rule reaches all B-quartets.
* `Corollary1`, the CF-detectability of 4-blobs for generic parameters, is the assumed result;
  see `External/AllmanEtAl2023/README.md`.
-/

@[expose] public noncomputable section

open Phylogenetics Phylogenetics.RootedNetwork MeasureTheory Set
open scoped Classical

namespace External.AllmanEtAl2023

variable {V E X : Type*} [Fintype X] [DecidableEq X] {N : RootedNetwork V E X}

omit [Fintype X] in
theorem ne_of_card_five {a b c d e : X} (h : ({a, b, c, d, e} : Finset X).card = 5) :
    a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ a ≠ e ∧ b ≠ c ∧ b ≠ d ∧ b ≠ e ∧ c ≠ d ∧ c ≠ e ∧ d ≠ e := by
  have key : ∀ u v w z t : X, ({u, v, w, z, t} : Finset X).card = 5 → u ≠ v := by
    rintro u v w z t h rfl
    have : ({u, u, w, z, t} : Finset X).card ≤ 4 := by
      rw [Finset.insert_idem]; exact Finset.card_le_four
    omega
  refine ⟨key _ _ _ _ _ h, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · apply key a c b d e; rw [← h]; congr 1; grind
  · apply key a d b c e; rw [← h]; congr 1; grind
  · apply key a e b c d; rw [← h]; congr 1; grind
  · apply key b c a d e; rw [← h]; congr 1; grind
  · apply key b d a c e; rw [← h]; congr 1; grind
  · apply key b e a c d; rw [← h]; congr 1; grind
  · apply key c d a b e; rw [← h]; congr 1; grind
  · apply key c e a b d; rw [← h]; congr 1; grind
  · apply key d e a b c; rw [← h]; congr 1; grind

/-- A quartet tree displayed on the tree of blobs is a cut-edge split of its induced network, by
restriction of cut splits. -/
theorem inducedCutSplit_of_displays (hN : N.IsPhylogenetic) {s : QuartetTree X}
    (h : Displays (treeOfBlobs N) s) : InducedCutSplit N s := by
  obtain ⟨A, hA, hmem⟩ := h
  obtain ⟨-, -, hcut⟩ := (Finset.mem_filter.mp hA).2
  refine ⟨A ∩ s.taxa, hmem, ?_⟩
  obtain ⟨x, hx⟩ := Finset.card_pos.mp (by rw [s.2.2.1 _ hmem]; omega : 0 < (A ∩ s.taxa).card)
  have hother := TreeMetric.sdiff_mem_of_mem hmem
  obtain ⟨y, hy⟩ := Finset.card_pos.mp (by rw [s.2.2.1 _ hother]; omega :
    0 < (s.taxa \ (A ∩ s.taxa)).card)
  obtain ⟨hyt, hyA⟩ := Finset.mem_sdiff.mp hy
  have h1 : N.HasCutSplitOn (s.taxa : Set X) (A : Set X) :=
    hcut.hasCutSplitOn hN ⟨x, by simpa using (Finset.mem_inter.mp hx).2,
      by simpa using (Finset.mem_inter.mp hx).1⟩
      ⟨y, by simpa using hyt, fun hyA' => hyA (Finset.mem_inter.mpr ⟨by simpa using hyA', hyt⟩)⟩
  refine (hasCutSplitOn_congr ?_).mp h1
  ext z
  simp only [Set.mem_inter_iff, Finset.mem_coe, Finset.mem_inter]
  tauto

/-- A 4-taxon set with no cut-edge split on its induced network is a B-quartet. -/
theorem isBQuartet_of_not_isTreelike (hN : N.IsPhylogenetic) {t : Finset X}
    (ht : ¬ IsTreelike N t) : IsBQuartet N t :=
  fun s hs hd => ht ⟨s, hs, inducedCutSplit_of_displays hN hd⟩

/-- The quartet trees displayed on the tree of blobs are the cut-edge splits of the induced networks
on the 4-taxon sets that are not B-quartets. -/
theorem displays_treeOfBlobs_iff (hN : N.IsPhylogenetic) (s : QuartetTree X) :
    Displays (treeOfBlobs N) s ↔ InducedCutSplit N s ∧ ¬ IsBQuartet N s.taxa := by
  constructor
  · intro h
    exact ⟨inducedCutSplit_of_displays hN h,
      fun hB => hB s (Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩) h⟩
  · rintro ⟨h, hB⟩
    unfold IsBQuartet at hB
    push Not at hB
    obtain ⟨s', hs', hd⟩ := hB
    have heq := inducedCutSplit_unique hN (inducedCutSplit_of_displays hN hd) h
      (Finset.mem_filter.mp hs').2
    exact heq ▸ hd

private theorem isSplitFamily_treeOfBlobs (hN : N.IsPhylogenetic) (hX : 2 ≤ Fintype.card X) :
    IsSplitFamily (treeOfBlobs N) := by
  have : Nonempty X := Fintype.card_pos_iff.mp (by omega)
  exact (isUnrootedTree_iff hX _).mp (treeOfBlobs_isUnrootedTree hN)

/-- No side of the tree of blobs has `a, e` and not `u, v`, if `{a,e,u,v}` is a B-quartet or a cut-edge
split of its induced network separates `a, e`. -/
private theorem not_separating (hN : N.IsPhylogenetic) (hS : IsSplitFamily (treeOfBlobs N))
    {a e u v : X} (h : ({a, e, u, v} : Finset X).card = 4) {A : Finset X}
    (hA : A ∈ treeOfBlobs N) (ha : a ∈ A) (he : e ∈ A) (hu : u ∉ A) (hv : v ∉ A)
    (hrule : IsBQuartet N {a, e, u, v} ∨
      ∃ s ∈ treesOn ({a, e, u, v} : Finset X), InducedCutSplit N s ∧ Separated s a e) : False := by
  have hcut := (Finset.mem_filter.mp hA).2.2.2
  rcases hrule with hB | ⟨s, hs, hcs, hsep⟩
  · exact hB (quartetTree a e u v h)
      (Finset.mem_filter.mpr ⟨Finset.mem_univ _, TreeMetric.taxa_quartetTree h⟩)
      ((TreeMetric.displays_quartetTree_iff hS h).mpr ⟨A, hA, ha, he, hu, hv⟩)
  · have hst : s.taxa = {a, e, u, v} := (Finset.mem_filter.mp hs).2
    have hs₀ := inducedCutSplit_of_hasCutSplit hN hcut h ha he hu hv
    have heq := inducedCutSplit_unique hN hcs hs₀ (by rw [hst, TreeMetric.taxa_quartetTree])
    subst heq
    exact hsep.2.2 {a, e} (by simp) (by simp)

/-- The rule in the form used by the closure: its third hypothesis is that one of the three sets is a
B-quartet of the network, or has a cut-edge split separating `a, e` on its induced network. The side
of a split of the tree of blobs resolving one of the three sets is located by cases on the taxa: it
resolves `{a,b,c,d}` or `{b,c,d,e}`, or it separates `a, e` from `b, c, d`. -/
theorem rule_core (hN : N.IsPhylogenetic) {a b c d e : X} (h5 : ({a, b, c, d, e} : Finset X).card = 5)
    (habcd : IsBQuartet N {a, b, c, d}) (hbcde : IsBQuartet N {b, c, d, e})
    {t : Finset X} (ht : t ∈ ({{a, b, c, e}, {a, b, d, e}, {a, c, d, e}} : Finset (Finset X)))
    (hrule : IsBQuartet N t ∨ ∃ s ∈ treesOn t, InducedCutSplit N s ∧ Separated s a e)
    {q : Finset X} (hq : q ∈ ({{a, b, c, e}, {a, b, d, e}, {a, c, d, e}} : Finset (Finset X))) :
    IsBQuartet N q := by
  obtain ⟨hab, hac, had, hae, hbc, hbd, hbe, hcd, hce, hde⟩ := ne_of_card_five h5
  have hX : 2 ≤ Fintype.card X := by
    have := Finset.card_le_univ ({a, b, c, d, e} : Finset X)
    omega
  have hS := isSplitFamily_treeOfBlobs hN hX
  -- no side separates `a, e` from `b, c, d`
  have hsep : ∀ A ∈ treeOfBlobs N, a ∈ A → e ∈ A → b ∉ A → c ∉ A → d ∉ A → False := by
    intro A hA ha he hb hc hd
    simp only [Finset.mem_insert, Finset.mem_singleton] at ht
    rcases ht with rfl | rfl | rfl
    · have hset : ({a, b, c, e} : Finset X) = {a, e, b, c} := by grind
      rw [hset] at hrule
      exact not_separating hN hS (TreeMetric.card_four_of_ne hae hab hac hbe.symm hce.symm hbc) hA
        ha he hb hc hrule
    · have hset : ({a, b, d, e} : Finset X) = {a, e, b, d} := by grind
      rw [hset] at hrule
      exact not_separating hN hS (TreeMetric.card_four_of_ne hae hab had hbe.symm hde.symm hbd) hA
        ha he hb hd hrule
    · have hset : ({a, c, d, e} : Finset X) = {a, e, c, d} := by grind
      rw [hset] at hrule
      exact not_separating hN hS (TreeMetric.card_four_of_ne hae hac had hce.symm hde.symm hcd) hA
        ha he hc hd hrule
  have h4₁ : ({a, b, c, d} : Finset X).card = 4 := TreeMetric.card_four_of_ne hab hac had hbc hbd hcd
  have h4₂ : ({b, c, d, e} : Finset X).card = 4 := TreeMetric.card_four_of_ne hbc hbd hbe hcd hce hde
  have h1 := (TreeMetric.forall_not_displays_iff h4₁).mp habcd
  have h2 := (TreeMetric.forall_not_displays_iff h4₂).mp hbcde
  -- the side is located by cases on the taxa
  have hcontra : ∀ A ∈ treeOfBlobs N, ((a ∈ A ∧ e ∈ A ∧ b ∉ A ∧ c ∉ A ∧ d ∉ A) ∨
      (a ∉ A ∧ e ∉ A ∧ b ∈ A ∧ c ∈ A ∧ d ∈ A)) → False := by
    rintro A hA (⟨ha, he, hb, hc, hd⟩ | ⟨ha, he, hb, hc, hd⟩)
    · exact hsep A hA ha he hb hc hd
    · refine hsep Aᶜ (hS.compl_mem A hA) (Finset.mem_compl.mpr ha) (Finset.mem_compl.mpr he) ?_ ?_ ?_
      · simpa using hb
      · simpa using hc
      · simpa using hd
  simp only [Finset.mem_insert, Finset.mem_singleton] at hq
  rcases hq with rfl | rfl | rfl
  · have h4 := TreeMetric.card_four_of_ne hab hac hae hbc hbe hce
    refine (TreeMetric.forall_not_displays_iff h4).mpr fun A hA h3 => hcontra A hA ?_
    have h1' := h1 A hA
    have h2' := h2 A hA
    rw [TreeMetric.card_inter_four h4₁] at h1'
    rw [TreeMetric.card_inter_four h4₂] at h2'
    rw [TreeMetric.card_inter_four h4] at h3
    by_cases ha : a ∈ A <;> by_cases hb : b ∈ A <;> by_cases hc : c ∈ A <;> by_cases hd : d ∈ A <;>
      by_cases he : e ∈ A <;> simp only [ha, hb, hc, hd, he, ite_true, ite_false] at h1' h2' h3 <;>
      first | omega | simp [ha, hb, hc, hd, he]
  · have h4 := TreeMetric.card_four_of_ne hab had hae hbd hbe hde
    refine (TreeMetric.forall_not_displays_iff h4).mpr fun A hA h3 => hcontra A hA ?_
    have h1' := h1 A hA
    have h2' := h2 A hA
    rw [TreeMetric.card_inter_four h4₁] at h1'
    rw [TreeMetric.card_inter_four h4₂] at h2'
    rw [TreeMetric.card_inter_four h4] at h3
    by_cases ha : a ∈ A <;> by_cases hb : b ∈ A <;> by_cases hc : c ∈ A <;> by_cases hd : d ∈ A <;>
      by_cases he : e ∈ A <;> simp only [ha, hb, hc, hd, he, ite_true, ite_false] at h1' h2' h3 <;>
      first | omega | simp [ha, hb, hc, hd, he]
  · have h4 := TreeMetric.card_four_of_ne hac had hae hcd hce hde
    refine (TreeMetric.forall_not_displays_iff h4).mpr fun A hA h3 => hcontra A hA ?_
    have h1' := h1 A hA
    have h2' := h2 A hA
    rw [TreeMetric.card_inter_four h4₁] at h1'
    rw [TreeMetric.card_inter_four h4₂] at h2'
    rw [TreeMetric.card_inter_four h4] at h3
    by_cases ha : a ∈ A <;> by_cases hb : b ∈ A <;> by_cases hc : c ∈ A <;> by_cases hd : d ∈ A <;>
      by_cases he : e ∈ A <;> simp only [ha, hb, hc, hd, he, ite_true, ite_false] at h1' h2' h3 <;>
      first | omega | simp [ha, hb, hc, hd, he]

/-- **Theorem 2 of the source (B-quartet Inference Rule; TINNiK Theorem 2).** If `{a,b,c,d}`
and `{b,c,d,e}` are B-quartets of the network, and on the induced 4-taxon network one of
`{a,b,c,e}`, `{a,b,d,e}`, `{a,c,d,e}` is a T-quartet with `a, e` separated or a B-quartet, then all
three are B-quartets. The source treats binary networks; the binary condition is not needed. -/
theorem theorem2 (hN : N.IsPhylogenetic) {a b c d e : X} (h5 : ({a, b, c, d, e} : Finset X).card = 5)
    (habcd : IsBQuartet N {a, b, c, d}) (hbcde : IsBQuartet N {b, c, d, e})
    {t : Finset X} (ht : t ∈ ({{a, b, c, e}, {a, b, d, e}, {a, c, d, e}} : Finset (Finset X)))
    (hrule : ¬ IsTreelike N t ∨ ∃ s ∈ treesOn t, InducedCutSplit N s ∧ Separated s a e)
    {q : Finset X} (hq : q ∈ ({{a, b, c, e}, {a, b, d, e}, {a, c, d, e}} : Finset (Finset X))) :
    IsBQuartet N q :=
  rule_core hN h5 habcd hbcde ht (hrule.imp_left (isBQuartet_of_not_isTreelike hN)) hq

/-- The cut edges of the subgraph induced on `Y` resolve `q`: some arc is a cut on `Y` with exactly two
taxa of `q` below it. -/
def Resolves (N : RootedNetwork V E X) (Y q : Finset X) : Prop :=
  ∃ e, IsCutOn N Y e ∧ (q.filter (N.IsBelow e)).card = 2

omit [Fintype X] [DecidableEq X] in
/-- A cut-edge split on `Y` with two taxa of `q` on each side resolves `q`. -/
theorem resolves_of_hasCutSplitOn (hN : N.IsPhylogenetic) {Y q : Finset X} {A : Set X}
    (h : N.HasCutSplitOn (Y : Set X) A) (hq : q ⊆ Y) (h4 : q.card = 4)
    (h2 : (q.filter (· ∈ A)).card = 2) : Resolves N Y q := by
  obtain ⟨e, he, -, hor⟩ := exists_isCutOn_of_hasCutSplitOn hN h
  refine ⟨e, he, ?_⟩
  rcases hor with hor | hor
  · rw [← h2]
    congr 1
    exact Finset.filter_congr fun x hx => hor x (hq hx)
  · have h3 : (q.filter (· ∉ A)).card = 2 := by
      have := Finset.card_filter_add_card_filter_not (s := q) (· ∈ A)
      omega
    rw [← h3]
    congr 1
    exact Finset.filter_congr fun x hx => hor x (hq hx)

omit [Fintype X] in
/-- **Lemma 3 of the source**, in the fixed network, for the subgraphs induced on subsets `Y`.
Departure from the source (a cited result): the source builds a cycle through the arcs ancestral
to `α` and the two components of the induced graph without `e₀`. Here the same facts are read off
from domination: since `e₀` is not a cut on `Y`, the taxon `α` is below `e₀` and not dominated by it,
and any arc `f` resolving `{a,b,c,α}` on `Y \ {d}` is compared with `e₀`. -/
theorem lemma3 (hN : N.IsPhylogenetic) {Y : Finset X} {a b c d α : X} {e₀ : E}
    (h4 : ({a, b, c, d} : Finset X).card = 4) (ha : a ∈ Y) (hb : b ∈ Y) (hc : c ∈ Y) (hd : d ∈ Y)
    (hα : α ∈ Y) (hαa : α ≠ a) (hαb : α ≠ b) (hαc : α ≠ c) (hαd : α ≠ d)
    (hcut : ∀ x ∈ Y, x ≠ α → N.IsBelow e₀ x → N.Dominates e₀ x)
    (hor : (N.IsBelow e₀ a ∧ N.IsBelow e₀ b ∧ ¬ N.IsBelow e₀ c ∧ ¬ N.IsBelow e₀ d) ∨
      (¬ N.IsBelow e₀ a ∧ ¬ N.IsBelow e₀ b ∧ N.IsBelow e₀ c ∧ N.IsBelow e₀ d))
    (hB : ¬ Resolves N Y {a, b, c, d}) : ¬ Resolves N (Y.erase d) {a, b, c, α} := by
  obtain ⟨hab, hac, had, hbc, hbd, hcd⟩ := TreeMetric.ne_of_card_four h4
  have h4' : ({a, b, c, α} : Finset X).card = 4 :=
    TreeMetric.card_four_of_ne hab hac hαa.symm hbc hαb.symm hαc.symm
  have hq0 : (({a, b, c, d} : Finset X).filter (N.IsBelow e₀)).card = 2 := by
    rw [TreeMetric.card_filter_four h4]
    rcases hor with ⟨h1, h2, h3, h5⟩ | ⟨h1, h2, h3, h5⟩ <;> simp [h1, h2, h3, h5]
  -- `e₀` is not a cut on `Y`: `α` is below it and not dominated by it
  have hαB : N.IsBelow e₀ α := by
    by_contra hn
    exact hB ⟨e₀, fun x hx hb' => hcut x hx (fun h => hn (h ▸ hb')) hb', hq0⟩
  have hαD : ¬ N.Dominates e₀ α := by
    intro hD
    refine hB ⟨e₀, fun x hx hb' => ?_, hq0⟩
    by_cases hxα : x = α
    · exact hxα ▸ hD
    · exact hcut x hx hxα hb'
  have hαA : N.AvoidingReach e₀ N.root (N.leaf α) := not_not.mp hαD
  rintro ⟨f, hf, hf2⟩
  rw [TreeMetric.card_filter_four h4'] at hf2
  have hfY : ∀ x ∈ Y, x ≠ d → N.IsBelow f x → N.Dominates f x :=
    fun x hx hxd hb' => hf x (Finset.mem_erase.mpr ⟨hxd, hx⟩) hb'
  by_cases hαF : N.IsBelow f α
  · have hfα := hfY α hα hαd hαF
    have hne : e₀ ≠ f := by
      rintro rfl
      exact hαD hfα
    rcases order_of_isBelow_of_dominates hN hαB hfα hne with h1 | h1
    · -- `f` is below `e₀`
      have hu : ∃ u ∈ Y, u ≠ d ∧ u ≠ α ∧ N.IsBelow f u := by
        by_contra hno
        push Not at hno
        have h1 := hno a ha had hαa.symm
        have h2 := hno b hb hbd hαb.symm
        have h3 := hno c hc hcd hαc.symm
        simp [h1, h2, h3, hαF] at hf2
      obtain ⟨u, hu, hud, huα, Fu⟩ := hu
      have Bu := isBelow_of_above h1 Fu
      have Du := hcut u hu huα Bu
      have hav : N.AvoidingReach e₀ N.root (N.graph.source f) := by
        rcases avoiding_split e₀ f hαA with h' | ⟨h', -⟩
        · exact absurd h' hfα
        · exact h'
      rcases reaches_split e₀ Fu with h2 | ⟨h2, -⟩
      · exact Du ((hav.trans (avoiding_step hne.symm)).trans h2)
      · exact above_antisymm hN h1 h2
    · -- `f` is above `e₀`
      rcases hor with ⟨ba, bb, bc, bd⟩ | ⟨ba, bb, bc, bd⟩
      · have Fa := isBelow_of_above h1 ba
        have Fb := isBelow_of_above h1 bb
        simp only [Fa, Fb, hαF, ite_true] at hf2
        split_ifs at hf2 <;> omega
      · have Fc := isBelow_of_above h1 bc
        have Fd := isBelow_of_above h1 bd
        have hna : ¬ N.IsBelow f a ∧ ¬ N.IsBelow f b := by
          simp only [Fc, hαF, ite_true] at hf2
          split_ifs at hf2 with h1' h2'
          all_goals first | omega | exact ⟨‹_›, ‹_›⟩
        have Dd : N.Dominates f d := by
          intro hav
          rcases avoiding_split f e₀ hav with h' | ⟨h', -⟩
          · exact hcut d hd hαd.symm bd h'
          · rcases reaches_split f bc with h2 | ⟨h2, -⟩
            · exact hfY c hc hcd Fc ((h'.trans (avoiding_step hne)).trans h2)
            · exact above_antisymm hN h1 h2
        refine hB ⟨f, fun x hx hb' => ?_, ?_⟩
        · by_cases hxd : x = d
          · exact hxd ▸ Dd
          · exact hfY x hx hxd hb'
        · rw [TreeMetric.card_filter_four h4]
          simp [hna.1, hna.2, Fc, Fd]
  · have hne : e₀ ≠ f := by
      rintro rfl
      exact hαF hαB
    have hnot : ¬ N.graph.Reaches (N.graph.target f) (N.graph.source e₀) :=
      fun h => hαF (isBelow_of_above h hαB)
    have hsub : ∀ u ∈ Y, u ≠ d → N.IsBelow e₀ u → N.IsBelow f u →
        N.graph.Reaches (N.graph.target e₀) (N.graph.source f) := by
      intro u hu hud hbu hfu
      rcases order_of_isBelow_of_dominates hN hbu (hfY u hu hud hfu) hne with h | h
      · exact h
      · exact absurd h hnot
    simp only [hαF, ite_false, add_zero] at hf2
    have hor2 : N.IsBelow f a ∨ N.IsBelow f b := by
      by_contra hno
      push Not at hno
      simp only [hno.1, hno.2, ite_false] at hf2
      split_ifs at hf2 <;> omega
    -- from now on `f` has exactly `a, b` below it
    have hfinal : N.IsBelow f a ∧ N.IsBelow f b ∧ ¬ N.IsBelow f c ∧ ¬ N.IsBelow f d := by
      rcases hor with ⟨ba, bb, nc, nd⟩ | ⟨na, nb, bc, bd⟩
      · have hlow : N.graph.Reaches (N.graph.target e₀) (N.graph.source f) := by
          rcases hor2 with h | h
          · exact hsub a ha had ba h
          · exact hsub b hb hbd bb h
        have hFc : ¬ N.IsBelow f c := fun h => nc (isBelow_of_above hlow h)
        have hFd : ¬ N.IsBelow f d := fun h => nd (isBelow_of_above hlow h)
        simp only [hFc, ite_false, add_zero] at hf2
        split_ifs at hf2 with h1' h2'
        all_goals first | omega | exact ⟨‹_›, ‹_›, hFc, hFd⟩
      · have hFc : ¬ N.IsBelow f c := by
          intro Fc
          have hlow := hsub c hc hcd bc Fc
          rcases hor2 with h | h
          · exact na (isBelow_of_above hlow h)
          · exact nb (isBelow_of_above hlow h)
        have hFa : N.IsBelow f a ∧ N.IsBelow f b := by
          simp only [hFc, ite_false, add_zero] at hf2
          split_ifs at hf2 with h1' h2'
          all_goals first | omega | exact ⟨‹_›, ‹_›⟩
        have hFd : ¬ N.IsBelow f d := by
          intro Fd
          rcases order_of_isBelow_of_dominates hN Fd (hcut d hd hαd.symm bd) hne.symm with h | h
          · exact hnot h
          · exact na (isBelow_of_above h hFa.1)
        exact ⟨hFa.1, hFa.2, hFc, hFd⟩
    obtain ⟨Fa, Fb, Fc, Fd⟩ := hfinal
    refine hB ⟨f, fun x hx hb' => hfY x hx (fun h => Fd (h ▸ hb')) hb', ?_⟩
    rw [TreeMetric.card_filter_four h4]
    simp [Fa, Fb, Fc, Fd]

/-- The induction of the source's Theorem 3, on the taxa `Y` of the subgraph. -/
private theorem closure_aux (hN : N.IsPhylogenetic) (n : ℕ) :
    ∀ Y : Finset X, Y.card = n → ∀ q : Finset X, q.card = 4 → q ⊆ Y → ¬ Resolves N Y q →
      BInferred {q' | q'.card = 4 ∧ ¬ IsTreelike N q'} {s | InducedCutSplit N s} q := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro Y hY q hq hqY hR
    by_cases hYq : Y = q
    · -- the base case: `q` is not treelike
      subst hYq
      refine BInferred.base Y ⟨hq, ?_⟩
      rintro ⟨s, hs, B, hB, hcB⟩
      have hst : s.taxa = Y := (Finset.mem_filter.mp hs).2
      rw [hst] at hcB
      have hBs : B ⊆ Y := hst ▸ TreeMetric.subset_taxa_of_mem hB
      refine hR (resolves_of_hasCutSplitOn hN hcB (Finset.Subset.refl _) hq ?_)
      convert s.2.2.1 B hB using 2
      ext x
      simp only [Finset.mem_filter, Finset.mem_coe]
      exact ⟨fun h => h.2, fun h => ⟨hBs h, h⟩⟩
    obtain ⟨α, hαY, hαq⟩ : ∃ α ∈ Y, α ∉ q := by
      by_contra hno
      push Not at hno
      exact hYq (Finset.Subset.antisymm hno hqY)
    by_cases hRα : Resolves N (Y.erase α) q
    · obtain ⟨e₀, hcut, h2⟩ := hRα
      have hc2 : (q.filter fun x => ¬ N.IsBelow e₀ x).card = 2 := by
        have := Finset.card_filter_add_card_filter_not (s := q) (N.IsBelow e₀)
        omega
      obtain ⟨a, b, hab, hfa⟩ := Finset.card_eq_two.mp h2
      obtain ⟨c, d, hcd, hfc⟩ := Finset.card_eq_two.mp hc2
      have hmem₁ : ∀ x, x ∈ q ∧ N.IsBelow e₀ x ↔ x = a ∨ x = b := by
        intro x
        have := Finset.ext_iff.mp hfa x
        simpa only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton] using this
      have hmem₂ : ∀ x, x ∈ q ∧ ¬ N.IsBelow e₀ x ↔ x = c ∨ x = d := by
        intro x
        have := Finset.ext_iff.mp hfc x
        simpa only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton] using this
      obtain ⟨haq, Ba⟩ := (hmem₁ a).mpr (Or.inl rfl)
      obtain ⟨hbq, Bb⟩ := (hmem₁ b).mpr (Or.inr rfl)
      obtain ⟨hcq, Nc⟩ := (hmem₂ c).mpr (Or.inl rfl)
      obtain ⟨hdq, Nd⟩ := (hmem₂ d).mpr (Or.inr rfl)
      have hqe : q = {a, b, c, d} := by
        ext x
        simp only [Finset.mem_insert, Finset.mem_singleton]
        constructor
        · intro hx
          by_cases hbx : N.IsBelow e₀ x
          · rcases (hmem₁ x).mp ⟨hx, hbx⟩ with h | h
            · exact Or.inl h
            · exact Or.inr (Or.inl h)
          · rcases (hmem₂ x).mp ⟨hx, hbx⟩ with h | h
            · exact Or.inr (Or.inr (Or.inl h))
            · exact Or.inr (Or.inr (Or.inr h))
        · rintro (rfl | rfl | rfl | rfl) <;> assumption
      have h4 : ({a, b, c, d} : Finset X).card = 4 := hqe ▸ hq
      obtain ⟨hab', hac, had, hbc, hbd, hcd'⟩ := TreeMetric.ne_of_card_four h4
      have hαa : α ≠ a := fun h => hαq (h ▸ haq)
      have hαb : α ≠ b := fun h => hαq (h ▸ hbq)
      have hαc : α ≠ c := fun h => hαq (h ▸ hcq)
      have hαd : α ≠ d := fun h => hαq (h ▸ hdq)
      have ha := hqY haq
      have hb := hqY hbq
      have hc := hqY hcq
      have hd := hqY hdq
      have hcut' : ∀ x ∈ Y, x ≠ α → N.IsBelow e₀ x → N.Dominates e₀ x :=
        fun x hx hxα hb' => hcut x (Finset.mem_erase.mpr ⟨hxα, hx⟩) hb'
      rw [hqe] at hR
      -- Lemma 3, twice
      have hL₁ := lemma3 hN h4 ha hb hc hd hαY hαa hαb hαc hαd hcut' (Or.inl ⟨Ba, Bb, Nc, Nd⟩) hR
      have h4r : ({d, c, b, a} : Finset X).card = 4 :=
        TreeMetric.card_four_of_ne hcd'.symm hbd.symm had.symm hbc.symm hac.symm hab'.symm
      have hL₂ := lemma3 hN h4r hd hc hb ha hαY hαd hαc hαb hαa hcut' (Or.inr ⟨Nd, Nc, Bb, Ba⟩)
        (by
          rwa [show ({d, c, b, a} : Finset X) = {a, b, c, d} by
            ext x; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto])
      -- the inductive hypothesis puts them in the closure
      have hlt₁ : (Y.erase d).card < n := by
        rw [Finset.card_erase_of_mem hd, hY]
        have := Finset.card_pos.mpr ⟨d, hd⟩
        omega
      have hlt₂ : (Y.erase a).card < n := by
        rw [Finset.card_erase_of_mem ha, hY]
        have := Finset.card_pos.mpr ⟨d, hd⟩
        omega
      have hI₁ := ih _ hlt₁ (Y.erase d) rfl {a, b, c, α}
        (TreeMetric.card_four_of_ne hab' hac hαa.symm hbc hαb.symm hαc.symm)
        (by
          intro x hx
          simp only [Finset.mem_insert, Finset.mem_singleton] at hx
          rcases hx with rfl | rfl | rfl | rfl
          · exact Finset.mem_erase.mpr ⟨had, ha⟩
          · exact Finset.mem_erase.mpr ⟨hbd, hb⟩
          · exact Finset.mem_erase.mpr ⟨hcd', hc⟩
          · exact Finset.mem_erase.mpr ⟨hαd, hαY⟩) hL₁
      have hI₂ := ih _ hlt₂ (Y.erase a) rfl {d, c, b, α}
        (TreeMetric.card_four_of_ne hcd'.symm hbd.symm hαd.symm hbc.symm hαc.symm hαb.symm)
        (by
          intro x hx
          simp only [Finset.mem_insert, Finset.mem_singleton] at hx
          rcases hx with rfl | rfl | rfl | rfl
          · exact Finset.mem_erase.mpr ⟨had.symm, hd⟩
          · exact Finset.mem_erase.mpr ⟨hac.symm, hc⟩
          · exact Finset.mem_erase.mpr ⟨hab'.symm, hb⟩
          · exact Finset.mem_erase.mpr ⟨hαa, hαY⟩) hL₂
      rw [show ({d, c, b, α} : Finset X) = {b, c, α, d} by
        ext x; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto] at hI₂
      -- `ab|cd` is a cut-edge split on its induced network, which separates `a, d`
      have hs : InducedCutSplit N (quartetTree a b c d h4) := by
        refine ⟨{a, b}, by simp, ?_⟩
        rw [TreeMetric.taxa_quartetTree]
        have hcq' : IsCutOn N {a, b, c, d} e₀ := fun x hx hb' =>
          hcut x (Finset.mem_erase.mpr ⟨fun h => hαq (hqe ▸ h ▸ hx), hqY (hqe ▸ hx)⟩) hb'
        refine hasCutSplitOn_of_isCutOn hN hcq' (fun x hx => ?_) (x := a) (by simp) Ba
        simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
          Set.mem_singleton_iff]
        exact ⟨fun hb' => (hmem₁ x).mp ⟨hqe ▸ hx, hb'⟩, fun h => ((hmem₁ x).mpr h).2⟩
      have h5 : ({a, b, c, α, d} : Finset X).card = 5 := by
        have hαn : α ∉ ({d} : Finset X) := by simpa using hαd
        rw [Finset.card_insert_of_notMem (by simp [hab', hac, had, hαa.symm]),
          Finset.card_insert_of_notMem (by simp [hbc, hbd, hαb.symm]),
          Finset.card_insert_of_notMem (by simp [hcd', hαc.symm]), Finset.card_pair hαd]
      have hsep : Separated (quartetTree a b c d h4) a d := by
        refine ⟨by simp, by simp, fun B hB ⟨h1, h2⟩ => ?_⟩
        simp only [TreeMetric.val_quartetTree, Finset.mem_insert, Finset.mem_singleton] at hB
        rcases hB with rfl | rfl
        · simp only [Finset.mem_insert, Finset.mem_singleton] at h2
          rcases h2 with h2 | h2
          · exact had h2.symm
          · exact hbd h2.symm
        · simp only [Finset.mem_insert, Finset.mem_singleton] at h1
          rcases h1 with h1 | h1
          · exact hac h1
          · exact had h1
      rw [hqe]
      exact BInferred.ruleT a b c α d (quartetTree a b c d h4) {a, b, c, d} h5 hI₁ hI₂ hs
        (by rw [TreeMetric.taxa_quartetTree]; simp) hsep (by simp)
    · -- `α` can be removed
      have hlt : (Y.erase α).card < n := by
        rw [Finset.card_erase_of_mem hαY, hY]
        have := Finset.card_pos.mpr ⟨α, hαY⟩
        omega
      refine ih _ hlt (Y.erase α) rfl q hq (fun x hx => ?_) hRα
      exact Finset.mem_erase.mpr ⟨fun h => hαq (h ▸ hx), hqY hx⟩

/-- **Theorem 3 of the source, combinatorial part.** From the 4-taxon sets with no cut-edge split on
their induced networks, and the quartet trees of the others, the closure under the inference rule
reaches every B-quartet of the network. With soundness (`theorem2`) this is what Theorem 3 uses of
Theorem 1. The induction is on the taxa of an induced subgraph, as in the source: if a taxon can be removed
with `q` staying unresolved, it is removed; otherwise `q` is inferred from Lemma 3, applied twice, by Inference
Rule (a). The source first passes to one representative taxon per component at the blob; the removal
step subsumes this. Departure from the source: Lemma 3 is proved without its cycle (see `lemma3`). -/
theorem closure_complete (hN : N.IsPhylogenetic) {q : Finset X} (hq : q.card = 4)
    (hB : IsBQuartet N q) :
    BInferred {q' | q'.card = 4 ∧ ¬ IsTreelike N q'} {s | InducedCutSplit N s} q := by
  refine closure_aux hN _ Finset.univ rfl q hq (Finset.subset_univ _) ?_
  rintro ⟨e, he, h2⟩
  have hbelow : (q.filter (N.IsBelow e)).Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨x, hx⟩ := hbelow
  obtain ⟨hxq, hxb⟩ := Finset.mem_filter.mp hx
  have hc2 : (q.filter fun x => ¬ N.IsBelow e x).card = 2 := by
    have := Finset.card_filter_add_card_filter_not (s := q) (N.IsBelow e)
    omega
  obtain ⟨y, hy⟩ : (q.filter fun x => ¬ N.IsBelow e x).Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨hyq, hyb⟩ := Finset.mem_filter.mp hy
  let A : Finset X := Finset.univ.filter (N.IsBelow e)
  have hcut : N.HasCutSplit (A : Set X) := by
    refine (hasCutSplit_iff_hasCutSplitOn_univ hN _).mpr ?_
    have := hasCutSplitOn_of_isCutOn hN he (A := (A : Set X)) (fun x _ => by simp [A]) (x := x)
      (Finset.mem_univ _) hxb
    simpa using this
  have hA : A ∈ treeOfBlobs N := by
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨x, by simpa [A] using hxb⟩,
      ⟨y, by simpa [A] using hyb⟩, hcut⟩
  have hinter : A ∩ q = q.filter (N.IsBelow e) := by
    ext z
    simp only [Finset.mem_inter, Finset.mem_filter, Finset.mem_univ, true_and, A]
    tauto
  exact (TreeMetric.forall_not_displays_iff hq).mp hB A hA (hinter ▸ h2)

/-- Soundness of the closure: everything the rule infers from the 4-taxon sets with no cut-edge split
on their induced networks is a B-quartet. -/
theorem closure_sound (hN : N.IsPhylogenetic) {q : Finset X}
    (h : BInferred {q' | q'.card = 4 ∧ ¬ IsTreelike N q'} {s | InducedCutSplit N s} q) :
    IsBQuartet N q := by
  induction h with
  | base q hq => exact isBQuartet_of_not_isTreelike hN hq.2
  | ruleB a b c d e t q h5 _ _ ht _ hq ih₁ ih₂ ih₃ => exact rule_core hN h5 ih₁ ih₂ ht (Or.inl ih₃) hq
  | ruleT a b c d e s q h5 _ _ hs hst hsep hq ih₁ ih₂ =>
    exact rule_core hN h5 ih₁ ih₂ hst
      (Or.inr ⟨s, Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩, hs, hsep⟩) hq

end External.AllmanEtAl2023
