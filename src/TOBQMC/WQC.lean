module

public import Basic.Defs
public import Basic.LocalObjective
public import External.AneEtAl2024.Exchangeability
public import Phylogenetics.NMSC.Basic
public import Phylogenetics.Tree.Detach
public import Mathlib.Probability.StrongLaw

/-!
# TOB-QMC §4.1–4.2: quartet-based species tree methods give a refinement of the tree of blobs

Definition 1, Equations (1)–(4), Lemma 3, the perturbation Lemma 4 of the Supplement, Theorem 1 and the
ASTRAL corollary. These results use the exchangeability of taxa on one side of a cut edge
(`External.AneEtAl2024.exchangeability`).

The route of Lemma 3 is the paper's. If every maximizer of the blob `v` part of the score broke a block,
detaching the taxa of a broken block and reattaching them to a best taxon of that block (`detachReattach`,
`vertexPart_detachReattach`, `exists_block_side`), for all broken blocks (`exists_all_blocks_side`), would
give a maximizer that does not: a contradiction (`exists_vertex_maximizer`). Such a maximizer is binary after removing all but one taxon from each block
(`isBinaryTree_pullTree_of_vertex_maximizer`): a refinement of the restricted tree, with the removed taxa
reattached (`reattach`), would gain at every choice of the representatives, and the gain on all the taxa, times the number of choices, is the sum of these gains (`vertexPart_lt_reattach`). Contracting the edges inside blocks leaves a family of
unions of blocks (`displays_filter_isBlockUnion`). These families and the tree of blobs have a common
refinement, the compatibility supertree of the paper, which is `splice`.
-/

@[expose] public noncomputable section

open Phylogenetics Phylogenetics.RootedNetwork Finset Filter Topology MeasureTheory ProbabilityTheory
open scoped Classical

namespace TOBQMC

variable {V E X : Type*} [Fintype X] [DecidableEq X]

/-- The arcs of the display tree of the choice `c`. -/
def displayArcs (N : RootedNetwork V E X) (c : V → E) : Set E :=
  {e | N.IsTreeArc e ∨ e = c (N.graph.target e)}

/-- A taxon is below an arc in the display tree of the choice `c`. -/
def BelowInDisplay (N : RootedNetwork V E X) (c : V → E) (u : V) (x : X) : Prop :=
  Relation.ReflTransGen (fun a b => ∃ f ∈ displayArcs N c, N.graph.source f = a ∧ N.graph.target f = b)
    u (N.leaf x)

/-- The network displays the quartet tree `s`: some display tree restricted to the taxa of `s` has
an edge with one cherry of `s` below it. -/
def NetworkDisplays (N : RootedNetwork V E X) (s : QuartetTree X) : Prop :=
  ∃ c, IsParentChoice N c ∧ ∃ e ∈ displayArcs N c,
    (s.taxa.filter fun x => BelowInDisplay N c (N.graph.target e) x) ∈ s.val

/-- **Definition 1** (`tob2025:definition1`), quartet-nonanomalous: every induced 4-taxon network
displays more than one quartet tree, or displays one, which has the largest concordance factor. -/
def IsQuartetNonanomalous (N : RootedNetwork V E X) (F : QuartetTree X → ℝ) : Prop :=
  ∀ q : Finset X, q.card = 4 →
    (∃ s ∈ treesOn q, ∃ s' ∈ treesOn q, s ≠ s' ∧ NetworkDisplays N s ∧ NetworkDisplays N s') ∨
    ∃ s ∈ treesOn q, NetworkDisplays N s ∧ ∀ r ∈ s.alternatives, F r < F s

/-- The tree part `QS^tree` of the quartet score of `t`: the quartet trees on the 4-taxon sets that `TN`
resolves. -/
def treePart (TN : Finset (Finset X)) (F : QuartetTree X → ℝ) (t : Finset (Finset X)) : ℝ :=
  ∑ s, if (∃ r ∈ treesOn s.taxa, Displays TN r) ∧ Displays t s then F s else 0

/-- The star part `QS^star` of the quartet score of `t`: the 4-taxon sets that `TN` does not resolve. -/
def starPart (TN : Finset (Finset X)) (F : QuartetTree X → ℝ) (t : Finset (Finset X)) : ℝ :=
  ∑ s, if (∀ r ∈ treesOn s.taxa, ¬ Displays TN r) ∧ Displays t s then F s else 0

/-- The part `QS^v` of the quartet score of `t` from the 4-taxon sets around the vertex `P` of `TN`. -/
def vertexPart (P : Finset (Finset X)) (F : QuartetTree X → ℝ) (t : Finset (Finset X)) : ℝ :=
  ∑ s, if InDistinctBlocks P s.taxa ∧ Displays t s then F s else 0

/-- Equation (4) (`tob2025:equation4`): the part `QS^{v(x)}` of the quartet score of `t` from the 4-taxon
sets around the vertex `P` containing the taxon `x`. -/
def vertexTaxonPart (P : Finset (Finset X)) (x : X) (F : QuartetTree X → ℝ)
    (t : Finset (Finset X)) : ℝ :=
  ∑ s, if InDistinctBlocks P s.taxa ∧ x ∈ s.taxa ∧ Displays t s then F s else 0

/-- **Equation (1)** (`tob2025:equation1`). -/
theorem equation1 (TN : Finset (Finset X)) (F : QuartetTree X → ℝ) (t : Finset (Finset X)) :
    quartetSupport F t = treePart TN F t + starPart TN F t := by
  unfold quartetSupport treePart starPart
  rw [← sum_add_distrib]
  refine sum_congr rfl fun s _ => ?_
  by_cases hD : Displays t s
  · by_cases hR : ∃ r ∈ treesOn s.taxa, Displays TN r
    · have e1 : ((∃ r ∈ treesOn s.taxa, Displays TN r) ∧ Displays t s) = True := eq_true ⟨hR, hD⟩
      have e2 : ((∀ r ∈ treesOn s.taxa, ¬ Displays TN r) ∧ Displays t s) = False :=
        eq_false fun h => by
          obtain ⟨r, h1, h2⟩ := hR
          exact h.1 r h1 h2
      simp only [e1, e2]
      simp only [hD, ↓reduceIte, add_zero]
    · have e1 : ((∃ r ∈ treesOn s.taxa, Displays TN r) ∧ Displays t s) = False :=
        eq_false fun h => hR h.1
      have e2 : ((∀ r ∈ treesOn s.taxa, ¬ Displays TN r) ∧ Displays t s) = True :=
        eq_true ⟨fun r h1 h2 => hR ⟨r, h1, h2⟩, hD⟩
      simp only [e1, e2]
      simp only [hD, ↓reduceIte, zero_add]
  · simp only [hD, and_false, ↓reduceIte, add_zero]

/-- The tree part as a sum over the sets of four taxa that `TN` resolves. -/
theorem treePart_eq_sum (TN : Finset (Finset X)) (F : QuartetTree X → ℝ) (t : Finset (Finset X)) :
    treePart TN F t = ∑ q ∈ powersetCard 4 (univ : Finset X),
      if ∃ r ∈ treesOn q, Displays TN r then quartetPart F t q else 0 := by
  have := sum_ite_eq_sum_powersetCard (fun q => ∃ r ∈ treesOn q, Displays TN r) F t
  unfold treePart
  convert this

/-- The star part as a sum over the sets of four taxa that `TN` does not resolve. -/
theorem starPart_eq_sum (TN : Finset (Finset X)) (F : QuartetTree X → ℝ) (t : Finset (Finset X)) :
    starPart TN F t = ∑ q ∈ powersetCard 4 (univ : Finset X),
      if ∀ r ∈ treesOn q, ¬ Displays TN r then quartetPart F t q else 0 := by
  have := sum_ite_eq_sum_powersetCard (fun q => ∀ r ∈ treesOn q, ¬ Displays TN r) F t
  unfold starPart
  convert this

/-- **Equation (2)** (`tob2025:equation2`). For a T-quartet-nonanomalous network, the tree part of the
score is larger at any tree resolving `T_N`, in particular at `T_N`, than at a tree not resolving it.
The score of a tree that resolves `T_N` is that of `T_N`. -/
theorem equation2 {V E : Type*} {N : RootedNetwork V E X} (hN : N.IsPhylogenetic)
    {F : QuartetTree X → ℝ} (hF : ∀ s, 0 < F s) (hNon : IsTQuartetNonanomalous N F)
    {B T : Finset (Finset X)} (hB : IsUnrootedTree B) (hBT : treeOfBlobs N ⊆ B)
    (hT : IsBinaryTree T) (hTN : ¬ treeOfBlobs N ⊆ T) :
    treePart (treeOfBlobs N) F T < treePart (treeOfBlobs N) F B := by
  have hX : Nonempty X := by
    obtain ⟨A, hA, -⟩ := not_subset.1 hTN
    obtain ⟨x, -⟩ := (mem_filter.1 hA).2.1
    exact ⟨x⟩
  have hTB : IsUnrootedTree (treeOfBlobs N) := treeOfBlobs_isUnrootedTree hN
  have hT' := hT.isUnrootedTree
  have hp : ∀ s, 0 ≤ F s := fun s => (hF s).le
  obtain ⟨r₀, hr₀, hnot⟩ : ∃ r, Displays (treeOfBlobs N) r ∧ ¬ Displays T r := by
    by_contra hcon
    push Not at hcon
    exact hTN (subset_of_forall_displays hT' hTB hcon)
  rw [treePart_eq_sum, treePart_eq_sum]
  refine sum_lt_sum (fun q hq => ?_) ⟨r₀.taxa, mem_powersetCard.2 ⟨subset_univ _, r₀.card_taxa⟩, ?_⟩
  · by_cases hR : ∃ r ∈ treesOn q, Displays (treeOfBlobs N) r
    · obtain ⟨r, hr, hdr⟩ := id hR
      have hrq := mem_treesOn.1 hr
      subst hrq
      simp only [hR, ↓reduceIte]
      rw [quartetPart_of_displays hB F (hdr.mono hBT)]
      by_cases hd : Displays T r
      · exact (quartetPart_of_displays hT' F hd).le
      · exact (quartetPart_lt_of_not_displays hT' hp (hNon r hdr) hd).le
    · simp only [hR, ↓reduceIte, le_refl]
  · have hR : ∃ r ∈ treesOn r₀.taxa, Displays (treeOfBlobs N) r := ⟨r₀, mem_treesOn.2 rfl, hr₀⟩
    simp only [hR, ↓reduceIte]
    rw [quartetPart_of_displays hB F (hr₀.mono hBT)]
    exact quartetPart_lt_of_not_displays hT' hp (hNon r₀ hr₀) hnot

/-- **Equation (3)** (`tob2025:equation3`). The star part is the sum over the vertices of degree greater
than three of `T_N` of their parts. -/
theorem equation3 {TN : Finset (Finset X)} (hTN : IsUnrootedTree TN) (F : QuartetTree X → ℝ)
    (t : Finset (Finset X)) :
    starPart TN F t = ∑ P ∈ multifurcations TN, vertexPart P F t := by
  have hc : ∑ P ∈ multifurcations TN, vertexPart P F t =
      ∑ s, ∑ P ∈ multifurcations TN, if InDistinctBlocks P s.taxa ∧ Displays t s then F s else 0 := by
    simp only [vertexPart]
    exact sum_comm
  rw [hc, starPart]
  refine sum_congr rfl fun s _ => ?_
  by_cases hD : Displays t s
  · by_cases hS : ∀ r ∈ treesOn s.taxa, ¬ Displays TN r
    · obtain ⟨P₀, ⟨hP₀, hI⟩, huniq⟩ := existsUnique_center hTN s.card_taxa hS
      have e1 : ((∀ r ∈ treesOn s.taxa, ¬ Displays TN r) ∧ Displays t s) = True := eq_true ⟨hS, hD⟩
      rw [sum_eq_single_of_mem P₀ hP₀ fun P hP hne =>
        ite_eq_right fun h => hne (huniq P ⟨hP, h.1⟩)]
      simp only [e1]
      simp only [hI, hD, and_self, ↓reduceIte]
    · have e1 : ((∀ r ∈ treesOn s.taxa, ¬ Displays TN r) ∧ Displays t s) = False :=
        eq_false fun h => hS h.1
      rw [sum_eq_zero]
      · simp only [e1, ↓reduceIte]
      · intro P hP
        refine ite_eq_right fun h => hS fun r hr hdr => ?_
        exact not_displays_of_inDistinctBlocks (mem_multifurcations.1 hP).1 (s := r)
          ((mem_treesOn.1 hr) ▸ h.1) hdr
  · rw [sum_eq_zero fun P _ => ite_eq_right fun h => hD h.2]
    simp only [hD, and_false, ↓reduceIte]

section DetachScore

variable {P : Finset (Finset X)} {B₀ : Finset X} {a b : X}

omit [Fintype X] in
theorem swap_mem_block_iff (hd : ∀ B ∈ P, ∀ C ∈ P, B ≠ C → Disjoint B C) (hB₀ : B₀ ∈ P)
    (ha : a ∈ B₀) (hb : b ∈ B₀) {C : Finset X} (hC : C ∈ P) (x : X) :
    Equiv.swap a b x ∈ C ↔ x ∈ C := by
  by_cases he : C = B₀
  · subst he
    by_cases hxa : x = a
    · subst hxa
      simp [ha, hb]
    by_cases hxb : x = b
    · subst hxb
      simp [ha, hb]
    rw [Equiv.swap_apply_of_ne_of_ne hxa hxb]
  · have hdis := hd C hC B₀ hB₀ he
    have haC : a ∉ C := fun h => disjoint_left.1 hdis h ha
    have hbC : b ∉ C := fun h => disjoint_left.1 hdis h hb
    by_cases hxa : x = a
    · subst hxa
      simp [haC, hbC]
    by_cases hxb : x = b
    · subst hxb
      simp [haC, hbC]
    rw [Equiv.swap_apply_of_ne_of_ne hxa hxb]

omit [Fintype X] in
/-- Exchanging two taxa of a block keeps quartets in distinct blocks. -/
theorem inDistinctBlocks_map_swap (hd : ∀ B ∈ P, ∀ C ∈ P, B ≠ C → Disjoint B C) (hB₀ : B₀ ∈ P)
    (ha : a ∈ B₀) (hb : b ∈ B₀) (s : QuartetTree X) :
    InDistinctBlocks P (s.map (Equiv.swap a b).injective).taxa ↔ InDistinctBlocks P s.taxa := by
  rw [QuartetTree.map_taxa]
  unfold InDistinctBlocks
  refine forall₂_congr fun C hC => ?_
  have : C ∩ s.taxa.image (Equiv.swap a b) = (C ∩ s.taxa).image (Equiv.swap a b) := by
    ext y
    simp only [mem_inter, mem_image]
    constructor
    · rintro ⟨h1, x, h2, rfl⟩
      exact ⟨x, ⟨(swap_mem_block_iff hd hB₀ ha hb hC x).1 h1, h2⟩, rfl⟩
    · rintro ⟨x, ⟨h1, h2⟩, rfl⟩
      exact ⟨(swap_mem_block_iff hd hB₀ ha hb hC x).2 h1, x, h2, rfl⟩
  rw [this, card_image_of_injective _ (Equiv.swap a b).injective]

omit [Fintype X] in
/-- Taxa of a block are exchangeable (ii of the paper's lines 480-482): the block is a cut side, with
`a`, `b` on it and the other three taxa off it. -/
theorem cutExchangeable_map_swap {N : RootedNetwork V E X} {F : QuartetTree X → ℝ}
    (hEx : CutExchangeable N F) (hcut : N.HasCutSplit (B₀ : Set X)) (hB₀ : B₀ ∈ P)
    (ha : a ∈ B₀) (hb : b ∈ B₀) (hab : a ≠ b) {s : QuartetTree X} (hbs : b ∈ s.taxa)
    (hI : InDistinctBlocks P s.taxa) : F s = F (s.map (Equiv.swap a b).injective) := by
  have hone := card_le_one.1 (hI B₀ hB₀)
  have has : a ∉ s.taxa := fun h =>
    hab (hone a (mem_inter.2 ⟨ha, h⟩) b (mem_inter.2 ⟨hb, hbs⟩))
  refine hEx s _ b a hbs has ?_ ⟨B₀, hcut, hb, ha, ?_⟩
  · rw [QuartetTree.map_val]
    refine image_congr fun C hC => ?_
    have haC : a ∉ C := fun h => has (s.subset_taxa hC h)
    by_cases hbC : b ∈ C
    · simp only [hbC, ↓reduceIte]
      ext z
      simp only [mem_image, mem_insert, mem_erase]
      constructor
      · rintro ⟨y, hy, rfl⟩
        by_cases hyb : y = b
        · subst hyb
          simp
        · have hya : y ≠ a := fun e => haC (e ▸ hy)
          rw [Equiv.swap_apply_of_ne_of_ne hya hyb]
          exact Or.inr ⟨hyb, hy⟩
      · rintro (rfl | ⟨hz, hzC⟩)
        · exact ⟨b, hbC, by simp⟩
        · have hza : z ≠ a := fun e => haC (e ▸ hzC)
          exact ⟨z, hzC, Equiv.swap_apply_of_ne_of_ne hza hz⟩
    · simp only [hbC, ↓reduceIte]
      ext z
      simp only [mem_image]
      constructor
      · rintro ⟨y, hy, rfl⟩
        have hya : y ≠ a := fun e => haC (e ▸ hy)
        have hyb : y ≠ b := fun e => hbC (e ▸ hy)
        rwa [Equiv.swap_apply_of_ne_of_ne hya hyb]
      · intro hz
        have hza : z ≠ a := fun e => haC (e ▸ hz)
        have hzb : z ≠ b := fun e => hbC (e ▸ hz)
        exact ⟨z, hz, Equiv.swap_apply_of_ne_of_ne hza hzb⟩
  · refine disjoint_left.2 fun y hy hy' => ?_
    obtain ⟨hyb, hyt⟩ := mem_erase.1 hy'
    exact hyb (hone y (mem_inter.2 ⟨hy, hyt⟩) b (mem_inter.2 ⟨hb, hbs⟩))

/-- The score after detaching `b` and reattaching it as sister to `a` (the paper's lines 479-482):
`QS^v(T) - QS^{v(b)}(T) + QS^{v(a)}(T)`, by the bijection `{b,x,y,z} ↔ {a,x,y,z}` and exchangeability. -/
theorem vertexPart_detachReattach {N : RootedNetwork V E X} {F : QuartetTree X → ℝ}
    (hEx : CutExchangeable N F) (hd : ∀ B ∈ P, ∀ C ∈ P, B ≠ C → Disjoint B C)
    (hcut : N.HasCutSplit (B₀ : Set X)) (hB₀ : B₀ ∈ P) (ha : a ∈ B₀) (hb : b ∈ B₀) (hab : a ≠ b)
    (T : Finset (Finset X)) :
    vertexPart P F (detachReattach a b T) =
      vertexPart P F T - vertexTaxonPart P b F T + vertexTaxonPart P a F T := by
  let G : QuartetTree X → ℝ := fun s =>
    if InDistinctBlocks P s.taxa ∧ b ∉ s.taxa ∧ Displays T s then F s else 0
  have h1 : vertexPart P F (detachReattach a b T) = ∑ s, G s +
      ∑ s : QuartetTree X, if InDistinctBlocks P s.taxa ∧ b ∈ s.taxa ∧
        Displays (detachReattach a b T) s then F s else 0 := by
    rw [vertexPart, ← sum_add_distrib]
    refine sum_congr rfl fun s _ => ?_
    by_cases hbs : b ∈ s.taxa
    · simp only [G, hbs, not_true_eq_false, true_and, false_and, and_false, ↓reduceIte, zero_add]
    · simp only [G, hbs, not_false_eq_true, true_and, false_and, and_false, ↓reduceIte, add_zero,
        displays_detachReattach_of_not_mem hbs]
  have h2 : vertexPart P F T = ∑ s, G s + vertexTaxonPart P b F T := by
    rw [vertexPart, vertexTaxonPart, ← sum_add_distrib]
    refine sum_congr rfl fun s _ => ?_
    by_cases hbs : b ∈ s.taxa
    · simp only [G, hbs, not_true_eq_false, true_and, false_and, and_false, ↓reduceIte, zero_add]
    · simp only [G, hbs, not_false_eq_true, true_and, false_and, and_false, ↓reduceIte, add_zero]
  have h3 : (∑ s : QuartetTree X, if InDistinctBlocks P s.taxa ∧ b ∈ s.taxa ∧
      Displays (detachReattach a b T) s then F s else 0) = vertexTaxonPart P a F T := by
    have hbij : Function.Bijective
        (QuartetTree.map (X := X) (Equiv.swap a b).injective) :=
      (QuartetTree.map_injective (Equiv.swap a b).injective).bijective_of_finite
    rw [vertexTaxonPart]
    refine Eq.trans ?_ (hbij.sum_comp _)
    refine sum_congr rfl fun s _ => ?_
    have hmem : a ∈ (s.map (Equiv.swap a b).injective).taxa ↔ b ∈ s.taxa := by
      rw [QuartetTree.map_taxa, mem_image]
      constructor
      · rintro ⟨y, hy, he⟩
        have : y = b := (Equiv.swap a b).injective (he.trans (by simp))
        exact this ▸ hy
      · exact fun h => ⟨b, h, by simp⟩
    simp only [inDistinctBlocks_map_swap hd hB₀ ha hb s]
    by_cases hI : InDistinctBlocks P s.taxa
    · by_cases hbs : b ∈ s.taxa
      · have has : a ∉ s.taxa := fun h =>
          hab (card_le_one.1 (hI B₀ hB₀) a (mem_inter.2 ⟨ha, h⟩) b (mem_inter.2 ⟨hb, hbs⟩))
        have hF := cutExchangeable_map_swap hEx hcut hB₀ ha hb hab hbs hI
        simp only [hI, hbs, hmem, true_and, displays_detachReattach_of_mem hbs has, ← hF]
      · have e1 : (a ∈ (s.map (Equiv.swap a b).injective).taxa) = False := eq_false fun h =>
          hbs (hmem.1 h)
        simp only [hbs, e1, false_and, and_false, ↓reduceIte]
    · simp only [hI, false_and, ↓reduceIte]
  rw [h1, h3, h2]
  ring

/-- Detaching `b` does not change the partial score of another taxon of its block: a quartet around
the vertex with that taxon does not contain `b`. This is why the paper's "repeating for all `b`" can
keep the taxon `a` chosen at the start. -/
theorem vertexTaxonPart_detachReattach_of_ne {F : QuartetTree X → ℝ} (hB₀ : B₀ ∈ P) {c : X}
    (hc : c ∈ B₀) (hb : b ∈ B₀) (hcb : c ≠ b) (T : Finset (Finset X)) :
    vertexTaxonPart P c F (detachReattach a b T) = vertexTaxonPart P c F T := by
  unfold vertexTaxonPart
  refine sum_congr rfl fun s _ => ?_
  by_cases h : InDistinctBlocks P s.taxa ∧ c ∈ s.taxa
  · have hbs : b ∉ s.taxa := fun hbs =>
      hcb (card_le_one.1 (h.1 B₀ hB₀) c (mem_inter.2 ⟨hc, h.2⟩) b (mem_inter.2 ⟨hb, hbs⟩))
    simp only [displays_detachReattach_of_not_mem hbs]
  · have e : ∀ D : Prop, (InDistinctBlocks P s.taxa ∧ c ∈ s.taxa ∧ D) = False := fun D =>
      eq_false fun h' => h ⟨h'.1, h'.2.1⟩
    simp only [e, ↓reduceIte]

/-- One block `P_j`: detach every other taxon of the block and reattach it to the chosen taxon `a`
(the paper's lines 476-485), with the paper's two cases, `QS^{v(a)} = QS^{v(b)}` and `QS^{v(a)} > QS^{v(b)}`.
The result has the block as a side, its blob `v` score is not smaller, and the other blocks that were
sides stay sides. The paper applies this to a block that `T*` breaks; the step itself does not use that. -/
theorem exists_block_side {N : RootedNetwork V E X} {F : QuartetTree X → ℝ}
    (hEx : CutExchangeable N F) (hd : ∀ B ∈ P, ∀ C ∈ P, B ≠ C → Disjoint B C)
    (hcut : N.HasCutSplit (B₀ : Set X)) (hB₀ : B₀ ∈ P) (hne : B₀.Nonempty) (hne' : B₀ᶜ.Nonempty)
    {T : Finset (Finset X)} (hT : IsUnrootedTree T) (hX : 2 ≤ Fintype.card X) :
    ∃ T', IsUnrootedTree T' ∧ B₀ ∈ T' ∧ vertexPart P F T ≤ vertexPart P F T' ∧
      ∀ C ∈ P, C ≠ B₀ → C ∈ T → C ∈ T' := by
  obtain ⟨a, haB, hamax⟩ := B₀.exists_max_image (fun x => vertexTaxonPart P x F T) hne
  have key : ∀ D : Finset X, D ⊆ B₀.erase a → ∃ T', IsUnrootedTree T' ∧ insert a D ∈ T' ∧
      vertexPart P F T ≤ vertexPart P F T' ∧
      (∀ c ∈ B₀, c ∉ D → vertexTaxonPart P c F T' = vertexTaxonPart P c F T) ∧
      ∀ C ∈ P, C ≠ B₀ → C ∈ T → C ∈ T' := by
    intro D
    induction D using Finset.induction_on with
    | empty =>
      intro _
      exact ⟨T, hT, (hT.isSplitFamily hX).singleton_mem a, le_refl _, fun _ _ _ => rfl,
        fun _ _ _ h => h⟩
    | insert b D hbD ih =>
      intro hsub
      have hbmem := hsub (mem_insert_self b D)
      obtain ⟨hba, hbB⟩ := mem_erase.1 hbmem
      obtain ⟨T₁, hT₁, hside, hle, hpart, hother⟩ :=
        ih fun x hx => hsub (mem_insert_of_mem hx)
      have hDsub : ∀ x ∈ insert a D, x ∈ B₀ := by
        intro x hx
        rcases mem_insert.1 hx with rfl | hx
        · exact haB
        · exact (mem_erase.1 (hsub (mem_insert_of_mem hx))).2
      have hbnot : b ∉ insert a D := by
        simp only [mem_insert, not_or]
        exact ⟨hba, hbD⟩
      refine ⟨detachReattach a b T₁, detachReattach_isUnrootedTree hT₁ (Ne.symm hba), ?_, ?_, ?_, ?_⟩
      · have : insert a (insert b D) = insert b (insert a D) := insert_comm _ _ _
        rw [this]
        refine insert_mem_detachReattach hside (mem_insert_self _ _) hbnot ?_
        obtain ⟨y, hy⟩ := hne'
        refine ⟨y, mem_compl.2 fun h => mem_compl.1 hy ?_⟩
        rcases mem_insert.1 h with rfl | h
        · exact hbB
        · exact hDsub y h
      · have hstep : vertexPart P F (detachReattach a b T₁) = vertexPart P F T₁ -
            vertexTaxonPart P b F T + vertexTaxonPart P a F T := by
          rw [vertexPart_detachReattach hEx hd hcut hB₀ haB hbB (Ne.symm hba),
            hpart b hbB hbD, hpart a haB (fun h =>
              (mem_erase.1 (hsub (mem_insert_of_mem h))).1 rfl)]
        -- the paper's two cases: the same blob `v` score, or a greater one
        rcases (hamax b hbB).eq_or_lt with heq | hlt
        · rw [hstep, heq, sub_add_cancel]
          exact hle
        · rw [hstep]
          linarith
      · intro c hc hcn
        have hcb : c ≠ b := fun e => hcn (e ▸ mem_insert_self _ _)
        rw [vertexTaxonPart_detachReattach_of_ne hB₀ hc hbB hcb]
        exact hpart c hc fun h => hcn (mem_insert_of_mem h)
      · intro C hC hCB hCT
        have hdis := hd C hC B₀ hB₀ hCB
        exact mem_detachReattach_of_not_mem hT₁ (hother C hC hCB hCT)
          (fun h => disjoint_left.1 hdis h haB) (fun h => disjoint_left.1 hdis h hbB)
  obtain ⟨T', hT', hside, hle, -, hother⟩ := key (B₀.erase a) (Subset.refl _)
  rw [insert_erase haB] at hside
  exact ⟨T', hT', hside, hle, hother⟩

/-- All blocks (the paper's "repeating for all `b` and all `P_j`", line 485). While the tree breaks a block
`P_j`, so that no edge induces `P_j | S \ P_j`, apply the detachment at `P_j`. The block becomes a side and
the blocks that were sides stay sides, so fewer blocks are broken. -/
theorem exists_all_blocks_side {N : RootedNetwork V E X} {F : QuartetTree X → ℝ} {TN : Finset (Finset X)}
    (hEx : CutExchangeable N F) (hTN : IsUnrootedTree TN) (hV : IsVertexPartition TN P)
    (hcut : ∀ B ∈ P, N.HasCutSplit (B : Set X)) {T : Finset (Finset X)} (hT : IsUnrootedTree T)
    (hX : 2 ≤ Fintype.card X) :
    ∃ T', IsUnrootedTree T' ∧ (∀ C ∈ P, C ∈ T') ∧ vertexPart P F T ≤ vertexPart P F T' := by
  have key : ∀ (n : ℕ) (T : Finset (Finset X)), IsUnrootedTree T →
      (P.filter fun C => C ∉ T).card < n →
      ∃ T', IsUnrootedTree T' ∧ (∀ C ∈ P, C ∈ T') ∧ vertexPart P F T ≤ vertexPart P F T' := by
    intro n
    induction n with
    | zero => exact fun _ _ h => absurd h (Nat.not_lt_zero _)
    | succ n ih =>
      intro T hT hn
      by_cases hall : ∀ C ∈ P, C ∈ T
      · exact ⟨T, hT, hall, le_refl _⟩
      · -- a block `P_j` that `T` breaks
        push Not at hall
        obtain ⟨Pj, hPj, hPjT⟩ := hall
        have hPjS := hV.mem Pj hPj
        obtain ⟨T₁, hT₁, hside, hle, hother⟩ := exists_block_side (F := F) hEx hV.pairwiseDisjoint
          (hcut Pj hPj) hPj (hTN.nonempty_of_mem hPjS) (hTN.nonempty_of_mem (hTN.compl_mem hPjS)) hT hX
        have hlt : (P.filter fun C => C ∉ T₁).card < (P.filter fun C => C ∉ T).card := by
          refine card_lt_card ⟨fun C hC => ?_, fun hsub => ?_⟩
          · obtain ⟨hCP, hCT₁⟩ := mem_filter.1 hC
            refine mem_filter.2 ⟨hCP, fun hCT => hCT₁ (hother C hCP ?_ hCT)⟩
            rintro rfl
            exact hCT₁ hside
          · exact (mem_filter.1 (hsub (mem_filter.2 ⟨hPj, hPjT⟩))).2 hside
        obtain ⟨T', hT', hall', hle'⟩ := ih T₁ hT₁ (by omega)
        exact ⟨T', hT', hall', hle.trans hle'⟩
  exact key _ T hT (Nat.lt_succ_self _)

/-- **The claim of the paper's lines 464-466**, by the contradiction of its lines 472-486. There is a tree
`B*(v)` that (1) maximizes `QS^v` and (2) does not break apart the blocks of `P`. Suppose that all
maximizers violate (2), and let `T*` be one, with a block `P_j` that it breaks. Detaching the taxa of `P_j`
and reattaching them to a best taxon of `P_j` does not lower the score, and repeating for all blocks gives a
tree with a blob `v` score at least that of `T*`, hence a maximizer, that satisfies (2). -/
theorem exists_vertex_maximizer {N : RootedNetwork V E X} {F : QuartetTree X → ℝ}
    {TN : Finset (Finset X)} (hEx : CutExchangeable N F) (hTN : IsUnrootedTree TN)
    (hV : IsVertexPartition TN P) (hcut : ∀ B ∈ P, N.HasCutSplit (B : Set X))
    (hX : 2 ≤ Fintype.card X) :
    ∃ T', IsUnrootedTree T' ∧ (∀ C ∈ P, C ∈ T') ∧
      ∀ T, IsUnrootedTree T → vertexPart P F T ≤ vertexPart P F T' := by
  -- suppose that all trees that maximize `QS^v` violate property (2)
  by_contra hcon
  have hviolate : ∀ T', IsUnrootedTree T' →
      (∀ T, IsUnrootedTree T → vertexPart P F T ≤ vertexPart P F T') → ∃ C ∈ P, C ∉ T' := by
    intro T' hT' hmax
    by_contra hall
    push Not at hall
    exact hcon ⟨T', hT', hall, hmax⟩
  -- let `T*` be one such tree: there is a block `P_j` such that no edge in `T*` induces `P_j | S \ P_j`
  obtain ⟨Tstar, hTstar, hmax⟩ := (univ.filter fun T : Finset (Finset X) => IsUnrootedTree T).exists_max_image
    (vertexPart P F) ⟨TN, by simpa using hTN⟩
  have hTstar' : IsUnrootedTree Tstar := (mem_filter.1 hTstar).2
  have hmax' : ∀ T, IsUnrootedTree T → vertexPart P F T ≤ vertexPart P F Tstar :=
    fun T hT => hmax T (by simpa using hT)
  obtain ⟨Pj, hPj, -⟩ := hviolate Tstar hTstar' hmax'
  -- detach each `b ∈ P_j` and reattach it to the chosen `a ∈ P_j`
  have hPjS := hV.mem Pj hPj
  obtain ⟨T₁, hT₁, -, hle₁, -⟩ := exists_block_side (F := F) hEx hV.pairwiseDisjoint (hcut Pj hPj) hPj
    (hTN.nonempty_of_mem hPjS) (hTN.nonempty_of_mem (hTN.compl_mem hPjS)) hTstar' hX
  -- repeating for all `P_j` yields a tree with property (2) and score at least that of `T*`
  obtain ⟨T', hT', hall, hle⟩ := exists_all_blocks_side (F := F) hEx hTN hV hcut hT₁ hX
  -- it is a maximizer, so it violates property (2): a contradiction
  obtain ⟨C, hC, hCT'⟩ := hviolate T' hT' fun T hT => (hmax' T hT).trans (hle₁.trans hle)
  exact hCT' (hall C hC)

/-- `QS^v`, multiplied by the number of representative tuples of the blocks, is the sum over the tuples of
its inner sums, each read on the taxa of the tuple. -/
theorem prod_card_mul_vertexPart (hd : ∀ B ∈ P, ∀ C ∈ P, B ≠ C → Disjoint B C)
    (hcover : P.sup id = univ) (F : QuartetTree X → ℝ) (T : Finset (Finset X)) :
    (∏ B ∈ P, (B.card : ℝ)) * vertexPart P F T =
      ∑ y ∈ (univ : Finset ({B // B ∈ P} → X)).filter (fun y => ∀ B, y B ∈ B.val),
        innerSum P F T y :=
  prod_card_mul_sum_eq_sum_innerSum hd hcover F T

/-- The gain in `QS^v` between two trees, multiplied by the number of representative tuples, is the sum of
the gains at the tuples. -/
theorem prod_card_mul_vertexPart_sub (hd : ∀ B ∈ P, ∀ C ∈ P, B ≠ C → Disjoint B C)
    (hcover : P.sup id = univ) (F : QuartetTree X → ℝ) (T T₁ : Finset (Finset X)) :
    (∏ B ∈ P, (B.card : ℝ)) * (vertexPart P F T₁ - vertexPart P F T) =
      ∑ y ∈ (univ : Finset ({B // B ∈ P} → X)).filter (fun y => ∀ B, y B ∈ B.val),
        (innerSum P F T₁ y - innerSum P F T y) := by
  rw [mul_sub, prod_card_mul_vertexPart hd hcover, prod_card_mul_vertexPart hd hcover, sum_sub_distrib]

/-- **The refinement step of the paper's lines 490-492.** Let `T'` have the blocks as sides, and let `R` be a
proper refinement of its restriction to the representatives `x`. Reattaching the removed taxa to `R` gains
at every representative tuple `y`, not only at `x`: `T'` has the same restriction to `y`, and a refinement
increases a score with positive weights. The gain on all the taxa, times the number of tuples, is the sum of these gains over the tuples (`prod_card_mul_vertexPart_sub`), which is the paper's "the score increase would be amplified after
reattaching the removed taxa". -/
theorem vertexPart_lt_reattach {F : QuartetTree X → ℝ} (hF : ∀ s, 0 < F s)
    (hd : ∀ B ∈ P, ∀ C ∈ P, B ≠ C → Disjoint B C) (hcover : P.sup id = univ) (hP : 2 ≤ P.card)
    {T' : Finset (Finset X)} (hT' : IsUnrootedTree T') (hall : ∀ C ∈ P, C ∈ T')
    {x : {B // B ∈ P} → X} (hx : IsRepTuple P x) {R : Finset (Finset {B // B ∈ P})}
    (hR : IsUnrootedTree R) (hsub : pullTree x T' ⊂ R) :
    vertexPart P F T' < vertexPart P F (reattach P T' R) := by
  have hne : ∀ B ∈ P, B.Nonempty := fun B hB => hT'.nonempty_of_mem (hall B hB)
  have hY : 2 ≤ Fintype.card {B // B ∈ P} := by rwa [Fintype.card_coe]
  have hW : 0 < ∏ B ∈ P, (B.card : ℝ) :=
    prod_pos fun B hB => by exact_mod_cast card_pos.2 (hne B hB)
  have hT'' := reattach_isUnrootedTree hd hcover hT' hall hR hx hsub.subset hP
  have hgain : ∀ y ∈ (univ : Finset ({B // B ∈ P} → X)).filter (fun y => ∀ B, y B ∈ B.val),
      0 < innerSum P F (reattach P T' R) y - innerSum P F T' y := by
    intro y hy
    have hy' : IsRepTuple P y := (mem_filter.1 hy).2
    rw [sub_pos, innerSum_eq_quartetSupport_pullTree hd hy', innerSum_eq_quartetSupport_pullTree hd hy']
    refine quartetSupport_lt_of_ssubset (fun s₀ => mul_pos (blockSizeProd_pos hne s₀) (hF _))
      (pullTree_isUnrootedTree (hy'.injective hd) hT' hY)
      (pullTree_isUnrootedTree (hy'.injective hd) hT'' hY) ?_
    rw [pullTree_eq_of_forall_mem hd hcover hT' hall hy' hx]
    exact Finset.ssubset_of_ssubset_of_subset hsub (subset_pullTree_reattach hd hR hy')
  have hsum := sum_pos hgain ⟨x, mem_filter.2 ⟨mem_univ x, hx⟩⟩
  rw [← prod_card_mul_vertexPart_sub hd hcover] at hsum
  exact sub_pos.1 ((mul_pos_iff_of_pos_left hW).1 hsum)

/-- **The second observation of the paper (lines 489-492).** `B*(v)` is binary after removing all but one
taxon from each block. By contradiction: a refinement of the modified tree, with the removed taxa
reattached, would increase `QS^v`. -/
theorem isBinaryTree_pullTree_of_vertex_maximizer {F : QuartetTree X → ℝ} (hF : ∀ s, 0 < F s)
    {TN : Finset (Finset X)} (hV : IsVertexPartition TN P) {T' : Finset (Finset X)}
    (hT' : IsUnrootedTree T') (hall : ∀ C ∈ P, C ∈ T')
    (hmax : ∀ T, IsUnrootedTree T → vertexPart P F T ≤ vertexPart P F T')
    {x : {B // B ∈ P} → X} (hx : IsRepTuple P x) : IsBinaryTree (pullTree x T') := by
  have hP : 2 ≤ P.card := by
    have := hV.three_le
    omega
  have hd := hV.pairwiseDisjoint
  have hY : 2 ≤ Fintype.card {B // B ∈ P} := by rwa [Fintype.card_coe]
  -- suppose that the restriction is not binary, and refine it
  by_contra hnb
  obtain ⟨R, hR, hsub⟩ := exists_ssubset_of_not_isBinaryTree
    (pullTree_isUnrootedTree (hx.injective hd) hT' hY) hnb
  -- reattaching the removed taxa gives a tree with a larger score
  exact absurd (hmax _ (reattach_isUnrootedTree hd hV.cover hT' hall hR hx hsub.subset hP))
    (not_le.2 (vertexPart_lt_reattach hF hd hV.cover hP hT' hall hx hR hsub))

/-- The second observation in terms of all the taxa: `B*(v)` resolves every set of four taxa in distinct
blocks, since these taxa lie among some representatives of the blocks. -/
theorem displays_of_vertex_maximizer {F : QuartetTree X → ℝ} (hF : ∀ s, 0 < F s)
    {TN : Finset (Finset X)} (hV : IsVertexPartition TN P) {T' : Finset (Finset X)}
    (hT' : IsUnrootedTree T') (hall : ∀ C ∈ P, C ∈ T')
    (hmax : ∀ T, IsUnrootedTree T → vertexPart P F T ≤ vertexPart P F T') {q : Finset X}
    (hq : q.card = 4) (hI : InDistinctBlocks P q) : ∃ s ∈ treesOn q, Displays T' s := by
  obtain ⟨x, hx, hqx⟩ := exists_isRepTuple_superset
    (fun B hB => hT'.nonempty_of_mem (hall B hB)) hV.cover hI
  have hinj := hx.injective hV.pairwiseDisjoint
  have himg : (univ.filter fun b => x b ∈ q).image x = q := by
    ext y
    simp only [mem_image, mem_filter, mem_univ, true_and]
    constructor
    · rintro ⟨b, hb, rfl⟩
      exact hb
    · intro hy
      obtain ⟨b, -, rfl⟩ := mem_image.1 (hqx hy)
      exact ⟨b, hy, rfl⟩
  obtain ⟨s₀, hs₀, hds⟩ := (isBinaryTree_pullTree_of_vertex_maximizer hF hV hT' hall hmax
    hx).exists_displays (q := univ.filter fun b => x b ∈ q) (by
      rw [← card_image_of_injective _ hinj, himg, hq])
  refine ⟨s₀.map hinj, mem_treesOn.2 ?_, (displays_pullTree_iff hinj s₀).1 hds⟩
  rw [QuartetTree.map_taxa, mem_treesOn.1 hs₀, himg]

/-- **The third observation of the paper (lines 492-496).** Keeping the sides of `T'` that are unions of
blocks contracts the edges inside blocks: on quartets in distinct blocks, nothing changes. -/
theorem displays_filter_isBlockUnion {T' : Finset (Finset X)} (hT' : IsUnrootedTree T')
    (hall : ∀ C ∈ P, C ∈ T') {s : QuartetTree X} (hI : InDistinctBlocks P s.taxa) :
    Displays T' s ↔ ∃ A ∈ T'.filter (IsBlockUnion P), A ∩ s.taxa ∈ s.val := by
  constructor
  · rintro ⟨A, hA, hAs⟩
    refine ⟨A, mem_filter.2 ⟨hA, fun B hB => ?_⟩, hAs⟩
    have hc := s.card_of_mem hAs
    have hc' := s.card_of_mem (s.sdiff_mem hAs)
    have h1 := hI B hB
    rcases hT'.compatible hA (hall B hB) with h | h | h | h
    · have := card_le_card (show A ∩ s.taxa ⊆ B ∩ s.taxa from inter_subset_inter_right h)
      omega
    · exact Or.inl h
    · exact Or.inr h.symm
    · have hsub : s.taxa \ (A ∩ s.taxa) ⊆ B ∩ s.taxa := by
        intro x hx
        obtain ⟨hx1, hx2⟩ := mem_sdiff.1 hx
        have : x ∈ A ∪ B := h ▸ mem_univ x
        rcases mem_union.1 this with h3 | h3
        · exact absurd (mem_inter.2 ⟨h3, hx1⟩) hx2
        · exact mem_inter.2 ⟨h3, hx1⟩
      have := card_le_card hsub
      omega
  · rintro ⟨A, hA, hAs⟩
    exact ⟨A, (mem_filter.1 hA).1, hAs⟩

theorem isBlockFamily_filter {T' : Finset (Finset X)} (hT' : IsUnrootedTree T') :
    IsBlockFamily P (T'.filter (IsBlockUnion P)) := by
  refine ⟨fun A hA => (mem_filter.1 hA).2, fun A hA => hT'.nonempty_of_mem (mem_filter.1 hA).1,
    fun A hA => hT'.nonempty_of_mem (hT'.compl_mem (mem_filter.1 hA).1), fun A hA => ?_,
    fun A hA B hB => hT'.compatible (mem_filter.1 hA).1 (mem_filter.1 hB).1⟩
  exact mem_filter.2 ⟨hT'.compl_mem (mem_filter.1 hA).1, (mem_filter.1 hA).2.compl⟩

end DetachScore

/-- **Lemma 3** (`tob2025:lemma3`), in the form its proof gives, for weights `F` with the properties that
the proof uses:
there is a binary refinement `B` of the tree of blobs that maximizes the star part of the score over binary trees, and has a larger score than every binary tree not refining the tree of
blobs. The compatibility supertree of the paper's lines 497-498 (Warnow, Chapters 3, 7: compatible
splits have a common refinement) is `splice`, by `splice_isUnrootedTree`. The strictness of the paper's
(2) needs that the quartets a tree displays determine its splits (`subset_of_forall_displays`). -/
theorem lemma3_of_properties {V E : Type*} {N : RootedNetwork V E X} (hN : N.IsPhylogenetic)
    {F : QuartetTree X → ℝ} (hF : ∀ s, 0 < F s) (hEx : CutExchangeable N F)
    (hNon : IsTQuartetNonanomalous N F) (hX : 4 ≤ Fintype.card X) :
    ∃ B, IsBinaryTree B ∧ treeOfBlobs N ⊆ B ∧
      (∀ T, IsBinaryTree T → starPart (treeOfBlobs N) F T ≤ starPart (treeOfBlobs N) F B) ∧
      ∀ T, IsBinaryTree T → ¬ treeOfBlobs N ⊆ T → quartetSupport F T < quartetSupport F B := by
  have hX' : 2 ≤ Fintype.card X := by omega
  have : Nonempty X := Fintype.card_pos_iff.1 (by omega)
  set TN := treeOfBlobs N with hTNdef
  have hTN : IsUnrootedTree TN := treeOfBlobs_isUnrootedTree hN
  -- at each multifurcation, a maximizer `B*(v)` and its local family
  have hM : ∀ P ∈ multifurcations TN, ∃ L₀, IsBlockFamily P L₀ ∧
      (∀ q : Finset X, q.card = 4 → InDistinctBlocks P q →
        ∃ s ∈ treesOn q, ∃ A ∈ L₀, A ∩ s.taxa ∈ s.val) ∧
      ∀ L : Finset (Finset X) → Finset (Finset X), (∀ P ∈ multifurcations TN, IsBlockFamily P (L P)) →
        L P = L₀ → ∀ T, IsUnrootedTree T → vertexPart P F T ≤ vertexPart P F (splice TN L) := by
    intro P hP
    obtain ⟨hV, -⟩ := mem_multifurcations.1 hP
    have hcut : ∀ B ∈ P, N.HasCutSplit (B : Set X) := fun B hB =>
      (mem_filter.1 (hV.mem B hB)).2.2.2
    obtain ⟨T', hT', hall, hmax⟩ := exists_vertex_maximizer (F := F) hEx hTN hV hcut hX'
    refine ⟨T'.filter (IsBlockUnion P), isBlockFamily_filter hT', ?_, ?_⟩
    · intro q hq hI
      obtain ⟨s, hs, hds⟩ := displays_of_vertex_maximizer hF hV hT' hall hmax hq hI
      exact ⟨s, hs, (displays_filter_isBlockUnion hT' hall ((mem_treesOn.1 hs) ▸ hI)).1 hds⟩
    · intro L hL hLP T hT
      refine (hmax T hT).trans (le_of_eq ?_)
      unfold vertexPart
      refine sum_congr rfl fun s _ => ?_
      by_cases hI : InDistinctBlocks P s.taxa
      · have hiff : Displays T' s ↔ Displays (splice TN L) s := by
          rw [displays_filter_isBlockUnion hT' hall hI, displays_splice_iff hTN hL hP hI, hLP]
        simp only [hI, hiff, true_and]
      · simp only [hI, false_and, ↓reduceIte]
  choose! L hLfam hLres hLmax using hM
  -- the compatibility supertree is the splice
  have hBtree : IsUnrootedTree (splice TN L) := splice_isUnrootedTree hTN hLfam
  have hBbin : IsBinaryTree (splice TN L) := by
    refine isBinaryTree_of_forall_displays hBtree fun q hq => ?_
    by_cases hstar : ∀ r ∈ treesOn q, ¬ Displays TN r
    · obtain ⟨P, ⟨hP, hI⟩, -⟩ := existsUnique_center hTN hq hstar
      obtain ⟨s, hs, A, hA, hAs⟩ := hLres P hP q hq hI
      exact ⟨s, hs, A, mem_splice.2 (Or.inr ⟨P, hP, hA⟩), hAs⟩
    · push Not at hstar
      obtain ⟨r, hr, hdr⟩ := hstar
      exact ⟨r, hr, hdr.mono (subset_splice TN L)⟩
  have hstarle : ∀ T, IsBinaryTree T → starPart TN F T ≤ starPart TN F (splice TN L) := by
    intro T hT
    rw [equation3 hTN, equation3 hTN]
    exact sum_le_sum fun P hP => hLmax P hP L hLfam rfl T hT.isUnrootedTree
  refine ⟨splice TN L, hBbin, subset_splice TN L, hstarle, fun T hT hne => ?_⟩
  rw [equation1 TN F T, equation1 TN F (splice TN L)]
  exact add_lt_add_of_lt_of_le (equation2 hN hF hNon hBtree (subset_splice TN L) hT hne)
    (hstarle T hT)

/-- **Lemma 3** (`tob2025:lemma3`). For a network under the standard
assumptions that is T-quartet-nonanomalous, with the exact expected concordance factors, there is a
binary refinement of the tree of blobs with higher quartet score than every binary tree that does
not refine it. -/
theorem lemma3 [Fintype V] [Fintype E] {N : RootedNetwork V E X} {θ : MetricData E} {ρ : ℝ}
    (hStd : StandardAssumptions N θ ρ)
    (hNon : IsTQuartetNonanomalous N (nmscCF N θ ρ)) (hX : 4 ≤ Fintype.card X) :
    ∃ B, IsBinaryTree B ∧ treeOfBlobs N ⊆ B ∧ ∀ T, IsBinaryTree T → ¬ treeOfBlobs N ⊆ T →
      quartetSupport (nmscCF N θ ρ) T < quartetSupport (nmscCF N θ ρ) B := by
  obtain ⟨B, hB, hBT, -, hlt⟩ := lemma3_of_properties hStd.phylogenetic
    (nmscCF_pos hStd.phylogenetic hStd.metric hStd.rho)
    (External.AneEtAl2024.exchangeability hStd.phylogenetic hStd.metric hStd.rho) hNon hX
  exact ⟨B, hB, hBT, hlt⟩

/-- `π` is a margin of the perturbation lemma: a lower bound, over the 4-taxon sets that `T_N`
resolves, on the differences between the concordance factor of the quartet tree `T_N` displays and those of the
alternatives. E22 of the report: the printed "minimum of all differences" vanishes, since the alternatives of a T-quartet are equal. -/
def Margin (N : RootedNetwork V E X) (F : QuartetTree X → ℝ) (π : ℝ) : Prop :=
  ∀ s, Displays (treeOfBlobs N) s → ∀ r ∈ s.alternatives, π ≤ F s - F r

/-- **Supplement, Lemma 4** (`tob2025:supplement_lemma4`). If all the errors of the weights `w` are below
`π / (2 |f₄(S)|)`, the score of a refinement `B` maximizing the star part exceeds that of every binary tree
not refining `T_N`. The proof is the supplement's: quartets on which the two trees agree cancel, the tree
part gains more than `|Y_tree| (π - 2δ)` (its (5)), the star part loses at most `2 |Y_star| δ` (its (6), (7)
and (8)), which gives its (4), since `|Y_tree| + |Y_star| ≤ |f₄(S)|`.

Departure from the paper: the supplement's `π` is the least of all three pairwise differences of a
T-quartet's concordance factors, which vanishes, since the alternatives are equal (E22). `Margin` compares
the displayed quartet with its alternatives. The supplement also weakens strict bounds on the errors to
non-strict ones and then claims a strict inequality at the boundary radius (E24); here (5) keeps them strict,
since `Y_tree` is not empty. Both changes are forced. The supplement takes `B*` to be a maximizer of `QS_E`,
and gets its maximal star part from Lemma 5 (its name for Lemma 3); here this is the hypothesis `hstar`, and
`theorem1` applies the lemma to the tree of Lemma 3. -/
theorem supplementLemma4 {V E : Type*} {N : RootedNetwork V E X} (hN : N.IsPhylogenetic)
    {F w : QuartetTree X → ℝ} {π : ℝ} (hπ : 0 < π) (hmargin : Margin N F π)
    (herr : ∀ s, |w s - F s| < π / (2 * ((Fintype.card X).choose 4 : ℝ)))
    {B T : Finset (Finset X)} (hB : IsBinaryTree B) (hBT : treeOfBlobs N ⊆ B)
    (hstar : starPart (treeOfBlobs N) F T ≤ starPart (treeOfBlobs N) F B)
    (hT : IsBinaryTree T) (hTN : ¬ treeOfBlobs N ⊆ T) :
    quartetSupport w T < quartetSupport w B := by
  have hX : Nonempty X := by
    obtain ⟨A, hA, -⟩ := not_subset.1 hTN
    obtain ⟨x, -⟩ := (mem_filter.1 hA).2.1
    exact ⟨x⟩
  have hTB : IsUnrootedTree (treeOfBlobs N) := treeOfBlobs_isUnrootedTree hN
  set TN := treeOfBlobs N with hTNdef
  have hB' := hB.isUnrootedTree
  have hT' := hT.isUnrootedTree
  set f4 := powersetCard 4 (univ : Finset X) with hf4
  have hf4mem : ∀ q ∈ f4, q.card = 4 := fun q hq => (mem_powersetCard.1 hq).2
  -- the tree part differs on at least one 4-taxon subset
  obtain ⟨r₀, hr₀, hnot⟩ : ∃ r, Displays TN r ∧ ¬ Displays T r := by
    by_contra hcon
    push Not at hcon
    exact hTN (subset_of_forall_displays hT' hTB hcon)
  have : Nonempty (QuartetTree X) := ⟨r₀⟩
  -- the quartet trees that `B` and `T` display
  choose! sB hsB hdB using fun q (hq : q ∈ f4) => hB.exists_displays (hf4mem q hq)
  choose! sT hsT hdT using fun q (hq : q ∈ f4) => hT.exists_displays (hf4mem q hq)
  have hpartB : ∀ (w' : QuartetTree X → ℝ), ∀ q ∈ f4, quartetPart w' B q = w' (sB q) := by
    intro w' q hq
    have := quartetPart_of_displays hB' w' (hdB q hq)
    rwa [mem_treesOn.1 (hsB q hq)] at this
  have hpartT : ∀ (w' : QuartetTree X → ℝ), ∀ q ∈ f4, quartetPart w' T q = w' (sT q) := by
    intro w' q hq
    have := quartetPart_of_displays hT' w' (hdT q hq)
    rwa [mem_treesOn.1 (hsT q hq)] at this
  -- the 4-taxon subsets on which the two trees differ
  obtain ⟨Pt, hPt⟩ : ∃ Pt : Finset X → Prop, ∀ q, Pt q ↔
      (∃ r ∈ treesOn q, Displays TN r) ∧ sT q ≠ sB q := ⟨_, fun _ => Iff.rfl⟩
  obtain ⟨Ps, hPs⟩ : ∃ Ps : Finset X → Prop, ∀ q, Ps q ↔
      (∀ r ∈ treesOn q, ¬ Displays TN r) ∧ sT q ≠ sB q := ⟨_, fun _ => Iff.rfl⟩
  let Ytree := f4.filter Pt
  let Ystar := f4.filter Ps
  -- agreeing quartets cancel (E24)
  have htree : ∀ w' : QuartetTree X → ℝ, treePart TN w' B - treePart TN w' T =
      ∑ q ∈ Ytree, (w' (sB q) - w' (sT q)) := by
    intro w'
    rw [treePart_eq_sum, treePart_eq_sum, ← sum_sub_distrib, sum_filter]
    refine sum_congr rfl fun q hq => ?_
    simp only [hPt]
    by_cases hR : ∃ r ∈ treesOn q, Displays TN r
    · by_cases he : sT q = sB q
      · simp only [hR, he, ↓reduceIte, hpartB w' q hq, hpartT w' q hq, ne_eq, not_true_eq_false,
          and_false, sub_self]
      · simp only [hR, he, ↓reduceIte, hpartB w' q hq, hpartT w' q hq, ne_eq, not_false_eq_true,
          and_self]
    · simp only [hR, ↓reduceIte, false_and, sub_self]
  have hstar' : ∀ w' : QuartetTree X → ℝ, starPart TN w' B - starPart TN w' T =
      ∑ q ∈ Ystar, (w' (sB q) - w' (sT q)) := by
    intro w'
    rw [starPart_eq_sum, starPart_eq_sum, ← sum_sub_distrib, sum_filter]
    refine sum_congr rfl fun q hq => ?_
    simp only [hPs]
    by_cases hR : ∀ r ∈ treesOn q, ¬ Displays TN r
    · have e1 : (∀ r ∈ treesOn q, ¬ Displays TN r) = True := eq_true hR
      by_cases he : sT q = sB q
      · simp only [e1, he, ↓reduceIte, hpartB w' q hq, hpartT w' q hq, ne_eq, not_true_eq_false,
          and_false, sub_self]
      · simp only [e1, he, ↓reduceIte, hpartB w' q hq, hpartT w' q hq, ne_eq, not_false_eq_true,
          and_self]
    · have e1 : (∀ r ∈ treesOn q, ¬ Displays TN r) = False := eq_false hR
      simp only [e1, ↓reduceIte, false_and, sub_self]
  set δ := π / (2 * ((Fintype.card X).choose 4 : ℝ)) with hδ
  have hup : ∀ s, w s < F s + δ := fun s => by
    have := (abs_lt.1 (herr s)).2
    linarith
  have hlo : ∀ s, F s - δ < w s := fun s => by
    have := (abs_lt.1 (herr s)).1
    linarith
  have hsBr : ∀ q ∈ f4, ∀ r ∈ treesOn q, Displays TN r → sB q = r := by
    intro q hq r hr hdr
    exact hB'.displays_unique (hdB q hq) (hdr.mono hBT)
      ((mem_treesOn.1 (hsB q hq)).trans (mem_treesOn.1 hr).symm)
  have hYne : Ytree.Nonempty := by
    have hq : r₀.taxa ∈ f4 := mem_powersetCard.2 ⟨subset_univ _, r₀.card_taxa⟩
    have hsb := hsBr _ hq r₀ (mem_treesOn.2 rfl) hr₀
    refine ⟨r₀.taxa, mem_filter.2 ⟨hq, (hPt _).2 ⟨⟨r₀, mem_treesOn.2 rfl, hr₀⟩, ?_⟩⟩⟩
    rw [hsb]
    intro he
    exact hnot (he ▸ hdT _ hq)
  -- Equation (5), with the strict inequality of E24
  have h5 : (Ytree.card : ℝ) * (π - 2 * δ) < treePart TN w B - treePart TN w T := by
    rw [htree w]
    have : ∑ _q ∈ Ytree, (π - 2 * δ) < ∑ q ∈ Ytree, (w (sB q) - w (sT q)) := by
      refine sum_lt_sum_of_nonempty hYne fun q hq => ?_
      obtain ⟨hqf, hq'⟩ := mem_filter.1 hq
      obtain ⟨⟨r, hr, hdr⟩, hne⟩ := (hPt q).1 hq'
      have hsb := hsBr q hqf r hr hdr
      have halt : sT q ∈ (sB q).alternatives := QuartetTree.mem_alternatives.2
        ⟨(mem_treesOn.1 (hsT q hqf)).trans (mem_treesOn.1 (hsB q hqf)).symm, hne⟩
      have hm := hmargin (sB q) (hsb ▸ hdr) (sT q) halt
      have h1 := hlo (sB q)
      have h2 := hup (sT q)
      linarith
    rwa [sum_const, nsmul_eq_mul] at this
  -- Equation (6)
  have h6 : ∑ q ∈ Ystar, F (sB q) - (Ystar.card : ℝ) * δ ≤ ∑ q ∈ Ystar, w (sB q) := by
    have : ∑ q ∈ Ystar, (F (sB q) - δ) ≤ ∑ q ∈ Ystar, w (sB q) :=
      sum_le_sum fun q _ => (hlo (sB q)).le
    rwa [sum_sub_distrib, sum_const, nsmul_eq_mul] at this
  -- Equation (7)
  have h7 : ∑ q ∈ Ystar, w (sT q) ≤ ∑ q ∈ Ystar, F (sT q) + (Ystar.card : ℝ) * δ := by
    have : ∑ q ∈ Ystar, w (sT q) ≤ ∑ q ∈ Ystar, (F (sT q) + δ) :=
      sum_le_sum fun q _ => (hup (sT q)).le
    rwa [sum_add_distrib, sum_const, nsmul_eq_mul] at this
  -- Equation (8)
  have h8 : starPart TN w T - starPart TN w B ≤ 2 * (Ystar.card : ℝ) * δ := by
    have h1 := hstar' w
    have h2 := hstar' F
    rw [sum_sub_distrib] at h1 h2
    linarith
  -- combining the bounds
  have hC : ((Fintype.card X).choose 4 : ℝ) = (f4.card : ℝ) := by
    rw [hf4, card_powersetCard, card_univ]
  have hYcard : (Ytree.card : ℝ) + Ystar.card ≤ f4.card := by
    have hdisj : Disjoint Ytree Ystar := disjoint_left.2 fun q h1 h2 => by
      obtain ⟨r, hr, hdr⟩ := ((hPt q).1 (mem_filter.1 h1).2).1
      exact ((hPs q).1 (mem_filter.1 h2).2).1 r hr hdr
    have := card_le_card (union_subset (filter_subset _ f4) (filter_subset _ f4) :
      Ytree ∪ Ystar ⊆ f4)
    rw [card_union_of_disjoint hdisj] at this
    exact_mod_cast this
  have hYpos : (1 : ℝ) ≤ Ytree.card := by exact_mod_cast card_pos.2 hYne
  have hCpos : (0 : ℝ) < f4.card := lt_of_lt_of_le (by linarith) hYcard
  have hδC : 2 * δ * (f4.card : ℝ) = π := by
    rw [hδ, hC]
    field_simp
  have hδpos : 0 < δ := by
    rw [hδ, hC]
    positivity
  have hcomb : 0 ≤ (Ytree.card : ℝ) * π - 2 * δ * ((Ytree.card : ℝ) + Ystar.card) := by
    have h1 : 2 * δ * ((Ytree.card : ℝ) + Ystar.card) ≤ 2 * δ * (f4.card : ℝ) :=
      mul_le_mul_of_nonneg_left hYcard (by positivity)
    have h2 : π ≤ (Ytree.card : ℝ) * π := le_mul_of_one_le_left hπ.le hYpos
    linarith
  -- Equation (4)
  have h4 : starPart TN w T - starPart TN w B < treePart TN w B - treePart TN w T := by
    nlinarith
  rw [equation1 TN w T, equation1 TN w B]
  linarith

/-- A positive margin exists when the network is T-quartet-nonanomalous. -/
theorem exists_margin {N : RootedNetwork V E X} {F : QuartetTree X → ℝ}
    (hNon : IsTQuartetNonanomalous N F) : ∃ π, 0 < π ∧ Margin N F π := by
  let S := (univ : Finset (QuartetTree X × QuartetTree X)).filter fun p =>
    Displays (treeOfBlobs N) p.1 ∧ p.2 ∈ p.1.alternatives
  by_cases hS : S.Nonempty
  · obtain ⟨p, hp, hmin⟩ := S.exists_min_image (fun p => F p.1 - F p.2) hS
    obtain ⟨h1, h2⟩ := (mem_filter.1 hp).2
    refine ⟨F p.1 - F p.2, sub_pos.2 (hNon p.1 h1 p.2 h2), fun s hs r hr => ?_⟩
    exact hmin (s, r) (mem_filter.2 ⟨mem_univ _, hs, hr⟩)
  · refine ⟨1, one_pos, fun s hs r hr => absurd ⟨(s, r), mem_filter.2 ⟨mem_univ _, hs, hr⟩⟩ hS⟩

/-! ### Almost sure convergence of the frequencies -/

/-- **The strong law of large numbers for gene trees**: the frequency among the first `k` gene trees of
any property converges almost surely to its probability. -/
theorem ae_tendsto_freq [Fintype V] [Fintype E] {N : RootedNetwork V E X} {θ : MetricData E} {ρ : ℝ}
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {G : ℕ → Ω → Finset (Finset X)} (hG : IsGeneTreeSample N θ ρ P G) (Φ : Finset (Finset X) → Prop) :
    ∀ᵐ ω ∂P, Tendsto (fun k : ℕ => (((range k).filter fun i => Φ (G i ω)).card : ℝ) / k) atTop
      (𝓝 (∑ g, if Φ g then geneTreeDist N θ ρ g else 0)) := by
  let mS : MeasurableSpace (Finset (Finset X)) := ⊤
  have : DiscreteMeasurableSpace (Finset (Finset X)) := ⟨fun _ => MeasurableSpace.measurableSet_top⟩
  have hmeas : ∀ i, Measurable (G i) := fun i => measurable_to_countable' (hG.measurable i)
  have hsing : ∀ i (g : Finset (Finset X)), P (G i ⁻¹' {g}) = P (G 0 ⁻¹' {g}) := by
    intro i g
    refine (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).1 ?_
    have h1 := hG.law i g
    have h2 := hG.law 0 g
    simp only [Measure.real] at h1 h2
    rw [h1, h2]
  have hident : ∀ i, IdentDistrib (G i) (G 0) P P := fun i =>
    ⟨(hmeas i).aemeasurable, (hmeas 0).aemeasurable, Measure.ext_iff_singleton.2 fun g => by
      rw [Measure.map_apply (hmeas i) (measurableSet_singleton g),
        Measure.map_apply (hmeas 0) (measurableSet_singleton g), hsing]⟩
  have hind : ∀ i j, i ≠ j → IndepFun (G i) (G j) P := by
    intro i j hij
    rw [indepFun_iff_map_prod_eq_prod_map_map (hmeas i).aemeasurable (hmeas j).aemeasurable]
    refine Measure.ext_iff_singleton.2 fun ⟨g, h⟩ => ?_
    have hprod : ({(g, h)} : Set (Finset (Finset X) × Finset (Finset X))) = {g} ×ˢ {h} :=
      Set.singleton_prod_singleton.symm
    rw [Measure.map_apply ((hmeas i).prodMk (hmeas j)) (measurableSet_singleton _), hprod,
      Measure.prod_prod, Measure.map_apply (hmeas i) (measurableSet_singleton g),
      Measure.map_apply (hmeas j) (measurableSet_singleton h)]
    have hji : j ≠ i := Ne.symm hij
    have := hG.indep {i, j} (fun n => if n = i then g else h)
    rw [prod_pair hij] at this
    simp only [↓reduceIte, hji] at this
    rw [← this]
    congr 1
    ext ω
    simp only [Set.mem_preimage, Set.mem_prod, Set.mem_singleton_iff, mem_insert, mem_singleton,
      Set.mem_iInter]
    constructor
    · rintro ⟨h1, h2⟩ n (rfl | rfl)
      · simpa using h1
      · simpa [hji] using h2
    · intro hn
      have h1 := hn i (Or.inl rfl)
      have h2 := hn j (Or.inr rfl)
      simp only [↓reduceIte, hji] at h1 h2
      exact ⟨h1, h2⟩
  let f : Finset (Finset X) → ℝ := fun g => if Φ g then 1 else 0
  have hf : Measurable f := Measurable.of_discrete
  let Y : ℕ → Ω → ℝ := fun i => f ∘ G i
  have hint : Integrable (Y 0) P := by
    refine Integrable.of_bound (hf.comp (hmeas 0)).aestronglyMeasurable 1 (ae_of_all _ fun ω => ?_)
    simp only [Y, f, Function.comp]
    split_ifs <;> simp
  have hmean : ∫ ω, Y 0 ω ∂P = ∑ g, if Φ g then geneTreeDist N θ ρ g else 0 := by
    have h1 : ∫ ω, Y 0 ω ∂P = ∫ g, f g ∂(P.map (G 0)) :=
      (integral_map (hmeas 0).aemeasurable hf.aestronglyMeasurable).symm
    rw [h1, integral_fintype (f := f) Integrable.of_finite]
    refine sum_congr rfl fun g _ => ?_
    rw [map_measureReal_apply (hmeas 0) (measurableSet_singleton g), hG.law 0 g]
    simp only [f, smul_eq_mul]
    split_ifs <;> simp
  have hlaw := strong_law_ae_real Y hint
    (fun i j hij => (hind i j hij).comp hf hf) (fun i => (hident i).comp hf)
  filter_upwards [hlaw] with ω hω
  rw [hmean] at hω
  refine hω.congr fun k => ?_
  congr 1
  simp only [Y, f, Function.comp]
  exact sum_boole _ _

/-- The observed concordance factors converge almost surely to the expected ones, simultaneously. -/
theorem ae_eventually_abs_lt [Fintype V] [Fintype E] {N : RootedNetwork V E X} {θ : MetricData E}
    {ρ : ℝ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {G : ℕ → Ω → Finset (Finset X)} (hG : IsGeneTreeSample N θ ρ P G) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᵐ ω ∂P, ∃ K, ∀ k, K ≤ k → ∀ s, |geneCount G k ω s / k - nmscCF N θ ρ s| < δ := by
  have hall : ∀ᵐ ω ∂P, ∀ s : QuartetTree X, Tendsto (fun k : ℕ => geneCount G k ω s / k) atTop
      (𝓝 (nmscCF N θ ρ s)) := by
    refine ae_all_iff.2 fun s => ?_
    have := ae_tendsto_freq hG (fun g => Displays (unroot g) s)
    filter_upwards [this] with ω hω
    simpa only [geneCount, nmscCF] using hω
  filter_upwards [hall] with ω hω
  have hev : ∀ᶠ k : ℕ in atTop, ∀ s, |geneCount G k ω s / k - nmscCF N θ ρ s| < δ := by
    refine eventually_all.2 fun s => ?_
    have := (Metric.tendsto_nhds.1 (hω s)) δ hδ
    simpa only [Real.dist_eq] using this
  obtain ⟨K, hK⟩ := eventually_atTop.1 hev
  exact ⟨K, hK⟩

/-- Scaling the weights scales the score. -/
theorem quartetScore_div (c : QuartetTree X → ℝ) (k : ℝ) (T : Finset (Finset X)) :
    quartetSupport (fun s => c s / k) T = quartetSupport c T / k := by
  unfold quartetSupport
  rw [sum_div]
  refine sum_congr rfl fun s _ => ?_
  split_ifs <;> simp

/-- The scores for counts compare when the observed concordance factors are within the error bound of
the supplement's Lemma 4. -/
theorem geneCount_score_lt {N : RootedNetwork V E X} (hN : N.IsPhylogenetic)
    {F : QuartetTree X → ℝ} {π : ℝ} (hπ : 0 < π) (hmargin : Margin N F π)
    {c : QuartetTree X → ℝ} {k : ℕ} (hk : 0 < k)
    (herr : ∀ s, |c s / k - F s| < π / (2 * ((Fintype.card X).choose 4 : ℝ)))
    {B T : Finset (Finset X)} (hB : IsBinaryTree B) (hBT : treeOfBlobs N ⊆ B)
    (hstar : starPart (treeOfBlobs N) F T ≤ starPart (treeOfBlobs N) F B)
    (hT : IsBinaryTree T) (hTN : ¬ treeOfBlobs N ⊆ T) :
    quartetSupport c T < quartetSupport c B := by
  have := supplementLemma4 hN hπ hmargin herr hB hBT hstar hT hTN
  rw [quartetScore_div, quartetScore_div] at this
  exact (div_lt_div_iff_of_pos_right (by exact_mod_cast hk)).1 this

/-- **Theorem 1** (`tob2025:theorem1`). For a network under the
standard assumptions that is T-quartet-nonanomalous and independent gene trees from the NMSC, for any
binary tree `T` not refining the tree of blobs and any `ε > 0` there are a binary refinement `B` and
`K` such that `QS_k(B) > QS_k(T)` for all `k ≥ K` with probability at least `1 - ε`. The strong law of
large numbers gives almost sure convergence of the observed concordance factors (`ae_eventually_abs_lt`);
the deterministic `K` comes from continuity of the measure along the increasing events. -/
theorem theorem1 [Fintype V] [Fintype E] {N : RootedNetwork V E X} {θ : MetricData E} {ρ : ℝ}
    (hStd : StandardAssumptions N θ ρ)
    (hNon : IsTQuartetNonanomalous N (nmscCF N θ ρ)) (hX : 4 ≤ Fintype.card X)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (G : ℕ → Ω → Finset (Finset X)) (hG : IsGeneTreeSample N θ ρ P G)
    (T : Finset (Finset X)) (hT : IsBinaryTree T) (hTN : ¬ treeOfBlobs N ⊆ T) {ε : ℝ} (hε : 0 < ε) :
    ∃ (B : Finset (Finset X)) (K : ℕ), IsBinaryTree B ∧ treeOfBlobs N ⊆ B ∧
      1 - ε ≤ P.real {ω | ∀ k, K ≤ k → quartetSupport (geneCount G k ω) T < quartetSupport (geneCount G k ω) B} := by
  have hN := hStd.phylogenetic
  obtain ⟨B, hB, hBT, hstar, -⟩ := lemma3_of_properties hN
    (nmscCF_pos hN hStd.metric hStd.rho)
    (External.AneEtAl2024.exchangeability hStd.phylogenetic hStd.metric hStd.rho) hNon hX
  obtain ⟨π, hπ, hmargin⟩ := exists_margin hNon
  have hC : (0 : ℝ) < ((Fintype.card X).choose 4 : ℝ) := by
    exact_mod_cast Nat.choose_pos hX
  have hδ : 0 < π / (2 * ((Fintype.card X).choose 4 : ℝ)) := by positivity
  set δ := π / (2 * ((Fintype.card X).choose 4 : ℝ)) with hδdef
  have hae := ae_eventually_abs_lt hG hδ
  -- the increasing events
  let Ev : ℕ → Set Ω := fun K => {ω | ∀ k, K ≤ k → ∀ s, |geneCount G k ω s / k - nmscCF N θ ρ s| < δ}
  have hmono : Monotone Ev := fun K K' hKK ω hω k hk => hω k (hKK.trans hk)
  have hun : P (⋃ K, Ev K) = 1 := by
    have : (⋃ K, Ev K) =ᵐ[P] Set.univ := by
      rw [ae_eq_univ]
      refine measure_mono_null (fun ω hω => ?_) (ae_iff.1 hae)
      rintro ⟨K, hK⟩
      exact hω (Set.mem_iUnion.2 ⟨K, hK⟩)
    rw [measure_congr this, measure_univ]
  have hlim : Tendsto (fun K => P.real (Ev K)) atTop (𝓝 1) := by
    have h1 := tendsto_measure_iUnion_atTop (μ := P) hmono
    rw [hun] at h1
    have h2 := (ENNReal.tendsto_toReal ENNReal.one_ne_top).comp h1
    simpa [Measure.real, Function.comp_def] using h2
  obtain ⟨K, hK, hK1⟩ := ((hlim.eventually (lt_mem_nhds (by linarith : 1 - ε < 1))).and
    (eventually_ge_atTop 1)).exists
  refine ⟨B, K, hB, hBT, hK.le.trans (measureReal_mono fun ω hω k hk => ?_)⟩
  exact geneCount_score_lt hN hπ hmargin (lt_of_lt_of_le hK1 hk) (hω k hk) hB hBT (hstar T hT) hT hTN

/-- **Theorem 1** (`tob2025:theorem1`), "put simply": almost surely, for all large `k`, every optimal
solution of Weighted Quartet Consensus is a refinement of the tree of blobs. -/
theorem theorem1_optimal [Fintype V] [Fintype E] {N : RootedNetwork V E X} {θ : MetricData E} {ρ : ℝ}
    (hStd : StandardAssumptions N θ ρ)
    (hNon : IsTQuartetNonanomalous N (nmscCF N θ ρ)) (hX : 4 ≤ Fintype.card X)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (G : ℕ → Ω → Finset (Finset X)) (hG : IsGeneTreeSample N θ ρ P G) :
    ∀ᵐ ω ∂P, ∃ K, ∀ k, K ≤ k → ∀ B, IsBinaryTree B →
      (∀ T, IsBinaryTree T → quartetSupport (geneCount G k ω) T ≤ quartetSupport (geneCount G k ω) B) →
      treeOfBlobs N ⊆ B := by
  have hN := hStd.phylogenetic
  obtain ⟨Bs, hBs, hBsT, hstar, -⟩ := lemma3_of_properties hN
    (nmscCF_pos hN hStd.metric hStd.rho)
    (External.AneEtAl2024.exchangeability hStd.phylogenetic hStd.metric hStd.rho) hNon hX
  obtain ⟨π, hπ, hmargin⟩ := exists_margin hNon
  have hC : (0 : ℝ) < ((Fintype.card X).choose 4 : ℝ) := by
    exact_mod_cast Nat.choose_pos hX
  have hδ : 0 < π / (2 * ((Fintype.card X).choose 4 : ℝ)) := by positivity
  filter_upwards [ae_eventually_abs_lt hG hδ] with ω ⟨K₀, hK₀⟩
  refine ⟨max K₀ 1, fun k hk B hB hopt => ?_⟩
  by_contra hne
  have hk0 : K₀ ≤ k := (le_max_left _ _).trans hk
  have hk1 : 0 < k := lt_of_lt_of_le one_pos ((le_max_right _ _).trans hk)
  exact absurd (hopt Bs hBs) (not_le.2 (geneCount_score_lt hN hπ hmargin hk1 (hK₀ k hk0) hBs hBsT
    (hstar B hB) hB hne))

/-- The constrained search space of ASTRAL (versions up to 3): binary trees whose splits all occur on
the first `k` gene trees. -/
def AstralSpace {Ω : Type*} (G : ℕ → Ω → Finset (Finset X)) (k : ℕ) (ω : Ω) (B : Finset (Finset X)) :
    Prop :=
  IsBinaryTree B ∧ ∀ A ∈ B, ∃ i < k, A ∈ unroot (G i ω)

/-- **Corollary of Theorem 1** (`tob2025:astral_corollary`): almost
surely, for all large `k`, every optimum of the score in ASTRAL's search space is a refinement of the
tree of blobs. Every bipartition of a binary tree has positive probability under the NMSC, at least that of
a binary gene tree inducing it (`geneTreeDist_pos`), so it appears almost surely (the paper cites Mirarab
et al.), and then ASTRAL's search space contains all binary trees, so Theorem 1 applies. -/
theorem astral_corollary [Fintype V] [Fintype E] {N : RootedNetwork V E X} {θ : MetricData E} {ρ : ℝ}
    (hStd : StandardAssumptions N θ ρ)
    (hNon : IsTQuartetNonanomalous N (nmscCF N θ ρ)) (hX : 4 ≤ Fintype.card X)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (G : ℕ → Ω → Finset (Finset X)) (hG : IsGeneTreeSample N θ ρ P G) :
    ∀ᵐ ω ∂P, ∃ K, ∀ k, K ≤ k → ∀ B, AstralSpace G k ω B →
      (∀ T, AstralSpace G k ω T → quartetSupport (geneCount G k ω) T ≤ quartetSupport (geneCount G k ω) B) →
      treeOfBlobs N ⊆ B := by
  have hN := hStd.phylogenetic
  have hne' : Nonempty X := Fintype.card_pos_iff.1 (by omega)
  -- every bipartition has positive probability, at least that of a binary gene tree inducing it, so it
  -- appears almost surely
  have hocc : ∀ᵐ ω ∂P, ∀ A : Finset X, (∃ H, IsBinaryHierarchy H ∧ A ∈ unroot H) →
      ∃ i, A ∈ unroot (G i ω) := by
    refine ae_all_iff.2 fun A => ?_
    by_cases hA : ∃ H, IsBinaryHierarchy H ∧ A ∈ unroot H
    · obtain ⟨H, hH, hAH⟩ := hA
      have hpos := geneTreeDist_pos hN hStd.metric hStd.rho hH
      have hsum : ∀ d : ∀ g : Finset (Finset X), Decidable (A ∈ unroot g),
          0 < ∑ g, @ite _ (A ∈ unroot g) (d g) (geneTreeDist N θ ρ g) 0 := by
        intro d
        refine lt_of_lt_of_le ?_ (single_le_sum (f := fun g =>
          @ite _ (A ∈ unroot g) (d g) (geneTreeDist N θ ρ g) 0) (fun g _ => ?_) (mem_univ H))
        · change 0 < @ite _ (A ∈ unroot H) (d H) (geneTreeDist N θ ρ H) 0
          rwa [ite_eq_left hAH]
        · split_ifs
          · exact geneTreeDist_nonneg hN hStd.metric hStd.rho g
          · exact le_rfl
      filter_upwards [ae_tendsto_freq hG (fun g => A ∈ unroot g)] with ω hω _
      obtain ⟨k, hk⟩ := (hω.eventually (lt_mem_nhds (hsum _))).exists
      by_contra hcon
      push Not at hcon
      simp [hcon] at hk
    · exact ae_of_all _ fun _ h => absurd h hA
  filter_upwards [theorem1_optimal hStd hNon hX P G hG, hocc] with ω ⟨K₀, hK₀⟩ hω
  -- from some point on, all these bipartitions have appeared, and ASTRAL's search space contains all
  -- binary trees
  obtain ⟨K₁, hK₁⟩ : ∃ K₁, ∀ A : Finset X, (∃ H, IsBinaryHierarchy H ∧ A ∈ unroot H) →
      ∃ i < K₁, A ∈ unroot (G i ω) := by
    classical
    choose! idx hidx using hω
    obtain ⟨M, hM⟩ := ((univ : Finset (Finset X)).image idx).exists_le
    exact ⟨M + 1, fun A hA => ⟨idx A, Nat.lt_succ_of_le (hM _ (mem_image_of_mem _ (mem_univ A))),
      hidx A hA⟩⟩
  have hspace : ∀ k, K₁ ≤ k → ∀ T, IsBinaryTree T → AstralSpace G k ω T := by
    intro k hk T hT
    refine ⟨hT, fun A hA => ?_⟩
    obtain ⟨H, hH, rfl, hbin⟩ := hT
    obtain ⟨i, hi, he⟩ := hK₁ A ⟨H, isBinaryHierarchy_iff_card_childClusters.2 ⟨hH, hbin⟩, hA⟩
    exact ⟨i, lt_of_lt_of_le hi hk, he⟩
  refine ⟨max K₀ K₁, fun k hk B hB hopt => ?_⟩
  exact hK₀ k ((le_max_left _ _).trans hk) B hB.1 fun T hT =>
    hopt T (hspace k ((le_max_right _ _).trans hk) T hT)

end TOBQMC
