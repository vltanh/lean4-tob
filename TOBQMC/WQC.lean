module

public import Basic.Phylogenetics.NMSC.Basic
public import Basic.Phylogenetics.TreeDetach
public import Basic.Probability.IID
public import External.AneEtAl2024.Exchangeability
public import Mathlib.Probability.StrongLaw

/-!
# TOB-QMC §4.1–4.2: quartet-based species tree methods give a refinement of the tree of blobs

Definition 1, Equations (1)–(4), Lemma 3, the perturbation Lemma 4 of the Supplement, Theorem 1 and the
ASTRAL corollary. These results take the exchangeability of taxa on one side of a cut edge from the
literature (`External.AneEtAl2024.Exchangeability`), so they are conditional on it.

The route of Lemma 3 is the paper's. A maximizer of the blob `v` part of the score is changed, by
detaching taxa and reattaching them to a best taxon of their block (`detachReattach`,
`vertexPart_detachReattach`, `exists_block_side`), into a maximizer that does not break the blocks
(`exists_vertex_maximizer`). It resolves every quartet around `v` (`displays_of_vertex_maximizer`), and
contracting the edges inside blocks leaves a family of unions of blocks (`displays_filter_isBlockUnion`).
These families and the tree of blobs have a common refinement, the compatibility supertree of the paper,
which is `splice`.
-/

@[expose] public noncomputable section

open Phylogenetics Phylogenetics.RootedNetwork Finset Filter Topology MeasureTheory ProbabilityTheory
open scoped Classical

namespace TOBQMC

variable {V E X : Type*} [Fintype X] [DecidableEq X]


/-- A choice of a parent at each vertex: the display trees of the network. -/
def IsDisplayChoice (N : RootedNetwork V E X) (c : V → E) : Prop :=
  ∀ v, 2 ≤ N.graph.indegree v → N.graph.target (c v) = v

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
  ∃ c, IsDisplayChoice N c ∧ ∃ e ∈ displayArcs N c,
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
    quartetScore F t = treePart TN F t + starPart TN F t := by
  unfold quartetScore treePart starPart
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

/-- The partial score of Equation (4), `vertexTaxonPart`: summing it over all taxa counts each 4-taxon set
four times. -/
theorem equation4 (P : Finset (Finset X)) (F : QuartetTree X → ℝ) (t : Finset (Finset X)) :
    ∑ x, vertexTaxonPart P x F t = 4 * vertexPart P F t := by
  simp only [vertexTaxonPart, vertexPart]
  rw [sum_comm, mul_sum]
  refine sum_congr rfl fun s _ => ?_
  by_cases hID : InDistinctBlocks P s.taxa ∧ Displays t s
  · have hstep : ∀ x : X, (if InDistinctBlocks P s.taxa ∧ x ∈ s.taxa ∧ Displays t s then F s else 0) =
        if x ∈ s.taxa then F s else 0 := by
      intro x
      by_cases hx : x ∈ s.taxa
      · simp only [hID.1, hID.2, hx, and_self, ↓reduceIte]
      · simp only [hx, false_and, and_false, ↓reduceIte]
    have e1 : (InDistinctBlocks P s.taxa ∧ Displays t s) = True := eq_true hID
    simp only [hstep]
    simp only [e1, ↓reduceIte]
    rw [sum_ite_mem, univ_inter, sum_const, s.card_taxa]
    simp
  · rw [sum_eq_zero fun x _ => ite_eq_right fun h => hID ⟨h.1, h.2.2⟩]
    simp only [hID, ↓reduceIte, mul_zero]

/-! ### The blob `v` part: detaching and reattaching taxa of a block -/

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

/-- One block: detach every other taxon of the block and reattach it to the chosen taxon `a`
(the paper's lines 476-485). The result has the block as a side, its blob `v` score is not smaller, and
the other blocks that were sides stay sides. -/
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
      · rw [vertexPart_detachReattach hEx hd hcut hB₀ haB hbB (Ne.symm hba),
          hpart b hbB hbD, hpart a haB (fun h =>
            (mem_erase.1 (hsub (mem_insert_of_mem h))).1 rfl)]
        have := hamax b hbB
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

/-- All blocks (the paper's "repeating for all `b` and all `P_j`", line 485). -/
theorem exists_all_blocks_side {N : RootedNetwork V E X} {F : QuartetTree X → ℝ} {TN : Finset (Finset X)}
    (hEx : CutExchangeable N F) (hTN : IsUnrootedTree TN) (hV : IsVertexPartition TN P)
    (hcut : ∀ B ∈ P, N.HasCutSplit (B : Set X)) {T : Finset (Finset X)} (hT : IsUnrootedTree T)
    (hX : 2 ≤ Fintype.card X) :
    ∃ T', IsUnrootedTree T' ∧ (∀ C ∈ P, C ∈ T') ∧ vertexPart P F T ≤ vertexPart P F T' := by
  have key : ∀ 𝔅 : Finset (Finset X), 𝔅 ⊆ P → ∃ T', IsUnrootedTree T' ∧ (∀ C ∈ 𝔅, C ∈ T') ∧
      vertexPart P F T ≤ vertexPart P F T' := by
    intro 𝔅
    induction 𝔅 using Finset.induction_on with
    | empty => exact fun _ => ⟨T, hT, by simp, le_refl _⟩
    | insert B₀ 𝔅 hB₀n ih =>
      intro hsub
      have hB₀ := hsub (mem_insert_self _ _)
      obtain ⟨T₁, hT₁, hall, hle⟩ := ih fun x hx => hsub (mem_insert_of_mem hx)
      have hB₀T := hV.mem B₀ hB₀
      obtain ⟨T₂, hT₂, hside, hle₂, hother⟩ := exists_block_side (F := F) hEx hV.pairwiseDisjoint
        (hcut B₀ hB₀) hB₀ (hTN.nonempty_of_mem hB₀T) (hTN.nonempty_of_mem (hTN.compl_mem hB₀T))
        hT₁ hX
      refine ⟨T₂, hT₂, fun C hC => ?_, hle.trans hle₂⟩
      rcases mem_insert.1 hC with rfl | hC
      · exact hside
      · exact hother C (hsub (mem_insert_of_mem hC)) (fun e => hB₀n (e ▸ hC)) (hall C hC)
  obtain ⟨T', hT', hall, hle⟩ := key P (Subset.refl _)
  exact ⟨T', hT', hall, hle⟩

/-- **The claim of the paper's lines 464-466.** There is a tree `B*(v)` that (1) maximizes `QS^v` and
(2) does not break apart the blocks of `P`. -/
theorem exists_vertex_maximizer {N : RootedNetwork V E X} {F : QuartetTree X → ℝ}
    {TN : Finset (Finset X)} (hEx : CutExchangeable N F) (hTN : IsUnrootedTree TN)
    (hV : IsVertexPartition TN P) (hcut : ∀ B ∈ P, N.HasCutSplit (B : Set X))
    (hX : 2 ≤ Fintype.card X) :
    ∃ T', IsUnrootedTree T' ∧ (∀ C ∈ P, C ∈ T') ∧
      ∀ T, IsUnrootedTree T → vertexPart P F T ≤ vertexPart P F T' := by
  obtain ⟨Tm, hTm, hmax⟩ := (univ.filter fun T : Finset (Finset X) => IsUnrootedTree T).exists_max_image
    (vertexPart P F) ⟨TN, by simpa using hTN⟩
  obtain ⟨T', hT', hall, hle⟩ := exists_all_blocks_side (F := F) hEx hTN hV hcut
    (mem_filter.1 hTm).2 hX
  exact ⟨T', hT', hall, fun T hT => (hmax T (by simpa using hT)).trans hle⟩

/-- **The second observation of the paper (lines 489-492).** A maximizer of `QS^v` resolves every set of
four taxa in distinct blocks, since a refinement resolving it would have a larger score: the concordance
factors are positive. -/
theorem displays_of_vertex_maximizer {F : QuartetTree X → ℝ} (hF : ∀ s, 0 < F s)
    {T' : Finset (Finset X)} (hT' : IsUnrootedTree T')
    (hmax : ∀ T, IsUnrootedTree T → vertexPart P F T ≤ vertexPart P F T') {q : Finset X}
    (hq : q.card = 4) (hI : InDistinctBlocks P q) : ∃ s ∈ treesOn q, Displays T' s := by
  by_contra hcon
  push Not at hcon
  -- some quartet tree on `q`
  obtain ⟨C, hCq, hCc⟩ := exists_subset_card_eq (s := q) (n := 2) (by omega)
  let s := quartetOfCherry q C hq hCq hCc
  have hst : s.taxa = q := quartetOfCherry_taxa q C hq hCq hCc
  obtain ⟨T₁, hT₁, hsub, hd⟩ := exists_refinement_displays hT' s (fun r hr => hcon r (hst ▸ hr))
  refine absurd (hmax T₁ hT₁) (not_le.2 ?_)
  refine sum_lt_sum (fun r _ => ?_) ⟨s, mem_univ _, ?_⟩
  · by_cases hr : InDistinctBlocks P r.taxa ∧ Displays T' r
    · have : InDistinctBlocks P r.taxa ∧ Displays T₁ r := ⟨hr.1, hr.2.mono hsub⟩
      simp only [hr, this, and_self, ↓reduceIte, le_refl]
    · rw [ite_eq_right hr]
      split_ifs
      · exact (hF r).le
      · exact le_refl _
  · have hIs : InDistinctBlocks P s.taxa := hst ▸ hI
    have hnot : ¬ Displays T' s := hcon s (mem_treesOn.2 hst)
    simp only [hIs, hnot, hd, and_self, and_false, ↓reduceIte]
    exact hF s

/-- **The third observation of the paper (lines 492-495).** Keeping the sides of `T'` that are unions of
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
there is a binary refinement `B` of the tree of blobs that maximizes the star part and the tree part of
the score over binary trees, and has a larger score than every binary tree not refining the tree of
blobs. The compatibility supertree of the paper's lines 497-498 (Warnow, Chapters 3, 7: compatible
splits have a common refinement) is `splice`, by `splice_isUnrootedTree`. -/
theorem lemma3_of_properties {V E : Type*} {N : RootedNetwork V E X} (hN : N.IsPhylogenetic)
    {F : QuartetTree X → ℝ} (hF : ∀ s, 0 < F s) (hEx : CutExchangeable N F)
    (hNon : IsTQuartetNonanomalous N F) (hX : 4 ≤ Fintype.card X) :
    ∃ B, IsBinaryTree B ∧ treeOfBlobs N ⊆ B ∧
      (∀ T, IsBinaryTree T → starPart (treeOfBlobs N) F T ≤ starPart (treeOfBlobs N) F B) ∧
      ∀ T, IsBinaryTree T → ¬ treeOfBlobs N ⊆ T → quartetScore F T < quartetScore F B := by
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
      obtain ⟨s, hs, hds⟩ := displays_of_vertex_maximizer hF hT' hmax hq hI
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

/-- **Lemma 3** (`tob2025:lemma3`), conditional on exchangeability. For a network under the standard
assumptions that is T-quartet-nonanomalous, with the exact expected concordance factors, there is a
binary refinement of the tree of blobs with higher quartet score than every binary tree that does
not refine it. -/
theorem lemma3 [Fintype V] [Fintype E] {N : RootedNetwork V E X} {θ : MetricData E} {ρ : ℝ}
    (hStd : StandardAssumptions N θ ρ) (hEx : External.AneEtAl2024.Exchangeability N θ ρ)
    (hNon : IsTQuartetNonanomalous N (nmscCF N θ ρ)) (hX : 4 ≤ Fintype.card X) :
    ∃ B, IsBinaryTree B ∧ treeOfBlobs N ⊆ B ∧ ∀ T, IsBinaryTree T → ¬ treeOfBlobs N ⊆ T →
      quartetScore (nmscCF N θ ρ) T < quartetScore (nmscCF N θ ρ) B := by
  obtain ⟨B, hB, hBT, -, hlt⟩ := lemma3_of_properties hStd.phylogenetic
    (nmscCF_pos hStd.phylogenetic hStd.metric hStd.rho) hEx hNon hX
  exact ⟨B, hB, hBT, hlt⟩

/-- The margin `π` of the perturbation lemma: the least difference, over the 4-taxon sets that `T_N`
resolves, between the concordance factor of the quartet tree `T_N` displays and those of the
alternatives. E12 of the report: the printed "minimum of all differences" can vanish. -/
def Margin (N : RootedNetwork V E X) (F : QuartetTree X → ℝ) (π : ℝ) : Prop :=
  ∀ s, Displays (treeOfBlobs N) s → ∀ r ∈ s.alternatives, π ≤ F s - F r

/-- **Supplement, Lemma 4** (`tob2025:supplement_lemma4`), with the corrected margin (E12) and strict
bounds (E13). If all the errors of the weights `w` are below `π / (2 |f₄(S)|)`, the score of a
refinement `B` maximizing the star part exceeds that of every binary tree not refining `T_N`. The proof
is the supplement's: quartets on which the two trees agree cancel, the tree part gains more than
`|Y_tree| (π - 2δ)` (its (5), strict since `Y_tree` is not empty), the star part loses at most
`2 |Y_star| δ` (its (8)), and `|Y_tree| + |Y_star| ≤ |f₄(S)|`. -/
theorem supplementLemma4 {V E : Type*} {N : RootedNetwork V E X} (hN : N.IsPhylogenetic)
    {F w : QuartetTree X → ℝ} {π : ℝ} (hπ : 0 < π) (hmargin : Margin N F π)
    (herr : ∀ s, |w s - F s| < π / (2 * ((Fintype.card X).choose 4 : ℝ)))
    {B T : Finset (Finset X)} (hB : IsBinaryTree B) (hBT : treeOfBlobs N ⊆ B)
    (hstar : starPart (treeOfBlobs N) F T ≤ starPart (treeOfBlobs N) F B)
    (hT : IsBinaryTree T) (hTN : ¬ treeOfBlobs N ⊆ T) :
    quartetScore w T < quartetScore w B := by
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
  -- agreeing quartets cancel (E13)
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
  -- Equation (5), with the strict inequality of E13
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
  -- Equation (8)
  have h8 : starPart TN w T - starPart TN w B ≤ 2 * (Ystar.card : ℝ) * δ := by
    have h1 := hstar' w
    have h2 := hstar' F
    have h3 : ∑ q ∈ Ystar, (F (sB q) - F (sT q)) - (Ystar.card : ℝ) * (2 * δ) ≤
        ∑ q ∈ Ystar, (w (sB q) - w (sT q)) := by
      have : ∑ q ∈ Ystar, ((F (sB q) - F (sT q)) - 2 * δ) ≤
          ∑ q ∈ Ystar, (w (sB q) - w (sT q)) := by
        refine sum_le_sum fun q _ => ?_
        have h4 := hlo (sB q)
        have h5 := hup (sT q)
        linarith
      rwa [sum_sub_distrib, sum_const, nsmul_eq_mul] at this
    have h4 := hstar
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
  rw [equation1 TN w T, equation1 TN w B]
  nlinarith

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
    {G : ℕ → Ω → Finset (Finset X)} (hG : IsGeneTreeSample P N θ ρ G) (Φ : Finset (Finset X) → Prop) :
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
    {G : ℕ → Ω → Finset (Finset X)} (hG : IsGeneTreeSample P N θ ρ G) {δ : ℝ} (hδ : 0 < δ) :
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
    quartetScore (fun s => c s / k) T = quartetScore c T / k := by
  unfold quartetScore
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
    quartetScore c T < quartetScore c B := by
  have := supplementLemma4 hN hπ hmargin herr hB hBT hstar hT hTN
  rw [quartetScore_div, quartetScore_div] at this
  exact (div_lt_div_iff_of_pos_right (by exact_mod_cast hk)).1 this

/-- **Theorem 1** (`tob2025:theorem1`), conditional on exchangeability. For a network under the
standard assumptions that is T-quartet-nonanomalous and independent gene trees from the NMSC, for any
binary tree `T` not refining the tree of blobs and any `ε > 0` there are a binary refinement `B` and
`K` such that `QS_k(B) > QS_k(T)` for all `k ≥ K` with probability at least `1 - ε`. The strong law of
large numbers gives almost sure convergence of the observed concordance factors (`ae_eventually_abs_lt`);
the deterministic `K` comes from continuity of the measure along the increasing events. -/
theorem theorem1 [Fintype V] [Fintype E] {N : RootedNetwork V E X} {θ : MetricData E} {ρ : ℝ}
    (hStd : StandardAssumptions N θ ρ) (hEx : External.AneEtAl2024.Exchangeability N θ ρ)
    (hNon : IsTQuartetNonanomalous N (nmscCF N θ ρ)) (hX : 4 ≤ Fintype.card X)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (G : ℕ → Ω → Finset (Finset X)) (hG : IsGeneTreeSample P N θ ρ G)
    (T : Finset (Finset X)) (hT : IsBinaryTree T) (hTN : ¬ treeOfBlobs N ⊆ T) {ε : ℝ} (hε : 0 < ε) :
    ∃ (B : Finset (Finset X)) (K : ℕ), IsBinaryTree B ∧ treeOfBlobs N ⊆ B ∧
      1 - ε ≤ P.real {ω | ∀ k, K ≤ k → quartetScore (geneCount G k ω) T < quartetScore (geneCount G k ω) B} := by
  have hN := hStd.phylogenetic
  obtain ⟨B, hB, hBT, hstar, -⟩ := lemma3_of_properties hN
    (nmscCF_pos hN hStd.metric hStd.rho) hEx hNon hX
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
    (hStd : StandardAssumptions N θ ρ) (hEx : External.AneEtAl2024.Exchangeability N θ ρ)
    (hNon : IsTQuartetNonanomalous N (nmscCF N θ ρ)) (hX : 4 ≤ Fintype.card X)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (G : ℕ → Ω → Finset (Finset X)) (hG : IsGeneTreeSample P N θ ρ G) :
    ∀ᵐ ω ∂P, ∃ K, ∀ k, K ≤ k → ∀ B, IsBinaryTree B →
      (∀ T, IsBinaryTree T → quartetScore (geneCount G k ω) T ≤ quartetScore (geneCount G k ω) B) →
      treeOfBlobs N ⊆ B := by
  have hN := hStd.phylogenetic
  obtain ⟨Bs, hBs, hBsT, hstar, -⟩ := lemma3_of_properties hN
    (nmscCF_pos hN hStd.metric hStd.rho) hEx hNon hX
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

/-- **Corollary of Theorem 1** (`tob2025:astral_corollary`), conditional on exchangeability: almost
surely, for all large `k`, every optimum of the score in ASTRAL's search space is a refinement of the
tree of blobs, since every split has positive probability under the NMSC: every binary gene tree has
positive probability (`geneTreeDist_pos`), so it occurs almost surely (the paper cites Mirarab et al.),
and then ASTRAL's search space contains all binary trees. -/
theorem astral_corollary [Fintype V] [Fintype E] {N : RootedNetwork V E X} {θ : MetricData E} {ρ : ℝ}
    (hStd : StandardAssumptions N θ ρ) (hEx : External.AneEtAl2024.Exchangeability N θ ρ)
    (hNon : IsTQuartetNonanomalous N (nmscCF N θ ρ)) (hX : 4 ≤ Fintype.card X)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (G : ℕ → Ω → Finset (Finset X)) (hG : IsGeneTreeSample P N θ ρ G) :
    ∀ᵐ ω ∂P, ∃ K, ∀ k, K ≤ k → ∀ B, AstralSpace G k ω B →
      (∀ T, AstralSpace G k ω T → quartetScore (geneCount G k ω) T ≤ quartetScore (geneCount G k ω) B) →
      treeOfBlobs N ⊆ B := by
  have hN := hStd.phylogenetic
  have hne' : Nonempty X := Fintype.card_pos_iff.1 (by omega)
  -- every binary gene tree occurs almost surely, since it has positive probability
  have hocc : ∀ᵐ ω ∂P, ∀ H : Finset (Finset X), IsBinaryHierarchy H → ∃ i, G i ω = H := by
    refine ae_all_iff.2 fun H => ?_
    by_cases hH : IsBinaryHierarchy H
    · have hpos := geneTreeDist_pos hN hStd.metric hStd.rho hH
      have hsum : ∀ d : ∀ g : Finset (Finset X), Decidable (g = H),
          (∑ g, @ite _ (g = H) (d g) (geneTreeDist N θ ρ g) 0) = geneTreeDist N θ ρ H := by
        intro d
        rw [sum_eq_single H]
        · simp
        · intro g _ hg
          simp [hg]
        · simp
      filter_upwards [ae_tendsto_freq hG (fun g => g = H)] with ω hω _
      obtain ⟨k, hk⟩ := (hω.eventually (lt_mem_nhds (a := 0)
        (lt_of_lt_of_eq hpos (hsum _).symm))).exists
      by_contra hcon
      push Not at hcon
      simp [hcon] at hk
    · exact ae_of_all _ fun _ h => absurd h hH
  filter_upwards [theorem1_optimal hStd hEx hNon hX P G hG, hocc] with ω ⟨K₀, hK₀⟩ hω
  -- from some point on, ASTRAL's search space contains all binary trees
  obtain ⟨K₁, hK₁⟩ : ∃ K₁, ∀ H : Finset (Finset X), IsBinaryHierarchy H → ∃ i < K₁, G i ω = H := by
    classical
    choose! idx hidx using hω
    obtain ⟨M, hM⟩ := ((univ : Finset (Finset (Finset X))).image idx).exists_le
    exact ⟨M + 1, fun H hH => ⟨idx H, Nat.lt_succ_of_le (hM _ (mem_image_of_mem _ (mem_univ H))),
      hidx H hH⟩⟩
  have hspace : ∀ k, K₁ ≤ k → ∀ T, IsBinaryTree T → AstralSpace G k ω T := by
    intro k hk T hT
    refine ⟨hT, fun A hA => ?_⟩
    obtain ⟨H, hH, rfl, hbin⟩ := hT
    obtain ⟨i, hi, he⟩ := hK₁ H ⟨hH, hbin⟩
    exact ⟨i, lt_of_lt_of_le hi hk, he ▸ hA⟩
  refine ⟨max K₀ K₁, fun k hk B hB hopt => ?_⟩
  exact hK₀ k ((le_max_left _ _).trans hk) B hB.1 fun T hT =>
    hopt T (hspace k ((le_max_right _ _).trans hk) T hT)

end TOBQMC
