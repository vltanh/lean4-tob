module

public import External.AllmanEtAl2023.CutOrder
public import External.AllmanEtAl2023.CycleLemma
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Allman, Baños, Mitchell, Rhodes 2023: the tree of blobs of a species network

E. S. Allman, H. Baños, J. D. Mitchell, J. A. Rhodes, *The tree of blobs of a species network:
identifiability under the coalescent*, J. Math. Biol. 86 (2023), 10.

* `theorem2`, the B-quartet inference rule, is proved by the source's argument, on the node `v` of the
  tree of blobs that `b, c, d` determine (`rule_core`).
* `lemma3` and `closure_complete`, the combinatorial content of Theorem 3, are proved: from the
  B-quartets detected on induced 4-taxon networks, the inference rule reaches all B-quartets.
  `lemma3` follows the source's cycle through `A`, `K_ab`, `e₀`, `K_cd` (`lemma3_blob`, in
  `External/AllmanEtAl2023/CycleLemma.lean`), and uses its Lemma 2 (`lemma2`, in
  `External/AllmanEtAl2023/SubgraphBlobs.lean`). `not_resolves_iff_exists_determines` and
  `isBQuartet_iff_not_resolves` translate between the source's "determines a blob" and the
  description by domination used here.
* `Corollary1`, the CF-detectability of 4-blobs for generic parameters, is defined here. Theorem 1 is proved in
  `External/AllmanEtAl2023/Theorem1.lean`, and Corollary 1 in `External/AllmanEtAl2023/Corollary1.lean`.
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

/-- No side of the tree of blobs has `a, e` and not `u, v`, if `{a,e,u,v}` is a B-quartet or a
cut-edge split of its induced network separates `a, e`. -/
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

/-- The cut edges of the subgraph induced on `Y` resolve `q`: some arc is a cut on `Y` with exactly
two taxa of `q` below it. -/
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

omit [Fintype X] [DecidableEq X] in
/-- **The source's B-quartets and `Resolves`.** On the subgraph induced on `Y`, four taxa of `Y`
determine a blob (Definitions 8 and 12 of the source) exactly when no arc dominating the taxa of `Y`
below it has two of them below it. -/
theorem not_resolves_iff_exists_determines (hN : N.IsPhylogenetic) {Y q : Finset X} (hq : q ⊆ Y)
    (h4 : q.card = 4) :
    ¬ Resolves N Y q ↔ ∃ v ∈ N.ancestralVertices (Y : Set X),
      Determines N.graph (N.ancestralArcs (Y : Set X)) v N.leaf q := by
  have hqY : ∀ s ∈ q, s ∈ (Y : Set X) := fun s hs => Finset.mem_coe.mpr (hq hs)
  constructor
  · intro hR
    refine exists_determines_of_no_split hN hqY (by omega) fun e T hO hT hT' => hR ?_
    obtain ⟨s, hs, t, ht, hst, hsT, htT⟩ := hT
    obtain ⟨s', hs', t', ht', hst', hsT', htT'⟩ := hT'
    -- the arc `e` is in the subgraph, since it separates two of its taxa
    obtain ⟨he, _, _, hl, hp, hq'⟩ := exists_links_of_walks hO.compl (not_not.mpr hsT)
      (walks_ancestral hN (N.leaf_mem_ancestralVertices (hqY s hs))
        (N.leaf_mem_ancestralVertices (hqY s' hs'))) hsT'
    have hcut : N.HasCutSplitOn (Y : Set X) {x | N.leaf x ∈ T} := by
      refine ⟨e, he, T, fun f hf => ⟨hO f hf, ?_⟩, fun x _ => Iff.rfl⟩
      rintro rfl
      exact Links.crosses hl.symm hq' (not_not.mp hp)
    refine resolves_of_hasCutSplitOn hN hcut hq h4 ?_
    have h1 : 2 ≤ (q.filter (· ∈ {x | N.leaf x ∈ T})).card :=
      Finset.one_lt_card.mpr ⟨s, by simp [hs, hsT], t, by simp [ht, htT], hst⟩
    have h2 : 2 ≤ (q.filter (fun x => ¬ x ∈ {x | N.leaf x ∈ T})).card :=
      Finset.one_lt_card.mpr ⟨s', Finset.mem_filter.mpr ⟨hs', hsT'⟩, t',
        Finset.mem_filter.mpr ⟨ht', htT'⟩, hst'⟩
    have := Finset.card_filter_add_card_filter_not (s := q) (· ∈ {x | N.leaf x ∈ T})
    omega
  · rintro ⟨v, hv, hdet⟩ ⟨e, he, h2⟩
    obtain ⟨x₀, hx₀⟩ : (q.filter (N.IsBelow e)).Nonempty := Finset.card_pos.mp (by omega)
    obtain ⟨hx₀q, hx₀b⟩ := Finset.mem_filter.mp hx₀
    have hY : ∀ y ∈ (Y : Set X), N.Dominates e y ∨ ¬ N.IsBelow e y := fun y hy => by
      by_cases hb : N.IsBelow e y
      · exact Or.inl (he y (Finset.mem_coe.mp hy) hb)
      · exact Or.inr hb
    obtain ⟨-, hc⟩ := crosses_domSet_iff hN (hqY x₀ hx₀q) (he x₀ (hq hx₀q) hx₀b) hY
    have hO : OnlyCrosses N.graph (N.ancestralArcs (Y : Set X)) e (N.domSet e) :=
      fun f hf hcf => (hc f hf).mp hcf
    have hW : ∀ s ∈ q, N.graph.Walks (N.ancestralArcs (Y : Set X)) v (N.leaf s) := fun s hs =>
      walks_ancestral hN hv (N.leaf_mem_ancestralVertices (hqY s hs))
    have h2' : (q.filter fun x => ¬ N.IsBelow e x).card = 2 := by
      have := Finset.card_filter_add_card_filter_not (s := q) (N.IsBelow e)
      omega
    obtain ⟨s, t, hst, hf⟩ := Finset.card_eq_two.mp h2
    obtain ⟨s', t', hst', hf'⟩ := Finset.card_eq_two.mp h2'
    have hs : s ∈ q.filter (N.IsBelow e) := by simp [hf]
    have ht : t ∈ q.filter (N.IsBelow e) := by simp [hf]
    have hs' : s' ∈ q.filter fun x => ¬ N.IsBelow e x := by simp [hf']
    have ht' : t' ∈ q.filter fun x => ¬ N.IsBelow e x := by simp [hf']
    obtain ⟨hsq, hsb⟩ := Finset.mem_filter.mp hs
    obtain ⟨htq, htb⟩ := Finset.mem_filter.mp ht
    obtain ⟨hsq', hsb'⟩ := Finset.mem_filter.mp hs'
    obtain ⟨htq', htb'⟩ := Finset.mem_filter.mp ht'
    have hnd : ∀ {x : X}, ¬ N.IsBelow e x → N.leaf x ∈ (N.domSet e)ᶜ := fun hb hd =>
      hb (Dominates.isBelow hN hd)
    by_cases hvT : v ∈ N.domSet e
    · exact hst' (hdet.eq_of_mem_side hO.compl (not_not.mpr hvT) hsq' htq' (hW s' hsq') (hW t' htq')
        (hnd hsb') (hnd htb'))
    · exact hst (hdet.eq_of_mem_side hO hvT hsq htq (hW s hsq) (hW t htq) (he s (hq hsq) hsb)
        (he t (hq htq) htb))

omit [Fintype X] [DecidableEq X] in
/-- **Corollary 2 of the source**, for taxon sets: a B-quartet on the subgraph induced on a set of
taxa is one on the subgraph induced on any larger set. From Lemma 2. -/
theorem corollary2 (hN : N.IsPhylogenetic) {Y Z q : Finset X} (hYZ : Y ⊆ Z) (hq : q ⊆ Y)
    (h4 : q.card = 4) (hR : ¬ Resolves N Y q) : ¬ Resolves N Z q := by
  obtain ⟨v, hv, hdet⟩ := (not_resolves_iff_exists_determines hN hq h4).mp hR
  have hsub : ((Y : Finset X) : Set X) ⊆ Z := Finset.coe_subset.mpr hYZ
  refine (not_resolves_iff_exists_determines hN (hq.trans hYZ) h4).mpr
    ⟨v, N.ancestralVertices_mono hsub hv, (lemma2 (N.ancestralArcs_mono hsub) (by omega)
      (fun s _ => isPendantIn_leaf hN s _) ?_ ?_ hdet).1⟩
  · exact fun s hs => walks_ancestral hN hv
      (N.leaf_mem_ancestralVertices (Finset.mem_coe.mpr (hq hs)))
  · exact fun f hf => walks_ancestral hN hv (N.source_mem_ancestralVertices hf)

omit [Fintype X] in
/-- **Lemma 3 of the source**, in the fixed network, for the subgraphs induced on subsets `Y`. Its
proof is `lemma3_blob` in the source's language of blobs: `¬ Resolves` is translated to and from
"determines a blob" by `not_resolves_iff_exists_determines`, and the hypotheses on `e₀` give a side
of a cut edge of the subgraph induced on `Y \ {α}`. -/
theorem lemma3 (hN : N.IsPhylogenetic) {Y : Finset X} {a b c d α : X} {e₀ : E}
    (h4 : ({a, b, c, d} : Finset X).card = 4) (ha : a ∈ Y) (hb : b ∈ Y) (hc : c ∈ Y) (hd : d ∈ Y)
    (hα : α ∈ Y) (hαa : α ≠ a) (hαb : α ≠ b) (hαc : α ≠ c) (hαd : α ≠ d)
    (hcut : ∀ x ∈ Y, x ≠ α → N.IsBelow e₀ x → N.Dominates e₀ x)
    (hor : (N.IsBelow e₀ a ∧ N.IsBelow e₀ b ∧ ¬ N.IsBelow e₀ c ∧ ¬ N.IsBelow e₀ d) ∨
      (¬ N.IsBelow e₀ a ∧ ¬ N.IsBelow e₀ b ∧ N.IsBelow e₀ c ∧ N.IsBelow e₀ d))
    (hB : ¬ Resolves N Y {a, b, c, d}) : ¬ Resolves N (Y.erase d) {a, b, c, α} := by
  obtain ⟨hab, hac, had, hbc, hbd, hcd⟩ := TreeMetric.ne_of_card_four h4
  have hq : ({a, b, c, d} : Finset X) ⊆ Y := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl <;> assumption
  have hq' : ({a, b, c, α} : Finset X) ⊆ Y.erase d := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact Finset.mem_erase.mpr ⟨had, ha⟩
    · exact Finset.mem_erase.mpr ⟨hbd, hb⟩
    · exact Finset.mem_erase.mpr ⟨hcd, hc⟩
    · exact Finset.mem_erase.mpr ⟨hαd, hα⟩
  have h4' : ({a, b, c, α} : Finset X).card = 4 :=
    TreeMetric.card_four_of_ne hab hac hαa.symm hbc hαb.symm hαc.symm
  obtain ⟨v₀, hv₀, hdet⟩ := (not_resolves_iff_exists_determines hN hq h4).mp hB
  -- the arc `e₀` gives a side of a cut edge of the subgraph induced on `Y \ {α}`
  have hmem : ∀ {x : X}, x ∈ Y → x ≠ α → x ∈ ((Y.erase α : Finset X) : Set X) := fun hx hne =>
    Finset.mem_coe.mpr (Finset.mem_erase.mpr ⟨hne, hx⟩)
  have hY : ∀ y ∈ ((Y.erase α : Finset X) : Set X), N.Dominates e₀ y ∨ ¬ N.IsBelow e₀ y := by
    intro y hy
    obtain ⟨hyα, hyY⟩ := Finset.mem_erase.mp (Finset.mem_coe.mp hy)
    by_cases hbe : N.IsBelow e₀ y
    · exact Or.inl (hcut y hyY hyα hbe)
    · exact Or.inr hbe
  have hnd : ∀ {x : X}, ¬ N.IsBelow e₀ x → N.leaf x ∉ N.domSet e₀ := fun hb' hd' =>
    hb' (Dominates.isBelow hN hd')
  obtain ⟨T₁, hT₁, ha₁, hb₁, hc₁, hd₁⟩ : ∃ T₁, OnlyCrosses N.graph (arcsOff N Y α) e₀ T₁ ∧
      N.leaf a ∉ T₁ ∧ N.leaf b ∉ T₁ ∧ N.leaf c ∈ T₁ ∧ N.leaf d ∈ T₁ := by
    rcases hor with ⟨ba, bb, nc, nd⟩ | ⟨na, nb, bc, bd⟩
    · obtain ⟨-, hcr⟩ := crosses_domSet_iff hN (hmem ha hαa.symm) (hcut a ha hαa.symm ba) hY
      refine ⟨(N.domSet e₀)ᶜ, OnlyCrosses.compl fun f hf hcf => (hcr f hf).mp hcf, ?_, ?_, hnd nc, hnd nd⟩
      · exact not_not.mpr (hcut a ha hαa.symm ba)
      · exact not_not.mpr (hcut b hb hαb.symm bb)
    · obtain ⟨-, hcr⟩ := crosses_domSet_iff hN (hmem hc hαc.symm) (hcut c hc hαc.symm bc) hY
      exact ⟨N.domSet e₀, fun f hf hcf => (hcr f hf).mp hcf, hnd na, hnd nb,
        hcut c hc hαc.symm bc, hcut d hd hαd.symm bd⟩
  obtain ⟨v, hv, hdet'⟩ := lemma3_blob hN h4 ha hb hc hd hα hαa hαb hαc hαd hv₀ hdet hT₁ ha₁ hb₁ hc₁ hd₁
  exact (not_resolves_iff_exists_determines hN hq' h4').mpr ⟨v, hv, hdet'⟩

omit [Fintype X] [DecidableEq X] in
/-- **"All edges in `ℬ` are retained"**, in the first step of the source's proof of Theorem 3. Let
`R` have a taxon from each component containing a taxon, of the graph left by deleting the blob of
`v`, which `q` determines. Each node of the blob is above a taxon of `R`: paths from it leave the
blob by a cut edge `g` directed away from it, and every taxon beyond `g` is below `g`. -/
theorem exists_reaches_rep (hN : N.IsPhylogenetic) {Y R q : Finset X} {v p : V}
    (hv : v ∈ N.ancestralVertices (Y : Set X)) (hqY : q ⊆ Y) (h3 : 3 ≤ q.card)
    (hdet : Determines N.graph (N.ancestralArcs (Y : Set X)) v N.leaf q) (hRY : R ⊆ Y)
    (hcov : ∀ x ∈ Y, ∃ r ∈ R, N.graph.Walks
      (N.ancestralArcs (Y : Set X) \ incidentCuts N.graph (N.ancestralArcs (Y : Set X)) v) (N.leaf x) (N.leaf r))
    (hp : SameBlobIn N.graph (N.ancestralArcs (Y : Set X)) v p) :
    ∃ r ∈ R, N.graph.Reaches p (N.leaf r) := by
  have hWq : ∀ t ∈ q, N.graph.Walks (N.ancestralArcs (Y : Set X)) v (N.leaf t) := fun t ht =>
    walks_ancestral hN hv (N.leaf_mem_ancestralVertices (Finset.mem_coe.mpr (hqY ht)))
  obtain ⟨x, hx, hpx⟩ := mem_ancestralVertices_of_walks hv hp.walks
  have hvx := walks_ancestral hN hv (N.leaf_mem_ancestralVertices hx)
  -- the cut edge `g` leading to the component of `x`
  have hb : ¬ SameBlobIn N.graph (N.ancestralArcs (Y : Set X)) v (N.leaf x) := fun h =>
    hdet.ne_of_isPendantIn h3 (isPendantIn_leaf hN x _) hWq ((isPendantIn_leaf hN x _).eq_of_sameBlobIn h)
  obtain ⟨g, hg⟩ := (exists_leadsTo hvx).resolve_left hb
  obtain ⟨r, hr, hw⟩ := hcov x (Finset.mem_coe.mp hx)
  have hO : OnlyCrosses N.graph (N.ancestralArcs (Y : Set X)) g
      (far N.graph (N.ancestralArcs (Y : Set X)) g v) := onlyCrosses_far
  have hrT : N.leaf r ∈ far N.graph (N.ancestralArcs (Y : Set X)) g v :=
    (N.graph.mem_iff_mem_of_walks
      (F := N.ancestralArcs (Y : Set X) \ incidentCuts N.graph (N.ancestralArcs (Y : Set X)) v)
      (fun f hf hc => hf.2 (hO f hf.1 hc ▸ hg.1)) hw).mp hg.2
  have hpT : p ∉ far N.graph (N.ancestralArcs (Y : Set X)) g v :=
    fun hc => hc (hp.walks_diff hg.1.1)
  obtain ⟨h1, h2, -, -⟩ := reaches_of_enters hO hpT hg.2 hpx fun f hf => ⟨x, hx, hf⟩
  -- the root is on the side of the blob
  have hroot : N.root ∉ far N.graph (N.ancestralArcs (Y : Set X)) g v := fun hrootT =>
    (reaches_of_enters hO.compl (not_not.mpr hrootT) h2 (hN.root_reaches _) fun f hf =>
      N.mem_ancestralVertices_of_reaches hf (N.source_mem_ancestralVertices hg.1.1.1)).2.1 h2
  obtain ⟨-, -, -, h4⟩ := reaches_of_enters hO hroot hrT (hN.root_reaches _) fun f hf =>
    ⟨r, Finset.mem_coe.mpr (hRY hr), hf⟩
  exact ⟨r, hr, (h1.tail ⟨g, rfl, rfl⟩).trans h4⟩

omit [Fintype X] in
/-- **The first step of the source's proof of Theorem 3.** If `q` determines a blob of the subgraph
on `Y`, choose one taxon from each component with a taxon of the graph left by deleting the blob,
four of these being `q`. Passing to the subgraph on those taxa, all arcs of the blob are retained,
and `q` still determines a blob. -/
theorem exists_representatives (hN : N.IsPhylogenetic) {Y q : Finset X} (hqY : q ⊆ Y) (h4 : q.card = 4)
    (hR : ¬ Resolves N Y q) : ∃ R, q ⊆ R ∧ R ⊆ Y ∧ ¬ Resolves N R q := by
  obtain ⟨v, hv, hdet⟩ := (not_resolves_iff_exists_determines hN hqY h4).mp hR
  have h3 : 3 ≤ q.card := by omega
  -- one taxon from each component: a largest subset of `Y` containing `q` with no two in one component
  have hmemq : q ∈ Y.powerset.filter
      fun R => q ⊆ R ∧ Determines N.graph (N.ancestralArcs (Y : Set X)) v N.leaf R :=
    Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hqY, Finset.Subset.refl _, hdet⟩
  obtain ⟨R, hqR, hmem, hmax⟩ := Finset.exists_le_maximal _ hmemq
  obtain ⟨hRY', -, hdetR⟩ := Finset.mem_filter.mp hmem
  have hRY := Finset.mem_powerset.mp hRY'
  have hcov : ∀ x ∈ Y, ∃ r ∈ R, N.graph.Walks
      (N.ancestralArcs (Y : Set X) \ incidentCuts N.graph (N.ancestralArcs (Y : Set X)) v)
      (N.leaf x) (N.leaf r) := by
    intro x hx
    by_contra hno
    push Not at hno
    have hins : insert x R ∈ Y.powerset.filter
        fun R => q ⊆ R ∧ Determines N.graph (N.ancestralArcs (Y : Set X)) v N.leaf R := by
      refine Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (Finset.insert_subset hx hRY),
        hqR.trans (Finset.subset_insert _ _), fun s hs t ht hst hw => ?_⟩
      rcases Finset.mem_insert.mp hs with rfl | hs' <;> rcases Finset.mem_insert.mp ht with rfl | ht'
      · exact hst rfl
      · exact hno t ht' hw
      · exact hno s hs' (N.graph.walks_symm hw)
      · exact hdetR s hs' t ht' hst hw
    have hxR : x ∈ R := hmax hins (Finset.subset_insert _ _) (Finset.mem_insert_self _ _)
    exact hno x hxR .refl
  have hsub : ((R : Finset X) : Set X) ⊆ Y := Finset.coe_subset.mpr hRY
  -- all arcs of the blob are retained
  have : Finite E := hN.finite_arcs
  have harcs : blobArcsIn N.graph (N.ancestralArcs (Y : Set X)) v ⊆ N.ancestralArcs (R : Set X) := by
    intro f hf
    obtain ⟨r, hr, hreach⟩ := exists_reaches_rep hN hv hqY h3 hdet hRY hcov
      (Relation.ReflTransGen.tail hf.2 ⟨f, hf.1, Or.inl ⟨rfl, rfl⟩⟩)
    exact ⟨r, Finset.mem_coe.mpr hr, hreach⟩
  have hblob : ∀ x, SameBlobIn N.graph (N.ancestralArcs (Y : Set X)) v x →
      SameBlobIn N.graph (N.ancestralArcs (R : Set X)) v x := fun x hx =>
    sameBlobIn_of_isBridgelessSubgraph (isBridgelessSubgraph_blob v) harcs
      Relation.ReflTransGen.refl hx
  obtain ⟨r, hr, hreach⟩ := exists_reaches_rep hN hv hqY h3 hdet hRY hcov Relation.ReflTransGen.refl
  exact ⟨R, hqR, hRY, (not_resolves_iff_exists_determines hN hqR h4).mpr
    ⟨v, ⟨r, Finset.mem_coe.mpr hr, hreach⟩,
      hdet.of_subset (N.ancestralArcs_mono hsub) hblob⟩⟩

/-- The induction of the source's Theorem 3, on the taxa `Y` of the subgraph. For `Y = q` the base
case; otherwise the source's three steps: pass to one taxon per component at the blob
(`exists_representatives`); remove a taxon if `q` stays unresolved; and otherwise Lemma 3 twice and
Inference Rule (a). -/
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
    -- one taxon per component at the blob
    obtain ⟨R, hqR, -, hRR⟩ := exists_representatives hN hqY hq hR
    by_cases hRlt : R ⊂ Y
    · exact ih _ (hY ▸ Finset.card_lt_card hRlt) R rfl q hq hqR hRR
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

/-- A B-quartet of the network, as the tree of blobs defines it, is a set of four taxa unresolved on
the whole network. With `not_resolves_iff_exists_determines`, this is the source's Definition 12:
`q` determines a blob. -/
theorem isBQuartet_iff_not_resolves (hN : N.IsPhylogenetic) {q : Finset X} (hq : q.card = 4) :
    IsBQuartet N q ↔ ¬ Resolves N Finset.univ q := by
  constructor
  · rintro hB ⟨e, he, h2⟩
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
  · refine fun hR => (TreeMetric.forall_not_displays_iff hq).mpr fun A hA h2 => hR ?_
    have hcut := (hasCutSplit_iff_hasCutSplitOn_univ hN _).mp (Finset.mem_filter.mp hA).2.2.2
    refine resolves_of_hasCutSplitOn hN (Y := Finset.univ) (by simpa using hcut)
      (Finset.subset_univ _) hq ?_
    rw [← h2]
    congr 1
    ext z
    simp only [Finset.mem_filter, Finset.mem_inter, Finset.mem_coe]
    tauto

/-- A blob determined by at least three taxa of a B-quartet `q` is the blob that `q` determines. This
is "since `{a, b, c, d}` and `{b, c, d, e}` are B-quartets, undirected paths in the tree of blobs from
the taxa `a` and `e` also first meet those from `b, c, d` at `v`" in the source's proof of Theorem 2. -/
theorem determines_of_isBQuartet (hN : N.IsPhylogenetic) {v : V} {q S : Finset X} (hq : q.card = 4)
    (hB : IsBQuartet N q) (hS : S ⊆ q) (h3 : 2 < S.card)
    (hv : v ∈ N.ancestralVertices ((Finset.univ : Finset X) : Set X))
    (hdet : Determines N.graph (N.ancestralArcs ((Finset.univ : Finset X) : Set X)) v N.leaf S) :
    Determines N.graph (N.ancestralArcs ((Finset.univ : Finset X) : Set X)) v N.leaf q := by
  obtain ⟨v', hv', hdet'⟩ := (not_resolves_iff_exists_determines hN (Finset.subset_univ q) hq).mp
    ((isBQuartet_iff_not_resolves hN hq).mp hB)
  refine hdet'.of_sameBlobIn ((hdet'.mono hS).sameBlobIn hdet h3 (fun s _ => ?_)
    (walks_ancestral hN hv' hv))
  exact walks_ancestral hN hv' (N.leaf_mem_ancestralVertices (Finset.mem_coe.mpr (Finset.mem_univ s)))

/-- "An edge in the tree of blobs, and hence a cut edge in the network" (the source's proof of Theorem
2): a cut edge of the network with a taxon on each side gives a side of the tree of blobs. -/
theorem filter_mem_treeOfBlobs (hN : N.IsPhylogenetic) {g : E} {T : Set V}
    (hg : g ∈ N.ancestralArcs ((Finset.univ : Finset X) : Set X))
    (hO : OnlyCrosses N.graph (N.ancestralArcs ((Finset.univ : Finset X) : Set X)) g T)
    (hc : N.graph.Crosses g T) {x y : X} (hx : N.leaf x ∈ T) (hy : N.leaf y ∉ T) :
    Finset.univ.filter (fun z => N.leaf z ∈ T) ∈ treeOfBlobs N := by
  rw [Finset.coe_univ] at hg hO
  refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨x, by simpa using hx⟩, ⟨y, by simpa using hy⟩, ?_⟩
  refine (hasCutSplit_iff_hasCutSplitOn_univ hN _).mpr ⟨g, hg, T, fun f hf => ⟨hO f hf, ?_⟩, fun z _ => ?_⟩
  · rintro rfl
    exact hc
  · simp

/-- The rule in the form used by the closure: its third hypothesis is that one of the three sets is
a B-quartet of the network, or has a cut-edge split separating `a, e` on its induced network. This
is stronger than the source's Theorem 2 (`theorem2`), whose hypothesis (b) asks for a B-quartet on
the induced 4-taxon network, and it is needed: the closure's rule fires from a set inferred to be a
B-quartet of the network, which may be treelike when induced (`closure_sound`). The source's proof
applies unchanged, since a cut edge separating `a, e` from `b, c, d` also resolves the set on the
network (`not_separating`).

The proof is the source's, `notes/sources/allman2023.txt` lines 199-200, in its order. The taxa `b, c, d`
determine a blob, a node `v` of the tree of blobs, and the two B-quartets make `a` and `e` first meet them
at `v` (`determines_of_isBQuartet`). If the paths from `a`, `e` met before `v`, they would use one incident
cut edge of the blob, separating `a, e` from `b, c, d` (`filter_mem_treeOfBlobs`), and picking any two of
`b, c, d` contradicts the third hypothesis (`not_separating`). So all five paths first meet at `v`
(`Determines.insert`), and every four of the five taxa determine that blob. -/
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
  have hU : ∀ x : X, x ∈ ((Finset.univ : Finset X) : Set X) := fun x =>
    Finset.mem_coe.mpr (Finset.mem_univ x)
  -- "The taxa `b, c, d` determine a blob in `𝒩⁺`, corresponding to a node `v` in its tree of blobs."
  obtain ⟨v, hv, hdet⟩ := exists_determines_three hN (hU b) (hU c) (hU d) hbc hbd hcd
  have hw : ∀ x, N.graph.Walks (N.ancestralArcs ((Finset.univ : Finset X) : Set X)) v (N.leaf x) :=
    fun x => walks_ancestral hN hv (N.leaf_mem_ancestralVertices (hU x))
  have h3 : ({b, c, d} : Finset X).card = 3 := by
    rw [Finset.card_insert_of_notMem (by simp [hbc, hbd]), Finset.card_pair hcd]
  have h4₁ : ({a, b, c, d} : Finset X).card = 4 := TreeMetric.card_four_of_ne hab hac had hbc hbd hcd
  have h4₂ : ({b, c, d, e} : Finset X).card = 4 := TreeMetric.card_four_of_ne hbc hbd hbe hcd hce hde
  have hsub₂ : ({b, c, d} : Finset X) ⊆ {b, c, d, e} := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx ⊢
    tauto
  -- "since `{a, b, c, d}` and `{b, c, d, e}` are B-quartets, undirected paths in the tree of blobs from
  -- the taxa `a` and `e` also first meet those from `b, c, d` at `v`"
  have hdet₁ := determines_of_isBQuartet hN h4₁ habcd (Finset.subset_insert a _) (by omega) hv hdet
  have hdet₂ := determines_of_isBQuartet hN h4₂ hbcde hsub₂ (by omega) hv hdet
  -- every taxon is beyond a cut edge incident to the blob
  have hlead : ∀ x, ∃ g, LeadsTo N.graph (N.ancestralArcs ((Finset.univ : Finset X) : Set X)) v g (N.leaf x) :=
    fun x => (exists_leadsTo (hw x)).resolve_left fun hb =>
      hdet.ne_of_isPendantIn (by omega) (isPendantIn_leaf hN x _) (fun s _ => hw s)
        ((isPendantIn_leaf hN x _).eq_of_sameBlobIn hb)
  -- "Suppose the paths from `a`, `e` do meet before `v`."
  have hmeet : ∀ g, LeadsTo N.graph (N.ancestralArcs ((Finset.univ : Finset X) : Set X)) v g (N.leaf a) →
      LeadsTo N.graph (N.ancestralArcs ((Finset.univ : Finset X) : Set X)) v g (N.leaf e) → False := by
    intro g hga hge
    -- "Then there is an edge in the tree of blobs, and hence a cut edge in the network, that separates
    -- `a`, `e` from `b`, `c`, `d`."
    have hO : OnlyCrosses N.graph (N.ancestralArcs ((Finset.univ : Finset X) : Set X)) g
        (far N.graph (N.ancestralArcs ((Finset.univ : Finset X) : Set X)) g v) := onlyCrosses_far
    have hvT : v ∉ far N.graph (N.ancestralArcs ((Finset.univ : Finset X) : Set X)) g v :=
      not_mem_far_self
    have hbT : N.leaf b ∉ far N.graph (N.ancestralArcs ((Finset.univ : Finset X) : Set X)) g v :=
      fun h => hab (hdet₁.eq_of_mem_side hO hvT (by simp) (by simp) (hw a) (hw b) hga.2 h)
    have hcT : N.leaf c ∉ far N.graph (N.ancestralArcs ((Finset.univ : Finset X) : Set X)) g v :=
      fun h => hac (hdet₁.eq_of_mem_side hO hvT (by simp) (by simp) (hw a) (hw c) hga.2 h)
    have hdT : N.leaf d ∉ far N.graph (N.ancestralArcs ((Finset.univ : Finset X) : Set X)) g v :=
      fun h => had (hdet₁.eq_of_mem_side hO hvT (by simp) (by simp) (hw a) (hw d) hga.2 h)
    obtain ⟨hgF, p, r, hl, hp, hr⟩ := exists_links_of_walks hO hvT (hw a) hga.2
    have hA := filter_mem_treeOfBlobs hN hgF hO (hl.crosses hp hr) hga.2 hbT
    have hmemA : ∀ {x}, N.leaf x ∈ far N.graph (N.ancestralArcs ((Finset.univ : Finset X) : Set X)) g v →
        x ∈ Finset.univ.filter (fun z => N.leaf z ∈ far N.graph (N.ancestralArcs ((Finset.univ : Finset X) : Set X)) g v) :=
      fun hx => Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx⟩
    have hnmemA : ∀ {x}, N.leaf x ∉ far N.graph (N.ancestralArcs ((Finset.univ : Finset X) : Set X)) g v →
        x ∉ Finset.univ.filter (fun z => N.leaf z ∈ far N.graph (N.ancestralArcs ((Finset.univ : Finset X) : Set X)) g v) :=
      fun hx hm => hx (Finset.mem_filter.mp hm).2
    -- "This implies that picking any two of `b, c, d`, the taxa `a`, `e` are not separated in the 4-taxon
    -- tree of blobs, nor do they form a B-quartet with `a`, `e`."
    simp only [Finset.mem_insert, Finset.mem_singleton] at ht
    rcases ht with rfl | rfl | rfl
    · have hset : ({a, b, c, e} : Finset X) = {a, e, b, c} := by grind
      rw [hset] at hrule
      exact not_separating hN hS (TreeMetric.card_four_of_ne hae hab hac hbe.symm hce.symm hbc) hA
        (hmemA hga.2) (hmemA hge.2) (hnmemA hbT) (hnmemA hcT) hrule
    · have hset : ({a, b, d, e} : Finset X) = {a, e, b, d} := by grind
      rw [hset] at hrule
      exact not_separating hN hS (TreeMetric.card_four_of_ne hae hab had hbe.symm hde.symm hbd) hA
        (hmemA hga.2) (hmemA hge.2) (hnmemA hbT) (hnmemA hdT) hrule
    · have hset : ({a, c, d, e} : Finset X) = {a, e, c, d} := by grind
      rw [hset] at hrule
      exact not_separating hN hS (TreeMetric.card_four_of_ne hae hac had hce.symm hde.symm hcd) hA
        (hmemA hga.2) (hmemA hge.2) (hnmemA hcT) (hnmemA hdT) hrule
  -- "so that all 5 paths from `a, b, c, d, e` first meet at `v`"
  obtain ⟨ge, hge⟩ := hlead e
  have hdet₅ : Determines N.graph (N.ancestralArcs ((Finset.univ : Finset X) : Set X)) v N.leaf
      (insert e {a, b, c, d}) := by
    refine hdet₁.insert (hw e) hge fun s hs => ?_
    obtain ⟨gs, hgs⟩ := hlead s
    refine ⟨gs, hgs, ?_⟩
    simp only [Finset.mem_insert, Finset.mem_singleton] at hs
    rcases hs with rfl | rfl | rfl | rfl
    · rintro rfl
      exact hmeet gs hgs hge
    · exact hdet₂.ne_of_leadsTo (by simp) (by simp) hbe (hw _) (hw e) hgs hge
    · exact hdet₂.ne_of_leadsTo (by simp) (by simp) hce (hw _) (hw e) hgs hge
    · exact hdet₂.ne_of_leadsTo (by simp) (by simp) hde (hw _) (hw e) hgs hge
  have hfin : ∀ q : Finset X, q ⊆ insert e {a, b, c, d} → q.card = 4 → IsBQuartet N q :=
    fun q hsub h4 => (isBQuartet_iff_not_resolves hN h4).mpr
      ((not_resolves_iff_exists_determines hN (Finset.subset_univ q) h4).mpr
        ⟨v, hv, hdet₅.mono hsub⟩)
  have hsub : ∀ {r s u v' : X}, r ∈ (insert e {a, b, c, d} : Finset X) →
      s ∈ (insert e {a, b, c, d} : Finset X) → u ∈ (insert e {a, b, c, d} : Finset X) →
      v' ∈ (insert e {a, b, c, d} : Finset X) → ({r, s, u, v'} : Finset X) ⊆ insert e {a, b, c, d} := by
    intro r s u v' hr hs hu hv' x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl <;> assumption
  simp only [Finset.mem_insert, Finset.mem_singleton] at hq
  rcases hq with rfl | rfl | rfl
  · exact hfin _ (hsub (by simp) (by simp) (by simp) (by simp))
      (TreeMetric.card_four_of_ne hab hac hae hbc hbe hce)
  · exact hfin _ (hsub (by simp) (by simp) (by simp) (by simp))
      (TreeMetric.card_four_of_ne hab had hae hbd hbe hde)
  · exact hfin _ (hsub (by simp) (by simp) (by simp) (by simp))
      (TreeMetric.card_four_of_ne hac had hae hcd hce hde)

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

/-- **Theorem 3 of the source, combinatorial part.** From the 4-taxon sets with no cut-edge split on
their induced networks, and the quartet trees of the others, the closure under the inference rule
reaches every B-quartet of the network. With soundness (`theorem2`) this is what Theorem 3 uses of
Theorem 1. The induction is on the taxa of an induced subgraph, as in the source, in `closure_aux`.
The source concludes on the induced networks and transfers to `𝒩⁺` by its Corollary 2
(`corollary2`). Here the closure is taken on the fixed network throughout, so the transfer is built
in. -/
theorem closure_complete (hN : N.IsPhylogenetic) {q : Finset X} (hq : q.card = 4)
    (hB : IsBQuartet N q) :
    BInferred {q' | q'.card = 4 ∧ ¬ IsTreelike N q'} {s | InducedCutSplit N s} q :=
  closure_aux hN _ Finset.univ rfl q hq (Finset.subset_univ _)
    ((isBQuartet_iff_not_resolves hN hq).mp hB)

/-- Soundness of the closure: everything the rule infers from the 4-taxon sets with no cut-edge
split on their induced networks is a B-quartet. -/
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
