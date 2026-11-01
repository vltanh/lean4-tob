module

public import Gusfield2007.BlobFacts
public import Mathlib.Basic.Finite.Sigma
public import Mathlib.Basic.Finite.Sum
public import Mathlib.SetTheory.Cardinal.Finite

/-!
# Gusfield et al. 2007: the restriction of a network to a component, and Lemma 5

The construction of the proof of Lemma 5. The paper removes parts of a network there, and "the resulting network is a phylogenetic network" (line 480): in Lean that last step is `Network.exists_trim`.

* `Network.RS_le_card_breaksAt`: "if we remove all such recombination nodes from `N`, and also remove any site that is not in `C*`, the resulting network
  is a phylogenetic network `N_{C*}` that derives the set of sequences `M(C*)`" (line 479). The recombination nodes kept are those that break `C`.
-/

@[expose] public section

open scoped Classical

namespace Gusfield2007

namespace Network

universe u v w

variable {ι : Type u} {V : Type v} {E : Type w}

section Restrict

variable [LinearOrder ι] (N : Network ι V E) (C : Set ι)

omit [LinearOrder ι] in
variable {N C} in
theorem exists_arc_of_not_breaksAt {x : V} (h : ¬ N.BreaksAt x C) :
    ∃ e, N.tgt e = x ∧ C.domRestrict (N.label x) = C.domRestrict (N.label (N.src e)) := by
  unfold BreaksAt at h
  push Not at h
  exact h

omit [LinearOrder ι] in
/-- An arc kept on restricting to the sites of `C`: all the arcs into a node that breaks `C`, and otherwise one arc from a parent with the same
sequence on `C`. So a recombination node that doesn't break `C` loses an arc. -/
def KeptArc (e : E) : Prop :=
  N.BreaksAt (N.tgt e) C ∨ ∃ h : ¬ N.BreaksAt (N.tgt e) C, e = (exists_arc_of_not_breaksAt h).choose

omit [LinearOrder ι] in
variable {N C} in
theorem keptArc_of_uniq {e : E} (h : ∀ f, N.tgt f = N.tgt e → f = e) : N.KeptArc C e := by
  by_cases hb : N.BreaksAt (N.tgt e) C
  · exact Or.inl hb
  · exact Or.inr ⟨hb, (h _ (exists_arc_of_not_breaksAt hb).choose_spec.1).symm⟩

/-- **Line 479.** The network `N_{C*}` of the proof of Lemma 5: only the sites of `C`, and only the recombination nodes that break `C`. All the nodes stay. -/
def restrictNet [Finite V] : Network C V {e // N.KeptArc C e} where
  src e := N.src e.1
  tgt e := N.tgt e.1
  root := N.root
  site i := ⟨N.site i.1, keptArc_of_uniq fun f hf => N.site_not_recomb i.1 f hf⟩
  label v i := N.label v i.1
  simple e f h₁ h₂ := Subtype.ext (N.simple _ _ h₁ h₂)
  acyclic := by
    obtain ⟨ρ, hρ⟩ := N.exists_rank
    exact acyclic_of_rank ρ fun e => hρ e.1
  root_iff v := by
    constructor
    · intro h
      refine (N.root_iff v).1 fun g hg => ?_
      by_cases hb : N.BreaksAt v C
      · exact h ⟨g, Or.inl (hg ▸ hb)⟩ hg
      · have hch := (exists_arc_of_not_breaksAt hb).choose_spec
        refine h ⟨(exists_arc_of_not_breaksAt hb).choose, Or.inr ?_⟩ hch.1
        have hne : ¬ N.BreaksAt (N.tgt (exists_arc_of_not_breaksAt hb).choose) C := by rwa [hch.1]
        refine ⟨hne, ?_⟩
        generalize_proofs h₁ h₂
        congr 1
        rw [hch.1]
    · rintro rfl e he
      exact (N.root_iff N.root).2 rfl e.1 he
  inDegree_le_two e f g h₁ h₂ := by
    rcases N.inDegree_le_two _ _ _ h₁ h₂ with h | h | h
    · exact Or.inl (Subtype.ext h)
    · exact Or.inr (Or.inl (Subtype.ext h))
    · exact Or.inr (Or.inr (Subtype.ext h))
  site_not_recomb i f h := Subtype.ext (N.site_not_recomb i.1 f.1 h)
  label_tree e he i := by
    by_cases huniq : ∀ f, N.tgt f = N.tgt e.1 → f = e.1
    · have := N.label_tree e.1 huniq i.1
      simpa [Subtype.ext_iff] using this
    · push Not at huniq
      obtain ⟨f, hf, hfe⟩ := huniq
      have hb : ¬ N.BreaksAt (N.tgt e.1) C := fun hb =>
        hfe (congrArg Subtype.val (he ⟨f, Or.inl (hf ▸ hb)⟩ hf))
      have hch := (exists_arc_of_not_breaksAt hb).choose_spec
      have hkept : e.1 = (exists_arc_of_not_breaksAt hb).choose := by
        rcases e.2 with h | ⟨_, h⟩
        · exact absurd h hb
        · exact h
      have hne : N.site i.1 ≠ e.1 := fun hs => hfe ((N.site_not_recomb i.1 f (hs ▸ hf)).trans hs)
      have hl : N.label (N.tgt e.1) i.1 = N.label (N.src e.1) i.1 := by
        have h₁ : N.label (N.tgt e.1) i.1 = N.label (N.src (exists_arc_of_not_breaksAt hb).choose) i.1 := congrFun hch.2 i
        rw [← hkept] at h₁
        exact h₁
      simpa [Subtype.ext_iff, hne] using hl
  label_recomb e f hef h i := N.label_recomb e.1 f.1 (fun h' => hef (Subtype.ext h')) h i.1

variable {N C}

omit [LinearOrder ι] in
theorem choose_congr {x y : V} (h : x = y) (hx : ¬ N.BreaksAt x C) (hy : ¬ N.BreaksAt y C) :
    (exists_arc_of_not_breaksAt hx).choose = (exists_arc_of_not_breaksAt hy).choose := by
  subst h
  rfl

omit [LinearOrder ι] in
theorem restrictNet_isRecomb [Finite V] {x : V} (h : (N.restrictNet C).IsRecomb x) : N.IsRecomb x ∧ N.BreaksAt x C := by
  obtain ⟨e, f, hef, he, hf⟩ := h
  refine ⟨⟨e.1, f.1, fun h' => hef (Subtype.ext h'), he, hf⟩, ?_⟩
  by_contra hb
  have he' : N.tgt e.1 = x := he
  have hf' : N.tgt f.1 = x := hf
  subst he'
  have hg : ∀ g : {e // N.KeptArc C e}, N.tgt g.1 = N.tgt e.1 → g.1 = (exists_arc_of_not_breaksAt hb).choose := by
    intro g hg
    rcases g.2 with h | ⟨h₀, h⟩
    · exact absurd (hg ▸ h) hb
    · rw [h]
      exact choose_congr hg h₀ hb
  exact hef (Subtype.ext ((hg e rfl).trans (hg f hf').symm))

theorem restrictNet_obeys [Finite V] {m : Crossover} (h : N.Obeys m) : (N.restrictNet C).Obeys m := by
  cases m with
  | single =>
    intro x hx
    obtain ⟨hr, hb⟩ := restrictNet_isRecomb hx
    obtain ⟨e, f, hef, he, hf, L, hL⟩ := h x hr
    refine ⟨⟨e, Or.inl (he ▸ hb)⟩, ⟨f, Or.inl (hf ▸ hb)⟩, fun h' => hef (congrArg Subtype.val h'), he, hf,
      ⟨{i | i.1 ∈ L}, fun _ _ hba ha => L.lower hba ha⟩, fun i => ?_⟩
    exact hL i.1
  | multiple => trivial
  | pointwise =>
    intro x hx
    obtain ⟨hr, hb⟩ := restrictNet_isRecomb hx
    obtain ⟨e, f, hef, he, hf, j, hL⟩ := h x hr
    by_cases hj : j ∈ C
    · refine ⟨⟨e, Or.inl (he ▸ hb)⟩, ⟨f, Or.inl (hf ▸ hb)⟩, fun h' => hef (congrArg Subtype.val h'), he, hf, ⟨j, hj⟩, fun i => ?_⟩
      have h₂ := hL i.1
      by_cases hij : i.1 = j
      · have h₁ : i = ⟨j, hj⟩ := Subtype.ext hij
        simp only [hij, ↓reduceIte] at h₂
        simp only [h₁, ↓reduceIte]
        exact h₂
      · have h₁ : i ≠ ⟨j, hj⟩ := fun h => hij (congrArg Subtype.val h)
        simp only [hij, ↓reduceIte] at h₂
        simp only [h₁, ↓reduceIte]
        exact h₂
    · exfalso
      refine hb e he (funext fun i => ?_)
      have := hL i.1
      have hne : i.1 ≠ j := fun h' => hj (h' ▸ i.2)
      simpa [hne] using this

variable [Finite V] [Finite E]

/-- **Lemma 5, for one component** (lines 479 to 485). Remove the sites out of `C`, and at each recombination node that doesn't break `C`, the arc from the other parent: "the resulting network is a phylogenetic network `N_{C*}` that derives the set
of sequences `M(C*)`", with ancestral sequence `S(C*)`. Its recombination nodes are those that break `C`. In Lean, deriving has the rows exactly at the leaves, so the network is trimmed (`exists_trim`). -/
theorem RS_le_card_breaksAt {m : Crossover} {M : Finset (ι → Bool)} (hm : N.Obeys m) (hd : N.Derives M)
    (hC : NoConstantColumn M) (C : Set ι) :
    RS m (C.domRestrict N.ancestral) (restrictRows C M) ≤ Nat.card {x // N.IsRecomb x ∧ N.BreaksAt x C} := by
  obtain ⟨l, hl, -⟩ := N.exists_isLeaf_reach N.root
  have hne : (restrictRows C M).Nonempty := ⟨_, mem_restrictRows.2 ⟨_, hd.mapsTo hl, rfl⟩⟩
  have hex : ∀ s : restrictRows C M, ∃ v, (N.restrictNet C).label v = s.1 := by
    rintro ⟨s, hs⟩
    obtain ⟨r, hr, rfl⟩ := mem_restrictRows.1 hs
    obtain ⟨v, -, rfl⟩ := hd.surjOn hr
    exact ⟨v, rfl⟩
  choose c₁ hc₁ using hex
  obtain ⟨a, b, N', h₁, h₂, h₃, h₄⟩ := (N.restrictNet C).exists_trim hne hc₁ fun i => (hC.restrictRows C).exists_ne _ i
  have hle : RS m (C.domRestrict N.ancestral) (restrictRows C M) ≤ N'.recombCount :=
    Nat.sInf_le ⟨a, b, N', h₁ m (restrictNet_obeys hm), h₂, h₃, rfl⟩
  refine hle.trans (h₄.trans ?_)
  have hinj : Function.Injective fun x : {x // (N.restrictNet C).IsRecomb x ∧ (N.restrictNet C).Kept c₁ x} =>
      (⟨x.1, restrictNet_isRecomb x.2.1⟩ : {x // N.IsRecomb x ∧ N.BreaksAt x C}) := fun x y h => by
    simpa [Subtype.ext_iff] using h
  exact Nat.card_le_card_of_injective _ hinj

/-- The sum over the components (line 488): if each recombination node breaks at most one component of `G`, the sum is at most `R(N)`. `lemma5` is this for `G_S(M)`. -/
theorem sum_RS_le_recombCount [Finite ι] {m : Crossover} {M : Finset (ι → Bool)} {G : SimpleGraph ι} (hm : N.Obeys m) (hd : N.Derives M)
    (hC : NoConstantColumn M)
    (h : ∀ x, N.IsRecomb x → ∀ c c' : G.ConnectedComponent, N.BreaksAt x c.supp → N.BreaksAt x c'.supp → c = c') :
    ∑ᶠ C : G.ConnectedComponent, RS m (C.supp.domRestrict N.ancestral) (restrictRows C.supp M) ≤ N.recombCount := by
  have : Finite G.ConnectedComponent := Quot.finite _
  have := Fintype.ofFinite G.ConnectedComponent
  rw [finsum_eq_sum_of_fintype]
  refine (Finset.sum_le_sum fun C _ => RS_le_card_breaksAt hm hd hC C.supp).trans ?_
  have hsum : ∑ C : G.ConnectedComponent, Nat.card {x // N.IsRecomb x ∧ N.BreaksAt x C.supp} =
      Nat.card (Σ C : G.ConnectedComponent, {x // N.IsRecomb x ∧ N.BreaksAt x C.supp}) := by
    rw [Nat.card_sigma]
  rw [hsum]
  refine Nat.card_le_card_of_injective (fun p => (⟨p.2.1, p.2.2.1⟩ : {x // N.IsRecomb x})) ?_
  rintro ⟨c, x, hx, hb⟩ ⟨c', x', hx', hb'⟩ hxx
  obtain rfl : x = x' := congrArg Subtype.val hxx
  obtain rfl := h x hx c c' hb hb'
  rfl

omit [LinearOrder ι] [Finite E] in
variable (N) in
/-- **The recombination nodes of a blob break only the components with a site on it**: a site off the blob doesn't change along it. -/
theorem exists_site_mem_of_breaksAt {x : V} (hx : N.IsRecomb x) {C : Set ι} (hb : N.BreaksAt x C) :
    ∃ B, N.IsBlob B ∧ (∃ e ∈ B, N.tgt e = x) ∧ ∃ i ∈ C, N.site i ∈ B := by
  obtain ⟨e, f, hef, rfl, hf⟩ := hx
  obtain ⟨B, hB, he, -⟩ := exists_isBlob_of_tgt_eq hef hf.symm
  refine ⟨B, hB, ⟨e, he, rfl⟩, ?_⟩
  by_contra hne
  push Not at hne
  exact hb e rfl (funext fun i => (hB.label_src_eq_label_tgt (hne i.1 i.2) he).symm)

end Restrict

/-! ### Fully decomposed networks -/

section FullyDecomposed

variable {N : Network ι V E} [Finite V]

omit [Finite V] in
/-- Being fully decomposed depends on a graph only through its connected components. It's how a network for `G_S(M)` is a network for `G(M)`. -/
theorem IsFullyDecomposedFor.of_reachable_iff {G G' : SimpleGraph ι} (h : ∀ i j, G.Reachable i j ↔ G'.Reachable i j)
    (hf : N.IsFullyDecomposedFor G) : N.IsFullyDecomposedFor G' where
  blob_component B hB := by
    obtain ⟨c, hc, hi⟩ := hf.blob_component B hB
    induction c using SimpleGraph.ConnectedComponent.ind with
    | _ i₀ =>
      have hs : (G'.connectedComponentMk i₀).supp = (G.connectedComponentMk i₀).supp := by
        ext i
        simp only [SimpleGraph.ConnectedComponent.mem_supp_iff, SimpleGraph.ConnectedComponent.eq]
        exact (h i i₀).symm
      refine ⟨G'.connectedComponentMk i₀, hs ▸ hc, fun i => ?_⟩
      rw [hs]
      exact hi i
  isolated_treeArc i hi := hf.isolated_treeArc i fun j hj => by
    obtain ⟨k, hk⟩ := exists_adj_of_reachable ((h i j).1 hj.reachable) hj.ne
    exact hi k hk
  nodeDisjoint := hf.nodeDisjoint

/-- In a fully decomposed network, each recombination node breaks at most one component: so it's a 0 or 1-component recombination. -/
theorem IsFullyDecomposedFor.breaksAt_unique {G : SimpleGraph ι} (hf : N.IsFullyDecomposedFor G) {x : V} (hx : N.IsRecomb x)
    {c c' : G.ConnectedComponent} (hb : N.BreaksAt x c.supp) (hb' : N.BreaksAt x c'.supp) : c = c' := by
  obtain ⟨B, hB, ⟨e, he, hex⟩, i, hi, his⟩ := N.exists_site_mem_of_breaksAt hx hb
  obtain ⟨B', hB', ⟨e', he', hex'⟩, i', hi', his'⟩ := N.exists_site_mem_of_breaksAt hx hb'
  have hBB : B = B' := hB.eq_of_inter_nonempty hB' ⟨e', hB.mem_of_tgt_eq he (hex.trans hex'.symm), he'⟩
  subst hBB
  obtain ⟨c₀, -, hc₀⟩ := hf.blob_component B hB
  have h₁ : c = c₀ := by
    rw [← (SimpleGraph.ConnectedComponent.mem_supp_iff _ _).1 hi, ← (SimpleGraph.ConnectedComponent.mem_supp_iff _ _).1 ((hc₀ i).1 his)]
  have h₂ : c' = c₀ := by
    rw [← (SimpleGraph.ConnectedComponent.mem_supp_iff _ _).1 hi', ← (SimpleGraph.ConnectedComponent.mem_supp_iff _ _).1 ((hc₀ i').1 his')]
  exact h₁.trans h₂.symm

/-- In a fully decomposed network, each recombination node is a 0 or 1-component recombination. -/
theorem IsFullyDecomposedFor.isZero_or_isOne {G : SimpleGraph ι} (hf : N.IsFullyDecomposedFor G) {x : V} (hx : N.IsRecomb x) :
    N.IsZeroComponent G x ∨ N.IsOneComponent G x := by
  by_cases hc : ∃ c : G.ConnectedComponent, N.BreaksAt x c.supp
  · obtain ⟨c, hb⟩ := hc
    exact Or.inr ⟨c, hb, fun c' hb' => hf.breaksAt_unique hx hb' hb⟩
  · push Not at hc
    exact Or.inl hc

end FullyDecomposed

end Network

section Lemma5

universe u'

variable {ι : Type u'} [LinearOrder ι] [Finite ι] {V E : Type*} [Finite V] [Finite E]

/-- **Lemma 5** (`g:lem5`). "Let `N` be an arbitrary phylogenetic network for `M` with ancestral sequence `S`, and suppose that every
recombination in `N` is either a 0 or 1-component recombination. [...] If multiple-crossover recombinations are allowed in `N`, then
`R(N) ≥ Σ_{C ∈ G_S(M)} R_{S(C)}(M(C))`, and if only single-crossover recombinations are allowed, then `R(N) ≥ Σ_{C ∈ G_S(M)} R¹_{S(C)}(M(C))`" (line 463).

The standing assumption is needed. With `M = {00} = {S}`, a network with one recombination node derives `M` by flipping both sites on one
arc and then taking the root's sequence, and it's a 0-component recombination; each of the two trivial components needs one
recombination node on its own, since its site must mutate and come back. So the sum is 2. -/
theorem lemma5 {c : Crossover} {M : Finset (ι → Bool)} {S : ι → Bool} (hC : NoConstantColumn M) (N : Network ι V E)
    (hc : N.Obeys c) (hd : N.Derives M) (hS : N.ancestral = S)
    (h : ∀ x, N.IsRecomb x → N.IsZeroComponent (conflictGraph S M) x ∨ N.IsOneComponent (conflictGraph S M) x) :
    ∑ᶠ C : (conflictGraph S M).ConnectedComponent, RS c (C.supp.domRestrict S) (restrictRows C.supp M) ≤ N.recombCount := by
  subst hS
  refine Network.sum_RS_le_recombCount hc hd hC fun x hx C C' hb hb' => ?_
  rcases h x hx with h₀ | ⟨C₀, -, huniq⟩
  · exact absurd hb (h₀ C)
  · exact (huniq C hb).trans (huniq C' hb').symm

end Lemma5

end Gusfield2007
