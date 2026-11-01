module

public import AllmanEtAl2023.Lemma1
public import AllmanEtAl2023.ClaimsTheorem1
public import AllmanEtAl2023.GenericCF

/-!
# Allman, Baños, Mitchell, Rhodes 2023: statement (a) in the proof of Theorem 1

"To establish (a), suppose `T` is resolved, with topology `ab|cd`. Permuting taxon names if necessary, we may assume that the reduced rooted tree of blobs thus has topology `(((a, b), c), d)`, `((a, b), (c, d))`, or
`((a, b), c, d)`." The rooted forms are `rootedForms`, a theorem on the clusters of `T_rd(𝒩⁺)`. The paper's three forms up to names are its seven: the names of the cherry below the edge are `a, b` in four of them, and `c, d` in three.

Each form gives the edge `f` that the paper argues on, and where its source is (`exists_edge_of_rootedForm`):

* "In the first case, `(((a, b), c), d)`": `f` is the edge above `a, b`, and its source is in a 3-blob, determined by `a, c, d` (`exists_edge_first`);
* "The remaining cases, of the reduced rooted trees of blobs `((a, b), (c, d))` and `((a, b), c, d)`": `f` is the edge above `a, b`, and its source is in the blob containing the LSA (`exists_edge_second`).

Then, on that edge:

* "if a gene tree forms under the NMSC by the `a, b` lineages coalescing below the 3-blob determined by `a, c, d`, it contributes to the frequency of unrooted gene quartets with topology `ab|cd`. Otherwise, `a, b` enter that blob
  as exchangeable lineages", and "Any coalescence below the blob containing the LSA leads to gene trees `ab|cd`. If no such coalescence occurs, then upon entering the blob containing the LSA the lineages from `a, b` are exchangeable": `nmscCF_alternatives_at`. So `theorem1_cut`.
* "if the cut edges in `𝒩⁺` are given a sufficiently large length, `CF_{ab|cd}` can be made as close to 1 as desired": `nmscCF_lt_nmscCF_of_splitOffAt`, at `f`, of length 3.
* "`CF_abcd` is an analytic function of parameters": `isGenericNull_nmscCF_eq`. So `theorem1_a`.

**Departure from the paper: what the case split carries.** The paper gives two arguments, on the two kinds of rooted form; in Lean they are one, as its "are similar" suggests. `nmscCF_alternatives_at` asks only that `f` dominates the cherry and has the other two taxa not below it: the lineages arriving at `source f` are the cherry's two, whatever is above `source f`. The paper's two arguments differ only in the name of the blob containing `source f`, and nothing in them uses what the blob is. So the rooted form selects `f` and locates its source, which is proved, and has no further content here. The location is not used by what follows.
-/

@[expose] public noncomputable section

open Phylogenetics Phylogenetics.RootedNetwork Phylogenetics.NMSC
open scoped Classical

namespace AllmanEtAl2023

variable {V E X : Type*} {N : RootedNetwork V E X}

/-! ### From `T_rd(𝒩⁻)` to cut edges -/

section Topology

variable [Fintype X] [DecidableEq X]

/-- On four taxa, a quartet tree is displayed on the tree of blobs exactly when it is a cut-edge split. -/
theorem inducedCutSplit_iff_displays (hN : N.IsPhylogenetic) (hcard : Fintype.card X = 4) (s : QuartetTree X) :
    InducedCutSplit N s ↔ Displays (treeOfBlobs N) s := by
  have hst : s.taxa = Finset.univ := Finset.eq_univ_of_card _ (s.card_taxa.trans hcard.symm)
  refine ⟨fun h => ?_, inducedCutSplit_of_displays hN⟩
  obtain ⟨B, hB, hc⟩ := h
  rw [hst, Finset.coe_univ, ← hasCutSplit_iff_hasCutSplitOn_univ hN] at hc
  have hB2 := s.card_of_mem hB
  have hc2 := s.card_of_mem (s.sdiff_mem hB)
  refine ⟨B, (mem_treeOfBlobs_iff B).mpr ⟨Finset.card_pos.mp (by omega), ?_, hc⟩, ?_⟩
  · rw [hst] at hc2
    have : Finset.univ \ B = Bᶜ := by
      ext x
      simp
    rw [this] at hc2
    exact Finset.card_pos.mp (by omega)
  · rw [hst, Finset.inter_univ]
    exact hB

/-- **`T_rd(𝒩⁻)` has the topology `ab|cd` exactly when `ab|cd` is a cut-edge split.** -/
theorem hasQuartetTopology_iff_inducedCutSplit (hN : IsBinaryNetwork N) (hcard : Fintype.card X = 4) {a b c d : X}
    (h : ({a, b, c, d} : Finset X).card = 4) :
    (Trd hN (nontrivial_of_card_four hcard)).HasQuartetTopology a b c d ↔ InducedCutSplit N (quartetTree a b c d h) := by
  rw [Bridges.hasQuartetTopology_iff_displays hN hcard h, Bridges.splits_Trd, inducedCutSplit_iff_displays hN.isPhylogenetic hcard]

/-- **`T_rd(𝒩⁻)` has the unresolved topology exactly when there is no cut-edge split on the four taxa.** -/
theorem hasStarTopology_iff_not_isTreelike (hN : IsBinaryNetwork N) (hcard : Fintype.card X = 4) {a b c d : X}
    (h : ({a, b, c, d} : Finset X).card = 4) :
    (Trd hN (nontrivial_of_card_four hcard)).HasStarTopology a b c d ↔ ¬ IsTreelike N {a, b, c, d} := by
  rw [Bridges.hasStarTopology_iff_displaysUnresolved hN hcard h, LabelledGraph.DisplaysUnresolved, Bridges.splits_Trd]
  constructor
  · rintro ⟨-, hno⟩ ⟨s, hs, hc⟩
    exact hno s hs ((inducedCutSplit_iff_displays hN.isPhylogenetic hcard s).mp hc)
  · intro hno
    exact ⟨h, fun s hs hd => hno ⟨s, hs, (inducedCutSplit_iff_displays hN.isPhylogenetic hcard s).mpr hd⟩⟩

end Topology

/-! ### The cut edge of a cluster -/

section Cluster

/-- What is below a cut edge of `𝒩⊕`, in `𝒩⁺`: every path to a taxon passes the LSA, and what lies below the LSA is in `𝒩⊕`. -/
theorem separates_of_lsaPlus (hN : IsBinaryNetwork N) (hX : Nontrivial X) {f : N.belowArcs (lsaNode hN hX) Set.univ} {P Q : Set X}
    (hsep : (lsaPlus hN hX).Separates f P Q) : N.Separates f.1 P Q := by
  have hP := hN.isPhylogenetic
  have hst : N.IsStableAncestor Set.univ (lsaNode hN hX) := (lsa_spec hP Set.univ Set.univ_nonempty).1
  have hlift : ∀ {u : N.belowVertices (lsaNode hN hX) Set.univ} {w : V}, N.graph.Reaches u.1 w → ∃ hw : w ∈ N.belowVertices (lsaNode hN hX) Set.univ,
      (lsaPlus hN hX).graph.Reaches u ⟨w, hw⟩ := by
    intro u w h
    induction h with
    | refl => exact ⟨u.2, .refl⟩
    | @tail a b _ hab ih =>
      obtain ⟨ha, hr⟩ := ih
      obtain ⟨g, hs, ht⟩ := hab
      have hg : g ∈ N.belowArcs (lsaNode hN hX) Set.univ := by
        refine ⟨hs ▸ ha.1, mem_ancestralVertices_univ hN _⟩
      have hb : b ∈ N.belowVertices (lsaNode hN hX) Set.univ := ⟨ha.1.trans (Relation.ReflTransGen.single ⟨g, hs, ht⟩), mem_ancestralVertices_univ hN _⟩
      exact ⟨hb, hr.tail ⟨⟨g, hg⟩, Subtype.ext hs, Subtype.ext ht⟩⟩
  -- a path avoiding `f` reaches what is below the LSA in `𝒩⊕`
  have key : ∀ w, N.AvoidingReach f.1 N.root w → ∀ hw : w ∈ N.belowVertices (lsaNode hN hX) Set.univ,
      (lsaPlus hN hX).AvoidingReach f (lsaPlus hN hX).root ⟨w, hw⟩ := by
    intro w hw
    induction hw with
    | refl =>
      intro hr
      have : (⟨N.root, hr⟩ : N.belowVertices (lsaNode hN hX) Set.univ) = (lsaPlus hN hX).root :=
        Subtype.ext (eq_of_reaches_of_reaches hP.acyclic (hP.root_reaches _) hr.1)
      rw [this]
      exact .refl
    | @tail a b _ hab ih =>
      obtain ⟨g, hgf, hs, ht⟩ := hab
      intro hb
      by_cases hbl : b = lsaNode hN hX
      · have : (⟨b, hb⟩ : N.belowVertices (lsaNode hN hX) Set.univ) = (lsaPlus hN hX).root := Subtype.ext hbl
        rw [this]
        exact .refl
      · have hg : g ∈ N.belowArcs (lsaNode hN hX) Set.univ := mem_belowArcs_of_target hP hst ⟨b, hb⟩ hbl ht
        have ha : a ∈ N.belowVertices (lsaNode hN hX) Set.univ := ⟨hs ▸ hg.1, mem_ancestralVertices_univ hN _⟩
        exact (ih ha).tail ⟨⟨g, hg⟩, fun he => hgf (congrArg Subtype.val he), Subtype.ext hs, Subtype.ext ht⟩
  refine ⟨fun x hx hav => hsep.1 x hx (key _ hav ((lsaPlus hN hX).leaf x).2), fun x hx hb => hsep.2 x hx ?_⟩
  obtain ⟨_, hr⟩ := hlift (u := (lsaPlus hN hX).graph.target f) hb
  exact hr

/-- The cut edge of a cluster of `T_rd(𝒩⁺)`: an edge of `𝒩⁺` with the cluster below it, each taxon dominated, and the others not below it. It is the edge of the rooted tree itself: an edge of the tree of blobs of `𝒩⊕`
is a cut edge of `𝒩⊕`, and has what it had below it. -/
theorem exists_separates_of_mem_rootedClusters (hN : IsBinaryNetwork N) (hX : Nontrivial X) {A : Set X} (hA : A ∈ rootedClusters (reducedRootedTree hN hX)) :
    ∃ f, N.Separates f A Aᶜ := by
  obtain ⟨-, e, rfl⟩ := hA
  have hM := lsaPlus_isPhylogenetic hN hX
  have hR : (reducedRootedTree hN hX).IsPhylogenetic := blobTree_isPhylogenetic hM
  -- the cut edge in `𝒩⊕`
  obtain ⟨S, hS, ht, hs⟩ := DirectedMultigraph.exists_oriented_cut e.1.2
  obtain ⟨T, hT⟩ := (lsaPlus hN hX).graph.exists_quotient_set_of_singleton_cut e.1.1 S hS
  have hTc : ∀ f, (lsaPlus hN hX).graph.bridgeQuotient.Crosses f T ↔ f = e.1 := by
    apply ((lsaPlus hN hX).graph.singleton_cut_preimage_iff e.1 T).mp
    rw [hT]
    exact hS
  -- in the rooted tree: the suppressed vertices keep the side
  have hTR : ∀ f, (reducedRootedTree hN hX).graph.Crosses f (Subtype.val ⁻¹' T) ↔ f = e := fun g => by
    refine (crosses_chain_iff (bridgeQuotientData_isPhylogenetic hM) hTc (f := g.1)).trans ⟨fun h => ?_, ?_⟩
    · exact Subtype.ext (h.unique (Or.inl rfl) g.2 e.2)
    · rintro rfl
      exact Or.inl rfl
  have hsT : (reducedRootedTree hN hX).graph.source e ∉ Subtype.val ⁻¹' T := fun h => by
    have : Quotient.mk (lsaPlus hN hX).graph.blobSetoid ((lsaPlus hN hX).graph.source e.1.1) ∈ T := h
    exact hs (hT ▸ this)
  have htT : (reducedRootedTree hN hX).graph.target e ∈ Subtype.val ⁻¹' T := by
    rcases (hTR e).mpr rfl with ⟨h, -⟩ | ⟨h, -⟩
    · exact absurd h hsT
    · exact h
  have hbelow : ∀ x, (reducedRootedTree hN hX).IsBelow e x ↔ (lsaPlus hN hX).leaf x ∈ S := fun x => by
    rw [← mem_side_iff_isBelow hR hTR htT hsT x, ← hT]
    exact Iff.rfl
  -- so in `𝒩⊕` the arc separates
  have hd : (lsaPlus hN hX).Separates e.1.1 {x | (reducedRootedTree hN hX).IsBelow e x} {x | (reducedRootedTree hN hX).IsBelow e x}ᶜ := by
    obtain ⟨y, hy⟩ := exists_reaches_leaf hM ((lsaPlus hN hX).graph.target e.1.1)
    obtain ⟨-, h₁, h₂⟩ := separates_of_crossing (Y := Set.univ) hM (e := e.1.1) ⟨y, Set.mem_univ y, hy⟩ (fun g _ hgf hc => hgf ((hS g).mp hc)) ht hs
    refine ⟨fun x hx => h₁ x (Set.mem_univ x) ((hbelow x).mp hx), fun x hx => h₂ x (Set.mem_univ x) fun hxS => hx ((hbelow x).mpr hxS)⟩
  exact ⟨_, separates_of_lsaPlus hN hX hd⟩

end Cluster

/-! ### The exchangeability argument, on an edge -/

section Exchange

open Finset

variable [Fintype V] [Fintype E] [Fintype X] [DecidableEq X] {θ : MetricData E} {ρ : ℝ}

omit [Fintype V] [Fintype E] [Fintype X] [DecidableEq X] in
theorem eq_of_mem_of_card_two {α : Type*} [DecidableEq α] {S : Finset α} (hS : #S = 2)
    {a b c : α} (ha : a ∈ S) (hb : b ∈ S) (hc : c ∈ S) (hab : a ≠ b) (hca : c ≠ a) : c = b := by
  obtain ⟨u, v, -, rfl⟩ := card_eq_two.1 hS
  simp only [mem_insert, mem_singleton] at ha hb hc
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> rcases hc with rfl | rfl <;>
    first
    | rfl
    | exact absurd rfl hab
    | exact absurd rfl hca

/-- **The analysis at an edge `e` dominating the cherry `P`**, the other cherry not being below it. This is a copy of the private `cut_alternatives_aux` of the library's `NMSC/Exchangeability.lean`, kept here while the library isn't edited: its public `cut_alternatives` takes a cut-edge split and picks its own arc, so it can't be given the paper's edge.

If the two lineages of `P` have coalesced at the top of `e`, the mass of each alternative is `0`: "it contributes to the frequency of unrooted gene quartets with topology `ab|cd`". Otherwise the forest at the top of `e` is the two lineages of `P`, and swapping them fixes what is injected at `source e`, and exchanges the alternatives: they "enter that blob as exchangeable lineages". -/
theorem cherryMass_alternatives_at (hN : N.IsPhylogenetic) (hθ : N.IsMetric θ)
    (hρ : 0 ≤ ρ ∧ ρ ≤ 1) (s : QuartetTree X) {P : Finset X} (hP : P ∈ s.val) {e : E}
    (hd : ∀ x ∈ P, N.Dominates e x) (hn : ∀ x ∈ s.taxa, x ∉ P → ¬ N.IsBelow e x)
    {r r' : QuartetTree X} (hr : r ∈ s.alternatives) (hr' : r' ∈ s.alternatives) :
    cherryMass N θ ρ (taxaInj N s.taxa) r = cherryMass N θ ρ (taxaInj N s.taxa) r' := by
  have hxP : ∀ x ∈ s.taxa, N.IsBelow e x → x ∈ P := fun x hx hb => by
    by_contra hxP
    exact hn x hx hxP hb
  have hdom : DominatedInj N e (taxaInj N s.taxa) := dominatedInj_taxaInj fun x hx hb =>
    hd x (hxP x hx hb)
  have hv := validInj_taxaInj (N := N) s.taxa
  refine cherryMass_eq_of_lift hN hθ hρ hv hv hdom hdom (fun _ _ => rfl) fun bot top hg => ?_
  have hgood := good_top_of_prod_ne_zero hN hv hg
  have hlinF : ∀ x, x ∈ lineages (top e) ↔ x ∈ s.taxa ∧ N.IsBelow e x := fun x =>
    (lineages_top_of_prod_ne_zero hN hv hdom hg x).trans (exists_mem_below_taxaInj x)
  have hlinP : ∀ x, x ∈ lineages (top e) ↔ x ∈ P := fun x => by
    rw [hlinF]
    exact ⟨fun h => hxP x h.1 h.2, fun h => ⟨s.subset_taxa hP h, (hd x h).isBelow hN⟩⟩
  have hl : ValidInj (liftInj N e (taxaInj N s.taxa) (top e)) :=
    validInj_liftInj hv hgood fun x hx => (exists_mem_below_taxaInj x).2 ((hlinF x).1 hx)
  have hrP : ∀ w ∈ s.alternatives, P ∉ w.val := fun w hw hPw => by
    obtain ⟨hwt, hwne⟩ := QuartetTree.mem_alternatives.1 hw
    exact hwne (QuartetTree.eq_of_taxa_eq_of_mem hwt hPw hP)
  by_cases h2 : ∃ C ∈ top e, #C = 2
  · obtain ⟨C, hC, hC2⟩ := h2
    have hCP : C = P := eq_of_subset_of_card_le
      (fun x hx => (hlinP x).1 (mem_lineages.2 ⟨C, hC, hx⟩)) (by rw [s.card_of_mem hP, hC2])
    subst hCP
    have hmem : C ∈ liftInj N e (taxaInj N s.taxa) (top e) (N.graph.source e) := by
      unfold liftInj
      exact mem_union_right _ (by simpa using hC)
    have hval : ∀ w ∈ s.alternatives,
        cherryMass N θ ρ (liftInj N e (taxaInj N s.taxa) (top e)) w = 0 := fun w hw => by
      have hCw : C ⊆ w.taxa := by
        rw [(QuartetTree.mem_alternatives.1 hw).1]
        exact s.subset_taxa hP
      rw [cherryMass_of_mem hN hθ hρ hl hmem hC2 hCw, ite_eq_right (hrP w hw)]
    rw [hval r hr, hval r' hr']
  · by_cases hrr : r = r'
    · rw [hrr]
    have hF := hgood.eq_singletons h2
    obtain ⟨x, y, hxy, hPxy⟩ := card_eq_two.1 (s.card_of_mem hP)
    have hxP' : x ∈ P := by simp [hPxy]
    have hyP' : y ∈ P := by simp [hPxy]
    set π := Equiv.swap x y with hπ
    have hsym : relabelInj π (liftInj N e (taxaInj N s.taxa) (top e)) =
        liftInj N e (taxaInj N s.taxa) (top e) := by
      refine relabelInj_lift_taxaInj (fun z hz hzb => ?_) ?_
      · have hzP : z ∉ P := fun h => hzb ((hd z h).isBelow hN)
        exact Equiv.swap_apply_of_ne_of_ne (fun h => hzP (h ▸ hxP')) (fun h => hzP (h ▸ hyP'))
      · rw [hF]
        exact relabelFamily_swap_singletons ((hlinP x).2 hxP') ((hlinP y).2 hyP')
    have hmapP : P.map π.symm.toEmbedding = P := by
      rw [hPxy, hπ, Equiv.symm_swap, map_insert, map_singleton]
      simp [pair_comm]
    obtain ⟨hrt, hrne⟩ := QuartetTree.mem_alternatives.1 hr
    have hπr : relabelQuartet π r = r' := by
      have hmem : relabelQuartet π r ∈ s.alternatives := by
        refine QuartetTree.mem_alternatives.2 ⟨?_, fun h => hrP r hr ?_⟩
        · rw [taxa_relabelQuartet, hrt]
          ext z
          rw [mem_map_equiv, hπ, Equiv.symm_swap]
          have hxY := s.subset_taxa hP hxP'
          have hyY := s.subset_taxa hP hyP'
          by_cases hzx : z = x
          · subst hzx
            simp [hxY, hyY]
          by_cases hzy : z = y
          · subst hzy
            simp [hxY, hyY]
          rw [Equiv.swap_apply_of_ne_of_ne hzx hzy]
        · have : P ∈ (relabelQuartet π r).val := h ▸ hP
          have h' := mem_relabelFamily.1 this
          rwa [hmapP] at h'
      have hne : relabelQuartet π r ≠ r := by
        intro h
        obtain ⟨D, hD, hxD⟩ := exists_cherry_mem r (hrt ▸ s.subset_taxa hP hxP')
        have hyD : y ∉ D := fun hyD => hrP r hr (by
          have hsub : P ⊆ D := by
            rw [hPxy]
            intro z hz
            simp only [mem_insert, mem_singleton] at hz
            rcases hz with rfl | rfl <;> assumption
          rwa [eq_of_subset_of_card_le hsub (by rw [r.card_of_mem hD, s.card_of_mem hP])] )
        obtain ⟨p, hpD, hpx⟩ := exists_mem_ne (by rw [r.card_of_mem hD]; omega : 1 < #D) x
        have hpy : p ≠ y := fun hpy => hyD (hpy ▸ hpD)
        have hDm : D.map π.toEmbedding ∈ r.val := by
          have : D.map π.toEmbedding ∈ (relabelQuartet π r).val := mem_image_of_mem _ hD
          rwa [h] at this
        have hne' : D.map π.toEmbedding ≠ D := by
          intro hmapD
          have : y ∈ D.map π.toEmbedding := by
            refine mem_map.2 ⟨x, hxD, ?_⟩
            simp [hπ]
          exact hyD (hmapD ▸ this)
        have hdisj := r.property.2.2 _ hDm D hD hne'
        have hpm : p ∈ D.map π.toEmbedding := by
          refine mem_map.2 ⟨p, hpD, ?_⟩
          simpa [hπ] using Equiv.swap_apply_of_ne_of_ne hpx hpy
        exact disjoint_left.1 hdisj hpm hpD
      exact eq_of_mem_of_card_two s.card_alternatives hr hr' hmem hrr hne
    rw [← hπr]
    conv_rhs => rw [← hsym]
    exact (cherryMass_relabel π _ r).symm

/-- **The paper's two sentences on the edge `e`**: at an edge dominating the cherry `P`, with the other cherry not below it, the two alternatives of `s` have equal concordance factors. -/
theorem nmscCF_alternatives_at (hN : N.IsPhylogenetic) (hθ : N.IsMetric θ) (hρ : 0 ≤ ρ ∧ ρ ≤ 1) (s : QuartetTree X) {P : Finset X} (hP : P ∈ s.val) {e : E}
    (hd : ∀ x ∈ P, N.Dominates e x) (hn : ∀ x ∈ s.taxa, x ∉ P → ¬ N.IsBelow e x) {r r' : QuartetTree X} (hr : r ∈ s.alternatives) (hr' : r' ∈ s.alternatives) :
    nmscCF N θ ρ r = nmscCF N θ ρ r' := by
  rw [nmscCF_eq_cherryMass hN hθ hρ r, nmscCF_eq_cherryMass hN hθ hρ r', (QuartetTree.mem_alternatives.1 hr).1, (QuartetTree.mem_alternatives.1 hr').1]
  exact cherryMass_alternatives_at hN hθ hρ s hP hd hn hr hr'

end Exchange

/-! ### The edge of a rooted form, and where its source is -/

section Edge

/-- A directed path does not leave the side of an arc that points into it. -/
theorem mem_of_reaches_of_side {V' E' : Type*} {G : DirectedMultigraph V' E'} {S : Set V'} {e : E'} (hS : ∀ f, G.Crosses f S ↔ f = e) (hs : G.source e ∉ S) {v w : V'} (h : G.Reaches v w) (hv : v ∈ S) : w ∈ S := by
  induction h with
  | refl => exact hv
  | tail _ hab ih =>
    obtain ⟨g, rfl, rfl⟩ := hab
    by_contra ht
    have hge := (hS g).mp (Or.inl ⟨ih, ht⟩)
    exact hs (hge ▸ ih)

/-- A directed path entering the side of an arc passes the arc. -/
theorem reaches_of_entry {V' E' : Type*} {G : DirectedMultigraph V' E'} {S : Set V'} {e : E'} (hS : ∀ f, G.Crosses f S ↔ f = e) {v w : V'} (h : G.Reaches v w) (hv : v ∉ S) (hw : w ∈ S) :
    G.Reaches v (G.source e) ∧ G.Reaches (G.target e) w := by
  induction h with
  | refl => exact absurd hw hv
  | @tail a b hva hab ih =>
    obtain ⟨g, rfl, rfl⟩ := hab
    by_cases ha : G.source g ∈ S
    · obtain ⟨h₁, h₂⟩ := ih ha
      exact ⟨h₁, h₂.tail ⟨g, rfl, rfl⟩⟩
    · have hge := (hS g).mp (Or.inr ⟨hw, ha⟩)
      subst hge
      exact ⟨hva, .refl⟩

variable {V' E' : Type*} {R : RootedNetwork V' E' X}

/-- In a rooted network that is a tree, a node has at most one arc into it. -/
theorem eq_of_target_eq_of_isTree (hR : R.IsPhylogenetic) (hT : R.graph.IsTree) {k₁ k₂ : E'} (ht : R.graph.target k₁ = R.graph.target k₂) : k₁ = k₂ := by
  by_contra hne
  obtain ⟨S, hS, htS, hsS, -⟩ := exists_side_of_isTree hR hT k₁
  have hs₂ : R.graph.source k₂ ∈ S := by
    by_contra hn
    exact hne ((hS k₂).mp (Or.inr ⟨ht ▸ htS, hn⟩)).symm
  have hroot : R.root ∉ S := fun h => hsS (mem_of_reaches_of_side hS hsS (hR.root_reaches _) h)
  have h₂ := (reaches_of_entry hS (hR.root_reaches _) hroot hs₂).2
  exact hR.acyclic _ (Relation.TransGen.tail' h₂ ⟨k₂, rfl, ht.symm⟩)

/-- No taxon is below both an arc and a sibling of it. -/
theorem not_isBelow_of_sibling (hR : R.IsPhylogenetic) (hT : R.graph.IsTree) {e e₂ : E'} (hne : e₂ ≠ e) (hs : R.graph.source e₂ = R.graph.source e) {x : X} (hx : R.IsBelow e₂ x) : ¬ R.IsBelow e x := by
  obtain ⟨S, hS, -, hsS, hSx⟩ := exists_side_of_isTree hR hT e
  intro hb
  have hs₂ : R.graph.source e₂ ∉ S := hs ▸ hsS
  have ht₂ : R.graph.target e₂ ∉ S := fun h => hne ((hS e₂).mp (Or.inr ⟨h, hs₂⟩))
  have := (reaches_of_entry hS hx ht₂ ((hSx x).mpr hb)).1
  exact hR.acyclic _ (Relation.TransGen.head' ⟨e₂, rfl, rfl⟩ (hs ▸ this))

/-- Below an arc with a sibling, some taxon is below the sibling and not below the arc. -/
theorem exists_isBelow_sibling (hR : R.IsPhylogenetic) (hT : R.graph.IsTree) {e e₂ : E'} (hne : e₂ ≠ e) (hs : R.graph.source e₂ = R.graph.source e) : ∃ x, R.IsBelow e₂ x ∧ ¬ R.IsBelow e x := by
  obtain ⟨x, hx⟩ := exists_reaches_leaf hR (R.graph.target e₂)
  exact ⟨x, hx, not_isBelow_of_sibling hR hT hne hs hx⟩

/-- The taxa below an arc whose source is not the root are a proper subset of those below the arc above it. -/
theorem exists_parent_cluster {W F : Type*} {Q : RootedNetwork W F X} (hQ : Q.IsPhylogenetic) (hT : (Q.suppress hQ).graph.IsTree) (e : {e // ¬ Q.IsChainVertex (Q.graph.source e)})
    (hroot : (Q.suppress hQ).graph.source e ≠ (Q.suppress hQ).root) :
    ∃ g, (Q.suppress hQ).graph.target g = (Q.suppress hQ).graph.source e ∧ (∀ x, (Q.suppress hQ).IsBelow e x → (Q.suppress hQ).IsBelow g x) ∧ ∃ x, (Q.suppress hQ).IsBelow g x ∧ ¬ (Q.suppress hQ).IsBelow e x := by
  have hR : (Q.suppress hQ).IsPhylogenetic := suppress_isPhylogenetic _
  have : Finite {e // ¬ Q.IsChainVertex (Q.graph.source e)} := hR.finite_arcs
  obtain ⟨g, hg⟩ := ((Q.suppress hQ).graph.one_le_indegree_iff _).mp (hR.nonroot_indegree _ hroot)
  have hin : (Q.suppress hQ).graph.indegree ((Q.suppress hQ).graph.source e) = 1 := (DirectedMultigraph.indegree_eq_one_iff _ _).mpr ⟨g, fun k => ⟨fun hk => eq_of_target_eq_of_isTree hR hT (hk.trans hg.symm), fun hk => hk ▸ hg⟩⟩
  -- the source of `e` is not a chain vertex
  obtain ⟨e₂, hne, hs⟩ : ∃ e₂, e₂ ≠ e ∧ (Q.suppress hQ).graph.source e₂ = (Q.suppress hQ).graph.source e := by
    by_contra hno
    push Not at hno
    have hout : (Q.suppress hQ).graph.outdegree ((Q.suppress hQ).graph.source e) = 1 := (DirectedMultigraph.outdegree_eq_one_iff _ _).mpr ⟨e, fun k => ⟨fun hk => by
      by_contra hke
      exact hno k hke hk, fun hk => hk ▸ rfl⟩⟩
    rw [suppress_indegree hQ] at hin
    rw [suppress_outdegree hQ] at hout
    exact ((Q.suppress hQ).graph.source e).2 ⟨hin, hout⟩
  obtain ⟨x, hx₂, hx⟩ := exists_isBelow_sibling hR hT hne hs
  refine ⟨g, hg, fun y hy => ?_, x, ?_, hx⟩
  · exact (Relation.ReflTransGen.single (⟨e, hg.symm, rfl⟩ : (Q.suppress hQ).graph.Adj _ _)).trans hy
  · exact (Relation.ReflTransGen.single (⟨e₂, hs.trans hg.symm, rfl⟩ : (Q.suppress hQ).graph.Adj _ _)).trans hx₂

variable (hN : IsBinaryNetwork N) (hX : Nontrivial X)

/-- **The side of the first or the last arc of an edge of `T_rd(𝒩⁺)`**, in `𝒩⊕`, with exactly the taxa below the edge. The arcs of an edge lie on a chain of 2-blobs of `T(𝒩⊕)`. -/
theorem exists_side_of_chain (e : {e // ¬ (lsaPlus hN hX).bridgeQuotientData.IsChainVertex ((lsaPlus hN hX).bridgeQuotientData.graph.source e)}) {q : (lsaPlus hN hX).graph.BridgeArc}
    (hq : q = e.1 ∨ q = chainLast (bridgeQuotientData_isPhylogenetic (lsaPlus_isPhylogenetic hN hX)) e.1) :
    ∃ S : Set (N.belowVertices (lsaNode hN hX) Set.univ), (∀ g, (lsaPlus hN hX).graph.Crosses g S ↔ g = q.1) ∧ (lsaPlus hN hX).graph.target q.1 ∈ S ∧ (lsaPlus hN hX).graph.source q.1 ∉ S ∧
      ∀ x, (lsaPlus hN hX).leaf x ∈ S ↔ (reducedRootedTree hN hX).IsBelow e x := by
  have hM := lsaPlus_isPhylogenetic hN hX
  have hR : (reducedRootedTree hN hX).IsPhylogenetic := blobTree_isPhylogenetic hM
  have hQ := bridgeQuotientData_isPhylogenetic hM
  obtain ⟨S, hS, ht, hs⟩ := DirectedMultigraph.exists_oriented_cut q.2
  obtain ⟨T, hT⟩ := (lsaPlus hN hX).graph.exists_quotient_set_of_singleton_cut q.1 S hS
  have hTc : ∀ f, (lsaPlus hN hX).graph.bridgeQuotient.Crosses f T ↔ f = q := by
    apply ((lsaPlus hN hX).graph.singleton_cut_preimage_iff q T).mp
    rw [hT]
    exact hS
  have hon : (lsaPlus hN hX).bridgeQuotientData.IsOnChain e.1 q := by
    rcases hq with h | h
    · exact Or.inl h
    · rw [h]
      exact isOnChain_chainLast hQ e.1
  have hTR : ∀ f, (reducedRootedTree hN hX).graph.Crosses f (Subtype.val ⁻¹' T) ↔ f = e := fun g =>
    (crosses_chain_iff hQ hTc (f := g.1)).trans ⟨fun h => Subtype.ext (h.unique hon g.2 e.2), by
      rintro rfl
      exact hon⟩
  have hsrc : Quotient.mk (lsaPlus hN hX).graph.blobSetoid ((lsaPlus hN hX).graph.source q.1) ∉ T := fun h => hs (hT ▸ h)
  have htgt : Quotient.mk (lsaPlus hN hX).graph.blobSetoid ((lsaPlus hN hX).graph.target q.1) ∈ T := by
    have : (lsaPlus hN hX).graph.target q.1 ∈ (Quotient.mk (lsaPlus hN hX).graph.blobSetoid) ⁻¹' T := hT ▸ ht
    exact this
  -- the orientation of the edge
  obtain ⟨hsT, htT⟩ : (reducedRootedTree hN hX).graph.source e ∉ Subtype.val ⁻¹' T ∧ (reducedRootedTree hN hX).graph.target e ∈ Subtype.val ⁻¹' T := by
    rcases hq with rfl | rfl
    · have h₁ : (reducedRootedTree hN hX).graph.source e ∉ Subtype.val ⁻¹' T := hsrc
      refine ⟨h₁, ?_⟩
      rcases (hTR e).mpr rfl with ⟨h, -⟩ | ⟨h, -⟩
      · exact absurd h h₁
      · exact h
    · have h₂ : (reducedRootedTree hN hX).graph.target e ∈ Subtype.val ⁻¹' T := by
        change chainEnd hQ ((lsaPlus hN hX).bridgeQuotientData.graph.target e.1) ∈ T
        rw [← target_chainLast hQ e.1]
        exact htgt
      refine ⟨?_, h₂⟩
      rcases (hTR e).mpr rfl with ⟨-, h⟩ | ⟨-, h⟩
      · exact absurd h₂ h
      · exact h
  refine ⟨S, hS, ht, hs, fun x => ?_⟩
  rw [← mem_side_iff_isBelow hR hTR htT hsT x, ← hT]
  exact Iff.rfl

/-- **The edge of `T_rd(𝒩⁺)` with a given cluster, as an arc of `𝒩⁺`**: its first arc separates the cluster, and its source is in the blob at the source of the edge. -/
theorem separates_first_arc (e : {e // ¬ (lsaPlus hN hX).bridgeQuotientData.IsChainVertex ((lsaPlus hN hX).bridgeQuotientData.graph.source e)}) :
    N.Separates e.1.1.1 {x | (reducedRootedTree hN hX).IsBelow e x} {x | (reducedRootedTree hN hX).IsBelow e x}ᶜ := by
  have hM := lsaPlus_isPhylogenetic hN hX
  obtain ⟨S, hS, ht, hs, hSx⟩ := exists_side_of_chain hN hX e (Or.inl rfl)
  obtain ⟨y, hy⟩ := exists_reaches_leaf hM ((lsaPlus hN hX).graph.target e.1.1)
  obtain ⟨-, h₁, h₂⟩ := separates_of_crossing (Y := Set.univ) hM (e := e.1.1) ⟨y, Set.mem_univ y, hy⟩ (fun g _ hgf hc => hgf ((hS g).mp hc)) ht hs
  exact separates_of_lsaPlus hN hX (f := e.1.1) ⟨fun x hx => h₁ x (Set.mem_univ x) ((hSx x).mpr hx), fun x hx => h₂ x (Set.mem_univ x) fun hxS => hx ((hSx x).mp hxS)⟩

variable {hN hX}

/-- **"The 3-blob determined by `a, c, d`"**, in the form `(((x, y), z), w)`: the edge above the cherry `x, y` has its source in a 3-blob of `𝒩⊕`, determined by `x, z, w`. Its cut edges include that edge, which separates `x` and `z`, and the last arc of the edge above it, which separates `x`, `z` from `w`. Its third cut edge leads to `z`. -/
theorem exists_edge_first [Fintype X] [DecidableEq X] {x y z w : X} (h4 : ({x, y, z, w} : Finset X).card = 4) (hF : rootedClusters (reducedRootedTree hN hX) = {{x, y}, {x, y, z}}) :
    ∃ f : N.belowArcs (lsaNode hN hX) Set.univ, N.Separates f.1 {x, y} {x, y}ᶜ ∧ cutDegree (lsaPlus hN hX).graph (blobOf (lsaPlus hN hX).graph ((lsaPlus hN hX).graph.source f)) = 3 ∧
      IsDeterminedBy (lsaPlus hN hX).graph (lsaPlus hN hX).leaf (blobOf (lsaPlus hN hX).graph ((lsaPlus hN hX).graph.source f)) {x, z, w} := by
  have hM := lsaPlus_isPhylogenetic hN hX
  have hQ := bridgeQuotientData_isPhylogenetic hM
  have hR : (reducedRootedTree hN hX).IsPhylogenetic := blobTree_isPhylogenetic hM
  have hT : (reducedRootedTree hN hX).graph.IsTree := blobTree_isTree hM
  obtain ⟨hxy, hxz, hxw, hyz, hyw, hzw⟩ := ne_of_card_four h4
  have hmem₂ : ({x, y} : Set X) ∈ rootedClusters (reducedRootedTree hN hX) := by
    rw [hF]
    simp
  have hmem₃ : ({x, y, z} : Set X) ∈ rootedClusters (reducedRootedTree hN hX) := by
    rw [hF]
    simp
  obtain ⟨-, e, he⟩ := hmem₂
  obtain ⟨-, g₀, hg₀⟩ := hmem₃
  have hbe : ∀ t, (reducedRootedTree hN hX).IsBelow e t ↔ t = x ∨ t = y := fun t => by
    have := Set.ext_iff.mp he t
    simpa using this.symm
  have hbg₀ : ∀ t, (reducedRootedTree hN hX).IsBelow g₀ t ↔ t = x ∨ t = y ∨ t = z := fun t => by
    have := Set.ext_iff.mp hg₀ t
    simpa using this.symm
  -- the source of `e` is not the root
  have hne : (reducedRootedTree hN hX).graph.source e ≠ (reducedRootedTree hN hX).root := by
    intro hroot
    obtain ⟨S, hS, -, hsS, hSx⟩ := exists_side_of_isTree hR hT e
    have htg : (reducedRootedTree hN hX).graph.target g₀ ∉ S := fun h => by
      have := (hSx z).mp (mem_of_reaches_of_side hS hsS ((hbg₀ z).mpr (Or.inr (Or.inr rfl))) h)
      rcases (hbe z).mp this with h' | h'
      · exact hxz h'.symm
      · exact hyz h'.symm
    have h₁ := (reaches_of_entry hS ((hbg₀ x).mpr (Or.inl rfl)) htg ((hSx x).mpr ((hbe x).mpr (Or.inl rfl)))).1
    rw [hroot] at h₁
    rcases Relation.ReflTransGen.cases_tail h₁ with h | ⟨c, -, k, -, hk⟩
    · exact target_ne_root hR g₀ h.symm
    · exact target_ne_root hR k hk
  -- the edge above it has the cluster `x, y, z`
  obtain ⟨g, hgt, hsub, t, htg, hte⟩ := exists_parent_cluster hQ hT e hne
  have hclg : {u | (reducedRootedTree hN hX).IsBelow g u} ∈ rootedClusters (reducedRootedTree hN hX) := by
    refine ⟨?_, g, rfl⟩
    have hss : ({x, y} : Set X) ⊆ {u | (reducedRootedTree hN hX).IsBelow g u} := by
      rintro u (rfl | rfl)
      · exact hsub _ ((hbe _).mpr (Or.inl rfl))
      · exact hsub _ ((hbe _).mpr (Or.inr rfl))
    rw [← Set.ncard_pair hxy]
    exact Set.ncard_le_ncard hss (Set.toFinite _)
  have hbg : ∀ u, (reducedRootedTree hN hX).IsBelow g u ↔ u = x ∨ u = y ∨ u = z := by
    rw [hF] at hclg
    rcases hclg with h | h
    · -- it is not the cluster `x, y`
      exfalso
      have htm : t ∈ ({x, y} : Set X) := h ▸ htg
      rcases htm with rfl | rfl
      · exact hte ((hbe _).mpr (Or.inl rfl))
      · exact hte ((hbe _).mpr (Or.inr rfl))
    · intro u
      have := Set.ext_iff.mp (h : {u | (reducedRootedTree hN hX).IsBelow g u} = {x, y, z}) u
      simpa using this
  -- it is a 3-blob: one arc in, the arc `e`, and one more arc out
  have hdeg : cutDegree (lsaPlus hN hX).graph (blobOf (lsaPlus hN hX).graph ((lsaPlus hN hX).graph.source e.1.1)) = 3 := by
    have : Finite {e // ¬ (lsaPlus hN hX).bridgeQuotientData.IsChainVertex ((lsaPlus hN hX).bridgeQuotientData.graph.source e)} := hR.finite_arcs
    have hin : (reducedRootedTree hN hX).graph.indegree ((reducedRootedTree hN hX).graph.source e) = 1 :=
      (DirectedMultigraph.indegree_eq_one_iff _ _).mpr ⟨g, fun k => ⟨fun hk => eq_of_target_eq_of_isTree hR hT (hk.trans hgt.symm), fun hk => hk ▸ hgt⟩⟩
    -- another arc out has `z` below it
    have hz : ∀ k, k ≠ e → (reducedRootedTree hN hX).graph.source k = (reducedRootedTree hN hX).graph.source e → (reducedRootedTree hN hX).IsBelow k z := by
      intro k hke hks
      obtain ⟨u, hu⟩ := exists_reaches_leaf hR ((reducedRootedTree hN hX).graph.target k)
      have hug : (reducedRootedTree hN hX).IsBelow g u :=
        (Relation.ReflTransGen.single (⟨k, hks.trans hgt.symm, rfl⟩ : (reducedRootedTree hN hX).graph.Adj _ _)).trans hu
      have hne' := not_isBelow_of_sibling hR hT hke hks hu
      rcases (hbg u).mp hug with rfl | rfl | rfl
      · exact absurd ((hbe _).mpr (Or.inl rfl)) hne'
      · exact absurd ((hbe _).mpr (Or.inr rfl)) hne'
      · exact hu
    have hout : (reducedRootedTree hN hX).graph.outdegree ((reducedRootedTree hN hX).graph.source e) ≤ 2 := by
      by_contra hgt2
      push Not at hgt2
      obtain ⟨p, q, r, hp, hq, hr, hpq, hpr, hqr⟩ := (Set.two_lt_ncard_iff (Set.toFinite _)).mp hgt2
      have key : ∀ {k₁ k₂}, k₁ ≠ k₂ → k₁ ≠ e → k₂ ≠ e → (reducedRootedTree hN hX).graph.source k₁ = (reducedRootedTree hN hX).graph.source e → (reducedRootedTree hN hX).graph.source k₂ = (reducedRootedTree hN hX).graph.source e → False := fun h₁₂ h₁ h₂ hs₁ hs₂ =>
        not_isBelow_of_sibling hR hT h₁₂ (hs₁.trans hs₂.symm) (hz _ h₁ hs₁) (hz _ h₂ hs₂)
      by_cases hpe : p = e
      · exact key hqr (fun h => hpq (hpe.trans h.symm)) (fun h => hpr (hpe.trans h.symm)) hq hr
      · by_cases hqe : q = e
        · exact key hpr hpe (fun h => hqr (hqe.trans h.symm)) hp hr
        · exact key hpq hpe hqe hp hq
    have h0 : (reducedRootedTree hN hX).graph.outdegree ((reducedRootedTree hN hX).graph.source e) ≠ 0 := fun h =>
      (DirectedMultigraph.outdegree_eq_zero_iff _ _).mp h e rfl
    have hchain := ((reducedRootedTree hN hX).graph.source e).2
    have hin' : (lsaPlus hN hX).bridgeQuotientData.graph.indegree ((reducedRootedTree hN hX).graph.source e).1 = 1 := (suppress_indegree hQ _).symm.trans hin
    have hout' : (lsaPlus hN hX).bridgeQuotientData.graph.outdegree ((reducedRootedTree hN hX).graph.source e).1 = (reducedRootedTree hN hX).graph.outdegree ((reducedRootedTree hN hX).graph.source e) := (suppress_outdegree hQ _).symm
    have hne1 : (reducedRootedTree hN hX).graph.outdegree ((reducedRootedTree hN hX).graph.source e) ≠ 1 := fun h => hchain ⟨hin', hout'.trans h⟩
    have hsum : nodeDegree (lsaPlus hN hX).graph.bridgeQuotient ((reducedRootedTree hN hX).graph.source e).1 = 3 := by
      unfold nodeDegree
      change (lsaPlus hN hX).bridgeQuotientData.graph.indegree _ + (lsaPlus hN hX).bridgeQuotientData.graph.outdegree _ = 3
      rw [hin', hout']
      omega
    have : Finite (N.belowArcs (lsaNode hN hX) Set.univ) := hM.finite_arcs
    exact (nodeDegree_bridgeQuotient _).symm.trans hsum
  -- the two sides
  obtain ⟨S₁, hS₁, ht₁, hs₁, hS₁x⟩ := exists_side_of_chain hN hX e (Or.inl rfl)
  obtain ⟨S₂, hS₂, ht₂, hs₂, hS₂x⟩ := exists_side_of_chain hN hX g (Or.inr rfl)
  have hsepf := separates_first_arc hN hX e
  have hcoe : {t | (reducedRootedTree hN hX).IsBelow e t} = ({x, y} : Set X) := he.symm
  rw [hcoe] at hsepf
  refine ⟨e.1.1, hsepf, hdeg, ?_⟩
  set β := blobOf (lsaPlus hN hX).graph ((lsaPlus hN hX).graph.source e.1.1) with hβ
  have hinc₁ : e.1.1 ∈ incidentCutEdges (lsaPlus hN hX).graph β := by
    refine ⟨e.1.2, Or.inl ⟨rfl, fun h => ?_⟩⟩
    have := (lsaPlus hN hX).graph.mem_iff_of_blobSetoid hS₁ h
    exact hs₁ (this.mp ht₁)
  have hlast : blobOf (lsaPlus hN hX).graph ((lsaPlus hN hX).graph.target (chainLast hQ g.1).1) = β := by
    have h₁ : (lsaPlus hN hX).bridgeQuotientData.graph.target (chainLast hQ g.1) = chainEnd hQ ((lsaPlus hN hX).bridgeQuotientData.graph.target g.1) := target_chainLast hQ g.1
    have h₂ : chainEnd hQ ((lsaPlus hN hX).bridgeQuotientData.graph.target g.1) = (lsaPlus hN hX).bridgeQuotientData.graph.source e.1 := congrArg Subtype.val hgt
    exact h₁.trans h₂
  have hinc₂ : (chainLast hQ g.1).1 ∈ incidentCutEdges (lsaPlus hN hX).graph β := by
    refine ⟨(chainLast hQ g.1).2, Or.inr ⟨hlast, fun h => ?_⟩⟩
    have := (lsaPlus hN hX).graph.mem_iff_of_blobSetoid hS₂ (h.trans hlast.symm)
    exact hs₂ (this.mpr ht₂)
  have hF₁ : ∀ k ∈ (incidentCutEdges (lsaPlus hN hX).graph β)ᶜ, ¬ (lsaPlus hN hX).graph.Crosses k S₁ := fun k hk hc => hk ((hS₁ k).mp hc ▸ hinc₁)
  have hF₂ : ∀ k ∈ (incidentCutEdges (lsaPlus hN hX).graph β)ᶜ, ¬ (lsaPlus hN hX).graph.Crosses k S₂ := fun k hk hc => hk ((hS₂ k).mp hc ▸ hinc₂)
  have hsep₁ : ∀ {u v : X}, (lsaPlus hN hX).leaf u ∈ S₁ → (lsaPlus hN hX).leaf v ∉ S₁ → ¬ (lsaPlus hN hX).graph.Walks (incidentCutEdges (lsaPlus hN hX).graph β)ᶜ ((lsaPlus hN hX).leaf u) ((lsaPlus hN hX).leaf v) := fun hu hv hw =>
    hv (((lsaPlus hN hX).graph.mem_iff_mem_of_walks hF₁ hw).mp hu)
  have hsep₂ : ∀ {u v : X}, (lsaPlus hN hX).leaf u ∈ S₂ → (lsaPlus hN hX).leaf v ∉ S₂ → ¬ (lsaPlus hN hX).graph.Walks (incidentCutEdges (lsaPlus hN hX).graph β)ᶜ ((lsaPlus hN hX).leaf u) ((lsaPlus hN hX).leaf v) := fun hu hv hw =>
    hv (((lsaPlus hN hX).graph.mem_iff_mem_of_walks hF₂ hw).mp hu)
  have hxS₁ : (lsaPlus hN hX).leaf x ∈ S₁ := (hS₁x x).mpr ((hbe x).mpr (Or.inl rfl))
  have hzS₁ : (lsaPlus hN hX).leaf z ∉ S₁ := fun h => by
    rcases (hbe z).mp ((hS₁x z).mp h) with h' | h'
    · exact hxz h'.symm
    · exact hyz h'.symm
  have hxS₂ : (lsaPlus hN hX).leaf x ∈ S₂ := (hS₂x x).mpr ((hbg x).mpr (Or.inl rfl))
  have hzS₂ : (lsaPlus hN hX).leaf z ∈ S₂ := (hS₂x z).mpr ((hbg z).mpr (Or.inr (Or.inr rfl)))
  have hwS₂ : (lsaPlus hN hX).leaf w ∉ S₂ := fun h => by
    rcases (hbg w).mp ((hS₂x w).mp h) with h' | h' | h'
    · exact hxw h'.symm
    · exact hyw h'.symm
    · exact hzw h'.symm
  have hxz' := hsep₁ hxS₁ hzS₁
  have hxw' := hsep₂ hxS₂ hwS₂
  have hzw' := hsep₂ hzS₂ hwS₂
  refine ⟨by rw [Finset.card_eq_three.mpr ⟨x, z, w, hxz, hxw, hzw, rfl⟩], fun s hs t ht hst hw => ?_⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at hs ht
  have hsym := fun {u v : (N.belowVertices (lsaNode hN hX) Set.univ)} (h : (lsaPlus hN hX).graph.Walks (incidentCutEdges (lsaPlus hN hX).graph β)ᶜ u v) => (lsaPlus hN hX).graph.walks_symm h
  rcases hs with rfl | rfl | rfl <;> rcases ht with rfl | rfl | rfl
  · exact hst rfl
  · exact hxz' hw
  · exact hxw' hw
  · exact hxz' (hsym hw)
  · exact hst rfl
  · exact hzw' hw
  · exact hxw' (hsym hw)
  · exact hzw' (hsym hw)
  · exact hst rfl

/-- **"The blob containing the LSA"**, in the forms `((x, y), (z, w))` and `((x, y), z, w)`: with no cluster of three, the edge above the cherry `x, y` leaves the root of `T_rd(𝒩⁺)`, which is the blob of `𝒩⊕` containing the LSA. -/
theorem exists_edge_second {x y : X} (hxy : x ≠ y) (hmem : ({x, y} : Set X) ∈ rootedClusters (reducedRootedTree hN hX)) (hno : ∀ A ∈ rootedClusters (reducedRootedTree hN hX), A.ncard ≤ 2) :
    ∃ f : N.belowArcs (lsaNode hN hX) Set.univ, N.Separates f.1 {x, y} {x, y}ᶜ ∧ blobOf (lsaPlus hN hX).graph ((lsaPlus hN hX).graph.source f) = blobOf (lsaPlus hN hX).graph (lsaPlus hN hX).root := by
  have hM := lsaPlus_isPhylogenetic hN hX
  have hQ := bridgeQuotientData_isPhylogenetic hM
  have hR : (reducedRootedTree hN hX).IsPhylogenetic := blobTree_isPhylogenetic hM
  have : Finite X := hR.finite_taxa
  obtain ⟨-, e, he⟩ := hmem
  have hsepf := separates_first_arc hN hX e
  rw [show {t | (reducedRootedTree hN hX).IsBelow e t} = ({x, y} : Set X) from he.symm] at hsepf
  refine ⟨e.1.1, hsepf, ?_⟩
  by_contra hne
  have hroot : (reducedRootedTree hN hX).graph.source e ≠ (reducedRootedTree hN hX).root := fun h => hne (congrArg Subtype.val h)
  obtain ⟨g, -, hsub, t, htg, hte⟩ := exists_parent_cluster hQ (blobTree_isTree hM) e hroot
  have hss : ({x, y} : Set X) ⊂ {u | (reducedRootedTree hN hX).IsBelow g u} := by
    refine ⟨fun u hu => hsub u ?_, fun h => hte ?_⟩
    · have hu' : u ∈ {t | (reducedRootedTree hN hX).IsBelow e t} := he ▸ hu
      exact hu'
    · have ht₂ : t ∈ {t | (reducedRootedTree hN hX).IsBelow e t} := he ▸ h htg
      exact ht₂
  have h3 : 2 < {u | (reducedRootedTree hN hX).IsBelow g u}.ncard := by
    rw [← Set.ncard_pair hxy]
    exact Set.ncard_lt_ncard hss (Set.toFinite _)
  have := hno _ ⟨h3.le, g, rfl⟩
  omega

end Edge

/-! ### The rooted forms -/

section Forms

variable [Fintype X] [DecidableEq X]

/-- **In each rooted form, the edge the paper argues on, and where its source is.** In `(((a, b), c), d)`, `(((a, b), d), c)`, `(((c, d), a), b)` and `(((c, d), b), a)` it is the edge above the cherry, with its source in a 3-blob, determined by one taxon of the cherry and the other two taxa. In `((a, b), (c, d))`, `((a, b), c, d)` and `((c, d), a, b)` it is the edge above the cherry, with its source in the blob containing the LSA. -/
theorem exists_edge_of_rootedForm (hN : IsBinaryNetwork N) (hcard : Fintype.card X = 4) {a b c d : X} (h : ({a, b, c, d} : Finset X).card = 4)
    (hT : (Trd hN (nontrivial_of_card_four hcard)).HasQuartetTopology a b c d) :
    ∃ f : N.belowArcs (lsaNode hN (nontrivial_of_card_four hcard)) Set.univ, N.SplitOffAt ∅ f.1 (quartetTree a b c d h) ∧
      ((cutDegree (lsaPlus hN (nontrivial_of_card_four hcard)).graph (blobOf (lsaPlus hN (nontrivial_of_card_four hcard)).graph ((lsaPlus hN (nontrivial_of_card_four hcard)).graph.source f)) = 3 ∧
          ∃ t : Finset X, t.card = 3 ∧ IsDeterminedBy (lsaPlus hN (nontrivial_of_card_four hcard)).graph (lsaPlus hN (nontrivial_of_card_four hcard)).leaf (blobOf (lsaPlus hN (nontrivial_of_card_four hcard)).graph ((lsaPlus hN (nontrivial_of_card_four hcard)).graph.source f)) t) ∨
        blobOf (lsaPlus hN (nontrivial_of_card_four hcard)).graph ((lsaPlus hN (nontrivial_of_card_four hcard)).graph.source f) = blobOf (lsaPlus hN (nontrivial_of_card_four hcard)).graph (lsaPlus hN (nontrivial_of_card_four hcard)).root) := by
  obtain ⟨hab, hac, had, hbc, hbd, hcd⟩ := ne_of_card_four h
  have hall := Bridges.forall_eq_of_card_four hcard h
  have hsep : ∀ {f : E} {P : Set X}, N.Separates f P Pᶜ → N.SeparatesOff ∅ f P Pᶜ := separatesOff_empty_iff.mpr
  -- the cherry `a, b`
  have key₁ : ∀ {f : E}, N.Separates f {a, b} {a, b}ᶜ → N.SplitOffAt ∅ f (quartetTree a b c d h) := fun {f} hf => by
    refine ⟨{a, b}, by simp, ?_⟩
    have := hsep hf
    convert this using 2
    · simp
    · ext x
      simp only [quartetTree_taxa, Finset.coe_sdiff, Finset.coe_insert, Finset.coe_singleton, Set.mem_sdiff, Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_compl_iff]
      rcases hall x with rfl | rfl | rfl | rfl <;> simp [hab, hac, had, hbc, hbd, hcd, hab.symm, hac.symm, had.symm, hbc.symm, hbd.symm, hcd.symm]
  -- the cherry `c, d`
  have key₂ : ∀ {f : E}, N.Separates f {c, d} {c, d}ᶜ → N.SplitOffAt ∅ f (quartetTree a b c d h) := fun {f} hf => by
    refine ⟨{c, d}, by simp, ?_⟩
    have := hsep hf
    convert this using 2
    · simp
    · ext x
      simp only [quartetTree_taxa, Finset.coe_sdiff, Finset.coe_insert, Finset.coe_singleton, Set.mem_sdiff, Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_compl_iff]
      rcases hall x with rfl | rfl | rfl | rfl <;> simp [hab, hac, had, hbc, hbd, hcd, hab.symm, hac.symm, had.symm, hbc.symm, hbd.symm, hcd.symm]
  have hthree : ∀ {u v w : X}, u ≠ v → u ≠ w → v ≠ w → ({u, v, w} : Finset X).card = 3 := fun huv huw hvw => Finset.card_eq_three.mpr ⟨_, _, _, huv, huw, hvw, rfl⟩
  have hsize : ∀ {p q : X} {u : Set X}, (u = {p, q}) → u.ncard ≤ 2 := fun {p q u} hu => by
    rw [hu]
    exact (Set.ncard_insert_le p {q}).trans (by simp)
  rcases rootedForms hN hcard hT with hF | hF | hF | hF | hF | hF | hF
  · -- `(((a, b), c), d)`
    obtain ⟨f, hf, h3, hl⟩ := exists_edge_first h hF
    exact ⟨f, key₁ hf, Or.inl ⟨h3, _, hthree hac had hcd, hl⟩⟩
  · -- `(((a, b), d), c)`
    have h' : ({a, b, d, c} : Finset X).card = 4 := TreeMetric.card_four_of_ne hab had hac hbd hbc hcd.symm
    obtain ⟨f, hf, h3, hl⟩ := exists_edge_first h' hF
    exact ⟨f, key₁ hf, Or.inl ⟨h3, _, hthree had hac hcd.symm, hl⟩⟩
  · -- `(((c, d), a), b)`
    have h' : ({c, d, a, b} : Finset X).card = 4 := TreeMetric.card_four_of_ne hcd hac.symm hbc.symm had.symm hbd.symm hab
    obtain ⟨f, hf, h3, hl⟩ := exists_edge_first h' hF
    exact ⟨f, key₂ hf, Or.inl ⟨h3, _, hthree hac.symm hbc.symm hab, hl⟩⟩
  · -- `(((c, d), b), a)`
    have h' : ({c, d, b, a} : Finset X).card = 4 := TreeMetric.card_four_of_ne hcd hbc.symm hac.symm hbd.symm had.symm hab.symm
    obtain ⟨f, hf, h3, hl⟩ := exists_edge_first h' hF
    exact ⟨f, key₂ hf, Or.inl ⟨h3, _, hthree hbc.symm hac.symm hab.symm, hl⟩⟩
  · -- `((a, b), (c, d))`
    obtain ⟨f, hf, hl⟩ := exists_edge_second hab (by rw [hF]; simp) (fun A hA => by
      rw [hF] at hA
      rcases hA with hA | hA
      · exact hsize hA
      · exact hsize hA)
    exact ⟨f, key₁ hf, Or.inr hl⟩
  · -- `((a, b), c, d)`
    obtain ⟨f, hf, hl⟩ := exists_edge_second hab (by rw [hF]; simp) (fun A hA => by
      rw [hF] at hA
      exact hsize hA)
    exact ⟨f, key₁ hf, Or.inr hl⟩
  · -- `((c, d), a, b)`
    obtain ⟨f, hf, hl⟩ := exists_edge_second hcd (by rw [hF]; simp) (fun A hA => by
      rw [hF] at hA
      exact hsize hA)
    exact ⟨f, key₂ hf, Or.inr hl⟩

variable [Fintype V] [Fintype E]

/-- **Theorem 1, (a), "for all parameters"** (`a:claim:thm1-cut`). In the proof of Theorem 1: "Thus `CF` is `(ab|cd)`-cut for all
parameters". Proposition 1 cites "statement 1 of Theorem 1" for this: a loose citation, since statement 1 is generic, though generic parameters are dense and `CF`s are continuous.

The rooted form gives the edge `f` (`exists_edge_of_rootedForm`), and `nmscCF_alternatives_at` is the paper's two sentences on it: "if a gene tree forms under the NMSC by the `a, b` lineages coalescing below" the blob, "it contributes
to the frequency of unrooted gene quartets with topology `ab|cd`. Otherwise, `a, b` enter that blob as exchangeable lineages, and `ac|bd` and `ad|bc` will be equally probable". What the form says of the location of `source f` is not used: see the head of this file. -/
theorem theorem1_cut (hN : IsBinaryNetwork N) (hcard : Fintype.card X = 4) {a b c d : X}
    (h : ({a, b, c, d} : Finset X).card = 4)
    (hT : (Trd hN (nontrivial_of_card_four hcard)).HasQuartetTopology a b c d) {θ : MetricData E}
    (hθ : N.IsMetric θ) : (cfTriple N θ a b c d h).2.1 = (cfTriple N θ a b c d h).2.2 := by
  obtain ⟨f, ⟨P, hP, hd, hn⟩, -⟩ := exists_edge_of_rootedForm hN hcard h hT
  refine nmscCF_alternatives_at (e := f.1) hN.isPhylogenetic hθ ⟨le_rfl, zero_le_one⟩ _ hP (fun x hx => dominatesOff_empty_iff.mp (hd x hx)) (fun x hx hxP hb => hn x (Finset.mem_coe.mpr (Finset.mem_sdiff.mpr ⟨hx, hxP⟩)) (isBelowOff_empty_iff.mpr hb)) ?_ ?_
  · exact QuartetTree.mem_alternatives.mpr ⟨by simp only [quartetTree_taxa]; exact (insert_acbd a b c d).symm, (quartetTree_ne_acbd h).symm⟩
  · exact QuartetTree.mem_alternatives.mpr ⟨by simp only [quartetTree_taxa]; exact (insert_adbc a b c d).symm, (quartetTree_ne_adbc h).symm⟩

/-- **Statement (a) in the proof of Theorem 1** (`a:claim:thm1a`). If `T` has the quartet tree topology `ab|cd`, then `CF_abcd` is
strictly `(ab|cd)`-cut, for generic parameters.

"Moreover, if the cut edges in `𝒩⁺` are given a sufficiently large length, `CF_{ab|cd}` can be made as close to 1 as desired, and hence distinct from the other `CF` entries. Since `CF_abcd` is an analytic function of parameters
and one parameter choice leads to its being strictly `(ab|cd)`-cut, generic ones must as well." -/
theorem theorem1_a (hN : IsBinaryNetwork N) (hcard : Fintype.card X = 4) :
    ForGenericParams N fun θ => ∀ (a b c d : X) (h : ({a, b, c, d} : Finset X).card = 4),
      (Trd hN (nontrivial_of_card_four hcard)).HasQuartetTopology a b c d →
        IsStrictlyCutAtFirst (cfTriple N θ a b c d h) := by
  have hP := hN.isPhylogenetic
  have hone : ∀ (a b c d : X) (h : ({a, b, c, d} : Finset X).card = 4), (Trd hN (nontrivial_of_card_four hcard)).HasQuartetTopology a b c d →
      IsGenericNull N {θ | N.IsMetric θ ∧ nmscCF N θ 0 (quartetTree a c b d (card_acbd h)) = nmscCF N θ 0 (quartetTree a b c d h)} := by
    intro a b c d h hT
    obtain ⟨f, hf, -⟩ := exists_edge_of_rootedForm hN hcard h hT
    refine isGenericNull_nmscCF_eq (isNormalized_deletionMetric hP (isDeletion_empty hP) fun _ => 3)
      (nmscCF_lt_nmscCF_of_splitOffAt hP (isDeletion_empty hP) (fun _ => by norm_num) rfl hf ?_).ne
    exact QuartetTree.mem_alternatives.mpr ⟨by simp only [quartetTree_taxa]; exact (insert_acbd a b c d).symm, (quartetTree_ne_acbd h).symm⟩
  refine (IsGenericNull.iUnion (ι := {p : X × X × X × X // ∃ h : ({p.1, p.2.1, p.2.2.1, p.2.2.2} : Finset X).card = 4,
    (Trd hN (nontrivial_of_card_four hcard)).HasQuartetTopology p.1 p.2.1 p.2.2.1 p.2.2.2}) fun p =>
      hone p.1.1 p.1.2.1 p.1.2.2.1 p.1.2.2.2 p.2.choose p.2.choose_spec).mono ?_
  rintro θ ⟨hθ, hnot⟩
  push Not at hnot
  obtain ⟨a, b, c, d, h, hT, hne⟩ := hnot
  have hcut := theorem1_cut hN hcard h hT hθ
  refine Set.mem_iUnion.mpr ⟨⟨(a, b, c, d), h, hT⟩, hθ, ?_⟩
  by_contra hd
  exact hne ⟨fun h' => hd h'.symm, hcut⟩

end Forms

end AllmanEtAl2023
