module

public import External.AllmanEtAl2023.CycleLemma

/-!
# ECToBlob §4: funnels, the subgraphs `G̃₃`, `G̃₄`, and their cut edges

The objects of the proof of Theorem 4.1 (`notes/paper2026/paper.txt`, lines 588-627), in the paper's
order, on the subgraphs induced on sets of taxa, which keep degree-2 nodes and everything above the LSA
(line 571). All of this is undirected, as in the paper, by the tools of
`External/AllmanEtAl2023/SubgraphBlobs.lean`. The root is used only to know that the induced subgraphs
are connected, and that a funnel has a first node in the subgraph it attaches to.

* `funnel`, `funnelNodes`, `ancestralArcs_insert` (lines 568-571): the funnel of a taxon, and the
  induced subgraph on one more taxon as the one on the others with the funnel attached at their common
  nodes.
* `Induces` (line 564): a cut edge whose removal disconnects the graph into components with given taxon
  sets. `Induces.hasCutSplitOn`, `exists_induces`: the link with `HasCutSplitOn`.
* `quartetCuts` (lines 588-590, 618): the set `E` of cut edges of `G̃₄` inducing `a₁a₂|b₁b₂`.
* `IsTwoBlobs`, `exists_isTwoBlobs`, `IsTwoBlobs.exists_three_cuts`, `IsTwoBlobs.sameBlobIn_of_determines` (line 591):
  the two 3-blobs, on `G̃₄`.
* `IsTwoBlobs.first_blob` (lines 593-595): paths from a taxon lead first to its 3-blob.
* `chain_between`, `IsTwoBlobs.mem_quartetCuts_iff` (lines 596-597): the cut edges between two nodes are linearly
  ordered, and `E` is the set of cut edges between the two 3-blobs.
* `compOff_subset_of_leadsTo`, `sameBlobIn_or_exists_isNextCut`, `exists_blob_of_isNextCut`, `IsTwoBlobs.exists_two_blob`,
  `IsTwoBlobs.exists_two_blob_left`, `IsTwoBlobs.exists_two_blob_right` (lines 596-597): the chains. Each stretch between
  consecutive cut edges is one blob, and a 2-blob on `G̃₄`, in the sense that its other incident cut edges have no taxon of
  the four beyond them.
* `Induces.threeTaxa` (lines 619-620): `G̃₃` also contains the edges in `E`.
* `sideOff`, `exists_sideOff_eq`, `leaf_mem_sideOff` (lines 620-621): the `ã₂`-side and the
  `b̃₁b̃₂`-side of `G̃₃`.
* `attaches_of_mem_quartetCuts`, `mem_quartetCuts_of_attaches` (lines 622-624): a cut edge of `G̃₃`
  remains a cut edge with the funnel of `z` attached exactly when the funnel attaches on its side of
  `ã₂`.
* `quartetCuts_subset_or_subset`, `funnel_attaches_side` (lines 624-625): the minimality of `|E|`
  implies that the funnel of `a₁` can only attach to `G̃₃` on the `ã₂`-side.
* `induces_block` (lines 625-626): the edges in `E` induce `A₁ ∪ {ã₂}|{b̃₁, b̃₂}`.
* `Induces.attach_funnels`, `Induces.attaches` (lines 626-627): "reasoning similarly", which
  `theorem4_1` carries out.

What the paper leaves implicit (E4 of `REPORT.md`) is proved here. The cut edges of `G̃₃` between `ã₂`
and `b̃₁` form a chain (`chain_between`), of which the cut edges remaining after a funnel is
attached form an up-set, which is what makes the minimality of `|E|` usable. And funnels attaching on
opposite sides of an edge of `E` have no node in common (`exists_common_node`), which is what lets all
the funnels be attached at once.
-/

@[expose] public section

open Phylogenetics Phylogenetics.RootedNetwork DirectedMultigraph External.AllmanEtAl2023

namespace ECToBlob

variable {V E X : Type*} {N : RootedNetwork V E X}

/-! ### Funnels -/

/-- **The funnel of the taxon `z`** over the taxa `Z` (line 568): the arcs ancestral to `z` and to no
taxon of `Z`. For `z ∉ Z` this is the funnel of `z` in the network on `Z ∪ {z}`, and for `z ∈ Z` it is
empty. -/
def funnel (N : RootedNetwork V E X) (Z : Set X) (z : X) : Set E :=
  N.ancestralArcs {z} \ N.ancestralArcs Z

/-- The nodes of the funnel. Those in the subgraph induced on `Z` are where the funnel attaches. -/
def funnelNodes (N : RootedNetwork V E X) (Z : Set X) (z : X) : Set V :=
  arcVertices N.graph (funnel N Z z)

section Funnel

variable {Z Z' Y : Set X} {z z' : X} {f : E} {x : V}

/-- **The network as its induced subgraph with a funnel attached** (lines 569-571): the subgraph
induced on `Z ∪ {z}` is the one induced on `Z` together with the funnel of `z`. -/
theorem ancestralArcs_insert (Z : Set X) (z : X) :
    N.ancestralArcs (insert z Z) = N.ancestralArcs Z ∪ funnel N Z z := by
  ext f
  constructor
  · rintro ⟨y, rfl | hy, hr⟩
    · by_cases hf : f ∈ N.ancestralArcs Z
      · exact Or.inl hf
      · exact Or.inr ⟨⟨y, rfl, hr⟩, hf⟩
    · exact Or.inl ⟨y, hy, hr⟩
  · rintro (hf | ⟨⟨y, rfl, hr⟩, -⟩)
    · exact N.ancestralArcs_mono (Set.subset_insert z Z) hf
    · exact ⟨y, Set.mem_insert _ _, hr⟩

/-- More generally, an arc of the subgraph induced on `Y` and not in the one induced on `Z` is in the
funnel of a taxon of `Y`. -/
theorem exists_mem_funnel (hf : f ∈ N.ancestralArcs Y) (hfZ : f ∉ N.ancestralArcs Z) :
    ∃ z ∈ Y, f ∈ funnel N Z z := by
  obtain ⟨z, hz, hr⟩ := hf
  exact ⟨z, hz, ⟨z, rfl, hr⟩, hfZ⟩

theorem funnel_subset_ancestralArcs (hz : z ∈ Y) : funnel N Z z ⊆ N.ancestralArcs Y :=
  fun _ hf => N.ancestralArcs_mono (Set.singleton_subset_iff.mpr hz) hf.1

theorem not_mem_funnelNodes (hz : z ∈ Z) : x ∉ funnelNodes N Z z := by
  rintro ⟨f, hf, -⟩
  exact hf.2 (N.ancestralArcs_mono (Set.singleton_subset_iff.mpr hz) hf.1)

theorem reaches_of_mem_funnel (hf : f ∈ funnel N Z z) :
    N.graph.Reaches (N.graph.target f) (N.leaf z) := by
  obtain ⟨⟨y, rfl, hr⟩, -⟩ := hf
  exact hr

/-- The funnel is connected (line 568): from the head of an arc of the funnel, a directed path to
the taxon stays in the funnel. -/
theorem walks_funnel_target (hf : f ∈ funnel N Z z) :
    N.graph.Walks (funnel N Z z) (N.graph.target f) (N.leaf z) :=
  walks_of_reaches (reaches_of_mem_funnel hf) fun g h1 h2 =>
    ⟨⟨z, rfl, h2⟩, fun hg => hf.2 (N.mem_ancestralVertices_of_reaches (h1.tail ⟨g, rfl, rfl⟩) hg)⟩

theorem walks_funnel_of_mem_funnelNodes (hx : x ∈ funnelNodes N Z z) :
    N.graph.Walks (funnel N Z z) x (N.leaf z) := by
  obtain ⟨f, hf, rfl | rfl⟩ := hx
  · exact Relation.ReflTransGen.head ⟨f, hf, Or.inl ⟨rfl, rfl⟩⟩ (walks_funnel_target hf)
  · exact walks_funnel_target hf

theorem reaches_of_mem_funnelNodes (hx : x ∈ funnelNodes N Z z) :
    N.graph.Reaches x (N.leaf z) := by
  obtain ⟨f, hf, rfl | rfl⟩ := hx
  · exact (reaches_of_mem_funnel hf).head ⟨f, rfl, rfl⟩
  · exact reaches_of_mem_funnel hf

/-- A taxon outside `Z` is a node of its funnel. -/
theorem leaf_mem_funnelNodes (hN : N.IsPhylogenetic) (hz : z ∉ Z) :
    N.leaf z ∈ funnelNodes N Z z := by
  obtain ⟨g, hg, -, -⟩ := exists_leaf_arc hN z
  refine ⟨g, ⟨⟨z, rfl, hg ▸ .refl⟩, ?_⟩, Or.inr hg⟩
  rintro ⟨y, hy, hr⟩
  rw [hg] at hr
  exact hz (hN.leaf_injective (eq_of_leaf_reaches hN hr) ▸ hy)

/-- A path from the root to a node outside the subgraph induced on `Z` leaves it by an arc. -/
theorem exists_arc_entering (hN : N.IsPhylogenetic) (hZ : Z.Nonempty)
    (hx : x ∉ N.ancestralVertices Z) :
    ∃ g, N.graph.source g ∈ N.ancestralVertices Z ∧ N.graph.target g ∉ N.ancestralVertices Z ∧
      N.graph.Reaches (N.graph.target g) x := by
  have key : ∀ v, N.graph.Reaches N.root v → v ∉ N.ancestralVertices Z →
      ∃ g, N.graph.source g ∈ N.ancestralVertices Z ∧ N.graph.target g ∉ N.ancestralVertices Z ∧
        N.graph.Reaches (N.graph.target g) v := by
    intro v hv
    induction hv with
    | refl => exact fun h => absurd (N.root_mem_ancestralVertices hZ hN.root_reaches) h
    | @tail a c _ hac ih =>
      obtain ⟨f, rfl, rfl⟩ := hac
      intro hc
      by_cases ha : N.graph.source f ∈ N.ancestralVertices Z
      · exact ⟨f, ha, hc, .refl⟩
      · obtain ⟨g, h1, h2, h3⟩ := ih ha
        exact ⟨g, h1, h2, h3.tail ⟨f, rfl, rfl⟩⟩
  exact key x (hN.root_reaches x) hx

/-- **Two funnels sharing a node share a node of attachment** (E4). Above a common node outside the
subgraph on `Z`, the arc entering it from that subgraph is ancestral to both taxa, so it is in both
funnels. -/
theorem exists_common_node (hN : N.IsPhylogenetic) (hZ : Z.Nonempty) (h : x ∈ funnelNodes N Z z)
    (h' : x ∈ funnelNodes N Z z') :
    ∃ y ∈ N.ancestralVertices Z, y ∈ funnelNodes N Z z ∧ y ∈ funnelNodes N Z z' := by
  by_cases hx : x ∈ N.ancestralVertices Z
  · exact ⟨x, hx, h, h'⟩
  · obtain ⟨g, h1, h2, h3⟩ := exists_arc_entering hN hZ hx
    have mem : ∀ {t : X}, x ∈ funnelNodes N Z t → g ∈ funnel N Z t := fun hx' =>
      ⟨⟨_, rfl, h3.trans (reaches_of_mem_funnelNodes hx')⟩, h2⟩
    exact ⟨_, h1, ⟨g, mem h, Or.inl rfl⟩, ⟨g, mem h', Or.inl rfl⟩⟩

end Funnel

/-! ### Cut edges inducing a split -/

/-- **`e` is a cut edge of `F` inducing `P|Q`** (line 564): "a cut edge `e` whose removal disconnects
the graph into connected components with taxon sets `A` and `B`". -/
structure Induces (N : RootedNetwork V E X) (F : Set E) (e : E) (P Q : Set X) : Prop where
  cut : IsCutIn N.graph F e
  left : ∀ x ∈ P, ∀ y ∈ P, N.graph.Walks (F \ {e}) (N.leaf x) (N.leaf y)
  right : ∀ x ∈ Q, ∀ y ∈ Q, N.graph.Walks (F \ {e}) (N.leaf x) (N.leaf y)
  sep : ∀ x ∈ P, ∀ y ∈ Q, ¬ N.graph.Walks (F \ {e}) (N.leaf x) (N.leaf y)

section Induces

variable {Y Z P Q P' Q' : Set X} {F : Set E} {e : E} {z p q : X} {x : V}

theorem Induces.symm (h : Induces N F e P Q) : Induces N F e Q P :=
  ⟨h.cut, h.right, h.left, fun x hx y hy hw => h.sep y hy x hx (N.graph.walks_symm hw)⟩

theorem Induces.ne (h : Induces N F e P Q) (hp : p ∈ P) (hq : q ∈ Q) : p ≠ q := by
  rintro rfl
  exact h.sep p hp p hq .refl

/-- An arc of the subgraph induced on `Y`, the only one of its arcs crossing `T`, induces the split
that `T` gives. -/
theorem induces_of_onlyCrosses (hN : N.IsPhylogenetic) {T : Set V} (he : e ∈ N.ancestralArcs Y)
    (hT : OnlyCrosses N.graph (N.ancestralArcs Y) e T) (hc : N.graph.Crosses e T)
    (hP : ∀ x ∈ P, x ∈ Y ∧ N.leaf x ∈ T) (hQ : ∀ x ∈ Q, x ∈ Y ∧ N.leaf x ∉ T) :
    Induces N (N.ancestralArcs Y) e P Q := by
  have hs : N.graph.source e ∈ N.ancestralVertices Y := N.source_mem_ancestralVertices he
  have ht : N.graph.target e ∈ N.ancestralVertices Y := he
  obtain ⟨u, w, hu, hw, huT, hwT⟩ : ∃ u w, u ∈ N.ancestralVertices Y ∧ w ∈ N.ancestralVertices Y ∧
      u ∉ T ∧ w ∈ T := by
    rcases hc with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨_, _, ht, hs, h2, h1⟩
    · exact ⟨_, _, hs, ht, h2, h1⟩
  have hleaf : ∀ {a : X}, a ∈ Y → N.leaf a ∈ N.ancestralVertices Y :=
    fun ha => N.leaf_mem_ancestralVertices ha
  refine ⟨hT.isCutIn he hc, fun x hx y hy => ?_, fun x hx y hy => ?_, fun x hx y hy hw => ?_⟩
  · exact walks_diff_of_mem_side hT huT (walks_ancestral hN hu (hleaf (hP x hx).1))
      (walks_ancestral hN hu (hleaf (hP y hy).1)) (hP x hx).2 (hP y hy).2
  · exact walks_diff_of_mem_side hT.compl (not_not.mpr hwT) (walks_ancestral hN hw (hleaf (hQ x hx).1))
      (walks_ancestral hN hw (hleaf (hQ y hy).1)) (hQ x hx).2 (hQ y hy).2
  · exact (hQ y hy).2 ((hT.mem_iff_of_walks_diff hw).mp (hP x hx).2)

/-- A cut-edge split of the subgraph induced on `Y` is given by a cut edge inducing it. -/
theorem exists_induces (hN : N.IsPhylogenetic) {A : Set X} (h : N.HasCutSplitOn Y A)
    (hP : ∀ x ∈ P, x ∈ Y ∧ x ∈ A) (hQ : ∀ x ∈ Q, x ∈ Y ∧ x ∉ A) :
    ∃ e, Induces N (N.ancestralArcs Y) e P Q := by
  obtain ⟨e, he, S, hS, hA⟩ := h
  refine ⟨e, induces_of_onlyCrosses hN he (fun f hf hc => (hS f hf).mp hc) ((hS e he).mpr rfl)
    (fun x hx => ⟨(hP x hx).1, (hA x (hP x hx).1).mpr (hP x hx).2⟩)
    (fun x hx => ⟨(hQ x hx).1, fun hxS => (hQ x hx).2 ((hA x (hQ x hx).1).mp hxS)⟩)⟩

/-- A cut edge inducing a split gives a cut-edge split. -/
theorem Induces.hasCutSplitOn (hN : N.IsPhylogenetic) (h : Induces N (N.ancestralArcs Y) e P Q)
    (hY : ∀ x ∈ Y, x ∈ P ∨ x ∈ Q) (hPY : P ⊆ Y) (hQY : Q ⊆ Y) (hp : p ∈ P) (hq : q ∈ Q) :
    N.HasCutSplitOn Y P := by
  have hT : OnlyCrosses N.graph (N.ancestralArcs Y) e
      (compOff N.graph (N.ancestralArcs Y) e (N.leaf p)) := onlyCrosses_compOff
  have hqT : N.leaf q ∉ compOff N.graph (N.ancestralArcs Y) e (N.leaf p) := h.sep p hp q hq
  have hc : N.graph.Crosses e (compOff N.graph (N.ancestralArcs Y) e (N.leaf p)) := by
    obtain ⟨-, a, b, hl, ha, hb⟩ := exists_links_of_walks hT hqT
      (walks_ancestral hN (N.leaf_mem_ancestralVertices (hQY hq))
        (N.leaf_mem_ancestralVertices (hPY hp))) (Relation.ReflTransGen.refl)
    exact hl.crosses ha hb
  refine ⟨e, h.cut.1, _, fun f hf => ⟨hT f hf, ?_⟩, fun x hx => ⟨fun hxT => ?_, h.left p hp x⟩⟩
  · rintro rfl
    exact hc
  · exact (hY x hx).resolve_right fun hxQ => h.sep p hp x hxQ hxT

/-- **Restriction of a cut edge to a smaller set of taxa**, with both sides nonempty: the arc is in
the smaller subgraph, by connectivity, and is a cut edge there inducing the restricted split. -/
theorem Induces.restrict (hN : N.IsPhylogenetic) (h : Induces N (N.ancestralArcs Y) e P Q)
    (hZY : Z ⊆ Y) (hP : P' ⊆ P) (hQ : Q' ⊆ Q) (hPZ : P' ⊆ Z) (hQZ : Q' ⊆ Z) (hp : p ∈ P')
    (hq : q ∈ Q') : Induces N (N.ancestralArcs Z) e P' Q' := by
  have hsub : N.ancestralArcs Z ⊆ N.ancestralArcs Y := N.ancestralArcs_mono hZY
  have hleaf : ∀ {a : X}, a ∈ Z → N.leaf a ∈ N.ancestralVertices Z :=
    fun ha => N.leaf_mem_ancestralVertices ha
  have hconn : ∀ {a b : X}, a ∈ Z → b ∈ Z → N.graph.Walks (N.ancestralArcs Z) (N.leaf a) (N.leaf b) :=
    fun ha hb => walks_ancestral hN (hleaf ha) (hleaf hb)
  have he : e ∈ N.ancestralArcs Z := by
    by_contra hn
    have hsub' : N.ancestralArcs Z ⊆ N.ancestralArcs Y \ {e} := fun f hf => ⟨hsub hf, by
      rintro rfl
      exact hn hf⟩
    exact h.sep p (hP hp) q (hQ hq) (walks_mono hsub' (hconn (hPZ hp) (hQZ hq)))
  have hsep : ∀ x ∈ P', ∀ y ∈ Q', ¬ N.graph.Walks (N.ancestralArcs Z \ {e}) (N.leaf x) (N.leaf y) :=
    fun x hx y hy hw => h.sep x (hP hx) y (hQ hy) (walks_mono (Set.sdiff_subset_sdiff_left hsub) hw)
  refine ⟨isCutIn_of_subset hsub h.cut he, fun x hx y hy => ?_, fun x hx y hy => ?_, hsep⟩
  · rcases mem_compOff_or_mem_compOff (hconn (hPZ hx) (hPZ hy)) (hconn (hPZ hx) (hQZ hq))
      (hsep x hx q hq) with h1 | h1
    · exact h1
    · exact absurd (N.graph.walks_symm h1) (hsep y hy q hq)
  · rcases mem_compOff_or_mem_compOff (hconn (hQZ hx) (hQZ hy)) (hconn (hQZ hx) (hPZ hp))
      (fun hw => hsep p hp x hx (N.graph.walks_symm hw)) with h1 | h1
    · exact h1
    · exact absurd h1 (hsep p hp y hy)

/-- **Where a funnel attaches.** If `e` induces a split on `Y`, with `z` on the side of `p`, then the
funnel of `z` over the taxa `Z ⊆ Y` attaches to the subgraph induced on `Z` only in the component of
`p`: a node of attachment joined to `q` without `e` would join `q` to `z` without `e`, through the
funnel. -/
theorem Induces.attaches (hN : N.IsPhylogenetic) (h : Induces N (N.ancestralArcs Y) e P Q)
    (hZY : Z ⊆ Y) (hz : z ∈ P) (hzY : z ∈ Y) (hp : p ∈ P) (hpZ : p ∈ Z) (hq : q ∈ Q) (hqZ : q ∈ Z)
    (hxZ : x ∈ N.ancestralVertices Z) (hx : x ∈ funnelNodes N Z z) :
    x ∈ compOff N.graph (N.ancestralArcs Z) e (N.leaf p) := by
  have hr : Induces N (N.ancestralArcs Z) e {p} {q} :=
    h.restrict hN hZY (Set.singleton_subset_iff.mpr hp) (Set.singleton_subset_iff.mpr hq)
      (Set.singleton_subset_iff.mpr hpZ) (Set.singleton_subset_iff.mpr hqZ) rfl rfl
  have hpV := N.leaf_mem_ancestralVertices hpZ
  have hqV := N.leaf_mem_ancestralVertices hqZ
  rcases mem_compOff_or_mem_compOff (walks_ancestral hN hpV hxZ) (walks_ancestral hN hpV hqV)
    (hr.sep p rfl q rfl) with h1 | h1
  · exact h1
  · exfalso
    have hsub : N.ancestralArcs Z \ {e} ⊆ N.ancestralArcs Y \ {e} :=
      Set.sdiff_subset_sdiff_left (N.ancestralArcs_mono hZY)
    have hfun : funnel N Z z ⊆ N.ancestralArcs Y \ {e} := fun f hf =>
      ⟨funnel_subset_ancestralArcs hzY hf, by
        rintro rfl
        exact hf.2 hr.cut.1⟩
    exact h.sep z hz q hq (N.graph.walks_symm ((walks_mono hsub h1).trans
      (walks_mono hfun (walks_funnel_of_mem_funnelNodes hx))))

/-- **Attaching funnels** (lines 622-627): let `e` be a cut edge of the subgraph induced on `Z`,
inducing `P|Q`. Attach the funnels of the taxa of `P' ⊇ P` and of `Q' ⊇ Q`, those of `P'` only on the
side of `P` and those of `Q'` only on the side of `Q`. Then `e` is a cut edge of the result, inducing
`P'|Q'`. A funnel of `P'` and a funnel of `Q'` have no node in common, which the paper does not say
(E4): by `exists_common_node`, they would have a node of attachment in common. -/
theorem Induces.attach_funnels (hN : N.IsPhylogenetic) (h : Induces N (N.ancestralArcs Z) e P Q)
    (hZ : Z = P ∪ Q) (hY : Y = P' ∪ Q') (hP : P ⊆ P') (hQ : Q ⊆ Q') (hdisj : Disjoint P' Q')
    (hp : p ∈ P) (hq : q ∈ Q)
    (hA : ∀ z ∈ P', ∀ x ∈ N.ancestralVertices Z, x ∈ funnelNodes N Z z →
      x ∈ compOff N.graph (N.ancestralArcs Z) e (N.leaf p))
    (hB : ∀ z ∈ Q', ∀ x ∈ N.ancestralVertices Z, x ∈ funnelNodes N Z z →
      x ∈ compOff N.graph (N.ancestralArcs Z) e (N.leaf q)) :
    Induces N (N.ancestralArcs Y) e P' Q' := by
  have hpZ : p ∈ Z := hZ ▸ Or.inl hp
  have hqZ : q ∈ Z := hZ ▸ Or.inr hq
  have hpV := N.leaf_mem_ancestralVertices hpZ
  have hqV := N.leaf_mem_ancestralVertices hqZ
  have hsep := h.sep p hp q hq
  -- the two sides of `e` after attaching the funnels
  let Sp : Set V := compOff N.graph (N.ancestralArcs Z) e (N.leaf p) ∪ {x | ∃ z ∈ P', x ∈ funnelNodes N Z z}
  let Sq : Set V := compOff N.graph (N.ancestralArcs Z) e (N.leaf q) ∪ {x | ∃ z ∈ Q', x ∈ funnelNodes N Z z}
  have hVp : ∀ {x}, x ∈ compOff N.graph (N.ancestralArcs Z) e (N.leaf p) → x ∈ N.ancestralVertices Z :=
    fun hx => mem_ancestralVertices_of_walks hpV (walks_mono Set.sdiff_subset hx)
  have hVq : ∀ {x}, x ∈ compOff N.graph (N.ancestralArcs Z) e (N.leaf q) → x ∈ N.ancestralVertices Z :=
    fun hx => mem_ancestralVertices_of_walks hqV (walks_mono Set.sdiff_subset hx)
  have hmeet : ∀ {x}, x ∈ compOff N.graph (N.ancestralArcs Z) e (N.leaf p) →
      x ∈ compOff N.graph (N.ancestralArcs Z) e (N.leaf q) → False := fun h1 h2 =>
    hsep (Relation.ReflTransGen.trans h1 (N.graph.walks_symm h2))
  -- the two sides are disjoint
  have hdis : ∀ x, x ∈ Sp → x ∈ Sq → False := by
    rintro x (hx | ⟨z, hz, hx⟩) (hx' | ⟨z', hz', hx'⟩)
    · exact hmeet hx hx'
    · exact hmeet hx (hB z' hz' x (hVp hx) hx')
    · exact hmeet (hA z hz x (hVq hx') hx) hx'
    · obtain ⟨y, hy, h1, h2⟩ := exists_common_node hN ⟨p, hpZ⟩ hx hx'
      exact hmeet (hA z hz y hy h1) (hB z' hz' y hy h2)
  -- on the subgraph induced on `Z`, the side of `p` is its component
  have hkey : ∀ x ∈ N.ancestralVertices Z,
      (x ∈ Sp ↔ x ∈ compOff N.graph (N.ancestralArcs Z) e (N.leaf p)) := fun x hx =>
    ⟨fun hxS => (mem_compOff_or_mem_compOff (walks_ancestral hN hpV hx)
      (walks_ancestral hN hpV hqV) hsep).resolve_right fun hxq => hdis x hxS (Or.inl hxq), Or.inl⟩
  have hO : OnlyCrosses N.graph (N.ancestralArcs Y) e Sp := by
    intro f hf hc
    by_contra hfe
    by_cases hfZ : f ∈ N.ancestralArcs Z
    · -- an arc of the subgraph induced on `Z`
      have hs := N.source_mem_ancestralVertices hfZ
      have hc' : N.graph.Crosses f (compOff N.graph (N.ancestralArcs Z) e (N.leaf p)) := by
        simp only [Crosses] at hc ⊢
        rwa [hkey _ hs, hkey _ hfZ] at hc
      exact hfe (onlyCrosses_compOff f hfZ hc')
    · -- an arc of a funnel
      obtain ⟨z, hz, hfun⟩ := exists_mem_funnel hf hfZ
      rw [hY] at hz
      rcases hz with hz | hz
      · have h1 : N.graph.source f ∈ Sp := Or.inr ⟨z, hz, f, hfun, Or.inl rfl⟩
        have h2 : N.graph.target f ∈ Sp := Or.inr ⟨z, hz, f, hfun, Or.inr rfl⟩
        rcases hc with ⟨-, h'⟩ | ⟨-, h'⟩
        · exact h' h2
        · exact h' h1
      · have h1 : N.graph.source f ∉ Sp := fun h' => hdis _ h' (Or.inr ⟨z, hz, f, hfun, Or.inl rfl⟩)
        have h2 : N.graph.target f ∉ Sp := fun h' => hdis _ h' (Or.inr ⟨z, hz, f, hfun, Or.inr rfl⟩)
        rcases hc with ⟨h', -⟩ | ⟨h', -⟩
        · exact h1 h'
        · exact h2 h'
  have hc : N.graph.Crosses e Sp := by
    obtain ⟨-, a, b, hl, ha, hb⟩ := exists_links_of_walks
      (onlyCrosses_compOff (G := N.graph) (F := N.ancestralArcs Z) (e := e) (v := N.leaf p)) hsep
      (walks_ancestral hN hqV hpV) Relation.ReflTransGen.refl
    have haV : a ∈ N.ancestralVertices Z := by
      rcases hl with ⟨rfl, -⟩ | ⟨-, rfl⟩
      · exact N.source_mem_ancestralVertices h.cut.1
      · exact h.cut.1
    exact hl.crosses (fun ha' => ha ((hkey a haV).mp ha')) (Or.inl hb)
  have hZY : Z ⊆ Y := by
    rw [hZ, hY]
    exact Set.union_subset_union hP hQ
  have hleaf : ∀ {x}, x ∉ Z → x ∈ P' → N.leaf x ∈ Sp := fun hxZ hx =>
    Or.inr ⟨_, hx, leaf_mem_funnelNodes hN hxZ⟩
  refine induces_of_onlyCrosses hN (N.ancestralArcs_mono hZY h.cut.1) hO hc
    (fun x hx => ⟨hY ▸ Or.inl hx, ?_⟩) (fun x hx => ⟨hY ▸ Or.inr hx, fun hxS => ?_⟩)
  · by_cases hxZ : x ∈ Z
    · rw [hZ] at hxZ
      rcases hxZ with hxP | hxQ
      · exact Or.inl (h.left p hp x hxP)
      · exact absurd (hQ hxQ) (Set.disjoint_left.mp hdisj hx)
    · exact hleaf hxZ hx
  · refine hdis _ hxS ?_
    by_cases hxZ : x ∈ Z
    · rw [hZ] at hxZ
      rcases hxZ with hxP | hxQ
      · exact absurd hx (Set.disjoint_left.mp hdisj (hP hxP))
      · exact Or.inl (h.right q hq x hxQ)
    · exact Or.inr ⟨_, hx, leaf_mem_funnelNodes hN hxZ⟩

end Induces

/-! ### The subgraphs `G̃₄`, `G̃₃`, and the set `E` -/

/-- **The subgraph `G̃₄`** (lines 588-590): the rooted subgraph induced on four taxa, "without
suppressing degree-2 nodes or removing anything above the LSA". -/
abbrev G₄ (N : RootedNetwork V E X) (a₁ a₂ b₁ b₂ : X) : Set E := N.ancestralArcs {a₁, a₂, b₁, b₂}

/-- **The subgraph `G̃₃`** (line 619): the subgraph induced on three taxa, in the same way. -/
abbrev G₃ (N : RootedNetwork V E X) (p q r : X) : Set E := N.ancestralArcs {p, q, r}

section QuartetCuts

variable {a₁ a₂ b₁ b₂ : X}

/-- **The set `E`** (line 618) for the taxa `a₁, a₂, b₁, b₂`: the cut edges of the subgraph `G̃₄`
induced on these taxa, without suppressing degree-2 nodes or removing anything above the LSA,
inducing `a₁a₂|b₁b₂`. -/
def quartetCuts (N : RootedNetwork V E X) (a₁ a₂ b₁ b₂ : X) : Set E :=
  {e | Induces N (G₄ N a₁ a₂ b₁ b₂) e {a₁, a₂} {b₁, b₂}}

theorem quartetCuts_comm_left : quartetCuts N a₂ a₁ b₁ b₂ = quartetCuts N a₁ a₂ b₁ b₂ := by
  simp only [quartetCuts, G₄]
  rw [Set.insert_comm a₂ a₁, Set.pair_comm a₂ a₁]

theorem quartetCuts_comm_right : quartetCuts N a₁ a₂ b₂ b₁ = quartetCuts N a₁ a₂ b₁ b₂ := by
  simp only [quartetCuts, G₄]
  rw [Set.pair_comm b₂ b₁]

theorem quartetCuts_swap : quartetCuts N b₁ b₂ a₁ a₂ = quartetCuts N a₁ a₂ b₁ b₂ := by
  have hset : ({b₁, b₂, a₁, a₂} : Set X) = {a₁, a₂, b₁, b₂} := by
    ext x
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    tauto
  ext e
  simp only [quartetCuts, G₄, Set.mem_ofPred_eq, hset]
  exact ⟨Induces.symm, Induces.symm⟩

/-- A cut-edge split of the 4-taxon induced network gives an arc of `E`. -/
theorem exists_mem_quartetCuts (hN : N.IsPhylogenetic) (h₁₁ : a₁ ≠ b₁) (h₁₂ : a₁ ≠ b₂) (h₂₁ : a₂ ≠ b₁)
    (h₂₂ : a₂ ≠ b₂) (h : N.HasCutSplitOn {a₁, a₂, b₁, b₂} {a₁, a₂}) :
    ∃ e, e ∈ quartetCuts N a₁ a₂ b₁ b₂ := by
  refine exists_induces hN h ?_ ?_
  · rintro x (rfl | rfl)
    · simp
    · simp
  · rintro x (rfl | rfl)
    · simp [h₁₁.symm, h₂₁.symm]
    · simp [h₁₂.symm, h₂₂.symm]

end QuartetCuts

/-! ### The two 3-blobs of `G̃₄`, and the chains between them (lines 591-597)

The paper states these for the induced subnetwork. They are stated on `G̃₄`, of which the induced
subnetwork is obtained by removing what lies above the LSA and suppressing degree-2 nodes. The paper's
proof doesn't refer to them afterwards. Neither does `theorem4_1`, except that the linear order of the cut edges
(`chain_between`) is what `quartetCuts_subset_or_subset` needs, on `G̃₃`. The chains themselves are in the section
`Chains` below. -/

section TwoBlobs

variable [DecidableEq X] {Y : Set X} {a₁ a₂ b₁ b₂ : X} {e g : E} {v w x : V}

/-- A blob determined by `a₁, a₂, b₁`, for `e` inducing `a₁a₂|b₁b₂`, is on the side of `a₁` of `e`. -/
theorem mem_compOff_of_determines (h : Induces N (N.ancestralArcs Y) e {a₁, a₂} {b₁, b₂})
    (ha₁ : a₁ ∈ Y) (ha₂ : a₂ ∈ Y) (hN : N.IsPhylogenetic) (hv : v ∈ N.ancestralVertices Y)
    (ha : a₁ ≠ a₂) (hdet : Determines N.graph (N.ancestralArcs Y) v N.leaf {a₁, a₂, b₁}) :
    v ∈ compOff N.graph (N.ancestralArcs Y) e (N.leaf a₁) := by
  by_contra hvT
  refine ha (hdet.eq_of_mem_side onlyCrosses_compOff hvT (by simp) (by simp)
    (walks_ancestral hN hv (N.leaf_mem_ancestralVertices ha₁))
    (walks_ancestral hN hv (N.leaf_mem_ancestralVertices ha₂)) .refl (h.left a₁ (by simp) a₂ (by simp)))

/-- The blob determined by `a₁, a₂, b₁` is determined by `a₁, a₂, b₂`, for `e` inducing `a₁a₂|b₁b₂`.
A side away from the blob with `b₂` and a taxon `a` of `a₁, a₂`, having neither `b₁` nor the other one,
would cross `e`. -/
theorem determines_of_induces (hN : N.IsPhylogenetic) (h : Induces N (N.ancestralArcs Y) e {a₁, a₂} {b₁, b₂})
    (ha₁ : a₁ ∈ Y) (ha₂ : a₂ ∈ Y) (hb₁ : b₁ ∈ Y) (hb₂ : b₂ ∈ Y) (ha : a₁ ≠ a₂)
    (hv : v ∈ N.ancestralVertices Y)
    (hdet : Determines N.graph (N.ancestralArcs Y) v N.leaf {a₁, a₂, b₁}) :
    Determines N.graph (N.ancestralArcs Y) v N.leaf {a₁, a₂, b₂} := by
  have h1b₂ : a₁ ≠ b₂ := h.ne (by simp) (by simp)
  have h2b₂ : a₂ ≠ b₂ := h.ne (by simp) (by simp)
  have h1b₁ : a₁ ≠ b₁ := h.ne (by simp) (by simp)
  have h2b₁ : a₂ ≠ b₁ := h.ne (by simp) (by simp)
  have hleaf : ∀ {t : X}, t ∈ Y → N.leaf t ∈ N.ancestralVertices Y :=
    fun ht => N.leaf_mem_ancestralVertices ht
  have hc : ∀ {u : V}, u ∈ N.ancestralVertices Y → ∀ {t : X}, t ∈ Y →
      N.graph.Walks (N.ancestralArcs Y) u (N.leaf t) := fun hu _ ht => walks_ancestral hN hu (hleaf ht)
  have hO : OnlyCrosses N.graph (N.ancestralArcs Y) e
      (compOff N.graph (N.ancestralArcs Y) e (N.leaf a₁)) := onlyCrosses_compOff
  have hm₁ : N.leaf a₁ ∈ compOff N.graph (N.ancestralArcs Y) e (N.leaf a₁) := .refl
  have hm₂ : N.leaf a₂ ∈ compOff N.graph (N.ancestralArcs Y) e (N.leaf a₁) := h.left a₁ (by simp) a₂ (by simp)
  have hm₃ : N.leaf b₁ ∉ compOff N.graph (N.ancestralArcs Y) e (N.leaf a₁) := h.sep a₁ (by simp) b₁ (by simp)
  have hm₄ : N.leaf b₂ ∉ compOff N.graph (N.ancestralArcs Y) e (N.leaf a₁) := h.sep a₁ (by simp) b₂ (by simp)
  refine determines_of_median ?_ (fun _ _ _ _ hxy => hN.leaf_injective hxy)
    (fun s _ => isPendantIn_leaf hN s _) ?_ ?_
  · rw [Finset.card_insert_of_notMem (by simp [ha, h1b₂]), Finset.card_pair h2b₂]
  · intro s hs
    simp only [Finset.mem_insert, Finset.mem_singleton] at hs
    rcases hs with rfl | rfl | rfl
    · exact hc hv ha₁
    · exact hc hv ha₂
    · exact hc hv hb₂
  · intro f T hT hvT s hs t ht hsT htT
    have hdet' : ∀ {c d : X}, c ∈ ({a₁, a₂, b₁} : Finset X) → d ∈ ({a₁, a₂, b₁} : Finset X) → c ∈ Y →
        d ∈ Y → N.leaf c ∈ T → N.leaf d ∈ T → c = d := fun hc' hd' hcY hdY h1 h2 =>
      hdet.eq_of_mem_side hT hvT hc' hd' (hc hv hcY) (hc hv hdY) h1 h2
    -- `a₁` and `b₂` on a side away from the blob
    have h₁ : N.leaf a₁ ∈ T → N.leaf b₂ ∈ T → False := fun h1T hT₂ =>
      hO.not_crossing hT (hc (hleaf ha₁) ha₂) (hc (hleaf ha₁) hb₂) (hc (hleaf ha₁) hb₁) hm₁ hm₂ hm₄ hm₃ h1T
        (fun h2T => ha (hdet' (by simp) (by simp) ha₁ ha₂ h1T h2T)) hT₂
        (fun hbT => h1b₁ (hdet' (by simp) (by simp) ha₁ hb₁ h1T hbT))
    -- `a₂` and `b₂` on a side away from the blob
    have h₂ : N.leaf a₂ ∈ T → N.leaf b₂ ∈ T → False := fun h2T hT₂ =>
      hO.not_crossing hT (hc (hleaf ha₂) ha₁) (hc (hleaf ha₂) hb₂) (hc (hleaf ha₂) hb₁)
        hm₂ hm₁ hm₄ hm₃ h2T
        (fun h1T => ha (hdet' (by simp) (by simp) ha₁ ha₂ h1T h2T)) hT₂
        (fun hbT => h2b₁ (hdet' (by simp) (by simp) ha₂ hb₁ h2T hbT))
    have h₃ : N.leaf a₁ ∈ T → N.leaf a₂ ∈ T → False := fun h1T h2T =>
      ha (hdet' (by simp) (by simp) ha₁ ha₂ h1T h2T)
    simp only [Finset.mem_insert, Finset.mem_singleton] at hs ht
    rcases hs with rfl | rfl | rfl <;> rcases ht with rfl | rfl | rfl <;>
      first
        | rfl
        | exact (h₁ hsT htT).elim
        | exact (h₁ htT hsT).elim
        | exact (h₂ hsT htT).elim
        | exact (h₂ htT hsT).elim
        | exact (h₃ hsT htT).elim
        | exact (h₃ htT hsT).elim

/-- **The two 3-blobs of `G̃₄`** (line 591), for taxa `a₁, a₂, b₁, b₂` with a cut-edge split
`a₁a₂|b₁b₂`: the blob of `v`, determined by `a₁, a₂` with `b₁` or `b₂`, and the blob of `w`, determined
by `b₁, b₂` with `a₁` or `a₂`. -/
structure IsTwoBlobs (N : RootedNetwork V E X) (a₁ a₂ b₁ b₂ : X) (v w : V) : Prop where
  mem_left : v ∈ N.ancestralVertices {a₁, a₂, b₁, b₂}
  mem_right : w ∈ N.ancestralVertices {a₁, a₂, b₁, b₂}
  left₁ : Determines N.graph (G₄ N a₁ a₂ b₁ b₂) v N.leaf {a₁, a₂, b₁}
  left₂ : Determines N.graph (G₄ N a₁ a₂ b₁ b₂) v N.leaf {a₁, a₂, b₂}
  right₁ : Determines N.graph (G₄ N a₁ a₂ b₁ b₂) w N.leaf {b₁, b₂, a₁}
  right₂ : Determines N.graph (G₄ N a₁ a₂ b₁ b₂) w N.leaf {b₁, b₂, a₂}
  ne : ¬ SameBlobIn N.graph (G₄ N a₁ a₂ b₁ b₂) v w

/-- **"The induced subnetwork has two 3-blobs"** (line 591). -/
theorem exists_isTwoBlobs (hN : N.IsPhylogenetic) (ha : a₁ ≠ a₂) (hb : b₁ ≠ b₂)
    (he : e ∈ quartetCuts N a₁ a₂ b₁ b₂) : ∃ v w, IsTwoBlobs N a₁ a₂ b₁ b₂ v w := by
  have h : Induces N (G₄ N a₁ a₂ b₁ b₂) e {a₁, a₂} {b₁, b₂} := he
  have hset : ({a₁, a₂, b₁, b₂} : Set X) = {b₁, b₂, a₁, a₂} := by
    ext x
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    tauto
  have h' : Induces N (N.ancestralArcs {b₁, b₂, a₁, a₂}) e {b₁, b₂} {a₁, a₂} := by
    rw [← hset]
    exact h.symm
  have ma₁ : a₁ ∈ ({a₁, a₂, b₁, b₂} : Set X) := by simp
  have ma₂ : a₂ ∈ ({a₁, a₂, b₁, b₂} : Set X) := by simp
  have mb₁ : b₁ ∈ ({a₁, a₂, b₁, b₂} : Set X) := by simp
  have mb₂ : b₂ ∈ ({a₁, a₂, b₁, b₂} : Set X) := by simp
  have h1b₁ : a₁ ≠ b₁ := h.ne (by simp) (by simp)
  have h2b₁ : a₂ ≠ b₁ := h.ne (by simp) (by simp)
  have h1b₂ : a₁ ≠ b₂ := h.ne (by simp) (by simp)
  obtain ⟨v, hv, hdv⟩ := exists_determines_three hN ma₁ ma₂ mb₁ ha h1b₁ h2b₁
  obtain ⟨w, hw, hdw⟩ := exists_determines_three hN mb₁ mb₂ ma₁ hb h1b₁.symm h1b₂.symm
  have hdw₂ : Determines N.graph (G₄ N a₁ a₂ b₁ b₂) w N.leaf {b₁, b₂, a₂} := by
    have := determines_of_induces hN h' (v := w) (by simp) (by simp) (by simp) (by simp) hb (hset ▸ hw)
      (hset ▸ hdw)
    rwa [← hset] at this
  refine ⟨v, w, hv, hw, hdv, determines_of_induces hN h ma₁ ma₂ mb₁ mb₂ ha hv hdv, hdw, hdw₂, fun hsame => ?_⟩
  have h₁ := mem_compOff_of_determines h ma₁ ma₂ hN hv ha hdv
  have h₂ := mem_compOff_of_determines h.symm mb₁ mb₂ hN hw hb hdw
  exact h.sep a₁ (by simp) b₁ (by simp) (Relation.ReflTransGen.trans
    (Relation.ReflTransGen.trans h₁ (hsame.walks_diff h.cut)) (N.graph.walks_symm h₂))

/-- **These are the only 3-blobs** (line 591): a node determined by three of the taxa is in one of the
two blobs. So a blob of `G̃₄` other than these two determines no three taxa. The chains of 2-blobs and cut edges of
lines 596-597 are proved in the section `Chains` below, and do not use this. -/
theorem IsTwoBlobs.sameBlobIn_of_determines (hN : N.IsPhylogenetic) (h : IsTwoBlobs N a₁ a₂ b₁ b₂ v w)
    (h4 : ({a₁, a₂, b₁, b₂} : Finset X).card = 4) {S : Finset X}
    (hS : S = {a₁, a₂, b₁} ∨ S = {a₁, a₂, b₂} ∨ S = {b₁, b₂, a₁} ∨ S = {b₁, b₂, a₂})
    (hx : x ∈ N.ancestralVertices {a₁, a₂, b₁, b₂})
    (hdet : Determines N.graph (G₄ N a₁ a₂ b₁ b₂) x N.leaf S) :
    SameBlobIn N.graph (G₄ N a₁ a₂ b₁ b₂) v x ∨
      SameBlobIn N.graph (G₄ N a₁ a₂ b₁ b₂) w x := by
  obtain ⟨h12, h13, h14, h23, h24, h34⟩ := TreeMetric.ne_of_card_four h4
  have hcard : ∀ {r s t : X}, r ≠ s → r ≠ t → s ≠ t → 2 < ({r, s, t} : Finset X).card := by
    intro r s t hrs hrt hst
    rw [Finset.card_insert_of_notMem (by simp [hrs, hrt]), Finset.card_pair hst]
    omega
  have hwalk : ∀ {u : V}, u ∈ N.ancestralVertices {a₁, a₂, b₁, b₂} → ∀ {r s t : X},
      r ∈ ({a₁, a₂, b₁, b₂} : Set X) → s ∈ ({a₁, a₂, b₁, b₂} : Set X) →
      t ∈ ({a₁, a₂, b₁, b₂} : Set X) → ∀ c ∈ ({r, s, t} : Finset X),
      N.graph.Walks (G₄ N a₁ a₂ b₁ b₂) u (N.leaf c) := by
    intro u hu r s t hr hs ht c hc
    simp only [Finset.mem_insert, Finset.mem_singleton] at hc
    rcases hc with rfl | rfl | rfl
    · exact walks_ancestral hN hu (N.leaf_mem_ancestralVertices hr)
    · exact walks_ancestral hN hu (N.leaf_mem_ancestralVertices hs)
    · exact walks_ancestral hN hu (N.leaf_mem_ancestralVertices ht)
  have m₁ : a₁ ∈ ({a₁, a₂, b₁, b₂} : Set X) := by simp
  have m₂ : a₂ ∈ ({a₁, a₂, b₁, b₂} : Set X) := by simp
  have m₃ : b₁ ∈ ({a₁, a₂, b₁, b₂} : Set X) := by simp
  have m₄ : b₂ ∈ ({a₁, a₂, b₁, b₂} : Set X) := by simp
  have hvx := walks_ancestral hN h.mem_left hx
  have hwx := walks_ancestral hN h.mem_right hx
  rcases hS with rfl | rfl | rfl | rfl
  · exact Or.inl (h.left₁.sameBlobIn hdet (hcard h12 h13 h23) (hwalk h.mem_left m₁ m₂ m₃) hvx)
  · exact Or.inl (h.left₂.sameBlobIn hdet (hcard h12 h14 h24) (hwalk h.mem_left m₁ m₂ m₄) hvx)
  · exact Or.inr (h.right₁.sameBlobIn hdet (hcard h34 h13.symm h14.symm) (hwalk h.mem_right m₃ m₄ m₁) hwx)
  · exact Or.inr (h.right₂.sameBlobIn hdet (hcard h34 h23.symm h24.symm) (hwalk h.mem_right m₃ m₄ m₂) hwx)

omit [DecidableEq X] in
/-- **Up-down paths from a taxon lead first to its 3-blob** (lines 593-595), in the generality the four
cases of `IsTwoBlobs.first_blob` need: a walk from `a` to the blob of `w`, not passing through the blob
of `v`, stays beyond the cut edge leading from the blob of `v` to `a`, and that side would have `w` and
exclude `b`, `b'`. -/
theorem not_walks_avoiding_blob (hN : N.IsPhylogenetic) {S₁ S₂ S₃ : Finset X} {a b b' : X}
    (hv : v ∈ N.ancestralVertices Y) (hw : w ∈ N.ancestralVertices Y) (haY : a ∈ Y) (hbY : b ∈ Y)
    (hbY' : b' ∈ Y) (h₁ : Determines N.graph (N.ancestralArcs Y) v N.leaf S₁)
    (h₂ : Determines N.graph (N.ancestralArcs Y) v N.leaf S₂)
    (h₃ : Determines N.graph (N.ancestralArcs Y) w N.leaf S₃) (h3 : 3 ≤ S₁.card)
    (hS₁ : ∀ s ∈ S₁, s ∈ Y) (ha₁ : a ∈ S₁) (hb₁ : b ∈ S₁) (ha₂ : a ∈ S₂) (hb₂ : b' ∈ S₂) (hb₃ : b ∈ S₃)
    (hb₃' : b' ∈ S₃) (hab : a ≠ b) (hab' : a ≠ b') (hbb : b ≠ b')
    (hx : SameBlobIn N.graph (N.ancestralArcs Y) w x) :
    ¬ N.graph.Walks (insideArcs N.graph (N.ancestralArcs Y)
      {y | ¬ SameBlobIn N.graph (N.ancestralArcs Y) v y}) (N.leaf a) x := by
  intro hwalk
  have hc : ∀ {u : V}, u ∈ N.ancestralVertices Y → ∀ {t : X}, t ∈ Y →
      N.graph.Walks (N.ancestralArcs Y) u (N.leaf t) :=
    fun hu _ ht => walks_ancestral hN hu (N.leaf_mem_ancestralVertices ht)
  -- the cut edge leading from the blob of `v` to `a`
  have hnb : ¬ SameBlobIn N.graph (N.ancestralArcs Y) v (N.leaf a) := fun hb =>
    h₁.ne_of_isPendantIn h3 (isPendantIn_leaf hN a _) (fun s hs => hc hv (hS₁ s hs))
      ((isPendantIn_leaf hN a _).eq_of_sameBlobIn hb)
  obtain ⟨g, hg⟩ := (exists_leadsTo (hc hv haY)).resolve_left hnb
  have hO : OnlyCrosses N.graph (N.ancestralArcs Y) g (far N.graph (N.ancestralArcs Y) g v) :=
    onlyCrosses_far
  have hvT : v ∉ far N.graph (N.ancestralArcs Y) g v := not_mem_far_self
  -- the walk stays on that side
  have hxT : x ∈ far N.graph (N.ancestralArcs Y) g v := by
    refine (N.graph.mem_iff_mem_of_walks (fun f hf hcr => ?_) hwalk).mp hg.2
    have hfg := hO f hf.1 hcr
    subst hfg
    obtain ⟨p, q, hl, hb, -⟩ := exists_ends_of_mem_incidentCuts hg.1
    rcases hl with ⟨rfl, -⟩ | ⟨-, rfl⟩
    · exact hf.2.1 hb
    · exact hf.2.2 hb
  have hwT : w ∈ far N.graph (N.ancestralArcs Y) g v := (SameBlobIn.mem_iff hO hx).mpr hxT
  have hbT : N.leaf b ∉ far N.graph (N.ancestralArcs Y) g v := fun h' =>
    hab (h₁.eq_of_mem_side hO hvT ha₁ hb₁ (hc hv haY) (hc hv hbY) hg.2 h')
  have hbT' : N.leaf b' ∉ far N.graph (N.ancestralArcs Y) g v := fun h' =>
    hab' (h₂.eq_of_mem_side hO hvT ha₂ hb₂ (hc hv haY) (hc hv hbY') hg.2 h')
  exact hbb (h₃.eq_of_mem_side hO.compl (not_not.mpr hwT) hb₃ hb₃' (hc hw hbY) (hc hw hbY') hbT hbT')

/-- **"Up-down paths from `ã₁` or `ã₂` to a 3-blob lead to one of these blobs first, while up-down paths
from `b̃₁` or `b̃₂` lead to the other"** (lines 593-595): a walk in `G̃₄` from `a₁` or `a₂` to the blob
of `w` meets the blob of `v`, and one from `b₁` or `b₂` to the blob of `v` meets the blob of `w`. -/
theorem IsTwoBlobs.first_blob (hN : N.IsPhylogenetic) (h : IsTwoBlobs N a₁ a₂ b₁ b₂ v w)
    (h4 : ({a₁, a₂, b₁, b₂} : Finset X).card = 4) :
    (∀ x, SameBlobIn N.graph (G₄ N a₁ a₂ b₁ b₂) w x →
      ¬ N.graph.Walks (insideArcs N.graph (G₄ N a₁ a₂ b₁ b₂)
        {y | ¬ SameBlobIn N.graph (G₄ N a₁ a₂ b₁ b₂) v y}) (N.leaf a₁) x ∧
      ¬ N.graph.Walks (insideArcs N.graph (G₄ N a₁ a₂ b₁ b₂)
        {y | ¬ SameBlobIn N.graph (G₄ N a₁ a₂ b₁ b₂) v y}) (N.leaf a₂) x) ∧
    (∀ x, SameBlobIn N.graph (G₄ N a₁ a₂ b₁ b₂) v x →
      ¬ N.graph.Walks (insideArcs N.graph (G₄ N a₁ a₂ b₁ b₂)
        {y | ¬ SameBlobIn N.graph (G₄ N a₁ a₂ b₁ b₂) w y}) (N.leaf b₁) x ∧
      ¬ N.graph.Walks (insideArcs N.graph (G₄ N a₁ a₂ b₁ b₂)
        {y | ¬ SameBlobIn N.graph (G₄ N a₁ a₂ b₁ b₂) w y}) (N.leaf b₂) x) := by
  obtain ⟨h12, h13, h14, h23, h24, h34⟩ := TreeMetric.ne_of_card_four h4
  have m₁ : a₁ ∈ ({a₁, a₂, b₁, b₂} : Set X) := by simp
  have m₂ : a₂ ∈ ({a₁, a₂, b₁, b₂} : Set X) := by simp
  have m₃ : b₁ ∈ ({a₁, a₂, b₁, b₂} : Set X) := by simp
  have m₄ : b₂ ∈ ({a₁, a₂, b₁, b₂} : Set X) := by simp
  have hcard : ∀ {r s t : X}, r ≠ s → r ≠ t → s ≠ t → 3 ≤ ({r, s, t} : Finset X).card := by
    intro r s t hrs hrt hst
    rw [Finset.card_insert_of_notMem (by simp [hrs, hrt]), Finset.card_pair hst]
  have hsub : ∀ {r s t : X}, r ∈ ({a₁, a₂, b₁, b₂} : Set X) → s ∈ ({a₁, a₂, b₁, b₂} : Set X) →
      t ∈ ({a₁, a₂, b₁, b₂} : Set X) → ∀ c ∈ ({r, s, t} : Finset X), c ∈ ({a₁, a₂, b₁, b₂} : Set X) := by
    intro r s t hr hs ht c hc
    simp only [Finset.mem_insert, Finset.mem_singleton] at hc
    rcases hc with rfl | rfl | rfl <;> assumption
  refine ⟨fun x hx => ⟨?_, ?_⟩, fun x hx => ⟨?_, ?_⟩⟩
  · exact not_walks_avoiding_blob hN h.mem_left h.mem_right m₁ m₃ m₄ h.left₁ h.left₂ h.right₁
      (hcard h12 h13 h23) (hsub m₁ m₂ m₃) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)
      h13 h14 h34 hx
  · exact not_walks_avoiding_blob hN h.mem_left h.mem_right m₂ m₃ m₄ h.left₁ h.left₂ h.right₁
      (hcard h12 h13 h23) (hsub m₁ m₂ m₃) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)
      h23 h24 h34 hx
  · exact not_walks_avoiding_blob hN h.mem_right h.mem_left m₃ m₁ m₂ h.right₁ h.right₂ h.left₁
      (hcard h34 h13.symm h14.symm) (hsub m₃ m₄ m₁) (by simp) (by simp) (by simp) (by simp) (by simp)
      (by simp) h13.symm h23.symm h12 hx
  · exact not_walks_avoiding_blob hN h.mem_right h.mem_left m₄ m₁ m₂ h.right₁ h.right₂ h.left₁
      (hcard h34 h13.symm h14.symm) (hsub m₃ m₄ m₁) (by simp) (by simp) (by simp) (by simp) (by simp)
      (by simp) h14.symm h24.symm h12 hx

omit [DecidableEq X] in
/-- **The order of the chains** (lines 596-597): the cut edges between two nodes of an induced subgraph, as between
a taxon and its closest 3-blob, or between the two 3-blobs, are linearly ordered by their sides. That the stretches
between them are 2-blobs is in the section `Chains` below. -/
theorem chain_between (hN : N.IsPhylogenetic) (hv : v ∈ N.ancestralVertices Y)
    (hw : w ∈ N.ancestralVertices Y) {e' : E}
    (he : ¬ N.graph.Walks (N.ancestralArcs Y \ {e}) v w)
    (he' : ¬ N.graph.Walks (N.ancestralArcs Y \ {e'}) v w) :
    compOff N.graph (N.ancestralArcs Y) e v ⊆ compOff N.graph (N.ancestralArcs Y) e' v ∨
      compOff N.graph (N.ancestralArcs Y) e' v ⊆ compOff N.graph (N.ancestralArcs Y) e v :=
  compOff_subset_or_subset (walks_ancestral hN hv hw) he he'

/-- **`E` is the set of cut edges of the chain connecting the two 3-blobs** (line 597): an arc induces
`a₁a₂|b₁b₂` on `G̃₄` exactly when it separates the two blobs. -/
theorem IsTwoBlobs.mem_quartetCuts_iff (hN : N.IsPhylogenetic) (h : IsTwoBlobs N a₁ a₂ b₁ b₂ v w)
    (h4 : ({a₁, a₂, b₁, b₂} : Finset X).card = 4) :
    g ∈ quartetCuts N a₁ a₂ b₁ b₂ ↔
      ¬ N.graph.Walks (G₄ N a₁ a₂ b₁ b₂ \ {g}) v w := by
  obtain ⟨h12, h13, h14, h23, h24, h34⟩ := TreeMetric.ne_of_card_four h4
  have m₁ : a₁ ∈ ({a₁, a₂, b₁, b₂} : Set X) := by simp
  have m₂ : a₂ ∈ ({a₁, a₂, b₁, b₂} : Set X) := by simp
  have m₃ : b₁ ∈ ({a₁, a₂, b₁, b₂} : Set X) := by simp
  have m₄ : b₂ ∈ ({a₁, a₂, b₁, b₂} : Set X) := by simp
  constructor
  · intro hg hwk
    have hg' : Induces N (G₄ N a₁ a₂ b₁ b₂) g {a₁, a₂} {b₁, b₂} := hg
    have h₁ := mem_compOff_of_determines hg' m₁ m₂ hN h.mem_left h12 h.left₁
    have h₂ := mem_compOff_of_determines hg'.symm m₃ m₄ hN h.mem_right h34 h.right₁
    exact hg'.sep a₁ (by simp) b₁ (by simp) (Relation.ReflTransGen.trans
      (Relation.ReflTransGen.trans h₁ hwk) (N.graph.walks_symm h₂))
  · intro hsep
    have hc : ∀ {u : V}, u ∈ N.ancestralVertices {a₁, a₂, b₁, b₂} → ∀ {t : X},
        t ∈ ({a₁, a₂, b₁, b₂} : Set X) →
        N.graph.Walks (G₄ N a₁ a₂ b₁ b₂) u (N.leaf t) :=
      fun hu _ ht => walks_ancestral hN hu (N.leaf_mem_ancestralVertices ht)
    have hO : OnlyCrosses N.graph (G₄ N a₁ a₂ b₁ b₂) g
        (far N.graph (G₄ N a₁ a₂ b₁ b₂) g v) := onlyCrosses_far
    have hvT : v ∉ far N.graph (G₄ N a₁ a₂ b₁ b₂) g v := not_mem_far_self
    have hwT : w ∈ far N.graph (G₄ N a₁ a₂ b₁ b₂) g v := hsep
    have hv := h.mem_left
    have hw := h.mem_right
    obtain ⟨hgF, p, q, hl, hp, hq⟩ := exists_links_of_walks hO hvT (walks_ancestral hN hv hw) hwT
    have hb₁ : N.leaf b₁ ∈ far N.graph (G₄ N a₁ a₂ b₁ b₂) g v := by
      by_contra hn
      have hb₂ : N.leaf b₂ ∈ far N.graph (G₄ N a₁ a₂ b₁ b₂) g v := by
        by_contra hn'
        exact h34 (h.right₁.eq_of_mem_side hO.compl (not_not.mpr hwT) (by simp) (by simp) (hc hw m₃)
          (hc hw m₄) hn hn')
      have ha₁ : N.leaf a₁ ∈ far N.graph (G₄ N a₁ a₂ b₁ b₂) g v := by
        by_contra hn'
        exact h13.symm (h.right₁.eq_of_mem_side hO.compl (not_not.mpr hwT) (by simp) (by simp) (hc hw m₃)
          (hc hw m₁) hn hn')
      exact h14 (h.left₂.eq_of_mem_side hO hvT (by simp) (by simp) (hc hv m₁) (hc hv m₄) ha₁ hb₂)
    have hb₂ : N.leaf b₂ ∈ far N.graph (G₄ N a₁ a₂ b₁ b₂) g v := by
      by_contra hn
      have ha₁ : N.leaf a₁ ∈ far N.graph (G₄ N a₁ a₂ b₁ b₂) g v := by
        by_contra hn'
        exact h14.symm (h.right₁.eq_of_mem_side hO.compl (not_not.mpr hwT) (by simp) (by simp) (hc hw m₄)
          (hc hw m₁) hn hn')
      exact h13 (h.left₁.eq_of_mem_side hO hvT (by simp) (by simp) (hc hv m₁) (hc hv m₃) ha₁ hb₁)
    have ha₁ : N.leaf a₁ ∉ far N.graph (G₄ N a₁ a₂ b₁ b₂) g v := fun h' =>
      h13 (h.left₁.eq_of_mem_side hO hvT (by simp) (by simp) (hc hv m₁) (hc hv m₃) h' hb₁)
    have ha₂ : N.leaf a₂ ∉ far N.graph (G₄ N a₁ a₂ b₁ b₂) g v := fun h' =>
      h23 (h.left₁.eq_of_mem_side hO hvT (by simp) (by simp) (hc hv m₂) (hc hv m₃) h' hb₁)
    refine Induces.symm (induces_of_onlyCrosses hN hgF hO (hl.crosses hp hq) ?_ ?_)
    · rintro x (rfl | rfl)
      · exact ⟨m₃, hb₁⟩
      · exact ⟨m₄, hb₂⟩
    · rintro x (rfl | rfl)
      · exact ⟨m₁, ha₁⟩
      · exact ⟨m₂, ha₂⟩

end TwoBlobs

/-! ### The chains of 2-blobs and cut edges (lines 596-597)

"The subgraphs between each taxon and its closest 3-blob have the form of a chain of 2-blobs and cut edges, as does the
subgraph connecting the two 3-blobs." The first three theorems are about any connected subgraph and two of its nodes `v`,
`w`: the cut edges between them are linearly ordered (`chain_between`, `compOff_subset_or_subset`), the first is incident to
the blob of `v` (`compOff_subset_of_leadsTo`), after each comes the next one (`sameBlobIn_or_exists_isNextCut`), and two
consecutive ones are incident to one blob, the one towards `v` and the other towards `w`
(`exists_blob_of_isNextCut`). The rest say that on `G̃₄` such a blob is a 2-blob: its other incident cut edges have no
taxon of the four beyond them (`IsTwoBlobs.exists_two_blob`, `IsTwoBlobs.exists_two_blob_left`,
`IsTwoBlobs.exists_two_blob_right`). An incident cut edge with no taxon beyond it does occur on `G̃₄`, and not on the
induced subnetwork of the paper: it is the arc coming down from the root to the LSA, for a chain through the LSA. -/

section Chains

variable {G : DirectedMultigraph V E} {F : Set E} {u v w x p q : V} {e e' g h : E}

/-- An arc separating two joined vertices is a cut edge. -/
theorem isCutIn_of_not_walks (hw : G.Walks F v w) (he : ¬ G.Walks (F \ {e}) v w) : IsCutIn G F e := by
  obtain ⟨heF, p, q, hl, hp, hq⟩ := exists_links_of_walks (onlyCrosses_far (G := G) (F := F) (e := e)
    (v := v)) not_mem_far_self hw he
  exact onlyCrosses_far.isCutIn heF (hl.crosses hp hq)

/-- An arc separating two joined vertices has one end on each side. -/
theorem exists_ends_of_not_walks (hw : G.Walks F v w) (he : ¬ G.Walks (F \ {e}) v w) :
    ∃ p q, Links G e p q ∧ p ∈ compOff G F e v ∧ q ∉ compOff G F e v := by
  obtain ⟨-, p, q, hl, hp, hq⟩ := exists_links_of_walks (onlyCrosses_far (G := G) (F := F) (e := e)
    (v := v)) not_mem_far_self hw he
  exact ⟨p, q, hl, not_not.mp hp, hq⟩

/-- A cut edge with an end in the blob of `x` is incident to that blob. -/
theorem mem_incidentCuts_of_links (hc : IsCutIn G F e) (hl : Links G e p q)
    (hb : SameBlobIn G F x p) : e ∈ incidentCuts G F x := by
  refine ⟨hc, ?_⟩
  rcases hl with ⟨rfl, -⟩ | ⟨-, rfl⟩
  · exact Or.inl hb
  · exact Or.inr hb

/-- The component of a vertex is the component of any of its vertices. -/
theorem compOff_eq_of_mem (hx : x ∈ compOff G F e v) : compOff G F e x = compOff G F e v :=
  Set.Subset.antisymm (fun _ hy => Relation.ReflTransGen.trans hx hy)
    fun _ hy => Relation.ReflTransGen.trans (G.walks_symm hx) hy

/-- **The first cut edge.** The cut edge leading from the blob of `x` towards `w` comes first among the
cut edges separating `x` from `w`. A cut edge `h` nearer to `x` would have both ends of `g` on the side of `x`, since
one end is in the blob of `x`. -/
theorem compOff_subset_of_leadsTo (hg : LeadsTo G F x g w) (hw : G.Walks F x w)
    (hh : ¬ G.Walks (F \ {h}) x w) : compOff G F g x ⊆ compOff G F h x := by
  rcases compOff_subset_or_subset hw hg.2 hh with h₁ | h₁
  · exact h₁
  · by_cases hgh : g = h
    · rw [hgh]
    · exfalso
      obtain ⟨p, q, hl, hb, hq⟩ := exists_ends_of_mem_incidentCuts hg.1
      have hp : p ∈ compOff G F h x := hb.walks_diff (isCutIn_of_not_walks hw hh)
      exact hq (h₁ (hp.tail ⟨g, ⟨hg.1.1.1, hgh⟩, hl⟩))

/-- Beyond a cut edge `e` towards `w`, with end `x`, an arc `g` with an end in the blob of `x` leaves `v` joined to `x`:
the side of `v` of `e`, with `e` itself, avoids `g`. -/
theorem walks_diff_of_mem_incidentCuts (hw : G.Walks F v w) (he : ¬ G.Walks (F \ {e}) v w)
    (hl : Links G e u x) (hu : u ∈ compOff G F e v) (hx : x ∉ compOff G F e v)
    (hg : g ∈ incidentCuts G F x) (hge : g ≠ e) : G.Walks (F \ {g}) v x := by
  have heF : e ∈ F := (isCutIn_of_not_walks hw he).1
  have hvu : G.Walks F v u := walks_mono Set.sdiff_subset hu
  have hux : G.Walks F u x := walks_of_links heF hl
  obtain ⟨p, q, hlg, hbp, -⟩ := exists_ends_of_mem_incidentCuts hg
  have hp : p ∉ compOff G F e v := fun hp =>
    hx ((SameBlobIn.mem_iff onlyCrosses_compOff hbp).mpr hp)
  have hin := walks_insideArcs_of_mem (onlyCrosses_compOff (G := G) (F := F) (e := e) (v := v)) hx
    (G.walks_symm (hvu.trans hux)) (G.walks_symm hux) (Relation.ReflTransGen.refl) hu
  exact (walks_mono (insideArcs_subset_diff hlg hp) hin).tail ⟨e, ⟨heF, hge.symm⟩, hl⟩

/-- **`e'` is the cut edge after `e`** between `v` and `w`, in the order of their sides containing `v`. -/
structure IsNextCut (G : DirectedMultigraph V E) (F : Set E) (v w : V) (e e' : E) : Prop where
  left : ¬ G.Walks (F \ {e}) v w
  right : ¬ G.Walks (F \ {e'}) v w
  lt : compOff G F e v ⊂ compOff G F e' v
  next : ∀ g, ¬ G.Walks (F \ {g}) v w → compOff G F e v ⊂ compOff G F g v →
    compOff G F e' v ⊆ compOff G F g v

theorem IsNextCut.ne (hn : IsNextCut G F v w e e') : e ≠ e' := fun h => hn.lt.ne (by rw [h])

/-- **After each cut edge between `v` and `w`, the chain goes on**: the end `x` of `e` towards `w` is in the blob of `w`,
or the next cut edge is the one leading from the blob of `x` towards `w`. -/
theorem sameBlobIn_or_exists_isNextCut (hw : G.Walks F v w) (he : ¬ G.Walks (F \ {e}) v w)
    (hl : Links G e u x) (hu : u ∈ compOff G F e v) (hx : x ∉ compOff G F e v) :
    SameBlobIn G F x w ∨ ∃ e', LeadsTo G F x e' w ∧ IsNextCut G F v w e e' := by
  have heF : e ∈ F := (isCutIn_of_not_walks hw he).1
  have hvx : G.Walks F v x := (walks_mono Set.sdiff_subset hu).trans (walks_of_links heF hl)
  have hxw : G.Walks F x w := (G.walks_symm hvx).trans hw
  refine (exists_leadsTo hxw).imp_right ?_
  rintro ⟨g, hg⟩
  have hge : g ≠ e := by
    rintro rfl
    exact hg.2 (walks_diff_of_mem_side onlyCrosses_far not_mem_far_self hvx hw hx he)
  have hvg : G.Walks (F \ {g}) v x := walks_diff_of_mem_incidentCuts hw he hl hu hx hg.1 hge
  have hsep : ¬ G.Walks (F \ {g}) v w := fun h => hg.2 ((G.walks_symm hvg).trans h)
  have hlt : compOff G F e v ⊂ compOff G F g v := by
    rcases compOff_subset_or_subset hw he hsep with h₁ | h₁
    · exact ⟨h₁, fun h₂ => hx (h₂ hvg)⟩
    · exact absurd (h₁ hvg) hx
  refine ⟨g, hg, he, hsep, hlt, fun h hh hlth => ?_⟩
  have hx' : x ∈ compOff G F h v := Relation.ReflTransGen.tail (hlth.subset hu)
    ⟨e, ⟨heF, fun heh => hlth.ne (by rw [heh])⟩, hl⟩
  have hxh : ¬ G.Walks (F \ {h}) x w := fun h' => hh (Relation.ReflTransGen.trans hx' h')
  have := compOff_subset_of_leadsTo hg hxw hxh
  rwa [compOff_eq_of_mem hvg, compOff_eq_of_mem hx'] at this

/-- Two cut edges between `v` and `w` with the same side of `v` are one. -/
theorem eq_of_compOff_eq (hw : G.Walks F v w) (he : ¬ G.Walks (F \ {e}) v w)
    (hc : compOff G F e v = compOff G F e' v) : e = e' := by
  by_contra hne
  obtain ⟨p, q, hl, hp, hq⟩ := exists_ends_of_not_walks hw he
  have hp' : p ∈ compOff G F e' v := hc ▸ hp
  exact hq (hc ▸ hp'.tail ⟨e, ⟨(isCutIn_of_not_walks hw he).1, hne⟩, hl⟩)

/-- **Each stretch between consecutive cut edges is one blob**, of which the two are incident cut edges, the one
towards `v` and the other towards `w`. -/
theorem exists_blob_of_isNextCut (hw : G.Walks F v w) (hn : IsNextCut G F v w e e') :
    ∃ x, LeadsTo G F x e v ∧ LeadsTo G F x e' w := by
  obtain ⟨u, x, hl, hu, hx⟩ := exists_ends_of_not_walks hw hn.left
  have heF : e ∈ F := (isCutIn_of_not_walks hw hn.left).1
  have hne : e ≠ e' := hn.ne
  have hxe' : x ∈ compOff G F e' v := Relation.ReflTransGen.tail (hn.lt.subset hu) ⟨e, ⟨heF, hne⟩, hl⟩
  have hexit : ¬ G.Walks (F \ {e'}) x w := fun h => hn.right (Relation.ReflTransGen.trans hxe' h)
  refine ⟨x, ⟨mem_incidentCuts_of_links (isCutIn_of_not_walks hw hn.left) hl.symm .refl, fun h => hx
    (G.walks_symm h)⟩, ?_⟩
  rcases sameBlobIn_or_exists_isNextCut hw hn.left hl hu hx with hb | ⟨g, hg, hng⟩
  · exact absurd (hb.walks_diff (isCutIn_of_not_walks hw hn.right)) hexit
  · have hc : compOff G F g v = compOff G F e' v :=
      Set.Subset.antisymm (hng.next e' hn.right hn.lt) (hn.next g hng.right hng.lt)
    rw [← eq_of_compOff_eq hw hng.right hc]
    exact hg

/-- Vertices of `F` joined to an end of an arc of an induced subgraph are in it. -/
theorem mem_ancestralVertices_of_mem_incidentCuts {Y : Set X} {x : V} {g : E}
    (hg : g ∈ incidentCuts N.graph (N.ancestralArcs Y) x) : x ∈ N.ancestralVertices Y := by
  obtain ⟨p, q, hl, hb, -⟩ := exists_ends_of_mem_incidentCuts hg
  have hg' : g ∈ N.ancestralArcs Y := hg.1.1
  have hp : p ∈ N.ancestralVertices Y := by
    rcases hl with ⟨rfl, -⟩ | ⟨-, rfl⟩
    · exact N.source_mem_ancestralVertices hg'
    · exact hg'
  exact mem_ancestralVertices_of_walks hp (N.graph.walks_symm hb.walks)

variable [DecidableEq X] {a₁ a₂ b₁ b₂ a b t : X} {Y : Set X}

/-- **The blobs between two 3-blobs are 2-blobs** (line 597): a blob of `G̃₄` with distinct incident cut edges `e` towards
`v` and `e'` towards `w` has no other incident cut edge with a taxon of the four beyond it. By
`IsTwoBlobs.mem_quartetCuts_iff`, `e` and `e'` induce `a₁a₂|b₁b₂`, so all four taxa are beyond `e` or `e'`. -/
theorem IsTwoBlobs.eq_or_eq_of_between (hN : N.IsPhylogenetic) (h : IsTwoBlobs N a₁ a₂ b₁ b₂ v w)
    (h4 : ({a₁, a₂, b₁, b₂} : Finset X).card = 4)
    (hl : LeadsTo N.graph (G₄ N a₁ a₂ b₁ b₂) x e v) (hr : LeadsTo N.graph (G₄ N a₁ a₂ b₁ b₂) x e' w)
    (hne : e ≠ e') (hg : g ∈ incidentCuts N.graph (G₄ N a₁ a₂ b₁ b₂) x)
    (ht : t ∈ ({a₁, a₂, b₁, b₂} : Set X)) (htg : N.leaf t ∈ far N.graph (G₄ N a₁ a₂ b₁ b₂) g x) :
    g = e ∨ g = e' := by
  obtain ⟨h12, -, -, -, -, h34⟩ := TreeMetric.ne_of_card_four h4
  have m₁ : a₁ ∈ ({a₁, a₂, b₁, b₂} : Set X) := by simp
  have m₂ : a₂ ∈ ({a₁, a₂, b₁, b₂} : Set X) := by simp
  have m₃ : b₁ ∈ ({a₁, a₂, b₁, b₂} : Set X) := by simp
  have m₄ : b₂ ∈ ({a₁, a₂, b₁, b₂} : Set X) := by simp
  have hx : x ∈ N.ancestralVertices {a₁, a₂, b₁, b₂} := mem_ancestralVertices_of_mem_incidentCuts hg
  have hc : ∀ {y : V}, y ∈ N.ancestralVertices {a₁, a₂, b₁, b₂} →
      N.graph.Walks (G₄ N a₁ a₂ b₁ b₂) x y := fun hy => walks_ancestral hN hx hy
  have hcl : ∀ {t : X}, t ∈ ({a₁, a₂, b₁, b₂} : Set X) →
      N.graph.Walks (G₄ N a₁ a₂ b₁ b₂) x (N.leaf t) := fun ht =>
    hc (N.leaf_mem_ancestralVertices ht)
  -- `e` and `e'` separate the two blobs, so they induce `a₁a₂|b₁b₂`
  have hwe : N.graph.Walks (G₄ N a₁ a₂ b₁ b₂ \ {e}) x w := by
    by_contra hn
    exact hne (LeadsTo.unique ⟨hl.1, hn⟩ hr (hc h.mem_right))
  have hve' : N.graph.Walks (G₄ N a₁ a₂ b₁ b₂ \ {e'}) x v := by
    by_contra hn
    exact hne (LeadsTo.unique hl ⟨hr.1, hn⟩ (hc h.mem_left))
  have hq₁ : Induces N (G₄ N a₁ a₂ b₁ b₂) e {a₁, a₂} {b₁, b₂} :=
    (h.mem_quartetCuts_iff hN h4).mpr fun hvw =>
      hl.2 (hwe.trans (N.graph.walks_symm hvw))
  have hq₂ : Induces N (G₄ N a₁ a₂ b₁ b₂) e' {a₁, a₂} {b₁, b₂} :=
    (h.mem_quartetCuts_iff hN h4).mpr fun hvw => hr.2 (hve'.trans hvw)
  have hv₁ := mem_compOff_of_determines hq₁ m₁ m₂ hN h.mem_left h12 h.left₁
  have hw₁ := mem_compOff_of_determines hq₂.symm m₃ m₄ hN h.mem_right h34 h.right₁
  have far₁ : N.leaf a₁ ∉ compOff N.graph (G₄ N a₁ a₂ b₁ b₂) e x := fun hb =>
    hl.2 (Relation.ReflTransGen.trans hb hv₁)
  have far₂ : N.leaf a₂ ∉ compOff N.graph (G₄ N a₁ a₂ b₁ b₂) e x := fun hb =>
    far₁ (Relation.ReflTransGen.trans hb (hq₁.left a₂ (by simp) a₁ (by simp)))
  have far₃ : N.leaf b₁ ∉ compOff N.graph (G₄ N a₁ a₂ b₁ b₂) e' x := fun hb =>
    hr.2 (Relation.ReflTransGen.trans hb hw₁)
  have far₄ : N.leaf b₂ ∉ compOff N.graph (G₄ N a₁ a₂ b₁ b₂) e' x := fun hb =>
    far₃ (Relation.ReflTransGen.trans hb (hq₂.right b₂ (by simp) b₁ (by simp)))
  have hlead : LeadsTo N.graph (G₄ N a₁ a₂ b₁ b₂) x g (N.leaf t) := ⟨hg, htg⟩
  rcases ht with rfl | rfl | rfl | rfl
  · exact Or.inl (hlead.unique ⟨hl.1, far₁⟩ (hcl m₁))
  · exact Or.inl (hlead.unique ⟨hl.1, far₂⟩ (hcl m₂))
  · exact Or.inr (hlead.unique ⟨hr.1, far₃⟩ (hcl m₃))
  · exact Or.inr (hlead.unique ⟨hr.1, far₄⟩ (hcl m₄))

omit [DecidableEq X] in
/-- A blob between the taxon `a` and a blob of `v` determined with `a` by any other taxon of `Y` has, in the subgraph
induced on `Y`, no other incident cut edge with a taxon of `Y` beyond it. The side of `e'` not containing `v` has `a`, and
so no other taxon. -/
theorem eq_or_eq_of_between_taxon (hN : N.IsPhylogenetic) (hv : v ∈ N.ancestralVertices Y) (ha : a ∈ Y)
    (hdet : ∀ t ∈ Y, t ≠ a → ∃ S : Finset X,
      Determines N.graph (N.ancestralArcs Y) v N.leaf S ∧ a ∈ S ∧ t ∈ S)
    (hl : LeadsTo N.graph (N.ancestralArcs Y) x e (N.leaf a))
    (hr : LeadsTo N.graph (N.ancestralArcs Y) x e' v) (hne : e ≠ e')
    (hg : g ∈ incidentCuts N.graph (N.ancestralArcs Y) x) (ht : t ∈ Y)
    (htg : N.leaf t ∈ far N.graph (N.ancestralArcs Y) g x) : g = e ∨ g = e' := by
  have hx : x ∈ N.ancestralVertices Y := mem_ancestralVertices_of_mem_incidentCuts hg
  have hcl : ∀ {t : X}, t ∈ Y → N.graph.Walks (N.ancestralArcs Y) x (N.leaf t) := fun ht =>
    walks_ancestral hN hx (N.leaf_mem_ancestralVertices ht)
  have hlead : LeadsTo N.graph (N.ancestralArcs Y) x g (N.leaf t) := ⟨hg, htg⟩
  by_cases hta : t = a
  · subst hta
    exact Or.inl (hlead.unique hl (hcl ht))
  · refine Or.inr (hlead.unique ⟨hr.1, fun htT => ?_⟩ (hcl ht))
    have haT : N.leaf a ∈ compOff N.graph (N.ancestralArcs Y) e' x := by
      by_contra hn
      exact hne (LeadsTo.unique hl ⟨hr.1, hn⟩ (hcl ha))
    obtain ⟨S, hS, haS, htS⟩ := hdet t ht hta
    have hvc : ∀ {t : X}, t ∈ Y → N.graph.Walks (N.ancestralArcs Y) v (N.leaf t) := fun ht =>
      walks_ancestral hN hv (N.leaf_mem_ancestralVertices ht)
    exact hta (hS.eq_of_mem_side onlyCrosses_compOff hr.2 htS haS (hvc ht) (hvc ha) htT haT)

/-- The two blobs, seen from `b₁, b₂`. -/
theorem IsTwoBlobs.symm (h : IsTwoBlobs N a₁ a₂ b₁ b₂ v w) : IsTwoBlobs N b₁ b₂ a₁ a₂ w v := by
  have hset : ({b₁, b₂, a₁, a₂} : Set X) = {a₁, a₂, b₁, b₂} := by
    ext x
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    tauto
  have hG : G₄ N b₁ b₂ a₁ a₂ = G₄ N a₁ a₂ b₁ b₂ := by
    simp only [G₄, hset]
  refine ⟨hset ▸ h.mem_right, hset ▸ h.mem_left, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hG]
    exact h.right₁
  · rw [hG]
    exact h.right₂
  · rw [hG]
    exact h.left₁
  · rw [hG]
    exact h.left₂
  · rw [hG]
    exact fun hsame => h.ne hsame.symm

/-- **"Has two 3-blobs"** (line 591), for the blob of `v`: it has exactly three incident cut edges with a taxon of the
four beyond them, those leading to `a₁`, to `a₂`, and to `b₁` and `b₂`. The last is the one leading to the blob of `w`. For
the blob of `w`, apply this to `IsTwoBlobs.symm`. -/
theorem IsTwoBlobs.exists_three_cuts (hN : N.IsPhylogenetic) (h : IsTwoBlobs N a₁ a₂ b₁ b₂ v w)
    (h4 : ({a₁, a₂, b₁, b₂} : Finset X).card = 4) :
    ∃ e₁ e₂ e₃, e₁ ≠ e₂ ∧ e₁ ≠ e₃ ∧ e₂ ≠ e₃ ∧
      LeadsTo N.graph (G₄ N a₁ a₂ b₁ b₂) v e₁ (N.leaf a₁) ∧
      LeadsTo N.graph (G₄ N a₁ a₂ b₁ b₂) v e₂ (N.leaf a₂) ∧
      LeadsTo N.graph (G₄ N a₁ a₂ b₁ b₂) v e₃ (N.leaf b₁) ∧
      LeadsTo N.graph (G₄ N a₁ a₂ b₁ b₂) v e₃ (N.leaf b₂) ∧
      LeadsTo N.graph (G₄ N a₁ a₂ b₁ b₂) v e₃ w ∧
      ∀ g ∈ incidentCuts N.graph (G₄ N a₁ a₂ b₁ b₂) v, ∀ t ∈ ({a₁, a₂, b₁, b₂} : Set X),
        N.leaf t ∈ far N.graph (G₄ N a₁ a₂ b₁ b₂) g v → g = e₁ ∨ g = e₂ ∨ g = e₃ := by
  obtain ⟨h12, h13, -, h23, -, h34⟩ := TreeMetric.ne_of_card_four h4
  have m₁ : a₁ ∈ ({a₁, a₂, b₁, b₂} : Set X) := by simp
  have m₂ : a₂ ∈ ({a₁, a₂, b₁, b₂} : Set X) := by simp
  have m₃ : b₁ ∈ ({a₁, a₂, b₁, b₂} : Set X) := by simp
  have m₄ : b₂ ∈ ({a₁, a₂, b₁, b₂} : Set X) := by simp
  have hcl : ∀ {t : X}, t ∈ ({a₁, a₂, b₁, b₂} : Set X) →
      N.graph.Walks (G₄ N a₁ a₂ b₁ b₂) v (N.leaf t) := fun ht =>
    walks_ancestral hN h.mem_left (N.leaf_mem_ancestralVertices ht)
  have h3 : 3 ≤ ({a₁, a₂, b₁} : Finset X).card := by
    rw [Finset.card_insert_of_notMem (by simp [h12, h13]), Finset.card_pair h23]
  have hS : ∀ s ∈ ({a₁, a₂, b₁} : Finset X), N.graph.Walks (G₄ N a₁ a₂ b₁ b₂) v (N.leaf s) := by
    intro s hs
    simp only [Finset.mem_insert, Finset.mem_singleton] at hs
    rcases hs with rfl | rfl | rfl
    · exact hcl m₁
    · exact hcl m₂
    · exact hcl m₃
  have hnb : ∀ {t : X}, ¬ SameBlobIn N.graph (G₄ N a₁ a₂ b₁ b₂) v (N.leaf t) := fun hb =>
    h.left₁.ne_of_isPendantIn h3 (isPendantIn_leaf hN _ _) hS
      ((isPendantIn_leaf hN _ _).eq_of_sameBlobIn hb)
  obtain ⟨e₁, he₁⟩ := (exists_leadsTo (hcl m₁)).resolve_left hnb
  obtain ⟨e₂, he₂⟩ := (exists_leadsTo (hcl m₂)).resolve_left hnb
  obtain ⟨e₃, he₃⟩ := (exists_leadsTo (walks_ancestral hN h.mem_left h.mem_right)).resolve_left h.ne
  -- `e₃` induces `a₁a₂|b₁b₂`
  have hq : Induces N (G₄ N a₁ a₂ b₁ b₂) e₃ {a₁, a₂} {b₁, b₂} :=
    (h.mem_quartetCuts_iff hN h4).mpr he₃.2
  have hv₁ := mem_compOff_of_determines hq m₁ m₂ hN h.mem_left h12 h.left₁
  have hw₁ := mem_compOff_of_determines hq.symm m₃ m₄ hN h.mem_right h34 h.right₁
  have hfar₃ : N.leaf b₁ ∉ compOff N.graph (G₄ N a₁ a₂ b₁ b₂) e₃ v := fun hb =>
    he₃.2 (Relation.ReflTransGen.trans hb hw₁)
  have hfar₄ : N.leaf b₂ ∉ compOff N.graph (G₄ N a₁ a₂ b₁ b₂) e₃ v := fun hb =>
    hfar₃ (Relation.ReflTransGen.trans hb (hq.right b₂ (by simp) b₁ (by simp)))
  have hnear₁ : N.leaf a₁ ∈ compOff N.graph (G₄ N a₁ a₂ b₁ b₂) e₃ v := N.graph.walks_symm hv₁
  have hnear₂ : N.leaf a₂ ∈ compOff N.graph (G₄ N a₁ a₂ b₁ b₂) e₃ v :=
    Relation.ReflTransGen.trans hnear₁ (hq.left a₁ (by simp) a₂ (by simp))
  have hne₁₃ : e₁ ≠ e₃ := by
    rintro rfl
    exact he₁.2 hnear₁
  have hne₂₃ : e₂ ≠ e₃ := by
    rintro rfl
    exact he₂.2 hnear₂
  have hne₁₂ : e₁ ≠ e₂ := by
    rintro rfl
    exact h12 (h.left₁.eq_of_mem_side onlyCrosses_far not_mem_far_self (s := a₁) (t := a₂) (by simp)
      (by simp) (hcl m₁) (hcl m₂) he₁.2 he₂.2)
  refine ⟨e₁, e₂, e₃, hne₁₂, hne₁₃, hne₂₃, he₁, he₂, ⟨he₃.1, hfar₃⟩, ⟨he₃.1, hfar₄⟩, he₃, ?_⟩
  rintro g hg t ht htg
  have hlead : LeadsTo N.graph (G₄ N a₁ a₂ b₁ b₂) v g (N.leaf t) := ⟨hg, htg⟩
  rcases ht with rfl | rfl | rfl | rfl
  · exact Or.inl (hlead.unique he₁ (hcl m₁))
  · exact Or.inr (Or.inl (hlead.unique he₂ (hcl m₂)))
  · exact Or.inr (Or.inr (hlead.unique ⟨he₃.1, hfar₃⟩ (hcl m₃)))
  · exact Or.inr (Or.inr (hlead.unique ⟨he₃.1, hfar₄⟩ (hcl m₄)))

/-- **The blobs between a taxon and its closest 3-blob are 2-blobs** (line 596), for `a₁` or `a₂` and the blob of `v`. -/
theorem IsTwoBlobs.eq_or_eq_of_between_left (hN : N.IsPhylogenetic) (h : IsTwoBlobs N a₁ a₂ b₁ b₂ v w)
    (ha : a = a₁ ∨ a = a₂) (hl : LeadsTo N.graph (G₄ N a₁ a₂ b₁ b₂) x e (N.leaf a))
    (hr : LeadsTo N.graph (G₄ N a₁ a₂ b₁ b₂) x e' v) (hne : e ≠ e')
    (hg : g ∈ incidentCuts N.graph (G₄ N a₁ a₂ b₁ b₂) x)
    (ht : t ∈ ({a₁, a₂, b₁, b₂} : Set X)) (htg : N.leaf t ∈ far N.graph (G₄ N a₁ a₂ b₁ b₂) g x) :
    g = e ∨ g = e' := by
  refine eq_or_eq_of_between_taxon hN h.mem_left (by rcases ha with rfl | rfl <;> simp) ?_ hl hr hne hg
    ht htg
  intro s hs hsa
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
  by_cases hsb : s = b₂
  · subst hsb
    exact ⟨_, h.left₂, by rcases ha with rfl | rfl <;> simp, by simp⟩
  · refine ⟨_, h.left₁, by rcases ha with rfl | rfl <;> simp, ?_⟩
    simp only [Finset.mem_insert, Finset.mem_singleton]
    tauto

/-- **The blobs between a taxon and its closest 3-blob are 2-blobs** (line 596), for `b₁` or `b₂` and the blob of `w`. -/
theorem IsTwoBlobs.eq_or_eq_of_between_right (hN : N.IsPhylogenetic) (h : IsTwoBlobs N a₁ a₂ b₁ b₂ v w)
    (hb : b = b₁ ∨ b = b₂) (hl : LeadsTo N.graph (G₄ N a₁ a₂ b₁ b₂) x e (N.leaf b))
    (hr : LeadsTo N.graph (G₄ N a₁ a₂ b₁ b₂) x e' w) (hne : e ≠ e')
    (hg : g ∈ incidentCuts N.graph (G₄ N a₁ a₂ b₁ b₂) x)
    (ht : t ∈ ({a₁, a₂, b₁, b₂} : Set X)) (htg : N.leaf t ∈ far N.graph (G₄ N a₁ a₂ b₁ b₂) g x) :
    g = e ∨ g = e' := by
  refine eq_or_eq_of_between_taxon hN h.mem_right (by rcases hb with rfl | rfl <;> simp) ?_ hl hr hne hg
    ht htg
  intro s hs hsb
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
  by_cases hsa : s = a₂
  · subst hsa
    exact ⟨_, h.right₂, by rcases hb with rfl | rfl <;> simp, by simp⟩
  · refine ⟨_, h.right₁, by rcases hb with rfl | rfl <;> simp, ?_⟩
    simp only [Finset.mem_insert, Finset.mem_singleton]
    tauto

/-- **"As does the subgraph connecting the two 3-blobs"** (line 597): two consecutive cut edges between the two blobs are
incident to one blob, which has no other incident cut edge with a taxon of the four beyond it. -/
theorem IsTwoBlobs.exists_two_blob (hN : N.IsPhylogenetic) (h : IsTwoBlobs N a₁ a₂ b₁ b₂ v w)
    (h4 : ({a₁, a₂, b₁, b₂} : Finset X).card = 4)
    (hn : IsNextCut N.graph (G₄ N a₁ a₂ b₁ b₂) v w e e') :
    ∃ x, LeadsTo N.graph (G₄ N a₁ a₂ b₁ b₂) x e v ∧ LeadsTo N.graph (G₄ N a₁ a₂ b₁ b₂) x e' w ∧
      ∀ g ∈ incidentCuts N.graph (G₄ N a₁ a₂ b₁ b₂) x, ∀ t ∈ ({a₁, a₂, b₁, b₂} : Set X),
        N.leaf t ∈ far N.graph (G₄ N a₁ a₂ b₁ b₂) g x → g = e ∨ g = e' := by
  obtain ⟨x, hl, hr⟩ := exists_blob_of_isNextCut (walks_ancestral hN h.mem_left h.mem_right) hn
  exact ⟨x, hl, hr, fun g hg t ht htg =>
    h.eq_or_eq_of_between hN h4 hl hr hn.ne hg ht htg⟩

/-- **"The subgraphs between each taxon and its closest 3-blob have the form of a chain of 2-blobs and cut edges"**
(line 596), for `a₁` or `a₂` and the blob of `v`: two consecutive cut edges between them are incident to one blob, which has
no other incident cut edge with a taxon of the four beyond it. -/
theorem IsTwoBlobs.exists_two_blob_left (hN : N.IsPhylogenetic) (h : IsTwoBlobs N a₁ a₂ b₁ b₂ v w)
    (ha : a = a₁ ∨ a = a₂) (hn : IsNextCut N.graph (G₄ N a₁ a₂ b₁ b₂) (N.leaf a) v e e') :
    ∃ x, LeadsTo N.graph (G₄ N a₁ a₂ b₁ b₂) x e (N.leaf a) ∧ LeadsTo N.graph (G₄ N a₁ a₂ b₁ b₂) x e' v ∧
      ∀ g ∈ incidentCuts N.graph (G₄ N a₁ a₂ b₁ b₂) x, ∀ t ∈ ({a₁, a₂, b₁, b₂} : Set X),
        N.leaf t ∈ far N.graph (G₄ N a₁ a₂ b₁ b₂) g x → g = e ∨ g = e' := by
  have hm : a ∈ ({a₁, a₂, b₁, b₂} : Set X) := by rcases ha with rfl | rfl <;> simp
  obtain ⟨x, hl, hr⟩ := exists_blob_of_isNextCut
    (walks_ancestral hN (N.leaf_mem_ancestralVertices hm) h.mem_left) hn
  exact ⟨x, hl, hr, fun g hg t ht htg =>
    h.eq_or_eq_of_between_left hN ha hl hr hn.ne hg ht htg⟩

/-- The same for `b₁` or `b₂` and the blob of `w` (line 596). -/
theorem IsTwoBlobs.exists_two_blob_right (hN : N.IsPhylogenetic) (h : IsTwoBlobs N a₁ a₂ b₁ b₂ v w)
    (hb : b = b₁ ∨ b = b₂) (hn : IsNextCut N.graph (G₄ N a₁ a₂ b₁ b₂) (N.leaf b) w e e') :
    ∃ x, LeadsTo N.graph (G₄ N a₁ a₂ b₁ b₂) x e (N.leaf b) ∧ LeadsTo N.graph (G₄ N a₁ a₂ b₁ b₂) x e' w ∧
      ∀ g ∈ incidentCuts N.graph (G₄ N a₁ a₂ b₁ b₂) x, ∀ t ∈ ({a₁, a₂, b₁, b₂} : Set X),
        N.leaf t ∈ far N.graph (G₄ N a₁ a₂ b₁ b₂) g x → g = e ∨ g = e' := by
  have hm : b ∈ ({a₁, a₂, b₁, b₂} : Set X) := by rcases hb with rfl | rfl <;> simp
  obtain ⟨x, hl, hr⟩ := exists_blob_of_isNextCut
    (walks_ancestral hN (N.leaf_mem_ancestralVertices hm) h.mem_right) hn
  exact ⟨x, hl, hr, fun g hg t ht htg =>
    h.eq_or_eq_of_between_right hN hb hl hr hn.ne hg ht htg⟩

end Chains

/-! ### The subgraph `G̃₃`, and funnels attached to it -/

section ThreeTaxa

variable {z z₀ z' p q r : X} {e e' : E} {x : V}

/-- **"`G̃₃` also contains the edges in `E`"** (lines 619-620): an arc of `E`, for the taxa `z, p, q, r`,
is a cut edge of the subgraph `G̃₃` induced on `p, q, r`, inducing `p|qr`. -/
theorem Induces.threeTaxa (hN : N.IsPhylogenetic) (he : e ∈ quartetCuts N z p q r) :
    Induces N (G₃ N p q r) e {p} {q, r} :=
  Induces.restrict hN he (Set.subset_insert _ _) (by simp) subset_rfl (by simp)
    (Set.subset_insert _ _) rfl (Set.mem_insert q _)

/-- **A funnel attaches on the side of `p` of an arc of `E`** (lines 622-624): if `e` remains a cut edge
of `G̃₃` with the funnel of `z` attached, inducing `zp|qr`, the funnel attaches only on the side of
`p`. -/
theorem attaches_of_mem_quartetCuts (hN : N.IsPhylogenetic) (he : e ∈ quartetCuts N z p q r)
    (hxZ : x ∈ N.ancestralVertices {p, q, r}) (hx : x ∈ funnelNodes N {p, q, r} z) :
    x ∈ compOff N.graph (G₃ N p q r) e (N.leaf p) :=
  Induces.attaches (Z := {p, q, r}) (Y := {z, p, q, r}) (P := {z, p}) (Q := {q, r}) (q := q) hN he
    (Set.subset_insert _ _) (Set.mem_insert _ _) (Set.mem_insert _ _) (by simp) (by simp) (by simp)
    (by simp) hxZ hx

/-- **The converse** (lines 622-624): a cut edge of `G̃₃` inducing `p|qr` remains one with the funnel of
`z` attached, inducing `zp|qr`, when the funnel attaches only on the side of `p`. -/
theorem mem_quartetCuts_of_attaches (hN : N.IsPhylogenetic)
    (h : Induces N (G₃ N p q r) e {p} {q, r}) (hzq : z ≠ q) (hzr : z ≠ r)
    (hA : ∀ x ∈ N.ancestralVertices {p, q, r}, x ∈ funnelNodes N {p, q, r} z →
      x ∈ compOff N.graph (G₃ N p q r) e (N.leaf p)) :
    e ∈ quartetCuts N z p q r := by
  have hpq : p ≠ q := h.ne rfl (Set.mem_insert q _)
  have hpr : p ≠ r := h.ne rfl (by simp)
  refine Induces.attach_funnels (Z := {p, q, r}) (Y := {z, p, q, r}) (P := {p}) (Q := {q, r})
    (P' := {z, p}) (Q' := {q, r}) (p := p) (q := q) hN h ?_ ?_ (by simp) subset_rfl ?_ rfl
    (Set.mem_insert q _) ?_ ?_
  · ext x
    simp only [Set.mem_insert_iff, Set.mem_union, Set.mem_singleton_iff]
  · ext x
    simp only [Set.mem_insert_iff, Set.mem_union, Set.mem_singleton_iff]
    tauto
  · rw [Set.disjoint_left]
    rintro x (rfl | rfl) (rfl | rfl)
    · exact hzq rfl
    · exact hzr rfl
    · exact hpq rfl
    · exact hpr rfl
  · rintro t (rfl | rfl) x hxZ hx
    · exact hA x hxZ hx
    · exact absurd hx (not_mem_funnelNodes (Set.mem_insert _ _))
  · rintro t (rfl | rfl) x hxZ hx
    · exact absurd hx (not_mem_funnelNodes (by simp))
    · exact absurd hx (not_mem_funnelNodes (by simp))

/-- **The cut edges of `G̃₄` for two choices of `a₁` are comparable** (E4), which is what "the minimality
of `|E|`" (line 624) rests on and the paper does not state. The cut edges of `G̃₃` inducing `p|qr` form a
chain (`chain_between`). The arcs of `E` for a taxon `z` are an up-set of it, since a funnel
attaching on the side of `p` of `e` attaches on the side of `p` of any `e'` further from `p`. -/
theorem quartetCuts_subset_or_subset (hN : N.IsPhylogenetic) (hzq : z ≠ q) (hzr : z ≠ r) (hzq' : z' ≠ q)
    (hzr' : z' ≠ r) : quartetCuts N z p q r ⊆ quartetCuts N z' p q r ∨
      quartetCuts N z' p q r ⊆ quartetCuts N z p q r := by
  by_contra hcon
  simp only [Set.not_subset, not_or] at hcon
  obtain ⟨⟨e, he, he'⟩, e', hf, hf'⟩ := hcon
  have h3 := Induces.threeTaxa hN he
  have h3' := Induces.threeTaxa hN hf
  rcases chain_between hN (N.leaf_mem_ancestralVertices (by simp))
    (N.leaf_mem_ancestralVertices (by simp)) (h3.sep p rfl q (Set.mem_insert q _))
    (h3'.sep p rfl q (Set.mem_insert q _)) with hsub | hsub
  · exact hf' (mem_quartetCuts_of_attaches hN h3' hzq hzr fun x hxZ hx =>
      hsub (attaches_of_mem_quartetCuts hN he hxZ hx))
  · exact he' (mem_quartetCuts_of_attaches hN h3 hzq' hzr' fun x hxZ hx =>
      hsub (attaches_of_mem_quartetCuts hN hf hxZ hx))

/-- The minimality step: of two comparable finite sets, the one that is not larger is contained in
the other. -/
theorem subset_of_comparable_of_ncard_le {α : Type*} [Finite α] {s t : Set α}
    (h : s ⊆ t ∨ t ⊆ s) (hc : s.ncard ≤ t.ncard) : s ⊆ t := by
  rcases h with h | h
  · exact h
  · exact (Set.eq_of_subset_of_ncard_le h hc).symm.subset

/-! ### The sides of `G̃₃` -/

/-- **A side of `G̃₃`** (lines 620-621): "the connected component in which `ã₂` lies when the edges in
`E` are deleted", for `F = G̃₃`, `C = E`, `p = ã₂`. -/
def sideOff (N : RootedNetwork V E X) (F C : Set E) (p : X) : Set V :=
  {x | N.graph.Walks (F \ C) (N.leaf p) x}

/-- The side of `p`, for `E` nonempty, is the component of `p` off the arc of `E` nearest to `p`. -/
theorem exists_sideOff_eq (hN : N.IsPhylogenetic) (hne : (quartetCuts N z p q r).Nonempty) :
    ∃ e₀ ∈ quartetCuts N z p q r,
      sideOff N (G₃ N p q r) (quartetCuts N z p q r) p =
        compOff N.graph (G₃ N p q r) e₀ (N.leaf p) := by
  have : Finite E := hN.finite_arcs
  exact exists_compOff_eq (Set.toFinite _) hne (walks_ancestral hN
    (N.leaf_mem_ancestralVertices (by simp)) (N.leaf_mem_ancestralVertices (x := q) (by simp)))
    fun e he => (Induces.threeTaxa hN he).sep p rfl q (Set.mem_insert q _)

/-- **The `b̃₁b̃₂`-side** (line 621), "similarly": the side of `q` has `r` too. It is the component of `q`
off the arc of `E` nearest to `q`, and `q`, `r` are joined off any arc of `E`. -/
theorem leaf_mem_sideOff (hN : N.IsPhylogenetic) (hne : (quartetCuts N z p q r).Nonempty) :
    N.leaf r ∈ sideOff N (G₃ N p q r) (quartetCuts N z p q r) q := by
  have : Finite E := hN.finite_arcs
  obtain ⟨e₀, he₀, heq⟩ := exists_compOff_eq (F := G₃ N p q r) (u := N.leaf q)
    (w := N.leaf p) (Set.toFinite (quartetCuts N z p q r)) hne (walks_ancestral hN
      (N.leaf_mem_ancestralVertices (by simp)) (N.leaf_mem_ancestralVertices (by simp)))
    fun e he hw => (Induces.threeTaxa hN he).sep p rfl q (Set.mem_insert q _) (N.graph.walks_symm hw)
  change N.leaf r ∈ {x | N.graph.Walks (G₃ N p q r \ quartetCuts N z p q r) (N.leaf q) x}
  rw [heq]
  exact (Induces.threeTaxa hN he₀).right q (Set.mem_insert q _) r (by simp)

/-- A side of `G̃₃` lies in the component off any arc of `E`. -/
theorem sideOff_subset {F C : Set E} (he : e ∈ C) :
    sideOff N F C p ⊆ compOff N.graph F e (N.leaf p) :=
  fun _ hx => walks_mono (Set.sdiff_subset_sdiff_right (Set.singleton_subset_iff.mpr he)) hx

/-- **"The minimality of `|E|` implies that the funnel of `a₁` can only attach to `G̃₃` on the
`ã₂`-side"** (lines 622-625). -/
theorem funnel_attaches_side (hN : N.IsPhylogenetic) (hz₀q : z₀ ≠ q) (hz₀r : z₀ ≠ r) (hzq : z ≠ q)
    (hzr : z ≠ r) (hne : (quartetCuts N z₀ p q r).Nonempty)
    (hmin : (quartetCuts N z₀ p q r).ncard ≤ (quartetCuts N z p q r).ncard)
    (hxZ : x ∈ N.ancestralVertices {p, q, r}) (hx : x ∈ funnelNodes N {p, q, r} z) :
    x ∈ sideOff N (G₃ N p q r) (quartetCuts N z₀ p q r) p := by
  have : Finite E := hN.finite_arcs
  obtain ⟨e₀, he₀, heq⟩ := exists_sideOff_eq (z := z₀) (p := p) (q := q) (r := r) hN hne
  rw [heq]
  exact attaches_of_mem_quartetCuts hN
    (subset_of_comparable_of_ncard_le (quartetCuts_subset_or_subset hN hz₀q hz₀r hzq hzr) hmin he₀)
    hxZ hx

/-- **"Since this is true for all `a₁ ∈ A₁`, the edges in `E` induce the split `A₁ ∪ {ã₂}|{b̃₁, b̃₂}` on
the subnetwork on those taxa"** (lines 625-626), for a block of taxa with a minimal choice `z₀`. -/
theorem induces_block (hN : N.IsPhylogenetic) {block : Set X} (hz₀ : z₀ ∈ block) (hq : q ∉ block)
    (hr : r ∉ block)
    (hmin : ∀ z ∈ block, (quartetCuts N z₀ p q r).ncard ≤ (quartetCuts N z p q r).ncard)
    (he : e ∈ quartetCuts N z₀ p q r) :
    Induces N (N.ancestralArcs (insert p block ∪ {q, r})) e (insert p block) {q, r} := by
  have hne : ∀ {z : X}, z ∈ block → z ≠ q ∧ z ≠ r := fun hz =>
    ⟨fun h => hq (h ▸ hz), fun h => hr (h ▸ hz)⟩
  have h3 := Induces.threeTaxa hN he
  have hpq : p ≠ q := h3.ne rfl (Set.mem_insert q _)
  have hpr : p ≠ r := h3.ne rfl (by simp)
  refine Induces.attach_funnels (Z := {p, q, r}) (P := {p}) (Q := {q, r}) (p := p) (q := q) hN h3 ?_ rfl
    (by simp) subset_rfl ?_ rfl (Set.mem_insert q _) ?_ ?_
  · ext x
    simp only [Set.mem_insert_iff, Set.mem_union, Set.mem_singleton_iff]
  · rw [Set.disjoint_left]
    rintro x (rfl | hx) (rfl | rfl)
    · exact hpq rfl
    · exact hpr rfl
    · exact hq hx
    · exact hr hx
  · rintro t (rfl | ht) x hxZ hx
    · exact absurd hx (not_mem_funnelNodes (Set.mem_insert _ _))
    · exact sideOff_subset he (funnel_attaches_side hN (hne hz₀).1 (hne hz₀).2 (hne ht).1 (hne ht).2
        ⟨e, he⟩ (hmin t ht) hxZ hx)
  · rintro t (rfl | rfl) x hxZ hx
    · exact absurd hx (not_mem_funnelNodes (by simp))
    · exact absurd hx (not_mem_funnelNodes (by simp))

end ThreeTaxa

end ECToBlob
