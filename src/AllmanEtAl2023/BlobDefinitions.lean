module

public import AllmanEtAl2023.InducedNetwork

/-!
# Allman, Baños, Mitchell, Rhodes 2023: Definitions 7 to 13

Blobs, the tree of blobs, its reduced forms, and B- and T-quartets, as objects.

* Definition 7: `blobOf`, `blobNodes` (`isBlob_blobNodes`, `exists_eq_blobNodes_of_isBlob`: the blobs of a graph are the
  library's `DirectedMultigraph.IsBlob`), `IsTrivialBlob`, `IsIncidentToBlob`, `incidentCutEdges`, `cutDegree`, and
  `blobDegree` on a rooted network: an unrooted network has no root, so there the degree is `cutDegree`.
* Definition 8: `IsDeterminedBy`.
* Definition 9: `IsChainOfBlobs`.
* Definition 10: `treeOfBlobsRooted` and, for a semidirected network, `SemidirectedNetwork.treeOfBlobs`.
  `treeOfBlobs_semidirected_isTree`: it is a tree. `nodeDegree_bridgeQuotient`: "a blob with `m` incident cut
  edges produces an `m`-multifurcation".
* Definition 11: `reducedRootedTree` and `Trd`. `Trd` is a labelled simple graph, in which the nodes of degree 2 of
  `T(𝒩⁻)` are gone and two nodes are adjacent when a path through nodes of degree 2 joins them.
* `LabelledGraph.HasQuartetTopology`, `LabelledGraph.HasStarTopology`: "has the quartet tree topology `ab|cd`" and "has
  the unresolved quartet topology", literally: these are the trees on the taxa drawn in the paper's Figure 4.
  `LabelledGraph.splits`: its sides of edges, with a taxon on each side, on which `Displays` of the library reads
  displayed quartets. The bridge `(Trd hN hX).splits = treeOfBlobs N` is `AllmanEtAl2023.Bridges.splits_Trd`.
* Definitions 12 and 13: `IsBlobQuartet`, `IsTreeQuartet`, `IsAssociatedQuartet`.

The names differ from the library's `Phylogenetics.IsBQuartet`, which is a different definition with the same
meaning on phylogenetic networks (`AllmanEtAl2023.Bridges.isBlobQuartet_iff_isBQuartet`): the library says the tree of blobs does not
resolve the set, and Definition 12 says that a blob is determined.
-/

@[expose] public noncomputable section

open Phylogenetics Phylogenetics.RootedNetwork Finset
open scoped Classical

namespace AllmanEtAl2023

variable {V E X : Type*}

/-! ### Blobs of a graph -/

section Blobs

variable {W F : Type*} (G : DirectedMultigraph W F)

/-- The degree of a node of a multigraph: a loop would count twice. -/
def nodeDegree (v : W) : ℕ := G.indegree v + G.outdegree v

/-- The blob containing a node. The blobs are the classes of `DirectedMultigraph.blobSetoid`, as the paper says
after Definition 7: "the connected components obtained by deleting all cut edges in the network". -/
def blobOf (v : W) : G.BlobVertex := Quotient.mk G.blobSetoid v

/-- The nodes of a blob. -/
def blobNodes (b : G.BlobVertex) : Set W := {v | blobOf G v = b}

/-- Definition 7: a blob is *trivial* if it consists of a single node. -/
def IsTrivialBlob (b : G.BlobVertex) : Prop := ∃ v, blobNodes G b = {v}

/-- Definition 7: an edge is *incident* to a blob if exactly one of its incident nodes is in the blob. -/
def IsIncidentToBlob (e : F) (b : G.BlobVertex) : Prop :=
  Xor (blobOf G (G.source e) = b) (blobOf G (G.target e) = b)

/-- The cut edges incident to a blob. -/
def incidentCutEdges (b : G.BlobVertex) : Set F := {e | G.underlying.IsBridge e ∧ IsIncidentToBlob G e b}

/-- **Definition 7** (`a:def:blob`), on a graph with no root: a blob has degree `m`, or is an `m`-blob, if exactly `m` cut
edges are incident to it. On a rooted network, see `blobDegree`. -/
def cutDegree (b : G.BlobVertex) : ℕ := (incidentCutEdges G b).ncard

/-- **Definition 8** (`a:def:determined`). A blob is *determined by* a set of labels `S` with `|S| ≥ 3` if deletion of the
cut edges incident to the blob leaves the elements of `S` in `|S|` distinct connected components. -/
def IsDeterminedBy {ι : Type*} (ℓ : ι → W) (b : G.BlobVertex) (S : Finset ι) : Prop :=
  3 ≤ S.card ∧ ∀ s ∈ S, ∀ t ∈ S, s ≠ t → ¬ G.Walks (incidentCutEdges G b)ᶜ (ℓ s) (ℓ t)

/-- **Definition 9** (`a:def:chain`). A *chain of blobs*: a sequence of 1- and 2-blobs connected by their incident edges.
The degree `deg` is that of the kind of network: `blobDegree` or `cutDegree`. -/
def IsChainOfBlobs (deg : G.BlobVertex → ℕ) (c : List G.BlobVertex) : Prop :=
  c.Nodup ∧ (∀ b ∈ c, deg b = 1 ∨ deg b = 2) ∧
    c.IsChain fun b b' => ∃ e, G.underlying.IsBridge e ∧ IsIncidentToBlob G e b ∧ IsIncidentToBlob G e b'

variable {G}

/-- A blob of Definition 7 in the library's form: a maximal connected subgraph without cut edges. -/
theorem isBlob_blobNodes [Finite F] (v : W) :
    G.IsBlob (blobNodes G (blobOf G v)) (G.blobArcs v) := by
  have h : blobNodes G (blobOf G v) = {w | G.blobSetoid.r v w} := by
    ext w
    simp only [blobNodes, blobOf, Set.mem_ofPred_eq]
    exact ⟨fun hw => G.blobSetoid.symm (Quotient.exact hw), fun hw => Quotient.sound (G.blobSetoid.symm hw)⟩
  rw [h]
  exact G.isBlob_blobClass v

/-- Every maximal connected subgraph without cut edges has the nodes of a blob of Definition 7. -/
theorem exists_eq_blobNodes_of_isBlob [Finite F] {U : Set W} {A : Set F} (h : G.IsBlob U A) :
    ∃ b, U = blobNodes G b := by
  obtain ⟨v, rfl, -⟩ := (G.isBlob_iff U A).mp h
  refine ⟨blobOf G v, ?_⟩
  ext w
  simp only [blobNodes, blobOf, Set.mem_ofPred_eq]
  exact ⟨fun hw => Quotient.sound (G.blobSetoid.symm hw), fun hw => G.blobSetoid.symm (Quotient.exact hw)⟩

/-- The two ends of a cut edge are in different blobs: "an edge in the network is said to be incident to a blob if
exactly one of its incident nodes is in the blob". -/
theorem blobOf_source_ne_target {e : F} (he : G.underlying.IsBridge e) :
    blobOf G (G.source e) ≠ blobOf G (G.target e) := by
  obtain ⟨S, hS⟩ := (G.isBridge_iff e).mp he
  intro h
  have hiff := G.mem_iff_of_blobSetoid hS h
  have hc := (hS e).mpr rfl
  simp only [DirectedMultigraph.Crosses] at hc
  tauto

/-- "A blob with `m` incident cut edges in a network produces an `m`-multifurcation in its tree of blobs." -/
theorem nodeDegree_bridgeQuotient [Finite F] (b : G.BlobVertex) :
    nodeDegree G.bridgeQuotient b = cutDegree G b := by
  have hin : G.bridgeQuotient.indegree b = {e | G.underlying.IsBridge e ∧ blobOf G (G.target e) = b}.ncard :=
    Set.ncard_congr' ⟨fun e => ⟨e.1.1, e.1.2, e.2⟩, fun e => ⟨⟨e.1, e.2.1⟩, e.2.2⟩, fun _ => rfl, fun _ => rfl⟩
  have hout : G.bridgeQuotient.outdegree b = {e | G.underlying.IsBridge e ∧ blobOf G (G.source e) = b}.ncard :=
    Set.ncard_congr' ⟨fun e => ⟨e.1.1, e.1.2, e.2⟩, fun e => ⟨⟨e.1, e.2.1⟩, e.2.2⟩, fun _ => rfl, fun _ => rfl⟩
  have hunion : incidentCutEdges G b = {e | G.underlying.IsBridge e ∧ blobOf G (G.target e) = b} ∪
      {e | G.underlying.IsBridge e ∧ blobOf G (G.source e) = b} := by
    ext e
    simp only [incidentCutEdges, IsIncidentToBlob, Set.mem_ofPred_eq, Set.mem_union]
    constructor
    · rintro ⟨he, ⟨h, -⟩ | ⟨h, -⟩⟩
      · exact Or.inr ⟨he, h⟩
      · exact Or.inl ⟨he, h⟩
    · rintro (⟨he, h⟩ | ⟨he, h⟩)
      · refine ⟨he, Or.inr ⟨h, fun h' => blobOf_source_ne_target he (h'.trans h.symm)⟩⟩
      · refine ⟨he, Or.inl ⟨h, fun h' => blobOf_source_ne_target he (h.trans h'.symm)⟩⟩
  have hdisj : Disjoint {e | G.underlying.IsBridge e ∧ blobOf G (G.target e) = b}
      {e | G.underlying.IsBridge e ∧ blobOf G (G.source e) = b} := by
    refine Set.disjoint_left.mpr fun e he he' => ?_
    exact blobOf_source_ne_target he.1 (he'.2.trans he.2.symm)
  rw [nodeDegree, hin, hout, cutDegree, hunion, Set.ncard_union_eq hdisj (Set.toFinite _) (Set.toFinite _)]

/-- A node of degree 1 has a single edge, which is not a loop. -/
theorem nodeDegree_eq_one_iff [Finite F] {v : W} : nodeDegree G v = 1 ↔ ∃ g, G.source g ≠ G.target g ∧ (G.source g = v ∨ G.target g = v) ∧
    ∀ f, (G.source f = v ∨ G.target f = v) → f = g := by
  constructor
  · intro hd
    unfold nodeDegree at hd
    have hcases : (G.indegree v = 1 ∧ G.outdegree v = 0) ∨ (G.indegree v = 0 ∧ G.outdegree v = 1) := by
      omega
    rcases hcases with ⟨h₁, h₀⟩ | ⟨h₀, h₁⟩
    · obtain ⟨g, hg⟩ := (G.indegree_eq_one_iff _).mp h₁
      have hno := (G.outdegree_eq_zero_iff _).mp h₀
      refine ⟨g, fun h => hno g (h.trans ((hg g).mpr rfl)), Or.inr ((hg g).mpr rfl), fun f hf => ?_⟩
      rcases hf with hf | hf
      · exact absurd hf (hno f)
      · exact (hg f).mp hf
    · obtain ⟨g, hg⟩ := (G.outdegree_eq_one_iff _).mp h₁
      have hno := (G.indegree_eq_zero_iff _).mp h₀
      refine ⟨g, fun h => hno g (h.symm.trans ((hg g).mpr rfl)), Or.inl ((hg g).mpr rfl), fun f hf => ?_⟩
      rcases hf with hf | hf
      · exact (hg f).mp hf
      · exact absurd hf (hno f)
  · rintro ⟨g, hne, hg, hu⟩
    unfold nodeDegree
    rcases hg with hs | ht
    · have h₀ : G.indegree v = 0 := (G.indegree_eq_zero_iff _).mpr fun f hf => hne (hs.trans (hu f (Or.inr hf) ▸ hf).symm)
      have h₁ : G.outdegree v = 1 := (G.outdegree_eq_one_iff _).mpr ⟨g, fun f => ⟨fun hf => hu f (Or.inl hf), fun h => h ▸ hs⟩⟩
      omega
    · have h₀ : G.outdegree v = 0 := (G.outdegree_eq_zero_iff _).mpr fun f hf => hne ((hu f (Or.inl hf) ▸ hf).trans ht.symm)
      have h₁ : G.indegree v = 1 := (G.indegree_eq_one_iff _).mpr ⟨g, fun f => ⟨fun hf => hu f (Or.inr hf), fun h => h ▸ ht⟩⟩
      omega

/-- The single edge at a node, not a loop, is the only edge crossing the node. -/
theorem crosses_singleton_iff {v : W} {g : F} (hne : G.source g ≠ G.target g) (hg : G.source g = v ∨ G.target g = v)
    (huniq : ∀ f, (G.source f = v ∨ G.target f = v) → f = g) (f : F) : G.Crosses f {v} ↔ f = g := by
  constructor
  · rintro (⟨hs, -⟩ | ⟨ht, -⟩)
    · exact huniq f (Or.inl hs)
    · exact huniq f (Or.inr ht)
  · rintro rfl
    rcases hg with hs | ht
    · exact Or.inl ⟨hs, fun ht => hne (hs.trans ht.symm)⟩
    · exact Or.inr ⟨ht, fun hs => hne (hs.trans ht.symm)⟩

/-- A degree-one node is a trivial blob, and a node of degree one in the tree of blobs. -/
theorem nodeDegree_bridgeQuotient_of_nodeDegree_eq_one [Finite F] {v : W} (h : nodeDegree G v = 1) :
    nodeDegree G.bridgeQuotient (blobOf G v) = 1 := by
  obtain ⟨g, hne, hg, huniq⟩ := nodeDegree_eq_one_iff.mp h
  have hcut := crosses_singleton_iff hne hg huniq
  have hb : G.underlying.IsBridge g := (G.isBridge_iff g).mpr ⟨{v}, hcut⟩
  have hclass : ∀ u, blobOf G u = blobOf G v → u = v := fun u hu =>
    (G.mem_iff_of_blobSetoid hcut hu).mpr rfl
  have hval : ∀ (e : G.BridgeArc) (u : W), u = G.source e.1 ∨ u = G.target e.1 →
      Quotient.mk G.blobSetoid u = blobOf G v → e = ⟨g, hb⟩ := fun e u hu hq => by
    have huv := hclass u hq
    apply Subtype.ext
    rcases hu with rfl | rfl
    · exact huniq _ (Or.inl huv)
    · exact huniq _ (Or.inr huv)
  have hsets : ∀ {P : G.BridgeArc → Prop}, (∀ e, P e → e = ⟨g, hb⟩) → P ⟨g, hb⟩ →
      {e | P e} = {⟨g, hb⟩} := fun h₁ h₂ => by
    ext e
    exact ⟨fun he => h₁ e he, fun he => (Set.mem_singleton_iff.mp he).symm ▸ h₂⟩
  have hempty : ∀ {P : G.BridgeArc → Prop}, (∀ e, P e → e = ⟨g, hb⟩) → ¬ P ⟨g, hb⟩ →
      {e | P e} = ∅ := fun h₁ h₂ => by
    ext e
    exact ⟨fun he => h₂ (h₁ e he ▸ he), fun he => he.elim⟩
  have hs' : ∀ e : G.BridgeArc, G.bridgeQuotient.source e = blobOf G v → e = ⟨g, hb⟩ := fun e he =>
    hval e _ (Or.inl rfl) he
  have ht' : ∀ e : G.BridgeArc, G.bridgeQuotient.target e = blobOf G v → e = ⟨g, hb⟩ := fun e he =>
    hval e _ (Or.inr rfl) he
  rcases hg with hs | ht
  · have hout : G.bridgeQuotient.outdegree (blobOf G v) = 1 := by
      rw [DirectedMultigraph.outdegree, hsets hs' (by simp [DirectedMultigraph.bridgeQuotient, blobOf, hs]),
        Set.ncard_singleton]
    have hin : G.bridgeQuotient.indegree (blobOf G v) = 0 := by
      rw [DirectedMultigraph.indegree, hempty ht' fun h => hne (hs.trans (hclass _ h).symm), Set.ncard_empty]
    rw [nodeDegree, hin, hout]
  · have hin : G.bridgeQuotient.indegree (blobOf G v) = 1 := by
      rw [DirectedMultigraph.indegree, hsets ht' (by simp [DirectedMultigraph.bridgeQuotient, blobOf, ht]),
        Set.ncard_singleton]
    have hout : G.bridgeQuotient.outdegree (blobOf G v) = 0 := by
      rw [DirectedMultigraph.outdegree, hempty hs' fun h => hne ((hclass _ h).trans ht.symm), Set.ncard_empty]
    rw [nodeDegree, hin, hout]

end Blobs

/-! ### Blobs of a rooted network -/

/-- **Definition 7** (`a:def:blob`), on a rooted network: a blob has degree `m`, or is an `m`-blob, if a) it has exactly `m` cut
edges incident to it and the root is not in the blob, or b) it has exactly `m - 1` cut edges incident to it and the
root is in the blob. -/
def blobDegree (N : RootedNetwork V E X) (b : N.graph.BlobVertex) : ℕ :=
  if blobOf N.graph N.root = b then cutDegree N.graph b + 1 else cutDegree N.graph b

/-- **Definition 10** (`a:def:tob`; Gusfield et al. 2007), on a rooted network: the *tree of blobs* `T(𝒩)`, "obtained by
contracting each blob to a node, that is, by removing all of the blob's edges and identifying all its nodes. If the
network is rooted, the tree of blobs remains rooted at the same node, or the one arising from identifying the
original root with other nodes". -/
abbrev treeOfBlobsRooted (N : RootedNetwork V E X) : RootedNetwork N.graph.BlobVertex N.graph.BridgeArc X :=
  N.bridgeQuotientData

/-! ### The semidirected network: connectedness, and its leaves -/

section Unroot

variable {M : RootedNetwork V E X}

/-- The other edge out of a root of out-degree 2. -/
theorem exists_other_root_arc (hout : M.graph.outdegree M.root = 2) {e₀ : E}
    (he₀ : M.graph.source e₀ = M.root) :
    ∃ e₁, e₁ ≠ e₀ ∧ ∀ f, M.graph.source f = M.root ↔ f = e₀ ∨ f = e₁ := by
  obtain ⟨p, q, hpq, h⟩ := Set.ncard_eq_two.mp hout
  have hmem : ∀ f, M.graph.source f = M.root ↔ f = p ∨ f = q := fun f => by
    have := Set.ext_iff.mp h f
    simpa using this
  rcases (hmem e₀).mp he₀ with rfl | rfl
  · exact ⟨q, hpq.symm, hmem⟩
  · exact ⟨p, hpq, fun f => (hmem f).trans or_comm⟩

variable (hM : M.IsPhylogenetic) {e₀ : E} (he₀ : M.graph.source e₀ = M.root)
  (hout : M.graph.outdegree M.root = 2)

include he₀ hout in
/-- A taxon is a node with one edge in a semidirected network. -/
theorem nodeDegree_unrootAt_leaf (x : X) :
    nodeDegree (unrootAt M hM e₀).graph ((unrootAt M hM e₀).leaf x) = 1 := by
  have : Finite E := hM.finite_arcs
  rw [nodeDegree_eq_one_iff]
  obtain ⟨e₁, hne₁, hroot⟩ := exists_other_root_arc hout he₀
  obtain ⟨g₀, hg₀⟩ := (M.graph.indegree_eq_one_iff _).mp (hM.leaf_indegree x)
  have hno : ∀ f, M.graph.source f ≠ M.leaf x :=
    (M.graph.outdegree_eq_zero_iff _).mp ((hM.leaves _).mpr ⟨x, rfl⟩)
  have hsrc : ∀ f : {e // e ≠ e₀}, ((unrootAt M hM e₀).graph.source f).1 =
      if M.graph.source f.1 = M.root then M.graph.target e₀ else M.graph.source f.1 := by
    intro f
    simp only [unrootAt]
    split_ifs <;> rfl
  have htgt : ∀ f : {e // e ≠ e₀}, ((unrootAt M hM e₀).graph.target f).1 = M.graph.target f.1 := fun _ => rfl
  have hleaf : ((unrootAt M hM e₀).leaf x).1 = M.leaf x := rfl
  by_cases hge : g₀ = e₀
  · -- the taxon is a child of the root, by the edge merged away
    have ht₀ : M.graph.target e₀ = M.leaf x := (hg₀ e₀).mpr hge.symm
    refine ⟨⟨e₁, hne₁⟩, fun h => ?_, Or.inl ?_, fun f hf => ?_⟩
    · have h' := congrArg Subtype.val h
      rw [hsrc, htgt, ite_eq_left ((hroot e₁).mpr (Or.inr rfl)), ht₀] at h'
      exact hne₁ (((hg₀ e₁).mp h'.symm).trans hge)
    · apply Subtype.ext
      rw [hsrc, ite_eq_left ((hroot e₁).mpr (Or.inr rfl)), ht₀]
      exact hleaf.symm
    · apply Subtype.ext
      rcases hf with hf | hf
      · have h' := congrArg Subtype.val hf
        rw [hsrc, hleaf] at h'
        split_ifs at h' with hr
        · exact ((hroot f.1).mp hr).resolve_left f.2
        · exact absurd h' (hno f.1)
      · have h' := congrArg Subtype.val hf
        rw [htgt, hleaf] at h'
        exact absurd (((hg₀ f.1).mp h').trans hge) f.2
  · refine ⟨⟨g₀, hge⟩, fun h => ?_, Or.inr (Subtype.ext ((hg₀ g₀).mpr rfl)), fun f hf => ?_⟩
    · have h' := congrArg Subtype.val h
      rw [hsrc, htgt, (hg₀ g₀).mpr rfl] at h'
      split_ifs at h' with hr
      · exact hge ((hg₀ e₀).mp h').symm
      · exact hno _ h'
    · apply Subtype.ext
      rcases hf with hf | hf
      · have h' := congrArg Subtype.val hf
        rw [hsrc, hleaf] at h'
        split_ifs at h' with hr
        · exact absurd ((hg₀ e₀).mp h').symm hge
        · exact absurd h' (hno f.1)
      · have h' := congrArg Subtype.val hf
        rw [htgt, hleaf] at h'
        exact (hg₀ f.1).mp h'

include he₀ hout in
/-- A semidirected network is connected. -/
theorem unrootAt_isConnected : (unrootAt M hM e₀).graph.IsConnected := by
  have : Finite E := hM.finite_arcs
  obtain ⟨e₁, hne₁, hroot⟩ := exists_other_root_arc hout he₀
  let c₀ : {v // v ≠ M.root} := ⟨M.graph.target e₀, target_ne_root hM e₀⟩
  have hsrc : ∀ (f : {e // e ≠ e₀}) (hf : M.graph.source f.1 ≠ M.root),
      (unrootAt M hM e₀).graph.source f = ⟨M.graph.source f.1, hf⟩ := by
    intro f hf
    simp only [unrootAt, dite_eq_right hf]
  -- a directed path from a node other than the root stays there
  have hpath : ∀ (a : {v // v ≠ M.root}) {t : V}, M.graph.Reaches a.1 t → ∀ ht : t ≠ M.root,
      (unrootAt M hM e₀).graph.Walks Set.univ a ⟨t, ht⟩ := by
    intro a t hat
    induction hat with
    | refl => exact fun _ => .refl
    | @tail s t' has hst ih =>
      intro ht
      have hsr : s ≠ M.root := by
        intro hs
        have := eq_of_reaches_of_reaches hM.acyclic (hs ▸ has) (hM.root_reaches a.1)
        exact a.2 this
      obtain ⟨f, hfs, hft⟩ := hst
      have hfne : f ≠ e₀ := by
        rintro rfl
        exact hsr (hfs.symm.trans he₀)
      refine (ih hsr).tail ⟨⟨f, hfne⟩, Set.mem_univ _, Or.inl ⟨?_, Subtype.ext hft⟩⟩
      rw [hsrc ⟨f, hfne⟩ (hfs ▸ hsr)]
      exact Subtype.ext hfs
  have hc : ∀ v : {v // v ≠ M.root}, (unrootAt M hM e₀).graph.Walks Set.univ c₀ v := by
    intro v
    rcases Relation.ReflTransGen.cases_head (hM.root_reaches v.1) with h | ⟨a, ⟨f, hfs, rfl⟩, hav⟩
    · exact absurd h.symm v.2
    · rcases (hroot f).mp hfs with rfl | rfl
      · exact hpath c₀ (t := v.1) hav v.2
      · have hedge : (unrootAt M hM e₀).graph.Walks Set.univ c₀ ⟨M.graph.target f, target_ne_root hM f⟩ := by
          refine Relation.ReflTransGen.single ⟨⟨f, hne₁⟩, Set.mem_univ _, Or.inl ⟨?_, rfl⟩⟩
          simp only [unrootAt, c₀, dite_eq_left hfs]
        exact hedge.trans (hpath ⟨M.graph.target f, target_ne_root hM f⟩ hav v.2)
  exact fun u v => ((unrootAt M hM e₀).graph.walks_symm (hc u)).trans (hc v)

end Unroot

/-! ### Definition 10 and Definition 11 -/

namespace SemidirectedNetwork

/-- **Definition 10** (`a:def:tob`), on a semidirected network: the *tree of blobs* `T(𝒩⁻)`. -/
abbrev treeOfBlobs (S : SemidirectedNetwork V E X) : DirectedMultigraph S.graph.BlobVertex S.graph.BridgeArc :=
  S.graph.bridgeQuotient

end SemidirectedNetwork

section Reduced

variable {N : RootedNetwork V E X}

/-- **Definition 11, first part** (`a:def:trd`). The *reduced rooted tree of blobs* `T_rd(𝒩⁺)`: "obtained from the tree of
blobs `T(𝒩⊕)` of the LSA network by suppressing all nodes of both in-degree 1 and out-degree 1". This is the library's
`RootedNetwork.blobTree` of `𝒩⊕`. -/
def reducedRootedTree (hN : IsBinaryNetwork N) (hX : Nontrivial X) :=
  (lsaPlus hN hX).blobTree (lsaPlus_isPhylogenetic hN hX)

/-- `T(𝒩⁻)` is a tree. -/
theorem treeOfBlobs_semidirected_isTree (hN : IsBinaryNetwork N) (hX : Nontrivial X) :
    (semidirected hN hX).treeOfBlobs.IsTree :=
  DirectedMultigraph.bridgeQuotient_isTree _ (unrootAt_isConnected _ (rootTreeArc_spec hN hX).1
    (lsaPlus_outdegree_root hN hX))

end Reduced

/-- A simple graph with labelled nodes. -/
structure LabelledGraph (W X : Type*) where
  graph : SimpleGraph W
  leaf : X → W

/-- `u` and `v` are joined in `G` by a path whose interior nodes all have degree 2. -/
def ChainLink {W F : Type*} (G : DirectedMultigraph W F) (u v : W) : Prop :=
  ∃ x, Relation.ReflTransGen (fun a b => G.AdjOn Set.univ a b ∧ nodeDegree G b = 2) u x ∧
    G.AdjOn Set.univ x v

/-- "Suppressing all nodes of degree 2" of a tree: the nodes of degree other than 2, in which two are adjacent when a
path through nodes of degree 2 joins them. A tree has at most one such path, so no parallel edges appear, and a simple
graph can hold the result. -/
def suppressDegreeTwo {W F : Type*} (G : DirectedMultigraph W F) : SimpleGraph {w // nodeDegree G w ≠ 2} :=
  SimpleGraph.fromRel fun u v => ChainLink G u.1 v.1

section Trd

variable {N : RootedNetwork V E X}

/-- A taxon is a node of degree 1 of a network. -/
theorem nodeDegree_leaf (hN : N.IsPhylogenetic) (x : X) : nodeDegree N.graph (N.leaf x) = 1 := by
  rw [nodeDegree, hN.leaf_indegree, (hN.leaves _).mpr ⟨x, rfl⟩]

/-- A taxon is a node of degree 1 in `T(𝒩⁻)`, hence not suppressed. -/
theorem nodeDegree_treeOfBlobs_leaf (hN : IsBinaryNetwork N) (hX : Nontrivial X) (x : X) :
    nodeDegree (semidirected hN hX).treeOfBlobs
      (blobOf (semidirected hN hX).graph ((semidirected hN hX).leaf x)) = 1 := by
  have := (lsaPlus_isPhylogenetic hN hX).finite_arcs
  exact nodeDegree_bridgeQuotient_of_nodeDegree_eq_one
    (nodeDegree_unrootAt_leaf (lsaPlus_isPhylogenetic hN hX) (rootTreeArc_spec hN hX).1 (lsaPlus_outdegree_root hN hX) x)

/-- The nodes of `T_rd(𝒩⁻)`. -/
abbrev TrdV (hN : IsBinaryNetwork N) (hX : Nontrivial X) :=
  {b : (semidirected hN hX).graph.BlobVertex // nodeDegree (semidirected hN hX).treeOfBlobs b ≠ 2}

/-- **Definition 11, second part** (`a:def:trd`). The *reduced unrooted tree of blobs* `T_rd(𝒩⁻)`: "obtained from the tree of
blobs `T(𝒩⁻)` of the unrooted semidirected network by suppressing all nodes of degree 2". -/
def Trd (hN : IsBinaryNetwork N) (hX : Nontrivial X) : LabelledGraph (TrdV hN hX) X where
  graph := suppressDegreeTwo (semidirected hN hX).treeOfBlobs
  leaf x := ⟨blobOf (semidirected hN hX).graph ((semidirected hN hX).leaf x), by
    rw [nodeDegree_treeOfBlobs_leaf hN hX x]
    omega⟩

end Trd

/-! ### Topologies of labelled trees -/

namespace LabelledGraph

variable {W : Type*} (T : LabelledGraph W X)

/-- `T` *has the quartet tree topology `ab|cd`*: "the topology with cherries `{a,b}` and `{c,d}` separated by an internal
edge". -/
def HasQuartetTopology (a b c d : X) : Prop :=
  ∃ u w : W, [T.leaf a, T.leaf b, T.leaf c, T.leaf d, u, w].Nodup ∧
    (∀ v, v ∈ [T.leaf a, T.leaf b, T.leaf c, T.leaf d, u, w]) ∧
    T.graph.edgeSet = {s(T.leaf a, u), s(T.leaf b, u), s(u, w), s(T.leaf c, w), s(T.leaf d, w)}

/-- `T` *has the unresolved quartet topology* `abcd`: "the star topology for the 4-taxon tree". -/
def HasStarTopology (a b c d : X) : Prop :=
  ∃ u : W, [T.leaf a, T.leaf b, T.leaf c, T.leaf d, u].Nodup ∧
    (∀ v, v ∈ [T.leaf a, T.leaf b, T.leaf c, T.leaf d, u]) ∧
    T.graph.edgeSet = {s(T.leaf a, u), s(T.leaf b, u), s(T.leaf c, u), s(T.leaf d, u)}

/-- `A` is the set of taxa on one side of an edge of `T`. -/
def HasSide (A : Set X) : Prop :=
  ∃ u w, T.graph.Adj u w ∧ ∀ x, x ∈ A ↔ (T.graph.deleteEdges {s(u, w)}).Reachable u (T.leaf x)

/-- The sides of the edges of `T` with a taxon on each side: the tree as a family of splits, as in the library's
`Phylogenetics.Displays` and `Phylogenetics.treeOfBlobs`. -/
def splits [Fintype X] [DecidableEq X] : Finset (Finset X) :=
  univ.filter fun A => A.Nonempty ∧ Aᶜ.Nonempty ∧ T.HasSide (A : Set X)

/-- Two labelled graphs are isomorphic by a map that respects the labels. -/
def IsIso {W' : Type*} (T' : LabelledGraph W' X) : Prop :=
  ∃ φ : T.graph ≃g T'.graph, ∀ x, φ (T.leaf x) = T'.leaf x

/-- The set of four taxa `q` is displayed unresolved: `T` displays none of the three resolved quartet trees on it.
See `abcd` in "the unresolved quartet `abcd` is displayed on the tree of blobs". -/
def DisplaysUnresolved [Fintype X] [DecidableEq X] (q : Finset X) : Prop :=
  q.card = 4 ∧ ∀ s ∈ treesOn q, ¬ Displays T.splits s

end LabelledGraph

/-! ### Definitions 12 and 13 -/

section Quartets

/-- **Definition 12** (`a:def:Bquartet`). A set of four taxa is a *Blob quartet*, or *B-quartet*, on a network if there is a blob
on the network which is determined by it. -/
def IsBlobQuartet (N : RootedNetwork V E X) (Q : Finset X) : Prop :=
  Q.card = 4 ∧ ∃ b, IsDeterminedBy N.graph N.leaf b Q

/-- **Definition 13** (`a:def:Tquartet`). A set of four taxa that is not a B-quartet is a *tree-like quartet*, or *T-quartet*. -/
def IsTreeQuartet (N : RootedNetwork V E X) (Q : Finset X) : Prop :=
  Q.card = 4 ∧ ¬ IsBlobQuartet N Q

variable {N : RootedNetwork V E X}

/-- **Definition 13**, second part (`a:def:Tquartet`). The resolved quartet `s` is *associated* to the T-quartet on its taxa:
it is that displayed on the tree of blobs `T_rd(𝒩⁻)`. -/
def IsAssociatedQuartet [Fintype X] [DecidableEq X] (hN : IsBinaryNetwork N) (hX : Nontrivial X)
    (s : QuartetTree X) : Prop :=
  IsTreeQuartet N s.taxa ∧ Displays (Trd hN hX).splits s

end Quartets

/-! ### Induced networks on sets of taxa -/

section InducedQuartets

variable {N : RootedNetwork V E X} [DecidableEq X]

omit [DecidableEq X] in
/-- A set of four taxa has at least two. -/
theorem nontrivial_coe_of_card_four {Q : Finset X} (hQ : Q.card = 4) : (Q : Set X).Nontrivial :=
  Finset.one_lt_card_iff_nontrivial.mp (by omega)

/-- `T_rd(𝒩⁻_Q)`, the reduced unrooted tree of blobs of the network induced on `Q`. -/
def inducedTrd (hN : IsBinaryNetwork N) (Q : Finset X) (hQ : Q.card = 4) :=
  Trd (induced_isBinaryNetwork hN (Q : Set X) (nontrivial_coe_of_card_four hQ))
    (nontrivial_coe_of_card_four hQ).coe_sort

/-- `T_rd(𝒩⁻_Q)` has the quartet tree topology `ab|cd`, for `Q = {a, b, c, d}`. -/
def InducedHasQuartetTopology (hN : IsBinaryNetwork N) (a b c d : X)
    (h : ({a, b, c, d} : Finset X).card = 4) : Prop :=
  (inducedTrd hN {a, b, c, d} h).HasQuartetTopology ⟨a, by simp⟩ ⟨b, by simp⟩ ⟨c, by simp⟩ ⟨d, by simp⟩

/-- `T_rd(𝒩⁻_Q)` has the unresolved quartet topology, for `Q = {a, b, c, d}`. -/
def InducedHasStarTopology (hN : IsBinaryNetwork N) (a b c d : X)
    (h : ({a, b, c, d} : Finset X).card = 4) : Prop :=
  (inducedTrd hN {a, b, c, d} h).HasStarTopology ⟨a, by simp⟩ ⟨b, by simp⟩ ⟨c, by simp⟩ ⟨d, by simp⟩

/-- The set `Q` of taxa is a B-quartet on the network induced on `Y`. -/
def IsBlobQuartetOnInduced (hN : IsBinaryNetwork N) (Y : Set X) (hY : Y.Nontrivial) (Q : Finset X) : Prop :=
  IsBlobQuartet (induced hN Y hY) (Q.subtype (· ∈ Y))

end InducedQuartets

end AllmanEtAl2023
