module

public import AllmanEtAl2023.TrivialEdges

/-!
# Allman, Baños, Mitchell, Rhodes 2023: the small remarks on blobs of Section 2

* "On a rooted binary phylogenetic tree, leaves are the only 1-blobs, while the root and internal nodes are 3-blobs. On a non-binary tree, polytomous nodes are `k`-blobs with `k ≥ 4`": `blobDegree_eq_one_iff_of_isTreeNetwork`, `blobDegree_eq_three_of_isTreeNetwork`, `four_le_blobDegree_of_isTreeNetwork`.
* "If the root of a binary network is a trivial blob, then it is a degree-2 node but forms a degree-3 blob": `root_of_isTrivialBlob`.
* "On a tree any 3 taxa determine a unique node": `existsUnique_node_of_isTreeNetwork`.
* "Nodes of degree 4 or more in the tree of blobs indicate non-trivial blobs for a binary network": `not_isTrivialBlob_of_four_le_cutDegree`.
* "Our restriction to binary networks rules out this possibility regardless", of two cycles sharing only a node: `exists_mem_inter_of_two_incident`.
* "(If the network is level-1, this is a chain of 2-cycles ...)", for the structure above the LSA: `ncard_blobNodes_of_isAboveLSA`, for the library's `RootedNetwork.IsLevelOne`, with `ncard_edges_of_isLevelOne`: "the form of cycles".
-/

@[expose] public noncomputable section

open Phylogenetics Phylogenetics.RootedNetwork Phylogenetics.DirectedMultigraph
open scoped Classical

namespace AllmanEtAl2023.BlobStructure

variable {V E X : Type*} {N : RootedNetwork V E X}

/-! ### A node alone in its blob -/

/-- The edges at a node. -/
def edgesAt (N : RootedNetwork V E X) (v : V) : Set E := {e | N.graph.source e = v ∨ N.graph.target e = v}

/-- The number of the edges at a node is its degree, since there are no loops. -/
theorem ncard_edgesAt (hN : N.IsPhylogenetic) (v : V) : (edgesAt N v).ncard = nodeDegree N.graph v := by
  have : Finite E := hN.finite_arcs
  have hset : edgesAt N v = {e | N.graph.target e = v} ∪ {e | N.graph.source e = v} := by
    ext e
    simp only [edgesAt, Set.mem_ofPred_eq, Set.mem_union]
    tauto
  rw [hset, Set.ncard_union_eq _ (Set.toFinite _) (Set.toFinite _)]
  · rfl
  · refine Set.disjoint_left.2 fun e h₁ h₂ => NMSC.source_ne_target hN e ?_
    exact (show N.graph.source e = v from h₂).trans (show N.graph.target e = v from h₁).symm

theorem blobOf_eq_iff_of_isTrivialBlob {v : V} (hv : IsTrivialBlob N.graph (blobOf N.graph v)) (u : V) : blobOf N.graph u = blobOf N.graph v ↔ u = v := by
  obtain ⟨x, hx⟩ := hv
  have hvx : v = x := by
    have : v ∈ blobNodes N.graph (blobOf N.graph v) := rfl
    rw [hx] at this
    exact this
  constructor
  · intro h
    have : u ∈ blobNodes N.graph (blobOf N.graph v) := h
    rw [hx] at this
    exact (show u = x from this).trans hvx.symm
  · rintro rfl
    rfl

/-- The cut edges at a node alone in its blob are the edges at the node. -/
theorem incidentCutEdges_of_isTrivialBlob (hN : N.IsPhylogenetic) {v : V} (hv : IsTrivialBlob N.graph (blobOf N.graph v)) :
    incidentCutEdges N.graph (blobOf N.graph v) = edgesAt N v := by
  ext e
  simp only [incidentCutEdges, IsIncidentToBlob, Set.mem_ofPred_eq, blobOf_eq_iff_of_isTrivialBlob hv, edgesAt]
  constructor
  · rintro ⟨-, (⟨h, -⟩ | ⟨h, -⟩)⟩
    · exact Or.inl h
    · exact Or.inr h
  · intro h
    refine ⟨TrivialEdges.isBridge_of_isTrivialBlob hN hv h, ?_⟩
    have hne := NMSC.source_ne_target hN e
    rcases h with h | h
    · exact Or.inl ⟨h, fun h' => hne (h.trans h'.symm)⟩
    · exact Or.inr ⟨h, fun h' => hne (h'.trans h.symm)⟩

/-- The cut degree of a node alone in its blob is its degree. -/
theorem cutDegree_of_isTrivialBlob (hN : N.IsPhylogenetic) {v : V} (hv : IsTrivialBlob N.graph (blobOf N.graph v)) :
    cutDegree N.graph (blobOf N.graph v) = nodeDegree N.graph v := by
  rw [cutDegree, incidentCutEdges_of_isTrivialBlob hN hv, ncard_edgesAt hN]

/-- **The degree of a blob that is a node**: the degree of the node, and one more at the root. -/
theorem blobDegree_of_isTrivialBlob (hN : N.IsPhylogenetic) {v : V} (hv : IsTrivialBlob N.graph (blobOf N.graph v)) :
    blobDegree N (blobOf N.graph v) = if v = N.root then nodeDegree N.graph v + 1 else nodeDegree N.graph v := by
  unfold blobDegree
  rw [cutDegree_of_isTrivialBlob hN hv]
  simp only [blobOf_eq_iff_of_isTrivialBlob hv, eq_comm (a := N.root)]

/-- **"If the root of a binary network is a trivial blob, then it is a degree-2 node but forms a degree-3 blob"** (`a:claim:root-degree`, after Definition 7). -/
theorem root_of_isTrivialBlob (hN : IsBinaryNetwork N) (hv : IsTrivialBlob N.graph (blobOf N.graph N.root)) :
    nodeDegree N.graph N.root = 2 ∧ blobDegree N (blobOf N.graph N.root) = 3 := by
  have h2 : nodeDegree N.graph N.root = 2 := by
    rw [nodeDegree, hN.root_in, hN.root_out]
  refine ⟨h2, ?_⟩
  rw [blobDegree_of_isTrivialBlob hN.isPhylogenetic hv, ite_eq_left rfl, h2]

/-- The degree of a node of a binary network. -/
theorem nodeDegree_le_three (hN : IsBinaryNetwork N) (v : V) : nodeDegree N.graph v ≤ 3 := by
  rcases hN.node_cases v with rfl | ⟨x, rfl⟩ | h | h
  · rw [nodeDegree, hN.root_in, hN.root_out]
    omega
  · rw [nodeDegree, hN.leaf_in, hN.leaf_out]
    omega
  · rw [nodeDegree, h.1, h.2]
  · rw [nodeDegree, h.1, h.2]

/-- **"Nodes of degree 4 or more in the tree of blobs indicate non-trivial blobs for a binary network"** (`a:claim:degree-four`, after Definition 10). The degree of a node of the tree of blobs is `cutDegree`, by `nodeDegree_bridgeQuotient`. -/
theorem not_isTrivialBlob_of_four_le_cutDegree (hN : IsBinaryNetwork N) {b : N.graph.BlobVertex} (hb : 4 ≤ cutDegree N.graph b) : ¬ IsTrivialBlob N.graph b := by
  obtain ⟨v, rfl⟩ := Quotient.exists_rep b
  intro h
  have h1 := cutDegree_of_isTrivialBlob hN.isPhylogenetic h
  have h2 := nodeDegree_le_three hN v
  change 4 ≤ cutDegree N.graph (blobOf N.graph v) at hb
  omega

/-! ### Trees -/

/-- A *tree*: a network with no hybrid node. -/
def IsTreeNetwork (N : RootedNetwork V E X) : Prop := ∀ v, N.graph.indegree v ≤ 1

/-- **On a tree every edge is a cut edge**: only it crosses the set of nodes below it. -/
theorem isBridge_of_isTreeNetwork (hN : N.IsPhylogenetic) (ht : IsTreeNetwork N) (e : E) : N.graph.underlying.IsBridge e := by
  have : Finite E := hN.finite_arcs
  have huniq : ∀ {f g : E}, N.graph.target f = N.graph.target g → f = g := by
    intro f g hfg
    have := (Set.ncard_le_one (Set.toFinite _)).1 (ht (N.graph.target g))
    exact this f hfg g rfl
  refine (N.graph.isBridge_iff e).2 ⟨{u | N.graph.Reaches (N.graph.target e) u}, fun f => ?_⟩
  constructor
  · rintro (⟨h₁, h₂⟩ | ⟨h₁, h₂⟩)
    · exact absurd (Relation.ReflTransGen.tail h₁ ⟨f, rfl, rfl⟩) h₂
    · rcases Relation.ReflTransGen.cases_tail h₁ with h | ⟨c, hc, g, hgc, hgt⟩
      · exact huniq h
      · have hfg : f = g := huniq hgt.symm
        subst hfg
        exact absurd (hgc ▸ hc) h₂
  · rintro rfl
    exact Or.inr ⟨.refl, not_reaches_target_source hN.acyclic f⟩

/-- **On a tree every blob is a node.** -/
theorem blobOf_eq_iff_of_isTreeNetwork (hN : N.IsPhylogenetic) (ht : IsTreeNetwork N) {u w : V} : blobOf N.graph u = blobOf N.graph w ↔ u = w := by
  rw [← sameBlobIn_univ_iff]
  constructor
  · intro h
    induction h with
    | refl => rfl
    | tail _ hstep ih =>
      obtain ⟨f, hf, -⟩ := hstep
      exact absurd (isCutIn_univ_iff.2 (isBridge_of_isTreeNetwork hN ht f)) hf.2
  · rintro rfl
    exact .refl

theorem isTrivialBlob_of_isTreeNetwork (hN : N.IsPhylogenetic) (ht : IsTreeNetwork N) (v : V) : IsTrivialBlob N.graph (blobOf N.graph v) :=
  ⟨v, Set.eq_singleton_iff_unique_mem.2 ⟨rfl, fun _ hw => (blobOf_eq_iff_of_isTreeNetwork hN ht).1 hw⟩⟩

/-- **"Leaves are the only 1-blobs"** (`a:claim:tree-blobs`, after Definition 7), on a rooted binary phylogenetic tree. -/
theorem blobDegree_eq_one_iff_of_isTreeNetwork (hN : IsBinaryNetwork N) (ht : IsTreeNetwork N) (v : V) :
    blobDegree N (blobOf N.graph v) = 1 ↔ ∃ x, N.leaf x = v := by
  have hP := hN.isPhylogenetic
  rw [blobDegree_of_isTrivialBlob hP (isTrivialBlob_of_isTreeNetwork hP ht v)]
  rcases hN.node_cases v with rfl | ⟨x, rfl⟩ | h | h
  · rw [ite_eq_left rfl, nodeDegree, hN.root_in, hN.root_out]
    constructor
    · omega
    · rintro ⟨x, hx⟩
      have := hN.leaf_in x
      rw [hx, hN.root_in] at this
      omega
  · have hne : N.leaf x ≠ N.root := fun h => by
      have := hN.leaf_in x
      rw [h, hN.root_in] at this
      omega
    rw [ite_eq_right hne, nodeDegree, hN.leaf_in, hN.leaf_out]
    exact ⟨fun _ => ⟨x, rfl⟩, fun _ => rfl⟩
  · have hne : v ≠ N.root := by
      rintro rfl
      have := h.1
      rw [hN.root_in] at this
      omega
    rw [ite_eq_right hne, nodeDegree, h.1, h.2]
    constructor
    · omega
    · rintro ⟨x, rfl⟩
      have h1 := hN.leaf_out x
      have h2 := h.2
      omega
  · have h1 := ht v
    have h2 := h.1
    omega

/-- **"The root and internal nodes are 3-blobs"** (`a:claim:tree-blobs`, after Definition 7), on a rooted binary phylogenetic tree. -/
theorem blobDegree_eq_three_of_isTreeNetwork (hN : IsBinaryNetwork N) (ht : IsTreeNetwork N) {v : V} (hl : ∀ x, N.leaf x ≠ v) :
    blobDegree N (blobOf N.graph v) = 3 := by
  have hP := hN.isPhylogenetic
  rw [blobDegree_of_isTrivialBlob hP (isTrivialBlob_of_isTreeNetwork hP ht v)]
  rcases hN.node_cases v with rfl | ⟨x, rfl⟩ | h | h
  · rw [ite_eq_left rfl, nodeDegree, hN.root_in, hN.root_out]
  · exact absurd rfl (hl x)
  · have hne : v ≠ N.root := by
      rintro rfl
      have := h.1
      rw [hN.root_in] at this
      omega
    rw [ite_eq_right hne, nodeDegree, h.1, h.2]
  · have h1 := ht v
    have h2 := h.1
    omega

/-- **"On a non-binary tree, polytomous nodes are `k`-blobs with `k ≥ 4`"** (`a:claim:tree-blobs`, after Definition 7): a node of a tree with at least three children. -/
theorem four_le_blobDegree_of_isTreeNetwork (hN : N.IsPhylogenetic) (ht : IsTreeNetwork N) {v : V} (h3 : 3 ≤ N.graph.outdegree v) :
    4 ≤ blobDegree N (blobOf N.graph v) := by
  rw [blobDegree_of_isTrivialBlob hN (isTrivialBlob_of_isTreeNetwork hN ht v)]
  by_cases hv : v = N.root
  · rw [ite_eq_left hv, nodeDegree]
    omega
  · rw [ite_eq_right hv, nodeDegree]
    have := hN.nonroot_indegree v hv
    omega

/-- **"As is well known, on a tree any 3 taxa determine a unique node"** (`a:claim:tree-three`, before Definition 8). -/
theorem existsUnique_node_of_isTreeNetwork (hN : IsBinaryNetwork N) (ht : IsTreeNetwork N) {S : Finset X} (h3 : S.card = 3) :
    ∃! v, IsDeterminedBy N.graph N.leaf (blobOf N.graph v) S := by
  obtain ⟨b, hb, huniq⟩ := existsUnique_isDeterminedBy_three hN h3
  obtain ⟨v, rfl⟩ := Quotient.exists_rep b
  exact ⟨v, hb, fun w hw => (blobOf_eq_iff_of_isTreeNetwork hN.isPhylogenetic ht).1 (huniq _ hw)⟩

/-! ### Two cycles at a node -/

/-- **"If two cycles share only a node as in Fig. 2R ... Our restriction to binary networks rules out this possibility regardless"** (`a:claim:cycles-share-edge`, after Definition 8). A cycle uses two edges at each of its nodes, and a node of a binary network has at most three: two sets of edges that each have two edges at a node have an edge in common. -/
theorem exists_mem_inter_of_two_incident (hN : IsBinaryNetwork N) {C₁ C₂ : Set E} {v : V} {e₁ e₁' e₂ e₂' : E} (h₁ : e₁ ∈ C₁) (h₁' : e₁' ∈ C₁) (hne₁ : e₁ ≠ e₁') (h₂ : e₂ ∈ C₂) (h₂' : e₂' ∈ C₂)
    (hne₂ : e₂ ≠ e₂') (hv₁ : e₁ ∈ edgesAt N v) (hv₁' : e₁' ∈ edgesAt N v) (hv₂ : e₂ ∈ edgesAt N v) (hv₂' : e₂' ∈ edgesAt N v) : ∃ f, f ∈ C₁ ∧ f ∈ C₂ := by
  have hP := hN.isPhylogenetic
  have : Finite E := hP.finite_arcs
  by_contra hno
  have hsep : ∀ {f g : E}, f ∈ C₁ → g ∈ C₂ → f ≠ g := fun hf hg h => hno ⟨_, hf, h ▸ hg⟩
  have hcard : ({e₁, e₁', e₂, e₂'} : Finset E).card = 4 := by
    rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_pair hne₂]
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨hsep h₁' h₂, hsep h₁' h₂'⟩
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨hne₁, hsep h₁ h₂, hsep h₁ h₂'⟩
  have hle : ((({e₁, e₁', e₂, e₂'} : Finset E) : Set E)).ncard ≤ (edgesAt N v).ncard := by
    refine Set.ncard_le_ncard (fun f hf => ?_) (Set.toFinite _)
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff, Set.mem_singleton_iff] at hf
    rcases hf with rfl | rfl | rfl | rfl <;> assumption
  rw [Set.ncard_coe_finset, hcard, ncard_edgesAt hP] at hle
  have := nodeDegree_le_three hN v
  omega

/-! ### Level-1 networks above the LSA -/

/-- The degree of a node that isn't a leaf. -/
theorem nodeDegree_of_ne_leaf (hN : IsBinaryNetwork N) {v : V} (hl : ∀ x, N.leaf x ≠ v) : nodeDegree N.graph v = if v = N.root then 2 else 3 := by
  rcases hN.node_cases v with rfl | ⟨x, rfl⟩ | h | h
  · rw [ite_eq_left rfl, nodeDegree, hN.root_in, hN.root_out]
  · exact absurd rfl (hl x)
  · have hne : v ≠ N.root := by
      rintro rfl
      have := h.1
      rw [hN.root_in] at this
      omega
    rw [ite_eq_right hne, nodeDegree, h.1, h.2]
  · have hne : v ≠ N.root := by
      rintro rfl
      have := h.1
      rw [hN.root_in] at this
      omega
    rw [ite_eq_right hne, nodeDegree, h.1, h.2]

/-- The degree of a leaf. -/
theorem nodeDegree_leaf_eq_one (hN : IsBinaryNetwork N) (x : X) : nodeDegree N.graph (N.leaf x) = 1 := by
  rw [nodeDegree, hN.leaf_in, hN.leaf_out]

/-- A node of a non-trivial blob has at least two edges of the blob. -/
theorem two_le_ncard_of_not_isTrivialBlob (hN : N.IsPhylogenetic) {v : V} (hv : ¬ IsTrivialBlob N.graph (blobOf N.graph v)) :
    2 ≤ {e | e ∈ edgesAt N v ∧ ¬ N.graph.underlying.IsBridge e}.ncard := by
  have : Finite E := hN.finite_arcs
  by_contra hlt
  have hle : {e | e ∈ edgesAt N v ∧ ¬ N.graph.underlying.IsBridge e}.ncard ≤ 1 := by omega
  have huniq := (Set.ncard_le_one (Set.toFinite _)).1 hle
  -- an edge of the blob at `v`
  have hex : ∃ x, blobOf N.graph x = blobOf N.graph v ∧ x ≠ v := by
    by_contra hno
    push Not at hno
    exact hv ⟨v, Set.eq_singleton_iff_unique_mem.2 ⟨rfl, fun w hw => hno w hw⟩⟩
  obtain ⟨x, hx, hxv⟩ := hex
  have hw : SameBlobIn N.graph Set.univ v x := sameBlobIn_univ_iff.2 hx.symm
  obtain ⟨f, hfat, hfb⟩ : ∃ f, f ∈ edgesAt N v ∧ ¬ N.graph.underlying.IsBridge f := by
    rcases Relation.ReflTransGen.cases_head hw with h | ⟨c, ⟨f, hf, hfe⟩, -⟩
    · exact absurd h.symm hxv
    · refine ⟨f, ?_, fun hb => hf.2 (isCutIn_univ_iff.2 hb)⟩
      rcases hfe with ⟨h1, -⟩ | ⟨-, h1⟩
      · exact Or.inl h1
      · exact Or.inr h1
  have hother : ∀ g ∈ edgesAt N v, g ≠ f → N.graph.underlying.IsBridge g := fun g hg hne => by
    by_contra hb
    exact hne (huniq g ⟨hg, hb⟩ f ⟨hfat, hfb⟩)
  -- the other edges at `v` are cut edges, so what `v` reaches without `f` is `v` and beyond them
  have hside : ∀ g ∈ edgesAt N v, g ≠ f → ∃ S : Set V, v ∉ S ∧ ∀ h, N.graph.Crosses h S ↔ h = g := by
    intro g hg hne
    obtain ⟨S, hS⟩ := (N.graph.isBridge_iff g).1 (hother g hg hne)
    by_cases hvS : v ∈ S
    · exact ⟨Sᶜ, fun h => h hvS, fun h => (N.graph.crosses_compl h S).trans (hS h)⟩
    · exact ⟨S, hvS, hS⟩
  have hinv : ∀ y, N.graph.Walks {f}ᶜ v y → y = v ∨ ∃ g S, g ∈ edgesAt N v ∧ g ≠ f ∧ v ∉ S ∧ (∀ h, N.graph.Crosses h S ↔ h = g) ∧ y ∈ S := by
    intro y hy
    induction hy with
    | refl => exact Or.inl rfl
    | @tail y z _ hstep ih =>
      obtain ⟨h, hhf, hhe⟩ := hstep
      have hhf' : h ≠ f := fun e => hhf (Set.mem_singleton_iff.2 e)
      rcases ih with rfl | ⟨g, S, hg, hgf, hvS, hS, hyS⟩
      · have hat : h ∈ edgesAt N y := by
          rcases hhe with ⟨h1, -⟩ | ⟨-, h1⟩
          · exact Or.inl h1
          · exact Or.inr h1
        obtain ⟨S, hvS, hS⟩ := hside h hat hhf'
        refine Or.inr ⟨h, S, hat, hhf', hvS, hS, ?_⟩
        rcases (hS h).2 rfl with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rcases hhe with ⟨h3, h4⟩ | ⟨h3, h4⟩
        · exact absurd (h3 ▸ h1) hvS
        · exact h3 ▸ h1
        · exact h4 ▸ h1
        · exact absurd (h4 ▸ h1) hvS
      · by_cases hzS : z ∈ S
        · exact Or.inr ⟨g, S, hg, hgf, hvS, hS, hzS⟩
        · refine Or.inl ?_
          have hcr : N.graph.Crosses h S := by
            rcases hhe with ⟨h3, h4⟩ | ⟨h3, h4⟩
            · exact Or.inl ⟨h3 ▸ hyS, h4 ▸ hzS⟩
            · exact Or.inr ⟨h4 ▸ hyS, h3 ▸ hzS⟩
          have hhg := (hS h).1 hcr
          subst hhg
          rcases hg with h1 | h1 <;> rcases hhe with ⟨h3, h4⟩ | ⟨h3, h4⟩
          · exact absurd ((h3.symm.trans h1) ▸ hyS) hvS
          · exact h3.symm.trans h1
          · exact h4.symm.trans h1
          · exact absurd ((h4.symm.trans h1) ▸ hyS) hvS
  -- the other end of `f`
  have hwalk := (N.graph.isBridge_iff_not_walks_delete f)
  have hnb : N.graph.Walks {f}ᶜ (N.graph.source f) (N.graph.target f) := by
    by_contra hno
    exact hfb (hwalk.2 hno)
  have hne := NMSC.source_ne_target hN f
  have hfin : ∀ y, y ≠ v → N.graph.Walks {f}ᶜ v y → (N.graph.source f = v ∧ N.graph.target f = y ∨ N.graph.target f = v ∧ N.graph.source f = y) → False := by
    intro y hyv hy hends
    rcases hinv y hy with h | ⟨g, S, -, hgf, hvS, hS, hyS⟩
    · exact hyv h
    · refine hgf ((hS f).1 ?_).symm
      rcases hends with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Or.inr ⟨h2 ▸ hyS, h1 ▸ hvS⟩
      · exact Or.inl ⟨h2 ▸ hyS, h1 ▸ hvS⟩
  rcases hfat with h1 | h1
  · exact hfin _ (fun h => hne (h1.trans h.symm)) (h1 ▸ hnb) (Or.inl ⟨h1, rfl⟩)
  · exact hfin _ (fun h => hne (h.trans h1.symm)) (h1 ▸ N.graph.walks_symm hnb) (Or.inr ⟨h1, rfl⟩)

/-- **A network with one hybrid node, of in-degree at most two, is level-1**, in the library's sense. -/
theorem isLevelOne_of_unique_hybrid [Fintype V] [Fintype E] {h : V} (hh : ∀ u, 2 ≤ N.graph.indegree u → u = h) (h2 : N.graph.indegree h ≤ 2) : N.IsLevelOne := by
  intro v
  set A := Finset.univ.filter fun e => N.IsHybridArc e ∧ N.graph.blobSetoid v (N.graph.source e) ∧ N.graph.blobSetoid v (N.graph.target e) with hA
  set B := Finset.univ.filter fun u => 2 ≤ N.graph.indegree u ∧ N.graph.blobSetoid v u with hB
  by_cases hne : A.Nonempty
  · obtain ⟨e, he⟩ := hne
    obtain ⟨he₁, -, he₂⟩ := (Finset.mem_filter.1 he).2
    have hte : N.graph.target e = h := hh _ he₁
    have hB1 : 1 ≤ B.card := Finset.card_pos.2 ⟨h, Finset.mem_filter.2 ⟨Finset.mem_univ _, hte ▸ he₁, hte ▸ he₂⟩⟩
    have hA2 : A.card ≤ 2 := by
      have hsub : (A : Set E) ⊆ {e | N.graph.target e = h} := fun f hf =>
        hh _ (Finset.mem_filter.1 (Finset.mem_coe.1 hf)).2.1
      have := Set.ncard_le_ncard hsub (Set.toFinite _)
      rw [Set.ncard_coe_finset] at this
      exact this.trans h2
    have h1 : (A.card : ℤ) ≤ 2 := by exact_mod_cast hA2
    have h3 : (1 : ℤ) ≤ B.card := by exact_mod_cast hB1
    change (A.card : ℤ) - B.card ≤ 1
    omega
  · rw [Finset.not_nonempty_iff_eq_empty] at hne
    change (A.card : ℤ) - B.card ≤ 1
    rw [hne]
    simp only [Finset.card_empty, Nat.cast_zero, zero_sub]
    have : (0 : ℤ) ≤ B.card := by positivity
    omega

/-- **On a binary level-1 network, in the library's sense, each node of a non-trivial blob has exactly two edges of the blob**: "the simplest blobs have the form of cycles, and a network with only such blobs is level-1". In a blob, the edges number at most the nodes: each node has at most one edge coming in, except the hybrid node, of which there is at most one, with two, and there is a node with none. And each node has at least two edges of the blob. -/
theorem ncard_edges_of_isLevelOne [Fintype V] [Fintype E] (hN : IsBinaryNetwork N) (hL : N.IsLevelOne) {v₀ : V} (hv₀ : ¬ IsTrivialBlob N.graph (blobOf N.graph v₀)) :
    {e | e ∈ edgesAt N v₀ ∧ ¬ N.graph.underlying.IsBridge e}.ncard = 2 := by
  have hP := hN.isPhylogenetic
  set b := blobOf N.graph v₀ with hb
  let W : Finset V := Finset.univ.filter fun u => blobOf N.graph u = b
  let Eb : Finset E := Finset.univ.filter fun e => ¬ N.graph.underlying.IsBridge e ∧ blobOf N.graph (N.graph.source e) = b
  have hends : ∀ {e : E}, e ∈ Eb → N.graph.source e ∈ W ∧ N.graph.target e ∈ W := by
    intro e he
    obtain ⟨h1, h2⟩ := (Finset.mem_filter.1 he).2
    refine ⟨Finset.mem_filter.2 ⟨Finset.mem_univ _, h2⟩, Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩⟩
    have hq : blobOf N.graph (N.graph.source e) = blobOf N.graph (N.graph.target e) := N.graph.quotient_eq_of_not_isBridge h1
    rw [← hq]
    exact h2
  let inC : V → ℕ := fun u => (Eb.filter fun e => N.graph.target e = u).card
  let outC : V → ℕ := fun u => (Eb.filter fun e => N.graph.source e = u).card
  have hsumIn : ∑ u ∈ W, inC u = Eb.card := (Finset.card_eq_sum_card_fiberwise fun e he => (hends he).2).symm
  have hsumOut : ∑ u ∈ W, outC u = Eb.card := (Finset.card_eq_sum_card_fiberwise fun e he => (hends he).1).symm
  -- the edges of the blob at a node
  have hdeg : ∀ u ∈ W, {e | e ∈ edgesAt N u ∧ ¬ N.graph.underlying.IsBridge e}.ncard = inC u + outC u := by
    intro u hu
    have huW : blobOf N.graph u = b := (Finset.mem_filter.1 hu).2
    have hset : {e | e ∈ edgesAt N u ∧ ¬ N.graph.underlying.IsBridge e} = ((Eb.filter fun e => N.graph.target e = u) ∪ (Eb.filter fun e => N.graph.source e = u) : Finset E) := by
      ext e
      simp only [Set.mem_ofPred_eq, edgesAt, Finset.coe_union, Finset.coe_filter, Set.mem_union, Eb, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨h1 | h1, h2⟩
        · exact Or.inr ⟨⟨h2, h1 ▸ huW⟩, h1⟩
        · refine Or.inl ⟨⟨h2, ?_⟩, h1⟩
          have hq : blobOf N.graph (N.graph.source e) = blobOf N.graph (N.graph.target e) := N.graph.quotient_eq_of_not_isBridge h2
          rw [hq, h1]
          exact huW
      · rintro (⟨⟨h1, -⟩, h2⟩ | ⟨⟨h1, -⟩, h2⟩)
        · exact ⟨Or.inr h2, h1⟩
        · exact ⟨Or.inl h2, h1⟩
    rw [hset, Set.ncard_coe_finset, Finset.card_union_of_disjoint]
    refine Finset.disjoint_left.2 fun e h₁ h₂ => NMSC.source_ne_target hP e ?_
    exact (Finset.mem_filter.1 h₂).2.trans (Finset.mem_filter.1 h₁).2.symm
  -- at most one hybrid node
  let hyb : Finset V := W.filter fun u => 2 ≤ N.graph.indegree u
  have hhyb2 : ∀ u ∈ hyb, N.graph.indegree u = 2 := by
    intro u hu
    have h2 := (Finset.mem_filter.1 hu).2
    rcases hN.node_cases u with rfl | ⟨x, rfl⟩ | h | h
    · rw [hN.root_in] at h2
      omega
    · rw [hN.leaf_in] at h2
      omega
    · rw [h.1] at h2
      omega
    · exact h.1
  have harcs : ∀ u ∈ hyb, ∀ e, N.graph.target e = u → e ∈ Eb := by
    intro u hu e he
    have huW := (Finset.mem_filter.1 (Finset.mem_filter.1 hu).1).2
    have hhe : IsHybridEdge N e := by
      have h2 := hhyb2 u hu
      rcases hN.node_cases u with rfl | ⟨x, rfl⟩ | h | h
      · rw [hN.root_in] at h2
        omega
      · rw [hN.leaf_in] at h2
        omega
      · rw [h.1] at h2
        omega
      · change IsHybridNode N _
        rw [he]
        exact h
    have hnb := InPassing.not_isBridge_of_isHybridEdge hN hhe
    refine Finset.mem_filter.2 ⟨Finset.mem_univ _, hnb, ?_⟩
    have hq : blobOf N.graph (N.graph.source e) = blobOf N.graph (N.graph.target e) := N.graph.quotient_eq_of_not_isBridge hnb
    rw [hq, he]
    exact huW
  have hin : ∀ u ∈ hyb, inC u = 2 := by
    intro u hu
    have h2 := hhyb2 u hu
    have hfil : ((Eb.filter fun e => N.graph.target e = u : Finset E) : Set E) = {e | N.graph.target e = u} := by
      ext e
      simp only [Finset.coe_filter, Set.mem_ofPred_eq]
      exact ⟨fun h => h.2, fun h => ⟨harcs u hu e h, h⟩⟩
    change (Eb.filter fun e => N.graph.target e = u).card = 2
    rw [← Set.ncard_coe_finset, hfil]
    exact h2
  have hhyb : hyb.card ≤ 1 := by
    have hlev := hL v₀
    set A := Finset.univ.filter fun e => N.IsHybridArc e ∧ N.graph.blobSetoid v₀ (N.graph.source e) ∧ N.graph.blobSetoid v₀ (N.graph.target e) with hA
    set B := Finset.univ.filter fun u => 2 ≤ N.graph.indegree u ∧ N.graph.blobSetoid v₀ u with hB
    have hrel : ∀ u, N.graph.blobSetoid v₀ u ↔ blobOf N.graph u = b := fun u =>
      ⟨fun h => (Quotient.sound h).symm, fun h => Quotient.exact h.symm⟩
    have hBeq : B = hyb := by
      ext u
      simp only [hB, hyb, W, Finset.mem_filter, Finset.mem_univ, true_and, hrel]
      tauto
    have hAge : 2 * hyb.card ≤ A.card := by
      have hmaps : ∀ e ∈ A.filter (fun e => N.graph.target e ∈ hyb), N.graph.target e ∈ hyb := fun e he => (Finset.mem_filter.1 he).2
      have hsum := Finset.card_eq_sum_card_fiberwise hmaps
      have hval : ∀ u ∈ hyb, ((A.filter fun e => N.graph.target e ∈ hyb).filter fun e => N.graph.target e = u).card = 2 := by
        intro u hu
        have h2 := hhyb2 u hu
        have hfil : (((A.filter fun e => N.graph.target e ∈ hyb).filter fun e => N.graph.target e = u : Finset E) : Set E) = {e | N.graph.target e = u} := by
          ext e
          simp only [Finset.coe_filter, Finset.mem_filter, Set.mem_ofPred_eq]
          constructor
          · exact fun h => h.2
          · intro he
            refine ⟨⟨?_, he ▸ hu⟩, he⟩
            have hmem := harcs u hu e he
            have hEb := (Finset.mem_filter.1 hmem).2
            have htarget : blobOf N.graph (N.graph.target e) = b := (Finset.mem_filter.1 (hends hmem).2).2
            refine Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_, (hrel _).2 hEb.2, (hrel _).2 htarget⟩
            change 2 ≤ N.graph.indegree (N.graph.target e)
            rw [he, h2]
        rw [← Set.ncard_coe_finset, hfil]
        exact h2
      rw [Finset.sum_congr rfl hval, Finset.sum_const, smul_eq_mul] at hsum
      have hle := Finset.card_filter_le A fun e => N.graph.target e ∈ hyb
      omega
    rw [hBeq] at hlev
    have h1 : (2 * hyb.card : ℤ) ≤ A.card := by exact_mod_cast hAge
    change (A.card : ℤ) - hyb.card ≤ 1 at hlev
    have : (hyb.card : ℤ) ≤ 1 := by omega
    exact_mod_cast this
  -- a node with no edge of the blob coming in
  have hWne : W.Nonempty := ⟨v₀, Finset.mem_filter.2 ⟨Finset.mem_univ _, rfl⟩⟩
  obtain ⟨u₀, hu₀, hmin⟩ : ∃ u₀ ∈ W, ∀ e ∈ Eb, N.graph.target e ≠ u₀ := by
    let r : V → V → Prop := fun x y => Relation.TransGen N.graph.Adj x y
    have : IsTrans V r := ⟨fun _ _ _ h h' => h.trans h'⟩
    have : Std.Irrefl r := ⟨fun x h => hP.acyclic x h⟩
    have : Finite V := hP.finite_vertices
    have hwf : WellFounded r := Finite.wellFounded_of_trans_of_irrefl r
    obtain ⟨m, hm, hmm⟩ := hwf.has_min (W : Set V) hWne
    refine ⟨m, Finset.mem_coe.1 hm, fun e he hte => ?_⟩
    exact hmm _ (Finset.mem_coe.2 (hends he).1) (.single ⟨e, rfl, hte⟩)
  have hin0 : inC u₀ = 0 := by
    refine Finset.card_eq_zero.2 (Finset.filter_eq_empty_iff.2 fun e he => hmin e he)
  have hle1 : ∀ u ∈ W, u ∉ hyb → inC u ≤ 1 := by
    intro u _ huh
    have huW : u ∈ W := by assumption
    have hdegin : N.graph.indegree u ≤ 1 := by
      by_contra hno
      exact huh (Finset.mem_filter.2 ⟨huW, by omega⟩)
    have hsub : ((Eb.filter fun e => N.graph.target e = u : Finset E) : Set E) ⊆ {e | N.graph.target e = u} := fun e he => (Finset.mem_filter.1 (Finset.mem_coe.1 he)).2
    have := Set.ncard_le_ncard hsub (Set.toFinite _)
    rw [Set.ncard_coe_finset] at this
    exact this.trans hdegin
  have hEle : Eb.card ≤ W.card := by
    have hpt : ∀ u ∈ W, inC u + (if u = u₀ then 1 else 0) ≤ 1 + (if u ∈ hyb then 1 else 0) := by
      intro u hu
      by_cases hh : u ∈ hyb
      · rw [ite_eq_left hh, hin u hh]
        have huu₀ : u ≠ u₀ := fun e => by
          have := hin u hh
          rw [e, hin0] at this
          omega
        rw [ite_eq_right huu₀]
      · rw [ite_eq_right hh]
        by_cases hu0 : u = u₀
        · rw [ite_eq_left hu0, hu0, hin0]
        · rw [ite_eq_right hu0]
          have := hle1 u hu hh
          omega
    have hs := Finset.sum_le_sum hpt
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, hsumIn, Finset.sum_ite_eq' W u₀, ite_eq_left hu₀, Finset.sum_const, smul_eq_mul, mul_one] at hs
    have hhf : ∑ u ∈ W, (if u ∈ hyb then 1 else 0) = hyb.card := by
      rw [Finset.sum_boole]
      simp only [Nat.cast_id]
      congr 1
      ext u
      simp only [Finset.mem_filter, hyb]
      tauto
    rw [hhf] at hs
    omega
  -- each node has exactly two
  have hge : ∀ u ∈ W, 2 ≤ inC u + outC u := by
    intro u hu
    rw [← hdeg u hu]
    refine two_le_ncard_of_not_isTrivialBlob hP ?_
    rw [(Finset.mem_filter.1 hu).2]
    exact hv₀
  have hmem₀ : v₀ ∈ W := Finset.mem_filter.2 ⟨Finset.mem_univ _, rfl⟩
  rw [hdeg v₀ hmem₀]
  by_contra hne
  have hlt : ∑ u ∈ W, 2 < ∑ u ∈ W, (inC u + outC u) := by
    refine Finset.sum_lt_sum hge ⟨v₀, hmem₀, ?_⟩
    have := hge v₀ hmem₀
    omega
  rw [Finset.sum_add_distrib, hsumIn, hsumOut, Finset.sum_const, smul_eq_mul] at hlt
  omega

section Level

variable (hN : IsBinaryNetwork N) (hX : Nontrivial X)

include hN hX

/-- **"(If the network is level-1, this is a chain of 2-cycles, as discussed in Banos 2019)"** (`a:claim:level1-above-lsa`, after Definition 4). On a level-1 network, a blob above the LSA has exactly two nodes. By `blobDegree_eq_two_of_isAboveLSA` it has degree 2, and each of its nodes other than the root has exactly one cut edge. -/
theorem ncard_blobNodes_of_isAboveLSA [Fintype V] [Fintype E] (hL : N.IsLevelOne) {b : N.graph.BlobVertex} (hb : IsAboveLSA hN hX b) : (blobNodes N.graph b).ncard = 2 := by
  have hP := hN.isPhylogenetic
  have : Finite E := hP.finite_arcs
  have : Finite V := hP.finite_vertices
  have hdeg := blobDegree_eq_two_of_isAboveLSA hN hX hb
  obtain ⟨v₀, rfl, hv₀⟩ := hb
  -- the blob isn't trivial
  have hnt : ¬ IsTrivialBlob N.graph (blobOf N.graph v₀) := by
    intro htr
    rw [blobDegree_of_isTrivialBlob hP htr] at hdeg
    by_cases hleaf : ∃ x, N.leaf x = v₀
    · obtain ⟨x, rfl⟩ := hleaf
      have hne : N.leaf x ≠ N.root := fun h => by
        have := hN.leaf_in x
        rw [h, hN.root_in] at this
        omega
      rw [ite_eq_right hne, nodeDegree_leaf_eq_one hN] at hdeg
      omega
    · have h3 := nodeDegree_of_ne_leaf hN (fun x hx => hleaf ⟨x, hx⟩)
      split_ifs at hdeg h3 <;> omega
  set W := blobNodes N.graph (blobOf N.graph v₀) with hW
  -- the cut edges at a node of the blob
  let cut : V → Finset E := fun u => (Set.toFinite {e | e ∈ edgesAt N u ∧ N.graph.underlying.IsBridge e}).toFinset
  have hcutmem : ∀ {u : V} {e : E}, e ∈ cut u ↔ e ∈ edgesAt N u ∧ N.graph.underlying.IsBridge e := by
    intro u e
    simp only [cut, Set.Finite.mem_toFinset, Set.mem_ofPred_eq]
  have hcard : ∀ u ∈ W, (cut u).card = if u = N.root then 0 else 1 := by
    intro u hu
    have hnt' : ¬ IsTrivialBlob N.graph (blobOf N.graph u) := by
      have hu' : blobOf N.graph u = blobOf N.graph v₀ := hu
      rw [hu']
      exact hnt
    have h2 := ncard_edges_of_isLevelOne hN hL hnt'
    have hsplit : edgesAt N u = {e | e ∈ edgesAt N u ∧ ¬ N.graph.underlying.IsBridge e} ∪ {e | e ∈ edgesAt N u ∧ N.graph.underlying.IsBridge e} := by
      ext e
      simp only [Set.mem_union, Set.mem_ofPred_eq]
      by_cases h : N.graph.underlying.IsBridge e <;> simp [h]
    have hn := ncard_edgesAt hP u
    rw [hsplit, Set.ncard_union_eq _ (Set.toFinite _) (Set.toFinite _), h2] at hn
    · have hc : (cut u).card = {e | e ∈ edgesAt N u ∧ N.graph.underlying.IsBridge e}.ncard :=
        (Set.ncard_eq_toFinset_card _ (Set.toFinite _)).symm
      rw [hc]
      have hnl : ∀ x, N.leaf x ≠ u := by
        rintro x rfl
        rw [nodeDegree_leaf_eq_one hN] at hn
        omega
      rw [nodeDegree_of_ne_leaf hN hnl] at hn
      split_ifs at hn ⊢ <;> omega
    · refine Set.disjoint_left.2 fun e h₁ h₂ => h₁.2 h₂.2
  -- the incident cut edges are the union
  let W' : Finset V := (Set.toFinite W).toFinset
  have hW' : ∀ {u : V}, u ∈ W' ↔ blobOf N.graph u = blobOf N.graph v₀ := by
    intro u
    simp only [W', Set.Finite.mem_toFinset]
    rfl
  have hunion : incidentCutEdges N.graph (blobOf N.graph v₀) = ((W'.biUnion cut : Finset E) : Set E) := by
    ext e
    simp only [incidentCutEdges, IsIncidentToBlob, Set.mem_ofPred_eq, Finset.coe_biUnion, Set.mem_iUnion, Finset.mem_coe, hcutmem, exists_prop]
    constructor
    · rintro ⟨hbr, (⟨h, -⟩ | ⟨h, -⟩)⟩
      · exact ⟨_, hW'.2 h, Or.inl rfl, hbr⟩
      · exact ⟨_, hW'.2 h, Or.inr rfl, hbr⟩
    · rintro ⟨u, hu, hat, hbr⟩
      refine ⟨hbr, ?_⟩
      have hne := blobOf_source_ne_target hbr
      have hu' := hW'.1 hu
      rcases hat with rfl | rfl
      · exact Or.inl ⟨hu', fun h => hne (hu'.trans h.symm)⟩
      · exact Or.inr ⟨hu', fun h => hne (h.trans hu'.symm)⟩
  have hdisj : ((W' : Set V)).PairwiseDisjoint cut := by
    intro u hu u' hu' hne
    refine Finset.disjoint_left.2 fun e h₁ h₂ => ?_
    obtain ⟨hat, hbr⟩ := hcutmem.1 h₁
    obtain ⟨hat', -⟩ := hcutmem.1 h₂
    have hne' := blobOf_source_ne_target hbr
    have e₁ := hW'.1 (Finset.mem_coe.1 hu)
    have e₂ := hW'.1 (Finset.mem_coe.1 hu')
    rcases hat with rfl | rfl <;> rcases hat' with h' | h'
    · exact hne h'
    · exact hne' (e₁.trans (h' ▸ e₂).symm)
    · exact hne' ((h' ▸ e₂).trans e₁.symm)
    · exact hne h'
  have hcd : cutDegree N.graph (blobOf N.graph v₀) = (W'.filter fun u => u ≠ N.root).card := by
    rw [cutDegree, hunion, Set.ncard_coe_finset, Finset.card_biUnion hdisj, Finset.card_filter]
    refine Finset.sum_congr rfl fun u hu => ?_
    rw [hcard u (hW'.1 hu)]
    by_cases h : u = N.root <;> simp [h]
  have hWcard : W.ncard = W'.card := Set.ncard_eq_toFinset_card _ (Set.toFinite _)
  rw [hWcard]
  unfold blobDegree at hdeg
  rw [hcd] at hdeg
  by_cases hr : blobOf N.graph N.root = blobOf N.graph v₀
  · rw [ite_eq_left hr] at hdeg
    have hmem : N.root ∈ W' := hW'.2 hr
    have hfe : (W'.filter fun u => u ≠ N.root) = W'.erase N.root := by
      ext u
      simp only [Finset.mem_filter, Finset.mem_erase]
      tauto
    rw [hfe, Finset.card_erase_of_mem hmem] at hdeg
    have := Finset.card_pos.2 ⟨_, hmem⟩
    omega
  · rw [ite_eq_right hr] at hdeg
    have hfe : (W'.filter fun u => u ≠ N.root) = W' := by
      refine Finset.filter_true_of_mem fun u hu h => hr ?_
      rw [← h]
      exact hW'.1 hu
    rw [hfe] at hdeg
    exact hdeg

end Level

/-! ### A network whose taxa cannot be reduced -/

section Separated

variable {b c : N.graph.BlobVertex}

/-- Two nodes of a blob are joined without the cut edges at any blob. -/
theorem walks_compl_of_blobOf_eq (b' : N.graph.BlobVertex) {x y : V} (h : blobOf N.graph x = blobOf N.graph y) : N.graph.Walks (incidentCutEdges N.graph b')ᶜ x y := by
  refine walks_mono (fun f hf => ?_) (sameBlobIn_univ_iff.2 h)
  intro hinc
  exact hf.2 (isCutIn_univ_iff.2 hinc.1)

/-- **A blob other than `b` isn't determined by three taxa, when each component of what remains of `𝒩⁺` without the cut edges at `b` has at most one taxon.** At most one of the three taxa is on the side of `b`, and the two others are joined through the other blob, away from `b`. -/
theorem not_isDeterminedBy_of_separated (hN : IsBinaryNetwork N) (hbc : c ≠ b)
    (hsep : ∀ s t, s ≠ t → ¬ N.graph.Walks (incidentCutEdges N.graph b)ᶜ (N.leaf s) (N.leaf t)) {S : Finset X} (hS : S.card = 3) :
    ¬ IsDeterminedBy N.graph N.leaf c S := by
  rintro ⟨-, hdet⟩
  obtain ⟨v, rfl⟩ := Quotient.exists_rep c
  obtain ⟨w, rfl⟩ := Quotient.exists_rep b
  change blobOf N.graph v ≠ blobOf N.graph w at hbc
  change ∀ s ∈ S, ∀ t ∈ S, s ≠ t → ¬ N.graph.Walks (incidentCutEdges N.graph (blobOf N.graph v))ᶜ (N.leaf s) (N.leaf t) at hdet
  change ∀ s t, s ≠ t → ¬ N.graph.Walks (incidentCutEdges N.graph (blobOf N.graph w))ᶜ (N.leaf s) (N.leaf t) at hsep
  set Dc : Set E := (incidentCutEdges N.graph (blobOf N.graph v))ᶜ with hDc
  set Db : Set E := (incidentCutEdges N.graph (blobOf N.graph w))ᶜ with hDb
  -- a taxon away from `b` is joined to `v` without the cut edges at `b`
  have key : ∀ s, ¬ N.graph.Walks Dc (N.leaf s) w → N.graph.Walks Db (N.leaf s) v := by
    intro s hs
    -- what the taxon reaches without the cut edges at the blob of `v` isn't in `b`
    have hclear : ∀ {x : V}, N.graph.Walks Dc (N.leaf s) x → blobOf N.graph x ≠ blobOf N.graph w := fun hx hxw =>
      hs (hx.trans (walks_compl_of_blobOf_eq _ hxw))
    have hin : ∀ {x : V}, N.graph.Walks Dc (N.leaf s) x → N.graph.Walks Db (N.leaf s) x := by
      intro x hx
      induction hx with
      | refl => exact .refl
      | @tail y z hy hstep ih =>
        have hzw := hclear (hy.tail hstep)
        have hyw := hclear hy
        obtain ⟨f, -, hfe⟩ := hstep
        refine ih.tail ⟨f, fun hinc => ?_, hfe⟩
        rcases hinc.2 with ⟨h1, -⟩ | ⟨h1, -⟩ <;> rcases hfe with ⟨h2, h3⟩ | ⟨h2, h3⟩
        · exact hyw (h2 ▸ h1)
        · exact hzw (h2 ▸ h1)
        · exact hzw (h3 ▸ h1)
        · exact hyw (h3 ▸ h1)
    by_cases hv : N.graph.Walks Dc (N.leaf s) v
    · exact hin hv
    -- the walk to `v` leaves what the taxon reaches, by a cut edge at the blob of `v`
    have gen : ∀ x, N.graph.Walks Set.univ (N.leaf s) x → ¬ N.graph.Walks Dc (N.leaf s) x →
        ∃ y z f, N.graph.Walks Dc (N.leaf s) y ∧ ¬ N.graph.Walks Dc (N.leaf s) z ∧ ((N.graph.source f = y ∧ N.graph.target f = z) ∨ (N.graph.source f = z ∧ N.graph.target f = y)) := by
      intro x hx
      induction hx with
      | refl => exact fun h => absurd .refl h
      | @tail y z _ hstep ih =>
        intro hz
        by_cases hy : N.graph.Walks Dc (N.leaf s) y
        · obtain ⟨f, -, hfe⟩ := hstep
          exact ⟨y, z, f, hy, hz, hfe⟩
        · exact ih hy
    obtain ⟨y, z, f, hy, hz, hfe⟩ := gen v (hN.connected _ v) hv
    have hfinc : f ∈ incidentCutEdges N.graph (blobOf N.graph v) := by
      by_contra hno
      exact hz (hy.tail ⟨f, hno, hfe⟩)
    have hyv : blobOf N.graph y ≠ blobOf N.graph v := fun h => hv (hy.trans (walks_compl_of_blobOf_eq _ h))
    have hzv : blobOf N.graph z = blobOf N.graph v := by
      rcases hfinc.2 with ⟨h1, -⟩ | ⟨h1, -⟩ <;> rcases hfe with ⟨h2, h3⟩ | ⟨h2, h3⟩
      · exact absurd (h2 ▸ h1) hyv
      · exact h2 ▸ h1
      · exact h3 ▸ h1
      · exact absurd (h3 ▸ h1) hyv
    have hfb : f ∈ Db := by
      intro hinc
      have hyw := hclear hy
      have hzw : blobOf N.graph z ≠ blobOf N.graph w := fun h => hbc (hzv.symm.trans h)
      rcases hinc.2 with ⟨h1, -⟩ | ⟨h1, -⟩ <;> rcases hfe with ⟨h2, h3⟩ | ⟨h2, h3⟩
      · exact hyw (h2 ▸ h1)
      · exact hzw (h2 ▸ h1)
      · exact hzw (h3 ▸ h1)
      · exact hyw (h3 ▸ h1)
    exact ((hin hy).tail ⟨f, hfb, hfe⟩).trans (walks_compl_of_blobOf_eq _ hzv)
  have huniq : ∀ s ∈ S, ∀ t ∈ S, s ≠ t → N.graph.Walks Dc (N.leaf s) w → ¬ N.graph.Walks Dc (N.leaf t) w := fun s hs t ht hne h₁ h₂ =>
    hdet s hs t ht hne (h₁.trans (N.graph.walks_symm h₂))
  obtain ⟨x, y, z, hxy, hxz, hyz, rfl⟩ := Finset.card_eq_three.1 hS
  by_cases hx : N.graph.Walks Dc (N.leaf x) w
  · have hy := huniq x (by simp) y (by simp) hxy hx
    have hz := huniq x (by simp) z (by simp) hxz hx
    exact hsep y z hyz ((key y hy).trans (N.graph.walks_symm (key z hz)))
  · by_cases hy : N.graph.Walks Dc (N.leaf y) w
    · have hz := huniq y (by simp) z (by simp) hyz hy
      exact hsep x z hxz ((key x hx).trans (N.graph.walks_symm (key z hz)))
    · exact hsep x y hxy ((key x hx).trans (N.graph.walks_symm (key y hy)))

/-- A cut edge at a blob below the LSA has a taxon beyond it. -/
theorem exists_leadsTo_of_isBelowLSA (hN : IsBinaryNetwork N) (hX : Nontrivial X) {v : V} (hb : IsBelowLSA hN hX (blobOf N.graph v)) {e : E} (he : e ∈ incidentCuts N.graph Set.univ v) :
    ∃ x, LeadsTo N.graph Set.univ v e (N.leaf x) := by
  have hP := hN.isPhylogenetic
  obtain ⟨hL, w, hw, hwr⟩ := hb
  have hv : N.graph.Reaches (lsaNode hN hX) v := (reaches_lsaNode_iff_of_blobOf_eq hN hX hw).mp hwr
  rcases he.2 with hs | ht
  · exact exists_leadsTo_leaf hP he hs
  · by_contra hno
    push Not at hno
    have hstable := isStableAncestor_target hP he ht hno
    have h₁ := (lsa_spec hP Set.univ Set.univ_nonempty).2 _ hstable
    have hbe := sameBlobIn_univ_iff.mp ht
    have h₂ := (reaches_lsaNode_iff_of_blobOf_eq hN hX hbe).mp hv
    have hEq := eq_of_reaches_of_reaches hP.acyclic h₁ h₂
    exact hL (by rw [hbe, hEq]; rfl)

/-- A cut edge at the blob of the LSA, other than the one entering the LSA, has a taxon beyond it. -/
theorem exists_leadsTo_of_lsaNode (hN : IsBinaryNetwork N) (hX : Nontrivial X) {e : E} (he : e ∈ incidentCuts N.graph Set.univ (lsaNode hN hX)) (hne : N.graph.target e ≠ lsaNode hN hX) :
    ∃ x, LeadsTo N.graph Set.univ (lsaNode hN hX) e (N.leaf x) := by
  have hP := hN.isPhylogenetic
  rcases he.2 with hs | ht
  · exact exists_leadsTo_leaf hP he hs
  · by_contra hno
    push Not at hno
    have hstable := isStableAncestor_target hP he ht hno
    have h₁ := (lsa_spec hP Set.univ Set.univ_nonempty).2 _ hstable
    have hbe := sameBlobIn_univ_iff.mp ht
    have h₂ := (reaches_lsaNode_iff_of_blobOf_eq hN hX hbe).mp .refl
    exact hne (eq_of_reaches_of_reaches hP.acyclic h₁ h₂)

/-- **"If the number of taxa was not decreased, then `𝒩⁺` has a relatively simple structure: Its LSA network `𝒩⊕` contains the blob `ℬ` with `n` incident cut edges"** (`a:claim:theorem3-structure`, in the proof of Theorem 3). Suppose each component of what remains of `𝒩⁺` without the cut edges at the blob `b` has at most one taxon. Then "the incident cut edges connect to (possibly empty) chains of 2-blobs leading to leaves": a blob below the LSA other than `b` has degree at most 2. The blob containing the LSA, if it isn't `b`, has degree at most 3: "a 3-blob containing the LSA". And for at least 3 taxa, `b` isn't above the LSA, and has exactly `n` incident cut edges in `𝒩⊕`: when it is below the LSA, its incident cut edges are all in `𝒩⊕`, and when it contains the LSA, it is the blob of the root of `𝒩⊕`. The proof of Theorem 3 here doesn't use this description. -/
theorem structure_of_separated (hN : IsBinaryNetwork N) (hX : Nontrivial X) {b : N.graph.BlobVertex}
    (hsep : ∀ s t, s ≠ t → ¬ N.graph.Walks (incidentCutEdges N.graph b)ᶜ (N.leaf s) (N.leaf t)) :
    (∀ c, IsBelowLSA hN hX c → c ≠ b → blobDegree N c ≤ 2) ∧
      (blobOf N.graph (lsaNode hN hX) ≠ b → blobDegree N (blobOf N.graph (lsaNode hN hX)) ≤ 3) ∧
      ∀ [Fintype X], 3 ≤ Fintype.card X →
        (IsBelowLSA hN hX b ∧ cutDegree N.graph b = Fintype.card X) ∨
          (blobOf N.graph (lsaNode hN hX) = b ∧ cutDegree (lsaPlus hN hX).graph (blobOf (lsaPlus hN hX).graph (lsaPlus hN hX).root) = Fintype.card X) := by
  have hP := hN.isPhylogenetic
  have : Finite E := hP.finite_arcs
  refine ⟨fun c hc hcb => ?_, fun hcb => ?_, fun hcard => ?_⟩
  · by_contra hno
    obtain ⟨S, hS, hd⟩ := exists_isDeterminedBy_of_isBelowLSA hN hX hc (by omega)
    exact not_isDeterminedBy_of_separated hN hcb hsep hS hd
  · by_contra hno
    obtain ⟨S, hS, hd⟩ := exists_isDeterminedBy_lsaNode hN hX (by omega)
    exact not_isDeterminedBy_of_separated hN hcb hsep hS hd
  have hd : IsDeterminedBy N.graph N.leaf b Finset.univ := ⟨by rwa [Finset.card_univ], fun s _ t _ hne => hsep s t hne⟩
  have hge := InPassing.card_le_cutDegree hP hd
  rw [Finset.card_univ] at hge
  -- `n` is an upper bound for edges with a taxon beyond them
  have hupper : ∀ {v : V} {A : Set E}, (∀ e ∈ A, ∃ x, LeadsTo N.graph Set.univ v e (N.leaf x)) → A.ncard ≤ Fintype.card X := by
    intro v A hA
    choose! g hg using hA
    have hw : ∀ u, N.graph.Walks Set.univ v u := fun u => N.graph_connected hP v u
    have hle := Set.ncard_le_ncard_of_injOn (s := A) (t := (Set.univ : Set X)) g (fun _ _ => Set.mem_univ _)
      (fun e he e' he' hee => (hg e he).unique (hee ▸ hg e' he') (hw _)) (Set.toFinite _)
    rwa [Set.ncard_univ, Nat.card_eq_fintype_card] at hle
  obtain ⟨v, rfl⟩ := Quotient.exists_rep b
  change IsDeterminedBy N.graph N.leaf (blobOf N.graph v) Finset.univ at hd
  change Fintype.card X ≤ cutDegree N.graph (blobOf N.graph v) at hge
  have habove : ¬ (N.graph.Reaches v (lsaNode hN hX) ∧ v ≠ lsaNode hN hX) := fun h =>
    not_isDeterminedBy_of_isAboveLSA hN hX ⟨v, rfl, h⟩ _ hd
  have hreach := (reaches_lsaNode_or hN hX v).resolve_right habove
  by_cases hL : blobOf N.graph (lsaNode hN hX) = blobOf N.graph v
  · refine Or.inr ⟨hL, ?_⟩
    rw [cutDegree_lsaPlus hN hX]
    have hu : incidentCutEdges N.graph (blobOf N.graph (lsaNode hN hX)) = incidentCuts N.graph Set.univ (lsaNode hN hX) := incidentCutEdges_blobOf
    rw [hu]
    refine le_antisymm (hupper (v := lsaNode hN hX) fun e he => exists_leadsTo_of_lsaNode hN hX he.1 he.2) ?_
    -- each taxon is beyond an edge that doesn't enter the LSA
    rw [← hL] at hd
    obtain ⟨h3, hdet⟩ := isDeterminedBy_blobOf_iff.mp hd
    have hw : ∀ u, N.graph.Walks Set.univ (lsaNode hN hX) u := fun u => N.graph_connected hP _ u
    have hlead : ∀ s : X, ∃ g, LeadsTo N.graph Set.univ (lsaNode hN hX) g (N.leaf s) := fun s =>
      (exists_leadsTo (hw _)).resolve_left fun hb =>
        hdet.ne_of_isPendantIn h3 (isPendantIn_leaf hP s _) (fun t _ => hw _)
          ((isPendantIn_leaf hP s _).eq_of_sameBlobIn hb)
    choose g hg using hlead
    have hmaps : ∀ s ∈ (Set.univ : Set X), g s ∈ incidentCuts N.graph Set.univ (lsaNode hN hX) \ {e | N.graph.target e = lsaNode hN hX} := by
      intro s _
      refine ⟨(hg s).1, fun hte => (hg s).2 ?_⟩
      have hr : N.graph.Reaches (lsaNode hN hX) (N.leaf s) := (lsa_spec hP Set.univ Set.univ_nonempty).1.reaches_leaf hP (Set.mem_univ s)
      have ht' : N.graph.Reaches (N.graph.target (g s)) (N.leaf s) := by
        rw [show N.graph.target (g s) = lsaNode hN hX from hte]
        exact hr
      have := walks_diff_target hP (g s) ht'
      rwa [show N.graph.target (g s) = lsaNode hN hX from hte] at this
    have hle := Set.ncard_le_ncard_of_injOn g hmaps
      (fun s _ t _ hst => by
        by_contra hne
        exact hdet.ne_of_leadsTo (Finset.mem_univ s) (Finset.mem_univ t) hne (hw _) (hw _) (hg s) (hg t) hst) (Set.toFinite _)
    rwa [Set.ncard_univ, Nat.card_eq_fintype_card] at hle
  · have hbelow : IsBelowLSA hN hX (blobOf N.graph v) := ⟨hL, v, rfl, hreach⟩
    refine Or.inl ⟨hbelow, le_antisymm ?_ hge⟩
    have hu : incidentCutEdges N.graph (blobOf N.graph v) = incidentCuts N.graph Set.univ v := incidentCutEdges_blobOf
    change (incidentCutEdges N.graph (blobOf N.graph v)).ncard ≤ _
    rw [hu]
    exact hupper fun e he => exists_leadsTo_of_isBelowLSA hN hX hbelow he

end Separated

/-! ### The concordance factors of a resolved tree -/

section ResolvedTree

variable [Fintype V] [Fintype E] [Fintype X] [DecidableEq X]

omit [Fintype V] [Fintype X] [DecidableEq X] in
/-- Below an edge of a tree with exactly two taxa below it, each child has one. -/
theorem not_both_below_of_isTreeNetwork (hN : IsBinaryNetwork N) (ht : IsTreeNetwork N) {e : E} {x y : X} (hxy : x ≠ y) (hbe : ∀ u, N.IsBelow e u → u = x ∨ u = y) (hx : N.IsBelow e x) (hy : N.IsBelow e y) :
    ∀ g, N.graph.source g = N.graph.target e → ¬ (N.IsBelow g x ∧ N.IsBelow g y) := by
  have hP := hN.isPhylogenetic
  have hbr := isBridge_of_isTreeNetwork hP ht
  have hleaf : ∀ u, N.leaf u ≠ N.graph.target e := by
    intro u hu
    have hreach : ∀ {w : X}, N.IsBelow e w → w = u := by
      intro w hw
      have hw' : N.graph.Reaches (N.leaf u) (N.leaf w) := hu ▸ hw
      rcases Relation.ReflTransGen.cases_head hw' with h | ⟨c, ⟨f, hf, -⟩, -⟩
      · exact (hP.leaf_injective h).symm
      · exact absurd hf ((N.graph.outdegree_eq_zero_iff _).mp ((hP.leaves _).mpr ⟨u, rfl⟩) f)
    exact hxy ((hreach hx).trans (hreach hy).symm)
  obtain ⟨p, g₁, g₂, -, -, hg₁, hg₂, hne, hall⟩ := TrivialEdges.exists_edges_of_isTrivialBlob hN (isTrivialBlob_of_isTreeNetwork hP ht _) (NMSC.target_ne_root hP e) hleaf
  have hbelow : ∀ {g : E} {u : X}, N.graph.source g = N.graph.target e → N.IsBelow g u → u = x ∨ u = y := fun hs hu =>
    hbe _ (Relation.ReflTransGen.head ⟨_, hs, rfl⟩ hu)
  intro g hg ⟨h₁, h₂⟩
  rcases hall g hg with rfl | rfl
  · obtain ⟨u, hu⟩ := exists_reaches_leaf hP (N.graph.target g₂)
    rcases hbelow hg₂ hu with rfl | rfl
    · exact TrivialEdges.not_isBelow_of_sibling hP hne (hg.trans hg₂.symm) (hbr g₂) hu h₁
    · exact TrivialEdges.not_isBelow_of_sibling hP hne (hg.trans hg₂.symm) (hbr g₂) hu h₂
  · obtain ⟨u, hu⟩ := exists_reaches_leaf hP (N.graph.target g₁)
    rcases hbelow hg₁ hu with rfl | rfl
    · exact TrivialEdges.not_isBelow_of_sibling hP hne.symm (hg.trans hg₁.symm) (hbr g₁) hu h₁
    · exact TrivialEdges.not_isBelow_of_sibling hP hne.symm (hg.trans hg₁.symm) (hbr g₁) hu h₂

/-- **On a resolved tree, the first entry is `1 - (2/3) exp (-t)`**, for an edge above a cherry `x, y`, where `t` is the length of the internal edge of `𝒩⁻`: the edge itself, or its sum with its sibling at the root. -/
theorem first_of_isTreeNetwork (hN : IsBinaryNetwork N) (ht : IsTreeNetwork N) (hcard : Fintype.card X = 4) {x y z w : X} (h : ({x, y, z, w} : Finset X).card = 4) {f : E}
    (hx : N.Dominates f x) (hy : N.Dominates f y) (hz : ¬ N.IsBelow f z) (hw : ¬ N.IsBelow f w) {θ : MetricData E} (hθ : N.IsMetric θ) :
    ∃ t, 0 < t ∧ nmscCF N θ 0 (quartetTree x y z w h) = 1 - 2 / 3 * Real.exp (-t) := by
  have hP := hN.isPhylogenetic
  have hbr := isBridge_of_isTreeNetwork hP ht
  obtain ⟨hxy, hxz, hxw, hyz, hyw, hzw⟩ := ne_of_card_four h
  have hall := Bridges.forall_eq_of_card_four hcard h
  have huniq : ∀ {g g' : E}, N.graph.target g = N.graph.target g' → g = g' := by
    intro g g' hgg
    exact (Set.ncard_le_one (Set.toFinite _)).1 (ht (N.graph.target g')) g hgg g' rfl
  have hlen : ∀ e : E, 0 < θ.length e := fun e => hθ.1 e (le_antisymm (ht _) (hP.nonroot_indegree _ (NMSC.target_ne_root hP e)))
  have hxb := hx.isBelow hP
  have hyb := hy.isBelow hP
  have hbe : ∀ u, N.IsBelow f u → u = x ∨ u = y := by
    intro u hu
    rcases hall u with rfl | rfl | rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr rfl
    · exact absurd hu hz
    · exact absurd hu hw
  have hsplit := not_both_below_of_isTreeNetwork hN ht hxy hbe hxb hyb
  -- the sibling of `f`
  have hsib : ∃ f', f' ≠ f ∧ N.graph.source f' = N.graph.source f := by
    have h2 : 1 < N.graph.outdegree (N.graph.source f) := by
      rcases hN.node_cases (N.graph.source f) with h0 | ⟨u, hu⟩ | h0 | h0
      · rw [h0, hN.root_out]
        omega
      · exact absurd rfl ((N.graph.outdegree_eq_zero_iff _).mp ((hP.leaves _).mpr ⟨u, hu⟩) f)
      · rw [h0.2]
        omega
      · have := ht (N.graph.source f)
        rw [h0.1] at this
        omega
    obtain ⟨f', hf', hne⟩ := Set.exists_ne_of_one_lt_ncard h2 f
    exact ⟨f', hne, hf'⟩
  obtain ⟨f', hne, hs⟩ := hsib
  have hxn : ¬ N.IsBelow f' x := TrivialEdges.not_isBelow_of_sibling hP hne hs (hbr f) hxb
  have hyn : ¬ N.IsBelow f' y := TrivialEdges.not_isBelow_of_sibling hP hne hs (hbr f) hyb
  have hbe' : ∀ u, N.IsBelow f' u → u = z ∨ u = w := by
    intro u hu
    rcases hall u with rfl | rfl | rfl | rfl
    · exact absurd hu hxn
    · exact absurd hu hyn
    · exact Or.inl rfl
    · exact Or.inr rfl
  have huf : ∀ g, N.graph.target g = N.graph.target f → g = f := fun g hg => huniq hg
  have hmem : ({x, y} : Finset X) ∈ (quartetTree x y z w h).val := by simp
  by_cases hfz : N.IsBelow f' z
  · by_cases hfw : N.IsBelow f' w
    · refine ⟨θ.length f + θ.length f', add_pos (hlen f) (hlen f'), ?_⟩
      exact TrivialEdges.nmscCF_of_root hP hθ hs huf (fun g hg => huniq hg) h hx hy hsplit hz hw (TrivialEdges.dominates_of_isBridge hP (hbr f') hfz)
        (TrivialEdges.dominates_of_isBridge hP (hbr f') hfw) (not_both_below_of_isTreeNetwork hN ht hzw hbe' hfz hfw) hxn hyn
    · refine ⟨θ.length f, hlen f, ?_⟩
      rw [TrivialEdges.nmscCF_of_edge hP hθ hs huf h hx hy hsplit hz hw (TrivialEdges.dominates_of_isBridge hP (hbr f') hfz) hfw (quartetTree_taxa _ _ _ _ _), ite_eq_left hmem]
      ring
  · by_cases hfw : N.IsBelow f' w
    · have h' : ({x, y, w, z} : Finset X).card = 4 := by
        rw [← h]
        congr 1
        ext u
        simp only [Finset.mem_insert, Finset.mem_singleton]
        tauto
      have hr : (quartetTree x y z w h).taxa = {x, y, w, z} := by
        rw [quartetTree_taxa]
        ext u
        simp only [Finset.mem_insert, Finset.mem_singleton]
        tauto
      refine ⟨θ.length f, hlen f, ?_⟩
      rw [TrivialEdges.nmscCF_of_edge hP hθ hs huf h' hx hy hsplit hw hz (TrivialEdges.dominates_of_isBridge hP (hbr f') hfw) hfz hr, ite_eq_left hmem]
      ring
    · obtain ⟨u, hu⟩ := exists_reaches_leaf hP (N.graph.target f')
      rcases hbe' u hu with rfl | rfl
      · exact absurd hu hfz
      · exact absurd hu hfw

/-- **On a resolved tree, all parameters**: `CF_abcd` is `(1 - (2/3) exp (-t), exp (-t) / 3, exp (-t) / 3)`, with `t > 0`, for a tree with `T_rd = ab|cd`. -/
theorem cfTriple_of_isTreeNetwork (hN : IsBinaryNetwork N) (ht : IsTreeNetwork N) (hcard : Fintype.card X = 4) {a b c d : X} (h : ({a, b, c, d} : Finset X).card = 4)
    (hT : (Trd hN (nontrivial_of_card_four hcard)).HasQuartetTopology a b c d) {θ : MetricData E} (hθ : N.IsMetric θ) :
    ∃ t, 0 < t ∧ cfTriple N θ a b c d h = (1 - 2 / 3 * Real.exp (-t), Real.exp (-t) / 3, Real.exp (-t) / 3) := by
  obtain ⟨hab, hac, had, hbc, hbd, hcd⟩ := ne_of_card_four h
  obtain ⟨f, ⟨P, hP, hd, hn⟩, -⟩ := exists_edge_of_rootedForm hN hcard h hT
  have hdom : ∀ x ∈ P, N.Dominates f.1 x := fun x hx => dominatesOff_empty_iff.mp (hd x hx)
  have hnb : ∀ x ∈ (quartetTree a b c d h).taxa, x ∉ P → ¬ N.IsBelow f.1 x := fun x hx hxP hb =>
    hn x (Finset.mem_coe.mpr (Finset.mem_sdiff.mpr ⟨hx, hxP⟩)) (isBelowOff_empty_iff.mpr hb)
  have hmemt : ∀ x ∈ ({a, b, c, d} : Finset X), x ∈ (quartetTree a b c d h).taxa := fun x hx => by
    rw [quartetTree_taxa]
    exact hx
  have hfirst : ∃ t, 0 < t ∧ nmscCF N θ 0 (quartetTree a b c d h) = 1 - 2 / 3 * Real.exp (-t) := by
    simp only [quartetTree_val, Finset.mem_insert, Finset.mem_singleton] at hP
    rcases hP with rfl | rfl
    · exact first_of_isTreeNetwork hN ht hcard h (hdom a (by simp)) (hdom b (by simp))
        (hnb c (hmemt c (by simp)) (by simp [hac.symm, hbc.symm])) (hnb d (hmemt d (by simp)) (by simp [had.symm, hbd.symm])) hθ
    · have h' : ({c, d, a, b} : Finset X).card = 4 := by
        rw [← h]
        congr 1
        ext u
        simp only [Finset.mem_insert, Finset.mem_singleton]
        tauto
      have heq : quartetTree c d a b h' = quartetTree a b c d h := by
        apply Subtype.ext
        change ({{c, d}, {a, b}} : Finset (Finset X)) = {{a, b}, {c, d}}
        exact Finset.pair_comm _ _
      rw [← heq]
      exact first_of_isTreeNetwork hN ht hcard h' (hdom c (by simp)) (hdom d (by simp))
        (hnb a (hmemt a (by simp)) (by simp [hac, had])) (hnb b (hmemt b (by simp)) (by simp [hbc, hbd])) hθ
  obtain ⟨t, ht0, hF⟩ := hfirst
  obtain ⟨p', q', heq, -, -, -, -, hsum⟩ := proposition1 hN hcard h hT hθ
  have hp : p' = 1 - 2 / 3 * Real.exp (-t) := by
    have h1 : (cfTriple N θ a b c d h).1 = 1 - 2 / 3 * Real.exp (-t) := hF
    rw [heq] at h1
    exact h1
  have hq : q' = Real.exp (-t) / 3 := by
    rw [hp] at hsum
    linarith
  exact ⟨t, ht0, by rw [heq, hp, hq]⟩

/-- **"If the species network is a tree then two of the three entries of `CF_abcd` must be equal, with the third no smaller"** (`a:claim:tree-third`, after Definition 14, citing Allman et al. 2011), and it is larger, and "`CF_{ab|cd}` may take on any value in the interval `(1/3, 1)`", as to the bounds. On every rooted binary tree with `T_rd = ab|cd`, for all parameters. That every value arises is `InPassing.cf_tree_range`. -/
theorem third_no_smaller_of_isTreeNetwork (hN : IsBinaryNetwork N) (ht : IsTreeNetwork N) (hcard : Fintype.card X = 4) {a b c d : X} (h : ({a, b, c, d} : Finset X).card = 4)
    (hT : (Trd hN (nontrivial_of_card_four hcard)).HasQuartetTopology a b c d) {θ : MetricData E} (hθ : N.IsMetric θ) :
    (cfTriple N θ a b c d h).2.1 = (cfTriple N θ a b c d h).2.2 ∧ (cfTriple N θ a b c d h).2.1 < (cfTriple N θ a b c d h).1 ∧
      1 / 3 < (cfTriple N θ a b c d h).1 ∧ (cfTriple N θ a b c d h).1 < 1 := by
  obtain ⟨t, ht0, heq⟩ := cfTriple_of_isTreeNetwork hN ht hcard h hT hθ
  rw [heq]
  have h0 := Real.exp_pos (-t)
  have h1 : Real.exp (-t) < 1 := Real.exp_lt_one_iff.2 (by linarith)
  refine ⟨rfl, ?_, ?_, ?_⟩ <;> simp only <;> linarith

end ResolvedTree

end AllmanEtAl2023.BlobStructure
