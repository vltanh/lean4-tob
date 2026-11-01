module

public import Phylogenetics.Graph.Tree
public import Phylogenetics.Network.Defs

/-!
# ECToBlob: blobs and biconnected subgraphs

Lines 214-218 of the paper: "A blob in a phylogenetic network N is a maximal 2-edge connected subgraph, and a trivial blob is a blob that
contains a single node. When a network is binary, a non-trivial blob is equivalently a maximal biconnected (i.e., 2-node connected)
subgraph. Note that in a non-binary network with two biconnected components sharing a single node, these components are in the same blob
by our definition."

Here a blob is a class of `DirectedMultigraph.blobSetoid`, and a set of vertices `S` is biconnected, `IsBiconnectedSet`, if removing any
vertex leaves it connected, by arcs within `S`.

* `isBiconnectedSet_blob`: on a graph of degree at most three, a blob is biconnected; `RootedNetwork.IsBinary.incident_le` says a binary
  network is one.
* `blobSetoid_of_isBiconnectedSet`: on any graph, a biconnected set of at least three vertices lies in one blob. Together: non-trivial
  blobs of at least three vertices are the maximal such sets.
* `blobSetoid_of_two_biconnected`: the note on two biconnected components sharing a node.

The argument for the first is the standard one: a cut vertex of degree three leaves a part attached to it by one arc, a bridge.
-/

@[expose] public noncomputable section

open Phylogenetics

namespace ECToBlob.Biconnected

variable {V E : Type*} (G : DirectedMultigraph V E)

/-- **Biconnected**: removing any vertex leaves the set connected, by arcs within it. -/
def IsBiconnectedSet (S : Set V) : Prop :=
  ∀ x u v : V, u ∈ S → v ∈ S → u ≠ x → v ≠ x →
    G.Walks {e | G.source e ∈ S ∧ G.target e ∈ S ∧ G.source e ≠ x ∧ G.target e ≠ x} u v

/-- The arcs incident to a vertex. -/
def incident (x : V) : Set E := {e | G.source e = x ∨ G.target e = x}

variable {G}

/-- The arc doesn't cross a set unless one end is in it and the other isn't. -/
theorem crosses_of_mem_notMem {e : E} {S : Set V} (h : (G.source e ∈ S ∧ G.target e ∉ S) ∨ (G.target e ∈ S ∧ G.source e ∉ S)) :
    G.Crosses e S := by
  unfold DirectedMultigraph.Crosses
  tauto

/-- **Deleting a bridge keeps a walk whose ends are on one side of it.** -/
theorem walks_diff_bridge {A : Set E} {b : E} {S : Set V} (hS : ∀ f, G.Crosses f S ↔ f = b) {u y : V} (hu : u ∈ S) (hy : y ∈ S)
    (h : G.Walks A u y) : G.Walks (A \ {b}) u y := by
  -- `p` and `q`: the ends of the bridge, in the set and out of it
  obtain ⟨p, q, hp, hq, hb⟩ : ∃ p q, p ∈ S ∧ q ∉ S ∧ ((G.source b = p ∧ G.target b = q) ∨ (G.source b = q ∧ G.target b = p)) := by
    have hc : G.Crosses b S := (hS b).2 rfl
    unfold DirectedMultigraph.Crosses at hc
    rcases hc with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
    · exact ⟨_, _, h₁, h₂, Or.inl ⟨rfl, rfl⟩⟩
    · exact ⟨_, _, h₁, h₂, Or.inr ⟨rfl, rfl⟩⟩
  have key : ∀ z, G.Walks A u z → (z ∈ S ∧ G.Walks (A \ {b}) u z) ∨
      (z ∉ S ∧ G.Walks (A \ {b}) u p ∧ G.Walks (A \ {b}) q z) := by
    intro z hz
    induction hz with
    | refl => exact Or.inl ⟨hu, .refl⟩
    | @tail z z' _ hadj ih =>
      obtain ⟨f, hfA, hf⟩ := hadj
      by_cases hfb : f = b
      · subst hfb
        have hz₁ : (z = p ∧ z' = q) ∨ (z = q ∧ z' = p) := by
          rcases hf with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rcases hb with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
          · exact Or.inl ⟨h₁, h₂⟩
          · exact Or.inr ⟨h₁, h₂⟩
          · exact Or.inr ⟨h₂, h₁⟩
          · exact Or.inl ⟨h₂, h₁⟩
        rcases ih with ⟨hzS, hw⟩ | ⟨hzS, hw₁, hw₂⟩
        · rcases hz₁ with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · exact Or.inr ⟨hq, hw, .refl⟩
          · exact absurd hzS hq
        · rcases hz₁ with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · exact absurd hp hzS
          · exact Or.inl ⟨hp, hw₁⟩
      · have hnc : ¬ G.Crosses f S := fun hc => hfb ((hS f).1 hc)
        have hfA' : f ∈ A \ {b} := ⟨hfA, hfb⟩
        have hadj' : G.AdjOn (A \ {b}) z z' := ⟨f, hfA', hf⟩
        have hiff : z ∈ S ↔ z' ∈ S := by
          unfold DirectedMultigraph.Crosses at hnc
          rcases hf with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> tauto
        rcases ih with ⟨hzS, hw⟩ | ⟨hzS, hw₁, hw₂⟩
        · exact Or.inl ⟨hiff.1 hzS, hw.tail hadj'⟩
        · exact Or.inr ⟨fun h' => hzS (hiff.2 h'), hw₁, hw₂.tail hadj'⟩
  rcases key y h with ⟨-, hw⟩ | ⟨hyS, -, -⟩
  · exact hw
  · exact absurd hy hyS

/-- The cut of a bridge, on the side of a given vertex. -/
theorem exists_cut_mem {b : E} (hb : G.underlying.IsBridge b) (u : V) : ∃ S : Set V, (∀ f, G.Crosses f S ↔ f = b) ∧ u ∈ S := by
  obtain ⟨S, hS⟩ := (G.isBridge_iff b).1 hb
  by_cases hu : u ∈ S
  · exact ⟨S, hS, hu⟩
  · refine ⟨Sᶜ, fun f => ?_, hu⟩
    rw [← hS f]
    unfold DirectedMultigraph.Crosses
    simp only [Set.mem_compl_iff, not_not]
    tauto

/-- **Deleting all the bridges keeps a walk between two vertices of one blob.** -/
theorem walks_diff_bridges [Finite E] {A : Set E} {u y : V} (hb : G.blobSetoid u y) (h : G.Walks A u y) :
    G.Walks (A ∩ {e | ¬ G.underlying.IsBridge e}) u y := by
  have hind : ∀ B : Set E, B.Finite → (∀ b ∈ B, G.underlying.IsBridge b) → G.Walks (A \ B) u y := by
    intro B hB
    induction B, hB using Set.Finite.induction_on with
    | empty =>
      intro _
      simpa using h
    | @insert b B _ _ ih =>
      intro hbr
      have hw := ih fun c hc => hbr c (Set.mem_insert_of_mem _ hc)
      obtain ⟨S, hS, hu⟩ := exists_cut_mem (hbr b (Set.mem_insert _ _)) u
      have hy : y ∈ S := by
        refine (G.mem_iff_mem_of_walks ?_ hb).1 hu
        intro f hf hc
        exact hf ((hS f).1 hc ▸ hbr b (Set.mem_insert _ _))
      have hw' := walks_diff_bridge hS hu hy hw
      refine G.walks_mono ?_ hw'
      rintro e ⟨⟨he₁, he₂⟩, he₃⟩
      refine ⟨he₁, ?_⟩
      rintro (he | he)
      · exact he₃ he
      · exact he₂ he
  have := hind {e | G.underlying.IsBridge e} (Set.toFinite _) fun _ h => h
  refine G.walks_mono ?_ this
  rintro e ⟨he₁, he₂⟩
  exact ⟨he₁, he₂⟩

/-- The non-bridge arcs that avoid a vertex. -/
def avoid (G : DirectedMultigraph V E) (x : V) : Set E :=
  {e | ¬ G.underlying.IsBridge e ∧ G.source e ≠ x ∧ G.target e ≠ x}

theorem walks_avoid_ne {x u z : V} (hu : u ≠ x) (h : G.Walks (avoid G x) u z) : z ≠ x := by
  induction h with
  | refl => exact hu
  | tail _ hadj _ =>
    obtain ⟨f, hf, hfz⟩ := hadj
    rcases hfz with ⟨_, rfl⟩ | ⟨rfl, _⟩
    · exact hf.2.2
    · exact hf.2.1

/-- The non-bridge arcs at `x` with the other end among the vertices reached from `u` avoiding `x`. -/
def attach (G : DirectedMultigraph V E) (x u : V) : Set E :=
  {f | ¬ G.underlying.IsBridge f ∧ f ∈ incident G x ∧ G.Crosses f {z | G.Walks (avoid G x) u z}}

/-- An arc crossing the set of vertices reached avoiding `x` is not one of those avoiding `x`. -/
theorem not_mem_avoid_of_crosses {x u : V} {f : E} (hc : G.Crosses f {z | G.Walks (avoid G x) u z}) : f ∉ avoid G x := by
  intro hf
  unfold DirectedMultigraph.Crosses at hc
  rcases hc with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
  · exact h₂ (Relation.ReflTransGen.tail h₁ ⟨f, hf, Or.inl ⟨rfl, rfl⟩⟩)
  · exact h₂ (Relation.ReflTransGen.tail h₁ ⟨f, hf, Or.inr ⟨rfl, rfl⟩⟩)

/-- A walk leaving the set of vertices reached avoiding `x` has an arc at `x`. -/
theorem exists_mem_attach {x u : V} {A : Set E} (hA : A ⊆ {e | ¬ G.underlying.IsBridge e}) (hu : u ≠ x) (h : G.Walks A u x) :
    ∃ f ∈ A, f ∈ attach G x u := by
  by_contra hne
  push Not at hne
  have hmem : u ∈ {z | G.Walks (avoid G x) u z} := Relation.ReflTransGen.refl
  have hx := (G.mem_iff_mem_of_walks (S := {z | G.Walks (avoid G x) u z}) (F := A) ?_ h).1 hmem
  · exact walks_avoid_ne hu hx rfl
  · intro f hf hc
    refine hne f hf ⟨hA hf, ?_, hc⟩
    by_contra hinc
    have hinc' : G.source f ≠ x ∧ G.target f ≠ x := by
      unfold incident at hinc
      simpa [not_or] using hinc
    exact not_mem_avoid_of_crosses hc ⟨hA hf, hinc'⟩

/-- **The attachments of two parts of a blob with a vertex removed are disjoint.** -/
theorem attach_disjoint {x u v : V} (huv : ¬ G.Walks (avoid G x) u v) (hu : u ≠ x) (hv : v ≠ x) :
    Disjoint (attach G x u) (attach G x v) := by
  rw [Set.disjoint_left]
  rintro f ⟨-, hf, hc⟩ ⟨-, -, hc'⟩
  have hnot : ∀ {w : V}, w ≠ x → x ∉ {z | G.Walks (avoid G x) w z} := fun hw hx => walks_avoid_ne hw hx rfl
  unfold DirectedMultigraph.Crosses at hc hc'
  have hxu := hnot hu
  have hxv := hnot hv
  rcases hf with hs | ht
  · rw [hs] at hc hc'
    have h₁ : G.target f ∈ {z | G.Walks (avoid G x) u z} := by tauto
    have h₂ : G.target f ∈ {z | G.Walks (avoid G x) v z} := by tauto
    exact huv (Relation.ReflTransGen.trans h₁ (G.walks_symm h₂))
  · rw [ht] at hc hc'
    have h₁ : G.source f ∈ {z | G.Walks (avoid G x) u z} := by tauto
    have h₂ : G.source f ∈ {z | G.Walks (avoid G x) v z} := by tauto
    exact huv (Relation.ReflTransGen.trans h₁ (G.walks_symm h₂))

/-- **A unique attachment is a bridge.** -/
theorem not_attach_eq_singleton [Finite E] {x u : V} {f : E} (hb : G.blobSetoid u x) (hu : u ≠ x) (hf : attach G x u = {f}) : False := by
  have hfm : f ∈ attach G x u := by
    rw [hf]
    exact Set.mem_singleton f
  obtain ⟨hfb, hfi, hfc⟩ := hfm
  by_cases hx : G.Walks ({f}ᶜ) u x
  · -- a second attachment
    have hw := walks_diff_bridges hb hx
    obtain ⟨g, hg, hga⟩ := exists_mem_attach (A := {f}ᶜ ∩ {e | ¬ G.underlying.IsBridge e}) (fun e he => he.2) hu hw
    rw [hf] at hga
    exact hg.1 hga
  · -- the arc is a bridge
    apply hfb
    refine (G.isBridge_iff f).2 ⟨{z | G.Walks ({f}ᶜ) u z}, fun g => ⟨fun hc => ?_, ?_⟩⟩
    · by_contra hgf
      unfold DirectedMultigraph.Crosses at hc
      have hg : g ∈ ({f}ᶜ : Set E) := hgf
      rcases hc with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
      · exact h₂ (Relation.ReflTransGen.tail h₁ ⟨g, hg, Or.inl ⟨rfl, rfl⟩⟩)
      · exact h₂ (Relation.ReflTransGen.tail h₁ ⟨g, hg, Or.inr ⟨rfl, rfl⟩⟩)
    · rintro rfl
      have hsub : avoid G x ⊆ ({g}ᶜ : Set E) := by
        intro e he hef
        have : e = g := hef
        subst this
        rcases hfi with h | h
        · exact he.2.1 h
        · exact he.2.2 h
      have hin : ∀ z, G.Walks (avoid G x) u z → G.Walks ({g}ᶜ) u z := fun z hz => G.walks_mono hsub hz
      unfold DirectedMultigraph.Crosses at hfc ⊢
      rcases hfc with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
      · refine Or.inl ⟨hin _ h₁, ?_⟩
        rcases hfi with h | h
        · exact absurd (h ▸ h₁ : G.Walks (avoid G x) u x) (fun h' => walks_avoid_ne hu h' rfl)
        · rw [h]
          exact hx
      · refine Or.inr ⟨hin _ h₁, ?_⟩
        rcases hfi with h | h
        · rw [h]
          exact hx
        · exact absurd (h ▸ h₁ : G.Walks (avoid G x) u x) (fun h' => walks_avoid_ne hu h' rfl)

/-- **On a graph of degree at most three, two vertices of a blob stay joined, by non-bridge arcs, after removing a third.** -/
theorem walks_avoid_of_blob [Finite E] (hdeg : ∀ x, (incident G x).ncard ≤ 3) {x u v : V} (hu : G.blobSetoid u x) (hv : G.blobSetoid v x)
    (hux : u ≠ x) (hvx : v ≠ x) : G.Walks (avoid G x) u v := by
  by_contra huv
  have hdis := attach_disjoint huv hux hvx
  obtain ⟨f, -, hf⟩ := exists_mem_attach (A := {e | ¬ G.underlying.IsBridge e}) subset_rfl hux hu
  obtain ⟨f', -, hf'⟩ := exists_mem_attach (A := {e | ¬ G.underlying.IsBridge e}) subset_rfl hvx hv
  have hsub : attach G x u ∪ attach G x v ⊆ incident G x := Set.union_subset (fun e he => he.2.1) fun e he => he.2.1
  have hcard : (attach G x u).ncard + (attach G x v).ncard ≤ 3 := by
    rw [← Set.ncard_union_eq hdis (Set.toFinite _) (Set.toFinite _)]
    exact (Set.ncard_le_ncard hsub (Set.toFinite _)).trans (hdeg x)
  have hone : (attach G x u).ncard = 1 ∨ (attach G x v).ncard = 1 := by
    have h₁ : 0 < (attach G x u).ncard := (Set.ncard_pos (Set.toFinite _)).2 ⟨f, hf⟩
    have h₂ : 0 < (attach G x v).ncard := (Set.ncard_pos (Set.toFinite _)).2 ⟨f', hf'⟩
    omega
  rcases hone with h | h
  · obtain ⟨g, hg⟩ := Set.ncard_eq_one.1 h
    exact not_attach_eq_singleton hu hux hg
  · obtain ⟨g, hg⟩ := Set.ncard_eq_one.1 h
    exact not_attach_eq_singleton hv hvx hg

/-- The ends of a non-bridge arc are in one blob. -/
theorem blobSetoid_ends {e : E} (he : ¬ G.underlying.IsBridge e) : G.blobSetoid (G.source e) (G.target e) :=
  Relation.ReflTransGen.single ⟨e, he, Or.inl ⟨rfl, rfl⟩⟩

/-- **Lines 215-216, one way** (`ecto:blob_biconnected`). On a graph of degree at most three, such as a binary network, a blob is
biconnected. -/
theorem isBiconnectedSet_blob [Finite E] (hdeg : ∀ x, (incident G x).ncard ≤ 3) (v₀ : V) :
    IsBiconnectedSet G {v | G.blobSetoid v₀ v} := by
  intro x u v hu hv hux hvx
  by_cases hx : G.blobSetoid v₀ x
  · have hux' : G.blobSetoid u x := G.blobSetoid.trans (G.blobSetoid.symm hu) hx
    have hvx' : G.blobSetoid v x := G.blobSetoid.trans (G.blobSetoid.symm hv) hx
    have hw := walks_avoid_of_blob hdeg hux' hvx' hux hvx
    -- the walk stays in the blob
    have key : ∀ z, G.Walks (avoid G x) u z → G.Walks {e | G.source e ∈ {v | G.blobSetoid v₀ v} ∧ G.target e ∈ {v | G.blobSetoid v₀ v} ∧
        G.source e ≠ x ∧ G.target e ≠ x} u z ∧ G.blobSetoid v₀ z := by
      intro z hz
      induction hz with
      | refl => exact ⟨.refl, hu⟩
      | @tail z z' _ hadj ih =>
        obtain ⟨f, hf, hfz⟩ := hadj
        have hzz' : G.blobSetoid z z' := Relation.ReflTransGen.single ⟨f, hf.1, hfz⟩
        have hz' : G.blobSetoid v₀ z' := G.blobSetoid.trans ih.2 hzz'
        refine ⟨ih.1.tail ⟨f, ?_, hfz⟩, hz'⟩
        rcases hfz with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact ⟨ih.2, hz', hf.2.1, hf.2.2⟩
        · exact ⟨hz', ih.2, hf.2.1, hf.2.2⟩
    exact (key v hw).1
  · -- with `x` elsewhere, the walks of the blob do
    have huv : G.blobSetoid u v := G.blobSetoid.trans (G.blobSetoid.symm hu) hv
    have key : ∀ z, G.Walks {e | ¬ G.underlying.IsBridge e} u z → G.Walks {e | G.source e ∈ {v | G.blobSetoid v₀ v} ∧
        G.target e ∈ {v | G.blobSetoid v₀ v} ∧ G.source e ≠ x ∧ G.target e ≠ x} u z ∧ G.blobSetoid v₀ z := by
      intro z hz
      induction hz with
      | refl => exact ⟨.refl, hu⟩
      | @tail z z' _ hadj ih =>
        obtain ⟨f, hf, hfz⟩ := hadj
        have hzz' : G.blobSetoid z z' := Relation.ReflTransGen.single ⟨f, hf, hfz⟩
        have hz' : G.blobSetoid v₀ z' := G.blobSetoid.trans ih.2 hzz'
        have hne : ∀ w, G.blobSetoid v₀ w → w ≠ x := fun w hw he => hx (he ▸ hw)
        refine ⟨ih.1.tail ⟨f, ?_, hfz⟩, hz'⟩
        rcases hfz with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact ⟨ih.2, hz', hne _ ih.2, hne _ hz'⟩
        · exact ⟨hz', ih.2, hne _ hz', hne _ ih.2⟩
    exact (key v huv).1

/-- **Lines 215-216, the other way** (`ecto:biconnected_blob`). On any graph, a biconnected set with at least three vertices lies in one
blob. -/
theorem blobSetoid_of_isBiconnectedSet {S : Set V} (hS : IsBiconnectedSet G S) (h3 : ∀ u v, ∃ r ∈ S, r ≠ u ∧ r ≠ v) {u v : V} (hu : u ∈ S)
    (hv : v ∈ S) : G.blobSetoid u v := by
  obtain ⟨x, -, hxu, hxv⟩ := h3 u v
  refine G.walks_mono ?_ (hS x u v hu hv hxu.symm hxv.symm)
  rintro e ⟨hs, ht, -, -⟩ hb
  obtain ⟨W, hW⟩ := (G.isBridge_iff e).1 hb
  have hc : G.Crosses e W := (hW e).2 rfl
  -- a vertex of the set that is neither end of the arc
  obtain ⟨r, hr, hrs, hrt⟩ := h3 (G.source e) (G.target e)
  have hnoe : ∀ {y : V}, (y = G.source e ∨ y = G.target e) → ∀ f ∈ {f | G.source f ∈ S ∧ G.target f ∈ S ∧ G.source f ≠ y ∧ G.target f ≠ y},
      ¬ G.Crosses f W := by
    rintro y hy f ⟨-, -, hf₁, hf₂⟩ hfc
    have hfe : f = e := (hW f).1 hfc
    subst hfe
    rcases hy with rfl | rfl
    · exact hf₁ rfl
    · exact hf₂ rfl
  have h₁ := G.mem_iff_mem_of_walks (hnoe (Or.inl rfl)) (hS (G.source e) r (G.target e) hr ht hrs ?_)
  have h₂ := G.mem_iff_mem_of_walks (hnoe (Or.inr rfl)) (hS (G.target e) r (G.source e) hr hs hrt ?_)
  · unfold DirectedMultigraph.Crosses at hc
    tauto
  · intro he
    unfold DirectedMultigraph.Crosses at hc
    rw [he] at hc
    tauto
  · intro he
    unfold DirectedMultigraph.Crosses at hc
    rw [he] at hc
    tauto

/-- **Lines 217-218** (`ecto:two_biconnected`). Two biconnected sets of at least three vertices sharing a node are in the same blob. -/
theorem blobSetoid_of_two_biconnected {S₁ S₂ : Set V} (h₁ : IsBiconnectedSet G S₁) (h₂ : IsBiconnectedSet G S₂)
    (h3₁ : ∀ u v, ∃ r ∈ S₁, r ≠ u ∧ r ≠ v) (h3₂ : ∀ u v, ∃ r ∈ S₂, r ≠ u ∧ r ≠ v) {w : V} (hw₁ : w ∈ S₁) (hw₂ : w ∈ S₂) {u v : V}
    (hu : u ∈ S₁) (hv : v ∈ S₂) : G.blobSetoid u v :=
  G.blobSetoid.trans (blobSetoid_of_isBiconnectedSet h₁ h3₁ hu hw₁) (blobSetoid_of_isBiconnectedSet h₂ h3₂ hw₂ hv)

/-- **A binary network has degree at most three.** -/
theorem incident_le {X : Type*} {N : RootedNetwork V E X} (hN : N.IsPhylogenetic) (hB : N.IsBinary) (x : V) :
    (incident N.graph x).ncard ≤ 3 := by
  have _ := hN.finite_arcs
  have hsub : incident N.graph x = {e | N.graph.source e = x} ∪ {e | N.graph.target e = x} := rfl
  have hle : (incident N.graph x).ncard ≤ N.graph.outdegree x + N.graph.indegree x := by
    rw [hsub]
    exact Set.ncard_union_le _ _
  by_cases hr : x = N.root
  · subst hr
    have h₁ := hB.1
    have h₂ := hN.root_indegree
    omega
  · by_cases ho : N.graph.outdegree x = 0
    · obtain ⟨y, rfl⟩ := (hN.leaves x).1 ho
      have h₁ := hN.leaf_indegree y
      omega
    · have h₁ := hB.2 x hr ho
      omega

/-- **Lines 215-216 on a binary network**: a blob is biconnected. -/
theorem isBiconnectedSet_blob_of_isBinary {X : Type*} {N : RootedNetwork V E X} (hN : N.IsPhylogenetic) (hB : N.IsBinary) (v₀ : V) :
    IsBiconnectedSet N.graph {v | N.graph.blobSetoid v₀ v} := by
  have _ := hN.finite_arcs
  exact isBiconnectedSet_blob (incident_le hN hB) v₀

end ECToBlob.Biconnected
