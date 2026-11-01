module

public import AllmanEtAl2023.BlobDefinitions
public import AllmanEtAl2023.SubgraphBlobs

/-!
# Allman, Baños, Mitchell, Rhodes 2023: Lemma 2

Lemma 2 needs `M` connected, or at least each `s` joined to `ℬ₀` in `M`. Its proof assumes this ("there exist undirected paths in `M` from `ℬ₀` to each `s ∈ S`") and all its uses
satisfy it, but the word is missing. For disconnected `M`, Definition 8 can hold vacuously and the conclusion fails: `lemma2_needs_connected`, on the caterpillar `(((a, b), c), d)`.
No result of the paper is affected.

"With degree-1 nodes bijectively labelled by `X`" is more than the uses satisfy: Lemma 3 applies Lemma 2 with `N := M`, a subnetwork of a rooted network, whose root can have degree 1 there
with no label. So `IsLabelledNetwork` asks only what the proof uses: distinct labels, on nodes of degree 1. This is a gap of the paper, with no effect on its results.

The proof is `AllmanEtAl2023.determines_of_subnetwork` of `src/AllmanEtAl2023/SubgraphBlobs.lean`, which follows the paper's, on arcs of a subgraph.
-/

@[expose] public noncomputable section

open Phylogenetics Phylogenetics.DirectedMultigraph
open scoped Classical

namespace AllmanEtAl2023

variable {W F X : Type*}

/-- "A network with degree-1 nodes bijectively labelled by `X`", as Lemma 2 uses it: distinct labels, on nodes of degree 1. Not every node of degree 1 need have a label: Lemma 3 applies Lemma 2 to
a subnetwork of a rooted network, whose root can have degree 1 there. See the module docstring. -/
structure IsLabelledNetwork (G : DirectedMultigraph W F) (ℓ : X → W) : Prop where
  injective : Function.Injective ℓ
  degree_one : ∀ x, nodeDegree G (ℓ x) = 1

/-- The nodes of the subnetwork with the edges `M`. -/
def nodesOf (G : DirectedMultigraph W F) (M : Set F) : Set W :=
  {v | ∃ f ∈ M, G.source f = v ∨ G.target f = v}

/-- The subnetwork with the edges `M` is connected. -/
def IsConnectedSubnetwork (G : DirectedMultigraph W F) (M : Set F) : Prop :=
  ∀ u ∈ nodesOf G M, ∀ v ∈ nodesOf G M, G.Walks M u v

/-- The incident cut edges of a blob of `F` are those of the subnetwork. -/
theorem image_incidentCutEdges_restrict {G : DirectedMultigraph W F} {M : Set F} (v : W) :
    Subtype.val '' incidentCutEdges (restrict G M) (blobOf (restrict G M) v) = incidentCuts G M v := by
  have hsame : ∀ u, blobOf (restrict G M) u = blobOf (restrict G M) v ↔ SameBlobIn G M v u := fun u => by
    constructor
    · intro h
      exact blobSetoid_restrict_iff.mp ((restrict G M).blobSetoid.symm (Quotient.exact h))
    · intro h
      exact Quotient.sound ((restrict G M).blobSetoid.symm (blobSetoid_restrict_iff.mpr h))
  ext f
  constructor
  · rintro ⟨g, ⟨hg, hi⟩, rfl⟩
    refine ⟨(isBridge_restrict_iff g).mp hg, ?_⟩
    rcases hi with ⟨h, -⟩ | ⟨h, -⟩
    · exact Or.inl ((hsame _).mp h)
    · exact Or.inr ((hsame _).mp h)
  · rintro ⟨hc, hb⟩
    have hb' : (restrict G M).underlying.IsBridge ⟨f, hc.1⟩ := (isBridge_restrict_iff ⟨f, hc.1⟩).mpr hc
    refine ⟨⟨f, hc.1⟩, ⟨hb', ?_⟩, rfl⟩
    have hne := blobOf_source_ne_target hb'
    rcases hb with hb | hb
    · have h := (hsame _).mpr hb
      exact Or.inl ⟨h, fun h' => hne (h.trans h'.symm)⟩
    · have h := (hsame _).mpr hb
      exact Or.inr ⟨h, fun h' => hne (h'.trans h.symm)⟩

/-- On a subnetwork, `IsDeterminedBy` is the library's `Determines`. -/
theorem isDeterminedBy_blobOf_restrict_iff {G : DirectedMultigraph W F} {M : Set F} {v : W} {ℓ : X → W}
    {S : Finset X} :
    IsDeterminedBy (restrict G M) ℓ (blobOf (restrict G M) v) S ↔ 3 ≤ S.card ∧ Determines G M v ℓ S := by
  have himg : Subtype.val '' (incidentCutEdges (restrict G M) (blobOf (restrict G M) v))ᶜ =
      M \ incidentCuts G M v := by
    rw [← image_incidentCutEdges_restrict (G := G) (M := M) v]
    ext f
    constructor
    · rintro ⟨g, hg, rfl⟩
      refine ⟨g.2, ?_⟩
      rintro ⟨g', hg', hgg⟩
      exact hg (Subtype.ext hgg ▸ hg')
    · rintro ⟨hf, hn⟩
      exact ⟨⟨f, hf⟩, fun h => hn ⟨_, h, rfl⟩, rfl⟩
  unfold IsDeterminedBy Determines
  simp only [walks_restrict_iff, himg]

/-- A cut edge of the whole network is a bridge. -/
theorem isCutIn_univ_iff {G : DirectedMultigraph W F} {e : F} : IsCutIn G Set.univ e ↔ G.underlying.IsBridge e := by
  rw [G.isBridge_iff_not_walks_delete, Set.compl_eq_univ_sdiff]
  exact ⟨fun h' => h'.2, fun h' => ⟨Set.mem_univ e, h'⟩⟩

/-- On the whole network, `SameBlobIn` is the blob relation: `SameBlobIn` of `SubgraphBlobs` is that of the paper's blobs. -/
theorem sameBlobIn_univ_iff {G : DirectedMultigraph W F} {u w : W} : SameBlobIn G Set.univ u w ↔ blobOf G u = blobOf G w := by
  constructor
  · intro h
    refine Quotient.sound (Relation.ReflTransGen.mono ?_ _ _ h)
    rintro a b ⟨e, he, hl⟩
    exact ⟨e, fun hb => he.2 (isCutIn_univ_iff.mpr hb), hl⟩
  · intro h
    refine Relation.ReflTransGen.mono ?_ _ _ (Quotient.exact h)
    rintro a b ⟨e, he, hl⟩
    exact ⟨e, ⟨Set.mem_univ e, fun hc => he (isCutIn_univ_iff.mp hc)⟩, hl⟩

/-- On the whole network, the incident cut edges of a blob are `incidentCuts`. -/
theorem incidentCutEdges_blobOf {G : DirectedMultigraph W F} {v : W} :
    incidentCutEdges G (blobOf G v) = incidentCuts G Set.univ v := by
  have hcut : ∀ {e}, IsCutIn G Set.univ e ↔ G.underlying.IsBridge e := isCutIn_univ_iff
  have hclass : ∀ u, blobOf G u = blobOf G v ↔ SameBlobIn G Set.univ v u := fun u => by
    rw [sameBlobIn_univ_iff]
    exact eq_comm
  ext e
  constructor
  · rintro ⟨hb, hi⟩
    refine ⟨hcut.mpr hb, ?_⟩
    rcases hi with ⟨h, -⟩ | ⟨h, -⟩
    · exact Or.inl ((hclass _).mp h)
    · exact Or.inr ((hclass _).mp h)
  · rintro ⟨hc, hb⟩
    have hb' := hcut.mp hc
    have hne := blobOf_source_ne_target hb'
    refine ⟨hb', ?_⟩
    rcases hb with hb | hb
    · have h := (hclass _).mpr hb
      exact Or.inl ⟨h, fun h' => hne (h.trans h'.symm)⟩
    · have h := (hclass _).mpr hb
      exact Or.inr ⟨h, fun h' => hne (h'.trans h.symm)⟩

/-- On the whole network, `IsDeterminedBy` is the library's `Determines`. -/
theorem isDeterminedBy_blobOf_iff {G : DirectedMultigraph W F} {v : W} {ℓ : X → W} {S : Finset X} :
    IsDeterminedBy G ℓ (blobOf G v) S ↔ 3 ≤ S.card ∧ Determines G Set.univ v ℓ S := by
  unfold IsDeterminedBy Determines
  rw [incidentCutEdges_blobOf, Set.compl_eq_univ_sdiff]

/-- A labelled node is pendant. -/
theorem IsLabelledNetwork.isPendantIn [Finite F] {G : DirectedMultigraph W F} {ℓ : X → W}
    (hG : IsLabelledNetwork G ℓ) (x : X) : IsPendantIn G Set.univ (ℓ x) := by
  obtain ⟨g, hne, -, hu⟩ := nodeDegree_eq_one_iff.mp (hG.degree_one x)
  exact ⟨g, hne, fun f _ hf => hu f hf⟩

/-- **Lemma 2** (`a:lem:inducedB`). Consider a network `N` with degree-1 nodes bijectively labelled by `X`, and a subnetwork `M` of `N`
with the restricted labelling of some degree-1 nodes by `Y ⊆ X`. If a set `S ⊆ Y` determines a blob on `M`, then `S` determines a blob
on `N`. Moreover, the incident cut edges of the blob on `N` leading to elements of `S` are in `M`.

`M` is connected, which the paper's proof assumes: see the module docstring, also for "bijectively". The blob on `N` is named: it is the one containing the blob on `M`, which the proof
says and Lemma 3 uses. "Leading to `s`" is that deleting the edge separates `s` from the blob. The proof is the paper's, in
`AllmanEtAl2023.determines_of_subnetwork`. -/
theorem lemma2 [Finite F] {G : DirectedMultigraph W F} {ℓ : X → W} (hG : IsLabelledNetwork G ℓ) {M : Set F}
    (hM : IsConnectedSubnetwork G M) {Y : Set X} (hY : ∀ y ∈ Y, ℓ y ∈ nodesOf G M) {S : Finset X} (hS : (S : Set X) ⊆ Y)
    {v : W} (hv : v ∈ nodesOf G M)
    (hdet : IsDeterminedBy (restrict G M) ℓ (blobOf (restrict G M) v) S) :
    IsDeterminedBy G ℓ (blobOf G v) S ∧
      ∀ s ∈ S, ∃ e ∈ M, e ∈ incidentCutEdges G (blobOf G v) ∧ ¬ G.Walks {e}ᶜ v (ℓ s) := by
  obtain ⟨h3, hd⟩ := isDeterminedBy_blobOf_restrict_iff.mp hdet
  obtain ⟨h₁, h₂⟩ := AllmanEtAl2023.determines_of_subnetwork (F := Set.univ) (Set.subset_univ M) h3
    (fun s _ => hG.isPendantIn s) (fun s hs => hM _ hv _ (hY s (hS hs)))
    (fun f hf => hM _ hv _ ⟨f, hf, Or.inl rfl⟩) hd
  have hdetN := isDeterminedBy_blobOf_iff.mpr ⟨h3, h₁⟩
  refine ⟨hdetN, fun s hs => ?_⟩
  obtain ⟨e, he, hlead, hw⟩ := h₂ s hs
  have hcut : e ∈ incidentCutEdges G (blobOf G v) := by
    obtain ⟨hc, hb⟩ := hlead
    have hb' : G.underlying.IsBridge e := by
      rw [G.isBridge_iff_not_walks_delete, Set.compl_eq_univ_sdiff]
      exact hc.2
    have hne := blobOf_source_ne_target hb'
    have hclass : ∀ u, SameBlobIn G Set.univ v u → blobOf G u = blobOf G v := fun u hu => by
      refine Quotient.sound (G.blobSetoid.symm ?_)
      refine Relation.ReflTransGen.mono ?_ _ _ hu
      rintro a b ⟨f, hf, hl⟩
      refine ⟨f, fun hbf => hf.2 ⟨Set.mem_univ f, ?_⟩, hl⟩
      rw [G.isBridge_iff_not_walks_delete, Set.compl_eq_univ_sdiff] at hbf
      exact hbf
    refine ⟨hb', ?_⟩
    rcases hb with hb | hb
    · have h := hclass _ hb
      exact Or.inl ⟨h, fun h' => hne (h.trans h'.symm)⟩
    · have h := hclass _ hb
      exact Or.inr ⟨h, fun h' => hne (h'.trans h.symm)⟩
  refine ⟨e, he, hcut, fun hwalk => hw ?_⟩
  rwa [Set.compl_eq_univ_sdiff] at hwalk

end AllmanEtAl2023
