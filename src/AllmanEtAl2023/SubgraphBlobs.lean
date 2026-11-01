module

public import Phylogenetics.Graph.Tree

/-!
# Blobs of a subnetwork, and the sets of taxa that determine them

Allman, Baños, Mitchell, Rhodes 2023, Definitions 7 and 8 and Lemma 2, for the subgraph of a
directed multigraph given by a set `F` of arcs, with orientations ignored. Nothing here is about
rooted networks; `src/AllmanEtAl2023/CycleLemma.lean` applies it to induced subgraphs.

* `IsCutIn`, `SameBlobIn`: the cut edges of `F`, and its blobs as the components left by deleting
  all of them, the description the source gives after its Definition 7. `isBlob_restrict` proves
  these are the maximal connected subgraphs without cut edges (`DirectedMultigraph.IsBlob`).
* `incidentCuts`, `Determines`: Definition 8 of the source. A blob is named by any of its vertices
  `v`.
* `LeadsTo`: the cut edge incident to a blob through which paths from the blob to a vertex pass;
  `exists_leadsTo`, `LeadsTo.unique`.
* `determines_of_subnetwork`: Lemma 2 of the source.
* `determines_of_median`, `exists_median`: Definition 8 in terms of the sides of cut edges, and the
  existence of the blob determined by three taxa, which the source states after Definition 8.
* `IsCycleThrough`: a cycle through an arc, obtained from a walk by the source's "removing edges to
  eliminate any self-intersections" (`exists_isCycleThrough`). It lies in one blob
  (`IsCycleThrough.isBridgelessSubgraph`, `sameBlobIn_of_isBridgelessSubgraph`).
* `IsPathIn`, `IsDirectedPath`: the paths combined into such a cycle, as sets of arcs; `exists_last_mem`:
  the last vertex of a walk on a set.
-/

@[expose] public section

open Phylogenetics.DirectedMultigraph

open Phylogenetics Phylogenetics.DirectedMultigraph

namespace AllmanEtAl2023

variable {V E : Type*} (G : DirectedMultigraph V E)

/-! ### Definitions -/

/-- The arc `e` joins `p` and `q`, in either orientation. -/
def Links (e : E) (p q : V) : Prop :=
  (G.source e = p ∧ G.target e = q) ∨ (G.source e = q ∧ G.target e = p)

/-- `e` is a cut edge of the subgraph with arcs `F`: deleting it separates its endpoints. -/
def IsCutIn (F : Set E) (e : E) : Prop :=
  e ∈ F ∧ ¬ G.Walks (F \ {e}) (G.source e) (G.target e)

/-- The arcs of `F` that are not cut edges of `F`. -/
def nonCutsIn (F : Set E) : Set E := {f | f ∈ F ∧ ¬ IsCutIn G F f}

/-- Two vertices lie in one blob of `F`: they are joined by arcs of `F` that are not cut edges. -/
def SameBlobIn (F : Set E) : V → V → Prop := G.Walks (nonCutsIn G F)

/-- The arcs of the blob of `v` in `F`. -/
def blobArcsIn (F : Set E) (v : V) : Set E :=
  {f | f ∈ nonCutsIn G F ∧ SameBlobIn G F v (G.source f)}

/-- The cut edges of `F` incident to the blob of `v`. -/
def incidentCuts (F : Set E) (v : V) : Set E :=
  {e | IsCutIn G F e ∧ (SameBlobIn G F v (G.source e) ∨ SameBlobIn G F v (G.target e))}

/-- **Definition 8 of the source**: the labels `S` determine the blob of `v` in `F`: deleting the
cut edges incident to the blob leaves the elements of `S` in distinct connected components. -/
def Determines {ι : Type*} (F : Set E) (v : V) (ℓ : ι → V) (S : Finset ι) : Prop :=
  ∀ s ∈ S, ∀ t ∈ S, s ≠ t → ¬ G.Walks (F \ incidentCuts G F v) (ℓ s) (ℓ t)

/-- `e` is the cut edge incident to the blob of `v` through which paths from `v` to `u` pass. -/
def LeadsTo (F : Set E) (v : V) (e : E) (u : V) : Prop :=
  e ∈ incidentCuts G F v ∧ ¬ G.Walks (F \ {e}) v u

/-- The connected component of `v` in `F` with the arc `e` deleted. -/
def compOff (F : Set E) (e : E) (v : V) : Set V := {u | G.Walks (F \ {e}) v u}

/-- The side of the arc `e` in `F` away from `v`. -/
def far (F : Set E) (e : E) (v : V) : Set V := (compOff G F e v)ᶜ

/-- Among the arcs of `F`, at most `e` crosses `T`. -/
def OnlyCrosses (F : Set E) (e : E) (T : Set V) : Prop := ∀ f ∈ F, G.Crosses f T → f = e

/-- The arcs of `F` with both endpoints in `T`. -/
def insideArcs (F : Set E) (T : Set V) : Set E :=
  {f | f ∈ F ∧ G.source f ∈ T ∧ G.target f ∈ T}

/-- At most one arc of `F` is at `x`, and it is not a loop: the degree-one nodes of the source. -/
def IsPendantIn (F : Set E) (x : V) : Prop :=
  ∃ g, G.source g ≠ G.target g ∧ ∀ f ∈ F, (G.source f = x ∨ G.target f = x) → f = g

/-- `C` is a cycle through `e`: the other arcs of `C` join the endpoints of `e`, and no fewer of
them do. A minimal set of arcs joining two vertices is a path without self-intersections, though
what is used below is only that `C` is connected without cut edges
(`IsCycleThrough.isBridgelessSubgraph`). -/
structure IsCycleThrough (C : Set E) (e : E) : Prop where
  mem : e ∈ C
  joins : G.Walks (C \ {e}) (G.source e) (G.target e)
  minimal : ∀ C', C' ⊂ C \ {e} → ¬ G.Walks C' (G.source e) (G.target e)

variable {G}
variable {F M : Set E} {T : Set V} {u v w p q : V} {e e' : E}

/-! ### Elementary facts on walks and cut edges -/

theorem Links.symm (h : Links G e p q) : Links G e q p := Or.symm h

theorem links_self (e : E) : Links G e (G.source e) (G.target e) := Or.inl ⟨rfl, rfl⟩

theorem walks_of_links (he : e ∈ F) (h : Links G e p q) : G.Walks F p q :=
  Relation.ReflTransGen.single ⟨e, he, h⟩

theorem Links.eq_or_eq {a c : V} (h : Links G e p q) (h' : Links G e a c) :
    (p = a ∧ q = c) ∨ (p = c ∧ q = a) := by
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rcases h' with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> simp [h1, h2]

theorem Links.crosses (h : Links G e p q) (hp : p ∉ T) (hq : q ∈ T) : G.Crosses e T := by
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact Or.inr ⟨hq, hp⟩
  · exact Or.inl ⟨hq, hp⟩

theorem Links.mem_iff_of_not_crosses (h : Links G e p q) (hc : ¬ G.Crosses e T) : p ∈ T ↔ q ∈ T := by
  simp only [Crosses] at hc
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> tauto

theorem IsCutIn.not_walks (he : IsCutIn G F e) (h : Links G e p q) : ¬ G.Walks (F \ {e}) p q := by
  have h' := he.2
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact h'
  · exact fun hw => h' (G.walks_symm hw)

theorem nonCutsIn_subset : nonCutsIn G F ⊆ F := fun _ h => h.1

theorem nonCutsIn_subset_diff (he : IsCutIn G F e) : nonCutsIn G F ⊆ F \ {e} := by
  rintro f ⟨hf, hfc⟩
  refine ⟨hf, ?_⟩
  rintro rfl
  exact hfc he

theorem SameBlobIn.walks (h : SameBlobIn G F u v) : G.Walks F u v :=
  walks_mono nonCutsIn_subset h

/-- Every arc of a cycle has a detour around it. -/
theorem SameBlobIn.walks_diff (he : IsCutIn G F e) (h : SameBlobIn G F u v) : G.Walks (F \ {e}) u v :=
  walks_mono (nonCutsIn_subset_diff he) h

theorem SameBlobIn.symm (h : SameBlobIn G F u v) : SameBlobIn G F v u := G.walks_symm h

/-- Two directed paths, one ending where the other starts, combine into a directed path. -/
theorem SameBlobIn.trans (h : SameBlobIn G F u v) (h' : SameBlobIn G F v w) : SameBlobIn G F u w :=
  Relation.ReflTransGen.trans h h'

theorem isCutIn_of_subset (hMF : M ⊆ F) (he : IsCutIn G F e) (heM : e ∈ M) : IsCutIn G M e :=
  ⟨heM, fun hw => he.2 (walks_mono (Set.sdiff_subset_sdiff_left hMF) hw)⟩

theorem nonCutsIn_mono (hMF : M ⊆ F) : nonCutsIn G M ⊆ nonCutsIn G F := by
  rintro f ⟨hf, hfc⟩
  exact ⟨hMF hf, fun hcut => hfc (isCutIn_of_subset hMF hcut hf)⟩

/-- A blob of a subnetwork lies in a blob of the network ("`ℬ₀` is contained in a blob `ℬ` of `N`").
-/
theorem SameBlobIn.mono (hMF : M ⊆ F) (h : SameBlobIn G M u v) : SameBlobIn G F u v :=
  walks_mono (nonCutsIn_mono hMF) h

theorem OnlyCrosses.compl (h : OnlyCrosses G F e T) : OnlyCrosses G F e Tᶜ :=
  fun f hf hc => h f hf ((G.crosses_compl f T).mp hc)

/-- A blob of a subnetwork lies in a blob of the network ("`ℬ₀` is contained in a blob `ℬ` of `N`").
-/
theorem OnlyCrosses.mono (hMF : M ⊆ F) (h : OnlyCrosses G F e T) : OnlyCrosses G M e T :=
  fun f hf hc => h f (hMF hf) hc

theorem OnlyCrosses.isCutIn (h : OnlyCrosses G F e T) (he : e ∈ F) (hc : G.Crosses e T) :
    IsCutIn G F e := by
  refine ⟨he, fun hw => ?_⟩
  have hiff := G.mem_iff_mem_of_walks (F := F \ {e}) (S := T)
    (fun f hf hcr => hf.2 (h f hf.1 hcr)) hw
  simp only [Crosses] at hc
  tauto

theorem OnlyCrosses.mem_iff_of_walks_diff (h : OnlyCrosses G F e T) (hw : G.Walks (F \ {e}) u v) :
    u ∈ T ↔ v ∈ T :=
  G.mem_iff_mem_of_walks (F := F \ {e}) (fun f hf hcr => hf.2 (h f hf.1 hcr)) hw

/-- A blob does not cross a side of a cut edge. -/
theorem SameBlobIn.mem_iff (h : OnlyCrosses G F e T) (hb : SameBlobIn G F u v) : u ∈ T ↔ v ∈ T :=
  G.mem_iff_mem_of_walks (F := nonCutsIn G F) (fun f hf hcr => by
    have hfe := h f hf.1 hcr
    subst hfe
    exact hf.2 (h.isCutIn hf.1 hcr)) hb

theorem onlyCrosses_compOff : OnlyCrosses G F e (compOff G F e v) := by
  intro f hf hc
  by_contra hfe
  exact G.not_crosses_walk_component (F \ {e}) v (e := f) ⟨hf, hfe⟩ hc

theorem onlyCrosses_far : OnlyCrosses G F e (far G F e v) := onlyCrosses_compOff.compl

theorem not_mem_far_self : v ∉ far G F e v := not_not.mpr Relation.ReflTransGen.refl

/-- An arc of `F` crossing `T` is the one arc at the boundary of `T`, when a walk in `F` enters `T`.
-/
theorem exists_links_of_walks (hT : OnlyCrosses G F e T) (hv : v ∉ T) (hw : G.Walks F v u)
    (hu : u ∈ T) : e ∈ F ∧ ∃ p q, Links G e p q ∧ p ∉ T ∧ q ∈ T := by
  induction hw with
  | refl => exact absurd hu hv
  | @tail a c _ hstep ih =>
    obtain ⟨g, hg, hl⟩ := hstep
    by_cases ha : a ∈ T
    · exact ih ha
    · have hge := hT g hg (Links.crosses hl ha hu)
      subst hge
      exact ⟨hg, a, c, hl, ha, hu⟩

/-- A side of a cut edge is connected: a walk entering `T` from outside gives a walk inside `T` from
the end `q` in `T` of the cut edge. -/
theorem walks_insideArcs (hT : OnlyCrosses G F e T) (hl : Links G e p q) (hp : p ∉ T)
    (hv : v ∉ T) (hw : G.Walks F v u) (hu : u ∈ T) :
    G.Walks (insideArcs G F T) q u := by
  induction hw with
  | refl => exact absurd hu hv
  | @tail a c _ hstep ih =>
    obtain ⟨g, hg, hlg⟩ := hstep
    by_cases ha : a ∈ T
    · refine (ih ha).tail ⟨g, ⟨hg, ?_, ?_⟩, hlg⟩
      · rcases hlg with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> assumption
      · rcases hlg with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> assumption
    · have hge := hT g hg (Links.crosses hlg ha hu)
      subst hge
      rcases Links.eq_or_eq hl hlg with ⟨-, h2⟩ | ⟨h1, -⟩
      · rw [h2]
        exact .refl
      · exact absurd (h1 ▸ hu) hp

/-- The arcs inside a side not containing an end of `e` avoid `e`. -/
theorem insideArcs_subset_diff (hl : Links G e p q) (hp : p ∉ T) : insideArcs G F T ⊆ F \ {e} := by
  rintro g ⟨hg, hgs, hgt⟩
  refine ⟨hg, ?_⟩
  rintro rfl
  rcases hl with ⟨rfl, -⟩ | ⟨-, rfl⟩
  · exact hp hgs
  · exact hp hgt

/-- With `e` deleted from a connected graph, a vertex is joined to one of the two ends of `e`. -/
theorem walks_of_not_walks (hl : Links G e p q) (hw : G.Walks F p u) (hu : ¬ G.Walks (F \ {e}) p u) :
    G.Walks (F \ {e}) q u := by
  have hp : p ∉ far G F e p := not_mem_far_self
  exact walks_mono (insideArcs_subset_diff hl hp)
    (walks_insideArcs onlyCrosses_far hl hp hp hw hu)

/-- Two vertices of a side of a cut edge are joined inside it. -/
theorem walks_insideArcs_of_mem (hT : OnlyCrosses G F e T) (hv : v ∉ T) (hs : G.Walks F v u)
    (ht : G.Walks F v w) (hu : u ∈ T) (hw : w ∈ T) : G.Walks (insideArcs G F T) u w := by
  obtain ⟨-, p, q, hl, hp, -⟩ := exists_links_of_walks hT hv hs hu
  exact (G.walks_symm (walks_insideArcs hT hl hp hv hs hu)).trans
    (walks_insideArcs hT hl hp hv ht hw)

/-! ### The cut edge leading from a blob to a vertex -/

/-- An incident cut edge has an end in the blob, and its other end on the far side. -/
theorem exists_ends_of_mem_incidentCuts (he : e ∈ incidentCuts G F v) :
    ∃ p q, Links G e p q ∧ SameBlobIn G F v p ∧ q ∈ far G F e v := by
  have key : ∀ p q, Links G e p q → SameBlobIn G F v p → q ∈ far G F e v := fun p q hl hb hw =>
    he.1.not_walks hl ((G.walks_symm (hb.walks_diff he.1)).trans hw)
  rcases he.2 with h | h
  · exact ⟨_, _, links_self e, h, key _ _ (links_self e) h⟩
  · exact ⟨_, _, (links_self e).symm, h, key _ _ (links_self e).symm h⟩

/-- Every vertex joined to `v` is in the blob of `v`, or beyond one of its incident cut edges. -/
theorem exists_leadsTo (hw : G.Walks F v u) : SameBlobIn G F v u ∨ ∃ e, LeadsTo G F v e u := by
  induction hw with
  | refl => exact Or.inl .refl
  | @tail a c _ hstep ih =>
    obtain ⟨g, hg, hl⟩ := hstep
    rcases ih with ih | ⟨e, he, hfar⟩
    · by_cases hcut : IsCutIn G F g
      · by_cases hc : SameBlobIn G F v c
        · exact Or.inl hc
        · refine Or.inr ⟨g, ⟨hcut, ?_⟩, fun hw => ?_⟩
          · rcases hl with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
            · exact Or.inl ih
            · exact Or.inr ih
          · exact hcut.not_walks hl ((G.walks_symm (ih.walks_diff hcut)).trans hw)
      · exact Or.inl (ih.tail ⟨g, ⟨hg, hcut⟩, hl⟩)
    · by_cases hge : g = e
      · subst hge
        obtain ⟨p, q, hlp, hb, -⟩ := exists_ends_of_mem_incidentCuts he
        have hpa : p ≠ a := by
          rintro rfl
          exact hfar (hb.walks_diff he.1)
        have hpc : p = c := by
          rcases hl with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rcases hlp with ⟨h1, h2⟩ | ⟨h1, h2⟩
          · exact absurd h1.symm hpa
          · exact h2.symm
          · exact h1.symm
          · exact absurd h2.symm hpa
        exact Or.inl (hpc ▸ hb)
      · exact Or.inr ⟨e, he, fun hw => hfar (hw.tail ⟨g, ⟨hg, hge⟩, Links.symm hl⟩)⟩

/-- The arcs inside a side away from `v` are not incident to the blob of `v`. -/
theorem insideArcs_subset_diff_incidentCuts (hT : OnlyCrosses G F e T) (hv : v ∉ T) :
    insideArcs G F T ⊆ F \ incidentCuts G F v := by
  rintro f ⟨hf, hs, ht⟩
  refine ⟨hf, fun hinc => ?_⟩
  rcases hinc.2 with h | h
  · exact hv ((SameBlobIn.mem_iff hT h).mpr hs)
  · exact hv ((SameBlobIn.mem_iff hT h).mpr ht)

/-- The cut edge leading from a blob to a vertex is unique: the sides away from the blob of two of
its incident cut edges are disjoint. -/
theorem LeadsTo.unique (h : LeadsTo G F v e u) (h' : LeadsTo G F v e' u) (hw : G.Walks F v u) :
    e = e' := by
  by_contra hne
  obtain ⟨p, q, hl, hb, -⟩ := exists_ends_of_mem_incidentCuts h.1
  have hT : OnlyCrosses G F e (far G F e v) := onlyCrosses_far
  have hvT : v ∉ far G F e v := not_mem_far_self
  have hp : p ∉ far G F e v := fun hc => hc (hb.walks_diff h.1.1)
  have hinside := walks_insideArcs hT hl hp hvT hw h.2
  have hsub : insideArcs G F (far G F e v) ⊆ F \ {e'} :=
    (insideArcs_subset_diff_incidentCuts hT hvT).trans
      (Set.sdiff_subset_sdiff_right (Set.singleton_subset_iff.mpr h'.1))
  refine h'.2 (((hb.walks_diff h'.1.1).trans (walks_of_links ⟨h.1.1.1, hne⟩ hl)).trans
    (walks_mono hsub hinside))

/-- Two vertices beyond distinct incident cut edges are in different components after deleting the
incident cut edges. -/
theorem not_walks_of_leadsTo (h : LeadsTo G F v e u) (h' : LeadsTo G F v e' w) (hne : e ≠ e')
    (hw : G.Walks F v w) : ¬ G.Walks (F \ incidentCuts G F v) u w := by
  intro huw
  have hiff := G.mem_iff_mem_of_walks (F := F \ incidentCuts G F v) (S := far G F e v)
    (fun f hf hc => hf.2 ((onlyCrosses_far f hf.1 hc) ▸ h.1)) huw
  exact hne (LeadsTo.unique ⟨h.1, hiff.mp h.2⟩ h' hw)

/-- Two elements on a side of a cut edge away from the blob are not separated. -/
theorem walks_diff_incidentCuts (hT : OnlyCrosses G F e T) (hv : v ∉ T) (hs : G.Walks F v u)
    (ht : G.Walks F v w) (hu : u ∈ T) (hw : w ∈ T) : G.Walks (F \ incidentCuts G F v) u w :=
  walks_mono (insideArcs_subset_diff_incidentCuts hT hv) (walks_insideArcs_of_mem hT hv hs ht hu hw)

section Determines

variable {ι : Type*} {ℓ : ι → V} {S : Finset ι} {s t : ι}

/-- **Definition 8, by sides of cut edges**: a side of a cut edge away from a blob determined by `S`
contains at most one element of `S`. -/
theorem Determines.eq_of_mem_side (hdet : Determines G F v ℓ S) (hT : OnlyCrosses G F e T)
    (hv : v ∉ T) (hs : s ∈ S) (ht : t ∈ S) (hws : G.Walks F v (ℓ s)) (hwt : G.Walks F v (ℓ t))
    (hsT : ℓ s ∈ T) (htT : ℓ t ∈ T) : s = t := by
  by_contra hne
  exact hdet s hs t ht hne (walks_diff_incidentCuts hT hv hws hwt hsT htT)

theorem Determines.ne (hdet : Determines G F v ℓ S) (hs : s ∈ S) (ht : t ∈ S) (hne : s ≠ t) :
    ℓ s ≠ ℓ t := fun h => hdet s hs t ht hne (h ▸ .refl)

theorem eq_of_walks_of_no_arc {x : V} (hF : ∀ f ∈ F, G.source f ≠ x ∧ G.target f ≠ x)
    (h : G.Walks F x w) : w = x := by
  induction h with
  | refl => rfl
  | @tail a c _ hstep ih =>
    subst ih
    obtain ⟨g, hg, hl⟩ := hstep
    rcases hl with ⟨h1, -⟩ | ⟨-, h1⟩
    · exact absurd h1 (hF g hg).1
    · exact absurd h1 (hF g hg).2

/-- A vertex with one arc is alone in its blob. -/
theorem IsPendantIn.eq_of_sameBlobIn {x : V} (hp : IsPendantIn G F x) (h : SameBlobIn G F v x) :
    v = x := by
  obtain ⟨g, hloop, hg⟩ := hp
  refine (eq_of_walks_of_no_arc ?_ (G.walks_symm h))
  rintro f ⟨hf, hcut⟩
  by_contra hat
  have hat' : G.source f = x ∨ G.target f = x := by
    by_contra hno
    push Not at hno
    exact hat hno
  have hfg := hg f hf hat'
  subst hfg
  refine hcut ⟨hf, fun hw => ?_⟩
  have hno : ∀ k ∈ F \ {f}, G.source k ≠ x ∧ G.target k ≠ x := by
    rintro k ⟨hk, hkf⟩
    constructor
    · exact fun h => hkf (hg k hk (Or.inl h))
    · exact fun h => hkf (hg k hk (Or.inr h))
  rcases hat' with h1 | h1
  · have := eq_of_walks_of_no_arc hno (h1 ▸ hw)
    exact hloop (h1.trans this.symm)
  · have := eq_of_walks_of_no_arc hno (h1 ▸ G.walks_symm hw)
    exact hloop (this.trans h1.symm)

/-- A blob of a subnetwork lies in a blob of the network ("`ℬ₀` is contained in a blob `ℬ` of `N`").
-/
theorem IsPendantIn.mono (hMF : M ⊆ F) {x : V} (h : IsPendantIn G F x) : IsPendantIn G M x := by
  obtain ⟨g, hloop, hg⟩ := h
  exact ⟨g, hloop, fun f hf => hg f (hMF hf)⟩

/-- `{x}ᶜ` is a side of the arc at a pendant vertex `x`. -/
theorem IsPendantIn.onlyCrosses {x : V} (h : IsPendantIn G F x) :
    ∃ g, OnlyCrosses G F g ({x}ᶜ : Set V) := by
  obtain ⟨g, -, hg⟩ := h
  refine ⟨g, fun f hf hc => hg f hf ?_⟩
  rcases hc with ⟨-, h1⟩ | ⟨-, h1⟩
  · exact Or.inr (by simpa using h1)
  · exact Or.inl (by simpa using h1)

/-- A blob determined by at least three labels isn't a pendant vertex. -/
theorem Determines.ne_of_isPendantIn {x : V} (hdet : Determines G F v ℓ S) (h3 : 3 ≤ S.card)
    (hp : IsPendantIn G F x) (hc : ∀ t ∈ S, G.Walks F v (ℓ t)) : v ≠ x := by
  rintro rfl
  obtain ⟨g, hg⟩ := hp.onlyCrosses
  have key : ∀ t ∈ S, ∀ t' ∈ S, t ≠ t' → ℓ t = v ∨ ℓ t' = v := by
    intro t ht t' ht' hne
    by_contra hno
    push Not at hno
    exact hne (hdet.eq_of_mem_side hg (by simp) ht ht' (hc t ht) (hc t' ht') (by simpa using hno.1)
      (by simpa using hno.2))
  obtain ⟨r, hr, t, ht, t', ht', h1, h2, h3'⟩ := Finset.two_lt_card.mp (by omega : 2 < S.card)
  have hu : ∀ {a b : ι}, a ∈ S → b ∈ S → a ≠ b → ℓ a = v → ℓ b ≠ v := fun ha hb hab h h' =>
    hdet.ne ha hb hab (h.trans h'.symm)
  rcases key r hr t ht h1 with h | h
  · exact (key t ht t' ht' h3').elim (hu hr ht h1 h) (hu hr ht' h2 h)
  · exact (key r hr t' ht' h2).elim (fun h' => hu hr ht h1 h' h) (hu ht ht' h3' h)

/-- Elements of a determining set are beyond distinct cut edges. -/
theorem Determines.ne_of_leadsTo (hdet : Determines G F v ℓ S) (hs : s ∈ S) (ht : t ∈ S)
    (hne : s ≠ t) (hws : G.Walks F v (ℓ s)) (hwt : G.Walks F v (ℓ t))
    (he : LeadsTo G F v e (ℓ s)) (he' : LeadsTo G F v e' (ℓ t)) : e ≠ e' := by
  rintro rfl
  exact hne (hdet.eq_of_mem_side onlyCrosses_far not_mem_far_self hs ht hws hwt he.2 he'.2)

/-- The arcs available to a path from the blob of `v` to `u`: the incident cut edge leading to `u`, and
all arcs beyond it (`LeadsTo.exists_walks_pathArcs`). -/
def pathArcs (G : DirectedMultigraph V E) (F : Set E) (v u : V) : Set E :=
  {g | ∃ e, LeadsTo G F v e u ∧ (g = e ∨ g ∈ insideArcs G F (far G F e v))}

theorem pathArcs_subset : pathArcs G F v u ⊆ F := by
  rintro g ⟨e, he, rfl | hg⟩
  · exact he.1.1.1
  · exact hg.1

/-- The path from the blob to a vertex beyond an incident cut edge. -/
theorem LeadsTo.exists_walks_pathArcs (h : LeadsTo G F v e u) (hw : G.Walks F v u) :
    ∃ x, SameBlobIn G F v x ∧ G.Walks (pathArcs G F v u) x u := by
  obtain ⟨p, q, hl, hb, -⟩ := exists_ends_of_mem_incidentCuts h.1
  refine ⟨p, hb, ?_⟩
  have hinside := walks_insideArcs onlyCrosses_far hl (fun hc => hc (hb.walks_diff h.1.1))
    not_mem_far_self hw h.2
  refine Relation.ReflTransGen.trans (walks_of_links ⟨e, h, Or.inl rfl⟩ hl) (walks_mono ?_ hinside)
  exact fun g hg => ⟨e, h, Or.inr hg⟩

/-- **Paths from the blob with no edges in common** (the first sentence of the source's proof of
Lemma 2): the paths to vertices beyond distinct incident cut edges share no arc. -/
theorem disjoint_pathArcs (hconn : ∀ f ∈ F, G.Walks F v (G.source f))
    (hne : ∀ e e', LeadsTo G F v e u → LeadsTo G F v e' w → e ≠ e') :
    Disjoint (pathArcs G F v u) (pathArcs G F v w) := by
  have key : ∀ {e e' g : E}, e ∈ incidentCuts G F v → e' ∈ incidentCuts G F v → e ≠ e' →
      g = e → g ∈ insideArcs G F (far G F e' v) → False := by
    intro e e' g he he' _ hg hin
    subst hg
    obtain ⟨p, q, hl, hb, -⟩ := exists_ends_of_mem_incidentCuts he
    have hp : p ∉ far G F e' v := fun hc => hc (hb.walks_diff he'.1)
    rcases hl with ⟨rfl, -⟩ | ⟨-, rfl⟩
    · exact hp hin.2.1
    · exact hp hin.2.2
  rw [Set.disjoint_left]
  rintro g ⟨e, he, hg⟩ ⟨e', he', hg'⟩
  have hee := hne e e' he he'
  rcases hg with hg | hg <;> rcases hg' with hg' | hg'
  · exact hee (hg.symm.trans hg')
  · exact key he.1 he'.1 hee hg hg'
  · exact key he'.1 he.1 hee.symm hg' hg
  · exact hee (LeadsTo.unique ⟨he.1, hg.2.1⟩ ⟨he'.1, hg'.2.1⟩ (hconn g hg.1))

/-- **Lemma 2 of the source** (`a:lem:inducedB`). Let `M` be a subnetwork of `F`, connected from the blob of `v` (`hc`,
`hconn`, which the source's proof assumes when it takes paths in `M`), with the labels `S` nodes of degree
one of `F`. If `S`, with at least three elements, determines the blob of `v` in `M`, then `S`
determines the blob of `v` in `F`, which contains it (`SameBlobIn.mono`), and the incident cut edges
of that blob leading to the elements of `S` are in `M`.

As in the source: there are paths in `M` from the blob to each `s ∈ S` with no edges in common. Each
must use the incident cut edge of `F` leading to `s`, since that arc separates `s` from the blob of
`F`, so these cut edges are in `M` and distinct. -/
theorem determines_of_subnetwork (hMF : M ⊆ F) (h3 : 3 ≤ S.card) (hp : ∀ s ∈ S, IsPendantIn G F (ℓ s))
    (hc : ∀ s ∈ S, G.Walks M v (ℓ s)) (hconn : ∀ f ∈ M, G.Walks M v (G.source f))
    (hdet : Determines G M v ℓ S) :
    Determines G F v ℓ S ∧ ∀ s ∈ S, ∃ e ∈ M, LeadsTo G F v e (ℓ s) := by
  have hcF : ∀ s ∈ S, G.Walks F v (ℓ s) := fun s hs => walks_mono hMF (hc s hs)
  -- the elements of `S` are outside the blob of `F`
  have hb : ∀ s ∈ S, ¬ SameBlobIn G F v (ℓ s) := fun s hs hbs =>
    hdet.ne_of_isPendantIn h3 ((hp s hs).mono hMF) hc ((hp s hs).eq_of_sameBlobIn hbs)
  have hbM : ∀ s ∈ S, ¬ SameBlobIn G M v (ℓ s) := fun s hs hbs => hb s hs (hbs.mono hMF)
  -- the paths in `M`
  have hdisj : ∀ s ∈ S, ∀ t ∈ S, s ≠ t → Disjoint (pathArcs G M v (ℓ s)) (pathArcs G M v (ℓ t)) :=
    fun s hs t ht hne => disjoint_pathArcs hconn fun e e' he he' =>
      hdet.ne_of_leadsTo hs ht hne (hc s hs) (hc t ht) he he'
  have hpath : ∀ s ∈ S, ∃ x, SameBlobIn G M v x ∧ G.Walks (pathArcs G M v (ℓ s)) x (ℓ s) := by
    intro s hs
    obtain ⟨e, he⟩ := (exists_leadsTo (hc s hs)).resolve_left (hbM s hs)
    exact he.exists_walks_pathArcs (hc s hs)
  -- each path uses the incident cut edge of `F`
  have hlead : ∀ s ∈ S, ∃ e ∈ pathArcs G M v (ℓ s), LeadsTo G F v e (ℓ s) := by
    intro s hs
    obtain ⟨e, he⟩ := (exists_leadsTo (hcF s hs)).resolve_left (hb s hs)
    refine ⟨e, ?_, he⟩
    by_contra hnot
    obtain ⟨x, hx, hwx⟩ := hpath s hs
    refine he.2 (((hx.mono hMF).walks_diff he.1.1).trans (walks_mono ?_ hwx))
    exact fun g hg => ⟨hMF (pathArcs_subset hg), fun hge => hnot (hge ▸ hg)⟩
  refine ⟨fun s hs t ht hne => ?_, fun s hs => ?_⟩
  · obtain ⟨e, he, hl⟩ := hlead s hs
    obtain ⟨e', he', hl'⟩ := hlead t ht
    refine not_walks_of_leadsTo hl hl' ?_ (hcF t ht)
    rintro rfl
    exact Set.disjoint_left.mp (hdisj s hs t ht hne) he he'
  · obtain ⟨e, he, hl⟩ := hlead s hs
    exact ⟨e, pathArcs_subset he, hl⟩

/-- The labels `S`, determining a blob, with one more label beyond another incident cut edge,
determine it. This is the last step of the source's proof of Lemma 3. -/
theorem Determines.insert [DecidableEq ι] {α : ι} (hdet : Determines G F v ℓ S)
    (hα : G.Walks F v (ℓ α)) (he : LeadsTo G F v e (ℓ α))
    (hne : ∀ s ∈ S, ∃ e', LeadsTo G F v e' (ℓ s) ∧ e' ≠ e) :
    Determines G F v ℓ (insert α S) := by
  have key : ∀ s ∈ S, ¬ G.Walks (F \ incidentCuts G F v) (ℓ s) (ℓ α) := fun s hs => by
    obtain ⟨e', hl, hee⟩ := hne s hs
    exact not_walks_of_leadsTo hl he hee hα
  intro s hs t ht hst hw
  rcases Finset.mem_insert.mp hs with rfl | hs' <;> rcases Finset.mem_insert.mp ht with rfl | ht'
  · exact hst rfl
  · exact key t ht' (G.walks_symm hw)
  · exact key s hs' hw
  · exact hdet s hs' t ht' hst hw

/-- A blob retained by a subnetwork stays determined: "`{a, b, c}` determines `ℬ′` in `N′` and hence
in `M ∩ N′`". -/
theorem Determines.of_subset (hMF : M ⊆ F)
    (hblob : ∀ x, SameBlobIn G F v x → SameBlobIn G M v x) (hdet : Determines G F v ℓ S) :
    Determines G M v ℓ S := by
  refine fun s hs t ht hne hw => hdet s hs t ht hne (walks_mono ?_ hw)
  rintro g ⟨hg, hgn⟩
  refine ⟨hMF hg, fun hinc => hgn ⟨isCutIn_of_subset hMF hinc.1 hg, ?_⟩⟩
  exact hinc.2.imp (hblob _) (hblob _)

/-- **The sides of cut edges give Definition 8**: if every side of a cut edge of `F` away from `v`
has at most one element of `S`, and `S` has at least three elements, of degree one, then `S`
determines the blob of `v`. The converse is `Determines.eq_of_mem_side`. -/
theorem determines_of_median (h3 : 3 ≤ S.card) (hinj : Set.InjOn ℓ S)
    (hp : ∀ s ∈ S, IsPendantIn G F (ℓ s)) (hc : ∀ s ∈ S, G.Walks F v (ℓ s))
    (hmed : ∀ e T, OnlyCrosses G F e T → v ∉ T → ∀ s ∈ S, ∀ t ∈ S, ℓ s ∈ T → ℓ t ∈ T → s = t) :
    Determines G F v ℓ S := by
  classical
  intro s hs t ht hne hw
  -- `s` is not in the blob
  have hb : ¬ SameBlobIn G F v (ℓ s) := by
    intro hbs
    have hv := (hp s hs).eq_of_sameBlobIn hbs
    have h2 : 1 < (S.erase s).card := by
      rw [Finset.card_erase_of_mem hs]
      omega
    obtain ⟨t₁, ht₁, t₂, ht₂, hne₁⟩ := Finset.one_lt_card.mp h2
    obtain ⟨g, hg⟩ := (hp s hs).onlyCrosses
    obtain ⟨h1, h1'⟩ := Finset.mem_erase.mp ht₁
    obtain ⟨h2', h2''⟩ := Finset.mem_erase.mp ht₂
    refine hne₁ (hmed g _ hg (by simpa using hv) t₁ h1' t₂ h2'' ?_ ?_)
    · simpa using fun h => h1 (hinj h1' hs h)
    · simpa using fun h => h2' (hinj h2'' hs h)
  obtain ⟨e, he⟩ := (exists_leadsTo (hc s hs)).resolve_left hb
  have hiff := G.mem_iff_mem_of_walks (F := F \ incidentCuts G F v) (S := far G F e v)
    (fun f hf hcr => hf.2 ((onlyCrosses_far f hf.1 hcr) ▸ he.1)) hw
  exact hne (hmed e _ onlyCrosses_far not_mem_far_self s hs t ht he.2 (hiff.mp he.2))

/-- At least two elements of `S` lie in `T`. -/
def TwoIn (ℓ : ι → V) (S : Finset ι) (T : Set V) : Prop :=
  ∃ s ∈ S, ∃ t ∈ S, s ≠ t ∧ ℓ s ∈ T ∧ ℓ t ∈ T

/-- Three elements do not have two on each side of a set. -/
theorem not_twoIn_compl_of_card_three (h3 : S.card = 3) {T : Set V} (h : TwoIn ℓ S T) : ¬ TwoIn ℓ S Tᶜ := by
  classical
  obtain ⟨s, hs, t, ht, hne, hsT, htT⟩ := h
  rintro ⟨s', hs', t', ht', hne', hsT', htT'⟩
  have h₁ : 1 < (S.filter fun x => ℓ x ∈ T).card := Finset.one_lt_card.mpr
    ⟨s, Finset.mem_filter.mpr ⟨hs, hsT⟩, t, Finset.mem_filter.mpr ⟨ht, htT⟩, hne⟩
  have h₂ : 1 < (S.filter fun x => ¬ ℓ x ∈ T).card := Finset.one_lt_card.mpr
    ⟨s', Finset.mem_filter.mpr ⟨hs', hsT'⟩, t', Finset.mem_filter.mpr ⟨ht', htT'⟩, hne'⟩
  have := Finset.card_filter_add_card_filter_not (s := S) fun x => ℓ x ∈ T
  omega

/-- **The blob determined by `S`**, as a median in the tree of blobs. If no cut edge has two
elements of `S` on each side, and some cut edge has two on one side, then a vertex `v` has at most
one element of `S` in each side away from it. It is an end of a cut edge with a side minimal among
those with two elements of `S`. -/
theorem exists_median [Finite V] {U : Set V} (hU : ∀ x ∈ U, ∀ y ∈ U, G.Walks F x y)
    (hend : ∀ f ∈ F, G.source f ∈ U ∧ G.target f ∈ U) (hS : ∀ s ∈ S, ℓ s ∈ U)
    (hstart : ∃ e T, e ∈ F ∧ OnlyCrosses G F e T ∧ G.Crosses e T ∧ TwoIn ℓ S T)
    (hsplit : ∀ e T, OnlyCrosses G F e T → TwoIn ℓ S T → TwoIn ℓ S Tᶜ → False) :
    ∃ v ∈ U, ∀ e T, OnlyCrosses G F e T → v ∉ T → ∀ s ∈ S, ∀ t ∈ S, ℓ s ∈ T → ℓ t ∈ T → s = t := by
  -- the family of sides, inside `U`, with two elements of `S`
  let 𝒯 : Set (Set V) :=
    {T | T ⊆ U ∧ ∃ e ∈ F, OnlyCrosses G F e T ∧ G.Crosses e T ∧ TwoIn ℓ S T}
  have hcross : ∀ {f : E} {T : Set V}, f ∈ F → (G.Crosses f (T ∩ U) ↔ G.Crosses f T) := by
    intro f T hf
    simp only [Crosses, Set.mem_inter_iff, (hend f hf).1, (hend f hf).2, and_true]
  have hinter : ∀ {e : E} {T : Set V}, e ∈ F → OnlyCrosses G F e T → G.Crosses e T → TwoIn ℓ S T →
      T ∩ U ∈ 𝒯 := by
    rintro e T he hO hC ⟨s, hs, t, ht, hne, hsT, htT⟩
    exact ⟨Set.inter_subset_right, e, he, fun f hf hc => hO f hf ((hcross hf).mp hc),
      (hcross he).mpr hC, s, hs, t, ht, hne, ⟨hsT, hS s hs⟩, ⟨htT, hS t ht⟩⟩
  obtain ⟨e₁, T₁, he₁, hO₁, hC₁, hT₁⟩ := hstart
  obtain ⟨T₀, hT₀, hmin⟩ := (Set.toFinite 𝒯).exists_minimal ⟨_, hinter he₁ hO₁ hC₁ hT₁⟩
  obtain ⟨hT₀U, e₀, he₀, hO₀, hC₀, hTwo₀⟩ := hT₀
  -- `v` is the end in `T₀` of its cut edge
  obtain ⟨p, q, hl, hp, hq⟩ : ∃ p q, Links G e₀ p q ∧ p ∉ T₀ ∧ q ∈ T₀ := by
    rcases hC₀ with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨_, _, (links_self e₀).symm, h2, h1⟩
    · exact ⟨_, _, links_self e₀, h2, h1⟩
  refine ⟨q, hT₀U hq, fun e T hO hqT s hs t ht hsT htT => ?_⟩
  by_contra hne
  have hwalk : ∀ x ∈ U, G.Walks F q x := fun x hx => hU q (hT₀U hq) x hx
  obtain ⟨he, p', r, hl', hp', hr⟩ := exists_links_of_walks hO hqT (hwalk _ (hS s hs)) hsT
  have hrT₀ : ∀ x ∈ U, x ∈ T → (r ∈ T₀ ↔ x ∈ T₀) := by
    intro x hxU hxT
    refine G.mem_iff_mem_of_walks (F := insideArcs G F T) ?_
      (walks_insideArcs hO hl' hp' hqT (hwalk x hxU) hxT)
    rintro g ⟨hg, hgs, hgt⟩ hc
    have hge := hO₀ g hg hc
    subst hge
    rcases hl with ⟨-, rfl⟩ | ⟨rfl, -⟩
    · exact hqT hgt
    · exact hqT hgs
  by_cases hrIn : r ∈ T₀
  · -- a smaller side
    have hmem := hinter he hO (Links.crosses hl' hp' hr) ⟨s, hs, t, ht, hne, hsT, htT⟩
    have hle : T ∩ U ≤ T₀ := fun x hx => (hrT₀ x hx.2 hx.1).mp hrIn
    exact hqT (hmin hmem hle hq).1
  · -- two elements of `S` on each side of the cut edge
    refine hsplit e₀ T₀ hO₀ hTwo₀ ⟨s, hs, t, ht, hne, ?_, ?_⟩
    · exact fun h => hrIn ((hrT₀ _ (hS s hs) hsT).mpr h)
    · exact fun h => hrIn ((hrT₀ _ (hS t ht) htT).mpr h)

end Determines

/-! ### Cycles -/

/-- A cycle through `e` from a walk avoiding `e`: "removing edges to eliminate any
self-intersections". -/
theorem exists_isCycleThrough [Finite E] (h : G.Walks (F \ {e}) (G.source e) (G.target e)) :
    ∃ C, IsCycleThrough G C e ∧ C \ {e} ⊆ F \ {e} := by
  obtain ⟨C₀, ⟨hsub, hjoin⟩, hmin⟩ := (Set.toFinite
    {C₀ : Set E | C₀ ⊆ F \ {e} ∧ G.Walks C₀ (G.source e) (G.target e)}).exists_minimal
      ⟨_, subset_rfl, h⟩
  have heq : insert e C₀ \ {e} = C₀ := by
    ext x
    constructor
    · rintro ⟨rfl | hx, hne⟩
      · exact absurd rfl hne
      · exact hx
    · intro hx
      exact ⟨Or.inr hx, fun hxe => (hsub hx).2 hxe⟩
  refine ⟨insert e C₀, ⟨Set.mem_insert _ _, ?_, ?_⟩, ?_⟩
  · rw [heq]
    exact hjoin
  · rw [heq]
    intro C' hC' hw
    exact hC'.2 (hmin ⟨hC'.1.trans hsub, hw⟩ hC'.1)
  · rw [heq]
    exact hsub

/-- A cycle crossing a vertex set at `e` crosses it at another arc. -/
theorem IsCycleThrough.exists_crosses {C : Set E} (h : IsCycleThrough G C e) (hc : G.Crosses e T) :
    ∃ g ∈ C \ {e}, G.Crosses g T := by
  by_contra hno
  push Not at hno
  have hiff := G.mem_iff_mem_of_walks hno h.joins
  simp only [Crosses] at hc
  tauto

/-- Each arc of the path `C \ {e}` is needed: one of its ends is joined to one end of `e`, and the
other to the other end, by the rest of the path. -/
theorem IsCycleThrough.exists_ends {C : Set E} (h : IsCycleThrough G C e) {f : E} (hf : f ∈ C \ {e}) :
    ∃ p q, Links G f p q ∧ G.Walks ((C \ {e}) \ {f}) (G.source e) p ∧
      G.Walks ((C \ {e}) \ {f}) (G.target e) q := by
  set D : Set E := (C \ {e}) \ {f} with hD
  have hnot : ¬ G.Walks D (G.source e) (G.target e) := h.minimal D
    ⟨Set.sdiff_subset, fun hsub => (hsub hf).2 rfl⟩
  have hO : OnlyCrosses G (C \ {e}) f (far G (C \ {e}) f (G.source e)) := onlyCrosses_far
  have hs : G.source e ∉ far G (C \ {e}) f (G.source e) := not_mem_far_self
  obtain ⟨-, p, q, hl, hp, -⟩ := exists_links_of_walks hO hs h.joins hnot
  exact ⟨p, q, hl, not_not.mp hp, G.walks_symm (walks_mono (insideArcs_subset_diff hl hp)
    (walks_insideArcs hO hl hp hs h.joins hnot))⟩

/-- The vertices on the arcs of `C`. -/
def arcVertices (G : DirectedMultigraph V E) (C : Set E) : Set V :=
  {x | ∃ f ∈ C, G.source f = x ∨ G.target f = x}

/-- Every arc of a cycle has a detour around it. -/
theorem IsCycleThrough.walks_diff {C : Set E} (h : IsCycleThrough G C e) {g : E} (hg : g ∈ C) :
    G.Walks (C \ {g}) (G.source g) (G.target g) := by
  by_cases hge : g = e
  · subst hge
    exact h.joins
  · obtain ⟨p, q, hl, hp, hq⟩ := h.exists_ends ⟨hg, hge⟩
    have hsub : (C \ {e}) \ {g} ⊆ C \ {g} := fun k hk => ⟨hk.1.1, hk.2⟩
    have heC : G.Walks (C \ {g}) (G.source e) (G.target e) :=
      walks_of_links ⟨h.mem, fun h' => hge h'.symm⟩ (links_self e)
    have hpq : G.Walks (C \ {g}) p q :=
      ((G.walks_symm (walks_mono hsub hp)).trans heC).trans (walks_mono hsub hq)
    rcases hl with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hpq
    · exact G.walks_symm hpq

/-- The ends of the arcs of a directed path are joined to its start along it. -/
theorem IsCycleThrough.walks_of_mem {C : Set E} (h : IsCycleThrough G C e) {x : V}
    (hx : x ∈ arcVertices G C) : G.Walks C (G.source e) x := by
  obtain ⟨f, hf, hfx⟩ := hx
  have hsub : C \ {e} ⊆ C := Set.sdiff_subset
  have hst : G.Walks C (G.source e) (G.target e) := walks_mono hsub h.joins
  by_cases hfe : f = e
  · subst hfe
    rcases hfx with rfl | rfl
    · exact .refl
    · exact hst
  · obtain ⟨p, q, hl, hp, hq⟩ := h.exists_ends ⟨hf, hfe⟩
    have hsub' : (C \ {e}) \ {f} ⊆ C := fun k hk => hk.1.1
    have hp' : G.Walks C (G.source e) p := walks_mono hsub' hp
    have hq' : G.Walks C (G.source e) q := hst.trans (walks_mono hsub' hq)
    rcases hl with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rcases hfx with rfl | rfl <;> assumption

/-- A detour around `g` turns a walk into one avoiding `g`. -/
theorem walks_diff_of_detour {C : Set E} {g : E} (hd : G.Walks (C \ {g}) (G.source g) (G.target g))
    (h : G.Walks C u v) : G.Walks (C \ {g}) u v := by
  induction h with
  | refl => exact .refl
  | @tail a c _ hstep ih =>
    obtain ⟨k, hk, hl⟩ := hstep
    by_cases hkg : k = g
    · subst hkg
      rcases hl with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact ih.trans hd
      · exact ih.trans (G.walks_symm hd)
    · exact ih.tail ⟨k, ⟨hk, hkg⟩, hl⟩

/-- A cycle is a connected subgraph with no cut edges. -/
theorem IsCycleThrough.isBridgelessSubgraph {C : Set E} (h : IsCycleThrough G C e) :
    G.IsBridgelessSubgraph (arcVertices G C) C := by
  have hconn : ∀ x ∈ arcVertices G C, ∀ y ∈ arcVertices G C, G.Walks C x y := fun x hx y hy =>
    (G.walks_symm (h.walks_of_mem hx)).trans (h.walks_of_mem hy)
  refine ⟨⟨_, e, h.mem, Or.inl rfl⟩, fun f hf => ⟨⟨f, hf, Or.inl rfl⟩, ⟨f, hf, Or.inr rfl⟩⟩, hconn, ?_⟩
  intro g hg x hx y hy
  exact walks_diff_of_detour (h.walks_diff hg) (hconn x hx y hy)

/-- A connected subgraph of `F` with no cut edges lies in one blob of `F`. -/
theorem sameBlobIn_of_isBridgelessSubgraph {U : Set V} {C : Set E} (h : G.IsBridgelessSubgraph U C)
    (hC : C ⊆ F) (hu : u ∈ U) (hv : v ∈ U) : SameBlobIn G F u v := by
  have hsub : C ⊆ nonCutsIn G F := fun g hg => ⟨hC hg, fun hcut => hcut.2 (walks_mono
    (Set.sdiff_subset_sdiff_left hC) (h.no_cut_edge g hg _ (h.endpoints g hg).1 _ (h.endpoints g hg).2))⟩
  exact walks_mono hsub (h.connected u hu v hv)

/-! ### Paths -/

/-- `P` is a path in `F` from `p` to `q`: a set of arcs of `F` joining `p` and `q`, no fewer of which
do. As for `IsCycleThrough`, a minimal set of arcs joining two vertices is a path without
self-intersections. -/
structure IsPathIn (G : DirectedMultigraph V E) (F P : Set E) (p q : V) : Prop where
  subset : P ⊆ F
  joins : G.Walks P p q
  minimal : ∀ P', P' ⊂ P → ¬ G.Walks P' p q

/-- A walk in `F` contains a path in `F`. -/
theorem exists_isPathIn [Finite E] (h : G.Walks F p q) : ∃ P, IsPathIn G F P p q := by
  obtain ⟨P, ⟨hsub, hjoin⟩, hmin⟩ := (Set.toFinite
    {P : Set E | P ⊆ F ∧ G.Walks P p q}).exists_minimal ⟨_, subset_rfl, h⟩
  exact ⟨P, hsub, hjoin, fun P' hP' hw => hP'.2 (hmin ⟨hP'.1.trans hsub, hw⟩ hP'.1)⟩

/-- `P` is the set of arcs of a directed path from `p`, followed along the orientations of its arcs.
In an acyclic graph, a directed walk has no self-intersections. -/
inductive IsDirectedPath (G : DirectedMultigraph V E) (p : V) : Set E → V → Prop
  | refl : IsDirectedPath G p ∅ p
  | tail {P : Set E} (f : E) :
      IsDirectedPath G p P (G.source f) → IsDirectedPath G p (insert f P) (G.target f)

section DirectedPath

variable {P P' : Set E} {f : E} {r : V}

theorem exists_isDirectedPath (h : G.Reaches p q) : ∃ P, IsDirectedPath G p P q := by
  induction h with
  | refl => exact ⟨∅, .refl⟩
  | tail _ hstep ih =>
    obtain ⟨P, hP⟩ := ih
    obtain ⟨f, rfl, rfl⟩ := hstep
    exact ⟨_, .tail f hP⟩

theorem IsDirectedPath.reaches (h : IsDirectedPath G p P q) : G.Reaches p q := by
  induction h with
  | refl => exact .refl
  | tail f _ ih => exact ih.tail ⟨f, rfl, rfl⟩

/-- An arc of a directed path lies between its ends. -/
theorem IsDirectedPath.reaches_of_mem (h : IsDirectedPath G p P q) (hf : f ∈ P) :
    G.Reaches p (G.source f) ∧ G.Reaches (G.target f) q := by
  induction h with
  | refl => exact absurd hf (Set.notMem_empty f)
  | tail g hg ih =>
    rcases hf with rfl | hf
    · exact ⟨hg.reaches, .refl⟩
    · exact ⟨(ih hf).1, (ih hf).2.tail ⟨g, rfl, rfl⟩⟩

theorem IsDirectedPath.walks (h : IsDirectedPath G p P q) : G.Walks P p q := by
  induction h with
  | refl => exact .refl
  | tail g _ ih => exact (walks_mono (Set.subset_insert g _) ih).tail ⟨g, Set.mem_insert g _, links_self g⟩

/-- The ends of the arcs of a directed path are joined to its start along it. -/
theorem IsDirectedPath.walks_of_mem (h : IsDirectedPath G p P q) (hf : f ∈ P) :
    G.Walks P p (G.source f) ∧ G.Walks P p (G.target f) := by
  induction h with
  | refl => exact absurd hf (Set.notMem_empty f)
  | tail g hg ih =>
    have hs : G.Walks (insert g _) p (G.source g) := walks_mono (Set.subset_insert g _) hg.walks
    rcases hf with rfl | hf
    · exact ⟨hs, hs.tail ⟨f, Set.mem_insert f _, links_self f⟩⟩
    · exact ⟨walks_mono (Set.subset_insert g _) (ih hf).1, walks_mono (Set.subset_insert g _) (ih hf).2⟩

/-- Two directed paths, one ending where the other starts, combine into a directed path. -/
theorem IsDirectedPath.trans (h : IsDirectedPath G p P q) (h' : IsDirectedPath G q P' r) :
    IsDirectedPath G p (P ∪ P') r := by
  induction h' with
  | refl => rwa [Set.union_empty]
  | tail g _ ih =>
    rw [Set.union_insert]
    exact .tail g ih

end DirectedPath

/-- The arcs of `P` meeting `S` at most at `m`. -/
def arcsAway (G : DirectedMultigraph V E) (P : Set E) (S : Set V) (m : V) : Set E :=
  {f | f ∈ P ∧ (G.source f ∈ S → G.source f = m) ∧ (G.target f ∈ S → G.target f = m)}

theorem arcsAway_subset {P : Set E} {S : Set V} {m : V} : arcsAway G P S m ⊆ P := fun _ h => h.1

/-- **The last vertex of a walk on a set `S`**: a walk from `S` splits at a vertex `m` of `S`, after
which it no longer meets `S`. -/
theorem exists_last_mem {P : Set E} {S : Set V} (h : G.Walks P p q) (hp : p ∈ S) :
    ∃ m ∈ S, G.Walks P p m ∧ G.Walks (arcsAway G P S m) m q ∧ (q ∈ S → q = m) := by
  induction h with
  | refl => exact ⟨p, hp, .refl, .refl, fun _ => rfl⟩
  | @tail a c hpa hstep ih =>
    by_cases hc : c ∈ S
    · exact ⟨c, hc, hpa.tail hstep, .refl, fun _ => rfl⟩
    · obtain ⟨m, hm, h1, h2, h3⟩ := ih
      obtain ⟨g, hg, hl⟩ := hstep
      refine ⟨m, hm, h1, h2.tail ⟨g, ⟨hg, ?_, ?_⟩, hl⟩, fun h => absurd h hc⟩
      · rcases hl with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact h3
        · exact fun h => absurd h hc
      · rcases hl with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact fun h => absurd h hc
        · exact h3

/-- A walk from `T` to outside it passes through `m`, if the only arcs of the walk crossing `T` are
at `m`. -/
theorem mem_arcVertices_of_walks {C : Set E} {m : V} (hw : G.Walks C p q) (hp : p ∈ T) (hq : q ∉ T)
    (hT : ∀ f ∈ C, G.Crosses f T → G.source f = m ∨ G.target f = m) : m ∈ arcVertices G C := by
  by_contra hm
  exact hq ((G.mem_iff_mem_of_walks (fun f hf hc => hm ⟨f, hf, hT f hf hc⟩) hw).mp hp)

theorem arcVertices_mono {C C' : Set E} (h : C ⊆ C') : arcVertices G C ⊆ arcVertices G C' := by
  rintro x ⟨f, hf, hx⟩
  exact ⟨f, h hf, hx⟩

/-! ### These are the blobs of `DirectedMultigraph` -/

/-- The subgraph with arcs `F`, on all the vertices. -/
def restrict (G : DirectedMultigraph V E) (F : Set E) : DirectedMultigraph V F where
  source e := G.source e
  target e := G.target e

theorem walks_restrict_iff {F' : Set F} :
    (restrict G F).Walks F' u v ↔ G.Walks (Subtype.val '' F') u v := by
  constructor
  · intro h
    refine Relation.ReflTransGen.mono ?_ _ _ h
    rintro a b ⟨e, he, hl⟩
    exact ⟨e.1, ⟨e, he, rfl⟩, hl⟩
  · intro h
    refine Relation.ReflTransGen.mono ?_ _ _ h
    rintro a b ⟨_, ⟨e, he, rfl⟩, hl⟩
    exact ⟨e, he, hl⟩

theorem image_compl_singleton (e : F) : Subtype.val '' ({e}ᶜ : Set F) = F \ {e.1} := by
  ext f
  constructor
  · rintro ⟨g, hg, rfl⟩
    exact ⟨g.2, fun h => hg (Subtype.ext h)⟩
  · rintro ⟨hf, hne⟩
    exact ⟨⟨f, hf⟩, fun h => hne (congrArg Subtype.val h), rfl⟩

/-- The cut edges of `F` are the bridges of the subgraph. -/
theorem isBridge_restrict_iff (e : F) :
    (restrict G F).underlying.IsBridge e ↔ IsCutIn G F e.1 := by
  rw [(restrict G F).isBridge_iff_not_walks_delete, walks_restrict_iff, image_compl_singleton]
  exact ⟨fun h => ⟨e.2, h⟩, fun h => h.2⟩

theorem image_not_isBridge :
    Subtype.val '' {e : F | ¬ (restrict G F).underlying.IsBridge e} = nonCutsIn G F := by
  ext f
  constructor
  · rintro ⟨g, hg, rfl⟩
    exact ⟨g.2, fun h => hg ((isBridge_restrict_iff g).mpr h)⟩
  · rintro ⟨hf, hne⟩
    exact ⟨⟨f, hf⟩, fun h => hne ((isBridge_restrict_iff ⟨f, hf⟩).mp h), rfl⟩

/-- `SameBlobIn` is the relation of `DirectedMultigraph.blobSetoid` for the subgraph. -/
theorem blobSetoid_restrict_iff : (restrict G F).blobSetoid.r u v ↔ SameBlobIn G F u v := by
  change (restrict G F).Walks _ u v ↔ _
  rw [walks_restrict_iff, image_not_isBridge]
  rfl

theorem image_blobArcs (v : V) :
    Subtype.val '' ((restrict G F).blobArcs v) = blobArcsIn G F v := by
  ext f
  constructor
  · rintro ⟨g, ⟨hg, hs⟩, rfl⟩
    exact ⟨⟨g.2, fun h => hg ((isBridge_restrict_iff g).mpr h)⟩, blobSetoid_restrict_iff.mp hs⟩
  · rintro ⟨⟨hf, hne⟩, hs⟩
    exact ⟨⟨f, hf⟩, ⟨fun h => hne ((isBridge_restrict_iff ⟨f, hf⟩).mp h),
      blobSetoid_restrict_iff.mpr hs⟩, rfl⟩

/-- **The blobs of a subgraph.** The classes of `SameBlobIn` are the blobs of the source's
Definition 7: the maximal connected subgraphs without cut edges. -/
theorem isBlob_restrict [Finite E] (v : V) :
    (restrict G F).IsBlob {w | SameBlobIn G F v w} (Subtype.val ⁻¹' blobArcsIn G F v) := by
  have h := (restrict G F).isBlob_blobClass v
  have h1 : {w | (restrict G F).blobSetoid.r v w} = {w | SameBlobIn G F v w} := by
    ext w
    exact blobSetoid_restrict_iff
  have h2 : (restrict G F).blobArcs v = Subtype.val ⁻¹' blobArcsIn G F v := by
    rw [← image_blobArcs, Set.preimage_image_eq _ Subtype.val_injective]
  rwa [h1, h2] at h

/-- A blob of `F` is a connected subgraph without cut edges. -/
theorem isBridgelessSubgraph_blob [Finite E] (v : V) :
    G.IsBridgelessSubgraph {w | SameBlobIn G F v w} (blobArcsIn G F v) := by
  have h := (restrict G F).isBridgelessSubgraph_blobClass v
  refine ⟨⟨v, .refl⟩, ?_, ?_, ?_⟩
  · rintro f ⟨hf, hs⟩
    exact ⟨hs, Relation.ReflTransGen.tail hs ⟨f, hf, Or.inl ⟨rfl, rfl⟩⟩⟩
  · intro u hu w hw
    have := h.connected u (blobSetoid_restrict_iff.mpr hu) w (blobSetoid_restrict_iff.mpr hw)
    rwa [walks_restrict_iff, image_blobArcs] at this
  · intro f hf u hu w hw
    have hf' : f ∈ F := hf.1.1
    have := h.no_cut_edge ⟨f, hf'⟩
      ((Set.ext_iff.mp (image_blobArcs (G := G) (F := F) v) f).mpr hf |> fun ⟨g, hg, hgf⟩ =>
        (Subtype.ext hgf : g = ⟨f, hf'⟩) ▸ hg) u
      (blobSetoid_restrict_iff.mpr hu) w (blobSetoid_restrict_iff.mpr hw)
    rw [walks_restrict_iff, Set.image_sdiff Subtype.val_injective, image_blobArcs,
      Set.image_singleton] at this
    exact this

/-! ### The cut edges between two vertices form a chain -/

/-- Two vertices on a side of `e` away from `v` are joined without `e`. -/
theorem walks_diff_of_mem_side (hT : OnlyCrosses G F e T) (hv : v ∉ T) (hs : G.Walks F v u)
    (ht : G.Walks F v w) (hu : u ∈ T) (hw : w ∈ T) : G.Walks (F \ {e}) u w := by
  obtain ⟨-, p, q, hl, hp, -⟩ := exists_links_of_walks hT hv hs hu
  exact walks_mono (insideArcs_subset_diff hl hp) (walks_insideArcs_of_mem hT hv hs ht hu hw)

/-- When `e` separates `v` from `w` in a connected graph, every vertex lies in one of the two
components of `v` and `w`. -/
theorem mem_compOff_or_mem_compOff (hu : G.Walks F v u) (hw : G.Walks F v w)
    (hsep : ¬ G.Walks (F \ {e}) v w) : u ∈ compOff G F e v ∨ u ∈ compOff G F e w := by
  by_cases h : u ∈ compOff G F e v
  · exact Or.inl h
  · exact Or.inr (G.walks_symm (walks_diff_of_mem_side onlyCrosses_far not_mem_far_self hu hw h hsep))

/-- **The arcs separating two vertices form a chain**, ordered by their sides containing `u`. An arc
`e'` other than `e` lies on one side of `e`. If it is on the side of `w`, a walk from `u` avoiding `e`
never meets it. If it is on the side of `u`, the side of `w` is connected without `e'`, so a walk from
`u` avoiding `e'` can't reach that side. -/
theorem compOff_subset_or_subset (hw : G.Walks F u w) (he : ¬ G.Walks (F \ {e}) u w)
    (he' : ¬ G.Walks (F \ {e'}) u w) :
    compOff G F e u ⊆ compOff G F e' u ∨ compOff G F e' u ⊆ compOff G F e u := by
  by_cases hee : e = e'
  · subst hee
    exact Or.inl subset_rfl
  have he'F : e' ∈ F := by
    by_contra hn
    have hsub : F ⊆ F \ {e'} := fun f hf => ⟨hf, fun h => hn (h ▸ hf)⟩
    exact he' (walks_mono hsub hw)
  have hnc : ¬ G.Crosses e' (compOff G F e u) := fun hc =>
    hee (onlyCrosses_compOff (G := G) (F := F) (e := e) (v := u) e' he'F hc).symm
  simp only [Crosses] at hnc
  by_cases hs : G.source e' ∈ compOff G F e u
  · -- `e'` is on the side of `u`
    have ht : G.target e' ∈ compOff G F e u := by tauto
    refine Or.inr fun x hx => ?_
    by_contra hxT
    have hsub : insideArcs G F (far G F e u) ⊆ F \ {e'} := by
      rintro g ⟨hg, hgs, -⟩
      refine ⟨hg, ?_⟩
      rintro rfl
      exact hgs hs
    exact he' (Relation.ReflTransGen.trans hx (walks_mono hsub
      (walks_insideArcs_of_mem onlyCrosses_far not_mem_far_self
        (walks_mono Set.sdiff_subset hx) hw hxT he)))
  · -- `e'` is on the side of `w`
    have ht : G.target e' ∉ compOff G F e u := by tauto
    refine Or.inl fun x hx => ?_
    have hx' : G.Walks (F \ {e}) u x := hx
    induction hx' with
    | refl => exact .refl
    | @tail a c hac hstep ih =>
      obtain ⟨g, hg, hl⟩ := hstep
      refine (ih hac).tail ⟨g, ⟨hg.1, ?_⟩, hl⟩
      rintro rfl
      rcases hl with ⟨rfl, -⟩ | ⟨-, rfl⟩
      · exact hs hac
      · exact ht hac

/-- **The component of `u` when all the arcs of `C` are deleted**, for a finite nonempty set `C` of
arcs separating `u` from `w`: it is the component of `u` off the arc of `C` nearest to `u`. -/
theorem exists_compOff_eq {C : Set E} (hC : C.Finite) (hne : C.Nonempty) (hw : G.Walks F u w)
    (hsep : ∀ e ∈ C, ¬ G.Walks (F \ {e}) u w) :
    ∃ e₀ ∈ C, {x | G.Walks (F \ C) u x} = compOff G F e₀ u := by
  obtain ⟨e₀, he₀, hmin⟩ := Set.Finite.exists_minimalFor (fun e => compOff G F e u) C hC hne
  have hle : ∀ g ∈ C, compOff G F e₀ u ⊆ compOff G F g u := fun g hg =>
    (compOff_subset_or_subset hw (hsep e₀ he₀) (hsep g hg)).elim id (hmin hg)
  refine ⟨e₀, he₀, Set.Subset.antisymm ?_ fun x hx => ?_⟩
  · exact fun x hx => walks_mono (Set.sdiff_subset_sdiff_right (Set.singleton_subset_iff.mpr he₀)) hx
  · have hx' : G.Walks (F \ {e₀}) u x := hx
    induction hx' with
    | refl => exact .refl
    | @tail a c hac hstep ih =>
      obtain ⟨g, hg, hl⟩ := hstep
      refine (ih hac).tail ⟨g, ⟨hg.1, fun hgC => ?_⟩, hl⟩
      -- both ends of `g` would be in the component of `u` off `g`
      have hac' : G.Walks (F \ {g}) a c :=
        (G.walks_symm (hle g hgC hac)).trans (hle g hgC (hac.tail ⟨g, hg, hl⟩))
      refine hsep g hgC (walks_diff_of_detour ?_ hw)
      rcases hl with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact hac'
      · exact G.walks_symm hac'

/-- **Two cut edges do not cross**: the vertices `w₁, w₂` on one side of `e` and `w₃, w₄` on the other
are not split two and two by `g`. An arc has its ends on one side of `e`, so `g` leaves one of the two
sides of `e` connected. -/
theorem OnlyCrosses.not_crossing {S : Set V} {g : E} {w₁ w₂ w₃ w₄ : V} (hS : OnlyCrosses G F e S)
    (hT : OnlyCrosses G F g T) (h₂ : G.Walks F w₁ w₂) (h₃ : G.Walks F w₁ w₃) (h₄ : G.Walks F w₁ w₄)
    (h₁S : w₁ ∈ S) (h₂S : w₂ ∈ S) (h₃S : w₃ ∉ S) (h₄S : w₄ ∉ S) (h₁T : w₁ ∈ T) (h₂T : w₂ ∉ T)
    (h₃T : w₃ ∈ T) (h₄T : w₄ ∉ T) : False := by
  by_cases hg : g ∈ insideArcs G F S
  · have hsub : insideArcs G F Sᶜ ⊆ F \ {g} := by
      rintro f ⟨hf, hfs, -⟩
      refine ⟨hf, ?_⟩
      rintro rfl
      exact hfs hg.2.1
    have hw := walks_insideArcs_of_mem hS.compl (not_not.mpr h₁S) h₃ h₄ h₃S h₄S
    exact h₄T ((hT.mem_iff_of_walks_diff (walks_mono hsub hw)).mp h₃T)
  · have hsub : insideArcs G F S ⊆ F \ {g} := by
      intro f hf
      refine ⟨hf.1, ?_⟩
      rintro rfl
      exact hg hf
    have hw := walks_insideArcs_of_mem hS h₃S ((G.walks_symm h₃).trans (Relation.ReflTransGen.refl))
      ((G.walks_symm h₃).trans h₂) h₁S h₂S
    exact h₂T ((hT.mem_iff_of_walks_diff (walks_mono hsub hw)).mp h₁T)

/-! ### The blob determined by a set of labels is unique -/

section DeterminesUnique

variable {ι : Type*} {ℓ : ι → V} {S S' : Finset ι}

/-- A blob of a subnetwork lies in a blob of the network ("`ℬ₀` is contained in a blob `ℬ` of `N`").
-/
theorem Determines.mono (h : Determines G F v ℓ S) (hS : S' ⊆ S) : Determines G F v ℓ S' :=
  fun s hs t ht hne => h s (hS hs) t (hS ht) hne

/-- Two vertices of a blob have the same incident cut edges. -/
theorem incidentCuts_congr (h : SameBlobIn G F v w) : incidentCuts G F v = incidentCuts G F w := by
  ext g
  refine and_congr_right fun _ => or_congr ?_ ?_
  · exact ⟨h.symm.trans, h.trans⟩
  · exact ⟨h.symm.trans, h.trans⟩

/-- What determines a blob does not depend on the vertex naming it. -/
theorem Determines.of_sameBlobIn (hdet : Determines G F v ℓ S) (h : SameBlobIn G F v w) :
    Determines G F w ℓ S := by
  unfold Determines
  rwa [← incidentCuts_congr h]

/-- **The blob determined by at least three labels is unique.** A cut edge between two such blobs
would have at most one label on each side. -/
theorem Determines.sameBlobIn (hdet : Determines G F v ℓ S) (hdet' : Determines G F w ℓ S)
    (h3 : 2 < S.card) (hc : ∀ s ∈ S, G.Walks F v (ℓ s)) (hvw : G.Walks F v w) :
    SameBlobIn G F v w := by
  by_contra hb
  obtain ⟨g, hg⟩ := (exists_leadsTo hvw).resolve_left hb
  have hc' : ∀ s ∈ S, G.Walks F w (ℓ s) := fun s hs => (G.walks_symm hvw).trans (hc s hs)
  have key : ∀ s ∈ S, ∀ t ∈ S, s ≠ t → (ℓ s ∉ far G F g v ∨ ℓ t ∉ far G F g v) ∧
      (ℓ s ∈ far G F g v ∨ ℓ t ∈ far G F g v) := by
    intro s hs t ht hne
    constructor
    · by_contra hcon
      push Not at hcon
      exact hne (hdet.eq_of_mem_side onlyCrosses_far not_mem_far_self hs ht (hc s hs) (hc t ht)
        hcon.1 hcon.2)
    · by_contra hcon
      push Not at hcon
      exact hne (hdet'.eq_of_mem_side onlyCrosses_far.compl (not_not.mpr hg.2) hs ht (hc' s hs)
        (hc' t ht) hcon.1 hcon.2)
  obtain ⟨r, hr, t, ht, t', ht', h1, h2, h3'⟩ := Finset.two_lt_card.mp h3
  have k1 := key r hr t ht h1
  have k2 := key r hr t' ht' h2
  have k3 := key t ht t' ht' h3'
  tauto

end DeterminesUnique

end AllmanEtAl2023
