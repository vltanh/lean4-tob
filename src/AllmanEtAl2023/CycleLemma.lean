module

public import AllmanEtAl2023.CutOrder
public import AllmanEtAl2023.SubgraphBlobs

/-!
# Lemma 3 of Allman, Baños, Mitchell, Rhodes 2023: the cycle through `A`, `K_ab`, `e₀` and `K_cd`

The network `𝒩⁺` of the source is here the subgraph induced on a set of taxa `Y` of a fixed network,
and its subnetworks are sets of arcs, before suppressing nodes of degree two, as in the source's
proof:

* `N′ = arcsOff N Y α`, the arcs ancestral to a taxon other than `α`;
* `M = arcsOff N Y d`, the arcs ancestral to a taxon other than `d`;
* `A = arcsOnly N Y α`, the arcs ancestral to `α` and no other taxon.

`lemma3_blob` is the source's statement: if `{a,b,c,d}` determines a blob on `Y`, and a cut edge of
`N′` separates `a, b` from `c, d`, then `{a,b,c,α}` determines a blob of `M`. The proof follows the
source's (`notes/sources/allman2023.txt`, lines 207-215), in its order, with paths and the cycle as
sets of arcs (`IsPathIn`, `IsDirectedPath`, `IsCycleThrough`). The source's "`N \ {e0}`" and "`Kbc`"
are misprints for `N′ \ {e₀}` and `K_cd`.

* `exists_determines_three`, `exists_cutEdgeData` (line 208): the blob `ℬ′` of `N′` determined by
  `a, b, c`, the cut edge `e₀` of `N′` incident to it through which paths to `c` pass, and the
  components `K_ab`, `K_cd` of `N′ \ {e₀}`, which are `compOff _ e₀ u` and `compOff _ e₀ w`;
* `CutEdgeData.arc_cases` (line 208): the arcs are partitioned by `A`, `K_ab`, `{e₀}`, `K_cd`;
* `CutEdgeData.exists_meet_near` (line 209): `P₁`, with its contradiction argument
  `CutEdgeData.onlyCrosses_of_no_meet`;
* `CutEdgeData.walks_near` (line 210): `P₂`;
* `CutEdgeData.exists_meet_far`, `exists_directedPath_of_walks` (line 211): `y`, and the directed
  path from `y` to `α` within `A`;
* `CutEdgeData.exists_commonAncestor`, `CutEdgeData.exists_leastCommonAncestor`,
  `CutEdgeData.directedPath_subset`, `CutEdgeData.Paths.isDirectedPath_P₄` (line 212): `z` and `P₄`;
* `CutEdgeData.walks_far_to_lca` (line 213): `P₃`;
* `CutEdgeData.exists_paths`: all of these, in the source's order (`CutEdgeData.Paths`);
* `CutEdgeData.Paths.exists_cycle` (line 214): the cycle `C` in `M`;
* `CutEdgeData.determines_off` (lines 214-215): `C` and `ℬ′` lie in one blob of `M`, and the rest, by
  Lemma 2.

The source leaves some steps implicit. They are proved here:

* `e₀` separates `a, b` from `c, d`, for `d` as well as `c` (`exists_cutEdgeData`);
* `ℬ′` and `P₂` lie in `M`, since no node of `K_ab` is ancestral only to `d`
  (`CutEdgeData.near_reaches`);
* the directed path from `z` to `y` avoids `e₀` (`CutEdgeData.not_reaches_through`), and `P₃` can be
  kept in `K_cd` (`CutEdgeData.walks_far_to_lca`), so `e₀` is used once by the closed walk;
* `P₁` meets `C` after the self-intersections are removed, which the source's "the initial segment
  of `P₁` gives a path from `α` to `C`" needs. `P₁` and the directed path from `y` to `α` both lie in
  `A` and both end at `α`, and `m`, the last node along `P₁` from `α` towards `x` on that directed
  path, is on `C` (`CutEdgeData.Paths.exists_meet`, `CutEdgeData.Paths.crosses_side`);
* `{a, b, c}` determines `ℬ′` in `M ∩ N′` (`Determines.of_subset`).
-/

@[expose] public noncomputable section

open Phylogenetics Phylogenetics.RootedNetwork Phylogenetics.DirectedMultigraph

open Phylogenetics.DirectedMultigraph

namespace AllmanEtAl2023

variable {V E X : Type*} {N : RootedNetwork V E X}

/-! ### Directed paths, undirected walks, and pendant taxa -/

/-- A directed path, as a walk in any set of arcs containing the arcs on it. -/
theorem walks_of_reaches {F : Set E} {u v : V} (h : N.graph.Reaches u v)
    (hF : ∀ f, N.graph.Reaches u (N.graph.source f) → N.graph.Reaches (N.graph.target f) v → f ∈ F) :
    N.graph.Walks F u v := by
  revert hF
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact fun _ => .refl
  | @head a b hab hbv ih =>
    intro hF
    obtain ⟨f, rfl, rfl⟩ := hab
    exact Relation.ReflTransGen.head ⟨f, hF f .refl hbv, Or.inl ⟨rfl, rfl⟩⟩
      (ih fun g h1 h2 => hF g (h1.head ⟨f, rfl, rfl⟩) h2)

/-- A directed path avoiding `e`, as a walk in any set of arcs containing the arcs other than `e`
above its end. -/
theorem walks_of_avoidingReach {F : Set E} {e : E} {u v : V} (h : N.AvoidingReach e u v)
    (hF : ∀ f, f ≠ e → N.graph.Reaches (N.graph.target f) v → f ∈ F) : N.graph.Walks F u v := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact .refl
  | @head a b hab hbv ih =>
    obtain ⟨f, hfe, rfl, rfl⟩ := hab
    exact Relation.ReflTransGen.head ⟨f, hF f hfe (AvoidingReach.reaches hbv), Or.inl ⟨rfl, rfl⟩⟩ ih

/-- A vertex of an induced subgraph is joined to the root in it. -/
theorem walks_root_ancestral (hN : N.IsPhylogenetic) {Z : Set X} {v : V}
    (hv : v ∈ N.ancestralVertices Z) : N.graph.Walks (N.ancestralArcs Z) N.root v :=
  walks_of_reaches (hN.root_reaches v) fun _ _ hf => N.mem_ancestralVertices_of_reaches hf hv

/-- An induced subgraph is connected. -/
theorem walks_ancestral (hN : N.IsPhylogenetic) {Z : Set X} {x y : V}
    (hx : x ∈ N.ancestralVertices Z) (hy : y ∈ N.ancestralVertices Z) :
    N.graph.Walks (N.ancestralArcs Z) x y :=
  (N.graph.walks_symm (walks_root_ancestral hN hx)).trans (walks_root_ancestral hN hy)

/-- A walk in an induced subgraph stays in it. -/
theorem mem_ancestralVertices_of_walks {Z : Set X} {x y : V} (hx : x ∈ N.ancestralVertices Z)
    (h : N.graph.Walks (N.ancestralArcs Z) x y) : y ∈ N.ancestralVertices Z := by
  induction h with
  | refl => exact hx
  | @tail a c _ hstep _ =>
    obtain ⟨g, hg, hl⟩ := hstep
    rcases hl with ⟨-, rfl⟩ | ⟨rfl, -⟩
    · exact hg
    · exact N.source_mem_ancestralVertices hg

/-- A directed path entering a side of a cut edge does so through the cut edge. -/
theorem reaches_of_enters {F : Set E} {g : E} {T : Set V} {p q : V} (hO : OnlyCrosses N.graph F g T)
    (hp : p ∉ T) (hq : q ∈ T) (hr : N.graph.Reaches p q)
    (hF : ∀ f, N.graph.Reaches (N.graph.target f) q → f ∈ F) :
    N.graph.Reaches p (N.graph.source g) ∧ N.graph.source g ∉ T ∧ N.graph.target g ∈ T ∧
      N.graph.Reaches (N.graph.target g) q := by
  induction hr with
  | refl => exact absurd hq hp
  | @tail a b hpa hab ih =>
    obtain ⟨f, rfl, rfl⟩ := hab
    by_cases ha : N.graph.source f ∈ T
    · obtain ⟨h1, h2, h3, h4⟩ := ih ha fun k hk => hF k (hk.tail ⟨f, rfl, rfl⟩)
      exact ⟨h1, h2, h3, h4.tail ⟨f, rfl, rfl⟩⟩
    · have hfg := hO f (hF f .refl) (Or.inr ⟨hq, ha⟩)
      subst hfg
      exact ⟨hpa, ha, hq, .refl⟩

/-- A taxon has one arc, entering it. -/
theorem exists_leaf_arc (hN : N.IsPhylogenetic) (x : X) :
    ∃ g, N.graph.target g = N.leaf x ∧ N.graph.source g ≠ N.graph.target g ∧
      ∀ f, (N.graph.source f = N.leaf x ∨ N.graph.target f = N.leaf x) → f = g := by
  have : Finite E := hN.finite_arcs
  obtain ⟨g, hg⟩ := Set.ncard_eq_one.mp (hN.leaf_indegree x)
  have hgx : N.graph.target g = N.leaf x := by
    have hmem : g ∈ {e | N.graph.target e = N.leaf x} := hg ▸ rfl
    exact hmem
  have hout := (N.graph.outdegree_eq_zero_iff (N.leaf x)).mp ((hN.leaves _).mpr ⟨x, rfl⟩)
  refine ⟨g, hgx, fun h => hN.acyclic (N.graph.target g) (.single ⟨g, h, rfl⟩), ?_⟩
  rintro f (h | h)
  · exact absurd h (hout f)
  · have hmem : f ∈ {e | N.graph.target e = N.leaf x} := h
    rwa [hg] at hmem

theorem isPendantIn_leaf (hN : N.IsPhylogenetic) (x : X) (F : Set E) :
    IsPendantIn N.graph F (N.leaf x) := by
  obtain ⟨g, -, hloop, hg⟩ := exists_leaf_arc hN x
  exact ⟨g, hloop, fun f _ h => hg f h⟩

/-- A taxon reaches only itself. -/
theorem eq_of_leaf_reaches (hN : N.IsPhylogenetic) {x : X} {v : V} (h : N.graph.Reaches (N.leaf x) v) :
    v = N.leaf x := by
  have : Finite E := hN.finite_arcs
  exact N.graph.eq_of_reaches_of_outdegree_eq_zero h ((hN.leaves _).mpr ⟨x, rfl⟩)

/-! ### Blobs of induced subgraphs determined by taxa -/

section Induced

variable {Z : Set X} {S : Finset X}

/-- If no cut edge of the subgraph induced on `Z` has two elements of `S` on each side, `S`, with at
least three taxa of `Z`, determines a blob of that subgraph. For three taxa this is the source's
remark after its Definition 8, and for four the characterization of B-quartets after its Definition
12. -/
theorem exists_determines_of_no_split (hN : N.IsPhylogenetic) (hS : ∀ s ∈ S, s ∈ Z) (h3 : 3 ≤ S.card)
    (hsplit : ∀ e T, OnlyCrosses N.graph (N.ancestralArcs Z) e T → TwoIn N.leaf S T →
      TwoIn N.leaf S Tᶜ → False) :
    ∃ v ∈ N.ancestralVertices Z, Determines N.graph (N.ancestralArcs Z) v N.leaf S := by
  classical
  have : Finite V := hN.finite_vertices
  have hleafU : ∀ s ∈ S, N.leaf s ∈ N.ancestralVertices Z :=
    fun s hs => N.leaf_mem_ancestralVertices (hS s hs)
  -- the arc at a taxon starts the search
  have hstart : ∃ e T, e ∈ N.ancestralArcs Z ∧ OnlyCrosses N.graph (N.ancestralArcs Z) e T ∧
      N.graph.Crosses e T ∧ TwoIn N.leaf S T := by
    obtain ⟨a, ha⟩ : S.Nonempty := Finset.card_pos.mp (by omega)
    obtain ⟨g, hgt, hloop, hg⟩ := exists_leaf_arc hN a
    have h2 : 1 < (S.erase a).card := by
      rw [Finset.card_erase_of_mem ha]
      omega
    obtain ⟨t, ht, t', ht', hne⟩ := Finset.one_lt_card.mp h2
    obtain ⟨hta, htS⟩ := Finset.mem_erase.mp ht
    obtain ⟨hta', htS'⟩ := Finset.mem_erase.mp ht'
    refine ⟨g, ({N.leaf a}ᶜ : Set V), ?_, ?_, ?_, t, htS, t', htS', hne, ?_, ?_⟩
    · change N.graph.target g ∈ N.ancestralVertices Z
      rw [hgt]
      exact hleafU a ha
    · refine fun f _ hc => hg f ?_
      rcases hc with ⟨-, h1⟩ | ⟨-, h1⟩
      · exact Or.inr (by simpa using h1)
      · exact Or.inl (by simpa using h1)
    · refine Or.inl ⟨?_, by simp [hgt]⟩
      simpa [hgt] using fun h => hloop (h.trans hgt.symm)
    · simpa using fun h => hta (hN.leaf_injective h)
    · simpa using fun h => hta' (hN.leaf_injective h)
  obtain ⟨v, hv, hmed⟩ := exists_median (F := N.ancestralArcs Z) (U := N.ancestralVertices Z) (ℓ := N.leaf)
    (S := S) (fun x hx y hy => walks_ancestral hN hx hy)
    (fun f hf => ⟨N.source_mem_ancestralVertices hf, hf⟩) hleafU hstart hsplit
  refine ⟨v, hv, determines_of_median h3 (fun _ _ _ _ h => hN.leaf_injective h)
    (fun s _ => isPendantIn_leaf hN s _) (fun s hs => walks_ancestral hN hv (hleafU s hs)) hmed⟩

/-- **Three taxa determine a blob** (the source, after its Definition 8). -/
theorem exists_determines_three [DecidableEq X] (hN : N.IsPhylogenetic) {a b c : X} (ha : a ∈ Z) (hb : b ∈ Z)
    (hc : c ∈ Z) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    ∃ v ∈ N.ancestralVertices Z, Determines N.graph (N.ancestralArcs Z) v N.leaf {a, b, c} := by
  have h3 : ({a, b, c} : Finset X).card = 3 := by
    rw [Finset.card_insert_of_notMem (by simp [hab, hac]), Finset.card_pair hbc]
  refine exists_determines_of_no_split hN ?_ h3.ge ?_
  · intro s hs
    simp only [Finset.mem_insert, Finset.mem_singleton] at hs
    rcases hs with rfl | rfl | rfl <;> assumption
  · rintro e T - ⟨s, hs, t, ht, hst, hsT, htT⟩ ⟨s', hs', t', ht', hst', hsT', htT'⟩
    have hne : ∀ {x y : X}, N.leaf x ∈ T → N.leaf y ∈ Tᶜ → x ≠ y := by
      rintro x y hx hy rfl
      exact hy hx
    have h4 : ({s, t, s', t'} : Finset X).card = 4 :=
      TreeMetric.card_four_of_ne hst (hne hsT hsT') (hne hsT htT') (hne htT hsT') (hne htT htT') hst'
    have hsub : ({s, t, s', t'} : Finset X) ⊆ {a, b, c} := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> assumption
    have := Finset.card_le_card hsub
    omega

end Induced

/-- A blob determined by `{a,b,c,d}` has no cut edge separating `a, b` from `c, d`. -/
theorem Determines.no_split [DecidableEq X] {F : Set E} {v : V} {a b c d : X} {e : E} {T : Set V}
    (hdet : Determines N.graph F v N.leaf {a, b, c, d}) (hab : a ≠ b) (hcd : c ≠ d)
    (hw : ∀ s ∈ ({a, b, c, d} : Finset X), N.graph.Walks F v (N.leaf s))
    (hT : OnlyCrosses N.graph F e T) (ha : N.leaf a ∈ T) (hb : N.leaf b ∈ T) (hc : N.leaf c ∉ T)
    (hd : N.leaf d ∉ T) : False := by
  have hma : a ∈ ({a, b, c, d} : Finset X) := by simp
  have hmb : b ∈ ({a, b, c, d} : Finset X) := by simp
  have hmc : c ∈ ({a, b, c, d} : Finset X) := by simp
  have hmd : d ∈ ({a, b, c, d} : Finset X) := by simp
  by_cases hv : v ∈ T
  · exact hcd (hdet.eq_of_mem_side hT.compl (not_not.mpr hv) hmc hmd (hw c hmc) (hw d hmd) hc hd)
  · exact hab (hdet.eq_of_mem_side hT hv hma hmb (hw a hma) (hw b hmb) ha hb)

/-- On the whole network, the cut edges are the bridges of `TOBQMC`. -/
theorem isCutIn_univ_iff {e : E} : IsCutIn N.graph Set.univ e ↔ N.graph.underlying.IsBridge e := by
  rw [N.graph.isBridge_iff_not_walks_delete, Set.compl_eq_univ_sdiff]
  exact ⟨fun h' => h'.2, fun h' => ⟨Set.mem_univ e, h'⟩⟩

/-- On the whole network, `SameBlobIn` is the blob relation of the graph. -/
theorem sameBlobIn_univ_iff {u v : V} : SameBlobIn N.graph Set.univ u v ↔ N.graph.blobSetoid u v := by
  constructor
  · intro h
    refine Relation.ReflTransGen.mono ?_ _ _ h
    rintro a b ⟨e, he, hl⟩
    exact ⟨e, fun hb => he.2 (isCutIn_univ_iff.mpr hb), hl⟩
  · intro h
    refine Relation.ReflTransGen.mono ?_ _ _ h
    rintro a b ⟨e, he, hl⟩
    exact ⟨e, ⟨Set.mem_univ e, fun hc => he (isCutIn_univ_iff.mp hc)⟩, hl⟩

/-! ### The subnetworks of Allman et al.'s proof -/

section Setup

variable [DecidableEq X] {Y : Finset X} {α a b c d t : X} {e₀ g : E} {u w x y z k : V}

/-- The arcs of the subgraph induced on `Y` ancestral to a taxon other than `t`: the subnetwork `N′`
of the source for `t = α`, and `M` for `t = d`. -/
abbrev arcsOff (N : RootedNetwork V E X) (Y : Finset X) (t : X) : Set E :=
  N.ancestralArcs ((Y.erase t : Finset X) : Set X)

/-- The vertices of `arcsOff N Y t`. -/
abbrev vertsOff (N : RootedNetwork V E X) (Y : Finset X) (t : X) : Set V :=
  N.ancestralVertices ((Y.erase t : Finset X) : Set X)

/-- The subnetwork `A` of the source: the arcs ancestral to `t` and no other taxon of `Y`. -/
def arcsOnly (N : RootedNetwork V E X) (Y : Finset X) (t : X) : Set E :=
  N.ancestralArcs (Y : Set X) \ arcsOff N Y t

theorem mem_vertsOff_iff : x ∈ vertsOff N Y t ↔ ∃ s ∈ Y, s ≠ t ∧ N.graph.Reaches x (N.leaf s) := by
  constructor
  · rintro ⟨s, hs, h⟩
    obtain ⟨h1, h2⟩ := Finset.mem_erase.mp (Finset.mem_coe.mp hs)
    exact ⟨s, h2, h1, h⟩
  · rintro ⟨s, hs, hne, h⟩
    exact ⟨s, Finset.mem_coe.mpr (Finset.mem_erase.mpr ⟨hne, hs⟩), h⟩

theorem leaf_mem_vertsOff {s : X} (hs : s ∈ Y) (hne : s ≠ t) : N.leaf s ∈ vertsOff N Y t :=
  mem_vertsOff_iff.mpr ⟨s, hs, hne, .refl⟩

theorem mem_arcsOff_of_reaches {s : X} (hs : s ∈ Y) (hne : s ≠ t)
    (h : N.graph.Reaches (N.graph.target g) (N.leaf s)) : g ∈ arcsOff N Y t :=
  mem_vertsOff_iff.mpr ⟨s, hs, hne, h⟩

theorem arcsOff_subset (t : X) : arcsOff N Y t ⊆ N.ancestralArcs (Y : Set X) :=
  N.ancestralArcs_mono fun _ h => Finset.mem_coe.mpr (Finset.mem_of_mem_erase (Finset.mem_coe.mp h))

/-- An arc of `A` has a directed path to the taxon, inside `A`. -/
theorem reaches_of_mem_arcsOnly (hg : g ∈ arcsOnly N Y t) : N.graph.Reaches (N.graph.target g) (N.leaf t) := by
  obtain ⟨s, hs, hr⟩ := hg.1
  by_cases hst : s = t
  · exact hst ▸ hr
  · exact absurd (mem_vertsOff_iff.mpr ⟨s, Finset.mem_coe.mp hs, hst, hr⟩) hg.2

/-- The arcs of `A` meeting `N′` at most at `x`. A path in these from the taxon `t` stops at `x`, its
one node in `N′`: these are the source's "paths from `α` to `N′` within `A`" (line 209). -/
def arcsOnlyTo (N : RootedNetwork V E X) (Y : Finset X) (t : X) (x : V) : Set E :=
  {f | f ∈ arcsOnly N Y t ∧ (N.graph.source f ∈ vertsOff N Y t → N.graph.source f = x)}

theorem arcsOnlyTo_subset : arcsOnlyTo N Y t x ⊆ arcsOnly N Y t := fun _ hf => hf.1

/-- The head of an arc of `A` is not in `N′`, so a node of `N′` at an arc of `arcsOnlyTo N Y t x` is
`x`. -/
theorem eq_of_mem_arcsOnlyTo {f : E} {v : V} (hf : f ∈ arcsOnlyTo N Y t x)
    (hv : N.graph.source f = v ∨ N.graph.target f = v) (hvN : v ∈ vertsOff N Y t) : v = x := by
  rcases hv with rfl | rfl
  · exact hf.2 hvN
  · exact absurd hvN hf.1.2

/-- An arc below an arc of `A` is in `A`, and meets `N′` nowhere. -/
theorem mem_arcsOnlyTo_of_reaches {f : E} (ht : t ∈ Y) (hg : g ∈ arcsOnly N Y t)
    (h1 : N.graph.Reaches (N.graph.target g) (N.graph.source f))
    (h2 : N.graph.Reaches (N.graph.target f) (N.leaf t)) : f ∈ arcsOnlyTo N Y t x := by
  have hoff : ∀ {v}, N.graph.Reaches (N.graph.target g) v → v ∉ vertsOff N Y t :=
    fun hr hv => hg.2 (N.mem_ancestralVertices_of_reaches hr hv)
  exact ⟨⟨⟨t, Finset.mem_coe.mpr ht, h2⟩, hoff (h1.tail ⟨f, rfl, rfl⟩)⟩, fun h => absurd h (hoff h1)⟩

/-- The tail of an arc of `A` is joined to the taxon by a path of `arcsOnlyTo`: the arc, then a
directed path below it. -/
theorem walks_source_arcsOnlyTo (ht : t ∈ Y) (hg : g ∈ arcsOnly N Y t) :
    N.graph.Walks (arcsOnlyTo N Y t (N.graph.source g)) (N.graph.source g) (N.leaf t) :=
  Relation.ReflTransGen.head ⟨g, ⟨hg, fun _ => rfl⟩, Or.inl ⟨rfl, rfl⟩⟩
    (walks_of_reaches (reaches_of_mem_arcsOnly hg) fun _ h1 h2 =>
      mem_arcsOnlyTo_of_reaches ht hg h1 h2)

/-- **The directed path from `y` to `α` within `A`** (line 211): "Because `y ∈ K_cd`, `y` is ancestral
to a taxon other than `α`. Since the edge in the path incident to `y` is ancestral only to `α`, that
edge's parent node must be `y` and there is a directed path from `y` to `α` within `A`. Choose some
such directed path." It meets `N′` only at `y`. -/
theorem exists_directedPath_of_walks (ht : t ∈ Y) (hy : y ∈ vertsOff N Y t)
    (h : N.graph.Walks (arcsOnly N Y t) (N.leaf t) y) :
    ∃ R, IsDirectedPath N.graph y R (N.leaf t) ∧ R ⊆ arcsOnlyTo N Y t y := by
  rcases Relation.ReflTransGen.cases_tail h with rfl | ⟨_, -, f, hf, hl⟩
  · exact ⟨∅, .refl, Set.empty_subset _⟩
  · rcases hl with ⟨-, rfl⟩ | ⟨rfl, -⟩
    · exact absurd hy hf.2
    · obtain ⟨R, hR⟩ := exists_isDirectedPath (reaches_of_mem_arcsOnly hf)
      have hf1 : IsDirectedPath N.graph (N.graph.source f) (insert f ∅) (N.graph.target f) :=
        .tail f .refl
      refine ⟨_, hf1.trans hR, ?_⟩
      rintro g ((rfl | hg) | hg)
      · exact ⟨hf, fun _ => rfl⟩
      · exact (Set.notMem_empty g hg).elim
      · exact mem_arcsOnlyTo_of_reaches ht hf (hR.reaches_of_mem hg).1 (hR.reaches_of_mem hg).2

/-- No cut edge of the subgraph induced on `Y` separates `a, b` from `c, d`. This is what the proof
of Lemma 3 uses of `{a, b, c, d}` being a B-quartet. -/
def NoSplitOn (N : RootedNetwork V E X) (Y : Finset X) (a b c d : X) : Prop :=
  ∀ e T, OnlyCrosses N.graph (N.ancestralArcs (Y : Set X)) e T → N.leaf a ∈ T → N.leaf b ∈ T →
    N.leaf c ∉ T → N.leaf d ∉ T → False

/-- The arcs of `M ∩ N′` inside the component of `k` in `N′ \ {e₀}`: those of `K_ab` for `k = u`, and
those of `K_cd` for `k = w`. -/
abbrev arcsIn (N : RootedNetwork V E X) (Y : Finset X) (α d : X) (e₀ : E) (k : V) : Set E :=
  insideArcs N.graph (arcsOff N Y α ∩ arcsOff N Y d) (compOff N.graph (arcsOff N Y α) e₀ k)

/-- The cut edge `e₀` of the source, with its ends `u ∈ K_ab` and `w ∈ K_cd`. -/
structure CutEdgeData (N : RootedNetwork V E X) (Y : Finset X) (α a b c d : X) (e₀ : E) (u w : V) : Prop where
  link : Links N.graph e₀ u w
  cut : IsCutIn N.graph (arcsOff N Y α) e₀
  ha : N.graph.Walks (arcsOff N Y α \ {e₀}) u (N.leaf a)
  hb : N.graph.Walks (arcsOff N Y α \ {e₀}) u (N.leaf b)
  hc : N.graph.Walks (arcsOff N Y α \ {e₀}) w (N.leaf c)
  hd : N.graph.Walks (arcsOff N Y α \ {e₀}) w (N.leaf d)
  cY : c ∈ Y
  dY : d ∈ Y
  cα : c ≠ α
  dα : d ≠ α
  cd : c ≠ d

namespace CutEdgeData

/-- `K_ab` and `K_cd` are disjoint. -/
theorem disjoint (D : CutEdgeData N Y α a b c d e₀ u w)
    (h1 : x ∈ compOff N.graph (arcsOff N Y α) e₀ u) (h2 : x ∈ compOff N.graph (arcsOff N Y α) e₀ w) : False :=
  D.cut.not_walks D.link (Relation.ReflTransGen.trans h1 (N.graph.walks_symm h2))

theorem u_not_mem (D : CutEdgeData N Y α a b c d e₀ u w) :
    u ∉ compOff N.graph (arcsOff N Y α) e₀ w :=
  fun h => D.disjoint Relation.ReflTransGen.refl h

theorem w_not_mem (D : CutEdgeData N Y α a b c d e₀ u w) :
    w ∉ compOff N.graph (arcsOff N Y α) e₀ u :=
  fun h => D.disjoint h Relation.ReflTransGen.refl

theorem source_mem (D : CutEdgeData N Y α a b c d e₀ u w) : N.graph.source e₀ ∈ vertsOff N Y α :=
  N.source_mem_ancestralVertices D.cut.1

theorem target_mem (D : CutEdgeData N Y α a b c d e₀ u w) : N.graph.target e₀ ∈ vertsOff N Y α :=
  D.cut.1

theorem u_mem (D : CutEdgeData N Y α a b c d e₀ u w) : u ∈ vertsOff N Y α := by
  rcases D.link with ⟨rfl, -⟩ | ⟨-, rfl⟩
  · exact D.source_mem
  · exact D.target_mem

theorem w_mem (D : CutEdgeData N Y α a b c d e₀ u w) : w ∈ vertsOff N Y α := by
  rcases D.link with ⟨-, rfl⟩ | ⟨rfl, -⟩
  · exact D.target_mem
  · exact D.source_mem

/-- The vertices of `K_ab` and of `K_cd` are vertices of `N′`. -/
theorem mem_of_mem_comp (hk : k ∈ vertsOff N Y α) (hx : x ∈ compOff N.graph (arcsOff N Y α) e₀ k) :
    x ∈ vertsOff N Y α :=
  mem_ancestralVertices_of_walks hk (walks_mono Set.sdiff_subset hx)

/-- A directed path avoiding `e₀` to a node of `N′` stays in a component of `N′ \ {e₀}`. -/
theorem walks_off (h : N.AvoidingReach e₀ x y) (hy : y ∈ vertsOff N Y α) :
    N.graph.Walks (arcsOff N Y α \ {e₀}) x y :=
  walks_of_avoidingReach h fun _ hfe hf => ⟨N.mem_ancestralVertices_of_reaches hf hy, hfe⟩

/-- If `e₀` is directed from `K_ab` to `K_cd`, its head is above every node of `K_cd`. -/
theorem reaches_of_mem (hN : N.IsPhylogenetic) (D : CutEdgeData N Y α a b c d e₀ u w)
    (hs : N.graph.source e₀ = u) (ht : N.graph.target e₀ = w)
    (hx : x ∈ compOff N.graph (arcsOff N Y α) e₀ w) (hxV : x ∈ vertsOff N Y α) :
    N.graph.Reaches w x := by
  rcases reaches_split e₀ (hN.root_reaches x) with h | ⟨-, h⟩
  · have h1 := walks_off h hxV
    have h2 := walks_off (Y := Y) (α := α)
      (avoidingReach_of_reaches_source hN.acyclic (hN.root_reaches _) .refl) D.source_mem
    rw [hs] at h2
    exact (D.disjoint (Relation.ReflTransGen.trans (N.graph.walks_symm h2) h1) hx).elim
  · exact ht ▸ h

/-- If `e₀` is directed from `K_cd` to `K_ab`, no node of `K_ab` is above a node of `K_cd`. -/
theorem not_reaches (hN : N.IsPhylogenetic) (D : CutEdgeData N Y α a b c d e₀ u w)
    (hs : N.graph.source e₀ = w) (hx : x ∈ compOff N.graph (arcsOff N Y α) e₀ u)
    (hy : y ∈ compOff N.graph (arcsOff N Y α) e₀ w) (hyV : y ∈ vertsOff N Y α) :
    ¬ N.graph.Reaches x y := by
  intro hr
  rcases reaches_split e₀ hr with h | ⟨h, -⟩
  · exact D.disjoint (Relation.ReflTransGen.trans hx (walks_off h hyV)) hy
  · have h1 := walks_off (Y := Y) (α := α)
      (avoidingReach_of_reaches_source hN.acyclic h .refl) D.source_mem
    rw [hs] at h1
    exact D.disjoint hx (Relation.ReflTransGen.trans (Relation.ReflTransGen.refl) (N.graph.walks_symm h1))

/-- Every node of `K_ab` is above a taxon other than `α, d`. The source doesn't state this, and it
is why `ℬ′` and the path `P₂` lie in `M`: paths from `K_ab` to `d` pass through `e₀`, so they can
also lead to `c`. -/
theorem near_reaches (hN : N.IsPhylogenetic) (D : CutEdgeData N Y α a b c d e₀ u w)
    (hx : x ∈ compOff N.graph (arcsOff N Y α) e₀ u) :
    ∃ s ∈ Y, s ≠ α ∧ s ≠ d ∧ N.graph.Reaches x (N.leaf s) := by
  obtain ⟨s, hsY, hsα, hr⟩ := mem_vertsOff_iff.mp (mem_of_mem_comp D.u_mem hx)
  by_cases hsd : s = d
  · subst hsd
    have hdV : N.leaf s ∈ vertsOff N Y α := leaf_mem_vertsOff D.dY D.dα
    rcases D.link with ⟨hs, ht⟩ | ⟨hs, -⟩
    · refine ⟨c, D.cY, D.cα, D.cd, ?_⟩
      rcases reaches_split e₀ hr with h | ⟨h, -⟩
      · exact (D.disjoint (Relation.ReflTransGen.trans hx (walks_off h hdV)) D.hd).elim
      · have h2 := D.reaches_of_mem hN hs ht D.hc (leaf_mem_vertsOff D.cY D.cα)
        rw [← ht] at h2
        exact (h.tail ⟨e₀, rfl, rfl⟩).trans h2
    · exact (D.not_reaches hN hs hx D.hd hdV hr).elim
  · exact ⟨s, hsY, hsα, hsd, hr⟩

/-- A node of `K_ab` is a node of `M ∩ N′`. -/
theorem near_mem (hN : N.IsPhylogenetic) (D : CutEdgeData N Y α a b c d e₀ u w)
    (hx : x ∈ compOff N.graph (arcsOff N Y α) e₀ u) :
    x ∈ vertsOff N Y α ∧ x ∈ vertsOff N Y d := by
  obtain ⟨s, hs, hsα, hsd, hr⟩ := D.near_reaches hN hx
  exact ⟨mem_vertsOff_iff.mpr ⟨s, hs, hsα, hr⟩, mem_vertsOff_iff.mpr ⟨s, hs, hsd, hr⟩⟩

/-- An arc of `N′` other than `e₀` at a node of `K_ab` has its head in `K_ab`, so it is in `M`. -/
theorem arc_near_mem (hN : N.IsPhylogenetic) (D : CutEdgeData N Y α a b c d e₀ u w)
    (hg : g ∈ arcsOff N Y α \ {e₀}) (hl : Links N.graph g x y)
    (hx : x ∈ compOff N.graph (arcsOff N Y α) e₀ u) : g ∈ arcsOff N Y d := by
  have hy : y ∈ compOff N.graph (arcsOff N Y α) e₀ u := hx.tail ⟨g, hg, hl⟩
  rcases hl with ⟨-, rfl⟩ | ⟨-, rfl⟩
  · exact (D.near_mem hN hy).2
  · exact (D.near_mem hN hx).2

/-- `e₀` is an arc of `M`: it is above a taxon other than `d`. -/
theorem mem_off (hN : N.IsPhylogenetic) (D : CutEdgeData N Y α a b c d e₀ u w) :
    e₀ ∈ arcsOff N Y d := by
  rcases D.link with ⟨hs, ht⟩ | ⟨-, ht⟩
  · have h2 := D.reaches_of_mem hN hs ht D.hc (leaf_mem_vertsOff D.cY D.cα)
    exact mem_arcsOff_of_reaches D.cY D.cd (ht ▸ h2)
  · change N.graph.target e₀ ∈ vertsOff N Y d
    rw [ht]
    exact (D.near_mem hN Relation.ReflTransGen.refl).2

theorem w_mem_off (hN : N.IsPhylogenetic) (D : CutEdgeData N Y α a b c d e₀ u w) :
    w ∈ vertsOff N Y d := by
  rcases D.link with ⟨-, rfl⟩ | ⟨rfl, -⟩
  · exact D.mem_off hN
  · exact N.source_mem_ancestralVertices (D.mem_off hN)

/-- `M ∩ N′` stays connected: deleting the arcs ancestral only to `d` from `N′` leaves every
remaining node joined to the root. -/
theorem walks_root_inter (hN : N.IsPhylogenetic) (hx : x ∈ vertsOff N Y α) (hx' : x ∈ vertsOff N Y d) :
    N.graph.Walks (arcsOff N Y α ∩ arcsOff N Y d) N.root x :=
  walks_of_reaches (hN.root_reaches x) fun _ _ hf =>
    ⟨N.mem_ancestralVertices_of_reaches hf hx, N.mem_ancestralVertices_of_reaches hf hx'⟩

theorem walks_inter (hN : N.IsPhylogenetic) (hx : x ∈ vertsOff N Y α) (hx' : x ∈ vertsOff N Y d)
    (hy : y ∈ vertsOff N Y α) (hy' : y ∈ vertsOff N Y d) :
    N.graph.Walks (arcsOff N Y α ∩ arcsOff N Y d) x y :=
  (N.graph.walks_symm (walks_root_inter hN hx hx')).trans (walks_root_inter hN hy hy')

/-- **The partition of the source**: an arc of the subgraph induced on `Y` is in `A` or is `e₀`, or
lies in `K_ab` or in `K_cd`. These are disjoint by the definition of `A`, and by `disjoint`. -/
theorem arc_cases (hN : N.IsPhylogenetic) (D : CutEdgeData N Y α a b c d e₀ u w) {f : E}
    (hf : f ∈ N.ancestralArcs (Y : Set X)) :
    f ∈ arcsOnly N Y α ∨ f = e₀ ∨
      (f ∈ arcsOff N Y α ∧ N.graph.source f ∈ compOff N.graph (arcsOff N Y α) e₀ u ∧
        N.graph.target f ∈ compOff N.graph (arcsOff N Y α) e₀ u) ∨
      (f ∈ arcsOff N Y α ∧ N.graph.source f ∈ compOff N.graph (arcsOff N Y α) e₀ w ∧
        N.graph.target f ∈ compOff N.graph (arcsOff N Y α) e₀ w) := by
  by_cases hfN : f ∈ arcsOff N Y α
  · by_cases hfe : f = e₀
    · exact Or.inr (Or.inl hfe)
    · have hstep : N.graph.AdjOn (arcsOff N Y α \ {e₀}) (N.graph.source f) (N.graph.target f) :=
        ⟨f, ⟨hfN, hfe⟩, Or.inl ⟨rfl, rfl⟩⟩
      by_cases hs : N.graph.source f ∈ compOff N.graph (arcsOff N Y α) e₀ u
      · exact Or.inr (Or.inr (Or.inl ⟨hfN, hs, Relation.ReflTransGen.tail hs hstep⟩))
      · have hw := walks_of_not_walks D.link
          (walks_ancestral hN D.u_mem (N.source_mem_ancestralVertices hfN)) hs
        exact Or.inr (Or.inr (Or.inr ⟨hfN, hw, Relation.ReflTransGen.tail hw hstep⟩))
  · exact Or.inl ⟨hf, hfN⟩

/-- **The contradiction argument for `P₁`** (line 209): if no path from `α` to `N′` within `A` ends at
a node of a component of `N′ \ {e₀}`, then no arc of `A` is at that component, so `e₀` is the only arc
of the subgraph induced on `Y` crossing it. -/
theorem onlyCrosses_of_no_meet (hαY : α ∈ Y) (hk : k ∈ vertsOff N Y α)
    (hK : ∀ x ∈ compOff N.graph (arcsOff N Y α) e₀ k,
      ¬ N.graph.Walks (arcsOnlyTo N Y α x) (N.leaf α) x) :
    OnlyCrosses N.graph (N.ancestralArcs (Y : Set X)) e₀ (compOff N.graph (arcsOff N Y α) e₀ k) := by
  intro f hf hc
  by_cases hfN : f ∈ arcsOff N Y α
  · exact onlyCrosses_compOff f hfN hc
  · have hfA : f ∈ arcsOnly N Y α := ⟨hf, hfN⟩
    rcases hc with ⟨h, -⟩ | ⟨h, -⟩
    · exact (hK _ h (N.graph.walks_symm (walks_source_arcsOnlyTo hαY hfA))).elim
    · exact (hfN (mem_of_mem_comp hk h)).elim

/-- **The path `P₁`** (line 209): "there is an undirected path `P₁` entirely within `A` from `α` to a
node `x` in `K_ab`. If this were not the case, then all paths from `α` to `N′` within `A` would end at
nodes in `K_cd`. But then `e₀` would separate `a, b` from `c, d, α` in `𝒩⁺`". As the argument says,
`P₁` is a path from `α` to `N′`: `x` is its one node in `N′`. -/
theorem exists_meet_near (D : CutEdgeData N Y α a b c d e₀ u w) (hαY : α ∈ Y)
    (hsep : NoSplitOn N Y a b c d) :
    ∃ x ∈ compOff N.graph (arcsOff N Y α) e₀ u, N.graph.Walks (arcsOnlyTo N Y α x) (N.leaf α) x := by
  by_contra hno
  push Not at hno
  exact hsep e₀ _ (onlyCrosses_of_no_meet hαY D.u_mem hno) D.ha D.hb (fun h => D.disjoint h D.hc)
    (fun h => D.disjoint h D.hd)

/-- **The path `P₂`** (line 210): "a path `P₂` from `x` to `e₀` in `K_ab`, by the connectedness of
`K_ab`". Its arcs lie in `M`, since no node of `K_ab` is ancestral only to `d`. -/
theorem walks_near (hN : N.IsPhylogenetic) (D : CutEdgeData N Y α a b c d e₀ u w)
    (hx : x ∈ compOff N.graph (arcsOff N Y α) e₀ u) :
    N.graph.Walks (arcsIn N Y α d e₀ u) u x := by
  have hxV := D.near_mem hN hx
  have hO : OnlyCrosses N.graph (arcsOff N Y α ∩ arcsOff N Y d) e₀
      (compOff N.graph (arcsOff N Y α) e₀ u) := onlyCrosses_compOff.mono Set.inter_subset_left
  exact walks_insideArcs hO D.link.symm D.w_not_mem D.w_not_mem
    (walks_inter hN D.w_mem (D.w_mem_off hN) hxV.1 hxV.2) hx

/-- **The path from `α` to `y ∈ K_cd` within `A`** (line 211), "by a similar argument to that for
`P₁`". -/
theorem exists_meet_far (D : CutEdgeData N Y α a b c d e₀ u w) (hαY : α ∈ Y)
    (hsep : NoSplitOn N Y a b c d) :
    ∃ y ∈ compOff N.graph (arcsOff N Y α) e₀ w, N.graph.Walks (arcsOnlyTo N Y α y) (N.leaf α) y := by
  by_contra hno
  push Not at hno
  exact hsep e₀ _ (onlyCrosses_of_no_meet hαY D.w_mem hno).compl (fun h => D.disjoint D.ha h)
    (fun h => D.disjoint D.hb h) (not_not.mpr D.hc) (not_not.mpr D.hd)

/-- **`y` and `c` have a common ancestor in `K_cd`** (line 212): "either the root of `𝒩′` is in `K_cd` or
any directed path from the root to any node in `K_cd` passes through `e₀` and the child node of `e₀` is
such an ancestor". -/
theorem exists_commonAncestor (hN : N.IsPhylogenetic) (D : CutEdgeData N Y α a b c d e₀ u w)
    (hy : y ∈ compOff N.graph (arcsOff N Y α) e₀ w) :
    ∃ z ∈ compOff N.graph (arcsOff N Y α) e₀ w, N.graph.Reaches z y ∧ N.graph.Reaches z (N.leaf c) := by
  rcases D.link with ⟨hs, ht⟩ | ⟨hs, -⟩
  · exact ⟨w, Relation.ReflTransGen.refl, D.reaches_of_mem hN hs ht hy (mem_of_mem_comp D.w_mem hy),
      D.reaches_of_mem hN hs ht D.hc (leaf_mem_vertsOff D.cY D.cα)⟩
  · have h1 := walks_off (Y := Y) (α := α)
      (avoidingReach_of_reaches_source hN.acyclic (hN.root_reaches _) .refl) D.source_mem
    rw [hs] at h1
    exact ⟨N.root, N.graph.walks_symm h1, hN.root_reaches _, hN.root_reaches _⟩

/-- **The node `z`** (line 212): a least common ancestor of `y` and `c` in `K_cd`, with no descendant that is
also a common ancestor in `K_cd`. The rest of the proof uses only that `z` is a common ancestor in
`K_cd`. -/
theorem exists_leastCommonAncestor (hN : N.IsPhylogenetic) (D : CutEdgeData N Y α a b c d e₀ u w)
    (hy : y ∈ compOff N.graph (arcsOff N Y α) e₀ w) :
    ∃ z ∈ compOff N.graph (arcsOff N Y α) e₀ w, N.graph.Reaches z y ∧ N.graph.Reaches z (N.leaf c) ∧
      ∀ z' ∈ compOff N.graph (arcsOff N Y α) e₀ w, N.graph.Reaches z' y → N.graph.Reaches z' (N.leaf c) →
        ¬ Relation.TransGen N.graph.Adj z z' := by
  have : Finite V := hN.finite_vertices
  let r : V → V → Prop := fun a b => Relation.TransGen N.graph.Adj b a
  have : IsTrans V r := ⟨fun _ _ _ h h' => h'.trans h⟩
  have : Std.Irrefl r := ⟨fun a h => hN.acyclic a h⟩
  have hwf : WellFounded r := Finite.wellFounded_of_trans_of_irrefl r
  obtain ⟨z, ⟨hz, hzy, hzc⟩, hmin⟩ := hwf.has_min
    {z | z ∈ compOff N.graph (arcsOff N Y α) e₀ w ∧ N.graph.Reaches z y ∧ N.graph.Reaches z (N.leaf c)}
    (by
      obtain ⟨z, h1, h2, h3⟩ := D.exists_commonAncestor hN hy
      exact ⟨z, h1, h2, h3⟩)
  exact ⟨z, hz, hzy, hzc, fun z' h1 h2 h3 h4 => hmin z' ⟨h1, h2, h3⟩ h4⟩

/-- A directed path between two nodes of `K_cd` avoids `e₀`, since a directed path can't use it
twice. -/
theorem not_reaches_through (hN : N.IsPhylogenetic) (D : CutEdgeData N Y α a b c d e₀ u w)
    (hz : z ∈ compOff N.graph (arcsOff N Y α) e₀ w) (hy : y ∈ compOff N.graph (arcsOff N Y α) e₀ w)
    (h1 : N.graph.Reaches z (N.graph.source e₀)) (h2 : N.graph.Reaches (N.graph.target e₀) y) :
    False := by
  have hyV := mem_of_mem_comp D.w_mem hy
  have h3 := walks_off (Y := Y) (α := α) (avoidingReach_of_reaches_source hN.acyclic h1 .refl) D.source_mem
  have h4 := walks_off (Y := Y) (α := α) (avoidingReach_of_target_reaches hN.acyclic .refl h2) hyV
  have hs : N.graph.source e₀ ∈ compOff N.graph (arcsOff N Y α) e₀ w :=
    Relation.ReflTransGen.trans hz h3
  have ht : N.graph.target e₀ ∈ compOff N.graph (arcsOff N Y α) e₀ w :=
    Relation.ReflTransGen.trans hy (N.graph.walks_symm h4)
  exact D.cut.2 (Relation.ReflTransGen.trans (N.graph.walks_symm hs) ht)

/-- **The directed path from `z` to `y`** (line 212): it stays in `K_cd`, and its arcs are ancestral to
`α`, so they lie in `M`. -/
theorem directedPath_subset (hN : N.IsPhylogenetic) (D : CutEdgeData N Y α a b c d e₀ u w)
    (hαY : α ∈ Y) (hαd : α ≠ d) (hz : z ∈ compOff N.graph (arcsOff N Y α) e₀ w)
    (hy : y ∈ compOff N.graph (arcsOff N Y α) e₀ w) (hyα : N.graph.Reaches y (N.leaf α))
    {P : Set E} (hP : IsDirectedPath N.graph z P y) : P ⊆ arcsIn N Y α d e₀ w := by
  have hsub : P ⊆ arcsOff N Y α \ {e₀} := by
    intro f hf
    obtain ⟨h1, h2⟩ := hP.reaches_of_mem hf
    refine ⟨N.mem_ancestralVertices_of_reaches h2 (mem_of_mem_comp D.w_mem hy), ?_⟩
    rintro rfl
    exact D.not_reaches_through hN hz hy h1 h2
  intro f hf
  obtain ⟨h1, h2⟩ := hP.walks_of_mem hf
  exact ⟨⟨(hsub hf).1, mem_arcsOff_of_reaches hαY hαd ((hP.reaches_of_mem hf).2.trans hyα)⟩,
    Relation.ReflTransGen.trans hz (walks_mono hsub h1),
    Relation.ReflTransGen.trans hz (walks_mono hsub h2)⟩

/-- **The path `P₃`** (line 213): "If all edges and nodes ancestral only to `d` are deleted from `N′`,
the network remains connected and contains both `z` and `e₀`. Thus there is a path `P₃` from `e₀` to
`z` in `K_cd` with no edges that are ancestral to only the taxon `d`". Since `e₀` is a cut edge, the
path can be kept in `K_cd`. -/
theorem walks_far_to_lca (hN : N.IsPhylogenetic) (D : CutEdgeData N Y α a b c d e₀ u w)
    (hz : z ∈ compOff N.graph (arcsOff N Y α) e₀ w) (hzc : N.graph.Reaches z (N.leaf c)) :
    N.graph.Walks (arcsIn N Y α d e₀ w) w z := by
  have huV := (D.near_mem hN (Relation.ReflTransGen.refl)).2
  have hzV : z ∈ vertsOff N Y α := mem_vertsOff_iff.mpr ⟨c, D.cY, D.cα, hzc⟩
  have hzV' : z ∈ vertsOff N Y d := mem_vertsOff_iff.mpr ⟨c, D.cY, D.cd, hzc⟩
  have hO : OnlyCrosses N.graph (arcsOff N Y α ∩ arcsOff N Y d) e₀
      (compOff N.graph (arcsOff N Y α) e₀ w) := onlyCrosses_compOff.mono Set.inter_subset_left
  exact walks_insideArcs hO D.link D.u_not_mem D.u_not_mem (walks_inter hN D.u_mem huV hzV hzV') hz

/-- **The paths of the source** (lines 209-213), as sets of arcs: `P₁`, within `A`, from `α` to
`x ∈ K_ab`, its one node in `N′`; `P₂` from `x` to `e₀` in `K_ab`; a directed path `R` from `y ∈ K_cd`
to `α` within `A`, whose one node in `N′` is `y`; a directed path `Pz` in `K_cd` from `z` to `y`, so
that `P₄` is `Pz ∪ R`; and `P₃` from `e₀` to `z` in `K_cd`. Those in `K_ab` and `K_cd` have no arc
ancestral only to `d`. -/
structure Paths (N : RootedNetwork V E X) (Y : Finset X) (α d : X) (e₀ : E) (u w x y z : V)
    (P₁ P₂ P₃ Pz R : Set E) : Prop where
  hx : x ∈ compOff N.graph (arcsOff N Y α) e₀ u
  hP₁ : IsPathIn N.graph (arcsOnlyTo N Y α x) P₁ (N.leaf α) x
  hP₂ : IsPathIn N.graph (arcsIn N Y α d e₀ u) P₂ x u
  hy : y ∈ compOff N.graph (arcsOff N Y α) e₀ w
  hR : IsDirectedPath N.graph y R (N.leaf α)
  hRA : R ⊆ arcsOnlyTo N Y α y
  hPz : IsDirectedPath N.graph z Pz y
  hPzK : Pz ⊆ arcsIn N Y α d e₀ w
  hP₃ : IsPathIn N.graph (arcsIn N Y α d e₀ w) P₃ w z

/-- **The construction of `x`, `y`, `z` and the paths**, in the source's order (lines 209-213). -/
theorem exists_paths (hN : N.IsPhylogenetic) (D : CutEdgeData N Y α a b c d e₀ u w) (hαY : α ∈ Y)
    (hαd : α ≠ d) (hsep : NoSplitOn N Y a b c d) :
    ∃ x y z P₁ P₂ P₃ Pz R, Paths N Y α d e₀ u w x y z P₁ P₂ P₃ Pz R := by
  have : Finite E := hN.finite_arcs
  -- "First, there is an undirected path `P₁` entirely within `A` from `α` to a node `x` in `K_ab`."
  obtain ⟨x, hx, hxA⟩ := D.exists_meet_near hαY hsep
  obtain ⟨P₁, hP₁⟩ := exists_isPathIn hxA
  -- "There is also a path `P₂` from `x` to `e₀` in `K_ab`, by the connectedness of `K_ab`."
  obtain ⟨P₂, hP₂⟩ := exists_isPathIn (N.graph.walks_symm (D.walks_near hN hx))
  -- "there is an undirected path from a node `y ∈ K_cd` to `α` within `A`", then directed
  obtain ⟨y, hy, hyA⟩ := D.exists_meet_far hαY hsep
  obtain ⟨R, hR, hRA⟩ := exists_directedPath_of_walks hαY (mem_of_mem_comp D.w_mem hy)
    (walks_mono arcsOnlyTo_subset hyA)
  -- "Choosing `z` as a least common ancestor of `y`, `c` in `K_cd`", "and a directed path from `z` to
  -- `y`"
  obtain ⟨z, hz, hzy, hzc, -⟩ := D.exists_leastCommonAncestor hN hy
  obtain ⟨Pz, hPz⟩ := exists_isDirectedPath hzy
  -- "there is a path `P₃` from `e₀` to `z` in `K_cd`"
  obtain ⟨P₃, hP₃⟩ := exists_isPathIn (D.walks_far_to_lca hN hz hzc)
  exact ⟨x, y, z, P₁, P₂, P₃, Pz, R, hx, hP₁, hP₂, hy, hR, hRA, hPz,
    D.directedPath_subset hN hαY hαd hz hy hR.reaches hPz, hP₃⟩

namespace Paths

variable {P₁ P₂ P₃ Pz R : Set E} {m : V}

/-- **The path `P₄`** (line 212): "a combined directed path `P₄` from `z` through `y` to `α`, with all
edges ancestral to `α`". -/
theorem isDirectedPath_P₄ (hP : Paths N Y α d e₀ u w x y z P₁ P₂ P₃ Pz R) :
    IsDirectedPath N.graph z (Pz ∪ R) (N.leaf α) :=
  hP.hPz.trans hP.hR

/-- The part of `P₁` between `m` and `x`, given by the arcs of `P₁` that meet the directed path `R`
from `y` at most at `m`. -/
abbrev segment (N : RootedNetwork V E X) (y : V) (P₁ R : Set E) (m : V) : Set E :=
  arcsAway N.graph P₁ {v | N.graph.Walks R y v} m

/-- **The node `m` where `P₁` leaves `P₄`.** `P₁` and the directed path from `y` to `α` both lie in `A`
and both end at `α`. `m` is the last node along `P₁`, going from `α` towards `x`, on that directed
path. So the initial segment of `P₁` goes from `α` to `m`, and the rest of `P₁` meets the directed path
only at `m`. (Both use the one arc at `α`, so `m` is above `α`; this isn't needed.) -/
theorem exists_meet (hP : Paths N Y α d e₀ u w x y z P₁ P₂ P₃ Pz R) :
    ∃ m, N.graph.Walks R y m ∧ N.graph.Walks P₁ (N.leaf α) m ∧
      N.graph.Walks (segment N y P₁ R m) m x := by
  obtain ⟨m, hm, h1, h2, -⟩ := exists_last_mem (S := {v | N.graph.Walks R y v}) hP.hP₁.joins hP.hR.walks
  exact ⟨m, hm, h1, h2⟩

/-- The arcs the source combines, other than `e₀` and the initial segment of `P₁`: `P₂`, `P₁` from `m`
to `x`, and `P₃` and `P₄ = Pz ∪ R`. -/
abbrev combined (N : RootedNetwork V E X) (y : V) (P₁ P₂ P₃ Pz R : Set E) (m : V) : Set E :=
  P₂ ∪ segment N y P₁ R m ∪ R ∪ Pz ∪ P₃

/-- The side of `K_ab`, cut off from `K_cd` by `m` and `e₀`: `K_ab`, and `P₁` from `m` to `x` without
`m`. -/
abbrev side (N : RootedNetwork V E X) (Y : Finset X) (α : X) (e₀ : E) (u y : V) (P₁ R : Set E) (m : V) :
    Set V :=
  compOff N.graph (arcsOff N Y α) e₀ u ∪ (arcVertices N.graph (segment N y P₁ R m) \ {m})

/-- `K_cd` is not on the side of `K_ab`: `P₁` meets `N′` only at `x ∈ K_ab`. -/
theorem notMem_side (D : CutEdgeData N Y α a b c d e₀ u w)
    (hP : Paths N Y α d e₀ u w x y z P₁ P₂ P₃ Pz R) {v : V}
    (hv : v ∈ compOff N.graph (arcsOff N Y α) e₀ w) : v ∉ side N Y α e₀ u y P₁ R m := by
  rintro (h | ⟨⟨g, hg, hgv⟩, -⟩)
  · exact D.disjoint h hv
  · have hvx := eq_of_mem_arcsOnlyTo (hP.hP₁.subset hg.1) hgv (mem_of_mem_comp D.w_mem hv)
    exact D.disjoint hP.hx (hvx ▸ hv)

/-- A node of the directed path `R` from `y` is on the side of `K_ab` only if it is `m`: it meets `N′`
only at `y ∈ K_cd`, and the part of `P₁` from `m` meets `R` only at `m`. -/
theorem eq_of_mem_side (D : CutEdgeData N Y α a b c d e₀ u w)
    (hP : Paths N Y α d e₀ u w x y z P₁ P₂ P₃ Pz R) {f : E} {v : V} (hf : f ∈ R)
    (hv : N.graph.source f = v ∨ N.graph.target f = v) (hT : v ∈ side N Y α e₀ u y P₁ R m) : v = m := by
  rcases hT with h | ⟨⟨k, hk, hkv⟩, -⟩
  · have hvy := eq_of_mem_arcsOnlyTo (hP.hRA hf) hv (mem_of_mem_comp D.u_mem h)
    exact (D.disjoint h (hvy ▸ hP.hy)).elim
  · have hvS : N.graph.Walks R y v := by
      rcases hv with rfl | rfl
      · exact (hP.hR.walks_of_mem hf).1
      · exact (hP.hR.walks_of_mem hf).2
    rcases hkv with rfl | rfl
    · exact hk.2.1 hvS
    · exact hk.2.2 hvS

/-- The combined arcs cross from the side of `K_ab` only at `m`: the pieces lie in `A`, `K_ab` and
`K_cd`, and meet only at the named nodes. -/
theorem crosses_side (D : CutEdgeData N Y α a b c d e₀ u w)
    (hP : Paths N Y α d e₀ u w x y z P₁ P₂ P₃ Pz R) {f : E} (hf : f ∈ combined N y P₁ P₂ P₃ Pz R m)
    (hc : N.graph.Crosses f (side N Y α e₀ u y P₁ R m)) :
    N.graph.source f = m ∨ N.graph.target f = m := by
  by_contra hno
  push Not at hno
  have hfar : ∀ {g : E}, g ∈ arcsIn N Y α d e₀ w → ¬ N.graph.Crosses g (side N Y α e₀ u y P₁ R m) := by
    rintro g hg (⟨h, -⟩ | ⟨h, -⟩)
    · exact notMem_side D hP hg.2.1 h
    · exact notMem_side D hP hg.2.2 h
  rcases hf with ((((hf | hf) | hf) | hf) | hf)
  · have hin := hP.hP₂.subset hf
    rcases hc with ⟨-, h⟩ | ⟨-, h⟩
    · exact h (Or.inl hin.2.2)
    · exact h (Or.inl hin.2.1)
  · rcases hc with ⟨-, h⟩ | ⟨-, h⟩
    · exact h (Or.inr ⟨⟨f, hf, Or.inr rfl⟩, hno.2⟩)
    · exact h (Or.inr ⟨⟨f, hf, Or.inl rfl⟩, hno.1⟩)
  · rcases hc with ⟨h, -⟩ | ⟨h, -⟩
    · exact hno.1 (eq_of_mem_side D hP hf (Or.inl rfl) h)
    · exact hno.2 (eq_of_mem_side D hP hf (Or.inr rfl) h)
  · exact hfar (hP.hPzK hf) hc
  · exact hfar (hP.hP₃.subset hf) hc

/-- None of the combined arcs is ancestral only to `d`, or is `e₀`: those of `A` and of `P₄` are
ancestral to `α`, and those of `K_ab` and `K_cd` lie in `M` by `Paths`. -/
theorem combined_subset (hαY : α ∈ Y) (hαd : α ≠ d) (D : CutEdgeData N Y α a b c d e₀ u w)
    (hP : Paths N Y α d e₀ u w x y z P₁ P₂ P₃ Pz R) :
    combined N y P₁ P₂ P₃ Pz R m ⊆ arcsOff N Y d \ {e₀} := by
  have hA : ∀ {f : E}, f ∈ arcsOnly N Y α → f ∈ arcsOff N Y d \ {e₀} := fun {f} hf =>
    ⟨mem_arcsOff_of_reaches hαY hαd (reaches_of_mem_arcsOnly hf), fun hfe => hf.2 (hfe ▸ D.cut.1)⟩
  have hnear : ∀ {f : E}, f ∈ arcsIn N Y α d e₀ u → f ∈ arcsOff N Y d \ {e₀} := fun {f} hf =>
    ⟨hf.1.2, (insideArcs_subset_diff D.link.symm D.w_not_mem hf).2⟩
  have hfar : ∀ {f : E}, f ∈ arcsIn N Y α d e₀ w → f ∈ arcsOff N Y d \ {e₀} := fun {f} hf =>
    ⟨hf.1.2, (insideArcs_subset_diff D.link D.u_not_mem hf).2⟩
  rintro f ((((hf | hf) | hf) | hf) | hf)
  · exact hnear (hP.hP₂.subset hf)
  · exact hA (hP.hP₁.subset hf.1).1
  · exact hA (hP.hRA hf).1
  · exact ⟨mem_arcsOff_of_reaches hαY hαd (hP.isDirectedPath_P₄.reaches_of_mem (Or.inl hf)).2,
      (hfar (hP.hPzK hf)).2⟩
  · exact hfar (hP.hP₃.subset hf)

/-- **The cycle `C`** (line 214): "Combining the paths `P₁`, `P₂`, the edge `e₀`, `P₃`, and `P₄`, and
removing edges to eliminate any self-intersections, yields a cycle `C` in `𝒩⁺` which passes through
`A`, `K_ab`, `e₀`, and `K_cd`. This cycle also lies in `M`, as none of its edges are ancestral only to
the taxon `d`."

The removal of edges has to keep a node of `P₁`, for "the initial segment of `P₁`" to reach `C`, and
the source does not say why it does. Here it is: `m` from `exists_meet` is on `C`. The arcs left to
remove from, `combined`, are `P₁` from `m` to `x`, then `P₂`, `P₃`, the part of `P₄` from `z` to `y`,
and the directed path from `y`. These lie in `A`, `K_ab`, `K_cd` and `A`, meeting only at `x`, `y` and
`m`, since `P₁` and the directed path meet `N′` only at `x` and at `y`. So any set of them joining the
two ends of `e₀` crosses from the side of `K_ab` at `m` (`crosses_side`), and the initial segment of
`P₁` is a path within `A` from `α` to the node `m` of `C`. -/
theorem exists_cycle (hN : N.IsPhylogenetic) (D : CutEdgeData N Y α a b c d e₀ u w) (hαY : α ∈ Y)
    (hαd : α ≠ d) (hP : Paths N Y α d e₀ u w x y z P₁ P₂ P₃ Pz R) :
    ∃ C m, IsCycleThrough N.graph C e₀ ∧ C ⊆ arcsOff N Y d ∧ (∃ k ∈ C, k ∈ arcsOnly N Y α) ∧
      u ∈ arcVertices N.graph C ∧ w ∈ arcVertices N.graph C ∧ m ∈ arcVertices N.graph C ∧
      N.graph.Walks (arcsOnly N Y α) (N.leaf α) m := by
  have : Finite E := hN.finite_arcs
  obtain ⟨m, hmR, hαm, hmx⟩ := hP.exists_meet
  have hsub := combined_subset (m := m) hαY hαd D hP
  -- combining the paths
  have hwalk : N.graph.Walks (combined N y P₁ P₂ P₃ Pz R m) u w := by
    have h1 : N.graph.Walks (combined N y P₁ P₂ P₃ Pz R m) x u :=
      walks_mono (fun _ hf => Or.inl (Or.inl (Or.inl (Or.inl hf)))) hP.hP₂.joins
    have h2 : N.graph.Walks (combined N y P₁ P₂ P₃ Pz R m) m x :=
      walks_mono (fun _ hf => Or.inl (Or.inl (Or.inl (Or.inr hf)))) hmx
    have h3 : N.graph.Walks (combined N y P₁ P₂ P₃ Pz R m) y m :=
      walks_mono (fun _ hf => Or.inl (Or.inl (Or.inr hf))) hmR
    have h4 : N.graph.Walks (combined N y P₁ P₂ P₃ Pz R m) z y :=
      walks_mono (fun _ hf => Or.inl (Or.inr hf)) hP.hPz.walks
    have h5 : N.graph.Walks (combined N y P₁ P₂ P₃ Pz R m) w z :=
      walks_mono (fun _ hf => Or.inr hf) hP.hP₃.joins
    exact N.graph.walks_symm (((h5.trans h4).trans h3).trans (h2.trans h1))
  have hdiff : combined N y P₁ P₂ P₃ Pz R m ⊆ combined N y P₁ P₂ P₃ Pz R m \ {e₀} :=
    fun _ hf => ⟨hf, (hsub hf).2⟩
  have hwalk' := walks_mono hdiff hwalk
  -- removing edges to eliminate any self-intersections
  obtain ⟨C, hC, hCsub⟩ : ∃ C, IsCycleThrough N.graph C e₀ ∧
      C \ {e₀} ⊆ combined N y P₁ P₂ P₃ Pz R m \ {e₀} := by
    refine exists_isCycleThrough ?_
    rcases D.link with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hwalk'
    · exact N.graph.walks_symm hwalk'
  -- it lies in `M`
  have hCM : C ⊆ arcsOff N Y d := by
    intro f hf
    by_cases hfe : f = e₀
    · exact hfe ▸ D.mem_off hN
    · exact (hsub (hCsub ⟨hf, hfe⟩).1).1
  -- it passes through `A`, `K_ab`, `e₀`, and `K_cd`
  obtain ⟨k, hk, hkc⟩ := hC.exists_crosses (T := compOff N.graph (arcsOff N Y α) e₀ u)
    (D.link.symm.crosses D.w_not_mem Relation.ReflTransGen.refl)
  have hkA : k ∈ arcsOnly N Y α :=
    ⟨arcsOff_subset d (hCM hk.1), fun hkN => hk.2 (onlyCrosses_compOff k hkN hkc)⟩
  have huC : u ∈ arcVertices N.graph C := by
    rcases D.link with ⟨h, -⟩ | ⟨-, h⟩
    · exact ⟨e₀, hC.mem, Or.inl h⟩
    · exact ⟨e₀, hC.mem, Or.inr h⟩
  have hwC : w ∈ arcVertices N.graph C := by
    rcases D.link with ⟨-, h⟩ | ⟨h, -⟩
    · exact ⟨e₀, hC.mem, Or.inr h⟩
    · exact ⟨e₀, hC.mem, Or.inl h⟩
  -- and through `m`
  have hCuw : N.graph.Walks (C \ {e₀}) u w := by
    have h := hC.joins
    rcases D.link with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact h
    · exact N.graph.walks_symm h
  have hmC : m ∈ arcVertices N.graph (C \ {e₀}) :=
    mem_arcVertices_of_walks (T := side N Y α e₀ u y P₁ R m) hCuw (Or.inl Relation.ReflTransGen.refl)
      (notMem_side D hP Relation.ReflTransGen.refl)
      (fun f hf hc => crosses_side D hP (hCsub hf).1 hc)
  exact ⟨C, m, hC, hCM, ⟨k, hk.1, hkA⟩, huC, hwC, arcVertices_mono Set.sdiff_subset hmC,
    walks_mono (fun _ hf => (hP.hP₁.subset hf).1) hαm⟩

end Paths

/-- **The rest of the source's proof** (lines 214-215). "Since `ℬ′` also lies in `M`, and the cycle `C`
and `ℬ′` intersect, they lie in the same blob `ℬ` of `M`": `C`, from `Paths.exists_cycle`, passes
through `u`, an end of `e₀` in `ℬ′`. "Since `{a, b, c}` determines `ℬ′` in `N′` and hence in `M ∩ N′`,
by Lemma 2 `{a, b, c}` determines `ℬ` in `M` with incident cut edges leading to `a, b, c` in
`M ∩ N′ ⊂ N′`." "But the initial segment of `P₁` gives a path from `α` to `C`. Since this path lies
entirely in `A`, the cut edge incident to `ℬ` that leads to `α` must be in `A`, and is therefore
distinct from those to `a, b, c`."

The source does not say why `P₁` still meets `C` once the self-intersections are removed. The gap is
filled along its lines: `P₁` and the directed path from `y` to `α` both lie in `A` and both end at `α`,
and `C` goes through `m`, the last node along `P₁` from `α` towards `x` on that directed path
(`Paths.exists_meet`), because the rest of `P₁` and the directed path meet `N′` only at `x ∈ K_ab` and
at `y ∈ K_cd`, and each other only at `m` (`Paths.crosses_side`). The initial segment of `P₁` is the
part from `α` to `m`. -/
theorem determines_off (hN : N.IsPhylogenetic) (D : CutEdgeData N Y α a b c d e₀ u w) (hαY : α ∈ Y)
    (hαd : α ≠ d) (hαa : α ≠ a) (hαb : α ≠ b) (hαc : α ≠ c) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (haY : a ∈ Y) (hbY : b ∈ Y) (had : a ≠ d) (hbd : b ≠ d)
    (hsep : NoSplitOn N Y a b c d) {v' : V}
    (hv' : SameBlobIn N.graph (arcsOff N Y α) v' u)
    (hdet : Determines N.graph (arcsOff N Y α) v' N.leaf {a, b, c}) :
    v' ∈ vertsOff N Y d ∧ Determines N.graph (arcsOff N Y d) v' N.leaf {a, b, c, α} := by
  have : Finite E := hN.finite_arcs
  have hv'K : v' ∈ compOff N.graph (arcsOff N Y α) e₀ u :=
    (hv'.symm.walks_diff D.cut)
  have hv'V := D.near_mem hN hv'K
  -- the paths, and the cycle `C` in `M`
  obtain ⟨x, y, z, P₁, P₂, P₃, Pz, R, hP⟩ := D.exists_paths hN hαY hαd hsep
  obtain ⟨C, m, hC, hCM, -, huC, -, hmC, hαm⟩ := hP.exists_cycle hN D hαY hαd
  -- `ℬ′` lies in `M ∩ N′`, and hence in a blob of it
  have hblob : blobArcsIn N.graph (arcsOff N Y α) v' ⊆ arcsOff N Y α ∩ arcsOff N Y d := by
    rintro f ⟨hf, hs⟩
    have hfe : f ≠ e₀ := by
      rintro rfl
      exact hf.2 D.cut
    refine ⟨hf.1, D.arc_near_mem hN ⟨hf.1, hfe⟩ (links_self f) ?_⟩
    exact Relation.ReflTransGen.trans hv'K (hs.walks_diff D.cut)
  have hblobQ : ∀ x, SameBlobIn N.graph (arcsOff N Y α) v' x →
      SameBlobIn N.graph (arcsOff N Y α ∩ arcsOff N Y d) v' x := fun x hx =>
    sameBlobIn_of_isBridgelessSubgraph (isBridgelessSubgraph_blob v') hblob
      Relation.ReflTransGen.refl hx
  -- `C` and `ℬ′` meet, so they lie in one blob of `M`
  have hu_blob : SameBlobIn N.graph (arcsOff N Y d) v' u :=
    (hblobQ u hv').mono Set.inter_subset_right
  have hsame : ∀ x ∈ arcVertices N.graph C, SameBlobIn N.graph (arcsOff N Y d) v' x := by
    intro x hx
    exact hu_blob.trans (sameBlobIn_of_isBridgelessSubgraph hC.isBridgelessSubgraph hCM huC hx)
  -- `{a, b, c}` determines `ℬ′` in `M ∩ N′`, and so the blob of `M`, by Lemma 2
  have hdetQ : Determines N.graph (arcsOff N Y α ∩ arcsOff N Y d) v' N.leaf {a, b, c} :=
    hdet.of_subset Set.inter_subset_left hblobQ
  have hmemS : ∀ s ∈ ({a, b, c} : Finset X), s ∈ Y ∧ s ≠ α ∧ s ≠ d := by
    intro s hs
    simp only [Finset.mem_insert, Finset.mem_singleton] at hs
    rcases hs with rfl | rfl | rfl
    · exact ⟨haY, hαa.symm, had⟩
    · exact ⟨hbY, hαb.symm, hbd⟩
    · exact ⟨D.cY, D.cα, D.cd⟩
  have h3 : ({a, b, c} : Finset X).card = 3 := by
    rw [Finset.card_insert_of_notMem (by simp [hab, hac]), Finset.card_pair hbc]
  obtain ⟨hdetM, hlead⟩ := lemma2 (M := arcsOff N Y α ∩ arcsOff N Y d) (F := arcsOff N Y d)
    (v := v') (ℓ := N.leaf) (S := {a, b, c}) Set.inter_subset_right h3.ge
    (fun s _ => isPendantIn_leaf hN s _)
    (fun s hs => walks_inter hN hv'V.1 hv'V.2 (leaf_mem_vertsOff (hmemS s hs).1 (hmemS s hs).2.1)
      (leaf_mem_vertsOff (hmemS s hs).1 (hmemS s hs).2.2))
    (fun f hf => walks_inter hN hv'V.1 hv'V.2 (N.source_mem_ancestralVertices hf.1)
      (N.source_mem_ancestralVertices hf.2)) hdetQ
  -- the initial segment of `P₁`: a path within `A` from `α` to the node `m` of `C`
  have hmblob : SameBlobIn N.graph (arcsOff N Y d) v' m := hsame m hmC
  have hαV : N.leaf α ∈ vertsOff N Y d := leaf_mem_vertsOff hαY hαd
  have hvα : N.graph.Walks (arcsOff N Y d) v' (N.leaf α) := walks_ancestral hN hv'V.2 hαV
  -- the taxon `α` is outside the blob
  have hαb' : ¬ SameBlobIn N.graph (arcsOff N Y d) v' (N.leaf α) := by
    intro h
    have hveq := (isPendantIn_leaf hN α _).eq_of_sameBlobIn h
    obtain ⟨s, -, hsα, -, hr⟩ := D.near_reaches hN hv'K
    rw [hveq] at hr
    exact hsα (hN.leaf_injective (eq_of_leaf_reaches hN hr))
  obtain ⟨eα, heα⟩ := (exists_leadsTo hvα).resolve_left hαb'
  -- the cut edge leading to `α` is in `A`
  have heαA : eα ∈ arcsOnly N Y α := by
    by_contra hnot
    refine heα.2 ((hmblob.walks_diff heα.1.1).trans (walks_mono ?_ (N.graph.walks_symm hαm)))
    intro f hf
    refine ⟨mem_arcsOff_of_reaches hαY hαd (reaches_of_mem_arcsOnly hf), ?_⟩
    rintro rfl
    exact hnot hf
  -- so it is distinct from those to `a, b, c`
  have hins := hdetM.insert (α := α) hvα heα (fun s hs => by
    obtain ⟨e, he, hl⟩ := hlead s hs
    refine ⟨e, hl, ?_⟩
    rintro rfl
    exact heαA.2 he.1)
  refine ⟨hv'V.2, ?_⟩
  have hset : ({a, b, c, α} : Finset X) = insert α {a, b, c} := by
    ext s
    simp only [Finset.mem_insert, Finset.mem_singleton]
    tauto
  rw [hset]
  exact hins

end CutEdgeData

/-- **The blob `ℬ′` and the cut edge `e₀` of the source.** From a cut edge `e₁` of `N′` separating
`a, b` from `c, d`, and a blob `ℬ′` of `N′` determined by `a, b, c`: the cut edge `e₀` incident to
`ℬ′` through which paths to `c` pass "also separates `a, b` from `c, d`". -/
theorem exists_cutEdgeData (hN : N.IsPhylogenetic) {e₁ : E} {T₁ : Set V} {v' : V}
    (hv' : v' ∈ vertsOff N Y α) (hdet : Determines N.graph (arcsOff N Y α) v' N.leaf {a, b, c})
    (hT₁ : OnlyCrosses N.graph (arcsOff N Y α) e₁ T₁) (ha₁ : N.leaf a ∉ T₁) (hb₁ : N.leaf b ∉ T₁)
    (hc₁ : N.leaf c ∈ T₁) (hd₁ : N.leaf d ∈ T₁) (haY : a ∈ Y) (hbY : b ∈ Y) (hcY : c ∈ Y) (hdY : d ∈ Y)
    (haα : a ≠ α) (hbα : b ≠ α) (hcα : c ≠ α) (hdα : d ≠ α) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hcd : c ≠ d) :
    ∃ e₀ u w, CutEdgeData N Y α a b c d e₀ u w ∧ SameBlobIn N.graph (arcsOff N Y α) v' u := by
  have hma : a ∈ ({a, b, c} : Finset X) := by simp
  have hmb : b ∈ ({a, b, c} : Finset X) := by simp
  have hmc : c ∈ ({a, b, c} : Finset X) := by simp
  have h3 : 3 ≤ ({a, b, c} : Finset X).card := by
    rw [Finset.card_insert_of_notMem (by simp [hab, hac]), Finset.card_pair hbc]
  have hW : ∀ {s : X}, s ∈ Y → s ≠ α → N.graph.Walks (arcsOff N Y α) v' (N.leaf s) :=
    fun hs hne => walks_ancestral hN hv' (leaf_mem_vertsOff hs hne)
  have hWS : ∀ s ∈ ({a, b, c} : Finset X), N.graph.Walks (arcsOff N Y α) v' (N.leaf s) := by
    intro s hs
    simp only [Finset.mem_insert, Finset.mem_singleton] at hs
    rcases hs with rfl | rfl | rfl
    · exact hW haY haα
    · exact hW hbY hbα
    · exact hW hcY hcα
  -- `e₀`
  have hbc' : ¬ SameBlobIn N.graph (arcsOff N Y α) v' (N.leaf c) := fun h =>
    hdet.ne_of_isPendantIn h3 (isPendantIn_leaf hN c _) hWS
      ((isPendantIn_leaf hN c _).eq_of_sameBlobIn h)
  obtain ⟨e₀, he₀⟩ := (exists_leadsTo (hW hcY hcα)).resolve_left hbc'
  obtain ⟨u, w, hl, hb, -⟩ := exists_ends_of_mem_incidentCuts he₀.1
  have hvu := hb.walks_diff he₀.1.1
  -- `a, b` are on the near side of `e₀`
  have hnear : ∀ s ∈ ({a, b, c} : Finset X), s ≠ c →
      N.graph.Walks (arcsOff N Y α \ {e₀}) u (N.leaf s) := by
    intro s hs hsc
    by_contra hno
    refine hsc (hdet.eq_of_mem_side onlyCrosses_far not_mem_far_self hs hmc (hWS s hs) (hWS c hmc) ?_ he₀.2)
    exact fun h => hno (Relation.ReflTransGen.trans (N.graph.walks_symm hvu) h)
  -- `c` is on the far side
  have huc : N.graph.Walks (arcsOff N Y α) u (N.leaf c) :=
    (N.graph.walks_symm hb.walks).trans (hW hcY hcα)
  have hcfar : ¬ N.graph.Walks (arcsOff N Y α \ {e₀}) u (N.leaf c) :=
    fun h => he₀.2 (hvu.trans h)
  have hc₀ := walks_of_not_walks hl huc hcfar
  -- `d` is on the far side: the side of `e₁` with `c, d` doesn't contain `ℬ′`
  have hv₁ : v' ∉ T₁ := fun hv => hab (hdet.eq_of_mem_side hT₁.compl (not_not.mpr hv) hma hmb
    (hWS a hma) (hWS b hmb) ha₁ hb₁)
  have hu₁ : u ∉ T₁ := fun hu => hv₁ ((SameBlobIn.mem_iff hT₁ hb).mpr hu)
  have hdfar : ¬ N.graph.Walks (arcsOff N Y α \ {e₀}) u (N.leaf d) := by
    intro h
    have hin := walks_insideArcs_of_mem hT₁ hv₁ (hW hdY hdα) (hW hcY hcα) hd₁ hc₁
    exact hcfar (h.trans (walks_mono (insideArcs_subset_diff hl hu₁) hin))
  have hud : N.graph.Walks (arcsOff N Y α) u (N.leaf d) :=
    (N.graph.walks_symm hb.walks).trans (hW hdY hdα)
  exact ⟨e₀, u, w, ⟨hl, he₀.1.1, hnear a hma hac, hnear b hmb hbc, hc₀, walks_of_not_walks hl hud hdfar,
    hcY, hdY, hcα, hdα, hcd⟩, hb⟩

/-- **Lemma 3 of the source**, in its language: for a network with `{a, b, c, d}` a B-quartet (on
the subgraph induced on `Y`), if the induced network on `Y \ {α}` has a cut edge separating `a, b`
from `c, d`, then `{a, b, c, α}` is a B-quartet on the induced network on `Y \ {d}`. -/
theorem lemma3_blob (hN : N.IsPhylogenetic) (h4 : ({a, b, c, d} : Finset X).card = 4) (ha : a ∈ Y)
    (hb : b ∈ Y) (hc : c ∈ Y) (hd : d ∈ Y) (hα : α ∈ Y) (hαa : α ≠ a) (hαb : α ≠ b) (hαc : α ≠ c)
    (hαd : α ≠ d) {v₀ : V} (hv₀ : v₀ ∈ N.ancestralVertices (Y : Set X))
    (hB : Determines N.graph (N.ancestralArcs (Y : Set X)) v₀ N.leaf {a, b, c, d}) {e₁ : E} {T₁ : Set V}
    (hT₁ : OnlyCrosses N.graph (arcsOff N Y α) e₁ T₁) (ha₁ : N.leaf a ∉ T₁) (hb₁ : N.leaf b ∉ T₁)
    (hc₁ : N.leaf c ∈ T₁) (hd₁ : N.leaf d ∈ T₁) :
    ∃ v ∈ vertsOff N Y d, Determines N.graph (arcsOff N Y d) v N.leaf {a, b, c, α} := by
  obtain ⟨hab, hac, had, hbc, hbd, hcd⟩ := ne_of_card_four h4
  have hWY : ∀ s ∈ ({a, b, c, d} : Finset X), N.graph.Walks (N.ancestralArcs (Y : Set X)) v₀ (N.leaf s) := by
    intro s hs
    refine walks_ancestral hN hv₀ (N.leaf_mem_ancestralVertices (Finset.mem_coe.mpr ?_))
    simp only [Finset.mem_insert, Finset.mem_singleton] at hs
    rcases hs with rfl | rfl | rfl | rfl <;> assumption
  have hsep : NoSplitOn N Y a b c d := fun _ _ hT h1 h2 h3 h5 =>
    hB.no_split hab hcd hWY hT h1 h2 h3 h5
  -- the blob `ℬ′` of `N′` determined by `a, b, c`
  obtain ⟨v', hv', hdet⟩ := exists_determines_three (N := N) (Z := ((Y.erase α : Finset X) : Set X))
    (a := a) (b := b) (c := c) hN (Finset.mem_coe.mpr (Finset.mem_erase.mpr ⟨hαa.symm, ha⟩))
    (Finset.mem_coe.mpr (Finset.mem_erase.mpr ⟨hαb.symm, hb⟩))
    (Finset.mem_coe.mpr (Finset.mem_erase.mpr ⟨hαc.symm, hc⟩)) hab hac hbc
  obtain ⟨e₀, u, w, D, hu⟩ := exists_cutEdgeData hN hv' hdet hT₁ ha₁ hb₁ hc₁ hd₁ ha hb hc hd hαa.symm hαb.symm
    hαc.symm hαd.symm hab hac hbc hcd
  obtain ⟨hv, hdet'⟩ := D.determines_off hN hα hαd hαa hαb hαc hab hac hbc ha hb had hbd hsep hu hdet
  exact ⟨v', hv, hdet'⟩

end Setup

end AllmanEtAl2023
