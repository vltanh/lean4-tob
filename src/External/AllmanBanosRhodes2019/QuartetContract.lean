module

public import External.AllmanBanosRhodes2019.Quartet
public import AllmanEtAl2023.TrdFour

/-!
# The network `Q̃`: contracting the 2- and 3-cycles of a quartet network

"After contracting all 2- and 3-cycles, and suppressing degree 2 nodes, we obtain a network `Q̃_xyzw` that is either a tree or has a
single 4-cycle" (Definition 20, line 1026), and "by contraction of a cycle, we mean the removal of its edges followed by the
identification of all vertices in it" (line 451). This module builds this graph, and `QuartetClass.lean` reads it.

* `contractedArcs`: the edges of the 2- and 3-cycles of the quartet network on `q`.
* `tildeGraph`: the graph with those removed and the ends of each identified, on the classes of the kept vertices.
* `qTilde`: with the vertices of degree two suppressed, by the same `suppressDegreeTwo` as `T_rd(𝒩⁻)` of Allman et al. 2023.
-/

@[expose] public noncomputable section

open Phylogenetics Phylogenetics.RootedNetwork Finset
open TOBQMC TOBQMC.Level1
open AllmanEtAl2023 AllmanEtAl2023.TreeSuppression
open scoped Classical

namespace External.AllmanBanosRhodes2019.Quartet

variable {V E X : Type*}

/-! ### The definitions -/

section Defs

variable (N : RootedNetwork V E X) (q : Finset X)

/-- The edges of the 2- and 3-cycles of the quartet network on `q`. -/
def contractedArcs : Set E :=
  {f | ∃ h, IsQuartetCycle N q h ∧ cycleSize N q h ≤ 3 ∧ f ∈ N.graph.blobArcs h}

/-- The ends of an edge of a contracted cycle are identified. -/
def contractRel (a b : V) : Prop :=
  ∃ f ∈ contractedArcs N q, N.graph.source f = a ∧ N.graph.target f = b

/-- A vertex is kept: an edge of the quartet network is at it. -/
def IsKept (v : V) : Prop := ∃ e ∈ trekArcs N q, N.graph.source e = v ∨ N.graph.target e = v

/-- The classes of the kept vertices, under the identification of contracted edges. -/
abbrev TildeV := {ξ : Quot (contractRel N q) // ∃ v, IsKept N q v ∧ Quot.mk _ v = ξ}

/-- The edges of the quartet network that are not contracted. -/
abbrev TildeE := {e : E // e ∈ trekArcs N q ∧ e ∉ contractedArcs N q}

variable {N q} in
/-- The class of a kept vertex. -/
def toV {v : V} (hv : IsKept N q v) : TildeV N q := ⟨Quot.mk _ v, v, hv, rfl⟩

variable {N q} in
theorem isKept_source {e : E} (he : e ∈ trekArcs N q) : IsKept N q (N.graph.source e) := ⟨e, he, Or.inl rfl⟩

variable {N q} in
theorem isKept_target {e : E} (he : e ∈ trekArcs N q) : IsKept N q (N.graph.target e) := ⟨e, he, Or.inr rfl⟩

/-- **The graph obtained by contracting all 2- and 3-cycles of the quartet network on `q`**: "the removal of [the] edges [of a
cycle] followed by the identification of all vertices in it" (line 451). -/
def tildeGraph : DirectedMultigraph (TildeV N q) (TildeE N q) where
  source e := toV (isKept_source e.2.1)
  target e := toV (isKept_target e.2.1)

end Defs

section Basic

variable {N : RootedNetwork V E X} {q : Finset X}

theorem tildeGraph_source (e : TildeE N q) : (tildeGraph N q).source e = toV (isKept_source e.2.1) := rfl

theorem tildeGraph_target (e : TildeE N q) : (tildeGraph N q).target e = toV (isKept_target e.2.1) := rfl

theorem exists_toV (w : TildeV N q) : ∃ v, ∃ hv : IsKept N q v, w = toV hv := by
  obtain ⟨ξ, v, hv, rfl⟩ := w
  exact ⟨v, hv, rfl⟩

/-- Two vertices in one class are on the same side of a set that no contracted edge crosses. -/
theorem mem_iff_of_toV_eq {S : Set V} (hS : ∀ f ∈ contractedArcs N q, ¬ N.graph.Crosses f S) {a b : V} {ha : IsKept N q a}
    {hb : IsKept N q b} (h : toV ha = toV hb) : a ∈ S ↔ b ∈ S := by
  have hq : (Quot.mk (contractRel N q) a) = Quot.mk _ b := congrArg Subtype.val h
  have hres : ∀ a b, contractRel N q a b → (a ∈ S) = (b ∈ S) := by
    rintro a b ⟨f, hf, rfl, rfl⟩
    exact propext (mem_iff_of_not_crosses (hS f hf))
  have := congrArg (Quot.lift (fun v => v ∈ S) hres) hq
  exact iff_of_eq this

/-- The end of a contracted edge are in one class. -/
theorem toV_eq_of_mem_contractedArcs {f : E} (hf : f ∈ contractedArcs N q) {ha : IsKept N q (N.graph.source f)}
    {hb : IsKept N q (N.graph.target f)} : toV ha = toV hb :=
  Subtype.ext (Quot.sound ⟨f, hf, rfl, rfl⟩)

/-- One kept edge is a step of a walk of the contracted graph, or nothing. -/
theorem walks_of_mem_trekArcs {e : E} (he : e ∈ trekArcs N q) {ha : IsKept N q (N.graph.source e)}
    {hb : IsKept N q (N.graph.target e)} : (tildeGraph N q).Walks Set.univ (toV ha) (toV hb) := by
  by_cases hc : e ∈ contractedArcs N q
  · rw [toV_eq_of_mem_contractedArcs hc]
    exact .refl
  · exact .single ⟨⟨e, he, hc⟩, Set.mem_univ _, Or.inl ⟨rfl, rfl⟩⟩

/-- A directed path of kept edges is a walk of the contracted graph. -/
theorem walks_of_isDirPath {a b : V} {p : List E} (hp : N.IsDirPath a p b) (hK : ∀ e ∈ p, e ∈ trekArcs N q)
    (ha : IsKept N q a) (hb : IsKept N q b) : (tildeGraph N q).Walks Set.univ (toV ha) (toV hb) := by
  induction p generalizing a with
  | nil =>
    obtain rfl : a = b := hp
    exact .refl
  | cons e p ih =>
    obtain ⟨rfl, hp⟩ := hp
    have he := hK e (by simp)
    exact (walks_of_mem_trekArcs he).trans (ih hp (fun f hf => hK f (by simp [hf])) (isKept_target he))

end Basic

/-! ### Sides of the contracted graph -/

section Sides

variable {N : RootedNetwork V E X} {q : Finset X}

/-- The classes of the kept vertices in a set. -/
def tildeSide (N : RootedNetwork V E X) (q : Finset X) (S : Set V) : Set (TildeV N q) :=
  {w | ∃ v, ∃ hv : IsKept N q v, v ∈ S ∧ w = toV hv}

theorem toV_mem_tildeSide {S : Set V} (hS : ∀ f ∈ contractedArcs N q, ¬ N.graph.Crosses f S) {v : V} (hv : IsKept N q v) :
    toV hv ∈ tildeSide N q S ↔ v ∈ S := by
  constructor
  · rintro ⟨v', hv', hm, he⟩
    exact (mem_iff_of_toV_eq hS he).2 hm
  · exact fun hm => ⟨v, hv, hm, rfl⟩

theorem crosses_tildeSide {S : Set V} (hS : ∀ f ∈ contractedArcs N q, ¬ N.graph.Crosses f S) (f : TildeE N q) :
    (tildeGraph N q).Crosses f (tildeSide N q S) ↔ N.graph.Crosses f.1 S := by
  simp only [DirectedMultigraph.Crosses, tildeGraph_source, tildeGraph_target, toV_mem_tildeSide hS]

/-- A cut of the kept edges at a not contracted edge is a side of it in the contracted graph. -/
theorem isSideOf_tildeSide {S : Set V} {e : TildeE N q} (hcr : N.graph.Crosses e.1 S)
    (hS : ∀ f ∈ trekArcs N q, f ≠ e.1 → ¬ N.graph.Crosses f S) : IsSideOf (tildeGraph N q) e (tildeSide N q S) := by
  have hC : ∀ f ∈ contractedArcs N q, ¬ N.graph.Crosses f S := by
    intro f hf
    obtain ⟨h, hQ, hs3, hb⟩ := hf
    refine hS f (hQ.2 f hb) ?_
    rintro rfl
    exact e.2.2 ⟨h, hQ, hs3, hb⟩
  intro f
  rw [crosses_tildeSide hC]
  constructor
  · intro hf
    by_contra hne
    exact hS f.1 f.2.1 (fun h => hne (Subtype.ext h)) hf
  · rintro rfl
    exact hcr

/-- A side of the contracted graph is a cut of the kept edges. -/
theorem crosses_of_isSideOf {T : Set (TildeV N q)} {e : TildeE N q} (hT : IsSideOf (tildeGraph N q) e T) {f : E}
    (hf : f ∈ trekArcs N q) (hne : f ≠ e.1) :
    ¬ N.graph.Crosses f {v | ∃ hv : IsKept N q v, toV hv ∈ T} := by
  by_cases hc : f ∈ contractedArcs N q
  · rintro (⟨⟨h₁, h₁'⟩, h₂⟩ | ⟨⟨h₁, h₁'⟩, h₂⟩)
    · refine h₂ ⟨isKept_target hf, ?_⟩
      rwa [← toV_eq_of_mem_contractedArcs hc]
    · refine h₂ ⟨isKept_source hf, ?_⟩
      rwa [toV_eq_of_mem_contractedArcs hc]
  · intro hcr
    have : (tildeGraph N q).Crosses ⟨f, hf, hc⟩ T := by
      rcases hcr with ⟨⟨h₁, h₁'⟩, h₂⟩ | ⟨⟨h₁, h₁'⟩, h₂⟩
      · exact Or.inl ⟨h₁', fun h' => h₂ ⟨isKept_target hf, h'⟩⟩
      · exact Or.inr ⟨h₁', fun h' => h₂ ⟨isKept_source hf, h'⟩⟩
    exact hne (congrArg Subtype.val ((hT _).1 this))

/-- No walk avoiding an edge joins its ends, if it has a side. -/
theorem not_walks_of_isSideOf {W F : Type*} {G : DirectedMultigraph W F} {e : F} {T : Set W} (hT : IsSideOf G e T) :
    ¬ G.Walks {e}ᶜ (G.source e) (G.target e) := by
  have hstep : ∀ {a b : W}, G.Walks {e}ᶜ a b → (a ∈ T ↔ b ∈ T) := by
    intro a b hw
    induction hw with
    | refl => exact Iff.rfl
    | @tail b c _ hbc ih =>
      obtain ⟨f, hf, hends⟩ := hbc
      have hnc : ¬ G.Crosses f T := fun hc => hf ((hT f).1 hc)
      have hiff : G.source f ∈ T ↔ G.target f ∈ T := by
        simp only [DirectedMultigraph.Crosses] at hnc
        tauto
      rcases hends with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact ih.trans hiff
      · exact ih.trans hiff.symm
  intro hw
  have := hstep hw
  have hc := (hT e).2 rfl
  simp only [DirectedMultigraph.Crosses] at hc
  tauto

end Sides

/-! ### Connected, and degrees -/

section Degrees

variable {N : RootedNetwork V E X} {q : Finset X}

theorem isKept_leaf (hN : N.IsPhylogenetic) {x y : X} (hx : x ∈ q) (hy : y ∈ q) (hxy : x ≠ y) : IsKept N q (N.leaf x) := by
  have := hN.finite_arcs
  obtain ⟨t, p, r, hw⟩ := exists_isWedgePath_leaf hN x y
  have hK : ∀ f, f ∈ p ∨ f ∈ r → f ∈ trekArcs N q := fun f hf => by
    rw [trekArcs_eq_wedgeArcs hN]
    exact ⟨x, hx, y, hy, hxy, t, p, r, hw, hf⟩
  rcases List.eq_nil_or_concat p with rfl | ⟨p', f, rfl⟩
  · exfalso
    obtain rfl : t = N.leaf x := hw.left
    have h0 := (hN.leaves (N.leaf x)).mpr ⟨x, rfl⟩
    cases r with
    | nil => exact hxy (hN.leaf_injective hw.right)
    | cons g r => exact (DirectedMultigraph.outdegree_eq_zero_iff _ _).mp h0 g hw.right.1
  · rw [List.concat_eq_append] at hw hK
    obtain ⟨c, -, -, hft⟩ := isDirPath_append.1 hw.left
    exact ⟨f, hK f (Or.inl (by simp)), Or.inr hft⟩

/-- **The contracted graph is connected.** Every kept edge is on a wedge path between taxa of `q`, and two taxa of `q` are joined by
one. -/
theorem tildeGraph_isConnected (hN : N.IsPhylogenetic) (hq : 2 ≤ #q) : (tildeGraph N q).IsConnected := by
  obtain ⟨x₀, hx₀, y₀, hy₀, hne₀⟩ := one_lt_card.1 (show 1 < #q by omega)
  have hl₀ := isKept_leaf hN hx₀ hy₀ hne₀
  have hleaf : ∀ {x y : X}, x ∈ q → y ∈ q → x ≠ y → ∀ (hx : IsKept N q (N.leaf x)) (hy : IsKept N q (N.leaf y)),
      (tildeGraph N q).Walks Set.univ (toV hx) (toV hy) := by
    intro x y hxq hyq hxy hx hy
    obtain ⟨t, p, r, hw⟩ := exists_isWedgePath_leaf hN x y
    have hK : ∀ f, f ∈ p ∨ f ∈ r → f ∈ trekArcs N q := fun f hf => by
      rw [trekArcs_eq_wedgeArcs hN]
      exact ⟨x, hxq, y, hyq, hxy, t, p, r, hw, hf⟩
    have htk : IsKept N q t := by
      cases p with
      | nil =>
        obtain rfl : t = N.leaf x := hw.left
        exact hx
      | cons g p =>
        rw [← hw.left.1]
        exact isKept_source (hK g (Or.inl (by simp)))
    exact (DirectedMultigraph.walks_symm _ (walks_of_isDirPath hw.left (fun f hf => hK f (Or.inl hf)) htk hx)).trans
      (walks_of_isDirPath hw.right (fun f hf => hK f (Or.inr hf)) htk hy)
  -- every vertex goes to a taxon
  have hto : ∀ w : TildeV N q, ∃ z ∈ q, ∃ hz : IsKept N q (N.leaf z), (tildeGraph N q).Walks Set.univ w (toV hz) := by
    intro w
    obtain ⟨v, hv, rfl⟩ := exists_toV w
    obtain ⟨e, he, hve⟩ := hv
    have he' := he
    rw [trekArcs_eq_wedgeArcs hN] at he'
    obtain ⟨x, hx, y, hy, hxy, t, p, r, hw, hep⟩ := he'
    have hK : ∀ f, f ∈ p ∨ f ∈ r → f ∈ trekArcs N q := fun f hf => by
      rw [trekArcs_eq_wedgeArcs hN]
      exact ⟨x, hx, y, hy, hxy, t, p, r, hw, hf⟩
    have hend : ∀ {z : X} {l : List E}, z ∈ q → (∃ z' ∈ q, z' ≠ z) → N.IsDirPath t l (N.leaf z) → (∀ f ∈ l, f ∈ trekArcs N q) → e ∈ l →
        ∃ z ∈ q, ∃ hz : IsKept N q (N.leaf z), (tildeGraph N q).Walks Set.univ (toV ⟨e, he, hve⟩) (toV hz) := by
      intro z l hz hz' hl hKl hel
      obtain ⟨l₁, l₂, heq, hl₁, hl₂⟩ := hl.split_of_mem hel
      obtain ⟨z', hz'q, hz'ne⟩ := hz'
      have hkz := isKept_leaf hN hz hz'q hz'ne.symm
      refine ⟨z, hz, hkz, ?_⟩
      have hw₂ := walks_of_isDirPath hl₂ (fun f hf => hKl f (by simp [heq, hf])) (isKept_target he) hkz
      rcases hve with rfl | rfl
      · exact (walks_of_mem_trekArcs he).trans hw₂
      · exact hw₂
    rcases hep with hep | hep
    · exact hend hx ⟨y, hy, hxy.symm⟩ hw.left (fun f hf => hK f (Or.inl hf)) hep
    · exact hend hy ⟨x, hx, hxy⟩ hw.right (fun f hf => hK f (Or.inr hf)) hep
  intro a b
  obtain ⟨z₁, hz₁, hk₁, hw₁⟩ := hto a
  obtain ⟨z₂, hz₂, hk₂, hw₂⟩ := hto b
  refine hw₁.trans (Relation.ReflTransGen.trans ?_ (DirectedMultigraph.walks_symm _ hw₂))
  by_cases hzz : z₁ = z₂
  · subst hzz
    exact .refl
  · exact hleaf hz₁ hz₂ hzz hk₁ hk₂

/-- A path from outside a set to inside it, or back, has an arc crossing the set. -/
theorem IsDirPath.exists_crosses {a b : V} {p : List E} (hp : N.IsDirPath a p b) {S : Set V} (h : ¬ (a ∈ S ↔ b ∈ S)) :
    ∃ f ∈ p, N.graph.Crosses f S := by
  by_contra hno
  push Not at hno
  exact h (hp.mem_iff hno)

/-- **A wedge path from outside a set through a vertex of it, and out again, has two arcs crossing the set.** -/
theorem IsWedgePath.exists_two_crosses (hN : N.IsPhylogenetic) {a b t v : V} {p r : List E} (hw : N.IsWedgePath a b t p r) {S : Set V}
    (ha : a ∉ S) (hb : b ∉ S) (hv : v ∈ S) (hvw : v ∈ t :: (p.map N.graph.target ++ r.map N.graph.target)) :
    ∃ f g, f ≠ g ∧ (f ∈ p ∨ f ∈ r) ∧ (g ∈ p ∨ g ∈ r) ∧ N.graph.Crosses f S ∧ N.graph.Crosses g S := by
  have hA := hN.acyclic
  by_cases ht : t ∈ S
  · obtain ⟨f, hf, hfc⟩ := IsDirPath.exists_crosses hw.left (S := S) (by tauto)
    obtain ⟨g, hg, hgc⟩ := IsDirPath.exists_crosses hw.right (S := S) (by tauto)
    refine ⟨f, g, ?_, Or.inl hf, Or.inr hg, hfc, hgc⟩
    rintro rfl
    exact hw.disjoint (List.mem_map_of_mem hf) (List.mem_map_of_mem hg)
  · have key : ∀ {b' : V} {l : List E}, N.IsDirPath t l b' → b' ∉ S → v ∈ l.map N.graph.target →
        ∃ f g, f ≠ g ∧ f ∈ l ∧ g ∈ l ∧ N.graph.Crosses f S ∧ N.graph.Crosses g S := by
      intro b' l hl hb' hvl
      obtain ⟨l₁, l₂, rfl, -, -, hl₁, hl₂⟩ := hl.split_of_mem_map hvl
      obtain ⟨f, hf, hfc⟩ := IsDirPath.exists_crosses hl₁ (S := S) (by tauto)
      obtain ⟨g, hg, hgc⟩ := IsDirPath.exists_crosses hl₂ (S := S) (by tauto)
      refine ⟨f, g, ?_, by simp [hf], by simp [hg], hfc, hgc⟩
      rintro rfl
      have hnd := hl.nodup hA
      rw [List.map_append] at hnd
      exact (List.nodup_append.1 hnd).2.2 _ (List.mem_map_of_mem hf) _ (List.mem_map_of_mem hg) rfl
    rcases List.mem_cons.1 hvw with rfl | hvw
    · exact absurd hv ht
    rcases List.mem_append.1 hvw with hvw | hvw
    · obtain ⟨f, g, hne, hf, hg, hfc, hgc⟩ := key hw.left ha hvw
      exact ⟨f, g, hne, Or.inl hf, Or.inl hg, hfc, hgc⟩
    · obtain ⟨f, g, hne, hf, hg, hfc, hgc⟩ := key hw.right hb hvw
      exact ⟨f, g, hne, Or.inr hf, Or.inr hg, hfc, hgc⟩

/-- **A class of the contracted graph other than that of a taxon has degree at least two**: a wedge path through it enters it and
leaves it. -/
theorem two_le_nodeDegree (hN : N.IsPhylogenetic) (w : TildeV N q)
    (hw : ∀ x ∈ q, ∀ hx : IsKept N q (N.leaf x), toV hx ≠ w) [Finite E] : 2 ≤ nodeDegree (tildeGraph N q) w := by
  obtain ⟨v, hv, rfl⟩ := exists_toV w
  obtain ⟨e, he, hve⟩ := id hv
  have he' := he
  rw [trekArcs_eq_wedgeArcs hN] at he'
  obtain ⟨x, hx, y, hy, hxy, t, p, r, hwp, hep⟩ := he'
  have hK : ∀ f, f ∈ p ∨ f ∈ r → f ∈ trekArcs N q := fun f hf => by
    rw [trekArcs_eq_wedgeArcs hN]
    exact ⟨x, hx, y, hy, hxy, t, p, r, hwp, hf⟩
  set S : Set V := {z | Quot.mk (contractRel N q) z = Quot.mk _ v} with hS
  have hSout : ∀ {z : X}, z ∈ q → (∃ z' ∈ q, z' ≠ z) → N.leaf z ∉ S := by
    intro z hz hz' hm
    obtain ⟨z', hz'q, hz'ne⟩ := hz'
    exact hw z hz (isKept_leaf hN hz hz'q hz'ne.symm) (Subtype.ext hm)
  have hvw : v ∈ t :: (p.map N.graph.target ++ r.map N.graph.target) := by
    have hmem : ∀ {l : List E} {b : V}, N.IsDirPath t l b → e ∈ l → v ∈ t :: l.map N.graph.target := by
      intro l b hl hel
      rcases hve with rfl | rfl
      · exact hl.source_mem_vertices hel
      · exact List.mem_cons_of_mem _ (List.mem_map_of_mem hel)
    rcases hep with hep | hep
    · rcases List.mem_cons.1 (hmem hwp.left hep) with h' | h'
      · simp [h']
      · simp [h']
    · rcases List.mem_cons.1 (hmem hwp.right hep) with h' | h'
      · simp [h']
      · simp [h']
  obtain ⟨f, g, hfg, hf, hg, hfc, hgc⟩ := IsWedgePath.exists_two_crosses hN hwp (hSout hx ⟨y, hy, hxy.symm⟩) (hSout hy ⟨x, hx, hxy⟩)
    (show v ∈ S from rfl) hvw
  -- neither is contracted
  have hnc : ∀ {f : E}, N.graph.Crosses f S → f ∉ contractedArcs N q := by
    intro f hc hfc
    have heq : Quot.mk (contractRel N q) (N.graph.source f) = Quot.mk _ (N.graph.target f) := Quot.sound ⟨f, hfc, rfl, rfl⟩
    simp only [hS, DirectedMultigraph.Crosses, Set.mem_ofPred_eq, heq] at hc
    tauto
  let F : TildeE N q := ⟨f, hK f hf, hnc hfc⟩
  let G' : TildeE N q := ⟨g, hK g hg, hnc hgc⟩
  have hFG : F ≠ G' := fun h => hfg (congrArg Subtype.val h)
  have hinc : ∀ {f' : TildeE N q}, N.graph.Crosses f'.1 S →
      f' ∈ ({e | (tildeGraph N q).target e = toV hv} ∪ {e | (tildeGraph N q).source e = toV hv} : Set (TildeE N q)) := by
    rintro f' (⟨h₁, -⟩ | ⟨h₁, -⟩)
    · exact Or.inr (Subtype.ext h₁)
    · exact Or.inl (Subtype.ext h₁)
  have hsub : ({F, G'} : Set (TildeE N q)) ⊆
      {e | (tildeGraph N q).target e = toV hv} ∪ {e | (tildeGraph N q).source e = toV hv} := by
    rintro f' (rfl | rfl)
    · exact hinc hfc
    · exact hinc hgc
  have hF : Finite (TildeE N q) := Subtype.finite
  have h₁ := Set.ncard_le_ncard hsub (Set.toFinite _)
  rw [Set.ncard_pair hFG] at h₁
  exact h₁.trans (Set.ncard_union_le _ _)

end Degrees

/-! ### The taxa, and `Q̃` -/

section QTilde

variable {N : RootedNetwork V E X} {q : Finset X}

theorem isKept_leaf' (hN : N.IsPhylogenetic) (hq : 2 ≤ #q) {x : X} (hx : x ∈ q) : IsKept N q (N.leaf x) := by
  obtain ⟨y, hy, hne⟩ := exists_mem_ne (show 1 < #q by omega) x
  exact isKept_leaf hN hx hy hne.symm

/-- **A taxon of `q` has degree one in the contracted graph**: it has one arc, a bridge, so that its class is itself. -/
theorem nodeDegree_toV_leaf (hN : N.IsPhylogenetic) {x : X} (hl : IsKept N q (N.leaf x)) : nodeDegree (tildeGraph N q) (toV hl) = 1 := by
  have := hN.finite_arcs
  have hF : Finite (TildeE N q) := Subtype.finite
  have hS : ∀ f ∈ contractedArcs N q, ¬ N.graph.Crosses f {N.leaf x} := by
    rintro f ⟨h, -, -, hb⟩ hc
    refine hb.1 (forall_isBridge_leaf hN x f ?_)
    rcases hc with ⟨h₁, -⟩ | ⟨h₁, -⟩
    · exact Or.inl h₁
    · exact Or.inr h₁
  have hiff : ∀ {v : V} (hv : IsKept N q v), toV hv = toV hl → v = N.leaf x := fun hv he =>
    (mem_iff_of_toV_eq hS he).2 rfl
  have h0 := (hN.leaves (N.leaf x)).mpr ⟨x, rfl⟩
  have hout : (tildeGraph N q).outdegree (toV hl) = 0 := by
    rw [DirectedMultigraph.outdegree_eq_zero_iff]
    intro e he
    exact (DirectedMultigraph.outdegree_eq_zero_iff _ _).mp h0 e.1 (hiff (isKept_source e.2.1) he)
  -- the arc into the taxon
  obtain ⟨e, he, hel⟩ := id hl
  have het : N.graph.target e = N.leaf x := by
    rcases hel with h' | h'
    · exact absurd h' ((DirectedMultigraph.outdegree_eq_zero_iff _ _).mp h0 e)
    · exact h'
  have hnc : e ∉ contractedArcs N q := by
    intro hc
    refine hS e hc ?_
    refine Or.inr ⟨het, fun hs => ?_⟩
    exact (DirectedMultigraph.outdegree_eq_zero_iff _ _).mp h0 e hs
  have hin : (tildeGraph N q).indegree (toV hl) = 1 := by
    rw [DirectedMultigraph.indegree, Set.ncard_eq_one]
    refine ⟨⟨e, he, hnc⟩, Set.eq_singleton_iff_unique_mem.2 ⟨?_, fun f hf => ?_⟩⟩
    · exact Subtype.ext (by simp only [tildeGraph_target, toV, het])
    · have hft : N.graph.target f.1 = N.leaf x := hiff (isKept_target f.2.1) hf
      refine Subtype.ext ?_
      exact eq_of_indegree_le_one hN (e := e) (f := f.1) (by rw [het, hN.leaf_indegree]) (hft.trans het.symm)
  rw [nodeDegree, hin, hout]

/-- **Definition 20** (`nanuq:definition20`), **`Q̃_xyzw`** (line 1026), for `q = {x, y, z, w}`: "contracting all 2- and 3-cycles, and suppressing degree 2 nodes",
as the labelled graph of `suppressDegreeTwo`. -/
def qTilde (hN : N.IsPhylogenetic) (hq : 2 ≤ #q) :
    LabelledGraph {w // nodeDegree (tildeGraph N q) w ≠ 2} {x // x ∈ q} where
  graph := suppressDegreeTwo (tildeGraph N q)
  leaf x := ⟨toV (isKept_leaf' hN hq x.2), by
    rw [nodeDegree_toV_leaf hN]
    omega⟩

end QTilde

/-! ### Cuts of the kept edges -/

section Cuts

variable [Fintype V] [Fintype E] {N : RootedNetwork V E X} {q : Finset X} {h : V}

/-- An arc of a cycle that is kept has a taxon of `q` not below the reticulation: if all were below it, both legs of a wedge path would
go through the arc below the reticulation. -/
theorem exists_not_below_of_mem_blobArcs (hN : N.IsPhylogenetic) (hBin : N.IsBinary) (hLevel : IsLevelOne N)
    (hh₂ : 2 ≤ N.graph.indegree h) {k : E} (hkb : k ∈ N.graph.blobArcs h) (hK : k ∈ N.wedgeArcs (q : Set X)) :
    ∃ c ∈ q, ¬ N.graph.Reaches h (N.leaf c) := by
  by_contra hall
  push Not at hall
  obtain ⟨eh, hehs, hehu, hehb⟩ := exists_child_arc hN hBin hLevel (v := h) .refl hh₂
  have hleaf : ∀ x, N.leaf x ≠ h := by
    intro x he
    have := hN.leaf_indegree x
    rw [he] at this
    omega
  have hbelow : ∀ x ∈ q, N.graph.Reaches (N.graph.target eh) (N.leaf x) := fun x hx =>
    reaches_target_of_unique_out hehu (hall x hx) (hleaf x)
  obtain ⟨x, hx, y, hy, -, t, p, r, hw, hk⟩ := hK
  have hs : N.graph.blobSetoid h (N.graph.source k) := (mem_blobArcs_iff.1 hkb).1
  have hsr : N.graph.Reaches (N.graph.source k) h := reaches_reticulation hN hLevel (v := h) .refl hh₂ hs
  have ht : N.graph.Reaches t (N.graph.source k) := by
    rcases hk with hk | hk
    · exact (hw.left.reaches_of_mem hk).1
    · exact (hw.right.reaches_of_mem hk).1
  have htn : t ∉ {w | N.graph.Reaches (N.graph.target eh) w} := fun hc =>
    not_reaches_source hN eh (hehs ▸ (Relation.ReflTransGen.trans hc ht).trans hsr)
  obtain ⟨f, hf, hfc⟩ := IsDirPath.exists_crosses hw.left (S := {w | N.graph.Reaches (N.graph.target eh) w})
    (fun hi => htn (hi.2 (hbelow x hx)))
  obtain ⟨g, hg, hgc⟩ := IsDirPath.exists_crosses hw.right (S := {w | N.graph.Reaches (N.graph.target eh) w})
    (fun hi => htn (hi.2 (hbelow y hy)))
  have hfe := (isBridge_crosses_iff hN hehb f).1 hfc
  have hge := (isBridge_crosses_iff hN hehb g).1 hgc
  subst hfe
  subst hge
  exact hw.disjoint (List.mem_map_of_mem hf) (List.mem_map_of_mem hg)

omit [Fintype V] [Fintype E] in
/-- A bridge has a cut. -/
theorem exists_cut_of_isBridge (hN : N.IsPhylogenetic) {e : E} (hb : N.graph.underlying.IsBridge e) :
    ∃ S : Set V, N.graph.Crosses e S ∧ ∀ f, f ≠ e → ¬ N.graph.Crosses f S :=
  ⟨{u | N.graph.Reaches (N.graph.target e) u}, (isBridge_crosses_iff hN hb e).2 rfl,
    fun _ hne hc => hne ((isBridge_crosses_iff hN hb _).1 hc)⟩

/-- **A kept arc of a cycle that is not kept whole has a cut of the kept arcs**: no taxon of `q` is below the reticulation, so the
reticulation arcs are not kept, and they are the only others to cross what is below the arc. -/
theorem exists_cut_of_not_isQuartetCycle (hN : N.IsPhylogenetic) (hBin : N.IsBinary) (hLevel : IsLevelOne N)
    (hh₂ : 2 ≤ N.graph.indegree h) {e : E} (heb : e ∈ N.graph.blobArcs h) (hK : e ∈ trekArcs N q)
    (hnq : ¬ IsQuartetCycle N q h) :
    ∃ S : Set V, N.graph.Crosses e S ∧ ∀ f ∈ trekArcs N q, f ≠ e → ¬ N.graph.Crosses f S := by
  rw [trekArcs_eq_wedgeArcs hN] at hK ⊢
  have hnone : ∀ a ∈ q, ¬ N.graph.Reaches h (N.leaf a) := by
    intro a ha hr
    exact hnq ((isQuartetCycle_iff hN hBin hLevel hh₂).2
      ⟨⟨a, ha, hr⟩, exists_not_below_of_mem_blobArcs hN hBin hLevel hh₂ heb hK⟩)
  have hnoh : ∀ f ∈ N.wedgeArcs (q : Set X), N.graph.target f ≠ h := fun f hf =>
    target_ne_of_mem_wedgeArcs hf hnone
  have htb : N.graph.blobSetoid h (N.graph.target e) := (mem_blobArcs_iff.1 heb).2
  refine ⟨{u | N.graph.Reaches (N.graph.target e) u}, Or.inr ⟨.refl, not_reaches_source hN e⟩, fun f hf hne hc => ?_⟩
  have hclosed : ¬ (N.graph.Reaches (N.graph.target e) (N.graph.source f) ∧
      ¬ N.graph.Reaches (N.graph.target e) (N.graph.target f)) := fun hc' =>
    hc'.2 (hc'.1.tail ⟨f, rfl, rfl⟩)
  rcases hc with hc | ⟨hft, hfs⟩
  · exact hclosed hc
  by_cases hfe : N.graph.target f = N.graph.target e
  · by_cases hdeg : 2 ≤ N.graph.indegree (N.graph.target e)
    · exact hnoh f hf (hfe.trans (reticulation_unique hN hLevel htb hdeg (v := h) .refl hh₂))
    · exact hne (eq_of_indegree_le_one hN (by omega) hfe)
  · obtain ⟨hb, h2⟩ := entering_of_strictBelow hN hft hfe hfs
    exact hnoh f hf (reticulation_unique hN hLevel (sameBlob_trans htb hb) h2 (v := h) .refl hh₂)

variable [Fintype X] [DecidableEq X]

/-- A kept cycle of size at least four has its four taxa in distinct blocks. -/
theorem not_blockWalk_of_four_le (hN : N.IsPhylogenetic) (hBin : N.IsBinary) (hLevel : IsLevelOne N) (hq : #q = 4)
    (hQ : IsQuartetCycle N q h) (h4 : 4 ≤ cycleSize N q h) {x y : X} (hx : x ∈ q) (hy : y ∈ q) (hxy : x ≠ y) :
    ¬ BlockWalk N h (N.leaf x) (N.leaf y) := by
  intro hw
  have hx' : ∀ z, ¬ N.graph.blobSetoid h (N.leaf z) := leaf_not_sameBlob hN .refl hQ.1
  have hex : ∀ z, ∃ b, IsAttachment N h z b := fun z => exists_isAttachment hN (hx' z)
  choose att hatt using hex
  have hsub : {u | ∃ z ∈ q, IsAttachment N h z u} ⊆ att '' ((q.erase y : Finset X) : Set X) := by
    rintro u ⟨z, hz, hzu⟩
    by_cases hzy : z = y
    · subst hzy
      refine ⟨x, mem_coe.2 (mem_erase.2 ⟨hxy, hx⟩), ?_⟩
      exact IsAttachment.eq_of_isAttachment (hx' _) (IsAttachment.of_blockWalk (hatt x) hw) hzu
    · exact ⟨z, mem_coe.2 (mem_erase.2 ⟨hzy, hz⟩), IsAttachment.eq_of_isAttachment (hx' z) (hatt z) hzu⟩
  have hc := Set.ncard_le_ncard hsub (Set.toFinite _)
  have hi := Set.ncard_image_le (f := att) (Set.toFinite ((q.erase y : Finset X) : Set X))
  rw [Set.ncard_coe_finset, card_erase_of_mem hy, hq] at hi
  rw [cycleSize_eq hN hBin hLevel hQ] at h4
  omega

omit [DecidableEq X] in
/-- A kept cycle has size at most four. -/
theorem cycleSize_le_four (hN : N.IsPhylogenetic) (hBin : N.IsBinary) (hLevel : IsLevelOne N) (hq : #q = 4)
    (hQ : IsQuartetCycle N q h) : cycleSize N q h ≤ 4 := by
  have hx' : ∀ z, ¬ N.graph.blobSetoid h (N.leaf z) := leaf_not_sameBlob hN .refl hQ.1
  have hex : ∀ z, ∃ b, IsAttachment N h z b := fun z => exists_isAttachment hN (hx' z)
  choose att hatt using hex
  have hsub : {u | ∃ z ∈ q, IsAttachment N h z u} ⊆ att '' (q : Set X) := by
    rintro u ⟨z, hz, hzu⟩
    exact ⟨z, mem_coe.2 hz, IsAttachment.eq_of_isAttachment (hx' z) (hatt z) hzu⟩
  have hc := Set.ncard_le_ncard hsub (Set.toFinite _)
  have hi := Set.ncard_image_le (f := att) (Set.toFinite (q : Set X))
  rw [Set.ncard_coe_finset, hq] at hi
  rw [cycleSize_eq hN hBin hLevel hQ]
  omega

/-- On a treelike set of four taxa all the kept cycles are contracted. -/
theorem cycleSize_le_three_of_isTreelike (hN : N.IsPhylogenetic) (hBin : N.IsBinary) (hLevel : IsLevelOne N) (hq : #q = 4)
    (ht : IsTreelike N q) (hQ : IsQuartetCycle N q h) : cycleSize N q h ≤ 3 := by
  by_contra hc
  obtain ⟨⟨a, ha, hr⟩, -⟩ := (isQuartetCycle_iff hN hBin hLevel hQ.1).1 hQ
  exact not_isTreelike_of_distinct hN hBin hLevel (v := h) .refl hQ.1 hq
    (fun x hx y hy hxy => not_blockWalk_of_four_le hN hBin hLevel hq hQ (by omega) hx hy hxy) ha hr ht

omit [Fintype V] [Fintype E] [Fintype X] [DecidableEq X] in
/-- An arc of a blob that is not a bridge is an arc of the cycle of a reticulation. -/
theorem exists_reticulation_of_not_isBridge (hN : N.IsPhylogenetic) {e : E} (hb : ¬ N.graph.underlying.IsBridge e) :
    ∃ h, 2 ≤ N.graph.indegree h ∧ e ∈ N.graph.blobArcs h := by
  rcases exists_reticulation_or_forall_isBridge hN (N.graph.target e) with ⟨h, hh, hh₂⟩ | hall
  · have hs := sameBlob_of_not_isBridge hb
    refine ⟨h, hh₂, mem_blobArcs_iff.2 ⟨sameBlob_trans (sameBlob_symm hh) (sameBlob_symm hs), sameBlob_symm hh⟩⟩
  · exact absurd (hall e (Or.inr rfl)) hb

/-- **On a treelike set of four taxa the contracted graph is a tree**: it is connected, and every edge has a side. -/
theorem isTree_tildeGraph (hN : N.IsPhylogenetic) (hBin : N.IsBinary) (hLevel : IsLevelOne N) (hq : #q = 4)
    (ht : IsTreelike N q) : (tildeGraph N q).IsTree := by
  refine ⟨tildeGraph_isConnected hN (by omega), fun e => ?_⟩
  obtain ⟨S, hcr, hS⟩ : ∃ S : Set V, N.graph.Crosses e.1 S ∧ ∀ f ∈ trekArcs N q, f ≠ e.1 → ¬ N.graph.Crosses f S := by
    by_cases hb : N.graph.underlying.IsBridge e.1
    · obtain ⟨S, h₁, h₂⟩ := exists_cut_of_isBridge hN hb
      exact ⟨S, h₁, fun f _ hne => h₂ f hne⟩
    · obtain ⟨h, hh₂, heb⟩ := exists_reticulation_of_not_isBridge hN hb
      refine exists_cut_of_not_isQuartetCycle hN hBin hLevel hh₂ heb e.2.1 fun hQ => e.2.2 ?_
      exact ⟨h, hQ, cycleSize_le_three_of_isTreelike hN hBin hLevel hq ht hQ, heb⟩
  exact not_walks_of_isSideOf (isSideOf_tildeSide hcr hS)

end Cuts

/-! ### The tree case -/

section TreeForm

variable [Fintype V] [Fintype E] [Fintype X] [DecidableEq X] {N : RootedNetwork V E X} {q : Finset X}

omit [Fintype X] [DecidableEq X] in
/-- The edges of a kept cycle that is contracted are not a cut of the kept edges. -/
theorem notMem_contractedArcs_of_cut (hN : N.IsPhylogenetic) (hBin : N.IsBinary) (hLevel : IsLevelOne N) {e : E} {S : Set V}
    (hS : ∀ f ∈ trekArcs N q, N.graph.Crosses f S ↔ f = e) : e ∉ contractedArcs N q := by
  rintro ⟨h, hQ, -, heb⟩
  obtain ⟨T, k₁, k₂, pL, pR, C⟩ := exists_blobCycle hN hBin hLevel (v := h) .refl hQ.1
  have hcyc : ∀ f, f ∈ pL ++ [k₁] ∨ f ∈ pR ++ [k₂] → f ∈ trekArcs N q := by
    rintro f (hf | hf)
    · exact hQ.2 f (mem_blobArcs_iff.2 (C.sameBlob_of_mem hN hf))
    · exact hQ.2 f (mem_blobArcs_iff.2 (C.swap.sameBlob_of_mem hN hf))
  have hF₁ := C.notMem_of_cut hN hcyc hS
  have hF₂ := C.swap.notMem_of_cut hN (fun f hf => hcyc f hf.symm) hS
  obtain ⟨h₁, h₂⟩ := mem_blobArcs_iff.1 heb
  by_cases hth : N.graph.target e = h
  · rcases C.arcs e hth with rfl | rfl
    · exact hF₁ (by simp)
    · exact hF₂ (by simp)
  · rcases C.mem_of_arc hN hLevel hQ.1 h₁ h₂ hth with hf | hf
    · exact hF₁ (by simp [hf])
    · exact hF₂ (by simp [hf])

omit [Fintype X] [DecidableEq X] in
/-- **The sides of the edges of `Q̃` are the cut-edge splits of the subnetwork on `q`**, on a treelike set. -/
theorem qTilde_hasSide_iff (hN : N.IsPhylogenetic) (hBin : N.IsBinary) (hLevel : IsLevelOne N) [Fintype X] [DecidableEq X] (hq : #q = 4)
    (ht : IsTreelike N q) (A : Set {x // x ∈ q}) :
    (qTilde hN (by omega : 2 ≤ #q)).HasSide A ↔ N.HasWedgeCutSplit (q : Set X) (Subtype.val '' A) := by
  have hG := isTree_tildeGraph hN hBin hLevel hq ht
  unfold qTilde
  rw [hasSide_iff hG]
  constructor
  · rintro ⟨e, T, hT, hA⟩
    refine ⟨e.1, by rw [← trekArcs_eq_wedgeArcs hN]; exact e.2.1, {v | ∃ hv : IsKept N q v, toV hv ∈ T}, fun f hf => ?_, fun x hx => ?_⟩
    · rw [← trekArcs_eq_wedgeArcs hN] at hf
      constructor
      · intro hc
        by_contra hne
        exact crosses_of_isSideOf hT hf hne hc
      · rintro rfl
        rcases hT.crosses with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
        · exact Or.inl ⟨⟨isKept_source e.2.1, h₁⟩, fun ⟨_, h'⟩ => h₂ h'⟩
        · exact Or.inr ⟨⟨isKept_target e.2.1, h₁⟩, fun ⟨_, h'⟩ => h₂ h'⟩
    · have hx' : x ∈ q := mem_coe.1 hx
      constructor
      · rintro ⟨hv, hm⟩
        refine ⟨⟨x, hx'⟩, ?_, rfl⟩
        rw [← hA]
        exact hm
      · rintro ⟨y, hy, rfl⟩
        rw [← hA] at hy
        exact ⟨isKept_leaf' hN (by omega) y.2, hy⟩
  · rintro ⟨e, heK, S, hS, hAS⟩
    rw [← trekArcs_eq_wedgeArcs hN] at heK
    have hS' : ∀ f ∈ trekArcs N q, N.graph.Crosses f S ↔ f = e := by
      intro f hf
      rw [trekArcs_eq_wedgeArcs hN] at hf
      exact hS f hf
    have hnc := notMem_contractedArcs_of_cut hN hBin hLevel hS'
    have hC : ∀ f ∈ contractedArcs N q, ¬ N.graph.Crosses f S := by
      rintro f hf hc
      obtain ⟨h, hQ, -, hb⟩ := id hf
      have := (hS' f (hQ.2 f hb)).1 hc
      exact hnc (this ▸ hf)
    refine ⟨⟨e, heK, hnc⟩, tildeSide N q S, isSideOf_tildeSide ((hS' e heK).2 rfl) fun f hf hne hc => hne ((hS' f hf).1 hc), ?_⟩
    ext x
    simp only [Set.mem_preimage]
    rw [toV_mem_tildeSide hC]
    have := hAS x.1 (mem_coe.2 x.2)
    rw [this]
    constructor
    · rintro ⟨y, hy, hyx⟩
      rwa [← Subtype.ext hyx]
    · exact fun hx => ⟨x, hx, rfl⟩

omit [Fintype V] [Fintype E] [Fintype X] [DecidableEq X] in
/-- A taxon is alone in its class. -/
theorem eq_of_toV_leaf_eq (hN : N.IsPhylogenetic) {x : X} {v : V} {hx : IsKept N q (N.leaf x)} {hv : IsKept N q v}
    (h : toV hv = toV hx) : v = N.leaf x := by
  have hS : ∀ f ∈ contractedArcs N q, ¬ N.graph.Crosses f {N.leaf x} := by
    rintro f ⟨h, -, -, hb⟩ hc
    refine hb.1 (forall_isBridge_leaf hN x f ?_)
    rcases hc with ⟨h₁, -⟩ | ⟨h₁, -⟩
    · exact Or.inl h₁
    · exact Or.inr h₁
  exact (mem_iff_of_toV_eq hS h).2 rfl

/-- The numbers of `LabelledGraph.hasStar_or_hasQuartet`. -/
theorem qTilde_hasStar_or_hasQuartet (hN : N.IsPhylogenetic) (hBin : N.IsBinary) (hLevel : IsLevelOne N) (hq : #q = 4)
    (ht : IsTreelike N q) {a b c d : {x // x ∈ q}} (h : ({a, b, c, d} : Finset {x // x ∈ q}).card = 4) :
    (qTilde hN (by omega : 2 ≤ #q)).HasStarTopology a b c d ∨ (qTilde hN (by omega : 2 ≤ #q)).HasQuartetTopology a b c d ∨
      (qTilde hN (by omega : 2 ≤ #q)).HasQuartetTopology a c b d ∨ (qTilde hN (by omega : 2 ≤ #q)).HasQuartetTopology a d b c := by
  have hG := isTree_tildeGraph hN hBin hLevel hq ht
  have hq2 : 2 ≤ #q := by omega
  have hne : Nonempty {w // nodeDegree (tildeGraph N q) w ≠ 2} := ⟨(qTilde hN hq2).leaf a⟩
  refine LabelledGraph.hasStar_or_hasQuartet (qTilde hN hq2) (isTree_suppressDegreeTwo hG) ?_ (by simpa using hq) (fun x => ?_) (fun v hv => ?_) h
  · intro x y hxy
    have h₁ : toV (isKept_leaf' hN hq2 x.2) = toV (isKept_leaf' hN hq2 y.2) := congrArg Subtype.val hxy
    exact Subtype.ext (hN.leaf_injective (eq_of_toV_leaf_eq hN h₁))
  · change ((suppressDegreeTwo (tildeGraph N q)).neighborSet _).ncard = 1
    rw [ncard_neighborSet_suppressDegreeTwo hG]
    exact nodeDegree_toV_leaf hN (isKept_leaf' hN hq2 x.2)
  · change 3 ≤ ((suppressDegreeTwo (tildeGraph N q)).neighborSet _).ncard
    rw [ncard_neighborSet_suppressDegreeTwo hG]
    have h₂ := two_le_nodeDegree hN v.1 fun x hx hk he => hv ⟨x, hx⟩ (Subtype.ext he)
    have h₃ := v.2
    omega

omit [Fintype V] [Fintype E] [Fintype X] in
/-- A cut-edge split of the subnetwork, on two taxa of `q`, is `InducedCutSplit`. -/
theorem inducedCutSplit_of_hasWedgeCutSplit (hN : N.IsPhylogenetic) {a b c d : X} (h : ({a, b, c, d} : Finset X).card = 4)
    (hqe : q = {a, b, c, d}) (hw : N.HasWedgeCutSplit (q : Set X) (({a, b} : Finset X) : Set X)) :
    InducedCutSplit N (quartetTree a b c d h) := by
  obtain ⟨hab, hac, had, hbc, hbd, hcd⟩ := ne_of_card_four h
  refine ⟨{a, b}, by simp, ?_⟩
  rw [quartetTree_taxa, ← hqe]
  refine (hasWedgeCutSplit_iff_hasCutSplitOn hN ?_ ?_).1 hw
  · exact ⟨a, by rw [hqe]; simp, by simp⟩
  · exact ⟨c, by rw [hqe]; simp, by simp [hac.symm, hbc.symm]⟩

/-- A side with two taxa of `q` is the cut-edge split. -/
theorem inducedCutSplit_of_mem_splits (hN : N.IsPhylogenetic) (hBin : N.IsBinary) (hLevel : IsLevelOne N) (hq : #q = 4)
    (ht : IsTreelike N q) {u v w z : {x // x ∈ q}} (hc : ({u.1, v.1, w.1, z.1} : Finset X).card = 4) (hq' : q = {u.1, v.1, w.1, z.1})
    (hm : ({u, v} : Finset {x // x ∈ q}) ∈ (qTilde hN (by omega : 2 ≤ #q)).splits) :
    InducedCutSplit N (quartetTree u.1 v.1 w.1 z.1 hc) := by
  obtain ⟨-, -, -, hS⟩ := mem_filter.1 hm
  have := (qTilde_hasSide_iff hN hBin hLevel hq ht _).1 hS
  refine inducedCutSplit_of_hasWedgeCutSplit hN hc hq' ?_
  convert this using 2
  ext x
  simp only [coe_insert, coe_singleton, Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_image]
  constructor
  · rintro (rfl | rfl)
    · exact ⟨u, Or.inl rfl, rfl⟩
    · exact ⟨v, Or.inr rfl, rfl⟩
  · rintro ⟨y, (rfl | rfl), rfl⟩
    · exact Or.inl rfl
    · exact Or.inr rfl

/-- The star has no side with two taxa on each side. -/
theorem false_of_star_of_cut (hN : N.IsPhylogenetic) (hBin : N.IsBinary) (hLevel : IsLevelOne N) (hq : #q = 4)
    (ht : IsTreelike N q) {a b c d : {x // x ∈ q}} (huniv : ∀ x : {x // x ∈ q}, x = a ∨ x = b ∨ x = c ∨ x = d)
    (hst : (qTilde hN (by omega : 2 ≤ #q)).HasStarTopology a b c d) {u v w z : {x // x ∈ q}}
    (hc : ({u.1, v.1, w.1, z.1} : Finset X).card = 4)
    (hcut : N.HasCutSplitOn (q : Set X) (({u.1, v.1} : Finset X) : Set X)) : False := by
  obtain ⟨huv, huw, huz, hvw, hvz, hwz⟩ := ne_of_card_four hc
  have hw' := (hasWedgeCutSplit_iff_hasCutSplitOn hN (Y := (q : Set X)) (A := (({u.1, v.1} : Finset X) : Set X))
    ⟨u.1, mem_coe.2 u.2, by simp⟩ ⟨w.1, mem_coe.2 w.2, by simp [huw.symm, hvw.symm]⟩).2 hcut
  have hs' : (qTilde hN (by omega : 2 ≤ #q)).HasSide (({u, v} : Finset {x // x ∈ q}) : Set {x // x ∈ q}) := by
    refine (qTilde_hasSide_iff hN hBin hLevel hq ht _).2 ?_
    convert hw' using 2
    ext x
    simp only [coe_insert, coe_singleton, Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_image]
    constructor
    · rintro ⟨y, (rfl | rfl), rfl⟩
      · exact Or.inl rfl
      · exact Or.inr rfl
    · rintro (rfl | rfl)
      · exact ⟨u, Or.inl rfl, rfl⟩
      · exact ⟨v, Or.inr rfl, rfl⟩
  have huv' : u ≠ v := fun he => huv (congrArg Subtype.val he)
  have hcu : ({u, v} : Finset {x // x ∈ q}).card = 2 := card_pair huv'
  have hmem : ({u, v} : Finset {x // x ∈ q}) ∈ (qTilde hN (by omega : 2 ≤ #q)).splits := by
    refine mem_filter.2 ⟨mem_univ _, ⟨u, by simp⟩, ⟨w, ?_⟩, hs'⟩
    simp only [mem_compl, mem_insert, mem_singleton, not_or]
    exact ⟨fun he => huw (congrArg Subtype.val he).symm, fun he => hvw (congrArg Subtype.val he).symm⟩
  have hcc : ({u, v} : Finset {x // x ∈ q})ᶜ.card = 2 := by
    rw [card_compl, hcu]
    simp [hq]
  rcases hst.card_of_mem_splits huniv hmem with h' | h' <;> omega

/-- **On a treelike set of four taxa, `Q̃` "has form `ab|cd`" exactly when `ab|cd` is the cut-edge split.** `Q̃` is the literal tree
with cherries `{a, b}`, `{c, d}`. -/
theorem qTilde_hasQuartetTopology_iff (hN : N.IsPhylogenetic) (hBin : N.IsBinary) (hLevel : IsLevelOne N) (hq : #q = 4)
    (ht : IsTreelike N q) {a b c d : {x // x ∈ q}} (h : ({a.1, b.1, c.1, d.1} : Finset X).card = 4) :
    (qTilde hN (by omega : 2 ≤ #q)).HasQuartetTopology a b c d ↔ InducedCutSplit N (quartetTree a.1 b.1 c.1 d.1 h) := by
  have hne : Nonempty X := ⟨a.1⟩
  obtain ⟨hab, hac, had, hbc, hbd, hcd⟩ := ne_of_card_four h
  have hqe : q = {a.1, b.1, c.1, d.1} := by
    refine (eq_of_subset_of_card_le (fun z hz => ?_) (by rw [h, hq])).symm
    simp only [mem_insert, mem_singleton] at hz
    rcases hz with rfl | rfl | rfl | rfl
    · exact a.2
    · exact b.2
    · exact c.2
    · exact d.2
  have huniv : ∀ x : {x // x ∈ q}, x = a ∨ x = b ∨ x = c ∨ x = d := by
    rintro ⟨x, hx⟩
    have hx' := hx
    rw [hqe] at hx'
    simp only [mem_insert, mem_singleton] at hx'
    rcases hx' with h' | h' | h' | h'
    · exact Or.inl (Subtype.ext h')
    · exact Or.inr (Or.inl (Subtype.ext h'))
    · exact Or.inr (Or.inr (Or.inl (Subtype.ext h')))
    · exact Or.inr (Or.inr (Or.inr (Subtype.ext h')))
  have hne' : ∀ {u v : {x // x ∈ q}}, u.1 ≠ v.1 → u ≠ v := fun h' he => h' (congrArg Subtype.val he)
  have hcard' : ({a, b, c, d} : Finset {x // x ∈ q}).card = 4 := by
    rw [card_insert_of_notMem (by simp [hne' hab, hne' hac, hne' had]), card_insert_of_notMem (by simp [hne' hbc, hne' hbd]),
      card_pair (hne' hcd)]
  constructor
  · intro hT
    exact inducedCutSplit_of_mem_splits hN hBin hLevel hq ht h hqe (hT.pair_mem_splits huniv)
  · intro hs
    rcases qTilde_hasStar_or_hasQuartet hN hBin hLevel hq ht hcard' with hst | h₁ | h₂ | h₃
    · exfalso
      obtain ⟨B, hB, hcut⟩ := hs
      rw [quartetTree_taxa, ← hqe] at hcut
      simp only [quartetTree_val, mem_insert, mem_singleton] at hB
      rcases hB with rfl | rfl
      · exact false_of_star_of_cut hN hBin hLevel hq ht huniv hst h hcut
      · have hc' : ({c.1, d.1, a.1, b.1} : Finset X).card = 4 := by
          rw [← h]
          congr 1
          ext x
          simp only [mem_insert, mem_singleton]
          tauto
        exact false_of_star_of_cut hN hBin hLevel hq ht huniv hst hc' hcut
    · exact h₁
    · exfalso
      have hc' := card_acbd h
      have hq' : q = {a.1, c.1, b.1, d.1} := by
        refine hqe.trans ?_
        ext x
        simp only [mem_insert, mem_singleton]
        tauto
      have hs' := inducedCutSplit_of_mem_splits hN hBin hLevel hq ht hc' hq' (h₂.pair_mem_splits (by
        intro x
        rcases huniv x with h' | h' | h' | h' <;> simp [h']))
      refine quartetTree_ne_acbd h (eq_of_inducedCutSplit hN hs hs' ?_)
      rw [quartetTree_taxa, quartetTree_taxa]
      exact hqe.symm.trans hq'
    · exfalso
      have hc' := card_adbc h
      have hq' : q = {a.1, d.1, b.1, c.1} := by
        refine hqe.trans ?_
        ext x
        simp only [mem_insert, mem_singleton]
        tauto
      have hs' := inducedCutSplit_of_mem_splits hN hBin hLevel hq ht hc' hq' (h₃.pair_mem_splits (by
        intro x
        rcases huniv x with h' | h' | h' | h' <;> simp [h']))
      refine quartetTree_ne_adbc h (eq_of_inducedCutSplit hN hs hs' ?_)
      rw [quartetTree_taxa, quartetTree_taxa]
      exact hqe.symm.trans hq'

end TreeForm

end External.AllmanBanosRhodes2019.Quartet
