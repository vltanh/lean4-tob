module

public import Basic.Phylogenetics.InducedNetwork
public import TOBQMC.Level1Blobs

/-!
# Wedge paths, the subnetwork on a set of taxa, and Lemma 4 of TOB-QMC on it

TOB-QMC reasons on the restriction `N⁻|Y` of a semi-directed network: the union of the wedge paths
between the taxa of `Y` (§4.1), with degree-two vertices, parallel arcs and degree-two blobs suppressed.
Wedge paths make sense on the rooted network `N⁺`, and correspond to the paths of `N⁻` with no
v-structure. This file defines them on `RootedNetwork`, and proves the graph statements of the paper's
proof of Lemma 4 (lines 541–556 of v5). `TOBQMC.lemma4` in `TOBQMC/Level1.lean` assembles them.

## The subnetwork and the representation bridge

* `IsDirPath`, `IsWedgePath`, `OnWedgePath`: directed paths as lists of arcs, and wedge paths.
* `wedgeArcs`, `HasWedgeCutSplit`: the arcs of the subnetwork on `Y` and the splits of its cut edges.
* `wedgeArcs_subset_belowArcs`: the subnetwork lies below the least stable ancestor of `Y`, in the part of
  `N⁺` that `N⁻` keeps.
* `hasWedgeCutSplit_iff_hasCutSplitOn`, `hasWedgeCutSplit_iff_inducedNetwork_hasCutSplit`: for a split of
  `Y` with both sides nonempty, a cut edge of the subnetwork inducing it is the predicate `HasCutSplitOn`,
  and a cut edge of the induced network. This holds for every network, binary or not, of any level.

The paper's suppression of degree-two vertices, parallel arcs and degree-two blobs is not carried out on the
subnetwork, and `inducedNetwork` suppresses only the degree-two vertices. The other two keep the splits of cut
edges: a parallel pair or a degree-two blob lies between two cut edges with one split, and the edge
replacing them has that split. This remark is not formalized, and no proof depends on it.

## A level-1 blob

* `BlobCycle`, `exists_blobCycle`: a blob of a binary level-1 network is a cycle, two directed paths from
  its top to its reticulation `h`.
* `isDirPath_unique`, `wedgePath_unique`: only one wedge path between two vertices of the blob other than `h`.
* `exactly_two_wedgePaths`: exactly two wedge paths from `h` to another vertex of the blob, and their
  union is the blob.
* `IsAttachment`, `AttachPath`: the attachment `B(x)` of a taxon, and the wedge path from `x` to `B(x)`.

## Lemma 4 on the subnetwork

* `not_hasWedgeCutSplit`: `⇐`. Four taxa in distinct blocks, one below `h`: the subnetwork contains the cycle
  with the four taxa attached, and no cut edge of it induces a `2|2` split.
* `exists_hasWedgeCutSplit`: `⇒`. Four taxa in distinct blocks, none below `h`: the attachments are distinct
  and on a single path, and their order along it gives a cut edge with a `2|2` split.
-/

@[expose] public noncomputable section

open Phylogenetics Phylogenetics.RootedNetwork
open scoped Classical

namespace Phylogenetics.RootedNetwork

variable {V E X : Type*} {N : RootedNetwork V E X}

/-! ### Directed paths as lists of arcs -/

/-- The list `p` of arcs is a directed path from `u` to `v`. -/
def IsDirPath (N : RootedNetwork V E X) : V → List E → V → Prop
  | u, [], v => u = v
  | u, e :: p, v => N.graph.source e = u ∧ IsDirPath N (N.graph.target e) p v

/-- **Wedge path** (TOB-QMC §4.1, lines 340–342 of v5): a sequence of distinct vertices
`v = u₀, …, u_k = v'` with a vertex `u` that "roots" it, so that the part from `u` to `v` and the part
from `u` to `v'` are directed paths, here `p` and `q`. The sequence is
`(p.map target).reverse ++ u :: q.map target`. In a semi-directed network, wedge paths are the paths
containing no v-structure. -/
structure IsWedgePath (N : RootedNetwork V E X) (v v' u : V) (p q : List E) : Prop where
  left : N.IsDirPath u p v
  right : N.IsDirPath u q v'
  distinct : ((p.map N.graph.target).reverse ++ u :: q.map N.graph.target).Nodup

/-- The arc `e` is on a wedge path from `v` to `v'`. -/
def OnWedgePath (N : RootedNetwork V E X) (v v' : V) (e : E) : Prop :=
  ∃ u p q, N.IsWedgePath v v' u p q ∧ (e ∈ p ∨ e ∈ q)

/-- The arcs of the subnetwork on `Y` (TOB-QMC §4.1, lines 348–350 of v5): the arcs on the wedge paths
between pairs of taxa of `Y`. -/
def wedgeArcs (N : RootedNetwork V E X) (Y : Set X) : Set E :=
  {e | ∃ x ∈ Y, ∃ y ∈ Y, x ≠ y ∧ N.OnWedgePath (N.leaf x) (N.leaf y) e}

/-- `A ∩ Y | Y \ A` is induced by a cut edge of the subnetwork on `Y`: an arc of the subnetwork is the
only arc of the subnetwork crossing a vertex set meeting `Y` exactly in `A`. -/
def HasWedgeCutSplit (N : RootedNetwork V E X) (Y A : Set X) : Prop :=
  ∃ e ∈ N.wedgeArcs Y, ∃ S : Set V,
    (∀ f ∈ N.wedgeArcs Y, N.graph.Crosses f S ↔ f = e) ∧ ∀ x ∈ Y, N.leaf x ∈ S ↔ x ∈ A

section Paths

variable {u v w : V} {e f : E} {p q : List E}

@[simp] theorem isDirPath_nil : N.IsDirPath u [] v ↔ u = v := Iff.rfl

@[simp] theorem isDirPath_cons :
    N.IsDirPath u (e :: p) v ↔ N.graph.source e = u ∧ N.IsDirPath (N.graph.target e) p v := Iff.rfl

theorem isDirPath_append : N.IsDirPath u (p ++ q) w ↔ ∃ v, N.IsDirPath u p v ∧ N.IsDirPath v q w := by
  induction p generalizing u with
  | nil => simp
  | cons e p ih =>
    simp only [List.cons_append, isDirPath_cons, ih]
    constructor
    · rintro ⟨rfl, v, h₁, h₂⟩
      exact ⟨v, ⟨rfl, h₁⟩, h₂⟩
    · rintro ⟨v, ⟨rfl, h₁⟩, h₂⟩
      exact ⟨rfl, v, h₁, h₂⟩

theorem IsDirPath.append (h₁ : N.IsDirPath u p v) (h₂ : N.IsDirPath v q w) :
    N.IsDirPath u (p ++ q) w :=
  isDirPath_append.mpr ⟨v, h₁, h₂⟩

theorem IsDirPath.snoc (h : N.IsDirPath u p (N.graph.source e)) :
    N.IsDirPath u (p ++ [e]) (N.graph.target e) :=
  h.append ⟨rfl, rfl⟩

theorem IsDirPath.reaches (h : N.IsDirPath u p v) : N.graph.Reaches u v := by
  induction p generalizing u with
  | nil =>
    obtain rfl : u = v := h
    exact .refl
  | cons e p ih =>
    obtain ⟨rfl, h⟩ := h
    exact .head ⟨e, rfl, rfl⟩ (ih h)

theorem exists_isDirPath (h : N.graph.Reaches u v) : ∃ p, N.IsDirPath u p v := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact ⟨[], rfl⟩
  | head hab _ ih =>
    obtain ⟨e, rfl, rfl⟩ := hab
    obtain ⟨p, hp⟩ := ih
    exact ⟨e :: p, rfl, hp⟩

theorem exists_isDirPath_of_avoidingReach (h : N.AvoidingReach e u v) :
    ∃ p, e ∉ p ∧ N.IsDirPath u p v := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact ⟨[], by simp, rfl⟩
  | head hab _ ih =>
    obtain ⟨g, hg, rfl, rfl⟩ := hab
    obtain ⟨p, hep, hp⟩ := ih
    refine ⟨g :: p, ?_, rfl, hp⟩
    simp only [List.mem_cons, not_or]
    exact ⟨hg.symm, hep⟩

theorem IsDirPath.split_of_mem (h : N.IsDirPath u p v) (hf : f ∈ p) :
    ∃ p₁ p₂, p = p₁ ++ f :: p₂ ∧ N.IsDirPath u p₁ (N.graph.source f) ∧
      N.IsDirPath (N.graph.target f) p₂ v := by
  obtain ⟨p₁, p₂, rfl⟩ := List.append_of_mem hf
  obtain ⟨m, h₁, rfl, h₂⟩ := isDirPath_append.mp h
  exact ⟨p₁, p₂, rfl, h₁, h₂⟩

theorem IsDirPath.split_of_mem_map (h : N.IsDirPath u p v) (hw : w ∈ p.map N.graph.target) :
    ∃ p₁ p₂, p = p₁ ++ p₂ ∧ p₁ ≠ [] ∧ w ∈ p₁.map N.graph.target ∧ N.IsDirPath u p₁ w ∧
      N.IsDirPath w p₂ v := by
  obtain ⟨f, hf, rfl⟩ := List.mem_map.mp hw
  obtain ⟨p₁, p₂, rfl, h₁, h₂⟩ := h.split_of_mem hf
  exact ⟨p₁ ++ [f], p₂, by simp, by simp, by simp, h₁.snoc, h₂⟩

theorem IsDirPath.split_of_mem_vertices (h : N.IsDirPath u p v)
    (hw : w ∈ u :: p.map N.graph.target) :
    ∃ p₁ p₂, p = p₁ ++ p₂ ∧ N.IsDirPath u p₁ w ∧ N.IsDirPath w p₂ v := by
  rcases List.mem_cons.mp hw with rfl | hw
  · exact ⟨[], p, rfl, rfl, h⟩
  · obtain ⟨p₁, p₂, rfl, -, -, h₁, h₂⟩ := h.split_of_mem_map hw
    exact ⟨p₁, p₂, rfl, h₁, h₂⟩

theorem IsDirPath.reaches_of_mem (h : N.IsDirPath u p v) (hf : f ∈ p) :
    N.graph.Reaches u (N.graph.source f) ∧ N.graph.Reaches (N.graph.target f) v := by
  obtain ⟨_, _, _, h₁, h₂⟩ := h.split_of_mem hf
  exact ⟨h₁.reaches, h₂.reaches⟩

theorem IsDirPath.reaches_of_mem_map (h : N.IsDirPath u p v) (hw : w ∈ p.map N.graph.target) :
    N.graph.Reaches u w ∧ N.graph.Reaches w v := by
  obtain ⟨_, _, _, _, _, h₁, h₂⟩ := h.split_of_mem_map hw
  exact ⟨h₁.reaches, h₂.reaches⟩

theorem IsDirPath.reaches_of_mem_vertices (h : N.IsDirPath u p v)
    (hw : w ∈ u :: p.map N.graph.target) : N.graph.Reaches u w ∧ N.graph.Reaches w v := by
  obtain ⟨_, _, _, h₁, h₂⟩ := h.split_of_mem_vertices hw
  exact ⟨h₁.reaches, h₂.reaches⟩

/-- The source of an arc on a path is among the vertices of the path. -/
theorem IsDirPath.source_mem_vertices (h : N.IsDirPath u p v) (hf : f ∈ p) :
    N.graph.source f ∈ u :: p.map N.graph.target := by
  induction p generalizing u with
  | nil => simp at hf
  | cons e p ih =>
    obtain ⟨rfl, h⟩ := h
    rcases List.mem_cons.mp hf with rfl | hf
    · simp
    · have := ih h hf
      simp only [List.map_cons]
      exact List.mem_cons_of_mem _ this

/-- The end of a path is among its vertices. -/
theorem IsDirPath.end_mem_vertices (h : N.IsDirPath u p v) : v ∈ u :: p.map N.graph.target := by
  induction p generalizing u with
  | nil =>
    obtain rfl : u = v := h
    simp
  | cons e p ih =>
    obtain ⟨rfl, h⟩ := h
    simp only [List.map_cons]
    exact List.mem_cons_of_mem _ (ih h)

/-- A vertex set no arc of the path crosses has both ends of the path on one side. -/
theorem IsDirPath.mem_iff {S : Set V} (h : N.IsDirPath u p v)
    (hS : ∀ f ∈ p, ¬ N.graph.Crosses f S) : u ∈ S ↔ v ∈ S := by
  induction p generalizing u with
  | nil => rw [show u = v from h]
  | cons e p ih =>
    obtain ⟨rfl, h⟩ := h
    have he := hS e (by simp)
    simp only [DirectedMultigraph.Crosses] at he
    have := ih h fun f hf => hS f (by simp [hf])
    tauto

section Acyclic

variable (hA : N.graph.IsAcyclic)
include hA

theorem IsDirPath.start_notMem (h : N.IsDirPath u p v) : u ∉ p.map N.graph.target := by
  intro hu
  obtain ⟨f, hf, rfl⟩ := List.mem_map.mp hu
  exact not_reaches_target_source hA f (h.reaches_of_mem hf).1

theorem IsDirPath.nodup (h : N.IsDirPath u p v) : (p.map N.graph.target).Nodup := by
  induction p generalizing u with
  | nil => simp
  | cons e p ih =>
    obtain ⟨rfl, h⟩ := h
    simp only [List.map_cons, List.nodup_cons]
    exact ⟨h.start_notMem hA, ih h⟩

/-- An arc with its source below the end of a path is not on it. -/
theorem IsDirPath.notMem_of_reaches_source (h : N.IsDirPath u p v)
    (he : N.graph.Reaches v (N.graph.source e)) : e ∉ p := fun hep =>
  not_reaches_target_source hA e ((h.reaches_of_mem hep).2.trans he)

/-- An arc with its target above the start of a path is not on it. -/
theorem IsDirPath.notMem_of_target_reaches (h : N.IsDirPath u p v)
    (he : N.graph.Reaches (N.graph.target e) u) : e ∉ p := fun hep =>
  not_reaches_target_source hA e (he.trans (h.reaches_of_mem hep).1)

theorem IsWedgePath.of_disjoint (hp : N.IsDirPath u p v) (hq : N.IsDirPath u q w)
    (hd : ∀ z ∈ p.map N.graph.target, z ∉ q.map N.graph.target) : N.IsWedgePath v w u p q := by
  refine ⟨hp, hq, ?_⟩
  rw [List.nodup_append]
  refine ⟨List.nodup_reverse.mpr (hp.nodup hA), ?_, ?_⟩
  · rw [List.nodup_cons]
    exact ⟨hq.start_notMem hA, hq.nodup hA⟩
  · intro a ha b hb hab
    subst hab
    rw [List.mem_reverse] at ha
    rcases List.mem_cons.mp hb with rfl | hb
    · exact hp.start_notMem hA ha
    · exact hd a ha hb

/-- **Every two vertices with a common ancestor are joined by a wedge path**: from two directed paths
with a common start, the wedge path rooted at the last vertex of the second path on the first. -/
theorem exists_isWedgePath_aux {r r' a b : V} {P Q : List E} (hP : N.IsDirPath r P a)
    (hQ : N.IsDirPath r' Q b) :
    (∀ z ∈ r' :: Q.map N.graph.target, z ∉ r :: P.map N.graph.target) ∨
      ∃ u P₁ P₂ Q₂, P = P₁ ++ P₂ ∧ N.IsDirPath r P₁ u ∧ Q₂ <:+ Q ∧ N.IsWedgePath a b u P₂ Q₂ := by
  induction Q generalizing r' with
  | nil =>
    obtain rfl : r' = b := hQ
    by_cases hb : r' ∈ r :: P.map N.graph.target
    · right
      obtain ⟨P₁, P₂, rfl, h₁, h₂⟩ := hP.split_of_mem_vertices hb
      exact ⟨r', P₁, P₂, [], rfl, h₁, List.suffix_refl _,
        IsWedgePath.of_disjoint hA h₂ rfl (by simp)⟩
    · left
      simpa using hb
  | cons g Q ih =>
    obtain ⟨rfl, hQ⟩ := hQ
    rcases ih hQ with hno | ⟨u, P₁, P₂, Q₂, rfl, h₁, hsuf, hw⟩
    · by_cases hb : N.graph.source g ∈ r :: P.map N.graph.target
      · right
        obtain ⟨P₁, P₂, rfl, h₁, h₂⟩ := hP.split_of_mem_vertices hb
        refine ⟨_, P₁, P₂, g :: Q, rfl, h₁, List.suffix_refl _,
          IsWedgePath.of_disjoint hA h₂ ⟨rfl, hQ⟩ fun z hz hz' => ?_⟩
        refine hno z (by simpa using hz') ?_
        simp only [List.map_append, List.mem_cons, List.mem_append] at hz ⊢
        exact Or.inr (Or.inr hz)
      · left
        intro z hz
        rcases List.mem_cons.mp hz with rfl | hz
        · exact hb
        · exact hno z hz
    · exact Or.inr ⟨u, P₁, P₂, Q₂, rfl, h₁, hsuf.trans (List.suffix_cons _ _), hw⟩

/-- A wedge path inside two directed paths with a common start. `P₁` is the part of the first path
above the summit. -/
theorem exists_isWedgePath {r a b : V} {P Q : List E} (hP : N.IsDirPath r P a)
    (hQ : N.IsDirPath r Q b) :
    ∃ u P₁ P₂ Q₂, P = P₁ ++ P₂ ∧ N.IsDirPath r P₁ u ∧ Q₂ <:+ Q ∧ N.IsWedgePath a b u P₂ Q₂ := by
  rcases exists_isWedgePath_aux hA hP hQ with hno | h
  · exact absurd (List.mem_cons_self) (hno r List.mem_cons_self)
  · exact h

end Acyclic

theorem IsWedgePath.disjoint {u' : V} (h : N.IsWedgePath v w u' p q) {z : V}
    (hp : z ∈ p.map N.graph.target) (hq : z ∈ q.map N.graph.target) : False := by
  have := h.distinct
  rw [List.nodup_append] at this
  exact this.2.2 z (List.mem_reverse.mpr hp) z (List.mem_cons_of_mem _ hq) rfl

theorem IsWedgePath.mem_iff {S : Set V} {u' : V} (h : N.IsWedgePath v w u' p q)
    (hS : ∀ f, f ∈ p ∨ f ∈ q → ¬ N.graph.Crosses f S) : v ∈ S ↔ w ∈ S :=
  (h.left.mem_iff fun f hf => hS f (Or.inl hf)).symm.trans
    (h.right.mem_iff fun f hf => hS f (Or.inr hf))

end Paths

/-! ### The subnetwork on `Y` -/

section Subnetwork

variable {Y A : Set X} {e : E}

/-- Two taxa are joined by a wedge path. -/
theorem exists_isWedgePath_leaf (hN : N.IsPhylogenetic) (x y : X) :
    ∃ u p q, N.IsWedgePath (N.leaf x) (N.leaf y) u p q := by
  obtain ⟨P, hP⟩ := exists_isDirPath (hN.root_reaches (N.leaf x))
  obtain ⟨Q, hQ⟩ := exists_isDirPath (hN.root_reaches (N.leaf y))
  obtain ⟨u, _, P₂, Q₂, _, _, _, hw⟩ := exists_isWedgePath hN.acyclic hP hQ
  exact ⟨u, P₂, Q₂, hw⟩

/-- The arcs of the subnetwork on `Y` are ancestral to `Y`. -/
theorem wedgeArcs_subset_ancestralArcs : N.wedgeArcs Y ⊆ N.ancestralArcs Y := by
  rintro e ⟨x, hx, y, hy, -, u, p, q, hw, he | he⟩
  · exact ⟨x, hx, (hw.left.reaches_of_mem he).2⟩
  · exact ⟨y, hy, (hw.right.reaches_of_mem he).2⟩

/-- A path whose vertices avoid `l`, when `l` does not reach its end. -/
theorem avoiding_of_not_reaches {l a b : V} (h : N.graph.Reaches a b)
    (hl : ¬ N.graph.Reaches l b) :
    Relation.ReflTransGen (fun c d => N.graph.Adj c d ∧ c ≠ l ∧ d ≠ l) a b := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact .refl
  | @head c d hcd hdb ih =>
    refine .head ⟨hcd, ?_, ?_⟩ ih
    · rintro rfl
      exact hl (hdb.head hcd)
    · rintro rfl
      exact hl hdb

/-- A directed path whose vertices avoid `l`. -/
theorem IsDirPath.avoiding {l a b : V} {p : List E} (h : N.IsDirPath a p b) (ha : a ≠ l)
    (hl : l ∉ p.map N.graph.target) :
    Relation.ReflTransGen (fun c d => N.graph.Adj c d ∧ c ≠ l ∧ d ≠ l) a b := by
  induction p generalizing a with
  | nil =>
    obtain rfl : a = b := h
    exact .refl
  | cons g p ih =>
    obtain ⟨rfl, h⟩ := h
    simp only [List.map_cons, List.mem_cons, not_or] at hl
    exact .head ⟨⟨g, rfl, rfl⟩, ha, Ne.symm hl.1⟩ (ih h (Ne.symm hl.1) hl.2)

/-- **The summit of a wedge path between taxa of `Y` lies below every stable ancestor of `Y`**: a path
from the root to the summit that avoids a stable ancestor would meet it on both legs. -/
theorem IsWedgePath.reaches_summit (hN : N.IsPhylogenetic) {l u : V} {p q : List E} {x y : X}
    (hl : N.IsStableAncestor Y l) (hx : x ∈ Y) (hy : y ∈ Y)
    (hw : N.IsWedgePath (N.leaf x) (N.leaf y) u p q) : N.graph.Reaches l u := by
  by_contra hlu
  have hul : u ≠ l := fun h => hlu (h ▸ .refl)
  have hrl : N.root ≠ l := fun h => hlu (h ▸ hN.root_reaches u)
  have hroot := avoiding_of_not_reaches (hN.root_reaches u) hlu
  have key : ∀ {t : X} {r : List E}, t ∈ Y → N.IsDirPath u r (N.leaf t) →
      l ∈ r.map N.graph.target := by
    intro t r ht hr
    by_contra hno
    refine hl t ht ⟨hrl, ?_, hroot.trans (hr.avoiding hul hno)⟩
    intro htl
    rcases List.mem_cons.mp hr.end_mem_vertices with h | h
    · exact hul (h.symm.trans htl)
    · exact hno (htl ▸ h)
  exact hw.disjoint (key hx hw.left) (key hy hw.right)

/-- **The subnetwork on `Y` lies below every stable ancestor of `Y`**, so below the least stable
ancestor: it does not see the part of the rooted network `N⁺` that the semi-directed network `N⁻` drops.
So it is contained in the arcs of `lsaNetwork`. For at least two taxa the two sets are equal, by a Menger
argument that this file does not need and does not formalize. -/
theorem wedgeArcs_subset_belowArcs (hN : N.IsPhylogenetic) {l : V} (hl : N.IsStableAncestor Y l) :
    N.wedgeArcs Y ⊆ N.belowArcs l Y := by
  intro e he
  refine ⟨?_, wedgeArcs_subset_ancestralArcs he⟩
  obtain ⟨x, hx, y, hy, -, u, p, q, hw, hep | heq⟩ := he
  · exact (hw.reaches_summit hN hl hx hy).trans (hw.left.reaches_of_mem hep).1
  · exact (hw.reaches_summit hN hl hx hy).trans (hw.right.reaches_of_mem heq).1

/-- A cut of the induced subgraph is one of the subnetwork. -/
theorem HasCutSplitOn.hasWedgeCutSplit (hN : N.IsPhylogenetic) (h₁ : (Y ∩ A).Nonempty)
    (h₂ : (Y \ A).Nonempty) (h : N.HasCutSplitOn Y A) : N.HasWedgeCutSplit Y A := by
  obtain ⟨e, -, S, hS, hA⟩ := h
  have hS' : ∀ f ∈ N.wedgeArcs Y, N.graph.Crosses f S ↔ f = e :=
    fun f hf => hS f (wedgeArcs_subset_ancestralArcs hf)
  refine ⟨e, ?_, S, hS', hA⟩
  obtain ⟨x, hx, hxA⟩ := h₁
  obtain ⟨y, hy, hyA⟩ := h₂
  obtain ⟨u, p, q, hw⟩ := exists_isWedgePath_leaf hN x y
  have hxy : x ≠ y := fun h => hyA (h ▸ hxA)
  by_contra hne
  have hmem : ∀ f, f ∈ p ∨ f ∈ q → ¬ N.graph.Crosses f S := by
    intro f hf hc
    have hfW : f ∈ N.wedgeArcs Y := ⟨x, hx, y, hy, hxy, u, p, q, hw, hf⟩
    have := (hS' f hfW).mp hc
    subst this
    exact hne hfW
  exact hyA ((hA y hy).mp ((hw.mem_iff hmem).mp ((hA x hx).mpr hxA)))

/-- A cut edge of the subnetwork separates. Let `T` be the side of its target. A wedge path between the two
sides of `T` uses the edge. So the taxa of `Y` in `T` are below it, on the leg that uses it. The other taxa
of `Y` are not below it, as a wedge path below the edge does not use it. The taxa in `T` are dominated: a path
to one of them avoiding the edge, with a path to the other side, gives a wedge path that uses the edge on its
other leg. -/
theorem separates_of_wedgeCut (hN : N.IsPhylogenetic) {T : Set V}
    (hS : ∀ f ∈ N.wedgeArcs Y, N.graph.Crosses f T ↔ f = e) (ht : N.graph.target e ∈ T)
    (hs : N.graph.source e ∉ T) {P Q : Set X} (hP : ∀ x ∈ P, x ∈ Y ∧ N.leaf x ∈ T)
    (hQ : ∀ x ∈ Q, x ∈ Y ∧ N.leaf x ∉ T) (hP₀ : P.Nonempty) (hQ₀ : Q.Nonempty) :
    N.Separates e P Q := by
  have hA := hN.acyclic
  -- a wedge path between the two sides of `T` uses `e`
  have huses : ∀ {x y : X} {u : V} {p q : List E}, x ∈ Y → N.leaf x ∈ T → y ∈ Y → N.leaf y ∉ T →
      N.IsWedgePath (N.leaf x) (N.leaf y) u p q → e ∈ p ∨ e ∈ q := by
    intro x y u p q hx hxT hy hyT hw
    by_contra hne
    have hxy : x ≠ y := fun h => hyT (h ▸ hxT)
    have hmem : ∀ f, f ∈ p ∨ f ∈ q → ¬ N.graph.Crosses f T := by
      intro f hf hc
      have := (hS f ⟨x, hx, y, hy, hxy, u, p, q, hw, hf⟩).mp hc
      subst this
      exact hne hf
    exact hyT ((hw.mem_iff hmem).mp hxT)
  -- the taxa of `T` are below `e`
  have hbelow : ∀ x ∈ P, N.IsBelow e x := by
    intro x hx
    obtain ⟨y, hy⟩ := hQ₀
    obtain ⟨hxY, hxT⟩ := hP x hx
    obtain ⟨hyY, hyT⟩ := hQ y hy
    obtain ⟨u, p, q, hw⟩ := exists_isWedgePath_leaf hN x y
    have hxy : x ≠ y := fun h => hyT (h ▸ hxT)
    rcases huses hxY hxT hyY hyT hw with hep | heq
    · exact (hw.left.reaches_of_mem hep).2
    · -- `e` is not on the leg to `y`: the rest of that leg would leave `T` by another arc
      exfalso
      obtain ⟨q₁, q₂, rfl, -, hq₂⟩ := hw.right.split_of_mem heq
      have hrest := hq₂.notMem_of_target_reaches hA (e := e) .refl
      have hno : ∀ f ∈ q₂, ¬ N.graph.Crosses f T := by
        intro f hf hc
        have := (hS f ⟨x, hxY, y, hyY, hxy, u, p, _, hw, Or.inr (by simp [hf])⟩).mp hc
        subst this
        exact hrest hf
      exact hyT ((hq₂.mem_iff hno).mp ht)
  -- the taxa outside `T` are not below `e`
  have hnot : ∀ y ∈ Q, ¬ N.IsBelow e y := by
    intro y hy hbe
    obtain ⟨x, hx⟩ := hP₀
    obtain ⟨hxY, hxT⟩ := hP x hx
    obtain ⟨hyY, hyT⟩ := hQ y hy
    obtain ⟨P', hP'⟩ := exists_isDirPath (hbelow x hx)
    obtain ⟨Q', hQ'⟩ := exists_isDirPath hbe
    obtain ⟨u, P₁, P₂, Q₂, rfl, -, hsuf, hw⟩ := exists_isWedgePath hA hP' hQ'
    rcases huses hxY hxT hyY hyT hw with hep | heq
    · exact hP'.notMem_of_target_reaches hA .refl (by simp [hep])
    · exact hQ'.notMem_of_target_reaches hA .refl (hsuf.subset heq)
  refine ⟨fun x hx hav => ?_, hnot⟩
  -- the taxa of `T` are dominated by `e`
  obtain ⟨y, hy⟩ := hQ₀
  obtain ⟨hxY, hxT⟩ := hP x hx
  obtain ⟨hyY, hyT⟩ := hQ y hy
  obtain ⟨R, heR, hR⟩ := exists_isDirPath_of_avoidingReach hav
  obtain ⟨Q', hQ'⟩ := exists_isDirPath (hN.root_reaches (N.leaf y))
  obtain ⟨u, P₁, P₂, Q₂, rfl, -, hsuf, hw⟩ := exists_isWedgePath hA hR hQ'
  rcases huses hxY hxT hyY hyT hw with hep | heq
  · exact heR (by simp [hep])
  · exact hnot y hy (hQ'.reaches_of_mem (hsuf.subset heq)).2

/-- A cut edge of the subnetwork is one of the induced subgraph. -/
theorem HasWedgeCutSplit.hasCutSplitOn (hN : N.IsPhylogenetic) (h₁ : (Y ∩ A).Nonempty)
    (h₂ : (Y \ A).Nonempty) (h : N.HasWedgeCutSplit Y A) : N.HasCutSplitOn Y A := by
  obtain ⟨e, -, S, hS, hA⟩ := h
  rw [hasCutSplitOn_iff_separates hN]
  refine ⟨e, ?_⟩
  have he : N.graph.Crosses e S := by
    obtain ⟨x, hx, hxA⟩ := h₁
    obtain ⟨y, hy, hyA⟩ := h₂
    obtain ⟨u, p, q, hw⟩ := exists_isWedgePath_leaf hN x y
    have hxy : x ≠ y := fun h => hyA (h ▸ hxA)
    by_contra hne
    have hmem : ∀ f, f ∈ p ∨ f ∈ q → ¬ N.graph.Crosses f S := by
      intro f hf hc
      have := (hS f ⟨x, hx, y, hy, hxy, u, p, q, hw, hf⟩).mp hc
      subst this
      exact hne hc
    exact hyA ((hA y hy).mp ((hw.mem_iff hmem).mp ((hA x hx).mpr hxA)))
  rcases he with ⟨hs, ht⟩ | ⟨ht, hs⟩
  · refine Or.inr ⟨h₂, separates_of_wedgeCut hN (T := Sᶜ)
      (fun f hf => ((N.graph.crosses_compl f S)).trans (hS f hf)) ht (not_not.mpr hs) ?_ ?_ h₂ h₁⟩
    · exact fun x hx => ⟨hx.1, fun hc => hx.2 ((hA x hx.1).mp hc)⟩
    · exact fun x hx => ⟨hx.1, not_not.mpr ((hA x hx.1).mpr hx.2)⟩
  · refine Or.inl ⟨h₁, separates_of_wedgeCut hN hS ht hs ?_ ?_ h₁ h₂⟩
    · exact fun x hx => ⟨hx.1, (hA x hx.1).mpr hx.2⟩
    · exact fun x hx => ⟨hx.1, fun hc => hx.2 ((hA x hx.1).mp hc)⟩

/-- **The representation bridge.** For a split of `Y` with both sides nonempty, in particular a `2|2`
split of four taxa: a cut edge of the subnetwork on `Y`, the union of the wedge paths between taxa of `Y`,
induces the split exactly when `HasCutSplitOn Y A` holds on the induced subgraph, which keeps everything
ancestral to `Y`. Neither direction needs the network to be binary or level-1. -/
theorem hasWedgeCutSplit_iff_hasCutSplitOn (hN : N.IsPhylogenetic) (h₁ : (Y ∩ A).Nonempty)
    (h₂ : (Y \ A).Nonempty) : N.HasWedgeCutSplit Y A ↔ N.HasCutSplitOn Y A :=
  ⟨HasWedgeCutSplit.hasCutSplitOn hN h₁ h₂, HasCutSplitOn.hasWedgeCutSplit hN h₁ h₂⟩

/-- The bridge to the network induced on `Y`, with what lies above the LSA removed and degree-two
vertices suppressed (`inducedNetwork`). -/
theorem hasWedgeCutSplit_iff_inducedNetwork_hasCutSplit (hN : N.IsPhylogenetic) (hY : Y.Nontrivial)
    (h₁ : (Y ∩ A).Nonempty) (h₂ : (Y \ A).Nonempty) :
    N.HasWedgeCutSplit Y A ↔ (inducedNetwork hN Y hY).HasCutSplit (Subtype.val ⁻¹' A) :=
  (hasWedgeCutSplit_iff_hasCutSplitOn hN h₁ h₂).trans
    (hasCutSplitOn_iff_inducedNetwork_hasCutSplit hN hY h₁ h₂)

end Subnetwork

end Phylogenetics.RootedNetwork

namespace TOBQMC.Level1

variable {V E X : Type*} {N : RootedNetwork V E X}

/-! ### Level-1 blobs are cycles -/

section Blob

variable {v h : V}

/-- A vertex on a directed path between two vertices of a blob is in the blob. -/
theorem sameBlob_of_reaches_of_reaches (hN : N.IsPhylogenetic) {a w c : V} (ha : SameBlob N v a)
    (hc : SameBlob N v c) (haw : N.graph.Reaches a w) (hwc : N.graph.Reaches w c) :
    SameBlob N v w := by
  induction haw using Relation.ReflTransGen.head_induction_on with
  | refl => exact ha
  | @head a b hab hbw ih =>
    obtain ⟨f, rfl, rfl⟩ := hab
    have hnb : ¬ IsBridge N f := fun hf =>
      not_sameBlob_of_reaches_exit hN hf ha (hbw.trans hwc) hc
    exact ih (sameBlob_trans ha (sameBlob_of_not_isBridge hnb))

/-- An arc with both ends in a blob is not a bridge. -/
theorem not_isBridge_of_sameBlob (hN : N.IsPhylogenetic) {f : E}
    (hs : SameBlob N v (N.graph.source f)) (ht : SameBlob N v (N.graph.target f)) :
    ¬ IsBridge N f :=
  fun hf => not_sameBlob_of_reaches_exit hN hf hs .refl ht

/-- A directed path from outside a blob into it goes through the top of the blob, since it enters by a
bridge, which has the whole blob below it. -/
theorem top_mem_of_outside (hN : N.IsPhylogenetic) {T u a : V} {p : List E} (hT : SameBlob N v T)
    (hTall : ∀ u, SameBlob N v u → N.graph.Reaches T u) (hu : ¬ SameBlob N v u)
    (ha : SameBlob N v a) (hp : N.IsDirPath u p a) : T ∈ p.map N.graph.target := by
  induction p generalizing u with
  | nil =>
    obtain rfl : u = a := hp
    exact absurd ha hu
  | cons e p ih =>
    obtain ⟨rfl, hp⟩ := hp
    by_cases ht : SameBlob N v (N.graph.target e)
    · have heb : IsBridge N e := by
        by_contra hnb
        exact hu (sameBlob_trans ht (sameBlob_symm (sameBlob_of_not_isBridge hnb)))
      have h₁ := reaches_of_sameBlob hN heb (sameBlob_trans (sameBlob_symm ht) hT)
      have := eq_of_reaches_of_reaches hN.acyclic h₁ (hTall _ ht)
      simp [this]
    · simp only [List.map_cons]
      exact List.mem_cons_of_mem _ (ih ht hp)

/-- A wedge path between two vertices of a blob has its summit in the blob: otherwise both legs would
go through the top of the blob. -/
theorem _root_.Phylogenetics.RootedNetwork.IsWedgePath.summit_sameBlob (hN : N.IsPhylogenetic)
    {a b u : V} {p q : List E} (hw : N.IsWedgePath a b u p q) (ha : SameBlob N v a) (hb : SameBlob N v b) :
    SameBlob N v u := by
  by_contra hu
  obtain ⟨T, hT, hTall⟩ := exists_top hN v
  exact hw.disjoint (top_mem_of_outside hN hT hTall hu ha hw.left)
    (top_mem_of_outside hN hT hTall hu hb hw.right)

/-- A wedge path between two vertices of a blob stays in the blob. -/
theorem _root_.Phylogenetics.RootedNetwork.IsWedgePath.sameBlob_of_mem (hN : N.IsPhylogenetic)
    {a b u z : V} {p q : List E} (hw : N.IsWedgePath a b u p q) (ha : SameBlob N v a) (hb : SameBlob N v b)
    (hz : z ∈ u :: (p.map N.graph.target ++ q.map N.graph.target)) : SameBlob N v z := by
  have hu := hw.summit_sameBlob hN ha hb
  rcases List.mem_cons.mp hz with rfl | hz
  · exact hu
  · rcases List.mem_append.mp hz with hz | hz
    · have := hw.left.reaches_of_mem_map hz
      exact sameBlob_of_reaches_of_reaches hN hu ha this.1 this.2
    · have := hw.right.reaches_of_mem_map hz
      exact sameBlob_of_reaches_of_reaches hN hu hb this.1 this.2

/-- A wedge path contains at most one arc into a vertex. This is the reason the paper gives for
`wedgePath_unique`: the other path between two vertices of the cycle crosses `p₁, v_h, p₂`, along the two
reticulation arcs, so it is not wedge. -/
theorem _root_.Phylogenetics.RootedNetwork.IsWedgePath.eq_of_target_eq (hN : N.IsPhylogenetic)
    {a b u : V} {p q : List E} {k₁ k₂ : E} (hw : N.IsWedgePath a b u p q) (h₁ : k₁ ∈ p ∨ k₁ ∈ q) (h₂ : k₂ ∈ p ∨ k₂ ∈ q)
    (ht : N.graph.target k₁ = N.graph.target k₂) : k₁ = k₂ := by
  have key : ∀ {r : List E} {c : V}, N.IsDirPath u r c → k₁ ∈ r → k₂ ∈ r → k₁ = k₂ := by
    intro r c hr hk₁ hk₂
    exact List.inj_on_of_nodup_map (hr.nodup hN.acyclic) hk₁ hk₂ ht
  rcases h₁ with h₁ | h₁ <;> rcases h₂ with h₂ | h₂
  · exact key hw.left h₁ h₂
  · exact (hw.disjoint (List.mem_map_of_mem h₁) (ht ▸ List.mem_map_of_mem h₂)).elim
  · exact (hw.disjoint (ht ▸ List.mem_map_of_mem h₂) (List.mem_map_of_mem h₁)).elim
  · exact key hw.right h₁ h₂

/-- The vertices of a directed path are comparable. -/
theorem _root_.Phylogenetics.RootedNetwork.IsDirPath.total {u c w w' : V} {p : List E}
    (hp : N.IsDirPath u p c) (hw : w ∈ u :: p.map N.graph.target) (hw' : w' ∈ u :: p.map N.graph.target) :
    N.graph.Reaches w w' ∨ N.graph.Reaches w' w := by
  induction p generalizing u with
  | nil =>
    simp only [List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hw hw'
    subst hw hw'
    exact Or.inl .refl
  | cons e p ih =>
    obtain ⟨rfl, hp'⟩ := hp
    rcases List.mem_cons.mp hw with rfl | hw₁
    · exact Or.inl ((isDirPath_cons.mpr ⟨rfl, hp'⟩).reaches_of_mem_vertices hw').1
    · rcases List.mem_cons.mp hw' with rfl | hw₁'
      · exact Or.inr ((isDirPath_cons.mpr ⟨rfl, hp'⟩).reaches_of_mem_vertices hw).1
      · exact ih hp' hw₁ hw₁'

variable [Fintype V] [Fintype E]

/-- The arc into a vertex of the blob other than the reticulation is unique. -/
theorem arc_eq_of_target_eq (hN : N.IsPhylogenetic) (hLevel : IsLevelOne N)
    (hh : SameBlob N v h) (hh₂ : 2 ≤ N.graph.indegree h) {u : V} (hu : SameBlob N v u)
    (huh : u ≠ h) {f g : E} (hf : N.graph.target f = u) (hg : N.graph.target g = u) : f = g := by
  by_contra hne
  have := two_le_indegree_of_ne hN hne (hf.trans hg.symm)
  rw [hf] at this
  exact huh (reticulation_unique hN hLevel hu this hh hh₂)

/-- **A directed path inside a blob, to a vertex other than the reticulation, is unique**: going up from
the end, each vertex has only one arc into it. -/
theorem isDirPath_unique (hN : N.IsPhylogenetic) (hLevel : IsLevelOne N)
    (hh : SameBlob N v h) (hh₂ : 2 ≤ N.graph.indegree h) {a b : V} {p p' : List E}
    (ha : SameBlob N v a) (hb : SameBlob N v b) (hbh : b ≠ h) (hp : N.IsDirPath a p b)
    (hp' : N.IsDirPath a p' b) : p = p' := by
  have hA := hN.acyclic
  induction p using List.reverseRecOn generalizing b p' with
  | nil =>
    obtain rfl : a = b := hp
    rcases List.eq_nil_or_concat' p' with rfl | ⟨L, g, rfl⟩
    · rfl
    · obtain ⟨m, _, rfl, rfl⟩ := isDirPath_append.mp hp'
      exact absurd ((hp'.start_notMem hA)) (by simp)
  | append_singleton P g ih =>
    obtain ⟨m, hP, rfl, rfl⟩ := isDirPath_append.mp hp
    rcases List.eq_nil_or_concat' p' with rfl | ⟨L, g', rfl⟩
    · exact absurd (hp.start_notMem hA) (by simp [show a = _ from hp'])
    · obtain ⟨m', hL, rfl, hm'⟩ := isDirPath_append.mp hp'
      have hgg : g = g' := arc_eq_of_target_eq hN hLevel hh hh₂ hb hbh rfl hm'
      subst hgg
      have hs : SameBlob N v (N.graph.source g) :=
        sameBlob_of_reaches_of_reaches hN ha hb hP.reaches (reaches_of_arc N g)
      have hsh : N.graph.source g ≠ h := by
        intro hsh
        exact not_reaches_source hN g (hsh ▸ reaches_reticulation hN hLevel hh hh₂ hb)
      rw [ih hs hsh hP hL]

/-- **Only one wedge path between two vertices of a level-1 blob other than the reticulation** (TOB-QMC,
proof of Lemma 4, lines 551–554 of v5). The other path between them around the cycle uses both
reticulation arcs, so it is not wedge (`IsWedgePath.eq_of_target_eq`). Formally: the summits are in the
blob and comparable, a summit strictly above another would have the lower one on both of its legs,
and the legs are unique by `isDirPath_unique`. -/
theorem wedgePath_unique (hN : N.IsPhylogenetic) (hLevel : IsLevelOne N)
    (hh : SameBlob N v h) (hh₂ : 2 ≤ N.graph.indegree h) {a b u u' : V} {p q p' q' : List E}
    (ha : SameBlob N v a) (hb : SameBlob N v b) (hah : a ≠ h) (hbh : b ≠ h)
    (hw : N.IsWedgePath a b u p q) (hw' : N.IsWedgePath a b u' p' q') :
    u = u' ∧ p = p' ∧ q = q' := by
  have hu := hw.summit_sameBlob hN ha hb
  have hu' := hw'.summit_sameBlob hN ha hb
  -- a summit above another is the other
  have key : ∀ {u u' : V} {p q p' q' : List E}, SameBlob N v u → SameBlob N v u' →
      N.IsWedgePath a b u p q → N.IsWedgePath a b u' p' q' → N.graph.Reaches u u' → u = u' := by
    intro u u' p q p' q' hu hu' hw hw' hr
    by_contra hne
    obtain ⟨A, hA⟩ := exists_isDirPath hr
    have hmem : u' ∈ A.map N.graph.target := by
      rcases List.mem_cons.mp hA.end_mem_vertices with h' | h'
      · exact absurd h'.symm hne
      · exact h'
    have h₁ : p = A ++ p' := isDirPath_unique hN hLevel hh hh₂ hu ha hah hw.left (hA.append hw'.left)
    have h₂ : q = A ++ q' := isDirPath_unique hN hLevel hh hh₂ hu hb hbh hw.right (hA.append hw'.right)
    exact hw.disjoint (z := u') (by rw [h₁, List.map_append]; exact List.mem_append_left _ hmem)
      (by rw [h₂, List.map_append]; exact List.mem_append_left _ hmem)
  obtain ⟨T, hT, hTall⟩ := exists_top hN v
  obtain ⟨A, hA⟩ := exists_isDirPath (hTall u hu)
  obtain ⟨A', hA'⟩ := exists_isDirPath (hTall u' hu')
  have hL : A ++ p = A' ++ p' :=
    isDirPath_unique hN hLevel hh hh₂ hT ha hah (hA.append hw.left) (hA'.append hw'.left)
  have hP := hA.append hw.left
  have hmem : u ∈ T :: (A ++ p).map N.graph.target := by
    have := hA.end_mem_vertices
    simp only [List.map_append, List.mem_cons, List.mem_append] at this ⊢
    tauto
  have hmem' : u' ∈ T :: (A ++ p).map N.graph.target := by
    rw [hL]
    have := hA'.end_mem_vertices
    simp only [List.map_append, List.mem_cons, List.mem_append] at this ⊢
    tauto
  have huu : u = u' := by
    rcases hP.total hmem hmem' with h' | h'
    · exact key hu hu' hw hw' h'
    · exact (key hu' hu hw' hw h').symm
  subst huu
  exact ⟨rfl, isDirPath_unique hN hLevel hh hh₂ hu ha hah hw.left hw'.left,
    isDirPath_unique hN hLevel hh hh₂ hu hb hbh hw.right hw'.right⟩

/-- **A level-1 blob of a binary network is a cycle**: two directed paths from its top `T` to its
reticulation `h`, sharing only their ends, `pL` then the reticulation arc `k₁`, and `pR` then `k₂`. The arcs
`k₁, k₂` are the paper's `(p₁, v_h)` and `(p₂, v_h)`. -/
structure BlobCycle (N : RootedNetwork V E X) (v h T : V) (k₁ k₂ : E) (pL pR : List E) : Prop where
  reticulation : SameBlob N v h
  top : SameBlob N v T
  top_reaches : ∀ u, SameBlob N v u → N.graph.Reaches T u
  ne : k₁ ≠ k₂
  target₁ : N.graph.target k₁ = h
  target₂ : N.graph.target k₂ = h
  arcs : ∀ f, N.graph.target f = h → f = k₁ ∨ f = k₂
  left : N.IsDirPath T pL (N.graph.source k₁)
  right : N.IsDirPath T pR (N.graph.source k₂)
  disjoint : ∀ w ∈ pL.map N.graph.target, w ∉ pR.map N.graph.target

/-- **The two sides of a level-1 blob share only the top**: an arc of the blob with both reticulation
arcs below it would have nothing else entering what is below it, so it would be a bridge. -/
theorem exists_blobCycle (hN : N.IsPhylogenetic) (hBin : N.IsBinary) (hLevel : IsLevelOne N)
    (hh : SameBlob N v h) (hh₂ : 2 ≤ N.graph.indegree h) :
    ∃ T k₁ k₂ pL pR, BlobCycle N v h T k₁ k₂ pL pR := by
  obtain ⟨T, hT, hTall⟩ := exists_top hN v
  have hin : N.graph.indegree h = 2 := by
    have h1 := outdegree_eq_one_of_reticulation hN hBin hh₂
    have h2 := hBin.2 h (reticulation_ne_root hN hh₂) (by omega)
    omega
  obtain ⟨k₁, k₂, hne, hset⟩ := Set.ncard_eq_two.mp hin
  have harcs : ∀ f, N.graph.target f = h ↔ f = k₁ ∨ f = k₂ := fun f => by
    have : f ∈ {e | N.graph.target e = h} ↔ f ∈ ({k₁, k₂} : Set E) := by rw [hset]
    simpa using this
  have hk₁ : N.graph.target k₁ = h := (harcs k₁).mpr (Or.inl rfl)
  have hk₂ : N.graph.target k₂ = h := (harcs k₂).mpr (Or.inr rfl)
  have hsrc : ∀ {k : E}, N.graph.target k = h → SameBlob N v (N.graph.source k) := by
    intro k hk
    have hnb := not_isBridge_of_two_le_indegree hN (e := k) (by rw [hk]; exact hh₂)
    have := sameBlob_of_not_isBridge hnb
    rw [hk] at this
    exact sameBlob_trans hh (sameBlob_symm this)
  have hs₁ := hsrc hk₁
  obtain ⟨pL, hpL⟩ := exists_isDirPath (hTall _ hs₁)
  obtain ⟨pR, hpR⟩ := exists_isDirPath (hTall _ (hsrc hk₂))
  refine ⟨T, k₁, k₂, pL, pR, ⟨hh, hT, hTall, hne, hk₁, hk₂, fun f => (harcs f).mp, hpL, hpR, ?_⟩⟩
  intro w hw hw'
  obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hw
  have hrL := hpL.reaches_of_mem hg
  have hrR := hpR.reaches_of_mem_map hw'
  have hsg := sameBlob_of_reaches_of_reaches hN hT hs₁ hrL.1 ((reaches_of_arc N g).trans hrL.2)
  have htg := sameBlob_of_reaches_of_reaches hN hT hs₁ (hrL.1.tail ⟨g, rfl, rfl⟩) hrL.2
  refine not_isBridge_of_sameBlob hN hsg htg ?_
  rw [isBridge_iff_reaches hN]
  intro f hfg hR
  by_contra hnot
  have hfh := target_eq_reticulation hN hLevel hh hh₂ htg hfg hR hnot
  rcases (harcs f).mp hfh with rfl | rfl
  · exact hnot hrL.2
  · exact hnot hrR.2

namespace BlobCycle

variable {T : V} {k₁ k₂ : E} {pL pR : List E}

omit [Fintype V] [Fintype E] in
theorem swap (C : BlobCycle N v h T k₁ k₂ pL pR) : BlobCycle N v h T k₂ k₁ pR pL :=
  ⟨C.reticulation, C.top, C.top_reaches, C.ne.symm, C.target₂, C.target₁,
    fun f hf => (C.arcs f hf).symm, C.right, C.left, fun w hw hw' => C.disjoint w hw' hw⟩

omit [Fintype V] [Fintype E] in
theorem source₁_sameBlob (hN : N.IsPhylogenetic) (C : BlobCycle N v h T k₁ k₂ pL pR) :
    SameBlob N v (N.graph.source k₁) := by
  have hnb := not_isBridge_of_two_le_indegree hN (e := k₁)
    (two_le_indegree_of_ne hN C.ne (C.target₁.trans C.target₂.symm))
  have := sameBlob_of_not_isBridge hnb
  rw [C.target₁] at this
  exact sameBlob_trans C.reticulation (sameBlob_symm this)

omit [Fintype V] [Fintype E] in
theorem source₁_ne (hN : N.IsPhylogenetic) (C : BlobCycle N v h T k₁ k₂ pL pR) :
    N.graph.source k₁ ≠ h := fun hc => target_ne_source hN k₁ (C.target₁.trans hc.symm)

omit [Fintype V] [Fintype E] in
theorem not_reaches_of_target₁ (hN : N.IsPhylogenetic) (C : BlobCycle N v h T k₁ k₂ pL pR) :
    ¬ N.graph.Reaches h (N.graph.source k₁) := fun hc =>
  not_reaches_source hN k₁ (C.target₁ ▸ hc)

omit [Fintype V] [Fintype E] in
theorem top_ne (hN : N.IsPhylogenetic) (C : BlobCycle N v h T k₁ k₂ pL pR) : T ≠ h := fun hc =>
  C.not_reaches_of_target₁ hN (hc ▸ C.left.reaches)

omit [Fintype V] [Fintype E] in
/-- `h` is not on the sides of the cycle. -/
theorem reticulation_notMem_left (hN : N.IsPhylogenetic) (C : BlobCycle N v h T k₁ k₂ pL pR) :
    h ∉ pL.map N.graph.target := fun hc =>
  C.not_reaches_of_target₁ hN (C.left.reaches_of_mem_map hc).2

/-- A vertex of the blob reaching `p₁` is on the side of `p₁`. -/
theorem mem_left_of_reaches (hN : N.IsPhylogenetic) (hLevel : IsLevelOne N)
    (hh₂ : 2 ≤ N.graph.indegree h) (C : BlobCycle N v h T k₁ k₂ pL pR) {u : V}
    (hu : SameBlob N v u) (hr : N.graph.Reaches u (N.graph.source k₁)) :
    u ∈ T :: pL.map N.graph.target := by
  obtain ⟨A, hA⟩ := exists_isDirPath (C.top_reaches u hu)
  obtain ⟨B, hB⟩ := exists_isDirPath hr
  have heq : pL = A ++ B := isDirPath_unique hN hLevel C.reticulation hh₂ C.top
    (C.source₁_sameBlob hN) (C.source₁_ne hN) C.left (hA.append hB)
  have := hA.end_mem_vertices
  simp only [heq, List.map_append, List.mem_cons, List.mem_append] at this ⊢
  tauto

/-- A vertex of the blob other than `h` is above one of the two parents of `h`. -/
theorem reaches_source (hN : N.IsPhylogenetic) (hLevel : IsLevelOne N)
    (hh₂ : 2 ≤ N.graph.indegree h) (C : BlobCycle N v h T k₁ k₂ pL pR) {u : V}
    (hu : SameBlob N v u) (huh : u ≠ h) :
    N.graph.Reaches u (N.graph.source k₁) ∨ N.graph.Reaches u (N.graph.source k₂) := by
  rcases Relation.ReflTransGen.cases_tail
    (reaches_reticulation hN hLevel C.reticulation hh₂ hu) with heq | ⟨c, hc, f, rfl, hf⟩
  · exact absurd heq.symm huh
  · rcases C.arcs f hf with rfl | rfl
    · exact Or.inl hc
    · exact Or.inr hc

/-- All vertices of the blob are on the cycle. -/
theorem mem_of_sameBlob (hN : N.IsPhylogenetic) (hLevel : IsLevelOne N)
    (hh₂ : 2 ≤ N.graph.indegree h) (C : BlobCycle N v h T k₁ k₂ pL pR) {u : V}
    (hu : SameBlob N v u) (huh : u ≠ h) :
    u ∈ T :: pL.map N.graph.target ∨ u ∈ T :: pR.map N.graph.target := by
  rcases C.reaches_source hN hLevel hh₂ hu huh with hr | hr
  · exact Or.inl (C.mem_left_of_reaches hN hLevel hh₂ hu hr)
  · exact Or.inr (C.swap.mem_left_of_reaches hN hLevel hh₂ hu hr)

/-- All arcs of the blob not entering `h` are on the two sides of the cycle: the directed path through
such an arc, and a side, are both the wedge path from `p₁` or `p₂` to the top. -/
theorem mem_of_arc (hN : N.IsPhylogenetic) (hLevel : IsLevelOne N)
    (hh₂ : 2 ≤ N.graph.indegree h) (C : BlobCycle N v h T k₁ k₂ pL pR) {f : E}
    (hs : SameBlob N v (N.graph.source f)) (ht : SameBlob N v (N.graph.target f))
    (hth : N.graph.target f ≠ h) : f ∈ pL ∨ f ∈ pR := by
  have hA := hN.acyclic
  have key : ∀ {k₁ k₂ : E} {pL pR : List E}, BlobCycle N v h T k₁ k₂ pL pR →
      N.graph.Reaches (N.graph.target f) (N.graph.source k₁) → f ∈ pL := by
    intro k₁ k₂ pL pR C hr
    obtain ⟨A', hA'⟩ := exists_isDirPath (C.top_reaches _ hs)
    obtain ⟨B, hB⟩ := exists_isDirPath hr
    have hw₁ : N.IsWedgePath (N.graph.source k₁) T T (A' ++ f :: B) [] :=
      IsWedgePath.of_disjoint hA (hA'.append ⟨rfl, hB⟩) rfl (by simp)
    have hw₂ : N.IsWedgePath (N.graph.source k₁) T T pL [] :=
      IsWedgePath.of_disjoint hA C.left rfl (by simp)
    have := (wedgePath_unique hN hLevel C.reticulation hh₂ (C.source₁_sameBlob hN) C.top
      (C.source₁_ne hN) (C.top_ne hN) hw₁ hw₂).2.1
    rw [← this]
    simp
  rcases C.reaches_source hN hLevel hh₂ ht hth with hr | hr
  · exact Or.inl (key C hr)
  · exact Or.inr (key C.swap hr)

/-- **Exactly two wedge paths from the reticulation to a vertex of the blob, and their union is the blob**
(TOB-QMC, proof of Lemma 4, lines 543–544 of v5), for a vertex on the side of `p₁`. -/
theorem exactly_two_of_left (hN : N.IsPhylogenetic) (hLevel : IsLevelOne N)
    (hh₂ : 2 ≤ N.graph.indegree h) (C : BlobCycle N v h T k₁ k₂ pL pR) {b : V}
    (hb : b ∈ T :: pL.map N.graph.target) (hbh : b ≠ h) :
    ∃ W₁ W₂ : V × List E × List E, W₁ ≠ W₂ ∧
      (∀ W : V × List E × List E, N.IsWedgePath h b W.1 W.2.1 W.2.2 ↔ W = W₁ ∨ W = W₂) ∧
      ∀ f, SameBlob N v (N.graph.source f) → SameBlob N v (N.graph.target f) →
        (f ∈ W₁.2.1 ∨ f ∈ W₁.2.2) ∨ (f ∈ W₂.2.1 ∨ f ∈ W₂.2.2) := by
  have hAc := hN.acyclic
  obtain ⟨A, B, rfl, hA, hB⟩ := C.left.split_of_mem_vertices hb
  have hbb : SameBlob N v b :=
    sameBlob_of_reaches_of_reaches hN C.top (C.source₁_sameBlob hN) hA.reaches hB.reaches
  have hk₁ : N.IsDirPath (N.graph.source k₁) [k₁] h := ⟨rfl, C.target₁⟩
  have hk₂ : N.IsDirPath (N.graph.source k₂) [k₂] h := ⟨rfl, C.target₂⟩
  have hw₁ : N.IsWedgePath h b b (B ++ [k₁]) [] :=
    IsWedgePath.of_disjoint hAc (hB.append hk₁) rfl (by simp)
  have hw₂ : N.IsWedgePath h b T (pR ++ [k₂]) A := by
    refine IsWedgePath.of_disjoint hAc (C.right.append hk₂) hA fun z hz hzA => ?_
    have hzL : z ∈ (A ++ B).map N.graph.target := by
      rw [List.map_append]
      exact List.mem_append_left _ hzA
    simp only [List.map_append, List.map_cons, List.map_nil, List.mem_append, List.mem_singleton]
      at hz
    rcases hz with hz | rfl
    · exact C.disjoint z hzL hz
    · rw [C.target₂] at hzL
      exact C.reticulation_notMem_left hN hzL
  refine ⟨(b, B ++ [k₁], []), (T, pR ++ [k₂], A), ?_, ?_, ?_⟩
  · intro heq
    have h₂ : B ++ [k₁] = pR ++ [k₂] := congrArg (fun W : V × List E × List E => W.2.1) heq
    have := (List.append_inj' h₂ (by simp)).2
    exact C.ne (by simpa using this)
  · rintro ⟨s, m₁, m₂⟩
    constructor
    · intro hw
      simp only at hw
      have hs : SameBlob N v s := hw.summit_sameBlob hN C.reticulation hbb
      rcases List.eq_nil_or_concat' m₁ with rfl | ⟨L, g, rfl⟩
      · exfalso
        obtain rfl : s = h := hw.left
        exact hbh (eq_of_reaches_of_reaches hAc
          (reaches_reticulation hN hLevel C.reticulation hh₂ hbb) hw.right.reaches)
      · obtain ⟨m, hL, rfl, hgh⟩ := isDirPath_append.mp hw.left
        rcases C.arcs g hgh with rfl | rfl
        · -- through `k₁`: the summit is `b`
          left
          have hLeq : L = m₂ ++ B := isDirPath_unique hN hLevel C.reticulation hh₂ hs
            (C.source₁_sameBlob hN) (C.source₁_ne hN) hL (hw.right.append hB)
          have hsb : s = b := by
            rcases List.mem_cons.mp hw.right.end_mem_vertices with h' | h'
            · exact h'.symm
            · exact (hw.disjoint (z := b)
                (by simp only [hLeq, List.map_append, List.mem_append]; exact Or.inl (Or.inl h')) h').elim
          subst hsb
          have hm₂ : m₂ = [] := isDirPath_unique hN hLevel C.reticulation hh₂ hbb hbb hbh hw.right rfl
          subst hm₂
          simp only [List.nil_append] at hLeq
          subst hLeq
          rfl
        · -- through `k₂`: the summit is the top
          right
          obtain ⟨A', hA'⟩ := exists_isDirPath (C.top_reaches s hs)
          have h₁ : pR = A' ++ L := isDirPath_unique hN hLevel C.reticulation hh₂ C.top
            (C.swap.source₁_sameBlob hN) (C.swap.source₁_ne hN) C.right (hA'.append hL)
          have h₂ : A ++ B = A' ++ (m₂ ++ B) := isDirPath_unique hN hLevel C.reticulation hh₂ C.top
            (C.source₁_sameBlob hN) (C.source₁_ne hN) C.left (hA'.append (hw.right.append hB))
          have hsT : s = T := by
            rcases List.mem_cons.mp hA'.end_mem_vertices with h' | h'
            · exact h'
            · refine (C.disjoint s ?_ ?_).elim
              · rw [h₂, List.map_append]
                exact List.mem_append_left _ h'
              · rw [h₁, List.map_append]
                exact List.mem_append_left _ h'
          subst hsT
          have hA'nil : A' = [] := isDirPath_unique hN hLevel C.reticulation hh₂ hs hs (C.top_ne hN) hA' rfl
          subst hA'nil
          simp only [List.nil_append] at h₁
          subst h₁
          have hm₂ : m₂ = A := isDirPath_unique hN hLevel C.reticulation hh₂ hs hbb hbh hw.right hA
          subst hm₂
          rfl
    · rintro (heq | heq)
      · cases heq
        exact hw₁
      · cases heq
        exact hw₂
  · intro f hs ht
    simp only [List.mem_append, List.mem_singleton, List.not_mem_nil, or_false]
    by_cases hth : N.graph.target f = h
    · rcases C.arcs f hth with rfl | rfl
      · exact Or.inl (Or.inr rfl)
      · exact Or.inr (Or.inl (Or.inr rfl))
    · rcases C.mem_of_arc hN hLevel hh₂ hs ht hth with hf | hf
      · rcases List.mem_append.mp hf with hf | hf
        · exact Or.inr (Or.inr hf)
        · exact Or.inl (Or.inl hf)
      · exact Or.inr (Or.inl (Or.inl hf))

end BlobCycle

/-- **Exactly two wedge paths from the reticulation of a level-1 blob to another of its vertices, and their
union is the blob** (TOB-QMC, proof of Lemma 4, lines 543–544 of v5). A path is given by its
summit and two legs. -/
theorem exactly_two_wedgePaths (hN : N.IsPhylogenetic) (hBin : N.IsBinary) (hLevel : IsLevelOne N)
    (hh : SameBlob N v h) (hh₂ : 2 ≤ N.graph.indegree h) {b : V} (hb : SameBlob N v b)
    (hbh : b ≠ h) :
    ∃ W₁ W₂ : V × List E × List E, W₁ ≠ W₂ ∧
      (∀ W : V × List E × List E, N.IsWedgePath h b W.1 W.2.1 W.2.2 ↔ W = W₁ ∨ W = W₂) ∧
      ∀ f, SameBlob N v (N.graph.source f) → SameBlob N v (N.graph.target f) →
        (f ∈ W₁.2.1 ∨ f ∈ W₁.2.2) ∨ (f ∈ W₂.2.1 ∨ f ∈ W₂.2.2) := by
  obtain ⟨T, k₁, k₂, pL, pR, C⟩ := exists_blobCycle hN hBin hLevel hh hh₂
  rcases C.mem_of_sameBlob hN hLevel hh₂ hb hbh with hm | hm
  · exact C.exactly_two_of_left hN hLevel hh₂ hm hbh
  · exact C.swap.exactly_two_of_left hN hLevel hh₂ hm hbh

end Blob

/-! ### Attaching the taxa to the blob -/

section Attachment

variable {v h b : V} {x : X}

/-- `B(x)` (TOB-QMC, proof of Lemma 4, lines 539–540 of v5): the vertex `b` of the blob incident to the cut
edge whose deletion separates the taxon `x` from the subgraph containing the blob. The block of `x` is the
component `{u | BlockWalk N v (N.leaf x) u}` of the complement of the blob. The cut edge leaves the blob, or
it enters the blob when the root is in the block. -/
def IsAttachment (N : RootedNetwork V E X) (v : V) (x : X) (b : V) : Prop :=
  SameBlob N v b ∧ ∃ k, IsBridge N k ∧
    (∀ f, N.graph.Crosses f {u | BlockWalk N v (N.leaf x) u} ↔ f = k) ∧
    ((N.graph.source k = b ∧ BlockWalk N v (N.leaf x) (N.graph.target k)) ∨
      (N.graph.target k = b ∧ BlockWalk N v (N.leaf x) (N.graph.source k)))

theorem exists_isAttachment (hN : N.IsPhylogenetic) (hx : ¬ SameBlob N v (N.leaf x)) :
    ∃ b, IsAttachment N v x b := by
  obtain ⟨k, hkb, hS, ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩⟩ := exists_blockWalk_cut hN hx
  · exact ⟨_, h₁, k, hkb, hS, Or.inl ⟨rfl, h₂⟩⟩
  · exact ⟨_, h₁, k, hkb, hS, Or.inr ⟨rfl, h₂⟩⟩

/-- The taxon is below its attachment, or the attachment is the top of the blob with the taxon not below it. -/
theorem IsAttachment.reaches_or_top (hN : N.IsPhylogenetic) (hx : ¬ SameBlob N v (N.leaf x))
    (ha : IsAttachment N v x b) :
    N.graph.Reaches b (N.leaf x) ∨
      ((∀ w, SameBlob N v w → N.graph.Reaches b w) ∧ ¬ N.graph.Reaches b (N.leaf x)) := by
  obtain ⟨hb, k, hkb, hS, ⟨rfl, h₂⟩ | ⟨rfl, h₂⟩⟩ := ha
  · exact Or.inl ((reaches_of_arc N k).trans (reaches_of_blockWalk_of_exit hN hx hS hb .refl))
  · refine Or.inr ⟨fun w hw => reaches_of_sameBlob hN hkb (sameBlob_trans (sameBlob_symm hb) hw),
      fun hc => not_reaches_of_blockWalk_of_entry hS h₂ ?_ hc .refl⟩
    exact fun hc => not_sameBlob_of_blockWalk hx hc hb

/-- A path into a set that only `e` crosses passes through `e`. -/
theorem reaches_source_of_cut {e : E} {S : Set V} (hS : ∀ f, N.graph.Crosses f S ↔ f = e) {a c : V}
    (ha : a ∉ S) (hc : c ∈ S) (h : N.graph.Reaches a c) :
    N.graph.Reaches a (N.graph.source e) := by
  induction h with
  | refl => exact absurd hc ha
  | @tail w c haw hwc ih =>
    obtain ⟨f, rfl, rfl⟩ := hwc
    by_cases hw : N.graph.source f ∈ S
    · exact ih hw
    · have := (hS f).mp (Or.inr ⟨hc, hw⟩)
      subst this
      exact haw

/-- A vertex of the blob above a taxon is above its attachment. -/
theorem IsAttachment.reaches_of_reaches (hN : N.IsPhylogenetic) (hx : ¬ SameBlob N v (N.leaf x))
    (ha : IsAttachment N v x b) {w : V} (hw : SameBlob N v w) (hr : N.graph.Reaches w (N.leaf x)) :
    N.graph.Reaches w b := by
  obtain ⟨hb, k, hkb, hS, ⟨rfl, -⟩ | ⟨rfl, h₂⟩⟩ := ha
  · exact reaches_source_of_cut hS (fun hc => not_sameBlob_of_blockWalk hx hc hw) .refl hr
  · have htop := reaches_of_sameBlob hN hkb (sameBlob_trans (sameBlob_symm hb) hw)
    exact absurd (htop.trans hr) fun hc => not_reaches_of_blockWalk_of_entry hS h₂
      (fun hc => not_sameBlob_of_blockWalk hx hc hb) hc .refl

/-- **The wedge path from a taxon to its attachment** (TOB-QMC, proof of Lemma 4, line 544 of v5): all its
vertices other than the attachment are in the block of the taxon. It is directed, or its summit is above
the top of the blob, in the block of the taxon, when the block contains the root. -/
structure AttachPath (N : RootedNetwork V E X) (v : V) (x : X) (b u : V) (l₁ l₂ : List E) : Prop where
  blob : SameBlob N v b
  wedge : N.IsWedgePath (N.leaf x) b u l₁ l₂
  summit : u = b ∨ BlockWalk N v (N.leaf x) u
  block₁ : ∀ z ∈ l₁.map N.graph.target, BlockWalk N v (N.leaf x) z
  block₂ : ∀ z ∈ l₂.map N.graph.target, z = b ∨ BlockWalk N v (N.leaf x) z
  kind : (u = b ∧ l₂ = []) ∨
    ((∀ w, SameBlob N v w → N.graph.Reaches b w) ∧ ¬ N.graph.Reaches b (N.leaf x))

/-- The ends of an arc of the wedge path from a taxon to its attachment. -/
theorem AttachPath.ends {u : V} {l₁ l₂ : List E} {f : E} (hP : AttachPath N v x b u l₁ l₂)
    (hf : f ∈ l₁ ∨ f ∈ l₂) :
    (N.graph.source f = b ∨ BlockWalk N v (N.leaf x) (N.graph.source f)) ∧
      (N.graph.target f = b ∨ BlockWalk N v (N.leaf x) (N.graph.target f)) := by
  rcases hf with hf | hf
  · refine ⟨?_, Or.inr (hP.block₁ _ (List.mem_map_of_mem hf))⟩
    rcases List.mem_cons.mp (hP.wedge.left.source_mem_vertices hf) with h' | h'
    · rw [h']
      exact hP.summit
    · exact Or.inr (hP.block₁ _ h')
  · refine ⟨?_, hP.block₂ _ (List.mem_map_of_mem hf)⟩
    rcases List.mem_cons.mp (hP.wedge.right.source_mem_vertices hf) with h' | h'
    · rw [h']
      exact hP.summit
    · exact hP.block₂ _ h'

/-- Every taxon outside the blob has a wedge path to its attachment. -/
theorem IsAttachment.exists_attachPath (hN : N.IsPhylogenetic) (hx : ¬ SameBlob N v (N.leaf x))
    (ha : IsAttachment N v x b) : ∃ u l₁ l₂, AttachPath N v x b u l₁ l₂ := by
  have hA := hN.acyclic
  have hkind := ha.reaches_or_top hN hx
  obtain ⟨hb, k, -, hS, ⟨rfl, h₂⟩ | ⟨rfl, h₂⟩⟩ := ha
  · -- the cut edge leaves the blob: a directed path
    have hnK : N.graph.source k ∉ {u | BlockWalk N v (N.leaf x) u} :=
      fun hc => not_sameBlob_of_blockWalk hx hc hb
    obtain ⟨l, hl⟩ := exists_isDirPath (reaches_of_blockWalk_of_exit hN hx hS hb .refl)
    refine ⟨_, k :: l, [], hb, IsWedgePath.of_disjoint hA ⟨rfl, hl⟩ rfl (by simp), Or.inl rfl,
      fun z hz => ?_, by simp, Or.inl ⟨rfl, rfl⟩⟩
    have hz' := (isDirPath_cons.mpr ⟨rfl, hl⟩ : N.IsDirPath _ (k :: l) _).reaches_of_mem_map hz
    rcases List.mem_cons.mp hz with rfl | hz₁
    · exact h₂
    · exact mem_of_reaches_of_cut hS hnK h₂ (hl.reaches_of_mem_map hz₁).1
  · -- the cut edge enters the blob: the summit is in the block
    rcases hkind with h' | ⟨htop, hno⟩
    · exact (not_reaches_of_blockWalk_of_entry hS h₂
        (fun hc => not_sameBlob_of_blockWalk hx hc hb) h' .refl).elim
    obtain ⟨P, hP⟩ := exists_isDirPath (hN.root_reaches (N.leaf x))
    obtain ⟨Q, hQ⟩ := exists_isDirPath (hN.root_reaches (N.graph.source k))
    obtain ⟨u, P₁, P₂, Q₂, -, -, -, hw⟩ := exists_isWedgePath hA hP hQ.snoc
    -- vertices above the taxon are in its block
    have habove : ∀ {z : V}, N.graph.Reaches z (N.leaf x) → BlockWalk N v (N.leaf x) z := by
      intro z hz
      refine blockWalk_symm (blockWalk_of_reaches hz fun w _ hwx hbw => ?_)
      exact hno ((htop w hbw).trans hwx)
    have hu : BlockWalk N v (N.leaf x) u := habove hw.left.reaches
    refine ⟨u, P₂, Q₂, hb, hw, Or.inr hu, fun z hz => habove (hw.left.reaches_of_mem_map hz).2,
      fun z hz => ?_, Or.inr ⟨htop, hno⟩⟩
    by_cases hzb : z = N.graph.target k
    · exact Or.inl hzb
    · refine Or.inr (blockWalk_trans hu (blockWalk_of_reaches (hw.right.reaches_of_mem_map hz).1 ?_))
      intro w _ hwz hbw
      have h₁ := (hw.right.reaches_of_mem_map hz).2
      exact hzb (eq_of_reaches_of_reaches hA h₁ ((htop w hbw).trans hwz))

/-- **Adding the wedge paths from the taxa to their attachments** (TOB-QMC, proof of Lemma 4, line 544
of v5): a wedge path from `h` to the attachment of `a`, the wedge path from `a` to its attachment, and a
directed path from `h` to a taxon `d` in another block form a wedge path from `d` to `a`. -/
theorem AttachPath.glue (hN : N.IsPhylogenetic) {a d : X} {u s : V} {l₁ l₂ l m₁ m₂ : List E}
    (ha : ¬ SameBlob N v (N.leaf a)) (hd : ¬ SameBlob N v (N.leaf d))
    (hne : ¬ BlockWalk N v (N.leaf a) (N.leaf d)) (hh : SameBlob N v h)
    (hP : AttachPath N v a b u l₁ l₂) (hl : N.IsDirPath h l (N.leaf d))
    (hlb : ∀ z ∈ l.map N.graph.target, BlockWalk N v (N.leaf d) z)
    (hW : N.IsWedgePath h b s m₁ m₂) :
    ∃ u' p q, N.IsWedgePath (N.leaf d) (N.leaf a) u' p q ∧
      ∀ f, (f ∈ l ∨ f ∈ m₁ ∨ f ∈ m₂ ∨ f ∈ l₁ ∨ f ∈ l₂) → f ∈ p ∨ f ∈ q := by
  have hA := hN.acyclic
  have hb := hP.blob
  have hinM : ∀ {z : V}, z ∈ m₁.map N.graph.target ∨ z ∈ m₂.map N.graph.target →
      SameBlob N v z := by
    intro z hz
    refine hW.sameBlob_of_mem hN hh hb (List.mem_cons_of_mem _ (List.mem_append.mpr hz))
  have hcross : ∀ {z : V}, BlockWalk N v (N.leaf a) z → BlockWalk N v (N.leaf d) z → False :=
    fun h₁ h₂ => hne (blockWalk_trans h₁ (blockWalk_symm h₂))
  rcases hP.kind with ⟨rfl, rfl⟩ | ⟨htop, hno⟩
  · refine ⟨s, m₁ ++ l, m₂ ++ l₁, IsWedgePath.of_disjoint hA (hW.left.append hl)
      (hW.right.append hP.wedge.left) fun z hz hz' => ?_, ?_⟩
    · simp only [List.map_append, List.mem_append] at hz hz'
      rcases hz with hz | hz <;> rcases hz' with hz' | hz'
      · exact hW.disjoint hz hz'
      · exact not_sameBlob_of_blockWalk ha (hP.block₁ z hz') (hinM (Or.inl hz))
      · exact not_sameBlob_of_blockWalk hd (hlb z hz) (hinM (Or.inr hz'))
      · exact hcross (hP.block₁ z hz') (hlb z hz)
    · intro f hf
      simp only [List.mem_append]
      rcases hf with hf | hf | hf | hf | hf
      · exact Or.inl (Or.inr hf)
      · exact Or.inl (Or.inl hf)
      · exact Or.inr (Or.inl hf)
      · exact Or.inr (Or.inr hf)
      · simp at hf
  · -- the attachment is the top of the blob, which is the summit from `h`
    have hs : SameBlob N v s := hW.summit_sameBlob hN hh hb
    obtain rfl : s = b := eq_of_reaches_of_reaches hA hW.right.reaches (htop s hs)
    obtain rfl : m₂ = [] := by
      cases m₂ with
      | nil => rfl
      | cons g m =>
        obtain ⟨hg, hm⟩ := hW.right
        exact absurd (hg ▸ hm.reaches) (not_reaches_target_source hA g)
    refine ⟨u, l₂ ++ (m₁ ++ l), l₁, IsWedgePath.of_disjoint hA
      (hP.wedge.right.append (hW.left.append hl)) hP.wedge.left fun z hz hz' => ?_, ?_⟩
    · simp only [List.map_append, List.mem_append] at hz
      rcases hz with hz | hz | hz
      · exact hP.wedge.disjoint hz' hz
      · exact not_sameBlob_of_blockWalk ha (hP.block₁ z hz') (hinM (Or.inl hz))
      · exact hcross (hP.block₁ z hz') (hlb z hz)
    · intro f hf
      simp only [List.mem_append]
      rcases hf with hf | hf | hf | hf | hf
      · exact Or.inl (Or.inr (Or.inr hf))
      · exact Or.inl (Or.inr (Or.inl hf))
      · simp at hf
      · exact Or.inr hf
      · exact Or.inl (Or.inl hf)

end Attachment

/-! ### The direction `⇐` of Lemma 4: the wedge paths form a cycle with the four taxa attached -/

section Backward

variable [Fintype V] [Fintype E] {v h : V}

omit [Fintype V] [Fintype E] in
/-- An arc that does not cross a vertex set has both ends on one side. -/
theorem mem_iff_of_not_crosses {f : E} {S : Set V} (h : ¬ N.graph.Crosses f S) :
    N.graph.source f ∈ S ↔ N.graph.target f ∈ S := by
  simp only [DirectedMultigraph.Crosses] at h
  tauto

/-- The directed path from the reticulation to a taxon below it stays in the block of the taxon. -/
theorem exists_path_of_below_reticulation (hN : N.IsPhylogenetic) (hLevel : IsLevelOne N)
    (hh : SameBlob N v h) (hh₂ : 2 ≤ N.graph.indegree h) {d : X}
    (hd : N.graph.Reaches h (N.leaf d)) :
    ∃ l, N.IsDirPath h l (N.leaf d) ∧ ∀ z ∈ l.map N.graph.target, BlockWalk N v (N.leaf d) z := by
  obtain ⟨l, hl⟩ := exists_isDirPath hd
  refine ⟨l, hl, fun z hz => blockWalk_symm
    (blockWalk_of_reaches (hl.reaches_of_mem_map hz).2 fun w hzw _ hbw => ?_)⟩
  have hzh : z = h := eq_of_reaches_of_reaches hN.acyclic
    (hzw.trans (reaches_reticulation hN hLevel hh hh₂ hbw)) (hl.reaches_of_mem_map hz).1
  exact hl.start_notMem hN.acyclic (hzh ▸ hz)

omit [Fintype V] [Fintype E] in
/-- **A cut edge of a graph containing the cycle is not on the cycle.** -/
theorem BlobCycle.notMem_of_cut (hN : N.IsPhylogenetic) {T : V} {k₁ k₂ : E} {pL pR : List E}
    (C : BlobCycle N v h T k₁ k₂ pL pR) {F : Set E} {S : Set V} {e : E}
    (hF : ∀ f, f ∈ pL ++ [k₁] ∨ f ∈ pR ++ [k₂] → f ∈ F)
    (hS : ∀ f ∈ F, N.graph.Crosses f S ↔ f = e) : e ∉ pL ++ [k₁] := by
  intro he
  have hA := hN.acyclic
  have hL : N.IsDirPath T (pL ++ [k₁]) h := C.left.append ⟨rfl, C.target₁⟩
  have hR : N.IsDirPath T (pR ++ [k₂]) h := C.right.append ⟨rfl, C.target₂⟩
  have heR : e ∉ pR ++ [k₂] := by
    intro he'
    simp only [List.mem_append, List.mem_singleton] at he he'
    rcases he with he | rfl <;> rcases he' with he' | rfl
    · exact C.disjoint _ (List.mem_map_of_mem he) (List.mem_map_of_mem he')
    · exact C.reticulation_notMem_left hN (C.target₂ ▸ List.mem_map_of_mem he)
    · exact C.swap.reticulation_notMem_left hN (C.target₁ ▸ List.mem_map_of_mem he')
    · exact C.ne rfl
  have h₁ : T ∈ S ↔ h ∈ S := hR.mem_iff fun f hf hc =>
    heR ((hS f (hF f (Or.inr hf))).mp hc ▸ hf)
  obtain ⟨L₁, L₂, hLeq, hL₁, hL₂⟩ := hL.split_of_mem he
  have hnd₁ : e ∉ L₁ := hL₁.notMem_of_reaches_source hA .refl
  have hnd₂ : e ∉ L₂ := hL₂.notMem_of_target_reaches hA .refl
  have h₂ : T ∈ S ↔ N.graph.source e ∈ S := hL₁.mem_iff fun f hf hc =>
    hnd₁ ((hS f (hF f (Or.inl (by simp [hLeq, hf])))).mp hc ▸ hf)
  have h₃ : N.graph.target e ∈ S ↔ h ∈ S := hL₂.mem_iff fun f hf hc =>
    hnd₂ ((hS f (hF f (Or.inl (by simp [hLeq, hf])))).mp hc ▸ hf)
  have hc := (hS e (hF e (Or.inl he))).mpr rfl
  simp only [DirectedMultigraph.Crosses] at hc
  tauto

omit [Fintype V] [Fintype E] in
/-- The arcs of the cycle have both ends in the blob. -/
theorem BlobCycle.sameBlob_of_mem (hN : N.IsPhylogenetic) {T : V} {k₁ k₂ : E} {pL pR : List E}
    (C : BlobCycle N v h T k₁ k₂ pL pR) {f : E} (hf : f ∈ pL ++ [k₁]) :
    SameBlob N v (N.graph.source f) ∧ SameBlob N v (N.graph.target f) := by
  have hL : N.IsDirPath T (pL ++ [k₁]) h := C.left.append ⟨rfl, C.target₁⟩
  have hr := hL.reaches_of_mem hf
  exact ⟨sameBlob_of_reaches_of_reaches hN C.top C.reticulation hr.1
      ((reaches_of_arc N f).trans hr.2),
    sameBlob_of_reaches_of_reaches hN C.top C.reticulation (hr.1.tail ⟨f, rfl, rfl⟩) hr.2⟩

/-- **Lemma 4, `⇐`, on the subnetwork** (TOB-QMC, lines 541–546 of v5). Take four taxa in distinct blocks,
with `d` below the reticulation. The other taxa are attached away from `h`. For each of them, the wedge paths
from `h` to its attachment cover the blob, and with the wedge paths from the taxa to their attachments, they
are wedge paths between taxa. So the subnetwork contains the cycle, with all four taxa attached, and
no cut edge of it induces a `2|2` split: such an edge is not on the cycle, so the cycle is on one side
of it, and two taxa on the other side would attach through it, while they are in distinct blocks. -/
theorem not_hasWedgeCutSplit (hN : N.IsPhylogenetic) (hBin : N.IsBinary) (hLevel : IsLevelOne N)
    (hh : SameBlob N v h) (hh₂ : 2 ≤ N.graph.indegree h) {Y : Finset X} (hY : Y.card = 4)
    (hdist : ∀ a ∈ Y, ∀ b ∈ Y, a ≠ b → ¬ BlockWalk N v (N.leaf a) (N.leaf b)) {d : X} (hd : d ∈ Y)
    (hdh : N.graph.Reaches h (N.leaf d)) {P : Finset X} (hPY : P ⊆ Y) (hP : P.card = 2) :
    ¬ N.HasWedgeCutSplit (Y : Set X) (P : Set X) := by
  rintro ⟨e, -, S, hS, hAS⟩
  obtain ⟨T, k₁, k₂, pL, pR, C⟩ := exists_blobCycle hN hBin hLevel hh hh₂
  have hx : ∀ x, ¬ SameBlob N v (N.leaf x) := leaf_not_sameBlob hN hh hh₂
  obtain ⟨l, hl, hlb⟩ := exists_path_of_below_reticulation hN hLevel hh hh₂ hdh
  -- the other taxa are attached away from `h`: by distinct blocks only `d` is below `h`
  have hne_h : ∀ {a : X} {b : V}, a ∈ Y → a ≠ d → IsAttachment N v a b → b ≠ h := by
    rintro a b ha hne hat rfl
    rcases hat.reaches_or_top hN (hx a) with hr | ⟨htop, -⟩
    · exact hdist a ha d hd hne (blockWalk_of_below_reticulation hN hBin hLevel hh hh₂ hr hdh)
    · exact C.not_reaches_of_target₁ hN (htop _ (C.source₁_sameBlob hN))
  -- wedge paths from `h` to an attachment and from the attachment to its taxon are wedge paths between taxa
  have hglue : ∀ {a : X} {b u s : V} {l₁ l₂ m₁ m₂ : List E}, a ∈ Y → a ≠ d →
      AttachPath N v a b u l₁ l₂ → N.IsWedgePath h b s m₁ m₂ →
      ∀ f, (f ∈ l ∨ f ∈ m₁ ∨ f ∈ m₂ ∨ f ∈ l₁ ∨ f ∈ l₂) → f ∈ N.wedgeArcs (Y : Set X) := by
    intro a b u s l₁ l₂ m₁ m₂ ha hne hPa hW f hf
    obtain ⟨u', p, q, hw, hc⟩ := hPa.glue hN (hx a) (hx d) (hdist a ha d hd hne) hh hl hlb hW
    exact ⟨d, hd, a, ha, hne.symm, u', p, q, hw, hc f hf⟩
  obtain ⟨a₀, ha₀, ha₀d⟩ := Finset.exists_mem_ne (by omega : 1 < Y.card) d
  obtain ⟨b₀, hb₀⟩ := exists_isAttachment hN (hx a₀)
  obtain ⟨W₁, W₂, -, hW, hcov⟩ :=
    exactly_two_wedgePaths hN hBin hLevel hh hh₂ hb₀.1 (hne_h ha₀ ha₀d hb₀)
  obtain ⟨u₀, l₁₀, l₂₀, hP₀⟩ := hb₀.exists_attachPath hN (hx a₀)
  -- the subnetwork contains the blob
  have hblob : ∀ f, SameBlob N v (N.graph.source f) → SameBlob N v (N.graph.target f) →
      f ∈ N.wedgeArcs (Y : Set X) := by
    intro f hs ht
    rcases hcov f hs ht with hf | hf
    · exact hglue ha₀ ha₀d hP₀ ((hW W₁).mpr (Or.inl rfl)) f (Or.inr (hf.imp_right Or.inl))
    · exact hglue ha₀ ha₀d hP₀ ((hW W₂).mpr (Or.inr rfl)) f (Or.inr (hf.imp_right Or.inl))
  -- it contains the wedge path from each taxon to its attachment
  have hattach : ∀ x ∈ Y, ∃ b u l₁ l₂, AttachPath N v x b u l₁ l₂ ∧
      ∀ f, f ∈ l₁ ∨ f ∈ l₂ → f ∈ N.wedgeArcs (Y : Set X) := by
    intro x hxY
    by_cases hxd : x = d
    · subst hxd
      refine ⟨h, h, l, [], ⟨hh, IsWedgePath.of_disjoint hN.acyclic hl rfl (by simp), Or.inl rfl, hlb,
        by simp, Or.inl ⟨rfl, rfl⟩⟩, fun f hf => ?_⟩
      exact hglue ha₀ ha₀d hP₀ ((hW W₁).mpr (Or.inl rfl)) f (Or.inl (by simpa using hf))
    · obtain ⟨b, hb⟩ := exists_isAttachment hN (hx x)
      obtain ⟨u, l₁, l₂, hPx⟩ := hb.exists_attachPath hN (hx x)
      obtain ⟨W, _, -, hW', -⟩ :=
        exactly_two_wedgePaths hN hBin hLevel hh hh₂ hb.1 (hne_h hxY hxd hb)
      exact ⟨b, u, l₁, l₂, hPx, fun f hf =>
        hglue hxY hxd hPx ((hW' W).mpr (Or.inl rfl)) f (Or.inr (Or.inr (Or.inr hf)))⟩
  -- a cut edge of the subnetwork is not an arc of the blob
  have hee : ¬ (SameBlob N v (N.graph.source e) ∧ SameBlob N v (N.graph.target e)) := by
    rintro ⟨h₁, h₂⟩
    have hcyc : ∀ f, f ∈ pL ++ [k₁] ∨ f ∈ pR ++ [k₂] → f ∈ N.wedgeArcs (Y : Set X) := by
      rintro f (hf | hf)
      · exact hblob f (C.sameBlob_of_mem hN hf).1 (C.sameBlob_of_mem hN hf).2
      · exact hblob f (C.swap.sameBlob_of_mem hN hf).1 (C.swap.sameBlob_of_mem hN hf).2
    have hF₁ := C.notMem_of_cut hN hcyc hS
    have hF₂ := C.swap.notMem_of_cut hN (fun f hf => hcyc f hf.symm) hS
    by_cases hth : N.graph.target e = h
    · rcases C.arcs e hth with rfl | rfl
      · exact hF₁ (by simp)
      · exact hF₂ (by simp)
    · rcases C.mem_of_arc hN hLevel hh₂ h₁ h₂ hth with hf | hf
      · exact hF₁ (by simp [hf])
      · exact hF₂ (by simp [hf])
  -- so the blob is on one side of it
  have hside : ∀ u, SameBlob N v u → (v ∈ S ↔ u ∈ S) := by
    intro u hu
    induction hu with
    | refl => exact Iff.rfl
    | @tail a c hac hstep ih =>
      have hca : SameBlob N v c := hac.tail hstep
      obtain ⟨f, -, hf⟩ := hstep
      have hfb : SameBlob N v (N.graph.source f) ∧ SameBlob N v (N.graph.target f) := by
        rcases hf with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact ⟨hac, hca⟩
        · exact ⟨hca, hac⟩
      have hnc : ¬ N.graph.Crosses f S := by
        intro hc
        have hfe := (hS f (hblob f hfb.1 hfb.2)).mp hc
        subst hfe
        exact hee hfb
      have heq := mem_iff_of_not_crosses hnc
      rcases hf with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact ih.trans heq
      · exact ih.trans heq.symm
  -- two taxa on the other side
  obtain ⟨x, hxY, y, hyY, hxy, hxS, hyS⟩ : ∃ x ∈ Y, ∃ y ∈ Y, x ≠ y ∧
      (N.leaf x ∈ S ↔ ¬ v ∈ S) ∧ (N.leaf y ∈ S ↔ ¬ v ∈ S) := by
    by_cases hv : v ∈ S
    · have hQ : 1 < (Y \ P).card := by
        rw [Finset.card_sdiff_of_subset hPY]
        omega
      obtain ⟨x, hx', y, hy', hxy⟩ := Finset.one_lt_card.mp hQ
      have key : ∀ z ∈ Y \ P, N.leaf z ∈ S ↔ ¬ v ∈ S := by
        intro z hz
        have hz' := Finset.mem_sdiff.mp hz
        have := hAS z (Finset.mem_coe.mpr hz'.1)
        rw [Finset.mem_coe] at this
        exact ⟨fun h' => absurd (this.mp h') hz'.2, fun h' => absurd hv h'⟩
      exact ⟨x, (Finset.mem_sdiff.mp hx').1, y, (Finset.mem_sdiff.mp hy').1, hxy, key x hx', key y hy'⟩
    · obtain ⟨x, hx', y, hy', hxy⟩ := Finset.one_lt_card.mp (by omega : 1 < P.card)
      have key : ∀ z ∈ P, N.leaf z ∈ S ↔ ¬ v ∈ S := by
        intro z hz
        have := hAS z (Finset.mem_coe.mpr (hPY hz))
        rw [Finset.mem_coe] at this
        exact ⟨fun _ => hv, fun _ => this.mpr hz⟩
      exact ⟨x, hPY hx', y, hPY hy', hxy, key x hx', key y hy'⟩
  -- each of the two attaches through the cut edge
  have huse : ∀ z ∈ Y, (N.leaf z ∈ S ↔ ¬ v ∈ S) → ∀ w, ¬ SameBlob N v w →
      (w = N.graph.source e ∨ w = N.graph.target e) → BlockWalk N v (N.leaf z) w := by
    intro z hz hzS w hw hwe
    obtain ⟨b, u, l₁, l₂, hPz, hin⟩ := hattach z hz
    have hmem : e ∈ l₁ ∨ e ∈ l₂ := by
      by_contra hno
      have h₁ : N.leaf z ∈ S ↔ b ∈ S := hPz.wedge.mem_iff fun f hf hc => by
        have hfe := (hS f (hin f hf)).mp hc
        subst hfe
        exact hno hf
      have h₂ := hside b hPz.blob
      exact iff_not_self ((hzS.symm.trans h₁).trans h₂.symm).symm
    have hends := hPz.ends hmem
    rcases hwe with rfl | rfl
    · rcases hends.1 with h' | h'
      · exact absurd (h' ▸ hPz.blob) hw
      · exact h'
    · rcases hends.2 with h' | h'
      · exact absurd (h' ▸ hPz.blob) hw
      · exact h'
  obtain ⟨w, hw, hwe⟩ : ∃ w, ¬ SameBlob N v w ∧ (w = N.graph.source e ∨ w = N.graph.target e) := by
    by_contra hcon
    push Not at hcon
    exact hee ⟨not_not.mp fun h' => (hcon _ h').1 rfl, not_not.mp fun h' => (hcon _ h').2 rfl⟩
  exact hdist x hxY y hyY hxy (blockWalk_trans (huse x hxY hxS w hw hwe)
    (blockWalk_symm (huse y hyY hyS w hw hwe)))

end Backward

/-! ### The direction `⇒` of Lemma 4: a single path, and the order of the attachments along it -/

section Forward

variable [Fintype V] [Fintype E] {v h : V}

omit [Fintype V] [Fintype E] in
/-- A vertex of a binary network has at most two outgoing arcs. -/
theorem false_of_three_out_arcs (hN : N.IsPhylogenetic) (hBin : N.IsBinary) {u : V} {g₁ g₂ g₃ : E}
    (h₁₂ : g₁ ≠ g₂) (h₁₃ : g₁ ≠ g₃) (h₂₃ : g₂ ≠ g₃) (s₁ : N.graph.source g₁ = u)
    (s₂ : N.graph.source g₂ = u) (s₃ : N.graph.source g₃ = u) : False := by
  have := hN.finite_arcs
  have hle := outdegree_le_two hN hBin u
  have hcard : ({g₁, g₂, g₃} : Set E).ncard = 3 :=
    Set.ncard_eq_three.mpr ⟨g₁, g₂, g₃, h₁₂, h₁₃, h₂₃, rfl⟩
  have hsub : ({g₁, g₂, g₃} : Set E) ⊆ {e | N.graph.source e = u} := by
    rintro f (rfl | rfl | rfl) <;> assumption
  have := Set.ncard_le_ncard hsub (Set.toFinite _)
  rw [DirectedMultigraph.outdegree] at hle
  omega

namespace BlobCycle

variable {T : V} {k₁ k₂ : E} {pL pR : List E}

/-- A vertex of the blob other than `h` has an outgoing arc in the blob, towards `h`. -/
theorem exists_out_arc (hN : N.IsPhylogenetic) (hLevel : IsLevelOne N)
    (hh₂ : 2 ≤ N.graph.indegree h) (C : BlobCycle N v h T k₁ k₂ pL pR) {u : V}
    (hu : SameBlob N v u) (huh : u ≠ h) : ∃ g, N.graph.source g = u ∧ ¬ IsBridge N g := by
  rcases Relation.ReflTransGen.cases_head
    (reaches_reticulation hN hLevel C.reticulation hh₂ hu) with heq | ⟨c, ⟨g, rfl, rfl⟩, hc⟩
  · exact absurd heq huh
  · exact ⟨g, rfl, not_isBridge_of_sameBlob hN hu
      (sameBlob_of_reaches_of_reaches hN hu C.reticulation (reaches_of_arc N g) hc)⟩

omit [Fintype V] [Fintype E] in
/-- The top of the blob has two outgoing arcs in the blob. -/
theorem exists_two_out_arcs (hN : N.IsPhylogenetic) (C : BlobCycle N v h T k₁ k₂ pL pR) :
    ∃ g₁ g₂, g₁ ≠ g₂ ∧ N.graph.source g₁ = T ∧ N.graph.source g₂ = T ∧ ¬ IsBridge N g₁ ∧
      ¬ IsBridge N g₂ := by
  have hnb : ∀ {k₁ k₂ : E} {pL pR : List E}, BlobCycle N v h T k₁ k₂ pL pR → ∀ f, f ∈ pL ++ [k₁] →
      ¬ IsBridge N f := fun C f hf =>
    not_isBridge_of_sameBlob hN (C.sameBlob_of_mem hN hf).1 (C.sameBlob_of_mem hN hf).2
  have hL := C.left
  have hR := C.right
  cases pL with
  | nil =>
    cases pR with
    | nil =>
      exact ⟨k₁, k₂, C.ne, hL.symm, hR.symm, hnb C _ (by simp), hnb C.swap _ (by simp)⟩
    | cons g r =>
      refine ⟨k₁, g, ?_, hL.symm, hR.1, hnb C _ (by simp), hnb C.swap _ (by simp)⟩
      rintro rfl
      exact C.swap.reticulation_notMem_left hN (C.target₁ ▸ (by simp))
  | cons g l =>
    cases pR with
    | nil =>
      refine ⟨g, k₂, ?_, hL.1, hR.symm, hnb C _ (by simp), hnb C.swap _ (by simp)⟩
      rintro rfl
      exact C.reticulation_notMem_left hN (C.target₂ ▸ (by simp))
    | cons g' r =>
      refine ⟨g, g', ?_, hL.1, hR.1, hnb C _ (by simp), hnb C.swap _ (by simp)⟩
      rintro rfl
      exact C.disjoint (N.graph.target g) (by simp) (by simp)

end BlobCycle

/-- **Taxa in distinct blocks have distinct attachments** (TOB-QMC, proof of Lemma 4, line 541 of v5). A
vertex of the blob has at most one cut edge. A vertex other than `h` has an outgoing arc in the blob, the
top has two, a vertex has at most two outgoing arcs and `h` has one, and only `h` has two incoming arcs,
none of them a bridge. -/
theorem IsAttachment.blockWalk_of_eq (hN : N.IsPhylogenetic) (hBin : N.IsBinary)
    (hLevel : IsLevelOne N) (hh₂ : 2 ≤ N.graph.indegree h) {T b : V} {k₁ k₂ : E} {pL pR : List E}
    (C : BlobCycle N v h T k₁ k₂ pL pR) {x y : X} (hax : IsAttachment N v x b)
    (hay : IsAttachment N v y b) : BlockWalk N v (N.leaf x) (N.leaf y) := by
  by_contra hne
  obtain ⟨hb, kx, hkx, -, hx'⟩ := hax
  obtain ⟨-, ky, hky, -, hy'⟩ := hay
  -- a bridge entering the blob enters at the top, which has no cut edge leaving it
  have hexit : ∀ {k l : E}, IsBridge N k → IsBridge N l → N.graph.source k = b →
      N.graph.target l = b → False := by
    intro k l hk hl hks hlt
    have hbT : b = T := eq_of_reaches_of_reaches hN.acyclic
      (hlt ▸ reaches_of_sameBlob hN hl (hlt ▸ sameBlob_trans (sameBlob_symm hb) C.top))
      (C.top_reaches b hb)
    obtain ⟨g₁, g₂, h₁₂, hs₁, hs₂, hb₁, hb₂⟩ := C.exists_two_out_arcs hN
    exact false_of_three_out_arcs hN hBin h₁₂ (fun h' => hb₁ (h' ▸ hk)) (fun h' => hb₂ (h' ▸ hk))
      hs₁ hs₂ (hks.trans hbT)
  rcases hx' with ⟨hxs, hxt⟩ | ⟨hxt, hxs⟩ <;> rcases hy' with ⟨hys, hyt⟩ | ⟨hyt, hys⟩
  · have hxy : kx ≠ ky := by
      rintro rfl
      exact hne (blockWalk_trans hxt (blockWalk_symm hyt))
    by_cases hbh : b = h
    · obtain ⟨g, hg⟩ := (N.graph.outdegree_eq_one_iff h).mp
        (outdegree_eq_one_of_reticulation hN hBin hh₂)
      exact hxy (((hg kx).mp (hxs.trans hbh)).trans ((hg ky).mp (hys.trans hbh)).symm)
    · obtain ⟨g, hg, hgb⟩ := C.exists_out_arc hN hLevel hh₂ hb hbh
      exact false_of_three_out_arcs (g₃ := g) hN hBin hxy (fun h' => hgb (h' ▸ hkx))
        (fun h' => hgb (h' ▸ hky)) hxs hys hg
  · exact hexit hkx hky hxs hyt
  · exact hexit hky hkx hys hxt
  · have hxy : kx ≠ ky := by
      rintro rfl
      exact hne (blockWalk_trans hxs (blockWalk_symm hys))
    have h2 := two_le_indegree_of_ne hN hxy (hxt.trans hyt.symm)
    exact not_isBridge_of_two_le_indegree hN h2 hkx

omit [Fintype V] [Fintype E] in
/-- **No wedge path between taxa of `Y` includes `h`** when no taxon of `Y` is below `h` (TOB-QMC, proof of
Lemma 4, line 554 of v5). -/
theorem target_ne_of_mem_wedgeArcs {Y : Set X} {f : E} (hf : f ∈ N.wedgeArcs Y)
    (hno : ∀ a ∈ Y, ¬ N.graph.Reaches h (N.leaf a)) : N.graph.target f ≠ h := by
  obtain ⟨z, hz, hzr⟩ := wedgeArcs_subset_ancestralArcs hf
  exact fun heq => hno z hz (heq ▸ hzr)

/-- **The order along the single path gives the split** (TOB-QMC, proof of Lemma 4, lines 554–555 of
v5). Four taxa in distinct blocks, none below `h`. No wedge path includes `h`, so the arcs of the blob in
the subnetwork are on the single path through `pL` and `pR`, by the uniqueness of wedge paths
(`BlobCycle.mem_of_arc`). The attachments are ordered along it. When two of them are on `pL`, let `x₁`, `x₂`
be the taxa of the two lowest, with `x₂` the higher, and let `e` be the arc of `pL` into `b x₂`: it is on the
path between the second attachment of the order and the third. Below `e` are `x₁` and `x₂` only, and `e` is
the only arc of the subnetwork crossing what is below `e`. -/
theorem BlobCycle.exists_cut_of_left (hN : N.IsPhylogenetic) (hLevel : IsLevelOne N)
    (hh₂ : 2 ≤ N.graph.indegree h) {T : V} {k₁ k₂ : E} {pL pR : List E}
    (C : BlobCycle N v h T k₁ k₂ pL pR) {Y : Finset X} (hY : Y.card = 4) {b : X → V}
    (hb : ∀ x, IsAttachment N v x (b x)) (hx : ∀ x, ¬ SameBlob N v (N.leaf x))
    (hinj : Set.InjOn b (Y : Set X)) (hbh : ∀ x ∈ Y, b x ≠ h)
    (hno : ∀ a ∈ Y, ¬ N.graph.Reaches h (N.leaf a))
    (h2 : 2 ≤ (Y.filter fun x => b x ∈ pL.map N.graph.target).card) :
    ∃ P : Finset X, P ⊆ Y ∧ P.card = 2 ∧ N.HasWedgeCutSplit (Y : Set X) (P : Set X) := by
  have hA := hN.acyclic
  set F := Y.filter fun x => b x ∈ pL.map N.graph.target with hF
  have hFmem : ∀ {x}, x ∈ F ↔ x ∈ Y ∧ b x ∈ pL.map N.graph.target := by
    intro x
    rw [hF, Finset.mem_filter]
  -- the lowest attachment in a nonempty set of taxa
  have hlow : ∀ G : Finset X, G.Nonempty →
      ∃ x ∈ G, ∀ z ∈ G, ¬ Relation.TransGen N.graph.Adj (b x) (b z) := by
    intro G hG
    obtain ⟨x₀, hx₀⟩ := hG
    obtain ⟨u, ⟨x, hx', rfl⟩, hmin⟩ :=
      exists_sink hN (S := b '' (G : Set X)) ⟨_, x₀, Finset.mem_coe.mpr hx₀, rfl⟩
    exact ⟨x, Finset.mem_coe.mp hx', fun z hz => hmin _ ⟨z, Finset.mem_coe.mpr hz, rfl⟩⟩
  obtain ⟨x₁, hx₁, hmin₁⟩ := hlow F (Finset.card_pos.mp (by omega))
  obtain ⟨x₂, hx₂', hmin₂⟩ := hlow (F.erase x₁) (by
    rw [← Finset.card_pos, Finset.card_erase_of_mem hx₁]
    omega)
  obtain ⟨hne, hx₂⟩ := Finset.mem_erase.mp hx₂'
  obtain ⟨hx₁Y, hx₁L⟩ := hFmem.mp hx₁
  obtain ⟨hx₂Y, hx₂L⟩ := hFmem.mp hx₂
  obtain ⟨e, he, hte⟩ := List.mem_map.mp hx₂L
  have hbe : SameBlob N v (N.graph.target e) := hte ▸ (hb x₂).1
  -- a taxon attached on `pL` is below its attachment
  have hdown : ∀ {x}, b x ∈ pL.map N.graph.target → N.graph.Reaches (b x) (N.leaf x) := by
    intro x hm
    rcases (hb x).reaches_or_top hN (hx x) with h' | ⟨htop, -⟩
    · exact h'
    · have hbT : T = b x := eq_of_reaches_of_reaches hA (C.left.reaches_of_mem_map hm).1 (htop T C.top)
      exact absurd hm (hbT ▸ C.left.start_notMem hA)
  have htrans : ∀ {a c : V}, N.graph.Reaches a c → a ≠ c → Relation.TransGen N.graph.Adj a c := by
    intro a c hac hne
    rcases Relation.reflTransGen_iff_eq_or_transGen.mp hac with h' | h'
    · exact absurd h'.symm hne
    · exact h'
  have hne_b : b x₂ ≠ b x₁ := fun hc => hne (hinj (Finset.mem_coe.mpr hx₂Y) (Finset.mem_coe.mpr hx₁Y) hc)
  -- `x₁` is below the attachment of `x₂`
  have h21 : N.graph.Reaches (b x₂) (b x₁) := by
    rcases C.left.total (List.mem_cons_of_mem _ hx₂L) (List.mem_cons_of_mem _ hx₁L) with h' | h'
    · exact h'
    · exact absurd (htrans h' hne_b.symm) (hmin₁ x₂ hx₂)
  -- the taxa below `e` are `x₁` and `x₂`
  have hbelow : ∀ z ∈ Y, N.graph.Reaches (N.graph.target e) (N.leaf z) ↔ z = x₁ ∨ z = x₂ := by
    intro z hz
    constructor
    · intro hr
      rw [hte] at hr
      by_contra hcon
      push Not at hcon
      have hzz : N.graph.Reaches (b x₂) (b z) := (hb z).reaches_of_reaches hN (hx z) (hb x₂).1 hr
      have hnez : b x₂ ≠ b z := fun hc =>
        hcon.2 (hinj (Finset.mem_coe.mpr hz) (Finset.mem_coe.mpr hx₂Y) hc.symm)
      by_cases hzL : b z ∈ pL.map N.graph.target
      · exact hmin₂ z (Finset.mem_erase.mpr ⟨hcon.1, hFmem.mpr ⟨hz, hzL⟩⟩) (htrans hzz hnez)
      · rcases C.reaches_source hN hLevel hh₂ (hb z).1 (hbh z hz) with hr₁ | hr₂
        · rcases List.mem_cons.mp (C.mem_left_of_reaches hN hLevel hh₂ (hb z).1 hr₁) with h' | h'
          · exact C.left.start_notMem hA (by
              have : b x₂ = T := eq_of_reaches_of_reaches hA (h' ▸ hzz) (C.top_reaches _ (hb x₂).1)
              rw [← this]
              exact hx₂L)
          · exact hzL h'
        · rcases List.mem_cons.mp (C.swap.mem_left_of_reaches hN hLevel hh₂ (hb x₂).1
            (hzz.trans hr₂)) with h' | h'
          · exact C.left.start_notMem hA (h' ▸ hx₂L)
          · exact C.disjoint _ hx₂L h'
    · rw [hte]
      rintro (rfl | rfl)
      · exact h21.trans (hdown hx₁L)
      · exact hdown hx₂L
  -- `e` is the only arc of the subnetwork crossing what is below it
  set S : Set V := {w | N.graph.Reaches (N.graph.target e) w} with hSdef
  have hcross : ∀ f ∈ N.wedgeArcs (Y : Set X), N.graph.Crosses f S ↔ f = e := by
    intro f hf
    constructor
    · rintro (⟨hs, ht⟩ | ⟨ht, hs⟩)
      · exact absurd (Relation.ReflTransGen.tail hs ⟨f, rfl, rfl⟩) ht
      · by_contra hfe
        have htf : SameBlob N v (N.graph.target f) := sameBlob_trans hbe (sameBlob_of_entering hN ht hs)
        have hnb : ¬ IsBridge N f := fun hbr => not_reaches_source hN e
          ((Relation.ReflTransGen.trans ht (reaches_of_sameBlob hN hbr
            (sameBlob_trans (sameBlob_symm htf) C.top))).trans (C.left.reaches_of_mem he).1)
        have hsf : SameBlob N v (N.graph.source f) :=
          sameBlob_trans htf (sameBlob_symm (sameBlob_of_not_isBridge hnb))
        -- no wedge path includes `h`, so `f` is on the single path
        have hth : N.graph.target f ≠ h :=
          target_ne_of_mem_wedgeArcs hf fun a ha => hno a (Finset.mem_coe.mp ha)
        rcases C.mem_of_arc hN hLevel hh₂ hsf htf hth with hfL | hfR
        · obtain ⟨A, B, heq, hA', hB⟩ := C.left.split_of_mem he
          rw [heq, List.mem_append, List.mem_cons] at hfL
          rcases hfL with hfA | rfl | hfB
          · exact not_reaches_source hN e (Relation.ReflTransGen.trans ht (hA'.reaches_of_mem hfA).2)
          · exact hfe rfl
          · exact hs (hB.reaches_of_mem hfB).1
        · rcases List.mem_cons.mp (C.swap.mem_left_of_reaches hN hLevel hh₂ hbe
            (Relation.ReflTransGen.trans ht (C.right.reaches_of_mem hfR).2)) with h' | h'
          · exact C.left.start_notMem hA (h' ▸ List.mem_map_of_mem he)
          · exact C.disjoint _ (List.mem_map_of_mem he) h'
    · rintro rfl
      exact Or.inr ⟨.refl, not_reaches_source hN _⟩
  have hPcard : ({x₁, x₂} : Finset X).card = 2 := Finset.card_pair hne.symm
  have hPY : ({x₁, x₂} : Finset X) ⊆ Y := by
    intro z hz
    rcases Finset.mem_insert.mp hz with rfl | hz
    · exact hx₁Y
    · rw [Finset.mem_singleton.mp hz]
      exact hx₂Y
  have hPmem : ∀ z ∈ Y, N.leaf z ∈ S ↔ z ∈ ({x₁, x₂} : Finset X) := by
    intro z hz
    rw [Finset.mem_insert, Finset.mem_singleton]
    exact hbelow z hz
  refine ⟨{x₁, x₂}, hPY, hPcard, e, ?_, S, hcross, fun z hz => ?_⟩
  · -- `e` is in the subnetwork: a wedge path between the two sides crosses it
    obtain ⟨y, hy, hyP⟩ : ∃ y ∈ Y, y ∉ ({x₁, x₂} : Finset X) := by
      by_contra hcon
      push Not at hcon
      have := Finset.card_le_card (show Y ⊆ {x₁, x₂} from hcon)
      omega
    obtain ⟨u, p, q, hw⟩ := exists_isWedgePath_leaf hN x₂ y
    have hx₂y : x₂ ≠ y := fun hc => hyP (hc ▸ by simp)
    by_contra hno'
    have hmem : ∀ f, f ∈ p ∨ f ∈ q → ¬ N.graph.Crosses f S := by
      intro f hf hc
      have hfW : f ∈ N.wedgeArcs (Y : Set X) :=
        ⟨x₂, Finset.mem_coe.mpr hx₂Y, y, Finset.mem_coe.mpr hy, hx₂y, u, p, q, hw, hf⟩
      have hfe := (hcross f hfW).mp hc
      subst hfe
      exact hno' hfW
    exact hyP ((hPmem y hy).mp ((hw.mem_iff hmem).mp ((hPmem x₂ hx₂Y).mpr (by simp))))
  · rw [Finset.mem_coe]
    exact hPmem z (Finset.mem_coe.mp hz)

/-- **Lemma 4, `⇒`, distinct blocks and no taxon below `h`, on the subnetwork** (TOB-QMC, lines 551–556 of
v5). The attachments are distinct and on the single path; since at most one of them is the top, two of
them are on one side. -/
theorem exists_hasWedgeCutSplit (hN : N.IsPhylogenetic) (hBin : N.IsBinary) (hLevel : IsLevelOne N)
    (hh : SameBlob N v h) (hh₂ : 2 ≤ N.graph.indegree h) {Y : Finset X} (hY : Y.card = 4)
    (hdist : ∀ a ∈ Y, ∀ b ∈ Y, a ≠ b → ¬ BlockWalk N v (N.leaf a) (N.leaf b))
    (hno : ∀ a ∈ Y, ¬ N.graph.Reaches h (N.leaf a)) :
    ∃ P : Finset X, P ⊆ Y ∧ P.card = 2 ∧ N.HasWedgeCutSplit (Y : Set X) (P : Set X) := by
  obtain ⟨T, k₁, k₂, pL, pR, C⟩ := exists_blobCycle hN hBin hLevel hh hh₂
  have hx : ∀ x, ¬ SameBlob N v (N.leaf x) := leaf_not_sameBlob hN hh hh₂
  choose b hb using fun x => exists_isAttachment hN (hx x)
  have hbh : ∀ x ∈ Y, b x ≠ h := by
    intro x hxY heq
    rcases (hb x).reaches_or_top hN (hx x) with hr | ⟨htop, -⟩
    · exact hno x hxY (heq ▸ hr)
    · exact C.not_reaches_of_target₁ hN (heq ▸ htop _ (C.source₁_sameBlob hN))
  have hinj : Set.InjOn b (Y : Set X) := by
    intro x hxY y hyY heq
    by_contra hne
    exact hdist x (Finset.mem_coe.mp hxY) y (Finset.mem_coe.mp hyY) hne
      ((hb x).blockWalk_of_eq hN hBin hLevel hh₂ C (heq ▸ hb y))
  by_cases hL : 2 ≤ (Y.filter fun x => b x ∈ pL.map N.graph.target).card
  · exact C.exists_cut_of_left hN hLevel hh₂ hY hb hx hinj hbh hno hL
  by_cases hR : 2 ≤ (Y.filter fun x => b x ∈ pR.map N.graph.target).card
  · exact C.swap.exists_cut_of_left hN hLevel hh₂ hY hb hx hinj hbh hno hR
  exfalso
  have hT : (Y.filter fun x => b x = T).card ≤ 1 := by
    refine Finset.card_le_one.mpr fun x hx' y hy' => ?_
    obtain ⟨hxY, hxT⟩ := Finset.mem_filter.mp hx'
    obtain ⟨hyY, hyT⟩ := Finset.mem_filter.mp hy'
    exact hinj (Finset.mem_coe.mpr hxY) (Finset.mem_coe.mpr hyY) (hxT.trans hyT.symm)
  have hsub : Y ⊆ (Y.filter fun x => b x ∈ pL.map N.graph.target) ∪
      ((Y.filter fun x => b x ∈ pR.map N.graph.target) ∪ (Y.filter fun x => b x = T)) := by
    intro x hxY
    simp only [Finset.mem_union, Finset.mem_filter]
    have hm := C.mem_of_sameBlob hN hLevel hh₂ (hb x).1 (hbh x hxY)
    simp only [List.mem_cons] at hm
    tauto
  have h₁ := Finset.card_le_card hsub
  have h₂ := Finset.card_union_le (Y.filter fun x => b x ∈ pL.map N.graph.target)
    ((Y.filter fun x => b x ∈ pR.map N.graph.target) ∪ (Y.filter fun x => b x = T))
  have h₃ := Finset.card_union_le (Y.filter fun x => b x ∈ pR.map N.graph.target)
    (Y.filter fun x => b x = T)
  omega

end Forward

end TOBQMC.Level1
