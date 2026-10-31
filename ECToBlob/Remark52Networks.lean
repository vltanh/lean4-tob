module

public import ECToBlob.Section5

/-!
# ECToBlob Remark 5.2: the three networks of Figure 1

The rooted networks `N₀`, `N₁`, `N₂` of Figure 1 of ECToBlob, on the taxa `Fin 4`, with `0, 1, 2, 3` for the paper's
`a, b, c, d`.

* `N₀`: the root has children `a`, `b` and a vertex `w`, by an arc of length `t₀`; `w` has children `c`, `d`.
* `N₁`: the root has children `a`, `b`, and two parallel arcs, of lengths `t₁`, `t₂`, enter a vertex `w` with
  children `c`, `d`.
* `N₂`: the root has children `a`, `b` and a vertex `Y`, by an arc of length `t`; each of `c`, `d` has a reticulation as
  its parent, with parents `Y` and the root.

## Main results

* `isPhylogenetic_N₀`, `isPhylogenetic_N₁`, `isPhylogenetic_N₂`.
* `inducedCutSplit_N₀`, `hasCutSplit_N₀`: `N₀` has the cut-edge split `ab|cd`.
* `not_inducedCutSplit_N₁`, `not_inducedCutSplit_N₂`, `not_hasCutSplit_N₁`, `not_hasCutSplit_N₂`: `N₁` and `N₂` have
  no non-trivial cut-edge split.
* `not_blobDegreeAtMostThree_N₁`, `not_blobDegreeAtMostThree_N₂`: their blobs have a vertex of degree `> 3`.
-/

@[expose] public noncomputable section

open Phylogenetics Phylogenetics.RootedNetwork Finset
open scoped Classical

namespace ECToBlob.Remark52

/-! ### Concrete networks -/

section Generic

variable {V E X : Type*} [Fintype V] [Fintype E] [Fintype X]

/-- The laws of a phylogenetic network, from a rank function that increases along the arcs. -/
theorem isPhylogenetic_of_rank {N : RootedNetwork V E X} (rank : V → ℕ)
    (hrank : ∀ e, rank (N.graph.source e) < rank (N.graph.target e))
    (h0 : ∀ e, N.graph.target e ≠ N.root)
    (h1 : ∀ v, v ≠ N.root → ∃ e, N.graph.target e = v)
    (hinj : Function.Injective N.leaf)
    (hleaf : ∀ x, ∃ e, N.graph.target e = N.leaf x ∧ ∀ f, N.graph.target f = N.leaf x → f = e)
    (hs : ∀ x e, N.graph.source e ≠ N.leaf x)
    (hint : ∀ v, (∀ x, N.leaf x ≠ v) → ∃ e, N.graph.source e = v) : N.IsPhylogenetic := by
  have hreach : ∀ n v, rank v = n → N.graph.Reaches N.root v := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro v hv
      by_cases hvr : v = N.root
      · exact hvr ▸ .refl
      · obtain ⟨e, he⟩ := h1 v hvr
        have hlt := hrank e
        rw [he, hv] at hlt
        exact (ih _ hlt _ rfl).tail ⟨e, rfl, he⟩
  have hTrans : ∀ u v, Relation.TransGen N.graph.Adj u v → rank u < rank v := by
    intro u v h
    induction h with
    | single h =>
      obtain ⟨e, rfl, rfl⟩ := h
      exact hrank e
    | tail _ h ih =>
      obtain ⟨e, rfl, rfl⟩ := h
      exact ih.trans (hrank e)
  refine ⟨inferInstance, inferInstance, inferInstance, fun v h => lt_irrefl _ (hTrans _ _ h),
    fun v => hreach _ v rfl, ?_, ?_, hinj, ?_, ?_⟩
  · unfold DirectedMultigraph.indegree
    rw [Set.ncard_eq_zero (Set.toFinite _)]
    exact Set.eq_empty_of_forall_notMem fun e he => h0 e he
  · intro v hv
    obtain ⟨e, he⟩ := h1 v hv
    unfold DirectedMultigraph.indegree
    exact (Set.ncard_pos (Set.toFinite _)).2 ⟨e, he⟩
  · intro x
    obtain ⟨e, he, hu⟩ := hleaf x
    unfold DirectedMultigraph.indegree
    rw [Set.ncard_eq_one]
    exact ⟨e, Set.ext fun f => ⟨fun hf => hu f hf, fun hf => by rw [Set.mem_singleton_iff.1 hf]; exact he⟩⟩
  · intro v
    unfold DirectedMultigraph.outdegree
    rw [Set.ncard_eq_zero (Set.toFinite _)]
    constructor
    · intro h
      by_contra hne
      push Not at hne
      obtain ⟨e, he⟩ := hint v hne
      have : e ∈ {e | N.graph.source e = v} := he
      rw [h] at this
      exact this
    · rintro ⟨x, rfl⟩
      exact Set.eq_empty_of_forall_notMem fun e he => hs x e he

variable {N : RootedNetwork V E X}

omit [Fintype V] [Fintype E] in
/-- Paths from the root to the taxa, pairwise without common arcs: at least two arcs cross any vertex
set separating two taxa from two others. This is why `N₁`, `N₂` have no non-trivial cut edge. -/
theorem not_hasCutSplitOn_of_star [DecidableEq X] (hN : N.IsPhylogenetic) (π : X → Finset E)
    (hdis : ∀ x y, x ≠ y → Disjoint (π x) (π y))
    (hπ : ∀ (S : Set V) (x : X), (N.root ∈ S ↔ N.leaf x ∉ S) → ∃ f ∈ π x, N.graph.Crosses f S)
    {B : Finset X} (hB : B.card = 2) (hB' : Bᶜ.card = 2) :
    ¬ N.HasCutSplitOn Set.univ (B : Set X) := by
  rintro ⟨e, -, S, hS, hleaf⟩
  have hall : ∀ f, f ∈ N.ancestralArcs Set.univ := fun f => by
    obtain ⟨x, hx⟩ := exists_reaches_leaf hN (N.graph.target f)
    exact ⟨x, Set.mem_univ x, hx⟩
  have hone : ∀ x y, x ≠ y → (N.root ∈ S ↔ N.leaf x ∉ S) → (N.root ∈ S ↔ N.leaf y ∉ S) → False := by
    intro x y hxy hx hy
    obtain ⟨f, hf, hfc⟩ := hπ S x hx
    obtain ⟨g, hg, hgc⟩ := hπ S y hy
    have h₁ := (hS f (hall f)).1 hfc
    have h₂ := (hS g (hall g)).1 hgc
    exact disjoint_left.1 (hdis x y hxy) hf (by rw [h₁, ← h₂]; exact hg)
  by_cases hr : N.root ∈ S
  · obtain ⟨x, y, hxy, hc⟩ := card_eq_two.1 hB'
    have hnot : ∀ z ∈ Bᶜ, N.leaf z ∉ S := fun z hz h =>
      (mem_compl.1 hz) (by simpa using (hleaf z (Set.mem_univ z)).1 h)
    refine hone x y hxy ?_ ?_
    · exact ⟨fun _ => hnot x (by simp [hc]), fun _ => hr⟩
    · exact ⟨fun _ => hnot y (by simp [hc]), fun _ => hr⟩
  · obtain ⟨x, y, hxy, hc⟩ := card_eq_two.1 hB
    have hin : ∀ z ∈ B, N.leaf z ∈ S := fun z hz =>
      (hleaf z (Set.mem_univ z)).2 (by simpa using hz)
    refine hone x y hxy ?_ ?_
    · exact ⟨fun h => absurd h hr, fun h => absurd (hin x (by simp [hc])) h⟩
    · exact ⟨fun h => absurd h hr, fun h => absurd (hin y (by simp [hc])) h⟩

end Generic

/-- A cherry of a quartet tree on `Fin 4` and its complement have two taxa each. -/
theorem card_compl_of_mem_quartet {s : QuartetTree (Fin 4)} {B : Finset (Fin 4)} (hB : B ∈ s.val) :
    B.card = 2 ∧ Bᶜ.card = 2 := by
  have h := s.property.2.1 B hB
  refine ⟨h, ?_⟩
  rw [card_compl, h]
  rfl

/-- A quartet tree on `Fin 4` has all the taxa. -/
theorem taxa_eq_univ (s : QuartetTree (Fin 4)) : s.taxa = univ :=
  eq_univ_of_card _ (by rw [QuartetTree.card_taxa]; rfl)

/-- A star of paths excludes the induced cut-edge splits on `Fin 4`. -/
theorem not_inducedCutSplit_of_star {V E : Type*} [Fintype V] [Fintype E]
    {N : RootedNetwork V E (Fin 4)} (hN : N.IsPhylogenetic) (π : Fin 4 → Finset E)
    (hdis : ∀ x y, x ≠ y → Disjoint (π x) (π y))
    (hπ : ∀ (S : Set V) (x : Fin 4), (N.root ∈ S ↔ N.leaf x ∉ S) → ∃ f ∈ π x, N.graph.Crosses f S)
    (s : QuartetTree (Fin 4)) : ¬ InducedCutSplit N s := by
  rintro ⟨B, hB, hcut⟩
  obtain ⟨h₁, h₂⟩ := card_compl_of_mem_quartet hB
  rw [taxa_eq_univ, coe_univ] at hcut
  exact not_hasCutSplitOn_of_star hN π hdis hπ h₁ h₂ hcut

/-! ### The vertices and arcs -/

/-- The vertices of `N₀` and `N₁`. -/
inductive V₀ | r | w | a | b | c | d
  deriving DecidableEq

instance : Fintype V₀ := ⟨{.r, .w, .a, .b, .c, .d}, fun x => by cases x <;> decide⟩

/-- The arcs of `N₀`, named by their targets. -/
inductive E₀ | a | b | w | c | d
  deriving DecidableEq

instance : Fintype E₀ := ⟨{.a, .b, .w, .c, .d}, fun x => by cases x <;> decide⟩

/-- The arcs of `N₁`: `e₁`, `e₂` are the parallel arcs into `w`. -/
inductive E₁ | a | b | e₁ | e₂ | c | d
  deriving DecidableEq

instance : Fintype E₁ := ⟨{.a, .b, .e₁, .e₂, .c, .d}, fun x => by cases x <;> decide⟩

/-- The vertices of `N₂`: `hc`, `hd` are the reticulations above `c`, `d`. -/
inductive V₂ | r | Y | hc | hd | a | b | c | d
  deriving DecidableEq

instance : Fintype V₂ := ⟨{.r, .Y, .hc, .hd, .a, .b, .c, .d}, fun x => by cases x <;> decide⟩

/-- The arcs of `N₂`: `Y` enters `Y`; `yc`, `rc` enter `hc` from `Y` and the root; `yd`, `rd` enter `hd`; the
others enter the leaves. -/
inductive E₂ | a | b | Y | yc | rc | yd | rd | c | d
  deriving DecidableEq

instance : Fintype E₂ := ⟨{.a, .b, .Y, .yc, .rc, .yd, .rd, .c, .d}, fun x => by cases x <;> decide⟩

/-- The network `N₀` of Figure 1. -/
def N₀ : RootedNetwork V₀ E₀ (Fin 4) where
  graph :=
    { source := fun
        | .a => .r | .b => .r | .w => .r | .c => .w | .d => .w
      target := fun
        | .a => .a | .b => .b | .w => .w | .c => .c | .d => .d }
  root := .r
  leaf := ![.a, .b, .c, .d]

/-- The network `N₁` of Figure 1. -/
def N₁ : RootedNetwork V₀ E₁ (Fin 4) where
  graph :=
    { source := fun
        | .a => .r | .b => .r | .e₁ => .r | .e₂ => .r | .c => .w | .d => .w
      target := fun
        | .a => .a | .b => .b | .e₁ => .w | .e₂ => .w | .c => .c | .d => .d }
  root := .r
  leaf := ![.a, .b, .c, .d]

/-- The network `N₂` of Figure 1. -/
def N₂ : RootedNetwork V₂ E₂ (Fin 4) where
  graph :=
    { source := fun
        | .a => .r | .b => .r | .Y => .r | .yc => .Y | .rc => .r | .yd => .Y | .rd => .r
        | .c => .hc | .d => .hd
      target := fun
        | .a => .a | .b => .b | .Y => .Y | .yc => .hc | .rc => .hc | .yd => .hd | .rd => .hd
        | .c => .c | .d => .d }
  root := .r
  leaf := ![.a, .b, .c, .d]

/-- `N₀` is a phylogenetic network. -/
theorem isPhylogenetic_N₀ : N₀.IsPhylogenetic := by
  refine isPhylogenetic_of_rank (fun | .r => 0 | .w => 1 | _ => 2) (fun e => by cases e <;> decide)
    (fun e => by cases e <;> decide) (fun v hv => ?_) ?_ (fun x => ?_) (fun x e => ?_) (fun v hv => ?_)
  · cases v
    · exact absurd rfl hv
    · exact ⟨.w, rfl⟩
    · exact ⟨.a, rfl⟩
    · exact ⟨.b, rfl⟩
    · exact ⟨.c, rfl⟩
    · exact ⟨.d, rfl⟩
  · decide
  · fin_cases x
    · exact ⟨.a, rfl, fun f hf => by cases f <;> first | rfl | exact absurd hf (by decide)⟩
    · exact ⟨.b, rfl, fun f hf => by cases f <;> first | rfl | exact absurd hf (by decide)⟩
    · exact ⟨.c, rfl, fun f hf => by cases f <;> first | rfl | exact absurd hf (by decide)⟩
    · exact ⟨.d, rfl, fun f hf => by cases f <;> first | rfl | exact absurd hf (by decide)⟩
  · fin_cases x <;> cases e <;> decide
  · cases v
    · exact ⟨.a, rfl⟩
    · exact ⟨.c, rfl⟩
    · exact absurd rfl (hv 0)
    · exact absurd rfl (hv 1)
    · exact absurd rfl (hv 2)
    · exact absurd rfl (hv 3)

/-- `N₁` is a phylogenetic network. -/
theorem isPhylogenetic_N₁ : N₁.IsPhylogenetic := by
  refine isPhylogenetic_of_rank (fun | .r => 0 | .w => 1 | _ => 2) (fun e => by cases e <;> decide)
    (fun e => by cases e <;> decide) (fun v hv => ?_) ?_ (fun x => ?_) (fun x e => ?_) (fun v hv => ?_)
  · cases v
    · exact absurd rfl hv
    · exact ⟨.e₁, rfl⟩
    · exact ⟨.a, rfl⟩
    · exact ⟨.b, rfl⟩
    · exact ⟨.c, rfl⟩
    · exact ⟨.d, rfl⟩
  · decide
  · fin_cases x
    · exact ⟨.a, rfl, fun f hf => by cases f <;> first | rfl | exact absurd hf (by decide)⟩
    · exact ⟨.b, rfl, fun f hf => by cases f <;> first | rfl | exact absurd hf (by decide)⟩
    · exact ⟨.c, rfl, fun f hf => by cases f <;> first | rfl | exact absurd hf (by decide)⟩
    · exact ⟨.d, rfl, fun f hf => by cases f <;> first | rfl | exact absurd hf (by decide)⟩
  · fin_cases x <;> cases e <;> decide
  · cases v
    · exact ⟨.a, rfl⟩
    · exact ⟨.c, rfl⟩
    · exact absurd rfl (hv 0)
    · exact absurd rfl (hv 1)
    · exact absurd rfl (hv 2)
    · exact absurd rfl (hv 3)

/-- `N₂` is a phylogenetic network. -/
theorem isPhylogenetic_N₂ : N₂.IsPhylogenetic := by
  refine isPhylogenetic_of_rank (fun | .r => 0 | .Y => 1 | .hc => 2 | .hd => 2 | _ => 3)
    (fun e => by cases e <;> decide)
    (fun e => by cases e <;> decide) (fun v hv => ?_) ?_ (fun x => ?_) (fun x e => ?_) (fun v hv => ?_)
  · cases v
    · exact absurd rfl hv
    · exact ⟨.Y, rfl⟩
    · exact ⟨.yc, rfl⟩
    · exact ⟨.yd, rfl⟩
    · exact ⟨.a, rfl⟩
    · exact ⟨.b, rfl⟩
    · exact ⟨.c, rfl⟩
    · exact ⟨.d, rfl⟩
  · decide
  · fin_cases x
    · exact ⟨.a, rfl, fun f hf => by cases f <;> first | rfl | exact absurd hf (by decide)⟩
    · exact ⟨.b, rfl, fun f hf => by cases f <;> first | rfl | exact absurd hf (by decide)⟩
    · exact ⟨.c, rfl, fun f hf => by cases f <;> first | rfl | exact absurd hf (by decide)⟩
    · exact ⟨.d, rfl, fun f hf => by cases f <;> first | rfl | exact absurd hf (by decide)⟩
  · fin_cases x <;> cases e <;> decide
  · cases v
    · exact ⟨.a, rfl⟩
    · exact ⟨.yc, rfl⟩
    · exact ⟨.c, rfl⟩
    · exact ⟨.d, rfl⟩
    · exact absurd rfl (hv 0)
    · exact absurd rfl (hv 1)
    · exact absurd rfl (hv 2)
    · exact absurd rfl (hv 3)

/-! ### The quartet trees -/

/-- The quartet tree `ab|cd`. -/
def abcd : QuartetTree (Fin 4) := ⟨{{0, 1}, {2, 3}}, by unfold IsQuartetTree; decide⟩

/-- The quartet tree `ac|bd`. -/
def acbd : QuartetTree (Fin 4) := ⟨{{0, 2}, {1, 3}}, by unfold IsQuartetTree; decide⟩

/-- The quartet tree `ad|bc`. -/
def adbc : QuartetTree (Fin 4) := ⟨{{0, 3}, {1, 2}}, by unfold IsQuartetTree; decide⟩

/-! ### Cut edges -/

section Cuts

variable {V E : Type*} {G : DirectedMultigraph V E} {S : Set V}

/-- An arc with one end in `S`. -/
theorem crosses_of_iff {e : E} (h : G.source e ∈ S ↔ G.target e ∉ S) : G.Crosses e S := by
  unfold DirectedMultigraph.Crosses
  tauto

/-- One arc of a path of two arcs with its ends separated by `S` crosses it. -/
theorem crosses_or_crosses {e f : E} (hj : G.target e = G.source f)
    (h : G.source e ∈ S ↔ G.target f ∉ S) : G.Crosses e S ∨ G.Crosses f S := by
  unfold DirectedMultigraph.Crosses
  rw [hj]
  tauto

end Cuts

/-- The arc-disjoint paths from the root to the taxa in `N₁`. -/
def star₁ : Fin 4 → Finset E₁ := ![{.a}, {.b}, {.e₁, .c}, {.e₂, .d}]

/-- The arc-disjoint paths from the root to the taxa in `N₂`. -/
def star₂ : Fin 4 → Finset E₂ := ![{.a}, {.b}, {.rc, .c}, {.rd, .d}]

theorem disjoint_star₁ (x y : Fin 4) (h : x ≠ y) : Disjoint (star₁ x) (star₁ y) := by
  revert x y
  decide

theorem disjoint_star₂ (x y : Fin 4) (h : x ≠ y) : Disjoint (star₂ x) (star₂ y) := by
  revert x y
  decide

theorem crosses_star₁ (S : Set V₀) (x : Fin 4) (h : N₁.root ∈ S ↔ N₁.leaf x ∉ S) :
    ∃ f ∈ star₁ x, N₁.graph.Crosses f S := by
  fin_cases x
  · exact ⟨.a, by decide, crosses_of_iff h⟩
  · exact ⟨.b, by decide, crosses_of_iff h⟩
  · rcases crosses_or_crosses (G := N₁.graph) (S := S) (e := .e₁) (f := .c) rfl h with h' | h'
    · exact ⟨.e₁, by decide, h'⟩
    · exact ⟨.c, by decide, h'⟩
  · rcases crosses_or_crosses (G := N₁.graph) (S := S) (e := .e₂) (f := .d) rfl h with h' | h'
    · exact ⟨.e₂, by decide, h'⟩
    · exact ⟨.d, by decide, h'⟩

theorem crosses_star₂ (S : Set V₂) (x : Fin 4) (h : N₂.root ∈ S ↔ N₂.leaf x ∉ S) :
    ∃ f ∈ star₂ x, N₂.graph.Crosses f S := by
  fin_cases x
  · exact ⟨.a, by decide, crosses_of_iff h⟩
  · exact ⟨.b, by decide, crosses_of_iff h⟩
  · rcases crosses_or_crosses (G := N₂.graph) (S := S) (e := .rc) (f := .c) rfl h with h' | h'
    · exact ⟨.rc, by decide, h'⟩
    · exact ⟨.c, by decide, h'⟩
  · rcases crosses_or_crosses (G := N₂.graph) (S := S) (e := .rd) (f := .d) rfl h with h' | h'
    · exact ⟨.rd, by decide, h'⟩
    · exact ⟨.d, by decide, h'⟩

/-- **`N₁` has no non-trivial cut-edge split** (Figure 1), on any quartet. -/
theorem not_inducedCutSplit_N₁ (s : QuartetTree (Fin 4)) : ¬ InducedCutSplit N₁ s :=
  not_inducedCutSplit_of_star isPhylogenetic_N₁ star₁ disjoint_star₁ crosses_star₁ s

/-- **`N₂` has no non-trivial cut-edge split** (Figure 1), on any quartet. -/
theorem not_inducedCutSplit_N₂ (s : QuartetTree (Fin 4)) : ¬ InducedCutSplit N₂ s :=
  not_inducedCutSplit_of_star isPhylogenetic_N₂ star₂ disjoint_star₂ crosses_star₂ s

/-- `N₁` has no cut edge with two taxa on each side. -/
theorem not_hasCutSplit_N₁ {B : Finset (Fin 4)} (hB : B.card = 2) : ¬ N₁.HasCutSplit (B : Set (Fin 4)) := by
  rw [hasCutSplit_iff_hasCutSplitOn_univ isPhylogenetic_N₁]
  exact not_hasCutSplitOn_of_star isPhylogenetic_N₁ star₁ disjoint_star₁ crosses_star₁ hB
    (by rw [card_compl, hB]; rfl)

/-- `N₂` has no cut edge with two taxa on each side. -/
theorem not_hasCutSplit_N₂ {B : Finset (Fin 4)} (hB : B.card = 2) : ¬ N₂.HasCutSplit (B : Set (Fin 4)) := by
  rw [hasCutSplit_iff_hasCutSplitOn_univ isPhylogenetic_N₂]
  exact not_hasCutSplitOn_of_star isPhylogenetic_N₂ star₂ disjoint_star₂ crosses_star₂ hB
    (by rw [card_compl, hB]; rfl)

/-- `N₀` has a cut edge with `a, b` on one side and `c, d` on the other. -/
theorem hasCutSplit_N₀ : N₀.HasCutSplit (({0, 1} : Finset (Fin 4)) : Set (Fin 4)) := by
  refine ⟨.w, {v | v = .r ∨ v = .a ∨ v = .b}, fun f => ?_, ?_⟩
  · cases f <;> simp [DirectedMultigraph.Crosses, N₀]
  · ext x
    fin_cases x <;> simp [N₀]

/-- **`N₀` has the cut-edge split `ab|cd`** (Figure 1). -/
theorem inducedCutSplit_N₀ : InducedCutSplit N₀ abcd := by
  refine ⟨{0, 1}, by simp [abcd], ?_⟩
  have := (hasCutSplit_iff_hasCutSplitOn_univ isPhylogenetic_N₀ _).1 hasCutSplit_N₀
  rwa [taxa_eq_univ, coe_univ]

/-! ### The degree of the vertices of the blobs -/

/-- An arc parallel to another is not a bridge. -/
theorem not_isBridge_e₁ : ¬ TOBQMC.IsBridge N₁ .e₁ := by
  rintro ⟨S, hS⟩
  have h₁ := (hS .e₁).2 rfl
  have h₂ := (hS .e₂).1 h₁
  cases h₂

/-- The arc into `Y` is on a cycle. -/
theorem not_isBridge_Y : ¬ TOBQMC.IsBridge N₂ .Y := by
  rintro ⟨S, hS⟩
  have h₁ := (hS .Y).2 rfl
  have h₂ : ¬ N₂.graph.Crosses .yc S := fun h => by cases (hS .yc).1 h
  have h₃ : ¬ N₂.graph.Crosses .rc S := fun h => by cases (hS .rc).1 h
  unfold DirectedMultigraph.Crosses at h₁ h₂ h₃
  simp only [N₂] at h₁ h₂ h₃
  tauto

/-- **The blob of `N₁` has a vertex of degree `> 3`**: the hypothesis of Proposition 5.1 fails. -/
theorem not_blobDegreeAtMostThree_N₁ : ¬ BlobDegreeAtMostThree N₁ := by
  intro h
  have hw := h .w .r (by decide) (.single ⟨.e₁, not_isBridge_e₁, Or.inr ⟨rfl, rfl⟩⟩)
  have hin : N₁.graph.indegree .w = 2 := by
    have : {e | N₁.graph.target e = V₀.w} = (({.e₁, .e₂} : Finset E₁) : Set E₁) := by
      ext e
      cases e <;> simp [N₁]
    unfold DirectedMultigraph.indegree
    rw [this, Set.ncard_coe_finset]
    rfl
  have hout : N₁.graph.outdegree .w = 2 := by
    have : {e | N₁.graph.source e = V₀.w} = (({.c, .d} : Finset E₁) : Set E₁) := by
      ext e
      cases e <;> simp [N₁]
    unfold DirectedMultigraph.outdegree
    rw [this, Set.ncard_coe_finset]
    rfl
  omega

/-- **The blob of `N₂` has a vertex of degree `> 3`**: the hypothesis of Proposition 5.1 fails. -/
theorem not_blobDegreeAtMostThree_N₂ : ¬ BlobDegreeAtMostThree N₂ := by
  intro h
  have hw := h .r .Y (by decide) (.single ⟨.Y, not_isBridge_Y, Or.inl ⟨rfl, rfl⟩⟩)
  have hout : N₂.graph.outdegree .r = 5 := by
    have : {e | N₂.graph.source e = V₂.r} = (({.a, .b, .Y, .rc, .rd} : Finset E₂) : Set E₂) := by
      ext e
      cases e <;> simp [N₂]
    unfold DirectedMultigraph.outdegree
    rw [this, Set.ncard_coe_finset]
    rfl
  omega

end ECToBlob.Remark52
