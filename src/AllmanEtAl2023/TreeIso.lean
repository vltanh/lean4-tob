module

public import AllmanEtAl2023.TrdTree
public import External.SempleSteel2003.SplitsEquivalence

/-!
# The splits-equivalence theorem, on labelled graphs

A labelled tree whose labelled nodes have degree 1 and whose other nodes have degree at least 3 is determined by its splits, up to an isomorphism respecting the labels: `LabelledGraph.isIso_of_splits_eq`. This is
the uniqueness in Buneman's theorem, `SempleSteel2003.xTree_unique` (Semple and Steel 2003, Theorem 3.1.4). A reduced tree is an `X`-tree, and its sides of edges with a taxon on each side are the sides of the
splits of the `X`-tree, since each side of an edge of it has a taxon.
-/

@[expose] public noncomputable section

open Phylogenetics Finset
open scoped Classical

namespace AllmanEtAl2023.LabelledGraph

variable {W W' X : Type*} [Fintype X] [DecidableEq X] {T : LabelledGraph W X} {T' : LabelledGraph W' X}

omit [Fintype X] [DecidableEq X] in
/-- A reduced tree is an `X`-tree. -/
theorem IsReducedTree.isXTree (hT : T.IsReducedTree) : SempleSteel2003.IsXTree T.graph T.leaf :=
  ⟨hT.isTree, fun v hv => by
    by_contra hn
    have := hT.degree v fun x hx => hn ⟨x, hx⟩
    omega⟩

/-- The sides of the splits of the `X`-tree are its sides of edges with a taxon on each side. -/
theorem splitSides_eq (hT : T.IsReducedTree) :
    SempleSteel2003.splitSides T.graph T.leaf = {A | ∃ B ∈ T.splits, A = (B : Set X)} := by
  have := hT.finite
  have hX := hT.isXTree
  ext A
  constructor
  · rintro ⟨e, he, x, rfl⟩
    induction e using Sym2.ind with
    | _ u w =>
    have hadj : T.graph.Adj u w := he
    obtain ⟨y, hy⟩ := SempleSteel2003.exists_label_branch hX hadj
    obtain ⟨z, hz⟩ := SempleSteel2003.exists_label_branch hX hadj.symm
    have hsym : s(w, u) = s(u, w) := Sym2.eq_swap
    rw [hsym] at hz
    have hne : ¬ (T.graph.deleteEdges {s(u, w)}).Reachable u w :=
      SimpleGraph.isAcyclic_iff_forall_adj_isBridge.mp hT.isTree.isAcyclic hadj
    rcases SempleSteel2003.reachable_of_three hX.isTree he (T.leaf x) u w with h | h | h
    · refine ⟨Finset.univ.filter fun t => (T.graph.deleteEdges {s(u, w)}).Reachable u (T.leaf t), ?_, ?_⟩
      · refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨x, by simpa using h.symm⟩, ⟨y, ?_⟩, u, w, hadj, fun t => by simp⟩
        simp only [Finset.mem_compl, Finset.mem_filter, Finset.mem_univ, true_and]
        exact fun hu => hne (hu.trans hy.symm)
      · ext t
        simp only [SempleSteel2003.edgeSide, Set.mem_ofPred_eq, Finset.coe_filter, Finset.mem_univ, true_and]
        exact ⟨fun ht => h.symm.trans ht, fun ht => h.trans ht⟩
    · refine ⟨Finset.univ.filter fun t => (T.graph.deleteEdges {s(u, w)}).Reachable w (T.leaf t), ?_, ?_⟩
      · refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨x, by simpa using h.symm⟩, ⟨z, ?_⟩, w, u, hadj.symm, fun t => ?_⟩
        · simp only [Finset.mem_compl, Finset.mem_filter, Finset.mem_univ, true_and]
          exact fun hu => hne (hz.trans hu.symm)
        · simp [hsym]
      · ext t
        simp only [SempleSteel2003.edgeSide, Set.mem_ofPred_eq, Finset.coe_filter, Finset.mem_univ, true_and]
        exact ⟨fun ht => h.symm.trans ht, fun ht => h.trans ht⟩
    · exact absurd h hne
  · rintro ⟨B, hB, rfl⟩
    obtain ⟨-, ⟨x, hx⟩, -, u, w, hadj, hside⟩ := Finset.mem_filter.mp hB
    refine ⟨s(u, w), hadj, x, ?_⟩
    ext t
    have hxu := (hside x).mp (Finset.mem_coe.mpr hx)
    simp only [SempleSteel2003.edgeSide, Set.mem_ofPred_eq, Finset.mem_coe]
    rw [show t ∈ B ↔ _ from (hside t)]
    exact ⟨fun ht => hxu.symm.trans ht, fun ht => hxu.trans ht⟩

/-- **The splits-equivalence theorem** (Buneman; Semple and Steel 2003, Theorem 3.1.4), on labelled graphs. Two labelled trees whose labelled nodes have degree 1, whose other nodes have degree at least 3, and with the same splits, are
isomorphic by a map respecting the labels. -/
theorem isIso_of_splits_eq [Nonempty X] (hT : T.IsReducedTree) (hT' : T'.IsReducedTree) (hS : T.splits = T'.splits) : T.IsIso T' := by
  have := hT.finite
  have := hT'.finite
  refine SempleSteel2003.xTree_unique hT.isXTree hT'.isXTree ?_
  rw [splitSides_eq hT, splitSides_eq hT', hS]

end AllmanEtAl2023.LabelledGraph
