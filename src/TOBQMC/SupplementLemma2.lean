module

public import Basic.FinNetwork
public import Basic.Level1Blobs
public import Mathlib.Tactic.FinCases

/-!
# TOB-QMC supplement, Lemma 2: the converse is false

E23 of the report. The supplement's text, lines 382-383: "Let `N` be a network and `T_N` be its tree of blobs. For any subset `Y` of four
taxa, `T_N|Y` is a quartet tree, if and only if, `N|Y` is not a 4-blob."

`N|Y` is the induced subnetwork on `Y` (the supplement, lines 129-134), so "`N|Y` is not a 4-blob" is `IsTreelike N Y`, and the direction
from it to a quartet tree of `T_N` fails, already on a binary level-1 network:

* `net`, on the taxa `e, a, b, c, d = 0, …, 4`, with the arcs `s→e, s→r, r→u, u→v, v→h, r→w, w→h, u→a, v→b, w→c, h→d`. It is a 5-cycle
  `r, u, v, h, w` with a taxon at each of its vertices but `r`, and `e` at `r` through `s`.
* Its tree of blobs is a star (`mem_treeOfBlobs_iff`), but with `h` and `d` gone the arc `r→u` is a cut edge of the network induced on
  `{e, a, b, c}`, with the split `ab|ce` (`isTreelike_eab`).

The forward direction is `TOBQMC.lemma2`.

The printed proof of the converse is by contradiction from "`N|Y` is a 4-blob", which it glosses as "there exists a blob `B` in `N` such
that each taxon in `Y` is separated from the other three taxa in `Y` by a cut edge incident to `B`", and it ends with `T_N|Y` a star: this
is the contrapositive of the forward direction. That gloss is about the blob of `N`, and not about `N|Y`. Under it the sets of this
counterexample are 4-blobs, and the printed equivalence is the definition of `T_N`; but the supplement's `N|Y` is the induced subnetwork,
and its use at lines 503-505 and 542-543 needs that.
-/

@[expose] public noncomputable section

open Phylogenetics Phylogenetics.RootedNetwork Finset
open scoped Classical

namespace TOBQMC.SupplementLemma2

open ECToBlob.FinNetwork ECToBlob.FalseEdge ECToBlob.Coarsening

/-- The tails of the arcs `s→e, s→r, r→u, u→v, v→h, r→w, w→h, u→a, v→b, w→c, h→d`, with the taxa `e, a, b, c, d = 0, …, 4`, and
`h, v, w, u, r, s = 5, …, 10`. -/
def src : Fin 11 → Fin 11 := ![10, 10, 9, 8, 6, 9, 7, 8, 6, 7, 5]

/-- The heads of the arcs. -/
def tgt : Fin 11 → Fin 11 := ![0, 9, 8, 6, 5, 7, 5, 1, 2, 3, 4]

/-- The taxa, as vertices. -/
def lf : Fin 5 → Fin 11 := ![0, 1, 2, 3, 4]

/-- What each vertex reaches. -/
def desc : Fin 11 → Finset (Fin 11) :=
  ![{0}, {1}, {2}, {3}, {4}, {4, 5}, {2, 4, 5, 6}, {3, 4, 5, 7}, {1, 2, 4, 5, 6, 8}, {1, 2, 3, 4, 5, 6, 7, 8, 9},
    {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10}]

/-- What the root reaches off each arc. -/
def avoid : Fin 11 → Finset (Fin 11) :=
  ![{1, 2, 3, 4, 5, 6, 7, 8, 9, 10}, {0, 10}, {0, 3, 4, 5, 7, 9, 10}, {0, 1, 3, 4, 5, 7, 8, 9, 10},
    {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10}, {0, 1, 2, 4, 5, 6, 8, 9, 10}, {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10},
    {0, 2, 3, 4, 5, 6, 7, 8, 9, 10}, {0, 1, 3, 4, 5, 6, 7, 8, 9, 10}, {0, 1, 2, 4, 5, 6, 7, 8, 9, 10},
    {0, 1, 2, 3, 5, 6, 7, 8, 9, 10}]

theorem tables : Tables src tgt 10 desc avoid :=
  ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩

/-- **The network of E23.** -/
abbrev net : RootedNetwork (Fin 11) (Fin 11) (Fin 5) := ECToBlob.FinNetwork.net src tgt 10 lf

theorem net_isPhylogenetic : net.IsPhylogenetic :=
  isPhylogenetic_of_down (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem indegree_eq (v : Fin 11) : net.graph.indegree v = (univ.filter fun e => tgt e = v).card := by
  rw [DirectedMultigraph.indegree, Set.ncard_eq_toFinset_card']
  congr 1
  ext e
  simp [ECToBlob.FinNetwork.net]

theorem outdegree_eq (v : Fin 11) : net.graph.outdegree v = (univ.filter fun e => src e = v).card := by
  rw [DirectedMultigraph.outdegree, Set.ncard_eq_toFinset_card']
  congr 1
  ext e
  simp [ECToBlob.FinNetwork.net]

/-- It is binary. -/
theorem net_isBinary : net.IsBinary := by
  refine ⟨?_, fun v hv ho => ?_⟩
  · rw [outdegree_eq]
    decide
  · rw [outdegree_eq] at ho
    rw [indegree_eq, outdegree_eq]
    revert v
    decide

/-- The only vertex with two parents is `h`. -/
theorem eq_of_two_le_indegree {v : Fin 11} (hv : 2 ≤ net.graph.indegree v) : v = 5 := by
  rw [indegree_eq] at hv
  revert v
  decide

/-- It is level-1: its only reticulation has two arcs. -/
theorem net_isLevelOne : net.IsLevelOne := by
  intro v
  have hH : (univ.filter fun e => net.IsHybridArc e ∧ net.graph.blobSetoid v (net.graph.source e) ∧
      net.graph.blobSetoid v (net.graph.target e)) ⊆ {4, 6} := by
    intro e he
    have key : ∀ e : Fin 11, tgt e = 5 → e ∈ ({4, 6} : Finset (Fin 11)) := by decide
    exact key e (eq_of_two_le_indegree (mem_filter.1 he).2.1)
  have hcard := card_le_card hH
  have hc2 : ({4, 6} : Finset (Fin 11)).card = 2 := by decide
  by_cases h5 : net.graph.blobSetoid v 5
  · have hR : 1 ≤ (univ.filter fun u => 2 ≤ net.graph.indegree u ∧ net.graph.blobSetoid v u).card := by
      refine card_pos.2 ⟨5, mem_filter.2 ⟨mem_univ _, ?_, h5⟩⟩
      rw [indegree_eq]
      decide
    omega
  · have hzero : (univ.filter fun e => net.IsHybridArc e ∧ net.graph.blobSetoid v (net.graph.source e) ∧
        net.graph.blobSetoid v (net.graph.target e)) = ∅ := by
      refine filter_eq_empty_iff.2 fun e _ he => h5 ?_
      have ht : tgt e = 5 := eq_of_two_le_indegree he.1
      have := he.2.2
      change net.graph.blobSetoid v (tgt e) at this
      rwa [ht] at this
    rw [hzero]
    simp

/-- **The tree of blobs of the network is a star on five leaves.** -/
theorem mem_treeOfBlobs_iff {A : Finset (Fin 5)} : A ∈ treeOfBlobs net ↔ A.card = 1 ∨ Aᶜ.card = 1 := by
  rw [tables.mem_treeOfBlobs_iff net_isPhylogenetic]
  revert A
  decide

/-- The tree of blobs resolves no four taxa. -/
theorem not_displays (s : QuartetTree (Fin 5)) : ¬ Displays (treeOfBlobs net) s := by
  rintro ⟨A, hA, hs⟩
  have h2 : (A ∩ s.taxa).card = 2 := s.2.2.1 _ hs
  have h4 : s.taxa.card = 4 := s.card_taxa
  rcases mem_treeOfBlobs_iff.1 hA with h | h
  · have : (A ∩ s.taxa).card ≤ A.card := card_le_card inter_subset_left
    omega
  · have h3 : (s.taxa \ A).card ≤ Aᶜ.card := card_le_card fun x hx => mem_compl.2 (mem_sdiff.1 hx).2
    have h5 := card_inter_add_card_sdiff s.taxa A
    rw [inter_comm] at h5
    omega

/-- The set `{e, a, b, c}`. -/
def eabc : Finset (Fin 5) := {0, 1, 2, 3}

/-- **The restriction to `{e, a, b, c}` has the cut edge `r→u`, with the split `ab|ce`.** -/
theorem inducedCutSplit_ab_ce : InducedCutSplit net (quartetTree 1 2 3 0 (by decide)) :=
  inducedCutSplit_of_rdom net_isPhylogenetic (by decide) (tables.rdom_iff.2 (by decide))

/-- The network induced on `{e, a, b, c}` is treelike: it is not a 4-blob. -/
theorem isTreelike_eabc : IsTreelike net eabc := by
  refine ⟨_, mem_treesOn.2 ?_, inducedCutSplit_ab_ce⟩
  rw [taxa_quartetTree]
  decide

/-- **The converse direction of Lemma 2 of the supplement, as printed**: if `N|Y` is not a 4-blob, then `T_N|Y` is a quartet tree. -/
def Lemma2Converse : Prop :=
  ∀ {V E X : Type} [Fintype V] [Fintype E] [Fintype X] [DecidableEq X] (N : RootedNetwork V E X),
    N.IsPhylogenetic → N.IsBinary → ∀ Y : Finset X, Y.card = 4 → IsTreelike N Y →
      ∃ s ∈ treesOn Y, Displays (treeOfBlobs N) s

/-- **Supplement, Lemma 2, the converse is false** (`tob2025:lemma2_converse_false`, E23 of the report): on the binary level-1 network
`net`, whose tree of blobs is a star, the network induced on `{e, a, b, c}` is treelike, with `ab|ce`, while `T_N` leaves these taxa
unresolved. -/
theorem not_lemma2Converse : ¬ Lemma2Converse := by
  intro h
  obtain ⟨s, -, hs⟩ := h net net_isPhylogenetic net_isBinary eabc (by decide) isTreelike_eabc
  exact not_displays s hs

end TOBQMC.SupplementLemma2
