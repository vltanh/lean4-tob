module

public import TOBQMC.Level1Blobs

/-!
# TOB-QMC supplement, Lemma 8: a reticulation at the boundary of a blob

The supplement's text, lines 560-575: "Let `N⁺` be a directed binary phylogenetic network with a finite
number of vertices. If `B` is a blob of `N⁺`, then there exists a reticulation node in `B` that is incident to a cut
edge of `B`."

The printed proof builds a sequence `u₀, u₁, u₂, ...` of distinct reticulations of `B`, each an ancestor of the next,
under the assumption that no reticulation of `B` is incident to a cut edge, against finiteness. Here finiteness gives
a lowest reticulation of `B` (`supplement_lemma8`), and the step of the sequence is `exists_reticulation_below`: a
vertex of `B` with a blob edge reaches a reticulation of `B`.

Two slips of the printed text:

* The statement needs `B` non-trivial, as the theorem says. A trivial blob, such as a single taxon, has no
  reticulation (`not_two_le_indegree_of_sameBlob_leaf`), and the paper's definition of a blob allows a single vertex
  ("A blob is trivial if it consists of a single vertex", v5, embedded line 357).
* "assume all reticulation nodes in `v`" is meant to read "in `B`".
-/

@[expose] public section

open Phylogenetics Phylogenetics.RootedNetwork

namespace TOBQMC

variable {V E X : Type*} {N : RootedNetwork V E X}

/-- **The step of the sequence in the proof of Lemma 8**: "there must exist a reticulation node [...] we know that
`u₀` is an ancestor of `u₁`". A vertex `u` with a blob edge reaches a reticulation of its blob (possibly `u` itself:
"`u₂` might be the child of `u₁`").

Departure from the paper: the printed step takes two disjoint paths from the root `r'` of the blob to `u` in the
undirected network, by biconnectivity, and a reticulation on one of them, by acyclicity. Disjoint paths need Menger's
theorem, which the library lacks, and they do not exist as written when `u = r'`; which reticulation on the cycle lies
below `u` also needs an argument. The Lean takes a sink `w` of the part of the blob below `u`: if `w` is no
reticulation then all its arcs are bridges (`forall_isBridge_of_indegree_le_one`), so `w` is alone in its blob, and `w
= u`, against the blob edge at `u`. -/
theorem exists_reticulation_below (hN : N.IsPhylogenetic) {u : V} {f : E}
    (hf : N.graph.source f = u ∨ N.graph.target f = u) (hnb : ¬ N.graph.underlying.IsBridge f) :
    ∃ h, N.graph.blobSetoid u h ∧ N.graph.Reaches u h ∧ 2 ≤ N.graph.indegree h := by
  obtain ⟨w, ⟨hw, hrw⟩, hmin⟩ := TOBQMC.Level1.exists_sink hN (S := {w | N.graph.blobSetoid u w ∧ N.graph.Reaches u w})
    ⟨u, .refl, .refl⟩
  by_cases h2 : 2 ≤ N.graph.indegree w
  · exact ⟨w, hw, hrw, h2⟩
  · exfalso
    have hout : ∀ g, N.graph.source g = w → N.graph.underlying.IsBridge g := by
      rintro g rfl
      by_contra hg
      exact hmin _ ⟨TOBQMC.Level1.sameBlob_trans hw (TOBQMC.Level1.sameBlob_of_not_isBridge hg),
        hrw.tail ⟨g, rfl, rfl⟩⟩ (.single ⟨g, rfl, rfl⟩)
    have hall := TOBQMC.Level1.forall_isBridge_of_indegree_le_one hN (by omega) hout
    have huw : u = w := TOBQMC.Level1.eq_of_sameBlob_of_forall_isBridge hall (TOBQMC.Level1.sameBlob_symm hw)
    subst huw
    exact hnb (hall f hf)

/-- A vertex with another vertex in its blob has a blob edge. -/
theorem exists_not_isBridge_of_sameBlob {v w : V} (hne : v ≠ w) (h : N.graph.blobSetoid v w) :
    ∃ f, (N.graph.source f = v ∨ N.graph.target f = v) ∧ ¬ N.graph.underlying.IsBridge f := by
  rcases Relation.ReflTransGen.cases_head h with heq | ⟨c, ⟨f, hf, hl⟩, -⟩
  · exact absurd heq hne
  · refine ⟨f, ?_, hf⟩
    rcases hl with ⟨h, -⟩ | ⟨-, h⟩
    · exact Or.inl h
    · exact Or.inr h

/-- A lowest reticulation of a blob has only cut edges below it: the child of a reticulation with a blob edge below it
would continue the sequence of the proof of Lemma 8. -/
theorem isBridge_of_lowest_reticulation (hN : N.IsPhylogenetic) {v u : V}
    (hu : N.graph.blobSetoid v u)
    (hlow : ∀ h, N.graph.blobSetoid v h → 2 ≤ N.graph.indegree h → ¬ Relation.TransGen N.graph.Adj u h)
    {g : E} (hg : N.graph.source g = u) : N.graph.underlying.IsBridge g := by
  by_contra hnb
  obtain ⟨h, hh, hr, h2⟩ := exists_reticulation_below hN (Or.inr rfl) hnb
  have hug : N.graph.blobSetoid u (N.graph.target g) := hg ▸ TOBQMC.Level1.sameBlob_of_not_isBridge hnb
  exact hlow h (TOBQMC.Level1.sameBlob_trans hu (TOBQMC.Level1.sameBlob_trans hug hh)) h2
    (Relation.TransGen.head' ⟨g, hg, rfl⟩ hr)

/-- **Lemma 8 of the supplement** (`tob2025supplied:lemma8`), for a non-trivial blob, the one containing `v` and
another vertex `w`: it has a reticulation with an outgoing cut edge.

The printed statement has "binary", which is not used: at any phylogenetic network, all outgoing arcs of a lowest
reticulation of the blob are bridges, and in a binary one the reticulation has exactly one. The printed sequence `u₀,
u₁, ...` is here a lowest reticulation (`isBridge_of_lowest_reticulation`), whose existence replaces the choice of the
printed `u₀`: any vertex of the blob will do as a start. See `exists_reticulation_below` for the departure in the
step. -/
theorem supplement_lemma8 (hN : N.IsPhylogenetic) {v w : V} (hne : v ≠ w) (hvw : N.graph.blobSetoid v w) :
    ∃ u, N.graph.blobSetoid v u ∧ 2 ≤ N.graph.indegree u ∧ ∃ g, N.graph.source g = u ∧ N.graph.underlying.IsBridge g := by
  have := hN.finite_arcs
  obtain ⟨f, hf, hnb⟩ := exists_not_isBridge_of_sameBlob hne hvw
  obtain ⟨h₀, hh₀, -, h₀2⟩ := exists_reticulation_below hN hf hnb
  obtain ⟨u, ⟨hu, hu2⟩, hmin⟩ := TOBQMC.Level1.exists_sink hN
    (S := {u | N.graph.blobSetoid v u ∧ 2 ≤ N.graph.indegree u}) ⟨h₀, hh₀, h₀2⟩
  have hout : N.graph.outdegree u ≠ 0 := by
    intro h0
    obtain ⟨x, rfl⟩ := (hN.leaves u).mp h0
    have := hN.leaf_indegree x
    omega
  obtain ⟨g, hg⟩ : ∃ g, N.graph.source g = u := by
    by_contra hcon
    push Not at hcon
    apply hout
    rw [DirectedMultigraph.outdegree, Set.ncard_eq_zero]
    exact Set.eq_empty_iff_forall_notMem.mpr hcon
  exact ⟨u, hu, hu2, g, hg, isBridge_of_lowest_reticulation hN hu (fun h hh h2 => hmin h ⟨hh, h2⟩) hg⟩

/-- The printed Lemma 8 fails on trivial blobs: the blob of a taxon contains no reticulation. -/
theorem not_two_le_indegree_of_sameBlob_leaf (hN : N.IsPhylogenetic) (x : X) {u : V}
    (hu : N.graph.blobSetoid (N.leaf x) u) : ¬ 2 ≤ N.graph.indegree u := by
  have hux := TOBQMC.Level1.eq_of_sameBlob_of_forall_isBridge (TOBQMC.Level1.forall_isBridge_leaf hN x) hu
  rw [hux, hN.leaf_indegree x]
  norm_num

end TOBQMC
