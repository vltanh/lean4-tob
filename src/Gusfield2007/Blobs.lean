module

public import Gusfield2007.Basic
public import Mathlib.Combinatorics.SimpleGraph.Acyclic

/-!
# Gusfield et al. 2007, Section 2.1: recombination cycles and blobs

Blobs are well defined; arcs on no recombination cycle are the bridges; the contraction of the blobs is a directed tree.
-/

@[expose] public section

open scoped Classical

namespace Gusfield2007

namespace Network

universe u v w

variable {ι : Type u} {V : Type v} {E : Type w} (N : Network ι V E)

/-- An arc on a cycle is on a blob. -/
theorem exists_isBlob_of_onCycle {e : E} (he : N.OnCycle e) : ∃ B, N.IsBlob B ∧ e ∈ B := by
  obtain ⟨Q, hQ, heQ⟩ := he
  exact ⟨_, ⟨Q, hQ, rfl⟩, Q, Relation.ReflTransGen.refl, heQ⟩

/-- **Line 139** (`g:blob_welldefined`). "The blobs in a phylogenetic network are well-defined, i.e., each blob can be
found as above, starting from any recombination cycle in the blob": two blobs with an arc in common are equal. -/
theorem IsBlob.eq_of_inter_nonempty {N : Network ι V E} {B B' : Set E} (hB : N.IsBlob B) (hB' : N.IsBlob B')
    (h : (B ∩ B').Nonempty) : B = B' := by
  obtain ⟨Q, hQ, rfl⟩ := hB
  obtain ⟨Q', hQ', rfl⟩ := hB'
  obtain ⟨e, ⟨Q₁, hQ₁, he₁⟩, ⟨Q₂, hQ₂, he₂⟩⟩ := h
  have : Std.Symm N.ShareArc := ⟨fun _ _ h => ⟨h.2.1, h.1, by rw [Set.inter_comm]; exact h.2.2⟩⟩
  have hsymm : ∀ {P P'}, Relation.ReflTransGen N.ShareArc P P' → Relation.ReflTransGen N.ShareArc P' P :=
    fun {P P'} h => (Relation.ReflTransGen.stdSymm (r := N.ShareArc)).symm P P' h
  have hcyc : ∀ {P P'}, N.IsCycle P → Relation.ReflTransGen N.ShareArc P P' → N.IsCycle P' := by
    intro P P' hP hPP'
    induction hPP' with
    | refl => exact hP
    | tail _ h _ => exact h.2.1
  have h12 : Relation.ReflTransGen N.ShareArc Q₁ Q₂ :=
    .single ⟨hcyc hQ hQ₁, hcyc hQ' hQ₂, ⟨e, he₁, he₂⟩⟩
  have hQQ' : Relation.ReflTransGen N.ShareArc Q Q' := Relation.ReflTransGen.trans hQ₁ (h12.trans (hsymm hQ₂))
  ext f
  constructor
  · rintro ⟨P, hP, hf⟩
    exact ⟨P, (hsymm hQQ').trans hP, hf⟩
  · rintro ⟨P, hP, hf⟩
    exact ⟨P, hQQ'.trans hP, hf⟩

/-- The graph underlying `N`: its directions are forgotten. -/
def underlying : SimpleGraph V := SimpleGraph.fromRel N.Arc

/-- The arcs on no recombination cycle are the bridges of the underlying graph. This is the fact behind the reason given
at line 141, "that cycle would correspond to a recombination cycle": a cycle of the underlying graph is not itself a
recombination cycle, since it can alternate directions several times, but each of its arcs is on one, because all nodes
are reachable from the root. -/
theorem isTreeArc_iff_isBridge [Finite V] [Finite E] (e : E) :
    N.IsTreeArc e ↔ N.underlying.IsBridge s(N.src e, N.tgt e) := by
  sorry

/-- **Lines 140 to 142** (`g:blobtree`). "If we contract each blob in a network to a single point, the resulting network is
a directed tree `T′`". The contraction, with an edge per tree arc, is a tree, which is directed away from the class of the
root. This doesn't need blobs to be node-disjoint, since `T′` contracts the connected components of the arcs on cycles,
and two blobs sharing a node make one class. -/
theorem blobbedTree_isTree [Finite V] [Finite E] :
    N.blobbedTree.IsTree ∧
      (∀ e, N.IsTreeArc e → N.toBlobNode (N.src e) ≠ N.toBlobNode (N.tgt e)) ∧
      Function.Injective (fun e : {e // N.IsTreeArc e} =>
        s(N.toBlobNode (N.src e.1), N.toBlobNode (N.tgt e.1))) ∧
      (∀ e, N.IsTreeArc e → N.toBlobNode (N.tgt e) ≠ N.toBlobNode N.root) ∧
      ∀ a, a ≠ N.toBlobNode N.root → ∃! e : {e // N.IsTreeArc e}, N.toBlobNode (N.tgt e.1) = a := by
  sorry

/-- **Line 135** (`g:separate`). "The network can be modified so that the cycle is node-disjoint from any other cycle. The
modification requires adding one new edge and one new node, with the same sequence labeling both ends of the new edge."
Repeating this makes blobs node-disjoint (line 140). It keeps the crossover model, the ancestral sequence, the rows derived,
the number of recombination nodes, and which sites lie on a common blob. So no minimum in the paper depends on the
convention. -/
theorem exists_blobsNodeDisjoint [LinearOrder ι] [Finite V] [Finite E] {c : Crossover} (hc : N.Obeys c) :
    ∃ (a b : ℕ) (N' : Network ι (Fin a) (Fin b)), N'.Obeys c ∧ N'.BlobsNodeDisjoint ∧
      N'.ancestral = N.ancestral ∧ N'.recombCount = N.recombCount ∧
      (∀ M, N.Derives M → N'.Derives M) ∧
      (∀ i, N'.IsTreeArc (N'.site i) ↔ N.IsTreeArc (N.site i)) ∧
      (∀ i j, (∃ B, N'.IsBlob B ∧ N'.site i ∈ B ∧ N'.site j ∈ B) ↔ ∃ B, N.IsBlob B ∧ N.site i ∈ B ∧ N.site j ∈ B) := by
  sorry

end Network

end Gusfield2007
