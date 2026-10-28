module

public import Basic.Combinatorics.MultigraphConnectivity

/-!
# Uniqueness of a cut bipartition in a connected multigraph

If precisely the same individually identified arcs cross two vertex cuts, then
the two cuts have the same sides up to complementation. The proof transports
membership agreement along undirected walks. No finiteness or nonempty-vertex
assumption is required.
-/

@[expose] public section

namespace DirectedMultigraph

variable {V E : Type*} (G : DirectedMultigraph V E)

/-- Identical crossing status preserves agreement of side membership along one arc. -/
theorem membership_agreement_of_adjOn {S T : Set V}
    (hST : ∀ e, G.Crosses e S ↔ G.Crosses e T) {u v : V}
    (h : G.AdjOn Set.univ u v) :
    (u ∈ S ↔ u ∈ T) ↔ (v ∈ S ↔ v ∈ T) := by
  obtain ⟨e, _, hlink⟩ := h
  have he := hST e
  rcases hlink with ⟨hs, ht⟩ | ⟨ht, hs⟩
  · simp only [Crosses, hs, ht] at he
    tauto
  · simp only [Crosses, hs, ht] at he
    tauto

/-- Agreement of two cuts' side memberships is constant along walks. -/
theorem membership_agreement_of_walks {S T : Set V}
    (hST : ∀ e, G.Crosses e S ↔ G.Crosses e T) {u v : V}
    (h : G.Walks Set.univ u v) :
    (u ∈ S ↔ u ∈ T) ↔ (v ∈ S ↔ v ∈ T) := by
  induction h with
  | refl => exact Iff.rfl
  | tail _ hstep ih => exact ih.trans (G.membership_agreement_of_adjOn hST hstep)

/-- In a connected graph, the set of crossing arcs determines a cut up to complement. -/
theorem eq_or_eq_compl_of_crosses_iff (hG : G.IsConnected) {S T : Set V}
    (hST : ∀ e, G.Crosses e S ↔ G.Crosses e T) : S = T ∨ S = Tᶜ := by
  classical
  by_cases heq : ∀ v, v ∈ S ↔ v ∈ T
  · exact Or.inl (Set.ext heq)
  · push Not at heq
    obtain ⟨u, hu⟩ := heq
    right
    ext v
    have hv := G.membership_agreement_of_walks hST (hG u v)
    simp only [Set.mem_compl_iff]
    tauto

/-- Two singleton cuts carried by the same actual arc agree up to complement. -/
theorem singleton_cuts_eq_or_eq_compl (hG : G.IsConnected) (e : E) {S T : Set V}
    (hS : ∀ f, G.Crosses f S ↔ f = e)
    (hT : ∀ f, G.Crosses f T ↔ f = e) : S = T ∨ S = Tᶜ :=
  G.eq_or_eq_compl_of_crosses_iff hG (fun f => (hS f).trans (hT f).symm)

/-- In Mathlib's edge-cut notation, a common singleton edge cut has unique sides
up to complementation. -/
theorem edgeCut_singleton_eq_or_eq_compl (hG : G.IsConnected) (e : E) {S T : Set V}
    (hS : G.underlying.edgeCut S = {e}) (hT : G.underlying.edgeCut T = {e}) :
    S = T ∨ S = Tᶜ :=
  G.singleton_cuts_eq_or_eq_compl hG e
    ((G.edgeCut_eq_singleton_iff e S).mp hS)
    ((G.edgeCut_eq_singleton_iff e T).mp hT)

end DirectedMultigraph
