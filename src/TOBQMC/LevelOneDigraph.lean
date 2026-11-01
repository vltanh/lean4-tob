module

public import Phylogenetics.Network.Level1.LevelOne
public import TOBQMC.Wedge

/-!
# The two definitions of a level-1 network agree on binary networks

`MetricDigraph.IsLevel1` says of a digraph that no two cycles of its undirected graph share an edge.
`RootedNetwork.IsLevelOne` says of a rooted network that every blob has at most one more reticulation arc than reticulation
vertices. The library has the implication from the first to the second (`MetricDigraph.isLevelOne_ofBinary`). The converse
uses the structure of a level-1 blob in `src/TOBQMC/Wedge.lean`: the arcs of a blob of a binary level-1 network are at most two at
each vertex (`Level1.BlobCycle.degLeTwo`), and an edge on a cycle has a second one at each end, so the edges that are not bridges
form a graph of cycles (`MetricDigraph.isLevel1_of_isCycles`).

Nothing else imports this file.
-/

@[expose] public noncomputable section

open Finset Phylogenetics Phylogenetics.RootedNetwork Phylogenetics.MetricDigraph
open scoped Classical

namespace TOBQMC

variable {V : Type*} {X : Type*} {G : MetricDigraph V X}

/-- An edge of the undirected graph is an arc, in one of its two directions. -/
theorem exists_arc_of_adj (hb : G.IsBinary) {v y : V} (h : G.undirected.Adj v y) :
    ∃ f : G.Arc, s(f.1.1, f.1.2) = s(v, y) ∧ (f.1.1 = v ∨ f.1.2 = v) ∧ (f.1.1 = y ∨ f.1.2 = y) := by
  rcases hb.undirected_adj_iff.1 h with h | h
  · exact ⟨⟨(v, y), h⟩, rfl, Or.inl rfl, Or.inr rfl⟩
  · exact ⟨⟨(y, v), h⟩, Sym2.eq_swap, Or.inr rfl, Or.inl rfl⟩

variable [Fintype V] [Fintype G.Arc]

/-- **A binary digraph that is level-1 in the sense of its blobs has no two cycles sharing an edge**: the edges that are not
bridges are at most two at each vertex, and at least two where there is one, so they form a graph of cycles. -/
theorem isLevel1_of_isLevelOne (hb : G.IsBinary) (hl : G.IsLabelled) (h : (ofBinary hb).IsLevelOne) : G.IsLevel1 := by
  have hN := ofBinary_isPhylogenetic hb hl
  have hBin := ofBinary_isBinary hb
  have hfin := hb.finite
  set N := ofBinary hb with hNdef
  let K : SimpleGraph V :=
    { Adj := fun x y => G.undirected.Adj x y ∧ ¬ G.undirected.IsBridge s(x, y)
      symm := ⟨fun x y hxy => ⟨hxy.1.symm, by rw [Sym2.eq_swap]; exact hxy.2⟩⟩
      loopless := ⟨fun x hx => G.undirected.loopless.irrefl x hx.1⟩ }
  have hKadj : ∀ {x y}, K.Adj x y ↔ G.undirected.Adj x y ∧ ¬ G.undirected.IsBridge s(x, y) := Iff.rfl
  refine isLevel1_of_isCycles (K := K) ?_ fun x y hxy hK => ?_
  · rintro v ⟨x, hx⟩
    have hx' : K.Adj v x := hx
    obtain ⟨hadj, hnb⟩ := hKadj.1 hx'
    -- at least two, along a cycle
    have hnb₂ := hnb
    rw [SimpleGraph.isBridge_iff_forall_cycle_notMem hadj] at hnb₂
    simp only [not_forall, not_not, exists_prop] at hnb₂
    obtain ⟨u, c, hc, hmem⟩ := hnb₂
    have hvc : v ∈ c.support := c.fst_mem_support_of_mem_edges hmem
    have hsub : c.toSubgraph.neighborSet v ⊆ K.neighborSet v := by
      intro z hz
      have hzm : s(v, z) ∈ c.edges := SimpleGraph.Walk.adj_toSubgraph_iff_mem_edges.1 hz
      have hzadj : G.undirected.Adj v z := c.adj_of_mem_edges hzm
      refine (hKadj.2 ⟨hzadj, fun hbr => ?_⟩ : K.Adj v z)
      exact (SimpleGraph.isBridge_iff_forall_cycle_notMem hzadj).1 hbr c hc hzm
    have hge : 2 ≤ (K.neighborSet v).ncard := by
      rw [← hc.ncard_neighborSet_toSubgraph_eq_two hvc]
      exact Set.ncard_le_ncard hsub (Set.toFinite _)
    -- at most two, in the blob
    refine le_antisymm (not_lt.1 fun hlt => ?_) hge
    obtain ⟨a, b, d, ha, hb', hd, hab, had, hbd⟩ := (Set.two_lt_ncard_iff (Set.toFinite _)).1 hlt
    have harc : ∀ {y}, y ∈ K.neighborSet v → ∃ f : G.Arc, N.Incident f v ∧ (f.1.1 = y ∨ f.1.2 = y) ∧
        ¬ N.graph.underlying.IsBridge f := by
      intro y hy
      obtain ⟨hya, hyb⟩ := hKadj.1 (show K.Adj v y from hy)
      obtain ⟨f, hf, hfv, hfy⟩ := exists_arc_of_adj hb hya
      refine ⟨f, hfv, hfy, fun hbr => hyb ?_⟩
      rw [← hf]
      exact (isBridge_iff_undirected_isBridge hb f).1 hbr
    obtain ⟨hret⟩ : Nonempty (∃ w, N.graph.blobSetoid v w ∧ 2 ≤ N.graph.indegree w) := by
      obtain ⟨f, hfv, -, hfb⟩ := harc ha
      rcases Level1.exists_reticulation_or_forall_isBridge hN v with hr | hr
      · exact ⟨hr⟩
      · exact absurd (hr f hfv) hfb
    obtain ⟨w, hvw, hw₂⟩ := hret
    obtain ⟨T, k₁, k₂, pL, pR, C⟩ := Level1.exists_blobCycle hN hBin h hvw hw₂
    have hdeg := C.degLeTwo hN h hw₂
    have hblob : ∀ f : G.Arc, N.Incident f v → ¬ N.graph.underlying.IsBridge f → f ∈ N.graph.blobArcs v := by
      intro f hfv hfb
      have hst := Level1.sameBlob_of_not_isBridge hfb
      rcases hfv with hfv | hfv
      · exact Level1.mem_blobArcs_iff.2 ⟨hfv ▸ .refl, hfv ▸ hst⟩
      · exact Level1.mem_blobArcs_iff.2 ⟨hfv ▸ Level1.sameBlob_symm hst, hfv ▸ .refl⟩
    obtain ⟨fa, hav, hay, hab'⟩ := harc ha
    obtain ⟨fb, hbv, hby, hbb'⟩ := harc hb'
    obtain ⟨fd, hdv, hdy, hdb'⟩ := harc hd
    have hother : ∀ {f : G.Arc} {y}, N.Incident f v → (f.1.1 = y ∨ f.1.2 = y) → y ≠ v →
        (f.1.1 = v ∧ f.1.2 = y) ∨ (f.1.2 = v ∧ f.1.1 = y) := by
      intro f y hfv hfy hyv
      rcases (hfv : f.1.1 = v ∨ f.1.2 = v) with hf | hf <;> rcases hfy with hf' | hf'
      · exact absurd (hf'.symm.trans hf) hyv
      · exact Or.inl ⟨hf, hf'⟩
      · exact Or.inr ⟨hf, hf'⟩
      · exact absurd (hf'.symm.trans hf) hyv
    have hne : ∀ {y y' : V} {f f' : G.Arc}, y ∈ K.neighborSet v → y' ∈ K.neighborSet v → y ≠ y' → N.Incident f v →
        N.Incident f' v → (f.1.1 = y ∨ f.1.2 = y) → (f'.1.1 = y' ∨ f'.1.2 = y') → f ≠ f' := by
      rintro y y' f f' hy hy' hyy' hfv hfv' hfy hfy' rfl
      have hyv : y ≠ v := fun e => (show K.Adj v y from hy).ne e.symm
      have hyv' : y' ≠ v := fun e => (show K.Adj v y' from hy').ne e.symm
      rcases hother hfv hfy hyv with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ <;> rcases hother hfv hfy' hyv' with ⟨h₃, h₄⟩ | ⟨h₃, h₄⟩
      · exact hyy' (h₂.symm.trans h₄)
      · exact hyv (h₂.symm.trans h₃)
      · exact hyv' (h₄.symm.trans h₁)
      · exact hyy' (h₂.symm.trans h₄)
    exact hdeg v fa fb fd (hblob fa hav hab') (hblob fb hbv hbb') (hblob fd hdv hdb') hav hbv hdv
      (hne ha hb' hab hav hbv hay hby) (hne ha hd had hav hdv hay hdy) (hne hb' hd hbd hbv hdv hby hdy)
  · by_contra hnb
    exact hK (hKadj.2 ⟨hxy, hnb⟩)

/-- **On a binary digraph with labelled leaves, the two definitions of level-1 agree.** -/
theorem isLevel1_iff_isLevelOne (hb : G.IsBinary) (hl : G.IsLabelled) : G.IsLevel1 ↔ (ofBinary hb).IsLevelOne :=
  ⟨isLevelOne_ofBinary hb hl, isLevel1_of_isLevelOne hb hl⟩

end TOBQMC
