module

public import Gusfield2007.Counterexamples
public import External.GusfieldEtAl2004.SameBlob
public import External.MyersGriffiths2003.Composite

/-!
# Gusfield et al. 2007, line 590: the conjecture of Huson and Klöpper

"This also establishes that Conjecture 1, recently stated in Huson and Klopper (2007), is false." (line 590); line 403: "a related version of the unrooted conjecture was also recently stated (as Conjecture 1)".

Huson and Klöpper 2007 (RECOMB, LNBI 4453, pp. 211-225) is closed and wasn't read. Its conjecture is read from the thesis of the second author, T. H. Klöpper, *Algorithms for the Calculation and Visualisation of Phylogenetic Networks* (Tübingen, 2008, open on the university's repository), pp. 17-18, who says of that paper: "In a recent article [HK07], we presented a Decomposition Theorem that holds for non-degenerate galled networks. Following the lead of [GB05], we also proposed a general Decomposition Conjecture:

> Conjecture 2.2. Given an input set of splits `Δ`, a minimal reticulation network `N` exists that explains `Δ` so that for any two tree edges `e` and `f` of `N` we have the following: Any two splits `S ∈ Δ ∩ Σ(e)` and `S′ ∈ Δ ∩ Σ(f)` are contained in the same connected component of `IG(Δ)` if and only if `e` and `f` are contained in a common unoriented cycle of `N`."

The thesis goes on: "Interestingly, our conjecture is not true in general, as was shown in [DGS07]", and its Figure 2.5, "Counter-example for Conjecture 2.2 published in [DGS07]", is the matrix of Figure 8 here (`Gusfield2007.fig8`), row by row. So whether the 2007 text has the same words wasn't checked; that the conjecture of that paper is this one, and that Figure 8 is meant to refute it, is the thesis's account.

In Lean, `Conjecture22` is that statement, on the thesis's own networks (`ReticulateNetwork`, its Definition 2.1). The reading:

* "Minimal" in the thesis is its Definition 2.2, with "a minimal number of reticulations" first and then more criteria, and in the paper it's "the number of reticulations and the number of edges" (the thesis, p. 86). Only the first is kept here, so that the Lean statement asks less of the network.
* `Σ(e)` isn't spelled out in the part of the thesis we read, which defines the clusters `H(e)`: "we can obtain an `X`-tree from `N` by choosing and removing one reticulation edge `p(r_i)` or `q(r_i)` for each reticulation", and `H(N)` is the set of clusters of those trees. So a split is in `Σ(e)` when in some such tree it's the split of the edge `e` (`ReticulateNetwork.HasSplit`), and a network "explains" `Δ` when each split is in `Σ(e)` for a tree edge `e`.
* `S` and `S′` are different splits. As printed, with `S = S′ ∈ Σ(e)` and `e = f`, it would require every tree edge carrying a split to lie on a cycle, which no tree does. Sites with equal or complementary columns are the same split (`SameSplit`).
* A set of splits is the columns of a matrix `M` with distinct rows, the taxa being the rows.

The bridge to the rest of this library: a reticulate network explaining the splits of `M` is a network for `M` with no constraint on crossovers (`ReticulateNetwork.toNetwork`): a split on a tree edge is a site on an arc, and the sampled tree says which parent a reticulation copies. Conversely, a network for `M` is such a reticulate network, after a pendant arc for each row (`ReticulateNetwork.ofNetwork`). So the minimal number of reticulations explaining the splits of `M` is `R(M)` (`R_multiple_le_reticCount`, `exists_reticulateNetwork`), and `Conjecture22` implies `HusonKloepperConjecture`, which is about the networks of this library.

**The refutation applies** (`husonKloepperConjecture_false`, `conjecture22_false`). A network with the property has no recombination node breaking both components of Figure 8: its parents would differ at a site of each, and the two sites would be on one unoriented cycle (`exists_onCommonCycle_of_label_ne`). Then `R(M(C₁)) + R(M(C₂))` is at most the number of recombination nodes, and this is `4 ≤ 3`: Figure 9 has three.

The one step that isn't in the source: two recombination cycles sharing an arc have, for any arc on each, an unoriented cycle through both (`exists_isCycle_of_share_edge`).
-/

@[expose] public section

open scoped Classical

namespace Gusfield2007

/-! ### Two cycles sharing an edge -/

section Graph

open SimpleGraph

variable {V : Type*} {G : SimpleGraph V}

/-- Two paths between two nodes, with no other node and no edge in common, make a cycle. -/
theorem isCycle_append_of_isPath {u v : V} {p : G.Walk u v} {q : G.Walk v u} (hp : p.IsPath) (hq : q.IsPath) (huv : u ≠ v)
    (hsupp : ∀ w ∈ p.support, w ∈ q.support → w = u ∨ w = v) (hedges : ∀ g ∈ p.edges, g ∉ q.edges) : (p.append q).IsCycle := by
  rw [Walk.isCycle_def]
  have hpn := hp.support_nodup
  have hqn := hq.support_nodup
  rw [← Walk.cons_tail_support, List.nodup_cons] at hpn hqn
  refine ⟨?_, ?_, ?_⟩
  · rw [Walk.isTrail_def, Walk.edges_append, List.nodup_append]
    exact ⟨hp.isTrail.edges_nodup, hq.isTrail.edges_nodup, fun a ha b hb hab => hedges a ha (hab ▸ hb)⟩
  · intro h
    have := congrArg Walk.length h
    rw [Walk.length_append, Walk.length_nil] at this
    exact huv (Walk.eq_of_length_eq_zero (by omega : p.length = 0))
  · rw [Walk.tail_support_append, List.nodup_append]
    refine ⟨hpn.2, hqn.2, fun a ha b hb hab => ?_⟩
    subst hab
    have ha' : a ∈ p.support := List.mem_of_mem_tail ha
    have hb' : a ∈ q.support := List.mem_of_mem_tail hb
    rcases hsupp a ha' hb' with rfl | rfl
    · exact hpn.1 ha
    · exact hqn.1 hb

/-- The first node of a walk in a set. -/
theorem Walk.exists_first_hit {u v : V} (p : G.Walk u v) (A : Set V) (h : ∃ w ∈ p.support, w ∈ A) :
    ∃ (c : V) (_ : c ∈ A) (p₁ : G.Walk u c) (p₂ : G.Walk c v), p = p₁.append p₂ ∧ ∀ w ∈ p₁.support, w ∈ A → w = c := by
  induction p with
  | nil =>
    obtain ⟨w, hw, hA⟩ := h
    rw [Walk.support_nil, List.mem_singleton] at hw
    subst hw
    exact ⟨_, hA, Walk.nil, Walk.nil, rfl, by simp⟩
  | @cons a b c hadj p ih =>
    by_cases ha : a ∈ A
    · exact ⟨a, ha, Walk.nil, Walk.cons hadj p, rfl, by simp⟩
    · have h' : ∃ w ∈ p.support, w ∈ A := by
        obtain ⟨w, hw, hA⟩ := h
        rw [Walk.support_cons, List.mem_cons] at hw
        rcases hw with rfl | hw
        · exact absurd hA ha
        · exact ⟨w, hw, hA⟩
      obtain ⟨d, hd, p₁, p₂, rfl, hp₁⟩ := ih h'
      refine ⟨d, hd, Walk.cons hadj p₁, p₂, rfl, fun w hw hA => ?_⟩
      rw [Walk.support_cons, List.mem_cons] at hw
      rcases hw with rfl | hw
      · exact absurd hA ha
      · exact hp₁ w hw hA

/-- A walk splits at an edge on it. -/
theorem Walk.exists_split_of_mem_edges {u v : V} (p : G.Walk u v) {b : Sym2 V} (hb : b ∈ p.edges) :
    ∃ (x y : V) (h : G.Adj x y) (p₁ : G.Walk u x) (p₂ : G.Walk y v), s(x, y) = b ∧ p = p₁.append (Walk.cons h p₂) := by
  induction p with
  | nil => simp at hb
  | @cons a c d hadj p ih =>
    rw [Walk.edges_cons, List.mem_cons] at hb
    rcases hb with rfl | hb
    · exact ⟨a, c, hadj, Walk.nil, p, rfl, rfl⟩
    · obtain ⟨x, y, h, p₁, p₂, hxy, rfl⟩ := ih hb
      exact ⟨x, y, h, Walk.cons hadj p₁, p₂, hxy, rfl⟩

/-- A cycle through an edge is that edge and a path between its ends. -/
theorem Walk.IsCycle.exists_path_of_mem_edges {u : V} {c : G.Walk u u} (hc : c.IsCycle) {b : Sym2 V} (hb : b ∈ c.edges) :
    ∃ (x y : V) (_ : G.Adj x y) (R : G.Walk y x), s(x, y) = b ∧ R.IsPath ∧ b ∉ R.edges ∧ (∀ z ∈ c.edges, z = b ∨ z ∈ R.edges) := by
  obtain ⟨x, y, h, p₁, p₂, hxy, rfl⟩ := Walk.exists_split_of_mem_edges c hb
  refine ⟨x, y, h, p₂.append p₁, hxy, ?_, ?_, ?_⟩
  · have htail := hc.support_nodup
    rw [Walk.tail_support_append, Walk.support_cons, List.tail_cons] at htail
    rw [Walk.isPath_def, Walk.support_append]
    exact (List.perm_append_comm.nodup_iff).1 htail
  · have hnd := hc.isTrail.edges_nodup
    rw [Walk.edges_append, Walk.edges_cons, List.nodup_append] at hnd
    rw [Walk.edges_append, List.mem_append]
    rintro (h₁ | h₁)
    · exact (List.nodup_cons.1 hnd.2.1).1 (hxy ▸ h₁)
    · exact hnd.2.2 b h₁ b (hxy ▸ List.mem_cons_self) rfl
  · intro z hz
    rw [Walk.edges_append, List.mem_append, Walk.edges_cons, List.mem_cons] at hz
    rw [Walk.edges_append, List.mem_append]
    rcases hz with hz | rfl | hz
    · exact Or.inr (Or.inr hz)
    · exact Or.inl hxy
    · exact Or.inr (Or.inl hz)

/-- An edge with both ends in a set isn't on a path having only its last node in the set. -/
theorem notMem_edges_of_last_hit {u c : V} {p : G.Walk u c} {A : Set V} (hp : ∀ w ∈ p.support, w ∈ A → w = c) {g : Sym2 V} (hg : g ∈ p.edges)
    (hA : ∀ w ∈ g, w ∈ A) : False := by
  induction g using Sym2.ind with
  | _ a b =>
    have ha := hp a (p.fst_mem_support_of_mem_edges hg) (hA a (Sym2.mem_mk_left a b))
    have hb := hp b (p.snd_mem_support_of_mem_edges hg) (hA b (Sym2.mem_mk_right a b))
    exact G.ne_of_adj (p.adj_of_mem_edges hg) (ha.trans hb.symm)

/-- **Two cycles sharing an edge** (`g:cycle_transitive`). If two cycles have an edge in common, then an edge of one and an edge of the other are on a common cycle. The other cycle, from the edge `b`, runs into the first at two different nodes, which gives a path with only its ends on the first cycle; these ends cut the first cycle into two paths, and the one with `a` closes up with it. -/
theorem exists_isCycle_of_share_edge {u₁ u₂ : V} {C₁ : G.Walk u₁ u₁} {C₂ : G.Walk u₂ u₂} (h₁ : C₁.IsCycle) (h₂ : C₂.IsCycle) {z a b : Sym2 V}
    (hz₁ : z ∈ C₁.edges) (hz₂ : z ∈ C₂.edges) (ha : a ∈ C₁.edges) (hb : b ∈ C₂.edges) :
    ∃ (w : V) (C : G.Walk w w), C.IsCycle ∧ a ∈ C.edges ∧ b ∈ C.edges := by
  by_cases hbC : b ∈ C₁.edges
  · exact ⟨u₁, C₁, h₁, ha, hbC⟩
  set A : Set V := {w | w ∈ C₁.support} with hA
  have hedgeA : ∀ g ∈ C₁.edges, ∀ w ∈ g, w ∈ A := fun g hg w hw => C₁.mem_support_of_mem_edges hg hw
  obtain ⟨x, y, hxy, R, hb', hRp, hbR, hRall⟩ := Walk.IsCycle.exists_path_of_mem_edges h₂ hb
  -- The shared edge is on `R`, so `R` has two different nodes on the first cycle.
  have hzb : z ≠ b := fun h => hbC (h ▸ hz₁)
  have hzR : z ∈ R.edges := (hRall z hz₂).resolve_left hzb
  induction z using Sym2.ind with
  | _ c d =>
  have hcd : c ≠ d := G.ne_of_adj (R.adj_of_mem_edges hzR)
  have hcA : c ∈ A := hedgeA _ hz₁ c (Sym2.mem_mk_left c d)
  have hdA : d ∈ A := hedgeA _ hz₁ d (Sym2.mem_mk_right c d)
  have hcR : c ∈ R.support := R.fst_mem_support_of_mem_edges hzR
  have hdR : d ∈ R.support := R.snd_mem_support_of_mem_edges hzR
  obtain ⟨c₁, hc₁, R₁, R', hsplit, hR₁⟩ := Walk.exists_first_hit R A ⟨c, hcR, hcA⟩
  obtain ⟨c₂, hc₂, R₃, R₄, hsplit', hR₃⟩ := Walk.exists_first_hit R'.reverse A ⟨c₁, by simp, hc₁⟩
  subst hsplit
  have hR'p : R'.IsPath := hRp.of_append_right
  have hR'r : R'.reverse = R₃.append R₄ := hsplit'
  have hRr'p : (R₃.append R₄).IsPath := hR'r ▸ hR'p.reverse
  have hR₃p : R₃.IsPath := hRr'p.of_append_left
  have hR₄p : R₄.IsPath := hRr'p.of_append_right
  have hR₁p : R₁.IsPath := hRp.of_append_left
  have hR'supp : ∀ w, w ∈ R'.support ↔ w ∈ R₃.support ∨ w ∈ R₄.support := by
    intro w
    have : w ∈ R'.reverse.support ↔ w ∈ R'.support := by simp
    rw [← this, hR'r, Walk.mem_support_append_iff]
  -- The two ends differ.
  have hne : c₁ ≠ c₂ := by
    rintro rfl
    have hnil : R₄ = Walk.nil := Walk.eq_nil_iff_nil.2 (Walk.isPath_iff_nil.1 hR₄p)
    have honly : ∀ w ∈ (R₁.append R').support, w ∈ A → w = c₁ := by
      intro w hw hwA
      rcases (Walk.mem_support_append_iff _ _).1 hw with h | h
      · exact hR₁ w h hwA
      · rcases (hR'supp w).1 h with h' | h'
        · exact hR₃ w h' hwA
        · rw [hnil] at h'
          simpa using h'
    exact hcd ((honly c hcR hcA).trans (honly d hdR hdA).symm)
  -- The ends of the new path are the only nodes on the first cycle.
  have hdisj : ∀ w ∈ R₁.support, w ∉ R₃.support := by
    intro w hw₁ hw₃
    have hnd := hRp.support_nodup
    rw [Walk.support_append, List.nodup_append] at hnd
    have hwR' : w ∈ R'.support := (hR'supp w).2 (Or.inl hw₃)
    rw [← Walk.cons_tail_support, List.mem_cons] at hwR'
    rcases hwR' with rfl | ht
    · exact hne (hR₃ _ hw₃ hc₁)
    · exact hnd.2.2 w hw₁ w ht rfl
  set P : G.Walk c₁ c₂ := R₁.reverse.append (Walk.cons hxy.symm R₃) with hP
  have hPp : P.IsPath := by
    rw [hP, Walk.isPath_def, Walk.support_append, Walk.support_cons, List.tail_cons, Walk.support_reverse, List.nodup_append]
    refine ⟨List.nodup_reverse.2 hR₁p.support_nodup, hR₃p.support_nodup, fun a' ha' b' hb' hab => ?_⟩
    subst hab
    exact hdisj a' (List.mem_reverse.1 ha') hb'
  have hPA : ∀ w ∈ P.support, w ∈ A → w = c₁ ∨ w = c₂ := by
    intro w hw hwA
    rw [hP, Walk.support_append, Walk.support_cons, List.tail_cons, List.mem_append, Walk.support_reverse, List.mem_reverse] at hw
    rcases hw with hw | hw
    · exact Or.inl (hR₁ w hw hwA)
    · exact Or.inr (hR₃ w hw hwA)
  have hPe : ∀ g ∈ P.edges, g ∉ C₁.edges := by
    intro g hg hgC
    rw [hP, Walk.edges_append, List.mem_append, Walk.edges_reverse, List.mem_reverse, Walk.edges_cons, List.mem_cons] at hg
    rcases hg with hg | hg | hg
    · exact notMem_edges_of_last_hit hR₁ hg (hedgeA g hgC)
    · refine hbC ?_
      rw [← hb', Sym2.eq_swap]
      exact hg ▸ hgC
    · exact notMem_edges_of_last_hit hR₃ hg (hedgeA g hgC)
  have hbP : b ∈ P.edges := by
    rw [hP, Walk.edges_append, List.mem_append, Walk.edges_cons, List.mem_cons]
    refine Or.inr (Or.inl ?_)
    rw [← hb', Sym2.eq_swap]
  -- Cut the first cycle at the two ends.
  have hc₁C : c₁ ∈ C₁.support := hc₁
  have hC' := h₁.rotate hc₁C
  have hc₂C : c₂ ∈ (C₁.rotate c₁ hc₁C).support := (C₁.mem_support_rotate_iff c₁ hc₁C).2 hc₂
  have hspec := (C₁.rotate c₁ hc₁C).take_spec hc₂C
  set A₁ := (C₁.rotate c₁ hc₁C).takeUntil c₂ hc₂C with hA₁
  set A₂ := (C₁.rotate c₁ hc₁C).dropUntil c₂ hc₂C with hA₂
  have hA₁p : A₁.IsPath := hC'.isPath_takeUntil hc₂C
  have hA₂p : A₂.IsPath := by
    rw [← hspec] at hC'
    exact hC'.isPath_of_append_right (Walk.not_nil_of_ne hne)
  have hsuppA : ∀ w, w ∈ A₁.support ∨ w ∈ A₂.support → w ∈ A := by
    intro w hw
    have : w ∈ (A₁.append A₂).support := (Walk.mem_support_append_iff _ _).2 hw
    rw [hspec] at this
    exact (C₁.mem_support_rotate_iff c₁ hc₁C).1 this
  have hedgesA : ∀ g, g ∈ A₁.edges ∨ g ∈ A₂.edges → g ∈ C₁.edges := by
    intro g hg
    have : g ∈ (A₁.append A₂).edges := by
      rw [Walk.edges_append, List.mem_append]
      exact hg
    rw [hspec] at this
    exact (C₁.rotate_edges c₁ hc₁C).mem_iff.1 this
  have haA : a ∈ A₁.edges ∨ a ∈ A₂.edges := by
    have : a ∈ (A₁.append A₂).edges := by
      rw [hspec]
      exact (C₁.rotate_edges c₁ hc₁C).mem_iff.2 ha
    rwa [Walk.edges_append, List.mem_append] at this
  rcases haA with haA | haA
  · refine ⟨c₁, A₁.append P.reverse, isCycle_append_of_isPath hA₁p hPp.reverse hne ?_ ?_, ?_, ?_⟩
    · intro w hw₁ hw₂
      exact hPA w (by simpa using hw₂) (hsuppA w (Or.inl hw₁))
    · intro g hg hg'
      rw [Walk.edges_reverse, List.mem_reverse] at hg'
      exact hPe g hg' (hedgesA g (Or.inl hg))
    · rw [Walk.edges_append, List.mem_append]
      exact Or.inl haA
    · rw [Walk.edges_append, List.mem_append, Walk.edges_reverse, List.mem_reverse]
      exact Or.inr hbP
  · refine ⟨c₁, P.append A₂, isCycle_append_of_isPath hPp hA₂p hne ?_ ?_, ?_, ?_⟩
    · intro w hw₁ hw₂
      exact hPA w hw₁ (hsuppA w (Or.inr hw₂))
    · intro g hg hg'
      exact hPe g hg (hedgesA g (Or.inr hg'))
    · rw [Walk.edges_append, List.mem_append]
      exact Or.inr haA
    · rw [Walk.edges_append, List.mem_append]
      exact Or.inl hbP

end Graph

/-! ### Unoriented cycles of a network -/

namespace Network

variable {ι V E : Type*} (N : Network ι V E)

/-- The undirected graph of a network. -/
def undirected : SimpleGraph V := SimpleGraph.fromRel N.Arc

/-- An arc as an edge of the undirected graph. -/
def edgeOf (e : E) : Sym2 V := s(N.src e, N.tgt e)

/-- The arcs `e` and `f` are "contained in a common unoriented cycle" (Conjecture 2.2 of the thesis). -/
def OnCommonCycle (e f : E) : Prop :=
  ∃ (v : V) (c : N.undirected.Walk v v), c.IsCycle ∧ N.edgeOf e ∈ c.edges ∧ N.edgeOf f ∈ c.edges

variable {N}

/-- A directed path is a walk with the same arcs, and nodes. -/
theorem IsPath.exists_walk {u v : V} {p : List E} (h : N.IsPath u v p) :
    ∃ w : N.undirected.Walk u v, w.edges = p.map N.edgeOf ∧ w.support = pathVerts N u p := by
  induction p generalizing u with
  | nil =>
    obtain rfl : u = v := h
    exact ⟨SimpleGraph.Walk.nil, rfl, rfl⟩
  | cons e p ih =>
    obtain ⟨rfl, h₂⟩ := h
    obtain ⟨w, hw₁, hw₂⟩ := ih h₂
    have hadj : N.undirected.Adj (N.src e) (N.tgt e) := by
      refine ⟨fun heq => N.acyclic (N.src e) (Relation.TransGen.single ?_), Or.inl ⟨e, rfl, rfl⟩⟩
      exact ⟨e, rfl, heq.symm⟩
    refine ⟨SimpleGraph.Walk.cons hadj w, ?_, ?_⟩
    · rw [SimpleGraph.Walk.edges_cons, hw₁]
      rfl
    · rw [SimpleGraph.Walk.support_cons, hw₂]
      rfl

/-- The nodes on a directed path are different. -/
theorem IsPath.pathVerts_nodup [Finite V] {u v : V} {p : List E} (h : N.IsPath u v p) : (pathVerts N u p).Nodup := by
  induction p generalizing u with
  | nil => exact List.nodup_singleton u
  | cons e p ih =>
    obtain ⟨rfl, h₂⟩ := h
    have := ih h₂
    refine List.nodup_cons.2 ⟨?_, this⟩
    intro hmem
    exact not_reach_tgt_src e (h₂.reach_of_mem hmem).1

/-- **A recombination cycle is an unoriented cycle**, with the same arcs. -/
theorem IsCycle.exists_walk [Finite V] {Q : Set E} (hQ : N.IsCycle Q) :
    ∃ (v : V) (c : N.undirected.Walk v v), c.IsCycle ∧ ∀ e ∈ Q, N.edgeOf e ∈ c.edges := by
  obtain ⟨w, x, p, q, ⟨-, hp, hq, hne, hmeet⟩, rfl⟩ := hQ
  obtain ⟨wp, hwp₁, hwp₂⟩ := hp.exists_walk
  obtain ⟨wq, hwq₁, hwq₂⟩ := hq.exists_walk
  have hwx : w ≠ x := by
    rintro rfl
    exact hne ((hp.eq_nil_of_self).trans (hq.eq_nil_of_self).symm)
  have hpp : wp.IsPath := by
    rw [SimpleGraph.Walk.isPath_def, hwp₂]
    exact hp.pathVerts_nodup
  have hqp : wq.IsPath := by
    rw [SimpleGraph.Walk.isPath_def, hwq₂]
    exact hq.pathVerts_nodup
  -- An arc on both paths is the only arc of both, which they don't allow.
  have hboth : ∀ g, g ∈ p → g ∉ q := by
    intro g hgp hgq
    have hgx : N.tgt g = x := hmeet g hgp g hgq rfl
    obtain ⟨p₁, p₂, rfl, h₁, h₂⟩ := hp.split hgp
    obtain ⟨q₁, q₂, rfl, h₃, h₄⟩ := hq.split hgq
    rw [hgx] at h₂ h₄
    obtain rfl := h₂.eq_nil_of_self
    obtain rfl := h₄.eq_nil_of_self
    by_cases hg : N.src g = w
    · rw [hg] at h₁ h₃
      obtain rfl := h₁.eq_nil_of_self
      obtain rfl := h₃.eq_nil_of_self
      exact hne rfl
    · -- The node above `g` is on both paths, and it isn't `x`.
      have hn₁ := h₁.end_mem_pathVerts
      have hn₂ := h₃.end_mem_pathVerts
      rcases List.mem_cons.1 hn₁ with h₅ | h₅
      · exact hg h₅
      rcases List.mem_cons.1 hn₂ with h₆ | h₆
      · exact hg h₆
      obtain ⟨g₁, hg₁, hg₁t⟩ := List.mem_map.1 h₅
      obtain ⟨g₂, hg₂, hg₂t⟩ := List.mem_map.1 h₆
      have heq := hmeet g₁ (List.mem_append_left _ hg₁) g₂ (List.mem_append_left _ hg₂) (hg₁t.trans hg₂t.symm)
      rw [hg₁t] at heq
      exact not_reach_tgt_src g (by rw [heq, hgx]; exact Relation.ReflTransGen.refl)
  refine ⟨w, wp.append wq.reverse, isCycle_append_of_isPath hpp hqp.reverse hwx ?_ ?_, ?_⟩
  · intro y hy₁ hy₂
    rw [SimpleGraph.Walk.support_reverse, List.mem_reverse, hwq₂] at hy₂
    rw [hwp₂] at hy₁
    rcases List.mem_cons.1 hy₁ with rfl | h₁
    · exact Or.inl rfl
    rcases List.mem_cons.1 hy₂ with rfl | h₂
    · exact Or.inl rfl
    obtain ⟨g₁, hg₁, rfl⟩ := List.mem_map.1 h₁
    obtain ⟨g₂, hg₂, hg₂t⟩ := List.mem_map.1 h₂
    exact Or.inr (hmeet g₁ hg₁ g₂ hg₂ hg₂t.symm)
  · intro g hg hg'
    rw [SimpleGraph.Walk.edges_reverse, List.mem_reverse, hwq₁] at hg'
    rw [hwp₁] at hg
    obtain ⟨g₁, hg₁, rfl⟩ := List.mem_map.1 hg
    obtain ⟨g₂, hg₂, hg₂e⟩ := List.mem_map.1 hg'
    rcases Sym2.eq_iff.1 hg₂e with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
    · obtain rfl := N.simple g₂ g₁ h₁ h₂
      exact hboth g₂ hg₁ hg₂
    · exact not_reach_tgt_src g₁ (by rw [← h₂, ← h₁]; exact Relation.ReflTransGen.single ⟨g₂, rfl, rfl⟩)
  · rintro e (he | he)
    · rw [SimpleGraph.Walk.edges_append, List.mem_append, hwp₁]
      exact Or.inl (List.mem_map_of_mem he)
    · rw [SimpleGraph.Walk.edges_append, List.mem_append, SimpleGraph.Walk.edges_reverse, List.mem_reverse, hwq₁]
      exact Or.inr (List.mem_map_of_mem he)

/-- **Sites on which the parents of a recombination node differ** are on a common unoriented cycle (`g:hk_common_cycle`). -/
theorem exists_onCommonCycle_of_label_ne [Finite V] {e f : E} (hef : e ≠ f) (ht : N.tgt e = N.tgt f) {i j : ι}
    (hi : N.label (N.src e) i ≠ N.label (N.src f) i) (hj : N.label (N.src e) j ≠ N.label (N.src f) j) :
    N.OnCommonCycle (N.site i) (N.site j) := by
  obtain ⟨Qi, hQi, hei, -, hsi⟩ := GusfieldEtAl2004.exists_isCycle_of_label_ne hef ht hi
  obtain ⟨Qj, hQj, hej, -, hsj⟩ := GusfieldEtAl2004.exists_isCycle_of_label_ne hef ht hj
  obtain ⟨_, C₁, hC₁, hall₁⟩ := IsCycle.exists_walk hQi
  obtain ⟨_, C₂, hC₂, hall₂⟩ := IsCycle.exists_walk hQj
  exact exists_isCycle_of_share_edge hC₁ hC₂ (hall₁ e hei) (hall₂ e hej) (hall₁ _ hsi) (hall₂ _ hsj)

/-- A node breaking a set of sites has parents differing at one of them. -/
theorem exists_label_ne_of_breaksAt {e f : E} (hef : e ≠ f) (ht : N.tgt e = N.tgt f) {C : Set ι} (hb : N.BreaksAt (N.tgt e) C) :
    ∃ i ∈ C, N.label (N.src e) i ≠ N.label (N.src f) i := by
  by_contra hno
  push Not at hno
  refine hb e rfl (funext ?_)
  rintro ⟨i, hi⟩
  have := N.label_recomb e f hef ht i
  change N.label (N.tgt e) i = N.label (N.src e) i
  rcases this with h | h
  · exact h
  · rw [h, hno i hi]

end Network

/-! ### The conjecture -/

section Conjecture

variable {ι : Type*}

/-- Columns `i` and `j` of `M` are one split of the rows: equal or complementary. -/
def SameSplit (M : Finset (ι → Bool)) (i j : ι) : Prop :=
  (∀ r ∈ M, r i = r j) ∨ (∀ r ∈ M, r i ≠ r j)

/-- **The conjecture on the networks of this library** (`g:hk_conjecture_network`): a network with the fewest recombination nodes, with no constraint on crossovers, in which two different splits are in one component of `G(M)` exactly when the arcs of their sites are on a common unoriented cycle. It follows from `Conjecture22`, Conjecture 2.2 of the thesis (`husonKloepperConjecture_of_conjecture22`). -/
def HusonKloepperConjecture : Prop :=
  ∀ (m : ℕ) (M : Finset (Fin m → Bool)), M.Nonempty → NoConstantColumn M →
    ∃ (V E : Type) (_ : Finite V) (_ : Finite E) (N : Network (Fin m) V E), N.Derives M ∧ N.recombCount = R .multiple M ∧
      ∀ i j, ¬ SameSplit M i j → ((incompatGraph M).Reachable i j ↔ N.OnCommonCycle (N.site i) (N.site j))

end Conjecture

/-- Disjoint classes of recombination nodes add up: the nodes breaking `C₁` and those breaking `C₂`, when no node breaks both. -/
theorem add_breakCount_le {ι V E : Type*} [Finite V] (N : Network ι V E) {C₁ C₂ : Set ι} (h : ∀ x, N.IsRecomb x → N.BreaksAt x C₁ → ¬ N.BreaksAt x C₂) :
    MyersGriffiths2003.breakCount N C₁ + MyersGriffiths2003.breakCount N C₂ ≤ N.recombCount := by
  have : Fintype V := Fintype.ofFinite V
  unfold MyersGriffiths2003.breakCount Network.recombCount
  simp only [Nat.card_eq_fintype_card, Fintype.card_subtype]
  rw [← Finset.card_union_of_disjoint]
  · refine Finset.card_le_card fun x hx => ?_
    rcases Finset.mem_union.1 hx with hx | hx
    · exact Finset.mem_filter.2 ⟨Finset.mem_univ _, (Finset.mem_filter.1 hx).2.1⟩
    · exact Finset.mem_filter.2 ⟨Finset.mem_univ _, (Finset.mem_filter.1 hx).2.1⟩
  · refine Finset.disjoint_left.2 fun x hx hx' => ?_
    obtain ⟨-, h₁, h₂⟩ := Finset.mem_filter.1 hx
    obtain ⟨-, -, h₃⟩ := Finset.mem_filter.1 hx'
    exact h x h₁ h₂ h₃

/-- The sites of the two components of Figure 8 are different splits. -/
theorem fig8_not_sameSplit : ∀ i j : Fin 10, i.val < 5 → 5 ≤ j.val → ¬ SameSplit fig8 i j := by
  unfold SameSplit
  decide +kernel

/-- **Line 590** (`g:hk_conjecture_false`). "This also establishes that Conjecture 1, recently stated in Huson and Klopper (2007), is false." By the matrix of Figure 8, as the thesis of the second author says: in a network with the property of the conjecture, no recombination node breaks both components of `G(M)`, so that the number of nodes is at least `R(M(C₁)) + R(M(C₂)) = 4`, while `R(M) ≤ 3`. -/
theorem husonKloepperConjecture_false : ¬ HusonKloepperConjecture := by
  intro hconj
  obtain ⟨V, E, _, _, N, hd, hcount, hprop⟩ := hconj 10 fig8 fig8_nonempty fig8_noConstantColumn
  have hbound : R .multiple fig8 ≤ 3 := unrootedConjecture_multiple_false.2.1
  obtain ⟨h₁, h₂⟩ := fig8_two_le_R
  have hb₁ := MyersGriffiths2003.R_multiple_restrictRows_le_breakCount N fig8_nonempty fig8_noConstantColumn hd.displays fig8C₁
  have hb₂ := MyersGriffiths2003.R_multiple_restrictRows_le_breakCount N fig8_nonempty fig8_noConstantColumn hd.displays fig8C₂
  have hdis : ∀ x, N.IsRecomb x → N.BreaksAt x fig8C₁ → ¬ N.BreaksAt x fig8C₂ := by
    rintro x ⟨e, f, hef, rfl, hf⟩ hb₁' hb₂'
    obtain ⟨i, hi, hine⟩ := Network.exists_label_ne_of_breaksAt hef hf.symm hb₁'
    obtain ⟨j, hj, hjne⟩ := Network.exists_label_ne_of_breaksAt hef hf.symm hb₂'
    have hi' : i.val < 5 := hi
    have hj' : 5 ≤ j.val := hj
    have hcycle := Network.exists_onCommonCycle_of_label_ne hef hf.symm hine hjne
    have hreach := (hprop i j (fig8_not_sameSplit i j hi' hj')).2 hcycle
    have hiff := (fig8_reachable i j).1 hreach
    have hjC : j ∈ fig8C₁ := hiff.1 hi
    have hj'' : j.val < 5 := hjC
    omega
  have hadd := add_breakCount_le N hdis
  omega

/-! ### The networks of the thesis -/

/-- **Definition 2.1 of the thesis** (`g:hk_reticulate_network`): a rooted reticulate network on the taxa `X`. One root; every other vertex has one or two arcs in, that is, it's a tree vertex or a reticulation; "the set of leaves consists only of tree vertices and is labeled by the set of taxa `X`, that is, `λ` maps `X` bijectively onto `L`". It's connected by the condition on the root, as it's finite and acyclic. -/
structure ReticulateNetwork (X V E : Type*) where
  /-- The source of an arc. -/
  src : E → V
  /-- The target of an arc. -/
  tgt : E → V
  /-- The root. -/
  root : V
  /-- The labelling `λ` of the leaves. -/
  taxon : X → V
  simple : ∀ e f, src e = src f → tgt e = tgt f → e = f
  acyclic : ∀ v, ¬ Relation.TransGen (fun a b => ∃ e, src e = a ∧ tgt e = b) v v
  root_iff : ∀ v, (∀ e, tgt e ≠ v) ↔ v = root
  inDegree_le_two : ∀ e f g, tgt e = tgt f → tgt f = tgt g → e = f ∨ e = g ∨ f = g
  taxon_injective : Function.Injective taxon
  isLeaf_iff : ∀ v, (∀ e, src e ≠ v) ↔ ∃ x, taxon x = v
  leaf_tree : ∀ x e f, tgt e = taxon x → tgt f = taxon x → e = f

namespace ReticulateNetwork

variable {X V E : Type*} (N : ReticulateNetwork X V E)

/-- A tree edge: "a tree edge leading to a vertex of indegree one". -/
def IsTreeEdge (e : E) : Prop := ∀ f, N.tgt f = N.tgt e → f = e

/-- A reticulation. -/
def IsRetic (x : V) : Prop := ∃ e f, e ≠ f ∧ N.tgt e = x ∧ N.tgt f = x

/-- The number of reticulations. -/
noncomputable def reticCount : ℕ := Nat.card {x // N.IsRetic x}

/-- A sampling: the arcs kept when "choosing and removing one reticulation edge `p(r_i)` or `q(r_i)` for each reticulation". -/
def IsSampling (keep : E → Prop) : Prop :=
  (∀ e, N.IsTreeEdge e → keep e) ∧ ∀ e f, e ≠ f → N.tgt e = N.tgt f → (keep e ↔ ¬ keep f)

/-- The vertex `v` is below the arc `e`, in the tree of the sampling. -/
def Below (keep : E → Prop) (e : E) (v : V) : Prop :=
  Relation.ReflTransGen (fun a b => ∃ g, keep g ∧ N.src g = a ∧ N.tgt g = b) (N.tgt e) v

/-- The arcs `e` and `f` are contained in a common unoriented cycle. -/
def OnCommonCycle (e f : E) : Prop :=
  ∃ (v : V) (c : (SimpleGraph.fromRel fun a b => ∃ g, N.src g = a ∧ N.tgt g = b).Walk v v), c.IsCycle ∧ s(N.src e, N.tgt e) ∈ c.edges ∧ s(N.src f, N.tgt f) ∈ c.edges

variable {N}

theorem IsSampling.unique {keep : E → Prop} (h : N.IsSampling keep) {g g' : E} (hg : keep g) (hg' : keep g') (ht : N.tgt g = N.tgt g') : g = g' := by
  by_contra hne
  exact (h.2 g g' hne ht).1 hg hg'

theorem not_below_src (keep : E → Prop) (e : E) : ¬ N.Below keep e (N.src e) := by
  intro h
  have hreach : ∀ v, N.Below keep e v → Relation.ReflTransGen (fun a b => ∃ g, N.src g = a ∧ N.tgt g = b) (N.tgt e) v := by
    intro v hv
    induction hv with
    | refl => exact Relation.ReflTransGen.refl
    | tail _ hs ih =>
      obtain ⟨g, -, h₁, h₂⟩ := hs
      exact ih.tail ⟨g, h₁, h₂⟩
  exact N.acyclic _ (Relation.TransGen.head' ⟨e, rfl, rfl⟩ (hreach _ h))

/-- Along a kept arc, other than one into the target of `e`: below its target exactly when below its source. -/
theorem below_tgt_iff {keep : E → Prop} (h : N.IsSampling keep) {e g : E} (hg : keep g) (hne : N.tgt e ≠ N.tgt g) :
    N.Below keep e (N.tgt g) ↔ N.Below keep e (N.src g) := by
  constructor
  · intro hb
    rcases Relation.ReflTransGen.cases_tail hb with h₁ | ⟨c, hc, g', hg', rfl, h₂⟩
    · exact absurd h₁.symm hne
    · obtain rfl := h.unique hg' hg h₂
      exact hc
  · exact fun hb => Relation.ReflTransGen.tail hb ⟨g, hg, rfl, rfl⟩

/-! ### From a reticulate network to a network -/

variable {ι : Type*} {M : Finset (ι → Bool)}

/-- The split of the column `i` of `M` is in `Σ(e)`, for the taxa that are the rows of `M`: in the tree of some sampling, the rows below `e` are those in one state `c` of the column. -/
def HasSplit (N : ReticulateNetwork M V E) (e : E) (i : ι) : Prop :=
  ∃ (keep : E → Prop) (c : Bool), N.IsSampling keep ∧ ∀ x : M, x.1 i = c ↔ N.Below keep e (N.taxon x)

/-- `N` explains the splits of `M`: each is in `Σ(e)` for a tree edge `e`. -/
def Explains (N : ReticulateNetwork M V E) : Prop := ∀ i, ∃ e, N.IsTreeEdge e ∧ N.HasSplit e i

/-- **A reticulate network, with its sampled splits, is a network** (`g:hk_to_network`): the site `i` on its tree edge, and the states given by the sampled tree. It has no constraint on crossovers: a reticulation copies, at each site, the parent kept for that site. -/
noncomputable def toNetwork (N : ReticulateNetwork X V E) (site : ι → E) (keep : ι → E → Prop) (c : ι → Bool) (hsite : ∀ i, N.IsTreeEdge (site i)) (hkeep : ∀ i, N.IsSampling (keep i)) : Network ι V E where
  src := N.src
  tgt := N.tgt
  root := N.root
  site := site
  label v i := if N.Below (keep i) (site i) v then c i else !c i
  simple := N.simple
  acyclic := N.acyclic
  root_iff := N.root_iff
  inDegree_le_two := N.inDegree_le_two
  site_not_recomb i f hf := hsite i f hf
  label_tree := by
    intro e he i
    by_cases hs : site i = e
    · subst hs
      have h₁ : N.Below (keep i) (site i) (N.tgt (site i)) := Relation.ReflTransGen.refl
      have h₂ := not_below_src (N := N) (keep i) (site i)
      simp [h₁, h₂]
    · have hne : N.tgt (site i) ≠ N.tgt e := fun h => hs (he _ h)
      have hiff := below_tgt_iff (hkeep i) ((hkeep i).1 e he) hne
      simp only [hs, ↓reduceIte, hiff]
  label_recomb := by
    intro e f hef ht i
    have hsame : ∀ {g : E}, keep i g → (∃ g', g' ≠ g ∧ N.tgt g' = N.tgt g) →
        (if N.Below (keep i) (site i) (N.tgt g) then c i else !c i) = if N.Below (keep i) (site i) (N.src g) then c i else !c i := by
      rintro g hg ⟨g', hne, hg'⟩
      have hne' : N.tgt (site i) ≠ N.tgt g := by
        intro h
        have h₁ : g = site i := hsite i g h.symm
        have h₂ : g' = site i := hsite i g' (hg'.trans h.symm)
        exact hne (h₂.trans h₁.symm)
      simp only [below_tgt_iff (hkeep i) hg hne']
    by_cases hk : keep i e
    · exact Or.inl (hsame hk ⟨f, hef.symm, ht.symm⟩)
    · have hkf : keep i f := by
        by_contra hc
        exact hk (((hkeep i).2 e f hef ht).2 hc)
      refine Or.inr ?_
      rw [ht]
      exact hsame hkf ⟨e, hef, ht⟩

/-- The rows are the labels of the leaves. -/
theorem toNetwork_derives (N : ReticulateNetwork M V E) (site : ι → E) (keep : ι → E → Prop) (c : ι → Bool) (hsite : ∀ i, N.IsTreeEdge (site i)) (hkeep : ∀ i, N.IsSampling (keep i))
    (hsplit : ∀ i (x : M), x.1 i = c i ↔ N.Below (keep i) (site i) (N.taxon x)) : (N.toNetwork site keep c hsite hkeep).Derives M := by
  have hlabel : ∀ x : M, (N.toNetwork site keep c hsite hkeep).label (N.taxon x) = x.1 := by
    intro x
    funext i
    change (if N.Below (keep i) (site i) (N.taxon x) then c i else !c i) = x.1 i
    by_cases hb : N.Below (keep i) (site i) (N.taxon x)
    · rw [ite_eq_left hb]
      exact ((hsplit i x).2 hb).symm
    · rw [ite_eq_right hb]
      have : x.1 i ≠ c i := fun h => hb ((hsplit i x).1 h)
      revert this
      cases x.1 i <;> cases c i <;> simp
  have hleaf : ∀ v, (N.toNetwork site keep c hsite hkeep).IsLeaf v ↔ ∃ x, N.taxon x = v := N.isLeaf_iff
  refine ⟨?_, ?_, ?_⟩
  · intro v hv
    obtain ⟨x, rfl⟩ := (hleaf v).1 hv
    rw [hlabel]
    exact x.2
  · intro v hv w hw hvw
    obtain ⟨x, rfl⟩ := (hleaf v).1 hv
    obtain ⟨y, rfl⟩ := (hleaf w).1 hw
    rw [hlabel, hlabel] at hvw
    rw [Subtype.ext hvw]
  · intro r hr
    exact ⟨N.taxon ⟨r, hr⟩, (hleaf _).2 ⟨_, rfl⟩, hlabel ⟨r, hr⟩⟩

/-- The sites, samplings and states of a network that explains the splits. -/
theorem Explains.exists_data {N : ReticulateNetwork M V E} (h : N.Explains) :
    ∃ (site : ι → E) (keep : ι → E → Prop) (c : ι → Bool), (∀ i, N.IsTreeEdge (site i)) ∧ (∀ i, N.IsSampling (keep i)) ∧
      (∀ i (x : M), x.1 i = c i ↔ N.Below (keep i) (site i) (N.taxon x)) ∧ ∀ i, N.HasSplit (site i) i := by
  choose site hsite hs using h
  choose keep c hkeep hsplit using hs
  exact ⟨site, keep, c, hsite, hkeep, hsplit, fun i => ⟨keep i, c i, hkeep i, hsplit i⟩⟩

/-- **The reticulations are at least `R(M)`** (`g:hk_R_le`). -/
theorem R_multiple_le_reticCount [LinearOrder ι] [Finite V] [Finite E] {N : ReticulateNetwork M V E} (h : N.Explains) : R .multiple M ≤ N.reticCount := by
  obtain ⟨site, keep, c, hsite, hkeep, hsplit, -⟩ := h.exists_data
  obtain ⟨a, b, N', _, _, hiso⟩ := (N.toNetwork site keep c hsite hkeep).exists_fin_iso
  obtain ⟨h₁, -, h₃, -, -⟩ := hiso.invariants
  have hle : R .multiple M ≤ N'.recombCount := Nat.sInf_le ⟨a, b, N', trivial, (h₃ M).2 (toNetwork_derives N site keep c hsite hkeep hsplit), rfl⟩
  rw [h₁] at hle
  exact hle

/-! ### From a network to a reticulate network -/

theorem exists_leaf_of_mem {N : Network ι V E} (hd : N.Derives M) (x : M) : ∃ v, N.IsLeaf v ∧ N.label v = x.1 := hd.surjOn x.2

/-- The leaf of a row. -/
noncomputable def leafOf {N : Network ι V E} (hd : N.Derives M) (x : M) : V := (exists_leaf_of_mem hd x).choose

theorem leafOf_isLeaf {N : Network ι V E} (hd : N.Derives M) (x : M) : N.IsLeaf (leafOf hd x) := (exists_leaf_of_mem hd x).choose_spec.1

theorem label_leafOf {N : Network ι V E} (hd : N.Derives M) (x : M) : N.label (leafOf hd x) = x.1 := (exists_leaf_of_mem hd x).choose_spec.2

/-- **A network for `M` with no recombination node as a leaf is a reticulate network on the rows** (`g:hk_of_network`). -/
noncomputable def ofNetwork (N : Network ι V E) (hd : N.Derives M) (hleaf : ∀ v, N.IsLeaf v → ¬ N.IsRecomb v) : ReticulateNetwork M V E where
  src := N.src
  tgt := N.tgt
  root := N.root
  taxon x := leafOf hd x
  simple := N.simple
  acyclic := N.acyclic
  root_iff := N.root_iff
  inDegree_le_two := N.inDegree_le_two
  taxon_injective := by
    intro x y hxy
    have hxy' : leafOf hd x = leafOf hd y := hxy
    apply Subtype.ext
    rw [← label_leafOf hd x, ← label_leafOf hd y, hxy']
  isLeaf_iff := by
    intro v
    constructor
    · intro hv
      have hmem : N.label v ∈ M := hd.mapsTo hv
      exact ⟨⟨N.label v, hmem⟩, hd.injOn (leafOf_isLeaf hd _) hv (label_leafOf hd _)⟩
    · rintro ⟨x, rfl⟩
      exact leafOf_isLeaf hd x
  leaf_tree := by
    intro x e f he hf
    by_contra hne
    exact hleaf _ (leafOf_isLeaf hd x) ⟨e, f, hne, he, hf⟩

/-- **A network for `M` explains the splits of `M`, each on the arc of its site** (`g:hk_explains`). At each reticulation, the sampling for a site keeps a parent with the state of the reticulation. Then the nodes below the arc of the site, in the sampled tree, are those off the root's state. -/
theorem ofNetwork_explains [Finite V] (N : Network ι V E) (hd : N.Derives M) (hleaf : ∀ v, N.IsLeaf v → ¬ N.IsRecomb v) : (ofNetwork N hd hleaf).Explains := by
  intro i
  refine ⟨N.site i, fun f hf => N.site_not_recomb i f hf, ?_⟩
  have hpick : ∀ x, N.IsRecomb x → ∃ g, N.tgt g = x ∧ N.label (N.src g) i = N.label x i := by
    rintro x ⟨e, f, hef, rfl, hf⟩
    rcases N.label_recomb e f hef hf.symm i with h | h
    · exact ⟨e, rfl, h.symm⟩
    · exact ⟨f, hf, h.symm⟩
  choose pick hpick₁ hpick₂ using hpick
  have hpc : ∀ {x y : V} (_ : x = y) (h : N.IsRecomb x) (h' : N.IsRecomb y), pick x h = pick y h' := by
    rintro x y rfl h h'
    rfl
  set R := ofNetwork N hd hleaf with hR
  set keep : E → Prop := fun g => (∀ f, N.tgt f = N.tgt g → f = g) ∨ ∃ h : N.IsRecomb (N.tgt g), pick _ h = g with hkeep
  have hsamp : R.IsSampling keep := by
    refine ⟨fun e he => Or.inl he, fun e f hef ht => ?_⟩
    have hx : N.IsRecomb (N.tgt e) := ⟨e, f, hef, rfl, ht.symm⟩
    have hntree : ∀ g, N.tgt g = N.tgt e → (∃ g', g' ≠ g ∧ N.tgt g' = N.tgt g) := by
      intro g hg
      by_cases hge : g = e
      · exact ⟨f, hge ▸ hef.symm, by rw [hge]; exact ht.symm⟩
      · exact ⟨e, fun h => hge h.symm, hg.symm⟩
    have hnt : ∀ g, N.tgt g = N.tgt e → (keep g ↔ pick _ hx = g) := by
      intro g hg
      constructor
      · rintro (h | ⟨h, hp⟩)
        · obtain ⟨g', hne, hg'⟩ := hntree g hg
          exact absurd (h g' hg') hne
        · exact (hpc hg.symm hx h).trans hp
      · intro hp
        have hx' : N.IsRecomb (N.tgt g) := hg ▸ hx
        exact Or.inr ⟨hx', (hpc hg hx' hx).trans hp⟩
    have hmem := Network.eq_or_eq_of_tgt hef ht (hpick₁ _ hx)
    rw [hnt e rfl, hnt f ht.symm]
    rcases hmem with h | h
    · rw [h]
      exact ⟨fun _ hc => hef hc, fun _ => rfl⟩
    · rw [h]
      exact ⟨fun hc _ => hef hc.symm, fun hc => absurd rfl hc⟩
  have hbelow : ∀ v, R.Below keep (N.site i) v ↔ N.label v i ≠ N.label N.root i := by
    intro v
    constructor
    · intro hb
      induction hb with
      | refl => exact N.label_tgt_site_ne i
      | @tail a b _ hstep ih =>
        obtain ⟨g, hg, rfl, rfl⟩ := hstep
        rcases hg with hg | ⟨hx, hp⟩
        · have hl := N.label_tree g hg i
          by_cases hs : N.site i = g
          · subst hs
            exact absurd (N.reach_of_label_ne ih) (N.not_reach_tgt_src _)
          · rw [ite_eq_right hs] at hl
            change N.label (N.tgt g) i ≠ _
            rw [hl]
            exact ih
        · change N.label (N.tgt g) i ≠ _
          rw [← hpick₂ _ hx]
          have hgp : pick _ hx = g := hp
          rw [hgp]
          exact ih
    · induction v using N.arc_induction with
      | _ v ih =>
        intro hv
        by_cases htop : v = N.tgt (N.site i)
        · rw [htop]
          exact Relation.ReflTransGen.refl
        have hroot : v ≠ N.root := fun h => hv (by rw [h])
        by_cases hx : N.IsRecomb v
        · have hg₁ := hpick₁ v hx
          have hg₂ := hpick₂ v hx
          have hbelow' : R.Below keep (N.site i) (N.src (pick v hx)) := ih _ hg₁ (by rw [hg₂]; exact hv)
          refine Relation.ReflTransGen.tail hbelow' ⟨pick v hx, Or.inr ?_, rfl, hg₁⟩
          have hx' : N.IsRecomb (N.tgt (pick v hx)) := by
            rw [hg₁]
            exact hx
          exact ⟨hx', hpc hg₁ hx' hx⟩
        · obtain ⟨g, hg⟩ : ∃ g, N.tgt g = v := by
            by_contra hno
            push Not at hno
            exact hroot ((N.root_iff v).1 hno)
          have htree : ∀ f, N.tgt f = N.tgt g → f = g := fun f hf => by
            by_contra hne
            exact hx ⟨f, g, hne, hf.trans hg, hg⟩
          have hl := N.label_tree g htree i
          have hs : N.site i ≠ g := fun h => htop (by rw [← hg, h])
          rw [ite_eq_right hs, hg] at hl
          have hbelow' := ih g hg (by rw [← hl]; exact hv)
          exact Relation.ReflTransGen.tail hbelow' ⟨g, Or.inl htree, rfl, hg⟩
  refine ⟨keep, !N.label N.root i, hsamp, fun x => ?_⟩
  have hx₁ : N.label (R.taxon x) = x.1 := label_leafOf hd x
  rw [hbelow, hx₁]
  cases x.1 i <;> cases N.label N.root i <;> simp

/-- **The fewest reticulations explaining the splits of `M` are `R(M)`** (`g:hk_exists`): the bridge to `R` of multiple crossovers. A network for `M` gets a pendant arc for each row, which is what `Gusfield2007.Network.trim` does, so that the leaves are tree vertices. -/
theorem exists_reticulateNetwork {ι : Type} [LinearOrder ι] [Finite ι] {M : Finset (ι → Bool)} (hM : M.Nonempty) (hC : NoConstantColumn M) :
    ∃ (V E : Type) (_ : Finite V) (_ : Finite E) (N : ReticulateNetwork M V E), N.Explains ∧ N.reticCount = R .multiple M := by
  obtain ⟨a, b, N₀, -, hd, hcount⟩ := Nat.sInf_mem (recombSet_nonempty .multiple hM)
  choose anchor hanchor using fun r : M => hd.displays r.1 r.2
  have hsite := fun i => Network.kept_tgt_site (N := N₀) (anchor := anchor) hanchor (hC.exists_ne (N₀.label N₀.root) i)
  set N₁ := N₀.trim anchor hM hanchor hsite with hN₁
  have hleaf : ∀ v, N₁.IsLeaf v → ¬ N₁.IsRecomb v := by
    intro v hv
    obtain ⟨r, rfl⟩ := (Network.trim_isLeaf_iff (N := N₀) (anchor := anchor) (hM := hM) (hanchor := hanchor) (hsite := hsite) v).1 hv
    exact Network.not_trim_isRecomb_inr
  have hd₁ : N₁.Derives M := Network.trim_derives
  have hexp := ofNetwork_explains N₁ hd₁ hleaf
  refine ⟨_, _, inferInstance, inferInstance, ofNetwork N₁ hd₁ hleaf, hexp, le_antisymm ?_ (R_multiple_le_reticCount hexp)⟩
  have h₁ : (ofNetwork N₁ hd₁ hleaf).reticCount = N₁.recombCount := rfl
  rw [h₁]
  refine (Network.trim_recombCount_le (N := N₀) (anchor := anchor) (hM := hM) (hanchor := hanchor) (hsite := hsite)).trans ?_
  have h₂ : N₀.recombCount = R .multiple M := hcount
  rw [← h₂]
  exact Nat.card_le_card_of_injective (fun x : {x // N₀.IsRecomb x ∧ N₀.Kept anchor x} => (⟨x.1, x.2.1⟩ : {x // N₀.IsRecomb x}))
    fun _ _ h => Subtype.ext (congrArg (fun z : {x // N₀.IsRecomb x} => z.1) h)

end ReticulateNetwork

/-- **Conjecture 2.2 of the thesis, which is Conjecture 1 of Huson and Klöpper 2007** (`g:hk_conjecture`). "Given an input set of splits `Δ`, a minimal reticulation network `N` exists that explains `Δ` so that for any two tree edges `e` and `f` of `N` we have the following: Any two splits `S ∈ Δ ∩ Σ(e)` and `S′ ∈ Δ ∩ Σ(f)` are contained in the same connected component of `IG(Δ)` if and only if `e` and `f` are contained in a common unoriented cycle of `N`." The splits are the columns of `M`, the taxa its rows, and `S`, `S′` are different splits. Of "minimal", only the number of reticulations is kept. See the module's docstring for this reading. -/
def Conjecture22 : Prop :=
  ∀ (m : ℕ) (M : Finset (Fin m → Bool)), M.Nonempty → NoConstantColumn M →
    ∃ (V E : Type) (_ : Finite V) (_ : Finite E) (N : ReticulateNetwork M V E), N.Explains ∧
      (∀ (V' E' : Type) [Finite V'] [Finite E'] (N' : ReticulateNetwork M V' E'), N'.Explains → N.reticCount ≤ N'.reticCount) ∧
      ∀ e f, N.IsTreeEdge e → N.IsTreeEdge f → ∀ i j, ¬ SameSplit M i j → N.HasSplit e i → N.HasSplit f j →
        ((incompatGraph M).Reachable i j ↔ N.OnCommonCycle e f)

/-- The conjecture of the thesis implies the statement on the networks of this library, by the bridge. -/
theorem husonKloepperConjecture_of_conjecture22 (h : Conjecture22) : HusonKloepperConjecture := by
  intro m M hM hC
  obtain ⟨V, E, _, _, N, hexp, hmin, hprop⟩ := h m M hM hC
  obtain ⟨site, keep, c, hsite, hkeep, hsplit, hs⟩ := hexp.exists_data
  refine ⟨V, E, inferInstance, inferInstance, N.toNetwork site keep c hsite hkeep, ReticulateNetwork.toNetwork_derives N site keep c hsite hkeep hsplit, ?_, ?_⟩
  · obtain ⟨V', E', _, _, N', hexp', hcount'⟩ := ReticulateNetwork.exists_reticulateNetwork hM hC
    refine le_antisymm ?_ (ReticulateNetwork.R_multiple_le_reticCount hexp)
    rw [← hcount']
    exact hmin V' E' N' hexp'
  · intro i j hij
    exact hprop _ _ (hsite i) (hsite j) i j hij (hs i) (hs j)

/-- **Line 590, for the conjecture as the thesis states it** (`g:hk_conjecture22_false`). "Interestingly, our conjecture is not true in general, as was shown in [DGS07]." -/
theorem conjecture22_false : ¬ Conjecture22 :=
  fun h => husonKloepperConjecture_false (husonKloepperConjecture_of_conjecture22 h)

end Gusfield2007
