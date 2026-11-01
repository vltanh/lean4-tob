module

public import External.AllmanBanosRhodes2019.Proposition9

/-!
# The source's induced quartet networks and types of cycle

The source reads everything about four taxa on `N⁻`, the unrooted network of its Definition 4, through the quartet network
of its Definition 5, and on it the `m_k`-cycles (line 399). This module defines them as printed, on a binary level-1 rooted
network, and proves that `HasThreeTwoCycle` of `NANUQ.lean`, stated by blocks, is the source's `3₂`-cycle.

## The definitions

* `IsMinusArc`, `SemiStep`, `IsSemiPath`, `IsSimpleTrek`, `trekArcs`: Definition 5, step 1, "keeping only the edges in simple
  treks between pairs of elements of `{a, b, c, d}`", with "a trek between vertices `x, y` on a network is the union of
  semidirected paths from some vertex `v` to `x` and from `v` to `y`. A trek is simple if the two paths intersect only at `v`"
  (lines 269-277). In `N⁻` a path may go along an arc, or against a tree arc, which is undirected there. The arcs of `N⁻` are
  those not above `LSA(X)`.
* `keptDegree`, `IsQuartetCycle`, `cycleSize`, `cycleDescendants`, `HasCycleType`: Definition 5, step 2, "suppressing all
  degree two nodes", and "an `m_k`-cycle in a level-1 network" is "an `m`-cycle with exactly `k` taxa descended from its unique
  hybrid node" (line 399). On a level-1 network "a blob is simply an undirected version of a cycle" (line 1381), and a blob has
  a unique hybrid node. Suppressing removes exactly the vertices of degree two, so the size of a cycle of the suppressed graph
  is the number of its vertices of degree other than two.

Representation. This module keeps `LSA(X)`, which Definition 4 suppresses: its two arcs stay, and a path of `N⁻` through the suppressed
vertex is a path through it here. It is a vertex of degree two of `N⁻` before suppression, so that Definition 5 suppresses it in any case,
if the arcs at it are kept (`keptDegree_lsa_le`). `QuartetSemidirected.lean` reads Definition 5 on `AllmanEtAl2023.semidirected`, which is
`N⁻` with the suppression carried out, and proves that the two readings keep the same edges (`mem_sTrekEdges_iff`, `image_sTrekEdges`) and
give each vertex the same degree (`sKeptDegree_eq`).

## The results

* `trekArcs_eq_wedgeArcs`: the arcs of Definition 5 are the arcs of TOB-QMC's subnetwork, `RootedNetwork.wedgeArcs`, for
  every network. A simple trek of `N⁻` is a directed trek of `N⁺`: a semidirected path goes up tree arcs, and then down, and two
  paths that both went up would share their first arc (`IsSemiPath.exists_wedge`, `IsSimpleTrek.exists_wedge`).
* `isQuartetCycle_iff`: a cycle of `N` is kept when it has a taxon of `q` below its reticulation, and one not below it.
* `keptDegree_ne_two_iff`, `cycleSize_eq`: a vertex of a kept cycle has degree other than two exactly when a taxon of `q` attaches
  there. So the size of the cycle is the number of blocks with a taxon of `q`.
* `hasThreeTwoCycle_iff`: **`HasThreeTwoCycle` is the source's `3₂`-cycle.**
-/

@[expose] public noncomputable section

open Phylogenetics Phylogenetics.RootedNetwork Finset
open TOBQMC TOBQMC.Level1
open scoped Classical

namespace External.AllmanBanosRhodes2019.Quartet

variable {V E X : Type*}

/-! ### The definitions -/

section Defs

variable (N : RootedNetwork V E X)

/-- **Definition 4** (`nanuq:definition4`), its arcs: `N⁻` is obtained by "deleting all edges and nodes above `LSA(X)`, undirecting all
tree edges, and suppressing `LSA(X)`". The undirecting is `SemiStep`, and `LSA(X)` is not suppressed here: see the module's docstring. -/
def IsMinusArc (e : E) : Prop :=
  ∀ l, N.IsLeastStableAncestor Set.univ l → N.graph.Reaches l (N.graph.source e)

/-- One step of a semidirected path of `N⁻`, on the edge `e` from `u` to `w`: along an arc, or against a tree arc, which `N⁻`
undirects. -/
def SemiStep (e : E) (u w : V) : Prop :=
  IsMinusArc N e ∧ ((N.graph.source e = u ∧ N.graph.target e = w) ∨
    (N.IsTreeArc e ∧ N.graph.target e = u ∧ N.graph.source e = w))

/-- A semidirected walk from `u` to `w`, as its steps: the edge, and the vertex that it leads to. -/
def IsSemiWalk : V → List (E × V) → V → Prop
  | u, [], w => u = w
  | u, s :: l, w => SemiStep N s.1 u s.2 ∧ IsSemiWalk s.2 l w

/-- A semidirected path: a semidirected walk with distinct vertices. -/
structure IsSemiPath (u : V) (l : List (E × V)) (w : V) : Prop where
  walk : IsSemiWalk N u l w
  nodup : (u :: l.map Prod.snd).Nodup

/-- A simple trek between `a` and `b`: semidirected paths from `v` to `a` and from `v` to `b` that "intersect only at `v`". -/
structure IsSimpleTrek (a b v : V) (l₁ l₂ : List (E × V)) : Prop where
  left : IsSemiPath N v l₁ a
  right : IsSemiPath N v l₂ b
  disjoint : ∀ z ∈ l₁.map Prod.snd, z ∉ l₂.map Prod.snd

/-- **Definition 5, step 1** (`nanuq:definition5`): the edges in simple treks between pairs of elements of `q`. -/
def trekArcs (q : Finset X) : Set E :=
  {e | ∃ x ∈ q, ∃ y ∈ q, x ≠ y ∧ ∃ v l₁ l₂, IsSimpleTrek N (N.leaf x) (N.leaf y) v l₁ l₂ ∧
    (e ∈ l₁.map Prod.fst ∨ e ∈ l₂.map Prod.fst)}

/-- The degree of a vertex in the graph of the kept edges. -/
def keptDegree (q : Finset X) (u : V) : ℕ :=
  {e | e ∈ trekArcs N q ∧ N.graph.target e = u}.ncard + {e | e ∈ trekArcs N q ∧ N.graph.source e = u}.ncard

/-- The cycle with hybrid node `h`, the blob of `h`, is a cycle of the quartet network on `q`: all its edges are kept. -/
def IsQuartetCycle (q : Finset X) (h : V) : Prop :=
  2 ≤ N.graph.indegree h ∧ ∀ f ∈ N.graph.blobArcs h, f ∈ trekArcs N q

/-- The number of edges of the cycle with hybrid node `h`, after "suppressing all degree two nodes": it has as many edges as
vertices, and those left are the vertices of degree other than two. -/
def cycleSize (q : Finset X) (h : V) : ℕ :=
  {u | N.graph.blobSetoid h u ∧ keptDegree N q u ≠ 2}.ncard

/-- The number of taxa of `q` descended from the hybrid node `h`. -/
def cycleDescendants (q : Finset X) (h : V) : ℕ :=
  (q.filter fun x => N.graph.Reaches h (N.leaf x)).card

/-- **An `m_k`-cycle** of the quartet network on `q` (line 399). -/
def HasCycleType (q : Finset X) (m k : ℕ) : Prop :=
  ∃ h, IsQuartetCycle N q h ∧ cycleSize N q h = m ∧ cycleDescendants N q h = k

end Defs

variable {N : RootedNetwork V E X}

/-! ### Simple treks are directed -/

/-- **A simple semidirected path goes up tree arcs, and then down.** After a step along an arc, the next cannot go against a tree
arc: a tree arc is the only arc into its target, so it would go back. -/
theorem IsSemiPath.exists_wedge (hN : N.IsPhylogenetic) {u w : V} {l : List (E × V)} (h : IsSemiPath N u l w) :
    ∃ t p r, N.IsDirPath t p u ∧ N.IsDirPath t r w ∧ (∀ f ∈ p, N.IsTreeArc f) ∧
      l.map Prod.fst = p.reverse ++ r ∧
      u :: l.map Prod.snd = (p.map N.graph.target).reverse ++ t :: r.map N.graph.target := by
  induction l generalizing u with
  | nil =>
    obtain rfl : u = w := h.walk
    exact ⟨u, [], [], rfl, rfl, by simp, by simp, by simp⟩
  | cons s l ih =>
    obtain ⟨e, w'⟩ := s
    obtain ⟨hstep, hwalk⟩ := h.walk
    have hnd := h.nodup
    simp only [List.map_cons] at hnd
    obtain ⟨hu, hnd'⟩ := List.nodup_cons.1 hnd
    obtain ⟨t, p, r, hp, hr, htree, harcs, hverts⟩ := ih ⟨hwalk, hnd'⟩
    rcases hstep.2 with ⟨hs, ht⟩ | ⟨htr, ht, hs⟩
    · -- along the arc `e`: the rest of the path does not go up
      have hp0 : p = [] := by
        rcases List.eq_nil_or_concat p with rfl | ⟨p', f, rfl⟩
        · rfl
        · exfalso
          rw [List.concat_eq_append] at hp htree hverts
          obtain ⟨c, hc, hc'⟩ := isDirPath_append.1 hp
          obtain ⟨hcs, hct⟩ := hc'
          have hc'' : N.graph.target f = w' := hct
          have hf : N.IsTreeArc f := htree f (by simp)
          have hef : e = f := eq_of_indegree_le_one hN (e := f) (f := e) (le_of_eq hf) (ht.trans hc''.symm)
          have hsrc : N.graph.source f = u := by rw [← hef, hs]
          have hmem : u ∈ t :: p'.map N.graph.target := by
            have := hc.end_mem_vertices
            rwa [← hcs, hsrc] at this
          simp only [List.map_append, List.map_cons, List.map_nil, List.reverse_append, List.reverse_cons,
            List.reverse_nil, List.nil_append, List.cons_append] at hverts
          have hlist : l.map Prod.snd = (p'.map N.graph.target).reverse ++ t :: r.map N.graph.target :=
            (List.cons.inj hverts).2
          refine hu (List.mem_cons_of_mem _ ?_)
          rw [hlist]
          rcases List.mem_cons.1 hmem with h' | h'
          · simp [h']
          · simp [List.mem_reverse.2 h' |> List.mem_reverse.1]
      subst hp0
      obtain rfl : t = w' := hp
      refine ⟨u, [], e :: r, rfl, ⟨hs, by rw [ht]; exact hr⟩, by simp, ?_, ?_⟩
      · simpa using harcs
      · simp only [List.map_nil, List.reverse_nil, List.nil_append, List.map_cons] at hverts ⊢
        rw [ht]
        simp only [List.cons.injEq, true_and]
        exact (List.cons.inj hverts).2
    · -- against the tree arc `e`: the path up is one longer
      refine ⟨t, p ++ [e], r, ?_, hr, ?_, ?_, ?_⟩
      · exact hp.append ⟨hs, ht⟩
      · intro f hf
        rcases List.mem_append.1 hf with hf | hf
        · exact htree f hf
        · rw [List.mem_singleton.1 hf]
          exact htr
      · simp only [List.map_cons, List.reverse_append, List.reverse_cons, List.reverse_nil, List.nil_append,
          List.cons_append]
        rw [harcs]
      · simp only [List.map_cons, List.map_append, List.map_nil, List.reverse_append, List.reverse_cons,
          List.reverse_nil, List.nil_append, List.cons_append]
        rw [ht]
        simp only [List.cons.injEq, true_and]
        simpa using hverts

/-- **A simple trek of `N⁻` is a directed trek of `N⁺`**, on the same arcs. Two paths from `v` that both went up would share their
first arc, the only arc into `v`. If only the first goes up, its top is the summit of the trek, with the second path below `v`. -/
theorem IsSimpleTrek.exists_wedge (hN : N.IsPhylogenetic) {a b v : V} {l₁ l₂ : List (E × V)}
    (h : IsSimpleTrek N a b v l₁ l₂) :
    ∃ t p r, N.IsWedgePath a b t p r ∧ ∀ e, e ∈ p ∨ e ∈ r ↔ e ∈ l₁.map Prod.fst ∨ e ∈ l₂.map Prod.fst := by
  have hA := hN.acyclic
  obtain ⟨t₁, p₁, r₁, hp₁, hr₁, ht₁, ha₁, hv₁⟩ := h.left.exists_wedge hN
  obtain ⟨t₂, p₂, r₂, hp₂, hr₂, ht₂, ha₂, hv₂⟩ := h.right.exists_wedge hN
  -- the vertices of each path after `v`
  have htail : ∀ {t : V} {p r : List E} {l : List (E × V)}, N.IsDirPath t p v →
      v :: l.map Prod.snd = (p.map N.graph.target).reverse ++ t :: r.map N.graph.target →
      (∀ z ∈ r.map N.graph.target, z ∈ l.map Prod.snd) ∧ (∀ z ∈ p, N.graph.source z ∈ l.map Prod.snd) := by
    intro t p r l hp hv
    rcases List.eq_nil_or_concat p with rfl | ⟨p', f, rfl⟩
    · obtain rfl : t = v := hp
      simp only [List.map_nil, List.reverse_nil, List.nil_append, List.cons.injEq, true_and] at hv
      rw [hv]
      simp
    · rw [List.concat_eq_append] at hp hv ⊢
      simp only [List.map_append, List.map_cons, List.map_nil, List.reverse_append, List.reverse_cons,
        List.reverse_nil, List.nil_append, List.cons_append] at hv
      have hlist : l.map Prod.snd = (p'.map N.graph.target).reverse ++ t :: r.map N.graph.target :=
        (List.cons.inj hv).2
      rw [hlist]
      refine ⟨fun z hz => by simp [hz], fun z hz => ?_⟩
      obtain ⟨c, hc, hcs, hct⟩ := isDirPath_append.1 hp
      rcases List.mem_append.1 hz with hz | hz
      · rcases List.mem_cons.1 (hc.source_mem_vertices hz) with h' | h'
        · simp [h']
        · have : N.graph.source z ∈ p'.map N.graph.target := h'
          simp [this]
      · obtain rfl := List.mem_singleton.1 hz
        rw [hcs]
        rcases List.mem_cons.1 hc.end_mem_vertices with h' | h'
        · simp [h']
        · simp [h']
  obtain ⟨hin₁, hsrc₁⟩ := htail hp₁ hv₁
  obtain ⟨hin₂, hsrc₂⟩ := htail hp₂ hv₂
  -- only one goes up
  have hone : p₁ = [] ∨ p₂ = [] := by
    by_contra hcon
    push Not at hcon
    obtain ⟨hn₁, hn₂⟩ := hcon
    rcases List.eq_nil_or_concat p₁ with rfl | ⟨p', f, rfl⟩
    · exact hn₁ rfl
    rcases List.eq_nil_or_concat p₂ with rfl | ⟨p'', g, rfl⟩
    · exact hn₂ rfl
    rw [List.concat_eq_append] at hp₁ hp₂ ht₁ ht₂ hsrc₁ hsrc₂
    obtain ⟨c, -, -, hft⟩ := isDirPath_append.1 hp₁
    obtain ⟨c', -, -, hgt⟩ := isDirPath_append.1 hp₂
    have hft' : N.graph.target f = v := hft
    have hgt' : N.graph.target g = v := hgt
    have hfg : g = f := eq_of_indegree_le_one hN (e := f) (f := g) (le_of_eq (ht₁ f (by simp))) (hgt'.trans hft'.symm)
    exact h.disjoint _ (hsrc₁ f (by simp)) (hfg ▸ hsrc₂ g (by simp))
  -- the same, with the two paths in either order
  have key : ∀ {a b : V} {l₁ l₂ : List (E × V)} {t : V} {p r r₂ : List E}, N.IsDirPath t p v → N.IsDirPath t r a →
      N.IsDirPath v r₂ b → (∀ z ∈ l₁.map Prod.snd, z ∉ l₂.map Prod.snd) →
      (∀ z ∈ r₂.map N.graph.target, z ∈ l₂.map Prod.snd) →
      (v :: l₁.map Prod.snd).Nodup →
      v :: l₁.map Prod.snd = (p.map N.graph.target).reverse ++ t :: r.map N.graph.target →
      N.IsWedgePath a b t r (p ++ r₂) := by
    intro a b l₁ l₂ t p r r₂ hp hr hr₂ hd hin₂ hnd hv
    refine IsWedgePath.of_disjoint hA hr (hp.append hr₂) fun z hz hz' => ?_
    have hnod : ∀ w, w ∈ p.map N.graph.target → w ∉ r.map N.graph.target := by
      intro w hw hw'
      rw [hv] at hnd
      exact (List.nodup_append.1 hnd).2.2 w (List.mem_reverse.2 hw) w (by simp [hw']) rfl
    have hmem₁ : z ∈ l₁.map Prod.snd := by
      have hz₁ : z ∈ v :: l₁.map Prod.snd := by
        rw [hv]
        simp [hz]
      rcases List.mem_cons.1 hz₁ with rfl | h'
      · rcases List.mem_cons.1 hp.end_mem_vertices with h' | h'
        · exact absurd (h' ▸ hz) (hr.start_notMem hA)
        · exact absurd hz (hnod _ h')
      · exact h'
    simp only [List.map_append, List.mem_append] at hz'
    rcases hz' with hz' | hz'
    · exact hnod z hz' hz
    · exact hd z hmem₁ (hin₂ z hz')
  rcases hone with rfl | rfl
  · -- the first path does not go up
    obtain rfl : t₁ = v := hp₁
    have hw := key hp₂ hr₂ hr₁ (fun z hz hz' => h.disjoint z hz' hz) hin₁ h.right.nodup hv₂
    refine ⟨t₂, p₂ ++ r₁, r₂, hw.symm hA, fun e => ?_⟩
    rw [ha₁, ha₂]
    simp only [List.reverse_nil, List.nil_append, List.mem_append, List.mem_reverse]
    tauto
  · obtain rfl : t₂ = v := hp₂
    have hw := key hp₁ hr₁ hr₂ h.disjoint hin₂ h.left.nodup hv₁
    refine ⟨t₁, r₁, p₁ ++ r₂, hw, fun e => ?_⟩
    rw [ha₁, ha₂]
    simp only [List.reverse_nil, List.nil_append, List.mem_append, List.mem_reverse]
    tauto

/-- A directed path below a vertex is a semidirected path, as steps. -/
theorem IsDirPath.isSemiPath (hA : N.graph.IsAcyclic) {u w : V} {p : List E} (h : N.IsDirPath u p w)
    (hm : ∀ e ∈ p, IsMinusArc N e) : IsSemiPath N u (N.downSteps p) w := by
  refine ⟨?_, ?_⟩
  · induction p generalizing u with
    | nil => exact h
    | cons e p ih =>
      obtain ⟨rfl, h⟩ := h
      exact ⟨⟨hm e (by simp), Or.inl ⟨rfl, rfl⟩⟩, ih h fun f hf => hm f (by simp [hf])⟩
  · rw [map_snd_downSteps]
    exact List.nodup_cons.2 ⟨h.start_notMem hA, h.nodup hA⟩

/-- **The arcs of Definition 5 are those of TOB-QMC's subnetwork**: a simple trek of `N⁻` is a wedge path of `N⁺`, and conversely.
It holds for every phylogenetic network. -/
theorem trekArcs_eq_wedgeArcs (hN : N.IsPhylogenetic) (q : Finset X) :
    trekArcs N q = N.wedgeArcs (q : Set X) := by
  ext e
  constructor
  · rintro ⟨x, hx, y, hy, hxy, v, l₁, l₂, ht, he⟩
    obtain ⟨t, p, r, hw, hiff⟩ := ht.exists_wedge hN
    exact ⟨x, hx, y, hy, hxy, t, p, r, hw, (hiff e).2 he⟩
  · rintro ⟨x, hx, y, hy, hxy, t, p, r, hw, he⟩
    have hmin : ∀ f, f ∈ p ∨ f ∈ r → IsMinusArc N f := by
      intro f hf l hl
      have hs : N.IsStableAncestor (q : Set X) l := fun z _ => hl.1 z trivial
      have hsum := hw.reaches_summit hN hs hx hy
      rcases hf with hf | hf
      · exact hsum.trans (hw.left.reaches_of_mem hf).1
      · exact hsum.trans (hw.right.reaches_of_mem hf).1
    refine ⟨x, hx, y, hy, hxy, t, N.downSteps p, N.downSteps r, ⟨IsDirPath.isSemiPath hN.acyclic hw.left fun f hf => hmin f (Or.inl hf),
      IsDirPath.isSemiPath hN.acyclic hw.right fun f hf => hmin f (Or.inr hf), fun z hz hz' => ?_⟩, ?_⟩
    · rw [map_snd_downSteps] at hz hz'
      exact hw.disjoint hz hz'
    · rw [map_fst_downSteps, map_fst_downSteps]
      exact he

/-- **`LSA(X)` has only its arcs leaving it in the graph of the kept edges**, of which it has two (`lsaNetwork_outdegree_root`). So it is a vertex of
degree two, or it is not kept, and it is suppressed in step 2 of Definition 5 if not in Definition 4. -/
theorem keptDegree_lsa_le [Finite E] {l : V} (hN : N.IsPhylogenetic) (hl : N.IsLeastStableAncestor Set.univ l) (q : Finset X) :
    keptDegree N q l ≤ N.graph.outdegree l := by
  have hin : {e | e ∈ trekArcs N q ∧ N.graph.target e = l} = ∅ := by
    refine Set.eq_empty_of_forall_notMem ?_
    rintro e ⟨he, hel⟩
    have hmin : IsMinusArc N e := by
      obtain ⟨x, -, y, -, -, v, l₁, l₂, ht, hep⟩ := he
      have hstep : ∀ {u w : V} {m : List (E × V)}, IsSemiWalk N u m w → e ∈ m.map Prod.fst → IsMinusArc N e := by
        intro u w m hm hem
        induction m generalizing u with
        | nil => simp at hem
        | cons t m ih =>
          simp only [List.map_cons, List.mem_cons] at hem
          rcases hem with rfl | hem
          · exact hm.1.1
          · exact ih hm.2 hem
      rcases hep with hep | hep
      · exact hstep ht.left.walk hep
      · exact hstep ht.right.walk hep
    exact not_reaches_source hN e (hel ▸ hmin l hl)
  have hsub : {e | e ∈ trekArcs N q ∧ N.graph.source e = l} ⊆ {e | N.graph.source e = l} := fun e he => he.2
  rw [keptDegree, hin, Set.ncard_empty, zero_add]
  exact Set.ncard_le_ncard hsub (Set.toFinite _)

/-! ### Which cycles are kept -/

section Cycle

variable [Fintype V] [Fintype E] [Fintype X] [DecidableEq X] {q : Finset X} {h u : V}

omit [Fintype X] [DecidableEq X] in
/-- A taxon below the reticulation and one not below it are in different blocks. -/
theorem not_blockWalk_of_below (hN : N.IsPhylogenetic) (hBin : N.IsBinary) (hLevel : IsLevelOne N)
    (hh₂ : 2 ≤ N.graph.indegree h) {a c : X} (ha : N.graph.Reaches h (N.leaf a))
    (hc : ¬ N.graph.Reaches h (N.leaf c)) : ¬ BlockWalk N h (N.leaf a) (N.leaf c) := by
  obtain ⟨eh, hehs, hehu, hehb⟩ := exists_child_arc hN hBin hLevel (v := h) .refl hh₂
  have hleaf : N.leaf a ≠ h := by
    intro he
    have := hN.leaf_indegree a
    rw [he] at this
    omega
  have key : ∀ w, BlockWalk N h (N.leaf a) w → N.graph.Reaches (N.graph.target eh) w := by
    intro w hw
    induction hw with
    | refl => exact reaches_target_of_unique_out hehu ha hleaf
    | @tail b w _ hstep ih =>
      obtain ⟨hb, hw, g, hg⟩ := hstep
      by_contra hn
      have hcr : N.graph.Crosses g {z | N.graph.Reaches (N.graph.target eh) z} := by
        rcases hg with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact Or.inl ⟨ih, hn⟩
        · exact Or.inr ⟨ih, hn⟩
      have hge := (isBridge_crosses_iff hN hehb g).1 hcr
      subst hge
      rcases hg with ⟨h₁, -⟩ | ⟨h₁, -⟩
      · exact hb (by rw [← h₁, hehs])
      · exact hw (by rw [← h₁, hehs])
  intro hw
  exact hc (hehs ▸ (reaches_of_arc N eh).trans (key _ hw))

omit [Fintype X] [DecidableEq X] in
/-- A taxon of `q` below the reticulation and one not below it keep all the arcs of the cycle. -/
theorem blobArcs_subset_wedgeArcs (hN : N.IsPhylogenetic) (hBin : N.IsBinary) (hLevel : IsLevelOne N)
    (hh₂ : 2 ≤ N.graph.indegree h) {a c : X} (haq : a ∈ q) (hcq : c ∈ q) (ha : N.graph.Reaches h (N.leaf a))
    (hc : ¬ N.graph.Reaches h (N.leaf c)) : ∀ f ∈ N.graph.blobArcs h, f ∈ N.wedgeArcs (q : Set X) := by
  have hx : ∀ x, ¬ N.graph.blobSetoid h (N.leaf x) := leaf_not_sameBlob hN .refl hh₂
  obtain ⟨T, k₁, k₂, pL, pR, C⟩ := exists_blobCycle hN hBin hLevel (v := h) .refl hh₂
  obtain ⟨l, hl, hlb⟩ := exists_path_of_below_reticulation hN hLevel (v := h) .refl hh₂ ha
  have hne : ¬ BlockWalk N h (N.leaf c) (N.leaf a) := fun hb =>
    not_blockWalk_of_below hN hBin hLevel hh₂ ha hc (blockWalk_symm hb)
  obtain ⟨b₀, hb₀⟩ := exists_isAttachment hN (hx c)
  have hb₀h : b₀ ≠ h := by
    rintro rfl
    rcases hb₀.reaches_or_top hN (hx c) with hr | ⟨htop, -⟩
    · exact hc hr
    · exact C.not_reaches_of_target₁ hN (htop _ (C.source₁_sameBlob hN))
  obtain ⟨W₁, W₂, -, hW, hcov⟩ := exactly_two_wedgePaths hN hBin hLevel (v := h) .refl hh₂ hb₀.1 hb₀h
  obtain ⟨u₀, l₁₀, l₂₀, hP₀⟩ := hb₀.exists_attachPath hN (hx c)
  have hac : a ≠ c := by
    rintro rfl
    exact hc ha
  have hglue : ∀ W : V × List E × List E, N.IsWedgePath h b₀ W.1 W.2.1 W.2.2 → ∀ f, (f ∈ W.2.1 ∨ f ∈ W.2.2) →
      f ∈ N.wedgeArcs (q : Set X) := by
    intro W hWw f hf
    obtain ⟨u', p, r, hw, hcase⟩ := hP₀.glue hN (hx c) (hx a) hne .refl hl hlb hWw
    exact ⟨a, haq, c, hcq, hac, u', p, r, hw, hcase f (Or.inr (hf.imp_right Or.inl))⟩
  intro f hf
  obtain ⟨hs, ht⟩ := mem_blobArcs_iff.1 hf
  rcases hcov f hs ht with h' | h'
  · exact hglue W₁ ((hW W₁).2 (Or.inl rfl)) f h'
  · exact hglue W₂ ((hW W₂).2 (Or.inr rfl)) f h'

omit [Fintype X] [DecidableEq X] in
/-- A kept cycle has a taxon of `q` below its reticulation, and one not below it. If all were below it, a wedge path through a
reticulation arc and the arc below the reticulation would have the arc below the reticulation on both legs. -/
theorem exists_below_of_mem_wedgeArcs (hN : N.IsPhylogenetic) (hBin : N.IsBinary) (hLevel : IsLevelOne N)
    (hh₂ : 2 ≤ N.graph.indegree h) {k : E} (hk : N.graph.target k = h) (hK : k ∈ N.wedgeArcs (q : Set X)) :
    (∃ a ∈ q, N.graph.Reaches h (N.leaf a)) ∧ ∃ c ∈ q, ¬ N.graph.Reaches h (N.leaf c) := by
  obtain ⟨z, hz, hzr⟩ := wedgeArcs_subset_ancestralArcs hK
  refine ⟨⟨z, hz, hk ▸ hzr⟩, ?_⟩
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
  -- on a leg through `k`, the arc below the reticulation is on it, and on the other leg
  have key : ∀ {t : V} {p r : List E} {x y : X}, N.IsWedgePath (N.leaf x) (N.leaf y) t p r → y ∈ q → k ∈ p → False := by
    intro t p r x y hw hy hkp
    obtain ⟨p₁, p₂, hpe, hp₁, hp₂⟩ := hw.left.split_of_mem hkp
    rw [hk] at hp₂
    have hehp : eh ∈ p := by
      cases p₂ with
      | nil => exact absurd (show h = N.leaf x from hp₂).symm (hleaf x)
      | cons g p₂ =>
        have hg : g = eh := hehu g hp₂.1
        rw [hpe, hg]
        simp
    have htn : ¬ N.graph.Reaches (N.graph.target eh) t := by
      intro hc
      have h₁ : N.graph.Reaches t h := by
        rw [← hk]
        exact hp₁.reaches.tail ⟨k, rfl, rfl⟩
      exact not_reaches_source hN eh (hehs ▸ hc.trans h₁)
    have hcr : ∃ f ∈ r, N.graph.Crosses f {w | N.graph.Reaches (N.graph.target eh) w} := by
      by_contra hno
      push Not at hno
      have := hw.right.mem_iff (S := {w | N.graph.Reaches (N.graph.target eh) w}) hno
      exact htn (this.2 (hbelow y hy))
    obtain ⟨f, hf, hc⟩ := hcr
    have hfe := (isBridge_crosses_iff hN hehb f).1 hc
    subst hfe
    exact hw.disjoint (List.mem_map_of_mem hehp) (List.mem_map_of_mem hf)
  obtain ⟨x, hx, y, hy, -, t, p, r, hw, hk' | hk'⟩ := hK
  · exact key hw hy hk'
  · exact key (hw.symm hN.acyclic) hx hk'

omit [Fintype X] [DecidableEq X] in
/-- **A cycle of `N` is a cycle of the quartet network on `q` exactly when `q` has a taxon below its hybrid node, and one not below
it.** So `1 ≤ k ≤ 3`, and these are the types in the source's list. -/
theorem isQuartetCycle_iff (hN : N.IsPhylogenetic) (hBin : N.IsBinary) (hLevel : IsLevelOne N)
    (hh₂ : 2 ≤ N.graph.indegree h) :
    IsQuartetCycle N q h ↔ (∃ a ∈ q, N.graph.Reaches h (N.leaf a)) ∧ ∃ c ∈ q, ¬ N.graph.Reaches h (N.leaf c) := by
  rw [IsQuartetCycle, trekArcs_eq_wedgeArcs hN]
  constructor
  · rintro ⟨-, hall⟩
    obtain ⟨T, k₁, k₂, pL, pR, C⟩ := exists_blobCycle hN hBin hLevel (v := h) .refl hh₂
    refine exists_below_of_mem_wedgeArcs hN hBin hLevel hh₂ C.target₁ (hall k₁ (mem_blobArcs_iff.2 ?_))
    exact ⟨C.source₁_sameBlob hN, C.target₁ ▸ C.reticulation⟩
  · rintro ⟨⟨a, haq, ha⟩, c, hcq, hc⟩
    exact ⟨hh₂, blobArcs_subset_wedgeArcs hN hBin hLevel hh₂ haq hcq ha hc⟩

/-! ### Where the taxa attach -/

omit [Fintype V] [Fintype E] [Fintype X] [DecidableEq X] in
/-- A taxon has at most one attachment. -/
theorem IsAttachment.eq_of_isAttachment {x : X} {b b' : V} (hx : ¬ N.graph.blobSetoid h (N.leaf x))
    (hb : IsAttachment N h x b) (hb' : IsAttachment N h x b') : b = b' := by
  obtain ⟨hbb, k, -, hS, hc⟩ := hb
  obtain ⟨hbb', k', -, hS', hc'⟩ := hb'
  have hkk : k = k' := (hS' k).1 ((hS k).2 rfl)
  subst hkk
  have hoff : ∀ {w : V}, BlockWalk N h (N.leaf x) w → ¬ N.graph.blobSetoid h w := fun hw =>
    not_sameBlob_of_blockWalk hx hw
  rcases hc with ⟨rfl, h₂⟩ | ⟨rfl, h₂⟩ <;> rcases hc' with ⟨h₃, h₄⟩ | ⟨h₃, h₄⟩
  · exact h₃
  · exact absurd hbb' (h₃ ▸ hoff h₂)
  · exact absurd hbb' (h₃ ▸ hoff h₂)
  · exact h₃

omit [Fintype V] [Fintype E] [Fintype X] [DecidableEq X] in
/-- Taxa in one block have the same attachment. -/
theorem IsAttachment.of_blockWalk {x y : X} {b : V} (hb : IsAttachment N h x b)
    (hxy : BlockWalk N h (N.leaf x) (N.leaf y)) : IsAttachment N h y b := by
  obtain ⟨hbb, k, hk, hS, hc⟩ := hb
  have hset : {u | BlockWalk N h (N.leaf y) u} = {u | BlockWalk N h (N.leaf x) u} := by
    ext u
    exact ⟨fun hu => blockWalk_trans hxy hu, fun hu => blockWalk_trans (blockWalk_symm hxy) hu⟩
  refine ⟨hbb, k, hk, by rw [hset]; exact hS, ?_⟩
  rcases hc with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
  · exact Or.inl ⟨h₁, blockWalk_trans (blockWalk_symm hxy) h₂⟩
  · exact Or.inr ⟨h₁, blockWalk_trans (blockWalk_symm hxy) h₂⟩

omit [Fintype V] [Fintype E] [Fintype X] [DecidableEq X] in
/-- What crosses the block of a taxon is its cut edge: the attachment of a taxon from a bridge with the taxon on its far side. -/
theorem isAttachment_of_bridge (hN : N.IsPhylogenetic) {x : X} (hx : ¬ N.graph.blobSetoid h (N.leaf x)) {g : E} {u w : V}
    (hg : N.graph.underlying.IsBridge g) (hu : N.graph.blobSetoid h u) (hcase : (N.graph.source g = u ∧ N.graph.target g = w) ∨
      (N.graph.target g = u ∧ N.graph.source g = w)) (hw : BlockWalk N h (N.leaf x) w) : IsAttachment N h x u := by
  obtain ⟨k, hkb, hS, -⟩ := exists_blockWalk_cut hN hx
  have huo : u ∉ {z | BlockWalk N h (N.leaf x) z} := fun hc => not_sameBlob_of_blockWalk hx hc hu
  have hcr : N.graph.Crosses g {z | BlockWalk N h (N.leaf x) z} := by
    rcases hcase with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
    · refine Or.inr ⟨?_, ?_⟩
      · rw [h₂]
        exact hw
      · rw [h₁]
        exact huo
    · refine Or.inl ⟨?_, ?_⟩
      · rw [h₂]
        exact hw
      · rw [h₁]
        exact huo
  have hgk : g = k := (hS g).1 hcr
  subst hgk
  refine ⟨hu, g, hg, hS, ?_⟩
  rcases hcase with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
  · exact Or.inl ⟨h₁, h₂ ▸ hw⟩
  · exact Or.inr ⟨h₁, h₂ ▸ hw⟩

omit [Fintype X] [DecidableEq X] in
/-- A taxon below the reticulation attaches at it. -/
theorem isAttachment_of_below (hN : N.IsPhylogenetic) (hBin : N.IsBinary) (hLevel : IsLevelOne N)
    (hh₂ : 2 ≤ N.graph.indegree h) {x : X} (hr : N.graph.Reaches h (N.leaf x)) : IsAttachment N h x h := by
  have hx : ¬ N.graph.blobSetoid h (N.leaf x) := leaf_not_sameBlob hN .refl hh₂ x
  obtain ⟨eh, hehs, hehu, hehb⟩ := exists_child_arc hN hBin hLevel (v := h) .refl hh₂
  have hleaf : N.leaf x ≠ h := by
    intro he
    have := hN.leaf_indegree x
    rw [he] at this
    omega
  have hre := reaches_target_of_unique_out hehu hr hleaf
  refine isAttachment_of_bridge hN hx (w := N.graph.target eh) hehb .refl (Or.inl ⟨hehs, rfl⟩) (blockWalk_symm ?_)
  exact blockWalk_of_reaches hre fun w hw _ hb =>
    not_sameBlob_of_reaches_exit hN hehb (by rw [hehs]) hw hb

omit [Fintype X] [DecidableEq X] in
/-- A taxon not below the reticulation attaches elsewhere. -/
theorem IsAttachment.ne_of_not_below (hN : N.IsPhylogenetic) (hBin : N.IsBinary) (hLevel : IsLevelOne N)
    (hh₂ : 2 ≤ N.graph.indegree h) {x : X} {b : V} (hb : IsAttachment N h x b) (hr : ¬ N.graph.Reaches h (N.leaf x)) :
    b ≠ h := by
  rintro rfl
  have hx : ¬ N.graph.blobSetoid b (N.leaf x) := leaf_not_sameBlob hN .refl hh₂ x
  obtain ⟨T, k₁, k₂, pL, pR, C⟩ := exists_blobCycle hN hBin hLevel (v := b) .refl hh₂
  rcases hb.reaches_or_top hN hx with h' | ⟨htop, -⟩
  · exact hr h'
  · exact C.not_reaches_of_target₁ hN (htop _ (C.source₁_sameBlob hN))

omit [Fintype X] [DecidableEq X] in
/-- **The cut edge of a taxon of `q` is kept**, on a kept cycle: another taxon of `q` is in another block. -/
theorem IsAttachment.exists_arc_mem_wedgeArcs (hN : N.IsPhylogenetic) (hBin : N.IsBinary) (hLevel : IsLevelOne N)
    (hh₂ : 2 ≤ N.graph.indegree h) (hQ : (∃ a ∈ q, N.graph.Reaches h (N.leaf a)) ∧ ∃ c ∈ q, ¬ N.graph.Reaches h (N.leaf c))
    {x : X} (hxq : x ∈ q) {b : V} (hb : IsAttachment N h x b) :
    ∃ k, k ∈ N.wedgeArcs (q : Set X) ∧ N.graph.underlying.IsBridge k ∧ (N.graph.source k = b ∨ N.graph.target k = b) := by
  obtain ⟨⟨a, haq, ha⟩, c, hcq, hc⟩ := hQ
  obtain ⟨y, hyq, hne⟩ : ∃ y ∈ q, ¬ BlockWalk N h (N.leaf x) (N.leaf y) := by
    by_cases hr : N.graph.Reaches h (N.leaf x)
    · exact ⟨c, hcq, not_blockWalk_of_below hN hBin hLevel hh₂ hr hc⟩
    · exact ⟨a, haq, fun hw => not_blockWalk_of_below hN hBin hLevel hh₂ ha hr (blockWalk_symm hw)⟩
  have hxy : x ≠ y := by
    rintro rfl
    exact hne .refl
  obtain ⟨hbb, k, hk, hS, hcase⟩ := hb
  obtain ⟨u, p, r, hw⟩ := exists_isWedgePath_leaf hN x y
  have hcr : ∃ f, (f ∈ p ∨ f ∈ r) ∧ N.graph.Crosses f {w | BlockWalk N h (N.leaf x) w} := by
    by_contra hno
    push Not at hno
    exact hne ((hw.mem_iff (S := {w | BlockWalk N h (N.leaf x) w}) fun f hf => hno f hf).1 .refl)
  obtain ⟨f, hf, hfc⟩ := hcr
  have hfk := (hS f).1 hfc
  subst hfk
  refine ⟨f, ⟨x, hxq, y, hyq, hxy, u, p, r, hw, hf⟩, hk, ?_⟩
  rcases hcase with ⟨h₁, -⟩ | ⟨h₁, -⟩
  · exact Or.inl h₁
  · exact Or.inr h₁

omit [Fintype V] [Fintype E] [Fintype X] [DecidableEq X] in
/-- **A kept arc at a vertex of a cycle and off the cycle is the cut edge of a taxon of `q`.** It is a bridge, and a wedge path through
it ends on its far side. -/
theorem exists_isAttachment_of_kept (hN : N.IsPhylogenetic)
    (hh₂ : 2 ≤ N.graph.indegree h) (hu : N.graph.blobSetoid h u) {e : E} (hK : e ∈ N.wedgeArcs (q : Set X))
    (he : e ∉ N.graph.blobArcs h) (hinc : N.graph.source e = u ∨ N.graph.target e = u) :
    ∃ x ∈ q, IsAttachment N h x u := by
  have hx : ∀ x, ¬ N.graph.blobSetoid h (N.leaf x) := leaf_not_sameBlob hN .refl hh₂
  -- it is a bridge
  have hb : N.graph.underlying.IsBridge e := by
    by_contra hnb
    refine he (mem_blobArcs_iff.2 ?_)
    have hsame := sameBlob_of_not_isBridge hnb
    rcases hinc with rfl | rfl
    · exact ⟨hu, sameBlob_trans hu hsame⟩
    · exact ⟨sameBlob_trans hu (sameBlob_symm hsame), hu⟩
  obtain ⟨x, hxq, y, hyq, hxy, t, p, r, hw, hep⟩ := hK
  rcases hinc with hs | ht
  · -- it leaves the blob: the taxon at the end of the leg through it
    have hub : N.graph.blobSetoid h (N.graph.source e) := hs ▸ hu
    have hfar : ∀ {z : X}, N.graph.Reaches (N.graph.target e) (N.leaf z) → IsAttachment N h z u := by
      intro z hz
      refine isAttachment_of_bridge hN (hx z) (w := N.graph.target e) hb hu (Or.inl ⟨hs, rfl⟩) (blockWalk_symm ?_)
      exact blockWalk_of_reaches hz fun w hw _ hbw => not_sameBlob_of_reaches_exit hN hb hub hw hbw
    rcases hep with hep | hep
    · exact ⟨x, hxq, hfar (hw.left.reaches_of_mem hep).2⟩
    · exact ⟨y, hyq, hfar (hw.right.reaches_of_mem hep).2⟩
  · -- it enters the blob: the taxon at the end of the other leg is not below it
    have hub : N.graph.blobSetoid h (N.graph.target e) := ht ▸ hu
    have hfar : ∀ {z : X}, ¬ N.graph.Reaches (N.graph.target e) (N.leaf z) → IsAttachment N h z u := by
      intro z hz
      refine isAttachment_of_bridge hN (hx z) (w := N.graph.source e) hb hu (Or.inr ⟨ht, rfl⟩) ?_
      have hnz : ∀ w, N.graph.Reaches w (N.leaf z) → ¬ N.graph.blobSetoid h w := fun w hwz hbw =>
        hz ((reaches_of_sameBlob hN hb (sameBlob_trans (sameBlob_symm hub) hbw)).trans hwz)
      have hns : ∀ w, N.graph.Reaches w (N.graph.source e) → ¬ N.graph.blobSetoid h w := fun w hws hbw =>
        not_reaches_source hN e ((reaches_of_sameBlob hN hb (sameBlob_trans (sameBlob_symm hub) hbw)).trans hws)
      exact blockWalk_trans
        (blockWalk_symm (blockWalk_of_reaches (hN.root_reaches _) fun w _ hwz => hnz w hwz))
        (blockWalk_of_reaches (hN.root_reaches _) fun w _ hws => hns w hws)
    have key : ∀ {t : V} {p r : List E} {x y : X}, N.IsWedgePath (N.leaf x) (N.leaf y) t p r → e ∈ p →
        ¬ N.graph.Reaches (N.graph.target e) (N.leaf y) := by
      intro t p r x y hw hep hy
      have htn : ¬ N.graph.Reaches (N.graph.target e) t := fun hc =>
        not_reaches_source hN e (hc.trans (hw.left.reaches_of_mem hep).1)
      have hcr : ∃ f ∈ r, N.graph.Crosses f {w | N.graph.Reaches (N.graph.target e) w} := by
        by_contra hno
        push Not at hno
        exact htn ((hw.right.mem_iff (S := {w | N.graph.Reaches (N.graph.target e) w}) hno).2 hy)
      obtain ⟨f, hf, hc⟩ := hcr
      have hfe := (isBridge_crosses_iff hN hb f).1 hc
      subst hfe
      exact hw.disjoint (List.mem_map_of_mem hep) (List.mem_map_of_mem hf)
    rcases hep with hep | hep
    · exact ⟨y, hyq, hfar (key hw hep)⟩
    · exact ⟨x, hxq, hfar (key (hw.symm hN.acyclic) hep)⟩

omit [Fintype X] [DecidableEq X] in
/-- Every vertex of a cycle has two arcs of the cycle. -/
theorem exists_two_blobArcs (hN : N.IsPhylogenetic) (hBin : N.IsBinary) (hLevel : IsLevelOne N)
    (hh₂ : 2 ≤ N.graph.indegree h) (hu : N.graph.blobSetoid h u) :
    ∃ f g, f ≠ g ∧ f ∈ N.graph.blobArcs h ∧ g ∈ N.graph.blobArcs h ∧ (N.graph.source f = u ∨ N.graph.target f = u) ∧
      (N.graph.source g = u ∨ N.graph.target g = u) := by
  obtain ⟨T, k₁, k₂, pL, pR, C⟩ := exists_blobCycle hN hBin hLevel (v := h) .refl hh₂
  have hmem : ∀ {f : E}, ¬ N.graph.underlying.IsBridge f → N.graph.blobSetoid h (N.graph.source f) →
      f ∈ N.graph.blobArcs h := fun hb hs => ⟨hb, hs⟩
  by_cases huh : u = h
  · subst huh
    refine ⟨k₁, k₂, C.ne, mem_blobArcs_iff.2 ⟨C.source₁_sameBlob hN, C.target₁ ▸ C.reticulation⟩,
      mem_blobArcs_iff.2 ⟨C.swap.source₁_sameBlob hN, C.target₂ ▸ C.reticulation⟩, Or.inr C.target₁, Or.inr C.target₂⟩
  by_cases huT : u = T
  · subst huT
    obtain ⟨g₁, g₂, h₁₂, hs₁, hs₂, hb₁, hb₂⟩ := C.exists_two_out_arcs hN
    exact ⟨g₁, g₂, h₁₂, hmem hb₁ (hs₁ ▸ C.top), hmem hb₂ (hs₂ ▸ C.top), Or.inl hs₁, Or.inl hs₂⟩
  · obtain ⟨g, hgs, hgb⟩ := C.exists_out_arc hN hLevel hh₂ hu huh
    rcases Relation.ReflTransGen.cases_tail (C.top_reaches u hu) with heq | ⟨c, hc, f, hfs, hft⟩
    · exact absurd heq huT
    · have hcb : N.graph.blobSetoid h c := sameBlob_of_reaches_of_reaches hN C.top hu hc (.single ⟨f, hfs, hft⟩)
      have hfm : f ∈ N.graph.blobArcs h := mem_blobArcs_iff.2 ⟨hfs ▸ hcb, hft ▸ hu⟩
      refine ⟨f, g, ?_, hfm, hmem hgb (hgs ▸ hu), Or.inr hft, Or.inl hgs⟩
      rintro rfl
      exact target_ne_source hN f (hft.trans hgs.symm)

omit [Fintype V] [Fintype X] [DecidableEq X] in
/-- The kept degree is the number of kept arcs at the vertex. -/
theorem keptDegree_eq_ncard (hN : N.IsPhylogenetic) (q : Finset X) (u : V) :
    keptDegree N q u = {e | e ∈ trekArcs N q ∧ (N.graph.target e = u ∨ N.graph.source e = u)}.ncard := by
  have hun : {e | e ∈ trekArcs N q ∧ (N.graph.target e = u ∨ N.graph.source e = u)} =
      {e | e ∈ trekArcs N q ∧ N.graph.target e = u} ∪ {e | e ∈ trekArcs N q ∧ N.graph.source e = u} := by
    ext e
    simp only [Set.mem_ofPred_eq, Set.mem_union]
    tauto
  rw [hun, Set.ncard_union_eq _ (Set.toFinite _) (Set.toFinite _)]
  · rfl
  · refine Set.disjoint_left.2 fun e he he' => ?_
    exact target_ne_source hN e (he.2.trans he'.2.symm)

omit [Fintype X] [DecidableEq X] in
/-- **A vertex of a kept cycle has degree other than two exactly when a taxon of `q` attaches there.** -/
theorem keptDegree_ne_two_iff (hN : N.IsPhylogenetic) (hBin : N.IsBinary) (hLevel : IsLevelOne N)
    (hQ : IsQuartetCycle N q h) (hu : N.graph.blobSetoid h u) :
    keptDegree N q u ≠ 2 ↔ ∃ x ∈ q, IsAttachment N h x u := by
  obtain ⟨hh₂, hall⟩ := hQ
  have hiff := isQuartetCycle_iff (q := q) hN hBin hLevel hh₂
  have hbelow := hiff.1 ⟨hh₂, hall⟩
  rw [trekArcs_eq_wedgeArcs hN] at hall
  obtain ⟨f, g, hfg, hf, hg, hfu, hgu⟩ := exists_two_blobArcs hN hBin hLevel hh₂ hu
  have hFin : {e | e ∈ trekArcs N q ∧ (N.graph.target e = u ∨ N.graph.source e = u)}.Finite := Set.toFinite _
  have hfk : f ∈ {e | e ∈ trekArcs N q ∧ (N.graph.target e = u ∨ N.graph.source e = u)} := by
    rw [trekArcs_eq_wedgeArcs hN]
    exact ⟨hall f hf, hfu.symm⟩
  have hgk : g ∈ {e | e ∈ trekArcs N q ∧ (N.graph.target e = u ∨ N.graph.source e = u)} := by
    rw [trekArcs_eq_wedgeArcs hN]
    exact ⟨hall g hg, hgu.symm⟩
  rw [keptDegree_eq_ncard hN]
  constructor
  · intro hne
    by_contra hno
    push Not at hno
    refine hne ?_
    have heq : {e | e ∈ trekArcs N q ∧ (N.graph.target e = u ∨ N.graph.source e = u)} = {f, g} := by
      ext e
      simp only [Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
      constructor
      · rintro ⟨hek, hei⟩
        rw [trekArcs_eq_wedgeArcs hN] at hek
        by_cases heb : e ∈ N.graph.blobArcs h
        · obtain ⟨T, k₁, k₂, pL, pR, C⟩ := exists_blobCycle hN hBin hLevel (v := h) .refl hh₂
          by_contra hcon
          push Not at hcon
          have hinc : ∀ {x : E}, (N.graph.source x = u ∨ N.graph.target x = u) → N.Incident x u := by
            rintro x (h₁ | h₁)
            · exact Or.inl h₁
            · exact Or.inr h₁
          exact C.degLeTwo hN hLevel hh₂ u e f g heb hf hg (hinc hei.symm) (hinc hfu) (hinc hgu) hcon.1 hcon.2 hfg
        · obtain ⟨x, hx, hxa⟩ := exists_isAttachment_of_kept hN hh₂ hu hek heb hei.symm
          exact absurd hxa (hno x hx)
      · rintro (rfl | rfl)
        · exact hfk
        · exact hgk
    rw [heq, Set.ncard_pair hfg]
  · rintro ⟨x, hx, hxa⟩ h2
    obtain ⟨k, hkK, hkb, hkinc⟩ := IsAttachment.exists_arc_mem_wedgeArcs hN hBin hLevel hh₂ hbelow hx hxa
    have hkf : k ≠ f := by
      rintro rfl
      exact hf.1 hkb
    have hkg : k ≠ g := by
      rintro rfl
      exact hg.1 hkb
    have hkk : k ∈ {e | e ∈ trekArcs N q ∧ (N.graph.target e = u ∨ N.graph.source e = u)} := by
      rw [trekArcs_eq_wedgeArcs hN]
      exact ⟨hkK, hkinc.symm⟩
    have hsub : ({k, f, g} : Set E) ⊆ {e | e ∈ trekArcs N q ∧ (N.graph.target e = u ∨ N.graph.source e = u)} := by
      rintro e (rfl | rfl | rfl)
      · exact hkk
      · exact hfk
      · exact hgk
    have hc3 : ({k, f, g} : Set E).ncard = 3 := by
      rw [Set.ncard_eq_toFinset_card']
      simp [hkf, hkg, hfg]
    have := Set.ncard_le_ncard hsub hFin
    omega

omit [Fintype X] [DecidableEq X] in
/-- **The size of a kept cycle is the number of vertices where a taxon of `q` attaches**, the number of blocks with a taxon of `q`. -/
theorem cycleSize_eq (hN : N.IsPhylogenetic) (hBin : N.IsBinary) (hLevel : IsLevelOne N)
    (hQ : IsQuartetCycle N q h) : cycleSize N q h = {u | ∃ x ∈ q, IsAttachment N h x u}.ncard := by
  unfold cycleSize
  congr 1
  ext u
  constructor
  · rintro ⟨hu, hne⟩
    exact (keptDegree_ne_two_iff hN hBin hLevel hQ hu).1 hne
  · rintro ⟨x, hx, hxa⟩
    exact ⟨hxa.1, (keptDegree_ne_two_iff hN hBin hLevel hQ hxa.1).2 ⟨x, hx, hxa⟩⟩

omit [Fintype X] in
/-- **`HasThreeTwoCycle`, by blocks, is the source's `3₂`-cycle**: "an `m`-cycle with exactly `k` taxa descended from its unique
hybrid node", for `m = 3`, `k = 2`, on the quartet network of Definition 5. -/
theorem hasThreeTwoCycle_iff (hN : N.IsPhylogenetic) (hBin : N.IsBinary) (hLevel : IsLevelOne N) (hq : #q = 4) :
    HasThreeTwoCycle N q ↔ HasCycleType N q 3 2 := by
  -- the taxa not below `h`, when two are below it
  have hsplit : ∀ {h : V}, (q.filter fun x => N.graph.Reaches h (N.leaf x)).card = 2 →
      ∃ c d, c ≠ d ∧ c ∈ q ∧ d ∈ q ∧ ¬ N.graph.Reaches h (N.leaf c) ∧ ¬ N.graph.Reaches h (N.leaf d) ∧
        ∀ z ∈ q, N.graph.Reaches h (N.leaf z) ∨ z = c ∨ z = d := by
    intro h hcard
    have hc2 : (q.filter fun x => ¬ N.graph.Reaches h (N.leaf x)).card = 2 := by
      have := card_filter_add_card_filter_not (s := q) fun x => N.graph.Reaches h (N.leaf x)
      omega
    obtain ⟨c, d, hcd, hE⟩ := card_eq_two.1 hc2
    have hc : c ∈ q.filter fun x => ¬ N.graph.Reaches h (N.leaf x) := by rw [hE]; simp
    have hd : d ∈ q.filter fun x => ¬ N.graph.Reaches h (N.leaf x) := by rw [hE]; simp
    refine ⟨c, d, hcd, (mem_filter.1 hc).1, (mem_filter.1 hd).1, (mem_filter.1 hc).2, (mem_filter.1 hd).2, fun z hz => ?_⟩
    by_cases hr : N.graph.Reaches h (N.leaf z)
    · exact Or.inl hr
    · have : z ∈ q.filter fun x => ¬ N.graph.Reaches h (N.leaf x) := mem_filter.2 ⟨hz, hr⟩
      rw [hE] at this
      simpa using Or.inr this
  constructor
  · rintro ⟨h, hh₂, hcard, hblock⟩
    obtain ⟨c, d, hcd, hcq, hdq, hc, hd, hall⟩ := hsplit hcard
    obtain ⟨a, b, -, hE⟩ := card_eq_two.1 hcard
    have ha : a ∈ q.filter fun x => N.graph.Reaches h (N.leaf x) := by rw [hE]; simp
    have hx : ∀ x, ¬ N.graph.blobSetoid h (N.leaf x) := leaf_not_sameBlob hN .refl hh₂
    obtain ⟨T, k₁, k₂, pL, pR, C⟩ := exists_blobCycle hN hBin hLevel (v := h) .refl hh₂
    have hQ : IsQuartetCycle N q h := (isQuartetCycle_iff hN hBin hLevel hh₂).2
      ⟨⟨a, (mem_filter.1 ha).1, (mem_filter.1 ha).2⟩, c, hcq, hc⟩
    obtain ⟨b₁, hb₁⟩ := exists_isAttachment hN (hx c)
    obtain ⟨b₂, hb₂⟩ := exists_isAttachment hN (hx d)
    have hne₁ := IsAttachment.ne_of_not_below hN hBin hLevel hh₂ hb₁ hc
    have hne₂ := IsAttachment.ne_of_not_below hN hBin hLevel hh₂ hb₂ hd
    have hne₃ : b₁ ≠ b₂ := by
      rintro rfl
      exact hblock c hcq d hdq hcd hc hd (IsAttachment.blockWalk_of_eq hN hBin hLevel hh₂ C hb₁ hb₂)
    have hset : {u | ∃ x ∈ q, IsAttachment N h x u} = {h, b₁, b₂} := by
      ext u
      simp only [Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
      constructor
      · rintro ⟨z, hz, hzu⟩
        rcases hall z hz with hr | rfl | rfl
        · exact Or.inl (IsAttachment.eq_of_isAttachment (hx z) hzu (isAttachment_of_below hN hBin hLevel hh₂ hr))
        · exact Or.inr (Or.inl (IsAttachment.eq_of_isAttachment (hx z) hzu hb₁))
        · exact Or.inr (Or.inr (IsAttachment.eq_of_isAttachment (hx z) hzu hb₂))
      · rintro (rfl | rfl | rfl)
        · exact ⟨a, (mem_filter.1 ha).1, isAttachment_of_below hN hBin hLevel hh₂ (mem_filter.1 ha).2⟩
        · exact ⟨c, hcq, hb₁⟩
        · exact ⟨d, hdq, hb₂⟩
    refine ⟨h, hQ, ?_, hcard⟩
    rw [cycleSize_eq hN hBin hLevel hQ, hset, Set.ncard_eq_toFinset_card']
    simp [hne₁.symm, hne₂.symm, hne₃]
  · rintro ⟨h, hQ, hsize, hdesc⟩
    have hh₂ := hQ.1
    have hx : ∀ x, ¬ N.graph.blobSetoid h (N.leaf x) := leaf_not_sameBlob hN .refl hh₂
    refine ⟨h, hh₂, hdesc, fun x hxq y hyq hxy hxr hyr hw => ?_⟩
    obtain ⟨c, d, -, -, -, hc, hd, hall⟩ := hsplit hdesc
    obtain ⟨b₁, hb₁⟩ := exists_isAttachment hN (hx x)
    have hb₂ := IsAttachment.of_blockWalk hb₁ hw
    have hsub : {u | ∃ z ∈ q, IsAttachment N h z u} ⊆ {h, b₁} := by
      rintro u ⟨z, hz, hzu⟩
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      by_cases hr : N.graph.Reaches h (N.leaf z)
      · exact Or.inl (IsAttachment.eq_of_isAttachment (hx z) hzu (isAttachment_of_below hN hBin hLevel hh₂ hr))
      · right
        -- `z` is `x` or `y`: there are two taxa not below `h`
        have hz' : z = x ∨ z = y := by
          have hxc : x = c ∨ x = d := (hall x hxq).resolve_left hxr
          have hyc : y = c ∨ y = d := (hall y hyq).resolve_left hyr
          have hzc : z = c ∨ z = d := (hall z hz).resolve_left hr
          rcases hxc with rfl | rfl <;> rcases hyc with rfl | rfl <;> rcases hzc with rfl | rfl <;> simp_all
        rcases hz' with rfl | rfl
        · exact IsAttachment.eq_of_isAttachment (hx z) hzu hb₁
        · exact IsAttachment.eq_of_isAttachment (hx z) hzu hb₂
    have hle := Set.ncard_le_ncard hsub (Set.toFinite _)
    have h2 : ({h, b₁} : Set V).ncard ≤ 2 := by
      have := Set.ncard_insert_le h ({b₁} : Set V)
      rwa [Set.ncard_singleton] at this
    rw [cycleSize_eq hN hBin hLevel hQ] at hsize
    omega

end Cycle

end External.AllmanBanosRhodes2019.Quartet
