module

public import Phylogenetics.Graph.Blobs
public import Phylogenetics.Graph.CutUniqueness
public import Phylogenetics.Network.Quartets
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Bridges by depth-first search with low-points

The supplement of TOB-QMC (line 206): the tree of blobs is formed by un-directing, "contracting all edges in the same blob" and "suppressing any vertices with degree two; these operations can be performed in linear time". Ané et al. 2024: "finding a network's blobs can be done in time
that is linear in the number of nodes and edges (Tarjan, 1972)". This file verifies Tarjan's depth-first search with low-points, on a directed multigraph taken as undirected, with parallel arcs.

* `visit`, `run`: the search, with a fuel argument, written with the arc to the parent, so that a parallel arc is not mistaken for it. It counts its steps: a step reads and writes a constant number of entries of the state.
* `visit_spec`: what a call does, the invariant of the proof: the vertices it discovers are an interval of discovery times, closed under adjacency except for arcs to proper ancestors, and `low` is the least discovery time reached from them by an arc other than the arc to a parent.
* `isBridge_iff`: an arc is a bridge exactly when it is the arc to the parent of a vertex `w` with `disc p < low w`.
* `count_eq`: the count is `|V| + 2 |E|`, on incidence lists.
* `labels`, `labels_eq_iff`, `length_order`: a pass over the vertices in the order of discovery, of `|V|` steps, labels the blobs.
* `hasCutSplit_iff`, `mem_treeOfBlobs_iff`: the splits of the tree of blobs are the taxa at or below a vertex `w` below a bridge, which are an interval of discovery times, or the rest. So the tree of blobs is represented by at most `|V|` pairs of numbers, after `|V| + 2 |E|` steps. Departure from the sources: they contract the blobs and suppress the vertices of degree two; `treeOfBlobs` is the family of sides, for which neither is needed, and `Phylogenetics.Network.TreeOfBlobs` proves the two the same.
-/

@[expose] public noncomputable section

open Finset
open scoped Classical

namespace Phylogenetics.BridgeDFS

variable {V E : Type*} [Fintype V]

/-- The state of the search. -/
structure St (V E : Type*) where
  vis : Finset V
  disc : V → ℕ
  low : V → ℕ
  fin : V → ℕ
  par : V → Option (E × V)
  time : ℕ
  count : ℕ
  /-- The vertices discovered, the last first. -/
  order : List V

/-- Discovering `w`, with the arc to its parent. -/
def start (w : V) (pa : Option (E × V)) (σ : St V E) : St V E :=
  { σ with vis := insert w σ.vis, disc := Function.update σ.disc w σ.time, low := Function.update σ.low w σ.time,
           par := Function.update σ.par w pa, time := σ.time + 1, count := σ.count + 1, order := w :: σ.order }

/-- Lowering `low w`. -/
def lower (w : V) (a : ℕ) (σ : St V E) : St V E :=
  { σ with low := Function.update σ.low w (min (σ.low w) a) }

/-- One entry of the adjacency list of `w`, with `rec` the search on the vertices below. The arc to the parent is skipped; a visited vertex lowers `low w` by its discovery time; a new one is searched, and lowers `low w` by its `low`. -/
def step (rec : V → Option (E × V) → St V E → St V E) (w : V) (pa : Option (E × V)) (σ₀ : St V E) (q : E × V) : St V E :=
  let σ : St V E := { σ₀ with count := σ₀.count + 1 }
  if pa.map Prod.fst = some q.1 then σ
  else if q.2 ∈ σ.vis then lower w (σ.disc q.2) σ
  else
    let σ' := rec q.2 (some (q.1, w)) σ
    lower w (σ'.low q.2) σ'

/-- **The search from `w`**, with fuel, on the adjacency lists `adj`. -/
def visit (adj : V → List (E × V)) : ℕ → V → Option (E × V) → St V E → St V E
  | 0, _, _, σ => σ
  | n + 1, w, pa, σ =>
    let σ' := (adj w).foldl (step (visit adj n) w pa) (start w pa σ)
    { σ' with fin := Function.update σ'.fin w σ'.time }

variable (adj : V → List (E × V))

/-- The vertices discovered during the call on `x`: an interval of discovery times. -/
def sub (σ : St V E) (x : V) : Finset V := σ.vis.filter fun y => σ.disc x ≤ σ.disc y ∧ σ.disc y < σ.fin x

/-- The property recorded of a vertex `x` when its call returns. -/
structure Good (σ : St V E) (x : V) : Prop where
  g0 : σ.disc x < σ.fin x
  g6 : σ.fin x ≤ σ.time
  g1 : ∀ y ∈ sub σ x, ∀ q ∈ adj y, q.2 ∈ σ.vis
  g2 : ∀ y ∈ sub σ x, ∀ q ∈ adj y, q.2 ∈ sub σ x ∨ ∃ e p, σ.par x = some (e, p) ∧ σ.disc q.2 ≤ σ.disc p
  g3 : ∀ y ∈ sub σ x, ∀ q ∈ adj y, (σ.par y).map Prod.fst ≠ some q.1 → σ.low x ≤ σ.disc q.2
  g4 : σ.low x ≤ σ.disc x
  g4' : σ.low x = σ.disc x ∨ ∃ y ∈ sub σ x, ∃ q ∈ adj y, (σ.par y).map Prod.fst ≠ some q.1 ∧ σ.disc q.2 = σ.low x
  g5 : ∀ y ∈ sub σ x, y ≠ x → ∃ f p, σ.par y = some (f, p) ∧ (f, p) ∈ adj y ∧ p ∈ sub σ x ∧ σ.disc p < σ.disc y
  g7 : ∀ e p, σ.par x = some (e, p) → p ∈ σ.vis ∧ (e, p) ∈ adj x ∧ σ.disc p < σ.disc x

variable {adj}

omit [Fintype V] in
/-- What a vertex recorded stays true: nothing it reads changes, and later vertices are outside its interval. -/
theorem Good.mono {σ σ' : St V E} {x : V} (h : Good adj σ x) (hx : x ∈ σ.vis) (hv : σ.vis ⊆ σ'.vis) (hd : ∀ y ∈ σ.vis, σ'.disc y = σ.disc y)
    (hp : ∀ y ∈ σ.vis, σ'.par y = σ.par y) (hf : σ'.fin x = σ.fin x) (hl : σ'.low x = σ.low x) (ht : σ.time ≤ σ'.time)
    (hn : ∀ z ∈ σ'.vis, z ∉ σ.vis → σ.time ≤ σ'.disc z) : Good adj σ' x := by
  have hsub : sub σ' x = sub σ x := by
    ext y
    simp only [sub, mem_filter]
    constructor
    · rintro ⟨hy, h₁, h₂⟩
      by_cases hyv : y ∈ σ.vis
      · rw [hd y hyv, hd x hx, hf] at *
        exact ⟨hyv, h₁, h₂⟩
      · have := hn y hy hyv
        have := h.g6
        rw [hf] at h₂
        omega
    · rintro ⟨hy, h₁, h₂⟩
      exact ⟨hv hy, by rw [hd y hy, hd x hx]; exact h₁, by rw [hd y hy, hf]; exact h₂⟩
  have hvis : ∀ y ∈ sub σ x, y ∈ σ.vis := fun y hy => (mem_filter.1 hy).1
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hd x hx, hf]
    exact h.g0
  · rw [hf]
    exact h.g6.trans ht
  · rw [hsub]
    exact fun y hy q hq => hv (h.g1 y hy q hq)
  · rw [hsub]
    intro y hy q hq
    rcases h.g2 y hy q hq with h₁ | ⟨e, p, h₁, h₂⟩
    · exact Or.inl h₁
    · have hq' := h.g1 y hy q hq
      refine Or.inr ⟨e, p, by rw [hp x hx]; exact h₁, ?_⟩
      rw [hd _ hq', hd p (h.g7 e p h₁).1]
      exact h₂
  · rw [hsub, hl]
    intro y hy q hq hne
    rw [hd _ (h.g1 y hy q hq)]
    exact h.g3 y hy q hq (by rwa [← hp y (hvis y hy)])
  · rw [hl, hd x hx]
    exact h.g4
  · rw [hl, hd x hx, hsub]
    rcases h.g4' with h₁ | ⟨y, hy, q, hq, h₁, h₂⟩
    · exact Or.inl h₁
    · exact Or.inr ⟨y, hy, q, hq, by rwa [hp y (hvis y hy)], by rw [hd _ (h.g1 y hy q hq)]; exact h₂⟩
  · rw [hsub]
    intro y hy hne
    obtain ⟨f, p, h₁, h₂, h₃, h₄⟩ := h.g5 y hy hne
    exact ⟨f, p, by rw [hp y (hvis y hy)]; exact h₁, h₂, h₃, by rw [hd y (hvis y hy), hd p (hvis p h₃)]; exact h₄⟩
  · intro e p hpar
    rw [hp x hx] at hpar
    obtain ⟨h₁, h₂, h₃⟩ := h.g7 e p hpar
    exact ⟨hv h₁, h₂, by rw [hd p h₁, hd x hx]; exact h₃⟩

/-- The discovery times are distinct and below the clock. -/
structure Inv (σ : St V E) : Prop where
  lt : ∀ x ∈ σ.vis, σ.disc x < σ.time
  inj : ∀ x ∈ σ.vis, ∀ y ∈ σ.vis, σ.disc x = σ.disc y → x = y
  ord : ∀ x, x ∈ σ.order ↔ x ∈ σ.vis
  sorted : σ.order.Pairwise fun a b => σ.disc b < σ.disc a

/-- The precondition of a call with the arc `pa` to the parent: a vertex discovered after the parent has finished, so all its neighbours are visited. -/
def PreAbove (adj : V → List (E × V)) (σ : St V E) (pa : Option (E × V)) : Prop :=
  ∀ y ∈ σ.vis, (∀ e p, pa = some (e, p) → σ.disc p < σ.disc y) → ∀ q ∈ adj y, q.2 ∈ σ.vis

/-- The arc to the parent is an entry of the adjacency list, to a visited vertex. -/
def PaOK (adj : V → List (E × V)) (σ : St V E) (w : V) (pa : Option (E × V)) : Prop :=
  ∀ e p, pa = some (e, p) → p ∈ σ.vis ∧ (e, p) ∈ adj w

/-- The adjacency lists are symmetric, and an arc has one other end. -/
structure IsIncidence (adj : V → List (E × V)) : Prop where
  symm : ∀ x f y, (f, y) ∈ adj x → (f, x) ∈ adj y
  other : ∀ x f y y', (f, y) ∈ adj x → (f, y') ∈ adj x → y = y' ∨ x = y ∨ x = y'

/-- A count of a set of visited vertices, with their adjacency lists. -/
def weight (adj : V → List (E × V)) (S : Finset V) : ℕ := ∑ x ∈ S, (1 + (adj x).length)

/-- What holds of the old and new vertices, along the loop of the call on `w`. -/
structure Frozen (w : V) (σ σ' : St V E) : Prop where
  vis : σ.vis ⊆ σ'.vis
  time : σ.time ≤ σ'.time
  disc : ∀ x ∈ σ.vis, σ'.disc x = σ.disc x
  fin : ∀ x ∈ σ.vis, σ'.fin x = σ.fin x
  par : ∀ x ∈ σ.vis, σ'.par x = σ.par x
  low : ∀ x ∈ σ.vis, x ≠ w → σ'.low x = σ.low x
  new : ∀ z ∈ σ'.vis, z ∉ σ.vis → σ.time ≤ σ'.disc z

omit [Fintype V] in
theorem Frozen.refl (w : V) (σ : St V E) : Frozen w σ σ :=
  ⟨Subset.rfl, le_rfl, fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl, fun _ _ _ => rfl, fun _ hz hz' => absurd hz hz'⟩

omit [Fintype V] in
theorem Frozen.trans {w : V} {σ σ' σ'' : St V E} (h : Frozen w σ σ') (h' : Frozen w σ' σ'') : Frozen w σ σ'' := by
  refine ⟨h.vis.trans h'.vis, h.time.trans h'.time, fun x hx => ?_, fun x hx => ?_, fun x hx => ?_, fun x hx hxw => ?_, fun z hz hzn => ?_⟩
  · rw [h'.disc x (h.vis hx), h.disc x hx]
  · rw [h'.fin x (h.vis hx), h.fin x hx]
  · rw [h'.par x (h.vis hx), h.par x hx]
  · rw [h'.low x (h.vis hx) hxw, h.low x hx hxw]
  · by_cases hz' : z ∈ σ'.vis
    · rw [h'.disc z hz']
      exact h.new z hz' hzn
    · exact h.time.trans (h'.new z hz hz')

/-- What a call returns. -/
structure Post (adj : V → List (E × V)) (w : V) (pa : Option (E × V)) (σ σ' : St V E) : Prop where
  frozen : Frozen w σ σ'
  mem : w ∈ σ'.vis
  disc : σ'.disc w = σ.time
  par : σ'.par w = pa
  fin : σ'.fin w = σ'.time
  lt : σ.time < σ'.time
  inv : Inv σ'
  good : ∀ x ∈ σ'.vis, x ∉ σ.vis → Good adj σ' x
  count : σ'.count + weight adj σ.vis = σ.count + weight adj σ'.vis

/-- The invariant of the loop of the call on `w`, after the entries `done`. -/
structure Loop (adj : V → List (E × V)) (w : V) (pa : Option (E × V)) (σ : St V E) (done : List (E × V)) (c : St V E) : Prop where
  frozen : Frozen w σ c
  mem : w ∈ c.vis
  disc : c.disc w = σ.time
  par : c.par w = pa
  lt : σ.time < c.time
  inv : Inv c
  good : ∀ x ∈ c.vis, x ∉ σ.vis → x ≠ w → Good adj c x
  tree : ∀ x ∈ c.vis, x ∉ σ.vis → x ≠ w → ∃ f p, c.par x = some (f, p) ∧ (f, p) ∈ adj x ∧ p ∈ c.vis ∧ p ∉ σ.vis ∧ c.disc p < c.disc x
  dn : ∀ q ∈ done, q.2 ∈ c.vis
  low : c.low w ≤ σ.time
  cover : ∀ x ∈ c.vis, x ∉ σ.vis → x ≠ w → ∀ q ∈ adj x, (c.par x).map Prod.fst ≠ some q.1 → c.low w ≤ c.disc q.2
  coverw : ∀ q ∈ done, pa.map Prod.fst ≠ some q.1 → c.low w ≤ c.disc q.2
  wit : c.low w = σ.time ∨ ∃ x ∈ c.vis, x ∉ σ.vis ∧ ∃ q ∈ adj x, q.2 ∈ c.vis ∧ (c.par x).map Prod.fst ≠ some q.1 ∧ c.disc q.2 = c.low w
  count : c.count + weight adj σ.vis + 1 + (adj w).length = σ.count + 1 + done.length + weight adj c.vis

/-! ### The loop -/

omit [Fintype V] in
theorem weight_insert {S : Finset V} {w : V} (h : w ∉ S) : weight adj (insert w S) = weight adj S + 1 + (adj w).length := by
  rw [weight, sum_insert h, weight]
  omega

omit [Fintype V] in
theorem Loop.start {w : V} {pa : Option (E × V)} {σ : St V E} (hw : w ∉ σ.vis) (hI : Inv σ) :
    Loop adj w pa σ [] (start w pa σ) := by
  have hne : ∀ {x}, x ∈ σ.vis → x ≠ w := fun hx h => hw (h ▸ hx)
  refine ⟨⟨subset_insert _ _, Nat.le_succ _, fun x hx => ?_, fun _ _ => rfl, fun x hx => ?_, fun x hx _ => ?_, fun z hz hz' => ?_⟩,
    mem_insert_self _ _, ?_, ?_, Nat.lt_succ_self _, ⟨fun x hx => ?_, fun x hx y hy hxy => ?_, fun x => ?_, ?_⟩, fun x hx hx' hxw => ?_, fun x hx hx' hxw => ?_,
    fun q hq => absurd hq List.not_mem_nil, ?_, fun x hx hx' hxw => ?_, fun q hq => absurd hq List.not_mem_nil, Or.inl ?_, ?_⟩
  · simp [BridgeDFS.start, Function.update_of_ne (hne hx)]
  · simp [BridgeDFS.start, Function.update_of_ne (hne hx)]
  · simp [BridgeDFS.start, Function.update_of_ne (hne hx)]
  · have : z = w := (mem_insert.1 hz).resolve_right hz' 
    subst this
    simp [BridgeDFS.start]
  · simp [BridgeDFS.start]
  · simp [BridgeDFS.start]
  · rcases mem_insert.1 hx with rfl | hx'
    · simp [BridgeDFS.start]
    · have := hI.lt x hx'
      simp only [BridgeDFS.start, Function.update_of_ne (hne hx')]
      omega
  · rcases mem_insert.1 hx with rfl | hx' <;> rcases mem_insert.1 hy with rfl | hy'
    · rfl
    · have := hI.lt y hy'
      simp only [BridgeDFS.start, Function.update_self, Function.update_of_ne (hne hy')] at hxy
      omega
    · have := hI.lt x hx'
      simp only [BridgeDFS.start, Function.update_self, Function.update_of_ne (hne hx')] at hxy
      omega
    · simp only [BridgeDFS.start, Function.update_of_ne (hne hx'), Function.update_of_ne (hne hy')] at hxy
      exact hI.inj x hx' y hy' hxy
  · simp only [BridgeDFS.start, List.mem_cons, mem_insert, hI.ord]
  · refine List.pairwise_cons.2 ⟨fun b hb => ?_, hI.sorted.imp_of_mem fun {a b} ha hb hab => ?_⟩
    · have hb' := (hI.ord b).1 hb
      have := hI.lt b hb'
      simp only [BridgeDFS.start, Function.update_self, Function.update_of_ne (hne hb')]
      exact this
    · simp only [BridgeDFS.start, Function.update_of_ne (hne ((hI.ord a).1 ha)), Function.update_of_ne (hne ((hI.ord b).1 hb))]
      exact hab
  · exact absurd ((mem_insert.1 hx).resolve_right hx') hxw
  · exact absurd ((mem_insert.1 hx).resolve_right hx') hxw
  · simp [BridgeDFS.start]
  · exact absurd ((mem_insert.1 hx).resolve_right hx') hxw
  · simp [BridgeDFS.start]
  · simp only [BridgeDFS.start, weight_insert hw, List.length_nil]
    omega

omit [Fintype V] in
/-- Counting a step: nothing else changes. -/
theorem Good.tick {σ : St V E} {x : V} (h : Good adj σ x) : Good adj { σ with count := σ.count + 1 } x :=
  ⟨h.g0, h.g6, h.g1, h.g2, h.g3, h.g4, h.g4', h.g5, h.g7⟩

omit [Fintype V] in
/-- Lowering `low w` changes nothing at `x ≠ w`. -/
theorem Good.lower {σ : St V E} {x w : V} {a : ℕ} (h : Good adj σ x) (hx : x ≠ w) : Good adj (BridgeDFS.lower w a σ) x := by
  have hl : (BridgeDFS.lower w a σ).low x = σ.low x := by simp [BridgeDFS.lower, Function.update_of_ne hx]
  exact ⟨h.g0, h.g6, h.g1, h.g2, by rw [hl]; exact h.g3, by rw [hl]; exact h.g4, by rw [hl]; exact h.g4', h.g5, h.g7⟩

omit [Fintype V] in
theorem Frozen.lower {w : V} {a : ℕ} {σ σ' : St V E} (h : Frozen w σ σ') : Frozen w σ (BridgeDFS.lower w a σ') :=
  ⟨h.vis, h.time, h.disc, h.fin, h.par, fun x hx hxw => by simp [BridgeDFS.lower, Function.update_of_ne hxw, h.low x hx hxw], h.new⟩

omit [Fintype V] in
theorem Frozen.tick {w : V} {σ σ' : St V E} (h : Frozen w σ σ') : Frozen w σ { σ' with count := σ'.count + 1 } :=
  ⟨h.vis, h.time, h.disc, h.fin, h.par, h.low, h.new⟩

omit [Fintype V] in
/-- The entry `q` of the adjacency list, at the arc to the parent: skipped. -/
theorem Loop.step_parent {w : V} {pa : Option (E × V)} {σ c : St V E} {done : List (E × V)} {q : E × V} (h : Loop adj w pa σ done c)
    (hinc : IsIncidence adj) (hw : w ∉ σ.vis) (hPa : PaOK adj σ w pa) (hq : q ∈ adj w) (hp : pa.map Prod.fst = some q.1) :
    Loop adj w pa σ (done ++ [q]) { c with count := c.count + 1 } := by
  obtain ⟨⟨e, p⟩, rfl, he⟩ := Option.map_eq_some_iff.1 hp
  simp only at he
  subst he
  obtain ⟨hpv, hpa⟩ := hPa q.1 p rfl
  have hqv : q.2 ∈ c.vis := by
    rcases hinc.other w q.1 q.2 p (by simpa using hq) hpa with h₁ | h₁ | h₁
    · exact h₁ ▸ h.frozen.vis hpv
    · exact h₁ ▸ h.mem
    · exact absurd (h₁ ▸ hpv) hw
  refine ⟨h.frozen.tick, h.mem, h.disc, h.par, h.lt, ⟨h.inv.lt, h.inv.inj, h.inv.ord, h.inv.sorted⟩, fun x hx hx' hxw => (h.good x hx hx' hxw).tick, h.tree, fun r hr => ?_, h.low, h.cover,
    fun r hr hne => ?_, h.wit, ?_⟩
  · rcases List.mem_append.1 hr with hr | hr
    · exact h.dn r hr
    · rw [List.mem_singleton.1 hr]
      exact hqv
  · rcases List.mem_append.1 hr with hr | hr
    · exact h.coverw r hr hne
    · rw [List.mem_singleton.1 hr] at hne
      exact absurd rfl hne
  · have := h.count
    simp only [List.length_append, List.length_singleton]
    omega

omit [Fintype V] in
/-- The entry `q`, to a visited vertex: `low w` is lowered by its discovery time. -/
theorem Loop.step_visited {w : V} {pa : Option (E × V)} {σ c : St V E} {done : List (E × V)} {q : E × V} (h : Loop adj w pa σ done c)
    (hw : w ∉ σ.vis) (hq : q ∈ adj w) (hp : pa.map Prod.fst ≠ some q.1) (hv : q.2 ∈ c.vis) :
    Loop adj w pa σ (done ++ [q]) (BridgeDFS.lower w (c.disc q.2) { c with count := c.count + 1 }) := by
  have hlow : (BridgeDFS.lower w (c.disc q.2) { c with count := c.count + 1 }).low w = min (c.low w) (c.disc q.2) := by
    simp [BridgeDFS.lower]
  refine ⟨h.frozen.tick.lower, h.mem, h.disc, h.par, h.lt, ⟨h.inv.lt, h.inv.inj, h.inv.ord, h.inv.sorted⟩, fun x hx hx' hxw => (h.good x hx hx' hxw).tick.lower hxw, h.tree, fun r hr => ?_, ?_, ?_,
    ?_, ?_, ?_⟩
  · rcases List.mem_append.1 hr with hr | hr
    · exact h.dn r hr
    · rw [List.mem_singleton.1 hr]
      exact hv
  · rw [hlow]
    exact (min_le_left _ _).trans h.low
  · intro x hx hx' hxw r hr hne
    rw [hlow]
    exact (min_le_left _ _).trans (h.cover x hx hx' hxw r hr hne)
  · intro r hr hne
    rw [hlow]
    rcases List.mem_append.1 hr with hr | hr
    · exact (min_le_left _ _).trans (h.coverw r hr hne)
    · rw [List.mem_singleton.1 hr]
      exact min_le_right _ _
  · rw [hlow]
    rcases le_total (c.low w) (c.disc q.2) with hle | hle
    · rw [min_eq_left hle]
      exact h.wit
    · rw [min_eq_right hle]
      refine Or.inr ⟨w, h.mem, hw, q, hq, hv, ?_, rfl⟩
      change (c.par w).map Prod.fst ≠ _
      rwa [h.par]
  · have := h.count
    simp only [BridgeDFS.lower, List.length_append, List.length_singleton]
    omega

omit [Fintype V] in
/-- The entry `q`, to a new vertex: the call on it returns, and `low w` is lowered by its `low`. -/
theorem Loop.step_new {w : V} {pa : Option (E × V)} {σ c σ₂ : St V E} {done : List (E × V)} {q : E × V} (h : Loop adj w pa σ done c)
    (hw : w ∉ σ.vis) (hq : q ∈ adj w) (hp : pa.map Prod.fst ≠ some q.1) (hnew : q.2 ∉ c.vis)
    (hpost : Post adj q.2 (some (q.1, w)) { c with count := c.count + 1 } σ₂) :
    Loop adj w pa σ (done ++ [q]) (BridgeDFS.lower w (σ₂.low q.2) σ₂) := by
  set y := q.2 with hy
  have hF : Frozen y { c with count := c.count + 1 } σ₂ := hpost.frozen
  have hwy : w ≠ y := fun e => hnew (e ▸ h.mem)
  have hne : ∀ {x}, x ∈ c.vis → x ≠ y := fun hx e => hnew (e ▸ hx)
  have hFw : Frozen w c σ₂ := ⟨hF.vis, hF.time, hF.disc, hF.fin, hF.par, fun x hx _ => hF.low x hx (hne hx), hF.new⟩
  have hlw : σ₂.low w = c.low w := hF.low w h.mem hwy
  have hlow : (BridgeDFS.lower w (σ₂.low y) σ₂).low w = min (c.low w) (σ₂.low y) := by
    simp [BridgeDFS.lower, hlw]
  have hyw : y ≠ w := hwy.symm
  have hgoody : Good adj σ₂ y := hpost.good y hpost.mem hnew
  have hsuby : ∀ x, x ∈ σ₂.vis → x ∉ c.vis → x ∈ sub σ₂ y := by
    intro x hx hx'
    refine mem_filter.2 ⟨hx, ?_, ?_⟩
    · rw [hpost.disc]
      exact hF.new x hx hx'
    · rw [hpost.fin]
      exact hpost.inv.lt x hx
  have hgoodc : ∀ x ∈ c.vis, x ∉ σ.vis → x ≠ w → Good adj σ₂ x := fun x hx hx' hxw =>
    (h.good x hx hx' hxw).tick.mono hx hF.vis hF.disc hF.par (hF.fin x hx) (hF.low x hx (hne hx)) hF.time hF.new
  have hgoodn : ∀ x ∈ σ₂.vis, x ∉ c.vis → Good adj σ₂ x := fun x hx hx' => hpost.good x hx hx'
  have hparent : ∀ {e p}, some (e, p) = some (q.1, w) → e = q.1 ∧ p = w := fun h' => by
    simpa using h'
  refine ⟨(h.frozen.trans hFw).lower, hF.vis h.mem, ?_, ?_, ?_, ⟨hpost.inv.lt, hpost.inv.inj, hpost.inv.ord, hpost.inv.sorted⟩, fun x hx hx' hxw => ?_, fun x hx hx' hxw => ?_, fun r hr => ?_, ?_, fun x hx hx' hxw r hr hrp => ?_,
    fun r hr hrp => ?_, ?_, ?_⟩
  · change σ₂.disc w = σ.time
    rw [hF.disc w h.mem]
    exact h.disc
  · change σ₂.par w = pa
    rw [hF.par w h.mem]
    exact h.par
  · exact lt_of_lt_of_le h.lt hF.time
  · -- what is recorded
    by_cases hxc : x ∈ c.vis
    · exact (hgoodc x hxc hx' hxw).lower hxw
    · exact (hgoodn x hx hxc).lower hxw
  · -- the tree
    by_cases hxc : x ∈ c.vis
    · obtain ⟨f, p, h₁, h₂, h₃, h₄, h₅⟩ := h.tree x hxc hx' hxw
      refine ⟨f, p, ?_, h₂, hF.vis h₃, h₄, ?_⟩
      · change σ₂.par x = _
        rw [hF.par x hxc]
        exact h₁
      · change σ₂.disc p < σ₂.disc x
        rw [hF.disc p h₃, hF.disc x hxc]
        exact h₅
    · by_cases hxy : x = y
      · subst hxy
        have hmem : (q.1, w) ∈ adj q.2 := (hgoody.g7 q.1 w hpost.par).2.1
        refine ⟨q.1, w, hpost.par, hmem, hF.vis h.mem, hw, (hgoody.g7 q.1 w hpost.par).2.2⟩
      · obtain ⟨f, p, h₁, h₂, h₃, h₄⟩ := hgoody.g5 x (hsuby x hx hxc) hxy
        have hpn : p ∉ σ.vis := by
          intro hpo
          have hpc := h.frozen.vis hpo
          have hdp : σ₂.disc y ≤ σ₂.disc p := (mem_filter.1 h₃).2.1
          rw [hpost.disc] at hdp
          have := h.inv.lt p hpc
          rw [hF.disc p hpc] at hdp
          change c.time ≤ c.disc p at hdp
          omega
        exact ⟨f, p, h₁, h₂, (mem_filter.1 h₃).1, hpn, h₄⟩
  · rcases List.mem_append.1 hr with hr | hr
    · exact hF.vis (h.dn r hr)
    · rw [List.mem_singleton.1 hr]
      exact hpost.mem
  · rw [hlow]
    exact (min_le_left _ _).trans h.low
  · -- `low w` covers the vertices below
    rw [hlow]
    change min (c.low w) (σ₂.low y) ≤ σ₂.disc r.2
    by_cases hxc : x ∈ c.vis
    · have h₁ := h.cover x hxc hx' hxw r hr (by rwa [← hF.par x hxc])
      have hrv : r.2 ∈ c.vis := (h.good x hxc hx' hxw).g1 x (mem_filter.2 ⟨hxc, le_rfl, (h.good x hxc hx' hxw).g0⟩) r hr
      rw [hF.disc _ hrv]
      exact (min_le_left _ _).trans h₁
    · exact (min_le_right _ _).trans (hgoody.g3 x (hsuby x hx hxc) r hr hrp)
  · rw [hlow]
    change min (c.low w) (σ₂.low y) ≤ σ₂.disc r.2
    rcases List.mem_append.1 hr with hr | hr
    · rw [hF.disc _ (h.dn r hr)]
      exact (min_le_left _ _).trans (h.coverw r hr hrp)
    · rw [List.mem_singleton.1 hr]
      exact (min_le_right _ _).trans hgoody.g4
  · -- the witness
    rw [hlow]
    rcases le_total (c.low w) (σ₂.low y) with hle | hle
    · rw [min_eq_left hle]
      rcases h.wit with h₁ | ⟨x, hx, hx', r, hr, hrv, h₁, h₂⟩
      · exact Or.inl h₁
      · refine Or.inr ⟨x, hF.vis hx, hx', r, hr, hF.vis hrv, ?_, ?_⟩
        · change (σ₂.par x).map Prod.fst ≠ _
          rwa [hF.par x hx]
        · change σ₂.disc r.2 = _
          rw [hF.disc _ hrv]
          exact h₂
    · rw [min_eq_right hle]
      rcases hgoody.g4' with h₁ | ⟨x, hx, r, hr, h₁, h₂⟩
      · refine Or.inr ⟨w, hF.vis h.mem, hw, q, hq, hpost.mem, ?_, ?_⟩
        · change (σ₂.par w).map Prod.fst ≠ _
          rw [hF.par w h.mem, h.par]
          exact hp
        · exact h₁.symm
      · have hxv := (mem_filter.1 hx).1
        have hxn : x ∉ σ.vis := by
          intro hxo
          have hxc := h.frozen.vis hxo
          have hdp : σ₂.disc y ≤ σ₂.disc x := (mem_filter.1 hx).2.1
          rw [hpost.disc, hF.disc x hxc] at hdp
          have := h.inv.lt x hxc
          change c.time ≤ c.disc x at hdp
          omega
        exact Or.inr ⟨x, hxv, hxn, r, hr, hgoody.g1 x hx r hr, h₁, h₂⟩
  · have h₁ := h.count
    have h₂ := hpost.count
    simp only [BridgeDFS.lower, List.length_append, List.length_singleton] at h₂ ⊢
    omega

omit [Fintype V] in
/-- The end of the loop: the call returns what it should. -/
theorem Loop.finish {w : V} {pa : Option (E × V)} {σ c : St V E} (h : Loop adj w pa σ (adj w) c) (hinc : IsIncidence adj) (hw : w ∉ σ.vis) (hI : Inv σ)
    (hPa : PaOK adj σ w pa) (hPre : PreAbove adj σ pa) : Post adj w pa σ { c with fin := Function.update c.fin w c.time } := by
  set τ : St V E := { c with fin := Function.update c.fin w c.time } with hτ
  have hne : ∀ {x}, x ∈ σ.vis → x ≠ w := fun hx e => hw (e ▸ hx)
  have hfw : τ.fin w = c.time := by simp [hτ]
  have hfx : ∀ {x}, x ≠ w → τ.fin x = c.fin x := fun hx => by simp [hτ, Function.update_of_ne hx]
  have hold : ∀ {x}, x ∈ σ.vis → c.disc x < σ.time := fun {x} hx => by
    rw [h.frozen.disc x hx]
    exact hI.lt x hx
  have hsub : ∀ y, y ∈ sub τ w ↔ y ∈ c.vis ∧ y ∉ σ.vis := by
    intro y
    simp only [sub, mem_filter, hfw]
    change y ∈ c.vis ∧ c.disc w ≤ c.disc y ∧ c.disc y < c.time ↔ _
    rw [h.disc]
    constructor
    · rintro ⟨hy, h₁, _⟩
      exact ⟨hy, fun hy' => absurd (hold hy') (not_lt.2 h₁)⟩
    · rintro ⟨hy, hy'⟩
      exact ⟨hy, h.frozen.new y hy hy', h.inv.lt y hy⟩
  have hgoodx : ∀ x ∈ c.vis, x ∉ σ.vis → x ≠ w → Good adj τ x := fun x hx hx' hxw =>
    (h.good x hx hx' hxw).mono hx Subset.rfl (fun _ _ => rfl) (fun _ _ => rfl) (hfx hxw) rfl le_rfl (fun z hz hz' => absurd hz hz')
  have hmemsub : ∀ {x}, x ∈ c.vis → x ∉ σ.vis → x ≠ w → x ∈ sub c x := fun {x} hx hx' hxw =>
    mem_filter.2 ⟨hx, le_rfl, (h.good x hx hx' hxw).g0⟩
  have hadj : ∀ y ∈ c.vis, y ∉ σ.vis → ∀ q ∈ adj y, q.2 ∈ c.vis := by
    intro y hy hy' q hq
    by_cases hyw : y = w
    · subst hyw
      exact h.dn q hq
    · exact (h.good y hy hy' hyw).g1 y (hmemsub hy hy' hyw) q hq
  refine ⟨⟨h.frozen.vis, h.frozen.time, h.frozen.disc, fun x hx => ?_, h.frozen.par, h.frozen.low, h.frozen.new⟩, h.mem, h.disc, h.par, hfw, h.lt, ⟨h.inv.lt, h.inv.inj, h.inv.ord, h.inv.sorted⟩, fun x hx hx' => ?_, ?_⟩
  · rw [hfx (hne hx)]
    exact h.frozen.fin x hx
  · by_cases hxw : x = w
    · subst hxw
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [hfw]
        change c.disc x < c.time
        exact h.inv.lt x h.mem
      · rw [hfw]
      · intro y hy q hq
        obtain ⟨h₁, h₂⟩ := (hsub y).1 hy
        exact hadj y h₁ h₂ q hq
      · intro y hy q hq
        obtain ⟨h₁, h₂⟩ := (hsub y).1 hy
        have hqv := hadj y h₁ h₂ q hq
        by_cases hq₂ : q.2 ∈ σ.vis
        · right
          have hsy := hinc.symm y q.1 q.2 hq
          by_cases hpa : ∀ e p, pa = some (e, p) → σ.disc p < σ.disc q.2
          · exact absurd (hPre q.2 hq₂ hpa (q.1, y) hsy) h₂
          · simp only [not_forall] at hpa
            obtain ⟨e, p, hpe, hlt⟩ := hpa
            refine ⟨e, p, by rw [← hpe]; exact h.par, ?_⟩
            change c.disc q.2 ≤ c.disc p
            rw [h.frozen.disc _ hq₂, h.frozen.disc p (hPa e p hpe).1]
            exact not_lt.1 hlt
        · exact Or.inl ((hsub _).2 ⟨hqv, hq₂⟩)
      · intro y hy q hq hne'
        obtain ⟨h₁, h₂⟩ := (hsub y).1 hy
        by_cases hyw : y = x
        · subst hyw
          refine h.coverw q hq ?_
          rw [← h.par]
          exact hne'
        · exact h.cover y h₁ h₂ hyw q hq hne'
      · change c.low x ≤ c.disc x
        rw [h.disc]
        exact h.low
      · change c.low x = c.disc x ∨ _
        rw [h.disc]
        rcases h.wit with h₁ | ⟨y, hy, hy', q, hq, _, h₁, h₂⟩
        · exact Or.inl h₁
        · exact Or.inr ⟨y, (hsub y).2 ⟨hy, hy'⟩, q, hq, h₁, h₂⟩
      · intro y hy hyx
        obtain ⟨h₁, h₂⟩ := (hsub y).1 hy
        obtain ⟨f, p, h₃, h₄, h₅, h₆, h₇⟩ := h.tree y h₁ h₂ hyx
        exact ⟨f, p, h₃, h₄, (hsub p).2 ⟨h₅, h₆⟩, h₇⟩
      · intro e p hp
        have hpe : pa = some (e, p) := by rw [← h.par]; exact hp
        obtain ⟨h₁, h₂⟩ := hPa e p hpe
        refine ⟨h.frozen.vis h₁, h₂, ?_⟩
        change c.disc p < c.disc x
        rw [h.disc]
        exact hold h₁
    · exact hgoodx x hx hx' hxw
  · have := h.count
    change c.count + weight adj σ.vis = σ.count + weight adj c.vis
    omega

omit [Fintype V] in
/-- What the entry `q` does, given what the calls below do. -/
theorem Loop.step {n : ℕ} {w : V} {pa : Option (E × V)} {σ c : St V E} {done : List (E × V)} {q : E × V} (h : Loop adj w pa σ done c)
    (hinc : IsIncidence adj) (hw : w ∉ σ.vis) (hPa : PaOK adj σ w pa) (hq : q ∈ adj w)
    (ih : ∀ c₁ : St V E, q.2 ∉ c₁.vis → PaOK adj c₁ q.2 (some (q.1, w)) → PreAbove adj c₁ (some (q.1, w)) → c₁.vis = c.vis → c₁.disc = c.disc → Inv c₁ →
      Post adj q.2 (some (q.1, w)) c₁ (visit adj n q.2 (some (q.1, w)) c₁))
    (hI : Inv σ) :
    Loop adj w pa σ (done ++ [q]) (BridgeDFS.step (visit adj n) w pa c q) := by
  by_cases hp : pa.map Prod.fst = some q.1
  · have hs : BridgeDFS.step (visit adj n) w pa c q = { c with count := c.count + 1 } := ite_eq_left hp
    rw [hs]
    exact h.step_parent hinc hw hPa hq hp
  by_cases hv : q.2 ∈ c.vis
  · have hs : BridgeDFS.step (visit adj n) w pa c q = BridgeDFS.lower w (c.disc q.2) { c with count := c.count + 1 } :=
      (ite_eq_right hp).trans (ite_eq_left hv)
    rw [hs]
    exact h.step_visited hw hq hp hv
  · have hs : BridgeDFS.step (visit adj n) w pa c q = BridgeDFS.lower w ((visit adj n q.2 (some (q.1, w)) { c with count := c.count + 1 }).low q.2)
        (visit adj n q.2 (some (q.1, w)) { c with count := c.count + 1 }) :=
      (ite_eq_right hp).trans (ite_eq_right hv)
    rw [hs]
    refine h.step_new hw hq hp hv (ih { c with count := c.count + 1 } hv (fun e p hep => ?_) (fun y hy hyd r hr => ?_) rfl rfl ⟨h.inv.lt, h.inv.inj, h.inv.ord, h.inv.sorted⟩)
    · obtain ⟨he, hp'⟩ : e = q.1 ∧ p = w := by
        have := Option.some.inj hep
        exact ⟨congrArg Prod.fst this.symm, congrArg Prod.snd this.symm⟩
      subst he hp'
      exact ⟨h.mem, hinc.symm _ _ _ hq⟩
    · have hd : c.disc w < c.disc y := hyd q.1 w rfl
      rw [h.disc] at hd
      have hy₁ : y ∉ σ.vis := fun hy' => by
        have := hI.lt y hy'
        rw [← h.frozen.disc y hy'] at this
        omega
      have hyw : y ≠ w := fun e => by
        rw [e, h.disc] at hd
        omega
      have hg := h.good y hy hy₁ hyw
      exact hg.g1 y (mem_filter.2 ⟨hy, le_rfl, hg.g0⟩) r hr

omit [Fintype V] in
/-- The loop over the rest `l` of the adjacency list. -/
theorem Loop.fold {n : ℕ} {w : V} {pa : Option (E × V)} {σ : St V E} (hinc : IsIncidence adj) (hw : w ∉ σ.vis) (hPa : PaOK adj σ w pa) (hI : Inv σ)
    (ih : ∀ {c : St V E} {done : List (E × V)} {q : E × V}, Loop adj w pa σ done c → q ∈ adj w → ∀ c₁ : St V E, q.2 ∉ c₁.vis → PaOK adj c₁ q.2 (some (q.1, w)) →
      PreAbove adj c₁ (some (q.1, w)) → c₁.vis = c.vis → c₁.disc = c.disc → Inv c₁ → Post adj q.2 (some (q.1, w)) c₁ (visit adj n q.2 (some (q.1, w)) c₁)) :
    ∀ (l done : List (E × V)) (c : St V E), done ++ l = adj w → Loop adj w pa σ done c →
      Loop adj w pa σ (adj w) (l.foldl (BridgeDFS.step (visit adj n) w pa) c) := by
  intro l
  induction l with
  | nil =>
    intro done c hl h
    rw [List.append_nil] at hl
    rw [List.foldl_nil, ← hl]
    exact h
  | cons q l ihl =>
    intro done c hl h
    have hq : q ∈ adj w := by
      rw [← hl]
      simp
    exact ihl (done ++ [q]) _ (by rw [← hl]; simp) (h.step hinc hw hPa hq (ih h hq) hI)

/-- **What a call does**, by induction on the fuel, which is enough when it covers the vertices not yet visited. -/
theorem visit_spec (hinc : IsIncidence adj) : ∀ (n : ℕ) (w : V) (pa : Option (E × V)) (σ : St V E),
    w ∉ σ.vis → (univ \ σ.vis).card ≤ n → Inv σ → PaOK adj σ w pa → PreAbove adj σ pa →
    Post adj w pa σ (visit adj n w pa σ) := by
  intro n
  induction n with
  | zero =>
    intro w pa σ hw hc
    have : w ∈ univ \ σ.vis := mem_sdiff.2 ⟨mem_univ w, hw⟩
    rw [card_eq_zero.1 (Nat.le_zero.1 hc)] at this
    exact absurd this (notMem_empty w)
  | succ n ih =>
    intro w pa σ hw hc hI hPa hPre
    have hfold := Loop.fold (n := n) hinc hw hPa hI (fun {c done q} h _ c₁ hq₁ hPa₁ hPre₁ hvc _ hI₁ => by
        refine ih q.2 _ c₁ hq₁ ?_ hI₁ hPa₁ hPre₁
        rw [hvc]
        have hlt : (univ \ c.vis).card < (univ \ σ.vis).card := by
          refine card_lt_card ⟨sdiff_subset_sdiff Subset.rfl h.frozen.vis, fun hsub => ?_⟩
          exact (mem_sdiff.1 (hsub (mem_sdiff.2 ⟨mem_univ w, hw⟩))).2 h.mem
        omega)
      (adj w) [] (BridgeDFS.start w pa σ) rfl (Loop.start hw hI)
    exact hfold.finish hinc hw hI hPa hPre

/-! ### The whole search -/

/-- The state before a search. -/
def init : St V E := ⟨∅, fun _ => 0, fun _ => 0, fun _ => 0, fun _ => none, 0, 0, []⟩

/-- **The search from `r`.** -/
def run (adj : V → List (E × V)) (r : V) : St V E := visit adj (Fintype.card V) r none init

theorem run_post (hinc : IsIncidence adj) (r : V) : Post adj r none (init : St V E) (run adj r) :=
  visit_spec hinc _ r none init (notMem_empty r) (card_le_univ _) ⟨fun _ h => absurd h (notMem_empty _), fun _ h => absurd h (notMem_empty _), fun x => by simp [init],
    List.Pairwise.nil⟩ (fun _ _ h => by simp at h) (fun _ h => absurd h (notMem_empty _))

/-- `adj x` lists the arcs at `x` with their other ends: the adjacency lists of `G`, taken as undirected. -/
def Lists (G : DirectedMultigraph V E) (adj : V → List (E × V)) : Prop :=
  ∀ x f y, (f, y) ∈ adj x ↔ (G.source f = x ∧ G.target f = y) ∨ (G.target f = x ∧ G.source f = y)

variable {G : DirectedMultigraph V E}

omit [Fintype V] in
theorem Lists.isIncidence (h : Lists G adj) : IsIncidence adj := by
  refine ⟨fun x f y hf => (h y f x).2 ?_, fun x f y y' hf hf' => ?_⟩
  · rcases (h x f y).1 hf with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
    · exact Or.inr ⟨h₂, h₁⟩
    · exact Or.inl ⟨h₂, h₁⟩
  · rcases (h x f y).1 hf with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ <;> rcases (h x f y').1 hf' with ⟨h₃, h₄⟩ | ⟨h₃, h₄⟩
    · exact Or.inl (h₂.symm.trans h₄)
    · exact Or.inr (Or.inl (h₃.symm.trans h₂))
    · exact Or.inr (Or.inr (h₁.symm.trans h₄))
    · exact Or.inl (h₂.symm.trans h₄)

omit [Fintype V] in
theorem Lists.crosses (h : Lists G adj) {f : E} {x y : V} {S : Set V} (hf : (f, y) ∈ adj x) (hx : x ∈ S) (hy : y ∉ S) : G.Crosses f S := by
  rcases (h x f y).1 hf with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
  · exact Or.inl ⟨h₁ ▸ hx, h₂ ▸ hy⟩
  · exact Or.inr ⟨h₁ ▸ hx, h₂ ▸ hy⟩

omit [Fintype V] in
theorem Lists.of_crosses (h : Lists G adj) {f : E} {S : Set V} (hf : G.Crosses f S) : ∃ x y, x ∈ S ∧ y ∉ S ∧ (f, y) ∈ adj x := by
  rcases hf with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
  · exact ⟨_, _, h₁, h₂, (h _ _ _).2 (Or.inl ⟨rfl, rfl⟩)⟩
  · exact ⟨_, _, h₁, h₂, (h _ _ _).2 (Or.inr ⟨rfl, rfl⟩)⟩

omit [Fintype V] in
/-- Two entries of one arc: the other end of one is an end of the other. -/
theorem Lists.ends (h : Lists G adj) {f : E} {a b c d : V} (h₁ : (f, a) ∈ adj b) (h₂ : (f, c) ∈ adj d) : a = c ∨ a = d := by
  rcases (h b f a).1 h₁ with ⟨h₃, h₄⟩ | ⟨h₃, h₄⟩ <;> rcases (h d f c).1 h₂ with ⟨h₅, h₆⟩ | ⟨h₅, h₆⟩
  · exact Or.inl (h₄.symm.trans h₆)
  · exact Or.inr (h₄.symm.trans h₅)
  · exact Or.inr (h₄.symm.trans h₅)
  · exact Or.inl (h₄.symm.trans h₆)

/-- What the proof reads of the state of a search that reached everything. -/
structure Done (adj : V → List (E × V)) (τ : St V E) (r : V) : Prop where
  all : ∀ x, x ∈ τ.vis
  good : ∀ x, Good adj τ x
  root : τ.par r = none
  top : ∀ x, x ∈ sub τ r
  inj : ∀ x y, τ.disc x = τ.disc y → x = y
  inv : Inv τ

/-- A search reaches everything in a connected graph. -/
theorem done_run (hG : G.IsConnected) (h : Lists G adj) (r : V) : Done adj (run adj r) r := by
  have hP := run_post h.isIncidence r
  have hgood : ∀ x ∈ (run adj r).vis, Good adj (run adj r) x := fun x hx => hP.good x hx (notMem_empty x)
  have hsub : ∀ x ∈ (run adj r).vis, x ∈ sub (run adj r) r := fun x hx =>
    mem_filter.2 ⟨hx, by rw [hP.disc]; exact Nat.zero_le _, by rw [hP.fin]; exact hP.inv.lt x hx⟩
  have hall : ∀ x, x ∈ (run adj r).vis := by
    intro x
    have hw := hG r x
    induction hw with
    | refl => exact hP.mem
    | @tail u v _ hstep ih =>
      obtain ⟨f, _, hf⟩ := hstep
      have hq : (f, v) ∈ adj u := by
        rcases hf with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
        · exact (h u f v).2 (Or.inl ⟨h₁, h₂⟩)
        · exact (h u f v).2 (Or.inr ⟨h₂, h₁⟩)
      rcases (hgood r hP.mem).g2 u (hsub u ih) (f, v) hq with h₁ | ⟨e, p, h₁, _⟩
      · exact (mem_filter.1 h₁).1
      · rw [hP.par] at h₁
        simp at h₁
  exact ⟨hall, fun x => hgood x (hall x), hP.par, fun x => hsub x (hall x), fun x y hxy => hP.inv.inj x (hall x) y (hall y) hxy, hP.inv⟩

/-! ### Bridges -/

section Bridges

variable {τ : St V E} {r : V}

omit [Fintype V] in
theorem Done.self_mem (hτ : Done adj τ r) (x : V) : x ∈ sub τ x := mem_filter.2 ⟨hτ.all x, le_rfl, (hτ.good x).g0⟩

omit [Fintype V] in
/-- The parent of a vertex in `sub τ x` keeps it there: `sub τ x` is closed under children. -/
theorem Done.child_mem (hτ : Done adj τ r) (hinc : IsIncidence adj) {x y p : V} {f : E} (hy : τ.par y = some (f, p)) (hp : p ∈ sub τ x) : y ∈ sub τ x := by
  obtain ⟨_, h₂, h₃⟩ := (hτ.good y).g7 f p hy
  rcases (hτ.good x).g2 p hp (f, y) (hinc.symm y f p h₂) with h₁ | ⟨e', p', h₁, h₄⟩
  · exact h₁
  · have h₅ := ((hτ.good x).g7 e' p' h₁).2.2
    have h₆ := (mem_filter.1 hp).2.1
    change τ.disc y ≤ τ.disc p' at h₄
    omega

omit [Fintype V] in
/-- The cut of an arc to a parent with `disc p < low w`: the vertices below `w`. -/
theorem Done.crosses_iff (hτ : Done adj τ r) (h : Lists G adj) {w p : V} {e : E} (hpar : τ.par w = some (e, p)) (hlt : τ.disc p < τ.low w) (f : E) :
    G.Crosses f (sub τ w : Set V) ↔ f = e := by
  have hg := hτ.good w
  obtain ⟨_, hep, hpw⟩ := hg.g7 e p hpar
  have hpn : p ∉ sub τ w := fun hp => absurd (mem_filter.1 hp).2.1 (not_le.2 hpw)
  constructor
  · intro hf
    obtain ⟨y, z, hy, hz, hfz⟩ := h.of_crosses hf
    have hy : y ∈ sub τ w := hy
    have hz : z ∉ sub τ w := hz
    obtain ⟨e', p', hpw', hle⟩ := (hg.g2 y hy (f, z) hfz).resolve_left hz
    obtain ⟨-, rfl⟩ : e' = e ∧ p' = p := by
      rw [hpar] at hpw'
      have := Option.some.inj hpw'
      exact ⟨congrArg Prod.fst this.symm, congrArg Prod.snd this.symm⟩
    change τ.disc z ≤ τ.disc p' at hle
    by_cases hp : (τ.par y).map Prod.fst = some f
    · by_cases hyw : y = w
      · subst hyw
        rw [hpar] at hp
        exact (Option.some.inj hp).symm
      · obtain ⟨f', p'', h₁, h₂, h₃, h₄⟩ := hg.g5 y hy hyw
        rw [h₁] at hp
        obtain rfl : f' = f := Option.some.inj hp
        rcases h.isIncidence.other y f' z p'' hfz h₂ with h₅ | h₅ | h₅
        · exact absurd (h₅ ▸ h₃) hz
        · exact absurd (h₅ ▸ hy) hz
        · rw [← h₅] at h₄
          exact absurd h₄ (lt_irrefl _)
    · have := hg.g3 y hy (f, z) hfz hp
      change τ.low w ≤ τ.disc z at this
      omega
  · rintro rfl
    exact h.crosses hep (hτ.self_mem w) hpn

omit [Fintype V] in
/-- A bridge is the arc to the parent of a vertex `w` with `disc p < low w`. -/
theorem Done.of_isBridge (hτ : Done adj τ r) (h : Lists G adj) {e : E} (he : G.underlying.IsBridge e) : ∃ w p, τ.par w = some (e, p) ∧ τ.disc p < τ.low w := by
  obtain ⟨S, hS⟩ := (G.isBridge_iff e).1 he
  obtain ⟨T, hT, hrT⟩ : ∃ T : Set V, (∀ f, G.Crosses f T ↔ f = e) ∧ r ∉ T := by
    by_cases hr : r ∈ S
    · refine ⟨Sᶜ, fun f => ?_, by simpa using hr⟩
      rw [← hS f]
      simp only [DirectedMultigraph.Crosses, Set.mem_compl_iff, not_not]
      tauto
    · exact ⟨S, hS, hr⟩
  have hne : ∃ x, x ∈ T := by
    rcases (hT e).2 rfl with ⟨h₁, _⟩ | ⟨h₁, _⟩ <;> exact ⟨_, h₁⟩
  obtain ⟨w, hwT, hmin⟩ : ∃ w ∈ T, ∀ y ∈ T, τ.disc w ≤ τ.disc y := by
    obtain ⟨x, hx⟩ := hne
    have hex : ∃ d, ∃ y ∈ T, τ.disc y = d := ⟨_, x, hx, rfl⟩
    obtain ⟨y, hy, hd⟩ := Nat.find_spec hex
    refine ⟨y, hy, fun z hz => ?_⟩
    rw [hd]
    exact Nat.find_min' hex ⟨z, hz, rfl⟩
  have hwr : w ≠ r := fun e' => hrT (e' ▸ hwT)
  obtain ⟨f, p, h₁, h₂, _, h₄⟩ := (hτ.good r).g5 w (hτ.top w) hwr
  have hpT : p ∉ T := fun hp => absurd (hmin p hp) (not_le.2 h₄)
  obtain rfl : f = e := (hT f).1 (h.crosses h₂ hwT hpT)
  refine ⟨w, p, h₁, ?_⟩
  by_contra hle
  have hle : τ.low w ≤ τ.disc p := not_lt.1 hle
  have hpn : p ∉ sub τ w := fun hp => absurd (mem_filter.1 hp).2.1 (not_le.2 h₄)
  have hg := hτ.good w
  have hsubT : ∀ d y, τ.disc y = d → y ∈ sub τ w → y ∈ T := by
    intro d
    induction d using Nat.strong_induction_on with
    | _ d ih =>
      intro y hd hy
      by_cases hyw : y = w
      · exact hyw ▸ hwT
      · obtain ⟨f', p', hy₁, hy₂, hy₃, hy₄⟩ := hg.g5 y hy hyw
        have hp'T := ih (τ.disc p') (hd ▸ hy₄) p' rfl hy₃
        by_contra hyT
        obtain rfl : f' = f := (hT f').1 (h.crosses (h.isIncidence.symm y f' p' hy₂) hp'T hyT)
        rcases h.ends h₂ hy₂ with h₅ | h₅
        · exact hpn (h₅ ▸ hy₃)
        · exact hpn (h₅ ▸ hy)
  rcases hg.g4' with h₅ | ⟨y, hy, q, hq, hne', hdq⟩
  · omega
  · have hyT := hsubT _ y rfl hy
    by_cases hqT : q.2 ∈ T
    · have := hmin q.2 hqT
      omega
    · have hqe : q.1 = f := (hT q.1).1 (h.crosses hq hyT hqT)
      have hq' : (f, y) ∈ adj q.2 := by
        have := h.isIncidence.symm y q.1 q.2 hq
        rwa [hqe] at this
      rcases h.ends hq' h₂ with h₅ | h₅
      · exact hpn (h₅ ▸ hy)
      · apply hne'
        rw [h₅, h₁, hqe]
        rfl

end Bridges

/-- **An arc is a bridge exactly when it is the arc to the parent of a vertex `w` with `disc p < low w`.** The graph is connected and may have parallel arcs; `adj` is any adjacency list of it. -/
theorem isBridge_iff (hG : G.IsConnected) (h : Lists G adj) (r : V) (e : E) :
    G.underlying.IsBridge e ↔ ∃ w p, (run adj r).par w = some (e, p) ∧ (run adj r).disc p < (run adj r).low w := by
  have hτ := done_run hG h r
  constructor
  · exact hτ.of_isBridge h
  · rintro ⟨w, p, hpar, hlt⟩
    exact (G.isBridge_iff e).2 ⟨_, hτ.crosses_iff h hpar hlt⟩

/-- The count: one step for each vertex and each entry of an adjacency list. -/
theorem count_run {r : V} (hinc : IsIncidence adj) (hall : ∀ x, x ∈ (run adj r).vis) :
    (run adj r).count = Fintype.card V + ∑ x, (adj x).length := by
  have hP := run_post hinc r
  have hc := hP.count
  have huniv : (run adj r).vis = univ := eq_univ_of_forall hall
  rw [huniv] at hc
  have h₀ : weight adj (init : St V E).vis = 0 := rfl
  have h₁ : (init : St V E).count = 0 := rfl
  rw [h₀, h₁] at hc
  simp only [weight, sum_add_distrib, sum_const, smul_eq_mul, mul_one, card_univ] at hc
  omega

/-- The incidence lists of `G`, from a list of its arcs. -/
def incidence (G : DirectedMultigraph V E) (l : List E) (x : V) : List (E × V) :=
  (l.filter fun f => G.source f = x).map (fun f => (f, G.target f)) ++ (l.filter fun f => G.target f = x).map fun f => (f, G.source f)

omit [Fintype V] in
theorem lists_incidence {l : List E} (hl : ∀ f, f ∈ l) : Lists G (incidence G l) := by
  intro x f y
  simp only [incidence, List.mem_append, List.mem_map, List.mem_filter, decide_eq_true_eq, Prod.mk.injEq]
  constructor
  · rintro (⟨g, ⟨_, h₂⟩, rfl, rfl⟩ | ⟨g, ⟨_, h₂⟩, rfl, rfl⟩)
    · exact Or.inl ⟨h₂, rfl⟩
    · exact Or.inr ⟨h₂, rfl⟩
  · rintro (⟨h₁, h₂⟩ | ⟨h₁, h₂⟩)
    · exact Or.inl ⟨f, ⟨hl f, h₁⟩, rfl, h₂⟩
    · exact Or.inr ⟨f, ⟨hl f, h₁⟩, rfl, h₂⟩

/-- Each arc is in the list of one vertex for each of its two ends. -/
theorem sum_length_filter (s : E → V) (l : List E) : ∑ x, (l.filter fun f => s f = x).length = l.length := by
  induction l with
  | nil => simp
  | cons a l ih =>
    have h₁ : ∀ x, ((a :: l).filter fun f => s f = x).length = (l.filter fun f => s f = x).length + if s a = x then 1 else 0 := by
      intro x
      by_cases hx : s a = x <;> simp [hx]
    simp only [h₁, sum_add_distrib, ih, sum_ite_eq, mem_univ, ite_true, List.length_cons]

theorem sum_length_incidence (l : List E) : ∑ x, (incidence G l x).length = 2 * l.length := by
  simp only [incidence, List.length_append, List.length_map, sum_add_distrib, sum_length_filter]
  omega

/-- **The operation count of the search**, on incidence lists: one step for each vertex and two for each arc. -/
theorem count_eq [Fintype E] (hG : G.IsConnected) (r : V) :
    (run (incidence G (univ : Finset E).toList) r).count = Fintype.card V + 2 * Fintype.card E := by
  have hL : Lists G (incidence G (univ : Finset E).toList) := lists_incidence fun f => by simp
  rw [count_run hL.isIncidence (done_run hG hL r).all, sum_length_incidence]
  simp

/-! ### Blobs -/

/-- `w` is the top of its blob: it has no parent, or the arc to it is a bridge. -/
def IsTop (τ : St V E) (w : V) : Prop := ∀ e p, τ.par w = some (e, p) → τ.disc p < τ.low w

/-- One pass over the vertices: a top is labelled by itself, another vertex by the label of its parent. -/
def labelStep (τ : St V E) (t : V → V) (x : V) : V → V :=
  Function.update t x (match τ.par x with
    | some (_, p) => if τ.disc p < τ.low x then x else t p
    | none => x)

/-- The labels, from the vertices in the order they were discovered: a parent is before its children, so one step for each vertex. -/
def labels (τ : St V E) : V → V := τ.order.reverse.foldl (labelStep τ) id

section Labels

variable {τ : St V E} {r : V}

omit [Fintype V] in
/-- The pass, on what remains: the equation of a label holds of what was passed. -/
theorem labels_fold (τ : St V E) (hpar : ∀ x f p, τ.par x = some (f, p) → p ≠ x) : ∀ (l P : List V) (t : V → V), (P ++ l).Nodup →
    (∀ x ∈ l, ∀ f p, τ.par x = some (f, p) → p ∈ P ∨ ∃ l₁ l₂, l = l₁ ++ x :: l₂ ∧ p ∈ l₁) →
    (∀ x ∈ P, ∀ f p, τ.par x = some (f, p) → p ∈ P) →
    (∀ x ∈ P, t x = match τ.par x with
      | some (_, p) => if τ.disc p < τ.low x then x else t p
      | none => x) →
    ∀ x ∈ P ++ l, l.foldl (labelStep τ) t x = match τ.par x with
      | some (_, p) => if τ.disc p < τ.low x then x else l.foldl (labelStep τ) t p
      | none => x := by
  intro l
  induction l with
  | nil =>
    intro P t _ _ _ ht x hx
    simpa using ht x (by simpa using hx)
  | cons y l ih =>
    intro P t hnd hl hP ht x hx
    rw [List.foldl_cons]
    have hnd' : (P ++ [y] ++ l).Nodup := by simpa using hnd
    have hyP : y ∉ P := by
      intro hy
      have := (List.nodup_append.1 hnd).2.2
      exact this y hy y (by simp) rfl
    have hy₂ : ∀ f p, τ.par y = some (f, p) → p ∈ P := by
      intro f p hp
      rcases hl y (by simp) f p hp with h₁ | ⟨l₁, l₂, h₁, h₂⟩
      · exact h₁
      · cases l₁ with
        | nil => simp at h₂
        | cons a l₃ =>
          exfalso
          simp only [List.cons_append, List.cons.injEq] at h₁
          obtain ⟨rfl, rfl⟩ := h₁
          rcases List.mem_cons.1 h₂ with h₃ | h₃
          · exact hpar _ _ _ hp h₃
          · have := List.nodup_append.1 hnd
            have hn : (y :: (l₃ ++ y :: l₂)).Nodup := this.2.1
            simp only [List.nodup_cons, List.mem_append, List.mem_cons, not_or] at hn
            exact absurd trivial hn.1.2.1
    refine ih (P ++ [y]) (labelStep τ t y) hnd' ?_ ?_ ?_ x (by simpa using hx)
    · intro z hz f p hp
      rcases hl z (List.mem_cons_of_mem _ hz) f p hp with h₁ | ⟨l₁, l₂, h₁, h₂⟩
      · exact Or.inl (List.mem_append_left _ h₁)
      · cases l₁ with
        | nil => simp at h₂
        | cons a l₃ =>
          simp only [List.cons_append, List.cons.injEq] at h₁
          obtain ⟨rfl, h₄⟩ := h₁
          rcases List.mem_cons.1 h₂ with h₃ | h₃
          · exact Or.inl (by simp [h₃])
          · exact Or.inr ⟨l₃, l₂, h₄, h₃⟩
    · intro z hz f p hp
      rcases List.mem_append.1 hz with hz | hz
      · exact List.mem_append_left _ (hP z hz f p hp)
      · rw [List.mem_singleton.1 hz] at hp
        exact List.mem_append_left _ (hy₂ f p hp)
    · intro z hz
      rcases List.mem_append.1 hz with hz | hz
      · have hzy : z ≠ y := fun e => hyP (e ▸ hz)
        simp only [labelStep, Function.update_of_ne hzy]
        have := ht z hz
        cases hq : τ.par z with
        | none => simpa [hq] using this
        | some a =>
          obtain ⟨f, p⟩ := a
          have hpy : p ≠ y := fun e => hyP (e ▸ hP z hz f p hq)
          rw [hq] at this
          simpa [Function.update_of_ne hpy] using this
      · rw [List.mem_singleton.1 hz]
        simp only [labelStep, Function.update_self]
        cases hq : τ.par y with
        | none => rfl
        | some a =>
          obtain ⟨f, p⟩ := a
          have hpy : p ≠ y := fun e => hyP (e ▸ hy₂ f p hq)
          simp [Function.update_of_ne hpy]

omit [Fintype V] in
/-- The equation of the labels. -/
theorem Done.labels_eq (hτ : Done adj τ r) (x : V) : labels τ x = match τ.par x with
    | some (_, p) => if τ.disc p < τ.low x then x else labels τ p
    | none => x := by
  have hsorted : τ.order.reverse.Pairwise fun a b => τ.disc a < τ.disc b := by
    rw [List.pairwise_reverse]
    exact hτ.inv.sorted
  have hnd : τ.order.reverse.Nodup := hsorted.imp fun {a b} hab e => by
    rw [e] at hab
    exact lt_irrefl _ hab
  have hpar : ∀ x f p, τ.par x = some (f, p) → p ≠ x := fun x f p hp e => by
    have := ((hτ.good x).g7 f p hp).2.2
    rw [e] at this
    exact lt_irrefl _ this
  refine labels_fold τ hpar τ.order.reverse [] id (by simpa using hnd) (fun y hy f p hp => Or.inr ?_) (fun _ h => by simp at h) (fun _ h => by simp at h) x (by
    simpa using (hτ.inv.ord x).2 (hτ.all x))
  obtain ⟨l₁, l₂, hl⟩ := List.append_of_mem hy
  refine ⟨l₁, l₂, hl, ?_⟩
  have hplt := ((hτ.good y).g7 f p hp).2.2
  have hpm : p ∈ τ.order.reverse := by simpa using (hτ.inv.ord p).2 (hτ.all p)
  rw [hl] at hpm hsorted
  rcases List.mem_append.1 hpm with h₁ | h₁
  · exact h₁
  · exfalso
    obtain ⟨_, _, h₂⟩ := List.pairwise_append.1 hsorted
    rcases List.mem_cons.1 h₁ with h₃ | h₃
    · rw [h₃] at hplt
      exact lt_irrefl _ hplt
    · have := (List.pairwise_cons.1 (List.pairwise_append.1 hsorted).2.1).1 p h₃
      omega

omit [Fintype V] in
/-- A label is the top of a blob containing the vertex, below it. -/
theorem Done.top_label (hτ : Done adj τ r) (hinc : IsIncidence adj) : ∀ (d : ℕ) (x : V), τ.disc x = d → IsTop τ (labels τ x) ∧ x ∈ sub τ (labels τ x) := by
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
    intro x hd
    have hself : IsTop τ x → IsTop τ x ∧ x ∈ sub τ x := fun hx => ⟨hx, hτ.self_mem x⟩
    have heq := hτ.labels_eq x
    cases hq : τ.par x with
    | none =>
      rw [hq] at heq
      rw [show labels τ x = x from heq]
      exact hself fun e p hp => by simp [hq] at hp
    | some a =>
      obtain ⟨f, p⟩ := a
      rw [hq] at heq
      by_cases hlt : τ.disc p < τ.low x
      · rw [show labels τ x = x by simpa [hlt] using heq]
        refine hself fun e p' hp => ?_
        rw [hq] at hp
        rw [show p' = p from (congrArg Prod.snd (Option.some.inj hp)).symm]
        exact hlt
      · rw [show labels τ x = labels τ p by simpa [hlt] using heq]
        have hlt' := ((hτ.good x).g7 f p hq).2.2
        obtain ⟨h₁, h₂⟩ := ih (τ.disc p) (hd ▸ hlt') p rfl
        exact ⟨h₁, hτ.child_mem hinc hq h₂⟩

omit [Fintype V] in
/-- A top above the vertex is at or above its label. -/
theorem Done.disc_le_label (hτ : Done adj τ r) {w : V} (hw : IsTop τ w) : ∀ (d : ℕ) (a : V), τ.disc a = d → a ∈ sub τ w → τ.disc w ≤ τ.disc (labels τ a) := by
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
    intro a hd ha
    have hle := (mem_filter.1 ha).2.1
    have heq := hτ.labels_eq a
    cases hq : τ.par a with
    | none =>
      rw [hq] at heq
      rw [show labels τ a = a from heq]
      exact hle
    | some q =>
      obtain ⟨f, p⟩ := q
      rw [hq] at heq
      by_cases hlt : τ.disc p < τ.low a
      · rw [show labels τ a = a by simpa [hlt] using heq]
        exact hle
      · rw [show labels τ a = labels τ p by simpa [hlt] using heq]
        have hne : a ≠ w := fun e => hlt (e ▸ hw f p (e ▸ hq))
        obtain ⟨f', p', h₁, _, h₃, h₄⟩ := (hτ.good w).g5 a ha hne
        rw [hq] at h₁
        obtain rfl : p = p' := congrArg Prod.snd (Option.some.inj h₁)
        exact ih (τ.disc p) (hd ▸ h₄) p rfl h₃

omit [Fintype V] in
/-- An arc that is not a bridge stays in the vertices below a top. -/
theorem Done.mem_of_not_bridge (hτ : Done adj τ r) (h : Lists G adj) {w a b : V} {f : E} (hw : IsTop τ w) (hf : ¬ G.underlying.IsBridge f) (hq : (f, b) ∈ adj a) (ha : a ∈ sub τ w) : b ∈ sub τ w := by
  rcases (hτ.good w).g2 a ha (f, b) hq with h₁ | ⟨e, p, h₁, _⟩
  · exact h₁
  · by_contra hb
    have hc := h.crosses (S := (sub τ w : Set V)) hq ha hb
    have hfe := (hτ.crosses_iff h h₁ (hw e p h₁) f).1 hc
    exact hf ((G.isBridge_iff f).2 ⟨_, fun g => (hτ.crosses_iff h h₁ (hw e p h₁) g).trans (by rw [hfe])⟩)

omit [Fintype V] in
/-- The two ends of an arc that is not a bridge have the same label. -/
theorem Done.label_eq_of_not_bridge (hτ : Done adj τ r) (h : Lists G adj) {a b : V} {f : E} (hf : ¬ G.underlying.IsBridge f) (hq : (f, b) ∈ adj a) : labels τ a = labels τ b := by
  have key : ∀ {a b : V}, (f, b) ∈ adj a → τ.disc (labels τ a) ≤ τ.disc (labels τ b) := fun {a b} hab => by
    obtain ⟨h₁, h₂⟩ := hτ.top_label h.isIncidence _ a rfl
    exact hτ.disc_le_label h₁ _ b rfl (hτ.mem_of_not_bridge h h₁ hf hab h₂)
  exact hτ.inj _ _ (le_antisymm (key hq) (key (h.isIncidence.symm a f b hq)))

omit [Fintype V] in
/-- A vertex and its label are in one blob. -/
theorem Done.walks_label (hτ : Done adj τ r) (h : Lists G adj) : ∀ (d : ℕ) (x : V), τ.disc x = d → G.Walks {e | ¬ G.underlying.IsBridge e} x (labels τ x) := by
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
    intro x hd
    have heq := hτ.labels_eq x
    cases hq : τ.par x with
    | none =>
      rw [hq] at heq
      rw [show labels τ x = x from heq]
      exact .refl
    | some a =>
      obtain ⟨f, p⟩ := a
      rw [hq] at heq
      by_cases hlt : τ.disc p < τ.low x
      · rw [show labels τ x = x by simpa [hlt] using heq]
        exact .refl
      · rw [show labels τ x = labels τ p by simpa [hlt] using heq]
        obtain ⟨_, hfp, hplt⟩ := (hτ.good x).g7 f p hq
        have hnb : ¬ G.underlying.IsBridge f := by
          intro hb
          obtain ⟨w, p', hw, hw'⟩ := hτ.of_isBridge h hb
          obtain ⟨_, hfp', hp'⟩ := (hτ.good w).g7 f p' hw
          have hinc := h.isIncidence
          rcases h.ends (hinc.symm x f p hfp) hfp' with e₁ | e₁
          · rcases h.ends hfp hfp' with e₂ | e₂
            · rw [e₁, ← e₂] at hplt
              exact lt_irrefl _ hplt
            · rw [e₁, e₂] at hplt
              exact absurd hp' (not_lt.2 hplt.le)
          · subst e₁
            rw [hq] at hw
            have := congrArg Prod.snd (Option.some.inj hw)
            exact hlt (by rw [show p = p' from this]; exact hw')
        have hadj : G.AdjOn {e | ¬ G.underlying.IsBridge e} x p := by
          refine ⟨f, hnb, ?_⟩
          rcases (h x f p).1 hfp with h₁ | ⟨h₁, h₂⟩
          · exact Or.inl h₁
          · exact Or.inr ⟨h₂, h₁⟩
        exact Relation.ReflTransGen.head hadj (ih (τ.disc p) (hd ▸ hplt) p rfl)

/-- **The labels are the blobs**: two vertices have the same label exactly when they are joined without a bridge. -/
theorem labels_eq_iff (hG : G.IsConnected) (h : Lists G adj) (r u v : V) :
    labels (run adj r) u = labels (run adj r) v ↔ G.blobSetoid.r u v := by
  have hτ := done_run hG h r
  constructor
  · intro he
    have h₁ := hτ.walks_label h _ u rfl
    have h₂ := hτ.walks_label h _ v rfl
    rw [← he] at h₂
    exact G.walks_trans h₁ (G.walks_symm h₂)
  · intro hw
    change G.Walks _ u v at hw
    induction hw with
    | refl => rfl
    | @tail a b _ hstep ih =>
      obtain ⟨f, hf, hab⟩ := hstep
      have hq : (f, b) ∈ adj a := by
        rcases hab with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
        · exact (h a f b).2 (Or.inl ⟨h₁, h₂⟩)
        · exact (h a f b).2 (Or.inr ⟨h₂, h₁⟩)
      exact ih.trans (hτ.label_eq_of_not_bridge h hf hq)

/-- The pass for the labels takes one step for each vertex. -/
theorem length_order (hG : G.IsConnected) (h : Lists G adj) (r : V) : (run adj r).order.length = Fintype.card V := by
  have hτ := done_run hG h r
  have hnd : (run adj r).order.Nodup := hτ.inv.sorted.imp fun {a b} hab e => by
    rw [e] at hab
    exact lt_irrefl _ hab
  rw [← List.toFinset_card_of_nodup hnd, ← card_univ]
  congr 1
  exact eq_univ_of_forall fun x => List.mem_toFinset.2 ((hτ.inv.ord x).2 (hτ.all x))

end Labels

/-! ### The tree of blobs -/

section TreeOfBlobs

variable {X : Type*} [Fintype X] [DecidableEq X]

/-- `w` is below a bridge: it is an arc to its parent with `disc p < low w`. -/
def IsCut (τ : St V E) (w : V) : Prop := ∃ e p, τ.par w = some (e, p) ∧ τ.disc p < τ.low w

/-- The taxa at or below `w`, which is an interval of discovery times: two numbers. -/
def side (N : RootedNetwork V E X) (τ : St V E) (w : V) : Finset X := univ.filter fun x => N.leaf x ∈ sub τ w

omit [Fintype X] [DecidableEq X] in
/-- **The cut splits, from the search**: each is the taxa at or below some `w` below a bridge, or the rest. -/
theorem hasCutSplit_iff {N : RootedNetwork V E X} (hG : N.graph.IsConnected) (h : Lists N.graph adj) (r : V) (A : Set X) :
    N.HasCutSplit A ↔ ∃ w, IsCut (run adj r) w ∧ (A = N.leaf ⁻¹' (sub (run adj r) w : Set V) ∨ A = (N.leaf ⁻¹' (sub (run adj r) w : Set V))ᶜ) := by
  have hτ := done_run hG h r
  constructor
  · rintro ⟨e, S, hS, rfl⟩
    obtain ⟨w, p, hw, hlt⟩ := hτ.of_isBridge h ((N.graph.isBridge_iff e).2 ⟨S, hS⟩)
    refine ⟨w, ⟨e, p, hw, hlt⟩, ?_⟩
    rcases N.graph.singleton_cuts_eq_or_eq_compl hG e hS (hτ.crosses_iff h hw hlt) with h₁ | h₁
    · exact Or.inl (by rw [h₁])
    · exact Or.inr (by rw [h₁]; rfl)
  · rintro ⟨w, ⟨e, p, hw, hlt⟩, rfl | rfl⟩
    · exact ⟨e, _, hτ.crosses_iff h hw hlt, rfl⟩
    · refine ⟨e, (sub (run adj r) w : Set V)ᶜ, fun f => ?_, rfl⟩
      rw [← hτ.crosses_iff h hw hlt f]
      simp only [DirectedMultigraph.Crosses, Set.mem_compl_iff, not_not]
      tauto

/-- **The tree of blobs, from the search**: a side of its splits is a proper nonempty set of taxa at or below some `w` below a bridge, or the rest. There is one such `w` for each bridge, so at most `|V|` splits, each given by two numbers: the sides are not written out, which would be quadratic. -/
theorem mem_treeOfBlobs_iff {N : RootedNetwork V E X} (hG : N.graph.IsConnected) (h : Lists N.graph adj) (r : V) (A : Finset X) :
    A ∈ treeOfBlobs N ↔ A.Nonempty ∧ Aᶜ.Nonempty ∧ ∃ w, IsCut (run adj r) w ∧ (A = side N (run adj r) w ∨ A = (side N (run adj r) w)ᶜ) := by
  simp only [treeOfBlobs, mem_filter, mem_univ, true_and]
  refine and_congr_right fun _ => and_congr_right fun _ => ?_
  rw [hasCutSplit_iff hG h r]
  refine exists_congr fun w => and_congr_right fun _ => or_congr ?_ ?_
  · rw [← coe_inj (s₁ := A)]
    simp only [side, coe_filter, mem_univ, true_and]
    rfl
  · rw [← coe_inj (s₁ := A)]
    simp only [side, coe_compl, coe_filter, mem_univ, true_and]
    rfl

end TreeOfBlobs

end Phylogenetics.BridgeDFS
