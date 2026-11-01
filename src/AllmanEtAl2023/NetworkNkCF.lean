module

public import AllmanEtAl2023.NetworkNkGraph
public import AllmanEtAl2023.KernelBounds

/-!
# Allman, Baños, Mitchell, Rhodes 2023: the probability `α` of the proof of Proposition 1

"With high probability the `a`, `b` lineages will be on different edges of the network when they reach a height of `1 + (k + 1)ε` above the taxa. This event is the union of `k` disjoint events, in which the lineages follow the
same path without coalescing to height `1 + ℓε` for any `ℓ ∈ {1, 2, …, k}` at which point they diverge on different paths. The probability of this for a specific `ℓ` is `(p/2)^ℓ`, where `p = exp (-ε)` is the probability two
lineages do not coalesce on an edge of length `ε`. Thus the probability of the full event is `α = ∑_{ℓ=1}^k (p/2)^ℓ`."

Here the process goes up `𝒩(k)⁺` one node at a time, in the order of the rank `rk`: the taxa (the stage `stgT`), the cherry (the stage `stg k 0`), and then the nodes of the inverted subtree
by their heap numbers (`stg k n` has those up to `n`). This order goes up the levels of the subtree, and then up the path along its 'leaves'. A function of the forests at the tops of the arcs is
compared along it by `KernelBounds.stageMass_eq_insert`.

* `DivAt a b n`: the lineages are on different arcs at the top of the stage `n`. For `n = 2 ^ k - 1` it is the paper's event at height `1 + (k + 1)ε`.
* `SplitAt a b m`: the lineages take the two parents of the node `m`. `DivLevel a b ℓ n`: they do so at a node of level `ℓ`, the event of the paper for `ℓ`.
* `PhiL`: the probability of `DivLevel ℓ` given the forests of a stage, `(p/2)^(ℓ-1-j) / 2` for two lineages together on an arc above level `j`, apart. `phiL_cherry` is the stem, and `phiL_step` one node of the subtree.
* `stageMass_divLevel`: `DivLevel ℓ` has probability `(p/2)^ℓ` (`a:claim:prop1-level`).
* `divAt_iff_exists_splitAt`, `eq_of_splitAt_of_splitAt`: the event is the union of the `DivLevel ℓ`, which are disjoint.
* `stageMass_divAt`: it has probability `α` (`a:claim:prop1-alpha`).
-/

@[expose] public noncomputable section

open Phylogenetics Phylogenetics.RootedNetwork Phylogenetics.NMSC Finset AllmanEtAl2023.KernelBounds
open scoped Classical

namespace AllmanEtAl2023.NetworkNk

variable {X : Type*} {k : ℕ}

/-! ### The ranks of the ends of an arc, and the stages -/

/-- The rank of the source of an arc. -/
def srcRk : Edge k → ℕ
  | .rootTaxon => 2 ^ (k + 1) + 1
  | .rootTop => 2 ^ (k + 1) + 1
  | .step t => 2 ^ k + t.1 + 2
  | .bottomTaxon => 2 ^ k + 1
  | .tree m => m.1 + 3
  | .stem => 2
  | .cherryLeft => 1
  | .cherryRight => 1

/-- The rank of the target of an arc. -/
def tgtRk : Edge k → ℕ
  | .rootTaxon => 0
  | .rootTop => 2 ^ (k + 1)
  | .step t => 2 ^ k + t.1 + 1
  | .bottomTaxon => 0
  | .tree m => (m.1 + 2) / 2 + 1
  | .stem => 1
  | .cherryLeft => 0
  | .cherryRight => 0

theorem rk_source {a b c d : X} (e : Edge k) : rk ((networkNk k a b c d).graph.source e) = srcRk e := by
  have := two_le_two_pow_succ k
  cases e with
  | rootTaxon => rfl
  | rootTop => rfl
  | step t => rw [source_step, rk_heapNode, srcRk]
  | bottomTaxon => rw [source_bottomTaxon, rk_heapNode, srcRk]
  | tree m => rw [source_tree, rk_heapNode, srcRk]
  | stem => rw [source_stem, rk_heapNode, srcRk]
  | cherryLeft => rfl
  | cherryRight => rfl

theorem rk_target {a b c d : X} (e : Edge k) : rk ((networkNk k a b c d).graph.target e) = tgtRk e := by
  have := two_le_two_pow_succ k
  cases e with
  | rootTaxon => rfl
  | rootTop =>
    rw [target_rootTop, rk_heapNode, tgtRk]
    omega
  | step t => rw [target_step, rk_heapNode, tgtRk]
  | bottomTaxon => rfl
  | tree m => rw [target_tree, rk_heapNode, tgtRk]
  | stem => rfl
  | cherryLeft => rfl
  | cherryRight => rfl

/-- The arc `f` leaves the stage `n`: the nodes of rank at most `n + 1` have been processed, which are the taxa, the cherry and the
heap numbers at most `n`. -/
def Fr (n : ℕ) (f : Edge k) : Prop := tgtRk f ≤ n + 1 ∧ n + 1 < srcRk f

theorem fr_tree {n : ℕ} {m : Fin (2 ^ (k + 1) - 2)} : Fr n (.tree m) ↔ (m.1 + 2) / 2 ≤ n ∧ n < m.1 + 2 := by
  simp only [Fr, tgtRk, srcRk]
  omega

variable [Fintype X]

/-- The nodes processed by the stage `n`. -/
def stg (k n : ℕ) : Finset (Vertex k X) := univ.filter fun v => rk v ≤ n + 1

/-- The nodes of the stage before the cherry: the taxa. -/
def stgT (k : ℕ) : Finset (Vertex k X) := univ.filter fun v => rk v = 0

omit [Fintype X] in
theorem rk_eq_zero_iff {v : Vertex k X} : rk v = 0 ↔ ∃ x, v = .taxon x := by
  cases v with
  | root => simp [rk]
  | cherry => simp [rk]
  | heap n => simp [rk]
  | taxon x => simp [rk]

@[simp] theorem mem_stg {n : ℕ} {v : Vertex k X} : v ∈ stg k n ↔ rk v ≤ n + 1 := by
  simp [stg]

@[simp] theorem mem_stgT {v : Vertex k X} : v ∈ stgT k ↔ rk v = 0 := by
  simp [stgT]

variable {a b c d : X}

theorem downClosed_stg (n : ℕ) : DownClosed (networkNk k a b c d) (stg k n) := fun e he => by
  rw [mem_stg] at he ⊢
  have := rk_target_lt_rk_source (a := a) (b := b) (c := c) (d := d) e
  omega

theorem downClosed_stgT : DownClosed (networkNk k a b c d) (stgT k) := fun e he => by
  rw [mem_stgT] at he ⊢
  have := rk_target_lt_rk_source (a := a) (b := b) (c := c) (d := d) e
  omega

theorem root_notMem_stg {n : ℕ} (hn : n + 1 < 2 ^ (k + 1) + 1) : (.root : Vertex k X) ∉ stg (X := X) k n := by
  simp only [mem_stg, rk]
  omega

theorem root_notMem_stgT : (.root : Vertex k X) ∉ stgT (X := X) k := by
  simp [rk]

theorem insert_heapNode_stg {n : ℕ} (h : n + 1 < 2 ^ (k + 1)) :
    (insert (heapNode (n + 1) (by omega) h : Vertex k X) (stg k n) : Finset (Vertex k X)) = stg k (n + 1) := by
  ext v
  simp only [mem_insert, mem_stg]
  cases v with
  | root =>
    simp only [root_ne_heapNode, false_or, rk]
    omega
  | cherry =>
    simp only [cherry_ne_heapNode, false_or, rk]
    omega
  | heap i =>
    simp only [heapNode, Vertex.heap.injEq, Fin.ext_iff, rk]
    omega
  | taxon x =>
    simp [rk]

theorem insert_cherry_stgT : insert .cherry (stgT k) = stg (X := X) k 0 := by
  ext v
  simp only [mem_insert, mem_stgT, mem_stg]
  cases v with
  | root =>
    have := two_le_two_pow_succ k
    simp [rk]
  | cherry => simp [rk]
  | heap i => simp [rk]
  | taxon x => simp [rk]

theorem stg_top : stg (X := X) k (2 ^ (k + 1) - 1) = univ.erase .root := by
  have h2 := two_le_two_pow_succ k
  ext v
  simp only [mem_stg, mem_erase, mem_univ, and_true]
  cases v with
  | root =>
    simp only [rk, ne_eq, not_true_eq_false, iff_false]
    omega
  | cherry =>
    simp only [rk, ne_eq, reduceCtorEq, not_false_eq_true, iff_true]
    omega
  | heap i =>
    have := i.2
    simp only [rk, ne_eq, reduceCtorEq, not_false_eq_true, iff_true]
    omega
  | taxon x => simp [rk]

/-! ### The states -/

section States

variable [DecidableEq X]

/-- The lineages of `a` and `b` are on different arcs of the inverted subtree, at the top of the stage `n`. This is the event of the paper, the "`a`, `b` lineages being on different
edges", at the height `1 + (k + 1) ε` for `n = 2 ^ k - 1`. -/
def DivAt (a b : X) (n : ℕ) (top : Edge k → Finset (Finset X)) : Prop :=
  ∃ m₁ m₂ : Fin (2 ^ (k + 1) - 2), m₁ ≠ m₂ ∧ Fr n (.tree m₁) ∧ Fr n (.tree m₂) ∧
    a ∈ lineages (top (.tree m₁)) ∧ b ∈ lineages (top (.tree m₂))

/-- The lineages of `a` and `b` are together on the arc `f`, at the top of the stage `n`, not coalesced. -/
def SameAt (a b : X) (n : ℕ) (top : Edge k → Finset (Finset X)) (f : Edge k) : Prop :=
  Fr n f ∧ a ∈ lineages (top f) ∧ b ∈ lineages (top f) ∧ ({a, b} : Finset X) ∉ top f

/-- The lineages of `a` and `b` take the two parents of the node `m` of the inverted subtree. -/
def SplitAt (a b : X) (m : ℕ) (h₁ : 1 ≤ m) (h₂ : m < 2 ^ k) (top : Edge k → Finset (Finset X)) : Prop :=
  (a ∈ lineages (top (leftArc m h₁ h₂)) ∧ b ∈ lineages (top (rightArc m h₁ h₂))) ∨
    (a ∈ lineages (top (rightArc m h₁ h₂)) ∧ b ∈ lineages (top (leftArc m h₁ h₂)))

/-- The lineages of `a` and `b` "diverge on different paths" at height `1 + ℓε`, by the stage `n`: at a node of the inverted subtree of level `ℓ`, the root of it having level 1. -/
def DivLevel (a b : X) (ℓ n : ℕ) (top : Edge k → Finset (Finset X)) : Prop :=
  ∃ (m : ℕ) (h₁ : 1 ≤ m) (h₂ : m < 2 ^ k), m ≤ n ∧ Nat.log 2 m + 1 = ℓ ∧ SplitAt a b m h₁ h₂ top

/-- The probability that two lineages together at a node of level `j + 1`, not coalesced, diverge at level `ℓ`. -/
def lvl (p : ℝ) (j ℓ : ℕ) : ℝ := if j < ℓ then (p / 2) ^ (ℓ - 1 - j) / 2 else 0

theorem lvl_recursion (p : ℝ) (j ℓ : ℕ) :
    lvl p j ℓ = (if j + 1 = ℓ then 1 / 2 else 0) + p / 2 * lvl p (j + 1) ℓ := by
  unfold lvl
  rcases lt_trichotomy (j + 1) ℓ with h | h | h
  · rw [ite_eq_left (by omega : j < ℓ), ite_eq_left h, ite_eq_right (by omega : ¬ j + 1 = ℓ)]
    obtain ⟨i, hi⟩ : ∃ i, ℓ - 1 - (j + 1) = i := ⟨_, rfl⟩
    rw [hi, show ℓ - 1 - j = i + 1 by omega, pow_succ]
    ring
  · subst h
    simp
  · rw [ite_eq_right (by omega : ¬ j < ℓ), ite_eq_right (by omega : ¬ j + 1 < ℓ), ite_eq_right (by omega : ¬ j + 1 = ℓ)]
    ring

/-- The value of the lineages of `a` and `b` being together on an arc, apart, for the event at level `ℓ`. -/
def levelVal (p : ℝ) (ℓ : ℕ) : Edge k → ℝ
  | .stem => lvl p 0 ℓ
  | .tree m => lvl p (Nat.log 2 (m.1 + 2)) ℓ
  | _ => 0

/-- The potential up to the 'leaves' of the inverted subtree: the probability of the event at level `ℓ`, given the forests of a stage. -/
def PhiL (a b : X) (p : ℝ) (ℓ n : ℕ) (top : Edge k → Finset (Finset X)) : ℝ :=
  if DivLevel a b ℓ n top then 1 else ∑ f, if SameAt a b n top f then levelVal p ℓ f else 0

omit [Fintype X] in
theorem phiL_of_level {a b : X} {p : ℝ} {ℓ n : ℕ} {top : Edge k → Finset (Finset X)} (h : DivLevel a b ℓ n top) :
    PhiL a b p ℓ n top = 1 := ite_eq_left h

omit [Fintype X] in
theorem phiL_of_same {a b : X} {p : ℝ} {ℓ n : ℕ} {top : Edge k → Finset (Finset X)} {g : Edge k} (h : ¬ DivLevel a b ℓ n top)
    (hg : SameAt a b n top g) (hs : ∀ f, SameAt a b n top f → f = g) : PhiL a b p ℓ n top = levelVal p ℓ g := by
  unfold PhiL
  rw [ite_eq_right h, sum_eq_single g]
  · rw [ite_eq_left hg]
  · exact fun f _ hf => ite_eq_right fun hS => hf (hs f hS)
  · exact fun h' => absurd (mem_univ _) h'

omit [Fintype X] in
theorem phiL_of_none {a b : X} {p : ℝ} {ℓ n : ℕ} {top : Edge k → Finset (Finset X)} (h : ¬ DivLevel a b ℓ n top)
    (hs : ∀ f, ¬ SameAt a b n top f) : PhiL a b p ℓ n top = 0 := by
  unfold PhiL
  rw [ite_eq_right h]
  exact sum_eq_zero fun f _ => ite_eq_right (hs f)

end States

/-! ### Histories of nonzero weight -/

section Frontier

variable [DecidableEq X]

/-- The lineages of all the taxa, at the leaves of `𝒩(k)⁺`. -/
abbrev injNk (k : ℕ) (a b c d : X) : Vertex k X → Finset (Finset X) := taxaInj (networkNk k a b c d) univ

theorem validInj_injNk : ValidInj (injNk k a b c d) := validInj_taxaInj univ

variable {n : ℕ} {bot top : Edge k → Finset (Finset X)}

/-- Each lineage is at the top of an arc that leaves a stage. -/
theorem exists_fr (hF : Frontier (networkNk k a b c d) (injNk k a b c d) (stg k n) bot top) (x : X) :
    ∃ f : Edge k, Fr n f ∧ x ∈ lineages (top f) := by
  obtain ⟨e, he₁, he₂, hx⟩ := (hF.mem x).2 ⟨.taxon x, by simp [rk], mem_lineages_taxaInj.2 ⟨mem_univ x, rfl⟩⟩
  rw [mem_stg, rk_target] at he₁
  rw [mem_stg, rk_source] at he₂
  exact ⟨e, ⟨he₁, by omega⟩, hx⟩

/-- A lineage is at the top of one arc leaving a stage. -/
theorem eq_of_fr (hF : Frontier (networkNk k a b c d) (injNk k a b c d) (stg k n) bot top) {f g : Edge k} (hf : Fr n f)
    (hg : Fr n g) {x : X} (hxf : x ∈ lineages (top f)) (hxg : x ∈ lineages (top g)) : f = g := by
  by_contra hne
  refine disjoint_left.1 (hF.disj f g ?_ ?_ ?_ ?_ hne) hxf hxg
  · rw [mem_stg, rk_target]
    exact hf.1
  · rw [mem_stg, rk_source]
    have := hf.2
    omega
  · rw [mem_stg, rk_target]
    exact hg.1
  · rw [mem_stg, rk_source]
    have := hg.2
    omega

/-- A lineage at the top of an arc is of a taxon below the arc. -/
theorem reaches_of_mem (hF : Frontier (networkNk k a b c d) (injNk k a b c d) (stg k n) bot top) {f : Edge k}
    (hf : tgtRk f ≤ n + 1) {x : X} (hx : x ∈ lineages (top f)) :
    (networkNk k a b c d).graph.Reaches ((networkNk k a b c d).graph.target f) (.taxon x) := by
  obtain ⟨u, hu, hxu⟩ := hF.below f (by rw [mem_stg, rk_target]; exact hf) x hx
  rw [(mem_lineages_taxaInj.1 hxu).2.symm] at hu
  exact hu

/-- No taxon is at a node of the inverted subtree. -/
theorem notMem_lineages_injNk_heap {i : Fin (2 ^ (k + 1) - 1)} {x : X} : x ∉ lineages (injNk k a b c d (.heap i)) := by
  intro h
  have := (mem_lineages_taxaInj.1 h).2
  simp [networkNk] at this

theorem notMem_lineages_injNk_cherry {x : X} : x ∉ lineages (injNk k a b c d .cherry) := by
  intro h
  have := (mem_lineages_taxaInj.1 h).2
  simp [networkNk] at this

/-- A lineage arriving at a node of the inverted subtree comes along an arc from below. -/
theorem exists_out_of_mem_arriving {m : ℕ} {h₁ : 1 ≤ m} {h₂ : m < 2 ^ (k + 1)} {x : X}
    (hx : x ∈ lineages (arriving (networkNk k a b c d) (injNk k a b c d) top (heapNode m h₁ h₂))) :
    ∃ g : Edge k, (networkNk k a b c d).graph.source g = heapNode m h₁ h₂ ∧ x ∈ lineages (top g) := by
  rcases (mem_lineages_arriving _ top _ x).1 hx with h | h
  · exact absurd h notMem_lineages_injNk_heap
  · exact h

/-- At a stage below the 'leaves' of the inverted subtree, the lineages of `a` and `b` are on its arcs. -/
theorem exists_tree_of_stage (hF : Frontier (networkNk k a b c d) (injNk k a b c d) (stg k n) bot top) (hn₁ : 1 ≤ n)
    (hn₂ : n < 2 ^ k) {x : X} (hxc : x ≠ c) (hxd : x ≠ d) :
    ∃ m : Fin (2 ^ (k + 1) - 2), Fr n (.tree m) ∧ x ∈ lineages (top (.tree m)) := by
  obtain ⟨f, hf, hx⟩ := exists_fr hF x
  have hr := reaches_of_mem hF hf.1 hx
  have h2 := two_pow_succ_eq k
  obtain ⟨hf₁, hf₂⟩ := hf
  cases f with
  | rootTaxon =>
    have := eq_of_taxon_reaches hr
    exact absurd (Vertex.taxon.inj this) hxd
  | rootTop =>
    simp only [tgtRk] at hf₁
    omega
  | step t =>
    simp only [tgtRk] at hf₁
    omega
  | bottomTaxon =>
    have := eq_of_taxon_reaches hr
    exact absurd (Vertex.taxon.inj this) hxc
  | tree m => exact ⟨m, ⟨hf₁, hf₂⟩, hx⟩
  | stem =>
    simp only [srcRk] at hf₂
    omega
  | cherryLeft =>
    simp only [srcRk] at hf₂
    omega
  | cherryRight =>
    simp only [srcRk] at hf₂
    omega

omit [Fintype X] [DecidableEq X] in
/-- A node of rank `n + 2` is the node with heap number `n + 1`. -/
theorem eq_heapNode_of_rk {n : ℕ} (hn : n + 1 < 2 ^ (k + 1)) {v : Vertex k X} (h : rk v = n + 2) :
    v = heapNode (n + 1) (by omega) hn := by
  cases v with
  | root =>
    simp only [rk] at h
    omega
  | cherry =>
    simp only [rk] at h
    omega
  | heap i =>
    simp only [rk] at h
    simp only [heapNode, Vertex.heap.injEq, Fin.ext_iff]
    omega
  | taxon x =>
    simp only [rk] at h
    omega

omit [Fintype X] [DecidableEq X] in
/-- An arc that leaves the stage `n`, other than from the next node, leaves the stage `n + 1`. -/
theorem fr_succ {n : ℕ} (hn : n + 1 < 2 ^ (k + 1)) {f : Edge k} (hf : Fr n f)
    (hs : (networkNk k a b c d).graph.source f ≠ heapNode (n + 1) (by omega) hn) : Fr (n + 1) f := by
  refine ⟨by have := hf.1; omega, ?_⟩
  have h1 := hf.2
  have h2 : srcRk f ≠ n + 2 := fun h => hs (eq_heapNode_of_rk hn ((rk_source f).trans h))
  omega

omit [Fintype X] [DecidableEq X] in
/-- An arc that leaves the stage `n` from the next node. -/
theorem fr_of_source_eq {n : ℕ} (hn : n + 1 < 2 ^ (k + 1)) {f : Edge k}
    (hs : (networkNk k a b c d).graph.source f = heapNode (n + 1) (by omega) hn) : Fr n f := by
  have h1 := rk_target_lt_rk_source (a := a) (b := b) (c := c) (d := d) f
  rw [rk_target, rk_source] at h1
  have h2 : srcRk f = n + 2 := by
    rw [← rk_source (a := a) (b := b) (c := c) (d := d), hs, rk_heapNode]
  exact ⟨by omega, by omega⟩

omit [Fintype X] [DecidableEq X] in
/-- The arcs processed by the stage `n` don't enter the next node. -/
theorem target_ne_of_tgtRk_le {n : ℕ} (hn : n + 1 < 2 ^ (k + 1)) {f : Edge k} (hf : tgtRk f ≤ n + 1) :
    (networkNk k a b c d).graph.target f ≠ heapNode (n + 1) (by omega) hn := fun h => by
  have := rk_target (a := a) (b := b) (c := c) (d := d) f
  rw [h, rk_heapNode] at this
  omega

omit [DecidableEq X] in
/-- What the next node needs of the stage `n`. -/
theorem heapNode_notMem_stg {n : ℕ} (hn : n + 1 < 2 ^ (k + 1)) :
    (heapNode (n + 1) (by omega) hn : Vertex k X) ∉ stg k n := by
  simp

omit [DecidableEq X] in
theorem target_mem_stg_of_source_eq {n : ℕ} (hn : n + 1 < 2 ^ (k + 1)) (e : Edge k)
    (he : (networkNk k a b c d).graph.source e = heapNode (n + 1) (by omega) hn) :
    (networkNk k a b c d).graph.target e ∈ stg k n := by
  have := rk_target_lt_rk_source (a := a) (b := b) (c := c) (d := d) e
  rw [he, rk_heapNode] at this
  rw [mem_stg]
  omega

/-- A node of the inverted subtree that isn't a 'leaf': the forest arriving there is the one at the top of the arc leaving it. -/
theorem arriving_inner {m : ℕ} (h₁ : 1 ≤ m) (h₂ : m < 2 ^ k) (h₃ : m < 2 ^ (k + 1)) (top : Edge k → Finset (Finset X)) :
    arriving (networkNk k a b c d) (injNk k a b c d) top (heapNode m h₁ h₃) = top (outTree m) := by
  unfold arriving
  have h4 : injNk k a b c d (heapNode m h₁ h₃) = ∅ := by
    refine eq_empty_of_forall_notMem fun A hA => ?_
    obtain ⟨x, hx, -⟩ := mem_image.1 hA
    have := (mem_filter.1 hx).2.2
    simp [networkNk] at this
  have h5 : (univ.filter fun e => (networkNk k a b c d).graph.source e = heapNode m h₁ h₃) = {outTree m} := by
    ext e
    simp only [mem_filter, mem_univ, true_and, mem_singleton]
    exact source_eq_inner_iff h₁ h₂ h₃ e
  rw [h4, h5, singleton_biUnion, empty_union]

omit [Fintype X] in
/-- The forest of two lineages `a`, `b`. -/
theorem left_mem_lineages_pair : a ∈ lineages ({{a}, {b}} : Finset (Finset X)) :=
  mem_lineages.2 ⟨{a}, by simp, by simp⟩

omit [Fintype X] in
theorem right_mem_lineages_pair : b ∈ lineages ({{a}, {b}} : Finset (Finset X)) :=
  mem_lineages.2 ⟨{b}, by simp, by simp⟩

omit [Fintype X] in
theorem pair_notMem_pair (hab : a ≠ b) : ({a, b} : Finset X) ∉ ({{a}, {b}} : Finset (Finset X)) := by
  simp only [mem_insert, mem_singleton, not_or]
  constructor
  · intro h
    have : b ∈ ({a} : Finset X) := h ▸ (by simp)
    exact hab (mem_singleton.1 this).symm
  · intro h
    have : a ∈ ({b} : Finset X) := h ▸ (by simp)
    exact hab (mem_singleton.1 this)

end Frontier

/-! ### The step at a node that isn't a 'leaf' -/

section StepInner

variable [DecidableEq X]

omit [Fintype X] [DecidableEq X] in
theorem isLow_target_outTree {m : ℕ} (h₃ : m < 2 ^ (k + 1)) :
    IsLow (k := k) a b ((networkNk k a b c d).graph.target (outTree m)) := by
  by_cases hm : 2 ≤ m
  · rw [outTree_of_two_le hm h₃]
    exact isLow_target_tree _
  · have : (outTree m : Edge k) = .stem := by
      simp only [outTree]
      rw [dite_eq_right (by omega)]
    rw [this]
    exact trivial

theorem levelVal_outTree {p : ℝ} {ℓ m : ℕ} (h₁ : 1 ≤ m) (h₃ : m < 2 ^ (k + 1)) :
    levelVal p ℓ (outTree m : Edge k) = lvl p (Nat.log 2 m) ℓ := by
  by_cases hm : 2 ≤ m
  · rw [outTree_of_two_le hm h₃]
    simp only [levelVal]
    congr 2
    omega
  · obtain rfl : m = 1 := by omega
    rw [outTree_one]
    simp [levelVal]

theorem log_left {m : ℕ} (h₁ : 1 ≤ m) : Nat.log 2 (2 * m - 2 + 2) = Nat.log 2 m + 1 := by
  rw [show 2 * m - 2 + 2 = m * 2 by omega]
  exact Nat.log_mul_base (by norm_num) (by omega)

theorem log_right {m : ℕ} (h₁ : 1 ≤ m) : Nat.log 2 (2 * m - 1 + 2) = Nat.log 2 m + 1 := by
  rw [Nat.log_of_one_lt_of_le (by norm_num) (by omega), show (2 * m - 1 + 2) / 2 = m by omega]

/-- **The recursion of the values**: at a node of the inverted subtree that isn't a 'leaf', the lineages of `a`, `b` diverge with probability `1/2`, or stay together, apart, on one of the two arcs. -/
theorem levelVal_recursion {ε M : ℝ} {ℓ m : ℕ} (hℓ : ℓ ≤ k) (h₁ : 1 ≤ m) (h₂ : m < 2 ^ k) (h₃ : m < 2 ^ (k + 1)) :
    levelVal (Real.exp (-ε)) ℓ (outTree m : Edge k) =
      1 / 4 * ((if Nat.log 2 m + 1 = ℓ then 1 else 0) + (if Nat.log 2 m + 1 = ℓ then 1 else 0)) +
      1 / 4 * (Real.exp (-(metricNk k ε M).length (leftArc m h₁ h₂)) * levelVal (Real.exp (-ε)) ℓ (leftArc m h₁ h₂) +
          (1 - Real.exp (-(metricNk k ε M).length (leftArc m h₁ h₂))) * 0) +
        1 / 4 * (Real.exp (-(metricNk k ε M).length (rightArc m h₁ h₂)) * levelVal (Real.exp (-ε)) ℓ (rightArc m h₁ h₂) +
          (1 - Real.exp (-(metricNk k ε M).length (rightArc m h₁ h₂))) * 0) := by
  set p := Real.exp (-ε) with hp
  rw [levelVal_outTree h₁ h₃]
  have hlen : ∀ m' : Fin (2 ^ (k + 1) - 2), Nat.log 2 (m'.1 + 2) = Nat.log 2 m + 1 →
      Real.exp (-(metricNk k ε M).length (.tree m')) * lvl p (Nat.log 2 m + 1) ℓ = p * lvl p (Nat.log 2 m + 1) ℓ := by
    intro m' hm'
    by_cases hj : Nat.log 2 m + 1 < ℓ
    · have hlt : m'.1 + 2 < 2 ^ k := Nat.lt_pow_of_log_lt (by norm_num) (by omega)
      simp only [metricNk]
      rw [ite_eq_left hlt]
    · simp [lvl, hj]
  have e₁ : levelVal p ℓ (leftArc m h₁ h₂) = lvl p (Nat.log 2 m + 1) ℓ := by
    simp only [leftArc, levelVal]
    rw [log_left h₁]
  have e₂ : levelVal p ℓ (rightArc m h₁ h₂) = lvl p (Nat.log 2 m + 1) ℓ := by
    simp only [rightArc, levelVal]
    rw [log_right h₁]
  have l₁ : Real.exp (-(metricNk k ε M).length (leftArc m h₁ h₂)) * lvl p (Nat.log 2 m + 1) ℓ = p * lvl p (Nat.log 2 m + 1) ℓ :=
    hlen ⟨2 * m - 2, by have := two_pow_succ_eq k; omega⟩ (log_left h₁)
  have l₂ : Real.exp (-(metricNk k ε M).length (rightArc m h₁ h₂)) * lvl p (Nat.log 2 m + 1) ℓ = p * lvl p (Nat.log 2 m + 1) ℓ :=
    hlen ⟨2 * m - 1, by have := two_pow_succ_eq k; omega⟩ (log_right h₁)
  rw [e₁, e₂, mul_zero, mul_zero, add_zero, add_zero, l₁, l₂, lvl_recursion]
  split_ifs <;> ring

/-- The index of the arc from the node `2 m` to the node `m`. -/
def leftIdx (m : ℕ) (h₁ : 1 ≤ m) (h₂ : m < 2 ^ k) : Fin (2 ^ (k + 1) - 2) :=
  ⟨2 * m - 2, by have := two_pow_succ_eq k; omega⟩

/-- The index of the arc from the node `2 m + 1` to the node `m`. -/
def rightIdx (m : ℕ) (h₁ : 1 ≤ m) (h₂ : m < 2 ^ k) : Fin (2 ^ (k + 1) - 2) :=
  ⟨2 * m - 1, by have := two_pow_succ_eq k; omega⟩

theorem leftIdx_ne_rightIdx (m : ℕ) (h₁ : 1 ≤ m) (h₂ : m < 2 ^ k) : leftIdx m h₁ h₂ ≠ rightIdx m h₁ h₂ := by
  simp only [leftIdx, rightIdx, ne_eq, Fin.mk.injEq]
  omega

theorem fr_leftIdx {n : ℕ} (h₁ : 1 ≤ n + 1) (h₂ : n + 1 < 2 ^ k) : Fr (n + 1) (.tree (leftIdx (n + 1) h₁ h₂)) := by
  rw [fr_tree]
  simp only [leftIdx]
  omega

theorem fr_rightIdx {n : ℕ} (h₁ : 1 ≤ n + 1) (h₂ : n + 1 < 2 ^ k) : Fr (n + 1) (.tree (rightIdx (n + 1) h₁ h₂)) := by
  rw [fr_tree]
  simp only [rightIdx]
  omega

omit [Fintype X] [DecidableEq X] in
theorem tgtRk_leftArc {m : ℕ} (h₁ : 1 ≤ m) (h₂ : m < 2 ^ k) : tgtRk (leftArc m h₁ h₂ : Edge k) = m + 1 := by
  simp only [leftArc, tgtRk]
  omega

omit [Fintype X] [DecidableEq X] in
theorem tgtRk_rightArc {m : ℕ} (h₁ : 1 ≤ m) (h₂ : m < 2 ^ k) : tgtRk (rightArc m h₁ h₂ : Edge k) = m + 1 := by
  simp only [rightArc, tgtRk]
  omega

variable (hd : ({a, b, c, d} : Finset X).card = 4) (hX : Fintype.card X = 4) {ε M : ℝ} (hε : 0 < ε) (hM : 0 < M)

include hd hX hε hM in
/-- **The step of the chain at a node of the inverted subtree that isn't a 'leaf'.** -/
theorem phiL_step {ℓ n : ℕ} (hℓ : ℓ ≤ k) (hn : n + 1 < 2 ^ k) (h₃ : n + 1 < 2 ^ (k + 1)) (bot top : Edge k → Finset (Finset X))
    (hw : ∏ u ∈ stg k n, vertexWeight (networkNk k a b c d) (metricNk k ε M) 0 (injNk k a b c d) u bot top ≠ 0) :
    PhiL a b (Real.exp (-ε)) ℓ n top *
        ((Fintype.card (Finset (Finset X)) : ℝ) ^ #(arcsInto (networkNk k a b c d) (heapNode (n + 1) (by omega) h₃))ᶜ) ^ 2 =
      vertexKernel (networkNk k a b c d) (metricNk k ε M) 0 (heapNode (n + 1) (by omega) h₃)
        (arriving (networkNk k a b c d) (injNk k a b c d) top (heapNode (n + 1) (by omega) h₃)) fun t =>
          PhiL a b (Real.exp (-ε)) ℓ (n + 1) (overwrite (arcsInto (networkNk k a b c d) (heapNode (n + 1) (by omega) h₃)) top t) := by
  obtain ⟨hab, hac, had, hbc, hbd, hcd⟩ := ne_of_card_four hd
  have hN := isPhylogenetic_networkNk (k := k) hd hX
  have hθ : (networkNk k a b c d).IsWeakMetric (metricNk k ε M) := (isMetric_metricNk hd hX hε hM).isWeakMetric
  have hρ : (0 : ℝ) ≤ 0 ∧ (0 : ℝ) ≤ 1 := ⟨le_rfl, zero_le_one⟩
  have hinj := validInj_injNk (k := k) (a := a) (b := b) (c := c) (d := d)
  have hD := downClosed_stg (k := k) (a := a) (b := b) (c := c) (d := d) n
  set v : Vertex k X := heapNode (n + 1) (by omega) h₃ with hv
  have hvD : v ∉ stg k n := heapNode_notMem_stg h₃
  have hvr : v ≠ (networkNk k a b c d).root := (root_ne_heapNode).symm
  have hch := target_mem_stg_of_source_eq (a := a) (b := b) (c := c) (d := d) h₃
  have hF := frontier_of_prod_ne_zero hN hinj hD hw
  have hout : ∀ g, (networkNk k a b c d).graph.source g = v ↔ g = outTree (n + 1) :=
    source_eq_inner_iff (by omega) hn h₃
  have hfrout : Fr n (outTree (n + 1) : Edge k) := fr_of_source_eq h₃ ((hout _).2 rfl)
  have harr : arriving (networkNk k a b c d) (injNk k a b c d) top v = top (outTree (n + 1)) :=
    arriving_inner (by omega) hn h₃ top
  have hL : (networkNk k a b c d).graph.target (leftArc (n + 1) (by omega) hn) = v :=
    (target_eq_inner_iff (by omega) hn _).2 (Or.inl rfl)
  have hR : (networkNk k a b c d).graph.target (rightArc (n + 1) (by omega) hn) = v :=
    (target_eq_inner_iff (by omega) hn _).2 (Or.inr rfl)
  -- an event at an earlier node stays, and the arcs of the earlier nodes don't change
  have hsplit_congr : ∀ {top' : Edge k → Finset (Finset X)}, (∀ f, (networkNk k a b c d).graph.target f ≠ v → top' f = top f) →
      ∀ {m : ℕ} (h₁ : 1 ≤ m) (h₂ : m < 2 ^ k), m ≤ n → (SplitAt a b m h₁ h₂ top' ↔ SplitAt a b m h₁ h₂ top) := by
    intro top' htop' m h₁ h₂ hm
    have h1 := htop' (leftArc m h₁ h₂) (target_ne_of_tgtRk_le h₃ (by rw [tgtRk_leftArc]; omega))
    have h2 := htop' (rightArc m h₁ h₂) (target_ne_of_tgtRk_le h₃ (by rw [tgtRk_rightArc]; omega))
    simp only [SplitAt, h1, h2]
  have hlevel_iff : ∀ {top' : Edge k → Finset (Finset X)}, (∀ f, (networkNk k a b c d).graph.target f ≠ v → top' f = top f) →
      ¬ DivLevel a b ℓ n top → (DivLevel a b ℓ (n + 1) top' ↔ Nat.log 2 (n + 1) + 1 = ℓ ∧ SplitAt a b (n + 1) (by omega) hn top') := by
    intro top' htop' hnot
    constructor
    · rintro ⟨m, h₁, h₂, hm, hlog, hs⟩
      rcases Nat.lt_or_ge m (n + 1) with hlt | hge
      · exact absurd ⟨m, h₁, h₂, by omega, hlog, (hsplit_congr htop' h₁ h₂ (by omega)).1 hs⟩ hnot
      · obtain rfl : m = n + 1 := by omega
        exact ⟨hlog, hs⟩
    · rintro ⟨hlog, hs⟩
      exact ⟨n + 1, by omega, hn, le_rfl, hlog, hs⟩
  by_cases hDiv : DivLevel a b ℓ n top
  · -- the event has happened
    rw [phiL_of_level hDiv]
    refine vertexKernel_overwrite_eq hN hθ hρ hinj hD hvD hvr hch hw fun bot' top' htop' _ _ _ => phiL_of_level ?_
    obtain ⟨m, h₁, h₂, hm, hlog, hs⟩ := hDiv
    exact ⟨m, h₁, h₂, by omega, hlog, (hsplit_congr htop' h₁ h₂ hm).2 hs⟩
  by_cases hS : ∃ f, SameAt a b n top f
  · obtain ⟨f, hSf⟩ := hS
    have hsameuniq : ∀ g, SameAt a b n top g → g = f := fun g hg => eq_of_fr hF hg.1 hSf.1 hg.2.1 hSf.2.1
    rw [phiL_of_same hDiv hSf hsameuniq]
    by_cases hfv : (networkNk k a b c d).graph.source f = v
    · -- the lineages are together at `v`
      have hfout := (hout f).1 hfv
      subst hfout
      have hlow : lineages (top (outTree (n + 1))) = {a, b} := by
        ext x
        simp only [mem_insert, mem_singleton]
        constructor
        · intro hx
          exact IsLow.of_reaches (reaches_of_mem hF hSf.1.1 hx) (isLow_target_outTree h₃)
        · rintro (rfl | rfl)
          · exact hSf.2.1
          · exact hSf.2.2.1
      have hpair := KernelBounds.eq_pair_of_lineages (hF.good_top _ (by
        rw [mem_stg, rk_target]
        exact hSf.1.1)) hab hlow hSf.2.2.2
      -- the other arcs that leave the next stage have neither lineage
      have hother : ∀ {g : Edge k}, Fr (n + 1) g → (networkNk k a b c d).graph.target g ≠ v → a ∉ lineages (top g) := by
        intro g hg htg hag
        have hgn : Fr n g := by
          refine ⟨?_, by have := hg.2; omega⟩
          have h1 := hg.1
          have h2 : tgtRk g ≠ n + 2 := fun h => htg (eq_heapNode_of_rk h₃ ((rk_target g).trans h))
          omega
        have hgf := eq_of_fr hF hgn hfrout hag hSf.2.1
        rw [hgf] at hg
        have := hg.2
        have h3 := fr_of_source_eq (a := a) (b := b) (c := c) (d := d) h₃ ((hout _).2 rfl)
        have h4 : srcRk (outTree (n + 1) : Edge k) = n + 2 := by
          rw [← rk_source (a := a) (b := b) (c := c) (d := d), (hout _).2 rfl, hv, rk_heapNode]
        omega
      have hsame_at : ∀ t : Edge k → Finset (Finset X), ∀ g,
          SameAt a b (n + 1) (overwrite (arcsInto (networkNk k a b c d) v) top t) g →
            g = leftArc (n + 1) (by omega) hn ∨ g = rightArc (n + 1) (by omega) hn := by
        intro t g hg
        by_cases htg : (networkNk k a b c d).graph.target g = v
        · exact (target_eq_inner_iff (by omega) hn g).1 htg
        · refine absurd ?_ (hother hg.1 htg)
          have := hg.2.1
          rwa [overwrite_of_notMem (fun h => htg (mem_arcsInto.1 h))] at this
      have hnosplit_left : ∀ t : Edge k → Finset (Finset X), lineages (t (rightArc (n + 1) (by omega) hn)) = ∅ →
          ¬ SplitAt a b (n + 1) (by omega) hn (overwrite (arcsInto (networkNk k a b c d) v) top t) := by
        intro t ht hs
        rw [SplitAt, overwrite_of_mem (mem_arcsInto.2 hL), overwrite_of_mem (mem_arcsInto.2 hR), ht] at hs
        simp at hs
      have hnosplit_right : ∀ t : Edge k → Finset (Finset X), lineages (t (leftArc (n + 1) (by omega) hn)) = ∅ →
          ¬ SplitAt a b (n + 1) (by omega) hn (overwrite (arcsInto (networkNk k a b c d) v) top t) := by
        intro t ht hs
        rw [SplitAt, overwrite_of_mem (mem_arcsInto.2 hL), overwrite_of_mem (mem_arcsInto.2 hR), ht] at hs
        simp at hs
      have htop_congr : ∀ t : Edge k → Finset (Finset X), ∀ f, (networkNk k a b c d).graph.target f ≠ v →
          overwrite (arcsInto (networkNk k a b c d) v) top t f = top f :=
        fun t f hf => overwrite_of_notMem (fun h => hf (mem_arcsInto.1 h)) _ _
      rw [harr, hpair, levelVal_recursion (M := M) hℓ (by omega) hn h₃]
      symm
      refine KernelBounds.kernel_two_arcs_eq (leftArc_ne_rightArc _ (by omega) hn) hL hR
        (target_eq_inner_iff (by omega) hn · |>.1) rfl rfl hab ?_ ?_ ?_ ?_ ?_ ?_
      · -- different arcs, one way
        intro t h1 h2
        have hs : SplitAt a b (n + 1) (by omega) hn (overwrite (arcsInto (networkNk k a b c d) v) top t) := Or.inl (by
          rw [overwrite_of_mem (mem_arcsInto.2 hL), overwrite_of_mem (mem_arcsInto.2 hR), h1, h2]
          simp)
        by_cases hl : Nat.log 2 (n + 1) + 1 = ℓ
        · rw [ite_eq_left hl]
          exact phiL_of_level ((hlevel_iff (htop_congr t) hDiv).2 ⟨hl, hs⟩)
        · rw [ite_eq_right hl]
          refine phiL_of_none (fun h => hl ((hlevel_iff (htop_congr t) hDiv).1 h).1) fun g hg => ?_
          rcases hsame_at t g hg with rfl | rfl
          · have := hg.2.2.1
            rw [overwrite_of_mem (mem_arcsInto.2 hL), h1] at this
            simp at this
            exact hab this.symm
          · have := hg.2.1
            rw [overwrite_of_mem (mem_arcsInto.2 hR), h2] at this
            simp at this
            exact hab this
      · -- different arcs, the other way
        intro t h1 h2
        have hs : SplitAt a b (n + 1) (by omega) hn (overwrite (arcsInto (networkNk k a b c d) v) top t) := Or.inr (by
          rw [overwrite_of_mem (mem_arcsInto.2 hL), overwrite_of_mem (mem_arcsInto.2 hR), h1, h2]
          simp)
        by_cases hl : Nat.log 2 (n + 1) + 1 = ℓ
        · rw [ite_eq_left hl]
          exact phiL_of_level ((hlevel_iff (htop_congr t) hDiv).2 ⟨hl, hs⟩)
        · rw [ite_eq_right hl]
          refine phiL_of_none (fun h => hl ((hlevel_iff (htop_congr t) hDiv).1 h).1) fun g hg => ?_
          rcases hsame_at t g hg with rfl | rfl
          · have := hg.2.1
            rw [overwrite_of_mem (mem_arcsInto.2 hL), h1] at this
            simp at this
            exact hab this
          · have := hg.2.2.1
            rw [overwrite_of_mem (mem_arcsInto.2 hR), h2] at this
            simp at this
            exact hab this.symm
      · -- the left arc, apart
        intro t h1 h2
        have hs : ¬ DivLevel a b ℓ (n + 1) (overwrite (arcsInto (networkNk k a b c d) v) top t) := fun h =>
          hnosplit_left t (by rw [h2]; simp) ((hlevel_iff (htop_congr t) hDiv).1 h).2
        have h0 : overwrite (arcsInto (networkNk k a b c d) v) top t (leftArc (n + 1) (by omega) hn) = {{a}, {b}} := by
          rw [overwrite_of_mem (mem_arcsInto.2 hL)]
          exact h1
        refine phiL_of_same hs ⟨fr_leftIdx (by omega) hn, h0 ▸ left_mem_lineages_pair, h0 ▸ right_mem_lineages_pair,
          h0 ▸ pair_notMem_pair hab⟩ fun g hg => ?_
        rcases hsame_at t g hg with rfl | rfl
        · rfl
        · have := hg.2.1
          rw [overwrite_of_mem (mem_arcsInto.2 hR), h2] at this
          simp at this
      · -- the left arc, coalesced
        intro t h1 h2
        have hs : ¬ DivLevel a b ℓ (n + 1) (overwrite (arcsInto (networkNk k a b c d) v) top t) := fun h =>
          hnosplit_left t (by rw [h2]; simp) ((hlevel_iff (htop_congr t) hDiv).1 h).2
        refine phiL_of_none hs fun g hg => ?_
        rcases hsame_at t g hg with rfl | rfl
        · have := hg.2.2.2
          rw [overwrite_of_mem (mem_arcsInto.2 hL), h1] at this
          exact this (mem_insert_self _ _)
        · have := hg.2.1
          rw [overwrite_of_mem (mem_arcsInto.2 hR), h2] at this
          simp at this
      · -- the right arc, apart
        intro t h1 h2
        have hs : ¬ DivLevel a b ℓ (n + 1) (overwrite (arcsInto (networkNk k a b c d) v) top t) := fun h =>
          hnosplit_right t (by rw [h2]; simp) ((hlevel_iff (htop_congr t) hDiv).1 h).2
        have h0 : overwrite (arcsInto (networkNk k a b c d) v) top t (rightArc (n + 1) (by omega) hn) = {{a}, {b}} := by
          rw [overwrite_of_mem (mem_arcsInto.2 hR)]
          exact h1
        refine phiL_of_same hs ⟨fr_rightIdx (by omega) hn, h0 ▸ left_mem_lineages_pair, h0 ▸ right_mem_lineages_pair,
          h0 ▸ pair_notMem_pair hab⟩ fun g hg => ?_
        rcases hsame_at t g hg with rfl | rfl
        · have := hg.2.1
          rw [overwrite_of_mem (mem_arcsInto.2 hL), h2] at this
          simp at this
        · rfl
      · -- the right arc, coalesced
        intro t h1 h2
        have hs : ¬ DivLevel a b ℓ (n + 1) (overwrite (arcsInto (networkNk k a b c d) v) top t) := fun h =>
          hnosplit_right t (by rw [h2]; simp) ((hlevel_iff (htop_congr t) hDiv).1 h).2
        refine phiL_of_none hs fun g hg => ?_
        rcases hsame_at t g hg with rfl | rfl
        · have := hg.2.1
          rw [overwrite_of_mem (mem_arcsInto.2 hL), h2] at this
          simp at this
        · have := hg.2.2.2
          rw [overwrite_of_mem (mem_arcsInto.2 hR), h1] at this
          exact this (mem_insert_self _ _)
    · -- the lineages are together on another arc
      refine vertexKernel_overwrite_eq hN hθ hρ hinj hD hvD hvr hch hw fun bot' top' htop' hmem _ hF' => ?_
      rw [insert_heapNode_stg h₃] at hF'
      have htf := htop' f (target_ne_of_tgtRk_le h₃ hSf.1.1)
      have hSf' : SameAt a b (n + 1) top' f := ⟨fr_succ h₃ hSf.1 hfv, htf ▸ hSf.2.1, htf ▸ hSf.2.2.1, htf ▸ hSf.2.2.2⟩
      refine phiL_of_same (fun h => ?_) hSf' fun g hg => eq_of_fr hF' hg.1 hSf'.1 hg.2.1 hSf'.2.1
      have hsp := ((hlevel_iff htop' hDiv).1 h).2
      have ha' : a ∈ lineages (arriving (networkNk k a b c d) (injNk k a b c d) top v) := by
        rcases hsp with ⟨h1, -⟩ | ⟨h1, -⟩
        · exact (hmem a).1 ⟨_, hL, h1⟩
        · exact (hmem a).1 ⟨_, hR, h1⟩
      rw [harr] at ha'
      exact hfv ((hout f).2 (eq_of_fr hF hSf.1 hfrout hSf.2.1 ha'))
  · -- the lineages have diverged at another level, or coalesced
    rw [phiL_of_none hDiv fun f hf => hS ⟨f, hf⟩]
    refine vertexKernel_overwrite_eq hN hθ hρ hinj hD hvD hvr hch hw fun bot' top' htop' hmem hclust hF' => ?_
    rw [insert_heapNode_stg h₃] at hF'
    -- if both arrive at `v` they have coalesced, and stay so
    have hboth : ∀ {e₁ e₂ : Edge k}, (networkNk k a b c d).graph.target e₁ = v → (networkNk k a b c d).graph.target e₂ = v →
        a ∈ lineages (top' e₁) → b ∈ lineages (top' e₂) → ∃ e, (networkNk k a b c d).graph.target e = v ∧ ({a, b} : Finset X) ∈ top' e := by
      intro e₁ e₂ h1 h2 h3 h4
      have ha' := (hmem a).1 ⟨_, h1, h3⟩
      have hb' := (hmem b).1 ⟨_, h2, h4⟩
      rw [harr] at ha' hb'
      have hmem2 : ({a, b} : Finset X) ∈ top (outTree (n + 1)) := by
        by_contra hne
        exact hS ⟨_, hfrout, ha', hb', hne⟩
      exact hclust _ (by rw [harr]; exact hmem2)
    have hfrin : ∀ {e : Edge k}, (networkNk k a b c d).graph.target e = v → Fr (n + 1) e := by
      intro e he
      rcases (target_eq_inner_iff (by omega) hn e).1 he with rfl | rfl
      · exact fr_leftIdx (by omega) hn
      · exact fr_rightIdx (by omega) hn
    refine phiL_of_none (fun h => ?_) fun g hg => ?_
    · obtain ⟨-, hs⟩ := (hlevel_iff htop' hDiv).1 h
      rcases hs with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · obtain ⟨e, he, hab'⟩ := hboth hL hR h1 h2
        have h3 := eq_of_fr hF' (hfrin he) (hfrin hL) (mem_lineages.2 ⟨_, hab', by simp⟩) h1
        have h4 := eq_of_fr hF' (hfrin he) (hfrin hR) (mem_lineages.2 ⟨_, hab', by simp⟩) h2
        exact leftArc_ne_rightArc _ _ _ (h3.symm.trans h4)
      · obtain ⟨e, he, hab'⟩ := hboth hR hL h1 h2
        have h3 := eq_of_fr hF' (hfrin he) (hfrin hR) (mem_lineages.2 ⟨_, hab', by simp⟩) h1
        have h4 := eq_of_fr hF' (hfrin he) (hfrin hL) (mem_lineages.2 ⟨_, hab', by simp⟩) h2
        exact leftArc_ne_rightArc _ _ _ (h4.symm.trans h3)
    · by_cases htg : (networkNk k a b c d).graph.target g = v
      · obtain ⟨e, he, hab'⟩ := hboth htg htg hg.2.1 hg.2.2.1
        have h3 := eq_of_fr hF' (hfrin he) hg.1 (mem_lineages.2 ⟨_, hab', by simp⟩) hg.2.1
        rw [h3] at hab'
        exact hg.2.2.2 hab'
      · refine hS ⟨g, ?_, ?_, ?_, ?_⟩
        · refine ⟨?_, by have := hg.1.2; omega⟩
          have h1 := hg.1.1
          have h2 : tgtRk g ≠ n + 2 := fun h => htg (eq_heapNode_of_rk h₃ ((rk_target g).trans h))
          omega
        · rw [← htop' g htg]
          exact hg.2.1
        · rw [← htop' g htg]
          exact hg.2.2.1
        · rw [← htop' g htg]
          exact hg.2.2.2

end StepInner

/-! ### The step at the cherry -/

section StepCherry

variable [DecidableEq X] (hd : ({a, b, c, d} : Finset X).card = 4) (hX : Fintype.card X = 4) {ε M : ℝ}

include hd hX in
/-- At the cherry, the lineages of `a` and `b` arrive apart, for any parameters. -/
theorem arriving_cherry {θ : MetricData (Edge k)} {ρ : ℝ} {bot top : Edge k → Finset (Finset X)}
    (hw : ∏ u ∈ stgT k, vertexWeight (networkNk k a b c d) θ ρ (injNk k a b c d) u bot top ≠ 0) :
    arriving (networkNk k a b c d) (injNk k a b c d) top .cherry = {{a}, {b}} := by
  obtain ⟨hab, hac, had, hbc, hbd, hcd⟩ := ne_of_card_four hd
  have hN := isPhylogenetic_networkNk (k := k) hd hX
  have hinj := validInj_injNk (k := k) (a := a) (b := b) (c := c) (d := d)
  have hD := downClosed_stgT (k := k) (a := a) (b := b) (c := c) (d := d)
  have hF := frontier_of_prod_ne_zero hN hinj hD hw
  have hbelow : ∀ {e : Edge k} {y x : X}, (networkNk k a b c d).graph.target e = .taxon y → x ∈ lineages (top e) → x = y := by
    intro e y x he hx
    obtain ⟨u, hu, hxu⟩ := hF.below e (by rw [he]; simp [rk]) x hx
    rw [he] at hu
    have h1 := eq_of_taxon_reaches hu
    have h2 := (mem_lineages_taxaInj.1 hxu).2
    rw [h1] at h2
    exact Vertex.taxon.inj h2
  have hat : ∀ x : X, ∃ e : Edge k, (networkNk k a b c d).graph.target e = .taxon x ∧ x ∈ lineages (top e) := by
    intro x
    obtain ⟨e, he₁, -, hx⟩ := (hF.mem x).2 ⟨.taxon x, by simp [rk], mem_lineages_taxaInj.2 ⟨mem_univ x, rfl⟩⟩
    obtain ⟨y, hy⟩ := rk_eq_zero_iff.1 (mem_stgT.1 he₁)
    have := hbelow hy hx
    subst this
    exact ⟨e, hy, hx⟩
  have hsrc : ∀ g : Edge k, (networkNk k a b c d).graph.source g = .cherry ↔ g = .cherryLeft ∨ g = .cherryRight := by
    intro g
    cases g <;> simp [source_step, source_bottomTaxon, source_tree, source_stem, heapNode]
  have hleft : a ∈ lineages (top .cherryLeft) := by
    obtain ⟨e, he, hx⟩ := hat a
    rcases (target_eq_taxon_iff e a).1 he with ⟨rfl, -⟩ | ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, h⟩
    · exact hx
    · exact absurd h hab.symm
    · exact absurd h hac.symm
    · exact absurd h had.symm
  have hright : b ∈ lineages (top .cherryRight) := by
    obtain ⟨e, he, hx⟩ := hat b
    rcases (target_eq_taxon_iff e b).1 he with ⟨-, h⟩ | ⟨rfl, -⟩ | ⟨-, h⟩ | ⟨-, h⟩
    · exact absurd h hab
    · exact hx
    · exact absurd h hbc.symm
    · exact absurd h hbd.symm
  have hgood : IsGoodForest (arriving (networkNk k a b c d) (injNk k a b c d) top .cherry) :=
    hF.good_arriving hinj (by simp [rk]) fun e he => by
      have h1 := rk_target_lt_rk_source (a := a) (b := b) (c := c) (d := d) e
      rw [he] at h1
      have h2 : rk (Vertex.cherry : Vertex k X) = 1 := rfl
      rw [mem_stgT]
      omega
  have hlin : lineages (arriving (networkNk k a b c d) (injNk k a b c d) top .cherry) = {a, b} := by
    ext x
    rw [mem_lineages_arriving]
    simp only [mem_insert, mem_singleton]
    constructor
    · rintro (h | ⟨g, hg, hx⟩)
      · exact absurd h notMem_lineages_injNk_cherry
      · rcases (hsrc g).1 hg with rfl | rfl
        · exact Or.inl (hbelow rfl hx)
        · exact Or.inr (hbelow rfl hx)
    · rintro (rfl | rfl)
      · exact Or.inr ⟨.cherryLeft, rfl, hleft⟩
      · exact Or.inr ⟨.cherryRight, rfl, hright⟩
  have hnot : ({a, b} : Finset X) ∉ arriving (networkNk k a b c d) (injNk k a b c d) top .cherry := by
    intro h
    rcases mem_union.1 h with h | h
    · exact notMem_lineages_injNk_cherry (x := a) (mem_lineages.2 ⟨_, h, by simp⟩)
    · obtain ⟨g, hg, hgm⟩ := mem_biUnion.1 h
      rcases (hsrc g).1 (mem_filter.1 hg).2 with rfl | rfl
      · exact hab (hbelow (x := b) rfl (mem_lineages.2 ⟨_, hgm, by simp⟩)).symm
      · exact hab (hbelow (x := a) rfl (mem_lineages.2 ⟨_, hgm, by simp⟩))
  exact KernelBounds.eq_pair_of_lineages hgood hab hlin hnot

omit [Fintype X] [DecidableEq X] in
/-- Only the stem enters the cherry. -/
theorem eq_stem_of_target_eq_cherry (f : Edge k) (hf : (networkNk k a b c d).graph.target f = .cherry) : f = .stem := by
  cases f <;> simp_all [target_rootTop, target_step, target_tree, heapNode]

include hd hX in
/-- **The step of the chain at the cherry.** The lineages of `a` and `b` arrive at the stem, and stay apart along it with probability `exp (-ε)`. -/
theorem phiL_cherry (ℓ : ℕ) (bot top : Edge k → Finset (Finset X))
    (hw : ∏ u ∈ stgT k, vertexWeight (networkNk k a b c d) (metricNk k ε M) 0 (injNk k a b c d) u bot top ≠ 0) :
    (Real.exp (-ε) * lvl (Real.exp (-ε)) 0 ℓ) *
        ((Fintype.card (Finset (Finset X)) : ℝ) ^ #(arcsInto (networkNk k a b c d) .cherry)ᶜ) ^ 2 =
      vertexKernel (networkNk k a b c d) (metricNk k ε M) 0 .cherry
        (arriving (networkNk k a b c d) (injNk k a b c d) top .cherry) fun t =>
          PhiL a b (Real.exp (-ε)) ℓ 0 (overwrite (arcsInto (networkNk k a b c d) .cherry) top t) := by
  obtain ⟨hab, hac, had, hbc, hbd, hcd⟩ := ne_of_card_four hd
  have hN := isPhylogenetic_networkNk (k := k) hd hX
  have hinj := validInj_injNk (k := k) (a := a) (b := b) (c := c) (d := d)
  have hD := downClosed_stgT (k := k) (a := a) (b := b) (c := c) (d := d)
  have hF := frontier_of_prod_ne_zero hN hinj hD hw
  have hbelow : ∀ {e : Edge k} {y x : X}, (networkNk k a b c d).graph.target e = .taxon y → x ∈ lineages (top e) → x = y := by
    intro e y x he hx
    obtain ⟨u, hu, hxu⟩ := hF.below e (by rw [he]; simp [rk]) x hx
    rw [he] at hu
    have h1 := eq_of_taxon_reaches hu
    have h2 := (mem_lineages_taxaInj.1 hxu).2
    rw [h1] at h2
    exact Vertex.taxon.inj h2
  have hin := eq_stem_of_target_eq_cherry (k := k) (a := a) (b := b) (c := c) (d := d)
  have hmem : (Edge.stem : Edge k) ∈ arcsInto (networkNk k a b c d) Vertex.cherry := mem_arcsInto.2 rfl
  rw [arriving_cherry hd hX hw]
  set S := arcsInto (networkNk k a b c d) Vertex.cherry with hS
  let g : Finset (Finset X) → ℝ := fun G => PhiL a b (Real.exp (-ε)) ℓ 0 (overwrite S top fun _ => G)
  have hψ : (fun t => PhiL a b (Real.exp (-ε)) ℓ 0 (overwrite S top t)) = fun t => g (t .stem) := by
    funext t
    change _ = PhiL a b (Real.exp (-ε)) ℓ 0 (overwrite S top fun _ => t .stem)
    congr 1
    funext f
    by_cases hf : f ∈ S
    · have : f = .stem := hin f (mem_arcsInto.1 hf)
      subst this
      rw [overwrite_of_mem hf, overwrite_of_mem hf]
    · rw [overwrite_of_notMem hf, overwrite_of_notMem hf]
  rw [hψ, vertexKernel_one_arc (N := networkNk k a b c d) (θ := metricNk k ε M) (ρ := 0) (v := Vertex.cherry) (e := Edge.stem) le_rfl rfl hin rfl
    ⟨{a}, by simp⟩ g, sum_kingman_pair hab]
  have hnolevel : ∀ top' : Edge k → Finset (Finset X), ¬ DivLevel a b ℓ 0 top' := by
    rintro top' ⟨m, h₁, -, hm, -⟩
    omega
  -- only the stem has both lineages
  have hstem : ∀ (G : Finset (Finset X)) (f : Edge k), SameAt a b 0 (overwrite S top fun _ => G) f → f = .stem := by
    intro G f hf
    obtain ⟨⟨hf₁, hf₂⟩, ha, -, -⟩ := hf
    have h2 := two_pow_succ_eq k
    have h1 := one_le_two_pow_k k
    cases f with
    | rootTaxon =>
      rw [overwrite_of_notMem (by simp [hS])] at ha
      exact absurd (hbelow rfl ha) had
    | rootTop =>
      simp only [tgtRk] at hf₁
      omega
    | step t =>
      simp only [tgtRk] at hf₁
      omega
    | bottomTaxon =>
      rw [overwrite_of_notMem (by simp [hS])] at ha
      exact absurd (hbelow rfl ha) hac
    | tree m =>
      simp only [tgtRk] at hf₁
      omega
    | stem => rfl
    | cherryLeft =>
      simp only [srcRk] at hf₂
      omega
    | cherryRight =>
      simp only [srcRk] at hf₂
      omega
  have hg₁ : g {{a}, {b}} = lvl (Real.exp (-ε)) 0 ℓ := by
    have h0 : overwrite S top (fun _ => ({{a}, {b}} : Finset (Finset X))) Edge.stem = {{a}, {b}} := overwrite_of_mem hmem _ _
    have ha' : a ∈ lineages (overwrite S top (fun _ => ({{a}, {b}} : Finset (Finset X))) Edge.stem) := by
      rw [h0]
      exact left_mem_lineages_pair
    have hb' : b ∈ lineages (overwrite S top (fun _ => ({{a}, {b}} : Finset (Finset X))) Edge.stem) := by
      rw [h0]
      exact right_mem_lineages_pair
    have hn' : ({a, b} : Finset X) ∉ overwrite S top (fun _ => ({{a}, {b}} : Finset (Finset X))) Edge.stem := by
      rw [h0]
      exact pair_notMem_pair hab
    exact phiL_of_same (hnolevel _) ⟨⟨by simp [tgtRk], by simp [srcRk]⟩, ha', hb', hn'⟩ (hstem _)
  have hg₂ : g (insert {a, b} {{a}, {b}}) = 0 := by
    refine phiL_of_none (hnolevel _) fun f hf => ?_
    have := hstem _ f hf
    subst this
    have h3 := hf.2.2.2
    rw [overwrite_of_mem hmem] at h3
    exact h3 (mem_insert_self _ _)
  rw [hg₁, hg₂, mul_zero, add_zero]
  rfl

end StepCherry

/-! ### The probability of each level -/

section Levels

variable [DecidableEq X] (hd : ({a, b, c, d} : Finset X).card = 4) (hX : Fintype.card X = 4) {ε M : ℝ} (hε : 0 < ε) (hM : 0 < M)

include hd hX hε hM in
/-- The mean of the potential doesn't change along the levels of the inverted subtree. -/
theorem stageMass_phiL {ℓ n : ℕ} (hℓ : ℓ ≤ k) (hn : n < 2 ^ k) :
    stageMass (networkNk k a b c d) (metricNk k ε M) 0 (injNk k a b c d) (stg k n) (PhiL a b (Real.exp (-ε)) ℓ n) =
      (Real.exp (-ε) * lvl (Real.exp (-ε)) 0 ℓ) * ((Fintype.card (Finset (Finset X)) : ℝ) ^ Fintype.card (Edge k)) ^ 2 := by
  have hN := isPhylogenetic_networkNk (k := k) hd hX
  have hθ : (networkNk k a b c d).IsWeakMetric (metricNk k ε M) := (isMetric_metricNk hd hX hε hM).isWeakMetric
  have hinj := validInj_injNk (k := k) (a := a) (b := b) (c := c) (d := d)
  have h2k := two_pow_succ_eq k
  induction n with
  | zero =>
    rw [← insert_cherry_stgT, ← stageMass_eq_insert downClosed_stgT (by simp [rk]) (fun e he => ?_) (phiL_cherry hd hX ℓ)]
    · exact stageMass_const hN hθ.isNormalized le_rfl hinj downClosed_stgT root_notMem_stgT _
    · have h1 := rk_target_lt_rk_source (a := a) (b := b) (c := c) (d := d) e
      rw [he] at h1
      have h2 : rk (Vertex.cherry : Vertex k X) = 1 := rfl
      rw [mem_stgT]
      omega
  | succ n ih =>
    have h₃ : n + 1 < 2 ^ (k + 1) := by omega
    rw [← insert_heapNode_stg h₃, ← stageMass_eq_insert (downClosed_stg n) (heapNode_notMem_stg h₃)
      (target_mem_stg_of_source_eq h₃) (phiL_step hd hX hε hM hℓ hn h₃)]
    exact ih (by omega)

omit [Fintype X] in
/-- At the height of the 'leaves', the potential is the indicator of the event at level `ℓ`. -/
theorem phiL_end {p : ℝ} {ℓ : ℕ} (hℓ : ℓ ≤ k) (top : Edge k → Finset (Finset X)) :
    PhiL a b p ℓ (2 ^ k - 1) top = if DivLevel a b ℓ (2 ^ k - 1) top then 1 else 0 := by
  unfold PhiL
  have h1 := one_le_two_pow_k k
  split_ifs with h
  · rfl
  · refine sum_eq_zero fun f _ => ?_
    split_ifs with hS
    swap
    · rfl
    obtain ⟨hf₁, hf₂⟩ := hS.1
    cases f with
    | stem =>
      simp only [srcRk] at hf₂
      have hk : k = 0 := by
        by_contra hk
        have : 2 ≤ 2 ^ k := by
          calc 2 = 2 ^ 1 := rfl
            _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
        omega
      subst hk
      obtain rfl : ℓ = 0 := by omega
      simp [levelVal, lvl]
    | tree m =>
      simp only [srcRk] at hf₂
      simp only [levelVal, lvl]
      have hlog : k ≤ Nat.log 2 (m.1 + 2) := Nat.le_log_of_pow_le (by norm_num) (by omega)
      rw [ite_eq_right (by omega)]
    | rootTaxon => rfl
    | rootTop => rfl
    | step t => rfl
    | bottomTaxon => rfl
    | cherryLeft => rfl
    | cherryRight => rfl

include hd hX hε hM in
/-- **"The probability of this for a specific `ℓ` is `(p/2)^ℓ`"** (`a:claim:prop1-level`). The lineages of `a` and `b` follow the same path without coalescing to height `1 + ℓε`, and diverge there. In `stageMass`, the
probability is up to the constant `(|forests| ^ |E|) ^ 2`. -/
theorem stageMass_divLevel {ℓ : ℕ} (h1 : 1 ≤ ℓ) (hℓ : ℓ ≤ k) :
    stageMass (networkNk k a b c d) (metricNk k ε M) 0 (injNk k a b c d) (stg k (2 ^ k - 1))
        (fun top => if DivLevel a b ℓ (2 ^ k - 1) top then 1 else 0) =
      (Real.exp (-ε) / 2) ^ ℓ * ((Fintype.card (Finset (Finset X)) : ℝ) ^ Fintype.card (Edge k)) ^ 2 := by
  have h1k := one_le_two_pow_k k
  have hm := stageMass_phiL (a := a) (b := b) (c := c) (d := d) (n := 2 ^ k - 1) hd hX hε hM hℓ (by omega)
  have hval : Real.exp (-ε) * lvl (Real.exp (-ε)) 0 ℓ = (Real.exp (-ε) / 2) ^ ℓ := by
    obtain ⟨i, rfl⟩ : ∃ i, ℓ = i + 1 := ⟨ℓ - 1, by omega⟩
    simp only [lvl, Nat.succ_pos, ↓reduceIte, Nat.add_sub_cancel, Nat.sub_zero, pow_succ]
    ring
  rw [hval] at hm
  rw [← hm]
  exact stageMass_congr fun _ top _ => (phiL_end hℓ top).symm

end Levels

/-! ### The union of the levels -/

section Union

variable [DecidableEq X] (hd : ({a, b, c, d} : Finset X).card = 4) (hX : Fintype.card X = 4) {ε M : ℝ}
  {bot top : Edge k → Finset (Finset X)} {N' : ℕ}

include hd hX in
theorem frontier_of_le {n : ℕ} (hn : n ≤ N') (hw : ∏ u ∈ stg k N', vertexWeight (networkNk k a b c d) (metricNk k ε M) 0 (injNk k a b c d) u bot top ≠ 0) :
    Frontier (networkNk k a b c d) (injNk k a b c d) (stg k n) bot top := by
  refine frontier_of_prod_ne_zero (isPhylogenetic_networkNk hd hX) validInj_injNk (downClosed_stg n)
    (prod_ne_zero_iff.2 fun u hu => prod_ne_zero_iff.1 hw u ?_)
  rw [mem_stg] at hu ⊢
  omega

include hd hX in
/-- A lineage on an arc entering a node that isn't a 'leaf' is on the arc leaving it. -/
theorem mem_out_of_mem_in {n : ℕ} (hn : n + 1 < 2 ^ k) (hN' : n + 1 ≤ N') (h₃ : n + 1 < 2 ^ (k + 1))
    (hw : ∏ u ∈ stg k N', vertexWeight (networkNk k a b c d) (metricNk k ε M) 0 (injNk k a b c d) u bot top ≠ 0)
    {e : Edge k} (he : (networkNk k a b c d).graph.target e = heapNode (n + 1) (by omega) h₃) {x : X}
    (hx : x ∈ lineages (top e)) : x ∈ lineages (top (outTree (n + 1))) := by
  have hF := frontier_of_le (n := n) hd hX (by omega) hw
  have hg := hF.good_arriving validInj_injNk (heapNode_notMem_stg h₃) (target_mem_stg_of_source_eq h₃)
  have hw' : vertexWeight (networkNk k a b c d) (metricNk k ε M) 0 (injNk k a b c d) (heapNode (n + 1) (by omega) h₃) bot top ≠ 0 :=
    prod_ne_zero_iff.1 hw _ (by rw [mem_stg, rk_heapNode]; omega)
  obtain ⟨-, -, hmem⟩ := good_of_vertexWeight_ne_zero hg hw'
  have := (hmem x).1 ⟨e, he, hx⟩
  rwa [arriving_inner (by omega) hn h₃] at this

omit [Fintype X] [DecidableEq X] in
theorem divAt_of_splitAt' [DecidableEq X] {n : ℕ} {h₁ : 1 ≤ n + 1} {h₂ : n + 1 < 2 ^ k} (h : SplitAt a b (n + 1) h₁ h₂ top) :
    DivAt a b (n + 1) top := by
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact ⟨leftIdx _ h₁ h₂, rightIdx _ h₁ h₂, leftIdx_ne_rightIdx _ _ _, fr_leftIdx h₁ h₂, fr_rightIdx h₁ h₂, h1, h2⟩
  · exact ⟨rightIdx _ h₁ h₂, leftIdx _ h₁ h₂, (leftIdx_ne_rightIdx _ _ _).symm, fr_rightIdx h₁ h₂, fr_leftIdx h₁ h₂, h1, h2⟩

include hd hX in
/-- Lineages on two arcs stay on two arcs. -/
theorem divAt_succ {n : ℕ} (hn : n + 1 < 2 ^ k) (hN' : n + 1 ≤ N')
    (hw : ∏ u ∈ stg k N', vertexWeight (networkNk k a b c d) (metricNk k ε M) 0 (injNk k a b c d) u bot top ≠ 0)
    (h : DivAt a b n top) : DivAt a b (n + 1) top := by
  obtain ⟨hab, hac, had, hbc, hbd, hcd⟩ := ne_of_card_four hd
  have h₃ : n + 1 < 2 ^ (k + 1) := by
    have := two_pow_succ_eq k
    omega
  have hF := frontier_of_le (n := n) hd hX (by omega) hw
  have hF' := frontier_of_le (n := n + 1) hd hX hN' hw
  obtain ⟨m₁, m₂, hne, hf₁, hf₂, ha, hb⟩ := h
  obtain ⟨m₁', hf₁', ha'⟩ := exists_tree_of_stage hF' (by omega) hn hac had
  obtain ⟨m₂', hf₂', hb'⟩ := exists_tree_of_stage hF' (by omega) hn hbc hbd
  refine ⟨m₁', m₂', ?_, hf₁', hf₂', ha', hb'⟩
  rintro rfl
  have hfrout : Fr n (outTree (n + 1) : Edge k) := fr_of_source_eq (a := a) (b := b) (c := c) (d := d) h₃ ((source_eq_inner_iff (by omega) hn h₃ _).2 rfl)
  by_cases htv : (networkNk k a b c d).graph.target (.tree m₁') = heapNode (n + 1) (by omega) h₃
  · have h1 := eq_of_fr hF hfrout hf₁ (mem_out_of_mem_in hd hX hn hN' h₃ hw htv ha') ha
    have h2 := eq_of_fr hF hfrout hf₂ (mem_out_of_mem_in hd hX hn hN' h₃ hw htv hb') hb
    exact hne (Edge.tree.inj (h1.symm.trans h2))
  · have hfr : Fr n (.tree m₁') := by
      rw [fr_tree] at hf₁' ⊢
      have h4 : (m₁'.1 + 2) / 2 ≠ n + 1 := fun h => htv (by
        rw [target_tree, heapNode_inj]
        exact h)
      omega
    have h1 := eq_of_fr hF hfr hf₁ ha' ha
    have h2 := eq_of_fr hF hfr hf₂ hb' hb
    exact hne (Edge.tree.inj (h1.symm.trans h2))

include hd hX in
/-- Lineages that split at the node `n + 1` were together below it. -/
theorem not_divAt_of_splitAt {n : ℕ} (hn : n + 1 < 2 ^ k) (hN' : n + 1 ≤ N') {h₁ : 1 ≤ n + 1}
    (hw : ∏ u ∈ stg k N', vertexWeight (networkNk k a b c d) (metricNk k ε M) 0 (injNk k a b c d) u bot top ≠ 0)
    (h : SplitAt a b (n + 1) h₁ hn top) : ¬ DivAt a b n top := by
  have h₃ : n + 1 < 2 ^ (k + 1) := by
    have := two_pow_succ_eq k
    omega
  have hF := frontier_of_le (n := n) hd hX (by omega) hw
  have hfrout : Fr n (outTree (n + 1) : Edge k) := fr_of_source_eq (a := a) (b := b) (c := c) (d := d) h₃ ((source_eq_inner_iff (by omega) hn h₃ _).2 rfl)
  have hL : (networkNk k a b c d).graph.target (leftArc (n + 1) h₁ hn) = heapNode (n + 1) (by omega) h₃ :=
    (target_eq_inner_iff h₁ hn _).2 (Or.inl rfl)
  have hR : (networkNk k a b c d).graph.target (rightArc (n + 1) h₁ hn) = heapNode (n + 1) (by omega) h₃ :=
    (target_eq_inner_iff h₁ hn _).2 (Or.inr rfl)
  have hboth : a ∈ lineages (top (outTree (n + 1))) ∧ b ∈ lineages (top (outTree (n + 1))) := by
    rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨mem_out_of_mem_in hd hX hn hN' h₃ hw hL h1, mem_out_of_mem_in hd hX hn hN' h₃ hw hR h2⟩
    · exact ⟨mem_out_of_mem_in hd hX hn hN' h₃ hw hR h1, mem_out_of_mem_in hd hX hn hN' h₃ hw hL h2⟩
  rintro ⟨m₁, m₂, hne, hf₁, hf₂, ha, hb⟩
  have h1 := eq_of_fr hF hfrout hf₁ hboth.1 ha
  have h2 := eq_of_fr hF hfrout hf₂ hboth.2 hb
  exact hne (Edge.tree.inj (h1.symm.trans h2))

include hd hX in
/-- **The event is the union of the splits**: the lineages of `a`, `b` are on different arcs of the subtree exactly when they have split at a node so far. -/
theorem divAt_iff_exists_splitAt {n : ℕ} (hn : n < 2 ^ k) (hN' : n ≤ N')
    (hw : ∏ u ∈ stg k N', vertexWeight (networkNk k a b c d) (metricNk k ε M) 0 (injNk k a b c d) u bot top ≠ 0) :
    DivAt a b n top ↔ ∃ (m : ℕ) (h₁ : 1 ≤ m) (h₂ : m < 2 ^ k), m ≤ n ∧ SplitAt a b m h₁ h₂ top := by
  induction n with
  | zero =>
    constructor
    · rintro ⟨m₁, -, -, hf, -⟩
      have := (fr_tree.1 hf).1
      omega
    · rintro ⟨m, h₁, -, hm, -⟩
      omega
  | succ n ih =>
    have ih' := ih (by omega) (by omega)
    have h₃ : n + 1 < 2 ^ (k + 1) := by
      have := two_pow_succ_eq k
      omega
    constructor
    · intro hdiv
      by_cases hprev : DivAt a b n top
      · obtain ⟨m, h₁, h₂, hm, hs⟩ := ih'.1 hprev
        exact ⟨m, h₁, h₂, by omega, hs⟩
      obtain ⟨m₁, m₂, hne, hf₁, hf₂, ha, hb⟩ := hdiv
      have hF := frontier_of_le (n := n) hd hX (by omega) hw
      have hfrout : Fr n (outTree (n + 1) : Edge k) := fr_of_source_eq (a := a) (b := b) (c := c) (d := d) h₃ ((source_eq_inner_iff (by omega) hn h₃ _).2 rfl)
      have hsrc_out : srcRk (outTree (n + 1) : Edge k) = n + 2 := by
        rw [← rk_source (a := a) (b := b) (c := c) (d := d), (source_eq_inner_iff (by omega) hn h₃ _).2 rfl, rk_heapNode]
      -- an arc off the next node that leaves the stage `n + 1` and the arc from the next node
      have hkey : ∀ {x y : X} {g g' : Fin (2 ^ (k + 1) - 2)}, Fr (n + 1) (.tree g) → Fr (n + 1) (.tree g') →
          x ∈ lineages (top (.tree g)) → y ∈ lineages (top (.tree g')) →
          (networkNk k a b c d).graph.target (.tree g) ≠ heapNode (n + 1) (by omega) h₃ →
          (networkNk k a b c d).graph.target (.tree g') = heapNode (n + 1) (by omega) h₃ →
          ∃ h : Fin (2 ^ (k + 1) - 2), Fr n (.tree g) ∧ Fr n (.tree h) ∧ g ≠ h ∧ y ∈ lineages (top (.tree h)) := by
        intro x y g g' hg hg' hx hy ht ht'
        have hgn : Fr n (.tree g) := by
          rw [fr_tree] at hg ⊢
          have h4 : (g.1 + 2) / 2 ≠ n + 1 := fun h => ht (by
            rw [target_tree, heapNode_inj]
            exact h)
          omega
        have hyout := mem_out_of_mem_in hd hX hn (by omega) h₃ hw ht' hy
        have h2n : 2 ≤ n + 1 := by
          have := (fr_tree.1 hgn).1
          omega
        rw [outTree_of_two_le h2n h₃] at hyout hfrout hsrc_out
        refine ⟨_, hgn, hfrout, ?_, hyout⟩
        rintro rfl
        have := hg.2
        omega
      by_cases ht₁ : (networkNk k a b c d).graph.target (.tree m₁) = heapNode (n + 1) (by omega) h₃
      · by_cases ht₂ : (networkNk k a b c d).graph.target (.tree m₂) = heapNode (n + 1) (by omega) h₃
        · refine ⟨n + 1, by omega, hn, le_rfl, ?_⟩
          rcases (target_eq_inner_iff (by omega) hn _).1 ht₁ with h1 | h1 <;>
            rcases (target_eq_inner_iff (by omega) hn _).1 ht₂ with h2 | h2
          · exact absurd (Edge.tree.inj (h1.trans h2.symm)) hne
          · exact Or.inl ⟨h1 ▸ ha, h2 ▸ hb⟩
          · exact Or.inr ⟨h1 ▸ ha, h2 ▸ hb⟩
          · exact absurd (Edge.tree.inj (h1.trans h2.symm)) hne
        · obtain ⟨g, hgn, hhn, hgh, hag⟩ := hkey hf₂ hf₁ hb ha ht₂ ht₁
          exact absurd ⟨g, m₂, hgh.symm, hhn, hgn, hag, hb⟩ hprev
      · by_cases ht₂ : (networkNk k a b c d).graph.target (.tree m₂) = heapNode (n + 1) (by omega) h₃
        · obtain ⟨g, hgn, hhn, hgh, hbg⟩ := hkey hf₁ hf₂ ha hb ht₁ ht₂
          exact absurd ⟨m₁, g, hgh, hgn, hhn, ha, hbg⟩ hprev
        · refine absurd ⟨m₁, m₂, hne, ?_, ?_, ha, hb⟩ hprev
          · rw [fr_tree] at hf₁ ⊢
            have h4 : (m₁.1 + 2) / 2 ≠ n + 1 := fun h => ht₁ (by
              rw [target_tree, heapNode_inj]
              exact h)
            omega
          · rw [fr_tree] at hf₂ ⊢
            have h4 : (m₂.1 + 2) / 2 ≠ n + 1 := fun h => ht₂ (by
              rw [target_tree, heapNode_inj]
              exact h)
            omega
    · rintro ⟨m, h₁, h₂, hm, hs⟩
      rcases Nat.lt_or_ge m (n + 1) with hlt | hge
      · exact divAt_succ hd hX hn hN' hw (ih'.2 ⟨m, h₁, h₂, by omega, hs⟩)
      · obtain rfl : m = n + 1 := by omega
        exact divAt_of_splitAt' hs

include hd hX in
/-- **The events are disjoint**: the lineages of `a`, `b` split at one node at most. -/
theorem eq_of_splitAt_of_splitAt {m m' : ℕ} {h₁ : 1 ≤ m} {h₂ : m < 2 ^ k} {h₁' : 1 ≤ m'} {h₂' : m' < 2 ^ k} (hm : m ≤ N') (hm' : m' ≤ N')
    (hw : ∏ u ∈ stg k N', vertexWeight (networkNk k a b c d) (metricNk k ε M) 0 (injNk k a b c d) u bot top ≠ 0)
    (hs : SplitAt a b m h₁ h₂ top) (hs' : SplitAt a b m' h₁' h₂' top) : m = m' := by
  have key : ∀ {m m' : ℕ} {h₁ : 1 ≤ m} {h₂ : m < 2 ^ k} {h₁' : 1 ≤ m'} {h₂' : m' < 2 ^ k}, m < m' → m' ≤ N' →
      SplitAt a b m h₁ h₂ top → SplitAt a b m' h₁' h₂' top → False := by
    intro m m' h₁ h₂ h₁' h₂' hlt hm' hs hs'
    obtain ⟨n, rfl⟩ : ∃ n, m' = n + 1 := ⟨m' - 1, by omega⟩
    exact not_divAt_of_splitAt hd hX h₂' hm' hw hs' ((divAt_iff_exists_splitAt hd hX (by omega) (by omega) hw).2 ⟨m, h₁, h₂, by omega, hs⟩)
  rcases Nat.lt_trichotomy m m' with h | h | h
  · exact (key h hm' hs hs').elim
  · exact h
  · exact (key h hm hs' hs).elim

include hd hX in
/-- The indicator of the event is the sum of those of the levels. -/
theorem sum_divLevel_eq (hw : ∏ u ∈ stg k (2 ^ k - 1), vertexWeight (networkNk k a b c d) (metricNk k ε M) 0 (injNk k a b c d) u bot top ≠ 0) :
    ∑ ℓ ∈ Finset.Icc 1 k, (if DivLevel a b ℓ (2 ^ k - 1) top then (1 : ℝ) else 0) = if DivAt a b (2 ^ k - 1) top then 1 else 0 := by
  have h1k := one_le_two_pow_k k
  have hiff := divAt_iff_exists_splitAt (a := a) (b := b) (c := c) (d := d) (n := 2 ^ k - 1) (N' := 2 ^ k - 1) (M := M) (ε := ε) hd hX (by omega) le_rfl hw
  by_cases hdiv : DivAt a b (2 ^ k - 1) top
  · rw [ite_eq_left hdiv]
    obtain ⟨m, h₁, h₂, hm, hs⟩ := hiff.1 hdiv
    have hlog : Nat.log 2 m < k := Nat.log_lt_of_lt_pow (by omega) h₂
    rw [sum_eq_single (Nat.log 2 m + 1)]
    · rw [ite_eq_left ⟨m, h₁, h₂, hm, rfl, hs⟩]
    · intro ℓ _ hℓ
      refine ite_eq_right ?_
      rintro ⟨m', h₁', h₂', hm', hlog', hs'⟩
      have := eq_of_splitAt_of_splitAt hd hX hm hm' hw hs hs'
      subst this
      exact hℓ hlog'.symm
    · intro h
      exact absurd (Finset.mem_Icc.2 ⟨by omega, by omega⟩) h
  · rw [ite_eq_right hdiv]
    refine sum_eq_zero fun ℓ _ => ite_eq_right ?_
    rintro ⟨m, h₁, h₂, hm, -, hs⟩
    exact hdiv (hiff.2 ⟨m, h₁, h₂, hm, hs⟩)

/-- `α` of the proof of Proposition 1, `∑_{ℓ=1}^k (p/2)^ℓ` with `p = exp (-ε)`, the probability that the `a`, `b` lineages are on different edges at height `1 + (k + 1)ε`: this is `stageMass_divAt`. -/
def alpha (k : ℕ) (ε : ℝ) : ℝ := ∑ ℓ ∈ Finset.Icc 1 k, (Real.exp (-ε) / 2) ^ ℓ

include hd hX in
/-- **"Thus the probability of the full event is `α`"** (`a:claim:prop1-alpha`). In `stageMass`, the probability is up to the constant `(|forests| ^ |E|) ^ 2`. -/
theorem stageMass_divAt (hε : 0 < ε) (hM : 0 < M) :
    stageMass (networkNk k a b c d) (metricNk k ε M) 0 (injNk k a b c d) (stg k (2 ^ k - 1))
        (fun top => if DivAt a b (2 ^ k - 1) top then 1 else 0) =
      alpha k ε * ((Fintype.card (Finset (Finset X)) : ℝ) ^ Fintype.card (Edge k)) ^ 2 := by
  rw [stageMass_congr (φ' := fun top => ∑ ℓ ∈ Finset.Icc 1 k, if DivLevel a b ℓ (2 ^ k - 1) top then (1 : ℝ) else 0)
    fun _ top hw => (sum_divLevel_eq hd hX hw).symm, stageMass_sum, alpha, sum_mul]
  exact sum_congr rfl fun ℓ hℓ =>
    stageMass_divLevel hd hX hε hM (Finset.mem_Icc.1 hℓ).1 (Finset.mem_Icc.1 hℓ).2

end Union

end AllmanEtAl2023.NetworkNk
