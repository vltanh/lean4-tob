module

public import AllmanEtAl2023.NetworkNk
public import Phylogenetics.Network.DeletedArcs

/-!
# Allman, Baños, Mitchell, Rhodes 2023: the graph of `𝒩(k)⁺`

The arcs entering and leaving each node of `𝒩(k)⁺`, its rank, and the facts of Proposition 1's proof about its shape: it is a
network of Definition 1, its lengths are valid parameters, and the arc above the cherry is a cut edge.
-/

@[expose] public noncomputable section

open Phylogenetics Phylogenetics.RootedNetwork Finset
open scoped Classical

namespace AllmanEtAl2023.NetworkNk

variable {X : Type*} {k : ℕ} {a b c d : X}

/-! ### The heap numbers -/

theorem two_pow_succ_sub_one_pos (k : ℕ) : 1 ≤ 2 ^ (k + 1) - 1 := by
  have := two_le_two_pow_succ k
  omega

@[simp] theorem heapNode_inj {m m' : ℕ} {h₁ h₂ h₁' h₂'} :
    (heapNode m h₁ h₂ : Vertex k X) = heapNode m' h₁' h₂' ↔ m = m' := by
  simp only [heapNode, Vertex.heap.injEq, Fin.mk.injEq]
  omega

@[simp] theorem root_ne_heapNode {m : ℕ} {h₁ h₂} : (Vertex.root : Vertex k X) ≠ heapNode m h₁ h₂ := by
  simp [heapNode]

@[simp] theorem cherry_ne_heapNode {m : ℕ} {h₁ h₂} : (Vertex.cherry : Vertex k X) ≠ heapNode m h₁ h₂ := by
  simp [heapNode]

@[simp] theorem taxon_ne_heapNode {x : X} {m : ℕ} {h₁ h₂} : (Vertex.taxon x : Vertex k X) ≠ heapNode m h₁ h₂ := by
  simp [heapNode]

/-- A node of the inverted subtree is the one with its heap number. -/
theorem heap_eq_heapNode (n : Fin (2 ^ (k + 1) - 1)) :
    (Vertex.heap n : Vertex k X) = heapNode (n.1 + 1) (by omega) (by have := n.2; omega) := by
  simp [heapNode]

/-- The rank of a node: arcs go down in rank. The node with heap number `m` has rank `m + 1`. -/
def rk : Vertex k X → ℕ
  | .root => 2 ^ (k + 1) + 1
  | .cherry => 1
  | .heap n => n.1 + 2
  | .taxon _ => 0

@[simp] theorem rk_heapNode {m : ℕ} {h₁ h₂} : rk (heapNode m h₁ h₂ : Vertex k X) = m + 1 := by
  simp only [heapNode, rk]
  omega

@[simp] theorem source_rootTaxon : (networkNk k a b c d).graph.source .rootTaxon = .root := rfl
@[simp] theorem target_rootTaxon : (networkNk k a b c d).graph.target .rootTaxon = .taxon d := rfl
@[simp] theorem source_rootTop : (networkNk k a b c d).graph.source .rootTop = .root := rfl
theorem target_rootTop : (networkNk k a b c d).graph.target .rootTop =
    heapNode (2 ^ (k + 1) - 1) (two_pow_succ_sub_one_pos k) (by have := two_le_two_pow_succ k; omega) := rfl
theorem source_step (t : Fin (2 ^ k - 1)) : (networkNk k a b c d).graph.source (.step t) =
    heapNode (2 ^ k + t.1 + 1) (by omega) (by
      have := t.2
      have := two_pow_succ_eq k
      have := one_le_two_pow_k k
      omega) := rfl
theorem target_step (t : Fin (2 ^ k - 1)) : (networkNk k a b c d).graph.target (.step t) =
    heapNode (2 ^ k + t.1) (by have := one_le_two_pow_k k; omega) (by
      have := t.2
      have := two_pow_succ_eq k
      have := one_le_two_pow_k k
      omega) := rfl
theorem source_bottomTaxon : (networkNk k a b c d).graph.source .bottomTaxon =
    heapNode (2 ^ k) (one_le_two_pow_k k) (by
      have := two_pow_succ_eq k
      have := one_le_two_pow_k k
      omega) := rfl
@[simp] theorem target_bottomTaxon : (networkNk k a b c d).graph.target .bottomTaxon = .taxon c := rfl
theorem source_tree (m : Fin (2 ^ (k + 1) - 2)) : (networkNk k a b c d).graph.source (.tree m) =
    heapNode (m.1 + 2) (by omega) (by
      have := m.2
      have := two_le_two_pow_succ k
      omega) := rfl
theorem target_tree (m : Fin (2 ^ (k + 1) - 2)) : (networkNk k a b c d).graph.target (.tree m) =
    heapNode ((m.1 + 2) / 2) (by omega) (by
      have := m.2
      have := two_le_two_pow_succ k
      omega) := rfl
theorem source_stem : (networkNk k a b c d).graph.source .stem =
    heapNode 1 le_rfl (by have := two_le_two_pow_succ k; omega) := rfl
@[simp] theorem target_stem : (networkNk k a b c d).graph.target .stem = .cherry := rfl
@[simp] theorem source_cherryLeft : (networkNk k a b c d).graph.source .cherryLeft = .cherry := rfl
@[simp] theorem target_cherryLeft : (networkNk k a b c d).graph.target .cherryLeft = .taxon a := rfl
@[simp] theorem source_cherryRight : (networkNk k a b c d).graph.source .cherryRight = .cherry := rfl
@[simp] theorem target_cherryRight : (networkNk k a b c d).graph.target .cherryRight = .taxon b := rfl

/-- Arcs go down in rank. -/
theorem rk_target_lt_rk_source (e : Edge k) :
    rk ((networkNk k a b c d).graph.target e) < rk ((networkNk k a b c d).graph.source e) := by
  have h1 := two_pow_succ_eq k
  have h2 := one_le_two_pow_k k
  cases e with
  | rootTaxon => simp [rk]
  | rootTop => rw [target_rootTop, rk_heapNode]; simp [rk]
  | step t => rw [target_step, source_step, rk_heapNode, rk_heapNode]; omega
  | bottomTaxon => rw [source_bottomTaxon, rk_heapNode]; simp [rk]
  | tree m => rw [target_tree, source_tree, rk_heapNode, rk_heapNode]; omega
  | stem => rw [source_stem, rk_heapNode]; simp [rk]
  | cherryLeft => simp [rk]
  | cherryRight => simp [rk]

theorem rk_le_root (v : Vertex k X) : rk v ≤ 2 ^ (k + 1) + 1 := by
  cases v with
  | root => simp [rk]
  | cherry =>
    have := two_le_two_pow_succ k
    simp only [rk]
    omega
  | heap n =>
    have := n.2
    simp only [rk]
    omega
  | taxon x => simp [rk]

/-- A node with a rank is below only nodes of a larger rank. -/
theorem rk_le_of_reaches {u v : Vertex k X} (h : (networkNk k a b c d).graph.Reaches u v) : rk v ≤ rk u := by
  induction h with
  | refl => exact le_rfl
  | tail _ hstep ih =>
    obtain ⟨e, rfl, rfl⟩ := hstep
    exact (rk_target_lt_rk_source e).le.trans ih

/-- `𝒩(k)⁺` is acyclic. -/
theorem isAcyclic_networkNk : (networkNk k a b c d).graph.IsAcyclic := by
  refine DirectedMultigraph.isAcyclic_of_rank _ (fun v => 2 ^ (k + 1) + 1 - rk v) fun e => ?_
  have h := rk_target_lt_rk_source (a := a) (b := b) (c := c) (d := d) e
  have hs := rk_le_root ((networkNk k a b c d).graph.source e)
  omega

/-! ### The arcs at each node -/

/-- The arc of the inverted subtree from the node `2 m` to the node `m`. -/
def leftArc (m : ℕ) (h₁ : 1 ≤ m) (h₂ : m < 2 ^ k) : Edge k :=
  .tree ⟨2 * m - 2, by have := two_pow_succ_eq k; omega⟩

/-- The arc of the inverted subtree from the node `2 m + 1` to the node `m`. -/
def rightArc (m : ℕ) (h₁ : 1 ≤ m) (h₂ : m < 2 ^ k) : Edge k :=
  .tree ⟨2 * m - 1, by have := two_pow_succ_eq k; omega⟩

/-- The arc entering a 'leaf' of the inverted subtree, of heap number `m`: a step of the path, or for the top one the
arc from the root. -/
def pathIn (m : ℕ) : Edge k := if h : m - 2 ^ k < 2 ^ k - 1 then .step ⟨m - 2 ^ k, h⟩ else .rootTop

/-- The arc of the inverted subtree leaving the node `m`, or the stem at `m = 1`. -/
def outTree (m : ℕ) : Edge k := if h : m - 2 < 2 ^ (k + 1) - 2 ∧ 2 ≤ m then .tree ⟨m - 2, h.1⟩ else .stem

/-- The arc of the path leaving a 'leaf' of the inverted subtree, of heap number `m`, or the arc to `c` at the lowest one. -/
def outPath (m : ℕ) : Edge k :=
  if h : 2 ^ k < m ∧ m - 2 ^ k - 1 < 2 ^ k - 1 then .step ⟨m - 2 ^ k - 1, h.2⟩ else .bottomTaxon

theorem leftArc_ne_rightArc (m : ℕ) (h₁ : 1 ≤ m) (h₂ : m < 2 ^ k) : leftArc m h₁ h₂ ≠ rightArc m h₁ h₂ := by
  simp only [leftArc, rightArc, ne_eq, Edge.tree.injEq, Fin.mk.injEq]
  omega

/-- The arcs entering a node of the inverted subtree that isn't a 'leaf'. -/
theorem target_eq_inner_iff {m : ℕ} (h₁ : 1 ≤ m) (h₂ : m < 2 ^ k) {h₃ : m < 2 ^ (k + 1)} (e : Edge k) :
    (networkNk k a b c d).graph.target e = heapNode m h₁ h₃ ↔ e = leftArc m h₁ h₂ ∨ e = rightArc m h₁ h₂ := by
  have h4 := two_pow_succ_eq k
  cases e with
  | rootTaxon => simp [heapNode, leftArc, rightArc]
  | rootTop =>
    rw [target_rootTop, heapNode_inj]
    simp only [leftArc, rightArc, reduceCtorEq, or_self, iff_false]
    omega
  | step t =>
    rw [target_step, heapNode_inj]
    simp only [leftArc, rightArc, reduceCtorEq, or_self, iff_false]
    omega
  | bottomTaxon => simp [heapNode, leftArc, rightArc]
  | tree m' =>
    rw [target_tree, heapNode_inj]
    simp only [leftArc, rightArc, Edge.tree.injEq, Fin.ext_iff]
    omega
  | stem => simp [heapNode, leftArc, rightArc]
  | cherryLeft => simp [heapNode, leftArc, rightArc]
  | cherryRight => simp [heapNode, leftArc, rightArc]

/-- The one arc entering a 'leaf' of the inverted subtree. -/
theorem target_eq_path_iff {m : ℕ} (h₁ : 1 ≤ m) (h₂ : 2 ^ k ≤ m) (h₃ : m < 2 ^ (k + 1)) (e : Edge k) :
    (networkNk k a b c d).graph.target e = heapNode m h₁ h₃ ↔ e = pathIn m := by
  have h4 := two_pow_succ_eq k
  have h5 := one_le_two_pow_k k
  cases e with
  | rootTaxon =>
    simp only [target_rootTaxon, heapNode, reduceCtorEq, pathIn, false_iff]
    split_ifs <;> simp
  | rootTop =>
    rw [target_rootTop, heapNode_inj]
    simp only [pathIn]
    split_ifs with h
    · simp only [iff_false]
      omega
    · simp only [iff_true]
      omega
  | step t =>
    rw [target_step, heapNode_inj]
    simp only [pathIn]
    split_ifs with h
    · simp only [Edge.step.injEq, Fin.ext_iff]
      omega
    · simp only [iff_false]
      have := t.2
      omega
  | bottomTaxon =>
    simp only [target_bottomTaxon, heapNode, reduceCtorEq, pathIn, false_iff]
    split_ifs <;> simp
  | tree m' =>
    rw [target_tree, heapNode_inj]
    simp only [pathIn]
    have := m'.2
    split_ifs with h
    · simp only [iff_false]
      omega
    · simp only [iff_false]
      omega
  | stem =>
    simp only [target_stem, heapNode, reduceCtorEq, pathIn, false_iff]
    split_ifs <;> simp
  | cherryLeft =>
    simp only [target_cherryLeft, heapNode, reduceCtorEq, pathIn, false_iff]
    split_ifs <;> simp
  | cherryRight =>
    simp only [target_cherryRight, heapNode, reduceCtorEq, pathIn, false_iff]
    split_ifs <;> simp

theorem outTree_ne_outPath (m : ℕ) : (outTree m : Edge k) ≠ outPath m := by
  simp only [outTree, outPath]
  split_ifs <;> simp_all

theorem outTree_of_two_le {m : ℕ} (hm : 2 ≤ m) (hm' : m < 2 ^ (k + 1)) :
    (outTree m : Edge k) = .tree ⟨m - 2, by omega⟩ := by
  simp only [outTree]
  rw [dite_eq_left ⟨by omega, hm⟩]

theorem outTree_one : (outTree 1 : Edge k) = .stem := by
  simp [outTree]

theorem outPath_self : (outPath (2 ^ k) : Edge k) = .bottomTaxon := by
  simp [outPath]

theorem outPath_of_lt {m : ℕ} (hm : 2 ^ k < m) (hm' : m < 2 ^ (k + 1)) :
    (outPath m : Edge k) = .step ⟨m - 2 ^ k - 1, by have := two_pow_succ_eq k; omega⟩ := by
  have := two_pow_succ_eq k
  simp only [outPath]
  rw [dite_eq_left ⟨hm, by omega⟩]

/-- The arc leaving a node of the inverted subtree that isn't a 'leaf'. -/
theorem source_eq_inner_iff {m : ℕ} (h₁ : 1 ≤ m) (h₂ : m < 2 ^ k) (h₃ : m < 2 ^ (k + 1)) (e : Edge k) :
    (networkNk k a b c d).graph.source e = heapNode m h₁ h₃ ↔ e = outTree m := by
  have h4 := two_pow_succ_eq k
  have h5 := one_le_two_pow_k k
  by_cases hm : 2 ≤ m
  · rw [outTree_of_two_le hm h₃]
    cases e <;> simp [source_step, source_bottomTaxon, source_tree, source_stem, Fin.ext_iff] <;> omega
  · obtain rfl : m = 1 := by omega
    rw [outTree_one]
    have hk : k ≠ 0 := by
      rintro rfl
      simp at h₂
    cases e <;> simp [source_step, source_bottomTaxon, source_tree, source_stem, hk]

/-- The two arcs leaving a 'leaf' of the inverted subtree. -/
theorem source_eq_path_iff {m : ℕ} (h₁ : 1 ≤ m) (h₂ : 2 ^ k ≤ m) (h₃ : m < 2 ^ (k + 1)) (e : Edge k) :
    (networkNk k a b c d).graph.source e = heapNode m h₁ h₃ ↔ e = outTree m ∨ e = outPath m := by
  have h4 := two_pow_succ_eq k
  have h5 := one_le_two_pow_k k
  rcases Nat.lt_or_ge m 2 with hm | hm <;> rcases h₂.lt_or_eq with hm' | hm'
  · obtain rfl : m = 1 := by omega
    rw [outTree_one, outPath_of_lt hm' h₃]
    cases e <;> simp [source_step, source_bottomTaxon, source_tree, source_stem, Fin.ext_iff] <;> omega
  · subst hm'
    rw [show (outTree (2 ^ k) : Edge k) = .stem by
      have : 2 ^ k = 1 := by omega
      rw [this, outTree_one], outPath_self]
    cases e <;> simp [source_step, source_bottomTaxon, source_tree, source_stem] <;> omega
  · rw [outTree_of_two_le hm h₃, outPath_of_lt hm' h₃]
    cases e <;> simp [source_step, source_bottomTaxon, source_tree, source_stem, Fin.ext_iff] <;> omega
  · subst hm'
    rw [outTree_of_two_le hm h₃, outPath_self]
    cases e <;> simp [source_step, source_bottomTaxon, source_tree, source_stem, Fin.ext_iff] <;> omega

/-! ### The taxa -/

section Taxa

/-- The arcs entering a taxon. -/
theorem target_eq_taxon_iff (e : Edge k) (x : X) :
    (networkNk k a b c d).graph.target e = .taxon x ↔
      (e = .cherryLeft ∧ a = x) ∨ (e = .cherryRight ∧ b = x) ∨ (e = .bottomTaxon ∧ c = x) ∨ (e = .rootTaxon ∧ d = x) := by
  cases e with
  | rootTaxon => simp
  | rootTop => simp [target_rootTop, heapNode]
  | step t => simp [target_step, heapNode]
  | bottomTaxon => simp
  | tree m => simp [target_tree, heapNode]
  | stem => simp
  | cherryLeft => simp
  | cherryRight => simp

theorem source_ne_taxon (e : Edge k) (x : X) : (networkNk k a b c d).graph.source e ≠ .taxon x := by
  cases e with
  | rootTaxon => simp
  | rootTop => simp
  | step t => simp [source_step, heapNode]
  | bottomTaxon => simp [source_bottomTaxon, heapNode]
  | tree m => simp [source_tree, heapNode]
  | stem => simp [source_stem, heapNode]
  | cherryLeft => simp
  | cherryRight => simp

theorem target_ne_root (e : Edge k) : (networkNk k a b c d).graph.target e ≠ .root := by
  cases e with
  | rootTaxon => simp
  | rootTop => simp [target_rootTop, heapNode]
  | step t => simp [target_step, heapNode]
  | bottomTaxon => simp
  | tree m => simp [target_tree, heapNode]
  | stem => simp
  | cherryLeft => simp
  | cherryRight => simp

/-- A taxon reaches only itself. -/
theorem eq_of_taxon_reaches {x : X} {v : Vertex k X} (h : (networkNk k a b c d).graph.Reaches (.taxon x) v) :
    v = .taxon x := by
  induction h with
  | refl => rfl
  | tail _ hstep ih =>
    subst ih
    obtain ⟨e, he, -⟩ := hstep
    exact absurd he (source_ne_taxon e x)

end Taxa

/-! ### Definition 1 -/

section Degrees

private theorem ncard_eq_one_of_iff {α : Type*} {P : α → Prop} {e₀ : α} (h : ∀ e, P e ↔ e = e₀) :
    {e | P e}.ncard = 1 := by
  have : {e | P e} = {e₀} := Set.ext fun e => by simpa using h e
  rw [this, Set.ncard_singleton]

private theorem ncard_eq_two_of_iff {α : Type*} {P : α → Prop} {e₁ e₂ : α} (hne : e₁ ≠ e₂)
    (h : ∀ e, P e ↔ e = e₁ ∨ e = e₂) : {e | P e}.ncard = 2 := by
  have : {e | P e} = {e₁, e₂} := Set.ext fun e => by simpa using h e
  rw [this, Set.ncard_pair hne]

theorem indegree_root : (networkNk k a b c d).graph.indegree .root = 0 := by
  unfold DirectedMultigraph.indegree
  rw [Set.ncard_eq_zero]
  exact Set.eq_empty_iff_forall_notMem.2 fun e he => target_ne_root e he

theorem outdegree_root : (networkNk k a b c d).graph.outdegree .root = 2 := by
  unfold DirectedMultigraph.outdegree
  refine ncard_eq_two_of_iff (e₁ := Edge.rootTaxon) (e₂ := Edge.rootTop) (by simp) fun e => ?_
  cases e with
  | rootTaxon => simp
  | rootTop => simp
  | step t => simp [source_step, heapNode]
  | bottomTaxon => simp [source_bottomTaxon, heapNode]
  | tree m => simp [source_tree, heapNode]
  | stem => simp [source_stem, heapNode]
  | cherryLeft => simp
  | cherryRight => simp

theorem indegree_cherry : (networkNk k a b c d).graph.indegree .cherry = 1 := by
  unfold DirectedMultigraph.indegree
  refine ncard_eq_one_of_iff (e₀ := Edge.stem) fun e => ?_
  cases e with
  | rootTaxon => simp
  | rootTop => simp [target_rootTop, heapNode]
  | step t => simp [target_step, heapNode]
  | bottomTaxon => simp
  | tree m => simp [target_tree, heapNode]
  | stem => simp
  | cherryLeft => simp
  | cherryRight => simp

theorem outdegree_cherry : (networkNk k a b c d).graph.outdegree .cherry = 2 := by
  unfold DirectedMultigraph.outdegree
  refine ncard_eq_two_of_iff (e₁ := Edge.cherryLeft) (e₂ := Edge.cherryRight) (by simp) fun e => ?_
  cases e with
  | rootTaxon => simp
  | rootTop => simp
  | step t => simp [source_step, heapNode]
  | bottomTaxon => simp [source_bottomTaxon, heapNode]
  | tree m => simp [source_tree, heapNode]
  | stem => simp [source_stem, heapNode]
  | cherryLeft => simp
  | cherryRight => simp

theorem degrees_inner {m : ℕ} (h₁ : 1 ≤ m) (h₂ : m < 2 ^ k) (h₃ : m < 2 ^ (k + 1)) :
    (networkNk k a b c d).graph.indegree (heapNode m h₁ h₃) = 2 ∧
      (networkNk k a b c d).graph.outdegree (heapNode m h₁ h₃) = 1 :=
  ⟨ncard_eq_two_of_iff (leftArc_ne_rightArc m h₁ h₂) (target_eq_inner_iff h₁ h₂),
    ncard_eq_one_of_iff (source_eq_inner_iff h₁ h₂ h₃)⟩

theorem degrees_path {m : ℕ} (h₁ : 1 ≤ m) (h₂ : 2 ^ k ≤ m) (h₃ : m < 2 ^ (k + 1)) :
    (networkNk k a b c d).graph.indegree (heapNode m h₁ h₃) = 1 ∧
      (networkNk k a b c d).graph.outdegree (heapNode m h₁ h₃) = 2 :=
  ⟨ncard_eq_one_of_iff (target_eq_path_iff h₁ h₂ h₃),
    ncard_eq_two_of_iff (outTree_ne_outPath m) (source_eq_path_iff h₁ h₂ h₃)⟩

/-- The heap number of a node of the inverted subtree. -/
theorem heap_bounds (n : Fin (2 ^ (k + 1) - 1)) : 1 ≤ n.1 + 1 ∧ n.1 + 1 < 2 ^ (k + 1) := by
  have := n.2
  omega

variable [DecidableEq X] (hd : ({a, b, c, d} : Finset X).card = 4)
include hd

theorem indegree_taxon [Fintype X] (hX : Fintype.card X = 4) (x : X) :
    (networkNk k a b c d).graph.indegree (.taxon x) = 1 := by
  obtain ⟨hab, hac, had, hbc, hbd, hcd⟩ := ne_of_card_four hd
  have hall : x = a ∨ x = b ∨ x = c ∨ x = d := by
    have hu : ({a, b, c, d} : Finset X) = univ :=
      eq_univ_of_card _ (by rw [hd, hX])
    have := mem_univ x
    rw [← hu] at this
    simpa using this
  unfold DirectedMultigraph.indegree
  rcases hall with rfl | rfl | rfl | rfl
  · exact ncard_eq_one_of_iff (e₀ := Edge.cherryLeft) fun e => by
      rw [target_eq_taxon_iff]
      simp only [hab.symm, hac.symm, had.symm, and_false, or_false, and_true]
  · exact ncard_eq_one_of_iff (e₀ := Edge.cherryRight) fun e => by
      rw [target_eq_taxon_iff]
      simp only [hab, hbc.symm, hbd.symm, and_false, or_false, false_or, and_true]
  · exact ncard_eq_one_of_iff (e₀ := Edge.bottomTaxon) fun e => by
      rw [target_eq_taxon_iff]
      simp only [hac, hbc, hcd.symm, and_false, or_false, false_or, and_true]
  · exact ncard_eq_one_of_iff (e₀ := Edge.rootTaxon) fun e => by
      rw [target_eq_taxon_iff]
      simp only [had, hbd, hcd, and_false, false_or, and_true]

theorem exists_target_eq [Fintype X] (hX : Fintype.card X = 4) (v : Vertex k X) (hv : v ≠ .root) :
    ∃ e, (networkNk k a b c d).graph.target e = v := by
  obtain ⟨hab, hac, had, hbc, hbd, hcd⟩ := ne_of_card_four hd
  cases v with
  | root => exact absurd rfl hv
  | cherry => exact ⟨.stem, rfl⟩
  | heap n =>
    obtain ⟨h₁, h₃⟩ := heap_bounds n
    rw [heap_eq_heapNode]
    rcases Nat.lt_or_ge (n.1 + 1) (2 ^ k) with h | h
    · exact ⟨_, (target_eq_inner_iff h₁ h _).2 (Or.inl rfl)⟩
    · exact ⟨_, (target_eq_path_iff h₁ h h₃ _).2 rfl⟩
  | taxon x =>
    have hi := indegree_taxon (k := k) hd hX x
    obtain ⟨e, he⟩ := ((networkNk k a b c d).graph.one_le_indegree_iff (.taxon x)).1 (by omega)
    exact ⟨e, he⟩

/-- The root is above every node. -/
theorem root_reaches [Fintype X] (hX : Fintype.card X = 4) (v : Vertex k X) :
    (networkNk k a b c d).graph.Reaches .root v := by
  induction hn : 2 ^ (k + 1) + 1 - rk v using Nat.strong_induction_on generalizing v with
  | _ n ih =>
    by_cases hv : v = .root
    · subst hv
      exact .refl
    · obtain ⟨e, rfl⟩ := exists_target_eq hd hX v hv
      have hlt := rk_target_lt_rk_source (a := a) (b := b) (c := c) (d := d) e
      have hs := rk_le_root ((networkNk k a b c d).graph.source e)
      exact (ih _ (by omega) _ rfl).tail ⟨e, rfl, rfl⟩

/-- `𝒩(k)⁺` is a phylogenetic network. -/
theorem isPhylogenetic_networkNk [Fintype X] (hX : Fintype.card X = 4) : (networkNk k a b c d).IsPhylogenetic := by
  have : Finite X := Finite.of_fintype X
  refine ⟨inferInstance, inferInstance, inferInstance, isAcyclic_networkNk, root_reaches hd hX, indegree_root,
    fun v hv => ?_, fun x y h => Vertex.taxon.inj h, indegree_taxon hd hX, fun v => ⟨fun h0 => ?_, ?_⟩⟩
  · obtain ⟨e, he⟩ := exists_target_eq hd hX v hv
    exact ((networkNk k a b c d).graph.one_le_indegree_iff v).2 ⟨e, he⟩
  · cases v with
    | root =>
      rw [outdegree_root] at h0
      omega
    | cherry =>
      rw [outdegree_cherry] at h0
      omega
    | heap n =>
      obtain ⟨h₁, h₃⟩ := heap_bounds n
      rw [heap_eq_heapNode] at h0
      rcases Nat.lt_or_ge (n.1 + 1) (2 ^ k) with h | h
      · rw [(degrees_inner h₁ h h₃).2] at h0
        omega
      · rw [(degrees_path h₁ h h₃).2] at h0
        omega
    | taxon x => exact ⟨x, rfl⟩
  · rintro ⟨x, rfl⟩
    rw [DirectedMultigraph.outdegree, Set.ncard_eq_zero]
    exact Set.eq_empty_iff_forall_notMem.2 fun e he => source_ne_taxon e x he

omit [DecidableEq X] hd in
/-- `𝒩(k)⁺` is binary. -/
theorem isBinary_networkNk : (networkNk k a b c d).IsBinary := by
  refine ⟨outdegree_root, fun v hv h0 => ?_⟩
  cases v with
  | root => exact absurd rfl hv
  | cherry =>
    rw [indegree_cherry, outdegree_cherry]
  | heap n =>
    obtain ⟨h₁, h₃⟩ := heap_bounds n
    rw [heap_eq_heapNode]
    rcases Nat.lt_or_ge (n.1 + 1) (2 ^ k) with h | h
    · rw [(degrees_inner h₁ h h₃).1, (degrees_inner h₁ h h₃).2]
    · rw [(degrees_path h₁ h h₃).1, (degrees_path h₁ h h₃).2]
  | taxon x =>
    exfalso
    apply h0
    rw [DirectedMultigraph.outdegree, Set.ncard_eq_zero]
    exact Set.eq_empty_iff_forall_notMem.2 fun e he => source_ne_taxon e x he

end Degrees

/-! ### The parameters -/

section Metric

variable [Fintype X] [DecidableEq X] (hd : ({a, b, c, d} : Finset X).card = 4) (hX : Fintype.card X = 4)

theorem target_tree_inner (m : Fin (2 ^ (k + 1) - 2)) : (m.1 + 2) / 2 < 2 ^ k := by
  have := m.2
  have := two_pow_succ_eq k
  omega

include hd hX in
/-- Only the arcs of the inverted subtree are hybrid arcs. -/
theorem isHybridArc_iff (e : Edge k) : (networkNk k a b c d).IsHybridArc e ↔ ∃ m, e = .tree m := by
  have hk := two_le_two_pow_succ k
  have hpath : ∀ {m : ℕ} (h₁ : 1 ≤ m) (h₂ : 2 ^ k ≤ m) (h₃ : m < 2 ^ (k + 1)),
      ¬ 2 ≤ (networkNk k a b c d).graph.indegree (heapNode m h₁ h₃) := fun h₁ h₂ h₃ => by
    rw [(degrees_path h₁ h₂ h₃).1]
    omega
  have htaxon : ∀ x : X, ¬ 2 ≤ (networkNk k a b c d).graph.indegree (.taxon x) := fun x => by
    rw [indegree_taxon hd hX]
    omega
  unfold IsHybridArc
  cases e with
  | rootTaxon => simpa using htaxon d
  | rootTop =>
    rw [target_rootTop]
    simpa using hpath _ (by have := two_pow_succ_eq k; have := one_le_two_pow_k k; omega) _
  | step t =>
    rw [target_step]
    simpa using hpath _ (by omega) _
  | bottomTaxon => simpa using htaxon c
  | tree m =>
    rw [target_tree, (degrees_inner _ (target_tree_inner m) _).1]
    simp
  | stem =>
    simp only [target_stem, indegree_cherry]
    simp
  | cherryLeft => simpa using htaxon a
  | cherryRight => simpa using htaxon b

include hd hX in
/-- The lengths of `𝒩(k)⁺` are valid numerical parameters of Definition 3, for `ε, M > 0`. -/
theorem isMetric_metricNk {ε M : ℝ} (hε : 0 < ε) (hM : 0 < M) :
    (networkNk k a b c d).IsMetric (metricNk k ε M) := by
  have hpow : (0 : ℝ) ≤ 2 ^ k - 1 := sub_nonneg.2 (one_le_pow₀ (by norm_num))
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have htree : ∀ e, (networkNk k a b c d).IsTreeArc e → ∀ m, e ≠ .tree m := by
    rintro e he m rfl
    have := (isHybridArc_iff hd hX (.tree m : Edge k)).2 ⟨m, rfl⟩
    unfold IsHybridArc at this
    unfold IsTreeArc at he
    omega
  refine ⟨fun e he => ?_, fun e he => ?_, fun e he => ?_, fun e he => ?_, fun v hv => ?_⟩
  · cases e with
    | rootTaxon => simp only [metricNk]; positivity
    | rootTop => simp [metricNk]
    | step t => simpa [metricNk] using hM
    | bottomTaxon => simp only [metricNk]; positivity
    | tree m => exact absurd rfl (htree _ he m)
    | stem => simpa [metricNk] using hε
    | cherryLeft => simp [metricNk]
    | cherryRight => simp [metricNk]
  · obtain ⟨m, rfl⟩ := (isHybridArc_iff hd hX e).1 he
    simp only [metricNk]
    split_ifs <;> positivity
  · cases e with
    | tree m => exact absurd rfl (htree _ he m)
    | _ => rfl
  · obtain ⟨m, rfl⟩ := (isHybridArc_iff hd hX e).1 he
    simp [metricNk]
  · have hv' : ∃ (m : ℕ) (h₁ : 1 ≤ m) (h₂ : m < 2 ^ k) (h₃ : m < 2 ^ (k + 1)), v = heapNode m h₁ h₃ := by
      cases v with
      | root =>
        rw [indegree_root] at hv
        omega
      | cherry =>
        rw [indegree_cherry] at hv
        omega
      | heap n =>
        obtain ⟨h₁, h₃⟩ := heap_bounds n
        rcases Nat.lt_or_ge (n.1 + 1) (2 ^ k) with h | h
        · exact ⟨_, h₁, h, h₃, heap_eq_heapNode n⟩
        · rw [heap_eq_heapNode, (degrees_path h₁ h h₃).1] at hv
          omega
      | taxon x =>
        rw [indegree_taxon hd hX] at hv
        omega
    obtain ⟨m, h₁, h₂, h₃, rfl⟩ := hv'
    rw [Finset.sum_eq_add (leftArc m h₁ h₂) (rightArc m h₁ h₂) (leftArc_ne_rightArc m h₁ h₂)]
    · rw [ite_eq_left ((target_eq_inner_iff h₁ h₂ _).2 (Or.inl rfl)), ite_eq_left ((target_eq_inner_iff h₁ h₂ _).2 (Or.inr rfl))]
      simp only [leftArc, rightArc, metricNk]
      norm_num
    · rintro e - ⟨h4, h5⟩
      refine ite_eq_right fun h6 => ?_
      rcases (target_eq_inner_iff h₁ h₂ _).1 h6 with h7 | h7
      · exact absurd h7 h4
      · exact absurd h7 h5
    · exact fun h => absurd (mem_univ _) h
    · exact fun h => absurd (mem_univ _) h

end Metric

/-! ### What is below the nodes -/

section Below

/-- The nodes whose lineages can only be those of `a` and `b`. -/
def IsLow (a b : X) : Vertex k X → Prop
  | .root => False
  | .cherry => True
  | .heap n => n.1 + 1 < 2 ^ k
  | .taxon x => x = a ∨ x = b

/-- What is below a node above only `a` and `b` is above only `a` and `b`. -/
theorem IsLow.of_reaches {u v : Vertex k X} (h : (networkNk k a b c d).graph.Reaches u v) (hu : IsLow a b u) :
    IsLow a b v := by
  induction h with
  | refl => exact hu
  | tail _ hstep ih =>
    obtain ⟨e, rfl, rfl⟩ := hstep
    cases e with
    | rootTaxon => exact ih.elim
    | rootTop => exact ih.elim
    | step t =>
      have hs := source_step (a := a) (b := b) (c := c) (d := d) t
      rw [hs] at ih
      simp only [heapNode, IsLow] at ih
      omega
    | bottomTaxon =>
      rw [source_bottomTaxon] at ih
      simp only [heapNode, IsLow] at ih
      have := one_le_two_pow_k k
      omega
    | tree m =>
      rw [target_tree]
      rw [source_tree] at ih
      simp only [heapNode, IsLow] at ih ⊢
      omega
    | stem => exact trivial
    | cherryLeft => exact Or.inl rfl
    | cherryRight => exact Or.inr rfl

/-- The arcs of the inverted subtree and the stem end in nodes above only `a` and `b`. -/
theorem isLow_target_tree (m : Fin (2 ^ (k + 1) - 2)) :
    IsLow (k := k) a b ((networkNk k a b c d).graph.target (.tree m)) := by
  rw [target_tree]
  simp only [heapNode, IsLow]
  have := target_tree_inner m
  omega

theorem taxon_mem_of_isLow {x : X} (h : IsLow (k := k) a b (.taxon x)) : x = a ∨ x = b := h

/-- Only the root and `d` itself reach `d`, if `d` is not `a`, `b` or `c`. -/
theorem eq_of_reaches_taxon_d (had : a ≠ d) (hbd : b ≠ d) (hcd : c ≠ d) {u : Vertex k X}
    (h : (networkNk k a b c d).graph.Reaches u (.taxon d)) : u = .taxon d ∨ u = .root := by
  rcases Relation.ReflTransGen.cases_tail h with h' | ⟨w, hw, e, rfl, he⟩
  · exact Or.inl h'.symm
  · have he' : e = .rootTaxon := by
      rcases (target_eq_taxon_iff e d).1 he with ⟨-, h1⟩ | ⟨-, h1⟩ | ⟨-, h1⟩ | ⟨h0, -⟩
      · exact absurd h1 had
      · exact absurd h1 hbd
      · exact absurd h1 hcd
      · exact h0
    subst he'
    rcases Relation.ReflTransGen.cases_tail hw with h' | ⟨w', -, f, -, hf⟩
    · exact Or.inr h'.symm
    · exact absurd hf (target_ne_root f)

end Below

/-! ### The stem -/

section Stem

variable [Fintype X] [DecidableEq X] (hd : ({a, b, c, d} : Finset X).card = 4)

/-- The side of the stem. -/
def stemSide (a b : X) : Set (Vertex k X) := {.cherry, .taxon a, .taxon b}

omit [Fintype X] [DecidableEq X] in
@[simp] theorem mem_stemSide {v : Vertex k X} : v ∈ stemSide a b ↔ v = .cherry ∨ v = .taxon a ∨ v = .taxon b := by
  simp [stemSide]

omit [Fintype X] in
include hd in
/-- The stem is the only arc crossing its side. -/
theorem crosses_stemSide_iff (f : Edge k) :
    (networkNk k a b c d).graph.Crosses f (stemSide a b) ↔ f = .stem := by
  obtain ⟨hab, hac, had, hbc, hbd, hcd⟩ := ne_of_card_four hd
  unfold DirectedMultigraph.Crosses
  cases f <;> simp [source_step, source_bottomTaxon, source_tree, source_stem, target_rootTop, target_step, target_tree, heapNode, hac.symm,
    had.symm, hbc.symm, hbd.symm]

omit [Fintype X] in
include hd in
/-- **The stem is a cut edge** with the split `ab|cd`. -/
theorem hasCutSplit_stem : (networkNk k a b c d).HasCutSplit ((({a, b} : Finset X) : Set X)) := by
  refine ⟨.stem, stemSide a b, crosses_stemSide_iff hd, ?_⟩
  ext x
  simp [networkNk]

include hd in
/-- `𝒩(k)⁺` displays `ab|cd`. -/
theorem displays_treeOfBlobs_networkNk :
    Displays (treeOfBlobs (networkNk k a b c d)) (quartetTree a b c d hd) := by
  obtain ⟨hab, hac, had, hbc, hbd, hcd⟩ := ne_of_card_four hd
  refine ⟨{a, b}, ?_, ?_⟩
  · rw [mem_treeOfBlobs_iff]
    refine ⟨⟨a, by simp⟩, ⟨c, by simp [hac.symm, hbc.symm]⟩, hasCutSplit_stem hd⟩
  · have hsub : ({a, b} : Finset X) ⊆ (quartetTree a b c d hd).taxa := by
      rw [quartetTree_taxa]
      intro x hx
      simp only [mem_insert, mem_singleton] at hx ⊢
      tauto
    rw [inter_eq_left.2 hsub]
    simp [quartetTree]

omit [Fintype X] in
include hd in
/-- A path off the stem from outside its side stays outside. -/
theorem notMem_stemSide_of_reachesOff {u v : Vertex k X}
    (h : (networkNk k a b c d).ReachesOff (insert Edge.stem ∅) u v) (hu : u ∉ stemSide a b) : v ∉ stemSide a b := by
  induction h with
  | refl => exact hu
  | tail _ hstep ih =>
    obtain ⟨f, hf, rfl, rfl⟩ := hstep
    intro hmem
    exact hf ((crosses_stemSide_iff hd f).1 (Or.inr ⟨hmem, ih⟩) ▸ Set.mem_insert _ _)

omit [Fintype X] in
include hd in
/-- The stem splits `ab|cd`: it dominates `a` and `b`, and neither `c` nor `d` is below it. -/
theorem splitOffAt_stem [Fintype X] : (networkNk k a b c d).SplitOffAt ∅ .stem (quartetTree a b c d hd) := by
  refine ⟨{a, b}, by simp [quartetTree], fun x hx => ?_, fun x hx => ?_⟩
  · intro hr
    have hx' : x = a ∨ x = b := by simpa using hx
    refine notMem_stemSide_of_reachesOff hd hr (u := .root) (by simp) ?_
    rcases hx' with rfl | rfl <;> simp [networkNk]
  · rintro ⟨-, hr⟩
    have hx' : x ∉ ({a, b} : Finset X) := (mem_sdiff.1 (mem_coe.1 hx)).2
    have hr' := reachesOff_empty_iff.1 hr
    have hlow : IsLow (k := k) a b (.taxon x) := IsLow.of_reaches hr' trivial
    rcases hlow with rfl | rfl <;> simp at hx'

end Stem

/-! ### "We make the network ultrametric" -/

section Ultrametric

/-- The height of a node of `𝒩(k)⁺` above the taxa, in coalescent units. -/
def heightNk (k : ℕ) (ε M : ℝ) : Vertex k X → ℝ
  | .root => 2 + (k + 1) * ε + (2 ^ k - 1) * M
  | .cherry => 1
  | .heap n => 1 + ((Nat.log 2 (n.1 + 1) + 1 : ℕ) : ℝ) * ε + ((n.1 + 1 - 2 ^ k : ℕ) : ℝ) * M
  | .taxon _ => 0

theorem heightNk_heapNode {ε M : ℝ} {m : ℕ} {h₁ h₂} :
    heightNk k ε M (heapNode m h₁ h₂ : Vertex k X) = 1 + ((Nat.log 2 m + 1 : ℕ) : ℝ) * ε + ((m - 2 ^ k : ℕ) : ℝ) * M := by
  simp only [heapNode, heightNk]
  rw [Nat.sub_add_cancel h₁]

/-- **"We make the network ultrametric"**: the taxa have height 0, and each arc goes down by its length. -/
theorem heightNk_source (ε M : ℝ) (e : Edge k) :
    heightNk k ε M ((networkNk k a b c d).graph.source e) =
      heightNk k ε M ((networkNk k a b c d).graph.target e) + (metricNk k ε M).length e := by
  have h1 := one_le_two_pow_k k
  have h2 := two_pow_succ_eq k
  have hlog : ∀ {m : ℕ}, 2 ^ k ≤ m → m < 2 ^ (k + 1) → Nat.log 2 m = k := fun h h' =>
    Nat.log_eq_of_pow_le_of_lt_pow h h'
  cases e with
  | rootTaxon =>
    simp only [source_rootTaxon, target_rootTaxon, heightNk, metricNk]
    ring
  | rootTop =>
    rw [source_rootTop, target_rootTop, heightNk_heapNode, hlog (by omega) (by omega)]
    have h3 : ((2 ^ (k + 1) - 1 - 2 ^ k : ℕ) : ℝ) = 2 ^ k - 1 := by
      rw [show 2 ^ (k + 1) - 1 - 2 ^ k = 2 ^ k - 1 by omega, Nat.cast_sub h1]
      simp
    rw [h3]
    simp only [heightNk, metricNk]
    push_cast
    ring
  | step t =>
    have ht := t.2
    rw [source_step, target_step, heightNk_heapNode, heightNk_heapNode, hlog (by omega) (by omega), hlog (by omega) (by omega),
      show 2 ^ k + t.1 + 1 - 2 ^ k = t.1 + 1 by omega, show 2 ^ k + t.1 - 2 ^ k = t.1 by omega]
    simp only [metricNk]
    push_cast
    ring
  | bottomTaxon =>
    rw [source_bottomTaxon, heightNk_heapNode, hlog le_rfl (by omega), Nat.sub_self]
    simp only [target_bottomTaxon, heightNk, metricNk]
    push_cast
    ring
  | tree m =>
    have hm := m.2
    rw [source_tree, target_tree, heightNk_heapNode, heightNk_heapNode,
      Nat.log_of_one_lt_of_le (b := 2) (n := m.1 + 2) (by norm_num) (by omega), show (m.1 + 2) / 2 - 2 ^ k = 0 by omega]
    simp only [metricNk]
    split_ifs with h
    · rw [show m.1 + 2 - 2 ^ k = 0 by omega]
      push_cast
      ring
    · push_cast
      ring
  | stem =>
    rw [source_stem, heightNk_heapNode, show 1 - 2 ^ k = 0 by omega]
    simp only [target_stem, heightNk, metricNk, Nat.log_one_right]
    push_cast
    ring
  | cherryLeft =>
    simp [heightNk, metricNk]
  | cherryRight =>
    simp [heightNk, metricNk]

end Ultrametric

/-! ### "A 3-blob" -/

section ThreeBlob

variable [Fintype X] [DecidableEq X] (hd : ({a, b, c, d} : Finset X).card = 4) (hX : Fintype.card X = 4)

include hd hX in
/-- An arc of the inverted subtree is not a cut edge: it has a sibling. -/
theorem not_isBridge_tree (m : Fin (2 ^ (k + 1) - 2)) : ¬ (networkNk k a b c d).graph.underlying.IsBridge (.tree m) := by
  have hN := isPhylogenetic_networkNk (k := k) hd hX
  have hmm := m.2
  have h2 := two_pow_succ_eq k
  have hin := target_tree_inner m
  have h₁ : 1 ≤ (m.1 + 2) / 2 := by omega
  have ht := (target_eq_inner_iff (a := a) (b := b) (c := c) (d := d) h₁ hin (h₃ := by omega) (.tree m)).1 (target_tree m)
  have hL := (target_eq_inner_iff (a := a) (b := b) (c := c) (d := d) h₁ hin (h₃ := by omega) (leftArc _ h₁ hin)).2 (Or.inl rfl)
  have hR := (target_eq_inner_iff (a := a) (b := b) (c := c) (d := d) h₁ hin (h₃ := by omega) (rightArc _ h₁ hin)).2 (Or.inr rfl)
  rcases ht with h | h
  · refine not_isBridge_of_two_parents hN (g := rightArc _ h₁ hin) (h ▸ leftArc_ne_rightArc _ h₁ hin) ?_
    rw [h, hL, hR]
  · refine not_isBridge_of_two_parents hN (g := leftArc _ h₁ hin) (h ▸ (leftArc_ne_rightArc _ h₁ hin).symm) ?_
    rw [h, hL, hR]

/-- Each node of the inverted subtree is joined to its 'root' by arcs of the subtree. -/
theorem walks_heapNode_one {m : ℕ} (h₁ : 1 ≤ m) (h₂ : m < 2 ^ (k + 1)) :
    (networkNk k a b c d).graph.Walks {e | ∃ m', e = Edge.tree m'} (heapNode m h₁ h₂)
      (heapNode 1 le_rfl (by have := two_le_two_pow_succ k; omega)) := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    by_cases hm : m = 1
    · subst hm
      exact .refl
    · have h3 : m - 2 < 2 ^ (k + 1) - 2 := by omega
      have hadj : (networkNk k a b c d).graph.AdjOn {e | ∃ m', e = Edge.tree m'} (heapNode m h₁ h₂) (heapNode (m / 2) (by omega) (by omega)) := by
        refine ⟨.tree ⟨m - 2, h3⟩, ⟨_, rfl⟩, Or.inl ⟨?_, ?_⟩⟩
        · rw [source_tree, heapNode_inj]
          simp only
          omega
        · rw [target_tree, heapNode_inj]
          simp only
          congr 1
          omega
      exact Relation.ReflTransGen.head hadj (ih (m / 2) (by omega) (by omega) (by omega))

/-- A step of the path is not a cut edge: its ends are joined through the inverted subtree. -/
theorem not_isBridge_step (t : Fin (2 ^ k - 1)) : ¬ (networkNk k a b c d).graph.underlying.IsBridge (.step t) := by
  rw [DirectedMultigraph.isBridge_iff_not_walks_delete, not_not]
  have hsub : {e : Edge k | ∃ m', e = Edge.tree m'} ⊆ ({Edge.step t}ᶜ : Set (Edge k)) := by
    rintro e ⟨m', rfl⟩
    simp
  have hmono : ∀ {u v : Vertex k X}, (networkNk k a b c d).graph.Walks {e | ∃ m', e = Edge.tree m'} u v →
      (networkNk k a b c d).graph.Walks ({Edge.step t}ᶜ : Set (Edge k)) u v := fun h =>
    Relation.ReflTransGen.mono (fun _ _ ⟨e, he, hh⟩ => ⟨e, hsub he, hh⟩) _ _ h
  have ht := t.2
  have h1k := one_le_two_pow_k k
  have h2k := two_pow_succ_eq k
  rw [source_step, target_step]
  have hu : 1 ≤ 2 ^ k + t.1 + 1 := by omega
  have hu' : 2 ^ k + t.1 + 1 < 2 ^ (k + 1) := by omega
  have hw : 1 ≤ 2 ^ k + t.1 := by omega
  have hw' : 2 ^ k + t.1 < 2 ^ (k + 1) := by omega
  exact (hmono (walks_heapNode_one hu hu')).trans ((networkNk k a b c d).graph.walks_symm (hmono (walks_heapNode_one hw hw')))

include hd hX in
/-- **The nodes of the inverted subtree are in one blob.** -/
theorem blobOf_heapNode {m : ℕ} (h₁ : 1 ≤ m) (h₂ : m < 2 ^ (k + 1)) :
    blobOf (networkNk k a b c d).graph (heapNode m h₁ h₂) =
      blobOf (networkNk k a b c d).graph (heapNode 1 le_rfl (by have := two_le_two_pow_succ k; omega)) := by
  apply Quotient.sound
  have hw : (networkNk k a b c d).graph.Walks {e | ¬ (networkNk k a b c d).graph.underlying.IsBridge e} (heapNode m h₁ h₂)
      (heapNode 1 le_rfl (by have := two_le_two_pow_succ k; omega)) := by
    have hstep : ∀ u v : Vertex k X, (networkNk k a b c d).graph.AdjOn {e | ∃ m', e = Edge.tree m'} u v →
        (networkNk k a b c d).graph.AdjOn {e | ¬ (networkNk k a b c d).graph.underlying.IsBridge e} u v := by
      rintro u v ⟨e, ⟨m', rfl⟩, hh⟩
      exact ⟨_, not_isBridge_tree hd hX m', hh⟩
    exact Relation.ReflTransGen.mono hstep _ _ (walks_heapNode_one h₁ h₂)
  exact hw

omit [Fintype X] [DecidableEq X] in
/-- A cut edge with a side `S`: the blobs don't cross it. -/
theorem blobOf_ne_of_side {e : Edge k} {S : Set (Vertex k X)} (hS : ∀ f, (networkNk k a b c d).graph.Crosses f S ↔ f = e) {u v : Vertex k X}
    (hu : u ∈ S) (hv : v ∉ S) : blobOf (networkNk k a b c d).graph u ≠ blobOf (networkNk k a b c d).graph v := by
  intro h
  have hw : (networkNk k a b c d).graph.Walks {f | ¬ (networkNk k a b c d).graph.underlying.IsBridge f} u v := Quotient.exact h
  have hno : ∀ f ∈ {f | ¬ (networkNk k a b c d).graph.underlying.IsBridge f}, ¬ (networkNk k a b c d).graph.Crosses f S := by
    intro f hf hc
    refine hf ?_
    rw [(hS f).1 hc]
    exact ((networkNk k a b c d).graph.isBridge_iff e).2 ⟨S, hS⟩
  exact hv (((networkNk k a b c d).graph.mem_iff_mem_of_walks hno hw).1 hu)

/-- The side of the arc from the root to the blob. -/
def rootSide (d : X) : Set (Vertex k X) := {.root, .taxon d}

/-- The side of the arc to `c`. -/
def cSide (c : X) : Set (Vertex k X) := {.taxon c}

omit [Fintype X] in
include hd in
theorem crosses_rootSide_iff (f : Edge k) : (networkNk k a b c d).graph.Crosses f (rootSide d) ↔ f = .rootTop := by
  obtain ⟨hab, hac, had, hbc, hbd, hcd⟩ := ne_of_card_four hd
  unfold DirectedMultigraph.Crosses rootSide
  cases f <;> simp [source_step, source_bottomTaxon, source_tree, source_stem, target_rootTop, target_step, target_tree, heapNode, had, hbd, hcd]

omit [Fintype X] in
include hd in
theorem crosses_cSide_iff (f : Edge k) : (networkNk k a b c d).graph.Crosses f (cSide c) ↔ f = .bottomTaxon := by
  obtain ⟨hab, hac, had, hbc, hbd, hcd⟩ := ne_of_card_four hd
  unfold DirectedMultigraph.Crosses cSide
  cases f <;> simp [source_step, source_bottomTaxon, source_tree, source_stem, target_rootTop, target_step, target_tree, heapNode, hac, hbc, hcd.symm]

include hd hX in
/-- **"Edges lead from the root to the taxon `d` and to a 3-blob. The other two edges incident to the 3-blob lead to `c`, and to a cherry of `a, b`"**: the cut edges incident to the blob of the inverted subtree. -/
theorem incidentCutEdges_blobNk :
    incidentCutEdges (networkNk k a b c d).graph (blobOf (networkNk k a b c d).graph (heapNode 1 le_rfl (by have := two_le_two_pow_succ k; omega))) =
      {.rootTop, .bottomTaxon, .stem} := by
  have h1k := one_le_two_pow_k k
  have h2k := two_pow_succ_eq k
  set B := blobOf (networkNk k a b c d).graph (heapNode 1 le_rfl (by have := two_le_two_pow_succ k; omega)) with hB
  have hheap : ∀ {m : ℕ} (h₁ : 1 ≤ m) (h₂ : m < 2 ^ (k + 1)), blobOf (networkNk k a b c d).graph (heapNode m h₁ h₂) = B := fun h₁ h₂ =>
    blobOf_heapNode hd hX h₁ h₂
  have h1top : 1 < 2 ^ (k + 1) := by omega
  have hrootNe : ∀ {v : Vertex k X}, v ∈ rootSide (k := k) d → blobOf (networkNk k a b c d).graph v ≠ B := fun hv =>
    blobOf_ne_of_side (crosses_rootSide_iff hd) hv (by simp [rootSide, heapNode])
  have hcNe : blobOf (networkNk k a b c d).graph (.taxon c) ≠ B :=
    blobOf_ne_of_side (crosses_cSide_iff hd) (by simp [cSide]) (by simp [cSide, heapNode])
  have hstemNe : ∀ {v : Vertex k X}, v ∈ stemSide (k := k) a b → blobOf (networkNk k a b c d).graph v ≠ B := fun hv =>
    blobOf_ne_of_side (crosses_stemSide_iff hd) hv (by simp [heapNode])
  have hbridge : ∀ {e : Edge k} {S : Set (Vertex k X)}, (∀ f, (networkNk k a b c d).graph.Crosses f S ↔ f = e) → (networkNk k a b c d).graph.underlying.IsBridge e :=
    fun hS => ((networkNk k a b c d).graph.isBridge_iff _).2 ⟨_, hS⟩
  ext e
  simp only [incidentCutEdges, IsIncidentToBlob, Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
  cases e with
  | rootTaxon =>
    simp only [reduceCtorEq, or_self, iff_false, not_and, source_rootTaxon, target_rootTaxon]
    intro _
    have h1 := hrootNe (v := .root) (by simp [rootSide])
    have h2 := hrootNe (v := .taxon d) (by simp [rootSide])
    simp [Xor, h1, h2]
  | rootTop =>
    simp only [true_or, iff_true]
    refine ⟨hbridge (crosses_rootSide_iff hd), ?_⟩
    rw [source_rootTop, target_rootTop, hheap]
    have h1 := hrootNe (v := .root) (by simp [rootSide])
    simp [Xor, h1]
  | step t =>
    simp only [reduceCtorEq, or_self, iff_false, not_and]
    exact fun h => absurd h (not_isBridge_step t)
  | bottomTaxon =>
    simp only [reduceCtorEq, true_or, or_true, iff_true]
    refine ⟨hbridge (crosses_cSide_iff hd), ?_⟩
    rw [source_bottomTaxon, target_bottomTaxon, hheap]
    simp [Xor, hcNe]
  | tree m =>
    simp only [reduceCtorEq, or_self, iff_false, not_and]
    exact fun h => absurd h (not_isBridge_tree hd hX m)
  | stem =>
    simp only [or_true, iff_true]
    refine ⟨hbridge (crosses_stemSide_iff hd), ?_⟩
    rw [source_stem, target_stem]
    have h1 := hstemNe (v := .cherry) (by simp)
    have h2 : blobOf (networkNk k a b c d).graph (heapNode 1 le_rfl (by omega)) = B := rfl
    simp only [Xor, h2, h1, and_true, not_false_eq_true, true_or]
  | cherryLeft =>
    simp only [reduceCtorEq, or_self, iff_false, not_and, source_cherryLeft, target_cherryLeft]
    intro _
    have h1 := hstemNe (v := .cherry) (by simp)
    have h2 := hstemNe (v := .taxon a) (by simp)
    simp [Xor, h1, h2]
  | cherryRight =>
    simp only [reduceCtorEq, or_self, iff_false, not_and, source_cherryRight, target_cherryRight]
    intro _
    have h1 := hstemNe (v := .cherry) (by simp)
    have h2 := hstemNe (v := .taxon b) (by simp)
    simp [Xor, h1, h2]

include hd hX in
/-- **`𝒩(k)⁺` has a 3-blob**: the blob of the inverted subtree, which doesn't contain the root, has degree 3. For `k ≥ 1` it isn't trivial (`not_isTrivialBlob_blobNk`). -/
theorem blobDegree_blobNk :
    blobDegree (networkNk k a b c d) (blobOf (networkNk k a b c d).graph (heapNode 1 le_rfl (by have := two_le_two_pow_succ k; omega))) = 3 := by
  have hroot : blobOf (networkNk k a b c d).graph (networkNk k a b c d).root ≠
      blobOf (networkNk k a b c d).graph (heapNode 1 le_rfl (by have := two_le_two_pow_succ k; omega)) :=
    blobOf_ne_of_side (crosses_rootSide_iff hd) (by simp [rootSide, networkNk]) (by simp [rootSide, heapNode])
  unfold blobDegree cutDegree
  rw [ite_eq_right hroot, incidentCutEdges_blobNk hd hX, Set.ncard_insert_of_notMem (by simp), Set.ncard_pair (by simp)]

include hd hX in
/-- The 3-blob has more than one node, for `k ≥ 1`. -/
theorem not_isTrivialBlob_blobNk (hk : 1 ≤ k) :
    ¬ IsTrivialBlob (networkNk k a b c d).graph (blobOf (networkNk k a b c d).graph (heapNode 1 le_rfl (by have := two_le_two_pow_succ k; omega))) := by
  rintro ⟨v, hv⟩
  have h2k := two_pow_succ_eq k
  have h4 : 2 ≤ 2 ^ k := by
    calc 2 = 2 ^ 1 := rfl
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
  have h1 : (heapNode 1 le_rfl (by omega) : Vertex k X) ∈ blobNodes (networkNk k a b c d).graph
      (blobOf (networkNk k a b c d).graph (heapNode 1 le_rfl (by omega))) := rfl
  have h2 : (heapNode 2 (by omega) (by omega) : Vertex k X) ∈ blobNodes (networkNk k a b c d).graph
      (blobOf (networkNk k a b c d).graph (heapNode 1 le_rfl (by omega))) := blobOf_heapNode hd hX _ _
  rw [hv] at h1 h2
  have h3 := (Set.mem_singleton_iff.1 h1).trans (Set.mem_singleton_iff.1 h2).symm
  rw [heapNode_inj] at h3
  omega

end ThreeBlob

end AllmanEtAl2023.NetworkNk
