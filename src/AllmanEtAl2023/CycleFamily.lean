module

public import AllmanEtAl2023.Figure1
public import AllmanEtAl2023.TreeBlobs

/-!
# Allman, Baños, Mitchell, Rhodes 2023: a blob of every degree, and what happens to it on induced networks

"Non-tree phylogenetic networks may have `k`-blobs that are not nodes for any `k > 1`" (after Definition 7), and "In passing from a network to an induced network on fewer taxa, blobs may split into smaller blobs, and in some cases reduce to tree-like relationships. Indeed, this happens even in the level-1 case with a single cycle of `k` edges, `k ≥ 5`" (after Definition 13).

`cycleNet j` is one family for both: a root with a taxon `y` and an edge to the top `t` of a cycle of `j + 2` edges, a direct edge from `t` to the hybrid node `h`, and on the other side a path through `p_{j-1}, …, p_0`, each `p_i` with a taxon `x_i`, down to `h`, which has a taxon `z`.

* `isBinaryNetwork_cycleNet`.
* `isBridge_iff`, `blobOf_eq_iff`: the cut edges and the blobs.
* `exists_kBlob`: a non-trivial `k`-blob, for every `k > 1`.
* `isLevelOne_cycleNet`, `ncard_not_isBridge`: the network is level-1 in the library's sense, with one cycle of `j + 2` edges.
* `cycleNet_b_to_t`: for `j ≥ 3`, so `k ≥ 5`, `{x₀, x₁, x₂, y}` is a B-quartet on the network and not on the network it induces.
-/

@[expose] public noncomputable section

open Phylogenetics Phylogenetics.RootedNetwork Phylogenetics.DirectedMultigraph
open scoped Classical

namespace AllmanEtAl2023.CycleFamily

open InPassing FigureCheck BlobStructure

/-! ### The network

The taxa are numbered: `x_i = i` for `i < j`, `z = j`, `y = j + 1`. The node `h` is `j + 2`, `p_i` is `j + 3 + i`, `t` is `2 j + 3`, the root is `2 j + 4`. So the path is the nodes `j + 2, …, 2 j + 3`, and the edge `i < 2 j + 4` is the one that enters the node `i`. The last edge is the direct edge from `t` to `h`. -/

variable (j : ℕ)

/-- The targets of the edges. -/
def tgtC (e : Fin (2 * j + 5)) : Fin (2 * j + 5) := ⟨if e.1 = 2 * j + 4 then j + 2 else e.1, by have := e.2; split_ifs <;> omega⟩

/-- The sources of the edges. -/
def srcC (e : Fin (2 * j + 5)) : Fin (2 * j + 5) :=
  ⟨if e.1 = 2 * j + 4 then 2 * j + 3 else if e.1 < j then j + 3 + e.1 else if e.1 = j then j + 2 else if e.1 = j + 1 then 2 * j + 4 else e.1 + 1, by
    have := e.2
    split_ifs <;> omega⟩

/-- The root. -/
def rootC : Fin (2 * j + 5) := ⟨2 * j + 4, by omega⟩

/-- The taxa. -/
def leafC : Fin (j + 2) → Fin (2 * j + 5) := Fin.castLE (by omega)

/-- **The network with one cycle of `j + 2` edges.** -/
def cycleNet : RootedNetwork (Fin (2 * j + 5)) (Fin (2 * j + 5)) (Fin (j + 2)) := finNetwork (srcC j) (tgtC j) (rootC j) (leafC j)

variable {j}

theorem tgtC_val (e : Fin (2 * j + 5)) : (tgtC j e).1 = if e.1 = 2 * j + 4 then j + 2 else e.1 := rfl

theorem srcC_val (e : Fin (2 * j + 5)) :
    (srcC j e).1 = if e.1 = 2 * j + 4 then 2 * j + 3 else if e.1 < j then j + 3 + e.1 else if e.1 = j then j + 2 else if e.1 = j + 1 then 2 * j + 4 else e.1 + 1 := rfl

theorem leafC_val (x : Fin (j + 2)) : (leafC j x).1 = x.1 := rfl

/-- **The network is a rooted binary phylogenetic network.** -/
theorem isBinaryNetwork_cycleNet : IsBinaryNetwork (cycleNet j) := by
  refine isBinaryNetwork_finNetwork ?_ ?_ ?_ (Fin.castLE_injective _) ?_ ?_ ?_ ?_
  · intro e
    have := e.2
    rw [Fin.lt_def, tgtC_val, srcC_val]
    split_ifs <;> omega
  · intro v hv
    have hv' : v.1 ≠ 2 * j + 4 := fun h => hv (Fin.ext h)
    refine ⟨⟨v.1, v.2⟩, Fin.ext ?_⟩
    rw [tgtC_val]
    simp [hv']
  · intro e h
    have h' := congrArg Fin.val h
    rw [tgtC_val] at h'
    have := e.2
    change _ = 2 * j + 4 at h'
    split_ifs at h' <;> omega
  · intro x
    refine Finset.card_eq_one.2 ⟨⟨x.1, by omega⟩, ?_⟩
    ext e
    have := x.2
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton, Fin.ext_iff, tgtC_val, leafC_val]
    split_ifs <;> omega
  · intro v
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    constructor
    · intro h
      by_contra hno
      have hv : j + 2 ≤ v.1 := by
        by_contra hlt
        exact hno ⟨⟨v.1, by omega⟩, Fin.ext rfl⟩
      have := v.2
      by_cases h1 : v.1 = j + 2
      · refine h (x := ⟨j, by omega⟩) (Finset.mem_univ _) (Fin.ext ?_)
        rw [srcC_val]
        simp only
        split_ifs <;> omega
      · by_cases h2 : v.1 = 2 * j + 4
        · refine h (x := ⟨j + 1, by omega⟩) (Finset.mem_univ _) (Fin.ext ?_)
          rw [srcC_val]
          simp only
          split_ifs <;> omega
        · refine h (x := ⟨v.1 - 1, by omega⟩) (Finset.mem_univ _) (Fin.ext ?_)
          rw [srcC_val]
          simp only
          split_ifs <;> omega
    · rintro ⟨x, rfl⟩ e _ he
      have h' := congrArg Fin.val he
      rw [srcC_val, leafC_val] at h'
      have := x.2
      have := e.2
      split_ifs at h' <;> omega
  · refine Finset.card_eq_two.2 ⟨⟨j + 1, by omega⟩, ⟨2 * j + 3, by omega⟩, ?_, ?_⟩
    · simp only [ne_eq, Fin.mk.injEq]
      omega
    · ext e
      have := e.2
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Finset.mem_singleton, Fin.ext_iff, srcC_val]
      change (_ = 2 * j + 4) ↔ _
      split_ifs <;> omega
  · intro v hv h0
    have hv' : v.1 ≠ 2 * j + 4 := fun h => hv (Fin.ext h)
    have hvlt := v.2
    have hge : j + 2 ≤ v.1 := by
      by_contra hlt
      refine h0 (Finset.card_eq_zero.2 (Finset.filter_eq_empty_iff.2 fun e _ he => ?_))
      have h' := congrArg Fin.val he
      rw [srcC_val] at h'
      have := e.2
      split_ifs at h' <;> omega
    -- the edges in and out
    by_cases hh : v.1 = j + 2
    · have hin : (Finset.univ.filter fun e => tgtC j e = v).card = 2 := by
        refine Finset.card_eq_two.2 ⟨⟨j + 2, by omega⟩, ⟨2 * j + 4, by omega⟩, ?_, ?_⟩
        · simp only [ne_eq, Fin.mk.injEq]
          omega
        · ext e
          have := e.2
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Finset.mem_singleton, Fin.ext_iff, tgtC_val]
          split_ifs <;> omega
      have hout : (Finset.univ.filter fun e => srcC j e = v).card = 1 := by
        refine Finset.card_eq_one.2 ⟨⟨j, by omega⟩, ?_⟩
        ext e
        have := e.2
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton, Fin.ext_iff, srcC_val]
        split_ifs <;> omega
      rw [hin, hout]
    · have hin : (Finset.univ.filter fun e => tgtC j e = v).card = 1 := by
        refine Finset.card_eq_one.2 ⟨⟨v.1, by omega⟩, ?_⟩
        ext e
        have := e.2
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton, Fin.ext_iff, tgtC_val]
        split_ifs <;> omega
      by_cases ht : v.1 = 2 * j + 3
      · have hout : (Finset.univ.filter fun e => srcC j e = v).card = 2 := by
          refine Finset.card_eq_two.2 ⟨⟨2 * j + 2, by omega⟩, ⟨2 * j + 4, by omega⟩, ?_, ?_⟩
          · simp only [ne_eq, Fin.mk.injEq]
            omega
          · ext e
            have := e.2
            simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Finset.mem_singleton, Fin.ext_iff, srcC_val]
            split_ifs <;> omega
        rw [hin, hout]
      · have hout : (Finset.univ.filter fun e => srcC j e = v).card = 2 := by
          refine Finset.card_eq_two.2 ⟨⟨v.1 - 1, by omega⟩, ⟨v.1 - j - 3, by omega⟩, ?_, ?_⟩
          · simp only [ne_eq, Fin.mk.injEq]
            omega
          · ext e
            have := e.2
            simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Finset.mem_singleton, Fin.ext_iff, srcC_val]
            split_ifs <;> omega
        rw [hin, hout]

/-! ### Walks along the cycle -/

/-- The nodes of the path. -/
def colC (j : ℕ) (v : Fin (2 * j + 5)) : Fin (2 * j + 5) := if j + 2 ≤ v.1 ∧ v.1 ≤ 2 * j + 3 then ⟨2 * j + 3, by omega⟩ else v

/-- A walk along the path, from `a` to `b`. -/
theorem walks_path {F : Set (Fin (2 * j + 5))} {a b : ℕ} (ha : j + 2 ≤ a) (hab : a ≤ b) (hb : b ≤ 2 * j + 3)
    (hF : ∀ (i : ℕ) (hi : i < 2 * j + 5), a ≤ i → i < b → (⟨i, hi⟩ : Fin (2 * j + 5)) ∈ F) :
    (graphOf (srcC j) (tgtC j)).Walks F ⟨a, by omega⟩ ⟨b, by omega⟩ := by
  induction b, hab using Nat.le_induction with
  | base => exact .refl
  | succ b hab ih =>
    refine (ih (by omega) fun i hi h1 h2 => hF i hi h1 (by omega)).tail ⟨⟨b, by omega⟩, hF b (by omega) hab (by omega), Or.inr ⟨Fin.ext ?_, Fin.ext ?_⟩⟩
    · change (srcC j ⟨b, _⟩).1 = b + 1
      rw [srcC_val]
      simp only
      split_ifs <;> omega
    · change (tgtC j ⟨b, _⟩).1 = b
      rw [tgtC_val]
      simp only
      split_ifs <;> omega

theorem colC_eq_iff (v w : Fin (2 * j + 5)) : colC j v = colC j w ↔ (v = w ∨ ((j + 2 ≤ v.1 ∧ v.1 ≤ 2 * j + 3) ∧ (j + 2 ≤ w.1 ∧ w.1 ≤ 2 * j + 3))) := by
  have hv := v.2
  have hw := w.2
  simp only [colC]
  split_ifs with h1 h2 h2
  · exact ⟨fun _ => Or.inr ⟨h1, h2⟩, fun _ => rfl⟩
  · rw [Fin.ext_iff, Fin.ext_iff]
    simp only []
    constructor <;> intro h <;> omega
  · rw [Fin.ext_iff, Fin.ext_iff]
    simp only []
    constructor <;> intro h <;> omega
  · exact ⟨Or.inl, fun h => h.resolve_right fun h' => h1 h'.1⟩

/-- **The cut edges**: those between the colours, where the nodes of the path have one colour. -/
theorem isBridge_iff {e : Fin (2 * j + 5)} : (graphOf (srcC j) (tgtC j)).underlying.IsBridge e ↔ colC j (srcC j e) ≠ colC j (tgtC j e) := by
  have he := e.2
  rw [Ne, colC_eq_iff, Fin.ext_iff, srcC_val, tgtC_val]
  by_cases hcyc : (j + 2 ≤ e.1 ∧ e.1 ≤ 2 * j + 2) ∨ e.1 = 2 * j + 4
  · -- an edge of the cycle isn't a cut edge
    have hnot : ¬ (graphOf (srcC j) (tgtC j)).underlying.IsBridge e := by
      rw [isBridge_iff_not_walks_delete, not_not]
      rcases hcyc with ⟨h1, h2⟩ | h1
      · have hs : srcC j e = ⟨e.1 + 1, by omega⟩ := Fin.ext (by
          rw [srcC_val]
          split_ifs <;> simp only [] <;> omega)
        have ht : tgtC j e = ⟨e.1, by omega⟩ := Fin.ext (by
          rw [tgtC_val, ite_eq_right (by omega)])
        change (graphOf (srcC j) (tgtC j)).Walks _ (srcC j e) (tgtC j e)
        rw [hs, ht]
        have w₁ := walks_path (j := j) (F := {e}ᶜ) (a := e.1 + 1) (b := 2 * j + 3) (by omega) (by omega) le_rfl (fun i hi h3 _ h4 => by
          have := congrArg Fin.val (Set.mem_singleton_iff.1 h4)
          simp only at this
          omega)
        have w₂ := walks_path (j := j) (F := {e}ᶜ) (a := j + 2) (b := e.1) le_rfl h1 (by omega) (fun i hi _ h3 h4 => by
          have := congrArg Fin.val (Set.mem_singleton_iff.1 h4)
          simp only at this
          omega)
        refine w₁.trans (Relation.ReflTransGen.head ⟨⟨2 * j + 4, by omega⟩, ?_, Or.inl ⟨Fin.ext ?_, Fin.ext ?_⟩⟩ w₂)
        · intro h4
          have := congrArg Fin.val (Set.mem_singleton_iff.1 h4)
          simp only at this
          omega
        · change (srcC j ⟨2 * j + 4, _⟩).1 = 2 * j + 3
          rw [srcC_val]
          simp
        · change (tgtC j ⟨2 * j + 4, _⟩).1 = j + 2
          rw [tgtC_val]
          simp
      · have hs : srcC j e = ⟨2 * j + 3, by omega⟩ := Fin.ext (by
          rw [srcC_val, ite_eq_left h1])
        have ht : tgtC j e = ⟨j + 2, by omega⟩ := Fin.ext (by
          rw [tgtC_val, ite_eq_left h1])
        change (graphOf (srcC j) (tgtC j)).Walks _ (srcC j e) (tgtC j e)
        rw [hs, ht]
        refine (graphOf (srcC j) (tgtC j)).walks_symm (walks_path (F := {e}ᶜ) le_rfl (by omega) le_rfl fun i hi _ h3 h4 => ?_)
        have := congrArg Fin.val (Set.mem_singleton_iff.1 h4)
        simp only at this
        omega
    constructor
    · exact fun h => absurd h hnot
    · intro h
      exfalso
      refine h ?_
      split_ifs <;> omega
  · -- the other edges are cut edges
    have hyes : (graphOf (srcC j) (tgtC j)).underlying.IsBridge e := by
      by_cases ht : e.1 = 2 * j + 3
      · refine isBridge_of_side (S := {⟨j + 1, by omega⟩, ⟨2 * j + 4, by omega⟩}) fun f => ?_
        have hf := f.2
        simp only [Finset.mem_insert, Finset.mem_singleton, Fin.ext_iff, srcC_val, tgtC_val]
        split_ifs <;> omega
      · refine isBridge_of_side (S := {⟨e.1, he⟩}) fun f => ?_
        have hf := f.2
        simp only [Finset.mem_singleton, Fin.ext_iff, srcC_val, tgtC_val]
        split_ifs <;> omega
    constructor
    · intro _ h
      split_ifs at h <;> omega
    · exact fun _ => hyes

/-- **The blobs**: the nodes of the path, and each other node alone. -/
theorem blobOf_eq_iff {u w : Fin (2 * j + 5)} : blobOf (graphOf (srcC j) (tgtC j)) u = blobOf (graphOf (srcC j) (tgtC j)) w ↔ colC j u = colC j w := by
  refine blobOf_eq_iff_of_col (fun {e} => isBridge_iff) fun v => ?_
  by_cases hv : j + 2 ≤ v.1 ∧ v.1 ≤ 2 * j + 3
  · have hc : colC j v = ⟨2 * j + 3, by omega⟩ := ite_eq_left hv
    rw [hc]
    refine walks_path (a := v.1) hv.1 hv.2 le_rfl fun i hi h1 h2 => ⟨Set.mem_univ _, fun hc => ?_⟩
    have hb := isBridge_iff.1 (isCutIn_univ_iff.1 hc)
    refine hb ?_
    have e₁ : srcC j ⟨i, hi⟩ = ⟨i + 1, by omega⟩ := Fin.ext (by
      rw [srcC_val]
      simp only
      split_ifs <;> omega)
    have e₂ : tgtC j ⟨i, hi⟩ = ⟨i, hi⟩ := Fin.ext (by
      rw [tgtC_val]
      simp only
      split_ifs <;> omega)
    rw [e₁, e₂]
    simp only [colC]
    rw [ite_eq_left (by omega), ite_eq_left (by omega)]
  · have hc : colC j v = v := ite_eq_right hv
    rw [hc]
    exact .refl

/-- The top of the cycle. -/
def topC (j : ℕ) : Fin (2 * j + 5) := ⟨2 * j + 3, by omega⟩

/-- The cut edges at the blob: those of the taxa `x_i`, `z`, and the one from the root. -/
theorem incidentCutEdges_top :
    incidentCutEdges (graphOf (srcC j) (tgtC j)) (blobOf (graphOf (srcC j) (tgtC j)) (topC j)) = {e | e.1 ≤ j ∨ e.1 = 2 * j + 3} := by
  ext e
  have he := e.2
  have htop : colC j (topC j) = topC j := ite_eq_left (by simp only [topC]; omega)
  have hcol : ∀ v : Fin (2 * j + 5), colC j v = topC j ↔ (j + 2 ≤ v.1 ∧ v.1 ≤ 2 * j + 3) := by
    intro v
    have hv := v.2
    simp only [colC, topC, Fin.ext_iff]
    split_ifs with h
    · simpa using h
    · constructor
      · intro h'
        omega
      · intro h'
        exact absurd h' h
  simp only [incidentCutEdges, IsIncidentToBlob, Set.mem_ofPred_eq, isBridge_iff, blobOf_eq_iff, htop]
  change (_ ∧ Xor (colC j (srcC j e) = topC j) (colC j (tgtC j e) = topC j)) ↔ _
  rw [hcol, hcol]
  constructor
  · rintro ⟨-, (⟨⟨h1, h2⟩, h3⟩ | ⟨⟨h1, h2⟩, h3⟩)⟩
    · rw [srcC_val] at h1 h2
      rw [tgtC_val] at h3
      split_ifs at h1 h2 h3 <;> omega
    · rw [tgtC_val] at h1 h2
      rw [srcC_val] at h3
      split_ifs at h1 h2 h3 <;> omega
  · intro h
    have hne : colC j (srcC j e) ≠ colC j (tgtC j e) := by
      rw [Ne, colC_eq_iff, Fin.ext_iff, srcC_val, tgtC_val]
      split_ifs <;> omega
    refine ⟨hne, ?_⟩
    by_cases ht : e.1 = 2 * j + 3
    · refine Or.inr ⟨?_, ?_⟩
      · rw [tgtC_val]
        split_ifs <;> omega
      · rw [srcC_val]
        split_ifs <;> omega
    · refine Or.inl ⟨?_, ?_⟩
      · rw [srcC_val]
        split_ifs <;> omega
      · rw [tgtC_val]
        split_ifs <;> omega

/-- The node of the top, and the hybrid node, are in one blob. -/
theorem blobOf_hyb_top : blobOf (graphOf (srcC j) (tgtC j)) (⟨j + 2, by omega⟩ : Fin (2 * j + 5)) = blobOf (graphOf (srcC j) (tgtC j)) (topC j) := by
  rw [blobOf_eq_iff, colC_eq_iff]
  refine Or.inr ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> simp only [topC] <;> omega

/-- The cut degree of the blob of the cycle is `j + 2`. -/
theorem cutDegree_top : cutDegree (graphOf (srcC j) (tgtC j)) (blobOf (graphOf (srcC j) (tgtC j)) (topC j)) = j + 2 := by
  rw [cutDegree, incidentCutEdges_top]
  let g : Fin (j + 2) → Fin (2 * j + 5) := fun i => if h : i.1 ≤ j then ⟨i.1, by omega⟩ else ⟨2 * j + 3, by omega⟩
  have hg : Function.Injective g := by
    intro i i' h
    have hi := i.2
    have hi' := i'.2
    have h' := congrArg Fin.val h
    simp only [g] at h'
    split_ifs at h' <;> simp only [] at h' <;> exact Fin.ext (by omega)
  have hset : {e : Fin (2 * j + 5) | e.1 ≤ j ∨ e.1 = 2 * j + 3} = g '' Set.univ := by
    ext e
    simp only [Set.mem_ofPred_eq, Set.image_univ, Set.mem_range]
    constructor
    · rintro (h | h)
      · exact ⟨⟨e.1, by omega⟩, by simp only [g]; rw [dite_eq_left h]⟩
      · exact ⟨⟨j + 1, by omega⟩, by
          simp only [g]
          rw [dite_eq_right (by omega)]
          exact Fin.ext h.symm⟩
    · rintro ⟨i, rfl⟩
      simp only [g]
      split_ifs with h
      · exact Or.inl h
      · exact Or.inr rfl
  rw [hset, Set.ncard_image_of_injective _ hg, Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fin]

/-- **The blob of the cycle** is not a node, and has degree `j + 2`. -/
theorem cycleNet_blob (j : ℕ) :
    ¬ IsTrivialBlob (cycleNet j).graph (blobOf (cycleNet j).graph (topC j)) ∧ blobDegree (cycleNet j) (blobOf (cycleNet j).graph (topC j)) = j + 2 := by
  constructor
  · intro htr
    have h1 := (blobOf_eq_iff_of_isTrivialBlob htr _).1 (blobOf_hyb_top (j := j))
    have := congrArg Fin.val h1
    simp only [topC] at this
    omega
  · unfold blobDegree
    have hc := cutDegree_top (j := j)
    have hr : ¬ blobOf (cycleNet j).graph (cycleNet j).root = blobOf (cycleNet j).graph (topC j) := by
      intro h
      have h' := (blobOf_eq_iff (j := j)).1 h
      rw [colC_eq_iff] at h'
      rcases h' with h' | ⟨⟨-, h'⟩, -⟩
      · have := congrArg Fin.val h'
        change 2 * j + 4 = 2 * j + 3 at this
        omega
      · change 2 * j + 4 ≤ 2 * j + 3 at h'
        omega
    rw [ite_eq_right hr]
    exact hc

/-- **"Non-tree phylogenetic networks may have `k`-blobs that are not nodes for any `k > 1`"** (`a:claim:k-blobs`, after Definition 7). -/
theorem exists_kBlob {k : ℕ} (hk : 1 < k) :
    ∃ j, j + 2 = k ∧ IsBinaryNetwork (cycleNet j) ∧ ∃ b, ¬ IsTrivialBlob (cycleNet j).graph b ∧ blobDegree (cycleNet j) b = k :=
  ⟨k - 2, by omega, isBinaryNetwork_cycleNet, _, (cycleNet_blob (k - 2)).1, (cycleNet_blob (k - 2)).2.trans (by omega)⟩

/-! ### One cycle -/

/-- The edges of the cycle are the edges that aren't cut edges. -/
theorem not_isBridge_iff {e : Fin (2 * j + 5)} : ¬ (graphOf (srcC j) (tgtC j)).underlying.IsBridge e ↔ (j + 2 ≤ e.1 ∧ e.1 ≤ 2 * j + 2) ∨ e.1 = 2 * j + 4 := by
  have he := e.2
  rw [isBridge_iff, not_not, colC_eq_iff, Fin.ext_iff, srcC_val, tgtC_val]
  split_ifs <;> omega

/-- **One cycle of `j + 2` edges.** -/
theorem ncard_not_isBridge : {e : Fin (2 * j + 5) | ¬ (cycleNet j).graph.underlying.IsBridge e}.ncard = j + 2 := by
  let g : Fin (j + 2) → Fin (2 * j + 5) := fun i => if h : i.1 ≤ j then ⟨j + 2 + i.1, by omega⟩ else ⟨2 * j + 4, by omega⟩
  have hg : Function.Injective g := by
    intro i i' h
    have hi := i.2
    have hi' := i'.2
    have h' := congrArg Fin.val h
    simp only [g] at h'
    split_ifs at h' <;> simp only [] at h' <;> exact Fin.ext (by omega)
  have hset : {e : Fin (2 * j + 5) | ¬ (cycleNet j).graph.underlying.IsBridge e} = g '' Set.univ := by
    ext e
    have he := e.2
    have h0 : ¬ (cycleNet j).graph.underlying.IsBridge e ↔ (j + 2 ≤ e.1 ∧ e.1 ≤ 2 * j + 2) ∨ e.1 = 2 * j + 4 := not_isBridge_iff
    simp only [Set.mem_ofPred_eq, Set.image_univ, Set.mem_range, h0]
    constructor
    · rintro (⟨h1, h2⟩ | h)
      · refine ⟨⟨e.1 - (j + 2), by omega⟩, ?_⟩
        simp only [g]
        rw [dite_eq_left (by omega)]
        exact Fin.ext (by simp only; omega)
      · refine ⟨⟨j + 1, by omega⟩, ?_⟩
        simp only [g]
        rw [dite_eq_right (by omega)]
        exact Fin.ext h.symm
    · rintro ⟨i, rfl⟩
      have hi := i.2
      simp only [g]
      split_ifs with h
      · exact Or.inl ⟨by simp only; omega, by simp only; omega⟩
      · exact Or.inr rfl
  rw [hset, Set.ncard_image_of_injective _ hg, Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fin]

/-- **The network is level-1**, in the library's sense: it has one hybrid node. -/
theorem isLevelOne_cycleNet : (cycleNet j).IsLevelOne := by
  have hcard : ∀ v : Fin (2 * j + 5), (cycleNet j).graph.indegree v = (Finset.univ.filter fun e => tgtC j e = v).card := indegree_finNetwork
  refine isLevelOne_of_unique_hybrid (h := (⟨j + 2, by omega⟩ : Fin (2 * j + 5))) (fun u hu => ?_) ?_
  · rw [hcard] at hu
    by_contra hne
    have hne' : u.1 ≠ j + 2 := fun h => hne (Fin.ext h)
    have hle : (Finset.univ.filter fun e => tgtC j e = u).card ≤ 1 := by
      refine Finset.card_le_one.2 fun e he f hf => ?_
      have h1 := congrArg Fin.val (Finset.mem_filter.1 he).2
      have h2 := congrArg Fin.val (Finset.mem_filter.1 hf).2
      rw [tgtC_val] at h1 h2
      refine Fin.ext ?_
      split_ifs at h1 h2 <;> omega
    omega
  · rw [hcard]
    refine (Finset.card_le_card (t := {⟨j + 2, by omega⟩, ⟨2 * j + 4, by omega⟩}) fun e he => ?_).trans (Finset.card_le_two)
    have h1 : (tgtC j e).1 = j + 2 := congrArg Fin.val (Finset.mem_filter.1 he).2
    rw [tgtC_val] at h1
    simp only [Finset.mem_insert, Finset.mem_singleton, Fin.ext_iff]
    split_ifs at h1 <;> omega

/-! ### From a B-quartet to a T-quartet -/

/-- A node above `z` only, or `z`: from the hybrid node only `z` is reached. -/
theorem reaches_hyb {w : Fin (2 * j + 5)} (h : (graphOf (srcC j) (tgtC j)).Reaches ⟨j + 2, by omega⟩ w) : w.1 = j + 2 ∨ w.1 = j := by
  induction h with
  | refl => exact Or.inl rfl
  | tail _ hstep ih =>
    obtain ⟨e, hs, ht⟩ := hstep
    have hs' : (srcC j e).1 = _ := congrArg Fin.val hs
    have ht' : (tgtC j e).1 = _ := congrArg Fin.val ht
    rw [srcC_val] at hs'
    rw [tgtC_val] at ht'
    have := e.2
    split_ifs at hs' ht' <;> omega

section BtoT

variable (hj : 3 ≤ j)

/-- The taxa `x₀, x₁, x₂, y`. -/
def quartetC : Finset (Fin (j + 2)) := {⟨0, by omega⟩, ⟨1, by omega⟩, ⟨2, by omega⟩, ⟨j + 1, by omega⟩}

include hj

theorem card_quartetC : (quartetC hj).card = 4 := by
  unfold quartetC
  rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_pair]
  · simp only [ne_eq, Fin.mk.injEq]
    omega
  · simp only [Finset.mem_insert, Finset.mem_singleton, Fin.mk.injEq, not_or]
    omega
  · simp only [Finset.mem_insert, Finset.mem_singleton, Fin.mk.injEq, not_or]
    omega

/-- **`{x₀, x₁, x₂, y}` is a B-quartet on the network**, determining the blob of the cycle. -/
theorem isBlobQuartet_quartetC : IsBlobQuartet (cycleNet j) (quartetC hj) := by
  refine ⟨card_quartetC hj, blobOf (cycleNet j).graph (topC j), by rw [card_quartetC hj]; omega, fun s hs u hu hne hw => hne ?_⟩
  -- a colouring in which the taxa `x_i` are alone
  let col : Fin (2 * j + 5) → ℕ := fun v => if v.1 < j then v.1 else j
  have hF : ∀ e ∈ (incidentCutEdges (cycleNet j).graph (blobOf (cycleNet j).graph (topC j)))ᶜ, col (srcC j e) = col (tgtC j e) := by
    intro e he
    have hinc : ¬ (e.1 ≤ j ∨ e.1 = 2 * j + 3) := fun h => he (by
      have h1 := incidentCutEdges_top (j := j)
      change e ∈ incidentCutEdges (graphOf (srcC j) (tgtC j)) (blobOf (graphOf (srcC j) (tgtC j)) (topC j))
      rw [h1]
      exact h)
    have := e.2
    simp only [col, srcC_val, tgtC_val]
    split_ifs <;> omega
  have heq := eq_of_walks_finNetwork col hF hw
  have hval : ∀ {z : Fin (j + 2)}, z ∈ quartetC hj → z.1 = 0 ∨ z.1 = 1 ∨ z.1 = 2 ∨ z.1 = j + 1 := by
    intro z hz
    simp only [quartetC, Finset.mem_insert, Finset.mem_singleton, Fin.ext_iff] at hz
    exact hz
  have h1 := hval hs
  have h2 := hval hu
  have hs' : (leafC j s).1 = s.1 := rfl
  have hu' : (leafC j u).1 = u.1 := rfl
  change col (leafC j s) = col (leafC j u) at heq
  simp only [col, hs', hu'] at heq
  refine Fin.ext ?_
  split_ifs at heq <;> omega

/-- **"Blobs may ... reduce to tree-like relationships. Indeed, this happens even in the level-1 case with a single cycle of `k` edges, `k ≥ 5`"** (`a:claim:cycle-splits`, after Definition 13). For `j ≥ 3` the set `{x₀, x₁, x₂, y}` is a B-quartet on the level-1 network `cycleNet j`, with its cycle of `j + 2 ≥ 5` edges, and not on the network it induces on these taxa: there the edge from `p₂` to `p₁` is a cut edge separating `x₀, x₁` from `x₂, y`. -/
theorem cycleNet_b_to_t (hY : ((quartetC hj : Finset (Fin (j + 2))) : Set (Fin (j + 2))).Nontrivial) :
    IsBlobQuartet (cycleNet j) (quartetC hj) ∧ ¬ IsBlobQuartetOnInduced isBinaryNetwork_cycleNet ((quartetC hj : Finset (Fin (j + 2))) : Set (Fin (j + 2))) hY (quartetC hj) := by
  refine ⟨isBlobQuartet_quartetC hj, fun hB => ?_⟩
  have hN := isBinaryNetwork_cycleNet (j := j)
  have hP := hN.isPhylogenetic
  obtain ⟨v, hv, hd⟩ := (Bridges.isBlobQuartetOnInduced_iff hN _ hY subset_rfl (card_quartetC hj)).mp hB
  set T : Finset (Fin (2 * j + 5)) := {⟨0, by omega⟩, ⟨1, by omega⟩, ⟨j + 3, by omega⟩, ⟨j + 4, by omega⟩} with hT
  have hmemT : ∀ w : Fin (2 * j + 5), w ∈ T ↔ w.1 = 0 ∨ w.1 = 1 ∨ w.1 = j + 3 ∨ w.1 = j + 4 := by
    intro w
    simp only [hT, Finset.mem_insert, Finset.mem_singleton, Fin.ext_iff]
  have hcross : OnlyCrosses (cycleNet j).graph ((cycleNet j).ancestralArcs ((quartetC hj : Finset (Fin (j + 2))) : Set (Fin (j + 2)))) ⟨j + 4, by omega⟩ (T : Set (Fin (2 * j + 5))) := by
    intro f hf hc
    have hf' := f.2
    have hc' : ((srcC j f ∈ T ∧ tgtC j f ∉ T) ∨ (tgtC j f ∈ T ∧ srcC j f ∉ T)) := by
      simpa [DirectedMultigraph.Crosses, cycleNet, finNetwork] using hc
    simp only [hmemT] at hc'
    have hs₀ := srcC_val f
    have ht₀ := tgtC_val f
    have hcases : f.1 = j + 4 ∨ f.1 = j + 2 := by
      split_ifs at hs₀ ht₀ <;> omega
    rcases hcases with h | h
    · exact Fin.ext h
    · exfalso
      -- the arc above the hybrid node isn't above these taxa
      obtain ⟨x, hx, hr⟩ := hf
      have htgt : tgtC j f = ⟨j + 2, by omega⟩ := Fin.ext (by
        rw [tgtC_val, ite_eq_right (by omega)]
        exact h)
      have hr' : (graphOf (srcC j) (tgtC j)).Reaches ⟨j + 2, by omega⟩ (leafC j x) := htgt ▸ hr
      have h1 := reaches_hyb hr'
      have h2 : (leafC j x).1 = x.1 := rfl
      have h3 := Finset.mem_coe.1 hx
      simp only [quartetC, Finset.mem_insert, Finset.mem_singleton, Fin.ext_iff] at h3
      omega
  have hmem : ∀ x ∈ quartetC hj, (cycleNet j).leaf x ∈ (cycleNet j).ancestralVertices ((quartetC hj : Finset (Fin (j + 2))) : Set (Fin (j + 2))) := fun x hx =>
    (cycleNet j).leaf_mem_ancestralVertices (Finset.mem_coe.mpr hx)
  have hleaf : ∀ (i : ℕ) (hi : i < j + 2), ((cycleNet j).leaf ⟨i, hi⟩).1 = i := fun _ _ => rfl
  refine Determines.no_split (a := (⟨0, by omega⟩ : Fin (j + 2))) (b := ⟨1, by omega⟩) (c := ⟨2, by omega⟩) (d := ⟨j + 1, by omega⟩) hd ?_ ?_ (fun s hs => walks_ancestral hP hv (hmem s hs)) hcross ?_ ?_ ?_ ?_
  · simp only [ne_eq, Fin.mk.injEq]
    omega
  · simp only [ne_eq, Fin.mk.injEq]
    omega
  · exact Finset.mem_coe.2 ((hmemT _).2 (Or.inl (hleaf 0 _)))
  · exact Finset.mem_coe.2 ((hmemT _).2 (Or.inr (Or.inl (hleaf 1 _))))
  · intro h
    have h' := (hmemT _).1 (Finset.mem_coe.1 h)
    rw [hleaf] at h'
    omega
  · intro h
    have h' := (hmemT _).1 (Finset.mem_coe.1 h)
    rw [hleaf] at h'
    omega

end BtoT

end AllmanEtAl2023.CycleFamily
