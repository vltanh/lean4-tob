module

public import AllmanEtAl2023.Bridges

/-!
# Allman, Baños, Mitchell, Rhodes 2023: the blobs of `𝒩⁻` on four taxa

The count behind Lemma 1, whose proof the paper omits ("A basic combinatorial observation, whose proof we omit"). The argument is ours, by the count of the degrees of the
tree `T(𝒩⁻)`:

1. in a finite tree, `∑ deg v = 2 (|V| - 1)` (`sum_nodeDegree`, `card_arcs_add_one`);
2. a blob of `𝒩⁻` without a taxon has at least two incident cut edges (`Bridges.nodeDegree_treeOfBlobs_ne_zero`, `Bridges.nodeDegree_treeOfBlobs_ne_one`);
3. so the four taxa are the only blobs of degree 1, and `∑ (deg - 2) = 2` over the others: one of degree 4, or two of degree 3, the rest of degree 2 (`excess_cases`);
4. the graph `T_rd(𝒩⁻)` is then the star or the H (`trd_cases`, with `Bridges.Trd_hasStar_or_hasQuartet`).
-/

@[expose] public noncomputable section

open Phylogenetics
open scoped Classical

namespace AllmanEtAl2023.TreeSuppression

variable {W F X : Type*} {G : DirectedMultigraph W F}

/-! ### The count of the degrees of a tree -/

/-- In a tree, two arcs with the same ends are equal. -/
theorem eq_of_ends (hG : G.IsTree) {e f : F} {p q : W} (he : Ends G e p q) (hf : Ends G f p q) : e = f := by
  by_contra hne
  have hw : G.AdjOn {e}ᶜ p q := ⟨f, fun h => hne h.symm, hf⟩
  have hwalk : G.Walks {e}ᶜ p q := Relation.ReflTransGen.single hw
  refine hG.2 e ?_
  rcases he with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
  · rw [h₁, h₂]
    exact hwalk
  · rw [h₁, h₂]
    exact G.walks_symm hwalk

/-- **A finite tree has one more node than edges.** -/
theorem card_arcs_add_one [Fintype W] [Fintype F] [Nonempty W] (hG : G.IsTree) :
    Fintype.card F + 1 = Fintype.card W := by
  have hS := hG.toSimpleGraph_isTree
  rw [← hS.card_edgeFinset]
  congr 1
  have hinj : Function.Injective fun e : F => s(G.source e, G.target e) := by
    intro e f hef
    have hef' : s(G.source e, G.target e) = s(G.source f, G.target f) := hef
    rcases Sym2.eq_iff.mp hef' with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
    · exact eq_of_ends hG (p := G.source e) (q := G.target e) (Or.inl ⟨rfl, rfl⟩) (Or.inl ⟨h₁.symm, h₂.symm⟩)
    · exact eq_of_ends hG (p := G.source e) (q := G.target e) (Or.inl ⟨rfl, rfl⟩) (Or.inr ⟨h₂.symm, h₁.symm⟩)
  rw [← Finset.card_univ, ← Finset.card_image_of_injective _ hinj]
  congr 1
  ext z
  induction z using Sym2.ind with
  | _ a b =>
    simp only [Finset.mem_image, Finset.mem_univ, true_and, SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
    rw [DirectedMultigraph.toSimpleGraph, SimpleGraph.fromRel_adj]
    constructor
    · rintro ⟨e, he⟩
      rcases Sym2.eq_iff.mp he with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
      · exact ⟨fun h => source_ne_target hG e (h₁.trans (h.trans h₂.symm)), Or.inl ⟨e, h₁, h₂⟩⟩
      · exact ⟨fun h => source_ne_target hG e (h₁.trans (h.symm.trans h₂.symm)), Or.inr ⟨e, h₁, h₂⟩⟩
    · rintro ⟨-, ⟨e, h₁, h₂⟩ | ⟨e, h₁, h₂⟩⟩
      · exact ⟨e, by rw [h₁, h₂]⟩
      · exact ⟨e, by rw [h₁, h₂, Sym2.eq_swap]⟩

/-- **The sum of the degrees is twice the number of edges.** -/
theorem sum_nodeDegree [Fintype W] [Fintype F] : ∑ w, nodeDegree G w = 2 * Fintype.card F := by
  have h₁ : ∑ w, G.indegree w = Fintype.card F := by
    rw [← Finset.card_univ, Finset.card_eq_sum_card_fiberwise (f := G.target) (t := Finset.univ)
      fun _ _ => Finset.mem_coe.mpr (Finset.mem_univ _)]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [DirectedMultigraph.indegree, ← Set.ncard_coe_finset]
    congr 1
    ext e
    simp
  have h₂ : ∑ w, G.outdegree w = Fintype.card F := by
    rw [← Finset.card_univ, Finset.card_eq_sum_card_fiberwise (f := G.source) (t := Finset.univ)
      fun _ _ => Finset.mem_coe.mpr (Finset.mem_univ _)]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [DirectedMultigraph.outdegree, ← Set.ncard_coe_finset]
    congr 1
    ext e
    simp
  simp only [nodeDegree, Finset.sum_add_distrib, h₁, h₂]
  ring

/-- The count: in a finite tree, `∑ deg + 2 = 2 |V|`. -/
theorem sum_nodeDegree_add_two [Fintype W] [Fintype F] [Nonempty W] (hG : G.IsTree) :
    ∑ w, nodeDegree G w + 2 = 2 * Fintype.card W := by
  rw [sum_nodeDegree, ← card_arcs_add_one hG]
  ring

/-- **The excess of the degrees over 2, on the nodes other than four of degree one.** A finite tree with four labelled nodes of degree 1, and the others of degree at
least 2: either one node has degree 4, or two have degree 3, and the others have degree 2. -/
theorem excess_cases [Fintype W] [Fintype F] [Fintype X] [Nonempty W] (hG : G.IsTree) (hX : Fintype.card X = 4) {ℓ : X → W}
    (hℓ : Function.Injective ℓ) (h₁ : ∀ x, nodeDegree G (ℓ x) = 1) (h₂ : ∀ w, (∀ x, ℓ x ≠ w) → 2 ≤ nodeDegree G w) :
    (∃ z, (∀ x, ℓ x ≠ z) ∧ nodeDegree G z = 4 ∧ ∀ w, (∀ x, ℓ x ≠ w) → w ≠ z → nodeDegree G w = 2) ∨
      (∃ z₁ z₂, z₁ ≠ z₂ ∧ (∀ x, ℓ x ≠ z₁) ∧ (∀ x, ℓ x ≠ z₂) ∧ nodeDegree G z₁ = 3 ∧ nodeDegree G z₂ = 3 ∧
        ∀ w, (∀ x, ℓ x ≠ w) → w ≠ z₁ → w ≠ z₂ → nodeDegree G w = 2) := by
  have hsum := sum_nodeDegree_add_two hG
  let I : Finset W := Finset.univ.filter fun w => ∀ x, ℓ x ≠ w
  have hL : (Finset.univ.image ℓ).card = 4 := by
    rw [Finset.card_image_of_injective _ hℓ, Finset.card_univ, hX]
  have hcompl : Iᶜ = Finset.univ.image ℓ := by
    ext w
    simp [I]
  have hsplit : ∑ w, nodeDegree G w = ∑ w ∈ I, nodeDegree G w + 4 := by
    rw [← Finset.sum_add_sum_compl I, hcompl, Finset.sum_image hℓ.injOn]
    simp only [h₁]
    simp [hX]
  have hcard : I.card + 4 = Fintype.card W := by
    rw [← hL, ← hcompl, Finset.card_add_card_compl]
  -- the excess
  let ex : W → ℕ := fun w => nodeDegree G w - 2
  have hdeg : ∀ w ∈ I, nodeDegree G w = ex w + 2 := fun w hw => by
    have := h₂ w (Finset.mem_filter.mp hw).2
    simp only [ex]
    omega
  have hex : ∑ w ∈ I, ex w = 2 := by
    have : ∑ w ∈ I, nodeDegree G w = ∑ w ∈ I, ex w + 2 * I.card := by
      rw [Finset.sum_congr rfl hdeg, Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul]
      ring
    omega
  by_cases hbig : ∃ z ∈ I, 2 ≤ ex z
  · left
    obtain ⟨z, hz, hz2⟩ := hbig
    have hle := Finset.single_le_sum (f := ex) (fun _ _ => Nat.zero_le _) hz
    have hrest : ∑ w ∈ I.erase z, ex w = 0 := by
      have := Finset.add_sum_erase I ex hz
      omega
    refine ⟨z, (Finset.mem_filter.mp hz).2, ?_, fun w hw hwz => ?_⟩
    · have := hdeg z hz
      omega
    · have hwI : w ∈ I := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hw⟩
      have h0 := (Finset.sum_eq_zero_iff.mp hrest) w (Finset.mem_erase.mpr ⟨hwz, hwI⟩)
      have := hdeg w hwI
      omega
  · right
    push Not at hbig
    have hle : ∀ w ∈ I, ex w = if ex w = 1 then 1 else 0 := fun w hw => by
      have := hbig w hw
      split_ifs <;> omega
    have hc : (I.filter fun w => ex w = 1).card = 2 := by
      rw [Finset.sum_congr rfl hle, Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, smul_eq_mul,
        mul_one] at hex
      exact hex
    obtain ⟨z₁, z₂, hne, hset⟩ := Finset.card_eq_two.mp hc
    have hz₁ : z₁ ∈ I.filter fun w => ex w = 1 := by simp [hset]
    have hz₂ : z₂ ∈ I.filter fun w => ex w = 1 := by simp [hset]
    obtain ⟨hz₁I, hz₁e⟩ := Finset.mem_filter.mp hz₁
    obtain ⟨hz₂I, hz₂e⟩ := Finset.mem_filter.mp hz₂
    refine ⟨z₁, z₂, hne, (Finset.mem_filter.mp hz₁I).2, (Finset.mem_filter.mp hz₂I).2, ?_, ?_, fun w hw h₁' h₂' => ?_⟩
    · have := hdeg z₁ hz₁I
      omega
    · have := hdeg z₂ hz₂I
      omega
    · have hwI : w ∈ I := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hw⟩
      have hn : ex w ≠ 1 := fun h => by
        have hm : w ∈ I.filter fun w => ex w = 1 := Finset.mem_filter.mpr ⟨hwI, h⟩
        rw [hset] at hm
        simp only [Finset.mem_insert, Finset.mem_singleton] at hm
        tauto
      have h3 := hbig w hwI
      have := hdeg w hwI
      omega

end AllmanEtAl2023.TreeSuppression

/-! ### `T_rd(𝒩⁻)` on four taxa -/

namespace AllmanEtAl2023

open Phylogenetics.RootedNetwork

variable {V E X : Type*} {N : RootedNetwork V E X} [Fintype X] [DecidableEq X]

/-- Four taxa have names. -/
theorem exists_names_of_card_four (hcard : Fintype.card X = 4) : ∃ a b c d : X, ({a, b, c, d} : Finset X).card = 4 := by
  have hu : (Finset.univ : Finset X).card = 4 := by rw [Finset.card_univ, hcard]
  obtain ⟨a, ha⟩ := Finset.card_pos.mp (show 0 < (Finset.univ : Finset X).card by omega)
  obtain ⟨b, c, d, -, -, -, he⟩ := Finset.card_eq_three.mp (by rw [Finset.card_erase_of_mem ha, hu] : ((Finset.univ : Finset X).erase a).card = 3)
  refine ⟨a, b, c, d, ?_⟩
  rw [← he, Finset.insert_erase ha, hu]

/-- **The shape of `T_rd(𝒩⁻)` on four taxa**: `T(𝒩⁻)` has one node of degree 4, or two of degree 3, off the taxa, and the others have degree 2, and `T_rd(𝒩⁻)` is the
star or the H. -/
theorem trd_cases (hN : IsBinaryNetwork N) (hcard : Fintype.card X = 4) :
    ((∃ z, (∀ x, blobOf (semidirected hN (nontrivial_of_card_four hcard)).graph ((semidirected hN (nontrivial_of_card_four hcard)).leaf x) ≠ z) ∧
        nodeDegree (semidirected hN (nontrivial_of_card_four hcard)).treeOfBlobs z = 4 ∧
        ∀ w, (∀ x, blobOf (semidirected hN (nontrivial_of_card_four hcard)).graph ((semidirected hN (nontrivial_of_card_four hcard)).leaf x) ≠ w) → w ≠ z →
          nodeDegree (semidirected hN (nontrivial_of_card_four hcard)).treeOfBlobs w = 2) ∧
      ∀ a b c d : X, ({a, b, c, d} : Finset X).card = 4 → (Trd hN (nontrivial_of_card_four hcard)).HasStarTopology a b c d) ∨
    ((∃ z₁ z₂, z₁ ≠ z₂ ∧ (∀ x, blobOf (semidirected hN (nontrivial_of_card_four hcard)).graph ((semidirected hN (nontrivial_of_card_four hcard)).leaf x) ≠ z₁) ∧
        (∀ x, blobOf (semidirected hN (nontrivial_of_card_four hcard)).graph ((semidirected hN (nontrivial_of_card_four hcard)).leaf x) ≠ z₂) ∧
        nodeDegree (semidirected hN (nontrivial_of_card_four hcard)).treeOfBlobs z₁ = 3 ∧ nodeDegree (semidirected hN (nontrivial_of_card_four hcard)).treeOfBlobs z₂ = 3 ∧
        ∀ w, (∀ x, blobOf (semidirected hN (nontrivial_of_card_four hcard)).graph ((semidirected hN (nontrivial_of_card_four hcard)).leaf x) ≠ w) → w ≠ z₁ → w ≠ z₂ →
          nodeDegree (semidirected hN (nontrivial_of_card_four hcard)).treeOfBlobs w = 2) ∧
      ∃ a b c d : X, ({a, b, c, d} : Finset X).card = 4 ∧ (Trd hN (nontrivial_of_card_four hcard)).HasQuartetTopology a b c d) := by
  have : Finite V := hN.finite_vertices
  have : Finite E := hN.finite_arcs
  have hX := nontrivial_of_card_four hcard
  have hTree := treeOfBlobs_semidirected_isTree hN hX
  have hinj : Function.Injective fun x => blobOf (semidirected hN hX).graph ((semidirected hN hX).leaf x) := fun x y hxy =>
    Bridges.Trd_leaf_injective hN hX (Subtype.ext hxy)
  have h₁ := nodeDegree_treeOfBlobs_leaf hN hX
  have h₂ : ∀ w, (∀ x, blobOf (semidirected hN hX).graph ((semidirected hN hX).leaf x) ≠ w) →
      2 ≤ nodeDegree (semidirected hN hX).treeOfBlobs w := fun w hw => by
    have h0 := Bridges.nodeDegree_treeOfBlobs_ne_zero hN hX hw
    have h1 := Bridges.nodeDegree_treeOfBlobs_ne_one hN hX hw
    omega
  let _ : Fintype (semidirected hN hX).graph.BlobVertex := Fintype.ofFinite _
  let _ : Fintype (semidirected hN hX).graph.BridgeArc := Fintype.ofFinite _
  obtain ⟨x₀⟩ := hX.to_nonempty
  have : Nonempty (semidirected hN hX).graph.BlobVertex := ⟨blobOf _ ((semidirected hN hX).leaf x₀)⟩
  -- a node of `T_rd(𝒩⁻)` off the taxa is a blob off the taxa
  have hoff : ∀ v : TrdV hN hX, (∀ x, (Trd hN hX).leaf x ≠ v) →
      ∀ x, blobOf (semidirected hN hX).graph ((semidirected hN hX).leaf x) ≠ v.1 := fun v hv x he =>
    hv x (Subtype.ext he)
  rcases TreeSuppression.excess_cases hTree hcard hinj h₁ h₂ with ⟨z, hz, hd, hrest⟩ | ⟨z₁, z₂, hne, hz₁, hz₂, hd₁, hd₂, hrest⟩
  · left
    refine ⟨⟨z, hz, hd, hrest⟩, fun a b c d h => ?_⟩
    have honly : ∀ v : TrdV hN hX, (∀ x, (Trd hN hX).leaf x ≠ v) → v.1 = z := fun v hv => by
      by_contra hvz
      exact v.2 (hrest v.1 (hoff v hv) hvz)
    -- two inner nodes would both be `z`
    have hno : ∀ {p q r t : X}, ({p, q, r, t} : Finset X).card = 4 → ¬ (Trd hN hX).HasQuartetTopology p q r t := by
      rintro p q r t hp ⟨u, w, hn, -, -⟩
      simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or, List.nodup_nil, and_true, not_false_eq_true] at hn
      obtain ⟨⟨-, -, -, hpu, hpw⟩, ⟨-, -, hqu, hqw⟩, ⟨-, hru, hrw⟩, ⟨htu, htw⟩, huw⟩ := hn
      have hall := Bridges.forall_eq_of_card_four hcard hp
      refine huw (Subtype.ext ((honly u fun x => ?_).trans (honly w fun x => ?_).symm))
      · rcases hall x with rfl | rfl | rfl | rfl <;> assumption
      · rcases hall x with rfl | rfl | rfl | rfl <;> assumption
    rcases Bridges.Trd_hasStar_or_hasQuartet hN hcard h with hS | hS | hS | hS
    · exact hS
    · exact absurd hS (hno h)
    · exact absurd hS (hno (card_acbd h))
    · exact absurd hS (hno (card_adbc h))
  · right
    refine ⟨⟨z₁, z₂, hne, hz₁, hz₂, hd₁, hd₂, hrest⟩, ?_⟩
    obtain ⟨a, b, c, d, h⟩ := exists_names_of_card_four hcard
    rcases Bridges.Trd_hasStar_or_hasQuartet hN hcard h with hS | hS | hS | hS
    · exfalso
      obtain ⟨u, -, hc, -⟩ := hS
      have hall := Bridges.forall_eq_of_card_four hcard h
      have hz : ∀ (z : (semidirected hN hX).graph.BlobVertex) (hz2 : nodeDegree (semidirected hN hX).treeOfBlobs z ≠ 2),
          (∀ x, blobOf (semidirected hN hX).graph ((semidirected hN hX).leaf x) ≠ z) → z = u.1 := fun z hz2 hzl => by
        have hm := hc ⟨z, hz2⟩
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
        rcases hm with hm | hm | hm | hm | hm
        · exact absurd (congrArg Subtype.val hm).symm (hzl a)
        · exact absurd (congrArg Subtype.val hm).symm (hzl b)
        · exact absurd (congrArg Subtype.val hm).symm (hzl c)
        · exact absurd (congrArg Subtype.val hm).symm (hzl d)
        · exact congrArg Subtype.val hm
      exact hne ((hz z₁ (by omega) hz₁).trans (hz z₂ (by omega) hz₂).symm)
    · exact ⟨a, b, c, d, h, hS⟩
    · exact ⟨a, c, b, d, card_acbd h, hS⟩
    · exact ⟨a, d, b, c, card_adbc h, hS⟩

end AllmanEtAl2023
