module

public import Basic.Phylogenetics.TreeMetric

/-!
# Rhodes 2020: the quartet metrization of a tree

J. A. Rhodes, *Topological metrizations of trees, and new quartet methods of tree inference*, IEEE/ACM
Trans. Comput. Biol. Bioinform. 17 (2020), 2107–2118.

An edge with blocks `X₁, …, X_m` at one end and `Y₁, …, Y_{m'}` at the other has weight
`∑_{i<j} |Xᵢ||Xⱼ| + ∑_{i<j} |Yᵢ||Yⱼ|`. Theorem 2: the tree metric of these weights is
`d(x, y) = 2 |Q_{x,y}| + 2N - 4`, with `Q_{x,y}` the quartets displayed on the tree of the form `xz|yw`
or `xyzw`. Internal edges have weight at least `2`.

The proof of Theorem 2 is the source's. A node `v ≠ x, y` on the path between `x` and `y` is a member
`P` of `TreeMetric.pathNodes T x y`, a vertex partition of the tree (`IsVertexPartition`), with
`A_v = blockOf P x`, `B_v = blockOf P y`, and blocks `C_v^i` the members of `otherBlocks P x y`.

The quartets `xu|yz` and `xyuz` at a node are `nodeQuartets P x y`. A quartet determines a node
(`exists_node_of_displays`, `exists_node_of_unresolved`), and at a node `z ∈ B_v \ {y}` gives `xu|yz`
(`displays_of_joinsAt_of_mem_block`) and distinct `C`'s give `xyuz` (`not_displays_of_joinsAt_of_ne`); so
`Q_{x,y}` is the disjoint union of these sets (`qSet_eq_biUnion`, `nodeQuartets_disjoint`). A quartet
containing `x, y` is given by its other two taxa (`quartetOfPair`), so these sets are counted as pairs
(`nodePairs`, `card_nodePairs`, `card_nodeQuartets`).
-/

@[expose] public noncomputable section

open Phylogenetics Phylogenetics.TreeMetric Finset
open scoped Classical

namespace External.Rhodes2020

variable {X : Type*} [Fintype X] [DecidableEq X]

/-- Two taxa on the side `A` lie in the same block of the edge when a split properly inside `A`
contains both; the blocks on that side are the maximal sides of `T` properly inside `A`, and single
taxa of `A` in no such side. The number of pairs in distinct blocks is
`∑_{i<j} |Xᵢ||Xⱼ|` (`sidePairs_compl_block`, at a node). -/
def sidePairs (T : Finset (Finset X)) (A : Finset X) : ℕ :=
  (univ.filter fun p : Finset X =>
    p.card = 2 ∧ p ⊆ A ∧ ¬ ∃ C ∈ T, C ⊂ A ∧ p ⊆ C).card

/-- The quartet metrization `Q` of the tree `T`: the weight of the edge with side `A`. -/
def quartetWeight (T : Finset (Finset X)) (A : Finset X) : ℝ :=
  (sidePairs T A : ℝ) + (sidePairs T Aᶜ : ℝ)

/-- The pairs counted by `sidePairs T A`. -/
private def pairsAt (T : Finset (Finset X)) (A : Finset X) : Finset (Finset X) :=
  univ.filter fun p : Finset X => p.card = 2 ∧ p ⊆ A ∧ ¬ ∃ C ∈ T, C ⊂ A ∧ p ⊆ C

/-! ### The sum `∑_{i<j} |Xᵢ||Xⱼ|` -/

/-- The sum `∑_{i<j} |Xᵢ||Xⱼ|` over the unordered pairs of members `Xᵢ, Xⱼ` of `F`. -/
def crossSum (F : Finset (Finset X)) : ℕ :=
  ∑ s ∈ F.powersetCard 2, ∏ B ∈ s, B.card

omit [Fintype X] in
theorem crossSum_insert {F : Finset (Finset X)} {B : Finset X} (hB : B ∉ F) :
    crossSum (insert B F) = crossSum F + B.card * ∑ C ∈ F, C.card := by
  have hdisj : Disjoint (F.powersetCard 2) ((F.powersetCard 1).image (insert B)) := by
    refine Finset.disjoint_left.mpr fun s hs hs' => ?_
    obtain ⟨t, -, rfl⟩ := Finset.mem_image.mp hs'
    exact hB ((Finset.mem_powersetCard.mp hs).1 (Finset.mem_insert_self B t))
  have hinj : Set.InjOn (insert B) (F.powersetCard 1 : Set (Finset (Finset X))) := by
    intro s hs t ht hst
    have hBs : B ∉ s := fun h => hB ((Finset.mem_powersetCard.mp (Finset.mem_coe.mp hs)).1 h)
    have hBt : B ∉ t := fun h => hB ((Finset.mem_powersetCard.mp (Finset.mem_coe.mp ht)).1 h)
    rw [← Finset.erase_insert hBs, ← Finset.erase_insert hBt]
    exact congrArg (fun r => Finset.erase r B) hst
  have hsplit : (insert B F).powersetCard 2 =
      F.powersetCard 2 ∪ (F.powersetCard 1).image (insert B) :=
    Finset.powersetCard_succ_insert hB 1
  unfold crossSum
  rw [hsplit, Finset.sum_union hdisj, Finset.sum_image hinj, Finset.powersetCard_one,
    Finset.sum_map, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun C hC => ?_
  have hBC : B ∉ ({C} : Finset (Finset X)) := by
    rw [Finset.mem_singleton]
    rintro rfl
    exact hB hC
  simp [Finset.prod_insert hBC]

/-- The unordered pairs of taxa in distinct members of `F`. -/
private def pairsAcross (F : Finset (Finset X)) : Finset (Finset X) :=
  univ.filter fun p : Finset X => p.card = 2 ∧ p ⊆ F.sup id ∧ ∀ B ∈ F, ¬ p ⊆ B

omit [Fintype X] in
private theorem card_image_pair {U V : Finset X} (h : Disjoint U V) :
    ((U ×ˢ V).image fun a : X × X => ({a.1, a.2} : Finset X)).card = U.card * V.card := by
  rw [Finset.card_image_of_injOn, Finset.card_product]
  rintro ⟨u, v⟩ hu ⟨u', v'⟩ hu' heq
  obtain ⟨huU, hvV⟩ := Finset.mem_product.mp (Finset.mem_coe.mp hu)
  obtain ⟨hu'U, hv'V⟩ := Finset.mem_product.mp (Finset.mem_coe.mp hu')
  simp only at huU hvV hu'U hv'V heq
  have h1 : u ∈ ({u', v'} : Finset X) := heq ▸ (by simp)
  have h2 : v ∈ ({u', v'} : Finset X) := heq ▸ (by simp)
  simp only [Finset.mem_insert, Finset.mem_singleton] at h1 h2
  rcases h1 with rfl | rfl
  · rcases h2 with rfl | rfl
    · exact absurd hvV (Finset.disjoint_left.mp h huU)
    · rfl
  · exact absurd hv'V (Finset.disjoint_left.mp h huU)

private theorem pairsAcross_insert {F : Finset (Finset X)} {B : Finset X}
    (hdis : Disjoint B (F.sup id)) :
    pairsAcross (insert B F) = pairsAcross F ∪
      (B ×ˢ F.sup id).image fun a : X × X => ({a.1, a.2} : Finset X) := by
  have hmem : ∀ {C t}, C ∈ F → t ∈ C → t ∈ F.sup id := fun {C t} hC ht =>
    Finset.mem_sup.mpr ⟨C, hC, ht⟩
  ext p
  simp only [pairsAcross, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union,
    Finset.mem_image, Finset.mem_product, Finset.sup_insert, id, Finset.forall_mem_insert]
  constructor
  · rintro ⟨hp2, hsub, hnB, hnF⟩
    obtain ⟨a, b, -, rfl⟩ := Finset.card_eq_two.mp hp2
    have ha : a ∈ B ∪ F.sup id := hsub (by simp)
    have hb : b ∈ B ∪ F.sup id := hsub (by simp)
    rcases Finset.mem_union.mp ha with ha | ha <;> rcases Finset.mem_union.mp hb with hb | hb
    · exact absurd (by simp [Finset.insert_subset_iff, ha, hb]) hnB
    · exact Or.inr ⟨(a, b), ⟨ha, hb⟩, rfl⟩
    · exact Or.inr ⟨(b, a), ⟨hb, ha⟩, Finset.pair_comm _ _⟩
    · refine Or.inl ⟨hp2, ?_, hnF⟩
      simp [Finset.insert_subset_iff, ha, hb]
  · rintro (⟨hp2, hsub, hn⟩ | ⟨⟨u, z⟩, ⟨hu, hz⟩, rfl⟩)
    · refine ⟨hp2, hsub.trans Finset.subset_union_right, fun hpB => ?_, hn⟩
      obtain ⟨t, ht⟩ := Finset.card_pos.mp (by omega : 0 < p.card)
      exact Finset.disjoint_left.mp hdis (hpB ht) (hsub ht)
    · have huz : u ≠ z := fun e => Finset.disjoint_left.mp hdis hu (e ▸ hz)
      refine ⟨Finset.card_pair huz, ?_, fun hsub => ?_, fun C hC hsub => ?_⟩
      · simp [Finset.insert_subset_iff, hu, hz]
      · exact Finset.disjoint_left.mp hdis (hsub (by simp)) hz
      · exact Finset.disjoint_left.mp hdis hu (hmem hC (hsub (by simp)))

/-- The pairs of taxa in distinct blocks number `∑_{i<j} |Xᵢ||Xⱼ|`. -/
private theorem card_pairsAcross {F : Finset (Finset X)}
    (hF : ∀ B ∈ F, ∀ C ∈ F, B ≠ C → Disjoint B C) : (pairsAcross F).card = crossSum F := by
  induction F using Finset.induction_on with
  | empty =>
    have h1 : pairsAcross (∅ : Finset (Finset X)) = ∅ :=
      Finset.filter_eq_empty_iff.mpr fun p _ hp => by
        have := Finset.card_le_card hp.2.1
        simp [hp.1] at this
    have h2 : crossSum (∅ : Finset (Finset X)) = 0 := by
      simp [crossSum]
    rw [h1, h2, Finset.card_empty]
  | insert B F hB ih =>
    have hF' : ∀ C ∈ F, ∀ D ∈ F, C ≠ D → Disjoint C D := fun C hC D hD =>
      hF C (Finset.mem_insert_of_mem hC) D (Finset.mem_insert_of_mem hD)
    have hdis : Disjoint B (F.sup id) := by
      refine Finset.disjoint_left.mpr fun t htB ht => ?_
      obtain ⟨C, hC, htC⟩ := Finset.mem_sup.mp ht
      have hne : B ≠ C := fun e => hB (e ▸ hC)
      exact Finset.disjoint_left.mp
        (hF B (Finset.mem_insert_self B F) C (Finset.mem_insert_of_mem hC) hne) htB htC
    have hd : Disjoint (pairsAcross F)
        ((B ×ˢ F.sup id).image fun a : X × X => ({a.1, a.2} : Finset X)) := by
      refine Finset.disjoint_left.mpr fun p hp hp' => ?_
      obtain ⟨⟨u, z⟩, ha, rfl⟩ := Finset.mem_image.mp hp'
      exact Finset.disjoint_left.mp hdis (Finset.mem_product.mp ha).1
        ((Finset.mem_filter.mp hp).2.2.1 (by simp))
    rw [pairsAcross_insert hdis, Finset.card_union_of_disjoint hd, ih hF', card_image_pair hdis,
      card_sup_eq_sum hF', crossSum_insert hB]

/-! ### The quartets at a node -/

/-- The two taxa other than `x, y` of the quartets `xu|yz` and `xyuz` that determine the node `P`: they
avoid `y` and the block `A_v` of `x`, and lie in distinct blocks of `P`. So at least one of them, `u`, is in
`C_v`, and the other is in `B_v` or in another block of `C_v` (`exists_of_mem_nodePairs`). -/
def nodePairs (P : Finset (Finset X)) (x y : X) : Finset (Finset X) :=
  univ.filter fun p : Finset X =>
    p.card = 2 ∧ y ∉ p ∧ (∀ t ∈ p, t ∉ blockOf P x) ∧ ∀ B ∈ P, ¬ p ⊆ B

/-- The set of four taxa `x, y` and the two taxa of `p`. A quartet containing `x, y` is given by the two
other taxa (`erase_erase_quartetOfPair`). -/
def quartetOfPair (x y : X) (p : Finset X) : Finset X := insert x (insert y p)

/-- The quartets `xu|yz` and `xyuz` that determine the node `P` (the source's paragraph before its
equation (2)): `u` joins the path at `P`, and `z` is in `B_v` other than `y`, or joins the path at `P` in
another block. -/
def nodeQuartets (P : Finset (Finset X)) (x y : X) : Finset (Finset X) :=
  (nodePairs P x y).image (quartetOfPair x y)

/-- The pair of a taxon joining the path at `P` and another beyond `P` towards `y`. -/
private theorem mem_nodePairs_of_joinsAt {T P : Finset (Finset X)} {x y u z : X}
    (hP : P ∈ pathNodes T x y) (hu : JoinsAt P x y u) (hz : z ∈ blockOf P y) (hzy : z ≠ y)
    (huz : u ≠ z) : ({u, z} : Finset X) ∈ nodePairs P x y := by
  obtain ⟨hV, hd⟩ := mem_pathNodes.1 hP
  refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, Finset.card_pair huz, ?_, ?_, ?_⟩
  · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨fun e => hu.2 (e ▸ mem_blockOf hV y), hzy.symm⟩
  · intro t ht
    simp only [Finset.mem_insert, Finset.mem_singleton] at ht
    rcases ht with rfl | rfl
    · exact hu.1
    · exact not_mem_blockOf_of_mem hP hz
  · intro B hB hsub
    have e := eq_of_mem_block hV hB (blockOf_mem hV y) (hsub (by simp)) hz
    exact hu.2 (e ▸ hsub (by simp))

/-- The pair of two taxa joining the path at `P` in distinct blocks. -/
private theorem mem_nodePairs_of_joinsAt_of_ne {T P : Finset (Finset X)} {x y u z : X}
    (hP : P ∈ pathNodes T x y) (hu : JoinsAt P x y u) (hz : JoinsAt P x y z)
    (hne : blockOf P u ≠ blockOf P z) : ({u, z} : Finset X) ∈ nodePairs P x y := by
  obtain ⟨hV, -⟩ := mem_pathNodes.1 hP
  have huz : u ≠ z := fun e => hne (e ▸ rfl)
  refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, Finset.card_pair huz, ?_, ?_, ?_⟩
  · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨fun e => hu.2 (e ▸ mem_blockOf hV y), fun e => hz.2 (e ▸ mem_blockOf hV y)⟩
  · intro t ht
    simp only [Finset.mem_insert, Finset.mem_singleton] at ht
    rcases ht with rfl | rfl
    · exact hu.1
    · exact hz.1
  · intro B hB hsub
    exact hne ((blockOf_eq hV hB (hsub (by simp))).trans (blockOf_eq hV hB (hsub (by simp))).symm)

/-- The two kinds of pairs at a node: `u` joins the path there, and `z` is in `B_v` other than `y`, or
joins the path there in another block. -/
private theorem exists_of_mem_nodePairs {P : Finset (Finset X)} {T : Finset (Finset X)} {x y : X}
    (hP : P ∈ pathNodes T x y) {p : Finset X} (hp : p ∈ nodePairs P x y) :
    ∃ u z, p = {u, z} ∧ u ≠ z ∧ JoinsAt P x y u ∧
      ((z ∈ blockOf P y ∧ z ≠ y) ∨ (JoinsAt P x y z ∧ blockOf P u ≠ blockOf P z)) := by
  obtain ⟨hV, -⟩ := mem_pathNodes.1 hP
  obtain ⟨-, hp2, hyp, hA, hno⟩ := Finset.mem_filter.mp hp
  obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp hp2
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hyp
  have hAa : a ∉ blockOf P x := hA a (by simp)
  have hAb : b ∉ blockOf P x := hA b (by simp)
  by_cases ha : a ∈ blockOf P y
  · have hb : b ∉ blockOf P y := fun hb => hno _ (blockOf_mem hV y) (by
      simp [Finset.insert_subset_iff, ha, hb])
    exact ⟨b, a, Finset.pair_comm _ _, hab.symm, ⟨hAb, hb⟩, Or.inl ⟨ha, Ne.symm hyp.1⟩⟩
  · refine ⟨a, b, rfl, hab, ⟨hAa, ha⟩, ?_⟩
    by_cases hb : b ∈ blockOf P y
    · exact Or.inl ⟨hb, Ne.symm hyp.2⟩
    · refine Or.inr ⟨⟨hAb, hb⟩, fun e => hno _ (blockOf_mem hV a) ?_⟩
      simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff]
      exact ⟨mem_blockOf hV a, e ▸ mem_blockOf hV b⟩

/-- A pair at a node has a taxon joining the path there. -/
private theorem joinsAt_of_mem_nodePairs {T P : Finset (Finset X)} {x y u z : X}
    (hP : P ∈ pathNodes T x y) (hp : ({u, z} : Finset X) ∈ nodePairs P x y) :
    JoinsAt P x y u ∨ JoinsAt P x y z := by
  obtain ⟨hV, -⟩ := mem_pathNodes.1 hP
  obtain ⟨-, -, -, hA, hno⟩ := Finset.mem_filter.mp hp
  by_cases hu : u ∈ blockOf P y
  · refine Or.inr ⟨hA z (by simp), fun hz => hno _ (blockOf_mem hV y) ?_⟩
    simp [Finset.insert_subset_iff, hu, hz]
  · exact Or.inl ⟨hA u (by simp), hu⟩

/-- A quartet determines one node only. -/
private theorem nodePairs_disjoint {T P P' : Finset (Finset X)} (hT : IsUnrootedTree T) {x y : X}
    (hP : P ∈ pathNodes T x y) (hP' : P' ∈ pathNodes T x y) (hne : P ≠ P') :
    Disjoint (nodePairs P x y) (nodePairs P' x y) := by
  refine Finset.disjoint_left.mpr fun p hp hp' => ?_
  obtain ⟨-, hp2, -, hA, -⟩ := Finset.mem_filter.mp hp
  obtain ⟨-, -, -, hA', -⟩ := Finset.mem_filter.mp hp'
  obtain ⟨u, z, -, rfl⟩ := Finset.card_eq_two.mp hp2
  have hnu : u ∉ blockOf P x := hA u (by simp)
  have hnz : z ∉ blockOf P x := hA z (by simp)
  have hnu' : u ∉ blockOf P' x := hA' u (by simp)
  have hnz' : z ∉ blockOf P' x := hA' z (by simp)
  rcases joinsAt_of_mem_nodePairs hP hp with hu | hz <;>
    rcases joinsAt_of_mem_nodePairs hP' hp' with hu' | hz'
  · exact hne (JoinsAt.unique hT hP hP' hu hu')
  · rcases pathNodes_order hT hP hP' hne hu hz' with h | h
    · exact hnu' h.2
    · exact hnz h.1
  · rcases pathNodes_order hT hP hP' hne hz hu' with h | h
    · exact hnz' h.2
    · exact hnu h.1
  · exact hne (JoinsAt.unique hT hP hP' hz hz')

/-- The pairs at the node `v` number `∑_i |C_v^i| (∑_{i<j} |C_v^j| + |B_v| - 1)`: the taxon `u` is in
`C_v^i`, and `z` in a later `C_v^j` or in `B_v` other than `y`. The source prints the upper limits of `i`
and `j` as `k`, for `k - 2` blocks `C_v^i`. -/
private theorem card_nodePairs {T P : Finset (Finset X)} (hS : IsSplitFamily T) {x y : X}
    (hP : P ∈ pathNodes T x y) :
    (nodePairs P x y).card =
      crossSum (otherBlocks P x y) + ((blockOf P y).card - 1) * ∑ C ∈ otherBlocks P x y, C.card := by
  obtain ⟨hV, hd⟩ := mem_pathNodes.1 hP
  have hBm := blockOf_mem hV y
  have hyB := mem_blockOf hV y
  have hother : ∀ C ∈ otherBlocks P x y, C ≠ blockOf P y := fun C hC e =>
    (Finset.mem_filter.mp hC).2.2 (e ▸ hyB)
  have hdB : ∀ C ∈ otherBlocks P x y, Disjoint ((blockOf P y).erase y) C := fun C hC =>
    (hV.pairwiseDisjoint C (Finset.mem_filter.mp hC).1 _ hBm (hother C hC)).symm.mono_left
      (Finset.erase_subset _ _)
  have hnot : (blockOf P y).erase y ∉ otherBlocks P x y := by
    intro h
    obtain ⟨t, ht⟩ := hS.nonempty _ (hV.mem _ (Finset.mem_filter.mp h).1)
    exact Finset.disjoint_left.mp (hdB _ h) ht ht
  have hdis : ∀ C ∈ insert ((blockOf P y).erase y) (otherBlocks P x y),
      ∀ D ∈ insert ((blockOf P y).erase y) (otherBlocks P x y), C ≠ D → Disjoint C D := by
    intro C hC D hD hCD
    rcases Finset.mem_insert.1 hC with rfl | hC <;> rcases Finset.mem_insert.1 hD with rfl | hD
    · exact absurd rfl hCD
    · exact hdB D hD
    · exact (hdB C hC).symm
    · exact hV.pairwiseDisjoint C (Finset.mem_filter.mp hC).1 D (Finset.mem_filter.mp hD).1 hCD
  have heq : nodePairs P x y = pairsAcross (insert ((blockOf P y).erase y) (otherBlocks P x y)) := by
    have hsup : ∀ t, t ∈ (insert ((blockOf P y).erase y) (otherBlocks P x y)).sup id ↔
        t ≠ y ∧ t ∉ blockOf P x := by
      intro t
      rw [Finset.sup_insert, id, Finset.sup_eq_union, Finset.mem_union, mem_sup_otherBlocks hV,
        Finset.mem_erase]
      constructor
      · rintro (⟨hty, htB⟩ | hJ)
        · exact ⟨hty, not_mem_blockOf_of_mem hP htB⟩
        · exact ⟨fun e => hJ.2 (e ▸ hyB), hJ.1⟩
      · rintro ⟨hty, htA⟩
        by_cases htB : t ∈ blockOf P y
        · exact Or.inl ⟨hty, htB⟩
        · exact Or.inr ⟨htA, htB⟩
    ext p
    simp only [nodePairs, pairsAcross, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.forall_mem_insert]
    refine and_congr_right fun hp2 => ?_
    obtain ⟨s, hs⟩ := Finset.card_pos.mp (by omega : 0 < p.card)
    have hsub : p ⊆ (insert ((blockOf P y).erase y) (otherBlocks P x y)).sup id ↔
        y ∉ p ∧ ∀ t ∈ p, t ∉ blockOf P x := by
      constructor
      · intro h
        exact ⟨fun hy => ((hsup y).1 (h hy)).1 rfl, fun t ht => ((hsup t).1 (h ht)).2⟩
      · rintro ⟨hy, hA⟩ t ht
        exact (hsup t).2 ⟨fun e => hy (e ▸ ht), hA t ht⟩
    rw [hsub, and_assoc]
    refine and_congr_right fun hyp => and_congr_right fun hA => ?_
    have herase : p ⊆ (blockOf P y).erase y ↔ p ⊆ blockOf P y :=
      ⟨fun h => h.trans (Finset.erase_subset _ _), fun h t ht =>
        Finset.mem_erase.mpr ⟨fun e => hyp (e ▸ ht), h ht⟩⟩
    rw [herase]
    constructor
    · intro hno
      exact ⟨hno _ hBm, fun C hC => hno C (Finset.mem_filter.mp hC).1⟩
    · rintro ⟨hnB, hnC⟩ B hB hpB
      by_cases hxB : x ∈ B
      · rw [blockOf_eq hV hB hxB] at hA
        exact hA s hs (hpB hs)
      · by_cases hyB' : y ∈ B
        · rw [blockOf_eq hV hB hyB'] at hnB
          exact hnB hpB
        · exact hnC B (Finset.mem_filter.mpr ⟨hB, hxB, hyB'⟩) hpB
  rw [heq, card_pairsAcross hdis, crossSum_insert hnot, Finset.card_erase_of_mem hyB]

/-- The sets `Q_{x,y}` of the theorem. -/
def qSet (T : Finset (Finset X)) (x y : X) : Finset (Finset X) :=
  univ.filter fun q : Finset X => q.card = 4 ∧ x ∈ q ∧ y ∈ q ∧
    (q ∈ {q : Finset X | ∀ s ∈ treesOn q, ¬ Displays T s} ∨
      ∃ s ∈ {s : QuartetTree X | Displays T s}, s.taxa = q ∧ Separated s x y)

/-! ### The quartets determine the nodes -/

/-- "`z ∈ B_v \ {y}` gives `xu|yz`": a taxon `u` joining the path at `v`, and `z` in `B_v`, give a displayed
quartet `xu|yz`. The edge from `v` towards `y` separates them. -/
theorem displays_of_joinsAt_of_mem_block {T P : Finset (Finset X)} (hS : IsSplitFamily T)
    {x y u z : X} (hP : P ∈ pathNodes T x y) (hu : JoinsAt P x y u) (hz : z ∈ blockOf P y)
    (h4 : ({x, u, y, z} : Finset X).card = 4) : Displays T (quartetTree x u y z h4) := by
  obtain ⟨hV, hd⟩ := mem_pathNodes.1 hP
  have hBy := blockOf_mem hV y
  refine (TreeMetric.displays_quartetTree_iff hS h4).mpr ⟨(blockOf P y)ᶜ, hS.compl_mem _ (hV.mem _ hBy),
    Finset.mem_compl.mpr fun hx => hd _ hBy hx (mem_blockOf hV y), Finset.mem_compl.mpr hu.2,
    fun h => Finset.mem_compl.mp h (mem_blockOf hV y), fun h => Finset.mem_compl.mp h hz⟩

/-- "Distinct `C`'s give `xyuz`": two taxa joining the path at `v` in distinct blocks give the unresolved
quartet `xyuz`, centred at `v`. -/
theorem not_displays_of_joinsAt_of_ne {T P : Finset (Finset X)} {x y u z : X}
    (hP : P ∈ pathNodes T x y) (hu : JoinsAt P x y u) (hz : JoinsAt P x y z)
    (hne : blockOf P u ≠ blockOf P z) : ∀ s ∈ treesOn ({x, y, u, z} : Finset X), ¬ Displays T s := by
  obtain ⟨hV, hd⟩ := mem_pathNodes.1 hP
  have hI : InDistinctBlocks P ({x, y, u, z} : Finset X) := by
    have hxy : blockOf P x ≠ blockOf P y := fun e =>
      hd _ (blockOf_mem hV x) (mem_blockOf hV x) (e ▸ mem_blockOf hV y)
    have hxu : blockOf P x ≠ blockOf P u := fun e => hu.1 (e ▸ mem_blockOf hV u)
    have hxz : blockOf P x ≠ blockOf P z := fun e => hz.1 (e ▸ mem_blockOf hV z)
    have hyu : blockOf P y ≠ blockOf P u := fun e => hu.2 (e ▸ mem_blockOf hV u)
    have hyz : blockOf P y ≠ blockOf P z := fun e => hz.2 (e ▸ mem_blockOf hV z)
    have key : ∀ a ∈ ({x, y, u, z} : Finset X), ∀ b ∈ ({x, y, u, z} : Finset X),
        blockOf P a = blockOf P b → a = b := by
      simp only [Finset.mem_insert, Finset.mem_singleton]
      rintro a (rfl | rfl | rfl | rfl) b (rfl | rfl | rfl | rfl) h <;>
        first
          | rfl
          | exact absurd h hxy
          | exact absurd h hxu
          | exact absurd h hxz
          | exact absurd h hyu
          | exact absurd h hyz
          | exact absurd h hne
          | exact absurd h.symm hxy
          | exact absurd h.symm hxu
          | exact absurd h.symm hxz
          | exact absurd h.symm hyu
          | exact absurd h.symm hyz
          | exact absurd h.symm hne
    intro B hB
    refine Finset.card_le_one.2 fun a ha b hb => ?_
    obtain ⟨haB, haq⟩ := Finset.mem_inter.1 ha
    obtain ⟨hbB, hbq⟩ := Finset.mem_inter.1 hb
    exact key a haq b hbq (by rw [blockOf_eq hV hB haB, blockOf_eq hV hB hbB])
  intro s hs
  exact not_displays_of_inDistinctBlocks hV (by rwa [mem_treesOn.1 hs])

/-- "Any quartet `xu|yz` … that is displayed on the tree `T` determines a node `v` on `P` at which the path
from `u` to `y` joins `P`": there, `z` is in `B_v`. -/
theorem exists_node_of_displays {T : Finset (Finset X)} (hS : IsSplitFamily T) {x y u z : X}
    (hxy : x ≠ y) (h4 : ({x, u, y, z} : Finset X).card = 4) (hd : Displays T (quartetTree x u y z h4)) :
    ∃ P ∈ pathNodes T x y, JoinsAt P x y u ∧ z ∈ blockOf P y := by
  obtain ⟨hxu, -, -, huy, -, -⟩ := TreeMetric.ne_of_card_four h4
  obtain ⟨C, hC, hxC, huC, hyC, hzC⟩ := (TreeMetric.displays_quartetTree_iff hS h4).mp hd
  obtain ⟨P, hP, hu⟩ := exists_joinsAt hS hxy (Ne.symm hxu) huy
  obtain ⟨hV, -⟩ := mem_pathNodes.1 hP
  refine ⟨P, hP, hu, ?_⟩
  rcases hV.edge_in_block C hC with ⟨F, hF, hsub⟩ | ⟨F, hF, hsub⟩
  · exact absurd (hsub huC) (by rw [← blockOf_eq hV hF (hsub hxC)]; exact hu.1)
  · rw [blockOf_eq hV hF (hsub (Finset.mem_compl.mpr hyC))]
    exact hsub (Finset.mem_compl.mpr hzC)

/-- "Any quartet … `xyuz` that is displayed on the tree `T` determines a node `v` on `P`", its centre, where
`u` and `z` join the path in distinct blocks. -/
theorem exists_node_of_unresolved {T : Finset (Finset X)} (hT : IsUnrootedTree T) {x y u z : X}
    (h4 : ({x, y, u, z} : Finset X).card = 4)
    (hstar : ∀ s ∈ treesOn ({x, y, u, z} : Finset X), ¬ Displays T s) :
    ∃ P ∈ pathNodes T x y, JoinsAt P x y u ∧ JoinsAt P x y z ∧ blockOf P u ≠ blockOf P z := by
  obtain ⟨hxy, hxu, hxz, hyu, hyz, huz⟩ := TreeMetric.ne_of_card_four h4
  obtain ⟨P, ⟨hP, hI⟩, -⟩ := existsUnique_center hT h4 hstar
  obtain ⟨hV, -⟩ := mem_multifurcations.1 hP
  have hone : ∀ B ∈ P, ∀ a ∈ ({x, y, u, z} : Finset X), ∀ b ∈ ({x, y, u, z} : Finset X),
      a ∈ B → b ∈ B → a = b := fun B hB a ha b hb haB hbB =>
    Finset.card_le_one.1 (hI B hB) a (Finset.mem_inter.2 ⟨haB, ha⟩) b (Finset.mem_inter.2 ⟨hbB, hb⟩)
  refine ⟨P, mem_pathNodes.2 ⟨hV, fun B hB hxB hyB =>
      hxy (hone B hB x (by simp) y (by simp) hxB hyB)⟩,
    ⟨fun h => hxu (hone _ (blockOf_mem hV x) x (by simp) u (by simp) (mem_blockOf hV x) h),
      fun h => hyu (hone _ (blockOf_mem hV y) y (by simp) u (by simp) (mem_blockOf hV y) h)⟩,
    ⟨fun h => hxz (hone _ (blockOf_mem hV x) x (by simp) z (by simp) (mem_blockOf hV x) h),
      fun h => hyz (hone _ (blockOf_mem hV y) y (by simp) z (by simp) (mem_blockOf hV y) h)⟩,
    fun e => huz (hone _ (blockOf_mem hV z) u (by simp) z (by simp) (e ▸ mem_blockOf hV u)
      (mem_blockOf hV z))⟩

omit [Fintype X] in
/-- A set of two taxa containing `x` is `{x, u}`. -/
private theorem exists_eq_pair_of_mem {B : Finset X} {x : X} (hB : B.card = 2) (hx : x ∈ B) :
    ∃ u, B = {x, u} := by
  obtain ⟨a, b, -, rfl⟩ := Finset.card_eq_two.mp hB
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx
  rcases hx with rfl | rfl
  · exact ⟨b, rfl⟩
  · exact ⟨a, Finset.pair_comm _ _⟩

omit [Fintype X] in
/-- A quartet tree separating `x, y` is `xu|yz`. -/
theorem exists_eq_quartetTree_of_separated {s : QuartetTree X} {x y : X} (h : Separated s x y) :
    ∃ u z, ∃ h4 : ({x, u, y, z} : Finset X).card = 4, s = quartetTree x u y z h4 := by
  obtain ⟨hx, hy, hno⟩ := h
  obtain ⟨B, hB, hxB⟩ : ∃ B ∈ s.val, x ∈ B := by
    simpa only [QuartetTree.taxa, Finset.mem_sup, id] using hx
  have hyC : y ∈ s.taxa \ B := Finset.mem_sdiff.2 ⟨hy, fun hyB => hno B hB ⟨hxB, hyB⟩⟩
  have hC := TreeMetric.sdiff_mem_of_mem hB
  obtain ⟨u, hu⟩ := exists_eq_pair_of_mem (s.card_of_mem hB) hxB
  obtain ⟨z, hz⟩ := exists_eq_pair_of_mem (s.card_of_mem hC) hyC
  have ht : s.taxa = {x, u, y, z} := by
    rw [← Finset.union_sdiff_of_subset (TreeMetric.subset_taxa_of_mem hB), hz, hu]
    ext t
    simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
    tauto
  have h4 : ({x, u, y, z} : Finset X).card = 4 := ht ▸ s.card_taxa
  refine ⟨u, z, h4, Subtype.ext ?_⟩
  rw [TreeMetric.val_eq_of_mem hB, hz, hu, TreeMetric.val_quartetTree]

omit [Fintype X] in
/-- The quartet tree `xu|yz` separates `x, y`. -/
theorem separated_quartetTree {x y u z : X} (h4 : ({x, u, y, z} : Finset X).card = 4) :
    Separated (quartetTree x u y z h4) x y := by
  obtain ⟨-, hxy, hxz, huy, -, -⟩ := TreeMetric.ne_of_card_four h4
  refine ⟨by simp, by simp, ?_⟩
  simp only [TreeMetric.val_quartetTree, Finset.mem_insert, Finset.mem_singleton]
  rintro B (rfl | rfl) ⟨h1, h2⟩
  · simp only [Finset.mem_insert, Finset.mem_singleton] at h2
    rcases h2 with h | h
    · exact hxy h.symm
    · exact huy h.symm
  · simp only [Finset.mem_insert, Finset.mem_singleton] at h1
    rcases h1 with h | h
    · exact hxy h
    · exact hxz h

/-- The sets `Q_{x,y}` are the quartets determining the nodes on the path: a quartet `xu|yz` determines the
node where `u` joins the path (`exists_node_of_displays`), a quartet `xyuz` its centre
(`exists_node_of_unresolved`). Conversely, at a node, `z ∈ B_v \ {y}` gives `xu|yz`
(`displays_of_joinsAt_of_mem_block`), and distinct `C`'s give `xyuz` (`not_displays_of_joinsAt_of_ne`). -/
theorem qSet_eq_biUnion {T : Finset (Finset X)} (hT : IsUnrootedTree T) (hS : IsSplitFamily T)
    {x y : X} (hxy : x ≠ y) :
    qSet T x y = (pathNodes T x y).biUnion fun P => nodeQuartets P x y := by
  ext q
  simp only [qSet, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion]
  constructor
  · rintro ⟨hq4, hxq, hyq, hstar | ⟨s, hs, hst, hsep⟩⟩
    · -- the quartet `xyuz`
      have hp2 : ((q.erase x).erase y).card = 2 := by
        rw [Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨hxy.symm, hyq⟩),
          Finset.card_erase_of_mem hxq, hq4]
      obtain ⟨u, z, -, hp⟩ := Finset.card_eq_two.mp hp2
      have hqeq : q = {x, y, u, z} := by
        rw [← hp, Finset.insert_erase (Finset.mem_erase.mpr ⟨hxy.symm, hyq⟩), Finset.insert_erase hxq]
      subst hqeq
      obtain ⟨P, hP, hu, hz, hne⟩ := exists_node_of_unresolved hT hq4 hstar
      exact ⟨P, hP, Finset.mem_image.mpr ⟨{u, z}, mem_nodePairs_of_joinsAt_of_ne hP hu hz hne, rfl⟩⟩
    · -- the quartet `xu|yz`
      obtain ⟨u, z, h4, rfl⟩ := exists_eq_quartetTree_of_separated hsep
      obtain ⟨-, -, -, -, huz, hyz⟩ := TreeMetric.ne_of_card_four h4
      obtain ⟨P, hP, hu, hzB⟩ := exists_node_of_displays hS hxy h4 hs
      refine ⟨P, hP, Finset.mem_image.mpr ⟨{u, z},
        mem_nodePairs_of_joinsAt hP hu hzB (Ne.symm hyz) huz, ?_⟩⟩
      rw [← hst, TreeMetric.taxa_quartetTree]
      ext t
      simp only [quartetOfPair, Finset.mem_insert, Finset.mem_singleton]
      tauto
  · rintro ⟨P, hP, hq⟩
    obtain ⟨hV, hd⟩ := mem_pathNodes.1 hP
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hq
    obtain ⟨u, z, rfl, huz, hu, hzB | hz⟩ := exists_of_mem_nodePairs hP hp
    · -- `z ∈ B_v \ {y}` gives `xu|yz`
      obtain ⟨hzB, hzy⟩ := hzB
      have hux : u ≠ x := fun e => hu.1 (e ▸ mem_blockOf hV x)
      have huy : u ≠ y := fun e => hu.2 (e ▸ mem_blockOf hV y)
      have hzx : z ≠ x := fun e => hd _ (blockOf_mem hV y) (e ▸ hzB) (mem_blockOf hV y)
      have h4 : ({x, u, y, z} : Finset X).card = 4 :=
        TreeMetric.card_four_of_ne (Ne.symm hux) hxy (Ne.symm hzx) huy huz (Ne.symm hzy)
      have hset : quartetOfPair x y {u, z} = {x, u, y, z} := by
        ext t
        simp only [quartetOfPair, Finset.mem_insert, Finset.mem_singleton]
        tauto
      rw [hset]
      exact ⟨h4, by simp, by simp, Or.inr ⟨_, displays_of_joinsAt_of_mem_block hS hP hu hzB h4,
        TreeMetric.taxa_quartetTree h4, separated_quartetTree h4⟩⟩
    · -- distinct `C`'s give `xyuz`
      obtain ⟨hz, hne⟩ := hz
      have hux : u ≠ x := fun e => hu.1 (e ▸ mem_blockOf hV x)
      have huy : u ≠ y := fun e => hu.2 (e ▸ mem_blockOf hV y)
      have hzx : z ≠ x := fun e => hz.1 (e ▸ mem_blockOf hV x)
      have hzy : z ≠ y := fun e => hz.2 (e ▸ mem_blockOf hV y)
      exact ⟨TreeMetric.card_four_of_ne hxy (Ne.symm hux) (Ne.symm hzx) (Ne.symm huy) (Ne.symm hzy) huz,
        by simp [quartetOfPair], by simp [quartetOfPair],
        Or.inl (not_displays_of_joinsAt_of_ne hP hu hz hne)⟩

omit [Fintype X] in
/-- A quartet containing `x, y` is given by the two other taxa. -/
private theorem erase_erase_quartetOfPair {x y : X} (hxy : x ≠ y) {p : Finset X} (hx : x ∉ p)
    (hy : y ∉ p) : ((quartetOfPair x y p).erase x).erase y = p := by
  rw [quartetOfPair, Finset.erase_insert fun h => (Finset.mem_insert.mp h).elim hxy hx,
    Finset.erase_insert hy]

/-- A pair at a node avoids `x, y`. -/
private theorem not_mem_of_mem_nodePairs {T P : Finset (Finset X)} {x y : X}
    (hP : P ∈ pathNodes T x y) {p : Finset X} (hp : p ∈ nodePairs P x y) : x ∉ p ∧ y ∉ p := by
  obtain ⟨hV, -⟩ := mem_pathNodes.1 hP
  obtain ⟨-, -, hyp, hA, -⟩ := Finset.mem_filter.mp hp
  exact ⟨fun hx => hA x hx (mem_blockOf hV x), hyp⟩

/-- The source's display before equation (2): the quartets determining the node `v` number
`∑_i |C_v^i| (∑_{i<j} |C_v^j| + |B_v| - 1)`, by `card_nodePairs`, each quartet being given by its two
taxa other than `x, y`. -/
theorem card_nodeQuartets {T P : Finset (Finset X)} (hS : IsSplitFamily T) {x y : X} (hxy : x ≠ y)
    (hP : P ∈ pathNodes T x y) :
    (nodeQuartets P x y).card =
      crossSum (otherBlocks P x y) + ((blockOf P y).card - 1) * ∑ C ∈ otherBlocks P x y, C.card := by
  rw [nodeQuartets, Finset.card_image_of_injOn, card_nodePairs hS hP]
  intro p hp p' hp' he
  have h1 := not_mem_of_mem_nodePairs hP (Finset.mem_coe.mp hp)
  have h2 := not_mem_of_mem_nodePairs hP (Finset.mem_coe.mp hp')
  rw [← erase_erase_quartetOfPair hxy h1.1 h1.2, he, erase_erase_quartetOfPair hxy h2.1 h2.2]

/-- A quartet determines one node only. -/
theorem nodeQuartets_disjoint {T P P' : Finset (Finset X)} (hT : IsUnrootedTree T) {x y : X}
    (hxy : x ≠ y) (hP : P ∈ pathNodes T x y) (hP' : P' ∈ pathNodes T x y) (hne : P ≠ P') :
    Disjoint (nodeQuartets P x y) (nodeQuartets P' x y) := by
  refine Finset.disjoint_left.mpr fun q hq hq' => ?_
  obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hq
  obtain ⟨p', hp', he⟩ := Finset.mem_image.mp hq'
  have h1 := not_mem_of_mem_nodePairs hP hp
  have h2 := not_mem_of_mem_nodePairs hP' hp'
  have hpp : p' = p := by
    rw [← erase_erase_quartetOfPair hxy h1.1 h1.2, ← he, erase_erase_quartetOfPair hxy h2.1 h2.2]
  exact Finset.disjoint_left.mp (nodePairs_disjoint hT hP hP' hne) hp (hpp ▸ hp')

private theorem qSet_comm (T : Finset (Finset X)) (x y : X) : qSet T y x = qSet T x y := by
  ext q
  simp only [qSet, Finset.mem_filter, Finset.mem_univ, true_and]
  have hsep : ∀ s : QuartetTree X, Separated s y x ↔ Separated s x y := by
    intro s
    simp only [Separated]
    constructor
    · rintro ⟨h1, h2, h3⟩
      exact ⟨h2, h1, fun B hB h => h3 B hB h.symm⟩
    · rintro ⟨h1, h2, h3⟩
      exact ⟨h2, h1, fun B hB h => h3 B hB h.symm⟩
  simp only [hsep]
  tauto

/-- The quartets of `Q_{x,y}` counted by the node they determine: the first line of the source's
equation (2), with `|B_v||C_v| - |C_v|` written `(|B_v| - 1) |C_v|`. -/
private theorem card_qSet_eq_sum {T : Finset (Finset X)} (hT : IsUnrootedTree T)
    (hS : IsSplitFamily T) {x y : X} (hxy : x ≠ y) :
    (qSet T x y).card = ∑ P ∈ pathNodes T x y,
      (crossSum (otherBlocks P x y) + ((blockOf P y).card - 1) * ∑ C ∈ otherBlocks P x y, C.card) := by
  rw [qSet_eq_biUnion hT hS hxy, Finset.card_biUnion
    fun P hP P' hP' hne => nodeQuartets_disjoint hT hxy hP hP' hne]
  exact Finset.sum_congr rfl fun P hP => card_nodeQuartets hS hxy hP

/-- **Equation (2)** of the source, `|Q_{x,y}| = ∑_v (∑_i |C_v^i| (∑_{i<j} |C_v^j| + |B_v|)) - N + 2`,
with the sum over the nodes `v ≠ x, y` on the path, and `N`, `2` moved across to stay in `ℕ`. It uses
`∑_v |C_v| = N - 2`, which the source leaves implicit (`sum_card_otherBlocks`). -/
theorem equation_two {T : Finset (Finset X)} (hT : IsUnrootedTree T)
    (hS : IsSplitFamily T) {x y : X} (hxy : x ≠ y) :
    (qSet T x y).card + Fintype.card X = ∑ P ∈ pathNodes T x y,
      (crossSum (otherBlocks P x y) + (blockOf P y).card * ∑ C ∈ otherBlocks P x y, C.card) + 2 := by
  rw [card_qSet_eq_sum hT hS hxy, ← sum_card_otherBlocks hT hS hxy, ← add_assoc,
    ← Finset.sum_add_distrib]
  congr 1
  refine Finset.sum_congr rfl fun P hP => ?_
  obtain ⟨hV, -⟩ := mem_pathNodes.1 hP
  obtain ⟨k, hk⟩ : ∃ k, (blockOf P y).card = k + 1 :=
    Nat.exists_eq_succ_of_ne_zero (Finset.card_ne_zero_of_mem (mem_blockOf hV y))
  rw [hk, Nat.add_sub_cancel]
  ring

/-- **Equation (3)** of the source, equation (2) with the roles of `x` and `y` interchanged:
`|Q_{x,y}| = ∑_w (∑_i |C_w^i| (∑_{i<j} |C_w^j| + |A_w|)) - N + 2`. -/
theorem equation_three {T : Finset (Finset X)} (hT : IsUnrootedTree T)
    (hS : IsSplitFamily T) {x y : X} (hxy : x ≠ y) :
    (qSet T x y).card + Fintype.card X = ∑ P ∈ pathNodes T x y,
      (crossSum (otherBlocks P x y) + (blockOf P x).card * ∑ C ∈ otherBlocks P x y, C.card) + 2 := by
  have h := equation_two hT hS hxy.symm
  simpa only [qSet_comm, pathNodes_comm T x y, otherBlocks_comm] using h

/-! ### The sum over the edges on the path -/

/-- The source's weight of an edge, at one of its ends: for the edge from the node `P` through its block
`B`, the side opposite to `B` has `∑_{i<j} |Xᵢ||Xⱼ|` pairs, over the other blocks `Xᵢ` of `P`. -/
theorem sidePairs_compl_block {T P : Finset (Finset X)} (hS : IsSplitFamily T)
    (hP : IsVertexPartition T P) {B : Finset X} (hB : B ∈ P) :
    sidePairs T Bᶜ = crossSum (P.erase B) := by
  have hsup : (P.erase B).sup id = Bᶜ := by
    ext t
    simp only [Finset.mem_sup, Finset.mem_erase, id, Finset.mem_compl]
    constructor
    · rintro ⟨C, ⟨hCB, hC⟩, htC⟩ htB
      exact Finset.disjoint_left.mp (hP.pairwiseDisjoint C hC B hB hCB) htC htB
    · intro htB
      obtain ⟨C, hC, htC⟩ := hP.exists_mem_block t
      exact ⟨C, ⟨fun e => htB (e ▸ htC), hC⟩, htC⟩
  have hdis : ∀ C ∈ P.erase B, ∀ D ∈ P.erase B, C ≠ D → Disjoint C D := fun C hC D hD =>
    hP.pairwiseDisjoint C (Finset.mem_of_mem_erase hC) D (Finset.mem_of_mem_erase hD)
  rw [← card_pairsAcross hdis]
  unfold sidePairs pairsAcross
  congr 1
  ext p
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, hsup]
  refine and_congr_right fun hp2 => and_congr_right fun hpB => ?_
  obtain ⟨t, ht⟩ := Finset.card_pos.mp (by omega : 0 < p.card)
  constructor
  · intro hno D hD hpD
    obtain ⟨hDB, hDP⟩ := Finset.mem_erase.mp hD
    exact hno ⟨D, hP.mem D hDP, block_ssubset_compl hS hP hB hDP hDB, hpD⟩
  · rintro hno ⟨C, hC, hCB, hpC⟩
    rcases hP.edge_in_block C hC with ⟨F, hF, hsub⟩ | ⟨F, hF, hsub⟩
    · by_cases hFB : F = B
      · subst hFB
        exact Finset.mem_compl.mp (hpB ht) (hsub (hpC ht))
      · exact hno F (Finset.mem_erase.mpr ⟨hFB, hF⟩) (hpC.trans hsub)
    · obtain ⟨b, hb⟩ := hS.nonempty B (hP.mem B hB)
      have hBC : ∀ s ∈ B, s ∈ Cᶜ := fun s hs => Finset.mem_compl.mpr fun h =>
        Finset.mem_compl.mp (hCB.1 h) hs
      have hFB : F = B := eq_of_mem_block hP hF hB (hsub (hBC b hb)) hb
      subst hFB
      exact not_subset_of_ssubset hCB (fun s hs => by
        by_contra hn
        exact Finset.mem_compl.mp hs (hsub (Finset.mem_compl.mpr hn)))

/-- The blocks at a node on the path other than that of `y`: `A_v` and the `C_v^i`. -/
private theorem erase_block_eq_insert {T P : Finset (Finset X)} {x y : X}
    (hP : P ∈ pathNodes T x y) : P.erase (blockOf P y) = insert (blockOf P x) (otherBlocks P x y) := by
  obtain ⟨hV, hd⟩ := mem_pathNodes.1 hP
  ext D
  simp only [Finset.mem_erase, Finset.mem_insert, otherBlocks, Finset.mem_filter]
  constructor
  · rintro ⟨hne, hD⟩
    by_cases hxD : x ∈ D
    · exact Or.inl (blockOf_eq hV hD hxD).symm
    · refine Or.inr ⟨hD, hxD, fun hyD => hne (blockOf_eq hV hD hyD).symm⟩
  · rintro (rfl | ⟨hD, hxD, hyD⟩)
    · refine ⟨fun e => ?_, blockOf_mem hV x⟩
      exact hd _ (blockOf_mem hV x) (mem_blockOf hV x) (e ▸ mem_blockOf hV y)
    · exact ⟨fun e => hyD (e ▸ mem_blockOf hV y), hD⟩

/-- The source's passage to a sum over the edges `e = (w, v)` on the path, with `w` towards `x`, at the
end `w`. The side of `e` containing `x` is `(B_w)ᶜ`, and its pairs are the term of `w` in equation (3).
The edge at the leaf `x` has the side `{x}` and no pairs, the source's empty sum. -/
theorem sum_sidePairs_eq {T : Finset (Finset X)} (hS : IsSplitFamily T) {x y : X} :
    ∑ A ∈ T.filter (fun A => x ∈ A ∧ y ∉ A), sidePairs T A =
      ∑ P ∈ pathNodes T x y,
        (crossSum (otherBlocks P x y) + (blockOf P x).card * ∑ C ∈ otherBlocks P x y, C.card) := by
  have h1 : ∑ A ∈ T.filter (fun A => x ∈ A ∧ y ∉ A), sidePairs T A =
      ∑ A ∈ T.filter (fun A => x ∈ A ∧ y ∉ A ∧ 2 ≤ A.card), sidePairs T A := by
    symm
    refine Finset.sum_subset (fun A hA => ?_) fun A hA hnA => ?_
    · obtain ⟨hAT, hx, hy, -⟩ := Finset.mem_filter.mp hA
      exact Finset.mem_filter.mpr ⟨hAT, hx, hy⟩
    · obtain ⟨hAT, hx, hy⟩ := Finset.mem_filter.mp hA
      have h2 : ¬ 2 ≤ A.card := fun h => hnA (Finset.mem_filter.mpr ⟨hAT, hx, hy, h⟩)
      refine Finset.card_eq_zero.mpr (Finset.filter_eq_empty_iff.mpr fun p _ hp => ?_)
      have := Finset.card_le_card hp.2.1
      omega
  rw [h1]
  symm
  have hval : ∀ P ∈ pathNodes T x y,
      crossSum (otherBlocks P x y) + (blockOf P x).card * ∑ C ∈ otherBlocks P x y, C.card =
        sidePairs T (blockOf P y)ᶜ := by
    intro P hP
    obtain ⟨hV, hd⟩ := mem_pathNodes.1 hP
    have hnot : blockOf P x ∉ otherBlocks P x y := fun h =>
      (Finset.mem_filter.mp h).2.1 (mem_blockOf hV x)
    rw [sidePairs_compl_block hS hV (blockOf_mem hV y), erase_block_eq_insert hP,
      crossSum_insert hnot]
  rw [Finset.sum_congr rfl hval]
  refine Finset.sum_nbij' (fun P => (blockOf P y)ᶜ) (nodeOfSide T y) ?_ ?_ ?_ ?_ (fun _ _ => rfl)
  · intro P hP
    obtain ⟨hV, hd⟩ := mem_pathNodes.1 hP
    have hBy := blockOf_mem hV y
    have hne : blockOf P x ≠ blockOf P y := fun e =>
      hd _ (blockOf_mem hV x) (mem_blockOf hV x) (e ▸ mem_blockOf hV y)
    have hlt := block_ssubset_compl hS hV hBy (blockOf_mem hV x) hne
    have hc1 := Finset.card_lt_card hlt
    have hc2 : 0 < (blockOf P x).card := Finset.card_pos.mpr ⟨x, mem_blockOf hV x⟩
    refine Finset.mem_filter.mpr ⟨hS.compl_mem _ (hV.mem _ hBy), hlt.1 (mem_blockOf hV x),
      fun h => Finset.mem_compl.mp h (mem_blockOf hV y), by omega⟩
  · intro A hA
    obtain ⟨hAT, hx, hy, h2⟩ := Finset.mem_filter.mp hA
    exact nodeOfSide_mem_pathNodes hS hAT hx hy h2
  · intro P hP
    obtain ⟨hV, -⟩ := mem_pathNodes.1 hP
    exact nodeOfSide_compl_block hS hV (blockOf_mem hV y) (mem_blockOf hV y)
  · intro A hA
    obtain ⟨hAT, hx, hy, h2⟩ := Finset.mem_filter.mp hA
    have hV := isVertexPartition_nodeOfSide hS hAT hy h2
    rw [blockOf_eq hV (Finset.mem_insert_self _ _) (Finset.mem_compl.mpr hy), compl_compl]

/-- The same at the end `v` of `e = (w, v)`: the side of `e` containing `y` is `(A_v)ᶜ`, and its pairs
are the term of `v` in equation (2). The edge at the leaf `y` has no pairs. -/
theorem sum_sidePairs_compl_eq {T : Finset (Finset X)} (hS : IsSplitFamily T) {x y : X} :
    ∑ A ∈ T.filter (fun A => x ∈ A ∧ y ∉ A), sidePairs T Aᶜ =
      ∑ P ∈ pathNodes T x y,
        (crossSum (otherBlocks P x y) + (blockOf P y).card * ∑ C ∈ otherBlocks P x y, C.card) := by
  have hcompl : ∑ A ∈ T.filter (fun A => x ∈ A ∧ y ∉ A), sidePairs T Aᶜ =
      ∑ A ∈ T.filter (fun A => y ∈ A ∧ x ∉ A), sidePairs T A := by
    refine Finset.sum_nbij' compl compl ?_ ?_ (by simp) (by simp) (by simp)
    · intro A hA
      obtain ⟨hAT, hxA, hyA⟩ := Finset.mem_filter.mp hA
      exact Finset.mem_filter.mpr ⟨hS.compl_mem A hAT, by simpa using hyA, by simpa using hxA⟩
    · intro A hA
      obtain ⟨hAT, hyA, hxA⟩ := Finset.mem_filter.mp hA
      exact Finset.mem_filter.mpr ⟨hS.compl_mem A hAT, by simpa using hxA, by simpa using hyA⟩
  rw [hcompl, sum_sidePairs_eq hS, pathNodes_comm]
  simp only [otherBlocks_comm]

/-- **Theorem 2.** The tree metric of the quartet metrization of an unrooted tree on `N` taxa is
`2 |Q_{x,y}| + 2N - 4`.

The proof is the source's. Each quartet of `Q_{x,y}` determines one node on the path
(`qSet_eq_biUnion`, `nodeQuartets_disjoint`), and the count by node (`card_nodeQuartets`) gives
equations (2) and (3) (`equation_two`, `equation_three`). Adding them and grouping the terms by the edges
on the path (`sum_sidePairs_eq`, `sum_sidePairs_compl_eq`) gives `2 |Q_{x,y}| = ∑_e w_Q(e) - 2N + 4`. -/
theorem theorem2 {T : Finset (Finset X)} (hT : IsUnrootedTree T) {x y : X} (hxy : x ≠ y) :
    treeMetric T (quartetWeight T) x y =
      quartetDistance {q | ∀ s ∈ treesOn q, ¬ Displays T s} {s | Displays T s} x y := by
  have hX : 2 ≤ Fintype.card X := Fintype.one_lt_card_iff.mpr ⟨x, y, hxy⟩
  have hS : IsSplitFamily T := (isUnrootedTree_iff hX T).mp hT
  have h2 := equation_two hT hS hxy
  have h3 := equation_three hT hS hxy
  have e1 := sum_sidePairs_eq (x := x) (y := y) hS
  have e2 := sum_sidePairs_compl_eq (x := x) (y := y) hS
  have hsum : treeMetric T (quartetWeight T) x y =
      ((∑ A ∈ T.filter (fun A => x ∈ A ∧ y ∉ A), sidePairs T A : ℕ) : ℝ) +
        ((∑ A ∈ T.filter (fun A => x ∈ A ∧ y ∉ A), sidePairs T Aᶜ : ℕ) : ℝ) := by
    simp only [treeMetric, quartetWeight, Finset.sum_add_distrib, Nat.cast_sum]
  have hdist : quartetDistance {q | ∀ s ∈ treesOn q, ¬ Displays T s} {s | Displays T s} x y =
      2 * ((qSet T x y).card : ℝ) + 2 * (Fintype.card X : ℝ) - 4 := by
    rw [quartetDistance, ite_eq_right hxy, qSet]
    congr!
  have hadd : ∑ A ∈ T.filter (fun A => x ∈ A ∧ y ∉ A), sidePairs T A +
      ∑ A ∈ T.filter (fun A => x ∈ A ∧ y ∉ A), sidePairs T Aᶜ + 4 =
      2 * (qSet T x y).card + 2 * Fintype.card X := by
    rw [e1, e2]
    omega
  have hadd' : ((∑ A ∈ T.filter (fun A => x ∈ A ∧ y ∉ A), sidePairs T A : ℕ) : ℝ) +
      ((∑ A ∈ T.filter (fun A => x ∈ A ∧ y ∉ A), sidePairs T Aᶜ : ℕ) : ℝ) + 4 =
      2 * ((qSet T x y).card : ℝ) + 2 * (Fintype.card X : ℝ) := by
    exact_mod_cast hadd
  rw [hsum, hdist]
  linarith

/-- Two taxa on the side `B` on either side of a maximal side inside it are counted by `sidePairs`. -/
private theorem mem_pairsAt_of_maximal {T : Finset (Finset X)} (hS : IsSplitFamily T)
    {B C₀ : Finset X} (hB : B ∈ T) (hC₀ : C₀ ∈ T) (hlt : C₀ ⊂ B)
    (hmax : ∀ C ∈ T, C ⊂ B → C.card ≤ C₀.card) {u z : X} (hu : u ∈ C₀) (hz : z ∈ B) (hzC : z ∉ C₀) :
    ({u, z} : Finset X) ∈ pairsAt T B := by
  refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, Finset.card_pair (fun h => hzC (h ▸ hu)), ?_, ?_⟩
  · intro t ht
    simp only [Finset.mem_insert, Finset.mem_singleton] at ht
    rcases ht with rfl | rfl
    · exact hlt.1 hu
    · exact hz
  · rintro ⟨C, hC, hCB, hsub⟩
    exact TreeMetric.not_mem_proper_of_maximal hS hB hC₀ hlt hmax hu hzC C hC hCB
      ⟨hsub (by simp), hsub (by simp)⟩

/-- A maximal side properly inside a side with at least two taxa. -/
private theorem exists_maximal {T : Finset (Finset X)} (hS : IsSplitFamily T) {B : Finset X}
    (hB2 : 2 ≤ B.card) : ∃ C₀ ∈ T, C₀ ⊂ B ∧ ∀ C ∈ T, C ⊂ B → C.card ≤ C₀.card := by
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp (by omega : 1 < B.card)
  have hne : (T.filter fun C => C ⊂ B).Nonempty := by
    refine ⟨{a}, Finset.mem_filter.mpr ⟨hS.singleton_mem a, ?_⟩⟩
    refine ⟨Finset.singleton_subset_iff.mpr ha, fun h => hab ?_⟩
    exact (Finset.mem_singleton.mp (h hb)).symm
  obtain ⟨C₀, hC₀, hmax⟩ := Finset.exists_max_image _ Finset.card hne
  obtain ⟨hC₀T, hC₀B⟩ := Finset.mem_filter.mp hC₀
  exact ⟨C₀, hC₀T, hC₀B, fun C hC hCB => hmax C (Finset.mem_filter.mpr ⟨hC, hCB⟩)⟩

/-- A side with at least two taxa has a counted pair, and with at least three, two. -/
private theorem sidePairs_ge {T : Finset (Finset X)} (hS : IsSplitFamily T) {B : Finset X}
    (hB : B ∈ T) : (2 ≤ B.card → 1 ≤ sidePairs T B) ∧ (3 ≤ B.card → 2 ≤ sidePairs T B) := by
  refine ⟨fun h2 => ?_, fun h3 => ?_⟩
  · obtain ⟨C₀, hC₀, hlt, hmax⟩ := exists_maximal hS h2
    obtain ⟨u, hu⟩ := hS.nonempty C₀ hC₀
    obtain ⟨z, hz, hzC⟩ := Finset.exists_of_ssubset hlt
    exact Finset.card_pos.mpr ⟨_, mem_pairsAt_of_maximal hS hB hC₀ hlt hmax hu hz hzC⟩
  · obtain ⟨C₀, hC₀, hlt, hmax⟩ := exists_maximal hS (by omega : 2 ≤ B.card)
    obtain ⟨u, hu⟩ := hS.nonempty C₀ hC₀
    obtain ⟨z, hz, hzC⟩ := Finset.exists_of_ssubset hlt
    suffices 1 < (pairsAt T B).card from this
    refine Finset.one_lt_card.mpr ?_
    by_cases hC₂ : 2 ≤ C₀.card
    · obtain ⟨u₁, hu₁, u₂, hu₂, hne⟩ := Finset.one_lt_card.mp (by omega : 1 < C₀.card)
      refine ⟨_, mem_pairsAt_of_maximal hS hB hC₀ hlt hmax hu₁ hz hzC, _,
        mem_pairsAt_of_maximal hS hB hC₀ hlt hmax hu₂ hz hzC, fun h => ?_⟩
      have : u₁ ∈ ({u₂, z} : Finset X) := by rw [← h]; simp
      simp only [Finset.mem_insert, Finset.mem_singleton] at this
      rcases this with h' | h'
      · exact hne h'
      · exact hzC (h' ▸ hu₁)
    · have hcard : (B \ C₀).card = B.card - C₀.card := Finset.card_sdiff_of_subset hlt.1
      obtain ⟨z₁, hz₁, z₂, hz₂, hne⟩ := Finset.one_lt_card.mp (by omega : 1 < (B \ C₀).card)
      obtain ⟨hz₁B, hz₁C⟩ := Finset.mem_sdiff.mp hz₁
      obtain ⟨hz₂B, hz₂C⟩ := Finset.mem_sdiff.mp hz₂
      refine ⟨_, mem_pairsAt_of_maximal hS hB hC₀ hlt hmax hu hz₁B hz₁C, _,
        mem_pairsAt_of_maximal hS hB hC₀ hlt hmax hu hz₂B hz₂C, fun h => ?_⟩
      have : z₁ ∈ ({u, z₂} : Finset X) := by rw [← h]; simp
      simp only [Finset.mem_insert, Finset.mem_singleton] at this
      rcases this with h' | h'
      · exact hz₁C (h' ▸ hu)
      · exact hne h'

/-- Edges have positive weight; internal edges have weight at least `2`, and for at least four taxa
so do pendant edges. -/
theorem quartetWeight_ge_two {T : Finset (Finset X)} (hT : IsUnrootedTree T)
    (hX : 4 ≤ Fintype.card X) {A : Finset X} (hA : A ∈ T) : 2 ≤ quartetWeight T A := by
  have hS : IsSplitFamily T := (isUnrootedTree_iff (by omega) T).mp hT
  have hcard : A.card + Aᶜ.card = Fintype.card X := Finset.card_add_card_compl A
  have h1 := sidePairs_ge hS hA
  have h2 := sidePairs_ge hS (hS.compl_mem A hA)
  have : 2 ≤ sidePairs T A + sidePairs T Aᶜ := by
    by_cases h3 : 3 ≤ A.card
    · have := h1.2 h3; omega
    · by_cases h3' : 3 ≤ Aᶜ.card
      · have := h2.2 h3'; omega
      · have := h1.1 (by omega); have := h2.1 (by omega); omega
  have : (2 : ℝ) ≤ ((sidePairs T A + sidePairs T Aᶜ : ℕ) : ℝ) := by exact_mod_cast this
  simpa [quartetWeight] using this

theorem quartetWeight_compl (T : Finset (Finset X)) (A : Finset X) :
    quartetWeight T Aᶜ = quartetWeight T A := by
  rw [quartetWeight, quartetWeight, compl_compl, add_comm]

/-- A tree metric with positive weights determines the tree and its weights (Buneman 1971): so
exact distance-based tree builders exist. -/
theorem exists_isExactBuilder : ∃ M : TreeBuilder X, IsExactBuilder M := by
  let Valid : (X → X → ℝ) → Finset (Finset X) × (Finset X → ℝ) → Prop := fun d p =>
    IsUnrootedTree p.1 ∧ (∀ A ∈ p.1, 0 < p.2 A ∧ p.2 Aᶜ = p.2 A) ∧ treeMetric p.1 p.2 = d
  refine ⟨fun d => if h : ∃ p, Valid d p then h.choose else (∅, 0), fun T w hT hw => ?_⟩
  have hex : ∃ p, Valid (treeMetric T w) p := ⟨(T, w), hT, hw, rfl⟩
  simp only [dite_eq_left hex]
  obtain ⟨hT', hw', heq⟩ := hex.choose_spec
  by_cases hX : 2 ≤ Fintype.card X
  · obtain ⟨h1, h2⟩ := TreeMetric.eq_of_treeMetric_eq hX hT' hT hw' hw heq
    refine ⟨hT', h1.ge, fun A hA => h2 A (by rw [h1]; exact hA), fun A hA hnA => ?_⟩
    exact absurd (h1 ▸ hA) hnA
  · have hT0 := TreeMetric.eq_empty_of_card_lt_two (by omega) hT
    have hT0' := TreeMetric.eq_empty_of_card_lt_two (by omega) hT'
    refine ⟨hT', by simp [hT0], fun A hA => ?_, fun A hA => ?_⟩
    · simp [hT0] at hA
    · simp [hT0'] at hA

end External.Rhodes2020
