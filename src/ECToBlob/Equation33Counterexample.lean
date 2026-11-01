module

public import ECToBlob.DisplayedTreeExample
public import ECToBlob.Section3
public import ECToBlob.UnitMetric

/-!
# ECToBlob, equation (3.3) as printed is false

E2 of the report. Equation (3.3) of the paper, in the proof of Theorem 3.1, says that with `X₁, …, X_k` the blocks at a multifurcation `m`,

  `f_m(T) = ∑_{ {a,b,c,d} ∈ S_m, ab|cd displayed on T } p_ab|cd = ∑_{x ∈ ∏ X_i} ∑_{x_g, x_h, x_i, x_j distinct entries of x, x_g x_h|x_i x_j displayed on T} p_{X_g X_h|X_i X_j}`.

The second sum counts a quartet once for each choice of representatives of the blocks it does not use. On a binary tree `T`, with all the probabilities of quartets
in distinct blocks equal to `c`, the left side is `c` times the number of sets of four taxa in distinct blocks (`starPart_eq_of_const`), and the right side is
`c (∏ |X_i|) C(k, 4)` (`printedRHS_eq_of_const`).

With blocks of sizes `(2, 1, 1, 1, 1)` and `c = 1/3`, this gives `3` and `10/3` (`values_of_const`). The network multispecies coalescent realizes these values, at
all valid parameters: `net` is the species tree with a cherry `0, 1` and a polytomy at its root (`values_nmsc`). This refutes the identity, not Theorem 3.1. The
repaired identity is `ECToBlob.equation3_3`, with weights by block sizes.
-/

@[expose] public noncomputable section

open Phylogenetics Phylogenetics.RootedNetwork Finset
open scoped Classical

namespace ECToBlob.Equation33Counterexample

open ECToBlob.FinNetwork

section General

variable {X : Type*} [Fintype X] [DecidableEq X]

/-- **The right side of (3.3) as printed**: the sum, over the tuples `x` of representatives of the blocks of `P`, of the probabilities of the quartet trees on
four entries of `x` that `T` displays. By assumption 2 of the paper, these probabilities depend only on the blocks. `ECToBlob.equation3_3` is the same sum with
weights by block sizes. -/
def printedRHS (P : Finset (Finset X)) (w : QuartetTree X → ℝ) (T : Finset (Finset X)) : ℝ :=
  ∑ x ∈ (univ : Finset ({B // B ∈ P} → X)).filter (fun x => ∀ B, x B ∈ B.val),
    ∑ s, if InDistinctBlocks P s.taxa ∧ Displays T s ∧ s.taxa ⊆ univ.image x then w s else 0

/-- A binary tree displays one quartet tree on each set of four taxa. -/
theorem card_filter_displays {T : Finset (Finset X)} (hT : IsBinaryTree T) (R : Finset X → Prop) [DecidablePred R]
    [DecidablePred fun s : QuartetTree X => R s.taxa ∧ Displays T s] :
    ((univ : Finset (QuartetTree X)).filter fun s => R s.taxa ∧ Displays T s).card =
      ((powersetCard 4 (univ : Finset X)).filter R).card := by
  refine card_bij (fun s _ => s.taxa) (fun s hs => ?_) (fun s hs s' hs' h => ?_) (fun q hq => ?_)
  · obtain ⟨hR, -⟩ := (mem_filter.1 hs).2
    exact mem_filter.2 ⟨mem_powersetCard.2 ⟨subset_univ _, s.card_taxa⟩, hR⟩
  · exact hT.isUnrootedTree.displays_unique (mem_filter.1 hs).2.2 (mem_filter.1 hs').2.2 h
  · obtain ⟨hq4, hR⟩ := mem_filter.1 hq
    obtain ⟨s, hs, hd⟩ := hT.exists_displays (mem_powersetCard.1 hq4).2
    have hst := mem_treesOn.1 hs
    exact ⟨s, mem_filter.2 ⟨mem_univ _, hst ▸ hR, hd⟩, hst⟩

/-- On a binary tree, with all the values on quartets in distinct blocks equal to `c`, `f_m` is `c` times the number of sets of four taxa in distinct blocks. -/
theorem starPart_eq_of_const {P : Finset (Finset X)} {w : QuartetTree X → ℝ} {T : Finset (Finset X)}
    (hT : IsBinaryTree T) {c : ℝ} (hw : ∀ s : QuartetTree X, InDistinctBlocks P s.taxa → w s = c) :
    starPart P w T = (((powersetCard 4 (univ : Finset X)).filter (InDistinctBlocks P)).card : ℝ) * c := by
  have hstep : ∀ s : QuartetTree X, (if InDistinctBlocks P s.taxa ∧ Displays T s then w s else 0) =
      if InDistinctBlocks P s.taxa ∧ Displays T s then c else 0 := by
    intro s
    split_ifs with h
    · exact hw s h.1
    · rfl
  unfold starPart
  simp only [hstep]
  rw [← sum_filter, sum_const, nsmul_eq_mul, card_filter_displays hT (InDistinctBlocks P)]

omit [Fintype X] in
/-- Entries of a tuple of representatives are in distinct blocks. -/
theorem inDistinctBlocks_of_subset_image {P : Finset (Finset X)} (hd : ∀ B ∈ P, ∀ C ∈ P, B ≠ C → Disjoint B C)
    {x : {B // B ∈ P} → X} (hx : ∀ B, x B ∈ B.val) {q : Finset X} (hq : q ⊆ univ.image x) :
    InDistinctBlocks P q := by
  intro B hB
  refine card_le_one.2 fun y hy z hz => ?_
  obtain ⟨hyB, hyq⟩ := mem_inter.1 hy
  obtain ⟨hzB, hzq⟩ := mem_inter.1 hz
  obtain ⟨b, -, rfl⟩ := mem_image.1 (hq hyq)
  obtain ⟨c, -, rfl⟩ := mem_image.1 (hq hzq)
  have hb : b = ⟨B, hB⟩ := block_eq_of_mem hd (hx b) hyB
  have hc : c = ⟨B, hB⟩ := block_eq_of_mem hd (hx c) hzB
  rw [hb, hc]

/-- The number of tuples of representatives is the product of the sizes of the blocks. -/
theorem card_reps (P : Finset (Finset X)) :
    ((univ : Finset ({B // B ∈ P} → X)).filter (fun x => ∀ B, x B ∈ B.val)).card = ∏ B ∈ P, B.card := by
  have hfil : (univ : Finset ({B // B ∈ P} → X)).filter (fun x => ∀ B, x B ∈ B.val) =
      Fintype.piFinset fun b : {B // B ∈ P} => b.val := by
    ext x
    simp [Fintype.mem_piFinset]
  rw [hfil, Fintype.card_piFinset]
  exact prod_coe_sort P fun B => B.card

/-- On a binary tree, with all the values on quartets in distinct blocks equal to `c`, the printed right side counts each tuple of representatives: it is
`c (∏ |X_i|) C(k, 4)`. -/
theorem printedRHS_eq_of_const {P : Finset (Finset X)} (hd : ∀ B ∈ P, ∀ C ∈ P, B ≠ C → Disjoint B C)
    {w : QuartetTree X → ℝ} {T : Finset (Finset X)} (hT : IsBinaryTree T) {c : ℝ}
    (hw : ∀ s : QuartetTree X, InDistinctBlocks P s.taxa → w s = c) :
    printedRHS P w T = ((∏ B ∈ P, B.card : ℕ) : ℝ) * ((P.card.choose 4 : ℕ) : ℝ) * c := by
  have hone : ∀ x ∈ (univ : Finset ({B // B ∈ P} → X)).filter (fun x => ∀ B, x B ∈ B.val),
      (∑ s : QuartetTree X, if InDistinctBlocks P s.taxa ∧ Displays T s ∧ s.taxa ⊆ univ.image x then w s else 0) =
        ((P.card.choose 4 : ℕ) : ℝ) * c := by
    intro x hx
    have hrep : ∀ B, x B ∈ B.val := (mem_filter.1 hx).2
    have hinj : Function.Injective x := fun b b' h => block_eq_of_mem hd (hrep b) (h ▸ hrep b')
    have hstep : ∀ s : QuartetTree X,
        (if InDistinctBlocks P s.taxa ∧ Displays T s ∧ s.taxa ⊆ univ.image x then w s else 0) =
          if s.taxa ⊆ univ.image x ∧ Displays T s then c else 0 := by
      intro s
      by_cases hs : s.taxa ⊆ univ.image x ∧ Displays T s
      · have hI := inDistinctBlocks_of_subset_image hd hrep hs.1
        rw [ite_eq_left ⟨hI, hs.2, hs.1⟩, ite_eq_left hs]
        exact hw s hI
      · rw [ite_eq_right fun h => hs ⟨h.2.2, h.2.1⟩, ite_eq_right hs]
    simp only [hstep]
    rw [← sum_filter, sum_const, nsmul_eq_mul, card_filter_displays hT (fun q => q ⊆ univ.image x)]
    congr 2
    have hfil : (powersetCard 4 (univ : Finset X)).filter (fun q => q ⊆ univ.image x) =
        powersetCard 4 (univ.image x) := by
      ext q
      simp only [mem_filter, mem_powersetCard, subset_univ, true_and]
      tauto
    rw [hfil, card_powersetCard, card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_coe]
  unfold printedRHS
  rw [sum_congr rfl hone, sum_const, nsmul_eq_mul, card_reps]
  ring

end General

/-! ### The blocks and the network -/

/-- The blocks of sizes `(2, 1, 1, 1, 1)`. -/
def P₀ : Finset (Finset (Fin 6)) := {{0, 1}, {2}, {3}, {4}, {5}}

theorem P₀_disjoint : ∀ B ∈ P₀, ∀ C ∈ P₀, B ≠ C → Disjoint B C := by decide

theorem P₀_cover : P₀.sup id = univ := by decide

theorem inDistinctBlocks_P₀_iff {q : Finset (Fin 6)} : InDistinctBlocks P₀ q ↔ ¬ ({0, 1} : Finset (Fin 6)) ⊆ q := by
  unfold InDistinctBlocks
  revert q
  decide +kernel

theorem card_cross : ((powersetCard 4 (univ : Finset (Fin 6))).filter (InDistinctBlocks P₀)).card = 9 := by
  have h : (powersetCard 4 (univ : Finset (Fin 6))).filter (InDistinctBlocks P₀) =
      (powersetCard 4 (univ : Finset (Fin 6))).filter fun q => ¬ ({0, 1} : Finset (Fin 6)) ⊆ q :=
    filter_congr fun q _ => inDistinctBlocks_P₀_iff
  rw [h]
  decide

/-- **E2 of the report, with abstract weights**: with blocks of sizes `(2, 1, 1, 1, 1)`, on a binary tree, with all the weights of quartets in distinct blocks `1/3`, the left
side of the printed (3.3) is `3` and the right side `10/3`. -/
theorem values_of_const {w : QuartetTree (Fin 6) → ℝ} {T : Finset (Finset (Fin 6))} (hT : IsBinaryTree T)
    (hw : ∀ s : QuartetTree (Fin 6), InDistinctBlocks P₀ s.taxa → w s = 1 / 3) :
    starPart P₀ w T = 3 ∧ printedRHS P₀ w T = 10 / 3 := by
  rw [starPart_eq_of_const hT hw, printedRHS_eq_of_const P₀_disjoint hT hw, card_cross]
  have h2 : ∏ B ∈ P₀, B.card = 2 := by decide
  have h5 : P₀.card.choose 4 = 5 := by decide
  rw [h2, h5]
  norm_num

/-- The tails of the arcs of the species tree with a polytomy at its root `7`, the taxa `2, 3, 4, 5` at the root, and the cherry `0, 1` below the vertex `6`. -/
def src : Fin 7 → Fin 8 := ![7, 7, 7, 7, 7, 6, 6]

/-- The heads of the arcs. -/
def tgt : Fin 7 → Fin 8 := ![6, 2, 3, 4, 5, 0, 1]

/-- The taxa, as vertices. -/
def lf : Fin 6 → Fin 8 := ![0, 1, 2, 3, 4, 5]

/-- What each vertex reaches. -/
def desc : Fin 8 → Finset (Fin 8) := ![{0}, {1}, {2}, {3}, {4}, {5}, {0, 1, 6}, {0, 1, 2, 3, 4, 5, 6, 7}]

/-- What the root reaches off each arc. -/
def avoid : Fin 7 → Finset (Fin 8) :=
  ![{2, 3, 4, 5, 7}, {0, 1, 3, 4, 5, 6, 7}, {0, 1, 2, 4, 5, 6, 7}, {0, 1, 2, 3, 5, 6, 7}, {0, 1, 2, 3, 4, 6, 7},
    {1, 2, 3, 4, 5, 6, 7}, {0, 2, 3, 4, 5, 6, 7}]

theorem tables : Tables src tgt 7 desc avoid :=
  ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩

/-- **The species tree realizing E2.** -/
abbrev net : RootedNetwork (Fin 8) (Fin 7) (Fin 6) := ECToBlob.FinNetwork.net src tgt 7 lf

theorem net_isPhylogenetic : net.IsPhylogenetic :=
  isPhylogenetic_of_down (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

/-- The sides of the tree of blobs. -/
theorem mem_treeOfBlobs_iff {A : Finset (Fin 6)} :
    A ∈ treeOfBlobs net ↔ A.card = 1 ∨ Aᶜ.card = 1 ∨ A = {0, 1} ∨ Aᶜ = {0, 1} := by
  rw [tables.mem_treeOfBlobs_iff net_isPhylogenetic]
  revert A
  decide

/-- **The blocks are those of the multifurcation of the tree of blobs.** -/
theorem P₀_mem_multifurcations : P₀ ∈ multifurcations (treeOfBlobs net) := by
  refine mem_multifurcations.2 ⟨⟨fun B hB => ?_, P₀_disjoint, P₀_cover, by decide, fun C hC => ?_⟩, by decide⟩
  · rw [mem_treeOfBlobs_iff]
    revert B
    decide
  · rw [mem_treeOfBlobs_iff] at hC
    revert C
    decide

/-- Four taxa in distinct blocks have a trivial 4-blob at the root. -/
theorem hasTrivialFourBlob_of_inDistinctBlocks {q : Finset (Fin 6)} (hq : q.card = 4) (hI : InDistinctBlocks P₀ q) :
    HasTrivialFourBlob net q := by
  rw [tables.hasTrivialFourBlob_iff net_isPhylogenetic hq]
  have hdec : ∀ q : Finset (Fin 6), q.card = 4 → ¬ ({0, 1} : Finset (Fin 6)) ⊆ q → HubT src tgt lf desc avoid q 7 := by
    decide
  exact ⟨7, hdec q hq (inDistinctBlocks_P₀_iff.1 hI)⟩

/-- **E2 of the report, under the coalescent**: on this species tree, at all valid parameters and for all binary trees, the left side of the printed (3.3) at the only multifurcation
is `3` and the right side `10/3`. -/
theorem values_nmsc {θ : MetricData (Fin 7)} (hθ : net.IsMetric θ) {ρ : ℝ} (hρ : 0 ≤ ρ ∧ ρ ≤ 1)
    {T : Finset (Finset (Fin 6))} (hT : IsBinaryTree T) :
    starPart P₀ (nmscCF net θ ρ) T = 3 ∧ printedRHS P₀ (nmscCF net θ ρ) T = 10 / 3 :=
  values_of_const hT fun s hs =>
    NMSC.trivial_uniform net_isPhylogenetic hθ hρ s.taxa s.card_taxa
      (hasTrivialFourBlob_of_inDistinctBlocks s.card_taxa hs) s (mem_treesOn.2 rfl)

/-- A binary tree on the six taxa, the caterpillar. -/
def caterpillar : Finset (Finset (Fin 6)) :=
  unroot {univ, {0}, {1}, {2}, {3}, {4}, {5}, {0, 1}, {0, 1, 2}, {0, 1, 2, 3}, {0, 1, 2, 3, 4}}

theorem caterpillar_isBinaryTree : IsBinaryTree caterpillar :=
  ⟨_, by unfold IsHierarchy; decide +kernel, rfl, by decide +kernel⟩

/-- **Equation (3.3) as printed** (`ecto:eq3_3_printed`): the claim for all partitions of the taxa into blocks and all binary trees. -/
def Equation33Printed : Prop :=
  ∀ {V E X : Type} [Fintype V] [Fintype E] [Fintype X] [DecidableEq X] (N : RootedNetwork V E X) (_ : N.IsPhylogenetic) (θ : MetricData E) (_ : N.IsMetric θ) (ρ : ℝ) (_ : 0 ≤ ρ ∧ ρ ≤ 1)
    (P : Finset (Finset X)) (_ : P ∈ multifurcations (treeOfBlobs N)) (T : Finset (Finset X)) (_ : IsBinaryTree T),
    starPart P (nmscCF N θ ρ) T = printedRHS P (nmscCF N θ ρ) T

/-- (`ecto:eq3_3_false`) **E2 of the report: equation (3.3) as printed is false**, under the network multispecies coalescent, at the multifurcation of `net`. The left side is `3`, and the
right side `10/3`. -/
theorem not_equation33Printed : ¬ Equation33Printed := by
  intro h
  have hθ := isMetric_unitMetric net
  have hρ : (0 : ℝ) ≤ 0 ∧ (0 : ℝ) ≤ 1 := ⟨le_rfl, zero_le_one⟩
  have he := h net net_isPhylogenetic _ hθ 0 hρ P₀ P₀_mem_multifurcations caterpillar caterpillar_isBinaryTree
  obtain ⟨h₁, h₂⟩ := values_nmsc hθ hρ caterpillar_isBinaryTree
  rw [h₁, h₂] at he
  norm_num at he

end ECToBlob.Equation33Counterexample
