module

public import Basic.Defs
public import Phylogenetics.NMSC.Basic
public import Phylogenetics.Tree.AstralDP
public import TOBQMC.WQC

/-!
# TOB-QMC §4.2: the tree that ASTRAL's dynamic program returns refines the tree of blobs

TOB-QMC (v5, embedded lines 517-521): "A corollary of Theorem 1 is that ASTRAL (version 3 or
earlier) returns a TOB refinement almost surely, as the number of gene trees goes to infinity. This is because ASTRAL
solves WQC within a constrained search space, defined by the bipartitions induced by the input gene trees, and all
bipartitions have probability strictly greater than zero under the NMSC and thus will appear as the number of gene
trees goes to infinity".

`TOBQMC.astral_corollary` speaks of the exact optima in the search space `AstralSpace`, and no algorithm appears in it.
This file runs the dynamic program of `Phylogenetics/Tree/AstralDP.lean` on the gene tree counts `geneCount`, with
the allowed clusters `astralClusters` (the default mode of Mirarab et al. 2014: "all bipartitions from the input set
of unrooted gene trees"), and shows that:

* the program returns an exact optimum in `AstralSpace` when that space is nonempty (`astral_isOptimal`);
* almost surely, the space is nonempty as soon as there is a gene tree (`ae_astralSpace_unroot`), and for all large `k`
  the program's output refines the tree of blobs (`astral_refines_treeOfBlobs`), whatever rule breaks the ties
  (`isTraceback_refines_treeOfBlobs`).

ASTRAL-II searches a larger space, the gene tree bipartitions and others that heuristics add (Mirarab and Warnow 2015,
Section 3.2); ASTRAL-III also adds to `X`. `isTraceback_refines_treeOfBlobs_of_superset` covers any allowed set
containing the gene tree bipartitions.
-/

@[expose] public noncomputable section

open Phylogenetics Phylogenetics.RootedNetwork Finset MeasureTheory
open scoped Classical

namespace TOBQMC

variable {V E X : Type*} [Fintype X] [DecidableEq X]

section Program

variable {Ω : Type*} {G : ℕ → Ω → Finset (Finset X)} {k : ℕ} {ω : Ω}

/-- The allowed clusters `X*` of ASTRAL's default mode (Mirarab et al. 2014, Section 2) on the first `k` gene trees: the
sides of their bipartitions. -/
def astralClusters (G : ℕ → Ω → Finset (Finset X)) (k : ℕ) (ω : Ω) : Finset (Finset X) :=
  (range k).biUnion fun i => unroot (G i ω)

theorem mem_astralClusters {A : Finset X} :
    A ∈ astralClusters G k ω ↔ ∃ i < k, A ∈ unroot (G i ω) := by
  simp [astralClusters]

/-- The allowed clusters are the sides of a set of bipartitions. -/
theorem compl_mem_astralClusters {A : Finset X} (h : A ∈ astralClusters G k ω) :
    Aᶜ ∈ astralClusters G k ω := by
  obtain ⟨i, hi, hA⟩ := mem_astralClusters.1 h
  exact mem_astralClusters.2 ⟨i, hi, compl_mem_unroot.2 hA⟩

/-- ASTRAL's search space `AstralSpace` is that of the dynamic program on `astralClusters`. -/
theorem astralSpace_iff {B : Finset (Finset X)} :
    AstralSpace G k ω B ↔ IsBinaryTree B ∧ B ⊆ astralClusters G k ω := by
  simp only [AstralSpace, subset_iff, mem_astralClusters]

/-- On the gene tree counts, "`W(A|B|C)` counts the number of gene tree quartets associated to tripartition
`(A|B|C)`" (Mirarab et al. 2014, Section 2). -/
theorem tripartitionWeight_geneCount (G : ℕ → Ω → Finset (Finset X)) (k : ℕ) (ω : Ω)
    (A B C : Finset X) :
    tripartitionWeight (geneCount G k ω) A B C =
      ∑ i ∈ range k,
        ((univ.filter fun s => IsAnchoredAt A B C s ∧ Displays (unroot (G i ω)) s).card : ℝ) := by
  simp only [tripartitionWeight, geneCount, card_filter, Nat.cast_sum]
  rw [sum_comm]
  refine sum_congr rfl fun s _ => ?_
  by_cases h : IsAnchoredAt A B C s <;> simp [h]

/-- The output of ASTRAL's dynamic program on the first `k` gene trees: on the gene tree counts, with the allowed
clusters of the default mode. -/
def astral (G : ℕ → Ω → Finset (Finset X)) (k : ℕ) (ω : Ω) : Finset (Finset X) :=
  astralTree (geneCount G k ω) (astralClusters G k ω)

/-- The dynamic program solves WQC exactly on its constrained search space ("ASTRAL solves WQC within a constrained
search space", TOB-QMC, embedded lines 518-519; Theorem 1 of Mirarab et al. 2014), when that space is nonempty, and
the value of the recursion at all the taxa is twice the score of the output ("`C(S)` gives the final score", which
"needs to be divided by two"). -/
theorem astral_isOptimal (h : ∃ T, AstralSpace G k ω T) :
    AstralSpace G k ω (astral G k ω) ∧
      (∀ T, AstralSpace G k ω T →
        quartetSupport (geneCount G k ω) T ≤ quartetSupport (geneCount G k ω) (astral G k ω)) ∧
      astralValue (geneCount G k ω) (astralClusters G k ω) univ =
        ((2 * quartetSupport (geneCount G k ω) (astral G k ω) : ℝ) : WithBot ℝ) := by
  obtain ⟨T, hT⟩ := h
  have hopt := astralTree_isAstralOptimal (geneCount G k ω)
    (fun _ hA => compl_mem_astralClusters hA) ⟨T, astralSpace_iff.1 hT⟩
  exact ⟨astralSpace_iff.2 ⟨hopt.isBinaryTree, hopt.subset⟩,
    fun T' hT' => hopt.le T' (astralSpace_iff.1 hT').1 (astralSpace_iff.1 hT').2, hopt.value⟩

/-- A gene tree that is binary lies in the search space, from the moment it has been seen. -/
theorem astralSpace_unroot_of_lt {i : ℕ} (hi : i < k) (h : IsBinaryHierarchy (G i ω)) :
    AstralSpace G k ω (unroot (G i ω)) :=
  ⟨⟨G i ω, h.1, rfl, (isBinaryHierarchy_iff_card_childClusters.1 h).2⟩, fun _ hA => ⟨i, hi, hA⟩⟩

end Program

section Sample

variable [Fintype V] [Fintype E] {N : RootedNetwork V E X} {θ : MetricData E} {ρ : ℝ}
  {Ω : Type*} [MeasurableSpace Ω]

/-- Gene trees are almost surely binary, from `geneTreeDist_support`. -/
theorem ae_isBinaryHierarchy (hN : N.IsPhylogenetic) [Nonempty X] {P : Measure Ω}
    [IsProbabilityMeasure P] {G : ℕ → Ω → Finset (Finset X)} (hG : IsGeneTreeSample N θ ρ P G)
    (i : ℕ) : ∀ᵐ ω ∂P, IsBinaryHierarchy (G i ω) := by
  have h : ∀ g : Finset (Finset X), ∀ᵐ ω ∂P, G i ω = g → IsBinaryHierarchy g := by
    intro g
    by_cases hg : IsBinaryHierarchy g
    · exact ae_of_all _ fun _ _ => hg
    · have h0 : geneTreeDist N θ ρ g = 0 := by
        by_contra hne
        exact hg (geneTreeDist_support hN hne)
      have h1 : P (G i ⁻¹' {g}) = 0 := by
        have hlaw := hG.law i g
        rw [h0] at hlaw
        exact (measureReal_eq_zero_iff (measure_ne_top _ _)).1 hlaw
      filter_upwards [measure_eq_zero_iff_ae_notMem.1 h1] with ω hω he
      exact absurd (Set.mem_preimage.2 (Set.mem_singleton_iff.2 he)) hω
  filter_upwards [ae_all_iff.2 h] with ω hω
  exact hω _ rfl

/-- Almost surely, the search space is nonempty as soon as there is a gene tree: it contains the first gene
tree. -/
theorem ae_astralSpace_unroot (hN : N.IsPhylogenetic) [Nonempty X] {P : Measure Ω}
    [IsProbabilityMeasure P] {G : ℕ → Ω → Finset (Finset X)} (hG : IsGeneTreeSample N θ ρ P G) :
    ∀ᵐ ω ∂P, ∀ k, 0 < k → AstralSpace G k ω (unroot (G 0 ω)) := by
  filter_upwards [ae_isBinaryHierarchy hN hG 0] with ω hω k hk
  exact astralSpace_unroot_of_lt hk hω

/-- The ASTRAL corollary of Theorem 1 (TOB-QMC §4.2, `TOBQMC.astral_corollary`), for the program under any rule for
breaking ties: almost surely, for all large `k`, every tree that backtracking can produce on the gene tree counts of
the first `k` gene trees refines the tree of blobs. The program returns an optimum in the search space
(`IsTraceback.isAstralOptimal`), and `astral_corollary` applies. -/
theorem isTraceback_refines_treeOfBlobs (hStd : StandardAssumptions N θ ρ)
    (hNon : IsTQuartetNonanomalous N (nmscCF N θ ρ)) (hX : 4 ≤ Fintype.card X)
    (P : Measure Ω) [IsProbabilityMeasure P] (G : ℕ → Ω → Finset (Finset X))
    (hG : IsGeneTreeSample N θ ρ P G) :
    ∀ᵐ ω ∂P, ∃ K, ∀ k, K ≤ k → ∀ R,
      IsTraceback (geneCount G k ω) (astralClusters G k ω) univ R → treeOfBlobs N ⊆ unroot R := by
  filter_upwards [astral_corollary hStd hNon hX P G hG] with ω ⟨K, hK⟩
  refine ⟨K, fun k hk R hR => ?_⟩
  have hopt := hR.isAstralOptimal fun _ hA => compl_mem_astralClusters hA
  exact hK k hk _ (astralSpace_iff.2 ⟨hopt.isBinaryTree, hopt.subset⟩) fun T hT =>
    hopt.le T (astralSpace_iff.1 hT).1 (astralSpace_iff.1 hT).2

/-- **The ASTRAL corollary of Theorem 1, for the program** (TOB-QMC §4.2, embedded lines 517-521: "ASTRAL (version 3
or earlier) returns a TOB refinement almost surely, as the number of gene trees goes to infinity";
`TOBQMC.astral_corollary` is its form for the optima of the search space). Under the hypotheses of `astral_corollary`,
almost surely, for all large `k`, the tree that the dynamic program returns on the first `k` gene trees is a binary tree
refining the tree of blobs. -/
theorem astral_refines_treeOfBlobs (hStd : StandardAssumptions N θ ρ)
    (hNon : IsTQuartetNonanomalous N (nmscCF N θ ρ)) (hX : 4 ≤ Fintype.card X)
    (P : Measure Ω) [IsProbabilityMeasure P] (G : ℕ → Ω → Finset (Finset X))
    (hG : IsGeneTreeSample N θ ρ P G) :
    ∀ᵐ ω ∂P, ∃ K, ∀ k, K ≤ k →
      IsBinaryTree (astral G k ω) ∧ treeOfBlobs N ⊆ astral G k ω := by
  have hne : Nonempty X := Fintype.card_pos_iff.1 (by omega)
  filter_upwards [astral_corollary hStd hNon hX P G hG,
    ae_astralSpace_unroot hStd.phylogenetic hG] with ω ⟨K, hK⟩ hspace
  refine ⟨max K 1, fun k hk => ?_⟩
  obtain ⟨hB, hopt, -⟩ := astral_isOptimal ⟨_, hspace k ((le_max_right K 1).trans hk)⟩
  exact ⟨hB.1, hK k ((le_max_left K 1).trans hk) _ hB hopt⟩

/-- Almost surely, from some point on, the search space contains all the binary trees: every bipartition of a binary
tree has positive probability, at least that of a binary gene tree inducing it (`geneTreeDist_pos`), so it appears.
This repeats a step of the proof of `TOBQMC.astral_corollary`, which does not export it. -/
theorem ae_forall_astralSpace (hStd : StandardAssumptions N θ ρ) [Nonempty X] {P : Measure Ω}
    [IsProbabilityMeasure P] {G : ℕ → Ω → Finset (Finset X)} (hG : IsGeneTreeSample N θ ρ P G) :
    ∀ᵐ ω ∂P, ∃ K, ∀ k, K ≤ k → ∀ T, IsBinaryTree T → AstralSpace G k ω T := by
  have hN := hStd.phylogenetic
  have hocc : ∀ᵐ ω ∂P, ∀ A : Finset X, (∃ H, IsBinaryHierarchy H ∧ A ∈ unroot H) →
      ∃ i, A ∈ unroot (G i ω) := by
    refine ae_all_iff.2 fun A => ?_
    by_cases hA : ∃ H, IsBinaryHierarchy H ∧ A ∈ unroot H
    · obtain ⟨H, hH, hAH⟩ := hA
      have hpos := geneTreeDist_pos hN hStd.metric hStd.rho hH
      have hsum : ∀ d : ∀ g : Finset (Finset X), Decidable (A ∈ unroot g),
          0 < ∑ g, @ite _ (A ∈ unroot g) (d g) (geneTreeDist N θ ρ g) 0 := by
        intro d
        refine lt_of_lt_of_le ?_ (single_le_sum (f := fun g =>
          @ite _ (A ∈ unroot g) (d g) (geneTreeDist N θ ρ g) 0) (fun g _ => ?_) (mem_univ H))
        · change 0 < @ite _ (A ∈ unroot H) (d H) (geneTreeDist N θ ρ H) 0
          rwa [ite_eq_left hAH]
        · split_ifs
          · exact geneTreeDist_nonneg hN hStd.metric hStd.rho g
          · exact le_rfl
      filter_upwards [ae_tendsto_freq hG (fun g => A ∈ unroot g)] with ω hω _
      obtain ⟨k, hk⟩ := (hω.eventually (lt_mem_nhds (hsum _))).exists
      by_contra hcon
      push Not at hcon
      simp [hcon] at hk
    · exact ae_of_all _ fun _ h => absurd h hA
  filter_upwards [hocc] with ω hω
  obtain ⟨K, hK⟩ : ∃ K, ∀ A : Finset X, (∃ H, IsBinaryHierarchy H ∧ A ∈ unroot H) →
      ∃ i < K, A ∈ unroot (G i ω) := by
    choose! idx hidx using hω
    obtain ⟨M, hM⟩ := ((univ : Finset (Finset X)).image idx).exists_le
    exact ⟨M + 1, fun A hA => ⟨idx A, Nat.lt_succ_of_le (hM _ (mem_image_of_mem _ (mem_univ A))),
      hidx A hA⟩⟩
  refine ⟨K, fun k hk T hT => ⟨hT, fun A hA => ?_⟩⟩
  obtain ⟨H, hH, rfl, hbin⟩ := hT
  obtain ⟨i, hi, he⟩ := hK A ⟨H, isBinaryHierarchy_iff_card_childClusters.2 ⟨hH, hbin⟩, hA⟩
  exact ⟨i, lt_of_lt_of_le hi hk, he⟩

/-- The ASTRAL corollary of Theorem 1 for a larger set of allowed bipartitions, as in ASTRAL-II, whose `X` contains the
gene tree bipartitions and others (Mirarab and Warnow 2015, Section 3.2; their Theorem 1 makes the same point for
consistency under the coalescent, for "any set X that contains those bipartitions (and perhaps others)"): almost
surely, for all large `k`, for every family `𝒳` of sides of bipartitions containing those of the first `k` gene trees,
however it depends on the data, every tree that backtracking can produce with allowed clusters `𝒳` refines the tree of
blobs. -/
theorem isTraceback_refines_treeOfBlobs_of_superset (hStd : StandardAssumptions N θ ρ)
    (hNon : IsTQuartetNonanomalous N (nmscCF N θ ρ)) (hX : 4 ≤ Fintype.card X)
    (P : Measure Ω) [IsProbabilityMeasure P] (G : ℕ → Ω → Finset (Finset X))
    (hG : IsGeneTreeSample N θ ρ P G) :
    ∀ᵐ ω ∂P, ∃ K, ∀ k, K ≤ k → ∀ 𝒳 R, astralClusters G k ω ⊆ 𝒳 → (∀ A ∈ 𝒳, Aᶜ ∈ 𝒳) →
      IsTraceback (geneCount G k ω) 𝒳 univ R → treeOfBlobs N ⊆ unroot R := by
  have hne : Nonempty X := Fintype.card_pos_iff.1 (by omega)
  filter_upwards [theorem1_optimal hStd hNon hX P G hG, ae_forall_astralSpace hStd hG] with
    ω ⟨K₀, hK₀⟩ ⟨K₁, hK₁⟩
  refine ⟨max K₀ K₁, fun k hk 𝒳 R hsub hcompl hR => ?_⟩
  have hopt := hR.isAstralOptimal hcompl
  refine hK₀ k ((le_max_left _ _).trans hk) _ hopt.isBinaryTree fun T hT => hopt.le T hT ?_
  exact (astralSpace_iff.1 (hK₁ k ((le_max_right _ _).trans hk) T hT)).2.trans hsub

end Sample

end TOBQMC
