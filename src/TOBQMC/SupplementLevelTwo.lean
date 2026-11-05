module

public import AllmanEtAl2023.CFDetectable
public import Basic.RhoOne
public import Basic.FinNetwork
public import Basic.UnitMetric
public import External.AneEtAl2024.Proposition12
public import TINNiK.Basic
public import TOBQMC.ConsistencyT3
public import TOBQMC.Implementation

/-!
# TOB-QMC supplement, Lemma 7 and Theorem 1: false at level 2

E25 of the report. The supplement states for "a directed binary species network", with no bound on its level:

* Lemma 7 (lines 494-502): an FP edge of a TOB refinement "will be successfully detected as a FP during hypothesis testing on the expected qCFs", if we select four species
  around it (1) from different blocks of the partition at the blob and (2) one of them from a block attached to the blob "via a cut edge that is incident to a reticulation
  vertex". Its proof reduces this to the induced subnetwork on these four taxa containing a 4-blob.
* Theorem 1 (lines 595-599): for a refinement of the tree of blobs, under a relaxed quartet-nonanomaly, "an algorithm `A` that contracts edges in `T|'_N` by applying hypothesis
  tests to disjoint covers of each branch is a consistent estimator of `T_N`".

Main v5 restricts these to level 1, as `TOBQMC.lemma4`, `TOBQMC.theorem2` and `TOBQMC.consistency`. This file shows that the restriction is needed.

## The network

`net` is the binary network with the printed arcs `(0,2), (1,3), (1,4), (3,6), (2,8), (6,9), (6,10), (9,12), (2,13), (13,7), (3,14), (14,5), (13,14), (0,15), (15,1), (9,16), (16,11),
(15,16)`, and the leaves `4, 5, 7, 8, 10, 11, 12`. Lean relabels the vertices so that arcs go down in the order of `Fin 17` (`relabel`, `src_eq`, `tgt_eq`, `lf_eq`), and calls the taxa
`0, …, 6`, in the order of the leaves. All its internal vertices form one blob, with the reticulations `14` and `16`; it has level `2` (`levelAt_root`, `levelAt_le_two`,
`not_isLevelOne`), and its tree of blobs is a star on seven leaves (`mem_treeOfBlobs_iff`).

The binary refinement `B` has the false edge with sides `{7, 10}` and its complement. The 3-fix-1-alter search on the blocks `{10}, {7}, {4, 5, 8}, {11, 12}` with the anchors
`10, 7, 8, 12` tests a disjoint cover of four sets (`threeFixOneAlter_eq`, `isDisjointCover_A₀`), and all four are treelike (`isTreelike_of_mem_cover`).

## What fails

* `not_supplementLemma7`: Lemma 7. `{5, 7, 10, 12}` and `{7, 8, 10, 11}` meet both conditions, and they are treelike. The expected qCFs on them are cut at all parameters
  (`not_isNonCut_of_mem_cover`).
* `not_theorem2_without_level_one`: Theorem 2 of v5 without "level 1", for the oracle on four taxa.
* `not_supplementTheorem1`: Theorem 1. At `ρ = 1`, at all valid parameters, every hypothesis holds, and for every `α_k → 0` and `β > 0`, the method keeps the false edge with
  probability tending to one (`tendsto_tobqmc_eq_treeOfBlobs_rho_one`), also with the T3 option (`tendsto_tobqmcT3_eq_treeOfBlobs_rho_one`). The same holds at `ρ = 0`, for generic parameters
  (`forGenericParams_tendsto_tobqmc_eq_treeOfBlobs`), where the concordance factors of the 4-blobs are non-cut.

This concerns disjoint covers. Testing all the sets around an edge is another matter: this edge has non-treelike sets around it, for example `{4, 7, 10, 11}` (`exists_around_not_isTreelike`).

The statistical failure is stated at `ρ = 1` and, for generic parameters, at `ρ = 0`. It needs the concordance factors on the four sets to be strictly cut. On `{7, 8, 10, 12}`, `{4, 7, 10, 12}` and `{7, 8, 10, 11}`
this is `NMSC.nmscCF_lt_of_fork` at all `ρ`, but `{5, 7, 10, 12}` has no fork, and other `ρ` are not treated here. The oracle's failure, `not_theorem2_without_level_one`, needs no parameters.
-/

@[expose] public noncomputable section

open Phylogenetics Phylogenetics.RootedNetwork Finset Filter Topology
open scoped Classical

namespace TOBQMC

/-! ### The tests on one set of four taxa -/

section Tests

variable {V E X : Type*} [Fintype V] [Fintype E] [Fintype X] [DecidableEq X] {N : RootedNetwork V E X}

/-- At a strictly cut concordance factor, TINNiK's tests judge the set of four taxa treelike, with probability tending to one: the star test rejects, and the cut test doesn't. -/
theorem tendsto_notMem_testedB (hN : N.IsPhylogenetic) {θ : MetricData E} (hθ : N.IsMetric θ) {ρ : ℝ}
    (hρ : 0 ≤ ρ ∧ ρ ≤ 1) {s : QuartetTree X} (hc : AllmanEtAl2023.IsStrictlyCutAt (nmscCF N θ ρ) s) {α : ℕ → ℝ}
    (hα₀ : Tendsto α atTop (𝓝 0)) {β : ℝ} (hβ : 0 < β) {ml : (QuartetTree X → ℝ) → Finset X → QuartetTree X}
    (hml : IsMLSelection ml) :
    Tendsto (fun k => iidProb (geneTreeDist N θ ρ) k fun ω =>
      s.taxa ∉ testedB ml (α k) β (quartetCount unroot ω)) atTop (𝓝 1) := by
  have hq := s.card_taxa
  have hne : Nonempty X := by
    obtain ⟨x, -⟩ := card_pos.1 (by omega : 0 < s.taxa.card)
    exact ⟨x⟩
  have hd : IsDist (geneTreeDist N θ ρ) := ⟨geneTreeDist_nonneg hN hθ hρ, sum_geneTreeDist hN hθ hρ⟩
  have hs := TINNiK.displaysOne_nmsc (θ := θ) (ρ := ρ) hN
  have hoff : ¬ ∀ r ∈ treesOn s.taxa, displayCF (geneTreeDist N θ ρ) unroot r = 1 / 3 := by
    intro hall
    obtain ⟨r, hr⟩ := card_pos.1 (by rw [s.card_alternatives]; norm_num : 0 < s.alternatives.card)
    refine hc.1 r hr ((hall r ?_).trans (hall s (mem_treesOn.2 rfl)).symm)
    exact mem_treesOn.2 (QuartetTree.mem_alternatives.1 hr).1
  have hstar := TINNiK.tendsto_star hd hs hq hoff hβ
  refine tendsto_iidProb_of_imp hd (Eventually.of_forall fun k ω hω => ?_)
    (TINNiK.tendsto_iidProb_and hd hstar (TINNiK.tendsto_good_cut hN hθ hρ hα₀ hml hc))
  obtain ⟨hω₁, hmlq, hω₃⟩ := hω
  rintro ⟨-, h | h⟩
  · exact absurd h (not_le.2 hω₁)
  · rw [hmlq] at h
    exact absurd h (not_lt.2 hω₃)

/-- At a strictly T1 concordance factor, TINNiK's tests with the T3 option judge the set of four taxa treelike, with probability tending to one. -/
theorem tendsto_notMem_testedBT3 (hN : N.IsPhylogenetic) {θ : MetricData E} (hθ : N.IsMetric θ) {ρ : ℝ}
    (hρ : 0 ≤ ρ ∧ ρ ≤ 1) {s : QuartetTree X} (hc : IsT1Strict (nmscCF N θ ρ) s) {α : ℕ → ℝ}
    (hα₀ : Tendsto α atTop (𝓝 0)) {β : ℝ} (hβ : 0 < β) {ml : (QuartetTree X → ℝ) → Finset X → QuartetTree X}
    (hml : TINNiK.IsT3MLSelection ml) :
    Tendsto (fun k => iidProb (geneTreeDist N θ ρ) k fun ω =>
      s.taxa ∉ TINNiK.testedBT3 ml (α k) β (quartetCount unroot ω)) atTop (𝓝 1) := by
  have hq := s.card_taxa
  have hne : Nonempty X := by
    obtain ⟨x, -⟩ := card_pos.1 (by omega : 0 < s.taxa.card)
    exact ⟨x⟩
  have hd : IsDist (geneTreeDist N θ ρ) := ⟨geneTreeDist_nonneg hN hθ hρ, sum_geneTreeDist hN hθ hρ⟩
  have hs := TINNiK.displaysOne_nmsc (θ := θ) (ρ := ρ) hN
  have hoff : ¬ ∀ r ∈ treesOn s.taxa, displayCF (geneTreeDist N θ ρ) unroot r = 1 / 3 := by
    intro hall
    obtain ⟨r, hr⟩ := card_pos.1 (by rw [s.card_alternatives]; norm_num : 0 < s.alternatives.card)
    refine (hc.1 r hr).ne ((hall r ?_).trans (hall s (mem_treesOn.2 rfl)).symm)
    exact mem_treesOn.2 (QuartetTree.mem_alternatives.1 hr).1
  have hstar := TINNiK.tendsto_star hd hs hq hoff hβ
  have hnull := QuartetTests.t3Test_null hd hs (s := s) hc (fun r _ => nmscCF_pos hN hθ hρ r) hα₀
  refine tendsto_iidProb_of_imp hd (Eventually.of_forall fun k ω hω => ?_)
    (TINNiK.tendsto_iidProb_and hd hstar hnull)
  obtain ⟨hω₁, hω₂, hω₃⟩ := hω
  rintro ⟨-, h | h⟩
  · exact absurd h (not_le.2 hω₁)
  · have hmlq : ml (quartetCount unroot ω) s.taxa = s := by
      obtain ⟨hm1, hm2⟩ := hml (quartetCount unroot ω) s.taxa hq
      by_contra hneq
      have halt : ml (quartetCount unroot ω) s.taxa ∈ s.alternatives :=
        QuartetTree.mem_alternatives.2 ⟨mem_treesOn.1 hm1, hneq⟩
      exact absurd (hm2 s (mem_treesOn.2 rfl)) (not_le.2 (hω₂ _ halt))
    rw [hmlq] at h
    exact absurd h (not_lt.2 hω₃)

end Tests

/-- **The relaxed quartet-nonanomaly of the supplement's Definition 1**, its condition 1 (lines 294-295): on a set of four taxa, a quartet that is the only one the display trees
induce has at least the probability of the two others. -/
def IsRelaxedNonanomalous {V E X : Type*} [Fintype V] [Fintype E] [Fintype X] [DecidableEq X]
    (N : RootedNetwork V E X) (θ : MetricData E) (ρ : ℝ) : Prop :=
  ∀ q : Finset X, q.card = 4 → ∀ s ∈ treesOn q, (∀ r ∈ treesOn q, External.AneEtAl2024.IsDisplayed N r → r = s) →
    ∀ r ∈ s.alternatives, nmscCF N θ ρ r ≤ nmscCF N θ ρ s

/-- Every network is relaxed quartet-nonanomalous at `ρ = 1`: Proposition 12 of Ané et al. 2024. -/
theorem isRelaxedNonanomalous_rho_one {V E X : Type*} [Fintype V] [Fintype E] [Fintype X] [DecidableEq X]
    {N : RootedNetwork V E X} (hN : N.IsPhylogenetic) {θ : MetricData E} (hθ : N.IsMetric θ) :
    IsRelaxedNonanomalous N θ 1 := by
  intro q hq s hs hone r hr
  obtain ⟨hrt, hne⟩ := QuartetTree.mem_alternatives.1 hr
  have hsq := mem_treesOn.1 hs
  exact External.AneEtAl2024.nmscCF_rho_one_le_of_not_isDisplayed hN hθ.isWeakMetric hq
    (mem_treesOn.2 (hrt.trans hsq)) hs fun hd => hne (hone r (mem_treesOn.2 (hrt.trans hsq)) hd)

/-- A taxon `x` is in a block attached to the blob of `v` via a cut edge incident to a reticulation of the blob: condition 2 of Lemma 7 of the supplement. -/
def AttachesAtReticulation {V E X : Type*} (N : RootedNetwork V E X) (v : V) (x : X) : Prop :=
  ∃ h g, N.graph.blobSetoid v h ∧ 2 ≤ N.graph.indegree h ∧ N.graph.source g = h ∧ N.graph.underlying.IsBridge g ∧ N.IsBelow g x

/-- **Lemma 7 of the supplement, as printed, at its proof's reduction**: for a binary network and a refinement of its tree of blobs with a false edge refining the blob of `v`, a set of four
taxa around the edge in distinct blocks at the blob, one of them attached at a reticulation, is not treelike. -/
def SupplementLemma7 : Prop :=
  ∀ {V E X : Type} [Fintype V] [Fintype E] [Fintype X] [DecidableEq X] (N : RootedNetwork V E X), N.IsPhylogenetic → N.IsBinary →
    ∀ (B : Finset (Finset X)) (v : V) (A : Finset X), IsUnrootedTree B → treeOfBlobs N ⊆ B → A ∈ internalSides B → A ∉ treeOfBlobs N →
      RefinesBlob N A v → ∀ Y : Finset X, Y.card = 4 → (A ∩ Y).card = 2 → (∀ x ∈ Y, ∀ y ∈ Y, x ≠ y → ¬ SameBlock N v x y) →
        (∃ x ∈ Y, AttachesAtReticulation N v x) → ¬ IsTreelike N Y

/-- **Theorem 2 of v5 without "level 1"**: `TOBQMC.theorem2` with its hypothesis on the level left out, as the supplement's Theorem 1 claims for the oracle on four taxa. -/
def Theorem2WithoutLevelOne : Prop :=
  ∀ {V E X : Type} [Fintype V] [Fintype E] [Fintype X] [DecidableEq X] (N : RootedNetwork V E X), N.IsPhylogenetic → N.IsBinary →
    ∀ B : Finset (Finset X), IsUnrootedTree B → treeOfBlobs N ⊆ B → ∀ Q : Finset X → Finset (Finset X),
      (∀ A ∈ internalSides B, IsDisjointCover B A (Q A)) →
      contractSides B ((internalSides B).filter fun A => ∃ Y ∈ Q A, ¬ IsTreelike N Y) = treeOfBlobs N

/-- **Theorem 1 of the supplement, as printed**: for a binary metric network under a relaxed quartet-nonanomaly, read as both conditions 1 of the supplement's Definition 1 and T-quartet-nonanomaly, and
any binary refinement of its tree of blobs with disjoint covers, TINNiK's tests on the covers give a consistent estimator of the tree of blobs. The levels are as in `TOBQMC.consistency`. -/
def SupplementTheorem1 : Prop :=
  ∀ {V E X : Type} [Fintype V] [Fintype E] [Fintype X] [DecidableEq X] (N : RootedNetwork V E X) (θ : MetricData E) (ρ : ℝ),
    StandardAssumptions N θ ρ → IsRelaxedNonanomalous N θ ρ → IsTQuartetNonanomalous N (nmscCF N θ ρ) → 4 ≤ Fintype.card X →
    ∀ B : Finset (Finset X), IsBinaryTree B → treeOfBlobs N ⊆ B → ∀ Q : Finset X → Finset (Finset X),
      (∀ A ∈ internalSides B, IsDisjointCover B A (Q A)) →
      ∃ α : ℕ → ℝ, Tendsto α atTop (𝓝 0) ∧ (∀ k, 0 < α k) ∧ ∀ β : ℝ, 0 < β →
        ∀ ml : (QuartetTree X → ℝ) → Finset X → QuartetTree X, IsMLSelection ml →
          Tendsto (fun k => iidProb (geneTreeDist N θ ρ) k fun ω =>
            tobqmc ml (α k) β (quartetCount unroot ω) B Q = treeOfBlobs N) atTop (𝓝 1)

namespace LevelTwo

open ECToBlob.FinNetwork ECToBlob.FalseEdge ECToBlob.Coarsening

/-! ### The network -/

/-- The tails of the printed arcs, on the printed vertices. -/
def printedSrc : Fin 18 → Fin 17 := ![0, 1, 1, 3, 2, 6, 6, 9, 2, 13, 3, 14, 13, 0, 15, 9, 16, 15]

/-- The heads of the printed arcs, on the printed vertices. -/
def printedTgt : Fin 18 → Fin 17 := ![2, 3, 4, 6, 8, 9, 10, 12, 13, 7, 14, 5, 14, 15, 1, 16, 11, 16]

/-- The printed leaves. -/
def printedLeaf : Fin 7 → Fin 17 := ![4, 5, 7, 8, 10, 11, 12]

/-- The relabelling of the printed vertices: the leaves first, and arcs go down. -/
def relabel : Fin 17 → Fin 17 := ![16, 12, 15, 11, 0, 1, 10, 2, 3, 9, 4, 5, 6, 14, 8, 13, 7]

/-- The tails of the arcs. -/
def src : Fin 18 → Fin 17 := ![16, 12, 12, 11, 15, 10, 10, 9, 15, 14, 11, 8, 14, 16, 13, 9, 7, 13]

/-- The heads of the arcs. -/
def tgt : Fin 18 → Fin 17 := ![15, 11, 0, 10, 3, 9, 4, 6, 14, 2, 8, 1, 8, 13, 12, 7, 5, 7]

/-- The taxa, as vertices. -/
def lf : Fin 7 → Fin 17 := ![0, 1, 2, 3, 4, 5, 6]

theorem relabel_bijective : Function.Bijective relabel := by decide +kernel

theorem src_eq : ∀ f, src f = relabel (printedSrc f) := by decide +kernel

theorem tgt_eq : ∀ f, tgt f = relabel (printedTgt f) := by decide +kernel

theorem lf_eq : ∀ x, lf x = relabel (printedLeaf x) := by decide +kernel

/-- What each vertex reaches. -/
def desc : Fin 17 → Finset (Fin 17) :=
  ![{0}, {1}, {2}, {3}, {4}, {5}, {6}, {5, 7}, {1, 8}, {5, 6, 7, 9}, {4, 5, 6, 7, 9, 10}, {1, 4, 5, 6, 7, 8, 9, 10, 11},
    {0, 1, 4, 5, 6, 7, 8, 9, 10, 11, 12}, {0, 1, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13}, {1, 2, 8, 14}, {1, 2, 3, 8, 14, 15},
    {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16}]

/-- What the root reaches off each arc. -/
def avoid : Fin 18 → Finset (Fin 17) :=
  ![{0, 1, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 16}, {0, 1, 2, 3, 5, 7, 8, 12, 13, 14, 15, 16},
    {1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16}, {0, 1, 2, 3, 5, 7, 8, 11, 12, 13, 14, 15, 16},
    {0, 1, 2, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16}, {0, 1, 2, 3, 4, 5, 7, 8, 10, 11, 12, 13, 14, 15, 16},
    {0, 1, 2, 3, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16}, {0, 1, 2, 3, 4, 5, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16},
    {0, 1, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 15, 16}, {0, 1, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16},
    {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16}, {0, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16},
    {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16}, {1, 2, 3, 8, 14, 15, 16},
    {1, 2, 3, 5, 7, 8, 13, 14, 15, 16}, {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16},
    {0, 1, 2, 3, 4, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16}, {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16}]

theorem tables : Tables src tgt 16 desc avoid :=
  ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel⟩

/-- **The network of E25.** -/
abbrev net : RootedNetwork (Fin 17) (Fin 18) (Fin 7) := ECToBlob.FinNetwork.net src tgt 16 lf

theorem net_isPhylogenetic : net.IsPhylogenetic :=
  isPhylogenetic_of_down (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)

theorem indegree_eq (v : Fin 17) : net.graph.indegree v = (univ.filter fun e => tgt e = v).card := by
  rw [DirectedMultigraph.indegree, Set.ncard_eq_toFinset_card']
  congr 1
  ext e
  simp [ECToBlob.FinNetwork.net]

theorem outdegree_eq (v : Fin 17) : net.graph.outdegree v = (univ.filter fun e => src e = v).card := by
  rw [DirectedMultigraph.outdegree, Set.ncard_eq_toFinset_card']
  congr 1
  ext e
  simp [ECToBlob.FinNetwork.net]

/-- It is binary. -/
theorem net_isBinary : net.IsBinary := by
  refine ⟨?_, fun v hv ho => ?_⟩
  · rw [outdegree_eq]
    decide +kernel
  · rw [outdegree_eq] at ho
    rw [indegree_eq, outdegree_eq]
    revert v
    decide +kernel

/-- The reticulations are the printed `16` and `14`. -/
theorem two_le_indegree_iff {v : Fin 17} : 2 ≤ net.graph.indegree v ↔ v = 7 ∨ v = 8 := by
  rw [indegree_eq]
  revert v
  decide +kernel

/-- **The tree of blobs is the star on seven leaves.** -/
theorem mem_treeOfBlobs_iff {A : Finset (Fin 7)} : A ∈ treeOfBlobs net ↔ A.card = 1 ∨ Aᶜ.card = 1 := by
  rw [tables.mem_treeOfBlobs_iff net_isPhylogenetic]
  revert A
  decide +kernel

/-- The tree of blobs resolves no four taxa. -/
theorem not_displays (s : QuartetTree (Fin 7)) : ¬ Displays (treeOfBlobs net) s := by
  rintro ⟨A, hA, hs⟩
  have h2 : (A ∩ s.taxa).card = 2 := s.2.2.1 _ hs
  have h4 : s.taxa.card = 4 := s.card_taxa
  rcases mem_treeOfBlobs_iff.1 hA with h | h
  · have : (A ∩ s.taxa).card ≤ A.card := card_le_card inter_subset_left
    omega
  · have h3 : (s.taxa \ A).card ≤ Aᶜ.card := card_le_card fun x hx => mem_compl.2 (mem_sdiff.1 hx).2
    have h5 := card_inter_add_card_sdiff s.taxa A
    rw [inter_comm] at h5
    omega

/-- T-quartet-nonanomaly holds vacuously, since the tree of blobs is a star. -/
theorem isTQuartetNonanomalous (F : QuartetTree (Fin 7) → ℝ) : IsTQuartetNonanomalous net F :=
  fun s hs => absurd hs (not_displays s)

/-! ### The blob and its level -/

/-- The bridges are the pendant arcs. -/
theorem isBridge_iff {e : Fin 18} : net.graph.underlying.IsBridge e ↔ (tgt e).val < 7 := by
  rw [Level1.isBridge_iff_reaches net_isPhylogenetic]
  have h : ∀ e f : Fin 18, net.graph.Reaches (net.graph.target e) (net.graph.target f) ↔ tgt f ∈ desc (tgt e) :=
    fun _ _ => tables.reaches_iff
  have h' : ∀ e f : Fin 18, net.graph.Reaches (net.graph.target e) (net.graph.source f) ↔ src f ∈ desc (tgt e) :=
    fun _ _ => tables.reaches_iff
  simp only [h, h']
  revert e
  decide +kernel

/-- All the internal vertices are in the blob of the root. -/
theorem sameBlob_root {u : Fin 17} (hu : 7 ≤ u.val) : net.graph.blobSetoid 16 u := by
  have hpar : ∀ u : Fin 17, 7 ≤ u.val → u ≠ 16 → ∃ e, tgt e = u ∧ 7 ≤ (src e).val ∧ u.val < (src e).val := by
    decide +kernel
  have key : ∀ n, ∀ u : Fin 17, 16 - u.val = n → 7 ≤ u.val → net.graph.blobSetoid 16 u := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro u hn hu
      by_cases h16 : u = 16
      · rw [h16]
      · obtain ⟨e, rfl, hs, hlt⟩ := hpar u hu h16
        have hb : ¬ net.graph.underlying.IsBridge e := fun h => by
          have := isBridge_iff.1 h
          omega
        have hsl := (src e).isLt
        exact Level1.sameBlob_trans (ih (16 - (src e).val) (by omega) (src e) rfl hs)
          (Level1.sameBlob_of_not_isBridge hb)
  exact key _ u rfl hu

/-- The leaves are not in the blob of the root. -/
theorem not_sameBlob_leaf (x : Fin 7) : ¬ net.graph.blobSetoid 16 (net.leaf x) :=
  Level1.leaf_not_sameBlob net_isPhylogenetic (h := 8) (sameBlob_root (by decide)) (two_le_indegree_iff.2 (Or.inr rfl)) x

/-- Distinct taxa are in distinct blocks at the blob: each block is a single taxon. -/
theorem eq_of_sameBlock {x y : Fin 7} (h : SameBlock net 16 x y) : x = y := by
  rcases Relation.ReflTransGen.cases_head h with he | ⟨c, ⟨hna, hnc, e, he⟩, -⟩
  · exact net_isPhylogenetic.leaf_injective he
  · exfalso
    have hs : ∀ e : Fin 18, 7 ≤ (src e).val := by decide +kernel
    have hb : net.graph.blobSetoid 16 (net.graph.source e) := sameBlob_root (hs e)
    rcases he with ⟨h1, -⟩ | ⟨h1, -⟩
    · exact hna (h1 ▸ hb)
    · exact hnc (h1 ▸ hb)

/-- Every edge refines the blob, since each block is a single taxon. -/
theorem refinesBlob (A : Finset (Fin 7)) : RefinesBlob net A 16 := fun x y h => by rw [eq_of_sameBlock h]

/-- The level of the blob of `v`, in the terms of `RootedNetwork.IsLevelOne`. -/
def levelAt {V E X : Type*} [Fintype V] [Fintype E] (N : RootedNetwork V E X) (v : V) : ℤ :=
  ((univ.filter fun e => N.IsHybridArc e ∧ N.graph.blobSetoid v (N.graph.source e) ∧
      N.graph.blobSetoid v (N.graph.target e)).card : ℤ) -
    ((univ.filter fun u => 2 ≤ N.graph.indegree u ∧ N.graph.blobSetoid v u).card : ℤ)

/-- **The blob has level two**: four reticulation arcs and two reticulations. -/
theorem levelAt_root : levelAt net 16 = 2 := by
  have hH : (univ.filter fun e => net.IsHybridArc e ∧ net.graph.blobSetoid 16 (net.graph.source e) ∧
      net.graph.blobSetoid 16 (net.graph.target e)) = {10, 12, 15, 17} := by
    have h₁ : ∀ e : Fin 18, (tgt e = 7 ∨ tgt e = 8) ↔ e ∈ ({10, 12, 15, 17} : Finset (Fin 18)) := by decide +kernel
    have h₂ : ∀ e : Fin 18, e ∈ ({10, 12, 15, 17} : Finset (Fin 18)) → 7 ≤ (src e).val ∧ 7 ≤ (tgt e).val := by decide +kernel
    ext e
    simp only [mem_filter, mem_univ, true_and]
    constructor
    · rintro ⟨h, -⟩
      exact (h₁ e).1 (two_le_indegree_iff.1 h)
    · intro he
      exact ⟨two_le_indegree_iff.2 ((h₁ e).2 he), sameBlob_root (h₂ e he).1, sameBlob_root (h₂ e he).2⟩
  have hR : (univ.filter fun u => 2 ≤ net.graph.indegree u ∧ net.graph.blobSetoid 16 u) = {7, 8} := by
    ext u
    simp only [mem_filter, mem_univ, true_and, mem_insert, mem_singleton]
    constructor
    · exact fun h => two_le_indegree_iff.1 h.1
    · rintro (rfl | rfl)
      · exact ⟨two_le_indegree_iff.2 (Or.inl rfl), sameBlob_root (by decide)⟩
      · exact ⟨two_le_indegree_iff.2 (Or.inr rfl), sameBlob_root (by decide)⟩
  unfold levelAt
  rw [hH, hR]
  decide

/-- The network has level at most two. -/
theorem levelAt_le_two (v : Fin 17) : levelAt net v ≤ 2 := by
  by_cases hv : net.graph.blobSetoid 16 v
  · have hiff : ∀ u, net.graph.blobSetoid v u ↔ net.graph.blobSetoid 16 u := fun u =>
      ⟨fun h => Level1.sameBlob_trans hv h, fun h => Level1.sameBlob_trans (Level1.sameBlob_symm hv) h⟩
    have : levelAt net v = levelAt net 16 := by
      unfold levelAt
      simp only [hiff]
    rw [this, levelAt_root]
  · have hzero : (univ.filter fun e => net.IsHybridArc e ∧ net.graph.blobSetoid v (net.graph.source e) ∧
        net.graph.blobSetoid v (net.graph.target e)) = ∅ := by
      refine filter_eq_empty_iff.2 fun e _ he => hv ?_
      have ht := two_le_indegree_iff.1 he.1
      have hb : net.graph.blobSetoid 16 (net.graph.target e) := by
        refine sameBlob_root ?_
        change 7 ≤ (tgt e).val
        change tgt e = 7 ∨ tgt e = 8 at ht
        rcases ht with h | h <;> rw [h] <;> decide
      exact Level1.sameBlob_trans hb (Level1.sameBlob_symm he.2.2)
    unfold levelAt
    rw [hzero]
    simp only [card_empty, Nat.cast_zero, zero_sub]
    have : (0 : ℤ) ≤ ((univ.filter fun u => 2 ≤ net.graph.indegree u ∧ net.graph.blobSetoid v u).card : ℤ) :=
      Int.natCast_nonneg _
    omega

/-- **The network is not level-1.** -/
theorem not_isLevelOne : ¬ net.IsLevelOne := by
  intro h
  have h16 : levelAt net 16 ≤ 1 := h 16
  rw [levelAt_root] at h16
  omega

/-! ### The refinement and the cover -/

/-- A rooting of the refinement. -/
def H₀ : Finset (Finset (Fin 7)) :=
  {univ, {0}, {1}, {2}, {3}, {4}, {5}, {6}, {2, 4}, {0, 1}, {0, 1, 3}, {5, 6}, {0, 1, 3, 5, 6}}

/-- **The binary refinement of the tree of blobs**: `(7, 10)`, `((4, 5), 8)` and `(11, 12)` around one vertex. -/
def B : Finset (Finset (Fin 7)) := unroot H₀

theorem B_isBinaryTree : IsBinaryTree B :=
  ⟨H₀, by unfold IsHierarchy H₀; decide +kernel, rfl, by unfold H₀; decide +kernel⟩

theorem treeOfBlobs_subset : treeOfBlobs net ⊆ B := by
  intro A hA
  rw [mem_treeOfBlobs_iff] at hA
  unfold B H₀ unroot
  revert A
  decide +kernel

/-- The side `{7, 10}` of the false edge. -/
def A₀ : Finset (Fin 7) := {2, 4}

theorem A₀_mem_internalSides : A₀ ∈ internalSides B := by
  unfold internalSides B H₀ unroot A₀
  decide +kernel

theorem A₀_compl_mem_internalSides : A₀ᶜ ∈ internalSides B := by
  unfold internalSides B H₀ unroot A₀
  decide +kernel

/-- **The edge is false.** -/
theorem A₀_notMem_treeOfBlobs : A₀ ∉ treeOfBlobs net := by
  rw [mem_treeOfBlobs_iff]
  decide

/-- The blocks `{10}, {7}, {4, 5, 8}, {11, 12}`. -/
def P : Fin 4 → Finset (Fin 7) := ![{4}, {2}, {0, 1, 3}, {5, 6}]

/-- The anchors `10, 7, 8, 12`. -/
def z : Fin 4 → Fin 7 := ![4, 2, 3, 6]

/-- The same blocks, from the other side of the edge. -/
def P' : Fin 4 → Finset (Fin 7) := ![{0, 1, 3}, {5, 6}, {4}, {2}]

/-- The same anchors, from the other side of the edge. -/
def z' : Fin 4 → Fin 7 := ![3, 6, 4, 2]

/-- **The four sets of the cover**: `{7, 8, 10, 12}`, `{4, 7, 10, 12}`, `{5, 7, 10, 12}`, `{7, 8, 10, 11}`. -/
def cover : Finset (Finset (Fin 7)) := {{2, 3, 4, 6}, {0, 2, 4, 6}, {1, 2, 4, 6}, {2, 3, 4, 5}}

theorem threeFixOneAlter_eq : threeFixOneAlter P z = cover := by decide +kernel

theorem threeFixOneAlter_eq' : threeFixOneAlter P' z' = cover := by decide +kernel

/-- **The 3-fix-1-alter search tests a disjoint cover around the false edge.** -/
theorem isDisjointCover_A₀ : IsDisjointCover B A₀ cover := by
  have h := (threeFixOneAlter_isDisjointCover B_isBinaryTree A₀_mem_internalSides P (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by unfold B H₀ unroot; decide +kernel) z (by decide +kernel)).1
  rwa [threeFixOneAlter_eq] at h

/-- The same around the other side. -/
theorem isDisjointCover_A₀_compl : IsDisjointCover B A₀ᶜ cover := by
  have h := (threeFixOneAlter_isDisjointCover B_isBinaryTree A₀_compl_mem_internalSides P' (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by unfold B H₀ unroot; decide +kernel) z' (by decide +kernel)).1
  rwa [threeFixOneAlter_eq'] at h

/-- A selection of disjoint covers of the edges of `B`, with `cover` at the false edge. -/
def Q₀ (A : Finset (Fin 7)) : Finset (Finset (Fin 7)) :=
  if A = A₀ ∨ A = A₀ᶜ then cover else if h : A ∈ internalSides B then (exists_isDisjointCover B_isBinaryTree h).choose else ∅

theorem Q₀_A₀ : Q₀ A₀ = cover := by simp [Q₀]

theorem Q₀_A₀_compl : Q₀ A₀ᶜ = cover := by simp [Q₀]

theorem Q₀_isDisjointCover : ∀ A ∈ internalSides B, IsDisjointCover B A (Q₀ A) := by
  intro A hA
  by_cases h₁ : A = A₀
  · rw [h₁, Q₀_A₀]
    exact isDisjointCover_A₀
  · by_cases h₂ : A = A₀ᶜ
    · rw [h₂, Q₀_A₀_compl]
      exact isDisjointCover_A₀_compl
    · have : Q₀ A = (exists_isDisjointCover B_isBinaryTree hA).choose := by
        simp [Q₀, h₁, h₂, hA]
      rw [this]
      exact (exists_isDisjointCover B_isBinaryTree hA).choose_spec

/-! ### All the sets of the cover are treelike -/

/-- The quartet tree `78|10,12`, by the printed taxa. -/
def s₁ : QuartetTree (Fin 7) := quartetTree 2 3 4 6 (by decide)

/-- The quartet tree `47|10,12`. -/
def s₂ : QuartetTree (Fin 7) := quartetTree 0 2 4 6 (by decide)

/-- The quartet tree `57|10,12`. -/
def s₃ : QuartetTree (Fin 7) := quartetTree 1 2 4 6 (by decide)

/-- The quartet tree `78|10,11`. -/
def s₄ : QuartetTree (Fin 7) := quartetTree 2 3 4 5 (by decide)

/-- The quartet trees of the sets of the cover. -/
def quartets : Fin 4 → QuartetTree (Fin 7) := ![s₁, s₂, s₃, s₄]

theorem inducedCutSplit_quartets (i : Fin 4) : InducedCutSplit net (quartets i) := by
  fin_cases i
  · exact inducedCutSplit_of_rdom net_isPhylogenetic (by decide) (tables.rdom_iff.2 (by decide +kernel))
  · exact inducedCutSplit_of_rdom net_isPhylogenetic (by decide) (tables.rdom_iff.2 (by decide +kernel))
  · exact inducedCutSplit_of_rdom net_isPhylogenetic (by decide) (tables.rdom_iff.2 (by decide +kernel))
  · exact inducedCutSplit_of_rdom net_isPhylogenetic (by decide) (tables.rdom_iff.2 (by decide +kernel))

theorem exists_quartets_of_mem_cover {Y : Finset (Fin 7)} (hY : Y ∈ cover) : ∃ i, (quartets i).taxa = Y := by
  simp only [cover, mem_insert, mem_singleton] at hY
  rcases hY with rfl | rfl | rfl | rfl
  · exact ⟨0, taxa_quartetTree (by decide)⟩
  · exact ⟨1, taxa_quartetTree (by decide)⟩
  · exact ⟨2, taxa_quartetTree (by decide)⟩
  · exact ⟨3, taxa_quartetTree (by decide)⟩

/-- **Every set of the cover is treelike**, though the edge is false. -/
theorem isTreelike_of_mem_cover {Y : Finset (Fin 7)} (hY : Y ∈ cover) : IsTreelike net Y := by
  obtain ⟨i, rfl⟩ := exists_quartets_of_mem_cover hY
  exact ⟨_, mem_treesOn.2 rfl, inducedCutSplit_quartets i⟩

/-- **The expected concordance factors on the sets of the cover are cut**, at all valid parameters: hypothesis testing on them finds no 4-blob. -/
theorem not_isNonCut_of_mem_cover {θ : MetricData (Fin 18)} (hθ : net.IsMetric θ) {ρ : ℝ} (hρ : 0 ≤ ρ ∧ ρ ≤ 1)
    {Y : Finset (Fin 7)} (hY : Y ∈ cover) : ¬ AllmanEtAl2023.IsNonCut (nmscCF net θ ρ) Y := by
  obtain ⟨i, rfl⟩ := exists_quartets_of_mem_cover hY
  intro hnc
  obtain ⟨r, hr, r', hr', hne⟩ := Finset.one_lt_card.1
    (by rw [(quartets i).card_alternatives]; norm_num : 1 < (quartets i).alternatives.card)
  exact hnc r (mem_treesOn.2 (QuartetTree.mem_alternatives.1 hr).1) r' (mem_treesOn.2 (QuartetTree.mem_alternatives.1 hr').1) hne
    (NMSC.cut_alternatives net_isPhylogenetic hθ hρ _ (inducedCutSplit_quartets i) r hr r' hr')

/-- Testing all the sets around the edge is another matter: `{4, 7, 10, 11}` is around the false edge, and it is not treelike. No disjoint cover has to contain it. -/
theorem exists_around_not_isTreelike : ∃ Y : Finset (Fin 7), Y.card = 4 ∧ (A₀ ∩ Y).card = 2 ∧ ¬ IsTreelike net Y := by
  refine ⟨{0, 2, 4, 5}, by decide, by decide, ?_⟩
  rintro ⟨s, hs, hc⟩
  obtain ⟨a, b, c, d, hcard, rfl, hr⟩ := exists_rdom_of_inducedCutSplit net_isPhylogenetic hc
  have ht := mem_treesOn.1 hs
  rw [taxa_quartetTree] at ht
  have hdec : ∀ a b c d : Fin 7, ({a, b, c, d} : Finset (Fin 7)) = {0, 2, 4, 5} → ¬ RDomT tgt lf desc avoid a b c d := by
    decide +kernel
  exact hdec a b c d ht (tables.rdom_iff.1 hr)

/-! ### Lemma 7 -/

/-- The taxon `5` attaches at the reticulation `14`. -/
theorem attachesAtReticulation_one : AttachesAtReticulation net 16 1 := by
  have h₁ : net.graph.blobSetoid 16 8 := sameBlob_root (by decide)
  have h₂ : 2 ≤ net.graph.indegree 8 := two_le_indegree_iff.2 (Or.inr rfl)
  have h₃ : net.graph.source 11 = 8 := by decide +kernel
  have h₄ : net.graph.underlying.IsBridge 11 := isBridge_iff.2 (by decide +kernel)
  have h₅ : net.IsBelow 11 1 := tables.isBelow_iff.2 (by decide +kernel)
  exact ⟨8, 11, h₁, h₂, h₃, h₄, h₅⟩

/-- The taxon `11` attaches at the reticulation `16`. -/
theorem attachesAtReticulation_five : AttachesAtReticulation net 16 5 := by
  have h₁ : net.graph.blobSetoid 16 7 := sameBlob_root (by decide)
  have h₂ : 2 ≤ net.graph.indegree 7 := two_le_indegree_iff.2 (Or.inl rfl)
  have h₃ : net.graph.source 16 = 7 := by decide +kernel
  have h₄ : net.graph.underlying.IsBridge 16 := isBridge_iff.2 (by decide +kernel)
  have h₅ : net.IsBelow 16 5 := tables.isBelow_iff.2 (by decide +kernel)
  exact ⟨7, 16, h₁, h₂, h₃, h₄, h₅⟩

/-- Each of `{5, 7, 10, 12}` and `{7, 8, 10, 11}` is around the false edge, in distinct blocks at the blob, with a taxon attached at a reticulation, and it is treelike. -/
theorem lemma7_witnesses : ∀ Y ∈ ({{1, 2, 4, 6}, {2, 3, 4, 5}} : Finset (Finset (Fin 7))), Y.card = 4 ∧ (A₀ ∩ Y).card = 2 ∧
    (∀ x ∈ Y, ∀ y ∈ Y, x ≠ y → ¬ SameBlock net 16 x y) ∧ (∃ x ∈ Y, AttachesAtReticulation net 16 x) ∧ IsTreelike net Y := by
  intro Y hY
  have hcover : Y ∈ cover := by
    revert Y
    decide +kernel
  have hcards : Y.card = 4 ∧ (A₀ ∩ Y).card = 2 := by
    revert Y
    decide +kernel
  refine ⟨hcards.1, hcards.2, fun x _ y _ hxy hb => hxy (eq_of_sameBlock hb), ?_, isTreelike_of_mem_cover hcover⟩
  simp only [mem_insert, mem_singleton] at hY
  rcases hY with rfl | rfl
  · exact ⟨1, by decide, attachesAtReticulation_one⟩
  · exact ⟨5, by decide, attachesAtReticulation_five⟩

/-- (`tob2025:supplement_lemma7_false`) **Lemma 7 of the supplement is false at level 2** (E25 of the report). On the binary level-2 network `net`, the set `{5, 7, 10, 12}` is around the false edge, in distinct blocks at the blob, with
`5` attached at a reticulation, and it is treelike (`lemma7_witnesses`). The printed proof keeps a subgraph of the blob that it connects by undirected paths. The induced subnetwork keeps only the arcs ancestral to the set: on this set the arcs into
the reticulation `16` leave, since `11` isn't in the set, and then the arc `(3, 6)` is a cut edge. -/
theorem not_supplementLemma7 : ¬ SupplementLemma7 := by
  intro h
  obtain ⟨h4, h2, hdist, hat, htl⟩ := lemma7_witnesses {1, 2, 4, 6} (by decide)
  exact h net net_isPhylogenetic net_isBinary B 16 A₀ B_isBinaryTree.isUnrootedTree treeOfBlobs_subset A₀_mem_internalSides
    A₀_notMem_treeOfBlobs (refinesBlob A₀) _ h4 h2 hdist hat htl

/-! ### Theorem 1 -/

/-- The edge with side `A₀` isn't labelled false by the oracle, on covers `cover` of the two sides. -/
theorem A₀_mem_contractSides {Q : Finset (Fin 7) → Finset (Finset (Fin 7))} (hQ : Q A₀ = cover) (hQ' : Q A₀ᶜ = cover)
    {R : Finset (Fin 7) → Prop} (hR : ∀ Y ∈ cover, ¬ R Y) :
    A₀ ∈ contractSides B ((internalSides B).filter fun A => ∃ Y ∈ Q A, R Y) := by
  refine mem_filter.2 ⟨(mem_filter.1 A₀_mem_internalSides).1, ?_, ?_⟩
  · intro hmem
    obtain ⟨Y, hY, hRY⟩ := (mem_filter.1 hmem).2
    rw [hQ] at hY
    exact hR Y hY hRY
  · intro hmem
    obtain ⟨Y, hY, hRY⟩ := (mem_filter.1 hmem).2
    rw [hQ'] at hY
    exact hR Y hY hRY

/-- (`tob2025:theorem2_needs_level_one`) **The oracle on four taxa fails on a disjoint cover at level 2** (E25 of the report): on the network `net` the output of `TOBQMC.theorem2`'s procedure keeps the false edge.
So `TOBQMC.theorem2` needs its hypothesis of level 1. -/
theorem not_theorem2_without_level_one : ¬ Theorem2WithoutLevelOne := by
  intro h
  have he := h net net_isPhylogenetic net_isBinary B B_isBinaryTree.isUnrootedTree treeOfBlobs_subset Q₀ Q₀_isDisjointCover
  have hmem := A₀_mem_contractSides (R := fun Y => ¬ IsTreelike net Y) Q₀_A₀ Q₀_A₀_compl
    fun Y hY hnt => hnt (isTreelike_of_mem_cover hY)
  refine A₀_notMem_treeOfBlobs ?_
  rw [← he]
  convert hmem

/-- **The method keeps the false edge**: at parameters at which the concordance factors of the four quartet trees are strictly cut, for all levels `α_k → 0` and `β > 0`, TINNiK's tests on a cover that is `cover` at the false edge
return the tree of blobs with probability tending to zero. -/
theorem tendsto_tobqmc_eq_treeOfBlobs {θ : MetricData (Fin 18)} (hθ : net.IsMetric θ) {ρ : ℝ} (hρ : 0 ≤ ρ ∧ ρ ≤ 1)
    (hc : ∀ i, AllmanEtAl2023.IsStrictlyCutAt (nmscCF net θ ρ) (quartets i)) {α : ℕ → ℝ} (hα₀ : Tendsto α atTop (𝓝 0))
    {β : ℝ} (hβ : 0 < β) {ml : (QuartetTree (Fin 7) → ℝ) → Finset (Fin 7) → QuartetTree (Fin 7)} (hml : IsMLSelection ml)
    {Q : Finset (Fin 7) → Finset (Finset (Fin 7))} (hQ : Q A₀ = cover) (hQ' : Q A₀ᶜ = cover) :
    Tendsto (fun k => iidProb (geneTreeDist net θ ρ) k fun ω =>
      tobqmc ml (α k) β (quartetCount unroot ω) B Q = treeOfBlobs net) atTop (𝓝 0) := by
  have hN := net_isPhylogenetic
  have hd : IsDist (geneTreeDist net θ ρ) := ⟨geneTreeDist_nonneg hN hθ hρ, sum_geneTreeDist hN hθ hρ⟩
  have hall := tendsto_iidProb_forall hd (ι := Fin 4)
    (fun i k ω => (quartets i).taxa ∉ testedB ml (α k) β (quartetCount unroot ω))
    fun i => tendsto_notMem_testedB hN hθ hρ (hc i) hα₀ hβ hml
  have hlim := (tendsto_const_nhds (x := (1 : ℝ))).sub hall
  rw [sub_self] at hlim
  refine squeeze_zero (fun k => iidProb_nonneg hd k _) (fun k => ?_) hlim
  rw [← iidProb_not hd]
  refine iidProb_mono hd fun ω hω hgood => ?_
  have hmem : A₀ ∈ tobqmc ml (α k) β (quartetCount unroot ω) B Q :=
    A₀_mem_contractSides hQ hQ' fun Y hY hYt => by
      obtain ⟨i, rfl⟩ := exists_quartets_of_mem_cover hY
      exact hgood i hYt
  rw [hω] at hmem
  exact A₀_notMem_treeOfBlobs hmem

/-- At `ρ = 1` the concordance factors of the quartet trees of the cover are strictly cut, at all valid parameters. -/
theorem isStrictlyCutAt_rho_one {θ : MetricData (Fin 18)} (hθ : net.IsMetric θ) (i : Fin 4) :
    AllmanEtAl2023.IsStrictlyCutAt (nmscCF net θ 1) (quartets i) :=
  ⟨fun _ hr => (nmscCF_lt_rho_one net_isPhylogenetic hθ (inducedCutSplit_quartets i) hr).ne,
    NMSC.cut_alternatives net_isPhylogenetic hθ ⟨zero_le_one, le_rfl⟩ _ (inducedCutSplit_quartets i)⟩

/-- (`tob2025:supplement_theorem1_rho_one`) **The method on `net` at `ρ = 1`** (E25 of the report): at all valid parameters, for all levels `α_k → 0`, `β > 0` and all selections of maximum likelihood topologies, the probability of returning the tree of blobs
tends to zero, on covers that are `cover` at the false edge. All of the supplement's hypotheses hold here: `isRelaxedNonanomalous_rho_one`, `isTQuartetNonanomalous`. -/
theorem tendsto_tobqmc_eq_treeOfBlobs_rho_one {θ : MetricData (Fin 18)} (hθ : net.IsMetric θ) {α : ℕ → ℝ}
    (hα₀ : Tendsto α atTop (𝓝 0)) {β : ℝ} (hβ : 0 < β)
    {ml : (QuartetTree (Fin 7) → ℝ) → Finset (Fin 7) → QuartetTree (Fin 7)} (hml : IsMLSelection ml)
    {Q : Finset (Fin 7) → Finset (Finset (Fin 7))} (hQ : Q A₀ = cover) (hQ' : Q A₀ᶜ = cover) :
    Tendsto (fun k => iidProb (geneTreeDist net θ 1) k fun ω =>
      tobqmc ml (α k) β (quartetCount unroot ω) B Q = treeOfBlobs net) atTop (𝓝 0) :=
  tendsto_tobqmc_eq_treeOfBlobs hθ ⟨zero_le_one, le_rfl⟩ (isStrictlyCutAt_rho_one hθ) hα₀ hβ hml hQ hQ'

/-- (`tob2025:supplement_theorem1_generic`) **The method on `net` at `ρ = 0`, for generic parameters** (E25 of the report): at parameters with CF-detectability, as generic parameters have (`AllmanEtAl2023.cfDetectable_generic`), the 4-blobs have non-cut concordance factors, so all the assumptions of
`TOBQMC.consistency` but the level hold; and the same conclusion holds as at `ρ = 1`. -/
theorem forGenericParams_tendsto_tobqmc_eq_treeOfBlobs :
    AllmanEtAl2023.ForGenericParams net fun θ =>
      (∀ q : Finset (Fin 7), q.card = 4 → ¬ IsTreelike net q → AllmanEtAl2023.IsNonCut (nmscCF net θ 0) q) ∧
      ∀ {α : ℕ → ℝ}, Tendsto α atTop (𝓝 0) → ∀ {β : ℝ}, 0 < β →
        ∀ {ml : (QuartetTree (Fin 7) → ℝ) → Finset (Fin 7) → QuartetTree (Fin 7)}, IsMLSelection ml →
        ∀ {Q : Finset (Fin 7) → Finset (Finset (Fin 7))}, Q A₀ = cover → Q A₀ᶜ = cover →
          Tendsto (fun k => iidProb (geneTreeDist net θ 0) k fun ω =>
            tobqmc ml (α k) β (quartetCount unroot ω) B Q = treeOfBlobs net) atTop (𝓝 0) := by
  refine (AllmanEtAl2023.cfDetectable_generic net_isPhylogenetic net_isBinary).mono ?_
  rintro θ ⟨hθ, hnot⟩
  refine ⟨hθ, fun hdet => hnot ⟨hdet.blob, ?_⟩⟩
  intro α hα₀ β hβ ml hml Q hQ hQ'
  exact tendsto_tobqmc_eq_treeOfBlobs hθ ⟨le_rfl, zero_le_one⟩ (fun i => hdet.cut _ (inducedCutSplit_quartets i)) hα₀ hβ hml hQ hQ'

/-- (`tob2025:supplement_theorem1_t3`) **The method on `net` at `ρ = 1`, with the T3 option** (E25 of the report), TINNiK's default: the same conclusion as `tendsto_tobqmc_eq_treeOfBlobs_rho_one`. -/
theorem tendsto_tobqmcT3_eq_treeOfBlobs_rho_one {θ : MetricData (Fin 18)} (hθ : net.IsMetric θ) {α : ℕ → ℝ}
    (hα₀ : Tendsto α atTop (𝓝 0)) {β : ℝ} (hβ : 0 < β)
    {ml : (QuartetTree (Fin 7) → ℝ) → Finset (Fin 7) → QuartetTree (Fin 7)} (hml : TINNiK.IsT3MLSelection ml)
    {Q : Finset (Fin 7) → Finset (Finset (Fin 7))} (hQ : Q A₀ = cover) (hQ' : Q A₀ᶜ = cover) :
    Tendsto (fun k => iidProb (geneTreeDist net θ 1) k fun ω =>
      tobqmcT3 ml (α k) β (quartetCount unroot ω) B Q = treeOfBlobs net) atTop (𝓝 0) := by
  have hN := net_isPhylogenetic
  have hρ : (0 : ℝ) ≤ 1 ∧ (1 : ℝ) ≤ 1 := ⟨zero_le_one, le_rfl⟩
  have hd : IsDist (geneTreeDist net θ 1) := ⟨geneTreeDist_nonneg hN hθ hρ, sum_geneTreeDist hN hθ hρ⟩
  have hstrict : ∀ i, IsT1Strict (nmscCF net θ 1) (quartets i) := fun i =>
    ⟨fun _ hr => nmscCF_lt_rho_one hN hθ (inducedCutSplit_quartets i) hr,
      NMSC.cut_alternatives hN hθ hρ _ (inducedCutSplit_quartets i)⟩
  have hall := tendsto_iidProb_forall hd (ι := Fin 4)
    (fun i k ω => (quartets i).taxa ∉ TINNiK.testedBT3 ml (α k) β (quartetCount unroot ω))
    fun i => tendsto_notMem_testedBT3 hN hθ hρ (hstrict i) hα₀ hβ hml
  have hlim := (tendsto_const_nhds (x := (1 : ℝ))).sub hall
  rw [sub_self] at hlim
  refine squeeze_zero (fun k => iidProb_nonneg hd k _) (fun k => ?_) hlim
  rw [← iidProb_not hd]
  refine iidProb_mono hd fun ω hω hgood => ?_
  have hmem : A₀ ∈ tobqmcT3 ml (α k) β (quartetCount unroot ω) B Q :=
    A₀_mem_contractSides hQ hQ' fun Y hY hYt => by
      obtain ⟨i, rfl⟩ := exists_quartets_of_mem_cover hY
      exact hgood i hYt
  rw [hω] at hmem
  exact A₀_notMem_treeOfBlobs hmem

/-- A selection of maximum likelihood topologies exists. -/
theorem exists_isMLSelection : ∃ ml : (QuartetTree (Fin 7) → ℝ) → Finset (Fin 7) → QuartetTree (Fin 7), IsMLSelection ml := by
  have hex : ∀ (c : QuartetTree (Fin 7) → ℝ) (q : Finset (Fin 7)), ∃ s : QuartetTree (Fin 7), q.card = 4 →
      s ∈ treesOn q ∧ ∀ r ∈ treesOn q, lineStat c s ≤ lineStat c r := by
    intro c q
    by_cases hq : q.card = 4
    · have hne : (treesOn q).Nonempty := card_pos.1 (by rw [card_treesOn hq]; norm_num)
      obtain ⟨s, hs, hmin⟩ := (treesOn q).exists_min_image (lineStat c) hne
      exact ⟨s, fun _ => ⟨hs, hmin⟩⟩
    · exact ⟨s₁, fun h => absurd h hq⟩
  choose ml hml using hex
  exact ⟨ml, fun c q hq => hml c q hq⟩

/-- (`tob2025:supplement_theorem1_false`) **Theorem 1 of the supplement is false at level 2** (E25 of the report). On the binary level-2 network `net`, at `ρ = 1` and at all valid parameters, all its hypotheses hold, and hypothesis tests on the disjoint covers `Q₀` of the refinement `B`,
with `cover` at the false edge, return the tree of blobs with probability tending to zero, at all levels. Main v5 restricts its Theorem 2 to level 1, as `TOBQMC.consistency` does. -/
theorem not_supplementTheorem1 : ¬ SupplementTheorem1 := by
  intro h
  have hθ := ECToBlob.isMetric_unitMetric net
  have hStd : StandardAssumptions net (ECToBlob.unitMetric net) 1 :=
    ⟨net_isPhylogenetic, net_isBinary, hθ, zero_le_one, le_rfl⟩
  obtain ⟨α, hα₀, -, hcons⟩ := h net (ECToBlob.unitMetric net) 1 hStd (isRelaxedNonanomalous_rho_one net_isPhylogenetic hθ)
    (isTQuartetNonanomalous _) (by decide) B B_isBinaryTree treeOfBlobs_subset Q₀ Q₀_isDisjointCover
  obtain ⟨ml, hml⟩ := exists_isMLSelection
  have h₁ := hcons 1 one_pos ml hml
  have h₀ := tendsto_tobqmc_eq_treeOfBlobs_rho_one hθ hα₀ one_pos hml Q₀_A₀ Q₀_A₀_compl
  exact one_ne_zero (tendsto_nhds_unique h₁ h₀)

end LevelTwo

end TOBQMC
