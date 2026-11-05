module

public import AllmanEtAl2023.Basic
public import AllmanEtAl2023.Concordance
public import Basic.Defs
public import Basic.FinNetwork
public import Basic.Testing.Defs
public import Basic.Testing.IID
public import External.AneEtAl2024.Proposition12
public import External.DinhBanos2025.Theorem1
public import External.HuberEtAl2025.Theorem51
public import External.KaneTao2017.PartitioningClusters
public import Phylogenetics.Hierarchy.Defs
public import Phylogenetics.NMSC.Defs
public import Phylogenetics.NMSC.DisplayedTreeModel
public import Phylogenetics.NMSC.History
public import Phylogenetics.Network.Defs
public import Phylogenetics.Network.Level1.Digraph.Defs
public import Phylogenetics.Network.Level1.Digraph.OfNet
public import Phylogenetics.Network.Level1.ToRootedNetwork
public import Phylogenetics.Network.Quartets
public import Phylogenetics.Tree.Defs
public import TINNiK.T3
public import TOBQMC.Consistency
public import TOBQMC.ConsistencyT3
public import TOBQMC.DisplayedRefinement
public import TOBQMC.Implementation
public import TOBQMC.Level1
public import TOBQMC.SupplementLemma2
public import TOBQMC.SupplementLemma4Margin
public import TOBQMC.SupplementLevelTwo
public import TOBQMC.WQC

/-!
# The main results of TOB-QMC

Dai, Han, Molloy, bioRxiv v5, 2026: Theorems 1 and 2 and the consistency claim of §4.3, the claims of its supplement, and the main results of sources it cites: Ané et al. 2024 (`ane_`), Huber et al. 2025 (`huber_`), Dinh, Baños 2025 (`dinhBanos_`) and Kane, Tao 2017 (`kaneTao_`).

Each theorem is stated in plain terms and proved from the libraries. `papers/TOBQMC/README.md` and `papers/TOBQMC/REPORT.md` describe the formalization and list every correction and departure, and `papers/TOBQMC/palomar/` has the paper's entry for Palomar. `MainResults` imports this module with those of the other papers.
-/

@[expose] public noncomputable section

open Finset MeasureTheory ProbabilityTheory
open scoped Classical

namespace TreeOfBlobs

universe u

section

open Phylogenetics Phylogenetics.RootedNetwork ECToBlob TOBQMC Filter Topology

/-- **TOB-QMC, Theorem 1**. For a network under the standard assumptions that
is T-quartet-nonanomalous and independent gene trees from the NMSC, for any binary tree `T` not refining the
tree of blobs and any `ε > 0` there are a binary refinement `B` and `K` such that `QS_k(B) > QS_k(T)` for all
`k ≥ K` with probability at least `1 - ε`. -/
theorem theorem1 {V E X : Type*} [Fintype V] [Fintype E] [Fintype X] [DecidableEq X]
    {N : RootedNetwork V E X} {θ : MetricData E} {ρ : ℝ}
    (hStd : StandardAssumptions N θ ρ)
    (hNon : IsTQuartetNonanomalous N (nmscCF N θ ρ)) (hX : 4 ≤ Fintype.card X)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (G : ℕ → Ω → Finset (Finset X)) (hG : IsGeneTreeSample N θ ρ P G)
    (T : Finset (Finset X)) (hT : IsBinaryTree T) (hTN : ¬ treeOfBlobs N ⊆ T) {ε : ℝ} (hε : 0 < ε) :
    ∃ (B : Finset (Finset X)) (K : ℕ), IsBinaryTree B ∧ treeOfBlobs N ⊆ B ∧
      1 - ε ≤ P.real {ω | ∀ k, K ≤ k → quartetSupport (geneCount G k ω) T < quartetSupport (geneCount G k ω) B} := TOBQMC.theorem1 hStd hNon hX P G hG T hT hTN hε

/-- **TOB-QMC, Theorem 1**, "put simply": almost surely, for all large `k`,
every optimal solution of Weighted Quartet Consensus on the first `k` gene trees refines the tree of blobs. -/
theorem theorem1_optimal {V E X : Type*} [Fintype V] [Fintype E] [Fintype X] [DecidableEq X]
    {N : RootedNetwork V E X} {θ : MetricData E} {ρ : ℝ}
    (hStd : StandardAssumptions N θ ρ)
    (hNon : IsTQuartetNonanomalous N (nmscCF N θ ρ)) (hX : 4 ≤ Fintype.card X)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (G : ℕ → Ω → Finset (Finset X)) (hG : IsGeneTreeSample N θ ρ P G) :
    ∀ᵐ ω ∂P, ∃ K, ∀ k, K ≤ k → ∀ B, IsBinaryTree B →
      (∀ T, IsBinaryTree T → quartetSupport (geneCount G k ω) T ≤ quartetSupport (geneCount G k ω) B) →
      treeOfBlobs N ⊆ B := TOBQMC.theorem1_optimal hStd hNon hX P G hG

/-- **TOB-QMC, Theorem 2.** For a binary level-1 network with tree of blobs `T_N`, and a refinement `B` of
`T_N`: applying the oracle for treelikeness to a disjoint cover of four-taxon subsets around each edge of
`B`, labelling an edge a false positive if the oracle answers non-treelike on one of them, and contracting
the false positives, returns `T_N`. -/
theorem theorem2 {V E X : Type*} [Fintype V] [Fintype E] [Fintype X] [DecidableEq X]
    {N : RootedNetwork V E X} (hN : N.IsPhylogenetic) (hBin : N.IsBinary) (hLevel : IsLevelOne N)
    {B : Finset (Finset X)} (hB : IsUnrootedTree B) (hTB : treeOfBlobs N ⊆ B)
    (Q : Finset X → Finset (Finset X)) (hQ : ∀ A ∈ internalSides B, IsDisjointCover B A (Q A)) :
    contractSides B ((internalSides B).filter fun A => ∃ Y ∈ Q A, ¬ IsTreelike N Y) = treeOfBlobs N := TOBQMC.theorem2 hN hBin hLevel hB hTB Q hQ

/-- **TOB-QMC, the consistency claim of §4.3**. For a binary level-1 network under the standard assumptions that is
T-quartet-nonanomalous, whose non-treelike 4-taxon sets have distinct concordance factors (assumption 6a), there are levels
`α_k → 0` such that for any `β > 0`, any selection of maximum likelihood topologies, any solver of Weighted Quartet Consensus
and any selection of disjoint covers, the method on `k` independent gene trees returns the tree of blobs with probability
tending to one. The tests are TINNiK's star and cut tests; the T3 option is `TOBQMC.consistencyT3_of_noAnomalous`. -/
theorem consistency {V E X : Type*} [Fintype V] [Fintype E] [Fintype X] [DecidableEq X]
    {N : RootedNetwork V E X} {θ : MetricData E} {ρ : ℝ}
    (hStd : StandardAssumptions N θ ρ) (hLevel : IsLevelOne N)
    (hNon : IsTQuartetNonanomalous N (nmscCF N θ ρ))
    (hBlob : ∀ q : Finset X, q.card = 4 → ¬ IsTreelike N q →
      AllmanEtAl2023.IsNonCut (nmscCF N θ ρ) q) (hX : 4 ≤ Fintype.card X) :
    ∃ α : ℕ → ℝ, Tendsto α atTop (𝓝 0) ∧ (∀ k, 0 < α k) ∧
      ∀ (β : ℝ), 0 < β →
      ∀ (ml : (QuartetTree X → ℝ) → Finset X → QuartetTree X), IsMLSelection ml →
      ∀ (solve : (QuartetTree X → ℝ) → Finset (Finset X)), (∀ c, IsWQCOptimal c (solve c)) →
      ∀ (cover : Finset (Finset X) → Finset X → Finset (Finset X)),
        (∀ B, IsBinaryTree B → ∀ A ∈ internalSides B, IsDisjointCover B A (cover B A)) →
        Tendsto (fun k => iidProb (geneTreeDist N θ ρ) k fun ω =>
          tobqmc ml (α k) β (quartetCount unroot ω) (solve (quartetCount unroot ω))
            (cover (solve (quartetCount unroot ω))) = treeOfBlobs N) atTop (𝓝 1) := TOBQMC.consistency hStd hLevel hNon hBlob hX

end

/-! ## What the paper says in passing, and its other claims -/

section

open Phylogenetics Phylogenetics.RootedNetwork ECToBlob TOBQMC AllmanEtAl2023 Filter Topology

/-- **TOB-QMC, the implementation.** Under the hypotheses of `consistency`, the procedure of the implementation, which tests all of a selection of four-taxon subsets around each edge, possibly depending on the data, that
contains a disjoint cover, and applies the star test to the minimizer only, returns the tree of blobs with probability tending to one. -/
theorem tobqmc_consistency_implementation {V E X : Type*} [Fintype V] [Fintype E] [Fintype X] [DecidableEq X] {N : RootedNetwork V E X} {θ : MetricData E} {ρ : ℝ}
    (hStd : StandardAssumptions N θ ρ) (hLevel : IsLevelOne N)
    (hNon : IsTQuartetNonanomalous N (nmscCF N θ ρ))
    (hBlob : ∀ q : Finset X, q.card = 4 → ¬ IsTreelike N q →
      AllmanEtAl2023.IsNonCut (nmscCF N θ ρ) q) (hX : 4 ≤ Fintype.card X) :
    ∃ α : ℕ → ℝ, Tendsto α atTop (𝓝 0) ∧ (∀ k, 0 < α k) ∧
      ∀ (β : ℝ), 0 < β →
      ∀ (ml : (QuartetTree X → ℝ) → Finset X → QuartetTree X), IsMLSelection ml →
      ∀ (solve : (QuartetTree X → ℝ) → Finset (Finset X)), (∀ c, IsWQCOptimal c (solve c)) →
      ∀ (tested : (QuartetTree X → ℝ) → Finset (Finset X) → Finset X → Finset (Finset X)),
        (∀ c B, IsBinaryTree B → ∀ A ∈ internalSides B, ∃ Q ⊆ tested c B A, IsDisjointCover B A Q) →
        (∀ c B, IsBinaryTree B → ∀ A ∈ internalSides B, ∀ Y ∈ tested c B A, Y.card = 4 ∧ (A ∩ Y).card = 2) →
      ∀ (mini : (QuartetTree X → ℝ) → Finset (Finset X) → Finset X → Finset X),
        (∀ c B, IsBinaryTree B → ∀ A ∈ internalSides B,
          IsMinimizerOf (fun Y => cutPValue c (ml c Y)) (tested c B A) (mini c B A)) →
        Tendsto (fun k => iidProb (geneTreeDist N θ ρ) k fun ω =>
          tobqmcImplementation (fun Y => cutPValue (quartetCount unroot ω) (ml (quartetCount unroot ω) Y))
            (starPValue .lrt (quartetCount unroot ω)) (α k) β (solve (quartetCount unroot ω))
            (tested (quartetCount unroot ω) (solve (quartetCount unroot ω)))
            (mini (quartetCount unroot ω) (solve (quartetCount unroot ω))) = treeOfBlobs N) atTop (𝓝 1) :=
  TOBQMC.consistency_implementation hStd hLevel hNon hBlob hX

/-- **TOB-QMC: a refinement of the tree of blobs need not be a display tree.** A binary tree refining the tree of blobs of a binary level-1 network, that no parent choice displays. -/
theorem tobqmc_refinement_not_displayed :
    IsBinaryTree DisplayedRefinement.T₁ ∧ treeOfBlobs FinNetwork.Binary.net ⊆ DisplayedRefinement.T₁ ∧
      ∀ c : FinNetwork.Binary.net.ParentChoice, FinNetwork.Binary.net.displayedSides c ≠ DisplayedRefinement.T₁ :=
  DisplayedRefinement.refinement_not_displayed

/-- **TOB-QMC's supplement, the margin of Lemma 4 as printed vanishes** (E22 of the report). On a network whose tree of blobs is not a star, `π_min`, the least difference between any two expected concordance factors over T-quartets, isn't positive. -/
theorem tobqmc_not_printedPiMin_pos {V E X : Type*} [Fintype X] [DecidableEq X] {N : RootedNetwork V E X} [Fintype V] [Fintype E] (hN : N.IsPhylogenetic) {θ : MetricData E}
    (hθ : N.IsMetric θ) {ρ : ℝ} (hρ : 0 ≤ ρ ∧ ρ ≤ 1) (hne : ∃ s, Displays (treeOfBlobs N) s) {π : ℝ}
    (hπ : IsPrintedPiMin N (nmscCF N θ ρ) π) : ¬ 0 < π :=
  not_printedPiMin_pos hN hθ hρ hne hπ

/-- **TOB-QMC's supplement, Lemma 4 as printed has no instance** (E22 of the report). On a network whose tree of blobs is not a star, no weights have errors below `π_min / (2 |f₄(S)|)`. -/
theorem tobqmc_not_exists_printedError_lt {V E X : Type*} [Fintype X] [DecidableEq X] {N : RootedNetwork V E X} [Fintype V] [Fintype E] (hN : N.IsPhylogenetic) {θ : MetricData E}
    (hθ : N.IsMetric θ) {ρ : ℝ} (hρ : 0 ≤ ρ ∧ ρ ≤ 1) (hne : ∃ s, Displays (treeOfBlobs N) s) {π : ℝ}
    (hπ : IsPrintedPiMin N (nmscCF N θ ρ) π) (w : QuartetTree X → ℝ) :
    ¬ ∀ s, |w s - nmscCF N θ ρ s| < π / (2 * ((Fintype.card X).choose 4 : ℝ)) :=
  not_exists_printedError_lt hN hθ hρ hne hπ w

/-- **TOB-QMC's supplement, the converse of Lemma 2 is false, with `N|Y` the induced subnetwork** (E23 of the report), which is how the supplement defines it. A binary level-1 network has a star as its tree of blobs, while the network induced on four taxa is treelike. The printed proof reads "4-blob" as a blob of `N`, and under that reading the converse doesn't fail. -/
theorem tobqmc_not_lemma2Converse : ¬ SupplementLemma2.Lemma2Converse := SupplementLemma2.not_lemma2Converse

/-- **TOB-QMC's supplement, Lemma 7 is false at level 2** (E25 of the report). On a binary level-2 network, a set of four taxa around a false edge meets both conditions of the lemma, and it is treelike. -/
theorem tobqmc_not_supplementLemma7 : ¬ TOBQMC.SupplementLemma7 := LevelTwo.not_supplementLemma7

/-- **TOB-QMC's supplement, Theorem 1 is false at level 2** (E25 of the report), for a binary network of arbitrary level. The counterexample is at `ρ = 1`, with "relaxed nonanomalous" read as condition 1 of the supplement's Definition 1 and T-quartet nonanomaly. -/
theorem tobqmc_not_supplementTheorem1 : ¬ TOBQMC.SupplementTheorem1 := LevelTwo.not_supplementTheorem1

/-- **TOB-QMC, Theorem 2 needs level 1** (E25 of the report). With the hypothesis on the level left out, the oracle on the four-taxon subsets of a disjoint cover keeps a false edge. -/
theorem tobqmc_not_theorem2_without_level_one : ¬ TOBQMC.Theorem2WithoutLevelOne := LevelTwo.not_theorem2_without_level_one

/-- **TOB-QMC's method at level 2, with the T3 option, at `ρ = 1`** (E25 of the report). On the network of `tobqmc_not_supplementLemma7`, with the cover at the false edge, the output is the tree of blobs with probability tending to zero, at all levels. -/
theorem tobqmc_tendsto_tobqmcT3_rho_one {θ : MetricData (Fin 18)} (hθ : LevelTwo.net.IsMetric θ) {α : ℕ → ℝ}
    (hα₀ : Tendsto α atTop (𝓝 0)) {β : ℝ} (hβ : 0 < β)
    {ml : (QuartetTree (Fin 7) → ℝ) → Finset (Fin 7) → QuartetTree (Fin 7)} (hml : TINNiK.IsT3MLSelection ml)
    {Q : Finset (Fin 7) → Finset (Finset (Fin 7))} (hQ : Q LevelTwo.A₀ = LevelTwo.cover) (hQ' : Q LevelTwo.A₀ᶜ = LevelTwo.cover) :
    Tendsto (fun k => iidProb (geneTreeDist LevelTwo.net θ 1) k fun ω =>
      tobqmcT3 ml (α k) β (quartetCount unroot ω) LevelTwo.B Q = treeOfBlobs LevelTwo.net) atTop (𝓝 0) :=
  LevelTwo.tendsto_tobqmcT3_eq_treeOfBlobs_rho_one hθ hα₀ hβ hml hQ hQ'

/-- **TOB-QMC's method at level 2, at `ρ = 0`, for generic parameters** (E25 of the report). There the 4-blobs have non-cut concordance factors, so all the assumptions of `consistency` but the level hold, and the output is the tree of blobs with probability tending to zero, at all levels. Other values of `ρ` aren't covered. -/
theorem tobqmc_forGenericParams_tendsto :
    ForGenericParams LevelTwo.net fun θ =>
      (∀ q : Finset (Fin 7), q.card = 4 → ¬ IsTreelike LevelTwo.net q → IsNonCut (nmscCF LevelTwo.net θ 0) q) ∧
      ∀ {α : ℕ → ℝ}, Tendsto α atTop (𝓝 0) → ∀ {β : ℝ}, 0 < β →
        ∀ {ml : (QuartetTree (Fin 7) → ℝ) → Finset (Fin 7) → QuartetTree (Fin 7)}, IsMLSelection ml →
        ∀ {Q : Finset (Fin 7) → Finset (Finset (Fin 7))}, Q LevelTwo.A₀ = LevelTwo.cover → Q LevelTwo.A₀ᶜ = LevelTwo.cover →
          Tendsto (fun k => iidProb (geneTreeDist LevelTwo.net θ 0) k fun ω =>
            tobqmc ml (α k) β (quartetCount unroot ω) LevelTwo.B Q = treeOfBlobs LevelTwo.net) atTop (𝓝 0) :=
  LevelTwo.forGenericParams_tendsto_tobqmc_eq_treeOfBlobs

end

/-! ## The sources that it cites -/

section

open Phylogenetics Phylogenetics.RootedNetwork Filter Topology Finset MeasureTheory ProbabilityTheory

/-- **Ané et al. 2024, Proposition 12.** Under the common inheritance model with `ρ = 1`, a network with weak parameters is not anomalous on any four taxa. The source states it for a 4-taxon binary metric network. -/
theorem ane_proposition12 {V E X : Type*} [Fintype V] [Fintype E] [Fintype X] [DecidableEq X] {N : RootedNetwork V E X} {θ : MetricData E}
    (hN : N.IsPhylogenetic) (hθ : N.IsWeakMetric θ) {q : Finset X} (hq : q.card = 4) : ¬ External.AneEtAl2024.IsAnomalous N θ 1 q :=
  External.AneEtAl2024.proposition12 hN hθ hq

/-- **Huber et al. 2025, Theorem 5.1.** A split `A|B` of the taxa is the split of a cut edge exactly when it is trivial, or it isn't and `a₁a₂|b₁b₂` is the split of a cut edge of the network induced on these taxa for all distinct `a₁, a₂ ∈ A` and `b₁, b₂ ∈ B`. -/
theorem huber_theorem5_1 {V E X : Type*} [Fintype X] [DecidableEq X] {N : RootedNetwork V E X} (hN : N.IsPhylogenetic) {A : Finset X} (hA : A.Nonempty) (hB : Aᶜ.Nonempty) :
    N.HasCutSplit (A : Set X) ↔ (A.card = 1 ∨ Aᶜ.card = 1) ∨ (2 ≤ A.card ∧ 2 ≤ Aᶜ.card ∧ ∀ a₁ ∈ A, ∀ a₂ ∈ A, a₁ ≠ a₂ → ∀ b₁ ∉ A, ∀ b₂ ∉ A, b₁ ≠ b₂ →
      N.HasCutSplitOn (({a₁, a₂, b₁, b₂} : Finset X) : Set X) (({a₁, a₂} : Finset X) : Set X)) :=
  External.HuberEtAl2025.theorem5_1 hN hA hB

open External.DinhBanos2025 in
/-- **Dinh, Baños 2025, Theorem 1.** Under the source's conditions (6), (7), the tree `S = (((A, E), B), C, D)`, which the network does not display, has a higher expected ASTRAL score than both displayed trees `T₁` and `T₂`. -/
theorem dinhBanos_theorem1 {γ e₂ e₃ e₄ : ℝ} (h : Params γ e₂ e₃ e₄) (h6 : 1 - Real.exp (-e₂) > γ / (1 - γ) * (1 - Real.exp (-e₃) * Real.exp (-e₄)))
    (h7 : 1 - Real.exp (-e₃) < min (γ / (2 - γ) * (1 - Real.exp (-e₄))) ((1 - γ) / (1 + γ) * (1 - Real.exp (-e₂)))) :
    score h (unroot hT₁) < score h (unroot hS) ∧ score h (unroot hT₂) < score h (unroot hS) ∧
      ∀ c, (rooted h).displayedSides c ≠ treeOn γ e₂ e₃ e₄ (unroot hS) :=
  External.DinhBanos2025.theorem1 h h6 h7

/-- **Kane, Tao 2017, Theorem 1**, the bound: `|{(A₁, A₂, A) ∈ X³ : A = A₁ ⊎ A₂}| ≤ |X|^(3/p)` for a finite collection `X` of finite sets, with `p = log₃(27/4)`. The proof of the inequality (abc) is a departure from the source, and that `p` can't be larger isn't formalized. -/
theorem kaneTao_theorem1 {α : Type*} [DecidableEq α] (X : Finset (Finset α)) :
    ((External.KaneTao2017.triples X X X).card : ℝ) ≤ (X.card : ℝ) ^ (3 / External.KaneTao2017.p) :=
  External.KaneTao2017.theorem1 X

end

end TreeOfBlobs
