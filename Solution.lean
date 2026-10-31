module

public import ECToBlob
public import External
public import TINNiK
public import TOBQMC

/-!
# The proofs of the statements of record

Each theorem of `Challenge.lean` is restated here, word for word, and proved from the library. This
module also imports the whole library: it is its entry point.
-/

@[expose] public noncomputable section

open Finset MeasureTheory ProbabilityTheory
open scoped Classical

namespace Challenge

open Phylogenetics Phylogenetics.RootedNetwork ECToBlob TOBQMC Filter Topology

universe u

/-- **ECToBlob, Theorem 3.1.** Let `p` be nonnegative weights on the quartet trees, the probabilities of a
gene tree distribution, such that (1) if a cut edge of the network separates `a, b` from `c, d`, then
`p_ab|cd > max(p_ac|bd, p_ad|bc)`, and (2) replacing a taxon by another on the same side of a cut edge, with the
other three taxa on the other side, does not change `p`. Then every unrooted tree maximizing the sum of `p`
over its displayed quartet trees is a resolution of the tree of blobs. Condition 2 follows from the condition
as printed, that `p` depends on the induced network but not on its pendant chains. -/
theorem theorem3_1 {V E X : Type*} [Fintype X] [DecidableEq X] {N : RootedNetwork V E X}
    (hN : N.IsPhylogenetic) (p : QuartetTree X → ℝ) (hp : ∀ s, 0 ≤ p s)
    (h₁ : ∀ s, Displays (treeOfBlobs N) s → ∀ r ∈ s.alternatives, p r < p s)
    (h₂ : CutExchangeable N p) {T : Finset (Finset X)} (hT : IsUnrootedTree T)
    (hmax : ∀ T', IsUnrootedTree T' → quartetScore p T' ≤ quartetScore p T) :
    treeOfBlobs N ⊆ T := ECToBlob.theorem3_1 hN p hp h₁ h₂ hT hmax

/-- **ECToBlob, Theorem 4.1.** Let `N` be a rooted network on `X`, not necessarily binary, and `A|B` a split
of `X`, with partitions `A = A₁ ⊔ A₂`, `B = B₁ ⊔ B₂` into nonempty sets. If for all `aᵢ ∈ Aᵢ`, `bᵢ ∈ Bᵢ` the split
`a₁a₂|b₁b₂` is a cut-edge split of the induced 4-taxon network, then `A|B` is a cut-edge split of `N`. -/
theorem theorem4_1 {V E X : Type*} [Fintype X] [DecidableEq X] {N : RootedNetwork V E X}
    (hN : N.IsPhylogenetic) (A₁ A₂ B₁ B₂ : Finset X)
    (hA₁ : A₁.Nonempty) (hA₂ : A₂.Nonempty) (hB₁ : B₁.Nonempty) (hB₂ : B₂.Nonempty)
    (hA : Disjoint A₁ A₂) (hB : Disjoint B₁ B₂) (hAB : Disjoint (A₁ ∪ A₂) (B₁ ∪ B₂))
    (hcover : (A₁ ∪ A₂) ∪ (B₁ ∪ B₂) = Finset.univ)
    (h : ∀ a₁ ∈ A₁, ∀ a₂ ∈ A₂, ∀ b₁ ∈ B₁, ∀ b₂ ∈ B₂,
      N.HasCutSplitOn (({a₁, a₂, b₁, b₂} : Finset X) : Set X) (({a₁, a₂} : Finset X) : Set X)) :
    N.HasCutSplit ((A₁ ∪ A₂ : Finset X) : Set X) := ECToBlob.theorem4_1 hN A₁ A₂ B₁ B₂ hA₁ hA₂ hB₁ hB₂ hA hB hAB hcover h

/-- **ECToBlob, Theorem 8.2**, corrected. There are sequences `α_n`, `β_n`, independent of the network, such
that for every resolution `T₀` of the tree of blobs, every variant of the algorithm, and every distribution
of binary gene trees whose quartet concordance factors satisfy both directions of Assumption 1 at the
network's parameters, the output on `n` independent gene trees is the tree of blobs with probability tending
to one.

Two corrections to the printed theorem, each necessary: Assumption 1's converse holds for generic parameters
only, so the theorem is for parameters where it holds, as the proof says; and for the Cauchy-based corrections
`cauchy` and `cbc`, an alternative of probability zero under (5.2) makes a T1 p-value exactly `1`, so they are
assumed positive. -/
theorem theorem8_2 : ∃ α β : ℕ → ℝ, Tendsto α atTop (𝓝 0) ∧ Tendsto β atTop (𝓝 0) ∧
    (∀ᶠ n in atTop, 0 < α n ∧ α n < 1) ∧ (∀ᶠ n in atTop, 0 < β n ∧ β n < 1) ∧
    ∀ {V E X : Type u} [Fintype X] [DecidableEq X] (N : RootedNetwork V E X)
      (_ : N.IsPhylogenetic) (dist : BinaryGeneTree X → ℝ)
      (_ : (∀ g, 0 ≤ dist g) ∧ ∑ g, dist g = 1)
      (_ : Assumption1Forward N (displayCF dist Subtype.val))
      (_ : Assumption1Converse N (displayCF dist Subtype.val))
      (T₀ : Finset (Finset X)) (_ : IsResolutionOf T₀ (treeOfBlobs N))
      (o : ECToBlobOptions)
      (_ : (o.testCo = .cauchy ∨ o.testCo = .cbc) →
        ∀ s, IsT1Strict (displayCF dist Subtype.val) s →
          ∀ r ∈ s.alternatives, 0 < displayCF dist Subtype.val r),
      Tendsto (fun n => iidProb dist n fun ω =>
        ectoblob o (α n) (β n) (quartetCount Subtype.val ω) T₀ = treeOfBlobs N) atTop (𝓝 1) := ECToBlob.theorem8_2

/-- **TOB-QMC, Theorem 1**, conditional on exchangeability. For a network under the standard assumptions that
is T-quartet-nonanomalous and independent gene trees from the NMSC, for any binary tree `T` not refining the
tree of blobs and any `ε > 0` there are a binary refinement `B` and `K` such that `QS_k(B) > QS_k(T)` for all
`k ≥ K` with probability at least `1 - ε`. -/
theorem theorem1 {V E X : Type*} [Fintype V] [Fintype E] [Fintype X] [DecidableEq X]
    {N : RootedNetwork V E X} {θ : MetricData E} {ρ : ℝ}
    (hStd : StandardAssumptions N θ ρ) (hEx : External.AneEtAl2024.Exchangeability N θ ρ)
    (hNon : IsTQuartetNonanomalous N (nmscCF N θ ρ)) (hX : 4 ≤ Fintype.card X)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (G : ℕ → Ω → Finset (Finset X)) (hG : IsGeneTreeSample P N θ ρ G)
    (T : Finset (Finset X)) (hT : IsBinaryTree T) (hTN : ¬ treeOfBlobs N ⊆ T) {ε : ℝ} (hε : 0 < ε) :
    ∃ (B : Finset (Finset X)) (K : ℕ), IsBinaryTree B ∧ treeOfBlobs N ⊆ B ∧
      1 - ε ≤ P.real {ω | ∀ k, K ≤ k → quartetScore (geneCount G k ω) T < quartetScore (geneCount G k ω) B} := TOBQMC.theorem1 hStd hEx hNon hX P G hG T hT hTN hε

/-- **TOB-QMC, Theorem 1**, "put simply", conditional on exchangeability: almost surely, for all large `k`,
every optimal solution of Weighted Quartet Consensus on the first `k` gene trees refines the tree of blobs. -/
theorem theorem1_optimal {V E X : Type*} [Fintype V] [Fintype E] [Fintype X] [DecidableEq X]
    {N : RootedNetwork V E X} {θ : MetricData E} {ρ : ℝ}
    (hStd : StandardAssumptions N θ ρ) (hEx : External.AneEtAl2024.Exchangeability N θ ρ)
    (hNon : IsTQuartetNonanomalous N (nmscCF N θ ρ)) (hX : 4 ≤ Fintype.card X)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (G : ℕ → Ω → Finset (Finset X)) (hG : IsGeneTreeSample P N θ ρ G) :
    ∀ᵐ ω ∂P, ∃ K, ∀ k, K ≤ k → ∀ B, IsBinaryTree B →
      (∀ T, IsBinaryTree T → quartetScore (geneCount G k ω) T ≤ quartetScore (geneCount G k ω) B) →
      treeOfBlobs N ⊆ B := TOBQMC.theorem1_optimal hStd hEx hNon hX P G hG

/-- **TOB-QMC, Theorem 2.** For a binary level-1 network with tree of blobs `T_N`, and a refinement `B` of
`T_N`: applying the oracle for treelikeness to a disjoint cover of four-taxon subsets around each edge of
`B`, labelling an edge a false positive if the oracle answers non-treelike on one of them, and contracting
the false positives, returns `T_N`. -/
theorem theorem2 {V E X : Type*} [Fintype V] [Fintype E] [Fintype X] [DecidableEq X]
    {N : RootedNetwork V E X} (hN : N.IsPhylogenetic) (hBin : N.IsBinary) (hLevel : IsLevelOne N)
    {B : Finset (Finset X)} (hB : IsUnrootedTree B) (hTB : treeOfBlobs N ⊆ B)
    (Q : Finset X → Finset (Finset X)) (hQ : ∀ A ∈ internalSides B, IsDisjointCover B A (Q A)) :
    contractSides B ((internalSides B).filter fun A => ∃ Y ∈ Q A, ¬ IsTreelike N Y) = treeOfBlobs N := TOBQMC.theorem2 hN hBin hLevel hB hTB Q hQ

/-- **TOB-QMC, the consistency claim of §4.3**, conditional on exchangeability. For a binary level-1 network
under the standard assumptions that is T-quartet-nonanomalous, at parameters where CF-detectability holds, there
are levels `α_k → 0` such that for any `β > 0`, any selection of maximum likelihood topologies, any solver of
Weighted Quartet Consensus and any selection of disjoint covers, the method on `k` independent gene trees
returns the tree of blobs with probability tending to one. -/
theorem consistency {V E X : Type*} [Fintype V] [Fintype E] [Fintype X] [DecidableEq X]
    {N : RootedNetwork V E X} {θ : MetricData E} {ρ : ℝ}
    (hStd : StandardAssumptions N θ ρ) (hLevel : IsLevelOne N)
    (hEx : External.AneEtAl2024.Exchangeability N θ ρ)
    (hNon : IsTQuartetNonanomalous N (nmscCF N θ ρ))
    (hdet : External.AllmanEtAl2023.CFDetectable N (nmscCF N θ ρ)) (hX : 4 ≤ Fintype.card X) :
    ∃ α : ℕ → ℝ, Tendsto α atTop (𝓝 0) ∧ (∀ k, 0 < α k) ∧
      ∀ (β : ℝ), 0 < β →
      ∀ (ml : (QuartetTree X → ℝ) → Finset X → QuartetTree X), IsMLSelection ml →
      ∀ (solve : (QuartetTree X → ℝ) → Finset (Finset X)), (∀ c, IsWQCOptimal c (solve c)) →
      ∀ (cover : Finset (Finset X) → Finset X → Finset (Finset X)),
        (∀ B, IsBinaryTree B → ∀ A ∈ internalSides B, IsDisjointCover B A (cover B A)) →
        Tendsto (fun k => iidProb (geneTreeDist N θ ρ) k fun ω =>
          tobqmc ml (α k) β (quartetCount unroot ω) (solve (quartetCount unroot ω))
            (cover (solve (quartetCount unroot ω))) = treeOfBlobs N) atTop (𝓝 1) := TOBQMC.consistency hStd hLevel hEx hNon hdet hX

/-- **TINNiK, Theorem 4**, conditional on CF-detectability for generic parameters
(`External.AllmanEtAl2023.Corollary1`). For generic numerical parameters on a binary network there is a sequence
`α_m → 0` such that for any `β > 0` and `2 > δ ≥ 0`, any exact distance-based tree building method and any
selection of maximum likelihood topologies, the TINNiK algorithm using the cut test on `m` independent gene trees
from the NMSC infers the tree of blobs with probability tending to one. -/
theorem theorem4 {V E X : Type*} [Fintype V] [Fintype E] [Fintype X] [DecidableEq X]
    {N : RootedNetwork V E X} (hN : N.IsPhylogenetic) (hBin : N.IsBinary) (hX : 4 ≤ Fintype.card X)
    (hCor : External.AllmanEtAl2023.Corollary1 N) :
    ∃ A : Set (MetricData E), External.AllmanEtAl2023.IsGenericNull N A ∧
      ∀ θ, N.IsMetric θ → θ ∉ A →
        ∃ α : ℕ → ℝ, Tendsto α atTop (𝓝 0) ∧ (∀ m, 0 < α m) ∧
          ∀ (β δ : ℝ), 0 < β → 0 ≤ δ → δ < 2 →
          ∀ (M : TreeBuilder X), IsExactBuilder M →
          ∀ (ml : (QuartetTree X → ℝ) → Finset X → QuartetTree X), IsMLSelection ml →
            Tendsto (fun m => iidProb (geneTreeDist N θ 0) m fun ω =>
              tinnik ml (α m) β δ M (quartetCount unroot ω) = treeOfBlobs N) atTop (𝓝 1) := TINNiK.theorem4 hN hBin hX hCor

end Challenge
