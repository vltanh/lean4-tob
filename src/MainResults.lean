module

public import AllmanEtAl2023.Algorithm
public import AllmanEtAl2023.BlobDistance
public import AllmanEtAl2023.Lemma1
public import AllmanEtAl2023.Lemma2Counterexample
public import AllmanEtAl2023.NetworkOne
public import AllmanEtAl2023.Proposition1
public import AllmanEtAl2023.Theorem4
public import Basic.Defs
public import Basic.Testing.IID
public import ECToBlob.BinaryLawExample
public import ECToBlob.DisplayedTreeExample
public import ECToBlob.Remark34
public import ECToBlob.Section3
public import ECToBlob.Section4
public import ECToBlob.Section8
public import ECToBlob.SumOfPairs
public import External.AllmanBanosRhodes2019.MissingTaxa
public import External.AllmanBanosRhodes2019.QuartetClass
public import External.AneEtAl2024.Proposition12
public import External.DinhBanos2025.Theorem1
public import External.GusfieldEtAl2004.BuildCount
public import External.GusfieldEtAl2004.Optimality
public import External.GusfieldEtAl2004.Theorem2_2
public import External.HuberEtAl2025.Theorem51
public import External.HudsonKaplan1985.Algorithm
public import External.KaneTao2017.PartitioningClusters
public import External.LegriedEtAl2021.Theorem1
public import External.MitchellAllmanRhodes2019.T1Limit
public import External.MyersGriffiths2003.Composite
public import External.SongHein2005.BinaryPaths
public import Gusfield2007.Counterexamples
public import Gusfield2007.EntryNet
public import Gusfield2007.HusonKloepper
public import Gusfield2007.MdLower
public import Gusfield2007.MergedTreeness
public import Gusfield2007.OpenStatements
public import Gusfield2007.Realizability
public import Gusfield2007.Theorem10PrintedMultiple
public import TINNiK.Basic
public import TINNiK.MissingTaxa
public import TOBQMC.Consistency
public import TOBQMC.DisplayedRefinement
public import TOBQMC.Implementation
public import TOBQMC.Level1
public import TOBQMC.WQC

/-!
# The main results: tree of blobs inference from quartets, and the theory of blobs behind it

Main results of five papers, each stated in plain terms and proved from its paper's library: **ECToBlob** (Rhodes, Allman,
Ané, Baños, bioRxiv v1, 2026), Theorems 3.1, 4.1, 8.2; **TOB-QMC** (Dai, Han, Molloy, bioRxiv v5, 2026), Theorems 1, 2 and the
consistency claim of §4.3; **TINNiK** (Allman, Baños, Mitchell, Rhodes, Algorithms Mol. Biol. 19, 2024), Theorem 4; **Allman et al.
2023** (Allman, Baños, Mitchell, Rhodes, J. Math. Biol. 86, 2023), Lemma 1, Theorems 1 to 4, Corollary 1, Proposition 1;
**Gusfield et al. 2007** (Gusfield, Bansal, Bafna, Song, J. Comput. Biol. 14, 2007), Lemma 4, Theorems 1 and 3 to 11, Corollaries 2,
3, and the refutation of its conjectures. After them come what these papers say in passing, and the main results of the sources they
cite, each with a prefix: `galled_` for Gusfield, Eddhu, Langley 2004, `myersGriffiths_`, `hudsonKaplan_`, `songHein_`, `nanuq_`,
`mitchell_`, `ane_`, `huber_`, `dinhBanos_`, `kaneTao_`, `legried_`. `docs/REPORT.md` lists every correction and departure.

All are proved, with no assumed result. This includes the CF-detectability of 4-blobs for generic parameters (Allman et
al. 2023, Theorem 1 and Corollary 1; TINNiK's Theorem 1), which `theorem4` uses. One theorem is conditional, and says so in its
statement: `gusfield_theorem10Printed_multiple_false_of_search` has the finite computation `printedMSearch` as a hypothesis, which the
kernel hasn't completed.

The definitions are those of the library `Phylogenetics` and of `src/Basic/Defs.lean`, which has the three algorithms and
the papers' standing assumptions. A network is a directed multigraph with named arcs; the sides of its splits represent an
unrooted tree; the tree of blobs is the family of nonempty proper cut-edge sides. A quartet tree `ab|cd` is an unordered pair
of cherries. `HasCutSplitOn Y A` says that `A ∩ Y | Y \ A` is a split of a cut edge of the network induced on `Y`. The NMSC
is `geneTreeDist`, with one lineage per taxon; `ρ = 0` is independent inheritance. `iidProb dist n Ev` is the probability
that `n` independent draws from `dist` lie in `Ev`.

The theorems `allman_*` are on the paper's own objects, in `AllmanEtAl2023`: `IsBinaryNetwork`, its Definition 1; `Trd`, the reduced
unrooted tree of blobs; `cfTriple`, the concordance factor `CF_abcd`; `ForGenericParams N P`, "for generic numerical parameters", `P`
outside a null set. The theorems `gusfield_*` are on sequences of binary sites, in `Gusfield2007`, whose `Defs` imports Mathlib only:
a `Network` derives a set of rows `M` at its leaves, `Crossover` is the model of recombination, and `R`, `F` are the least numbers of
recombination nodes in a network for `M` and in a fully decomposed one.

Nothing imports this module, and it imports only what its theorems need.
-/

@[expose] public noncomputable section

open Finset MeasureTheory ProbabilityTheory
open scoped Classical

namespace TreeOfBlobs

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
    (hmax : ∀ T', IsUnrootedTree T' → quartetSupport p T' ≤ quartetSupport p T) :
    treeOfBlobs N ⊆ T := ECToBlob.theorem3_1 hN p hp h₁ h₂ hT hmax

/-- **ECToBlob, Theorem 4.1.** Let `N` be a rooted network on `X`, not necessarily binary, and `A|B` a split
of `X`, with partitions `A = A₁ ⊔ A₂`, `B = B₁ ⊔ B₂` into nonempty sets. If for all `aᵢ ∈ Aᵢ`, `bᵢ ∈ Bᵢ` the split
`a₁a₂|b₁b₂` is a cut-edge split of the induced 4-taxon network, then `A|B` is a cut-edge split of `N`. -/
theorem theorem4_1 {V E X : Type*} [Fintype X] [DecidableEq X] {N : RootedNetwork V E X}
    (hN : N.IsPhylogenetic) (A₁ A₂ B₁ B₂ : Finset X)
    (hA₁ : A₁.Nonempty) (hA₂ : A₂.Nonempty) (hB₁ : B₁.Nonempty) (hB₂ : B₂.Nonempty)
    (_ : Disjoint A₁ A₂) (_ : Disjoint B₁ B₂) (hAB : Disjoint (A₁ ∪ A₂) (B₁ ∪ B₂))
    (hcover : (A₁ ∪ A₂) ∪ (B₁ ∪ B₂) = Finset.univ)
    (h : ∀ a₁ ∈ A₁, ∀ a₂ ∈ A₂, ∀ b₁ ∈ B₁, ∀ b₂ ∈ B₂,
      N.HasCutSplitOn (({a₁, a₂, b₁, b₂} : Finset X) : Set X) (({a₁, a₂} : Finset X) : Set X)) :
    N.HasCutSplit ((A₁ ∪ A₂ : Finset X) : Set X) := ECToBlob.theorem4_1 hN A₁ A₂ B₁ B₂ hA₁ hA₂ hB₁ hB₂ hAB hcover h

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

/-- **TINNiK, Theorem 4.** For generic numerical parameters on a binary network, there is a sequence `α_m → 0` such that for
any `β > 0` and `0 ≤ δ < 2`, any exact tree builder and any selection of maximum likelihood topologies, the TINNiK
algorithm on `m` independent gene trees infers the tree of blobs with probability tending to one. -/
theorem theorem4 {V E X : Type*} [Fintype V] [Fintype E] [Fintype X] [DecidableEq X]
    {N : RootedNetwork V E X} (hN : N.IsPhylogenetic) (hBin : N.IsBinary) (hX : 4 ≤ Fintype.card X) :
    ∃ A : Set (MetricData E), IsGenericNull N A ∧
      ∀ θ, N.IsMetric θ → θ ∉ A →
        ∃ α : ℕ → ℝ, Tendsto α atTop (𝓝 0) ∧ (∀ m, 0 < α m) ∧
          ∀ (β δ : ℝ), 0 < β → 0 ≤ δ → δ < 2 →
          ∀ (M : TreeBuilder X), IsExactBuilder M →
          ∀ (ml : (QuartetTree X → ℝ) → Finset X → QuartetTree X), IsMLSelection ml →
            Tendsto (fun m => iidProb (geneTreeDist N θ 0) m fun ω =>
              tinnik ml (α m) β δ M (quartetCount unroot ω) = treeOfBlobs N) atTop (𝓝 1) := TINNiK.theorem4 hN hX hBin

end TreeOfBlobs

/-! ## Allman, Baños, Mitchell, Rhodes 2023 -/

namespace TreeOfBlobs

open Phylogenetics Phylogenetics.RootedNetwork Phylogenetics.DirectedMultigraph AllmanEtAl2023

universe u

/-- **Allman et al. 2023, Lemma 1.** The semidirected network of a 4-taxon rooted binary phylogenetic network has either exactly
one 4-blob, an unresolved reduced tree of blobs and the taxa a B-quartet, or exactly two 3-blobs, a resolved reduced tree of blobs and
the taxa a T-quartet. In either case its other blobs without a taxon are 2-blobs. -/
theorem allman_lemma1 {V E X : Type*} [Fintype X] [DecidableEq X] {N : RootedNetwork V E X}
    (hN : IsBinaryNetwork N) (hcard : Fintype.card X = 4) :
    ((∃! b, cutDegree (semidirected hN (nontrivial_of_card_four hcard)).graph b = 4) ∧
      (∀ b, (∀ x, blobOf _ ((semidirected hN (nontrivial_of_card_four hcard)).leaf x) ≠ b) →
        cutDegree (semidirected hN (nontrivial_of_card_four hcard)).graph b = 2 ∨
          cutDegree (semidirected hN (nontrivial_of_card_four hcard)).graph b = 4) ∧
      (∀ a b c d : X, ({a, b, c, d} : Finset X).card = 4 →
        (Trd hN (nontrivial_of_card_four hcard)).HasStarTopology a b c d) ∧
      IsBlobQuartet N Finset.univ) ∨
    ((∃ b₁ b₂, b₁ ≠ b₂ ∧ ∀ b, cutDegree (semidirected hN (nontrivial_of_card_four hcard)).graph b = 3 ↔
        b = b₁ ∨ b = b₂) ∧
      (∀ b, (∀ x, blobOf _ ((semidirected hN (nontrivial_of_card_four hcard)).leaf x) ≠ b) →
        cutDegree (semidirected hN (nontrivial_of_card_four hcard)).graph b = 2 ∨
          cutDegree (semidirected hN (nontrivial_of_card_four hcard)).graph b = 3) ∧
      (∃ a b c d : X, ({a, b, c, d} : Finset X).card = 4 ∧
        (Trd hN (nontrivial_of_card_four hcard)).HasQuartetTopology a b c d) ∧
      IsTreeQuartet N Finset.univ) := AllmanEtAl2023.lemma1 hN hcard

/-- **Allman et al. 2023, Theorem 1**, CF-detectability of 4-blobs. On a 4-taxon rooted binary phylogenetic network, for generic
parameters, the reduced tree of blobs has the topology `ab|cd` exactly when `CF_abcd` is strictly `(ab|cd)`-cut, and is unresolved
exactly when `CF_abcd` is non-cut. -/
theorem allman_theorem1 {V E X : Type*} [Fintype V] [Fintype E] [Fintype X] [DecidableEq X] {N : RootedNetwork V E X}
    (hN : IsBinaryNetwork N) (hcard : Fintype.card X = 4) :
    ForGenericParams N fun θ => ∀ (a b c d : X) (h : ({a, b, c, d} : Finset X).card = 4),
      ((Trd hN (nontrivial_of_card_four hcard)).HasQuartetTopology a b c d ↔
        IsStrictlyCutAtFirst (cfTriple N θ a b c d h)) ∧
      ((Trd hN (nontrivial_of_card_four hcard)).HasStarTopology a b c d ↔
        IsNonCutCF (cfTriple N θ a b c d h)) := AllmanEtAl2023.theorem1 hN hcard

/-- **Allman et al. 2023, Corollary 1.** On a rooted binary phylogenetic network, for generic parameters, the topology of the reduced
tree of blobs of each induced 4-taxon network is what `readTopology`, a function of `CF_abcd` alone, reads. -/
theorem allman_corollary1 {V E X : Type*} [Fintype V] [Fintype E] [Fintype X] [DecidableEq X] {N : RootedNetwork V E X}
    (hN : IsBinaryNetwork N) :
    ForGenericParams N fun θ => ∀ (a b c d : X) (h : ({a, b, c, d} : Finset X).card = 4),
      InducedTopologyIs hN a b c d h (readTopology (cfTriple N θ a b c d h)) := AllmanEtAl2023.corollary1 hN

/-- **Allman et al. 2023, Proposition 1.** On a 4-taxon rooted binary phylogenetic network whose reduced tree of blobs has the topology
`ab|cd`, for all parameters, `CF_abcd = (p, q, q)` with `0 < p, q < 1` and `p + 2q = 1`. -/
theorem allman_proposition1 {V E X : Type*} [Fintype V] [Fintype E] [Fintype X] [DecidableEq X] {N : RootedNetwork V E X}
    (hN : IsBinaryNetwork N) (hcard : Fintype.card X = 4) {a b c d : X} (h : ({a, b, c, d} : Finset X).card = 4)
    (hT : (Trd hN (nontrivial_of_card_four hcard)).HasQuartetTopology a b c d) {θ : MetricData E} (hθ : N.IsMetric θ) :
    ∃ p q : ℝ, cfTriple N θ a b c d h = (p, q, q) ∧ 0 < p ∧ p < 1 ∧ 0 < q ∧ q < 1 ∧ p + 2 * q = 1 :=
  AllmanEtAl2023.proposition1 hN hcard h hT hθ

/-- **Allman et al. 2023, Proposition 1, the converse.** Every triple `(p, q, q)` with `0 < p, q < 1` and `p + 2q = 1` is `CF_abcd` on
a 4-taxon rooted binary phylogenetic network whose reduced tree of blobs has the topology `ab|cd`. -/
theorem allman_proposition1_converse {X : Type u} [Fintype X] [DecidableEq X] (hcard : Fintype.card X = 4) {a b c d : X}
    (h : ({a, b, c, d} : Finset X).card = 4) {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) (hq1 : q < 1)
    (hpq : p + 2 * q = 1) :
    ∃ (V : Type u) (E : Type) (_ : Fintype V) (_ : Fintype E) (N : RootedNetwork V E X) (hN : IsBinaryNetwork N)
      (θ : MetricData E), N.IsMetric θ ∧
        (Trd hN (nontrivial_of_card_four hcard)).HasQuartetTopology a b c d ∧
        cfTriple N θ a b c d h = (p, q, q) := AllmanEtAl2023.proposition1_converse hcard h hp hp1 hq hq1 hpq

/-- **Allman et al. 2023, Lemma 2 needs a connected subnetwork**, a correction: the word is missing from the paper, whose proof and uses
all assume it. Without it the hypotheses hold, on labelled nodes of `M`, and no blob of the network is determined by `S`. -/
theorem allman_lemma2_needs_connected :
    ∃ (W F X : Type) (G : DirectedMultigraph W F) (ℓ : X → W) (M : Set F) (S : Finset X) (v : W),
      Finite F ∧ IsLabelledNetwork G ℓ ∧ (∀ s ∈ S, ℓ s ∈ nodesOf G M) ∧ v ∈ nodesOf G M ∧
        IsDeterminedBy (restrict G M) ℓ (blobOf (restrict G M) v) S ∧ ¬ ∃ b, IsDeterminedBy G ℓ b S :=
  AllmanEtAl2023.lemma2_needs_connected

/-- **Allman et al. 2023, Theorem 2**, the B-quartet Inference Rule. If `{a, b, c, d}` and `{b, c, d, e}` are B-quartets on a rooted
binary phylogenetic network, and one of `{a, b, c, e}`, `{a, b, d, e}`, `{a, c, d, e}` is on its induced network a T-quartet with `a, e`
separated, or a B-quartet, then all three are B-quartets. -/
theorem allman_theorem2 {V E X : Type*} [DecidableEq X] {N : RootedNetwork V E X} (hN : IsBinaryNetwork N) {a b c d e : X}
    (h5 : ({a, b, c, d, e} : Finset X).card = 5)
    (habcd : IsBlobQuartet N {a, b, c, d}) (hbcde : IsBlobQuartet N {b, c, d, e}) {t : Finset X}
    (ht : t ∈ ({{a, b, c, e}, {a, b, d, e}, {a, c, d, e}} : Finset (Finset X)))
    (hrule : InducedTreeSeparates hN t a e ∨ InducedIsBlobQuartet hN t) :
    IsBlobQuartet N {a, b, c, e} ∧ IsBlobQuartet N {a, b, d, e} ∧ IsBlobQuartet N {a, c, d, e} :=
  AllmanEtAl2023.theorem2 hN h5 habcd hbcde ht hrule

/-- **Allman et al. 2023, Theorem 3.** On a rooted binary phylogenetic network, for generic parameters, the sets that CF-detectability and
applications of the Inference Rule give from the `CF`s, `CFInferred`, are exactly the B-quartets. -/
theorem allman_theorem3 {V E X : Type*} [Fintype V] [Fintype E] [Fintype X] [DecidableEq X] {N : RootedNetwork V E X}
    (hN : IsBinaryNetwork N) :
    ForGenericParams N fun θ => ∀ Q : Finset X, Q.card = 4 →
      (CFInferred (nmscCF N θ 0) Q ↔ IsBlobQuartet N Q) := AllmanEtAl2023.theorem3 hN

/-- **Allman et al. 2023, Theorem 4.** There is a function `F`, chosen before the network, such that for generic parameters on any rooted
binary phylogenetic network, `F` of the distribution of gene quartet topologies is the reduced unrooted tree of blobs. -/
theorem allman_theorem4 (X : Type*) [Fintype X] [DecidableEq X] (hX : Nontrivial X) :
    ∃ F : (QuartetTree X → ℝ) → Finset (Finset X),
      ∀ (V E : Type u) [Fintype V] [Fintype E] (N : RootedNetwork V E X) (hN : IsBinaryNetwork N),
        ForGenericParams N fun θ => F (nmscCF N θ 0) = (Trd hN hX).splits := AllmanEtAl2023.theorem4 X hX

end TreeOfBlobs

/-! ## Gusfield, Bansal, Bafna, Song 2007 -/

namespace TreeOfBlobs

open Gusfield2007

/-- **Gusfield et al. 2007, Theorem 1**, the Decomposition Theorem. In any crossover model, a nonempty `M` with no constant column has a
network in which every blob contains all and only the sites of one non-trivial connected component of the incompatibility graph, and
every compatible site is on a tree edge. The paper assumes no constant column at line 112, and that `M` is nonempty implicitly. -/
theorem gusfield_theorem1 {ι : Type*} [LinearOrder ι] [Finite ι] (c : Crossover) (M : Finset (ι → Bool)) (hM : M.Nonempty)
    (hC : NoConstantColumn M) :
    ∃ (a b : ℕ) (N : Network ι (Fin a) (Fin b)), N.Obeys c ∧ N.Derives M ∧
      N.IsFullyDecomposedFor (incompatGraph M) := Gusfield2007.theorem1 c M hM hC

/-- **Gusfield et al. 2007, Theorem 3.** For any ancestral sequence `S` and crossover model, there is a network fully decomposed for the
conflict graph `G_S(M)`, with `S` at its root and exactly `Σ_C R_{S(C)}(M(C))` recombination nodes. -/
theorem gusfield_theorem3 {ι : Type*} [LinearOrder ι] [Finite ι] (c : Crossover) (M : Finset (ι → Bool)) (S : ι → Bool)
    (hM : M.Nonempty) (hC : NoConstantColumn M) :
    ∃ (a b : ℕ) (N : Network ι (Fin a) (Fin b)), N.Obeys c ∧ N.Derives M ∧ N.ancestral = S ∧
      N.IsFullyDecomposedFor (conflictGraph S M) ∧
      N.recombCount = ∑ᶠ C : (conflictGraph S M).ConnectedComponent,
        RS c (C.supp.domRestrict S) (restrictRows C.supp M) := Gusfield2007.theorem3 c M S hM hC

/-- **Gusfield et al. 2007, Lemma 4.** For a component `C` of `G(M)`, the tree `T̄` has a node `v_C` on all the edges labelled by characters
that originate from `C`, on the 0-side of each of their splits. A reading: a trivial `C` keeps both of its columns here, which label
one edge with opposite 0-sides, so the second clause is for a non-trivial `C`, and the third is what a trivial `C` has. -/
theorem gusfield_lemma4 {ι : Type*} {M : Finset (ι → Bool)} {W : Type*} [Finite W] {T : SimpleGraph W} {φ : M → W}
    {edge : SuperChar M → Sym2 W} (h : IsTBar M T φ edge) (c : (incompatGraph M).ConnectedComponent) :
    ∃ v, (∀ k : SuperChar M, k.1 = c → v ∈ edge k) ∧
      (c.supp.Nontrivial → ∀ k : SuperChar M, k.1 = c → ∀ r : M, charValue k r = true →
        ¬ SameSide T (edge k) (φ r) v) ∧
      ∀ k : SuperChar M, k.1 = c → ∃ v ∈ edge k, ∀ r : M, charValue k r = true → ¬ SameSide T (edge k) (φ r) v :=
  Gusfield2007.lemma4 h c

/-- **Gusfield et al. 2007, Theorem 4, with the entry node counted**, a correction. For a fully decomposed network, the blobbed tree `T′` is
`T̄` exactly when the network is efficient with the entry node of a blob counted, and it has `RegularArcs` and the degree condition.
The repair isn't ours: Gusfield, *ReCombinatorics* (MIT Press, 2014), Section 7.3.5, states the theorem for canonical networks, a stricter class, as its Theorem 7.3.3 (read only in snippets; `docs/REPORT.md`, E42). -/
theorem gusfield_theorem4_entry {ι : Type*} [LinearOrder ι] {V E : Type*} [Finite V] [Finite E] {N : Network ι V E}
    {M : Finset (ι → Bool)} (hd : N.Derives M) (hf : N.IsFullyDecomposedFor (incompatGraph M)) {W : Type*} [Finite W]
    {T : SimpleGraph W} {φ : M → W} {edge : SuperChar M → Sym2 W} (hT : IsTBar M T φ edge) :
    (∃ f : N.blobbedTree ≃g T, ∀ v r (hr : r ∈ M), N.IsLeaf v → N.label v = r → f (N.toBlobNode v) = φ ⟨r, hr⟩) ↔
      N.IsEfficientAtEntry ∧ N.RegularArcs ∧ N.DegreeCond := Gusfield2007.theorem4_entry hd hf hT

/-- **Gusfield et al. 2007, Theorem 4, exactly**, a correction. With the printed definition of efficient, `T′` is `T̄` for a fully decomposed
network exactly when it is efficient, and it has `IsTreeNormalStructural` and the degree condition. -/
theorem gusfield_theorem4_iff {ι : Type*} [LinearOrder ι] {V E : Type*} [Finite V] [Finite E] {N : Network ι V E}
    {M : Finset (ι → Bool)} (hd : N.Derives M) (hf : N.IsFullyDecomposedFor (incompatGraph M)) {W : Type*} [Finite W]
    {T : SimpleGraph W} {φ : M → W} {edge : SuperChar M → Sym2 W} (hT : IsTBar M T φ edge) :
    (∃ f : N.blobbedTree ≃g T, ∀ v r (hr : r ∈ M), N.IsLeaf v → N.label v = r → f (N.toBlobNode v) = φ ⟨r, hr⟩) ↔
      N.IsEfficient ∧ N.IsTreeNormalStructural ∧ N.DegreeCond := Gusfield2007.theorem4_iff hd hf hT

/-- **Gusfield et al. 2007, Theorem 4, its true forms are not vacuous.** For every `M` with at least three rows, in any crossover model,
some efficient fully decomposed network has `T′` equal to `T̄`, with all the hypotheses of the true forms, and its root at a node of `T′`
of degree at least three. This is not in the paper. -/
theorem gusfield_exists_realization {ι : Type*} [LinearOrder ι] [Finite ι] {M : Finset (ι → Bool)} {W : Type*} [Finite W]
    {T : SimpleGraph W} {φ : M → W} {edge : SuperChar M → Sym2 W} (c : Crossover) (hC : NoConstantColumn M)
    (h3 : 3 ≤ M.card) (h : IsTBar M T φ edge) :
    ∃ (a b : ℕ) (N : Network ι (Fin a) (Fin b)), N.Obeys c ∧ N.Derives M ∧ N.IsFullyDecomposedFor (incompatGraph M) ∧
      N.IsEfficient ∧ N.IsEfficientAtEntry ∧ N.IsTreeNormalStructural ∧ N.DegreeCond ∧
      (∃ f : N.blobbedTree ≃g T, ∀ v r (hr : r ∈ M), N.IsLeaf v → N.label v = r → f (N.toBlobNode v) = φ ⟨r, hr⟩) ∧
      3 ≤ (N.blobbedTree.neighborSet (N.toBlobNode N.root)).ncard := Gusfield2007.exists_realization c hC h3 h

/-- **Gusfield et al. 2007, Theorem 4 is false**: the printed definition of efficient omits the entry node of a blob. On `topRows`, in any
crossover model, the theorem fails even for a network with `RegularArcs` and the degree condition, so neither convention causes it. -/
theorem gusfield_theorem4_false_top (c : Crossover) :
    ¬ Theorem4Form c topRows fun {a b} (N : Network (Fin 5) (Fin a) (Fin b)) => N.IsRegular :=
  Gusfield2007.theorem4_false_top c

/-- **Gusfield et al. 2007, Theorem 4 is false on a site-free arc**, which the paper allows. On `fiveRows`, in any crossover model, it fails
for a perfect phylogeny, with no recombination node and no blob, so the entry node doesn't account for this failure. -/
theorem gusfield_theorem4_false_siteFree (c : Crossover) :
    ¬ Theorem4Form c fiveRows fun {a b} (N : Network (Fin 5) (Fin a) (Fin b)) =>
      (∀ x, N.IsRecomb x → ¬ N.IsLeaf x) ∧ N.NoAncestralExit ∧ N.DegreeCond :=
  Gusfield2007.theorem4_false_siteFree c

/-- **Gusfield et al. 2007, Theorem 5.** If an optimal network for `M` with ancestral sequence `S` has node labels `L` with `G_S(L)` and
`G_S(M)` having the same number of components, then `M` is S-min (or S-min-1) decomposable. -/
theorem gusfield_theorem5 {ι : Type*} [LinearOrder ι] [Finite ι] {V E : Type*} [Fintype V] [Finite E] {c : Crossover}
    {M : Finset (ι → Bool)} {S : ι → Bool} (hC : NoConstantColumn M) (N : Network ι V E) (hN : N.IsOptimalRooted c S M)
    (h : Nat.card (conflictGraph S N.labelSet).ConnectedComponent = Nat.card (conflictGraph S M).ConnectedComponent) :
    SMinDecomposable c S M := Gusfield2007.theorem5 hC N hN h

/-- **Gusfield et al. 2007, Theorem 6.** If a network for `M` with ancestral sequence `S`, not necessarily optimal, has every node visible
and at most one site on each edge, then `M` is S-min (or S-min-1) decomposable. -/
theorem gusfield_theorem6 {ι : Type*} [LinearOrder ι] [Finite ι] {V E : Type*} [Fintype V] [Finite E] {c : Crossover}
    {M : Finset (ι → Bool)} {S : ι → Bool} (hC : NoConstantColumn M) (N : Network ι V E) (hc : N.Obeys c) (hd : N.Derives M)
    (hS : N.ancestral = S) (hv : N.AllVisible M S) (he : Function.Injective N.site) : SMinDecomposable c S M :=
  Gusfield2007.theorem6 hC N hc hd hS hv he

/-- **Gusfield et al. 2007, Theorem 7.** If every recombination node of a network for `M` with ancestral sequence `S` is a 0- or 1-component
recombination for `G_S(M)`, then there is a fully decomposed network, in the same model, with at most as many recombination nodes. -/
theorem gusfield_theorem7 {ι : Type*} [LinearOrder ι] [Finite ι] {V E : Type*} [Fintype V] [Finite E] {c : Crossover}
    {M : Finset (ι → Bool)} {S : ι → Bool} (hC : NoConstantColumn M) (N : Network ι V E) (hc : N.Obeys c) (hd : N.Derives M)
    (hS : N.ancestral = S)
    (h : ∀ x, N.IsRecomb x → N.IsZeroComponent (conflictGraph S M) x ∨ N.IsOneComponent (conflictGraph S M) x) :
    ∃ (a b : ℕ) (N' : Network ι (Fin a) (Fin b)), N'.Obeys c ∧ N'.Derives M ∧ N'.ancestral = S ∧
      N'.IsFullyDecomposedFor (conflictGraph S M) ∧ N'.recombCount ≤ N.recombCount :=
  Gusfield2007.theorem7 hC N hc hd hS h

/-- **Gusfield et al. 2007, Theorem 8.** Given `S`, if `M` is spatially disjoint then it is S-min-1 decomposable. -/
theorem gusfield_theorem8 {ι : Type*} [LinearOrder ι] [Finite ι] {M : Finset (ι → Bool)} {S : ι → Bool} (hM : M.Nonempty)
    (hC : NoConstantColumn M) (h : SpatiallyDisjoint S M) : SMinDecomposable .single S M :=
  Gusfield2007.theorem8 hM hC h

/-- **Gusfield et al. 2007, Theorem 9.** If the node labels of a network for `M` with ancestral sequence `S` respect `G_S(M)`, then there is a
fully decomposed network, in the same model, with at most as many recombination nodes. -/
theorem gusfield_theorem9 {ι : Type*} [LinearOrder ι] [Finite ι] {V E : Type*} [Fintype V] [Finite E] {c : Crossover}
    {M : Finset (ι → Bool)} {S : ι → Bool} (hC : NoConstantColumn M) (N : Network ι V E) (hc : N.Obeys c) (hd : N.Derives M)
    (hS : N.ancestral = S) (h : Respects N.labelSet S M) :
    ∃ (a b : ℕ) (N' : Network ι (Fin a) (Fin b)), N'.Obeys c ∧ N'.Derives M ∧ N'.ancestral = S ∧
      N'.IsFullyDecomposedFor (conflictGraph S M) ∧ N'.recombCount ≤ N.recombCount :=
  Gusfield2007.theorem9 hC N hc hd hS h

/-- **Gusfield et al. 2007, Theorem 10**, corrected. If `H(M + S) = R_S(M)`, or `R¹_S(M)`, then `M` is S-min, or S-min-1, decomposable. The correction: `R_S` in
place of the printed `R(M + S)`, since the proof's network has ancestral sequence `S`. The printed form is false for single crossovers (`gusfield_theorem10Printed_single_false`). -/
theorem gusfield_theorem10 {ι : Type*} [LinearOrder ι] [Finite ι] {c : Crossover} {M : Finset (ι → Bool)} {S : ι → Bool}
    (hM : M.Nonempty) (hC : NoConstantColumn M)
    (h : haplotypeBound (addRow M S) = RS c S M) : SMinDecomposable c S M := Gusfield2007.theorem10 hM hC h

/-- **Gusfield et al. 2007, Theorem 11.** For any positive `d` there is a set of sequences `M` with `F¹(M) - R¹(M) ≥ d`, written as a sum so
that the truncation on `ℕ` plays no part. -/
theorem gusfield_theorem11 (d : ℕ) (hd : 0 < d) :
    ∃ (m : ℕ) (M : Finset (Fin m → Bool)), M.Nonempty ∧ NoConstantColumn M ∧ R .single M + d ≤ F .single M :=
  Gusfield2007.theorem11 d hd

/-- **Gusfield et al. 2007, Corollary 2.** If every node of an optimal network for `M` with ancestral sequence `S` is visible, then `M` is S-min (or
S-min-1) decomposable. -/
theorem gusfield_corollary2 {ι : Type*} [LinearOrder ι] [Finite ι] {V E : Type*} [Fintype V] [Finite E] {c : Crossover}
    {M : Finset (ι → Bool)} {S : ι → Bool} (hC : NoConstantColumn M) (N : Network ι V E) (hN : N.IsOptimalRooted c S M)
    (h : N.AllVisible M S) : SMinDecomposable c S M := Gusfield2007.corollary2 hC N hN h

/-- **Gusfield et al. 2007, Corollary 3.** When recombinations only model back or recurrent mutations, the model `pointwise`, `M` is S-min decomposable
for any `S`, and the maximum parsimony score of `M` is the sum of the scores of the components of `G_S(M)`. -/
theorem gusfield_corollary3 {ι : Type*} [LinearOrder ι] [Finite ι] (M : Finset (ι → Bool)) (S : ι → Bool) (hM : M.Nonempty)
    (hC : NoConstantColumn M) :
    SMinDecomposable .pointwise S M ∧
      parsimonyScore S M = ∑ᶠ C : (conflictGraph S M).ConnectedComponent,
        parsimonyScore (C.supp.domRestrict S) (restrictRows C.supp M) := Gusfield2007.corollary3 M S hM hC

/-- **Gusfield et al. 2007, Section 5.3.1.** The unrooted Full-Decomposition Optimality Conjecture is false for single crossovers: on Figure 6,
`F¹ ≥ 4` and `R¹ ≤ 3`. -/
theorem gusfield_unrootedConjecture_single_false :
    4 ≤ F .single fig6 ∧ R .single fig6 ≤ 3 ∧ ¬ UnrootedConjecture .single := Gusfield2007.unrootedConjecture_single_false

/-- **Gusfield et al. 2007, Section 5.3.2.** The unrooted Full-Decomposition Optimality Conjecture is false for multiple crossovers: on Figure 8,
`F ≥ 4` and `R ≤ 3`. -/
theorem gusfield_unrootedConjecture_multiple_false :
    4 ≤ F .multiple fig8 ∧ R .multiple fig8 ≤ 3 ∧ ¬ UnrootedConjecture .multiple :=
  Gusfield2007.unrootedConjecture_multiple_false

/-- **Gusfield et al. 2007, Section 5.3.1.** The rooted Full-Decomposition Optimality Conjecture is false for single crossovers. -/
theorem gusfield_rootedConjecture_single_false : ¬ RootedConjecture .single := Gusfield2007.rootedConjecture_single_false

/-- **Gusfield et al. 2007, Section 5.3.** The rooted Full-Decomposition Optimality Conjecture is false for multiple crossovers. -/
theorem gusfield_rootedConjecture_multiple_false : ¬ RootedConjecture .multiple := Gusfield2007.rootedConjecture_multiple_false

/-- **Gusfield et al. 2007, Theorem 10 without an ancestral sequence**, which isn't in the paper. If `H(M) = R(M)` then `M` is min decomposable, and if `H(M) = R¹(M)` then
`M` is min-1 decomposable. -/
theorem gusfield_theorem10_unrooted {ι : Type*} [LinearOrder ι] [Finite ι] {c : Crossover} {M : Finset (ι → Bool)} (hM : M.Nonempty)
    (hC : NoConstantColumn M) (h : haplotypeBound M = R c M) : MinDecomposable c M :=
  Gusfield2007.minDecomposable_of_haplotypeBound_eq hM hC h

/-- **Gusfield et al. 2007, Theorem 10 as printed is false for single crossovers.** With the unrooted count `R¹(M + S)`, it fails on `printedRows`, fourteen rows on eight sites, with
`S = printedRoot`, one of the rows: `H(M + S) = R¹(M + S)` and `R¹_S(M) = 6`, and `M` is not S-min-1 decomposable. -/
theorem gusfield_theorem10Printed_single_false : printedRows.Nonempty ∧ NoConstantColumn printedRows ∧
    haplotypeBound (addRow printedRows printedRoot) = R .single (addRow printedRows printedRoot) ∧
    RS .single printedRoot printedRows = 6 ∧ ¬ SMinDecomposable .single printedRoot printedRows ∧
    ¬ Theorem10Printed .single printedRows printedRoot := Gusfield2007.theorem10Printed_single_false

/-- **Gusfield et al. 2007, Theorem 10 as printed, for multiple crossovers: false, given one computation.** This theorem is conditional. Its hypothesis `printedMSearch` is a
finite computation, a search showing that two extra labels never suffice on the second component of `printedMRows`, and it is not proved here: Lean's kernel hasn't completed it. Everything else
is proved: given it, the statement with the unrooted count `R(M + S)` fails on `printedMRows`, seventy-four rows on thirty-four sites, with `S = printedMRoot`, one of the rows. -/
theorem gusfield_theorem10Printed_multiple_false_of_search (hs : printedMSearch) : printedMRows.Nonempty ∧ NoConstantColumn printedMRows ∧
    haplotypeBound (addRow printedMRows printedMRoot) = R .multiple (addRow printedMRows printedMRoot) ∧
    ¬ SMinDecomposable .multiple printedMRoot printedMRows ∧ ¬ Theorem10Printed .multiple printedMRows printedMRoot :=
  Gusfield2007.theorem10Printed_multiple_false_of_search hs

/-- **Gusfield et al. 2007, line 425, reduced to roots.** The sentence at line 425 is open. When `M` is S-min decomposable for all `S`, it is min decomposable exactly when some
optimal root doesn't merge components of `G(M)`. -/
theorem gusfield_minDecomposable_iff_exists_root {ι : Type*} [LinearOrder ι] [Finite ι] {c : Crossover} {M : Finset (ι → Bool)} (hM : M.Nonempty)
    (hall : ∀ S, SMinDecomposable c S M) :
    MinDecomposable c M ↔ ∃ S, RS c S M = R c M ∧ ∀ i j, (conflictGraph S M).Reachable i j ↔ (incompatGraph M).Reachable i j :=
  Gusfield2007.minDecomposable_iff_exists_root hM hall

/-- **Gusfield et al. 2007, line 329, with the entry node counted.** A fully decomposed network can be made efficient, in the printed sense and with the entry node of a blob counted,
without increasing the number of recombination nodes, with the same ancestral sequence, staying fully decomposed. -/
theorem gusfield_exists_isEfficientAtEntry {ι : Type*} [LinearOrder ι] [Finite ι] {V E : Type*} [Finite V] [Finite E] (N : Network ι V E) {c : Crossover}
    {M : Finset (ι → Bool)} {G : SimpleGraph ι} (hC : NoConstantColumn M) (hc : N.Obeys c) (hd : N.Derives M)
    (hG : G = incompatGraph M ∨ G = conflictGraph N.ancestral M) (hf : N.IsFullyDecomposedFor G) :
    ∃ (a b : ℕ) (N' : Network ι (Fin a) (Fin b)), N'.Obeys c ∧ N'.Derives M ∧ N'.ancestral = N.ancestral ∧ N'.IsFullyDecomposedFor G ∧
      N'.IsEfficient ∧ N'.IsEfficientAtEntry ∧ N'.recombCount ≤ N.recombCount :=
  Gusfield2007.exists_isEfficientAtEntry_of_fullyDecomposed N hC hc hd hG hf

/-- **Gusfield et al. 2007, Section 4.2: the treeness inequality fails for a blob that merges two components.** `mergedNet` has every other condition of the true form, on rows with no
incompatible pair, its one blob has the sites `0` and `1`, its treeness is `5`, and `T̄` has `4` edges. -/
theorem gusfield_treeness_merged_false (c : Crossover) {W : Type*} [Finite W] {T : SimpleGraph W} {φ : starRows → W}
    {edge : SuperChar starRows → Sym2 W} (hT : IsTBar starRows T φ edge) :
    mergedNet.Obeys c ∧ mergedNet.Derives starRows ∧ NoConstantColumn starRows ∧ mergedNet.BlobsNodeDisjoint ∧ mergedNet.RegularArcs ∧
      mergedNet.NonPendantPortsDistinct ∧ mergedNet.DegreeCond ∧
      (∃ B, mergedNet.IsBlob B ∧ mergedNet.site 0 ∈ B ∧ mergedNet.site 1 ∈ B) ∧ (∀ i j, ¬ (incompatGraph starRows).Adj i j) ∧
      mergedNet.treeness = 5 ∧ T.edgeSet.ncard = 4 :=
  Gusfield2007.treeness_merged_false c hT

/-- **Gusfield et al. 2007, line 656, with equality.** `R¹(M_d) = 3d`; the paper claims the upper bound, and Theorem 11 needs only that. -/
theorem gusfield_Md_R_eq (d : ℕ) : R .single (Md d) = 3 * d := Gusfield2007.Md_R_eq d

/-- **Gusfield et al. 2007, line 590, the conjecture of Huson and Klöpper is false**, as the thesis of the second author states it, its Conjecture 2.2. -/
theorem gusfield_conjecture22_false : ¬ Conjecture22 := Gusfield2007.conjecture22_false

end TreeOfBlobs

/-! ## Gusfield, Eddhu, Langley 2004 -/

namespace TreeOfBlobs

open Gusfield2007 GusfieldEtAl2004

/-- **Gusfield, Eddhu, Langley 2004, in the proof of Theorem 2.2.** Two sites that conflict, in any set of rows labelling nodes of a network, are together on a recombination cycle. -/
theorem galled_exists_isCycle_of_conflict {ι V E : Type*} [Finite V] (N : Network ι V E) {L : Finset (ι → Bool)} (hL : ∀ r ∈ L, ∃ v, N.label v = r) {i j : ι}
    (h : Conflict N.ancestral L i j) : ∃ Q, N.IsCycle Q ∧ N.site i ∈ Q ∧ N.site j ∈ Q :=
  GusfieldEtAl2004.exists_isCycle_of_conflict N hL h

/-- **Gusfield, Eddhu, Langley 2004, Theorem 2.2.** On a galled tree with single crossovers, two sites `i < j` conflict exactly when they are together on a gall with recombination point
between them, arranged on it in one of the three ways `W1`, `W2`, `W3`. -/
theorem galled_theorem2_2 {ι V E : Type*} [LinearOrder ι] [Finite V] {N : Network ι V E} {M : Finset (ι → Bool)} (hG : IsGalledTree N) (hc₁ : N.Obeys .single)
    (hD : N.Derives M) {i j : ι} (hij : i < j) :
    Conflict N.ancestral M i j ↔ ∃ w x p q L₀, N.IsCycleOn w x p q ∧ IsRecombPoint N x p q L₀ ∧ i ∈ L₀ ∧ j ∉ L₀ ∧
      (W1 N w p q i j ∨ W2 N w p q i j ∨ W3 N w p q i j) :=
  GusfieldEtAl2004.theorem2_2 hG hc₁ hD hij

/-- **Gusfield, Eddhu, Langley 2004, Theorem 8.3.** A reduced galled tree for `M` has the least number of recombination nodes, in its model and even with multiple crossovers at each node,
and that number is the bound by removals. -/
theorem galled_theorem8_3 {ι V E : Type*} [LinearOrder ι] [Finite ι] [Finite V] [Finite E] {N : Network ι V E} {M : Finset (ι → Bool)}
    (h : IsReducedGalledTree N (conflictGraph N.ancestral M)) (hD : N.Derives M) {c : Crossover} (hc : N.Obeys c) :
    minRemovals N.ancestral M = N.recombCount ∧ RS c N.ancestral M = N.recombCount ∧ RS .multiple N.ancestral M = N.recombCount :=
  GusfieldEtAl2004.theorem8_3 h hD hc

/-- **Gusfield et al. 2007, line 381.** A galled tree reduced for `G(M)` makes `M` min decomposable, in its model and for multiple crossovers. -/
theorem galled_line381 {ι V E : Type*} [LinearOrder ι] [Finite ι] [Finite V] [Finite E] {N : Network ι V E} {M : Finset (ι → Bool)}
    (h : IsReducedGalledTree N (incompatGraph M)) (hD : N.Derives M) {c : Crossover} (hc : N.Obeys c) :
    MinDecomposable c M ∧ MinDecomposable .multiple M :=
  GusfieldEtAl2004.line381 h hD hc

open GusfieldEtAl2004.Algorithm in
/-- **Gusfield, Eddhu, Langley 2004, the algorithm: what it returns is a reduced galled tree** (Gusfield et al. 2007, line 180). If the computable function `galledBuild` returns a table, it is
the table of a network that derives `M` with ancestral sequence `S` and single crossovers, and that is a reduced galled tree. It's a departure from the source's Sections 3 to 7 in places, recorded in its docstrings. -/
theorem galled_galledBuild_correct {m : ℕ} {S : Row m} {M : List (Row m)} (hM : M ≠ []) (h1 : ∀ i, ∃ r ∈ M, r i ≠ S i) {t : GalledOut m} (ht : galledBuild S M = some t) :
    ∃ (f : Fin m → Fin m) (ar : Fin m → Arr m) (hs : Std S M f) (har : ∀ c, isNT f c = true → ArrOK S M f c (ar c)),
      t = (gTable S M f ar, List.ofFn (siteNode S f ar)) ∧ (gNet hs har).Obeys .single ∧ (gNet hs har).Derives M.toFinset ∧
      (gNet hs har).ancestral = S ∧ IsReducedGalledTree (gNet hs har) (conflictGraph S M.toFinset) :=
  GusfieldEtAl2004.Algorithm.galledBuild_correct hM h1 ht

open GusfieldEtAl2004.Algorithm in
/-- **Gusfield, Eddhu, Langley 2004, the algorithm, "polynomial time"** (Gusfield et al. 2007, line 180). On `n` rows and `m` sites, `galledBuildOps`, which returns the value of `galledBuild`, counts at most
`233 (n + m + 1)⁶` operations. This bound isn't the source's `O(nm + n³)`. -/
theorem galled_galledBuildOps_le {m : ℕ} (S : Row m) (M : List (Row m)) : (galledBuildOps S M).2 ≤ 233 * (M.length + m + 1) ^ 6 :=
  GusfieldEtAl2004.Algorithm.galledBuildOps_le S M

end TreeOfBlobs

/-! ## Myers, Griffiths 2003; Hudson, Kaplan 1985; Song, Hein 2005 -/

namespace TreeOfBlobs

open Gusfield2007

/-- **Myers, Griffiths 2003, Algorithm 1.** The matrix that the computable function `algorithm1` constructs is the matrix of optimal values of the integer program on regions: minimize
`Σ_{l=s}^{t-1} r_l` over nonnegative integers subject to the local bounds `B`. -/
theorem myersGriffiths_algorithm1_isOptimalValue (B : ℕ → ℕ → ℕ) {S s t : ℕ} (hst : s ≤ t) (ht : t < S) :
    MyersGriffiths2003.IsOptimalValue S B s t (MyersGriffiths2003.algorithm1 B S s t) :=
  MyersGriffiths2003.algorithm1_isOptimalValue B hst ht

/-- **Myers, Griffiths 2003, the bound `R_h`.** The haplotype bounds on regions, combined by Algorithm 1, are a lower bound on `R¹(M)`. -/
theorem myersGriffiths_Rh_le_R {S : ℕ} {M : Finset (Fin S → Bool)} (hM : M.Nonempty) (hS : 0 < S) : MyersGriffiths2003.Rh M ≤ R .single M :=
  MyersGriffiths2003.Rh_le_R hM hS

/-- **Hudson, Kaplan 1985, the algorithm of Appendix 2.** The final number of intervals on the list of the computable function `hudsonKaplan` is the optimal value of the program for the matrix `D`
of incompatible pairs: the bound `R_M`. -/
theorem hudsonKaplan_isOptimalValue {S : ℕ} {d : ℕ → ℕ → Bool} (hS : 0 < S) :
    MyersGriffiths2003.IsOptimalValue S (HudsonKaplan1985.incompatBounds d) 0 (S - 1) (HudsonKaplan1985.hudsonKaplan S d) :=
  HudsonKaplan1985.hudsonKaplan_isOptimalValue hS

/-- **Song, Hein 2005, equations (3), (5).** The minimum of `L(P)`, over sequences of binary trees with a total order on their internal nodes compatible with the columns, with the distance through such
trees, is `R¹(M)`, and it is attained. The columns aren't constant, as a constant column has no compatible tree here. -/
theorem songHein_exists_orderedLength_eq_R {m : ℕ} (M : Finset (Fin m → Bool)) (hM : M.Nonempty) (hC : NoConstantColumn M) :
    ∃ P : Fin m → TimeOrderedTree M, (∀ i, SongHein2005.IsOrdered (P i)) ∧ (∀ i, (P i).CompatibleWith fun r => (r : Fin m → Bool) i) ∧
      SongHein2005.orderedLength (List.ofFn P) = R .single M :=
  SongHein2005.exists_orderedLength_eq_R M hM hC

end TreeOfBlobs

/-! ## What the papers on the tree of blobs say in passing, and their other claims -/

namespace TreeOfBlobs

open Phylogenetics Phylogenetics.RootedNetwork ECToBlob TOBQMC AllmanEtAl2023 Filter Topology

universe u

/-- **Allman et al. 2023, Section 5: the distance between blobs is not identifiable.** On one network `𝒩(k)`, for every `k ≥ 1`, whose reduced tree of blobs is `ab|cd`, with stem of length `ε₀ > 0`: a
nondegenerate segment of concordance factors arises at `ε₀` and at every `ε′` near it, with other lengths `M`. -/
theorem allman_blobDistance_not_identifiable {X : Type*} [Fintype X] [DecidableEq X] {a b c d : X} (h : ({a, b, c, d} : Finset X).card = 4)
    (hX : Fintype.card X = 4) {k : ℕ} (hk : 1 ≤ k) {ε₀ : ℝ} (hε₀ : 0 < ε₀) :
    (Trd (NetworkNk.isBinaryNetwork_networkNk k h hX) (nontrivial_of_card_four hX)).HasQuartetTopology a b c d ∧
      ∃ q₁ q₂ : ℝ, q₁ < q₂ ∧ ∀ᶠ ε' in 𝓝 ε₀, 0 < ε' ∧ ∀ v ∈ Set.Icc q₁ q₂, ∃ M M' : ℝ, 0 < M ∧ 0 < M' ∧
        cfTriple (NetworkNk.networkNk k a b c d) (NetworkNk.metricNk k ε₀ M) a b c d h = (v, (1 - v) / 2, (1 - v) / 2) ∧
        cfTriple (NetworkNk.networkNk k a b c d) (NetworkNk.metricNk k ε' M') a b c d h = (v, (1 - v) / 2, (1 - v) / 2) :=
  InPassing.blobDistance_not_identifiable h hX hk hε₀

/-- **Allman et al. 2023, before Proposition 1, Baños's range.** `𝒩(1)` is level-1, with reduced tree of blobs `ab|cd`, and the values of the first entry of its `CF`, over all parameters, are exactly `(1/6, 1)`.
Baños's further bound on all level-1 networks isn't proved here. -/
theorem allman_banos_range {X : Type*} [Fintype X] [DecidableEq X] {a b c d : X} (hd : ({a, b, c, d} : Finset X).card = 4) (hX : Fintype.card X = 4) :
    (NetworkNk.networkNk 1 a b c d).IsLevelOne ∧
      (Trd (NetworkNk.isBinaryNetwork_networkNk 1 hd hX) (nontrivial_of_card_four hX)).HasQuartetTopology a b c d ∧
      {v | ∃ θ, (NetworkNk.networkNk 1 a b c d).IsMetric θ ∧ nmscCF (NetworkNk.networkNk 1 a b c d) θ 0 (quartetTree a b c d hd) = v} = Set.Ioo (1 / 6) 1 ∧
      ∀ v ∈ Set.Ioo (1 / 6 : ℝ) 1, ∃ θ, (NetworkNk.networkNk 1 a b c d).IsMetric θ ∧
        cfTriple (NetworkNk.networkNk 1 a b c d) θ a b c d hd = (v, (1 - v) / 2, (1 - v) / 2) :=
  NetworkNk.banos_range hd hX

/-- **Allman et al. 2023, Section 5: the outline of an algorithm is consistent.** For any test that is right on each set of four taxa with probability tending to one, the steps of the outline return the tree of blobs on
`m` independent gene trees with probability tending to one. -/
theorem allman_outline_consistent {V E X : Type*} [Fintype V] [Fintype E] [Fintype X] [DecidableEq X] {N : RootedNetwork V E X} (hN : N.IsPhylogenetic)
    (hX : 4 ≤ Fintype.card X) {θ : MetricData E} (hθ : N.IsMetric θ) {reject : ℕ → (QuartetTree X → ℝ) → Finset X → Prop}
    {top : (QuartetTree X → ℝ) → Finset X → QuartetTree X}
    (hright : ∀ q : Finset X, q.card = 4 → Tendsto (fun m => iidProb (geneTreeDist N θ 0) m fun ω =>
      Algorithm.RightOn N (reject m) top (quartetCount unroot ω) q) atTop (𝓝 1))
    {M : TreeBuilder X} (hM : IsExactBuilder M) :
    Tendsto (fun m => iidProb (geneTreeDist N θ 0) m fun ω =>
      Algorithm.outline (reject m) top M (quartetCount unroot ω) = treeOfBlobs N) atTop (𝓝 1) :=
  Algorithm.outline_consistent hN hX hθ hright hM

/-- **TINNiK, the sentence before Theorem 4: with missing taxa.** As `theorem4`, for gene trees on subsets of the taxa that leave each set of four taxa on more and more of them. -/
theorem tinnik_theorem4_missing {V E X : Type*} [Fintype V] [Fintype E] [Fintype X] [DecidableEq X] {N : RootedNetwork V E X} (hN : N.IsPhylogenetic)
    (hX : 4 ≤ Fintype.card X) (hBin : N.IsBinary) :
    ∃ A : Set (MetricData E), IsGenericNull N A ∧
      ∀ θ, N.IsMetric θ → θ ∉ A → ∀ on : (m : ℕ) → Fin m → Finset X, TINNiK.Covers on →
        ∃ α : ℕ → ℝ, Tendsto α atTop (𝓝 0) ∧ (∀ m, 0 < α m) ∧
          ∀ (β δ : ℝ), 0 < β → 0 ≤ δ → δ < 2 → ∀ (M : TreeBuilder X), IsExactBuilder M →
          ∀ (ml : (QuartetTree X → ℝ) → Finset X → QuartetTree X), IsMLSelection ml →
            Tendsto (fun m => iidProb (geneTreeDist N θ 0) m fun ω =>
              tinnik ml (α m) β δ M (quartetCountOn unroot (on m) ω) = treeOfBlobs N) atTop (𝓝 1) :=
  TINNiK.theorem4_missing hN hX hBin

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

/-- **ECToBlob, Theorem 8.2, for the displayed tree model, for Bon and BBC.** There are sequences `α_n`, `β_n`, independent of the network, such that for every network, possibly non-binary, every resolution `T₀` of the
tree of blobs and every variant with Bon or BBC, the output on the counts of `n` displayed trees is the tree of blobs with probability tending to one. The converse of Assumption 1 is a hypothesis at the parameters. -/
theorem ectoblob_theorem8_2_displayed : ∃ α β : ℕ → ℝ, Tendsto α atTop (𝓝 0) ∧ Tendsto β atTop (𝓝 0) ∧
    (∀ᶠ n in atTop, 0 < α n ∧ α n < 1) ∧ (∀ᶠ n in atTop, 0 < β n ∧ β n < 1) ∧
    ∀ {V E X : Type u} [Fintype V] [Fintype E] [Fintype X] [DecidableEq X] [Nonempty X]
      (N : RootedNetwork V E X) (_ : N.IsPhylogenetic) (θ : MetricData E) (_ : N.IsWeakMetric θ)
      (_ : Assumption1Converse N (displayedCF N θ))
      (T₀ : Finset (Finset X)) (_ : IsResolutionOf T₀ (treeOfBlobs N))
      (o : ECToBlobOptions) (_ : o.testCo = .bon ∨ o.testCo = .bbc),
      Tendsto (fun n => iidProb (displayedTreeDist N θ) n fun ω =>
        ectoblob o (α n) (β n) (conventionCount ω) T₀ = treeOfBlobs N) atTop (𝓝 1) :=
  DisplayedTree.theorem8_2_displayed

/-- **ECToBlob, Theorem 8.2 fails for Cauchy and CBC on the displayed tree model.** At all valid parameters of a binary network, both directions of Assumption 1 hold and `T₀` resolves the tree of blobs. At any levels
`α_n ≤ 1`, `β_n → 0` from above with `o(n)` cutoffs, the output with Cauchy or CBC is `T₀` with probability tending to one, and so the tree of blobs with probability tending to zero; with Bon or BBC it is the tree of blobs. All of this
rests on the extension of the Cauchy transform at `p = 1`, as `theorem8_2` does. -/
theorem ectoblob_displayed_counterexample {θ : MetricData (Fin 11)} (hθ : FinNetwork.Binary.net.IsMetric θ) :
    Assumption1Forward FinNetwork.Binary.net (displayedCF FinNetwork.Binary.net θ) ∧
      Assumption1Converse FinNetwork.Binary.net (displayedCF FinNetwork.Binary.net θ) ∧
      IsResolutionOf FinNetwork.Binary.T₀ (treeOfBlobs FinNetwork.Binary.net) ∧ FinNetwork.Binary.T₀ ≠ treeOfBlobs FinNetwork.Binary.net ∧
      (∀ o : ECToBlobOptions, (o.testCo = .cauchy ∨ o.testCo = .cbc) → ∀ {α β : ℕ → ℝ},
        (∀ᶠ n in atTop, α n ≤ 1) → Tendsto β atTop (𝓝[>] 0) →
        Tendsto (fun n : ℕ => Real.log (β n) / n) atTop (𝓝 0) →
        Tendsto (fun n => iidProb (displayedTreeDist FinNetwork.Binary.net θ) n fun ω =>
          ectoblob o (α n) (β n) (conventionCount ω) FinNetwork.Binary.T₀ = FinNetwork.Binary.T₀) atTop (𝓝 1) ∧
        Tendsto (fun n => iidProb (displayedTreeDist FinNetwork.Binary.net θ) n fun ω =>
          ectoblob o (α n) (β n) (conventionCount ω) FinNetwork.Binary.T₀ = treeOfBlobs FinNetwork.Binary.net) atTop (𝓝 0)) ∧
      (∀ o : ECToBlobOptions, (o.testCo = .bon ∨ o.testCo = .bbc) → ∀ {α β : ℕ → ℝ},
        Tendsto α atTop (𝓝[>] 0) → Tendsto β atTop (𝓝[>] 0) →
        Tendsto (fun n : ℕ => Real.log (α n) / n) atTop (𝓝 0) →
        Tendsto (fun n : ℕ => Real.log (β n) / n) atTop (𝓝 0) →
        Tendsto (fun n => iidProb (displayedTreeDist FinNetwork.Binary.net θ) n fun ω =>
          ectoblob o (α n) (β n) (conventionCount ω) FinNetwork.Binary.T₀ = treeOfBlobs FinNetwork.Binary.net) atTop (𝓝 1)) :=
  FinNetwork.Binary.counterexample hθ

/-- **ECToBlob, Theorem 8.2 without its hypothesis on the alternatives is false for Cauchy and CBC, at all sequences.** No sequences `α_n`, `β_n` are valid for every law of binary gene trees meeting both directions of Assumption 1,
with no condition on the alternatives, for all the variants with that correction. -/
theorem ectoblob_not_theorem8_2_without_hpos {m : TestCorrection} (hm : m = .cauchy ∨ m = .cbc) :
    ¬ ∃ α β : ℕ → ℝ, Tendsto α atTop (𝓝 0) ∧ Tendsto β atTop (𝓝 0) ∧
      (∀ᶠ n in atTop, 0 < α n ∧ α n < 1) ∧ (∀ᶠ n in atTop, 0 < β n ∧ β n < 1) ∧
      ∀ {V E X : Type} [Fintype X] [DecidableEq X] (N : RootedNetwork V E X)
        (_ : N.IsPhylogenetic) (dist : BinaryGeneTree X → ℝ) (_ : IsDist dist)
        (_ : Assumption1Forward N (displayCF dist Subtype.val))
        (_ : Assumption1Converse N (displayCF dist Subtype.val))
        (T₀ : Finset (Finset X)) (_ : IsResolutionOf T₀ (treeOfBlobs N))
        (o : ECToBlobOptions) (_ : o.testCo = m),
        Tendsto (fun n => iidProb dist n fun ω =>
          ectoblob o (α n) (β n) (quartetCount Subtype.val ω) T₀ = treeOfBlobs N) atTop (𝓝 1) :=
  BinaryLaw.not_theorem8_2_without_hpos hm

/-- **ECToBlob, §10: combining the edge p-values under CBC is not consistent.** On one network and one law that meets both directions of Assumption 1, with positive alternatives, the other three corrections are consistent, and the variant
with CBC outputs the tree `T₀` with its false edge with probability at least `1/2 - ε`, for large `n`. -/
theorem ectoblob_not_consistency_edge_combination_cbc :
    IsDist BinaryLaw.OnBinary.lawC ∧ Assumption1Forward FinNetwork.Binary.net (displayCF BinaryLaw.OnBinary.lawC Subtype.val) ∧
      Assumption1Converse FinNetwork.Binary.net (displayCF BinaryLaw.OnBinary.lawC Subtype.val) ∧
      (∀ s, IsT1Strict (displayCF BinaryLaw.OnBinary.lawC Subtype.val) s →
        ∀ r ∈ s.alternatives, 0 < displayCF BinaryLaw.OnBinary.lawC Subtype.val r) ∧
      (∀ o : ECToBlobOptions, o.testCo ≠ .cbc → Tendsto (fun n => iidProb BinaryLaw.OnBinary.lawC n fun ω =>
        Remarks.ectoblobEdge o (alphaSeq n) (betaSeq n) (quartetCount Subtype.val ω) FinNetwork.Binary.T₀ = treeOfBlobs FinNetwork.Binary.net)
        atTop (𝓝 1)) ∧
      ∀ o : ECToBlobOptions, o.testCo = .cbc → ∀ {α β : ℕ → ℝ}, (∀ᶠ n in atTop, α n ≤ 1) →
        Tendsto β atTop (𝓝[>] 0) → Tendsto (fun n : ℕ => Real.log (β n) / n) atTop (𝓝 0) →
        (∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, 1 / 2 - ε < iidProb BinaryLaw.OnBinary.lawC n fun ω =>
          Remarks.ectoblobEdge o (α n) (β n) (quartetCount Subtype.val ω) FinNetwork.Binary.T₀ = FinNetwork.Binary.T₀) ∧
        ¬ Tendsto (fun n => iidProb BinaryLaw.OnBinary.lawC n fun ω =>
          Remarks.ectoblobEdge o (α n) (β n) (quartetCount Subtype.val ω) FinNetwork.Binary.T₀ = treeOfBlobs FinNetwork.Binary.net) atTop (𝓝 1) :=
  BinaryLaw.OnBinary.not_consistency_edge_combination_cbc

/-- **ECToBlob, Remark 3.4, duplication and loss.** On the network of a species tree, whose tree of blobs is the unrooted species tree, (3.1) holds as the hypothesis of Theorem 3.1: `p` is the probability of a quartet tree under a uniform pick
of one gene copy per species, in the model of Legried et al. 2021 with any law on each edge, without incomplete lineage sorting. -/
theorem ectoblob_remark3_4_displays {Y : Type} [Fintype Y] [DecidableEq Y] {T : External.LegriedEtAl2021.SpeciesTree Y} (hT : T.Nodup) (hall : ∀ x, T.Has x) (hS : T.Survives) :
    ∀ s, Displays (treeOfBlobs (External.LegriedEtAl2021.speciesNetwork T hT hall)) s → ∀ r ∈ s.alternatives,
      External.LegriedEtAl2021.quartetP T r < External.LegriedEtAl2021.quartetP T s :=
  Remark34.remark3_4_displays hT hall hS

/-- **ECToBlob, §10: the framework on distances.** For a sample of `n` loci with bounded distances `d`, of mean `D`, with the analogue of Assumption 1 for `D`, the algorithm on the p-values `spStarP` and `spT1P`, with Bon or BBC, returns the tree of blobs
with probability tending to one, at any levels with `o(n)` cutoffs. -/
theorem ectoblob_consistency_sumOfPairs {V E X : Type*} [Fintype X] [DecidableEq X] {Γ : Type*} [Fintype Γ] {N : RootedNetwork V E X} {dist : Γ → ℝ}
    {d : Γ → X → X → ℝ} {B : ℝ} (hN : N.IsPhylogenetic) (hd : IsDist dist) (hB : 0 < B)
    (hb : ∀ g x y, |d g x y| ≤ B) (hF : SumOfPairs.SPForward N (SumOfPairs.meanDist dist d))
    (hC : SumOfPairs.SPConverse N (SumOfPairs.meanDist dist d)) {T₀ : Finset (Finset X)}
    (hT₀ : IsResolutionOf T₀ (treeOfBlobs N)) {o : ECToBlobOptions}
    (hm : o.testCo = .bon ∨ o.testCo = .bbc) {α β : ℕ → ℝ} (hα₀ : Tendsto α atTop (𝓝[>] 0))
    (hβ₀ : Tendsto β atTop (𝓝[>] 0)) (hα : Tendsto (fun n : ℕ => Real.log (α n) / n) atTop (𝓝 0))
    (hβ : Tendsto (fun n : ℕ => Real.log (β n) / n) atTop (𝓝 0)) :
    Tendsto (fun n => iidProb dist n fun ω =>
      Framework.ectoblobBy o (α n) (β n) (fun s => SumOfPairs.spStarP (8 * B) d s n ω) (fun s => SumOfPairs.spT1P (8 * B) d s n ω) T₀ =
        treeOfBlobs N) atTop (𝓝 1) :=
  SumOfPairs.consistency_sumOfPairs hN hd hB hb hF hC hT₀ hm hα₀ hβ₀ hα hβ

end TreeOfBlobs

/-! ## The other sources: NANUQ; Mitchell, Allman, Rhodes 2019; Ané et al. 2024; Huber et al. 2025; Dinh, Baños 2025; Kane, Tao 2017; Legried et al. 2021 -/

namespace TreeOfBlobs

open Phylogenetics Phylogenetics.RootedNetwork Filter Topology Finset MeasureTheory ProbabilityTheory

open External.AllmanBanosRhodes2019 in
/-- **NANUQ (Allman, Baños, Rhodes 2019), Proposition 9**, in the source's own terms, on a set of four taxa of a binary level-1 network, for the network multispecies coalescent at any `0 ≤ ρ ≤ 1`. `Q̃` is `qTilde`, and an `m_k`-cycle is `HasCycleType`. With no `4₁`- or `3₂`-cycle, the
concordance factor is tree-like and supports `Q̃`; with a `3₂`-cycle, its entry for `Q̃` is at least `1/6`, the other two are equal, and a tree-like one supports `Q̃` or is the centroid; with a `4₁`-cycle, it isn't tree-like, and on the 4-cycle `a, b, c, d` the entry of `ac|bd` is the least. -/
theorem nanuq_proposition9_source {V E X : Type*} [Fintype V] [Fintype E] [Fintype X] [DecidableEq X] {N : RootedNetwork V E X} {q : Finset X}
    (hN : N.IsPhylogenetic) (hBin : N.IsBinary) (hLevel : IsLevelOne N) {θ : MetricData E} (hθ : N.IsMetric θ)
    {ρ : ℝ} (hρ : 0 ≤ ρ ∧ ρ ≤ 1) (hq : #q = 4) {a b c d : {x // x ∈ q}} (h : ({a.1, b.1, c.1, d.1} : Finset X).card = 4)
    (h' : ({a.1, c.1, b.1, d.1} : Finset X).card = 4) (h'' : ({a.1, d.1, b.1, c.1} : Finset X).card = 4) :
    (¬ Quartet.HasCycleType N q 4 1 → ¬ Quartet.HasCycleType N q 3 2 → (Quartet.qTilde hN (by omega : 2 ≤ #q)).HasQuartetTopology a b c d →
      nmscCF N θ ρ (quartetTree a.1 c.1 b.1 d.1 h') < nmscCF N θ ρ (quartetTree a.1 b.1 c.1 d.1 h) ∧
      nmscCF N θ ρ (quartetTree a.1 c.1 b.1 d.1 h') = nmscCF N θ ρ (quartetTree a.1 d.1 b.1 c.1 h'')) ∧
    (Quartet.HasCycleType N q 3 2 → (Quartet.qTilde hN (by omega : 2 ≤ #q)).HasQuartetTopology a b c d →
      1 / 6 ≤ nmscCF N θ ρ (quartetTree a.1 b.1 c.1 d.1 h) ∧
      nmscCF N θ ρ (quartetTree a.1 c.1 b.1 d.1 h') = nmscCF N θ ρ (quartetTree a.1 d.1 b.1 c.1 h'') ∧
      (IsT3Null (nmscCF N θ ρ) q →
        nmscCF N θ ρ (quartetTree a.1 c.1 b.1 d.1 h') < nmscCF N θ ρ (quartetTree a.1 b.1 c.1 d.1 h) ∨
          ∀ r ∈ treesOn q, nmscCF N θ ρ r = 1 / 3)) ∧
    (Quartet.HasCycleType N q 4 1 → (¬ IsT3Null (nmscCF N θ ρ) q) ∧
      (Quartet.HasFourCycleTopology (Quartet.qTilde hN (by omega : 2 ≤ #q)) a b c d →
        nmscCF N θ ρ (quartetTree a.1 c.1 b.1 d.1 h') < nmscCF N θ ρ (quartetTree a.1 b.1 c.1 d.1 h) ∧
        nmscCF N θ ρ (quartetTree a.1 c.1 b.1 d.1 h') < nmscCF N θ ρ (quartetTree a.1 d.1 b.1 c.1 h''))) :=
  Quartet.proposition9_source hN hBin hLevel hθ hρ hq h h' h''

open External.AllmanBanosRhodes2019 in
/-- **NANUQ, Theorem 36, corrected, with gene trees on subsets of the taxa.** With probability tending to one, on the concordance factors of `m` independent gene trees, the classification of all sets of four taxa, and so the quartet distance, is that of the network. The rest of the
source's Theorem 36, the splits graph of the output, isn't formalized. -/
theorem nanuq_theorem36_missing {V E X : Type*} [Fintype V] [Fintype E] [Fintype X] [DecidableEq X] [Nonempty X] {N : RootedNetwork V E X} {θ : MetricData E}
    (hN : N.IsPhylogenetic) (hBin : N.IsBinary) (hLevel : IsLevelOne N) (hθ : N.IsMetric θ)
    (h32 : ThreeTwoTreelike N (nmscCF N θ 0)) (hcen : TINNiK.NoCentroidCF (nmscCF N θ 0))
    {on : (m : ℕ) → Fin m → Finset X} (hon : TINNiK.Covers on) :
    ∃ α : ℕ → ℝ, (∀ m, 0 < α m) ∧ (∀ᶠ m in atTop, α m < 1) ∧ Tendsto α atTop (𝓝 0) ∧
      ∀ β : ℝ, 0 < β → β < 1 → ∀ mlT mlC : (QuartetTree X → ℝ) → Finset X → QuartetTree X,
        IsMaxCountSelection mlT → IsMinCountSelection mlC →
        Tendsto (fun m => iidProb (geneTreeDist N θ 0) m fun ω =>
          (∀ q : Finset X, q.card = 4 →
            classify mlT mlC (α m) β (quartetCountOn unroot (on m) ω) q = networkClass N q) ∧
            nanuqDistance (classify mlT mlC (α m) β (quartetCountOn unroot (on m) ω)) = networkDistance N)
          atTop (𝓝 1) :=
  theorem36_missing hN hBin hLevel hθ h32 hcen hon

open External.MitchellAllmanRhodes2019 Trinomial QuartetTests in
/-- **Mitchell, Allman, Rhodes 2019, Proposition 4.1**, for the trinomial. At the true point `(1 - 2φ/3, φ/3, φ/3)`, `0 < φ ≤ 1`, the likelihood ratio statistic of model T3 and the variable `t3Var φ`, with `Z ~ N(0, 1)`, `Z̄ ~ N(μ₀(n), 1)` independent, converge in
distribution to the same limit. The source's route through van der Vaart's Theorem 16.7 is replaced by the central limit theorem for this model. -/
theorem mitchell_proposition4_1 {φ : ℝ} (hφ : 0 < φ ∧ φ < 3 / 2) (hφ1 : φ ≤ 1) : ∃ ν : ProbabilityMeasure ℝ,
    (∀ f : BoundedContinuousFunction ℝ ℝ,
      Tendsto (fun n : ℕ ↦ ∫ x, f x ∂((Measure.pi fun _ : Fin n ↦
          (cutPoint_isDist hφ).toPMF.toMeasure).map fun η ↦ t3S (count η 0) (count η 1) (count η 2)))
        atTop (𝓝 (∫ x, f x ∂(ν : Measure ℝ)))) ∧
    (∀ f : BoundedContinuousFunction ℝ ℝ,
      Tendsto (fun n : ℕ ↦ ∫ x, f x ∂((normalSample (muZero φ n)).map (t3Var φ)))
        atTop (𝓝 (∫ x, f x ∂(ν : Measure ℝ)))) :=
  proposition4_1 hφ hφ1

/-- **Mitchell, Allman, Rhodes 2019, Proposition 4.2.** The printed density `t3Density` is the density of the variable `t3Var φ`, for all `φ < 3/2`; the source states it for `(0, 1]`. -/
theorem mitchell_proposition4_2 {φ : ℝ} (hφ : φ < 3 / 2) (n : ℝ) :
    (∀ lam, 0 ≤ t3Density φ n lam) ∧
      ((gaussianReal 0 1).prod (gaussianReal (muZero φ n) 1)).map (t3Var φ) =
        volume.withDensity (fun lam => ENNReal.ofReal (t3Density φ n lam)) :=
  External.MitchellAllmanRhodes2019.proposition4_2 hφ n

open External.MitchellAllmanRhodes2019 Trinomial QuartetTests in
/-- **Mitchell, Allman, Rhodes 2019, Proposition 5.1**, for the trinomial: as `mitchell_proposition4_1`, for model T1 and the variable `t1Var`. -/
theorem mitchell_proposition5_1 {φ : ℝ} (hφ : 0 < φ ∧ φ < 3 / 2) (hφ1 : φ ≤ 1) : ∃ ν : ProbabilityMeasure ℝ,
    (∀ f : BoundedContinuousFunction ℝ ℝ,
      Tendsto (fun n : ℕ ↦ ∫ x, f x ∂((Measure.pi fun _ : Fin n ↦
          (cutPoint_isDist hφ).toPMF.toMeasure).map fun η ↦ t1S (count η 0) (count η 1) (count η 2)))
        atTop (𝓝 (∫ x, f x ∂(ν : Measure ℝ)))) ∧
    (∀ f : BoundedContinuousFunction ℝ ℝ,
      Tendsto (fun n : ℕ ↦ ∫ x, f x ∂((normalSample (muZero φ n)).map t1Var))
        atTop (𝓝 (∫ x, f x ∂(ν : Measure ℝ)))) :=
  proposition5_1 hφ hφ1

/-- **Mitchell, Allman, Rhodes 2019, Proposition 5.2.** The printed density `t1Density` is the density of the variable `t1Var`, with `μ₀ = muZero φ n`. -/
theorem mitchell_proposition5_2 (φ n : ℝ) :
    (∀ lam, 0 ≤ t1Density (muZero φ n) lam) ∧
      ((gaussianReal 0 1).prod (gaussianReal (muZero φ n) 1)).map t1Var =
        volume.withDensity (fun lam => ENNReal.ofReal (t1Density (muZero φ n) lam)) :=
  External.MitchellAllmanRhodes2019.proposition5_2 φ n

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

open External.LegriedEtAl2021 in
/-- **Legried, Molloy, Warnow, Roch 2021, Theorem 1**, on quartets: a species tree is identifiable from the distribution of gene trees under gene duplication and loss. If two species trees give the same probabilities of topologies on four gene copies picked uniformly, and all four species have a
copy with positive probability, then the unrooted trees display the same quartets. -/
theorem legried_theorem1 {X : Type} {T T' : SpeciesTree X} (hT : T.Nodup) (hT' : T'.Nodup) {A B C D : X} (hAB : A ≠ B) (hAC : A ≠ C) (hAD : A ≠ D)
    (hBC : B ≠ C) (hBD : B ≠ D) (hCD : C ≠ D) (hA : T.Has A) (hB : T.Has B) (hC : T.Has C) (hD : T.Has D) (hA' : T'.Has A)
    (hB' : T'.Has B) (hC' : T'.Has C) (hD' : T'.Has D)
    (hSc : expect (geneLaw T) (Sc pickWeight A B C D) = expect (geneLaw T') (Sc pickWeight A B C D))
    (hAlt : expect (geneLaw T) (Alt pickWeight A B C D) = expect (geneLaw T') (Alt pickWeight A B C D))
    (hAlt₂ : expect (geneLaw T) (Alt₂ pickWeight A B C D) = expect (geneLaw T') (Alt₂ pickWeight A B C D))
    (hpos : 0 < expect (geneLaw T) fun L => ind (Present A B C D L)) (hq : T.IsQuartet A B C D) : T'.IsQuartet A B C D :=
  External.LegriedEtAl2021.theorem1 hT hT' hAB hAC hAD hBC hBD hCD hA hB hC hD hA' hB' hC' hD' hSc hAlt hAlt₂ hpos hq

end TreeOfBlobs
