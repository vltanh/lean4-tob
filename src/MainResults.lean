module

public import AllmanEtAl2023.Lemma1
public import AllmanEtAl2023.Lemma2Counterexample
public import AllmanEtAl2023.Proposition1
public import AllmanEtAl2023.Theorem4
public import Basic.Defs
public import Basic.Testing.IID
public import ECToBlob.Section3
public import ECToBlob.Section4
public import ECToBlob.Section8
public import Gusfield2007.Counterexamples
public import Gusfield2007.Realizability
public import TINNiK.Basic
public import TOBQMC.Consistency
public import TOBQMC.Level1
public import TOBQMC.WQC

/-!
# The main results: tree of blobs inference from quartets, and the theory of blobs behind it

Main results of five papers, each stated in plain terms and proved from its paper's library: **ECToBlob** (Rhodes, Allman,
Ané, Baños, bioRxiv v1, 2026), Theorems 3.1, 4.1, 8.2; **TOB-QMC** (Dai, Han, Molloy, bioRxiv v5, 2026), Theorems 1, 2 and the
consistency claim of §4.3; **TINNiK** (Allman, Baños, Mitchell, Rhodes, Algorithms Mol. Biol. 19, 2024), Theorem 4; **Allman et al.
2023** (Allman, Baños, Mitchell, Rhodes, J. Math. Biol. 86, 2023), Lemma 1, Theorems 1 to 4, Corollary 1, Proposition 1;
**Gusfield et al. 2007** (Gusfield, Bansal, Bafna, Song, J. Comput. Biol. 14, 2007), Lemma 4, Theorems 1 and 3 to 11, Corollaries 2,
3, and the refutation of its conjectures. `docs/REPORT.md` lists every correction and departure.

All are proved, with no assumed result. This includes the CF-detectability of 4-blobs for generic parameters (Allman et
al. 2023, Theorem 1 and Corollary 1; TINNiK's Theorem 1), which `theorem4` uses.

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
tending to one. The tests are TINNiK's star and cut tests; the T3 option is not treated. -/
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
every compatible site is on a tree edge. The two hypotheses are implicit in the paper. -/
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
that originate from `C`, on the 0-side of each of their splits. A correction: a trivial `C` keeps both of its columns here, which label
one edge with opposite 0-sides, so the second clause is for a non-trivial `C`, and the third is what a trivial `C` has. -/
theorem gusfield_lemma4 {ι : Type*} {M : Finset (ι → Bool)} {W : Type*} [Finite W] {T : SimpleGraph W} {φ : M → W}
    {edge : SuperChar M → Sym2 W} (h : IsTBar M T φ edge) (c : (incompatGraph M).ConnectedComponent) :
    ∃ v, (∀ k : SuperChar M, k.1 = c → v ∈ edge k) ∧
      (c.supp.Nontrivial → ∀ k : SuperChar M, k.1 = c → ∀ r : M, charValue k r = true →
        ¬ SameSide T (edge k) (φ r) v) ∧
      ∀ k : SuperChar M, k.1 = c → ∃ v ∈ edge k, ∀ r : M, charValue k r = true → ¬ SameSide T (edge k) (φ r) v :=
  Gusfield2007.lemma4 h c

/-- **Gusfield et al. 2007, Theorem 4, with the entry node counted**, a correction. For a fully decomposed network, the blobbed tree `T′` is
`T̄` exactly when the network is efficient with the entry node of a blob counted, and it has `RegularArcs` and the degree condition. -/
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

/-- **Gusfield et al. 2007, Theorem 10**, corrected. If `H(M + S) = R_S(M)`, or `R¹_S(M)`, then `M` is S-min, or S-min-1, decomposable. Two
corrections: `R_S` in place of the printed `R(M + S)`, since the proof's network has ancestral sequence `S`; and, for single crossovers, distinct
columns in `M + S`, which the equality case of the printed proof needs. -/
theorem gusfield_theorem10 {ι : Type*} [LinearOrder ι] [Finite ι] {c : Crossover} {M : Finset (ι → Bool)} {S : ι → Bool}
    (hM : M.Nonempty) (hC : NoConstantColumn M)
    (hinj : c = .single → Function.Injective fun i : ι => fun r : addRow M S => (r : ι → Bool) i)
    (h : haplotypeBound (addRow M S) = RS c S M) : SMinDecomposable c S M := Gusfield2007.theorem10 hM hC hinj h

/-- **Gusfield et al. 2007, Theorem 10, multiple crossovers**: the hypothesis of distinct columns isn't needed, though the printed proof doesn't
apply without it. If `H(M + S) = R_S(M)` then `M` is S-min decomposable. -/
theorem gusfield_theorem10_multiple {ι : Type*} [LinearOrder ι] [Finite ι] {M : Finset (ι → Bool)} {S : ι → Bool}
    (hM : M.Nonempty) (hC : NoConstantColumn M) (h : haplotypeBound (addRow M S) = RS .multiple S M) :
    SMinDecomposable .multiple S M := Gusfield2007.theorem10_multiple hM hC h

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

end TreeOfBlobs
