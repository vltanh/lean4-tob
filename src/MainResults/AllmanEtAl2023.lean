module

public import AllmanEtAl2023.Algorithm
public import AllmanEtAl2023.BlobDefinitions
public import AllmanEtAl2023.BlobDistance
public import AllmanEtAl2023.Concordance
public import AllmanEtAl2023.Corollary1
public import AllmanEtAl2023.Definitions
public import AllmanEtAl2023.Lemma1
public import AllmanEtAl2023.Lemma2
public import AllmanEtAl2023.Lemma2Counterexample
public import AllmanEtAl2023.NetworkNk
public import AllmanEtAl2023.NetworkOne
public import AllmanEtAl2023.Proposition1
public import AllmanEtAl2023.SubgraphBlobs
public import AllmanEtAl2023.Theorem1
public import AllmanEtAl2023.Theorem2
public import AllmanEtAl2023.Theorem3
public import AllmanEtAl2023.Theorem4
public import Basic.Testing.IID
public import Phylogenetics.Graph.Blobs
public import Phylogenetics.Graph.Defs
public import Phylogenetics.Hierarchy.Defs
public import Phylogenetics.NMSC.Defs
public import Phylogenetics.Network.Defs
public import Phylogenetics.Network.Quartets
public import Phylogenetics.Tree.Defs
public import Phylogenetics.Tree.Metric
public import Phylogenetics.Tree.Splits

/-!
# The main results of Allman et al. 2023

Allman, Baños, Mitchell, Rhodes, J. Math. Biol. 86, 2023: Lemma 1, Theorems 1 to 4, Corollary 1, Proposition 1 and its converse, and what the paper says in passing. The theorems are on the paper's own objects, in `AllmanEtAl2023`: `IsBinaryNetwork`, its Definition 1; `Trd`, the reduced unrooted tree of blobs; `cfTriple`, the concordance factor `CF_abcd`; `ForGenericParams N P`, "for generic numerical parameters", `P` outside a null set.

Each theorem is stated in plain terms and proved from the libraries. `papers/AllmanEtAl2023/README.md` and `papers/AllmanEtAl2023/REPORT.md` describe the formalization and list every correction and departure, and `papers/AllmanEtAl2023/palomar/` has the paper's entry for Palomar. `MainResults` imports this module with those of the other papers.
-/

@[expose] public noncomputable section

open Finset MeasureTheory ProbabilityTheory
open scoped Classical

namespace TreeOfBlobs

universe u

section

open Phylogenetics Phylogenetics.RootedNetwork Phylogenetics.DirectedMultigraph AllmanEtAl2023

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

end

/-! ## What the paper says in passing, and its other claims -/

section

open Phylogenetics Phylogenetics.RootedNetwork ECToBlob TOBQMC AllmanEtAl2023 Filter Topology

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

end

end TreeOfBlobs
