module

public import AllmanEtAl2023.BlobDefinitions
public import Basic.Defs
public import Basic.FinNetwork
public import Basic.Testing.Combining
public import Basic.Testing.IID
public import Basic.Testing.MissingTaxa
public import ECToBlob.BinaryLawExample
public import ECToBlob.DisplayedTree
public import ECToBlob.DisplayedTreeExample
public import ECToBlob.Equation33Counterexample
public import ECToBlob.Framework
public import ECToBlob.Remark33
public import ECToBlob.Remark34
public import ECToBlob.Remarks
public import ECToBlob.Section3
public import ECToBlob.Section4
public import ECToBlob.Section5
public import ECToBlob.Section8
public import ECToBlob.SumOfPairs
public import ECToBlob.Theorem82Literal
public import External.AllmanBanosRhodes2019.MissingTaxa
public import External.AllmanBanosRhodes2019.NANUQ
public import External.AllmanBanosRhodes2019.Quartet
public import External.AllmanBanosRhodes2019.QuartetClass
public import External.AllmanBanosRhodes2019.QuartetContract
public import External.AllmanBanosRhodes2019.QuartetForm
public import External.LegriedEtAl2021.Bridge
public import External.LegriedEtAl2021.Expect
public import External.LegriedEtAl2021.Model
public import External.LegriedEtAl2021.Theorem1
public import External.MitchellAllmanRhodes2019.T3Test
public import Phylogenetics.Hierarchy.Defs
public import Phylogenetics.NMSC.Defs
public import Phylogenetics.NMSC.History
public import Phylogenetics.Network.Defs
public import Phylogenetics.Network.OfHierarchy
public import Phylogenetics.Network.Quartets
public import Phylogenetics.Tree.Defs
public import Phylogenetics.Tree.Splits
public import TINNiK.Basic
public import TINNiK.MissingTaxa

/-!
# The main results of ECToBlob

Rhodes, Allman, Ané, Baños, bioRxiv v1, 2026: Theorems 3.1, 4.1 and 8.2, what the paper says in passing, and the main results of two sources it cites, NANUQ (`nanuq_`) and Legried et al. 2021 (`legried_`).

Each theorem is stated in plain terms and proved from the libraries. `docs/reports/ECToBlob.md` lists every correction and departure, and `palomar/ECToBlob/` has the paper's entry for Palomar. `MainResults` imports this module with those of the other papers.
-/

@[expose] public noncomputable section

open Finset MeasureTheory ProbabilityTheory
open scoped Classical

namespace TreeOfBlobs

universe u

section

open Phylogenetics Phylogenetics.RootedNetwork ECToBlob TOBQMC Filter Topology

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

end

/-! ## What the paper says in passing, and its other claims -/

section

open Phylogenetics Phylogenetics.RootedNetwork ECToBlob TOBQMC AllmanEtAl2023 Filter Topology

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

/-- **ECToBlob, equation (3.3) as printed is false** (E2 of the report). At the multifurcation of a species tree, under the network multispecies coalescent at all valid parameters, the left side is `3` and the right side `10/3`. The repair is the weights of `ECToBlob.equation3_3`. -/
theorem ectoblob_not_equation33Printed : ¬ Equation33Counterexample.Equation33Printed := Equation33Counterexample.not_equation33Printed

/-- **ECToBlob, Theorem 8.2 on the literal general model is false** (E10 of the report). For each variant of the algorithm, no levels `α_n`, `β_n` serve all valid parameters of all models meeting Assumption 1: a one-parameter model on a rooted 4-cycle has, at one parameter, the law of a resolved tree, with the same `T₀`. This is not a counterexample under the network multispecies coalescent, and `ECToBlob.theorem8_2` takes the parameters that it needs. -/
theorem ectoblob_not_theorem8_2_literal (o : ECToBlobOptions) :
    ¬ ∃ α β : ℕ → ℝ, ∀ {V E X : Type} [Fintype V] [Fintype E] [Fintype X] [DecidableEq X] (N : RootedNetwork V E X)
      (_ : N.IsPhylogenetic) (dist : MetricData E → BinaryGeneTree X → ℝ) (_ : ∀ θ, N.IsMetric θ → IsDist (dist θ))
      (_ : Assumption1 N fun θ => displayCF (dist θ) Subtype.val) (θ : MetricData E) (_ : N.IsMetric θ)
      (T₀ : Finset (Finset X)) (_ : IsResolutionOf T₀ (treeOfBlobs N))
      (_ : (o.testCo = .cauchy ∨ o.testCo = .cbc) →
        ∀ s, IsT1Strict (displayCF (dist θ) Subtype.val) s →
          ∀ r ∈ s.alternatives, 0 < displayCF (dist θ) Subtype.val r),
      Tendsto (fun n => iidProb (dist θ) n fun ω =>
        ectoblob o (α n) (β n) (quartetCount Subtype.val ω) T₀ = treeOfBlobs N) atTop (𝓝 1) :=
  Theorem82Literal.not_theorem8_2_literal o

end

/-! ## The sources that it cites -/

section

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

end

end TreeOfBlobs
