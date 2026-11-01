module

public import Phylogenetics.Network.Quartets
public import Phylogenetics.NMSC.Defs
public import Basic.Testing.Combining
public import Basic.Testing.Defs
public import Phylogenetics.Tree.Metric

/-!
# Definitions specific to ECToBlob, TOB-QMC and TINNiK

What the statements of record of the three papers need, beyond the library `Phylogenetics`: the three
algorithms with their options and steps, and the papers' standing assumptions. Networks, trees, quartets,
the coalescent, the statistics and the p-values are the library's.

* ECToBlob: `QuartetType`, `SelectionRule`, `ECToBlobOptions`, the steps of Algorithm 7.1 from `edgeStarP`
  to `selectedIteration`, and `ectoblob`; `ECToBlob.Assumption1Forward`, `ECToBlob.Assumption1Converse`,
  `ECToBlob.BinaryGeneTree`, and the sequences `ECToBlob.alphaSeq`, `ECToBlob.betaSeq` of the proof of
  Theorem 8.2.
* TINNiK: `BInferred`, `IsMLSelection`, `testedB`, `testedT`, `tinnik`.
* Shared by the papers: `RootedNetwork.IsParentChoice`, `NoAnomalousQuartets`, `IsT1Null`.
* TOB-QMC: `TOBQMC.StandardAssumptions`, `TOBQMC.IsTQuartetNonanomalous`, `TOBQMC.IsDisjointCover`,
  `TOBQMC.tobqmc`.
-/

@[expose] public noncomputable section

open Finset MeasureTheory ProbabilityTheory
open scoped Classical

namespace Phylogenetics

section ECToBlobAlgorithm

variable {X : Type*} [Fintype X] [DecidableEq X]

/-- The quartet type of Algorithm 7.1. -/
inductive QuartetType
  | bi
  | mul
  | quad

/-- The selection rule of Algorithm 7.1. -/
inductive SelectionRule
  | early
  | late

/-- The options of a run of the algorithm: the quartet type, the correction method, the selection
rule, and the star test. -/
structure ECToBlobOptions where
  qType : QuartetType
  testCo : TestCorrection
  rule : SelectionRule
  starTest : StarTest

variable (o : ECToBlobOptions) (α β : ℝ) (c : QuartetTree X → ℝ) (T₀ : Finset (Finset X))

/-- Step 3: the combined star p-value of the edge with side `A` of `T₀`. -/
def edgeStarP (A : Finset X) : ℝ :=
  combineP o.testCo ((multipartitionQuartets T₀ A).val.map fun s => starPValue o.starTest c s.taxa)

/-- Step 3: contract the edges of `T₀` with `p_e^star > β`. -/
def afterStar : Finset (Finset X) :=
  contractSides T₀ ((internalSides T₀).filter fun A => β < edgeStarP o c T₀ A)

/-- Step 6: the quartet trees used to assess the edge with side `A` of the current tree `T`. For
`quad` they come from `T₀`. On a nonbinary `T₀`, whose edges may have no quadripartition, `quad` uses
the multipartition of `T₀` at `A`, which is the quadripartition when `T₀` is binary. -/
def edgeQuartets (T : Finset (Finset X)) (A : Finset X) : Finset (QuartetTree X) :=
  match o.qType with
  | .bi => bipartitionQuartets A
  | .mul => multipartitionQuartets T A
  | .quad => multipartitionQuartets T₀ A

/-- Step 6: the combined T1 p-value of the edge with side `A` of the current tree `T`. -/
def edgeT1P (T : Finset (Finset X)) (A : Finset X) : ℝ :=
  combineP o.testCo ((edgeQuartets o T₀ T A).val.map fun s => t1PValue c s)

/-- Steps 4 and 8: the combined T1 p-value of the tree `T`, over the quartet trees it displays. -/
def treeT1P (T : Finset (Finset X)) : ℝ :=
  combineP o.testCo ((univ.filter fun s => Displays T s).val.map fun s => t1PValue c s)

/-- Step 7: contract the internal edges of `T` with the minimal `p_e^T1`. -/
def contractStep (T : Finset (Finset X)) : Finset (Finset X) :=
  contractSides T ((internalSides T).filter fun A =>
    ∀ B ∈ internalSides T, edgeT1P o c T₀ T A ≤ edgeT1P o c T₀ T B)

/-- The sequence of trees of Algorithm 7.1, indexed from `0` (the paper's iteration `i = 1`). -/
def treeSeq (i : ℕ) : Finset (Finset X) :=
  (contractStep o c T₀)^[i] (afterStar o β c T₀)

/-- The last iteration: the first at which the tree has no internal edges. -/
def lastIteration : ℕ := sInf {i | internalSides (treeSeq o β c T₀ i) = ∅}

/-- Step 10: the selected iteration. The late rule selects the iteration after the last p-value below
`α`, and the first iteration if there is none (the implementation's convention, E9 of the report). -/
def selectedIteration : ℕ :=
  match o.rule with
  | .early => sInf {i | i ≤ lastIteration o β c T₀ ∧ α ≤ treeT1P o c (treeSeq o β c T₀ i)}
  | .late =>
      if ∃ i ≤ lastIteration o β c T₀, treeT1P o c (treeSeq o β c T₀ i) < α then
        sSup {i | i ≤ lastIteration o β c T₀ ∧ treeT1P o c (treeSeq o β c T₀ i) < α} + 1
      else 0

/-- The output of the ECToBlob algorithm on the quartet counts `c` and the starting tree `T₀`. -/
def ectoblob : Finset (Finset X) := treeSeq o β c T₀ (selectedIteration o α β c T₀)

end ECToBlobAlgorithm

section TINNiKAlgorithm

variable {X : Type*} [Fintype X] [DecidableEq X]

/-- The set of 4-taxon sets inferred as B-quartets by the B-quartet Inference Algorithm: the sets `B₀`
judged by the hypothesis tests, closed under Step 3's rule, given the quartet trees `τ` inferred in
Step 2c. The rule is stated with the labels of TINNiK Theorem 2. The worklist of the printed
algorithm computes this least closed family, since the rule is monotone. -/
inductive BInferred (B₀ : Set (Finset X)) (τ : Set (QuartetTree X)) : Finset X → Prop
  | base (q : Finset X) : q ∈ B₀ → BInferred B₀ τ q
  | ruleB (a b c d e : X) (t q : Finset X) :
      ({a, b, c, d, e} : Finset X).card = 5 →
      BInferred B₀ τ {a, b, c, d} → BInferred B₀ τ {b, c, d, e} →
      t ∈ ({{a, b, c, e}, {a, b, d, e}, {a, c, d, e}} : Finset (Finset X)) → BInferred B₀ τ t →
      q ∈ ({{a, b, c, e}, {a, b, d, e}, {a, c, d, e}} : Finset (Finset X)) →
      BInferred B₀ τ q
  | ruleT (a b c d e : X) (s : QuartetTree X) (q : Finset X) :
      ({a, b, c, d, e} : Finset X).card = 5 →
      BInferred B₀ τ {a, b, c, d} → BInferred B₀ τ {b, c, d, e} →
      s ∈ τ → s.taxa ∈ ({{a, b, c, e}, {a, b, d, e}, {a, c, d, e}} : Finset (Finset X)) →
      Separated s a e →
      q ∈ ({{a, b, c, e}, {a, b, d, e}, {a, c, d, e}} : Finset (Finset X)) →
      BInferred B₀ τ q

/-- A selection of maximum likelihood topologies: on each set of four taxa a quartet tree whose line
has the least statistic. The printed algorithm breaks ties at random; the results hold for every
selection. -/
def IsMLSelection (ml : (QuartetTree X → ℝ) → Finset X → QuartetTree X) : Prop :=
  ∀ c q, q.card = 4 → ml c q ∈ treesOn q ∧ ∀ r ∈ treesOn q, lineStat c (ml c q) ≤ lineStat c r

variable (ml : (QuartetTree X → ℝ) → Finset X → QuartetTree X)

/-- Step 2 of the B-quartet inference algorithm: the 4-taxon sets judged B-quartets. A set is judged
one when the star test fails to reject at level `β`, or when the cut test rejects at level `α`. -/
def testedB (α β : ℝ) (c : QuartetTree X → ℝ) : Set (Finset X) :=
  {q | q.card = 4 ∧ (β ≤ starPValue .lrt c q ∨ cutPValue c (ml c q) < α)}

/-- Step 2c: the maximum likelihood quartet trees of the other 4-taxon sets. -/
def testedT (α β : ℝ) (c : QuartetTree X → ℝ) : Set (QuartetTree X) :=
  {s | s.taxa ∉ testedB ml α β c ∧ s = ml c s.taxa}

/-- The output of the TINNiK algorithm on the quartet counts `c`, with cutoff `δ`: Steps 2 to 5. An edge
set to length zero is contracted, and so is one the method returned with length zero. -/
def tinnik (α β δ : ℝ) (M : TreeBuilder X) (c : QuartetTree X → ℝ) : Finset (Finset X) :=
  let B := {q | BInferred (testedB ml α β c) (testedT ml α β c) q}
  let built := M (quartetDistance B {s | s ∈ testedT ml α β c ∧ s.taxa ∉ B})
  built.1.filter fun A => A ∉ internalSides built.1 ∨ (δ ≤ built.2 A ∧ 0 < built.2 A)

end TINNiKAlgorithm

section NetworkConditions

variable {V E X : Type*}

/-- A choice of a parent arc at each reticulation. ECToBlob leaves it out of the coordinates of the inheritance
probabilities (`ECToBlob.IsNullParams`); TOB-QMC's display trees keep it (`TOBQMC.displayArcs`). -/
def RootedNetwork.IsParentChoice (N : RootedNetwork V E X) (d : V → E) : Prop :=
  ∀ v, 2 ≤ N.graph.indegree v → N.graph.target (d v) = v

variable [Fintype X] [DecidableEq X]

/-- **No anomalous quartets**: on every cut-edge split of an induced network, the quartet tree of the split has the strictly
largest concordance factor. This is ECToBlob §3, and TINNiK, "The T3 model and testing" (line 144), where a set of four taxa is
anomalous when its CF is `ab|cd` cut of the form `(p, q, q)` with `q ≥ 1/3`. It is also TOB-QMC's condition 6b, class 1
quartet-nonanomalous, "for every subset of four taxa whose relationship is treelike, the topology of the highest expected qCF
matches the TOB of the subnetwork".

Departure from ECToBlob: this reads "no anomalous quartets" strictly. The definition the paper cites (Definition 2 of
[8], Ané et al. 2024, `notes/sources/ane2024.txt`, lines 295-297) calls a network anomalous when `p_ab|cd < 1/3`, so its
absence is only `1/3 ≤ p_ab|cd`. That does not give the strict inequality of (5.2) at lines 403, 716 and 722: by Example 1
of [8] there are valid parameters with a cut edge and all three concordance factors `1/3`. This is forced, and the example
is worked out at `ECToBlob.remark3_3_nmsc` (`src/ECToBlob/Remark33.lean`). -/
def NoAnomalousQuartets (N : RootedNetwork V E X) (p : QuartetTree X → ℝ) : Prop :=
  ∀ s, InducedCutSplit N s → ∀ r ∈ s.alternatives, p r < p s

/-- The concordance factor `p` is on the null of the T1 test for the quartet tree `s`, as a closed half-line:
`p_s ≥ p_{s'} = p_{s''}` (Mitchell, Allman, Rhodes 2019, "Model T1"). When the three entries sum to one, this says
`p = (1 - 2q, q, q)` with `q ≤ 1/3` (`isT1Null_iff_le_third`). -/
def IsT1Null (p : QuartetTree X → ℝ) (s : QuartetTree X) : Prop :=
  (∀ r ∈ s.alternatives, p r ≤ p s) ∧ ∀ r ∈ s.alternatives, ∀ r' ∈ s.alternatives, p r = p r'

end NetworkConditions

end Phylogenetics

namespace ECToBlob

open Phylogenetics Phylogenetics.RootedNetwork

variable {V E X : Type*} [Fintype X] [DecidableEq X]

variable (N : RootedNetwork V E X)

/-- The two implications of Assumption 1 that hold for all parameters: a trivial 4-blob gives (5.1),
and a cut-edge split gives (5.2). -/
structure Assumption1Forward (p : QuartetTree X → ℝ) : Prop where
  star : ∀ q : Finset X, q.card = 4 → HasTrivialFourBlob N q → IsUniformOn p q
  t1 : ∀ s : QuartetTree X, InducedCutSplit N s → IsT1Strict p s

/-- The two converse implications of Assumption 1 at a given parameter: they hold for generic
parameters. -/
structure Assumption1Converse (p : QuartetTree X → ℝ) : Prop where
  star : ∀ q : Finset X, q.card = 4 → ¬ HasTrivialFourBlob N q → ¬ IsUniformOn p q
  t1 : ∀ s : QuartetTree X, ¬ InducedCutSplit N s → ¬ IsT1Strict p s

/-- Binary gene trees. -/
abbrev BinaryGeneTree (X : Type*) [Fintype X] [DecidableEq X] :=
  {T : Finset (Finset X) // IsBinaryTree T}

/-- The sequence `α_n` of the proof of Theorem 8.2: the upper tail of `χ²₁` at `log n`. -/
def alphaSeq (n : ℕ) : ℝ := chiSqOneTail (Real.log n)

/-- The sequence `β_n` of the proof of Theorem 8.2: the upper tail of `χ²₂` at `log n`, `1/√n`. -/
def betaSeq (n : ℕ) : ℝ := chiSqTwoTail (Real.log n)

end ECToBlob

namespace TOBQMC

open Phylogenetics Phylogenetics.RootedNetwork

variable {V E X : Type*} [Fintype X] [DecidableEq X]

/-- The standard assumptions of TOB-QMC §2.1 (conditions 1–3): a binary network, positive tree edge
lengths, nonnegative reticulation edge lengths, and inheritance proportions in `(0,1)` summing to
one at each reticulation; with the inheritance correlation in `[0,1]`. -/
structure StandardAssumptions [Fintype E] (N : RootedNetwork V E X) (θ : MetricData E) (ρ : ℝ) :
    Prop where
  phylogenetic : N.IsPhylogenetic
  binary : N.IsBinary
  metric : N.IsMetric θ
  rho : 0 ≤ ρ ∧ ρ ≤ 1

/-- `T-quartet-nonanomalous` (§4.1, after Definition 1, `tob2025:definition1`): on every 4-taxon set
that the tree of blobs resolves, the quartet tree it displays has the largest expected concordance
factor. -/
def IsTQuartetNonanomalous (N : RootedNetwork V E X) (F : QuartetTree X → ℝ) : Prop :=
  ∀ s, Displays (treeOfBlobs N) s → ∀ r ∈ s.alternatives, F r < F s

/-- **Definition 2** (`tob2025:definition2`). A *disjoint cover* around the edge with side `A` of the
tree `T`: four-taxon subsets each drawing one taxon from each block of the quadripartition induced by
the edge (of the multipartition, when `T` is not binary), whose union is all the taxa. -/
structure IsDisjointCover (T : Finset (Finset X)) (A : Finset X) (Q : Finset (Finset X)) : Prop where
  around : ∀ Y ∈ Q, ∃ s ∈ multipartitionQuartets T A, s.taxa = Y
  cover : ∀ x : X, ∃ Y ∈ Q, x ∈ Y

/-- The output of the method: from the tree `B`, contract the edges where the tests (of TINNiK's
algorithm, Step 2) judge a 4-taxon set of the disjoint cover `Q` to be non-treelike. -/
def tobqmc (ml : (QuartetTree X → ℝ) → Finset X → QuartetTree X) (α β : ℝ) (c : QuartetTree X → ℝ)
    (B : Finset (Finset X)) (Q : Finset X → Finset (Finset X)) : Finset (Finset X) :=
  contractSides B ((internalSides B).filter fun A => ∃ Y ∈ Q A, Y ∈ testedB ml α β c)

end TOBQMC
