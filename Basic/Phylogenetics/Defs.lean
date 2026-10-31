/-
The definitions `IsHierarchy`, `childClusters`, `unroot`, `roots`, `kingmanGenerator`, `kingmanTransition`,
`kingmanAbsorption` and `forestBelow` are adapted from https://github.com/vltanh/lean4-phylogenetics,
commit 06f684e526e276ca2ccf668a1c3a808a2b8c181d.
Licensed under the Apache License, Version 2.0:
https://www.apache.org/licenses/LICENSE-2.0
Exact source regions: docs/COALESCENT_SOURCES.md and docs/ADAPTED_SOURCES.md.
-/
module

public import Mathlib.Analysis.Normed.Algebra.MatrixExponential
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Data.Set.Card
public import Mathlib.Logic.Relation
public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.Probability.Independence.Basic
public import Mathlib.Topology.Instances.Matrix

/-!
# Shared definitions of the tree-of-blobs formalization

Everything that a statement of record in `Challenge.lean` mentions is defined here, between the two
marker comments, importing only Mathlib. `scripts/sync_challenge_defs.py` copies the block word
for word into `Challenge.lean`, because Comparator needs the same constants in the Challenge and
in the Solution.

Conventions, for a reader checking the statements against the three papers.

* A rooted network is a finite directed multigraph with individually named arcs, a root and an
  injective labelling of its sinks. Parallel arcs and vertices of any degree are allowed; the
  papers' binary and level-1 conditions are separate predicates.
* An unrooted tree on the taxa is represented by the family of the sides of its splits, and is
  required to come from a rooted hierarchy. A resolution (refinement) of `T` is a family containing
  `T`; the tree of blobs is the family of nonempty proper cut-edge sides of the network.
  `Basic/Phylogenetics/` proves these representations correct for the actual graphs.
* A resolved quartet tree `ab|cd` is the unordered pair of its two cherries.
* The network multispecies coalescent is written as a product over vertices and arcs of the joint
  law of the forests at the bottom and the top of every arc, summed over all such histories, so
  that it mentions no processing order. It uses one lineage per taxon and includes the
  inheritance correlation `ρ`: `ρ = 0` is independent and `ρ = 1` common inheritance.

The sections of the block, in order: directed multigraphs; rooted phylogenetic networks; unrooted trees
as split families; the tree of blobs and the quartets of a network; Kingman's coalescent and the network
multispecies coalescent; sampling gene trees; hypothesis tests on quartet counts; combining p-values
(ECToBlob §6); the ECToBlob algorithm (Algorithm 7.1); the TINNiK algorithm; the statements' hypotheses.
-/

@[expose] public noncomputable section

open Finset MeasureTheory ProbabilityTheory
open scoped Classical

-- BEGIN SHARED DEFINITIONS

/-- A directed multigraph on given vertex and arc types. Every element of the arc type is an actual
arc; parallel arcs remain distinct. -/
structure DirectedMultigraph (V E : Type*) where
  source : E → V
  target : E → V

namespace DirectedMultigraph

variable {V E : Type*} (G : DirectedMultigraph V E)

/-- Directed adjacency. -/
def Adj (u v : V) : Prop := ∃ e, G.source e = u ∧ G.target e = v

/-- Directed reachability; the empty path is allowed. -/
def Reaches : V → V → Prop := Relation.ReflTransGen G.Adj

/-- No nonempty directed closed path. -/
def IsAcyclic : Prop := ∀ v, ¬ Relation.TransGen G.Adj v v

/-- The number of arcs entering a vertex, counting parallel arcs separately. -/
def indegree (v : V) : ℕ := {e | G.target e = v}.ncard

/-- The number of arcs leaving a vertex, counting parallel arcs separately. -/
def outdegree (v : V) : ℕ := {e | G.source e = v}.ncard

/-- An arc crosses a vertex bipartition, in either orientation. -/
def Crosses (e : E) (S : Set V) : Prop :=
  (G.source e ∈ S ∧ G.target e ∉ S) ∨ (G.target e ∈ S ∧ G.source e ∉ S)

end DirectedMultigraph

namespace Phylogenetics

/-- A rooted network on taxa `X`: graph, root and taxon labels. -/
structure RootedNetwork (V E X : Type*) where
  graph : DirectedMultigraph V E
  root : V
  leaf : X → V

namespace RootedNetwork

variable {V E X : Type*} (N : RootedNetwork V E X)

/-- The defining laws of a rooted phylogenetic network (ECToBlob §2, TOB-QMC §4.1, TINNiK
§"Phylogenetic networks"): a finite directed acyclic graph in which the root, of indegree zero,
reaches every vertex; sinks are exactly the taxon labels, bijectively, each of indegree one. Internal
vertices of any degree are allowed, including tree vertices of outdegree one. The root need not be the
LSA of the taxa, unlike ECToBlob's standing convention: what lies above the LSA affects no split with
taxa on both sides. -/
structure IsPhylogenetic : Prop where
  finite_vertices : Finite V
  finite_arcs : Finite E
  finite_taxa : Finite X
  acyclic : N.graph.IsAcyclic
  root_reaches : ∀ v, N.graph.Reaches N.root v
  root_indegree : N.graph.indegree N.root = 0
  nonroot_indegree : ∀ v, v ≠ N.root → 1 ≤ N.graph.indegree v
  leaf_injective : Function.Injective N.leaf
  leaf_indegree : ∀ x, N.graph.indegree (N.leaf x) = 1
  leaves : ∀ v, N.graph.outdegree v = 0 ↔ ∃ x, N.leaf x = v

/-- A tree arc enters a vertex with one incoming arc. -/
def IsTreeArc (e : E) : Prop := N.graph.indegree (N.graph.target e) = 1

/-- A hybrid (reticulation) arc enters a vertex with at least two incoming arcs. -/
def IsHybridArc (e : E) : Prop := 2 ≤ N.graph.indegree (N.graph.target e)

/-- Binary: the root has degree two and every other internal vertex has degree three. -/
def IsBinary : Prop :=
  N.graph.outdegree N.root = 2 ∧
    ∀ v, v ≠ N.root → N.graph.outdegree v ≠ 0 →
      N.graph.indegree v + N.graph.outdegree v = 3

/-- The numerical parameters of a network: edge lengths in coalescent units and inheritance
probabilities. Their ranges are the separate predicate `IsMetric`. -/
structure MetricData (E : Type*) where
  length : E → ℝ
  inheritance : E → ℝ

/-- Valid numerical parameters: tree edges have positive length, hybrid edges nonnegative length,
and the inheritance probabilities of the hybrid edges entering a vertex are positive and sum to one;
tree edges have inheritance one. -/
def IsMetric [Fintype E] (m : MetricData E) : Prop :=
  (∀ e, N.IsTreeArc e → 0 < m.length e) ∧
  (∀ e, N.IsHybridArc e → 0 ≤ m.length e) ∧
  (∀ e, N.IsTreeArc e → m.inheritance e = 1) ∧
  (∀ e, N.IsHybridArc e → 0 < m.inheritance e) ∧
  ∀ v, 2 ≤ N.graph.indegree v →
    ∑ e, (if N.graph.target e = v then m.inheritance e else 0) = 1

/-- `A` is the taxon side of a cut edge: some arc `e` is the only arc crossing a vertex set `S` whose
taxa are exactly `A`. Since the graph is connected, deleting `e` leaves exactly the two components
`S` and its complement, so this is the papers' cut-edge split `A|Aᶜ` (`hasCutSplit_compl`). -/
def HasCutSplit (A : Set X) : Prop :=
  ∃ (e : E) (S : Set V), (∀ f, N.graph.Crosses f S ↔ f = e) ∧ N.leaf ⁻¹' S = A

/-- The vertices ancestral to a taxon of `Y`. -/
def ancestralVertices (Y : Set X) : Set V :=
  {v | ∃ x ∈ Y, N.graph.Reaches v (N.leaf x)}

/-- The arcs ancestral to a taxon of `Y`. They and the vertices above form the induced subgraph on
`Y` of ECToBlob §2, which retains degree-two vertices and everything above the LSA of `Y`. -/
def ancestralArcs (Y : Set X) : Set E :=
  {e | N.graph.target e ∈ N.ancestralVertices Y}

/-- `A ∩ Y | Y \ A` is a cut-edge split of the network induced on `Y`: some arc of the induced
subgraph is the only arc of that subgraph crossing a vertex set meeting `Y` exactly in `A`. For a
split with two taxa on each side this is unchanged by removing what lies above the LSA of `Y` and by
suppressing degree-two vertices, so it is the cut-edge split of the induced 4-taxon network of the
papers (`Basic/Phylogenetics/InducedNetwork.lean`). -/
def HasCutSplitOn (Y A : Set X) : Prop :=
  ∃ e ∈ N.ancestralArcs Y, ∃ S : Set V,
    (∀ f ∈ N.ancestralArcs Y, N.graph.Crosses f S ↔ f = e) ∧ ∀ x ∈ Y, N.leaf x ∈ S ↔ x ∈ A

end RootedNetwork

section Trees

variable {X : Type*} [Fintype X] [DecidableEq X]

/-- A hierarchy of clusters on `X`: a rooted tree on `X` given by its clusters. -/
def IsHierarchy (H : Finset (Finset X)) : Prop :=
  univ ∈ H ∧ (∀ x : X, {x} ∈ H) ∧ (∀ A ∈ H, A.Nonempty) ∧
    ∀ A ∈ H, ∀ B ∈ H, A ⊆ B ∨ B ⊆ A ∨ Disjoint A B

/-- The children of a cluster `A` in a family `H` of clusters: the maximal members of `H`
strictly contained in `A`. -/
def childClusters (H : Finset (Finset X)) (A : Finset X) : Finset (Finset X) :=
  H.filter fun B => B ⊂ A ∧ ∀ C ∈ H, B ⊂ C → ¬ C ⊂ A

/-- The sides of the splits of the unrooted tree of a rooted tree `G`: its non-root clusters
and their complements. -/
def unroot {L : Type*} [Fintype L] [DecidableEq L] (G : Finset (Finset L)) : Finset (Finset L) :=
  G.erase univ ∪ (G.erase univ).image compl

/-- An unrooted phylogenetic tree on `X`, given by the sides of its splits (pendant edges
included). -/
def IsUnrootedTree (T : Finset (Finset X)) : Prop :=
  ∃ H : Finset (Finset X), IsHierarchy H ∧ unroot H = T

/-- A binary unrooted tree: it has a binary rooting, in which every cluster with at least two taxa
has exactly two children. -/
def IsBinaryTree (T : Finset (Finset X)) : Prop :=
  ∃ H : Finset (Finset X), IsHierarchy H ∧ unroot H = T ∧
    ∀ A ∈ H, 2 ≤ A.card → (childClusters H A).card = 2

/-- `T` is a resolution of `T'`: an unrooted tree from which `T'` is obtained by contracting edges,
that is, by removing splits. It may be nonbinary. -/
def IsResolutionOf (T T' : Finset (Finset X)) : Prop := IsUnrootedTree T ∧ T' ⊆ T

/-- A resolved quartet tree `ab|cd`: the unordered pair of its cherries `{a,b}`, `{c,d}`. -/
def IsQuartetTree (s : Finset (Finset X)) : Prop :=
  s.card = 2 ∧ (∀ B ∈ s, B.card = 2) ∧ ∀ B ∈ s, ∀ C ∈ s, B ≠ C → Disjoint B C

/-- The resolved quartet trees on `X`. -/
abbrev QuartetTree (X : Type*) [DecidableEq X] := {s : Finset (Finset X) // IsQuartetTree s}

instance : Fintype (QuartetTree X) := Fintype.ofFinite _

omit [Fintype X] in
/-- The four taxa of a quartet tree. -/
def QuartetTree.taxa (s : QuartetTree X) : Finset X := s.val.sup id

/-- The quartet trees on the same four taxa as `s`, other than `s`: the two alternatives. -/
def QuartetTree.alternatives (s : QuartetTree X) : Finset (QuartetTree X) :=
  univ.filter fun r => r.taxa = s.taxa ∧ r ≠ s

/-- The three resolved quartet trees on a set of four taxa. -/
def treesOn (q : Finset X) : Finset (QuartetTree X) := univ.filter fun r => r.taxa = q

/-- The tree (given by the sides of its splits) displays the quartet tree `ab|cd`: some split
restricts to `ab|cd`. An unresolved quartet on `T` is one with no displayed quartet tree. -/
def Displays (T : Finset (Finset X)) (s : QuartetTree X) : Prop := ∃ A ∈ T, A ∩ s.taxa ∈ s.val

/-- The Maximum Quartet Support objective: the sum, over the quartet trees that `T` displays, of the
weight `w`. -/
def quartetScore (w : QuartetTree X → ℝ) (T : Finset (Finset X)) : ℝ :=
  ∑ s, if Displays T s then w s else 0

/-- The family obtained from a tree `T` by contracting the edges with sides in `C`. -/
def contractSides (T C : Finset (Finset X)) : Finset (Finset X) := T.filter fun A => A ∉ C ∧ Aᶜ ∉ C

/-- The sides of the internal edges of `T`: both sides have at least two taxa. -/
def internalSides (T : Finset (Finset X)) : Finset (Finset X) :=
  T.filter fun A => 2 ≤ A.card ∧ 2 ≤ Aᶜ.card

/-- The quartet trees whose two cherries lie on the two sides of the edge with side `A`: the
4-taxon sets `Sbi(e)` of ECToBlob §4, each with the quartet tree that defines `e` on a tree. -/
def bipartitionQuartets (A : Finset X) : Finset (QuartetTree X) :=
  univ.filter fun s => A ∩ s.taxa ∈ s.val

/-- The quartet trees around the edge with side `A` of `T` drawing their taxa from distinct blocks
of the multipartition of `T` at that edge: `Smul(e)` of ECToBlob §4. Two taxa on one side are in one
block exactly when a split of `T` properly inside that side contains both. On a binary `T` these are
the quartets of the quadripartition, `Squad(e)`, and the disjoint-cover quartets of TOB-QMC
Definition 2. -/
def multipartitionQuartets (T : Finset (Finset X)) (A : Finset X) : Finset (QuartetTree X) :=
  (bipartitionQuartets A).filter fun s =>
    (¬ ∃ C ∈ T, C ⊂ A ∧ A ∩ s.taxa ⊆ C) ∧ (¬ ∃ C ∈ T, C ⊂ Aᶜ ∧ Aᶜ ∩ s.taxa ⊆ C)

end Trees

section NetworkQuartets

variable {V E X : Type*} [Fintype X] [DecidableEq X] (N : RootedNetwork V E X)

/-- The (reduced unrooted) tree of blobs `T_B(N)`, given by the sides of its splits: the nonempty
proper taxon sides of the cut edges of `N`. `Basic/Phylogenetics/TreeOfBlobs.lean` proves
that contracting the blobs of `N` and suppressing degree-two vertices gives a tree with exactly
these splits. -/
def treeOfBlobs : Finset (Finset X) :=
  univ.filter fun A => A.Nonempty ∧ Aᶜ.Nonempty ∧ N.HasCutSplit (A : Set X)

/-- The quartet tree `s = ab|cd` is a cut-edge split of the network induced on its four taxa. -/
def InducedCutSplit (s : QuartetTree X) : Prop :=
  ∃ B ∈ s.val, N.HasCutSplitOn (s.taxa : Set X) (B : Set X)

/-- The network induced on the taxa `q` has a nontrivial cut-edge split: it is *treelike* in the
sense of TOB-QMC §4.1 and has no 4-blob. Its negation is the oracle's "non-treelike". -/
def IsTreelike (q : Finset X) : Prop :=
  ∃ s ∈ treesOn q, InducedCutSplit N s

/-- The network induced on `q` has a trivial 4-blob, a multifurcation: there is a vertex `v` with,
for each taxon `x` of `q`, a cut edge of the induced subgraph at `v` separating exactly `x`
from `v`. (ECToBlob §5.1.) Chains of 2-blobs may lead to the taxa, but `v` itself lies on no cycle: a
vertex of a non-trivial blob is not a trivial 4-blob, as in ECToBlob §2. -/
def HasTrivialFourBlob (q : Finset X) : Prop :=
  ∃ v : V, ∀ x ∈ q, ∃ e ∈ N.ancestralArcs (q : Set X), ∃ S : Set V,
    (∀ f ∈ N.ancestralArcs (q : Set X), N.graph.Crosses f S ↔ f = e) ∧
    (∀ y ∈ q, N.leaf y ∈ S ↔ y = x) ∧ v ∉ S ∧ (N.graph.source e = v ∨ N.graph.target e = v)

/-- Condition 2 of ECToBlob Theorem 3.1, in the form in which its proof uses it (see
`ECToBlob.pendantChainInvariant_cutExchangeable` for the literal form): replacing a taxon `a` of a
quartet tree `s` by a taxon `a'` that a cut edge groups with it, away from the other three taxa, does
not change the weight. This is also the exchangeability of TOB-QMC's proof of Lemma 3. -/
def CutExchangeable (p : QuartetTree X → ℝ) : Prop :=
  ∀ (s s' : QuartetTree X) (a a' : X), a ∈ s.taxa → a' ∉ s.taxa →
    s'.val = s.val.image (fun B => if a ∈ B then insert a' (B.erase a) else B) →
    (∃ A : Finset X, N.HasCutSplit (A : Set X) ∧ a ∈ A ∧ a' ∈ A ∧ Disjoint A (s.taxa.erase a)) →
    p s = p s'

end NetworkQuartets

section Coalescent

variable {L : Type*} [Fintype L] [DecidableEq L]

/-- The roots of a forest `F` of gene lineages, given by its clusters: its maximal clusters. -/
def roots (F : Finset (Finset L)) : Finset (Finset L) :=
  F.filter fun A => ∀ B ∈ F, A ⊆ B → B = A

/-- The generator of Kingman's coalescent on forests. From a forest `F` with `k` roots, each of
the `k.choose 2` pairs of distinct roots `A, B` merges at rate `1`; the merge adds the cluster
`A ∪ B` to `F`. -/
def kingmanGenerator : Matrix (Finset (Finset L)) (Finset (Finset L)) ℝ :=
  fun F G =>
    if G = F then -((#(roots F)).choose 2 : ℝ)
    else if ∃ A ∈ roots F, ∃ B ∈ roots F, A ≠ B ∧ G = insert (A ∪ B) F then 1 else 0

/-- The transition probabilities of Kingman's coalescent on forests over a time `t`, in
coalescent units: the matrix exponential `exp (t • Q)` of the generator. -/
def kingmanTransition (t : ℝ) : Matrix (Finset (Finset L)) (Finset (Finset L)) ℝ :=
  NormedSpace.exp (t • kingmanGenerator)

/-- The transition probabilities of Kingman's coalescent on forests over an infinite time: the
entrywise limits of `kingmanTransition t` as `t → ∞`. -/
def kingmanAbsorption : Matrix (Finset (Finset L)) (Finset (Finset L)) ℝ :=
  fun F G => Filter.limUnder Filter.atTop fun t : ℝ => kingmanTransition t F G

/-- The part of the forest `F` below its roots in `A`: the clusters contained in a member of `A`. -/
def forestBelow (F A : Finset (Finset L)) : Finset (Finset L) :=
  F.filter fun B => ∃ C ∈ A, B ⊆ C

/-- The probability that the lineages `R` choose the parents `a` at a reticulation with inheritance
probabilities `γ` and inheritance correlation `ρ` (TOB-QMC supplement §1.2): the Pólya urn in which
the first lineage draws from `γ` and the lineage after `i` others takes a given parent with weight
`((1 - ρ) γ_e + ρ n_e) / ((1 - ρ) + ρ i)`, `n_e` being the number of earlier lineages that took it.
This closed form does not depend on the order of the lineages and holds at `ρ = 1` too; it is
`∏ γ_{a r}` at `ρ = 0`, and at `ρ = 1` it vanishes unless all lineages take one parent `e`, when it
is `γ_e` (`Basic/Phylogenetics/NMSC/Inheritance.lean`). -/
def allocationWeight {R P : Type*} [Fintype R] [Fintype P] [DecidableEq P] (ρ : ℝ) (γ : P → ℝ)
    (a : R → P) : ℝ :=
  (1 - ρ) ^ ((univ.image a).card - 1) *
    (∏ e ∈ univ.image a,
      (γ e * ∏ j ∈ Ico 1 (univ.filter fun r => a r = e).card, ((1 - ρ) * γ e + ρ * j))) /
    ∏ i ∈ Ico 1 (Fintype.card R), ((1 - ρ) + ρ * i)

end Coalescent

section NMSC

variable {V E X : Type*} [Fintype V] [Fintype E] [Fintype X] [DecidableEq X]
variable (N : RootedNetwork V E X) (θ : RootedNetwork.MetricData E) (ρ : ℝ)

/-- The forest arriving at the vertex `v` from below, given the forests `top e` at the top of its
child arcs: the singleton lineage of the taxon labelling `v`, if any, and those forests. -/
def arrivingForest (top : E → Finset (Finset X)) (v : V) : Finset (Finset X) :=
  ((univ.filter fun x => N.leaf x = v).image fun x => ({x} : Finset X)) ∪
    (univ.filter fun e => N.graph.source e = v).biUnion top

/-- The probability that the roots of the forest `F` arriving at `v` choose the parents that put the
forests `bot e` at the bottom of the arcs `e` entering `v`. -/
def allocationFactor (F : Finset (Finset X)) (v : V) (bot : E → Finset (Finset X)) : ℝ :=
  ∑ a : {A // A ∈ roots F} → {e // N.graph.target e = v},
    if ∀ e : {e // N.graph.target e = v},
        bot e.val = forestBelow F ((univ.filter fun r => a r = e).image Subtype.val) then
      allocationWeight ρ (fun e : {e // N.graph.target e = v} => θ.inheritance e.val) a
    else 0

/-- The joint probability of a history of the network multispecies coalescent: the forests `bot e`
at the bottom and `top e` at the top of every arc. Going up from the taxa, the roots of the forest
arriving at each non-root vertex choose parents, and along each arc the lineages coalesce by Kingman's
coalescent for the length of the arc, independently given the bottoms. -/
def historyWeight (bot top : E → Finset (Finset X)) : ℝ :=
  (∏ v ∈ univ.erase N.root, allocationFactor N θ ρ (arrivingForest N top v) v bot) *
    ∏ e, kingmanTransition (θ.length e) (bot e) (top e)

/-- The distribution of rooted gene trees on `X` (given by their clusters) under the network
multispecies coalescent with inheritance correlation `ρ`: the forest arriving at the root coalesces
in the population above the root, of infinite length. -/
def geneTreeDist (G : Finset (Finset X)) : ℝ :=
  ∑ bot : E → Finset (Finset X), ∑ top : E → Finset (Finset X),
    historyWeight N θ ρ bot top * kingmanAbsorption (arrivingForest N top N.root) G

/-- The quartet concordance factor of the quartet tree `s` under the network multispecies
coalescent: the probability that a gene tree displays `s`. -/
def nmscCF (s : QuartetTree X) : ℝ :=
  ∑ G : Finset (Finset X), if Displays (unroot G) s then geneTreeDist N θ ρ G else 0

end NMSC

section Sampling

variable {Γ : Type*} [Fintype Γ]

/-- The probability that `n` independent draws from the distribution `dist` on the finite set `Γ`
lie in the event `Ev`. -/
def iidProb (dist : Γ → ℝ) (n : ℕ) (Ev : (Fin n → Γ) → Prop) : ℝ :=
  ∑ ω : Fin n → Γ, if Ev ω then ∏ i, dist (ω i) else 0

variable {X : Type*} [Fintype X] [DecidableEq X]

/-- The number of the gene trees `ω`, each given by the sides of its splits through `sides`, that
display the quartet tree `s`. -/
def quartetCount {n : ℕ} (sides : Γ → Finset (Finset X)) (ω : Fin n → Γ) (s : QuartetTree X) : ℝ :=
  ((univ.filter fun i => Displays (sides (ω i)) s).card : ℝ)

end Sampling

section Tests

variable {X : Type*} [Fintype X] [DecidableEq X]

/-- The likelihood ratio statistic for the cut-model line of the quartet tree `s`: twice the difference
of the maximal trinomial log-likelihoods, unconstrained and on the line `p_{s'} = p_{s''}`, where
`s'`, `s''` are the alternatives of `s` (TINNiK Appendix C.1). `x log x` vanishes at `x = 0`. -/
def lineStat (c : QuartetTree X → ℝ) (s : QuartetTree X) : ℝ :=
  2 * (∑ r ∈ s.alternatives, c r * Real.log (c r) -
    (∑ r ∈ s.alternatives, c r) * Real.log (∑ r ∈ s.alternatives, c r) +
    (∑ r ∈ s.alternatives, c r) * Real.log 2)

/-- The likelihood ratio statistic of the star test on the taxa `q`: twice the difference
of the maximal trinomial log-likelihoods, unconstrained and at `(1/3, 1/3, 1/3)`. -/
def starStat (c : QuartetTree X → ℝ) (q : Finset X) : ℝ :=
  2 * (∑ r ∈ treesOn q, c r * Real.log (c r) -
    (∑ r ∈ treesOn q, c r) * Real.log ((∑ r ∈ treesOn q, c r) / 3))

/-- Pearson's chi-square statistic of the star test on the taxa `q`, the alternative that ECToBlob
§5.2 allows. -/
def pearsonStat (c : QuartetTree X → ℝ) (q : Finset X) : ℝ :=
  ∑ r ∈ treesOn q, (c r - (∑ t ∈ treesOn q, c t) / 3) ^ 2 / ((∑ t ∈ treesOn q, c t) / 3)

/-- The likelihood ratio statistic of the T1 test (Mitchell, Allman, Rhodes 2019, "Model T1"; ECToBlob
§5.2) with null hypothesis `p_s ≥ p_{s'} = p_{s''}`: the maximum on this null is on the line of `s` when the
data have `c s` at least the mean of the alternatives, and otherwise at the centroid. -/
def t1Stat (c : QuartetTree X → ℝ) (s : QuartetTree X) : ℝ :=
  if (∑ r ∈ s.alternatives, c r) / 2 ≤ c s then lineStat c s else starStat c s.taxa

/-- The parameter `μ₀` of the test distributions, `√(2n) (1 - φ) / √(φ (3 - 2φ))`, for the point
`(1 - 2φ/3, φ/3, φ/3)` and sample size `n`. -/
def muZero (φ n : ℝ) : ℝ := Real.sqrt (2 * n) * (1 - φ) / Real.sqrt (φ * (3 - 2 * φ))

/-- The upper tail at `t` of the T1 test distribution of Mitchell, Allman, Rhodes 2019 ("Application to
Model T1"): that of `Z² + ½ (1 - sgn Z̄) Z̄²` for independent `Z ~ N(0,1)` and `Z̄ ~ N(μ,1)`. -/
def t1Tail (μ t : ℝ) : ℝ :=
  ((gaussianReal 0 1).prod (gaussianReal μ 1)).real
    {z | t < z.1 ^ 2 + if z.2 < 0 then z.2 ^ 2 else 0}

/-- The maximum likelihood estimate of `φ` on the T1 null. -/
def t1Phi (c : QuartetTree X → ℝ) (s : QuartetTree X) : ℝ :=
  min 1 (3 * (∑ r ∈ s.alternatives, c r) / (2 * (c s + ∑ r ∈ s.alternatives, c r)))

/-- The p-value of the T1 test, with the estimated `φ` in the test distribution, as in Mitchell, Allman,
Rhodes 2019. The separate procedures of those papers and of MSCquartets for small counts are not modelled:
they do not arise in the limit, when the concordance factors are positive. -/
def t1PValue (c : QuartetTree X → ℝ) (s : QuartetTree X) : ℝ :=
  t1Tail (muZero (t1Phi c s) (c s + ∑ r ∈ s.alternatives, c r)) (t1Stat c s)

/-- The upper tail at `t` of the `χ²` distribution with 2 degrees of freedom. -/
def chiSqTwoTail (t : ℝ) : ℝ := Real.exp (-t / 2)

/-- The star test used: likelihood ratio (the default) or Pearson. -/
inductive StarTest
  | lrt
  | pearson

/-- The p-value of the star test on the taxa `q`, against the `χ²₂` distribution. -/
def starPValue (k : StarTest) (c : QuartetTree X → ℝ) (q : Finset X) : ℝ :=
  match k with
  | .lrt => chiSqTwoTail (starStat c q)
  | .pearson => chiSqTwoTail (pearsonStat c q)

end Tests

section Combining

/-- The Cauchy transform `f(p) = tan(π(1/2 - p))`. -/
def cauchyTransform (p : ℝ) : ℝ := Real.tan (Real.pi * (1 / 2 - p))

/-- The inverse of the Cauchy transform on `(0, 1)`. -/
def cauchyInverse (y : ℝ) : ℝ := 1 / 2 - Real.arctan y / Real.pi

/-- The minimum of a multiset of p-values, with the value `1` for the empty multiset. -/
def minP (P : Multiset ℝ) : ℝ := P.fold min 1

/-- `Bon(P) = min(1, k min(P))`. -/
def bonP (P : Multiset ℝ) : ℝ := min 1 ((Multiset.card P : ℝ) * minP P)

/-- The Cauchy combination `f⁻¹(mean f(pᵢ))`. The transform has infinite values at `0` and `1`,
and the mean is extended continuously: a p-value `0` gives `0`, and otherwise a p-value `1` gives `1`.
(No continuous extension exists at multisets with both `0` and `1`, which the algorithm's
analysis never reaches; the implementation also gives `0` there.) -/
def cauchyP (P : Multiset ℝ) : ℝ :=
  if (0 : ℝ) ∈ P then 0 else if (1 : ℝ) ∈ P then 1 else
    cauchyInverse ((P.map cauchyTransform).sum / (Multiset.card P : ℝ))

/-- `BBC(P) = Bon({Bon(P), Cauchy(P)})`. -/
def bbcP (P : Multiset ℝ) : ℝ := bonP {bonP P, cauchyP P}

/-- `CBC(P) = Cauchy({Bon(P), Cauchy(P)})`. -/
def cbcP (P : Multiset ℝ) : ℝ := cauchyP {bonP P, cauchyP P}

/-- The multiple-test correction methods of ECToBlob §6. -/
inductive TestCorrection
  | bon
  | cauchy
  | bbc
  | cbc

/-- Combining p-values by a correction method. An empty multiset of p-values, with no null hypothesis
to test, gets the value `1`, as Algorithm 7.1's Step 4 does for a star tree. -/
def combineP (m : TestCorrection) (P : Multiset ℝ) : ℝ :=
  if P = 0 then 1 else
  match m with
  | .bon => bonP P
  | .cauchy => cauchyP P
  | .bbc => bbcP P
  | .cbc => cbcP P

end Combining

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

/-- Taxa `a`, `e` are separated in the quartet tree `s`: they lie in different cherries. -/
def Separated (s : QuartetTree X) (a e : X) : Prop :=
  a ∈ s.taxa ∧ e ∈ s.taxa ∧ ∀ B ∈ s.val, ¬ (a ∈ B ∧ e ∈ B)

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

/-- The cut-model likelihood ratio statistic on the taxa `q`: the least of the statistics of its
three lines. -/
def cutStat (c : QuartetTree X → ℝ) (q : Finset X) : ℝ := ⨅ s : {s // s ∈ treesOn q}, lineStat c s.val

/-- The angle `α₀` of TINNiK Appendix C.2. -/
def alphaZero (φ : ℝ) : ℝ := Real.arctan (1 / Real.sqrt (3 * (3 - 2 * φ)))

/-- The upper tail at `t` of the distribution of TINNiK Proposition 5 for `φ` and sample size `n`:
that of `min(Z², (sin α₀ Z + cos α₀ Z̄)², (sin α₀ Z - cos α₀ Z̄)²)` for independent `Z ~ N(0,1)`
and `Z̄ ~ N(μ₀,1)`. -/
def cutTail (φ n t : ℝ) : ℝ :=
  ((gaussianReal 0 1).prod (gaussianReal (muZero φ n) 1)).real
    {z | t < min (z.1 ^ 2) (min ((Real.sin (alphaZero φ) * z.1 + Real.cos (alphaZero φ) * z.2) ^ 2)
      ((Real.sin (alphaZero φ) * z.1 - Real.cos (alphaZero φ) * z.2) ^ 2))}

/-- The p-value of the cut test, with `φ` estimated on the cut-model line of the quartet tree `s`, a
maximum likelihood topology: TINNiK Appendix C.2. At the edges `φ̂ = 0` or `3/2`, excluded in the paper's
`φ₀ ∈ (0, 3/2)`, division by zero gives arbitrary values; TINNiK uses other procedures for small counts,
and these counts have vanishing probability when the concordance factors are positive. -/
def cutPValue (c : QuartetTree X → ℝ) (s : QuartetTree X) : ℝ :=
  cutTail (3 * (∑ r ∈ s.alternatives, c r) / (2 * (c s + ∑ r ∈ s.alternatives, c r)))
    (c s + ∑ r ∈ s.alternatives, c r) (cutStat c s.taxa)

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

/-- The quartet intertaxon distance of Rhodes 2020 Theorem 2, from a family `Bq` of unresolved 4-taxon
sets and a family `τ` of resolved quartet trees: for `x ≠ y`, `2 |Q_{x,y}| + 2N - 4` where `Q_{x,y}`
holds the unresolved sets containing `x, y` and the quartet trees separating `x, y`. -/
def quartetDistance (Bq : Set (Finset X)) (τ : Set (QuartetTree X)) (x y : X) : ℝ :=
  if x = y then 0 else
    2 * (((univ.filter fun q : Finset X =>
        q.card = 4 ∧ x ∈ q ∧ y ∈ q ∧ (q ∈ Bq ∨ ∃ s ∈ τ, s.taxa = q ∧ Separated s x y)).card : ℕ) : ℝ) +
      2 * (Fintype.card X : ℝ) - 4

/-- The tree metric of the tree with sides `T` and edge weights `w`: the total weight of the splits
separating two taxa. -/
def treeMetric (T : Finset (Finset X)) (w : Finset X → ℝ) (x y : X) : ℝ :=
  ∑ A ∈ T.filter (fun A => x ∈ A ∧ y ∉ A), w A

/-- A distance-based tree building method (NJ, FastME, …), returning sides of splits and
edge weights. -/
abbrev TreeBuilder (X : Type*) := (X → X → ℝ) → Finset (Finset X) × (Finset X → ℝ)

/-- The method recovers the tree from an exact tree metric, whose edge weights are positive and agree
on the two sides of an edge: it returns a tree resolving it with the same weights, and any further
edges have weight at most zero. This is what TINNiK §"Statistical consistency" uses of NJ, which on the
metric of a tree with a polytomy returns a binary tree with edges of length zero. -/
def IsExactBuilder (M : TreeBuilder X) : Prop :=
  ∀ (T : Finset (Finset X)) (w : Finset X → ℝ), IsUnrootedTree T →
    (∀ A ∈ T, 0 < w A ∧ w Aᶜ = w A) →
    IsUnrootedTree (M (treeMetric T w)).1 ∧ T ⊆ (M (treeMetric T w)).1 ∧
      (∀ A ∈ T, (M (treeMetric T w)).2 A = w A) ∧
      ∀ A ∈ (M (treeMetric T w)).1, A ∉ T → (M (treeMetric T w)).2 A ≤ 0

/-- The output of the TINNiK algorithm on the quartet counts `c`, with cutoff `δ`: Steps 2 to 5. An edge
set to length zero is contracted, and so is one the method returned with length zero. -/
def tinnik (α β δ : ℝ) (M : TreeBuilder X) (c : QuartetTree X → ℝ) : Finset (Finset X) :=
  let B := {q | BInferred (testedB ml α β c) (testedT ml α β c) q}
  let built := M (quartetDistance B {s | s ∈ testedT ml α β c ∧ s.taxa ∉ B})
  built.1.filter fun A => A ∉ internalSides built.1 ∨ (δ ≤ built.2 A ∧ 0 < built.2 A)

end TINNiKAlgorithm

section ECToBlobStatements

variable {V E X : Type*} [Fintype X] [DecidableEq X]

/-- The probability that a gene tree displays the quartet tree `s`, for a distribution `dist` on gene
trees given by the sides of their splits through `sides`. -/
def displayCF {Γ : Type*} [Fintype Γ] (dist : Γ → ℝ) (sides : Γ → Finset (Finset X))
    (s : QuartetTree X) : ℝ :=
  ∑ g, if Displays (sides g) s then dist g else 0

end ECToBlobStatements

end Phylogenetics

namespace ECToBlob

open Phylogenetics Phylogenetics.RootedNetwork

variable {V E X : Type*} [Fintype X] [DecidableEq X]

/-- Equation (5.1) (`ecto:eq5_1`) on the taxa `q`: all three concordance factors are `1/3`. -/
def IsUniformOn (p : QuartetTree X → ℝ) (q : Finset X) : Prop := ∀ r ∈ treesOn q, p r = 1 / 3

/-- Equation (5.2) (`ecto:eq5_2`) for the quartet tree `s = ab|cd`:
`p_ab|cd > p_ac|bd = p_ad|bc`. -/
def IsT1Strict (p : QuartetTree X → ℝ) (s : QuartetTree X) : Prop :=
  (∀ r ∈ s.alternatives, p r < p s) ∧ ∀ r ∈ s.alternatives, ∀ r' ∈ s.alternatives, p r = p r'

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

/-- The number of the first `k` gene trees of the sequence `G` that display `s`. -/
def geneCount {Ω : Type*} (G : ℕ → Ω → Finset (Finset X)) (k : ℕ) (ω : Ω) (s : QuartetTree X) : ℝ :=
  ((Finset.range k).filter fun i => Displays (unroot (G i ω)) s).card

/-- A sequence of independent gene trees, each from the network multispecies coalescent. -/
structure IsGeneTreeSample {Ω : Type*} [MeasurableSpace Ω] [Fintype V] [Fintype E]
    (P : Measure Ω) (N : RootedNetwork V E X) (θ : MetricData E) (ρ : ℝ)
    (G : ℕ → Ω → Finset (Finset X)) : Prop where
  measurable : ∀ i g, MeasurableSet (G i ⁻¹' {g})
  indep : ∀ (s : Finset ℕ) (g : ℕ → Finset (Finset X)),
    P (⋂ i ∈ s, G i ⁻¹' {g i}) = ∏ i ∈ s, P (G i ⁻¹' {g i})
  law : ∀ i g, P.real (G i ⁻¹' {g}) = geneTreeDist N θ ρ g

/-- An arc is a bridge: a cut edge of the network. -/
def IsBridge (N : RootedNetwork V E X) (e : E) : Prop := ∃ S : Set V, ∀ f, N.graph.Crosses f S ↔ f = e

/-- Vertices in the same blob: joined by a walk of arcs that are not bridges. -/
def SameBlob (N : RootedNetwork V E X) : V → V → Prop :=
  Relation.ReflTransGen fun u v => ∃ e, ¬ IsBridge N e ∧
    ((N.graph.source e = u ∧ N.graph.target e = v) ∨ (N.graph.source e = v ∧ N.graph.target e = u))

/-- A blob's level: its reticulation edges minus its reticulation vertices. The network is level-1 if
every blob has level at most one (§4.1). -/
def IsLevelOne [Fintype V] [Fintype E] (N : RootedNetwork V E X) : Prop :=
  ∀ v : V,
    ((univ.filter fun e => N.IsHybridArc e ∧ SameBlob N v (N.graph.source e) ∧
        SameBlob N v (N.graph.target e)).card : ℤ) -
      ((univ.filter fun u => 2 ≤ N.graph.indegree u ∧ SameBlob N v u).card : ℤ) ≤ 1

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

/-- An optimal solution of Weighted Quartet Consensus for the counts `c`. -/
def IsWQCOptimal (c : QuartetTree X → ℝ) (B : Finset (Finset X)) : Prop :=
  IsBinaryTree B ∧ ∀ T, IsBinaryTree T → quartetScore c T ≤ quartetScore c B

end TOBQMC

namespace External.AllmanEtAl2023

open Phylogenetics Phylogenetics.RootedNetwork MeasureTheory

variable {V E X : Type*} [Fintype X] [DecidableEq X]

/-- `CF` is strictly `s`-cut (Definition 15): the alternatives of `s` are equal, and differ from `s`. -/
def IsStrictlyCut (p : QuartetTree X → ℝ) (s : QuartetTree X) : Prop :=
  (∀ r ∈ s.alternatives, p r ≠ p s) ∧ ∀ r ∈ s.alternatives, ∀ r' ∈ s.alternatives, p r = p r'

/-- `CF` on the taxa `q` is non-cut (Definition 15): its three entries are distinct. -/
def IsNonCut (p : QuartetTree X → ℝ) (q : Finset X) : Prop :=
  ∀ r ∈ treesOn q, ∀ r' ∈ treesOn q, r ≠ r' → p r ≠ p r'

/-- CF-detectability of the induced 4-taxon networks at given concordance factors: a cut-edge split
of the induced network gives a strictly cut CF, and an induced network without one (with a 4-blob)
gives a non-cut CF. -/
structure CFDetectable (N : RootedNetwork V E X) (p : QuartetTree X → ℝ) : Prop where
  cut : ∀ s : QuartetTree X, InducedCutSplit N s → IsStrictlyCut p s
  blob : ∀ q : Finset X, q.card = 4 → ¬ IsTreelike N q → IsNonCut p q

variable [Fintype V] [Fintype E]

/-- A set of numerical parameters of a binary network is null: in the coordinates given by all edge
lengths and, at each hybrid vertex, the inheritance probability of all but one parent, for Lebesgue
measure. -/
def IsGenericNull (N : RootedNetwork V E X) (A : Set (MetricData E)) : Prop :=
  ∀ d : V → E, (∀ v, 2 ≤ N.graph.indegree v → N.graph.target (d v) = v) →
    ((Measure.pi fun _ : E => (volume : Measure ℝ)).prod (Measure.pi fun _ : E => (volume : Measure ℝ)))
      {x | ∃ θ ∈ A, N.IsMetric θ ∧ θ.length = x.1 ∧
        ∀ e, N.IsHybridArc e → e ≠ d (N.graph.target e) → θ.inheritance e = x.2 e} = 0

/-- **Assumed result: Corollary 1 of the source**, from its Theorem 1 (TINNiK Theorem 1). For a rooted
binary phylogenetic network, the numerical parameters at which the NMSC with independent inheritance
fails CF-detectability on some induced 4-taxon network form a null set. -/
def Corollary1 (N : RootedNetwork V E X) : Prop :=
  IsGenericNull N {θ | N.IsMetric θ ∧ ¬ CFDetectable N (nmscCF N θ 0)}

end External.AllmanEtAl2023

-- END SHARED DEFINITIONS

/-! The definitions below are used in the library, and in no statement of the Challenge. -/

namespace Phylogenetics

/-- The taxa `q` form a B-quartet of the network (TINNiK Definition 4): the tree of blobs does not
resolve them. -/
def IsBQuartet {V E X : Type*} [Fintype X] [DecidableEq X] (N : RootedNetwork V E X)
    (q : Finset X) : Prop := ∀ s ∈ treesOn q, ¬ Displays (treeOfBlobs N) s

/-- The upper tail at `t` of the `χ²` distribution with 1 degree of freedom. -/
def chiSqOneTail (t : ℝ) : ℝ := (gaussianReal 0 1).real {z | t < z ^ 2}

/-- The maximum of a multiset of p-values, with the value `0` for the empty multiset. -/
def maxP (P : Multiset ℝ) : ℝ := P.fold max 0

end Phylogenetics

namespace ECToBlob

open Phylogenetics

/-- The sequence `α_n` of the proof of Theorem 8.2: the upper tail of `χ²₁` at `log n`. -/
def alphaSeq (n : ℕ) : ℝ := chiSqOneTail (Real.log n)

/-- The sequence `β_n` of the proof of Theorem 8.2: the upper tail of `χ²₂` at `log n`, `1/√n`. -/
def betaSeq (n : ℕ) : ℝ := chiSqTwoTail (Real.log n)

end ECToBlob
