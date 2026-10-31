# Shared mathematical foundations

General definitions, representation bridges and helper lemmas. They do not count as proofs of the papers' numbered
results, and they depend on Mathlib only.

| Module | Content | Possible home |
| --- | --- | --- |
| `Analysis/FiniteOptimization` | Perturbations of finite optimization problems: stability of maximizers, with ties | Mathlib, order or analysis |
| `Analysis/AnalyticZeroSet` | The zero set of a nonzero real analytic function on a finite product of lines is null, also for measures with atoms at 0 | Mathlib, measure theory |
| `Analysis/MatrixExponential` | The entries of `exp (t • A)` are entire in `t` | Mathlib, analysis |
| `Analysis/SpecialFunctions/Erf` | The real error function: derivative, monotonicity, limits | Mathlib, special functions |
| `Analysis/SpecialFunctions/EntropyExcess` | Second-order expansion of `x log x`, with an explicit error | Mathlib, special functions |
| `Analysis/SpecialFunctions/GibbsInequality` | The maximum of a multinomial likelihood | Mathlib, information theory |
| `Combinatorics/DirectedMultigraph`, `MultigraphDegree`, `MultigraphConnectivity`, `MultigraphCutUniqueness`, `MultigraphBlobs`, `MultigraphTree`, `BridgeCutLaminar` | Directed multigraphs with named arcs; connectivity and bridges; quotient by bridge components; blobs, trees, the bridge to `SimpleGraph.IsTree` | Mathlib, multigraphs |
| `Phylogenetics/Defs` | **The shared definitions** of the statements, copied verbatim into `Challenge.lean` | This project |
| `Phylogenetics/Network`, `PendantCuts`, `AncestralRestriction`, `NetworkCuts` | Rooted networks; ancestral subgraph; cut edges through domination | A phylogenetics library |
| `Phylogenetics/DeletedArcs` | Reachability, domination and cut splits off a set of deleted arcs, for boundary parameters | A phylogenetics library |
| `Phylogenetics/InducedNetwork`, `TreeOfBlobs` | The induced network as an actual graph, by LSA and suppression; the tree of blobs as a graph; both agree with the split families of `Defs` | A phylogenetics library |
| `Phylogenetics/Hierarchy`, `HierarchyParents`, `HierarchyGraph`, `CutHierarchy` | Finite hierarchies, their graphs, and the hierarchy of a network's cuts | A phylogenetics library |
| `Phylogenetics/Quartet`, `TreeSplits`, `TreeSplice`, `TreeDetach`, `TreeMetric` | Quartet trees; unrooted trees as split families; splicing, detaching and reattaching; tree metrics | A phylogenetics library |
| `Phylogenetics/Coalescent/*` | Kingman's coalescent on forests: transition, absorption, Tavaré's formula, jump chain, binary forests, relabelling, lumpability. Adapted, see `docs/COALESCENT_SOURCES.md` | A phylogenetics library |
| `Phylogenetics/InducedMetric`, `Phylogenetics/NMSC/Induced*` | The parameters of an induced network; CFs don't change on passing to it; null sets carry back | A phylogenetics library |
| `Phylogenetics/NeighborJoining`, `FourPoint`, `AstralDP`, `DisplayedTreeModel` | Neighbor joining is exact on tree metrics, with a count; Buneman's four-point theorem; ASTRAL's dynamic program; the displayed tree model and the mixture at `ρ = 1` | A phylogenetics library |
| `Phylogenetics/NMSC/*` | The network multispecies coalescent on arbitrary networks, with correlated inheritance: a probability law on binary trees; Markov property at an arc; marginals; symmetry; exchangeability; analyticity in the parameters; bounds at boundary parameters; strict dominance at a fork | A phylogenetics library |
| `Probability/IID`, `Trinomial/Bridge` | Independent samples from a finite distribution, as finite sums and as product measures | Mathlib, probability |
| `Probability/GaussianPlane`, `GaussianTail` | Rotation invariance and strips of the standard Gaussian on the plane; `χ²` tails | Mathlib, probability |
| `Probability/Trinomial/CLT`, `Transfer`, `Statistics`, `Whiten`, `Gaussian`, `Tests` | Limits of the likelihood ratio statistics of a trinomial, from the central limit theorem | Partly Mathlib (`Transfer`) |
| `Probability/T3Test` | The T3 test: statistic, reference law, null and alternative | This project |
| `MeasureTheory/HaarPreimage` | Preimages of null sets under surjective linear maps on products of `Measure.pi` | Mathlib, measure theory |
| `Probability/QuartetTails`, `QuartetLimits` | Quartet hypothesis tests: tail bounds, growth under the alternative, limits under the null | This project |
