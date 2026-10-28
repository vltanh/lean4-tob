# Shared mathematical foundations

These modules contain general definitions, representation bridges and helper
lemmas. They do not count as proofs of the papers' numbered results.

| Area | Content | Possible upstream home |
| --- | --- | --- |
| `Analysis/FiniteOptimization` | Strict finite-sum error bounds and stability of maximizers, including tied true optima | Mathlib finite ordered sums and extrema |
| `Analysis/SpecialFunctions/Erf` | Integral definition of the real error function | Mathlib special functions |
| `Combinatorics/DirectedMultigraph` | Individually identified directed arcs, degrees, and a bridge to Mathlib multigraph cuts | Mathlib graph theory |
| `Combinatorics/MultigraphConnectivity` | Undirected walks with allowed arc sets; edge-deletion characterization of bridges | Mathlib graph connectivity |
| `Combinatorics/MultigraphBlobs` | Actual bridge-component quotient, connectedness, retained bridges, and preservation of labelled cuts | Mathlib graph contraction |
| `Phylogenetics/Network` | Rooted multigraph data and separate finite network/metric laws | A phylogenetics library; a new Mathlib area would first need discussion on Lean Zulip |
| `Phylogenetics/Quartet` | Unordered pair partitions, exactly three resolutions, and ordered-label bridges | A phylogenetics library |
| `Phylogenetics/ConcordanceFactor` | Resolved/star probability laws, normalized CFs and coordinate relabeling | A phylogenetics library |
| `Phylogenetics/AncestralRestriction` | Actual ancestral vertex/arc subtypes and exact adjacency/reachability bridges | A phylogenetics library |
| `Phylogenetics/Hierarchy` | Finite tree hierarchy laws, compatible split families and restrictions | Adapted from the public phylogenetics library; see [provenance](../docs/ADAPTED_SOURCES.md) |
| `Phylogenetics/Star` | Concrete finite rooted stars witnessing network validity | A phylogenetics library |

The graph model permits parallel arcs and nonbinary vertices. Forgetting
multiplicity for cuts would be unsound: two parallel arcs are not bridges.
Directed reachability may forget arc identity, while cuts and deletion retain it.

The current network validity convention excludes a root-only single-taxon graph:
labelled leaves have indegree one and the root has indegree zero. Any restriction
construction used for single taxa must handle that degenerate case explicitly.
The papers' quartet restrictions always have four distinct taxa.

The bridge-component quotient is constructed and its cut correspondence is
proved. Identification with maximal 2-edge-connected subgraphs and suppression
of degree-two vertices are still separate obligations. No reduced tree of blobs
is claimed merely from a data type bearing that name.
