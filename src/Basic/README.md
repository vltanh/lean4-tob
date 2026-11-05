# What the papers share, beyond the library

| Module | Content | Possible home |
| --- | --- | --- |
| `Defs` | **The definitions specific to the three papers**: the algorithms ECToBlob, TINNiK and TOB-QMC with their options and steps, and the papers' standing assumptions | This project |
| `Testing/*` | Hypothesis tests on quartet counts: statistics and p-values, combining p-values, independent samples, tails, limit laws through the trinomial central limit theorem | This project |
| `ForMathlib/*` | Analysis and probability that do not mention phylogenetics: zero sets of analytic functions, finite optimization, the error function, `x log x`, the multinomial likelihood, the Gaussian plane and its tails, transferring limit laws | Mathlib |
| `LocalObjective` | The local objective at a multifurcation of ECToBlob's Theorem 3.1: attaching subtrees, sums over representatives | This project |
| `RhoOne` | No anomalous quartets at `ρ = 1`: the strict form of Proposition 12 of Ané et al. 2024 | The library `Phylogenetics` |
| `LCA` | Lowest common ancestors: a sparse table with `O(1)` queries, and binary lifting, whose queries take `log` many jumps | The library `Phylogenetics` |
| `BridgeDFS` | Bridges and blobs by a search with low-points, in `\|V\| + 2 \|E\|` steps, and the tree of blobs as intervals of discovery times | The library `Phylogenetics` |
| `General` | Taxa that a parent choice leaves unresolved have concordance factors `1/3`, for all correlations; null sets of parameters are closed under subsets and countable unions (`IsGenericNull.mono`, `union`, `iUnion`) | The library `Phylogenetics` |
| `Level1Blobs` | Blobs of level-1 networks in the language of domination: bridges, the reticulation of a blob, walks that avoid a blob | The library `Phylogenetics` |
| `Wedge` | Wedge paths, the subnetwork on a set of taxa and its cut edges, the cycle of a blob of a binary level-1 network | The library `Phylogenetics` |
| `Level1Blocks` | Blocks at a blob, treelike sets of four taxa, and two of the three cases of TOB-QMC's Lemma 4, which NANUQ's Proposition 9 uses too | This project |
| `Level1CF` | At level 1, an induced cut-edge split that the tree of blobs does not display has the strictly largest concordance factor. TOB-QMC and NANUQ use it | This project |
| `InducedSplits` | Cut splits of induced networks in the language of domination, quartet trees as four taxa, and splits off a deletion | The library `Phylogenetics` |
| `FinNetwork` | Networks given by tables of arcs, checked by `decide`, and the binary network with a 4-cycle and a cut edge that the counterexamples of ECToBlob and TOB-QMC use | This project |
| `TreeCounts` | How many clusters a hierarchy has, and how many internal edges a binary tree has | The library `Phylogenetics` |
| `UnitMetric` | Valid parameters on any network: unit lengths, equal inheritance | The library `Phylogenetics` |
| `NMSCChain` | The chain of the network multispecies coalescent on a concrete network, from the root down, and the laws of a phylogenetic network from a rank function. ECToBlob's Remarks 3.3 and 5.2, NANUQ's counterexamples and the examples of Allman et al. 2023 use it | The library `Phylogenetics` |

Networks, trees, quartets, the coalescent and the theory of the network multispecies coalescent are in the library `Phylogenetics`.

`Basic` imports no paper ([`scripts/layers.toml`](../../scripts/layers.toml)). A declaration that moved here from a paper's folder, because another paper uses it, keeps its name, in the namespace of the paper that first needed it (`TOBQMC.Level1`, `ECToBlob.FalseEdge`, `TINNiK`).
