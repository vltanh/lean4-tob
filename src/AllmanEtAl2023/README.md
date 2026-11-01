# Allman, Baños, Mitchell, Rhodes 2023: identifiability of the tree of blobs

Source: E. S. Allman, H. Baños, J. D. Mitchell, J. A. Rhodes, *The tree of blobs of a species network:
identifiability under the coalescent*, J. Math. Biol. 86 (2023), 10,
<https://doi.org/10.1007/s00285-022-01838-9>. Read in the PMC author manuscript NIHMS1884071 (PMC10062380) and the arXiv TeX. The journal's text wasn't
reachable, so "the PMC manuscript" is what is meant below and in the docstrings.

"Line 149" and "the PMC text, line 149" in the docstrings mean line 149 of the plain text of the PMC page, one line per paragraph. The labels `a:thm:…`, `a:lem:…`, `a:cor:…`, `a:prop:…`, `a:def::…` are those of the arXiv TeX; the routes of the proofs are in `docs/paper_routes.tsv`, and their differences from the paper's in `docs/route_differences.tsv`.

All names are in the namespace `AllmanEtAl2023`. No module here imports `ECToBlob`, `TOBQMC` or `TINNiK`. The bridge from the outline of an algorithm in Section 5 to the later paper is `TINNiK.AllmanOutline`, in `src/TINNiK/`. There is no `sorry`.

## Results

| Result of the paper | Lean | Module | Proof |
| --- | --- | --- | --- |
| Lemma 1 | `lemma1` | `Lemma1`, `TrdFour` | the paper omits the proof; ours, by the count of the degrees of `T(𝒩⁻)` |
| Theorem 1 | `theorem1`, with `theorem1_a`, `theorem1_b`, `theorem1_cut` | `Theorem1`, `Theorem1a`, `Theorem1b` | the paper's: statement (a) on the edge of the rooted form, (b) by induction, with the 2-blob step, Lemma 1, the deleted networks and the mixture |
| Corollary 1 | `corollary1` | `Corollary1` | the paper's: Theorem 1 on each induced network, `isGenericNull_inducedParams`, `nmscCF_induced` |
| Proposition 1 | `proposition1`, `proposition1_converse` | `Proposition1`, `GenericDense`, `NetworkNk`, `NetworkNkGraph`, `NetworkNkCF`, `NetworkNkSpecies`, `NetworkNkMixture`, `KernelBounds` | the paper's: `α` exact, `CF = α CF₁ + (1 - α) CF₂`, `CF₁` from the two species trees |
| Lemma 2 | `lemma2` | `Lemma2`, from `determines_of_subnetwork` in `SubgraphBlobs` | the paper's. `M` is connected, and the labels are distinct on nodes of degree 1: what the proof and its uses need (`lemma2_needs_connected`, in `Lemma2Counterexample`) |
| Corollary 2 | `corollary2` | `Corollary2`, `BlobsPass` | the paper's: blobs pass to blobs and cut edges to cut edges, then Lemma 2 |
| Theorem 2 | `theorem2` | `Theorem2`, from `rule_core` in `Basic` | the paper's |
| Lemma 3 | `lemma3` | `Lemma3`, from `lemma3_blob` in `CycleLemma` | the paper's cycle; its gaps are listed at the head of `CycleLemma` and `Lemma3` |
| Theorem 3 | `theorem3`, `theorem3_core` | `Theorem3` | the paper's induction, on networks |
| Theorem 4 | `theorem4`, `theorem4_treeFromCF`, `theorem4_two_networks`, `theorem4_iso` | `Theorem4` | the paper's: the quartets displayed, then "the collection of displayed quartets determine the tree" |
| Definitions 1 to 15 | see the docstrings, each with its label | `Definitions`, `InducedNetwork`, `BlobDefinitions`, `Concordance` | |

## Modules

| Modules | Content |
| --- | --- |
| `Definitions`, `InducedNetwork`, `BlobDefinitions`, `Concordance`, `NetworkNk` | the paper's definitions, on its objects |
| `SubgraphBlobs`, `CutOrder`, `CycleLemma`, `Reduction`, `Basic` | the subgraph language: blobs of a set of arcs of a fixed network, cuts by domination. Lemma 2, the cycle of Lemma 3 and the rule live here, and the later papers use them |
| `Bridges`, `InducedTransfer`, `BlobsPass` | from the paper's objects to that language; blobs and cut-edge splits through the steps of Definition 6 |
| `TreeSuppression`, `TrdTree`, `TreeIso`, `TrdFour` | suppressing nodes of degree 2 of a tree; `T_rd` on four taxa; a bridge to `SempleSteel2003.xTree_unique` for labelled graphs (`LabelledGraph.isIso_of_splits_eq`) |
| `InducedCF`, `SuppressStem`, `ClaimsTheorem1`, `KernelBounds`, `Theorem1a` | `CF`s through Definition 6; statement (a) of the proof of Theorem 1, and the bounds it uses. `SuppressStem` is what induced, deleted and contracted networks share |
| `DeletedNetwork`, `ContractBlob`, `Theorem1b`, `GenericCF`, `GenericParams`, `GenericDense` | statement (b): the networks `𝒩ᵢ⁺`, the 2-blob step, the choice of parameters; generic parameters exist and are dense |
| `Theorem1`, `Corollary1`, `Lemma1`, `Proposition1`, `Lemma2`, `Lemma2Counterexample`, `Corollary2`, `Theorem2`, `Lemma3`, `Theorem3`, `Theorem4`, `Claims` | the numbered results, and the claims their proofs use |
| `InPassing`, `BlobDistance`, `NetworkNkExact`, `NetworkOne`, `TwoBlobs`, `BlobStructure`, `LSABlob`, `TreeBlobs`, `CycleFamily`, `CFGeometry`, `FourCycle`, `TrivialEdges`, `Figures`, `Figure1`, `Figure2`, `FigureCheck` | what the paper says in passing, below. `FigureCheck` checks claims about a numbered network by computation, in the kernel, and `Figure1` adds certificates for a large one. `NetworkNkExact` is the first entry of `CF_abcd` on `𝒩(k)⁺`, exactly, and `NetworkOne` the same on `𝒩(1)⁺` for all parameters |
| `Algorithm` | the outline of an algorithm in Section 5: its steps, its consistency for a test right on four taxa, and the estimate of edge lengths it cites. The bridge to TINNiK is `TINNiK.AllmanOutline` |
| `CFDetectable` | for the later papers: `cfDetectable_generic`, `isGenericNull_not_isNonCut` on `CFDetectable`. TINNiK's Theorem 1 is `cfDetectable_generic` |

For the later papers, besides `CFDetectable`: `closure_complete`, `closure_sound` (`Basic`), the closure at any degree, which `ECToBlob.remark83_tinnik` needs; `exists_reduction_aux`, `exists_reduction`, `exists_reduction_of_blobDegree` (`Reduction`), which ECToBlob's Section 5, TOB-QMC's Lemma 1 and `InPassing.isTreelike_iff_forall_displays` use, on non-binary networks too. `Basic.NMSCChain`, outside this directory, has the chain of the NMSC on a concrete network, which `FourCycle` and `TrivialEdges` use.

## Departures that remain

The proofs of the numbered results follow the paper, apart from these.

* **Statement (a) of Theorem 1.** The paper's cases of the rooted forms have two arguments; in Lean they are one. The rooted form selects the edge `f` and locates its source (`exists_edge_of_rootedForm`), and `nmscCF_alternatives_at` doesn't use the location. See the head of `Theorem1a`.
* **Statement (b) of Theorem 1, on what is forced by the representation.** A stem is removed from `𝒩ᵢ⁺` as well, since a root can lose a child (`DeletedNetwork`); 2-blobs are removed one at a time, where the paper says "repeatedly"; length 3 is "sufficiently large".
* **Proposition 1.** None. "By Theorem 1, `CF_abcd` is strictly `(ab|cd)`-cut for `ε > 0`" is wrong for all `ε`, and isn't used (`NetworkNk.exists_not_isStrictlyCutAtFirst`).
* **Theorem 3.** "Theorem 1 thus shows that `CF_abcd` is `(ab|cd)`-cut" is unused: the rule of `theorem3_core` reads the topology. The description of a network whose taxa cannot be reduced, by chains of 2-blobs, is unused too. `theorem3` needs only `corollary1`, with `readTopology`.
* **"The distance between blobs cannot be identified"** (`InPassing.blobDistance_not_identifiable`). None: it holds for every `k ≥ 1` and `ε₀ > 0`. The paper gives no proof; ours computes the limits of the first entry at `M → 0⁺` and `M → ∞` along the paper's `CF_abcd = α CF₁ + (1 - α) CF₂`. "`k` or `M` varied" is loose, since `k` is discrete: `M` varied at fixed `k`, and `k` and `M` varied together (`isPreconnected_iUnion_cf_first`), both hold.
* **"For edges between trivial blobs ... identifiable"** is wrong for pendant edges (`FourCycle.pendant_not_identifiable`), and on the root of `𝒩⊕` only the sum of the two lengths is identifiable. `TrivialEdges.semidirected_length_eq` is the corrected statement, on `𝒩⁻`, for internal edges.
* **Forms for the later papers.** `exists_reduction_aux` isn't the paper's proof of (b): it has no 2-blob step and no Lemma 1 (see its docstring). The numbered results don't use it.

The gaps of the paper are recorded where they matter: `Lemma2`, `Lemma3`, `CycleLemma`, `DeletedNetwork`, the head of `Theorem1b` and of `Reduction`, `Theorem3`.

## What the paper says in passing

No later proof uses these, except that the mixture is used in the proof of Theorem 1 (b). Lean names are in `InPassing` unless said.

| In the paper | Lean |
| --- | --- |
| "`𝒩⁻` may have any number of 2-blobs", in Lemma 1 | `exists_network_star`, `exists_network_resolved`, in `TwoBlobs`: a 4-cycle or a tree, with 2-cycles inserted above a taxon |
| "hybrid edges, which are in blobs" | `not_isBridge_of_isHybridEdge` |
| "it must be an `m`-blob with `m ≥ k`" | `card_le_cutDegree`, `card_le_blobDegree` |
| Condition (1) after Definition 12 | `isBlobQuartet_iff_deletion`: it needs a binary network |
| "`T_rd(𝒩⁻)` can also be obtained from the rooted one" | `trdFromRooted`, `isIso_trdFromRooted` |
| `T_rd(𝒩⁻)` is a tree | `Bridges.isTree_Trd` |
| "every tree displayed on the 4-taxon network has the same resolved quartet topology" | `isTreelike_iff_forall_displays`, `isTreeQuartet_iff_forall_displays`; the converse uses `exists_reduction`, which the paper's proof of Theorem 1 (b) contains |
| `CF(𝒩⁺) = γ₁ CF(𝒩₂⁺) + γ₂ CF(𝒩₁⁺)` in the proof of Theorem 1 (b) | `cf_mixture`, on the networks `deleted`; the proof of Theorem 1 (b) uses it as `nmscCF_withPair_mixture`, in `DeletedNetwork` |
| `CF_abcd = α CF₁ + (1 - α) CF₂` in the proof of Proposition 1 | `NetworkNk.nmscCF_eq_mixture`, in `NetworkNkMixture` |
| "the distance between blobs cannot be identified" | `blobDistance_not_identifiable`, in `BlobDistance`: on one `𝒩(k)⁺`, for every `k ≥ 1` and `ε₀ > 0`, all `ε′` near `ε₀` share a segment of `CF`s with `ε₀`. `NetworkNk.cf_first_eq`, `cfZero`, `cfInfty`, `cfInfty_lt_cfZero`, in `NetworkNkExact`; at `k = 1` the two limits differ by `p (1 - p) / 6` (`cfZero_sub_cfInfty_one`) |
| "`k` or `M` varied, the `CF` varies over a line segment" | `isPreconnected_cf_first`, `exists_M_of_value`, `isPreconnected_iUnion_cf_first`, in `BlobDistance` |
| Steps 1 to 4 of the outline in Section 5 | `Algorithm.stepTwoB`, `stepTwoT`, `stepThree`, `outline`, for any test |
| "it can be shown to provide a statistically consistent estimate" | `Algorithm.outline_consistent`, for any test right on four taxa with probability tending to one. In `TINNiK.AllmanOutline`: `outline_cut_consistent`, `outline_cut_consistent_nj`, for generic parameters and the cut test, the "novel statistical test" of step 2, developed in TINNiK. `outline_cut_eq_tinnik` is the bridge to `tinnik`, and the proof is `TINNiK.theorem4` |
| "in time `O(n⁵)`"; "the computational time is `O((n + m) n⁴)`" | `TINNiK.stepThree_count`, `TINNiK.outline_operations_le`, in `TINNiK.AllmanOutline`, counts of operations from `TINNiK.Counts` |
| "the point `(1/3, 1/3, 1/3)` where the 3 model lines intersect" | `Algorithm.cutLine_inter` |
| "heuristics such as those used by ASTRAL ... provide a fast estimate of them" | `Algorithm.astralLength`, Sayyari and Mirarab's Theorem 2: `astralLength_semidirected`, exact on the `CF`, and `astralLength_semidirected_consistent`, on gene trees. "Fast" isn't a claim to prove |
| "leaves are the only 1-blobs, while the root and internal nodes are 3-blobs"; "polytomous nodes are `k`-blobs with `k ≥ 4`" | `BlobStructure.blobDegree_eq_one_iff_of_isTreeNetwork`, `blobDegree_eq_three_of_isTreeNetwork`, `four_le_blobDegree_of_isTreeNetwork`, in `TreeBlobs` |
| "if the root of a binary network is a trivial blob, then it is a degree-2 node but forms a degree-3 blob" | `BlobStructure.root_of_isTrivialBlob` |
| "on a tree any 3 taxa determine a unique node" | `BlobStructure.existsUnique_node_of_isTreeNetwork` |
| "nodes of degree 4 or more in the tree of blobs indicate non-trivial blobs"; "those of degree 2 or 3 may correspond to trivial or non-trivial blobs" | `BlobStructure.not_isTrivialBlob_of_four_le_cutDegree`; `Figures.fig1_degree_examples` |
| "our restriction to binary networks rules out this possibility", of two cycles sharing only a node; Figure 2R | `BlobStructure.exists_mem_inter_of_two_incident`; `Figures.fig2R_blob` |
| "(if the network is level-1, this is a chain of 2-cycles)", above the LSA; "the simplest blobs have the form of cycles" | `BlobStructure.ncard_blobNodes_of_isAboveLSA`, `BlobStructure.ncard_edges_of_isLevelOne`, for the library's `RootedNetwork.IsLevelOne` |
| "non-tree phylogenetic networks may have `k`-blobs that are not nodes for any `k > 1`" | `CycleFamily.exists_kBlob` |
| "this happens even in the level-1 case with a single cycle of `k` edges, `k ≥ 5`"; "can even be a tree"; "`{a, b, c, f}` is a B-quartet on both" | `CycleFamily.cycleNet_b_to_t`, `isLevelOne_cycleNet`, `ncard_not_isBridge`; `Figures.fig3_induced_tree`; `Figures.fig3_abcf` |
| The description of a network whose taxa cannot be reduced, in the proof of Theorem 3: "`𝒩⊕` contains the blob `ℬ` with `n` incident cut edges" | `BlobStructure.structure_of_separated`: at most 2 and at most 3 for the other blobs, and exactly `n` for `ℬ`. The proof of Theorem 3 doesn't use it |
| The caption of Figure 2: "a planar 5-blob", "a non-planar 4-blob" | `Figures.fig2L_blob`, `fig2C_blob`, `fig2L_edges`, `fig2C_edges`, `fig2L_planar`, `fig2C_not_planar`, in `Figure2`, with `FigureCheck.Rotation.IsPlanar`, a rotation system of genus 0. Non-planarity is a finite check |
| "in Fig. 1L, the child edges of `v` are both tree edges and non-cut, while the parent edge of `v` is tree and cut"; the caption of Figure 1: "The LSA of the network is `v`", "6 non-trivial blobs (a 5-blob, two 3-blobs, and three 2-blobs), and a single trivial 3-blob"; the panel R | `Figures.fig1_edges_at_v`, `fig1_lsa`, `fig1_blobs`, `fig1_panelR`, in `Figure1` |
| Allman et al. (2011), as cited: "two of the three entries ... equal, with the third no smaller"; "any value in the interval `(1/3, 1)`" | `BlobStructure.third_no_smaller_of_isTreeNetwork`, `cfTriple_of_isTreeNetwork`, on all resolved trees, from `TrivialEdges.nmscCF_of_edge`, `nmscCF_of_root`; that every value arises is `InPassing.cf_tree_range` |
| Baños (2019), as cited: "If `𝒩⁺` is level-1 ... `CF_{ab|cd}` may take on any value in `(1/6, 1)`" | `NetworkNk.banos_range`, on `𝒩(1)⁺`, level-1 with `T_rd = ab|cd`, by `nmscCF_one`: the range over all its parameters is exactly `(1/6, 1)`. That the bound holds on every level-1 network is Baños's further claim, not proved here |
| "`CF_abcd` is cut if, and only if, it is strictly cut", for generic parameters | `isCutCF_iff_isStrictlyCutCF`, in `CFGeometry`, by the paper's argument |
| "only part (a) of Theorem 2 is needed" | `theorem3_core_partA`, `theorem3_partA`, in `Theorem3` |
| "every subset of 3 taxa determines a blob" | `BlobStructure.existsUnique_isDeterminedBy_three` |
| "every `m`-blob with `m ≥ 3` that is below the LSA is determined by one or more subsets of 3 taxa" | `BlobStructure.exists_isDeterminedBy_of_isBelowLSA` |
| "blobs above the LSA are not determined by any subset of taxa" | `BlobStructure.not_isDeterminedBy_of_isAboveLSA` |
| "an `m`-blob containing the LSA is determined by 3 taxa if `m ≥ 4`" | `BlobStructure.exists_isDeterminedBy_lsaNode` |
| "all other blobs in the chain will be 2-blobs" | `BlobStructure.IsChainOfBlobs.deg_eq_two` |
| "a (possibly empty) chain of blobs as the subnetwork between its root and LSA" | `BlobStructure.exists_chain_root_lsaNode`, `BlobStructure.blobDegree_eq_two_of_isAboveLSA` |
| "the degree of the blob containing the LSA not changing in passing from `𝒩⁺` to `𝒩⊕`" | `BlobStructure.blobDegree_lsaPlus`, in `LSABlob` |
| "that blob gives only an `(m - 1)`-multifurcation"; "that blob will be completely suppressed" | `BlobStructure.existsUnique_multifurcation`, `BlobStructure.not_liesIn_of_three`, in `LSABlob` |
| The geometry after Proposition 1: the simplex; the three segments, and every point of them; off the segments only unresolved trees | `cfTriple_mem_simplex`, `proposition1`, `cfTriple_of_hasQuartetTopology_acbd`, `cfTriple_of_hasQuartetTopology_adbc`, `proposition1_converse`, `hasStarTopology_of_isNonCutCF`, in `CFGeometry` and `Proposition1` |
| "by Baños (2019), all points off the line segments arise from level-1 networks with 4-cycles"; a 4-blob "may produce a CF on the line segments for certain numerical parameters" | `FourCycle.exists_cfTriple_eq`, with `FourCycle.isBridge_network_iff`; `FourCycle.exists_isCutCF`. Baños's theorem is cited; the proof is ours, a mixture of two trees (`FourCycle.nmscCF_network`) |
| "for edges between trivial blobs, it is straightforward to see that edge lengths are identifiable" | `TrivialEdges.semidirected_length_eq`, on `𝒩⁻`, for internal edges. Pendant edges have to be left out: `FourCycle.pendant_not_identifiable` is a pendant edge between trivial blobs with no `CF` depending on its length |
| The examples of Figures 3 and 9 | `Figures.fig3_*`, `Figures.fig9L_*`, `Figures.fig9R_*`, with `fig3_cf`, `fig9L_single_rule`, `fig9L_cf`, `fig9R_three_rules`, `fig9R_cf` |

## What was read

* The paper: the PMC author manuscript and the arXiv TeX, not the journal's text.
* Semple and Steel 2005, Rhodes 2020, in the proof of Theorem 4, for "the collection of displayed quartets determine the tree": the library's `mem_of_forall_displays` (Steel's theorem), through `treeFromQuartets_displays`. Neither was read for this.
* The splits-equivalence theorem on graphs: not cited by the paper, and needed for `theorem4_iso`. It is `SempleSteel2003.xTree_unique`, through `TreeIso`; see the README of `External/SempleSteel2003` for what was read.
* Baños 2019, for "all points off the line segments arise from level-1 networks": proved here, in `FourCycle`. It wasn't read for this.
* Sayyari and Mirarab 2016, for the estimate of edge lengths: read in the PMC copy, PMC4915361; `Algorithm.astralLength` is its Theorem 2. Only the formula is taken from it, with the limit proved here.
* Figure 1: read from the image of the PMC page, panel by panel. The network in `Figure1` is that reading; its blobs, by the kernel, agree with the caption.
* Baños 2019, for the range `(1/6, 1)`: its Proposition 7 was read in PMC6344282. `NetworkOne` computes the `CF` on the network with only a `3₂`-cycle, by our chain, and gets its equation (9). The proof of Proposition 7 in the PMC copy cites that as "(7)" once. Its reduction of the other level-1 networks, by its Lemmas 9 and 10, isn't followed.
* Steel 2016, Baños 2019, Gusfield et al. 2007, Solís-Lemus and Ané 2016, Xu and Ané 2021: for definitions only.
