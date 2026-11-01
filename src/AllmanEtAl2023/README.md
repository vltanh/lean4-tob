# Allman, Baños, Mitchell, Rhodes 2023: identifiability of the tree of blobs

Source: E. S. Allman, H. Baños, J. D. Mitchell, J. A. Rhodes, *The tree of blobs of a species network:
identifiability under the coalescent*, J. Math. Biol. 86 (2023), 10,
<https://doi.org/10.1007/s00285-022-01838-9>. Read in the PMC author manuscript NIHMS1884071 (PMC10062380) and the arXiv TeX. The journal's text wasn't
reachable, so "the PMC manuscript" is what is meant below and in the docstrings.

"Line 149" and "the PMC text, line 149" in the docstrings mean line 149 of the plain text of the PMC page, one line per paragraph. The labels `a:thm:…`, `a:lem:…`, `a:cor:…`, `a:prop:…`, `a:def::…` are those of the arXiv TeX; the routes of the proofs are in `docs/paper_routes.tsv`, and their differences from the paper's in `docs/route_differences.tsv`.

All names are in the namespace `AllmanEtAl2023`. No module here imports `ECToBlob`, `TOBQMC` or `TINNiK`. There is no `sorry`.

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
| `InPassing`, `BlobDistance`, `TwoBlobs`, `BlobStructure`, `LSABlob`, `CFGeometry`, `FourCycle`, `TrivialEdges`, `Figures`, `FigureCheck` | what the paper says in passing, below. `FigureCheck` checks claims about a numbered network by computation, in the kernel |
| `CFDetectable` | for the later papers: `cfDetectable_generic`, `isGenericNull_not_isNonCut` on `CFDetectable`. TINNiK's Theorem 1 is `cfDetectable_generic` |

For the later papers, besides `CFDetectable`: `closure_complete`, `closure_sound` (`Basic`), the closure at any degree, which `ECToBlob.remark83_tinnik` needs; `exists_reduction_aux`, `exists_reduction`, `exists_reduction_of_blobDegree` (`Reduction`), which ECToBlob's Section 5, TOB-QMC's Lemma 1 and `InPassing.isTreelike_iff_forall_displays` use, on non-binary networks too. `Basic.NMSCChain`, outside this directory, has the chain of the NMSC on a concrete network, which `FourCycle` and `TrivialEdges` use.

## Departures that remain

The proofs of the numbered results follow the paper, apart from these.

* **Statement (a) of Theorem 1.** The paper's cases of the rooted forms have two arguments; in Lean they are one. The rooted form selects the edge `f` and locates its source (`exists_edge_of_rootedForm`), and `nmscCF_alternatives_at` doesn't use the location. See the head of `Theorem1a`.
* **Statement (b) of Theorem 1, on what is forced by the representation.** A stem is removed from `𝒩ᵢ⁺` as well, since a root can lose a child (`DeletedNetwork`); 2-blobs are removed one at a time, where the paper says "repeatedly"; length 3 is "sufficiently large".
* **Proposition 1.** None. "By Theorem 1, `CF_abcd` is strictly `(ab|cd)`-cut for `ε > 0`" is wrong for all `ε`, and isn't used (`NetworkNk.exists_not_isStrictlyCutAtFirst`).
* **Theorem 3.** "Theorem 1 thus shows that `CF_abcd` is `(ab|cd)`-cut" is unused: the rule of `theorem3_core` reads the topology. The description of a network whose taxa cannot be reduced, by chains of 2-blobs, is unused too. `theorem3` needs only `corollary1`, with `readTopology`.
* **"The distance between blobs cannot be identified"** (`InPassing.blobDistance_not_identifiable`). The bounds need `k ≥ 2` and `ε₀` small. The paper's example has `k = 3` in Figure 6, and no value of `ε`. `k = 1` isn't formalized: see the head of `BlobDistance`.
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
| "the distance between blobs cannot be identified" | `blobDistance_not_identifiable`, in `BlobDistance`: on one `𝒩(k)⁺`, `k ≥ 2`, two nearby values of `ε` share a segment of `CF`s |
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
* Steel 2016, Baños 2019, Gusfield et al. 2007, Solís-Lemus and Ané 2016, Xu and Ané 2021: for definitions only. Allman et al. 2011, Baños 2019 before Proposition 1: for context only.
