# ECToBlob: statistical inference of the tree of blobs from quartet concordance factors, in Lean

[![CI](https://github.com/vltanh/lean4-tob/actions/workflows/lean_action_ci.yml/badge.svg)](https://github.com/vltanh/lean4-tob/actions/workflows/lean_action_ci.yml)

J. A. Rhodes, E. S. Allman, C. Ané and H. Baños, *Statistical inference of the Tree of Blobs of a phylogenetic network from
quartet concordance factors* ([bioRxiv 10.64898/2026.05.28.728501 v1](https://www.biorxiv.org/content/10.64898/2026.05.28.728501v1)),
infer the tree of blobs of a phylogenetic network, the tree left when each blob, a maximal 2-edge connected subgraph, is
contracted to a node, from gene trees sampled under the network multispecies coalescent. Their algorithm, ECToBlob, starts
from a resolution `T₀` of the tree of blobs, such as a tree optimizing the Maximum Quartet Support criterion, which by
Theorem 3.1 resolves the tree of blobs under two conditions on the quartet concordance factors. It then contracts the
edges of `T₀` that star tests and T1 tests on 4-taxon concordance factors, with their p-values combined under dependence,
find not to be cut edges. Theorem 4.1, for networks of any level and degree, says that if `a₁a₂|b₁b₂` is a cut-edge split of
the induced 4-taxon network for all `aᵢ ∈ Aᵢ`, `bᵢ ∈ Bᵢ`, then `A₁ ∪ A₂ | B₁ ∪ B₂` is a cut-edge split of the network.
Theorem 8.2 says that, at test levels chosen independently of the network, the algorithm returns the tree of blobs with
probability tending to one as the number of gene trees grows. The formalization, in Lean 4 with Mathlib, is
unconditional: no result of the literature is assumed.

This paper is part of the collection of formalizations described in [`../../README.md`](../../README.md).

## What is proved

- Every numbered result of the paper: Theorems 3.1, 4.1, 8.2; Lemmas 3.5, 6.1, 8.1; Corollaries 3.6, 4.2, 4.3;
  Proposition 5.1; equations (3.2), (3.3); Remark 3.2. They are proved by the paper's arguments, except the departures
  listed in [Section 7 of the report](REPORT.md#7-departures-from-the-papers-proofs), and [its Section 8](REPORT.md#8-what-each-result-depends-on)
  has what each depends on. Theorem 8.2 and (3.3) are proved in corrected forms (see the audit summary below).
- What the paper says in passing: the observation in §3 on MQS and displayed trees, Remarks 3.3, 5.2 and 8.3, Remark 8.4
  for binary networks with a counterexample on a non-binary one, Remark 3.4 without incomplete lineage sorting, the levels
  of lines 1159–1167, and from §10 the line test, a random `T₀`, data splitting, combining edge p-values, the framework on
  other tests and on sum-of-pairs distances, and Log-det distances. [Section 9 of the report](REPORT.md#9-not-formalized)
  lists what remains: empirical claims, and statements that are false, each with its counterexample.
- The results it cites, in [`src/External/`](../../src/External), each folder with a README that says whether its source
  was read: NANUQ (Proposition 9; Theorem 36, corrected), Legried et al. 2021 (Theorem 1 on quartets), Mitchell et al. 2019
  (Theorem 3.1 for this model, the limit laws and densities of T3 and T1), Ané et al. 2024 (exchangeability, Proposition
  12), Dinh and Baños 2025 (Theorem 1), and, through NANUQ and TINNiK, Huber et al. 2025 (Theorem 5.1) and Rhodes 2020
  (Theorem 2). What the paper uses of Allman et al. 2023 and TINNiK is proved in their folders,
  [`src/AllmanEtAl2023/`](../../src/AllmanEtAl2023) and [`src/TINNiK/`](../../src/TINNiK).
- `lake build` passes with no warnings, and there is no `sorry`, `axiom`, `native_decide` or `implemented_by`.
  [`scripts/Audit.lean`](../../scripts/Audit.lean) checks every declaration of the project and of the library it uses,
  including private and generated ones, against [`propext`](https://leanprover-community.github.io/mathlib4_docs/Init/Core.html#propext), [`Classical.choice`](https://leanprover-community.github.io/mathlib4_docs/Init/Prelude.html#Classical.choice) and [`Quot.sound`](https://leanprover-community.github.io/mathlib4_docs/Init/Prelude.html#Quot.sound) (see Building).

## The main results

[`src/MainResults/ECToBlob.lean`](../../src/MainResults/ECToBlob.lean) states these theorems in the namespace
`TreeOfBlobs`, each with a docstring in plain terms and with the paper's hypotheses, and proves them from the libraries.

The paper's theorems:

- [`TreeOfBlobs.theorem3_1`](../../src/MainResults/ECToBlob.lean#L72) (Theorem 3.1): every tree maximizing the Maximum Quartet Support objective resolves the tree of
  blobs, for quartet probabilities with strict dominance across cut edges and exchangeability across them.
- [`TreeOfBlobs.theorem4_1`](../../src/MainResults/ECToBlob.lean#L82) (Theorem 4.1): on a rooted network, not necessarily binary, if `a₁a₂|b₁b₂` is a cut-edge split of
  every induced 4-taxon network for `aᵢ ∈ Aᵢ`, `bᵢ ∈ Bᵢ`, then `A₁ ∪ A₂ | B₁ ∪ B₂` is a cut-edge split of the network.
- [`TreeOfBlobs.theorem8_2`](../../src/MainResults/ECToBlob.lean#L101) (Theorem 8.2, corrected): there are test levels `α_n`, `β_n`, independent of the network, such
  that every variant of the algorithm, from any resolution of the tree of blobs, returns the tree of blobs with
  probability tending to one, for every law of binary gene trees meeting both directions of Assumption 1 at the
  network's parameters, and, for Cauchy and CBC, with positive alternatives on quartets strictly in the T1 null.

What the paper says in passing, and its claims that fail:

- [`TreeOfBlobs.ectoblob_theorem8_2_displayed`](../../src/MainResults/ECToBlob.lean#L126): Theorem 8.2 for the displayed tree model, with Bon or BBC, on every network,
  binary or not, with the converse of Assumption 1 as a hypothesis at the parameters.
- [`TreeOfBlobs.ectoblob_displayed_counterexample`](../../src/MainResults/ECToBlob.lean#L140): on a binary network on five taxa, at all valid parameters of the
  displayed tree model, both directions of Assumption 1 hold, and Cauchy and CBC return a resolution `T₀` that is not the
  tree of blobs with probability tending to one, while Bon and BBC return the tree of blobs. This rests on Lean's
  extension of the Cauchy transform at `p = 1`.
- [`TreeOfBlobs.ectoblob_not_theorem8_2_without_hpos`](../../src/MainResults/ECToBlob.lean#L161): without its hypothesis on the alternatives, Theorem 8.2 fails for
  Cauchy and CBC at all sequences of levels.
- [`TreeOfBlobs.ectoblob_not_consistency_edge_combination_cbc`](../../src/MainResults/ECToBlob.lean#L176) (§10): on one law meeting both directions of Assumption 1,
  with positive alternatives, combining the edge p-values is consistent with Bon, BBC and Cauchy, and with CBC it keeps a
  false edge with probability at least `1/2 - ε` for large `n`.
- [`TreeOfBlobs.ectoblob_remark3_4_displays`](../../src/MainResults/ECToBlob.lean#L194) (Remark 3.4): under gene duplication and loss without incomplete lineage
  sorting, in the model of Legried et al. 2021 with any law on each edge, the quartet probabilities on a species tree
  satisfy (3.1), the hypothesis of Theorem 3.1.
- [`TreeOfBlobs.ectoblob_consistency_sumOfPairs`](../../src/MainResults/ECToBlob.lean#L201) (§10): from bounded distances on `n` loci, with the analogue of
  Assumption 1 for their mean, the algorithm with Bon or BBC on sum-of-pairs p-values returns the tree of blobs with
  probability tending to one.
- [`TreeOfBlobs.ectoblob_not_equation33Printed`](../../src/MainResults/ECToBlob.lean#L215): (3.3) as printed is false. At a multifurcation of a species tree, under the
  network multispecies coalescent at all valid parameters, its left side is `3` and its right side `10/3`.
- [`TreeOfBlobs.ectoblob_not_theorem8_2_literal`](../../src/MainResults/ECToBlob.lean#L218): Theorem 8.2 on the literal general model is false. No levels serve all
  valid parameters of all models meeting Assumption 1, by a one-parameter model on a rooted 4-cycle. This is not a
  counterexample under the network multispecies coalescent.

The sources it cites:

- [`TreeOfBlobs.nanuq_proposition9_source`](../../src/MainResults/ECToBlob.lean#L241) (NANUQ, Proposition 9, in the source's own terms): on four taxa of a binary
  level-1 network, at any `0 ≤ ρ ≤ 1`, what the concordance factor is when the induced network has no `4₁`- or
  `3₂`-cycle, a `3₂`-cycle, or a `4₁`-cycle.
- [`TreeOfBlobs.nanuq_theorem36_missing`](../../src/MainResults/ECToBlob.lean#L263) (NANUQ, Theorem 36, corrected, with gene trees on subsets of the taxa): with
  probability tending to one, the classification of all sets of four taxa, and so the quartet distance, is that of the
  network. The splits graph of the output isn't formalized.
- [`TreeOfBlobs.legried_theorem1`](../../src/MainResults/ECToBlob.lean#L280) (Legried, Molloy, Warnow, Roch 2021, Theorem 1, on quartets): under gene duplication and
  loss, two species trees that give the same probabilities of topologies on four gene copies picked uniformly display the
  same quartets.

## Palomar

No submission to [Palomar](https://github.com/mathlib-initiative) is planned. [`palomar/`](palomar) keeps the files in
case that changes:

- [`palomar/comparator.json`](palomar/comparator.json) runs Comparator on the theorems above, with [`MainResults.ECToBlob`](../../src/MainResults/ECToBlob.lean)
  as both the challenge and the solution module, and permits the axioms [`propext`](https://leanprover-community.github.io/mathlib4_docs/Init/Core.html#propext), [`Quot.sound`](https://leanprover-community.github.io/mathlib4_docs/Init/Prelude.html#Quot.sound) and [`Classical.choice`](https://leanprover-community.github.io/mathlib4_docs/Init/Prelude.html#Classical.choice).
- [`palomar/formalization.yaml`](palomar/formalization.yaml) is the entry's metadata, valid against the schema it names:
  the paper, the sources it cites, the statements aligned to the `TreeOfBlobs.*` theorems, and its fidelity section, which
  lists every divergence from the paper.

From the repository root, after `lake build`:

```sh
scripts/check_kernels.sh papers/ECToBlob/palomar/comparator.json
```

This checks the closure of each theorem under Lean's kernel, NanoDa and con-ron, and rejects `sorryAx`. It does not
compare a separate statement file with a proof, which is what Palomar's Challenge and Solution are for. `lake comparator`,
`leanexport` and `con-ron` come from the toolchain under `lake env`.

A submission would still need:

1. A Challenge that imports only Mathlib, with the definitions that its statements use in a block of its own, and the
   bridges from them to the library's definitions. The last such file, with `scripts/sync_challenge_defs.py`, which kept
   its block equal to the library's, and `scripts/gen_solution.py`, which generated the Solution from it, is in the git
   history at `f838ea4`, for the three papers of the time together.
2. A Solution that restates those theorems and proves them from the libraries, and a `comparator.json` that names the two
   modules.
3. These files at the root of the repository that holds the paper, with `formalization.yaml` pointing at the new modules.

## Audit summary

The numbers are those of [the report](REPORT.md), which gives each finding with its location, the paper's sentence, a
Lean counterexample where there is one, and the repair.

- **Errors.** (3.3) overcounts (E2). Remark 8.4 fails on a non-binary network (E35). Remark 3.3 needs "no anomalous
  quartets" read strictly (E36). Under the displayed tree model, line 1065 is false, and Theorem 8.2 holds for Bon and BBC
  and fails for Cauchy and CBC (E37).
- **Gaps.** The largest is in the proof of Theorem 8.2: the witness of a false edge may have a trivial 4-blob, which needed
  a new argument (E12). The others, E1, E3, E4, E6, E7 and E13–E17, are repaired too. At the centroid, the sentence on
  uniform T1 p-values is false (E13). Line 1422 asks too little of the tests (E68).
- **Missing hypotheses.** Theorem 8.2 needs parameters meeting Assumption 1 (E10), and, for its Cauchy and CBC variants,
  positive alternatives on null quartets (E11). Both corrections were agreed with the person who asked for this
  formalization, and the second doesn't affect the network multispecies coalescent.
- **Redundant hypotheses.** The disjointness of `A₁, A₂` and of `B₁, B₂` in Theorem 4.1, and the others of
  [Section 5](REPORT.md#5-redundant-hypotheses).
- **Cited results.** Proposition 5.1 adapts Allman et al.'s Theorem 1 by "checking the argument", which turns out right,
  and the adaptation is proved (E5). NANUQ's Theorem 36 is false as printed, at the distance, and its proof picks the wrong
  level; the corrected form is proved. E80, E82 and E84 are misprints in Legried et al., Mitchell et al. and NANUQ, which
  leave the results standing.
- **Proofs.** They follow the paper's arguments, except the departures in [Section 7](REPORT.md#7-departures-from-the-papers-proofs),
  each with what the paper does, what Lean does and why. Most repair gaps or errors: Theorem 3.1 (E2), Remark 3.2 (E1),
  Corollary 3.6 (E3), Theorem 8.2 (E11–E17), and Theorem 8.2 on the displayed tree model, where line 1065 is false (E37).
  Two aren't forced, and say so: Theorem 4.1 and Proposition 5.1. [`docs/route_differences.tsv`](../../docs/route_differences.tsv)
  records every difference of route.

## Credits

- Requested and supervised by The-Anh Vu-Le, who chose the paper and its version, agreed to the corrections of Theorem 8.2
  (E10, E11), and decided the library's boundary and the project's layout. **No person has reviewed the proofs.**
  Independent agents reviewed the statements and compared the proofs with the paper.
- Source audit and first foundations by Codex; statements, proofs, audit and documents by Claude (Opus 5.5) in Claude Code,
  with sub-agents, following the [formalize-math-paper](https://github.com/vltanh/formalize-math-paper) procedure.
- Made on 2026-10-27 and from 2026-10-31 to 2026-11-01, with the rest of the collection: three sub-agents in the Codex
  round, and 85 in Claude Code, at most 11 at once, up to commit `282215c`. [`docs/CREDITS.md`](../../docs/CREDITS.md) has
  the details.

## Related work

From [Section 10 of the report](REPORT.md#10-the-paper-in-the-literature), from a search made on 2026-10-31.

- History: Allman et al. 2023 showed that the tree of blobs is identifiable from gene quartet distributions, with no bound
  on the level, and TINNiK (2024) made this an algorithm with a consistency theorem. Huber et al. 2025 and Frohn et al.
  2025 give the exact-quarnet form that Theorem 4.1 extends. For binary networks, Corollary 4.2 is Lemma 1 of Frohn et al.,
  as the paper says.
- Concurrent: TOB-QMC (Dai, Han, Molloy, first posted 2025-11-06) proves the same result, that an optimum of the quartet
  criterion refines the tree of blobs, and contracts edges by other tests, with guarantees at level 1. ECToBlob calls the
  two works independent. Its formalization is in [`../TOBQMC/`](../TOBQMC/README.md).
- Since: we found no erratum and no version newer than v1. MSCquartets 3.3 implements ECToBlob. Dai and Molloy (WABI 2026)
  reconstruct level-1 blobs from a tree of blobs. No work we read settles whether the treelikeness of the 4-taxon sets
  around an edge decides it beyond level 1, which the paper's §10 raises.
- We found no other formalization of the paper. This project imports the public library
  [lean4-phylogenetics](https://github.com/vltanh/lean4-phylogenetics).

## What's next

The open directions are Assumption 1 under correlated inheritance (`0 < ρ < 1`, and `ρ = 1` on non-binary networks),
whether the treelikeness of the 4-taxon sets around an edge decides it beyond level 1, and Theorem 8.2 for Cauchy and CBC
without the hypothesis on the alternatives. [Section 11 of the report](REPORT.md#11-whats-next) has these, with rates,
coarsening and the no-anomaly assumption, and the simpler arguments that the formalization found.

## Building

From the root of the repository:

```sh
lake exe cache get
lake build
lake build MainResults.ECToBlob                                                  # this paper's main theorems
lake build Phylogenetics                                                         # the audit reads the whole library
lake env lean -DautoImplicit=false -DmaxSynthPendingDepth=3 scripts/Audit.lean   # axioms and dependencies
python3 scripts/route_check.py check docs/paper_routes.tsv --accept docs/route_differences.tsv
python3 scripts/check_layers.py                                                  # imports between units
scripts/check_kernels.sh papers/ECToBlob/palomar/comparator.json                 # Lean's kernel, NanoDa, con-ron
```

- The audit and the route check cover the whole collection. The route check confirms that every proof uses the results
  that the paper's proof cites, except the differences recorded in [`docs/route_differences.tsv`](../../docs/route_differences.tsv).
- Toolchain: Lean and Mathlib `v4.36.0-rc1` ([`lean-toolchain`](../../lean-toolchain), [`lake-manifest.json`](../../lake-manifest.json)).
  The library [lean4-phylogenetics](https://github.com/vltanh/lean4-phylogenetics) is required by commit, `f1a3592`, in
  [`lakefile.toml`](../../lakefile.toml).
- After adding a module, run `python3 scripts/gen_audit.py`. After moving declarations, run
  `python3 scripts/linkify_docs.py` to update the documents' links.
- CI ([`.github/workflows/lean_action_ci.yml`](../../.github/workflows/lean_action_ci.yml)) builds the project and the
  whole library, runs the audit, the route check and the check of imports between units, and checks the generated files,
  the documents' links and the Markdown tables. The kernels aren't in CI, so run them by hand.
- [`docs/CONFIGURATION.md`](../../docs/CONFIGURATION.md) records the version of the paper, the decisions, and what "line N"
  means.

## Layout

The paper's modules, in [`src/ECToBlob/`](../../src/ECToBlob):

| Module | Content |
| --- | --- |
| [`Section3`](../../src/ECToBlob/Section3.lean) | §3, resolving the tree of blobs: Lemma 3.5, Theorem 3.1, Remark 3.2, Corollary 3.6, (3.2), (3.3) |
| [`Section3Observations`](../../src/ECToBlob/Section3Observations.lean) | §3: the observations on what MQS infers |
| [`Equation33Counterexample`](../../src/ECToBlob/Equation33Counterexample.lean) | Equation (3.3) as printed is false |
| [`Remark33`](../../src/ECToBlob/Remark33.lean) | Remark 3.3: the assumptions of Theorem 3.1 for common models |
| [`Remark33Counterexample`](../../src/ECToBlob/Remark33Counterexample.lean) | Remark 3.3: "no anomalous quartets" has to be strict |
| [`Remark34`](../../src/ECToBlob/Remark34.lean) | Remark 3.4: duplication and loss |
| [`Biconnected`](../../src/ECToBlob/Biconnected.lean) | Blobs and biconnected subgraphs (lines 214–218) |
| [`Section4`](../../src/ECToBlob/Section4.lean) | §4, combinatorics of quartets and cut-edge splits: Theorem 4.1, Corollaries 4.2 and 4.3 |
| [`Section4Funnels`](../../src/ECToBlob/Section4Funnels.lean) | §4: funnels, the subgraphs `G̃₃`, `G̃₄`, and their cut edges |
| [`Section5`](../../src/ECToBlob/Section5.lean) | §5: the measure on numerical parameters, Assumption 1, Proposition 5.1 |
| [`FaceWitness`](../../src/ECToBlob/FaceWitness.lean) | Non-cut parameters on a face, at a reduction, for the adaptation of Allman et al.'s Theorem 1 |
| [`Remark52`](../../src/ECToBlob/Remark52.lean) | Remark 5.2: the degree condition of Proposition 5.1 cannot be dropped |
| [`Remark52Networks`](../../src/ECToBlob/Remark52Networks.lean) | Remark 5.2: the three networks of Figure 1 |
| [`Section6`](../../src/ECToBlob/Section6.lean) | §6, combining p-values: Lemma 6.1 |
| [`Counts`](../../src/ECToBlob/Counts.lean) | Operation counts (lines 922–935) |
| [`Lemma81`](../../src/ECToBlob/Lemma81.lean) | §8: Lemma 8.1 |
| [`Section8`](../../src/ECToBlob/Section8.lean) | §8, statistical consistency: Theorem 8.2 |
| [`Deterministic`](../../src/ECToBlob/Deterministic.lean) | §8: the deterministic core of the proof of Theorem 8.2 |
| [`FalseEdge`](../../src/ECToBlob/FalseEdge.lean) | §8: a false edge has a witness that is neither a cut split nor a trivial 4-blob |
| [`Theorem82Literal`](../../src/ECToBlob/Theorem82Literal.lean) | Theorem 8.2 on the literal general model: the genericity is needed |
| [`BinaryLawExample`](../../src/ECToBlob/BinaryLawExample.lean) | Two laws of binary gene trees on the network of `FinNetwork.Binary` |
| [`LevelCutoffs`](../../src/ECToBlob/LevelCutoffs.lean) | Lines 1164–1167: the `o(n)` cutoffs of `α_n` |
| [`DisplayedTree`](../../src/ECToBlob/DisplayedTree.lean) | Theorem 8.2 for the displayed tree model |
| [`DisplayedTreeExample`](../../src/ECToBlob/DisplayedTreeExample.lean) | Theorem 8.2 for Cauchy and CBC on the displayed tree model: the counterexamples |
| [`Remark83`](../../src/ECToBlob/Remark83.lean) | Remark 8.3: the consistency of NANUQ and TINNiK, with explicit levels |
| [`Remark84`](../../src/ECToBlob/Remark84.lean) | Remark 8.4: an input tree that is not a resolution of the tree of blobs |
| [`Remarks`](../../src/ECToBlob/Remarks.lean) | §10: variants of the algorithm |
| [`Framework`](../../src/ECToBlob/Framework.lean) | §10: other data types and other tests |
| [`SumOfPairs`](../../src/ECToBlob/SumOfPairs.lean) | §10: sums of pairs of distances |
| [`LogDet`](../../src/ECToBlob/LogDet.lean) | The Log-det distance (§10) |
| [`InPassing`](../../src/ECToBlob/InPassing.lean) | What the paper says in passing, by its lines |

[`src/MainResults/ECToBlob.lean`](../../src/MainResults/ECToBlob.lean) has the main theorems.

The sources it uses, in [`src/External/`](../../src/External), each with a README:

- [`AllmanBanosRhodes2019/`](../../src/External/AllmanBanosRhodes2019): NANUQ, for Remark 8.3 and the main theorems prefixed `nanuq_`.
- [`LegriedEtAl2021/`](../../src/External/LegriedEtAl2021): Legried et al. 2021, for Remark 3.4 and [`legried_theorem1`](../../src/MainResults/ECToBlob.lean#L280).
- [`MitchellAllmanRhodes2019/`](../../src/External/MitchellAllmanRhodes2019): Mitchell et al. 2019, the T1 and T3 tests
  and their limit laws.
- Through NANUQ and TINNiK: [`HuberEtAl2025/`](../../src/External/HuberEtAl2025), [`Rhodes2020/`](../../src/External/Rhodes2020)
  and [`StudierKeppler1988/`](../../src/External/StudierKeppler1988).
- What the paper uses of Ané et al. 2024, exchangeability and the strict form of Proposition 12, is in the library and in
  [`src/Basic/RhoOne.lean`](../../src/Basic/RhoOne.lean). [`AneEtAl2024/`](../../src/External/AneEtAl2024) has the source's
  own proofs, and this unit doesn't import it. Nor does it import [`DinhBanos2025/`](../../src/External/DinhBanos2025),
  the source the paper cites in passing.

It also imports two other papers of the collection: Allman et al. 2023, in [`src/AllmanEtAl2023/`](../../src/AllmanEtAl2023)
([its folder](../AllmanEtAl2023/README.md)), and TINNiK, in [`src/TINNiK/`](../../src/TINNiK) ([its folder](../TINNiK/README.md)).

The modules of [`src/Basic/`](../../src/Basic) that it imports ([its README](../../src/Basic/README.md) has them all):

| Module | Content |
| --- | --- |
| `Defs` | The algorithms with their options and steps, and the papers' standing assumptions, among them Assumption 1 |
| `Testing/*` | Hypothesis tests on quartet counts: statistics and p-values, combining p-values, independent samples, tails, limit laws through the trinomial central limit theorem |
| `ForMathlib/*` | Analysis and probability that do not mention phylogenetics, reached through `Testing/*` |
| `LocalObjective` | The local objective at a multifurcation of Theorem 3.1: attaching subtrees, sums over representatives |
| `RhoOne` | No anomalous quartets at `ρ = 1`: the strict form of Proposition 12 of Ané et al. 2024 |
| `General` | Taxa that a parent choice leaves unresolved have concordance factors `1/3`; null sets of parameters |
| `Level1Blobs` | Blobs of level-1 networks in the language of domination |
| `Level1CF` | At level 1, an induced cut-edge split that the tree of blobs does not display has the strictly largest concordance factor |
| `InducedSplits` | Cut splits of induced networks in the language of domination, quartet trees as four taxa, splits off a deletion |
| `FinNetwork` | Networks given by tables of arcs, checked by `decide`, and the binary network with a 4-cycle and a cut edge of the counterexamples |
| `TreeCounts` | How many clusters a hierarchy has, and how many internal edges a binary tree has |
| `UnitMetric` | Valid parameters on any network: unit lengths, equal inheritance |
| `NMSCChain` | The chain of the network multispecies coalescent on a concrete network, from the root down |

[`scripts/layers.toml`](../../scripts/layers.toml) lists what this unit, [`ECToBlob`](../../src/ECToBlob) ([`src/ECToBlob/`](../../src/ECToBlob) and
[`src/MainResults/ECToBlob.lean`](../../src/MainResults/ECToBlob.lean)), may import: [`Basic`](../../src/Basic), [`AllmanEtAl2023`](../../src/AllmanEtAl2023), [`TINNiK`](../../src/TINNiK), `AllmanBanosRhodes2019`,
`LegriedEtAl2021` and `MitchellAllmanRhodes2019`, besides Mathlib and the library. TOB-QMC and ECToBlob are concurrent and
independent, so neither imports the other. `python3 scripts/check_layers.py` checks every import against it.

## License

Apache-2.0: [`LICENSE`](../../LICENSE). Code adapted from [lean4-phylogenetics](https://github.com/vltanh/lean4-phylogenetics)
(Apache-2.0) keeps its notice in each file's header.
