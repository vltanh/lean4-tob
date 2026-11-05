# Audit of ECToBlob and its formalization

Paper: J. A. Rhodes, E. S. Allman, C. Ané, H. Baños, *Statistical inference of the Tree of Blobs of a phylogenetic network
from quartet concordance factors*, [bioRxiv 10.64898/2026.05.28.728501 v1](https://www.biorxiv.org/content/10.64898/2026.05.28.728501v1),
posted 2026-05-31, with its supplement, whose appendices A and B are simulations. No author TeX source exists, so the audit
was made against the text of the v1 PDF: "line N" is a line of `pdftotext -layout` run on it, as
[`docs/CONFIGURATION.md`](../../docs/CONFIGURATION.md) defines, and [`docs/sources.json`](../../docs/sources.json) has the
hash of the PDF. Section, result and equation numbers are the paper's.

This paper is part of the collection described in [`../../README.md`](../../README.md). It cites two other papers of the
collection, Allman et al. 2023 and TINNiK, which have their own folders, [`../AllmanEtAl2023/`](../AllmanEtAl2023/README.md)
and [`../TINNiK/`](../TINNiK/README.md). The findings keep the collection's numbers (Section 3).

Status of the formalization:

- **Proved, by the paper's arguments** except for the departures of Section 7: every numbered result of the paper
  (Theorems 3.1, 4.1, 8.2; Lemmas 3.5, 6.1, 8.1; Corollaries 3.6, 4.2, 4.3; Proposition 5.1; equations (3.2), (3.3);
  Remark 3.2), as printed or in a corrected form.
- **Also proved, from what the paper says in passing:** its observation in §3 on MQS and displayed trees, its Remarks
  3.3, 5.2 and 8.3, Remark 8.4 for binary networks, with a counterexample on a non-binary one (E35), Remark 3.4 without
  incomplete lineage sorting, the levels of lines 1159–1167, and from its §10, the line test without the no-anomaly
  assumption, a random `T₀` and data splitting, combining edge p-values, the framework on other tests and on sum-of-pairs
  distances, and what it says of Log-det distances. Running times are counts of operations, with no machine model.
  Section 9 lists what remains.
- **Proved cited results**, in [`src/External/`](../../src/External): NANUQ's Theorem 36, corrected, with its
  Proposition 9, all three parts, on binary level-1 networks; Legried et al. 2021, Theorem 1 on quartets, and its
  equations (5), (7); Mitchell et al. 2019 Theorem 3.1 for this model, and Propositions 4.1, 4.2, 5.1, 5.2; Ané et al.
  2024 exchangeability and Proposition 12; Dinh and Baños 2025, Theorem 1 and Corollary 2; and, through NANUQ and TINNiK,
  Huber et al. 2025 Theorem 5.1, both directions, and Rhodes 2020 Theorem 2. Rhodes et al. 2025, Proposition 6.1, item 1,
  is proved in [`src/ECToBlob/SumOfPairs.lean`](../../src/ECToBlob/SumOfPairs.lean). What the paper uses of Allman et al.
  2023 and TINNiK is proved in [`src/AllmanEtAl2023/`](../../src/AllmanEtAl2023) and [`src/TINNiK/`](../../src/TINNiK).
  Section 2 says which sources were read.
- **Unconditional.** No result of the literature is assumed. Assumption 1 stays a hypothesis of Theorem 8.2, as in the
  paper ([`ECToBlob.Assumption1Forward`](../../src/Basic/Defs.lean#L213), [`ECToBlob.Assumption1Converse`](../../src/Basic/Defs.lean#L219)).
- **Statements.** Theorem 8.2 is proved for parameters meeting both directions of Assumption 1 (E10), and, for its
  Cauchy and CBC variants, with positive alternatives on quartets strictly in the T1 null, under the continuous extension
  of the Cauchy transform at `p = 1`, where the printed formula is undefined (E11). Both corrections were agreed with the
  user who requested this formalization. Theorem 8.2 is stated on binary gene trees, and on the displayed tree model on
  any network it is proved for Bon and BBC and refuted for Cauchy and CBC (E37). Equation (3.3) is weighted by block sizes
  (E2). E35, E36, E37 and the correction of NANUQ's Theorem 36 came later, from reading and proving what the paper says in
  passing, and are reported here for that user to read. Section 4 and the end of Section 6 list the corrections.
- `lake build` passes with no warnings, and there is no `sorry`, `axiom`, `native_decide` or `implemented_by` in
  [`src/`](../../src). [`scripts/Audit.lean`](../../scripts/Audit.lean) checks every declaration of the libraries,
  including private and generated ones and those of the library [`lean4-phylogenetics`](https://github.com/vltanh/lean4-phylogenetics),
  against the standard axioms [`propext`](https://leanprover-community.github.io/mathlib4_docs/Init/Core.html#propext),
  [`Classical.choice`](https://leanprover-community.github.io/mathlib4_docs/Init/Prelude.html#Classical.choice),
  [`Quot.sound`](https://leanprover-community.github.io/mathlib4_docs/Init/Prelude.html#Quot.sound).
- [`src/MainResults/ECToBlob.lean`](../../src/MainResults/ECToBlob.lean) states the main theorems of this paper and of
  two sources it cites, NANUQ and Legried et al. 2021, with the paper's hypotheses, and proves them from the libraries.
  `scripts/check_kernels.sh papers/ECToBlob/palomar/comparator.json` checks them under Lean's kernel, NanoDa, through
  Comparator's normal mode, and con-ron, and all three accept them. There is no separate Challenge: Comparator runs on
  that module as both challenge and solution, so it compares no statement file with a proof ([`README.md`](README.md#palomar)).
- **Proofs.** Every proof follows the paper's, except the departures of Section 7, each with what the paper does, what
  Lean does and why. Most repair gaps or errors: Theorem 3.1 (E2), Remark 3.2 (E1), Corollary 3.6 (E3), Theorem 8.2
  (E11–E17), and Theorem 8.2 on the displayed tree model, where line 1065 is false (E37). Two are not forced, and are
  documented: Theorem 4.1 (3-blobs and chains on the unsuppressed graph) and Proposition 5.1 (on the network, not on each
  quarnet). [`docs/route_differences.tsv`](../../docs/route_differences.tsv) records every difference of route.
- No person has reviewed the proofs. Independent agents reviewed the statements against the sources and compared the
  formal proofs with the paper's, and a separate agent checked the findings ([`docs/CREDITS.md`](../../docs/CREDITS.md)).

## 1. Summary

- **Errors.** (3.3) overcounts (E2), and Remark 8.4, worded as what the argument "indicates", fails on a non-binary
  network, by an explicit tree and `T₀` (E35). Remark 3.3 cites for "no anomalous quartets" a paper whose definition is
  non-strict, under which (3.1) and the conclusion of Theorem 3.1 fail on a null set of parameters (E36); the paper's own
  use is strict. Line 1065 on uniform p-values is false under the displayed tree model (E37).
- **Gaps.** The proof of Theorem 8.2 has the most serious ones: the quartet witnessing a false edge may have a trivial
  4-blob, where the T1 null holds (E12); this needed a new 1,100-line argument, [`ECToBlob.falseEdge_witness`](../../src/ECToBlob/FalseEdge.lean#L807),
  and changes no statement. Others: E1, E3, E4, E6, E7, E13–E17. All are repaired, and none changes a statement. Under the
  displayed tree model on any network, Theorem 8.2 holds for Bon and BBC and fails for Cauchy and CBC, under the extension
  of E7 (E37). E13 and E68 are also loose sentences, neither affecting a result: at the centroid, the sentence on uniform
  T1 p-values is false (E13), and line 1422 asks too little of the tests (E68). E38 and E41 record what the remarks of
  §3, §7 and §10 need, and E34 the typos.
- **Missing hypotheses.** Theorem 8.2 needs generic parameters for the literal general model (E10, agreed) and, for its
  Cauchy and CBC variants, positive alternatives (E11, agreed; E11 holds for Lean's continuous extension of the Cauchy
  transform at `p = 1`, where the printed formula is undefined). Section 4 has all of them.
- **Redundant hypotheses.** Section 5. The most notable: the disjointness of `A₁, A₂` and of `B₁, B₂` in Theorem 4.1.
- **Use of cited results.** Proposition 5.1 adapts a theorem by "checking the argument", which turns out right (E5).
  Remark 3.3 needs the definition of Ané et al. 2024 read strictly (E36). Line 1017 excepts the centroid from the limit
  of Mitchell et al. 2019, as the source does, and the next sentence doesn't repeat the exception (E13). Section 2 lists gaps in the proofs of cited results. Among results
  only cited, Theorem 36 of NANUQ is false as printed, at the level of the distance, and its proof picks the wrong level.
  Section 3 has the misprints found in the sources, E80, E82 and E84.

## 2. Results from prior work and how the paper uses them

Allman et al. 2023 and TINNiK are papers of this collection, and this paper cites both. Their own results, by their own
proofs, are in [`src/AllmanEtAl2023/`](../../src/AllmanEtAl2023) and [`src/TINNiK/`](../../src/TINNiK), with their audits
in [`../AllmanEtAl2023/REPORT.md`](../AllmanEtAl2023/REPORT.md) and [`../TINNiK/REPORT.md`](../TINNiK/REPORT.md). The rows
below on them are the forms this paper uses.

### Proved in `src/External/`, and in the other papers of the collection

| Result | Where the paper uses it | Source | Theorem |
| --- | --- | --- | --- |
| Taxa on one side of a cut edge are exchangeable for quartets with the other taxa on the other side | §3, Prop. 5.1 | Ané et al. 2024 | [`External.AneEtAl2024.exchangeability`](../../src/External/AneEtAl2024/Exchangeability.lean#L28) |
| A network isn't anomalous under common inheritance | Remark 3.3 | Ané et al. 2024, Proposition 12 | [`External.AneEtAl2024.proposition12`](../../src/External/AneEtAl2024/Proposition12.lean#L156), [`External.AneEtAl2024.proposition12_class2`](../../src/External/AneEtAl2024/Proposition12.lean#L163); in a strict form, [`Phylogenetics.RootedNetwork.nmscCF_lt_rho_one`](../../src/Basic/RhoOne.lean#L27) |
| Limit laws and densities of the T3 and T1 tests at the singularity | Line 1017; the T3 test of Remark 8.3 and E38 | Mitchell et al. 2019, Propositions 4.1, 4.2, 5.1, 5.2 | [`External.MitchellAllmanRhodes2019.proposition4_1`](../../src/External/MitchellAllmanRhodes2019/T3Limit.lean#L481), [`External.MitchellAllmanRhodes2019.proposition4_2`](../../src/External/MitchellAllmanRhodes2019/T3Density.lean#L839), [`External.MitchellAllmanRhodes2019.proposition5_1`](../../src/External/MitchellAllmanRhodes2019/T1Limit.lean#L1092), [`External.MitchellAllmanRhodes2019.proposition5_2`](../../src/External/MitchellAllmanRhodes2019/T1Limit.lean#L1079), for the trinomial |
| (3.1) under gene duplication and loss, without incomplete lineage sorting | Remark 3.4 | Legried et al. 2021 | [`External.LegriedEtAl2021.eq5`](../../src/External/LegriedEtAl2021/Theorem1.lean#L868), [`External.LegriedEtAl2021.eq7`](../../src/External/LegriedEtAl2021/Theorem1.lean#L896), [`External.LegriedEtAl2021.theorem1`](../../src/External/LegriedEtAl2021/Theorem1.lean#L1106), in a model with any law on each edge; [`Remark34.remark3_4_displays`](../../src/ECToBlob/Remark34.lean#L52) |
| Average distances across a cut edge | §10 | Rhodes et al. 2025, Proposition 6.1, item 1 | [`SumOfPairs.spForward_averageDist`](../../src/ECToBlob/SumOfPairs.lean#L923) |
| ASTRAL's expected score can favour a tree that isn't displayed | In passing | Dinh, Baños 2025, Theorem 1, Corollary 2 | [`External.DinhBanos2025.theorem1`](../../src/External/DinhBanos2025/Theorem1.lean#L599), [`External.DinhBanos2025.corollary2`](../../src/External/DinhBanos2025/Theorem1.lean#L629) (Section 7) |
| Theorem 1, adapted to the measure of §5 on networks whose blob vertices have degree at most 3 | Prop. 5.1 | Allman et al. 2023, Theorem 1 | [`ECToBlob.adaptedAllmanTheorem1`](../../src/ECToBlob/Section5.lean#L151), through [`AllmanEtAl2023.exists_reduction_of_blobDegree`](../../src/AllmanEtAl2023/Reduction.lean#L951) (see Assumed, below) |
| The consistency of NANUQ and TINNiK, which the argument of Theorem 8.2 strengthens | Remark 8.3 | NANUQ, Proposition 9 and Theorem 36; TINNiK, Theorem 4 | [`External.AllmanBanosRhodes2019.proposition9`](../../src/External/AllmanBanosRhodes2019/Proposition9.lean#L1501), [`External.AllmanBanosRhodes2019.theorem36`](../../src/External/AllmanBanosRhodes2019/Proposition9.lean#L1636); [`TINNiK.theorem4_explicit`](../../src/TINNiK/Basic.lean#L657), [`TINNiK.theorem4T3_explicit`](../../src/TINNiK/T3.lean#L492) |
| CF-detectability, the B-quartet inference rule and the quartet metrization, behind TINNiK's Theorem 4 | Remark 8.3, through TINNiK's Theorem 4 | Allman et al. 2023, Theorems 1, 2, 3 and Corollary 1; Rhodes 2020, Theorem 2 | [`AllmanEtAl2023.CFDetectable`](../../src/AllmanEtAl2023/CFDetectable.lean), [`AllmanEtAl2023.closure_sound`](../../src/AllmanEtAl2023/Basic.lean#L732), [`AllmanEtAl2023.closure_complete`](../../src/AllmanEtAl2023/Basic.lean#L724); [`External.Rhodes2020.theorem2`](../../src/External/Rhodes2020/Theorem2.lean#L776), [`External.Rhodes2020.quartetWeight_ge_two`](../../src/External/Rhodes2020/Theorem2.lean#L868) |
| Theorem 5.1: a cut edge's split induces cut-edge splits on quartets, and the converse | NANUQ Proposition 9, in its proof here, the forward direction | Huber et al. 2025 | [`External.HuberEtAl2025.theorem5_1_forward`](../../src/External/HuberEtAl2025/Theorem51.lean#L25); both directions, [`External.HuberEtAl2025.theorem5_1`](../../src/External/HuberEtAl2025/Theorem51.lean#L168), the converse by another proof (Section 7) |

The rows on Mitchell et al. prove the source's conclusions for the model used, by the central limit theorem, not from van der Vaart's Theorem 16.7
(Section 7). The Lean form of exchangeability is on arbitrary networks with inheritance correlation.

### What was read

| Source | Cited by | Read? |
| --- | --- | --- |
| Mitchell et al. 2019 | TINNiK, ECToBlob | Read: the arXiv TeX and PDF (1806.08458v1), not the journal's text |
| NANUQ (Allman et al. 2019) | ECToBlob Remark 8.3; TINNiK, Allman et al. 2023 | Read: arXiv v1 and the PMC text. The references behind its Proposition 9, which prints no proof, weren't read |
| Ané et al. 2024 | TOB-QMC, ECToBlob | Read: the bioRxiv text |
| Legried et al. 2021 | ECToBlob Remark 3.4 | Read: the conference version's bioRxiv text, in the copy on NSF PAR. The journal's text wasn't read |
| Markin, Eulenstein 2021; Hill et al. 2022 | ECToBlob Remark 3.4 | Their statements only (Theorem 2 of each), in the arXiv versions |
| Rhodes et al. 2025; Xu, Ané 2023; Allman et al. 2022 | ECToBlob §10 | Read in the arXiv versions, for the statements that §10 refers to |
| Dinh, Baños 2025 | TOB-QMC, ECToBlob | Read: the PMC text (PMC11934270), not its supplement's simulations |
| Huber et al. 2025 | TOB-QMC Lemma 2; used here by NANUQ's Proposition 9 | Read: the PMC text (PMC12394373), including the proof of its Theorem 5.1, which the converse here doesn't follow (Section 7) |
| Rhodes 2020 | TINNiK, whose Theorem 4 Remark 8.3 uses; Allman et al. 2023, for Theorem 4 | Read for TINNiK. For Allman et al.'s Theorem 4 the library's Steel theorem is used, so neither it nor Semple and Steel 2005 was read for that citation |

### Assumed

Nothing from the literature, and no theorem here is conditional. ECToBlob's adaptation of Allman et al.'s Theorem 1 is also proved: [`ECToBlob.adaptedAllmanTheorem1`](../../src/ECToBlob/Section5.lean#L151), for its measure (`δ₀ + μ` on hybrid lengths) on networks whose blob vertices have degree at most 3. It goes beyond the source's proof, and the paper only sketches it ("checking the argument"). The witness lies on the face where all hybrid lengths are `0`, since under the degree condition the two cut arcs of the reduction can be taken to be tree arcs ([`AllmanEtAl2023.exists_reduction_of_blobDegree`](../../src/AllmanEtAl2023/Reduction.lean#L951)). Assumption 1 of ECToBlob is the paper's own hypothesis of Theorem 8.2, not a cited result, and appears as [`ECToBlob.Assumption1Forward`](../../src/Basic/Defs.lean#L213) and [`ECToBlob.Assumption1Converse`](../../src/Basic/Defs.lean#L219).

### Standard facts used without citation

| Fact | Where | In the formalization |
| --- | --- | --- |
| Central limit theorem, in dimension 2 by Cramér–Wold | The star and T1 limits below | Mathlib's `tendstoInDistribution_inv_sqrt_mul_sum_sub`; [`Phylogenetics.Trinomial.tendstoInDistribution_normalizedSums`](../../src/Basic/Testing/Trinomial/CLT.lean#L110) |
| Wilks-type limits: χ²₂ for the star test, the T1 mixture | §5.2, §8 | Proved directly for the trinomial: [`Phylogenetics.Trinomial.tendsto_star_lrt`](../../src/Basic/Testing/Trinomial/Tests.lean#L369), [`Phylogenetics.Trinomial.tendsto_t1`](../../src/Basic/Testing/Trinomial/Tests.lean#L418) |
| Weak law for empirical frequencies | Cor. 3.6, Theorem 8.2 | [`Phylogenetics.QuartetTests.tendsto_iidProb_freq`](../../src/Basic/Testing/Tails.lean#L434) |
| Absorption of Kingman's coalescent; Tavaré's formula | The NMSC's definition | The library `Phylogenetics`, [`Phylogenetics/Coalescent/`](https://github.com/vltanh/lean4-phylogenetics/tree/f1a3592dee6e3f7d5e7a68a0695ac457de23d2de/Phylogenetics/Coalescent) |
| Compatible splits have a common tree | §3 | [`Phylogenetics.splice_isUnrootedTree`](https://github.com/vltanh/lean4-phylogenetics/blob/f1a3592dee6e3f7d5e7a68a0695ac457de23d2de/Phylogenetics/Tree/Splice.lean#L118) |

### Gaps in the proofs of cited results

Proving the cited results by their sources' arguments exposed these. All the results hold, except NANUQ's Theorem 36 as
printed. E80, E82 and E84 in Section 3 are the later points on these sources.

- **NANUQ (Allman, Baños, Rhodes 2019), Theorem 36.** False as printed at the level of the distance: line 2023 of our text says binary networks have `p_i ≠ 1/3`, but Definition 8 calls the centroid tree-like, and a binary level-1 network with a `3₂`-cycle has CF `(1/3, 1/3, 1/3)` at positive lengths ([`External.AllmanBanosRhodes2019.ThreeTwo.centroid_N₃`](../../src/External/AllmanBanosRhodes2019/ThreeTwoCycle.lean#L1024)). There the star test rejects with probability tending to `β` only, so for no levels does the distance reach the theoretical one with probability tending to 1 ([`External.AllmanBanosRhodes2019.not_tendsto_of_centroid`](../../src/External/AllmanBanosRhodes2019/NANUQ.lean#L1120), [`External.AllmanBanosRhodes2019.ThreeTwo.not_theorem36AsPrinted_N₃`](../../src/External/AllmanBanosRhodes2019/ThreeTwoCycle.lean#L1089)). The formal statement [`External.AllmanBanosRhodes2019.Theorem36AsPrinted`](../../src/External/AllmanBanosRhodes2019/NANUQ.lean#L1454) has the printed hypothesis and quantifiers, at `ρ = 0`, and concludes at the distance, which is the reduction its proof makes at the start, not the printed conclusion on the network inferred. On `N₃` that conclusion fails too, by an argument by hand, not in Lean: on the star class the distance is constant, and its circular decomposition has no split `ab|cd`. The theorem holds with no centroid CF, which holds off a null set ([`External.AllmanBanosRhodes2019.theorem36_generic`](../../src/External/AllmanBanosRhodes2019/Proposition9.lean#L1664)). Its proof says "we choose `α_m` to be the minimum of the `α'_m`", which must be the maximum, since a test rejects when the p-value is below the level ([`External.AllmanBanosRhodes2019.exists_levels`](../../src/External/AllmanBanosRhodes2019/NANUQ.lean#L660)); and `α'_m` is not a number, since the law of the test depends on the estimated `φ̂`. Steps 4 and 5, to the splits graph, are not formalized.
- **Ané et al. 2024, Definition 2.** It calls a class-1 quartet anomalous when `P(T₁|N) < 1/3`, so that a CF at `1/3` is not anomalous, while TINNiK and TOB-QMC count it as anomalous. Consequences in E36.

### Does the paper use each cited result correctly?

| Cited result | Where | Verdict |
| --- | --- | --- |
| Ané et al. exchangeability | §3, §5 | Correct |
| Allman et al. Theorem 1, adapted | Prop. 5.1 | Correct. The paper only says "checking the argument"; the adaptation is proved here (E5) |
| Ané et al. Definition 2 and Example 1 | Remark 3.3 | Needs the strict reading: E36 |
| Legried et al. 2021 | Remark 3.4 | Correct, for both samplings ([`Remark34.remark3_4_single`](../../src/ECToBlob/Remark34.lean#L41), [`Remark34.remark3_4_multi`](../../src/ECToBlob/Remark34.lean#L68)) |
| Dinh, Baños 2025 | In passing | Correct ([`External.DinhBanos2025.theorem1_displayed`](../../src/External/DinhBanos2025/Theorem1.lean#L1120)) |
| Mitchell et al. Theorem 3.1 | Lines 1017–1020 | Line 1017 excepts the centroid from the limit, as the source does, and the next sentence doesn't repeat the exception (E13) |

Remark 3.4 cites Markin and Eulenstein 2021 and Hill, Legried and Roch 2022 (Theorem 2 of each) for the case with
incomplete lineage sorting, under the DLCoal model. Neither that model nor these results are formalized
([`src/ECToBlob/Remark34.lean`](../../src/ECToBlob/Remark34.lean)), and no proof here uses them.

## 3. Errors and gaps in the paper

The findings are numbered across the collection: E1–E17, E35–E38, E41 and E68 here, E80, E82 and E84 on the sources the paper uses, and E34 for the typos.

**E1. Remark 3.2.** "Any multifurcation in a potential maximizer can be arbitrarily resolved to increase the MQS score" is
loose when some probabilities vanish: an arbitrary resolution need not increase the score. Some resolution with positive
probability does, since the three probabilities on a quartet sum to 1. [`ECToBlob.remark3_2`](../../src/ECToBlob/Section3.lean#L569) proves the remark.

**E2. Equation (3.3) is false as printed.** Summing over representative tuples counts a quartet once for each choice of
representatives of the other blocks, so a quartet in distinct blocks is overcounted by the product of the sizes of the
unused blocks. With blocks of sizes `(2,1,1,1,1)` and all cross-block CFs `1/3`, the left side is `3` and the right side `10/3` on a binary `T`; a multifurcating species tree with one positive-length cherry realizes these CFs, at all valid parameters under the NMSC ([`ECToBlob.Equation33Counterexample.not_equation33Printed`](../../src/ECToBlob/Equation33Counterexample.lean#L239)). This refutes
the identity, not Theorem 3.1. Repair, along the paper's route: weight each local term by the product of its four block sizes,
divide by `∏ᵢ |Xᵢ|`, and use the weighted local objective for the splicing. Lean: [`ECToBlob.equation3_3`](../../src/ECToBlob/Section3.lean#L86), [`ECToBlob.localWeight`](../../src/ECToBlob/Section3.lean#L187),
[`ECToBlob.theorem3_1`](../../src/ECToBlob/Section3.lean#L488). The identity also needs the `Xᵢ` to cover `X`, as the paper's do. The side claims at lines 497–500 and 504–507, and lines 501–504 (a splice of maximizers maximizes `f_m`), are false for the printed, unweighted `f̃_m`: with block sizes `(4,1,1,1,1)` and abstract weights, the maximizers of `f_m` and of the unweighted `f̃_m` can differ (not shown realized by a network). All hold for the weighted objective. Lines 461–463 also use, unstated, that the quartets a tree displays determine its splits ([`Phylogenetics.subset_of_forall_displays`](https://github.com/vltanh/lean4-phylogenetics/blob/f1a3592dee6e3f7d5e7a68a0695ac457de23d2de/Phylogenetics/Tree/Splits.lean#L748)), and lines 504–507 that a side of a maximizer outside `T_B` refines one multifurcation ([`Phylogenetics.exists_mem_multifurcations_isBlockUnion`](https://github.com/vltanh/lean4-phylogenetics/blob/f1a3592dee6e3f7d5e7a68a0695ac457de23d2de/Phylogenetics/Tree/Detach.lean#L230)).

**E3. Corollary 3.6, proof.** "The probability that `f̂` and `f` have different sets of optima → 0" is false when `f` has
ties: `f(a)=f(b)=0`, `fₙ(a)=1/(n+1)`, `fₙ(b)=0` converges uniformly with different argmax sets for every `n`, and ties do
occur here. The result holds: the empirical optima lie among the expected ones, by the gap to non-maximizers, which is what
the corollary says. Lean: [`ECToBlob.corollary3_6`](../../src/ECToBlob/Section3.lean#L1483).

**E4. Theorem 4.1, proof.** "The minimality of `|E|` implies that the funnel of `a₁` can only attach to `G̃₃` on the
`ã₂`-side" is elliptical: it needs the comparability of the sets `E(z, …)` of cut edges for different replacements. Going from
one funnel to all of them at once needs that funnels on opposite sides of an edge share no node, which is true and unstated. The "two
3-blobs" and "chain of 2-blobs" remarks are used only in part: the chain on `G̃₃` gives the comparability ([`ECToBlob.quartetCuts_subset_or_subset`](../../src/ECToBlob/Section4Funnels.lean#L1204)), and funnels on opposite sides share no node ([`ECToBlob.Induces.attach_funnels`](../../src/ECToBlob/Section4Funnels.lean#L301)).
Also unstated: that the `ã₂`-side is the component off the arc of `E` nearest `ã₂`, and that `b̃₁`, `b̃₂` lie in one component of `G̃₃ \ E`. The result holds.

**E5. Proposition 5.1.** Its proof rests on an adaptation of Allman et al.'s Theorem 1 stated by "checking the argument", and on atoms at hybrid length 0 that the source's measure doesn't have. The sketch is filled in here, and the claim holds, including on the face where all hybrid lengths vanish ([`ECToBlob.adaptedAllmanTheorem1`](../../src/ECToBlob/Section5.lean#L151), [`ECToBlob.proposition5_1`](../../src/ECToBlob/Section5.lean#L184)). The two other facts are proved for every network: [`Phylogenetics.NMSC.cut_alternatives`](https://github.com/vltanh/lean4-phylogenetics/blob/f1a3592dee6e3f7d5e7a68a0695ac457de23d2de/Phylogenetics/NMSC/Exchangeability.lean#L550), [`Phylogenetics.NMSC.trivial_uniform`](https://github.com/vltanh/lean4-phylogenetics/blob/f1a3592dee6e3f7d5e7a68a0695ac457de23d2de/Phylogenetics/NMSC/Exchangeability.lean#L771).

**E6. Lemma 6.1, proof.** `Bon(P) = km` omits the clipping at one in the paper's definition: `{3/4, 3/4}` gives `Bon = 1`, not
`3/2`. The inequality needed still holds. Lean: [`ECToBlob.bonP_le_mul`](../../src/ECToBlob/Section6.lean#L144).

**E7. §6 and Lemma 6.1: Cauchy endpoints.** The Cauchy combination is undefined at `p = 0`, an allowed input by `P ⊂ [0,1)`, and CBC
can feed `Bon = 1` into it. Lean's total tangent is not a reading of the undefined expression, so the Lean definitions
extend `f` continuously at the endpoints. Simultaneous inputs `0` and `1` have no continuous extension, but this case does not
occur on the lemma's domain: `Bon = 1` forces all inputs positive. Lean: [`Phylogenetics.cauchyP`](../../src/Basic/Testing/Combining.lean#L40), [`ECToBlob.cauchyP_pair_le_max`](../../src/ECToBlob/Section6.lean#L182). E11 and the value of CBC in E15 rest on this choice.

**E8. Lemma 6.1, part 1: the domain of the bound.** The lemma gives no domain for `B`, and evaluates it only at `(min P, max P)`, so `η ≤ D`. There the printed `B_{Cauchy,k}(η, D)`, with `f` extended at `0` as in E7, has all the claimed properties, and this is all that Theorem 8.2 uses. Off that domain it does not: it is not non-decreasing in `k` when `η > D` (at `η = 0.9`, `D = 0.1` it is `0.9` at `k = 1` and `0.5` at `k = 2`), and it fails `∼ kη` at `D = 0`. Lean states the lemma on `0 ≤ η ≤ D < 1` with the printed bound ([`ECToBlob.lemma6_1_part1`](../../src/ECToBlob/Section6.lean#L539), [`ECToBlob.cauchyBound`](../../src/ECToBlob/Section6.lean#L274)).

**E9. Algorithm 7.1, Step 10.** The late rule needs a convention when no iteration is rejected. Lean chooses the first iteration, which agrees
with the rule's intent ([`Phylogenetics.selectedIteration`](../../src/Basic/Defs.lean#L105)).

**E10. Theorem 8.2: missing genericity.** The theorem quantifies over any model meeting Assumption 1, whose converse clauses
hold only generically, while the proof invokes "our assumption of generic numerical parameters". For the literal general model
the statement is false: a one-parameter family of laws on a rooted 4-cycle network (Section 4) coincides at one parameter with the law of a
resolved tree, and no levels `α_n`, `β_n` of ECToBlob's algorithm can serve both ([`ECToBlob.Theorem82Literal.not_theorem8_2_literal`](../../src/ECToBlob/Theorem82Literal.lean#L227)). This is not a counterexample under the NMSC. Lean quantifies over
parameters meeting both clauses: [`ECToBlob.theorem8_2`](../../src/ECToBlob/Section8.lean#L714), and [`ECToBlob.theorem8_2_generic`](../../src/ECToBlob/Section8.lean#L751) for the generic form. Corrected as the user
agreed, 2026-10-27.

**E11. Theorem 8.2: boundary laws.** Assumption 1 allows both alternatives of a quartet with a cut-edge split to have probability zero, since (5.2) is a condition on `p₁ > p₂ = p₃` with no positivity, though the source's T1 null is `p₁ ≥ p₂ = p₃ > 0`. Counts on such a quartet are `(n,0,0)` almost surely, so its T1 statistic is `0` and its p-value is exactly `1` for every `n` ([`Phylogenetics.QuartetTests.t1PValue_degenerate`](../../src/Basic/Testing/Limits.lean#L339)). The proof does not cover this: Lemma 6.1 assumes `P ⊂ [0,1)`, and "individual p-values `≤ 1-δ`" fails. The printed Cauchy formula is undefined at `p = 1`, so what the theorem says here depends on how `f` is extended. With Lean's continuous extension (E7), `Cauchy` of positive p-values containing `1` is `1`, and the theorem fails for Cauchy and CBC, as follows. With a finite value of `f(1)`, as in the authors' R code (`tan((0.5-1)π)` is finite in floating point), Lemma 6.1 holds at `D = 1`, the printed proof goes through, and the output on the example below is correct.

Counterexample: the rooted 5-sunlet with arcs `r→v_b, r→v_c, v_b→v_a, v_c→v_d, v_a→h, v_d→h, h→e, v_a→a, v_b→b, v_c→c, v_d→d`, whose tree of blobs is the five-leaf star, under the Displayed Tree model with weights `γ` on `((a,e),b,(c,d))` and `1-γ` on `((a,b),c,(d,e))`. On `abcd`, the
network has the cut split `ab|cd` and the CF is `(1,0,0)`; the other four quartets have CFs `(γ, 1-γ, 0)` up to order, and no cut split or trivial 4-blob. Both directions of Assumption 1 hold, for all `γ ∈ (0,1)`. Take `T₀` with cherries `ab`, `cd`, a resolution of the star. The star test keeps `T₀`, since these CFs are not uniform; `T₀` displays `ab|cd`, so its overall
Cauchy p-value is `1 ≥ α_n`; so for all `α, β` both selection rules return `T₀`, which is not the star. Bon and BBC are not affected, since clipping loses the `1`. A mixture with weights `δ, 1-δ` of a point mass at `T₀` and the uniform law on all 15 binary trees shows that `-log β_n = o(n)` for any
sequence working on trees, so the failure does not depend on the choice of sequences. An independent reader recomputed the law, the network's predicates and Assumption 1, and simulated the Lean definitions on this example and on a second law with the same CF on `abcd` at `n = 500, 5000, 50000`: Cauchy and CBC returned `T₀` in every replicate, and Bon and BBC returned the star at `n ≥ 5000`. The same failure is proved in Lean, on another network, with the cut edge `de|abc` and a 4-cycle: [`FinNetwork.Binary.counterexample`](../../src/ECToBlob/DisplayedTreeExample.lean#L286) at the displayed tree model and all valid parameters, and [`BinaryLaw.not_theorem8_2_without_hpos`](../../src/ECToBlob/BinaryLawExample.lean#L707), that no sequences `α_n`, `β_n` serve all laws of binary gene trees meeting both directions of Assumption 1.

The NMSC has positive CFs ([`Phylogenetics.nmscCF_pos`](https://github.com/vltanh/lean4-phylogenetics/blob/f1a3592dee6e3f7d5e7a68a0695ac457de23d2de/Phylogenetics/NMSC/Basic.lean#L96)), so the paper's main model loses nothing. Lean adds the hypothesis `hpos` to [`ECToBlob.theorem8_2`](../../src/ECToBlob/Section8.lean#L714), for these two variants only and on T1-strict quartets only. So `hpos` is what Lean's extension needs; a finite `f(1)` would need no such hypothesis. The user agreed to this correction on 2026-10-31.

**E12. Theorem 8.2, proof: the witness may be a trivial 4-blob.** "By Corollaries 4.2 and 4.3, `S^a(e)` is empty exactly when `e` is a cut-edge" fails for non-binary
networks: the quartet that those corollaries find may have a trivial 4-blob, on which the T1 null hypothesis holds (`CF = (1/3,1/3,1/3)` is on every T1 null).
So those corollaries do not show that a false edge has a T1-rejecting quartet. The statement holds. Repair: an edge surviving Step 3 has a quartet with no trivial 4-blob in its
multipartition, and from it [`ECToBlob.falseEdge_witness`](../../src/ECToBlob/FalseEdge.lean#L807) produces a quartet in the multipartition of `T₀` with neither a cut-edge split on the wanted bipartition nor a
trivial 4-blob, for all three quartet types at every stage. The formal proof starts from the paper's witness ([`ECToBlob.Deterministic.exists_not_inducedCutSplit_edgeQuartets`](../../src/ECToBlob/Deterministic.lean#L352)); the trivial 4-blob is the case that needs the repair ([`ECToBlob.Deterministic.Run.exists_not_t1Null_of_witness`](../../src/ECToBlob/Deterministic.lean#L375)). Logically Corollary 4.2 is then redundant (Section 11).

**E13. Theorem 8.2, proof: T1 at the centroid (a gap, and a loose sentence behind it).** "Arguing as for the star test" is not enough. Line 1017 excepts the centroid from the `χ²₁` limit, and the next sentence, lines 1018–1020, says "if the expected quartet CFs satisfy the null hypothesis, then the p-value from each individual 4-taxon set has a uniform distribution on [0, 1], asymptotically as the number of genes increases". At the centroid that fails: the fitted T1 p-value is not asymptotically uniform ([`Phylogenetics.QuartetTests.t1PValue_centroid_not_asymptoticallyUniform`](../../src/External/MitchellAllmanRhodes2019/T1Limit.lean#L1241)), though the p-value with the true parameter is ([`Phylogenetics.QuartetTests.t1Tail_t1Stat_asymptoticallyUniform`](../../src/External/MitchellAllmanRhodes2019/T1Limit.lean#L1225)). So Lemma 8.1 does not apply there. Repaired by tightness ([`Phylogenetics.QuartetTests.t1PValue_centroid_tight`](../../src/Basic/Testing/Limits.lean#L377)) and a union bound.

**E14. Theorem 8.2, proof: the threshold.** `B(η_n, 1-δ) ∼ β_n` does not give `< β_n`. Repaired with a constant: `η_n = c₀ · level` ([`ECToBlob.Deterministic.exists_combineBounds`](../../src/ECToBlob/Deterministic.lean#L636)). Only
`b_n = o(n)` is used, not `b_n ∼ log n`, and the asymptotic of `α_n` is unused. "An individual p-value is below `η_n` exactly when the test statistic is above `b_n`" holds for the star test, whose test law is fixed, and "the T1 tests are handled similarly" does not carry it over:
the T1 law depends on an estimated `μ`. Lean bounds the T1 p-value by the `χ²₂` tail at the statistic: with `Z̄ = Z̄₀ + μ`, for `μ ≥ 0` the extra term `½(1 - sgn Z̄)Z̄²` is at most `Z̄₀²`, so the variable is at most `Z² + Z̄₀²` ([`Phylogenetics.QuartetTests.t1Tail_le_chiSqTwoTail`](../../src/Basic/Testing/Tails.lean#L81)).

**E15. Theorem 8.2, proof: bounds on the combined p-values.** "In `(α_n, 1-δ)`" is false on the upper side for Bon, BBC and CBC, even with positive alternatives: `Bon({3/4, 3/4}) = 1`, and then `BBC` is `1`, and so is `CBC` under the extension of E7. Individual p-values `≤ 1-δ` is false when alternatives vanish (E11). Only the
lower bounds are needed, and the upper individual bounds only for Cauchy and CBC. Lean uses [`ECToBlob.minP_le_combineP`](../../src/ECToBlob/Section6.lean#L234) and [`ECToBlob.combineP_le_two_mul`](../../src/ECToBlob/Section6.lean#L249) for Bon and BBC, and Lemma 6.1 for Cauchy and CBC.

**E16. Theorem 8.2, proof: intermediate trees.** The bounds `ε/(2s)` are per edge, but for type `mul` an edge's quartets depend on the random current tree `T_k`, so the union must
run over all states the algorithm could visit. Likewise "our prior choice of `M`" does not cover the sets that the overall `p_k` uses. The formal proof keeps the paper's test-by-test bounds with one test for each pair of a subset `T ⊆ T₀` and an edge of `T`, and one overall test for each `T`, and their number `K` replaces `s` ([`ECToBlob.eventually_t1_all`](../../src/ECToBlob/Section8.lean#L558)).

**E17. Theorem 8.2, proof: Step 3.** "`T_{k₁}` is obtained from `T₀` by contracting precisely those edges that resolve multifurcations" is false as written: on a 4-cycle, `ab|cd` resolves a multifurcation of the tree of blobs and survives Step 3, since its quartet is not uniform. The formal
proof shows what is needed: `T_B` is kept and each kept edge has a non-uniform quartet ([`ECToBlob.Deterministic.Run.treeOfBlobs_subset_afterStar`](../../src/ECToBlob/Deterministic.lean#L264), [`ECToBlob.Deterministic.Run.exists_not_uniform`](../../src/ECToBlob/Deterministic.lean#L281)).

### Remarks, discussion, and smaller points

These came from formalizing what the paper says in passing.

**E35. ECToBlob Remark 8.4: fails on a non-binary network.** The remark says the argument "indicates" that with `T₀` not a resolution the output keeps the cut edges of `T₀` and contracts the others, with no restriction on the network. For binary networks this holds ([`ECToBlob.Coarsening.remark8_4`](../../src/ECToBlob/Remark84.lean#L1560), with `hpos` of Theorem 8.2 for Cauchy and CBC), and on many non-binary pairs too ([`ECToBlob.Coarsening.remark8_4_of_noTrivial`](../../src/ECToBlob/Remark84.lean#L1529)). It fails on the tree `((0,1),2,3,4)` with one internal edge, with `T₀` the binary tree with cherries `02`, `34` and middle taxon `1`, the false edge `34|012` stays, since `34|01` is a cut split and `34|02`, `34|12` are trivial 4-blobs, all on the T1 null, and `34|01` is not uniform, so neither test contracts it ([`ECToBlob.Coarsening.Counterexample.not_remark8_4`](../../src/ECToBlob/Remark84.lean#L2306), for all options, at the sequences of Theorem 8.2, for a law on nine gene trees meeting Assumption 1 in the form of [`ECToBlob.theorem8_2`](../../src/ECToBlob/Section8.lean#L714); and [`ECToBlob.Coarsening.Counterexample.not_remark8_4_nmsc`](../../src/ECToBlob/Remark84.lean#L2358) for the NMSC itself, at every valid `θ` and `ρ ∈ [0,1]`). The limit on any network and any `T₀` is [`ECToBlob.Coarsening.limitTree`](../../src/ECToBlob/Remark84.lean#L780), and [`ECToBlob.Coarsening.limitTree_eq_inter_iff`](../../src/ECToBlob/Remark84.lean#L1148) is the exact criterion for the remark on a pair `(N, T₀)`. The cut edges of `T₀` stay in all cases, and every edge of the limit is compatible with the tree of blobs. The remark's wording is hedged ("indicates", "should").

**E36. ECToBlob Remark 3.3 and Proposition 5.1: "no anomalous quartets" must be strict.** Lines 402–404 cite Ané et al. for: the NMSC satisfies (3.1) when the network has no anomalous quartets and cut edges have positive lengths. The remark quotes no definition, and the paper's own use is strict (line 722). Their Definition 2 gives only `1/3 ≤ p_ab|cd`. At a `3₂`-cycle with hybrid arcs of length 0, arcs `s₁, s₂` on the other side of the cycle, whose sum is their `s₀`, and cut edge `t = log(1 + (1-ρ)γ(1-γ)(1-e^{-(s₁+s₂)}))`, all three CFs equal `1/3`: nothing is anomalous in that sense, (3.1) fails, and all three binary trees tie, so the conclusion of Theorem 3.1 fails too ([`ECToBlob.Remark33Counterexample.remark3_3_strict`](../../src/ECToBlob/Remark33Counterexample.lean#L683), for any `0 ≤ ρ < 1`). The parameters with a tie form a null set. Under TINNiK's definition, or TOB-QMC's, the claim holds. Lean's [`IsTQuartetNonanomalous`](../../src/Basic/Defs.lean#L254) and [`NoAnomalousQuartets`](../../src/Basic/Defs.lean#L190) are strict.

**E37. ECToBlob Theorem 8.2: "any model" and the displayed tree model (a step that fails; the conclusion depends on the variant).** With the convention of lines 289–293 that a star contributes `(1/3, 1/3, 1/3)`, a trivial 4-blob under the displayed tree model gives counts `(n/3, n/3, n/3)` on every sample and p-values exactly `1` ([`ECToBlob.pValues_of_hasTrivialFourBlob`](../../src/ECToBlob/Remark33.lean#L719)). So line 1065, "each individual p-value is uniformly distributed as n → ∞", is false there ([`ECToBlob.not_asymptoticallyUniform_starPValue`](../../src/ECToBlob/Remark33.lean#L732)), and Lemma 8.1 doesn't apply. [`ECToBlob.theorem8_2`](../../src/ECToBlob/Section8.lean#L714) takes binary gene trees, so it doesn't reach this model on non-binary networks. For Bon and BBC the conclusion holds on every network, binary or not, since the repaired proof uses only the lower bound on p-values: [`DisplayedTree.theorem8_2_displayed`](../../src/ECToBlob/DisplayedTree.lean#L410), with the converse of Assumption 1 as a hypothesis at the parameters, as in Theorem 8.2. For Cauchy and CBC it fails, through E11, and so under Lean's extension of the Cauchy transform at `p = 1` (E7): if an internal edge of the tree of blobs survives Step 3, the output is the tree after Step 3 at every level `α ≤ 1` ([`DisplayedTree.ectoblob_eq_afterStar`](../../src/ECToBlob/DisplayedTree.lean#L577)), with counterexamples on a binary network on five taxa ([`FinNetwork.Binary.counterexample`](../../src/ECToBlob/DisplayedTreeExample.lean#L286)) and on a non-binary one on six, with a trivial 4-blob and a polytomy ([`FinNetwork.NonBinary.counterexample`](../../src/ECToBlob/DisplayedTreeExample.lean#L564)).

**E38. ECToBlob §10: "the T1 test has greater power".** The null of T1 is nested in that of T3 ([`Phylogenetics.QuartetTests.isT3Null_of_isT1Null`](../../src/External/MitchellAllmanRhodes2019/T3Test.lean#L1230)), and the T3 statistic is at most the T1 statistic ([`Phylogenetics.QuartetTests.t3Stat_le_t1Stat`](../../src/External/MitchellAllmanRhodes2019/T3Test.lean#L538)). The p-values compare the other way at the maximum likelihood topology, since there the statistics agree and the T3 reference law is lower: [`Phylogenetics.QuartetTests.t3PValue_lt_t1PValue`](../../src/External/MitchellAllmanRhodes2019/T3Test.lean#L1253), and [`Phylogenetics.QuartetTests.exists_t3PValue_lt_t1PValue`](../../src/External/MitchellAllmanRhodes2019/T3Test.lean#L1262) at counts `(3,2,1)`. At a fixed level, if T1 rejects `s` and T3 doesn't, then `s` isn't the maximum likelihood topology. The sentence holds in the sense that at a CF on another half-line T1 rejects and T3 doesn't ([`Phylogenetics.QuartetTests.t1_rejects_where_t3_cannot`](../../src/External/MitchellAllmanRhodes2019/T3Test.lean#L1299)).

**E41. ECToBlob §3 and §7: what the observations need.**

- Lines 363–369 say that for `γ`s near 0 and 1, MQS infers displayed trees, on a set of positive measure, and that ties occur between. All three hold for the NMSC at every `ρ` ([`ECToBlob.Section3Observations.not_isNull_selectsDisplayed`](../../src/ECToBlob/Section3Observations.lean#L788), [`ECToBlob.Section3Observations.exists_tie_of_displayedTrees`](../../src/ECToBlob/Section3Observations.lean#L941), and [`ECToBlob.Section3Observations.fourCycle_not_isNull`](../../src/ECToBlob/Section3Observations.lean#L1114), [`ECToBlob.Section3Observations.fourCycle_exists_tie`](../../src/ECToBlob/Section3Observations.lean#L1104) on a 4-cycle). "Select a displayed tree" needs that tree binary: optimal trees are binary, so otherwise the statement is about its resolutions. "Sufficiently close" needs positive length on each internal edge of the displayed tree, which holds on binary networks and when all lengths are positive; it fails on `N₁` of Figure 1 with both hybrid arcs of length 0, where all CFs are `1/3` ([`ECToBlob.Section3Observations.isMQSOptimal_treeAC_of_length_zero`](../../src/ECToBlob/Section3Observations.lean#L1235)).
- Lines 922–935 on time. "The `k`th edge contracted might be incident to as many as `4 + k` other internal edges" holds as an upper bound ([`ECToBlob.Counts.card_incidentSides_le`](../../src/ECToBlob/Counts.lean#L410)) when `k` counts all edges contracted so far, Step 3's included, and the `4 + k` includes pendant edges; a step may contract several tied edges. It is not attained for `k > (s - 8)/2`. The printed sum `∑_{k=0}^{s-3}` has one term too many. And the `O(s⁵)` for `bi` and `quad` assumes p-values are stored: as written the algorithm recomputes at each step, which is `O(s⁶)` for every type. Storing them is sound ([`ECToBlob.Counts.edgeT1P_eq_of_qType_ne_mul`](../../src/ECToBlob/Counts.lean#L496)). The bounds are [`ECToBlob.Counts.ectoblobOperations_le`](../../src/ECToBlob/Counts.lean#L828), [`ECToBlob.Counts.ectoblobOperationsMul_le`](../../src/ECToBlob/Counts.lean#L849), [`ECToBlob.Counts.ectoblobOperationsRecomputing_le`](../../src/ECToBlob/Counts.lean#L869).

**E68. ECToBlob line 1422: "any valid test" (a loose sentence).** "The input star test p-values could come from any valid test of a multifurcation, and the input T1 test p-values from any test that the 4-taxon subnetwork has the desired edge split." The sentence says "could", and proving it shows what that takes. Validity isn't all that Theorem 8.2's proof uses: the tests need power at the levels `α_n`, `β_n`, and for Cauchy and CBC the null p-values must stay away from `1`. [`Framework.AdequateTests`](../../src/ECToBlob/Framework.lean#L252) lists what the proof needs, and [`Framework.consistency_ectoblobBy`](../../src/ECToBlob/Framework.lean#L327) is the conclusion for any tests meeting it. The passage after it, lines 1424–1432 on sum-of-pairs distances, is [`SumOfPairs.consistency_sumOfPairs`](../../src/ECToBlob/SumOfPairs.lean#L665), for the tests built there, with Bon and BBC.

### Points on cited works

These are about the sources that the paper cites or uses, and none affects a result of the paper. Section 2 has the
earlier points on them.

**E80. Legried et al. 2021, line 229 of the NSF PAR copy (a misprint).** After their (4), "and similarly for P′[q = ac|bd]" should be `ad|bc`. The result holds: [`External.LegriedEtAl2021.eq5`](../../src/External/LegriedEtAl2021/Theorem1.lean#L868).

**E82. Mitchell et al. 2019, Appendix C (a misprint, and a loose word).** In the first display for model T1, the second line of `d/dx G₁` repeats that of `G₂`; it should be `(1/2π) e^{-x²/2} √(2π) ½(1 + erf(μ₀/√2))`. And the appendix calls `x` the distance to the mean, where it is the distance to the half-line. Proposition 5.2 holds as printed: [`External.MitchellAllmanRhodes2019.proposition5_2`](../../src/External/MitchellAllmanRhodes2019/T1Limit.lean#L1079).

**E84. NANUQ, Definition 11 (a misprint).** "For appropriately chosen 1 ≤ p < q < n" must allow `p = q`, since a circular split can have a single taxon on one side. It affects no result, and the definition isn't in the Lean.

### Typos

**E34.**

- ECToBlob, proof of Corollary 4.3: `∪_{j′≠i} B_{j′}` should be `∪_{j′≠j} B_{j′}`.
- ECToBlob, §7: "Theorem 3.6" for Corollary 3.6; §10: "Theorem 4.2 and Theorem 4.3" for Corollaries.
- Mitchell et al. 2019: "Proposition 16.7" for van der Vaart's Theorem 16.7, in one place.
- Rhodes 2020, the display before (2), and (2), (3): the sums over `C_v^i` run to `k` or `k(v)`, though there are `k - 2` blocks; (2) prints `v on p` for `P`.

## 4. Missing hypotheses

| Where | Missing hypothesis | Counterexample without it | In the formalization |
| --- | --- | --- | --- |
| ECToBlob Theorem 8.2 (E10), agreed | Parameters outside the exceptional sets of Assumption 1's converse | A rooted 4-cycle network with arcs `s→r, s→d, r→u, r→v, u→h, v→h, u→a, v→b, h→c`, whose tree of blobs is a star, with the model `(1/2, 1/4+h(t), 1/4-h(t))`, `h(t) = (t-1)/(8(1+(t-1)²))`, with `t` the length of the arc `s→r`: at `t = 1` its law equals that of a resolved tree `ab\|cd`, which has the same `T₀`, so no levels `α_n`, `β_n` of ECToBlob's algorithm serve both ([`ECToBlob.Theorem82Literal.not_theorem8_2_literal`](../../src/ECToBlob/Theorem82Literal.lean#L227)) | [`ECToBlob.Assumption1Forward`](../../src/Basic/Defs.lean#L213), [`ECToBlob.Assumption1Converse`](../../src/Basic/Defs.lean#L219) hold at the given law; [`ECToBlob.theorem8_2_generic`](../../src/ECToBlob/Section8.lean#L751) |
| ECToBlob Theorem 8.2 (E11), agreed | For Cauchy and CBC only: positive alternatives on T1-strict quartets | The 5-sunlet of E11, under the continuous extension of `f` at `p = 1`; see E11 | `hpos` in [`ECToBlob.theorem8_2`](../../src/ECToBlob/Section8.lean#L714) |
| ECToBlob (3.3) (E2) | Block-size weights; the blocks cover `X` (they do in the paper) | E2; for the cover, `X = {a,b,c,d}`, `P = {{a}}`, `s = ab\|cd`, `w` the indicator of `s` | [`ECToBlob.equation3_3`](../../src/ECToBlob/Section3.lean#L86) |
| ECToBlob Theorem 8.2, "any model" (E37) | For Cauchy and CBC, under Lean's extension at `p = 1`: positive alternatives, which the displayed tree model lacks. The formal [`ECToBlob.theorem8_2`](../../src/ECToBlob/Section8.lean#L714) is on binary gene trees, a narrowing | [`FinNetwork.Binary.counterexample`](../../src/ECToBlob/DisplayedTreeExample.lean#L286), [`FinNetwork.NonBinary.counterexample`](../../src/ECToBlob/DisplayedTreeExample.lean#L564) | [`ECToBlob.theorem8_2`](../../src/ECToBlob/Section8.lean#L714); for Bon and BBC on the displayed tree model on any network, [`DisplayedTree.theorem8_2_displayed`](../../src/ECToBlob/DisplayedTree.lean#L410) |
| ECToBlob Remark 8.4 (E35) | Binary network, or [`ECToBlob.Coarsening.limitTree_eq_inter_iff`](../../src/ECToBlob/Remark84.lean#L1148) | E35 | [`ECToBlob.Coarsening.remark8_4`](../../src/ECToBlob/Remark84.lean#L1560) |
| ECToBlob Remark 3.3 (E36) | The strict reading of "no anomalous quartets" | E36 | [`ECToBlob.remark3_3_nmsc`](../../src/ECToBlob/Remark33.lean#L294) |
| NANUQ Theorem 36 (Section 2) | No centroid CF | [`External.AllmanBanosRhodes2019.ThreeTwo.not_theorem36AsPrinted_N₃`](../../src/External/AllmanBanosRhodes2019/ThreeTwoCycle.lean#L1089) | [`External.AllmanBanosRhodes2019.theorem36`](../../src/External/AllmanBanosRhodes2019/Proposition9.lean#L1636) |

## 5. Redundant hypotheses

The Lean statements leave these out, except where the last column says otherwise and in [`src/MainResults/ECToBlob.lean`](../../src/MainResults/ECToBlob.lean), which keeps the paper's hypotheses.

| Result | Hypothesis that is not needed | Why | Lean |
| --- | --- | --- | --- |
| ECToBlob Theorem 4.1 | `A₁ ∩ A₂ = ∅`, `B₁ ∩ B₂ = ∅` | Only `A ∩ B = ∅` and the cover are used | [`ECToBlob.theorem4_1`](../../src/ECToBlob/Section4.lean#L55) |
| ECToBlob Proposition 5.1, forward clauses | Degree 2 or 3 in blobs | Exchangeability holds on every network | [`ECToBlob.proposition5_1`](../../src/ECToBlob/Section5.lean#L184), where the condition enters only through the generic clause |
| ECToBlob (3.3) | Nonempty blocks | | [`ECToBlob.equation3_3`](../../src/ECToBlob/Section3.lean#L86) |
| ECToBlob Remark 3.3, common inheritance | The standing conditions on parameters other than the cut arc's length | The bound holds at boundary parameters: each displayed tree gives it | [`Phylogenetics.RootedNetwork.one_sub_exp_le_sub_nmscCF_rho_one`](https://github.com/vltanh/lean4-phylogenetics/blob/f1a3592dee6e3f7d5e7a68a0695ac457de23d2de/Phylogenetics/NMSC/DisplayedTreeModel.lean#L1231), [`ECToBlob.remark3_3_common`](../../src/ECToBlob/Remark33.lean#L302) |
| ECToBlob Remark 3.3, displayed tree model | Positive lengths on cut edges | The model is topological | [`ECToBlob.remark3_3_displayed`](../../src/ECToBlob/Remark33.lean#L519) |

Of the cited results:

| Result | Hypothesis that is not needed | Why | Lean |
| --- | --- | --- | --- |
| Huber et al. Theorem 5.1 | Binary, and semi-directed, in both directions | | [`External.HuberEtAl2025.theorem5_1_forward`](../../src/External/HuberEtAl2025/Theorem51.lean#L25), [`External.HuberEtAl2025.theorem5_1`](../../src/External/HuberEtAl2025/Theorem51.lean#L168) |
| Ané et al. Proposition 12 | A 4-taxon binary metric network | The argument works on four taxa of any network at weak parameters | [`External.AneEtAl2024.proposition12`](../../src/External/AneEtAl2024/Proposition12.lean#L156) |
| Mitchell et al. Proposition 4.2 | `φ ∈ (0, 1]` | The printed density is the density for all `φ < 3/2` | [`External.MitchellAllmanRhodes2019.proposition4_2`](../../src/External/MitchellAllmanRhodes2019/T3Density.lean#L839) |

## 6. How the formalization reads the paper

### Readings specific to this paper

- **Gene trees in ECToBlob's Theorem 8.2** are binary ([`ECToBlob.BinaryGeneTree`](../../src/Basic/Defs.lean#L224)), which is what the proof and the NMSC give; ECToBlob's unrooted topological gene trees need not be. So the theorem covers the NMSC at any `ρ`, and, for Bon and BBC, the Displayed Tree model when all displayed trees are binary: on a cut split that model's CF is `(1,0,0)`, so the hypothesis `hpos` fails for Cauchy and CBC. The Displayed Tree model on any network, whose gene trees need not be binary, is [`DisplayedTree.theorem8_2_displayed`](../../src/ECToBlob/DisplayedTree.lean#L410), for Bon and BBC (E37).
- **[`CutExchangeable`](https://github.com/vltanh/lean4-phylogenetics/blob/f1a3592dee6e3f7d5e7a68a0695ac457de23d2de/Phylogenetics/Network/Quartets.lean#L67)** is the form in which ECToBlob's Theorem 3.1 uses its condition 2; [`ECToBlob.pendantChainInvariant_cutExchangeable`](../../src/ECToBlob/Section3.lean#L1363) derives it from the literal form, and [`ECToBlob.pendantChainInvariant_nmscCF`](../../src/ECToBlob/Remark33.lean#L1395), [`ECToBlob.pendantChainInvariant_displayedCF`](../../src/ECToBlob/Remark33.lean#L1436) prove the literal form for the models of Remark 3.3.
- **ECToBlob's Lemma 6.1** gives no domain for its bound. Lean states it on `0 ≤ η ≤ D < 1`, the values `(min P, max P)` reach, with the printed bound (E8).
- **Lemma 8.1** of ECToBlob is proved for functions of iid finite samples, with `δ` chosen first. This is the form its use needs, and is stronger in the order of quantifiers.
- **ECToBlob's §10, sentence by sentence.** "May increase power" (line 1411) and "might" (line 1433) claim nothing. That quartets are used for several edges is [`InPassing.exists_quartet_of_two_edges`](../../src/ECToBlob/InPassing.lean#L303). Lines 1419–1423 are E68. Combining edge p-values under CBC fails on one law meeting Assumption 1 ([`BinaryLaw.OnBinary.not_consistency_edge_combination_cbc`](../../src/ECToBlob/BinaryLawExample.lean#L1106)); on the general NMSC it isn't treated. On sum-of-pairs distances, the analogue of Assumption 1 is a hypothesis ([`SumOfPairs.SPForward`](../../src/ECToBlob/SumOfPairs.lean#L401), [`SumOfPairs.SPConverse`](../../src/ECToBlob/SumOfPairs.lean#L406)), the forward direction is [`SumOfPairs.spForward_averageDist`](../../src/ECToBlob/SumOfPairs.lean#L923) for the displayed tree model, on any network, and the converse is [`SumOfPairs.Instance.spConverse_averageDist`](../../src/ECToBlob/SumOfPairs.lean#L1136) on one binary network. On Log-det distances, a single Markov model on a tree is additive ([`LogDet.logDetDist_path`](../../src/ECToBlob/LogDet.lean#L165)) and a mixture need not be ([`LogDet.not_logDet_additive_mixture`](../../src/ECToBlob/LogDet.lean#L243)). "May be non-uniform" at lines 1435–1440 is [`InPassing.tendsto_prob_le_given_gt`](../../src/ECToBlob/InPassing.lean#L319), for a selection chosen for the purpose; the selection by MQS isn't treated. Post-selection p-values are future work there, and nothing is stated.
- **Remark 3.4.** Legried et al.'s model is [`External.LegriedEtAl2021.SpeciesTree`](../../src/External/LegriedEtAl2021/Model.lean#L41), a rooted binary species tree with a law on each edge of what one copy becomes, and gene trees as the addresses of their leaves in each species. The birth-death law isn't defined here, so the results hold for every such law, which their proofs allow. [`External.LegriedEtAl2021.displays_treeOfBlobs_iff`](../../src/External/LegriedEtAl2021/Bridge.lean#L556) and [`External.LegriedEtAl2021.displays_pickTree_iff`](../../src/External/LegriedEtAl2021/Bridge.lean#L408) connect it with the library's trees and networks, and [`Remark34.remark3_4_displays`](../../src/ECToBlob/Remark34.lean#L52) is (3.1) as the hypothesis of Theorem 3.1. The question the remark leaves open, on networks, has no model in any source, so [`Remark34.OpenQuestion`](../../src/ECToBlob/Remark34.lean#L100) has the model as a parameter.
- **The displayed tree model** of ECToBlob is [`Phylogenetics.RootedNetwork.displayedSides`](https://github.com/vltanh/lean4-phylogenetics/blob/f1a3592dee6e3f7d5e7a68a0695ac457de23d2de/Phylogenetics/NMSC/DisplayedTreeModel.lean#L183) with [`ECToBlob.displayedTreeDist`](../../src/ECToBlob/Remark33.lean#L406). Remark 3.2's "no impact on the score" holds for the raw probabilities of resolved topologies ([`ECToBlob.remark3_2_no_impact`](../../src/ECToBlob/Remark33.lean#L606)), and under the convention of lines 289–293 each new quartet adds `1/3` ([`ECToBlob.quartetScore_displayedCF_of_resolution`](../../src/ECToBlob/Remark33.lean#L619)), the reason for the remark's last sentence, [`ECToBlob.isBinaryTree_of_displayedCF_maximizer`](../../src/ECToBlob/Remark33.lean#L541).

### Readings shared with TOB-QMC and TINNiK

- **Networks** are directed multigraphs with named arcs ([`Phylogenetics.RootedNetwork`](https://github.com/vltanh/lean4-phylogenetics/blob/f1a3592dee6e3f7d5e7a68a0695ac457de23d2de/Phylogenetics/Network/Defs.lean#L30)), rooted, with parallel arcs allowed. The papers' semi-directed networks are handled through the rooted networks they come from; TOB-QMC's `N⁻` is `N` with a root.
- **Unrooted trees** are families of sides of splits ([`Phylogenetics.IsUnrootedTree`](https://github.com/vltanh/lean4-phylogenetics/blob/f1a3592dee6e3f7d5e7a68a0695ac457de23d2de/Phylogenetics/Tree/Defs.lean#L49): [`unroot`](https://github.com/vltanh/lean4-phylogenetics/blob/f1a3592dee6e3f7d5e7a68a0695ac457de23d2de/Phylogenetics/Hierarchy/Defs.lean#L43) of a hierarchy). The tree of blobs `T_B(N)` is the family of nonempty proper sides of cut edges ([`Phylogenetics.treeOfBlobs`](https://github.com/vltanh/lean4-phylogenetics/blob/f1a3592dee6e3f7d5e7a68a0695ac457de23d2de/Phylogenetics/Network/Quartets.lean#L40)).
  Bridges to the graphs: [`Phylogenetics.RootedNetwork.blobTree`](https://github.com/vltanh/lean4-phylogenetics/blob/f1a3592dee6e3f7d5e7a68a0695ac457de23d2de/Phylogenetics/Network/TreeOfBlobs.lean#L127) is the graph with blobs contracted; [`Phylogenetics.RootedNetwork.mem_treeOfBlobs_iff_blobTree`](https://github.com/vltanh/lean4-phylogenetics/blob/f1a3592dee6e3f7d5e7a68a0695ac457de23d2de/Phylogenetics/Network/TreeOfBlobs.lean#L213) says the two agree on splits, and [`Phylogenetics.RootedNetwork.blobTree_isTree`](https://github.com/vltanh/lean4-phylogenetics/blob/f1a3592dee6e3f7d5e7a68a0695ac457de23d2de/Phylogenetics/Network/TreeOfBlobs.lean#L134) that it is a tree. The root of `blobTree` is not deleted. Allman et al.'s [`AllmanEtAl2023.Trd`](../../src/AllmanEtAl2023/BlobDefinitions.lean#L422) is the reduced graph, and [`AllmanEtAl2023.Bridges.splits_Trd`](../../src/AllmanEtAl2023/Bridges.lean#L353) says its splits are this family.
- **Induced networks**: `HasCutSplitOn Y A` says that one arc of the subgraph of ancestors of `Y` is the only arc of it crossing a vertex set that meets `Y` in `A`; [`Phylogenetics.RootedNetwork.hasCutSplitOn_iff_separates`](https://github.com/vltanh/lean4-phylogenetics/blob/f1a3592dee6e3f7d5e7a68a0695ac457de23d2de/Phylogenetics/Network/Cuts.lean#L253) gives the domination form, and [`Phylogenetics.RootedNetwork.hasCutSplitOn_iff_inducedNetwork_hasCutSplit`](https://github.com/vltanh/lean4-phylogenetics/blob/f1a3592dee6e3f7d5e7a68a0695ac457de23d2de/Phylogenetics/Network/Induced.lean#L857) proves it equal to the cut splits of the graph `inducedNetwork` (LSA restriction, then suppression). The later papers use this network, whose CFs are those of `N` on four taxa ([`Phylogenetics.NMSC.nmscCF_inducedNetwork`](https://github.com/vltanh/lean4-phylogenetics/blob/f1a3592dee6e3f7d5e7a68a0695ac457de23d2de/Phylogenetics/NMSC/Induced.lean#L76)). Allman et al.'s own results use their Definition 6, [`AllmanEtAl2023.induced`](../../src/AllmanEtAl2023/InducedNetwork.lean#L296), which keeps what lies above the LSA; the two have the same cut-edge splits ([`AllmanEtAl2023.Bridges.induced_hasCutSplit_iff`](../../src/AllmanEtAl2023/Bridges.lean#L210)).
- **Quartet trees** are unordered pairs of cherries; [`Phylogenetics.Displays`](https://github.com/vltanh/lean4-phylogenetics/blob/f1a3592dee6e3f7d5e7a68a0695ac457de23d2de/Phylogenetics/Tree/Defs.lean#L84).
- **The NMSC** on arbitrary networks is an order-free sum over histories ([`Phylogenetics.geneTreeDist`](https://github.com/vltanh/lean4-phylogenetics/blob/f1a3592dee6e3f7d5e7a68a0695ac457de23d2de/Phylogenetics/NMSC/Defs.lean#L94)), the product over vertices and arcs of the joint law of the forests at the bottom and top of each arc. One lineage per taxon. `ρ` is the inheritance correlation of TOB-QMC's supplement, in closed form as an exchangeable Pólya law ([`Phylogenetics.allocationWeight`](https://github.com/vltanh/lean4-phylogenetics/blob/f1a3592dee6e3f7d5e7a68a0695ac457de23d2de/Phylogenetics/NMSC/Defs.lean#L54), proved equal to the urn in [`Phylogenetics.allocationWeight_eq_urn`](https://github.com/vltanh/lean4-phylogenetics/blob/f1a3592dee6e3f7d5e7a68a0695ac457de23d2de/Phylogenetics/NMSC/Inheritance.lean#L232)). [`Phylogenetics.sum_geneTreeDist`](https://github.com/vltanh/lean4-phylogenetics/blob/f1a3592dee6e3f7d5e7a68a0695ac457de23d2de/Phylogenetics/NMSC/Basic.lean#L51) and [`Phylogenetics.geneTreeDist_support`](https://github.com/vltanh/lean4-phylogenetics/blob/f1a3592dee6e3f7d5e7a68a0695ac457de23d2de/Phylogenetics/NMSC/Basic.lean#L64) validate it: a law on binary rooted trees.
- **Sampling**: `Phylogenetics.iidProb dist n Ev` is the finite sum over samples, proved equal to the product measure ([`Phylogenetics.iidProb_eq_pi`](../../src/Basic/Testing/IID.lean#L264)).
- **Test statistics** follow the implementation (MSCquartets, Mitchell et al.). The T1 p-value uses the plug-in `min(1, φ̂)` at all counts; small-count procedures of software are not modelled. Star: likelihood ratio by default, Pearson as `StarTest.pearson`.
- **Parameters**: `MetricData` has lengths on all arcs and hybridization parameters; `IsMetric` requires positivity on tree edges, and `γ` strictly between 0 and 1 where a reticulation has two parents.
- **The T3 test**: [`Phylogenetics.t3Stat`](../../src/External/MitchellAllmanRhodes2019/T3Test.lean#L56) is the minimum over topologies of [`t1Stat`](../../src/Basic/Testing/Defs.lean#L63), and [`Phylogenetics.t3Var`](../../src/External/MitchellAllmanRhodes2019/T3Test.lean#L63) the random variable of Mitchell et al.'s Proposition T3approx, whose squared distance to the three half-lines is [`Phylogenetics.QuartetTests.t3Var_eq_min_sqDistHalfLine`](../../src/External/MitchellAllmanRhodes2019/T3Test.lean#L172) (a step they leave as "it can be shown"); at `Z = 0` their formula gives 0, harmless since `Z = 0` has probability zero. The sources differ at the centroid: Mitchell et al.'s null includes it, TINNiK's Fig. 2 caption excludes it, and its anomalous condition `q ≥ 1/3` counts it as anomalous. Lean follows each: [`Phylogenetics.IsT3Null`](../../src/External/MitchellAllmanRhodes2019/T3Test.lean#L51) follows Mitchell et al., `TINNiK.NoAnomalousQuartets` TINNiK.
- **Counts of operations** are counts of what the paper's claims are about, tied to the definitions by `Finset.card` of what a step enumerates or by an instrumented run. There is no machine model, so these aren't running times. NANUQ's count takes NeighborNet and the Circular Network algorithm as parameters ([`External.AllmanBanosRhodes2019.nanuqOperations_le`](../../src/External/AllmanBanosRhodes2019/Counts.lean#L35)).
- **Missing taxa.** TINNiK and NANUQ state no model. Here gene trees are independent draws from the NMSC, each with taxa `on m i` fixed in advance. A gene tree on a subset is the restriction of a full gene tree ([`Phylogenetics.partialCount_restrict`](../../src/Basic/Testing/MissingTaxa.lean#L69)), by sampling consistency. Each set of four taxa is on more and more gene trees ([`TINNiK.Covers`](../../src/TINNiK/MissingTaxa.lean#L97)). NANUQ's level is below `1` only eventually there ([`External.AllmanBanosRhodes2019.theorem36_missing`](../../src/External/AllmanBanosRhodes2019/MissingTaxa.lean#L196)).
- **NANUQ's own terms.** Its Proposition 9 is proved on four taxa of a whole network; [`External.AllmanBanosRhodes2019.Quartet.proposition9_source`](../../src/External/AllmanBanosRhodes2019/QuartetClass.lean#L563) states it in the source's terms, through [`External.AllmanBanosRhodes2019.Quartet.hasThreeTwoCycle_iff`](../../src/External/AllmanBanosRhodes2019/Quartet.lean#L764), [`External.AllmanBanosRhodes2019.Quartet.networkClass_eq_tree_iff`](../../src/External/AllmanBanosRhodes2019/QuartetClass.lean#L180) and [`External.AllmanBanosRhodes2019.Quartet.networkClass_eq_cycle_iff`](../../src/External/AllmanBanosRhodes2019/QuartetClass.lean#L215), and [`External.AllmanBanosRhodes2019.Quartet.networkDistance_eq_sourceDistance`](../../src/External/AllmanBanosRhodes2019/QuartetClass.lean#L459) is its Definition 22. [`External.AllmanBanosRhodes2019.theorem36_output`](../../src/External/AllmanBanosRhodes2019/Proposition9.lean#L1652) has the steps after the distance, NeighborNet and the Circular Network algorithm, as a visible hypothesis.

### Corrections of statements

Listed here for reference: E2 (3.3); E10 and E11, Theorem 8.2, and its binary gene trees (E37). Of results stated in
passing or only cited: E35, Remark 8.4; E36, Remark 3.3; NANUQ's Theorem 36.

## 7. Departures from the paper's proofs

The last column but one says why, and says so plainly when a departure isn't forced. Mechanics and representation with the same content aren't listed: paths as sets of arcs, for instance, and a concrete value for "sufficiently long".

| Result | The paper's argument | The formalization's | Why | E-item |
| --- | --- | --- | --- | --- |
| ECToBlob Theorem 3.1 | Local objective `f̃_m`; (3.3) | Weighted by the block sizes; the claims on all maximizers hold in that form ([`ECToBlob.innerSum_le_of_isBlockAttachment`](../../src/ECToBlob/Section3.lean#L219), [`ECToBlob.quartetScore_le_pullTree_of_starPart_maximizer`](../../src/ECToBlob/Section3.lean#L287), [`ECToBlob.exists_splice_of_maximizer`](../../src/ECToBlob/Section3.lean#L517)) | Gap: (3.3) is false, and so is the side claim at lines 497–500 for the unweighted objective | E2 |
| ECToBlob Remark 3.2 | "Arbitrarily resolved" increases the score | One chosen split of positive weight | Gap: a resolution of weight zero doesn't increase it | E1 |
| ECToBlob Corollary 3.6 | Equal sets of optima | Containment, by the gap to non-maximizers | Gap | E3 |
| ECToBlob Theorem 4.1 | The induced subnetwork has two 3-blobs, joined by chains of 2-blobs and cut edges | The same on `G̃₄`, without suppression, with degree counted by cut edges with a taxon beyond them ([`ECToBlob.IsTwoBlobs.exists_three_cuts`](../../src/ECToBlob/Section4Funnels.lean#L1007), [`ECToBlob.IsTwoBlobs.exists_two_blob`](../../src/ECToBlob/Section4Funnels.lean#L1109)) | Not forced. On `G̃₄` the arc from the root to the LSA can be a third cut edge | E4 |
| ECToBlob Proposition 5.1 | Quarnet by quarnet, "checking the argument" of Allman et al. | On `N` directly, for each 4-set, with the witness on the face where hybrid lengths are 0; "no anomalous quartets" read strictly | The first isn't forced: it avoids pushing this measure, with its atoms, through the map of parameters. The second is forced | E5, E36 |
| ECToBlob Theorem 8.2 | Per-edge bounds, Lemma 8.1 per edge, Corollaries 4.2, 4.3; `B ∼ β_n`; T1 threshold "exactly when"; Step 3 "precisely"; bounds `(α_n, 1-δ)` | The same structure. Repairs: one test per pair (`T ⊆ T₀`, edge of `T`) and `K` tests; [`falseEdge_witness`](../../src/ECToBlob/FalseEdge.lean#L807) in the trivial 4-blob case; a constant `c₀`; tightness at the centroid; the `χ²₂` bound for T1; a weaker Step 3 claim; only the lower bounds; degenerate nulls apart; `2k · min` for Bon and BBC. The statement is on binary gene trees, a narrowing and not a repair (E37). `quad` on a non-binary `T₀` uses the multipartition, and the late rule fixes a value when no `p_k < α` (E9); these fill what the paper leaves undefined | Gaps, except the count: `K` counts sides of edges, and shares of the failure probability differ, which is immaterial and not forced | E10–E17, E37 |
| ECToBlob Theorem 8.2, displayed tree model | Line 1065, uniform p-values, and Lemma 8.1 | Each null p-value is `1` on every sample of positive probability, which gives the lower bound Bon and BBC use ([`DisplayedTree.theorem8_2_displayed`](../../src/ECToBlob/DisplayedTree.lean#L410)) | Forced: line 1065 is false under this model | E37 |

Of the cited results:

| Result | The paper's argument | The formalization's | Why | E-item |
| --- | --- | --- | --- | --- |
| Ané et al. Proposition 12 (cited, for Remark 3.3) | Average over displayed trees, then "greater than or equal to" on a species tree; it prints no formula | The same average, with a strict quantitative bound by conditioning at the arc; hybrid arcs of length 0 by a limit. The source's own proof, the mixture and a convex sum, is [`External.AneEtAl2024.proposition12`](../../src/External/AneEtAl2024/Proposition12.lean#L156), with the class-2 half, on any four taxa | Not forced. `TreeCF.lean` asks for positive lengths | — |
| NANUQ Proposition 9 (cited) | The source prints no proof and cites others | Our own proof, placing lineages at vertices and moving them up by the Markov property, stated on four taxa of a whole network with the CF as a marginal ([`External.AllmanBanosRhodes2019.proposition9`](../../src/External/AllmanBanosRhodes2019/Proposition9.lean#L1501)). The sources it cites weren't read. Part 2, whose bound the source doesn't use either, is [`External.AllmanBanosRhodes2019.proposition9_part2`](../../src/External/AllmanBanosRhodes2019/Proposition9Part2.lean#L725), in the same form | No printed argument to follow | — |
| NANUQ Theorem 36 (cited) | Levels `α'_m = P(W_m > md/2)`, their minimum | The bound `P(χ²₂ > md/2)`, their maximum | Gap: `α'_m` isn't a number, and the minimum is wrong | Section 2 |
| Huber et al. Theorem 5.1, converse (cited, and used by no proof here) | Induction on the non-trivial cut-edge splits, on binary semi-directed networks, with the base case by excellent cycles (its Lemmas 5.2–5.5) | Through domination, on rooted networks of any degree: the arcs dominating a taxon form a chain ([`External.HuberEtAl2025.theorem5_1_converse`](../../src/External/HuberEtAl2025/Theorem51.lean#L124)) | Not forced. It is the shorter route the domination language gives, and the source's would need its cycles | — |
| Mitchell et al. Propositions 4.1, 5.1 (cited) | Read off its Theorem 3.1, and so van der Vaart's Theorem 16.7 | The central limit theorem for the trinomial ([`Phylogenetics.QuartetTests.t3Stat_limitLaw`](../../src/External/MitchellAllmanRhodes2019/T3Limit.lean#L622), [`Phylogenetics.QuartetTests.t1Stat_limitLaw`](../../src/External/MitchellAllmanRhodes2019/T1Limit.lean#L1150)) | Lean lacks that theorem | — |
| Legried et al. 2021 (cited) | Fixes `R` and conditions on the copies there; a function `h(x, y)` and its minimum; Lemmas 1 and 2 apart | One edge at a time, on forests of copies ([`External.LegriedEtAl2021.exch_U`](../../src/External/LegriedEtAl2021/Correlation.lean#L315)); the display in the proof of their Theorem 3, term by term ([`External.LegriedEtAl2021.quartet_dom`](../../src/External/LegriedEtAl2021/Theorem1.lean#L784)); one statement for any weight | Not forced for the first: a single step would need the composite law of a path of edges. The second covers (5) and (7) in `ℝ≥0∞`. The third is forced: their factorization isn't available for `φ n = 1/n` | — |
| Dinh, Baños 2025 (cited) | A semi-directed network with any lengths on pendant and hybrid edges | Rooted on the hybrid edge of `D`, with those lengths `1`, and `ρ = 0` | A restriction of the setting, as the source notes that those lengths have no effect | — |

## 8. What each result depends on

<!-- Generated from scripts/Audit.lean -->

| Result | Lean | Results from prior work used |
| --- | --- | --- |
| ECToBlob Lemma 3.5 | [`ECToBlob.lemma3_5`](../../src/ECToBlob/Section3.lean#L34) | – |
| ECToBlob (3.2) | [`ECToBlob.equation3_2`](../../src/ECToBlob/Section3.lean#L52) | – |
| ECToBlob (3.3), repaired | [`ECToBlob.equation3_3`](../../src/ECToBlob/Section3.lean#L86) | – |
| ECToBlob Theorem 3.1 | [`ECToBlob.theorem3_1`](../../src/ECToBlob/Section3.lean#L488) | – |
| ECToBlob Remark 3.2 | [`ECToBlob.remark3_2`](../../src/ECToBlob/Section3.lean#L569) | – |
| ECToBlob Corollary 3.6 | [`ECToBlob.corollary3_6`](../../src/ECToBlob/Section3.lean#L1483) | – |
| ECToBlob Theorem 4.1 | [`ECToBlob.theorem4_1`](../../src/ECToBlob/Section4.lean#L55) | – |
| ECToBlob Corollary 4.2 | [`ECToBlob.corollary4_2`](../../src/ECToBlob/Section4.lean#L172) | – |
| ECToBlob Corollary 4.3 | [`ECToBlob.corollary4_3`](../../src/ECToBlob/Section4.lean#L204) | – |
| ECToBlob Proposition 5.1 | [`ECToBlob.proposition5_1`](../../src/ECToBlob/Section5.lean#L184) | [`ECToBlob.adaptedAllmanTheorem1`](../../src/ECToBlob/Section5.lean#L151) |
| ECToBlob Lemma 6.1, part 1 | [`ECToBlob.lemma6_1_part1`](../../src/ECToBlob/Section6.lean#L539) | – |
| ECToBlob Lemma 6.1, part 2 | [`ECToBlob.lemma6_1_part2`](../../src/ECToBlob/Section6.lean#L576) | – |
| ECToBlob Lemma 8.1 | [`ECToBlob.lemma8_1`](../../src/ECToBlob/Lemma81.lean#L18) | – |
| ECToBlob Theorem 8.2 | [`ECToBlob.theorem8_2`](../../src/ECToBlob/Section8.lean#L714) | – |
| ECToBlob Remark 3.3, NMSC | [`ECToBlob.remark3_3_nmsc`](../../src/ECToBlob/Remark33.lean#L294) | – |
| ECToBlob Remark 3.3, common inheritance | [`ECToBlob.remark3_3_common`](../../src/ECToBlob/Remark33.lean#L302) | – |
| ECToBlob Remark 3.3, displayed tree model | [`ECToBlob.remark3_3_displayed`](../../src/ECToBlob/Remark33.lean#L519) | – |
| ECToBlob Remark 3.3, the counterexample to its non-strict reading | [`ECToBlob.Remark33Counterexample.remark3_3_strict`](../../src/ECToBlob/Remark33Counterexample.lean#L683) | – |
| ECToBlob Remark 5.2 | [`ECToBlob.Remark52.remark5_2`](../../src/ECToBlob/Remark52.lean#L1082) | – |
| ECToBlob Remark 8.3, NANUQ | [`ECToBlob.remark83_nanuq`](../../src/ECToBlob/Remark83.lean#L102) | – |
| ECToBlob Remark 8.3, TINNiK | [`ECToBlob.remark83_tinnik`](../../src/ECToBlob/Remark83.lean#L235) | [`AllmanEtAl2023.CFDetectable`](../../src/AllmanEtAl2023/CFDetectable.lean), [`AllmanEtAl2023.closure_complete`](../../src/AllmanEtAl2023/Basic.lean#L724), [`AllmanEtAl2023.closure_sound`](../../src/AllmanEtAl2023/Basic.lean#L732), [`External.Rhodes2020.theorem2`](../../src/External/Rhodes2020/Theorem2.lean#L776), [`External.Rhodes2020.quartetWeight_ge_two`](../../src/External/Rhodes2020/Theorem2.lean#L868) |
| ECToBlob Remark 8.4, binary networks | [`ECToBlob.Coarsening.remark8_4`](../../src/ECToBlob/Remark84.lean#L1560) | – |
| ECToBlob Remark 8.4, the counterexample | [`ECToBlob.Coarsening.Counterexample.not_remark8_4`](../../src/ECToBlob/Remark84.lean#L2306) | – |
| ECToBlob Remark 8.4, the counterexample under the NMSC | [`ECToBlob.Coarsening.Counterexample.not_remark8_4_nmsc`](../../src/ECToBlob/Remark84.lean#L2358) | – |
| ECToBlob §3, MQS at a displayed tree, positive measure | [`ECToBlob.Section3Observations.not_isNull_selectsDisplayed`](../../src/ECToBlob/Section3Observations.lean#L788) | – |
| ECToBlob §3, ties | [`ECToBlob.Section3Observations.exists_tie_of_displayedTrees`](../../src/ECToBlob/Section3Observations.lean#L941) | – |
| ECToBlob §10, the line test | [`ECToBlob.Remarks.consistency_line_nmsc`](../../src/ECToBlob/Remarks.lean#L566) | [`ECToBlob.adaptedAllmanTheorem1`](../../src/ECToBlob/Section5.lean#L151) |
| ECToBlob §10, a random T₀ | [`ECToBlob.Remarks.consistency_random_tree`](../../src/ECToBlob/Remarks.lean#L637) | – |
| ECToBlob §10, data splitting | [`ECToBlob.Remarks.consistency_data_splitting`](../../src/ECToBlob/Remarks.lean#L718) | – |
| ECToBlob §10, combining edge p-values | [`ECToBlob.Remarks.consistency_edge_combination`](../../src/ECToBlob/Remarks.lean#L978) | – |
| Rhodes et al. 2025, The analogue of Assumption 1 in the forward direction, for the displayed tree model, on any network | [`ECToBlob.SumOfPairs.spForward_averageDist`](../../src/ECToBlob/SumOfPairs.lean#L923) | – |
| Hoeffding 1963, Hoeffding's inequality | [`ECToBlob.SumOfPairs.iidProb_mean_ge_le`](../../src/ECToBlob/SumOfPairs.lean#L87) | – |
| ECToBlob, Lines 215-216, the other way | [`ECToBlob.Biconnected.blobSetoid_of_isBiconnectedSet`](../../src/ECToBlob/Biconnected.lean#L307) | – |
| ECToBlob, Lines 215-216, one way | [`ECToBlob.Biconnected.isBiconnectedSet_blob`](../../src/ECToBlob/Biconnected.lean#L265) | – |
| ECToBlob, Lines 217-218 | [`ECToBlob.Biconnected.blobSetoid_of_two_biconnected`](../../src/ECToBlob/Biconnected.lean#L338) | – |
| ECToBlob, Lines 1419-1423: the conclusion of Theorem 8.2 for any adequate tests | [`ECToBlob.Framework.consistency_ectoblobBy`](../../src/ECToBlob/Framework.lean#L327) | – |
| ECToBlob, The choice of the BIC (lines 1160-1163) | [`ECToBlob.Framework.theorem8_2_bic`](../../src/ECToBlob/Framework.lean#L464) | – |
| ECToBlob, Theorem 8.2 at other levels (lines 1159-1167) | [`ECToBlob.Framework.theorem8_2_levels`](../../src/ECToBlob/Framework.lean#L440) | – |
| ECToBlob, Under the displayed tree model, Cauchy and CBC return the tree after Step 3 | [`ECToBlob.DisplayedTree.ectoblob_eq_afterStar`](../../src/ECToBlob/DisplayedTree.lean#L577) | – |
| ECToBlob, Theorem 8.2 | [`ECToBlob.DisplayedTree.theorem8_2_displayed`](../../src/ECToBlob/DisplayedTree.lean#L410) | – |
| ECToBlob, Cauchy and CBC on the displayed tree model: a false edge that Step 3 keeps stays | [`ECToBlob.DisplayedTree.tendsto_ectoblob_displayed_zero`](../../src/ECToBlob/DisplayedTree.lean#L622) | – |
| ECToBlob, The counterexample on a non-binary network | [`ECToBlob.FinNetwork.NonBinary.counterexample`](../../src/ECToBlob/DisplayedTreeExample.lean#L564) | – |
| ECToBlob, The counterexample on a binary network | [`ECToBlob.FinNetwork.Binary.counterexample`](../../src/ECToBlob/DisplayedTreeExample.lean#L286) | – |
| ECToBlob, E11 of the report: Theorem 8.2 without its hypothesis on the alternatives is false for Cauchy and CBC, at all ... | [`ECToBlob.BinaryLaw.not_theorem8_2_without_hpos`](../../src/ECToBlob/BinaryLawExample.lean#L707) | – |
| ECToBlob, Lines 1164-1167: we also need o(n) cutoff values | [`ECToBlob.BinaryLaw.OnFour.tendsto_log_beta_of_consistent`](../../src/ECToBlob/BinaryLawExample.lean#L622) | – |
| ECToBlob §10: combining the edge p-values under CBC fails | [`ECToBlob.BinaryLaw.OnBinary.not_consistency_edge_combination_cbc`](../../src/ECToBlob/BinaryLawExample.lean#L1106) | – |
| ECToBlob, Lines 1419-1432: the framework on distances | [`ECToBlob.SumOfPairs.consistency_sumOfPairs`](../../src/ECToBlob/SumOfPairs.lean#L665) | – |
| ECToBlob, The tree of blobs is identifiable from average pairwise distances | [`ECToBlob.SumOfPairs.treeOfBlobs_eq_of_eq`](../../src/ECToBlob/SumOfPairs.lean#L525) | – |
| ECToBlob, The framework on average distances, for the displayed tree model | [`ECToBlob.SumOfPairs.consistency_averageDist`](../../src/ECToBlob/SumOfPairs.lean#L1057) | – |
| ECToBlob, Line 882 (multipartitionQuartets_anti) | [`ECToBlob.InPassing.multipartitionQuartets_anti`](../../src/ECToBlob/InPassing.lean#L1314) | – |
| ECToBlob, Lines 892-893: the combined p-value assessing all edges remaining in T_ki need not monotonically increase ... | [`ECToBlob.InPassing.exists_treeTestP_decreasing`](../../src/ECToBlob/InPassing.lean#L1034) | – |
| ECToBlob, Lines 673-679 | [`ECToBlob.InPassing.Sunlet.not_corollary4_3_with_taxa`](../../src/ECToBlob/InPassing.lean#L286) | – |
| ECToBlob, Line 882 (multipartitionQuartets_subset_bipartitionQuartets) | [`ECToBlob.InPassing.multipartitionQuartets_subset_bipartitionQuartets`](../../src/ECToBlob/InPassing.lean#L1325) | – |
| ECToBlob, Lines 1164-1165: any valid choice needs β_n → 0 | [`ECToBlob.InPassing.tendsto_beta_of_consistent`](../../src/ECToBlob/InPassing.lean#L856) | – |
| ECToBlob, Lines 760-761 | [`ECToBlob.InPassing.tendsto_starS_sub_pearsonS`](../../src/ECToBlob/InPassing.lean#L1262) | – |
| ECToBlob, tendsto_prob_le_given_gt | [`ECToBlob.InPassing.tendsto_prob_le_given_gt`](../../src/ECToBlob/InPassing.lean#L319) | – |
| ECToBlob, The statement of line 728 | [`ECToBlob.InPassing.Assumption1ForAllRho`](../../src/ECToBlob/InPassing.lean#L229) | – |
| ECToBlob, If the sequence of combined p-values is monotone, then both methods agree | [`ECToBlob.InPassing.selected_early_eq_late_of_monotone`](../../src/ECToBlob/InPassing.lean#L171) | – |
| ECToBlob, Lines 293-306 | [`ECToBlob.InPassing.tendsto_inferred`](../../src/ECToBlob/InPassing.lean#L493) | – |
| ECToBlob, Lines 1164-1165: any valid choice needs α_n → 0, in order to fail to reject a true null consistently | [`ECToBlob.InPassing.tendsto_alpha_of_consistent`](../../src/ECToBlob/InPassing.lean#L780) | – |
| ECToBlob, Lines 523-526 | [`ECToBlob.InPassing.exists_oscillating_optimum`](../../src/ECToBlob/InPassing.lean#L656) | – |
| ECToBlob, tendsto_altBon_div | [`ECToBlob.InPassing.tendsto_altBon_div`](../../src/ECToBlob/InPassing.lean#L43) | – |
| ECToBlob, cauchyP_pair | [`ECToBlob.InPassing.cauchyP_pair`](../../src/ECToBlob/InPassing.lean#L75) | – |
| ECToBlob, exists_quartet_of_two_edges | [`ECToBlob.InPassing.exists_quartet_of_two_edges`](../../src/ECToBlob/InPassing.lean#L303) | – |
| ECToBlob, Otherwise, the early method tree is more resolved than the late one | [`ECToBlob.InPassing.selectedIteration_early_le_late`](../../src/ECToBlob/InPassing.lean#L142) | – |
| ECToBlob, exists_early_selected | [`ECToBlob.InPassing.exists_early_selected`](../../src/ECToBlob/InPassing.lean#L119) | – |
| ECToBlob, Lines 1164-1167, both levels: we also need o(n) cutoff values | [`ECToBlob.BinaryLaw.tendsto_log_levels_of_valid`](../../src/ECToBlob/LevelCutoffs.lean#L462) | – |
| ECToBlob, Lines 1164-1167: we also need o(n) cutoff values, for α_n | [`ECToBlob.BinaryLaw.OnBlob.tendsto_log_alpha_of_consistent`](../../src/ECToBlob/LevelCutoffs.lean#L377) | – |
| ECToBlob, A mixture is not additive | [`ECToBlob.LogDet.not_logDet_additive_mixture`](../../src/ECToBlob/LogDet.lean#L243) | – |
| ECToBlob, Tree additivity | [`ECToBlob.LogDet.logDetDist_path`](../../src/ECToBlob/LogDet.lean#L165) | – |
| ECToBlob, A gene family that follows one species tree picked at random | [`ECToBlob.Remark34.remark3_4_mixture`](../../src/ECToBlob/Remark34.lean#L80) | – |
| ECToBlob, Remark 3.4, multiple alleles | [`ECToBlob.Remark34.remark3_4_multi`](../../src/ECToBlob/Remark34.lean#L68) | [`External.LegriedEtAl2021.eq7`](../../src/External/LegriedEtAl2021/Theorem1.lean#L896) |
| ECToBlob, The open question of Remark 3.4 | [`ECToBlob.Remark34.OpenQuestion`](../../src/ECToBlob/Remark34.lean#L100) | – |
| ECToBlob, Remark 3.4, one gene copy | [`ECToBlob.Remark34.remark3_4_single`](../../src/ECToBlob/Remark34.lean#L41) | [`External.LegriedEtAl2021.eq5`](../../src/External/LegriedEtAl2021/Theorem1.lean#L868) |
| ECToBlob, Remark 3.4, on the network of the species tree | [`ECToBlob.Remark34.remark3_4_displays`](../../src/ECToBlob/Remark34.lean#L52) | [`External.LegriedEtAl2021.eq5`](../../src/External/LegriedEtAl2021/Theorem1.lean#L868) |
| ECToBlob, equation (3.3) as printed is false | [`ECToBlob.Equation33Counterexample.not_equation33Printed`](../../src/ECToBlob/Equation33Counterexample.lean#L239) | – |
| ECToBlob, Theorem 8.2 on the literal general model is false | [`ECToBlob.Theorem82Literal.not_theorem8_2_literal`](../../src/ECToBlob/Theorem82Literal.lean#L227) | – |

Of the cited results:

| Result | Lean | Results from prior work used |
| --- | --- | --- |
| Legried et al. 2021, Lemmas 1 and 2 | [`External.LegriedEtAl2021.exch_U`](../../src/External/LegriedEtAl2021/Correlation.lean#L315) | – |
| Legried et al. 2021, Equations (5) and (7) together | [`External.LegriedEtAl2021.quartet_dom`](../../src/External/LegriedEtAl2021/Theorem1.lean#L784) | – |
| Legried et al. 2021, Equation (5) in the proof of Theorem 1 | [`External.LegriedEtAl2021.eq5`](../../src/External/LegriedEtAl2021/Theorem1.lean#L868) | – |
| Legried et al. 2021, Equation (7) in the proof of Theorem 3 | [`External.LegriedEtAl2021.eq7`](../../src/External/LegriedEtAl2021/Theorem1.lean#L896) | – |
| Legried et al. 2021, Theorem 1 of Legried, Molloy, Warnow and Roch | [`External.LegriedEtAl2021.theorem1`](../../src/External/LegriedEtAl2021/Theorem1.lean#L1106) | – |
| Legried et al. 2021, (3.1) on a species tree, as the hypothesis of ECToBlob's Theorem 3.1 | [`External.LegriedEtAl2021.quartetP_lt`](../../src/External/LegriedEtAl2021/Bridge.lean#L828) | [`External.LegriedEtAl2021.eq5`](../../src/External/LegriedEtAl2021/Theorem1.lean#L868) |
| NANUQ, Thus the total time for NANUQ is O(n⁴ m) | [`External.AllmanBanosRhodes2019.nanuqOperations_le`](../../src/External/AllmanBanosRhodes2019/Counts.lean#L35) | – |
| NANUQ, Theorem 36 | [`External.AllmanBanosRhodes2019.theorem36`](../../src/External/AllmanBanosRhodes2019/Proposition9.lean#L1636) | [`External.AllmanBanosRhodes2019.proposition9`](../../src/External/AllmanBanosRhodes2019/Proposition9.lean#L1501) |
| NANUQ, Proposition 9 of NANUQ (proposition9) | [`External.AllmanBanosRhodes2019.proposition9`](../../src/External/AllmanBanosRhodes2019/Proposition9.lean#L1501) | [`External.HuberEtAl2025.theorem5_1_forward`](../../src/External/HuberEtAl2025/Theorem51.lean#L25) |
| NANUQ, Theorem 36 with gene trees on subsets of the taxa (theorem36_missing_of_proposition9) | [`External.AllmanBanosRhodes2019.theorem36_missing_of_proposition9`](../../src/External/AllmanBanosRhodes2019/MissingTaxa.lean#L169) | – |
| NANUQ, Theorem 36 for generic parameters, with gene trees on subsets of the taxa | [`External.AllmanBanosRhodes2019.theorem36_generic_missing`](../../src/External/AllmanBanosRhodes2019/MissingTaxa.lean#L211) | [`AllmanEtAl2023.cfDetectable_generic`](../../src/AllmanEtAl2023/CFDetectable.lean#L24), [`AllmanEtAl2023.CFDetectable`](../../src/AllmanEtAl2023/CFDetectable.lean), [`External.AllmanBanosRhodes2019.theorem36_missing`](../../src/External/AllmanBanosRhodes2019/MissingTaxa.lean#L196) |
| NANUQ, Theorem 36 with gene trees on subsets of the taxa (theorem36_missing) | [`External.AllmanBanosRhodes2019.theorem36_missing`](../../src/External/AllmanBanosRhodes2019/MissingTaxa.lean#L196) | [`External.AllmanBanosRhodes2019.proposition9`](../../src/External/AllmanBanosRhodes2019/Proposition9.lean#L1501) |
| NANUQ, Proposition 9, part 2 | [`External.AllmanBanosRhodes2019.proposition9_part2`](../../src/External/AllmanBanosRhodes2019/Proposition9Part2.lean#L725) | – |
| NANUQ, Definition 5, step 1 (trekArcs) | [`External.AllmanBanosRhodes2019.Quartet.trekArcs`](../../src/External/AllmanBanosRhodes2019/Quartet.lean#L86) | – |
| NANUQ, Definition 4 | [`External.AllmanBanosRhodes2019.Quartet.IsMinusArc`](../../src/External/AllmanBanosRhodes2019/Quartet.lean#L60) | – |
| NANUQ, Definition 20 (qTilde) | [`External.AllmanBanosRhodes2019.Quartet.qTilde`](../../src/External/AllmanBanosRhodes2019/QuartetContract.lean#L422) | – |
| NANUQ, Definition 20 (rhoTilde) | [`External.AllmanBanosRhodes2019.Quartet.rhoTilde`](../../src/External/AllmanBanosRhodes2019/QuartetClass.lean#L38) | – |
| NANUQ, Definition 22 | [`External.AllmanBanosRhodes2019.Quartet.sourceDistance`](../../src/External/AllmanBanosRhodes2019/QuartetClass.lean#L46) | – |
| NANUQ, Proposition 9 of NANUQ (proposition9_source) | [`External.AllmanBanosRhodes2019.Quartet.proposition9_source`](../../src/External/AllmanBanosRhodes2019/QuartetClass.lean#L563) | [`External.HuberEtAl2025.theorem5_1_forward`](../../src/External/HuberEtAl2025/Theorem51.lean#L25), [`External.AllmanBanosRhodes2019.proposition9_part2`](../../src/External/AllmanBanosRhodes2019/Proposition9Part2.lean#L725) |
| NANUQ, Definition 5, step 1 (sTrekEdges) | [`External.AllmanBanosRhodes2019.Quartet.sTrekEdges`](../../src/External/AllmanBanosRhodes2019/QuartetSemidirected.lean#L60) | – |
| Mitchell et al. 2019, The density tends to that of χ²₁ (tendsto_t3Density_atTop) | [`Phylogenetics.QuartetTests.tendsto_t3Density_atTop`](../../src/External/MitchellAllmanRhodes2019/T3Density.lean#L753) | – |
| Mitchell et al. 2019, The density at the singularity | [`Phylogenetics.QuartetTests.t3Density_one`](../../src/External/MitchellAllmanRhodes2019/T3Density.lean#L709) | – |
| Mitchell et al. 2019, Proposition 4.2 (t3Var_density) | [`Phylogenetics.QuartetTests.t3Var_density`](../../src/External/MitchellAllmanRhodes2019/T3Density.lean#L604) | – |
| Mitchell et al. 2019, t3Tail_eq_integral | [`Phylogenetics.QuartetTests.t3Tail_eq_integral`](../../src/External/MitchellAllmanRhodes2019/T3Density.lean#L614) | – |
| Mitchell et al. 2019, The density is continuous in φ₀ | [`Phylogenetics.QuartetTests.continuousOn_t3Density`](../../src/External/MitchellAllmanRhodes2019/T3Density.lean#L791) | – |
| Mitchell et al. 2019, Proposition 4.2 (proposition4_2) | [`External.MitchellAllmanRhodes2019.proposition4_2`](../../src/External/MitchellAllmanRhodes2019/T3Density.lean#L839) | – |
| Mitchell et al. 2019, The p-value with the true parameter at the singularity is asymptotically uniform | [`Phylogenetics.QuartetTests.t3Tail_t3Stat_asymptoticallyUniform`](../../src/External/MitchellAllmanRhodes2019/T3Limit.lean#L707) | – |
| Mitchell et al. 2019, tendstoInDistribution_t3Stat | [`Phylogenetics.QuartetTests.tendstoInDistribution_t3Stat`](../../src/External/MitchellAllmanRhodes2019/T3Limit.lean#L738) | – |
| Mitchell et al. 2019, t3Stat_limitLaw_density | [`Phylogenetics.QuartetTests.t3Stat_limitLaw_density`](../../src/External/MitchellAllmanRhodes2019/T3Limit.lean#L663) | – |
| Mitchell et al. 2019, Proposition 4.1 | [`External.MitchellAllmanRhodes2019.proposition4_1`](../../src/External/MitchellAllmanRhodes2019/T3Limit.lean#L481) | – |
| Mitchell et al. 2019, t3Stat is the likelihood ratio statistic | [`Phylogenetics.QuartetTests.t3Stat_eq_likelihoodRatio`](../../src/External/MitchellAllmanRhodes2019/T3Limit.lean#L582) | – |
| Mitchell et al. 2019, Off the singularity, the limit law of the T3 statistic is χ²₁ | [`Phylogenetics.QuartetTests.t3Stat_limitLaw_of_isT1Strict`](../../src/External/MitchellAllmanRhodes2019/T3Limit.lean#L638) | – |
| Mitchell et al. 2019, The limit law of the T3 statistic at the singularity | [`Phylogenetics.QuartetTests.t3Stat_limitLaw`](../../src/External/MitchellAllmanRhodes2019/T3Limit.lean#L622) | – |
| Mitchell et al. 2019, This distribution is not a χ² | [`Phylogenetics.QuartetTests.map_t3Var_one_ne_chiSqLaw`](../../src/External/MitchellAllmanRhodes2019/T3Limit.lean#L857) | – |
| Mitchell et al. 2019, The T3 statistic is the likelihood ratio statistic of the source | [`Phylogenetics.Trinomial.t3S_eq_likelihoodRatio`](../../src/External/MitchellAllmanRhodes2019/T3Limit.lean#L195) | – |
| Mitchell et al. 2019, The T1 statistic is the likelihood ratio statistic of the source | [`Phylogenetics.Trinomial.t1S_eq_likelihoodRatio`](../../src/External/MitchellAllmanRhodes2019/T1Limit.lean#L697) | – |
| Mitchell et al. 2019, The limit law of the T1 statistic at the boundary point | [`Phylogenetics.QuartetTests.t1Stat_limitLaw`](../../src/External/MitchellAllmanRhodes2019/T1Limit.lean#L1150) | – |
| Mitchell et al. 2019, The T1 test distribution at μ₀ = 0 is ½ χ²₁ + ½ χ²₂ | [`Phylogenetics.QuartetTests.t1Tail_zero`](../../src/External/MitchellAllmanRhodes2019/T1Limit.lean#L563) | – |
| Mitchell et al. 2019, Off the boundary, the limit law of the T1 statistic is χ²₁ | [`Phylogenetics.QuartetTests.t1Stat_limitLaw_of_isT1Strict`](../../src/External/MitchellAllmanRhodes2019/T1Limit.lean#L1162) | – |
| Mitchell et al. 2019, Proposition 5.2 (t1Var_density) | [`Phylogenetics.QuartetTests.t1Var_density`](../../src/External/MitchellAllmanRhodes2019/T1Limit.lean#L438) | – |
| Mitchell et al. 2019, tendstoInDistribution_t1Stat | [`Phylogenetics.QuartetTests.tendstoInDistribution_t1Stat`](../../src/External/MitchellAllmanRhodes2019/T1Limit.lean#L1213) | – |
| Mitchell et al. 2019, tendsto_struveM₀_atTop | [`Phylogenetics.QuartetTests.tendsto_struveM₀_atTop`](../../src/External/MitchellAllmanRhodes2019/T1Limit.lean#L87) | – |
| Mitchell et al. 2019, Proposition 5.1 | [`External.MitchellAllmanRhodes2019.proposition5_1`](../../src/External/MitchellAllmanRhodes2019/T1Limit.lean#L1092) | – |
| Mitchell et al. 2019, t1Stat_limitLaw_density | [`Phylogenetics.QuartetTests.t1Stat_limitLaw_density`](../../src/External/MitchellAllmanRhodes2019/T1Limit.lean#L1185) | – |
| Mitchell et al. 2019, The density at μ₀ = 0 | [`Phylogenetics.QuartetTests.t1Density_zero`](../../src/External/MitchellAllmanRhodes2019/T1Limit.lean#L545) | – |
| Mitchell et al. 2019, Proposition 5.2 (proposition5_2) | [`External.MitchellAllmanRhodes2019.proposition5_2`](../../src/External/MitchellAllmanRhodes2019/T1Limit.lean#L1079) | – |
| Mitchell et al. 2019, With the true parameter, the T1 p-value at the boundary point is asymptotically uniform | [`Phylogenetics.QuartetTests.t1Tail_t1Stat_asymptoticallyUniform`](../../src/External/MitchellAllmanRhodes2019/T1Limit.lean#L1225) | – |
| Mitchell et al. 2019, The density tends to that of χ²₁ (tendsto_t1Density_atTop) | [`Phylogenetics.QuartetTests.tendsto_t1Density_atTop`](../../src/External/MitchellAllmanRhodes2019/T1Limit.lean#L648) | – |
| Mitchell et al. 2019, With the fitted parameter, the T1 p-value at the boundary point is not asymptotically uniform | [`Phylogenetics.QuartetTests.t1PValue_centroid_not_asymptoticallyUniform`](../../src/External/MitchellAllmanRhodes2019/T1Limit.lean#L1241) | – |
| Ané et al. 2024, Proposition 12, class 1 | [`External.AneEtAl2024.proposition12_class1`](../../src/External/AneEtAl2024/Proposition12.lean#L174) | – |
| Ané et al. 2024, Proposition 12 | [`External.AneEtAl2024.proposition12`](../../src/External/AneEtAl2024/Proposition12.lean#L156) | – |
| Ané et al. 2024, Proposition 12, class 2 | [`External.AneEtAl2024.proposition12_class2`](../../src/External/AneEtAl2024/Proposition12.lean#L163) | – |
| Ané et al. 2024, Definition 2 | [`External.AneEtAl2024.IsAnomalousClassTwo`](../../src/External/AneEtAl2024/Proposition12.lean#L65) | – |
| Ané et al. 2024, Definition 1 | [`External.AneEtAl2024.IsAnomalous`](../../src/External/AneEtAl2024/Proposition12.lean#L60) | – |
| Ané et al. 2024, Rule 2 | [`External.AneEtAl2024.rule2`](../../src/External/AneEtAl2024/Rules.lean#L134) | – |
| Huber et al. 2025, Theorem 5.1 | [`External.HuberEtAl2025.theorem5_1`](../../src/External/HuberEtAl2025/Theorem51.lean#L168) | [`External.HuberEtAl2025.theorem5_1_forward`](../../src/External/HuberEtAl2025/Theorem51.lean#L25) |
| Dinh, Baños 2025, Theorem 1 of Dinh, Baños 2025 | [`External.DinhBanos2025.theorem1`](../../src/External/DinhBanos2025/Theorem1.lean#L599) | – |
| Dinh, Baños 2025, Corollary 2 of Dinh, Baños 2025 | [`External.DinhBanos2025.corollary2`](../../src/External/DinhBanos2025/Theorem1.lean#L629) | – |

The route check (`python3 scripts/route_check.py check docs/paper_routes.tsv --accept docs/route_differences.tsv`)
confirms that every proof uses the results that the paper's proof cites, except the differences recorded in
[`docs/route_differences.tsv`](../../docs/route_differences.tsv), each with its reason. Its labels for this paper,
`ecto:…`, are the project's. It merges all the declarations that share a label. The rows of [`docs/paper_routes.tsv`](../../docs/paper_routes.tsv) for
this paper are written by hand, since it has no TeX source.

## 9. Not formalized

What remains is empirical claims and statements that are false. Results of cited sources that no proof here uses are left
out, and aren't listed. A sentence worded as a hope or as future work, with "could", "may", "might" or "we suspect", claims
nothing; Section 6 says how those of §10 are read, and Section 11 has the open questions of the paper.

**Empirical claims.**

- The simulations, the data analyses and measured running times, and the evidence at lines 907–910 that combined p-values aren't monotone. Asymptotic running times are proved as counts of operations, with no machine model (Section 6).

**Statements that are false.** Each row is a statement, read as the row says, with the theorem that shows it fails. What's formalized is the failure, and the true form where there is one (Sections 3 and 4). Loose sentences, and proof steps that fail with the result standing, are in Section 3 and not here: among them E13 and E68.

| Statement | Item | Counterexample |
| --- | --- | --- |
| ECToBlob (3.3) | E2 | [`ECToBlob.Equation33Counterexample.not_equation33Printed`](../../src/ECToBlob/Equation33Counterexample.lean#L239) |
| ECToBlob Theorem 8.2 on the literal general model, for ECToBlob's levels | E10 | [`ECToBlob.Theorem82Literal.not_theorem8_2_literal`](../../src/ECToBlob/Theorem82Literal.lean#L227) |
| ECToBlob Theorem 8.2, for Cauchy and CBC with no hypothesis on the alternatives, under Lean's continuous extension of a formula undefined at `p = 1` | E11 | [`BinaryLaw.not_theorem8_2_without_hpos`](../../src/ECToBlob/BinaryLawExample.lean#L707), [`FinNetwork.Binary.counterexample`](../../src/ECToBlob/DisplayedTreeExample.lean#L286) |
| ECToBlob Remark 3.3, under the non-strict definition it cites | E36 | [`ECToBlob.Remark33Counterexample.remark3_3_strict`](../../src/ECToBlob/Remark33Counterexample.lean#L683) |
| ECToBlob Remark 8.4, what it says the argument "indicates", on a non-binary network | E35 | [`ECToBlob.Coarsening.Counterexample.not_remark8_4`](../../src/ECToBlob/Remark84.lean#L2306), [`ECToBlob.Coarsening.Counterexample.not_remark8_4_nmsc`](../../src/ECToBlob/Remark84.lean#L2358) |
| ECToBlob line 1065 under the displayed tree model | E37 | [`ECToBlob.not_asymptoticallyUniform_starPValue`](../../src/ECToBlob/Remark33.lean#L732) |

**Of cited works.**

- Remark 3.4's sources with incomplete lineage sorting, Markin and Eulenstein 2021 and Hill, Legried and Roch 2022, and
  their DLCoal model (Section 2).
- NANUQ's Steps 4 and 5, to the splits graph of the output. Its Theorem 36 is proved up to the distance (Section 2).

A statement of a cited work that is false as printed:

| Statement | Item | Counterexample |
| --- | --- | --- |
| NANUQ Theorem 36, at the level of the distance | Section 2 | [`External.AllmanBanosRhodes2019.ThreeTwo.not_theorem36AsPrinted_N₃`](../../src/External/AllmanBanosRhodes2019/ThreeTwoCycle.lean#L1089) |

## 10. The paper in the literature

The search was made on 2026-10-31, for this paper together with TOB-QMC and TINNiK, in OpenAlex (works citing TINNiK, TOB-QMC, ECToBlob, Allman et al. 2023, Ané et al. 2024, Huber et al. 2025, "Beyond level-1", Rhodes et al. 2025, Xu and Ané 2023, NANUQ+, and the WABI paper of Dai and Molloy; keyword searches), Crossref (title searches; its `updates` filter for corrections), Europe PMC and PubMed, the bioRxiv API (versions, journal links), the arXiv API, GitHub's search API, the Archive of Formal Proofs, and web search. We kept every correction or counterexample found, and otherwise the works that state or claim a result about the tree of blobs, about which four-taxon information decides it, or about a method that starts from a tree of blobs with a stated guarantee. Empirical studies, reviews and work on other problems were screened by abstract and left out. Each statement below comes from the cited work's abstract or numbered statements, and we say where only the abstract was read. We could not read the full text of Justison et al. (bioRxiv answered HTTP 429), or of Rasschaert's preprint (SSRN answered HTTP 403). Citation indexes lag: OpenAlex lists one work citing ECToBlob, so recent citing work may be missing. Crossref's deposited reference lists add Justison et al. for ECToBlob. A preprint's results are reported as claimed.

### Before the paper

- Solís-Lemus, Ané, [PLoS Genet. 12 (2016)](https://doi.org/10.1371/journal.pgen.1005896) (SNaQ, pseudolikelihood on quartets); Baños, [Bull. Math. Biol. 81 (2019)](https://doi.org/10.1007/s11538-018-0485-4) ([arXiv 2017-11-28](https://arxiv.org/abs/1711.10545); read for its Proposition 7): "every cycle of size at least 4 and every hybrid node in a cycle of size at least 5" of a level-1 network are identifiable from gene tree quartets; Allman, Baños, Rhodes, [NANUQ, Algorithms Mol. Biol. 14 (2019)](https://doi.org/10.1186/s13015-019-0159-2) ([arXiv 2019-05-16](https://arxiv.org/abs/1905.07050)): level-1 inference from quartet hypothesis tests and a quartet intertaxon distance. ECToBlob's Remark 8.3 strengthens NANUQ's consistency result (Section 2).
- Allman, Baños, Mitchell, Rhodes, [J. Math. Biol. 86 (2023), 10](https://doi.org/10.1007/s00285-022-01838-9) ([arXiv 2022-05-06](https://arxiv.org/abs/2205.03466)): "most features of the unrooted tree of blobs" are determined by the distribution of gene quartet topologies, with no assumption on the level, through a B-quartet inference rule. It names the difficulty that this paper, TOB-QMC and TINNiK meet in different ways: a B-quartet of the network can have a cut-edge split on its induced 4-taxon network, "the main obstacle". It is a paper of this collection, with its own audit, [`../AllmanEtAl2023/REPORT.md`](../AllmanEtAl2023/REPORT.md).
- Xu, Ané, [J. Math. Biol. 86 (2023), 12](https://doi.org/10.1007/s00285-022-01847-8) ([arXiv 2021-10-22](https://arxiv.org/abs/2110.11814)): the "distance split tree" built from average pairwise distances refines the tree of blobs, and at level 1 equals the tree of blobs refined to separate polytomies from blobs (Theorem 10). Its Conjecture 9 is taken up by a preprint under Since the paper. ECToBlob's §10 suggests applying its framework to distances.
- Solís-Lemus, Yang, Ané, [Syst. Biol. 65 (2016)](https://doi.org/10.1093/sysbio/syw030): species tree methods can be inconsistent under gene flow. Dinh, Baños, [Mol. Biol. Evol. 42 (2025), msaf049](https://doi.org/10.1093/molbev/msaf049) (published 2025-03-07): under the NMSC, "including nonanomalous scenarios", ASTRAL can produce a tree "that does not correspond to any topology displayed by the true underlying network". ECToBlob cites both as the reason a statement about quartet optima on networks is needed (its [14, 37]).
- Ané, Fogg, Allman, Baños, Rhodes, [J. Math. Biol. 88 (2024), 29](https://doi.org/10.1007/s00285-024-02050-7) ([bioRxiv 2023-08-21](https://doi.org/10.1101/2023.08.18.553582)): under common inheritance "4-taxon networks are never anomalous"; under independent and correlated inheritance simulations find "truly anomalous networks are rare" and many networks close to the anomaly zone. Source of the no-anomaly hypotheses of TOB-QMC and ECToBlob, and of the exchangeability of Section 2.
- Rhodes, Baños, Xu, Ané, [Adv. Appl. Math. 163 (2025), 102804](https://doi.org/10.1016/j.aam.2024.102804) ([arXiv 2024-02-18](https://arxiv.org/abs/2402.11693)): circular orders of outer-labeled planar blobs are identified from 4-taxon subnetworks. Its Corollary 6.6 gives the tree of blobs under the displayed tree model, common inheritance, and independent inheritance with no anomalous quartets. Its Lemma A.1 classifies 4-taxon networks, and ECToBlob says of its Corollary 4.2 that it extends part of that lemma to more taxa.
- Huber, van Iersel, Jones, Moulton, Veenema-Nipius, [Bull. Math. Biol. 87 (2025), 136](https://doi.org/10.1007/s11538-025-01510-5) ([arXiv 2024-08-23](https://arxiv.org/abs/2408.12997)). Theorem 5.1, for binary semi-directed networks, which "does not put any restriction on the level": a nontrivial `A|B` is a cut-edge split exactly when `a₁a₂|b₁b₂` is a cut-edge split of the quarnet for all `a₁, a₂ ∈ A`, `b₁, b₂ ∈ B`. Corollary 5.6: the quarnets determine the blob tree.
- Frohn, Holtgrefe, van Iersel, Jones, Kelk, [J. Comput. Syst. Sci. 152 (2025), 103655](https://doi.org/10.1016/j.jcss.2025.103655) ([arXiv 2024-09-09](https://arxiv.org/abs/2409.06034)). Lemma 1 sharpens Huber et al.'s theorem by fixing `a₁` and `b₁`. Theorem 5 reconstructs the tree of blobs of a binary network of any level in `O(n³)` time from `O(n³)` quarnet-splits, and Proposition 6 gives a lower bound of `Ω(n log n + ℓn)` quarnet-splits at level `ℓ`. For binary networks ECToBlob's Corollary 4.2 is this Lemma 1, as ECToBlob says: it "follows from Lemma 1 of [17], which depends on results in [22]. Our proof is considerably briefer and we relax the binary condition". ECToBlob's Theorem 4.1 goes further in two ways: the network need not be binary, and the partitions `A₁, A₂` and `B₁, B₂` are arbitrary. Huber et al. and Frohn et al. work from exact quarnet information, with no statistical model.
- Allman, Baños, Rhodes, Wicke, NANUQ⁺, [Algorithms Mol. Biol. 20 (2025), 14](https://doi.org/10.1186/s13015-025-00274-w) ([bioRxiv 2024-11-03](https://doi.org/10.1101/2024.10.30.621146); abstract only): given a tree of blobs from TINNiK, resolves its multifurcations to level-1 structure.
- Allman, Ané, Baños, Rhodes, "Beyond level-1", [Bull. Math. Biol. 87 (2025), 166](https://doi.org/10.1007/s11538-025-01545-8) ([arXiv 2025-04-29](https://arxiv.org/abs/2504.21116)): identifiability of classes of galled tree-child networks of any level, by first identifying the tree of blobs. Its Proposition 5.1 states tree of blobs identifiability for binary networks with generic parameters under the displayed tree model and both independent and common inheritance, by "straightforward modifications" of Allman et al. 2023. On the analogue of its Assumption 1 under common or correlated inheritance, ECToBlob's §5 says "We strongly suspect" it holds. Nevins, Claudio, Nguyen, SEQUoIA, [SIAM Undergrad. Res. Online 19 (2026)](https://doi.org/10.1137/26S1843342), turn that result into an algorithm using the NANUQ⁺ and TINNiK functions.
- Holtgrefe, Allman, Baños, van Iersel, Moulton, Rhodes, Wicke, [Bull. Math. Biol. 87 (2025), 168](https://doi.org/10.1007/s11538-025-01549-4) ([arXiv 2025-07-23](https://arxiv.org/abs/2507.17308); [correction, 88 (2026), 26](https://doi.org/10.1007/s11538-025-01564-5): a production error omitted Fig. 12b, results unaffected): features of outer-labeled planar galled level-2 networks distinguishable from displayed quartets, and circular decomposability of an inter-taxon quartet distance (Theorem 4.7). Its outline for an inference method starts from TINNiK's tree of blobs.

What the paper adds. TINNiK ([bioRxiv 2024-04-24](https://doi.org/10.1101/2024.04.20.590418); [`../TINNiK/README.md`](../TINNiK/README.md))
turns the sketch of Allman et al. 2023 into an algorithm with a consistency theorem (Theorem 4) and writes "We know of no
other proposed algorithm for tree of blobs inference from biological data"; ECToBlob describes it as the first. ECToBlob,
like TOB-QMC, adds a different outline: an optimum of the quartet criterion refines the tree of blobs, and edges are then
contracted by quartet tests. We found no earlier statement of that refinement result. Section 2 lists the cited results
the proofs use, including Mitchell et al. 2019 and Rhodes 2020.

### Concurrent work

- TOB-QMC and ECToBlob. First public versions: TOB-QMC [bioRxiv v1, 2025-11-06](https://doi.org/10.1101/2025.11.05.686850), under the title "Fast and accurate tree of blobs reconstruction under the network multispecies coalescent"; ECToBlob [bioRxiv v1, 2026-05-31](https://doi.org/10.64898/2026.05.28.728501). ECToBlob's statement: "When this work was well underway, we learned a different group was independently pursuing the same outline for tree of blobs inference", with its research dated to a residence at ICERM in Fall 2024, and thanks to Dai, Han and Molloy "for sharing their pre-publication work". TOB-QMC v5 does not mention ECToBlob; it thanks Ané, Allman, Baños and Rhodes for feedback.
  - Same result: an optimum of the quartet criterion refines the tree of blobs. TOB-QMC's Theorem 1 assumes the binary NMSC model and T-quartet-nonanomalous networks. ECToBlob's Theorem 3.1 and Corollary 3.6 assume only two conditions on the gene tree distribution, which its Remark 3.3 says hold for the NMSC with no anomalous quartets, for common inheritance and for the displayed tree model.
  - Same question by another method: the contraction step. TOB-QMC applies TINNiK's tests (ECToBlob compares with the T3 option) to `O(n)` four-taxon subsets around an edge and keeps the smallest p-value, with guarantees at level 1 (its Corollary 1, Theorem 2). ECToBlob applies the T1 test to the bipartition, quadripartition or multipartition sets of an edge, combines p-values under dependence, and contracts one step at a time; its Theorem 4.1 and Theorem 8.2 hold at any level. ECToBlob's §10 gives the authors' comparison of the two.
- Englander, Frohn, Gross, Holtgrefe, van Iersel, Jones, Sullivant, [bioRxiv 2025-04-24](https://doi.org/10.1101/2025.04.18.649493) (v4, 2026-07-04; preprint, no journal link in the bioRxiv API; abstract only): claims that under the Jukes-Cantor and Kimura 2-parameter models any two binary semi-directed networks displaying different quartets are distinguishable, so that the tree of blobs is identifiable at any level. Same question on sequence data. ECToBlob cites it.
- Frohn, Holtgrefe, van Iersel, Jones, Kelk, [Ann. Comb. (2026)](https://doi.org/10.1007/s00026-026-00830-0) ([arXiv 2025-11-27](https://arxiv.org/abs/2511.22736); abstract only): sequence length sufficient to reconstruct binary level-1 networks under the CFN model. This is a finite-sample result on sequences at level 1. We found no such bound for the tests of ECToBlob.

### Since the paper

We found no erratum, retraction or published counterexample to a statement of ECToBlob, and no newer version (below). Crossref's `updates` filter returned nothing for the cited papers we checked (Allman et al. 2023, Ané et al. 2024, Huber et al., Frohn et al., "Beyond level-1", NANUQ+, Rhodes et al., Xu and Ané, Dinh and Baños); Europe PMC lists no correction for Allman et al. 2023, Ané et al. 2024, Huber et al., "Beyond level-1" or NANUQ+. Among the works cited in this section, the only correction we found is that to Holtgrefe et al. 2025, for an omitted figure. The errors recorded in Section 3 are this audit's own.

Versions of the paper:

- ECToBlob: the bioRxiv API lists v1 only and no journal link. Crossref's [listing of the SIAM Journal on Life Sciences](https://api.crossref.org/journals/3066-7410/works) (25 works, to 2026-10-14) does not contain it. No version newer than the one audited was found.
- MSCquartets 3.3 implements ECToBlob, with TINNiK and NANUQ+ (Rhodes, Allman, Ané, Baños, Mitchell, Wicke, [Bioinformatics, 2026-10-20](https://doi.org/10.1093/bioinformatics/btag775); [EcoEvoRxiv 2026-06-09](https://doi.org/10.32942/x24d5w); abstract only).

Later work:

- Dai, Molloy, *Is level-1 blob reconstruction under the network multispecies coalescent easy?*, [WABI 2026, LIPIcs 390, 1:1–1:24](https://doi.org/10.4230/LIPIcs.WABI.2026.1) (published 2026-08-27, revised 2026-09-28; [bioRxiv v1 2026-06-10, v2 2026-09-21](https://doi.org/10.64898/2026.06.06.730607)). "Blob reconstruction" here means the inside of a level-1 blob, with the tree of blobs given as input. For binary semi-directed level-1 networks, NetCS finds the hybrid block and circular order of each blob of degree at least 5 (Lemma 1, Theorems 1–3); Corollary 1 states statistical consistency with `O(n log(n) k)` time and `O(n log n)` quarnet queries in its fast mode, matching Frohn et al.'s lower bound. Every statement assumes level 1, and the paper says nothing about treelikeness tests beyond level 1. Its proofs use TOB-QMC's Theorem 2 and the result it numbers Lemma 5 (v5's Lemma 4), and cite TINNiK's Theorem 4 for correctness of the tests on all 4-taxon subsets.
- Justison et al., [bioRxiv 2026-09-04](https://doi.org/10.64898/2026.09.01.748505) (preprint; abstract only): reports by simulation that SNaQ on non-level-1 networks "frequently recovers a tree of blobs compatible with the true network".
- Holtgrefe, Huber, van Iersel, Moulton, [arXiv 2026-10-06](https://arxiv.org/abs/2610.07855) (preprint): claims level-3 semi-directed networks are encoded by their quinnets and that one known counterexample is the only obstruction for quarnets; restates Huber et al.'s Corollary 5.6.
- Cummings, Curiel, Currie, Kagy, Ranasinghe, Rhodes, [arXiv 2026-08-04](https://arxiv.org/abs/2608.03544) (preprint): claims features of level-1 networks identifiable from quintet concordance factors and not from quartets; its Proposition 4.1 claims a limit that holds for `m`-tet concordance factors of every `m`.
- Brits, Holtgrefe, van Iersel, Martin, [arXiv 2026-07-14, v3 2026-08-25](https://arxiv.org/abs/2607.12919) (preprint; abstract and statements scanned): claims that under Jukes-Cantor no network and tree induce the same leaf-pattern distribution unless the network is a tree with 2-blobs.
- Rasschaert, [SSRN 7292396 (2026)](https://doi.org/10.2139/ssrn.7292396) (preprint, DOI registered 2026-08-16; abstract read through Crossref, text not read). Claims a six-taxon binary level-5 counterexample to Xu and Ané's Conjecture 9: a distance split tree with an internal split that "no average-distance-equivalent metric semidirected network of any level" realizes by a cut edge. This is a claimed counterexample to a conjecture, not to a result of the three papers.

Treelikeness beyond level 1. TOB-QMC's oracle asks only whether the network induced on four taxa has a 4-blob. No work we read proves or refutes that this suffices at higher level, on all four-taxon subsets around an edge.

- ECToBlob's §10: "we know of no proof of a stronger result that would justify using the T3 test. Thus the formal justification for TOB-QMC is currently limited to level-1 networks [13, Theorem 2], although simulations suggest it may perform well beyond that case."
- Huber et al.'s Theorem 5.1, Frohn et al.'s Lemma 1 and ECToBlob's Theorem 4.1 hold at any level, but they ask whether a named split `a₁a₂|b₁b₂` is a cut-edge split of the quarnet, which is more than treelikeness: Frohn et al.'s count of a quarnet-split includes identifying "the specific split".
- Allman et al. 2023 and TINNiK work at any level and use resolved topologies with the inference rule, since "the induced network on a B-quartet may or may not have a 4-blob, and can even be a tree". They do not ask about four-taxon sets around an edge of a refinement.
- Dai and Molloy's WABI paper, "Beyond level-1" and Holtgrefe et al. do not address the question. Justison et al., read only by abstract, does not mention it there; its text was not read.

### Formalizations

We found no other formalization of ECToBlob, of the other papers of the collection, or of Huber et al. 2025, in any system. Searches covered GitHub (repository and code search, by language), the [Archive of Formal Proofs](https://www.isa-afp.org/) sitemap, OpenAlex and web search; they see public work only.

- [vltanh/lean4-phylogenetics](https://github.com/vltanh/lean4-phylogenetics) (Lean 4, public, Apache-2.0, created 2026-10-10, by the user who requested this formalization): the multispecies coalescent, Kingman's coalescent on forests with Tavaré's formula, rooted metric level-1 networks and their network coalescent, and the concordance factors of a cycle (Baños 2019). This project imports it, pinned at commit `f1a3592`, for its definitions and general results. Before that, it adapted the library's hierarchy kernel and Kingman modules from commit `06f684e` ([`docs/ADAPTED_SOURCES.md`](../../docs/ADAPTED_SOURCES.md), [`docs/COALESCENT_SOURCES.md`](../../docs/COALESCENT_SOURCES.md)). Its term-based level-1 network coalescent isn't used, and the network coalescent on arbitrary networks, first written for this project, has moved there.
- [vltanh/lean4-camus](https://github.com/vltanh/lean4-camus) (Lean 4, public, created 2026-10-10, same owner): the CAMUS dynamic program for level-1 networks (Willson, Warnow, [Bioinformatics 2026](https://doi.org/10.1093/bioinformatics/btag245)) and the statistical steps of that paper. Surveyed for this project ([`docs/CONFIGURATION.md`](../../docs/CONFIGURATION.md)), not imported.
- [vltanh/lean4-adr11](https://github.com/vltanh/lean4-adr11) (Lean 4, public, created 2026-10-04, same owner): Allman, Degnan, Rhodes 2011, identifying the rooted species tree from unrooted gene trees under the multispecies coalescent. Not used here.
- [SauersML/Descent](https://github.com/SauersML/Descent) (Lean 4, public, created 2026-08-05): "A Lean 4 formalization of genetic theory", with coalescent modules (`Descent/Coalescent/`); a code search of it for "multispecies" returns nothing. Not used here.
- Poindexter, [Zenodo 2026-08-04](https://doi.org/10.5281/zenodo.21802297) (preprint; abstract only), claims a Lean 4 proof of confluence of a saturation procedure for rooted triples. [Paureel/rooted-forest-frontier](https://github.com/Paureel/rooted-forest-frontier) (created 2026-10-16) concerns rooted maximum agreement forests of two trees, and its README says its argument "is not an end-to-end machine-checked runtime theorem". Neither treats networks or the coalescent.
- Coq/Rocq, Isabelle, Agda: GitHub's language-filtered repository searches for "phylogenetic", "phylogeny" and "coalescent" returned nothing. Code search found only incidental uses, of which the closest is [CharlesCNorton/sciuridae-verified](https://github.com/CharlesCNorton/sciuridae-verified), a Rocq formalization of squirrel taxonomy. No entry name in the [Archive of Formal Proofs](https://www.isa-afp.org/) sitemap contains "phylogen" or "coalesc"; we did not search the entries' contents.

## 11. What's next

### Open directions

- **Treelikeness beyond level 1.** ECToBlob's §10 says of the T3 test: "we know of no proof of a stronger result that would justify using the T3 test", and that the formal justification for TOB-QMC stops at level 1; Section 10 finds no published work that settles this. The question: for a network of any level and a refinement `B` of its tree of blobs, does every edge of `B` not in the tree of blobs have a non-treelike 4-taxon set among those around it?
- **Assumption 1 under correlated inheritance.** ECToBlob's §5 says "We strongly suspect Assumption 1 also holds for the NMSC model with common or correlated inheritance". For binary networks at generic parameters, "Beyond level-1" (Proposition 5.1, Section 10) extends the arguments of Allman et al. 2023 to common inheritance, `ρ = 1`, for tree of blobs identifiability, and leaves other `ρ` aside. So what is open is `0 < ρ < 1`, and `ρ = 1` on non-binary networks with ECToBlob's measure. [`AllmanEtAl2023.cfDetectable_generic`](../../src/AllmanEtAl2023/CFDetectable.lean#L24) here covers only `ρ = 0`. [`Phylogenetics.geneTreeDist`](https://github.com/vltanh/lean4-phylogenetics/blob/f1a3592dee6e3f7d5e7a68a0695ac457de23d2de/Phylogenetics/NMSC/Defs.lean#L94) includes `ρ`, and the equalities of the forward clauses are proved for all `ρ` ([`Phylogenetics.NMSC.cut_alternatives`](https://github.com/vltanh/lean4-phylogenetics/blob/f1a3592dee6e3f7d5e7a68a0695ac457de23d2de/Phylogenetics/NMSC/Exchangeability.lean#L550), [`Phylogenetics.NMSC.trivial_uniform`](https://github.com/vltanh/lean4-phylogenetics/blob/f1a3592dee6e3f7d5e7a68a0695ac457de23d2de/Phylogenetics/NMSC/Exchangeability.lean#L771)); the strict inequality of (5.2) is the no-anomaly hypothesis. What is needed is the generic clause: a nonvanishing witness for each 4-taxon network, for each `ρ`.
- **Rates.** All consistency statements here are asymptotic, with no rate. The proof of Theorem 8.2 runs on bounds per test, and could run on one event per quartet (below), so a non-asymptotic statement would follow from a concentration bound on each test, with constants depending on the distance of the CF from the null. What stands in the way is the non-regularity at the centroid and the boundary (E11, E13).
- **Theorem 8.2 for Cauchy and CBC on the boundary.** E11 shows these two variants need positive alternatives on null quartets. The T1 test's own null excludes the boundary in Mitchell et al., while (5.2) does not. A test that behaves at `(1,0,0)` would remove the hypothesis, as would a finite value of the Cauchy transform at `p = 1` (E11). An assumption that excludes the boundary would too, but it would drop the Displayed Tree model from these two variants, since a quartet with a cut-edge split has CF `(1,0,0)` there.
- **Coarsening, when Remark 8.4 fails.** E35 settles the remark, and [`ECToBlob.Coarsening.limitTree`](../../src/ECToBlob/Remark84.lean#L780) is what the algorithm tends to. What should the algorithm do on a non-binary network when `T₀` isn't a resolution? A test that sees the false edge in E35 would have to use quartets beyond those around it.
- **The no-anomaly assumption.** ECToBlob's §10 would like to drop it. For its T1 test this is done, as it says, by the test of the line alone ([`ECToBlob.Remarks.consistency_line_nmsc`](../../src/ECToBlob/Remarks.lean#L566)); it is easier than T1, since the centroid is interior to the line, so E13 disappears. The step that remains is the resolution: without the assumption, an optimum of the quartet criterion need not refine the tree of blobs, and ECToBlob asks for an algorithm that uses the CF entry that differs from the others: "Developing an algorithm to give a resolution of the tree of blobs based on that fact would be valuable". We found no work that does this.
- **Duplication and loss on networks.** ECToBlob's Remark 3.4 says "it remains an open question whether these results hold for duplication and loss models when the species phylogeny has reticulations". No source defines such a model, so [`Remark34.OpenQuestion`](../../src/ECToBlob/Remark34.lean#L100) has it as a parameter, and [`Remark34.remark3_4_mixture`](../../src/ECToBlob/Remark34.lean#L80) is the case of a gene family that follows one tree picked at random, where no reticulation acts on each gene copy separately.

### Simpler proofs

Each of these is the argument of the formal proof, or of an earlier version of it where the item says so, so it is checked in Lean. We found none of them published, in the search of Section 10.

- **ECToBlob Theorem 4.1, in domination language.** An arc `e` induces the split `a₁a₂|b₁b₂` on a quartet exactly when `e` dominates `a₁, a₂` (every root path to them uses `e`) and `b₁, b₂` are not below it, or the reverse ([`Phylogenetics.RootedNetwork.hasCutSplitOn_iff_separates`](https://github.com/vltanh/lean4-phylogenetics/blob/f1a3592dee6e3f7d5e7a68a0695ac457de23d2de/Phylogenetics/Network/Cuts.lean#L253)). So a cut edge of a quartet is a statement about each taxon separately. The paper's minimal choice of quadruple stays; the funnel step becomes the comparability that E4 finds unstated: replacing one taxon by another of its block gives comparable sets of cut arcs, by four cases on how two arcs are oriented, ordered when they dominate a common taxon. This saves the funnels, the graph `G̃₄`, Figure 2 and the "two 3-blobs" remark: about 300 lines against about 1,070. An earlier version of the formal proof did this (in the repository's history); the formal proof now follows the paper.
- **ECToBlob Theorem 8.2, one event.** One event per quartet, Lemma 8.1 applied once to all null quartets, a joint tightness bound at the centroid and growth under the alternative give one `δ` and `c₀` that make every combined test on every possible tree come out right together. So E16 disappears, with no count `K` and no bound `C(s,4)`. And [`ECToBlob.falseEdge_witness`](../../src/ECToBlob/FalseEdge.lean#L807) alone gives a quartet in the multipartition of `T₀`, which serves all types, so Corollary 4.2 isn't needed. An earlier version of the formal proof did this; it now follows the paper.
- **ECToBlob Theorem 3.1.** Only the splice is needed of the attachments at lines 495–497: [`Phylogenetics.displays_splice_iff`](https://github.com/vltanh/lean4-phylogenetics/blob/f1a3592dee6e3f7d5e7a68a0695ac457de23d2de/Phylogenetics/Tree/Splice.lean#L159) gives its inner sums directly.
- **The T3 test at the singularity.** Non-collapse needs no limit law: the T3 statistic is at most the T1 statistic, which is tight on the null, and the p-value is at least `½ χ²₁(10 t)`, since `sin² α₀ ≥ 1/10` on `[0,1]`.
- **NANUQ's Theorem 36.** Explicit levels prove it directly ([`ECToBlob.remark83_nanuq_fixed_beta`](../../src/ECToBlob/Remark83.lean#L147)), with no levels built from the unknown `d`s. The formal [`External.AllmanBanosRhodes2019.theorem36`](../../src/External/AllmanBanosRhodes2019/Proposition9.lean#L1636) keeps the source's route.
- **Remark 3.3's displayed tree model.** It is the limit of `ρ = 1` as all lengths grow ([`ECToBlob.abs_nmscCF_sub_displayedCF_le`](../../src/ECToBlob/Remark33.lean#L461)), which also justifies the star convention, since a polytomy gives exactly `1/3` at all lengths.
- **Wilks-type limits for a trinomial.** The paper uses these limits; for a trinomial there is an elementary proof. One estimate, `|(1+v) log(1+v) - v - v²/2| ≤ 4|v|³` for `|v| ≤ 1/2` ([`Real.abs_entropyExcess_sub_le`](../../src/Basic/ForMathlib/Analysis/SpecialFunctions/EntropyExcess.lean#L50)), gives each likelihood ratio statistic as a sum of such terms, so each is uniformly close on bounded sets to a continuous function of the whitened frequencies, and an extended continuous mapping theorem, proved from the portmanteau theorem on open sets (`Phylogenetics.Trinomial.tendstoInDistribution_of_closeOnBalls`), finishes. This does not use van der Vaart's Theorem 16.7. At the centroid, Pearson's statistic is exactly `Z₁² + Z₂²` ([`Phylogenetics.Trinomial.pearsonS_centroid`](../../src/Basic/Testing/Trinomial/Whiten.lean#L425)); the T1 test at the centroid is handled separately (E13).

### The formalization

Nothing is assumed (Section 2), and Section 9 lists what is not formalized.

- **Other inheritance.** [`AllmanEtAl2023.corollary1`](../../src/AllmanEtAl2023/Corollary1.lean#L67) is at `ρ = 0`. [`Phylogenetics.NMSC.one_sub_exp_le_nmscCF`](https://github.com/vltanh/lean4-phylogenetics/blob/f1a3592dee6e3f7d5e7a68a0695ac457de23d2de/Phylogenetics/NMSC/Witness.lean#L687) and the analytic parametrization hold for all `ρ`, and the mixture does too, so the same proof may reach the generic clause at other `ρ`: see the open direction above.
- **Generality to reach.** Theorem 8.2 on other laws of non-binary gene trees, for Bon and BBC: only the displayed tree model is proved (E37).
- **Contributions to other libraries.** [`src/Basic/ForMathlib/`](../../src/Basic/ForMathlib) holds what could move to Mathlib: the error function ([`src/Basic/ForMathlib/Analysis/SpecialFunctions/Erf.lean`](../../src/Basic/ForMathlib/Analysis/SpecialFunctions/Erf.lean)), the second-order expansion of `x log x` ([`src/Basic/ForMathlib/Analysis/SpecialFunctions/EntropyExcess.lean`](../../src/Basic/ForMathlib/Analysis/SpecialFunctions/EntropyExcess.lean)), the maximum of a multinomial likelihood ([`src/Basic/ForMathlib/Analysis/SpecialFunctions/GibbsInequality.lean`](../../src/Basic/ForMathlib/Analysis/SpecialFunctions/GibbsInequality.lean); Mathlib has Gibbs' inequality for `klDiv`), zero sets of analytic functions ([`src/Basic/ForMathlib/Analysis/AnalyticZeroSet.lean`](../../src/Basic/ForMathlib/Analysis/AnalyticZeroSet.lean)), stability of maximizers under perturbation ([`src/Basic/ForMathlib/Analysis/FiniteOptimization.lean`](../../src/Basic/ForMathlib/Analysis/FiniteOptimization.lean)), strip probabilities and the orthonormal change of coordinates for two independent unit normals ([`src/Basic/ForMathlib/Probability/GaussianPlane.lean`](../../src/Basic/ForMathlib/Probability/GaussianPlane.lean); Mathlib has rotation invariance as `stdGaussian_map`), the `χ²₂` tail and Gaussian interval bounds ([`src/Basic/ForMathlib/Probability/GaussianTail.lean`](../../src/Basic/ForMathlib/Probability/GaussianTail.lean)), and an extended continuous mapping theorem ([`src/Basic/ForMathlib/Probability/Transfer.lean`](../../src/Basic/ForMathlib/Probability/Transfer.lean)). What is general to phylogenetics is already in the library [`lean4-phylogenetics`](https://github.com/vltanh/lean4-phylogenetics), which keeps what is standard to the field; [`src/Basic/README.md`](../../src/Basic/README.md) says what here could still go there.
- **What [`src/Basic/`](../../src/Basic) holds for this paper.** Of the modules of [`src/Basic/`](../../src/Basic) that this paper imports, [its README](../../src/Basic/README.md) marks `RhoOne`, `General`, `Level1Blobs`, `InducedSplits`, `TreeCounts`, `UnitMetric` and `NMSCChain` for the library `Phylogenetics`, `ForMathlib/*`, which it reaches through `Testing/*`, for Mathlib, and `Defs`, `Testing/*`, `LocalObjective`, `Level1CF` and `FinNetwork` for this project. [`Basic`](../../src/Basic) imports no paper, only Mathlib and the library.
- **Reuse of [`src/External/`](../../src/External).** The forward direction of Huber et al.'s Theorem 5.1 and exchangeability under the NMSC are stated for arbitrary rooted networks, and the quartet metrization of Rhodes for arbitrary unrooted trees. [`src/External/MitchellAllmanRhodes2019/`](../../src/External/MitchellAllmanRhodes2019) has the limit law of the likelihood ratio at a cut model. These are for other formalizations citing the same sources.
