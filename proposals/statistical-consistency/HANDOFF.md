# Handoff: TOB-QMC and ECToBlob stronger statistical consistency

**PR:** [lean4-tob #1](https://github.com/vltanh/lean4-tob/pull/1), draft, branch \`proposal/strong-consistency-and-explicit-levels\`, target \`formalize/tree-of-blobs\`.
**Companion:** [QWC #6](https://github.com/vltanh/QWC/pull/6), branch \`theory/rate-robustness-and-approximate-guides\`, target \`main\`.

**All new results are proposed handproofs or uncompiled source.** Nothing in the checked \`src/\` proof graph, Palomar/audit manifest, source paper statements, dependency versions, or run-time code has been altered by this PR. No Lean, Lake, CI, kernel audit or test run was performed for these commits.

## Strengthenings delivered on this branch

| Result | Mathematical conclusion | Kernel status |
|---|---|---|
| TOB-QMC prescribed schedule | Cut/T3 TOB-QMC consistency for any explicit \`alpha_m>0\`, \`alpha_m→0\`, \`log(alpha_m)/m→0\` under its exact WQC/cover/model assumptions | Composed Lean-style bodies in \`drafts/TOBQMCExplicitLevels.lean.txt\`; **not compiled** |
| Original T3/T1/LRT-star | Actual p-values at \`alpha_m=(m+1)^(-100)\` have summable false-null error via type counting; positive-gap alternatives are detected exponentially | Full handproof in \`OriginalPValuesStrong.md\`; not compiled |
| ECToBlob Bon/BBC | Arbitrary-guide eventual correct coarsening and end-to-end a.s. recovery under supplied/consistent guides and exact Assumption 1 | Handproof, BBC sandwich; not compiled |
| Cauchy/CBC limitation | Exact p=1 recurrent endpoint can mask alternative evidence in mixed scalar families, preventing blanket a.s. rejection | Scalar obstruction handproof, not a full NMSC output counterexample |
| Binary ECToBlob beta | In binary Assumption-1 networks (no centroid quartets), **fixed positive beta** is compatible with strong consistency; alpha must shrink | Handproof, not compiled |
| Approximate guide | Population WQC gap + vanishing normalized regret + candidate availability yield eventual guide refinement | Deterministic Lean-style \`ScoreGap.lean.txt\`, uncompiled |
| **New pipeline bound** | Joint guide/contraction finite-sample error B5, tail-of-time B6; same-data guide allowed; explicit candidate-space bound for exact ASTRAL | \`PipelineBounds.md\` handproof, not compiled |
| Conservative calibration variant | Explicit composite-null p-type with finite-sample validity; **different statistic** from shipped methods | \`FiniteSample.md\`; not implemented |

## Nearest finite proof gates

1. **T0**: Elaborate and kernel-check \`TOBQMCExplicitLevels.lean.txt\` against the current Lean API; it uses only existing rejection/test/refinement lemmas. No new numerical tail lemma should be required. Do not mark the proof complete merely because the text contains no \`sorry\`.
2. **G0**: Check the elementary \`ScoreGap.lean.txt\` inequality; then prove the finite WQC bad-tree score gap from a population theorem, not an assumed correct optimizer.
3. **O1**: Prove that the exact T1/T3/star statistics equal \(2m\) times the appropriate closed-null KL projection, including zero coordinates. This enables the type-counting bound for the *existing p-values*.
4. **O2**: Formalize \(\Pr_p(T>t)\le(m+1)^2e^{-t/2}\), then derive the original-test false-null probability \(\le(m+1)^{-2}\) from pre-existing chi-square tail lemmas.
5. **O3**: Prove the joint alternative bound with \(\delta_*>0\) by Pinsker/Hoeffding. Verify that **nested** Bon/BBC correction factors multiply: use the correct total amplification \(H_n\).
6. **O4**: Connect all-correct scalar tests to the exact TOB-QMC-T3 and ECToBlob Bon/BBC deterministic reconstruction APIs; keep the two methods and options separate.
7. **O5**: Prove B5/B6 with the common sample event, candidate-space availability and regret (no sample splitting). The guide event must have a.s. eventual validity or summable failures for strong consistency.
8. **O6**: Prove or give exact hypotheses for fixed-beta binary ECToBlob, and isolate Cauchy/CBC endpoint behaviour from Bon/BBC.
9. **O7**: Only after verified kernels and reviewer approval, update the published theorem inventory/Palomar audit. This PR deliberately leaves them unchanged.

## Constraints for the next session

- **No Lean compile / CI** until the project decides to audit. This handoff does not authorize compilation and does not claim the uncompiled drafts already elaborate.
- Prove a result once in the paper-owned part of the repository, with shared statistical lemmas only when truly reusable; preserve TOB-QMC and ECToBlob theorem ownership.
- Do not claim arbitrary-level sparse TOB-QMC consistency: its contraction theorem is level-1 with a cover/witness condition.
- Do not call a fixed \`0.05\` alpha consistent; no finite-sample accuracy optimality of exponent 100 is asserted.
- Do not claim an arbitrary heuristic is consistent absent the vanishing-regret and candidate-space evidence.
- Do not assume within-gene quartet independence or independence of the guide from its test loci.
- Keep the published Theorem 8.2 exceptional genericity, Cauchy/CBC positivity, and any network-centroid issues explicit.

## Suggested reading order

[README](README.md) → [TOB-QMC](TOBQMC.md) → [Original tests](OriginalPValuesStrong.md) → [BBC/Cauchy](CombinationStrong.md) → [Pipeline bounds](PipelineBounds.md) → [Guide regret](GuideRegret.md) → [ECToBlob](ECToBlob.md) → [formalization ledger](FORMALIZATION.md).

**Handoff status:** theory pushed to a draft PR; no checked new theorem, external empirical benchmark or software change is claimed.
