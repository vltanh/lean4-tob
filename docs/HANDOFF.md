# Handoff

Work stopped at the user's request on 2026-10-27, America/Chicago.

**The formalization is incomplete. No numbered result of the three target papers
has been proved, and the full statements baseline has not been committed.** The
committed work consists of source inventories, checked corrections and
counterexamples, shared mathematical foundations, and TINNiK definitions.

## Repository and authorization

- Workspace: `/home/vltanh/Documents/lean4-tob-qmc`.
- Branch: `formalize/tree-of-blobs`. Run `git log -1 --oneline` for this handoff's
  final commit. Earlier milestones are `3b331c8` and `8c6f322`.
- Lean/Mathlib: `v4.36.0-rc1`; Mathlib commit
  `625d8914199bc567cca9b91f90e8e5afafa5ae51`.
- Local edits, compilation and milestone commits are authorized. No remote push,
  publication, repository creation, Palomar preflight, submission or registration
  is authorized.
- Follow the invoked `formalize-math-paper` skill at
  `/home/vltanh/.agents/skills/formalize-math-paper/SKILL.md`. Keep statements and
  proofs faithful, and finish independent statement review before numbered proofs.
- Only one `lake build` may run in this checkout at a time.

## Decisions already settled

Do not ask for these decisions again. Details and evidence are in
[CONFIGURATION.md](CONFIGURATION.md) and [REPORT.md](../REPORT.md).

| Item | Approved choice |
| --- | --- |
| TOB-QMC source | Prefer the journal, but use bioRxiv v5 if the journal is inaccessible; that fallback applies |
| TINNiK MLE, E9 | Closed simplex for estimation; strictly positive generating probabilities |
| ECToBlob Theorem 8.2, E7 | Explicit pointwise generic-parameter restriction from Assumption 1's exceptional sets |
| Supplied TOB-QMC Lemma 2, E11 | Keep only the valid forward implication; document the false converse |
| Supplied TOB-QMC Lemma 8, E14 | Require a nontrivial blob; document the binary-tree counterexample |

Both supplied supplements have been read and hashed in [sources.json](sources.json).
The 43-page TOB-QMC supplement is internally dated February 26, 2026. Its exact
attachment linkage to main v5 remains unconfirmed despite official-site checks;
keep its labels and stronger claims separate from the main text.

## Stable mathematical work

The library now constructs directed multigraphs with individually identified
arcs, deletion-walk connectivity, bridge-component contraction, and exact cut
correspondences. Parallel arcs are preserved. Ancestral restriction is an actual
vertex/arc subtype graph and preserves network validity for nonempty taxon sets.

Finite hierarchies have concrete graph realizations with exactly the corresponding
labelled cuts. Every binary topology displays exactly one of the three actual
unordered quartet splits. `CutHierarchy` constructs a hierarchy from a valid
network's nonempty proper cut sides; its graph realizes exactly those cuts.

`QuartetScore` defines actual whole-tree PMF marginals, quartet counts and scores,
and proves their normalization/count identities. Its observed trees are complete
and binary on the same taxon set. It does not define an NMSC law.

Finite optimization helpers allow tied true maxima and prove stability under
strict uniform errors. TINNiK's probability/simplex/count/LR/Gaussian/density
definitions and elementary representation bridges are implemented.

Four finite Kingman modules were extracted from the public phylogenetics library:
Defs, Forest, Factorization and Tavare. Their real-array transition laws are
proved. Absorption-law proofs and PMF wrappers are not integrated. See
[ADAPTED_SOURCES.md](ADAPTED_SOURCES.md) and
[COALESCENT_SOURCES.md](COALESCENT_SOURCES.md) for exact attribution and scope.

The sunlet certificate checks all 2,048 vertex cuts, full binary network validity,
the exact ancestral graph, and its `ab|ce` split. It does not yet certify the
complete LSA reduction/suppression/reduced-tree-of-blobs construction.

## Local drafts and sources

`notes/` is ignored and not available in a clean clone. It contains the downloaded
papers and supplements, source inventories, independent reviews and run log.
Preserve it when transferring this workspace. The three detailed agent handoffs
are `notes/paper2025/HANDOFF.md`, `notes/paper2026/HANDOFF.md`, and
`notes/tinnik/HANDOFF.md`.

| Local path | Status and next use |
| --- | --- |
| `notes/paper2025/CorrelatedInheritanceDraft.lean` | Cleanly compiled, audited and independently reviewed; 19 public declarations plus a private helper. Full joint Pólya assignment law and independent/common endpoint laws. Not promoted; exchangeability, correlation interpretation and graph integration remain |
| `notes/paper2025/CORRELATED_INHERITANCE_PLAN.md` | Source formulas, the reciprocal α typo (E15), and joint-frontier requirements |
| `notes/tinnik/CoordinatesDraft.lean` | Cleanly compiled whitening/inverse and cut-line bridges; awaiting independent review |
| `notes/tinnik/CoordinatesMomentsInProgress.lean` | Interrupted optional moment/sign work; five known compilation errors. Not a verified result |
| `notes/tinnik/StatisticsDraft.lean` | Earlier compiling statement draft with 16 expected `sorry`s; includes C.1 and Propositions 5–6. Port to current definitions and independently review before baseline |
| `notes/tinnik/MITCHELL_SURVEY.md` | Exact Mitchell 3.1 and van der Vaart 16.7/7.13 source review, library survey and application obligations |
| `notes/tinnik/MitchellConclusionDraft.lean` | Compiling conclusion schema only; no complete external theorem or assumed hypothesis |
| `notes/paper2026/coalescent_draft/` | Uncompiled Absorption, Outcome and PMF extraction drafts; preserve current source attribution and finish dependencies before compilation |
| `notes/paper2026/kingman_reuse_survey.md` | Reusable kernel/support/absorption source map and missing arbitrary-DAG scheduling |
| `notes/paper2026/DefinitionsDraft.lean` | Earlier compiling ECToBlob model/genericity interface; provisional graph predicates and old quartet types must be replaced |
| `notes/paper2026/boundary_five_taxa.md` | Unproved boundary-CF/Cauchy-selection concern. Do not silently add positivity to Assumption 1 |
| `notes/paper2025/ScoreStatementsDraft.lean` | Older design sketch; use public topology/score definitions instead of its duplicate types. Actual NMSC constructor is deliberately absent |

## Remaining work, in dependency order

1. Finish the representation bridges between maximal 2-edge-connected blobs,
   bridge contraction, LSA truncation, degree-two suppression and tree refinement.
   Cut-family correspondence alone is not an arc-to-split bijection: a binary
   root's two arcs can give the same unordered split.
2. Complete the model construction using real Kingman kernels and the reviewed
   correlated-inheritance law. Preserve the joint forest across frontier edges;
   multiplying edge marginals loses dependence after hybrid ancestry. The old
   source's level-1 `Net` type cannot represent these arbitrary-level networks.
3. State every numbered result, algorithms and reused equations, with exact
   source assumptions. Review all statements independently and commit the full
   baseline. `docs/paper_routes.tsv` has 79 preliminary source labels; it is not a
   generated or passing formal proof-route audit.
4. Prove paper-owned results by their source arguments. Apply the documented
   local repairs in REPORT: weighted representative sums, argmax containment,
   the positive dominant quartet margin, endpoint strictness and statistical
   tail controls. Do not replace a paper-owned theorem with a hypothesis or a
   structure field.
5. Handle cited results exactly. The LR approximation lacks a general Mathlib
   likelihood-asymptotic framework. The verified source requires DQM, nonsingular
   Fisher information, local log-density regularity, consistent MLEs and the
   specified set convergence. Open-supremum/closed-maximum equality alone does
   not supply MLE existence; the localization bridge remains unproved. Any
   permitted external assumption must be explicit, named and reported as conditional.
6. Complete axiom/nonvacuity/route audits, Challenge/Solution, Comparator, CI,
   `formalization.yaml`, final report and private follow-up-paper research.
   `NEXT.md` has not been written. Nothing has been published.

## Verification commands

At the final verification checkpoint (2026-10-27, approximately 23:03
America/Chicago), `lake build` passed for all 24 implemented modules.
`AuditFoundations.lean` checked 815 declarations, including private and generated
ones, and found only `propext`, `Classical.choice` and `Quot.sound`. All five
certificate scripts below compiled successfully. These checks establish the
current code's status, not completion of any numbered paper theorem.

```sh
lake build
lake env lean -DautoImplicit=false -DmaxSynthPendingDepth=3 scripts/AuditFoundations.lean
lake env lean -DautoImplicit=false -DmaxSynthPendingDepth=3 scripts/SourceChecks.lean
lake env lean -DautoImplicit=false -DmaxSynthPendingDepth=3 scripts/BoundaryCheck.lean
lake env lean -DautoImplicit=false -DmaxSynthPendingDepth=3 scripts/IndistinguishabilityCheck.lean
lake env lean -DautoImplicit=false -DmaxSynthPendingDepth=3 scripts/SunletCheck.lean
lake env lean -DautoImplicit=false -DmaxSynthPendingDepth=3 scripts/TOBQMCGapCheck.lean
```

`AuditFoundations.lean` imports every implemented library module with `import all`
and checks private/generated declarations as well. Extend its import list when
adding modules. It is separate from the still-pending numbered-result route audit.
