# Credits

How this formalization was made, from the run log and the session transcripts.

## Who

- **Author and maintainer:** The-Anh Vu-Le, who asked for the formalization, chose the five papers and the versions of the first three, agreed to the statement corrections listed as agreed in [`REPORT.md`](REPORT.md), decided what the library holds, the layout and the kernels, and published the repository.
- **Formalization:** Codex (GPT-6 family; exact revision and harness version not exposed), for the source audit and first foundations, in two rounds of one evening. Claude Code 2.1.314 (VS Code extension) with Claude Opus 5.5 (`claude-opus-5-5`), for the statements, proofs, audit and documents of all five papers, in one session.
- **Procedure:** the [formalize-math-paper](https://github.com/vltanh/formalize-math-paper) skill, version 3.0.0 in the first rounds, and checkout commit `e339f64` from the formalization on. The run log of the last round names the skill and not a commit.
- **Review:** no person has reviewed the proofs. Independent agents, which didn't write what they checked, reviewed the statements, compared the proofs with the papers, and checked the audit's findings and its literature section. The three kernels and the route check ran locally.

## Source audit and project setup (2026-10-27)

The user asked for the three papers to be formalized, then for a handoff before completion. No numbered result was proved in this round.

How it was made:

- Codex and three sub-agents read TINNiK, TOB-QMC and ECToBlob, each paper by one agent, and checked each other's counterexamples. The user supplied the two supplements and agreed to the corrections E10, E23, E26 and E31.
- The main session built the multigraph and network foundations, integrated the agents' work and wrote a preliminary audit. A tree-only hierarchy kernel and finite Kingman modules were adapted from the public [lean4-phylogenetics](https://github.com/vltanh/lean4-phylogenetics) library ([`docs/ADAPTED_SOURCES.md`](ADAPTED_SOURCES.md), [`docs/COALESCENT_SOURCES.md`](COALESCENT_SOURCES.md)).

Figures, from the run log (Codex exposes no totals):

- Two rounds, from 2026-10-27 21:09:21 to about 23:03 America/Chicago: about 1 h 54 min.
- Three sub-agents; at most four agents at once, the main session included.
- Tokens, tool calls, model calls and cost were not recorded. Overlapping agent time isn't summed.
- Output: 24 modules of foundations, 815 declarations checked against the standard axioms, and the certificate scripts `scripts/*Check.lean`.

## Formalization (2026-10-31)

The user invoked the skill again with the three links, to continue from the handoff to the end.

How it was made:

- The main session designed the shared definitions (`Basic/Phylogenetics/Defs.lean`), wrote every statement with `sorry`, and an independent agent reviewed them against the papers, finding one false definition ([`IsExactBuilder`](https://github.com/vltanh/lean4-phylogenetics/blob/9948de9b3cba330596424efd2dca9617be2efb0c/Phylogenetics/Tree/Metric.lean#L51) excluded neighbor joining) and several readings.
- Proof agents worked in parallel on private snapshots of the build, one set of files each: graphs and cut edges; trees and splits (ECToBlob §3, TOB-QMC §4.1–4.2); tails and combining p-values; limit laws from the central limit theorem; Proposition 6; the NMSC on arbitrary networks, resumed to prove exchangeability; the B-quartet rule, the quartet metrization and TINNiK's Theorem 4; level-1 blobs; and Theorem 8.2 with its false-edge repair.
- The main session integrated the proofs, wrote the Challenge, Solution and audit scripts (the first two since replaced by [`src/MainResults.lean`](../src/MainResults.lean)), and ran the route check, cleanup and Comparator.
- Two independent agents compared the proofs with the papers, one agent checked every finding of the audit against the sources by script, one researched the literature and another checked that section and the section on what comes next. Their corrections are applied. Those that changed Lean: Theorem 4 of TINNiK uses the paper's levels, Lemma 6.1 the printed bound.

Figures, from 2026-10-31 07:25:55 America/Chicago to commit `b2be3ef` at 10:51:30, the commit completing [`REPORT.md`](REPORT.md):

- Elapsed time: 3.43 h.
- Sub-agents: 17, of which at most 10 ran at once, with 4 resumptions; total working time 10.6 h. This includes two agents exploring follow-up papers, private to the user.
- Tool calls: 1,182 for the sub-agents, 243 for the main session.
- Tokens, sub-agents: 3.84M output, 10.05M input, 241M cache reads. Main session: 0.68M output, 1.51M input, 89M cache reads.
- Model calls: 960 to `claude-opus-5-5` (189 main session, 771 sub-agents).
- Cost was not tracked. The figures leave out the Codex rounds above and any work after that commit.

After that commit, the packaging checks and this file were finished, and two more agents checked the private follow-up file. By the end of the session the totals were 5.29 h elapsed, 19 sub-agents, 13.4 h of sub-agent working time, and 1,449 and 254 tool calls for the sub-agents and the main session.

## Corollary 1 and faithful proofs (2026-10-31)

The user read the report, agreed to the correction E11, and asked to prove the assumed Corollary 1 of Allman et al., to rewrite the departures that weren't forced, and to push everything to a private repository, with the follow-up notes kept on a separate branch.

How it was made:

- The main session split Corollary 1 into five contracts and a shared file on deleted arcs. Four agents proved the analytic parametrization, the null zero sets, the probability bounds at boundary parameters, and the graph reduction, and a fifth assembled them, with ECToBlob's adaptation.
- Seven agents rewrote the proofs of TOB-QMC's Lemmas 3, 4 and consistency, TINNiK's Proposition 6 and the null of its Theorem 4, Allman et al.'s Lemma 3, and Rhodes's Theorem 2.
- The main session integrated them. Two independent agents reviewed the rewritten proofs and the new cited results.

Figures, from 2026-10-31 12:49:23 America/Chicago, the user's request, to the commit that completes this round, about 14:30:

- Elapsed time: 1.67 h.
- Sub-agents: 14, of which at most 11 ran at once, with 1 resumption; total working time 5.1 h.
- Tool calls: 585 for the sub-agents, 44 for the main session.
- Tokens, sub-agents: 2.01M output, 5.79M input, 94M cache reads. Main session: 0.14M output, 0.24M input, 36M cache reads.
- Model calls: 431 to `claude-opus-5-5` (43 main session, 388 sub-agents).
- Cost was not tracked.

## Following the sources, and what the papers say in passing (2026-10-31)

The user read the last report, and asked to match the sources closely, with any shorter proof that remains documented, and then to formalize as much as possible of what the report listed as not formalized, unless it's wrong.

How it was made:

- Six agents rewrote proofs along their sources: Allman et al.'s Theorem 1, its Lemma 3, ECToBlob's Theorem 8.2, and smaller items. One proved that concordance factors don't change on an induced network, and one carried null sets back, so that Corollary 1 goes through induced networks as in the source. The main session connected them. A further agent rewrote ECToBlob's Theorem 4.1 and Allman et al.'s Theorem 2 when the first pass flagged them.
- Other agents formalized Section 9 of the report: neighbor joining, the T3 option, ECToBlob's remarks, TOB-QMC's Lemmas 1 and 8 and its bipartition search, counts of operations, ASTRAL's dynamic program, and NANUQ. Remark 8.4 and a reading of Remark 3.3 turned out false, with counterexamples in Lean.
- Two independent agents compared the rewritten proofs with the sources, and one more checked the new findings against the sources. The main session and one agent fixed what they found.

Figures, from 2026-10-31 14:51 America/Chicago, the user's request, to about 18:20:

- Elapsed time: 3.36 h.
- Sub-agents: 20 (20 launched by the main session; at most 11 running at once; 7 resumptions); total working time and tool calls: 13.7 h, 1,518 tool calls; tokens: 5.19M output, 15.61M input, 416M cache reads.
- Main session: 115 tool calls; tokens: 0.23M output, 0.50M input, 45M cache reads.
- Model calls: claude-opus-5-5 (114 main, 1154 sub-agents).
- Cost was not tracked.

Totals for the Claude Code session to this point, these rounds and the private follow-up work: 10.79 h elapsed; sub-agents 53 (53 launched by the main session; at most 11 running at once; 12 resumptions); sub-agent work 32.2 h, 3,552 tool calls; tokens: 11.64M output, 33.50M input, 815M cache reads; main session 432 tool calls; tokens: 1.13M output, 2.45M input, 188M cache reads.

## Two more papers, on the library (2026-10-31 to 2026-11-01)

The user asked to formalize Gusfield, Bansal, Bafna, Song 2007 and Allman, Baños, Mitchell, Rhodes 2023 as primary papers, in this repository, and made these decisions as the round went:

- the project imports the library [`lean4-phylogenetics`](https://github.com/vltanh/lean4-phylogenetics), by commit, in place of its own general layer;
- that library keeps only what is standard to phylogenetics, each thing acknowledged to its source, and things move upstream only when several projects use them;
- Palomar is not a target, so there is no Challenge or Solution: main theorems are in [`src/MainResults.lean`](../src/MainResults.lean), since split into one module per paper in [`src/MainResults/`](../src/MainResults), the files for a possible submission are in [`palomar/`](../palomar), one entry per paper since, and the main theorems are checked by several kernels;
- the layout has [`src/`](../src) and `docs/`, and the working notes are private, in another repository;
- this repository is public.

How it was made:

- Two agents wrote the statements of the two papers, with `sorry`, and found the first of the errors: Theorem 4, §4.2 and line 560 of Gusfield et al., and Lemma 2 of Allman et al. Two independent agents reviewed them against the papers, with search programs of their own. These reviews confirmed the errors, corrected how they should be reported, added others, and found that the Allman et al. text available is an author manuscript. Their corrections were applied in the proof phase.
- One agent ported the older code onto the library, and another made the library's boundary as the user decided. The main session committed that as a baseline.
- Proof agents worked in parallel on private snapshots of the build, one set of files each: for Gusfield et al., the foundations and cited results, the decomposition, uniqueness and the conjectures, the sufficient conditions, and the counterexamples and their counts; for Allman et al., Proposition 1, Theorem 1 and Corollary 1, and Lemma 2 through Theorem 4. Lower bounds on `R` are by a verified search in the kernel.
- Two independent agents compared the proofs with the papers. Their findings sent the proof agents back: Theorem 4's account was corrected, and a realizability theorem added; several departures that weren't forced were replaced by the paper's argument, among them Proposition 1's converse, and the same-blob theorem was brought closer to the source's argument.
- Two agents merged duplicates, one for each paper, and one integrated everything: the audit's lists, the routes, a clean build, the three kernels, and the private references. After that commit, one agent searched the literature for the report's Sections 10 and 11, with a second agent checking its quotes, and found Gusfield's 2014 book, which has the repair of E42, and an author's copy of the 2007 paper with its symbols. Another wrote the report's new sections and the other documents, checking each claim against the Lean and the sources. A further independent agent checked those documents against the sources, and the corrections it asked for are applied.

Figures, from 2026-10-31 18:44 America/Chicago, the user's request, to commit `5693efe` at 2026-11-01 02:04:51 -06:00, the commit that completes the proofs, from the `session_stats.py` script of the formalize-math-paper skill:

- Elapsed time: 8.34 h, with the user's own pauses included.
- Sub-agents: 20 (19 launched by the main session; at most 8 running at once; 18 resumptions); total working time 24.9 h.
- Tool calls: 2,541 for the sub-agents, 207 for the main session.
- Tokens, sub-agents: 7.94M output, 27.94M input, 899M cache reads. Main session: 0.34M output, 0.73M input, 106M cache reads.
- Model calls: 2,227 to `claude-opus-5-5` (223 main session, 2,004 sub-agents).
- Cost was not tracked. These figures leave out the documents and the literature search made after that commit. They include the agent that worked on the library, and the separate rebuilds of each agent's snapshot aren't separated out.

At that commit: 177 modules, 7,336 jobs in a clean `lake build` with no warnings, 19,669 declarations on the standard axioms, 304 results in the audit's table, and 39 main theorems accepted by Lean's kernel, NanoDa and con-ron.

Totals for the Claude Code session, all rounds and the private follow-up work, to that commit: 19.65 h elapsed; sub-agents 72 (all launched by the main session; at most 11 running at once; 30 resumptions); sub-agent work 57.0 h, 6,093 tool calls; tokens: 19.58M output, 61.44M input, 1,715M cache reads; main session 647 tool calls; tokens: 1.48M output, 3.20M input, 300M cache reads.

## Finishing what the papers claim (2026-11-01)

The user asked, of Section 9 of the report: "why don't we finish the formalizations in 9? leave only empirical and wrong stuff". Later, of what was still left: "if they are cited but unused then we can just leave them out", and "anything private should just go to the private notes, right?"

The main session chose how to carry that out: a wrong statement is listed with its counterexample in Lean; Section 9 has a short list of what stays open; the results left out aren't listed; and that a search outside Lean supports the hypothesis of the one conditional theorem is stated, with its limits.

How it was made:

- Nine agents worked in parallel on private snapshots of the build, one set of files each, and most were sent back for what their first report left: the limit laws and densities of the T3 and T1 tests; the integer program, Algorithms 1 and 3, the conjecture of line 590 through Klöpper's thesis, and Song and Hein, read at last; galled trees, optimality, and the algorithm with its count; line 329 at the entry node, line 299 at any node, `R¹(M_d) = 3d`, and merged blobs; Allman et al.'s outline and remaining remarks; TOB-QMC's implementation, missing taxa, running times, Kane and Tao, bridge-finding, Huber et al.'s converse, and Dinh and Baños; NANUQ's source definitions; ECToBlob's displayed tree model, Remark 3.4 and §10; and the open statements on Gusfield et al., where Theorem 10 turned out false if `R(M + S)` is read by line 385's definition.
- One agent integrated everything: the audit's lists, the routes, a clean build and the three kernels.
- Another brought the documents up to date, checking each claim against the Lean and the sources, and an independent agent checked those documents. Its findings on fairness to the authors are applied: Theorem 10 is graded by what the paper's own use of its symbol suggests, and Section 9's list holds only what is false.
- After the commit below, one more agent stated the remaining counterexamples as theorems in [`src/`](../src), so that five scripts, `SourceChecks`, `IndistinguishabilityCheck`, `TOBQMCGapCheck`, `SunletCheck` and `BoundaryCheck`, could go.

Figures, from the `session_stats.py` script of the formalize-math-paper skill, from the user's request at 2026-11-01 06:58 America/Chicago to commit `282215c` at 11:34:39 -06:00, the commit that completes the proofs:

- Elapsed time: 4.61 h.
- Sub-agents: 10 (all launched by the main session; at most 9 running at once; 8 resumptions); total working time 15.6 h.
- Tool calls: 1,498 for the sub-agents, 42 for the main session.
- Tokens, sub-agents: 5.48M output, 16.13M input, 612M cache reads. Main session: 0.05M output, 0.12M input, 29M cache reads.
- Model calls: 1,280 to `claude-opus-5-5` (53 main session, 1,227 sub-agents).
- Cost was not tracked. These figures leave out the documents made after that commit.

From the last figures, at commit `5693efe`, to commit `282215c`, which adds the documents and the literature search of the last round: 9.50 h elapsed; sub-agents 14 (12 launched by the main session; at most 9 running at once; 10 resumptions); sub-agent work 19.7 h, 1,951 tool calls; tokens: 6.41M output, 20.70M input, 742M cache reads; main session 59 tool calls; tokens: 0.08M output, 1.06M input, 38M cache reads.

At that commit: 256 modules in [`src/`](../src), 147,954 lines of Lean, 8,646 jobs in a clean `lake build` with no warnings, 26,218 declarations on the standard axioms, 587 results in the audit's table, and 79 main theorems accepted by Lean's kernel, NanoDa and con-ron, one of them conditional on a computation that none of those kernels has checked.

Totals for the Claude Code session, all rounds and the private follow-up work, to that commit: 29.14 h elapsed; sub-agents 85 (84 launched by the main session; at most 11 running at once; 40 resumptions); sub-agent work 76.8 h, 8,044 tool calls; tokens: 25.97M output, 82.14M input, 2,456M cache reads; main session 706 tool calls; tokens: 1.55M output, 4.25M input, 338M cache reads.

At the end of this round, after those later edits: 264 modules in [`src/`](../src), 149,784 lines of Lean, 8,662 jobs in `lake build` with no warnings, 26,534 declarations on the standard axioms, 598 results in the audit's table, and 90 main theorems accepted by Lean's kernel, NanoDa and con-ron, in 6:55, with con-ron at 72,580 declarations, one of them conditional on a computation that none of those kernels has checked.
