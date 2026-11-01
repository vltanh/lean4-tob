# Credits

How this formalization was made, from the run log and the session transcripts.

## Who

- **Author and maintainer:** The-Anh Vu-Le, who asked for the formalization, chose the three papers and their versions, and agreed to the statement corrections listed in [`REPORT.md`](REPORT.md). Public authorship is theirs to confirm.
- **Formalization:** Codex (GPT-6 family; exact revision and harness version not exposed), for the source audit and first foundations, in two rounds of one evening. Claude Code 2.1.314 (VS Code extension) with Claude Opus 5.5 (`claude-opus-5-5`), for the statements, proofs, audit, documents and packaging, in one session.
- **Procedure:** the [formalize-math-paper](https://github.com/vltanh/formalize-math-paper) skill, version 3.0.0 in the first rounds, and checkout commit `e339f64` in the last.
- **Review:** no person has reviewed the proofs. Independent agents, which didn't write what they checked, reviewed the statements, compared the proofs with the papers, and checked the audit's findings and its literature section. Comparator and the route check ran locally.

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
- The main session integrated the proofs, wrote the Challenge, Solution and audit scripts, and ran the route check, cleanup and Comparator.
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

Totals for the Claude Code session, all rounds and the private follow-up work: 10.79 h elapsed; sub-agents 53 (53 launched by the main session; at most 11 running at once; 12 resumptions); sub-agent work 32.2 h, 3,552 tool calls; tokens: 11.64M output, 33.50M input, 815M cache reads; main session 432 tool calls; tokens: 1.13M output, 2.45M input, 188M cache reads.
