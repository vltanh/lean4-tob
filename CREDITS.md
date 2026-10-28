# Credits

## Source audit and project setup, 2026-10-27

- Requested by The-Anh Vu-Le, whose existing local Git identity was used for local
  milestone commits. Public authorship and maintainership have not been finalized.
- Procedure: [formalize-math-paper](https://github.com/vltanh/formalize-math-paper),
  version 3.0.0. The installed skill has no Git metadata, so its commit is unknown.
  Local commits follow the installed git-commit workflow.
- System: Codex, GPT-6 family, using the shared local workspace and Lean compiler.
  The exact model revision and harness version are not exposed by this session.
- Three sub-agents read TINNiK, TOB-QMC and ECToBlob respectively. The TINNiK
  reader subsequently checked the boundary and genericity counterexamples in Lean.
  The TOB-QMC and ECToBlob readers independently reviewed the representative-tuple
  counting error. The ECToBlob reader independently reviewed the two initial Lean
  check files. Root integrated sources, wrote the finite counting checks and the
  public preliminary report, and inspected the final genericity certificate.
- No human review is claimed. Lean checks only the certificate statements; the
  full graph/model counterexample remains a written argument, as the report states.

Timing from the untracked run log:

- Start: 2026-10-27 21:09:21 America/Chicago (02:09:21 UTC the following day).
- Initial scaffold build and configuration milestone: commit `0468633`.
- Preliminary source-audit report assembled at approximately 21:31 America/Chicago,
  about 22 minutes after start. This is **not** time to a completed formalization.
- Three sub-agents; peak concurrency: three sub-agents plus root. The TINNiK
  reader was resumed once and ECToBlob reader once. Agent wall spans overlap and
  cannot be summed as CPU or model time; exact total active agent time is unavailable.
- Input tokens, output tokens, cache reads, tool/model call totals and monetary
  cost were not exposed in a reliable aggregate. They are not estimated here.

No paper-result baseline or completed proof corpus was produced in this round.
The run's output is a compiled project scaffold, source inventories, independently
reviewed findings and partial Lean counterexample certificates. No remote writes,
publishing, Palomar preflight, submission or registration were performed.

## Supplement review and shared foundations, 2026-10-27

The second round began at 21:34:56 America/Chicago, after the user approved the
ECToBlob genericity correction. During this round the user supplied both
supplements and approved the TOB-QMC supplement's forward-only quartet lemma.

At the 22:13 checkpoint, about 39 minutes into this round and 64 minutes after
initial setup, the full build passed. The declaration audit checked 388 library
declarations, including private and generated declarations, using only Lean's
three standard axioms. This count is **not** a count of paper theorems: none of
the numbered paper results has been proved. The two new counterexample scripts
also compiled with standard axioms only.

The same three agents were resumed for source review, statistics definitions,
finite optimization, quartet and ancestral representations, and the finite
sunlet certificate. Reviews were assigned to agents other than the respective
authors. Root built the general multigraph, connectivity and bridge-contraction
modules, integrated the work and performed the aggregate audit. The tree-only
hierarchy kernel was adapted from the public phylogenetics library; its exact
source and proof adaptations are recorded in [ADAPTED_SOURCES.md](docs/ADAPTED_SOURCES.md).

Peak concurrency remained root plus three agents. One continuation briefly failed
because the selected model was at capacity and was resumed without a model
change. Active agent time, exact model revision, token totals and monetary cost
remain unavailable; overlapping wall spans are not summed as compute time.
Source/statement work continues. No publishing or registry action was taken.
