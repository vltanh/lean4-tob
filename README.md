# Tree-of-blobs formalization

**Incomplete: source inventory, shared foundations and preliminary audit. No
numbered paper result has been formalized.** The full statements baseline remains
unfinished. The current foundations cover directed multigraphs, rooted
network data, ancestral restriction, quartet probability representations, finite
tree hierarchies, exact quartet scores and stability of maximizers under finite
uniform perturbations. Selected finite Kingman kernel foundations are included;
an arbitrary-network NMSC law has not been constructed.

Work stopped at the user's request. See [HANDOFF.md](docs/HANDOFF.md) for the
current verification, local drafts and next steps.

Sources: ECToBlob bioRxiv v1, TOB-QMC bioRxiv v5 (user-authorized fallback from the
subscription-only journal), and published TINNiK. The two supplements supplied by
the user have been read; exact linkage of the internally February-dated TOB-QMC
supplement to main v5 remains unconfirmed. See [configuration](docs/CONFIGURATION.md), [source hashes](docs/sources.json)
and the [preliminary audit](REPORT.md).

The audit records an overcount in ECToBlob (3.3), a missing genericity restriction
in Theorem 8.2 under its literal general-model scope, and TINNiK's open-domain MLE
problem. Approved corrections are generic numerical parameters for ECToBlob
Theorem 8.2, closed-simplex estimation for TINNiK, and only the forward implication
of TOB-QMC supplementary Lemma 2, and a nontrivial-blob condition for supplementary
Lemma 8. The supplement's probability-gap definition also
needs a local proof repair. Verification limits are explicit in the report.

Build/check with Lean and Mathlib `v4.36.0-rc1`:

```sh
lake exe cache get
lake build
lake env lean scripts/AuditFoundations.lean
lake env lean -DautoImplicit=false -DmaxSynthPendingDepth=3 scripts/SourceChecks.lean
lake env lean -DautoImplicit=false -DmaxSynthPendingDepth=3 scripts/BoundaryCheck.lean
lake env lean -DautoImplicit=false -DmaxSynthPendingDepth=3 scripts/IndistinguishabilityCheck.lean
lake env lean scripts/SunletCheck.lean
lake env lean scripts/TOBQMCGapCheck.lean
```

`Basic/` contains general mathematics, `External/` is reserved for cited results, and
`TINNiK/`, `TOBQMC/`, `ECToBlob/` for the papers. `Challenge.lean` and
`Solution.lean` are empty placeholders. Comparator, full axiom/route audits and
Palomar packaging are pending; nothing has been published.

Prepared with Codex and three parallel readers following
[formalize-math-paper 3.0.0](https://github.com/vltanh/formalize-math-paper).
See [CREDITS.md](CREDITS.md) for the run's scope and measurement limits.
A general tree-hierarchy kernel was adapted from
[Phylogenetics](https://github.com/vltanh/lean4-phylogenetics); exact provenance and
changes are in [ADAPTED_SOURCES.md](docs/ADAPTED_SOURCES.md).
The finite coalescent extraction is documented in [COALESCENT_SOURCES.md](docs/COALESCENT_SOURCES.md).
[CAMUS](https://github.com/vltanh/lean4-camus) was inspected but not incorporated.

License: Apache-2.0.
