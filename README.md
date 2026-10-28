# Tree-of-blobs formalization

**Incomplete: source inventory and preliminary audit. No numbered paper result has
been formalized.** The Lean project builds, and audit scripts verify several
counterexamples. ECToBlob Theorem 8.2 needs a decision on its missing genericity
restriction before a faithful statements baseline can be completed.

Sources: ECToBlob bioRxiv v1, TOB-QMC bioRxiv v5 (user-authorized fallback from the
subscription-only journal), and published TINNiK. Both bioRxiv supplements remain
unread. See [configuration](docs/CONFIGURATION.md), [source hashes](docs/sources.json)
and the [preliminary audit](REPORT.md).

The audit records an overcount in ECToBlob (3.3), a missing genericity restriction
in Theorem 8.2 under its literal general-model scope, and TINNiK's open-domain MLE
problem. The user approved closed-simplex estimation for the last issue. Proposed
proof repairs and their verification limits are explicit in the report.

Build/check with Lean and Mathlib `v4.36.0-rc1`:

```sh
lake exe cache get
lake build
lake env lean -DautoImplicit=false -DmaxSynthPendingDepth=3 scripts/SourceChecks.lean
lake env lean -DautoImplicit=false -DmaxSynthPendingDepth=3 scripts/BoundaryCheck.lean
lake env lean -DautoImplicit=false -DmaxSynthPendingDepth=3 scripts/IndistinguishabilityCheck.lean
```

`Basic/` is reserved for general mathematics, `External/` for cited results, and
`TINNiK/`, `TOBQMC/`, `ECToBlob/` for the papers. `Challenge.lean` and
`Solution.lean` are empty placeholders. Comparator, full axiom/route audits and
Palomar packaging are pending; nothing has been published.

Prepared with Codex and three parallel readers following
[formalize-math-paper 3.0.0](https://github.com/vltanh/formalize-math-paper).
See [CREDITS.md](CREDITS.md) for the run's scope and measurement limits.
Relevant earlier foundations include [Phylogenetics](https://github.com/vltanh/lean4-phylogenetics)
and [CAMUS](https://github.com/vltanh/lean4-camus); neither has been incorporated.

License: Apache-2.0.
