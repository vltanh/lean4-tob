# Tree-of-blobs formalization

This project is in source inventory and setup. **No result of the papers has been formalized yet.** The empty Lean modules build; this verifies the project configuration only.

Sources of record are the ECToBlob bioRxiv v1 paper, the TOB-QMC journal paper (selected by the user), and the published TINNiK paper. See [configuration](docs/CONFIGURATION.md) for source links, version decisions and dependency pins.

Build with Lean/Mathlib `v4.36.0-rc1`:

```sh
lake exe cache get
lake build
```

`Basic/` is reserved for general mathematics, `External/` for cited results, and `TINNiK/`, `TOBQMC/`, `ECToBlob/` for the papers. `Challenge.lean` and `Solution.lean` are empty placeholders, not a completed Palomar submission.

Prepared with Codex and three parallel paper readers, following [formalize-math-paper 3.0.0](https://github.com/vltanh/formalize-math-paper). License: Apache-2.0.
