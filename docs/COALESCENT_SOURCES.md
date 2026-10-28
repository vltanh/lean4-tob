# Coalescent source extraction

The public modules in `Basic/Phylogenetics/Coalescent/` are adapted from
[vltanh/lean4-phylogenetics](https://github.com/vltanh/lean4-phylogenetics), exact commit
[`06f684e526e276ca2ccf668a1c3a808a2b8c181d`](https://github.com/vltanh/lean4-phylogenetics/tree/06f684e526e276ca2ccf668a1c3a808a2b8c181d).
The source is Apache-2.0 licensed. Its original toolchain is v4.35.0-rc4;
the following extracted modules compiled without warnings using the destination's
v4.36.0-rc1 and `lake env lean -o`.

| Destination | Exact original regions | Adaptation |
| --- | --- | --- |
| `Defs.lean` | `Phylogenetics/MSC/Defs.lean`49–71 and84–87; `Phylogenetics/MSC/Notions.lean`122–131 | Retained roots, generator, matrix-exponential transition, absorption-limit definition, sampled singleton forest, singletonForest and coalescenceProb. Restored the section-inherited X/DecidableEq X binders for sampledForest. No SpeciesTree or level-1 Net datatype copied. |
| `Forest.lean` | Whole `Phylogenetics/Coalescent/Forest.lean` | Only the import path and attribution header changed; all statements and proofs retained. |
| `Factorization.lean` | Whole `Phylogenetics/Coalescent/Factorization.lean` | Local Defs supplies the extracted MSC.Defs/MSC.Notions primitives; other import path and attribution-header changes only. All statements and proofs retained. |
| `Tavare.lean` | Whole `Phylogenetics/Coalescent/Tavare.lean` | Only the import path and attribution header changed; all statements and proofs retained. |

These are finite real-array Kingman primitives. Finite-time nonnegativity,
normalization and support are proved; Tavaré's pure-death formula is proved.
The definition of the infinite-time absorption kernel is present, but its limit
existence and probability-law proofs have **not** been integrated. No actual PMF
wrapper, arbitrary-network NMSC model or target-paper theorem is supplied by
this partial extraction. Work stopped at the user's explicit handoff request.

The planned Absorption, Outcome and PMF modules are preserved as uncompiled
ignored drafts under `notes/paper2026/coalescent_draft/`; they are not part of the
public library or a completed formalization.
