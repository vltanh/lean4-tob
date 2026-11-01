# Coalescent source extraction

The paths under `Basic/Phylogenetics/` below are this repository at commit `f838ea4`. These modules have since moved to the library `lean4-phylogenetics`, which this project imports; `Challenge.lean` is gone as well (see [CONFIGURATION.md](CONFIGURATION.md)).

The public modules in `Basic/Phylogenetics/Coalescent/` are adapted from
[vltanh/lean4-phylogenetics](https://github.com/vltanh/lean4-phylogenetics), exact commit
[`06f684e526e276ca2ccf668a1c3a808a2b8c181d`](https://github.com/vltanh/lean4-phylogenetics/tree/06f684e526e276ca2ccf668a1c3a808a2b8c181d).
The source is Apache-2.0 licensed. Its original toolchain is v4.35.0-rc4;
the following extracted modules compile without warnings on the destination's
v4.36.0-rc1.

| Destination | Exact original regions | Adaptation |
| --- | --- | --- |
| `Defs.lean` | `Phylogenetics/MSC/Defs.lean`49–71 and84–87; `Phylogenetics/MSC/Notions.lean`122–131 | Retained roots, generator, matrix-exponential transition, absorption-limit definition, sampled singleton forest, singletonForest and coalescenceProb. Restored the section-inherited X/DecidableEq X binders for sampledForest. No SpeciesTree or level-1 Net datatype copied. |
| `Forest.lean` | Whole `Phylogenetics/Coalescent/Forest.lean` | Only the import path and attribution header changed; all statements and proofs retained. |
| `Factorization.lean` | Whole `Phylogenetics/Coalescent/Factorization.lean` | Local Defs supplies the extracted MSC.Defs/MSC.Notions primitives; other import path and attribution-header changes only. All statements and proofs retained. |
| `Tavare.lean` | Whole `Phylogenetics/Coalescent/Tavare.lean` | Only the import path and attribution header changed; all statements and proofs retained. |

| `Absorption.lean` | Whole `Phylogenetics/Coalescent/Absorption.lean` | Import path and attribution header; the two private `deathPow`/`deathProb` zero lemmas are replaced by `deathPow_zero_right`, `deathProb_zero_right` of `Factorization.lean`. All public statements retained. |
| `Outcome.lean` | Whole `Phylogenetics/Coalescent/Outcome.lean` | Import paths and attribution header; `Hierarchy.lean` supplies the hierarchy definitions. All statements and proofs retained. |
| `PMF.lean` | New wrapper; `kingmanAbsorption_support_forest` follows `Phylogenetics/NMSC/Basic.lean`338–355 without its binary-forest conjunct | PMF wrappers of the proved rows, built with `PMF.ofFintype`; no renormalization. |
| `BinaryForest.lean` | `Phylogenetics/MSC/History.lean`499–536 (`model_IsBinaryForest`, merge and jump-chain preservation); `Phylogenetics/NMSC/Basic.lean`38–93 (`IsGood`, `isGood_empty`, `isGood_singletons`, `IsGood.union`, `mem_forestBelow`, `isGood_forestBelow`, `lineages_forestBelow`), 249–255 and 338–355 (`kingmanTransition_support_isGood`, `kingmanAbsorption_support`) | Renamed `IsBinaryForest`, `IsGoodForest`, `kingmanTransition_support_good`, `kingmanAbsorption_support_good`; no species-tree or level-1 `Net` datatype copied. New here: `IsGoodForest.biUnion`, `IsGoodForest.singleton_mem`, `isGoodForest_iff_binaryHierarchy`, `exists_binary_completion`, `kingmanAbsorption_singletons_pos`. |
| `Relabel.lean` | `Phylogenetics/MSC/Relabel.lean`36–228, 322–329 (`relabelFamily`, `relabelFamilyEquiv`, membership lemmas, `roots_relabelFamily`, `card_relabelFamily`, `kingmanGenerator_relabelFamily`, `kingmanTransition_relabelFamily`, `kingmanAbsorption_relabelFamily`, `relabelFamily_refl`); `Phylogenetics/NMSC/Basic.lean`117–133 (`IsGood.relabel`), 136–145 (`lineages_relabel`), 157–165 (`relabel_forestBelow`) | Species-tree material dropped; `forestBelow_relabelFamily`, `relabelFamily_biUnion` restated for this project's `forestBelow`. |
| `Trace.lean` | `Phylogenetics/MSC/Marginal.lean`54–403 (`restrictForest`, the merge count `marg_sum_merges`, the intertwining of the generators, `kingmanTransition_lump`, `kingmanAbsorption_lump`) | The embedding `e : L' ↪ L` is replaced by a finite set `Z` of lineages, and `restrictForest e F` by `traceForest Z F := (F.filter (A ∩ Z).Nonempty).image (· ∩ Z)`, so that the restriction stays a forest on `L`; same proofs. New: `traceForest_forestBelow`, `traceForest_biUnion`. |
| `BinaryForest.lean`, addition | `Phylogenetics/NMSC/Symmetry.lean`223–237 (`ns_exists_two`) | `IsGoodForest.exists_two`, with the extra conclusion `C ⊆ A`; `IsGoodForest.eq_singletons` is new. |

The modules `Basic/Phylogenetics/NMSC/{Inheritance,History,Factor,Exchangeability}.lean` are new. `NMSC/Marginal.lean` has the
shape of `Phylogenetics/MSC/Marginal.lean`484–545 (`marg_enteringDist_comp_embedding`, `forestDist_comp_embedding`), by
induction along the hierarchy, carried out here on down-closed vertex sets of a network, with the urn consistency in place of
a product of independent parent assignments. `NMSC/Symmetry.lean` has the dichotomy of `NiceKernel.score` in
`Phylogenetics/NMSC/Symmetry.lean`319–375 (a cluster of two lineages stays and decides the split; otherwise the transpositions
make the splits equally likely), applied to the process with injected forests; the transposition argument is rewritten for
quartet trees on a set of four taxa instead of the lineages `Fin 4`.

These are finite real-array Kingman primitives. Finite-time nonnegativity,
normalization and support are proved; Tavaré's pure-death formula is proved. The
absorption limit exists on forests and is a probability distribution on one-root
forests (`Absorption.lean`), with the PMF wrappers in `PMF.lean`. The network
multispecies coalescent itself is not adapted from the source, whose `Net` syntax
is level-1 with independent inheritance: `Basic/Phylogenetics/NMSC/` is new.

`Basic/Phylogenetics/Defs.lean`, and its copy in `Challenge.lean`, carries the definitions `IsHierarchy`, `childClusters`, `unroot`, `roots`,
`kingmanGenerator`, `kingmanTransition`, `kingmanAbsorption` and `forestBelow`, adapted from the same commit
(`Phylogenetics/Hierarchy/Basic.lean`, `Phylogenetics/MSC/Defs.lean`, `Phylogenetics/MSC/Notions.lean`), with a notice in its header.
