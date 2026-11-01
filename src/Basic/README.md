# What the papers share, beyond the library

| Module | Content | Possible home |
| --- | --- | --- |
| `Defs` | **The definitions specific to the three papers**: the algorithms ECToBlob, TINNiK and TOB-QMC with their options and steps, and the papers' standing assumptions | This project |
| `Testing/*` | Hypothesis tests on quartet counts: statistics and p-values, combining p-values, independent samples, tails, limit laws through the trinomial central limit theorem | This project |
| `ForMathlib/*` | Analysis and probability that do not mention phylogenetics: zero sets of analytic functions, finite optimization, the error function, `x log x`, the multinomial likelihood, the Gaussian plane and its tails, transferring limit laws | Mathlib |
| `LocalObjective` | The local objective at a multifurcation of ECToBlob's Theorem 3.1: attaching subtrees, sums over representatives | This project |
| `RhoOne` | No anomalous quartets at `ρ = 1`: the strict form of Proposition 12 of Ané et al. 2024 | The library `Phylogenetics` |
| `General` | Taxa that a parent choice leaves unresolved have concordance factors `1/3`, for all correlations | The library `Phylogenetics` |

Networks, trees, quartets, the coalescent and the theory of the network multispecies coalescent are in the library `Phylogenetics`.
`notes/migration_renames.tsv` and `notes/migration_modules.tsv` list where each declaration of the former `src/Basic/` went.
