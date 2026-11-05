module

public import MainResults.ECToBlob
public import MainResults.TOBQMC
public import MainResults.TINNiK
public import MainResults.AllmanEtAl2023

/-!
# The main results: inferring the tree of blobs from quartets

Main results of four papers, each stated in plain terms and proved from its paper's library: **ECToBlob** (Rhodes, Allman,
Ané, Baños, bioRxiv v1, 2026), Theorems 3.1, 4.1, 8.2; **TOB-QMC** (Dai, Han, Molloy, bioRxiv v5, 2026), Theorems 1, 2 and the
consistency claim of §4.3; **TINNiK** (Allman, Baños, Mitchell, Rhodes, Algorithms Mol. Biol. 19, 2024), Theorem 4; **Allman et al.
2023** (Allman, Baños, Mitchell, Rhodes, J. Math. Biol. 86, 2023), Lemma 1, Theorems 1 to 4, Corollary 1, Proposition 1.
After them come what these papers say in passing, and the main results of the sources they
cite, each with a prefix: `nanuq_`,
`mitchell_`, `ane_`, `huber_`, `dinhBanos_`, `kaneTao_`, `legried_`, `studierKeppler_`. Each paper has its own front page and report, in `papers/<Paper>/`, which list every correction and departure; `docs/REPORT.md` gives an overview of the field.

All are proved, with no assumed result. This includes the CF-detectability of 4-blobs for generic parameters (Allman et
al. 2023, Theorem 1 and Corollary 1; TINNiK's Theorem 1), which `theorem4` uses.

The definitions are those of the library `Phylogenetics` and of `src/Basic/Defs.lean`, which has the three algorithms and
the papers' standing assumptions. A network is a directed multigraph with named arcs; the sides of its splits represent an
unrooted tree; the tree of blobs is the family of nonempty proper cut-edge sides. A quartet tree `ab|cd` is an unordered pair
of cherries. `HasCutSplitOn Y A` says that `A ∩ Y | Y \ A` is a split of a cut edge of the network induced on `Y`. The NMSC
is `geneTreeDist`, with one lineage per taxon; `ρ = 0` is independent inheritance. `iidProb dist n Ev` is the probability
that `n` independent draws from `dist` lie in `Ev`.

The theorems `allman_*` are on the paper's own objects, in `AllmanEtAl2023`: `IsBinaryNetwork`, its Definition 1; `Trd`, the reduced
unrooted tree of blobs; `cfTriple`, the concordance factor `CF_abcd`; `ForGenericParams N P`, "for generic numerical parameters", `P`
outside a null set.

The theorems of each paper are in a module of their own, with those of the sources that it cites, and each imports only what its theorems need: `MainResults.ECToBlob`, `MainResults.TOBQMC`, `MainResults.TINNiK`, `MainResults.AllmanEtAl2023`. This module imports the four, and nothing imports it.
-/
