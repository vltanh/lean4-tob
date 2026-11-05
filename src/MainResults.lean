module

public import MainResults.ECToBlob
public import MainResults.TOBQMC
public import MainResults.TINNiK
public import MainResults.AllmanEtAl2023
public import MainResults.Gusfield2007

/-!
# The main results: tree of blobs inference from quartets, and the theory of blobs behind it

Main results of five papers, each stated in plain terms and proved from its paper's library: **ECToBlob** (Rhodes, Allman,
Ané, Baños, bioRxiv v1, 2026), Theorems 3.1, 4.1, 8.2; **TOB-QMC** (Dai, Han, Molloy, bioRxiv v5, 2026), Theorems 1, 2 and the
consistency claim of §4.3; **TINNiK** (Allman, Baños, Mitchell, Rhodes, Algorithms Mol. Biol. 19, 2024), Theorem 4; **Allman et al.
2023** (Allman, Baños, Mitchell, Rhodes, J. Math. Biol. 86, 2023), Lemma 1, Theorems 1 to 4, Corollary 1, Proposition 1;
**Gusfield et al. 2007** (Gusfield, Bansal, Bafna, Song, J. Comput. Biol. 14, 2007), Lemma 4, Theorems 1 and 3 to 11, Corollaries 2,
3, and the refutation of its conjectures. After them come what these papers say in passing, and the main results of the sources they
cite, each with a prefix: `galled_` for Gusfield, Eddhu, Langley 2004, `myersGriffiths_`, `hudsonKaplan_`, `songHein_`, `nanuq_`,
`mitchell_`, `ane_`, `huber_`, `dinhBanos_`, `kaneTao_`, `legried_`, `studierKeppler_`. `docs/REPORT.md` and the reports of `docs/reports/`, one per paper, list every correction and departure.

All are proved, with no assumed result. This includes the CF-detectability of 4-blobs for generic parameters (Allman et
al. 2023, Theorem 1 and Corollary 1; TINNiK's Theorem 1), which `theorem4` uses. One theorem is conditional, and says so in its
statement: `gusfield_theorem10Printed_multiple_false_of_search` has the finite computation `printedMSearch` as a hypothesis, which the
kernel hasn't completed.

The definitions are those of the library `Phylogenetics` and of `src/Basic/Defs.lean`, which has the three algorithms and
the papers' standing assumptions. A network is a directed multigraph with named arcs; the sides of its splits represent an
unrooted tree; the tree of blobs is the family of nonempty proper cut-edge sides. A quartet tree `ab|cd` is an unordered pair
of cherries. `HasCutSplitOn Y A` says that `A ∩ Y | Y \ A` is a split of a cut edge of the network induced on `Y`. The NMSC
is `geneTreeDist`, with one lineage per taxon; `ρ = 0` is independent inheritance. `iidProb dist n Ev` is the probability
that `n` independent draws from `dist` lie in `Ev`.

The theorems `allman_*` are on the paper's own objects, in `AllmanEtAl2023`: `IsBinaryNetwork`, its Definition 1; `Trd`, the reduced
unrooted tree of blobs; `cfTriple`, the concordance factor `CF_abcd`; `ForGenericParams N P`, "for generic numerical parameters", `P`
outside a null set. The theorems `gusfield_*` are on sequences of binary sites, in `Gusfield2007`, whose `Defs` imports Mathlib only:
a `Network` derives a set of rows `M` at its leaves, `Crossover` is the model of recombination, and `R`, `F` are the least numbers of
recombination nodes in a network for `M` and in a fully decomposed one.

The theorems of each paper are in a module of their own, with those of the sources that it cites, and each imports only what its theorems need: `MainResults.ECToBlob`, `MainResults.TOBQMC`, `MainResults.TINNiK`, `MainResults.AllmanEtAl2023`, `MainResults.Gusfield2007`. This module imports the five, and nothing imports it.
-/
