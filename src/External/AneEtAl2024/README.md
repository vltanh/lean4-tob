# Ané et al. 2024: exchangeability under the NMSC

Source: C. Ané, J. Fogg, E. S. Allman, H. Baños, J. A. Rhodes, *Anomalous networks under the
multispecies coalescent: theory and prevalence*, J. Math. Biol. 88 (2024),
<https://doi.org/10.1007/s00285-024-02050-7>. The source's text is not in the project's notes: the fact is taken as
TOB-QMC's Lemma 3 and ECToBlob's §5.1 state it.

Used by TOB-QMC's proof of Lemma 3: "any 4-tuple of species covering `{Pi, Pj, Pk, Pl}` have the same
expected qCFs ... see [1, 5]". `External.AneEtAl2024.exchangeability` proves it for this project's
NMSC, on arbitrary networks and with inheritance correlation, in the more general form `Phylogenetics.CutExchangeable`:
a taxon may be replaced by any other that a cut edge groups with it, away from the other three taxa.

The proof is in `Phylogenetics/NMSC/` of the library: the Markov property of the process at an arc (`Factor`), its
equivariance under relabelling lineages (`Symmetry`), and sampling consistency (`Marginal`). It also gives
the two forward facts that ECToBlob's Proposition 5.1 uses: a cut-edge split of an induced network makes the two alternatives equally
probable (`Phylogenetics.NMSC.cut_alternatives`), and a trivial 4-blob makes all three `1/3`
(`Phylogenetics.NMSC.trivial_uniform`).
