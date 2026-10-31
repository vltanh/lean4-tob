# Ané et al. 2024: exchangeability under the NMSC

Source: C. Ané, J. Fogg, E. S. Allman, H. Baños, J. A. Rhodes, *Anomalous networks under the
multispecies coalescent: theory and prevalence*, J. Math. Biol. 88 (2024),
<https://doi.org/10.1007/s00285-024-02050-7>.

Used by TOB-QMC's proof of Lemma 3: "any 4-tuple of species covering `{Pi, Pj, Pk, Pl}` have the same
expected qCFs ... see [1, 5]". `External.AneEtAl2024.Exchangeability` states it for this project's
NMSC, on arbitrary networks and with inheritance correlation.

**Assumed, not proved here.** Lean lacks the Markov decomposition of the process at a cut edge and its
equivariance under relabelling lineages; building them on the order-free formula of
`Phylogenetics.geneTreeDist` is a large but feasible effort. The statements that use the assumption
take it as a named hypothesis.
