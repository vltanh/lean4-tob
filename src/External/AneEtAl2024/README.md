# Ané et al. 2024: exchangeability under the NMSC

Source: C. Ané, J. Fogg, E. S. Allman, H. Baños, J. A. Rhodes, *Anomalous networks under the
multispecies coalescent: theory and prevalence*, J. Math. Biol. 88 (2024),
<https://doi.org/10.1007/s00285-024-02050-7>, read in its bioRxiv text (10.1101/2023.08.18.553582).

Used by TOB-QMC's proof of Lemma 3: "any 4-tuple of species covering `{Pi, Pj, Pk, Pl}` have the same
expected qCFs ... see [1, 5]". `External.AneEtAl2024.exchangeability` proves it for this project's
NMSC, on arbitrary networks and with inheritance correlation, in the more general form `Phylogenetics.CutExchangeable`:
a taxon may be replaced by any other that a cut edge groups with it, away from the other three taxa.

The proof is in `Phylogenetics/NMSC/` of the library: the Markov property of the process at an arc (`Factor`), its
equivariance under relabelling lineages (`Symmetry`), and sampling consistency (`Marginal`). It also gives
the two forward facts that ECToBlob's Proposition 5.1 uses: a cut-edge split of an induced network makes the two alternatives equally
probable (`Phylogenetics.NMSC.cut_alternatives`), and a trivial 4-blob makes all three `1/3`
(`Phylogenetics.NMSC.trivial_uniform`).

## Proposition 12 (`Proposition12.lean`)

"Under the common inheritance model with `ρ = 1`, a 4-taxon binary metric network is not anomalous", by the source's proof: the mixture over displayed trees, the entries of each displayed tree, a convex sum.
`proposition12` is Definition 1, on any four taxa of any network at weak parameters; `proposition12_class2` and `proposition12_class1` are Definition 2. Being binary is not used. The strict form on cut-edge splits is
`Phylogenetics.RootedNetwork.nmscCF_lt_rho_one` in `src/Basic/RhoOne.lean`.

## Section 3.3, `3₂`-cycle containment (`Rules.lean`)

"Even the number of subnetworks with exactly `1` hybrid node can be as large as `k 2^(k-1)`": `card_oneHybridChoices` counts these choices.

Rule 2, "If the edges that are incident to `B` and that exit `B` ... have at most 2 descendants total, then `B` does not contain a `3₂`-cycle", is `rule2`, for the `3₂`-cycles of subnetworks, in the sense of `External.AllmanBanosRhodes2019.HasThreeTwoCycle`. Its reason, "the number of descendant leaves of a `3₂`-cycle is either 3 ... or 4", is `three_le_card_belowBlob` and `card_belowBlob_of_root`. "Deciding if rule 1 or 2 applies takes constant time after calculating a blob decomposition": on four taxa at most four arcs leave a blob by a bridge (`card_exitArcs_le`), so that the rules read at most four sets of descendants, each a subset of four taxa. The blob decomposition is `Basic/BridgeDFS.lean`.

Not formalized: rule 1 in general, which is the source's Lemma 11, with its Lemmas 9 and 10. On a level-1 network it is the definition of a `3₂`-cycle by blocks. On a network with several hybrid nodes in the blob it constructs a cycle of a subnetwork from four paths.
