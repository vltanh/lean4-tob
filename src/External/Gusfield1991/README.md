# Gusfield 1991: the Perfect Phylogeny Theorem

Source: D. Gusfield, *Efficient algorithms for inferring evolutionary trees*, Networks 21 (1991), 19--28, as recalled in
Gusfield et al. 2007, line 154 (the line numbers are explained in `src/Gusfield2007/README.md`), which also points to Gusfield 1997, Semple, Steel
2003, Theorem 3.1.4, and the Pairwise Compatibility Theorem of Felsenstein 2004. **The paper wasn't read.** It was looked for again: Wiley answers 403 to both the abstract and the PDF, and the Internet Archive has only the abstract page; OpenAlex and Semantic Scholar list no open copy, Gusfield's own list of papers has no link to it, and no copy of the 1988 technical report it began as was found. Unpaywall wasn't used, since it asks for an email address. Gusfield's book *ReCombinatorics* (2014) has the theorem as its Theorem 2.1.1, and the rooted form as Theorem 2.2.2, seen only as short snippets of a public search, which show the statements and not the proofs. So the proofs are the standard argument, as recalled, and whether they follow the source isn't known. The statements are those of line 154, which is what Gusfield et al. use.

Gusfield et al. 2007 use it at line 264, to get the tree `T̄` from Lemma 3, and for the case with no recombination.

`PerfectPhylogeny.lean` proves it in three forms: as an undirected tree on a matrix (`exists_isPerfectPhylogeny_iff`), as a network
with no recombination node deriving `M` (`exists_network_iff`), and as such a network with a given ancestral sequence
(`exists_network_rooted_iff`).

- From no conflict to a network: the rows that differ from a base at a column are disjoint from or nested with those of another
  column. These sets, with the singletons of rows, are a laminar family, and its tree carries the network. The base is the ancestral
  sequence in the rooted form, and in the others a row, flipped at the constant columns.
- From a network to no conflict: a recombination-free network has no blob, so this is a case of
  `GusfieldEtAl2004.exists_isBlob_of_incompatible`, whose proof doesn't use this theorem.

The rooted form needs no constant column in `M + S`: with `M = {S}`, a column must mutate on some arc, and without a
recombination node its state can't come back. The standing assumption of the paper gives that.

Line 156 also says that the network with ancestral sequence `S` is unique. That holds only when no arc or node can be suppressed:
`network_rooted_unique` states it for `IsReducedTree`, and `exists_network_of_no_conflict` gives such a network.

The module imports `SameBlob.lean`, and through it `Gusfield2007.Blobs`, since the statements are about those networks.
