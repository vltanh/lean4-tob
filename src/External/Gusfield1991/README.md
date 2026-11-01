# Gusfield 1991: the Perfect Phylogeny Theorem

Source: D. Gusfield, *Efficient algorithms for inferring evolutionary history*, Networks 21 (1991), 19--28, as recalled in
Gusfield et al. 2007, line 154 of `notes/sources/gusfield2007/pmc.txt`, which also points to Gusfield 1997, Semple, Steel
2003, Theorem 3.1.4, and the Pairwise Compatibility Theorem of Felsenstein 2004. Not read for this statement.

Gusfield et al. 2007 use it at line 264, to get the tree `T̄` from Lemma 3, and for the case with no recombination.

`PerfectPhylogeny.lean` states it with `sorry`, in three forms: as an undirected tree on a matrix, as a network with no
recombination node deriving `M`, and as such a network with a given ancestral sequence. This module imports
`Gusfield2007.Defs`, which imports Mathlib only, because the statement is about those networks.

The rooted form needs no constant column in `M + S`: with `M = {S}`, a column must mutate on some arc, and without a
recombination node its state can't come back. The standing assumption of the paper gives that.
