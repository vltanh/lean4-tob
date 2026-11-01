# Gusfield, Eddhu, Langley 2004: sites of one component lie on one blob

Source: D. Gusfield, S. Eddhu, C. Langley, *Optimal, efficient reconstruction of phylogenetic networks with constrained
recombination*, J. Bioinformatics and Computational Biology 2 (2004), 173--213, as cited by Gusfield et al. 2007, lines 182
to 185 and 375 of `notes/sources/gusfield2007/pmc.txt`: "all sites from the same non-trivial connected component of G(M)
must appear on the same blob". Not read for this statement.

`SameBlob.lean` states it with `sorry`, for any set of rows that label nodes of the network, which gives `M`, `M + S` and
the set `L` of all node labels at once. This module imports `Gusfield2007.Defs`, which imports Mathlib only, because the
statement is about those networks.

Gusfield et al. 2007 say it's easy. `Gusfield2007.converse` and `Gusfield2007.converse_rooted` are derived from it.

A proof: a site on a tree arc, which is a bridge, is flipped exactly on the leaves below the arc, so it's compatible with
every other site. Two sites on different classes of `T′` are compatible because each side of a tree arc between them has one
of the two sites constant.
