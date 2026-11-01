# Semple, Steel 2003: the Splits Equivalence Theorem

Source: C. Semple, M. Steel, *Phylogenetics*, Oxford University Press, 2003, Theorem 3.1.4. Not read for this statement:
it's recalled from the book and from how Gusfield et al. 2007 use it. Check it against the book when the book is available.

Gusfield et al. 2007 use it twice. At line 156 of `notes/sources/gusfield2007/pmc.txt`, as a reference for the Perfect
Phylogeny Theorem. At line 344, in the proof of Theorem 4: "the splits of an undirected tree uniquely define the tree".

`SplitsEquivalence.lean` states it for `X`-trees, with `sorry`: a collection of `X`-splits is the split system of an
`X`-tree exactly when its splits are pairwise compatible, and the `X`-tree is then unique up to isomorphism.

A proof can start from the library: `Phylogenetics.isUnrootedTree_iff` is the existence half for split families containing
all the singletons, and `Phylogenetics.hierarchyNetwork` is the graph of a hierarchy.
