# Semple, Steel 2003: the Splits Equivalence Theorem

Source: C. Semple, M. Steel, *Phylogenetics*, Oxford University Press, 2003, Theorem 3.1.4. The book wasn't read: it's a printed book,
and no copy was looked for. The statement is recalled from the book and from how Gusfield et al. 2007 use it, and the proofs are
standard arguments, which may differ from the book's. Check them against the book when it's available.

Gusfield et al. 2007 use it twice. At line 156 (the line numbers are explained in `src/Gusfield2007/README.md`), as a reference for the Perfect
Phylogeny Theorem. At line 344, in the proof of Theorem 4: "the splits of an undirected tree uniquely define the tree".

`SplitsEquivalence.lean` proves it for `X`-trees: a collection of `X`-splits is the split system of an `X`-tree exactly when its
splits are pairwise compatible (`exists_xTree_iff`), and the `X`-tree is then unique up to isomorphism (`xTree_unique`).

- Existence: the sides not containing a base element `x₀` are a laminar family, whose graph is the tree.
- Compatibility of the splits of a tree: two edges have sides pointing away from each other, which share no node.
- Uniqueness: each node orients the splits towards itself. The orientations of the nodes are the consistent orientations of the
  split system, adjacent nodes are those whose orientations differ in one split, and a labelled node has the orientation given by
  its label.

`Support.lean` has what's about trees and laminar families, also used by the Perfect Phylogeny Theorem and by `Gusfield2007.TreeFacts`. Both modules import Mathlib
only, since `Gusfield2007` does. The library has related results in another representation: `Phylogenetics.isUnrootedTree_iff` is
the existence half for split families containing all the singletons, and `Phylogenetics.hierarchyNetwork` is the graph of a hierarchy.
