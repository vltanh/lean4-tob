# Semple, Steel 2003: the Splits Equivalence Theorem

Source: C. Semple, M. Steel, *Phylogenetics*, Oxford University Press, 2003, Theorem 3.1.4. **The book wasn't read.** It was looked for: it isn't open, the publisher's pages answer 403, the Internet Archive's record `phylogenetics00char` has no text to search, and a public search of the Internet Archive's books finds the theorem's name only in other books. The statement here agrees with the one in S. Roch's lecture notes (Wisconsin, 2010, lecture 3), which give the book's Chapters 3 and 4 as their reference: "Let `Σ` be a collection of `X`-splits. Then, `Σ = Σ(T)` for some `X`-tree `T` if and only if the splits in `Σ` are pairwise compatible. Such tree is unique up to isomorphism." It also agrees with Theorem 2.1 of T. H. Klöpper's thesis (Tübingen, 2008), which calls it the Buneman theorem. The number 3.1.4 comes from Gusfield et al. 2007, line 156, and wasn't compared with the book.

So the proofs are standard arguments, which may differ from the book's. In particular, those notes prove existence by induction on the number of splits, "Tree Popping" with their Label Painting Lemma, and existence here comes from a laminar family in one step, while their uniqueness is part of the same induction, and here it's through consistent orientations. Check them against the book when it's available.

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
