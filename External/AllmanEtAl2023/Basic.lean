module

public import Basic.Phylogenetics.NetworkCuts
public import Basic.Phylogenetics.TreeSplits
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Allman, Baños, Mitchell, Rhodes 2023: the tree of blobs of a species network

E. S. Allman, H. Baños, J. D. Mitchell, J. A. Rhodes, *The tree of blobs of a species network:
identifiability under the coalescent*, J. Math. Biol. 86 (2023), 10.

* `theorem2`, the B-quartet inference rule, is proved, from the description of the tree of blobs
  by cut edges.
* `lemma3` and `closure_complete`, the combinatorial content of Theorem 3, are proved: from the
  B-quartets detected on induced 4-taxon networks, the inference rule reaches all B-quartets.
* `Corollary1`, the CF-detectability of 4-blobs for generic parameters, is the assumed result;
  see `External/AllmanEtAl2023/README.md`.
-/

@[expose] public noncomputable section

open Phylogenetics Phylogenetics.RootedNetwork MeasureTheory Set
open scoped Classical

namespace External.AllmanEtAl2023

variable {V E X : Type*} [Fintype X] [DecidableEq X] {N : RootedNetwork V E X}

/-- **Theorem 2 of the source (B-quartet Inference Rule; TINNiK Theorem 2).** If `{a,b,c,d}`
and `{b,c,d,e}` are B-quartets of the network, and on the induced 4-taxon network one of
`{a,b,c,e}`, `{a,b,d,e}`, `{a,c,d,e}` is a T-quartet with `a, e` separated or a B-quartet, then all
three are B-quartets. The source treats binary networks; the binary condition is not needed. -/
theorem theorem2 (hN : N.IsPhylogenetic) {a b c d e : X} (h5 : ({a, b, c, d, e} : Finset X).card = 5)
    (habcd : IsBQuartet N {a, b, c, d}) (hbcde : IsBQuartet N {b, c, d, e})
    {t : Finset X} (ht : t ∈ ({{a, b, c, e}, {a, b, d, e}, {a, c, d, e}} : Finset (Finset X)))
    (hrule : ¬ IsTreelike N t ∨ ∃ s ∈ treesOn t, InducedCutSplit N s ∧ Separated s a e)
    {q : Finset X} (hq : q ∈ ({{a, b, c, e}, {a, b, d, e}, {a, c, d, e}} : Finset (Finset X))) :
    IsBQuartet N q := by
  sorry

/-- **Theorem 3 of the source, combinatorial part.** From the 4-taxon sets with no cut-edge split on
their induced networks, and the quartet trees of the others, the closure under the inference rule
reaches every B-quartet of the network. With soundness (`theorem2`) this is what Theorem 3 uses of
Theorem 1. The induction is on the taxa of an induced subgraph, as in the source. -/
theorem closure_complete (hN : N.IsPhylogenetic) {q : Finset X} (hq : q.card = 4)
    (hB : IsBQuartet N q) :
    BInferred {q' | q'.card = 4 ∧ ¬ IsTreelike N q'} {s | InducedCutSplit N s} q := by
  sorry

/-- Soundness of the closure: everything the rule infers from the 4-taxon sets with no cut-edge split
on their induced networks is a B-quartet. -/
theorem closure_sound (hN : N.IsPhylogenetic) {q : Finset X}
    (h : BInferred {q' | q'.card = 4 ∧ ¬ IsTreelike N q'} {s | InducedCutSplit N s} q) :
    IsBQuartet N q := by
  sorry

end External.AllmanEtAl2023
