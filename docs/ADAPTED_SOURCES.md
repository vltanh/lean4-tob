# Adapted public sources

## Finite hierarchy kernel

Destination: `Basic/Phylogenetics/Hierarchy.lean`. Source repository: https://github.com/vltanh/lean4-phylogenetics, local clean commit `06f684e526e276ca2ccf668a1c3a808a2b8c181d`. Source license: Apache2.0; destination header preserves the source URL, commit and license reference. No source repository file was changed.

The source pins Lean/Mathlib v4.35.0-rc4. Destination was compiled successfully using `lake env lean Basic/Phylogenetics/Hierarchy.lean` with this project's Lean/Mathlib v4.36.0-rc1, no warnings. Only Mathlib finite-set/order/common-tactic modules are imported; no coalescent, level1 network, or project model module is imported.

## Source regions

All paths below are relative to the upstream repository at that exact commit.

- `Phylogenetics/MSC/Basic.lean`49–52: exact `IsHierarchy` definition.
- `Phylogenetics/MSC/Defs.lean`79–83: exact `childClusters` definition.
- `Phylogenetics/MSC/Defs.lean`124–127: exact `unroot` definition; formerly section-inherited L/Fintype/DecidableEq binders made explicit.
- `Phylogenetics/MSC/Notions.lean`36–43: exact `restrictClusters`, `restrictSplits` definitions.
- `Phylogenetics/MSC/Basic.lean`221–248: exact membership/subset facts; singleton has no children; distinct children disjoint.
- `Phylogenetics/Hierarchy/Basic.lean`63–77: exact common-element and nondisjoint-cluster nesting lemmas, inside namespace IsHierarchy.
- `Phylogenetics/MSC/Basic.lean`509–548: exact child existence/coverage/pairwise-disjointness/at-least-two children proofs. All require the source's precise cardinality conditions.
- `Phylogenetics/Hierarchy/Basic.lean`300–316: exact cluster/split restriction membership bridges; restored source `omit [Fintype X]` for the first lemma to avoid an unused section variable.
- `Phylogenetics/Hierarchy/Basic.lean`400–470: exact `mem_unroot`, `compl_mem_unroot`, compatibility helpers and `IsHierarchy.compatible_of_mem_unroot`.
- `Phylogenetics/Hierarchy/Basic.lean`317–337,345–350: exact trace nonemptiness, complement and properness helpers, and trace membership.

Two transparent adaptations remove unused metric data and keep the original proof argument:

1. `IsHierarchy.restrict`: combines the four topology-law proofs `SpeciesTree.restrict_univ_mem`, `restrict_singleton_mem`, `restrict_nonempty_of_mem`, `restrict_laminar` from `Phylogenetics/MSC/Notions.lean`47–80. Replace sigma.clusters by H and sigma's law fields by the corresponding conjuncts of hH. No argument uses lengths. The nonempty restriction-set premise is retained. This theorem is a generalized helper, not a renamed paper result.
2. `unroot_restrictClusters`: the finite-family identity underlying `SpeciesTree.restrict_unroot`, `Phylogenetics/Hierarchy/Basic.lean`612–635. Replace `(sigma.restrict S hS).clusters` by its definition `restrictClusters S H`; the source's metric tree/hierarchy/nonempty assumptions are unused in this set identity and therefore omitted rather than introduced as unused hypotheses. The membership equivalence proof, complement case split, witnesses and helper calls are unchanged.

These changes are dependency disentangling for general mathematical groundwork; none formalizes a numbered theorem of the three target papers or claims an arbitrary-network theorem follows from level1 results. The representation still requires a graph-to-hierarchy equivalence, split-to-tree realization, and refinement/contraction bridges. All remain explicit future work.

## Verification

The module compiles under the current pin. A copied-source diagnostic checked all26 public extracted definitions and theorems; each depends only on `propext`, `Classical.choice` and `Quot.sound`. No axiom, sorry, admit or native_decide was introduced. Source proof routes were retained, with only the two wrapper removals above.

## Parent clusters

`Basic/Phylogenetics/HierarchyParents.lean` copies the same upstream commit's
`Phylogenetics/Hierarchy/Basic.lean` lines 89–98 (intersection closure) and
226–284 (parent definition, minimality, membership and uniqueness). Only the
surrounding imports and namespace/variable declarations change. Two independent
readers compared these regions against the pinned source. This extraction has
no coalescent or network-level dependency.

`Basic/Phylogenetics/HierarchyGraph.lean` then constructs the actual rooted graph
from those clusters and parents. Its new proofs establish network validity when
there are at least two taxa, bridges, descendant/cluster equivalence and exact
labelled-cut correspondence with `unroot`. It does not claim an arc-to-unordered-
split bijection: the two arcs at a binary root can carry the same split.
