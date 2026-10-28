/-
Adapted from https://github.com/vltanh/lean4-phylogenetics,
commit 06f684e526e276ca2ccf668a1c3a808a2b8c181d.
Licensed under the Apache License, Version 2.0:
https://www.apache.org/licenses/LICENSE-2.0
Exact source regions and adaptations: docs/COALESCENT_SOURCES.md.
-/
module

public import Mathlib.Analysis.Normed.Algebra.Exponential
public import Mathlib.Topology.Instances.Matrix

/-!
# Finite Kingman coalescent data

Forest states retain all gene-lineage clusters. The transition is the actual
matrix exponential of the pairwise-merger generator. Root absorption is defined
as its entrywise limit; its existence, normalization and support proofs remain
in uncompiled local drafts at this handoff. No species-tree or network syntax
is assumed here.
-/

@[expose] public section

namespace Phylogenetics

open Finset


variable {L : Type*} [Fintype L] [DecidableEq L]

/-- The roots of a forest `F`: its maximal clusters. -/
def roots (F : Finset (Finset L)) : Finset (Finset L) :=
  F.filter fun A => ∀ B ∈ F, A ⊆ B → B = A

/-- The generator of Kingman's coalescent on forests. From a forest `F` with `k` roots, each of
the `k.choose 2` pairs of distinct roots `A, B` merges at rate `1`; the merge adds the cluster
`A ∪ B` to `F`. -/
noncomputable def kingmanGenerator : Matrix (Finset (Finset L)) (Finset (Finset L)) ℝ :=
  fun F G =>
    if G = F then -((#(roots F)).choose 2 : ℝ)
    else if ∃ A ∈ roots F, ∃ B ∈ roots F, A ≠ B ∧ G = insert (A ∪ B) F then 1 else 0

/-- The transition probabilities of Kingman's coalescent on forests over a time `t`, in
coalescent units: the matrix exponential `exp (t • Q)` of the generator. -/
noncomputable def kingmanTransition (t : ℝ) : Matrix (Finset (Finset L)) (Finset (Finset L)) ℝ :=
  NormedSpace.exp (t • kingmanGenerator)

/-- The transition probabilities of Kingman's coalescent on forests over an infinite time: the
entrywise limits of `kingmanTransition t` as `t → ∞`. -/
noncomputable def kingmanAbsorption : Matrix (Finset (Finset L)) (Finset (Finset L)) ℝ :=
  fun F G => Filter.limUnder Filter.atTop fun t : ℝ => kingmanTransition t F G


variable {X : Type*} [DecidableEq X]

/-- The forest of singleton clusters `{l}` of the lineages `l` sampled from the taxa in `A` (at an
internal cluster these singletons already belong to the forests of its children). -/
def sampledForest (s : L → X) (A : Finset X) : Finset (Finset L) :=
  (univ.filter fun l => s l ∈ A).image fun l => {l}


/-- The forest of `n` singleton lineages `{0}, …, {n - 1}`. -/
def singletonForest (n : ℕ) : Finset (Finset (Fin n)) :=
  univ.image fun l => {l}

/-- The `g_ij(t)` of Allman, Degnan and Rhodes (2011, Section 3): the probability that `i` lineages
coalesce into `j` lineages within time `t` under Kingman's coalescent, that is, that the forest
reached from `i` singletons after time `t` has `j` roots. -/
noncomputable def coalescenceProb (i j : ℕ) (t : ℝ) : ℝ :=
  ∑ G : Finset (Finset (Fin i)), if #(roots G) = j then kingmanTransition t (singletonForest i) G
    else 0


end Phylogenetics
