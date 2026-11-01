module

public import External.LegriedEtAl2021.Bridge
public import ECToBlob.Section3

/-!
# ECToBlob's Remark 3.4: duplication and loss

"Under models with gene duplication and loss, (3.1) is also known to hold when the species phylogeny is a tree, either when a single
gene copy is sampled per individual, or when all gene copies from each individual are treated as multiple alleles [24, without ILS],
[27, 21, with ILS]. However, it remains an open question whether these results hold for duplication and loss models when the species
phylogeny has reticulations."

* `remark3_4_single`, `remark3_4_multi`: the two claims from [24], Legried, Molloy, Warnow and Roch, without incomplete lineage sorting,
  on the model of `External.LegriedEtAl2021`: (3.1) on a species tree, where every edge is a cut edge. See
  `External.LegriedEtAl2021.eq5` and `External.LegriedEtAl2021.eq7`.
  The hypotheses that the expected numbers are positive follow from `External.LegriedEtAl2021.present_pos` and
  `External.LegriedEtAl2021.numChoices_pos`, when a copy can go through each edge with no duplication and no loss.
* `remark3_4_displays`, `remark3_4_sum`: the same claim on the library's objects: on the network of the species tree (`speciesNetwork`), (3.1) in
  the form of the hypothesis of Theorem 3.1, for probabilities of quartet trees that sum to one on four taxa. The bridges are
  `External.LegriedEtAl2021.displays_treeOfBlobs_iff` for species trees and `External.LegriedEtAl2021.displays_pickTree_iff` for gene trees.
* `OpenQuestion`: the open question, as a statement.
* `remark3_4_mixture`: a partial answer that isn't in the paper, if a gene family follows one displayed species tree.

The results with incomplete lineage sorting, [27] Markin and Eulenstein, Theorem 2, and [21] Hill, Legried and Roch, Theorem 2, are
under the DLCoal model, of a locus tree and a bounded coalescent within it. Neither that model nor these results are formalized.
-/

@[expose] public noncomputable section

open scoped ENNReal
open Phylogenetics Phylogenetics.RootedNetwork External.LegriedEtAl2021

namespace ECToBlob.Remark34

variable {X : Type}

/-- **Remark 3.4, one gene copy** (`ecto:rem3_4`). On a species tree, with `a`, `b` separated from `c`, `d` by an edge, which is a cut
edge, (3.1) holds under duplication and loss without incomplete lineage sorting, for one gene copy picked uniformly in each species. This
is the source's (5). -/
theorem remark3_4_single {T : SpeciesTree X} (hT : T.Nodup) {A B C D : X} (hAB : A ≠ B) (hCD : C ≠ D) (hA : T.Has A) (hB : T.Has B)
    (hC : T.Has C) (hD : T.Has D) (hq : T.IsQuartet A B C D)
    (hpos : 0 < expect (geneLaw T) fun L => ind (Present A B C D L)) :
    max (probTopology T (fun a b c d => Pat a c b d) A B C D) (probTopology T (fun a b c d => Pat a d b c) A B C D) <
      probTopology T Pat A B C D := by
  obtain ⟨h₁, h₂⟩ := eq5 hT hAB hCD hA hB hC hD hq hpos
  exact max_lt h₁ h₂

/-- **Remark 3.4, on the network of the species tree** (`ecto:rem3_4`). For the species network, the tree of blobs of which is the unrooted
species tree, (3.1) holds in the form of the hypothesis of Theorem 3.1, with `p` the probability of a quartet tree under a uniform pick of one
gene copy per species. -/
theorem remark3_4_displays {Y : Type} [Fintype Y] [DecidableEq Y] {T : SpeciesTree Y} (hT : T.Nodup) (hall : ∀ x, T.Has x) (hS : T.Survives) :
    ∀ s, Displays (treeOfBlobs (speciesNetwork T hT hall)) s → ∀ r ∈ s.alternatives, quartetP T r < quartetP T s :=
  fun _ hs _ hr => quartetP_lt hT hall hS hs hr

/-- These `p` are probabilities on the quartet trees of each set of four taxa: they sum to one. -/
theorem remark3_4_sum {Y : Type} [Fintype Y] [DecidableEq Y] {T : SpeciesTree Y} (hS : T.Survives) (hall : ∀ x, T.Has x) {q : Finset Y}
    (hq : q.card = 4) : ∑ r ∈ treesOn q, quartetP T r = 1 :=
  sum_treesOn_quartetP hS hall hq

/-- **The share of a topology among all the choices of one gene copy in each species**, as multiple alleles. -/
def alleleShare (T : SpeciesTree X) (pat : Path → Path → Path → Path → Prop) (A B C D : X) : ℝ≥0∞ :=
  expect (geneLaw T) (numTopology pat A B C D) / expect (geneLaw T) (numChoices A B C D)

/-- **Remark 3.4, multiple alleles** (`ecto:rem3_4_alleles`). On a species tree, with `a`, `b` separated from `c`, `d` by an edge, (3.1)
holds under duplication and loss without incomplete lineage sorting, with all gene copies treated as multiple alleles, when the expected
number of choices is positive and finite. This is the source's (7), divided by that number. -/
theorem remark3_4_multi {T : SpeciesTree X} (hT : T.Nodup) {A B C D : X} (hAB : A ≠ B) (hCD : C ≠ D) (hA : T.Has A) (hB : T.Has B)
    (hC : T.Has C) (hD : T.Has D) (hq : T.IsQuartet A B C D) (hpos : 0 < expect (geneLaw T) (numChoices A B C D))
    (hfin : expect (geneLaw T) (numChoices A B C D) < ⊤) :
    max (alleleShare T (fun a b c d => Pat a c b d) A B C D) (alleleShare T (fun a b c d => Pat a d b c) A B C D) <
      alleleShare T Pat A B C D := by
  obtain ⟨h₁, h₂⟩ := eq7 hT hAB hCD hA hB hC hD hq hpos hfin
  exact max_lt (div_lt_div_of_lt h₁ hpos.ne' hfin.ne) (div_lt_div_of_lt h₂ hpos.ne' hfin.ne)

/-- **A gene family that follows one species tree picked at random** (`ecto:rem3_4_mixture`). This is a partial answer to the open
question that isn't in the paper: if a gene family first picks a species tree, such as a tree displayed by a network, and all the trees
that can be picked display `AB|CD`, as they do when a cut edge of the network separates `A`, `B` from `C`, `D`, then (3.1) holds for
one gene copy. The network's own arcs aren't used, and no reticulation acts on each gene copy separately, which is the case left open. -/
theorem remark3_4_mixture {ι : Type*} (ν : PMF ι) (T : ι → SpeciesTree X) {A B C D : X} (hAB : A ≠ B) (hCD : C ≠ D)
    (h : ∀ i, ν i ≠ 0 → (T i).Nodup ∧ (T i).Has A ∧ (T i).Has B ∧ (T i).Has C ∧ (T i).Has D ∧ (T i).IsQuartet A B C D)
    (hpos : 0 < expect (ν.bind fun i => geneLaw (T i)) fun L => ind (Present A B C D L)) :
    max (expect (ν.bind fun i => geneLaw (T i)) (Alt pickWeight A B C D))
        (expect (ν.bind fun i => geneLaw (T i)) (Alt₂ pickWeight A B C D)) <
      expect (ν.bind fun i => geneLaw (T i)) (Sc pickWeight A B C D) := by
  obtain ⟨h₁, h₂⟩ := mixture_dom pickWeight ν T hAB hCD h
  have ht : expect (ν.bind fun i => geneLaw (T i)) (Tot pickWeight A B C D) =
      expect (ν.bind fun i => geneLaw (T i)) fun L => ind (Present A B C D L) :=
    congrArg _ (funext (Tot_pick A B C D))
  have hfin : (expect (ν.bind fun i => geneLaw (T i)) fun L => ind (Present A B C D L)) < ⊤ :=
    (expect_ind_le_one _ _).trans_lt ENNReal.one_lt_top
  rw [ht] at h₁ h₂
  exact max_lt (h₁.2 hpos hfin) (h₂.2 hpos hfin)

/-- **The open question of Remark 3.4** (`ecto:rem3_4_open`): "it remains an open question whether these results hold for duplication
and loss models when the species phylogeny has reticulations". The paper defines no such model, and the sources it cites treat trees: how
a gene copy behaves at a reticulation is part of the question. So the model is a parameter: `M` indexes the parameters of a duplication
and loss model on networks, `N m` is the network, and `p m` the probabilities of quartet topologies of gene trees, under one of the two
samplings of the remark. The question is whether (3.1) holds, in the form of Theorem 3.1's hypothesis. -/
def OpenQuestion {V E X : Type*} [Fintype X] [DecidableEq X] {M : Type*} (N : M → RootedNetwork V E X) (p : M → QuartetTree X → ℝ) : Prop :=
  ∀ m s, Displays (treeOfBlobs (N m)) s → ∀ r ∈ s.alternatives, p m r < p m s

end ECToBlob.Remark34
