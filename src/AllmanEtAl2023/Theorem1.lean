module

public import AllmanEtAl2023.Theorem1b

/-!
# Allman, Baños, Mitchell, Rhodes 2023: Theorem 1

The statement of the paper on `T_rd(𝒩⁻)` and the triple `CF_abcd`, with its statements (a), (b) of the proof, and the claim
of its proof that (a) has "`CF` is `(ab|cd)`-cut for all parameters".
-/

@[expose] public noncomputable section

open Phylogenetics Phylogenetics.RootedNetwork
open scoped Classical

namespace AllmanEtAl2023

variable {V E X : Type*} [Fintype V] [Fintype E] [Fintype X] [DecidableEq X] {N : RootedNetwork V E X}

/-- **Theorem 1** (`a:thm:CFdetect`; `CF`-detectability of 4-blobs on 4-taxon networks). Consider a 4-taxon rooted binary phylogenetic
network `𝒩⁺` on taxa `{a, b, c, d}` with quartet concordance factor `CF = CF_abcd` and reduced unrooted tree of blobs
`T = T_rd(𝒩⁻)`. Then under the NMSC for generic parameters:
1. `T` has the quartet tree topology `ab|cd` if, and only if, `CF_abcd` is strictly `(ab|cd)`-cut.
2. `T` has the unresolved quartet topology if, and only if, `CF_abcd` is non-cut.

One exceptional set serves all namings of the taxa, of which there are finitely many. The text followed is the PMC manuscript, not the journal's version. -/
theorem theorem1 (hN : IsBinaryNetwork N) (hcard : Fintype.card X = 4) :
    ForGenericParams N fun θ => ∀ (a b c d : X) (h : ({a, b, c, d} : Finset X).card = 4),
      ((Trd hN (nontrivial_of_card_four hcard)).HasQuartetTopology a b c d ↔
        IsStrictlyCutAtFirst (cfTriple N θ a b c d h)) ∧
      ((Trd hN (nontrivial_of_card_four hcard)).HasStarTopology a b c d ↔
        IsNonCutCF (cfTriple N θ a b c d h)) := by
  refine ((theorem1_a hN hcard).union (theorem1_b hN hcard)).mono ?_
  rintro θ ⟨hθ, hnot⟩
  by_contra hall
  have ha : ∀ (a b c d : X) (h : ({a, b, c, d} : Finset X).card = 4),
      (Trd hN (nontrivial_of_card_four hcard)).HasQuartetTopology a b c d → IsStrictlyCutAtFirst (cfTriple N θ a b c d h) := by
    by_contra h'
    exact hall (Or.inl ⟨hθ, h'⟩)
  have hb : ∀ (a b c d : X) (h : ({a, b, c, d} : Finset X).card = 4),
      (Trd hN (nontrivial_of_card_four hcard)).HasStarTopology a b c d → IsNonCutCF (cfTriple N θ a b c d h) := by
    by_contra h'
    exact hall (Or.inr ⟨hθ, h'⟩)
  -- "Were it not for the distinction between 'cut' and 'strictly cut', these statements would immediately yield claims 1 and 2."
  have hdet : CFDetectable N (nmscCF N θ 0) := by
    refine ⟨fun s hs => ?_, fun q hq hnt => ?_⟩
    · obtain ⟨a, b, c, d, h, rfl⟩ := TreeMetric.exists_eq_quartetTree s
      exact (isStrictlyCutAtFirst_iff (nmscCF N θ 0) h).mp (ha a b c d h ((hasQuartetTopology_iff_inducedCutSplit hN hcard h).mpr hs))
    · obtain ⟨a, b, c, d, h⟩ := exists_names_of_card_four hcard
      have hu : ({a, b, c, d} : Finset X) = Finset.univ := Finset.eq_univ_of_card _ (h.trans hcard.symm)
      have hqu : q = {a, b, c, d} := by
        rw [hu]
        exact Finset.eq_univ_of_card _ (hq.trans hcard.symm)
      subst hqu
      exact (isNonCutCF_iff (nmscCF N θ 0) h).mp (hb a b c d h ((hasStarTopology_iff_not_isTreelike hN hcard h).mpr hnt))
  refine hnot fun a b c d h => ⟨?_, ?_⟩
  · rw [hasQuartetTopology_iff_inducedCutSplit hN hcard h, hdet.inducedCutSplit_iff]
    exact (isStrictlyCutAtFirst_iff (nmscCF N θ 0) h).symm
  · -- by Lemma 1, `T` is unresolved or resolved
    refine ⟨hb a b c d h, fun hnc => ?_⟩
    rcases lemma1 hN hcard with ⟨-, -, hS, -⟩ | ⟨-, -, ⟨p, q, r, t, hp, hH⟩, -⟩
    · exact hS a b c d h
    · have hnt := (hdet.not_isTreelike_iff h).mpr ((isNonCutCF_iff (nmscCF N θ 0) h).mp hnc)
      have hu : ({a, b, c, d} : Finset X) = ({p, q, r, t} : Finset X) :=
        (Finset.eq_univ_of_card _ (h.trans hcard.symm)).trans (Finset.eq_univ_of_card _ (hp.trans hcard.symm)).symm
      exact absurd ⟨_, mem_treesOn.mpr ((quartetTree_taxa _ _ _ _ _).trans hu.symm), (hasQuartetTopology_iff_inducedCutSplit hN hcard hp).mp hH⟩ hnt

end AllmanEtAl2023
