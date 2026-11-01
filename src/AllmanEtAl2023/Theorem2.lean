module

public import AllmanEtAl2023.Corollary2
public import AllmanEtAl2023.Concordance

/-!
# Allman, Baños, Mitchell, Rhodes 2023: Theorem 2, the B-quartet Inference Rule
-/

@[expose] public noncomputable section

open Phylogenetics Phylogenetics.RootedNetwork
open scoped Classical

namespace AllmanEtAl2023

variable {V E X : Type*} [DecidableEq X] {N : RootedNetwork V E X}

/-- The hypothesis (a) of Theorem 2: on the induced 4-taxon network, `t` is a T-quartet, with `a, e` separated in the reduced unrooted
tree of blobs. Whether the set is a T-quartet there is whether the tree is resolved (Lemma 1). -/
def InducedTreeSeparates (hN : IsBinaryNetwork N) (t : Finset X) (a e : X) : Prop :=
  ∃ (u v w z : X) (h : ({u, v, w, z} : Finset X).card = 4), ({u, v, w, z} : Finset X) = t ∧
    InducedHasQuartetTopology hN u v w z h ∧ Separated (quartetTree u v w z h) a e

/-- The hypothesis (b) of Theorem 2: `t` is a B-quartet on its induced 4-taxon network. -/
def InducedIsBlobQuartet (hN : IsBinaryNetwork N) (t : Finset X) : Prop :=
  ∃ ht : t.card = 4, IsBlobQuartetOnInduced hN (t : Set X) (nontrivial_coe_of_card_four ht) t

/-- **Theorem 2** (`a:thm:infrule`; B-quartet Inference Rule). Consider a rooted binary phylogenetic network `𝒩⁺` on `n` taxa, `n ≥ 5`.
Suppose that `{a, b, c, d}` and `{b, c, d, e}` are B-quartets on `𝒩⁺`. If on the induced 4-taxon network any one of `{a, b, c, e}`,
`{a, b, d, e}`, or `{a, c, d, e}` is (a) a T-quartet, with `a, e` separated in the reduced unrooted tree of blobs for the induced
4-taxon network, or (b) a B-quartet, then all of `{a, b, c, e}`, `{a, b, d, e}`, and `{a, c, d, e}` are B-quartets on `𝒩⁺`.

That the taxa are five distinct ones, and so `n ≥ 5`, is what the sets being sets of four taxa says. The proof is `rule_core`, which follows the paper's, through `Bridges.isBlobQuartet_iff_isBQuartet`, `Bridges.isBlobQuartetOnInduced_self_iff`, and
`Bridges.inducedHasQuartetTopology_iff`. -/
theorem theorem2 (hN : IsBinaryNetwork N) {a b c d e : X} (h5 : ({a, b, c, d, e} : Finset X).card = 5)
    (habcd : IsBlobQuartet N {a, b, c, d}) (hbcde : IsBlobQuartet N {b, c, d, e}) {t : Finset X}
    (ht : t ∈ ({{a, b, c, e}, {a, b, d, e}, {a, c, d, e}} : Finset (Finset X)))
    (hrule : InducedTreeSeparates hN t a e ∨ InducedIsBlobQuartet hN t) :
    IsBlobQuartet N {a, b, c, e} ∧ IsBlobQuartet N {a, b, d, e} ∧ IsBlobQuartet N {a, c, d, e} := by
  have hP := hN.isPhylogenetic
  have : Finite X := hP.finite_taxa
  let _ : Fintype X := Fintype.ofFinite X
  obtain ⟨hab, hac, had, hae, hbc, hbd, hbe, hcd, hce, hde⟩ := ne_of_card_five h5
  have h₁ := TreeMetric.card_four_of_ne hab hac had hbc hbd hcd
  have h₂ := TreeMetric.card_four_of_ne hbc hbd hbe hcd hce hde
  have q₁ := TreeMetric.card_four_of_ne hab hac hae hbc hbe hce
  have q₂ := TreeMetric.card_four_of_ne hab had hae hbd hbe hde
  have q₃ := TreeMetric.card_four_of_ne hac had hae hcd hce hde
  have hr : ¬ IsTreelike N t ∨ ∃ s ∈ treesOn t, InducedCutSplit N s ∧ Separated s a e := by
    rcases hrule with ⟨u, v, w, z, h, rfl, htop, hsep⟩ | ⟨ht4, hB⟩
    · exact Or.inr ⟨quartetTree u v w z h, mem_treesOn.2 (quartetTree_taxa _ _ _ _ _),
        (Bridges.inducedHasQuartetTopology_iff hN h).mp htop, hsep⟩
    · exact Or.inl ((Bridges.isBlobQuartetOnInduced_self_iff hN ht4).mp hB)
  have key : ∀ q ∈ ({{a, b, c, e}, {a, b, d, e}, {a, c, d, e}} : Finset (Finset X)), q.card = 4 → IsBlobQuartet N q :=
    fun q hq h4 => (Bridges.isBlobQuartet_iff_isBQuartet hP h4).mpr
      (rule_core hP h5 ((Bridges.isBlobQuartet_iff_isBQuartet hP h₁).mp habcd)
        ((Bridges.isBlobQuartet_iff_isBQuartet hP h₂).mp hbcde) ht (hr.imp_left (isBQuartet_of_not_isTreelike hP)) hq)
  exact ⟨key _ (by simp) q₁, key _ (by simp) q₂, key _ (by simp) q₃⟩

end AllmanEtAl2023
