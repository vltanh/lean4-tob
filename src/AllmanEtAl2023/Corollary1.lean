module

public import AllmanEtAl2023.Theorem1
public import AllmanEtAl2023.InducedTransfer

/-!
# Allman, Baños, Mitchell, Rhodes 2023: Corollary 1

Through the paper's induced network (Definition 6), with what "identifiable from `CF_Q`" means: a function of `CF_Q`
alone, `readTopology`, returns the topology, for generic parameters on the network.
-/

@[expose] public noncomputable section

open Phylogenetics Phylogenetics.RootedNetwork
open scoped Classical

namespace AllmanEtAl2023

variable {V E X : Type*} [Fintype V] [Fintype E] [Fintype X] [DecidableEq X] {N : RootedNetwork V E X}

omit [Fintype X] in
/-- **`CF`s of the induced network are those of the network**: `nmscCF_induced`, on the triple. -/
theorem cfTriple_induced [Fintype X] (hN : IsBinaryNetwork N) {θ : MetricData E} (hθ : N.IsMetric θ) {Q : Finset X} (hQ : (Q : Set X).Nontrivial) [Fintype (InducedV hN (Q : Set X) hQ)]
    [Fintype (InducedE hN (Q : Set X) hQ)] {a b c d : (Q : Set X)} (h' : ({a, b, c, d} : Finset (Q : Set X)).card = 4) (h : ({a.1, b.1, c.1, d.1} : Finset X).card = 4) :
    cfTriple (induced hN (Q : Set X) hQ) (inducedParams hN (Q : Set X) hQ θ) a b c d h' = cfTriple N θ a.1 b.1 c.1 d.1 h := by
  unfold cfTriple quartetCF
  rw [nmscCF_induced hN hθ (Q : Set X) hQ, nmscCF_induced hN hθ (Q : Set X) hQ, nmscCF_induced hN hθ (Q : Set X) hQ, Bridges.map_quartetTree h' h, Bridges.map_quartetTree _ (card_acbd h),
    Bridges.map_quartetTree _ (card_adbc h)]

/-- What Theorem 1 says on the network induced on `Q`, in the `CF`s of the network. -/
def InducedDetectable (hN : IsBinaryNetwork N) (θ : MetricData E) (Q : Finset X) (hQ : Q.card = 4) : Prop :=
  ∀ (a b c d : (Q : Set X)) (h : ({a.1, b.1, c.1, d.1} : Finset X).card = 4),
    ((inducedTrd hN Q hQ).HasQuartetTopology a b c d ↔ IsStrictlyCutAtFirst (cfTriple N θ a.1 b.1 c.1 d.1 h)) ∧
      ((inducedTrd hN Q hQ).HasStarTopology a b c d ↔ IsNonCutCF (cfTriple N θ a.1 b.1 c.1 d.1 h))

/-- **"Since the generic conditions only exclude a set of measure zero from the numerical parameter space of each 4-taxon network, they give rise to a generic condition on numerical parameter
values on the `n`-taxon network"**, for one 4-taxon network. -/
theorem forGenericParams_inducedDetectable (hN : IsBinaryNetwork N) (Q : Finset X) (hQ : Q.card = 4) : ForGenericParams N fun θ => InducedDetectable hN θ Q hQ := by
  have hnt := nontrivial_coe_of_card_four hQ
  let _ : Fintype (InducedV hN (Q : Set X) hnt) := Fintype.ofFinite _
  let _ : Fintype (InducedE hN (Q : Set X) hnt) := Fintype.ofFinite _
  have hc : Fintype.card (Q : Set X) = 4 := by
    rw [← Nat.card_eq_fintype_card, Nat.card_coe_set_eq, Set.ncard_coe_finset]
    exact hQ
  have hT := theorem1 (induced_isBinaryNetwork hN (Q : Set X) hnt) hc
  refine (isGenericNull_inducedParams hN (Q : Set X) hnt hT).mono ?_
  rintro θ ⟨hθ, hnot⟩
  refine ⟨hθ, isMetric_inducedParams hN hθ (Q : Set X) hnt, fun hall => hnot fun a b c d h => ?_⟩
  have h' : ({a, b, c, d} : Finset (Q : Set X)).card = 4 := by
    obtain ⟨h₁, h₂, h₃, h₄, h₅, h₆⟩ := ne_of_card_four h
    have sne : ∀ {x y : (Q : Set X)}, x.1 ≠ y.1 → x ≠ y := fun hxy he => hxy (congrArg Subtype.val he)
    exact TreeMetric.card_four_of_ne (sne h₁) (sne h₂) (sne h₃) (sne h₄) (sne h₅) (sne h₆)
  have := hall a b c d h'
  rw [cfTriple_induced hN hθ hnt h' h] at this
  exact this

/-- **Corollary 1** (`a:cor:largeCFdetect`). Let `𝒩⁺` be a metric rooted binary phylogenetic network on taxa `X`, `|X| ≥ 4`, with
generic numerical parameters. Then under the NMSC, for each 4-taxon subset `Q ⊆ X`, the topology of the reduced unrooted tree of blobs
on the induced network `T_rd(𝒩⁻_Q)` is identifiable from `CF_Q`.

The hypothesis `|X| ≥ 4` is what makes a 4-taxon subset exist, so it is not needed in Lean. "Identifiable" reads: the function
`readTopology`, which does not depend on the network or on the parameters, returns the topology.

The proof is the paper's: Theorem 1 on each induced 4-taxon network (`theorem1`, on `induced`, `induced_isBinaryNetwork`), the map of parameters (`isGenericNull_inducedParams`), the identity of `CF`s
(`nmscCF_induced`), and a finite union. No exchangeability of four lineages is used beyond Theorem 1. -/
theorem corollary1 (hN : IsBinaryNetwork N) :
    ForGenericParams N fun θ => ∀ (a b c d : X) (h : ({a, b, c, d} : Finset X).card = 4),
      InducedTopologyIs hN a b c d h (readTopology (cfTriple N θ a b c d h)) := by
  refine (IsGenericNull.iUnion (ι := {Q : Finset X // Q.card = 4}) fun Q => forGenericParams_inducedDetectable hN Q.1 Q.2).mono ?_
  rintro θ ⟨hθ, hnot⟩
  by_contra hall
  have hdet : ∀ (Q : Finset X) (hQ : Q.card = 4), InducedDetectable hN θ Q hQ := by
    intro Q hQ
    by_contra hn
    exact hall (Set.mem_iUnion.mpr ⟨⟨Q, hQ⟩, hθ, hn⟩)
  refine hnot fun a b c d h => ?_
  -- the names on each induced network
  have hA : ({a, b, c, d} : Finset X).card = 4 := h
  have hq := hdet {a, b, c, d} h ⟨a, by simp⟩ ⟨b, by simp⟩ ⟨c, by simp⟩ ⟨d, by simp⟩ h
  have hq₂ := hdet {a, c, b, d} (card_acbd h) ⟨a, by simp⟩ ⟨c, by simp⟩ ⟨b, by simp⟩ ⟨d, by simp⟩ (card_acbd h)
  have hq₃ := hdet {a, d, b, c} (card_adbc h) ⟨a, by simp⟩ ⟨d, by simp⟩ ⟨b, by simp⟩ ⟨c, by simp⟩ (card_adbc h)
  -- the same trees, with their names changed
  have e₂ : quartetTree a d c b (card_adbc (card_acbd h)) = quartetTree a d b c (card_adbc h) := Subtype.ext (by
    simp only [quartetTree_val]
    rw [Finset.pair_comm c b])
  have e₃ : quartetTree a b d c (card_acbd (card_adbc h)) = quartetTree a b c d h := Subtype.ext (by
    simp only [quartetTree_val]
    rw [Finset.pair_comm d c])
  have e₄ : quartetTree a c d b (card_adbc (card_adbc h)) = quartetTree a c b d (card_acbd h) := Subtype.ext (by
    simp only [quartetTree_val]
    rw [Finset.pair_comm d b])
  have ht₂ : cfTriple N θ a c b d (card_acbd h) = ((cfTriple N θ a b c d h).2.1, (cfTriple N θ a b c d h).1, (cfTriple N θ a b c d h).2.2) := by
    unfold cfTriple quartetCF
    simp only [e₂]
  have ht₃ : cfTriple N θ a d b c (card_adbc h) = ((cfTriple N θ a b c d h).2.2, (cfTriple N θ a b c d h).1, (cfTriple N θ a b c d h).2.1) := by
    unfold cfTriple quartetCF
    simp only [e₃, e₄]
  have hsc₂ : IsStrictlyCutAtFirst (cfTriple N θ a c b d (card_acbd h)) ↔ (cfTriple N θ a b c d h).2.1 ≠ (cfTriple N θ a b c d h).1 ∧ (cfTriple N θ a b c d h).1 = (cfTriple N θ a b c d h).2.2 := by
    rw [ht₂]
    exact Iff.rfl
  have hsc₃ : IsStrictlyCutAtFirst (cfTriple N θ a d b c (card_adbc h)) ↔ (cfTriple N θ a b c d h).2.2 ≠ (cfTriple N θ a b c d h).1 ∧ (cfTriple N θ a b c d h).1 = (cfTriple N θ a b c d h).2.1 := by
    rw [ht₃]
    exact Iff.rfl
  unfold readTopology
  split_ifs with h₁ h₂ h₃
  · exact (hq.1).mpr h₁
  · exact (hq₂.1).mpr (hsc₂.mpr h₂)
  · exact (hq₃.1).mpr (hsc₃.mpr h₃)
  · -- otherwise `T_rd(𝒩⁻_Q)` has the unresolved topology, since a resolved one would give one of the three
    change (inducedTrd hN {a, b, c, d} h).HasStarTopology _ _ _ _
    have hc : Fintype.card (({a, b, c, d} : Finset X) : Set X) = 4 := by
      rw [← Nat.card_eq_fintype_card, Nat.card_coe_set_eq, Set.ncard_coe_finset]
      exact h
    obtain ⟨n₁, n₂, n₃, n₄, n₅, n₆⟩ := ne_of_card_four h
    have sne : ∀ {x y : (({a, b, c, d} : Finset X) : Set X)}, x.1 ≠ y.1 → x ≠ y := fun hxy he => hxy (congrArg Subtype.val he)
    have hp' := TreeMetric.card_four_of_ne (a := (⟨a, by simp⟩ : (({a, b, c, d} : Finset X) : Set X))) (b := ⟨b, by simp⟩) (c := ⟨c, by simp⟩) (d := ⟨d, by simp⟩)
      (sne n₁) (sne n₂) (sne n₃) (sne n₄) (sne n₅) (sne n₆)
    rcases Bridges.Trd_hasStar_or_hasQuartet (induced_isBinaryNetwork hN _ (nontrivial_coe_of_card_four h)) hc hp' with hS | hS | hS | hS
    · exact hS
    · exact absurd ((hq.1).mp hS) h₁
    · exact absurd (hsc₂.mp ((hdet {a, b, c, d} h ⟨a, by simp⟩ ⟨c, by simp⟩ ⟨b, by simp⟩ ⟨d, by simp⟩ (card_acbd h)).1.mp hS)) h₂
    · exact absurd (hsc₃.mp ((hdet {a, b, c, d} h ⟨a, by simp⟩ ⟨d, by simp⟩ ⟨b, by simp⟩ ⟨c, by simp⟩ (card_adbc h)).1.mp hS)) h₃

end AllmanEtAl2023
