module

public import AllmanEtAl2023.Corollary1
public import AllmanEtAl2023.Proposition1

/-!
# Allman, Baños, Mitchell, Rhodes 2023: the geometry of concordance factors

* "For generic parameters `CF_abcd` is cut if, and only if, it is strictly cut" (in the proof of Theorem 1): `isCutCF_iff_isStrictlyCutCF`, by the paper's argument.

"The statements of Theorem 1 and Proposition 1 can be made geometric by plotting CFs" (after Proposition 1):

* "A CF is a point in the interior of the 2-dimensional probability simplex": `cfTriple_mem_simplex`.
* "If the unrooted reduced tree of blobs of a 4-taxon network is `ab|cd`, then `CF_abcd` lies on the vertical line segment": `proposition1`, and the two other segments: `cfTriple_of_hasQuartetTopology_acbd`,
  `cfTriple_of_hasQuartetTopology_adbc`.
* "Every point on this line segment within the simplex arises from some such network": `proposition1_converse`, and on the two other segments the same, with the names of the taxa changed.
* "Points in the simplex off these line segments arise as CFs only for networks whose unrooted reduced trees of blobs are unresolved": `hasStarTopology_of_isNonCutCF`.
* "This cannot happen for generic parameters by Theorem 1": `theorem1_b`.

"By Baños (2019), all points off the line segments arise from level-1 networks with 4-cycles" is in `AllmanEtAl2023.FourCycle`.
-/

@[expose] public noncomputable section

open Phylogenetics Phylogenetics.RootedNetwork
open scoped Classical

namespace AllmanEtAl2023

variable {V E X : Type*} [Fintype V] [Fintype E] [Fintype X] [DecidableEq X] {N : RootedNetwork V E X}

/-- `CF_acbd` is `CF_abcd` with the first two entries exchanged. -/
theorem cfTriple_acbd (θ : MetricData E) {a b c d : X} (h : ({a, b, c, d} : Finset X).card = 4) :
    cfTriple N θ a c b d (card_acbd h) = ((cfTriple N θ a b c d h).2.1, (cfTriple N θ a b c d h).1, (cfTriple N θ a b c d h).2.2) := by
  have e₂ : quartetTree a d c b (card_adbc (card_acbd h)) = quartetTree a d b c (card_adbc h) := Subtype.ext (by
    simp only [quartetTree_val]
    rw [Finset.pair_comm c b])
  unfold cfTriple quartetCF
  simp only [e₂]

/-- `CF_adbc` is `CF_abcd` in the order `(CF_{ad|bc}, CF_{ab|cd}, CF_{ac|bd})`. -/
theorem cfTriple_adbc (θ : MetricData E) {a b c d : X} (h : ({a, b, c, d} : Finset X).card = 4) :
    cfTriple N θ a d b c (card_adbc h) = ((cfTriple N θ a b c d h).2.2, (cfTriple N θ a b c d h).1, (cfTriple N θ a b c d h).2.1) := by
  have e₃ : quartetTree a b d c (card_acbd (card_adbc h)) = quartetTree a b c d h := Subtype.ext (by
    simp only [quartetTree_val]
    rw [Finset.pair_comm d c])
  have e₄ : quartetTree a c d b (card_adbc (card_adbc h)) = quartetTree a c b d (card_acbd h) := Subtype.ext (by
    simp only [quartetTree_val]
    rw [Finset.pair_comm d b])
  unfold cfTriple quartetCF
  simp only [e₃, e₄]

/-- **"For generic parameters `CF_abcd` is cut if, and only if, it is strictly cut"** (`a:claim:cut-strict`, in the proof of Theorem 1): "Statement (b) implies for generic parameters that if `CF_abcd` is cut, then `T` has a resolved tree topology, which by (a)
implies that `CF_abcd` is strictly cut." -/
theorem isCutCF_iff_isStrictlyCutCF (hN : IsBinaryNetwork N) (hcard : Fintype.card X = 4) :
    ForGenericParams N fun θ => ∀ (a b c d : X) (h : ({a, b, c, d} : Finset X).card = 4), IsCutCF (cfTriple N θ a b c d h) ↔ IsStrictlyCutCF (cfTriple N θ a b c d h) := by
  refine ((theorem1_a hN hcard).union (theorem1_b hN hcard)).mono ?_
  rintro θ ⟨hθ, hnot⟩
  by_contra hall
  refine hnot fun a b c d h => ⟨fun hc => ?_, fun hc => hc.1⟩
  have hA : ∀ (a b c d : X) (h : ({a, b, c, d} : Finset X).card = 4), (Trd hN (nontrivial_of_card_four hcard)).HasQuartetTopology a b c d → IsStrictlyCutAtFirst (cfTriple N θ a b c d h) := by
    by_contra hna
    exact hall (Or.inl ⟨hθ, hna⟩)
  have hB : ∀ (a b c d : X) (h : ({a, b, c, d} : Finset X).card = 4), (Trd hN (nontrivial_of_card_four hcard)).HasStarTopology a b c d → IsNonCutCF (cfTriple N θ a b c d h) := by
    by_contra hnb
    exact hall (Or.inr ⟨hθ, hnb⟩)
  rcases Bridges.Trd_hasStar_or_hasQuartet hN hcard h with hS | hS | hS | hS
  · exact absurd hc (hB a b c d h hS)
  · exact (hA a b c d h hS).isStrictlyCutCF
  · have := hA a c b d (card_acbd h) hS
    rw [cfTriple_acbd θ h] at this
    exact ⟨hc, fun h' => this.1 h'.1.symm⟩
  · have := hA a d b c (card_adbc h) hS
    rw [cfTriple_adbc θ h] at this
    exact ⟨hc, fun h' => this.1 h'.2.symm⟩

/-! ### The geometry -/

/-- **"A CF is a point in the interior of the 2-dimensional probability simplex"** (`a:claim:cf-simplex`, after Proposition 1). -/
theorem cfTriple_mem_simplex (hP : N.IsPhylogenetic) {θ : MetricData E} (hθ : N.IsMetric θ) {a b c d : X} (h : ({a, b, c, d} : Finset X).card = 4) :
    0 < (cfTriple N θ a b c d h).1 ∧ 0 < (cfTriple N θ a b c d h).2.1 ∧ 0 < (cfTriple N θ a b c d h).2.2 ∧
      (cfTriple N θ a b c d h).1 + (cfTriple N θ a b c d h).2.1 + (cfTriple N θ a b c d h).2.2 = 1 := by
  have hρ : (0 : ℝ) ≤ 0 ∧ (0 : ℝ) ≤ 1 := ⟨le_rfl, zero_le_one⟩
  exact ⟨nmscCF_pos hP hθ hρ _, nmscCF_pos hP hθ hρ _, nmscCF_pos hP hθ hρ _, sum_cfTriple hP hθ.isWeakMetric h⟩

/-- **The second segment**: if the tree of blobs is `ac|bd`, the `CF` is `(q, p, q)`, for all parameters (after Proposition 1). -/
theorem cfTriple_of_hasQuartetTopology_acbd (hN : IsBinaryNetwork N) (hcard : Fintype.card X = 4) {a b c d : X} (h : ({a, b, c, d} : Finset X).card = 4)
    (hT : (Trd hN (nontrivial_of_card_four hcard)).HasQuartetTopology a c b d) {θ : MetricData E} (hθ : N.IsMetric θ) :
    ∃ p q : ℝ, cfTriple N θ a b c d h = (q, p, q) ∧ 0 < p ∧ p < 1 ∧ 0 < q ∧ q < 1 ∧ p + 2 * q = 1 := by
  obtain ⟨p, q, ht, hrest⟩ := proposition1 hN hcard (card_acbd h) hT hθ
  rw [cfTriple_acbd θ h] at ht
  simp only [Prod.mk.injEq] at ht
  exact ⟨p, q, Prod.ext ht.2.1 (Prod.ext ht.1 ht.2.2), hrest⟩

/-- **The third segment**: if the tree of blobs is `ad|bc`, the `CF` is `(q, q, p)`, for all parameters (after Proposition 1). -/
theorem cfTriple_of_hasQuartetTopology_adbc (hN : IsBinaryNetwork N) (hcard : Fintype.card X = 4) {a b c d : X} (h : ({a, b, c, d} : Finset X).card = 4)
    (hT : (Trd hN (nontrivial_of_card_four hcard)).HasQuartetTopology a d b c) {θ : MetricData E} (hθ : N.IsMetric θ) :
    ∃ p q : ℝ, cfTriple N θ a b c d h = (q, q, p) ∧ 0 < p ∧ p < 1 ∧ 0 < q ∧ q < 1 ∧ p + 2 * q = 1 := by
  obtain ⟨p, q, ht, hrest⟩ := proposition1 hN hcard (card_adbc h) hT hθ
  rw [cfTriple_adbc θ h] at ht
  simp only [Prod.mk.injEq] at ht
  exact ⟨p, q, Prod.ext ht.2.1 (Prod.ext ht.2.2 ht.1), hrest⟩

/-- **"Points in the simplex off these line segments arise as CFs only for networks whose unrooted reduced trees of blobs are unresolved"** (`a:claim:cf-off-lines`, after Proposition 1), for all parameters: the contrapositive of Proposition 1. -/
theorem hasStarTopology_of_isNonCutCF (hN : IsBinaryNetwork N) (hcard : Fintype.card X = 4) {a b c d : X} (h : ({a, b, c, d} : Finset X).card = 4) {θ : MetricData E} (hθ : N.IsMetric θ)
    (hnc : IsNonCutCF (cfTriple N θ a b c d h)) : (Trd hN (nontrivial_of_card_four hcard)).HasStarTopology a b c d := by
  rcases Bridges.Trd_hasStar_or_hasQuartet hN hcard h with hS | hS | hS | hS
  · exact hS
  · obtain ⟨p, q, ht, -⟩ := proposition1 hN hcard h hS hθ
    exact absurd (Or.inr (Or.inr (by rw [ht]))) hnc
  · obtain ⟨p, q, ht, -⟩ := cfTriple_of_hasQuartetTopology_acbd hN hcard h hS hθ
    exact absurd (Or.inr (Or.inl (by rw [ht]))) hnc
  · obtain ⟨p, q, ht, -⟩ := cfTriple_of_hasQuartetTopology_adbc hN hcard h hS hθ
    exact absurd (Or.inl (by rw [ht])) hnc

end AllmanEtAl2023
