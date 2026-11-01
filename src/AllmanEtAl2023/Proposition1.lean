module

public import AllmanEtAl2023.Theorem1AsPrinted
public import AllmanEtAl2023.NetworkNk

/-!
# Allman, Baños, Mitchell, Rhodes 2023: Proposition 1

The first part holds at all valid numerical parameters, not only at generic ones, by the first step of the proof of Theorem 1
(`theorem1_cut`), though the proof of Proposition 1 cites "statement 1 of Theorem 1", which is generic.

In the converse, "arises" means: there are a network of the sort described and valid numerical parameters of Definition 3 at
which the CF is the triple. The proof gives more: the network is `𝒩(k)⁺` for some `k`, with lengths `metricNk k ε M` for some
`ε, M > 0`, and hybridization parameters `1/2` (`NetworkNk.exists_params`).
-/

@[expose] public noncomputable section

open Phylogenetics Phylogenetics.RootedNetwork AllmanEtAl2023.NetworkNk
open scoped Classical

universe u

namespace AllmanEtAl2023.Printed

variable {X : Type u} [Fintype X] [DecidableEq X]

namespace NetworkNk

/-- `𝒩(k)⁺` is a network of Definition 1. -/
theorem isBinaryNetwork_networkNk (k : ℕ) {a b c d : X} (h : ({a, b, c, d} : Finset X).card = 4)
    (hX : Fintype.card X = 4) : IsBinaryNetwork (networkNk k a b c d) := by
  sorry

/-- The lengths of `𝒩(k)⁺` are valid numerical parameters of Definition 3, for `ε, M > 0`. -/
theorem isMetric_metricNk (k : ℕ) {a b c d : X} (h : ({a, b, c, d} : Finset X).card = 4)
    (hX : Fintype.card X = 4) {ε M : ℝ} (hε : 0 < ε) (hM : 0 < M) :
    (networkNk k a b c d).IsMetric (metricNk k ε M) := by
  sorry

/-- `T_rd(𝒩(k)⁻)` has the quartet tree topology `ab|cd`: "edges lead from the root to the taxon `d` and to a 3-blob. The other two
edges incident to the 3-blob lead to `c`, and to a cherry of `a, b`". -/
theorem hasQuartetTopology_networkNk (k : ℕ) {a b c d : X} (h : ({a, b, c, d} : Finset X).card = 4)
    (hX : Fintype.card X = 4) :
    (Trd (isBinaryNetwork_networkNk k h hX) (nontrivial_of_card_four hX)).HasQuartetTopology a b c d := by
  sorry

/-- `α` of the proof of Proposition 1: the probability that the `a, b` lineages are on different edges at height `1 + (k + 1)ε`.
With `p = exp (-ε)`, `α = ∑_{ℓ=1}^k (p/2)^ℓ`. -/
def alpha (k : ℕ) (ε : ℝ) : ℝ := ∑ ℓ ∈ Finset.Icc 1 k, (Real.exp (-ε) / 2) ^ ℓ

/-- "We can make `CF_abcd` as close to `(0, 1/2, 1/2)` as desired by choices of `ε ≈ 0` and `k, M ≫ 0`", in the form of the bound
behind it: `CF_{ab|cd} = α CF₁ + (1 - α) CF₂`, in which the first entry of `CF₂` is at most 1, and that of `CF₁` is at most
`exp (-M)`, because the `a` and `c` or the `b` and `c` lineages must fail to coalesce on an edge of length at least `M`. -/
theorem cf_first_le (k : ℕ) {a b c d : X} (h : ({a, b, c, d} : Finset X).card = 4) (hX : Fintype.card X = 4)
    {ε M : ℝ} (hε : 0 < ε) (hM : 0 < M) :
    (cfTriple (networkNk k a b c d) (metricNk k ε M) a b c d h).1 ≤
      (1 - alpha k ε) + Real.exp (-M) := by
  sorry

/-- "We could instead take `ε ≫ 0`, making the probability of coalescence of `a, b` on the edge above the `{a, b}` cherry as close to
1 as we like, so that `CF_abcd` is arbitrarily close to `(1, 0, 0)`." -/
theorem one_sub_exp_le_cf_first (k : ℕ) {a b c d : X} (h : ({a, b, c, d} : Finset X).card = 4)
    (hX : Fintype.card X = 4) {ε M : ℝ} (hε : 0 < ε) (hM : 0 < M) :
    1 - Real.exp (-ε) ≤ (cfTriple (networkNk k a b c d) (metricNk k ε M) a b c d h).1 := by
  sorry

/-- The proof of the converse of Proposition 1: "a triple `(p, q, q)` arises as a `CF` on `𝒩(k)⁺` for sufficiently large `k` and
certain numerical parameters". -/
theorem exists_params {a b c d : X} (h : ({a, b, c, d} : Finset X).card = 4) (hX : Fintype.card X = 4)
    {p q : ℝ} (hp : 0 < p) (hq : 0 < q) (hpq : p + 2 * q = 1) :
    ∃ (k : ℕ) (ε M : ℝ), 0 < ε ∧ 0 < M ∧
      cfTriple (networkNk k a b c d) (metricNk k ε M) a b c d h = (p, q, q) := by
  sorry

end NetworkNk

/- Inventory. New here. The first part: `cut_alternatives`, `sum_geneTreeDist`, `geneTreeDist_pos`, `theorem1_cut`. -/
/-- **Proposition 1** (`a:prop:Nk`). Let `𝒩⁺` be a 4-taxon rooted binary phylogenetic network whose reduced tree of blobs has quartet
topology `ab|cd`. Then under the NMSC the `CF` is `ab|cd`-cut, with `CF_abcd = (CF_{ab|cd}, CF_{ac|bd}, CF_{ad|bc}) = (p, q, q)`,
where `0 < p, q < 1`, `p + 2q = 1`. Conversely (`proposition1_converse`), every such triple `(p, q, q)` arises as the `CF` from
such a network. -/
theorem proposition1 {V E : Type*} [Fintype V] [Fintype E] {N : RootedNetwork V E X} (hN : IsBinaryNetwork N)
    (hcard : Fintype.card X = 4) {a b c d : X} (h : ({a, b, c, d} : Finset X).card = 4)
    (hT : (Trd hN (nontrivial_of_card_four hcard)).HasQuartetTopology a b c d) {θ : MetricData E}
    (hθ : N.IsMetric θ) :
    ∃ p q : ℝ, cfTriple N θ a b c d h = (p, q, q) ∧ 0 < p ∧ p < 1 ∧ 0 < q ∧ q < 1 ∧ p + 2 * q = 1 := by
  sorry

/- Inventory. New here. `NetworkNk.exists_params`, whose hard step is `NetworkNk.cf_first_le`. See `notes/allman_inventory.md`. -/
/-- **Proposition 1, the converse** (`a:prop:Nk`): every triple `(p, q, q)` with `0 < p, q < 1`, `p + 2q = 1`, arises as the `CF` from
a 4-taxon rooted binary phylogenetic network whose reduced tree of blobs has quartet topology `ab|cd`. -/
theorem proposition1_converse (hcard : Fintype.card X = 4) {a b c d : X} (h : ({a, b, c, d} : Finset X).card = 4)
    {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) (hq1 : q < 1) (hpq : p + 2 * q = 1) :
    ∃ (V : Type u) (E : Type) (_ : Fintype V) (_ : Fintype E) (N : RootedNetwork V E X) (hN : IsBinaryNetwork N)
      (θ : MetricData E), N.IsMetric θ ∧
        (Trd hN (nontrivial_of_card_four hcard)).HasQuartetTopology a b c d ∧
        cfTriple N θ a b c d h = (p, q, q) := by
  sorry

end AllmanEtAl2023.Printed
