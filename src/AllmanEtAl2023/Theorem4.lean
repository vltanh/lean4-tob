module

public import AllmanEtAl2023.Theorem3

/-!
# Allman, Baños, Mitchell, Rhodes 2023: Theorem 4

"For generic numerical parameters, the reduced unrooted tree of blobs is identifiable from the distribution of gene quartet topologies."

What this means. The introduction says: "the distribution of gene quartet topologies arising under the NMSC on a fixed species network
uniquely determines the unrooted tree of blobs of that network. We make no assumptions on blob structure, but do require that numerical
parameters lie outside an exceptional set of measure zero". The proof builds a procedure from the CFs that sees no network and no
parameters: CF-detectability, the rule, and then "the collection of displayed quartets determine the tree". The exceptional set depends on
the network, since that of Theorem 1 does. So:

* `theorem4`: there is one function `F` of the CFs, for all networks on `X`, with `F (CFs) = T_rd(𝒩⁻)` off a null set of parameters of each
  network. This is what the words and the proof say, and it isn't vacuous: `F` sees the CFs only. A function allowed to depend on the network
  would say nothing, since `T_rd(𝒩⁻)` is itself a function of the network.
* `theorem4_treeFromCF`: the function is `treeFromCF`.
* `theorem4_two_networks`: the form usual in the literature. Two networks with parameters off null sets, with the same CFs, have the same tree.
  It follows from `theorem4`, and implies it, by choosing `F` on each value of the CFs.
* `theorem4_iso`: the same, with the trees isomorphic as labelled graphs, not only with the same splits (the splits-equivalence theorem).

A tree here is compared through its splits, `LabelledGraph.splits`: `AllmanEtAl2023.Bridges.splits_Trd` says they are the library's `treeOfBlobs N`. These statements live in
`AllmanEtAl2023.Printed` because the older code has `AllmanEtAl2023.theorem1`, and so on, in other forms.
-/

@[expose] public noncomputable section

open Phylogenetics Phylogenetics.RootedNetwork
open scoped Classical

universe u

namespace AllmanEtAl2023.Printed

variable {X : Type*} [Fintype X] [DecidableEq X]

/- Inventory. From `Claims.displayedFromCF_eq` (from `theorem3`, `corollary1`, `Claims.exists_displays_of_isTreeQuartet`, `Claims.inducedHasQuartetTopology_of_displays`), `Claims.treeFromQuartets_displays`,
`Bridges.splits_Trd`, and the library's `isUnrootedTree_treeOfBlobs`. `TINNiK` has no such theorem: its algorithm has tests in place of CFs. -/
/-- **Theorem 4, with the function** (`a:thm:ToBident`). For generic numerical parameters, `treeFromCF` applied to the distribution of gene
quartet topologies is `T_rd(𝒩⁻)`. -/
theorem theorem4_treeFromCF {V E : Type*} [Fintype V] [Fintype E] {N : RootedNetwork V E X} (hN : IsBinaryNetwork N)
    (hX : Nontrivial X) :
    ForGenericParams N fun θ => treeFromCF (nmscCF N θ 0) = (Trd hN hX).splits := by
  sorry

/-- **Theorem 4** (`a:thm:ToBident`). Let `𝒩⁺` be a rooted binary phylogenetic network. Then for generic numerical parameters, the reduced
unrooted tree of blobs `T_rd(𝒩⁻)` is identifiable from the distribution of gene quartet topologies under the NMSC model.

`F` is chosen before the network. The distribution of gene quartet topologies is the function `s ↦ nmscCF N θ 0 s`. -/
theorem theorem4 (X : Type*) [Fintype X] [DecidableEq X] (hX : Nontrivial X) :
    ∃ F : (QuartetTree X → ℝ) → Finset (Finset X),
      ∀ (V E : Type u) [Fintype V] [Fintype E] (N : RootedNetwork V E X) (hN : IsBinaryNetwork N),
        ForGenericParams N fun θ => F (nmscCF N θ 0) = (Trd hN hX).splits :=
  ⟨treeFromCF, fun _ _ _ _ _ hN => theorem4_treeFromCF hN hX⟩

/-- **Theorem 4, for two networks** (`a:thm:ToBident`). Off null sets of parameters of each, two networks with the same distribution of gene
quartet topologies have reduced unrooted trees of blobs with the same splits. -/
theorem theorem4_two_networks {V₁ E₁ V₂ E₂ : Type*} [Fintype V₁] [Fintype E₁] [Fintype V₂] [Fintype E₂]
    {N₁ : RootedNetwork V₁ E₁ X} {N₂ : RootedNetwork V₂ E₂ X} (hN₁ : IsBinaryNetwork N₁) (hN₂ : IsBinaryNetwork N₂)
    (hX : Nontrivial X) :
    ∃ (A₁ : Set (MetricData E₁)) (A₂ : Set (MetricData E₂)), N₁.IsGenericNull A₁ ∧ N₂.IsGenericNull A₂ ∧
      ∀ θ₁ θ₂, N₁.IsMetric θ₁ → θ₁ ∉ A₁ → N₂.IsMetric θ₂ → θ₂ ∉ A₂ → nmscCF N₁ θ₁ 0 = nmscCF N₂ θ₂ 0 →
        (Trd hN₁ hX).splits = (Trd hN₂ hX).splits := by
  refine ⟨_, _, theorem4_treeFromCF hN₁ hX, theorem4_treeFromCF hN₂ hX, fun θ₁ θ₂ hθ₁ hA₁ hθ₂ hA₂ h => ?_⟩
  have h₁ : treeFromCF (nmscCF N₁ θ₁ 0) = (Trd hN₁ hX).splits := by
    by_contra hne
    exact hA₁ ⟨hθ₁, hne⟩
  have h₂ : treeFromCF (nmscCF N₂ θ₂ 0) = (Trd hN₂ hX).splits := by
    by_contra hne
    exact hA₂ ⟨hθ₂, hne⟩
  rw [← h₁, ← h₂, h]

/-- **The splits of `T_rd(𝒩⁻)` determine it** (`a:claim:splits-tree`): the splits-equivalence theorem of Buneman, as in Semple and Steel (2005),
on these graphs. -/
theorem isIso_Trd_of_splits_eq {V₁ E₁ V₂ E₂ : Type*} {N₁ : RootedNetwork V₁ E₁ X} {N₂ : RootedNetwork V₂ E₂ X}
    (hN₁ : IsBinaryNetwork N₁) (hN₂ : IsBinaryNetwork N₂) (hX : Nontrivial X)
    (h : (Trd hN₁ hX).splits = (Trd hN₂ hX).splits) : (Trd hN₁ hX).IsIso (Trd hN₂ hX) := by
  sorry

/-- **Theorem 4, for two networks, as labelled trees** (`a:thm:ToBident`). -/
theorem theorem4_iso {V₁ E₁ V₂ E₂ : Type*} [Fintype V₁] [Fintype E₁] [Fintype V₂] [Fintype E₂]
    {N₁ : RootedNetwork V₁ E₁ X} {N₂ : RootedNetwork V₂ E₂ X} (hN₁ : IsBinaryNetwork N₁) (hN₂ : IsBinaryNetwork N₂)
    (hX : Nontrivial X) :
    ∃ (A₁ : Set (MetricData E₁)) (A₂ : Set (MetricData E₂)), N₁.IsGenericNull A₁ ∧ N₂.IsGenericNull A₂ ∧
      ∀ θ₁ θ₂, N₁.IsMetric θ₁ → θ₁ ∉ A₁ → N₂.IsMetric θ₂ → θ₂ ∉ A₂ → nmscCF N₁ θ₁ 0 = nmscCF N₂ θ₂ 0 →
        (Trd hN₁ hX).IsIso (Trd hN₂ hX) := by
  obtain ⟨A₁, A₂, h₁, h₂, h⟩ := theorem4_two_networks hN₁ hN₂ hX
  exact ⟨A₁, A₂, h₁, h₂, fun θ₁ θ₂ a b c d e => isIso_Trd_of_splits_eq hN₁ hN₂ hX (h θ₁ θ₂ a b c d e)⟩

end AllmanEtAl2023.Printed
