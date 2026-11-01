module

public import AllmanEtAl2023.Theorem3
public import AllmanEtAl2023.TreeIso

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
  It follows from `theorem4`. It does not immediately imply `theorem4`: there, `A₁` may depend on `N₂`, and passing to one null set for each network needs a countable union over isomorphism
  classes of networks.
* `theorem4_iso`: the same, with the trees isomorphic as labelled graphs, not only with the same splits (the splits-equivalence theorem).

A tree here is compared through its splits, `LabelledGraph.splits`: `AllmanEtAl2023.Bridges.splits_Trd` says they are the library's `treeOfBlobs N`, and `isIso_Trd_of_splits_eq` says that they determine the
tree (`LabelledGraph.isIso_of_splits_eq`).

Semple and Steel (2005) and Rhodes (2020) are cited for "the collection of displayed quartets determine the tree". This is the library's `mem_of_forall_displays`, which is Steel's theorem, through `treeFromQuartets_displays`.
-/

@[expose] public noncomputable section

open Phylogenetics Phylogenetics.RootedNetwork
open scoped Classical

universe u

namespace AllmanEtAl2023

variable {X : Type*} [Fintype X] [DecidableEq X]

/-- **"Treating B-quartets on `𝒩⁺` as unresolved, we thus can identify the topology of every displayed quartet tree on `T_rd(𝒩⁻)`"** (`a:claim:thm4-displayed`, in the proof of Theorem 4). It needs Theorem 3, so it
is here, not with the other claims. -/
theorem displayedFromCF_eq {V E : Type*} [Fintype V] [Fintype E] {N : RootedNetwork V E X} (hN : IsBinaryNetwork N) (hX : Nontrivial X) :
    ForGenericParams N fun θ => displayedFromCF (nmscCF N θ 0) = {s | Displays (Trd hN hX).splits s} := by
  have hP := hN.isPhylogenetic
  refine ((theorem3 hN).union (corollary1 hN)).mono ?_
  rintro θ ⟨hθ, hnot⟩
  by_contra hall
  have h₃ : ∀ Q : Finset X, Q.card = 4 → (CFInferred (nmscCF N θ 0) Q ↔ IsBlobQuartet N Q) := by
    by_contra h'
    exact hall (Or.inl ⟨hθ, h'⟩)
  have h₁ : ∀ (a b c d : X) (h : ({a, b, c, d} : Finset X).card = 4), InducedTopologyIs hN a b c d h (readTopology (cfTriple N θ a b c d h)) := by
    by_contra h'
    exact hall (Or.inr ⟨hθ, h'⟩)
  refine hnot (Set.ext fun s => ?_)
  obtain ⟨a, b, c, d, h, rfl⟩ := TreeMetric.exists_eq_quartetTree s
  have htaxa : (quartetTree a b c d h).taxa = {a, b, c, d} := quartetTree_taxa _ _ _ _ _
  constructor
  · -- a strictly cut `CF`, not inferred to be a B-quartet, is the displayed quartet of a T-quartet
    rintro ⟨hs, hni⟩
    rw [htaxa] at hni
    have hT : IsTreeQuartet N {a, b, c, d} := ⟨h, fun hB => hni ((h₃ _ h).mpr hB)⟩
    obtain ⟨s', hs', hd⟩ := exists_displays_of_isTreeQuartet hN hX hT
    have hq := (isStrictlyCutAt_iff_inducedHasQuartetTopology hN h₁ h).mp hs
    have hc := (Bridges.inducedHasQuartetTopology_iff hN h).mp hq
    rw [Bridges.splits_Trd hN hX] at hd
    have hc' := inducedCutSplit_of_displays hP hd
    have hEq := inducedCutSplit_unique hP hc hc' (htaxa.trans (mem_treesOn.1 hs').symm)
    change Displays (Trd hN hX).splits _
    rw [hEq, Bridges.splits_Trd hN hX]
    exact hd
  · -- a displayed quartet is a T-quartet, whose `CF` is strictly cut
    intro hd
    have hd' : Displays (Trd hN hX).splits (quartetTree a b c d h) := hd
    have hB : ¬ IsBlobQuartet N {a, b, c, d} := fun hB =>
      ((isBlobQuartet_iff_displaysUnresolved hN hX h).mp hB).2 _ (mem_treesOn.2 htaxa) hd'
    refine ⟨(isStrictlyCutAt_iff_inducedHasQuartetTopology hN h₁ h).mpr (inducedHasQuartetTopology_of_displays hN hX h hd'), ?_⟩
    rw [htaxa]
    exact fun hi => hB ((h₃ _ h).mp hi)

/-- **Theorem 4, with the function** (`a:thm:ToBident`). For generic numerical parameters, `treeFromCF` applied to the distribution of gene
quartet topologies is `T_rd(𝒩⁻)`. The proof is the paper's: Theorem 3 gives the B-quartets, Corollary 1 the resolved topologies (`displayedFromCF_eq`), and "the collection of displayed quartets determine the
tree" (Semple and Steel 2005; Rhodes 2020), `treeFromQuartets_displays`, from the library's `mem_of_forall_displays`. -/
theorem theorem4_treeFromCF {V E : Type*} [Fintype V] [Fintype E] {N : RootedNetwork V E X} (hN : IsBinaryNetwork N)
    (hX : Nontrivial X) :
    ForGenericParams N fun θ => treeFromCF (nmscCF N θ 0) = (Trd hN hX).splits := by
  refine (displayedFromCF_eq hN hX).mono ?_
  rintro θ ⟨hθ, hnot⟩
  refine ⟨hθ, fun h => hnot ?_⟩
  have h' : displayedFromCF (nmscCF N θ 0) = {s | Displays (Trd hN hX).splits s} := h
  change treeFromQuartets (displayedFromCF (nmscCF N θ 0)) = _
  rw [h']
  refine treeFromQuartets_displays ?_ Fintype.one_lt_card
  rw [Bridges.splits_Trd hN hX]
  exact isUnrootedTree_treeOfBlobs hN.isPhylogenetic

/-- **Theorem 4** (`a:thm:ToBident`). Let `𝒩⁺` be a rooted binary phylogenetic network. Then for generic numerical parameters, the reduced
unrooted tree of blobs `T_rd(𝒩⁻)` is identifiable from the distribution of gene quartet topologies under the NMSC model.

`F` is chosen before the network. The distribution of gene quartet topologies is the function `s ↦ nmscCF N θ 0 s`. -/
theorem theorem4 (X : Type*) [Fintype X] [DecidableEq X] (hX : Nontrivial X) :
    ∃ F : (QuartetTree X → ℝ) → Finset (Finset X),
      ∀ (V E : Type u) [Fintype V] [Fintype E] (N : RootedNetwork V E X) (hN : IsBinaryNetwork N),
        ForGenericParams N fun θ => F (nmscCF N θ 0) = (Trd hN hX).splits :=
  ⟨treeFromCF, fun _ _ _ _ _ hN => theorem4_treeFromCF hN hX⟩

/-- **Theorem 4, for two networks** (`a:thm:ToBident`). Off null sets of parameters of each, two networks with the same distribution of gene
quartet topologies have reduced unrooted trees of blobs with the same splits. `A₁` may depend on `N₂` in this form, so it doesn't immediately imply `theorem4`. -/
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
    (h : (Trd hN₁ hX).splits = (Trd hN₂ hX).splits) : (Trd hN₁ hX).IsIso (Trd hN₂ hX) :=
  LabelledGraph.isIso_of_splits_eq (Bridges.isReducedTree_Trd hN₁ hX) (Bridges.isReducedTree_Trd hN₂ hX) h

/-- **Theorem 4, for two networks, as labelled trees** (`a:thm:ToBident`). -/
theorem theorem4_iso {V₁ E₁ V₂ E₂ : Type*} [Fintype V₁] [Fintype E₁] [Fintype V₂] [Fintype E₂]
    {N₁ : RootedNetwork V₁ E₁ X} {N₂ : RootedNetwork V₂ E₂ X} (hN₁ : IsBinaryNetwork N₁) (hN₂ : IsBinaryNetwork N₂)
    (hX : Nontrivial X) :
    ∃ (A₁ : Set (MetricData E₁)) (A₂ : Set (MetricData E₂)), N₁.IsGenericNull A₁ ∧ N₂.IsGenericNull A₂ ∧
      ∀ θ₁ θ₂, N₁.IsMetric θ₁ → θ₁ ∉ A₁ → N₂.IsMetric θ₂ → θ₂ ∉ A₂ → nmscCF N₁ θ₁ 0 = nmscCF N₂ θ₂ 0 →
        (Trd hN₁ hX).IsIso (Trd hN₂ hX) := by
  obtain ⟨A₁, A₂, h₁, h₂, h⟩ := theorem4_two_networks hN₁ hN₂ hX
  exact ⟨A₁, A₂, h₁, h₂, fun θ₁ θ₂ a b c d e => isIso_Trd_of_splits_eq hN₁ hN₂ hX (h θ₁ θ₂ a b c d e)⟩

end AllmanEtAl2023
