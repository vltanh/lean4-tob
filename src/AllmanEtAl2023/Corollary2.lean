module

public import AllmanEtAl2023.Bridges

/-!
# Allman, Baños, Mitchell, Rhodes 2023: Corollary 2

Proved from `AllmanEtAl2023.corollary2`, on subgraphs, by Lemma 2. Departure from the paper, not forced: the paper passes to the induced network by "blobs pass to blobs, and cut edges to cut
edges". `Bridges.isBlobQuartetOnInduced_iff` goes through cut-edge splits instead, by `not_resolves_iff_exists_determines`.
-/

@[expose] public noncomputable section

open Phylogenetics Phylogenetics.RootedNetwork
open scoped Classical

namespace AllmanEtAl2023.Printed

variable {V E X : Type*} {N : RootedNetwork V E X}

/- Inventory. Proved from `AllmanEtAl2023.corollary2`, which is this on subgraphs by Lemma 2, as the paper's sentence says, with `Bridges.isBlobQuartetOnInduced_iff`. That bridge goes through
cut-edge splits, and the paper says "blobs pass to blobs". -/
/-- **Corollary 2** (`a:cor:inducedB`). Let `𝒩⁺` be a rooted binary phylogenetic network on `X`, and `ℳ⁺` the induced network on
`Y ⊂ X`. Then any B-quartet on `ℳ⁺` is a B-quartet on `𝒩⁺`. -/
theorem corollary2 (hN : IsBinaryNetwork N) (Y : Set X) (hY : Y.Nontrivial) {Q : Finset X} (hQ : (Q : Set X) ⊆ Y)
    (h : IsBlobQuartetOnInduced hN Y hY Q) : IsBlobQuartet N Q := by
  have hP := hN.isPhylogenetic
  have : Finite X := hP.finite_taxa
  let _ : Fintype X := Fintype.ofFinite X
  let _ : DecidableEq X := Classical.decEq X
  let _ : Fintype Y := Fintype.ofFinite Y
  have h4 : Q.card = 4 := by
    have := h.1
    rwa [Finset.card_subtype, Finset.filter_true_of_mem (fun x hx => hQ hx)] at this
  have hY' : ((Y.toFinset : Finset X) : Set X) = Y := Set.coe_toFinset Y
  have hQY' : Q ⊆ Y.toFinset := fun x hx => Set.mem_toFinset.mpr (hQ hx)
  obtain ⟨v, hv, hd⟩ := (Bridges.isBlobQuartetOnInduced_iff hN Y hY hQ h4).mp h
  have hR : ¬ Resolves N Y.toFinset Q := (not_resolves_iff_exists_determines hP hQY' h4).mpr
    ⟨v, by rwa [hY'], by rwa [hY']⟩
  exact (Bridges.isBlobQuartet_iff_not_resolves hN h4).mpr
    (AllmanEtAl2023.corollary2 hP (Finset.subset_univ _) hQY' h4 hR)

end AllmanEtAl2023.Printed
