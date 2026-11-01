module

public import AllmanEtAl2023.Theorem1AsPrinted

/-!
# Allman, Baños, Mitchell, Rhodes 2023: Corollary 1, as printed

Through the paper's induced network (Definition 6), with what "identifiable from `CF_Q`" means: a function of `CF_Q`
alone, `readTopology`, returns the topology, for generic parameters on the network.
-/

@[expose] public noncomputable section

open Phylogenetics Phylogenetics.RootedNetwork
open scoped Classical

namespace AllmanEtAl2023.Printed

variable {V E X : Type*} [Fintype V] [Fintype E] [Fintype X] [DecidableEq X] {N : RootedNetwork V E X}

/- Inventory. `AllmanEtAl2023.corollary1` applies Theorem 1 to `inducedNetwork`, cut at the LSA, and needs `nmscCF_belowNetwork`: departure D7, not forced. To follow the paper: Theorem 1 on
`induced` (`induced_isBinaryNetwork`), with `Claims.nmscCF_induced`, `Claims.isMetric_inducedParams`, `Claims.isGenericNull_inducedParams`, and a finite union (`IsGenericNull.iUnion`). -/
/-- **Corollary 1** (`a:cor:largeCFdetect`). Let `𝒩⁺` be a metric rooted binary phylogenetic network on taxa `X`, `|X| ≥ 4`, with
generic numerical parameters. Then under the NMSC, for each 4-taxon subset `Q ⊆ X`, the topology of the reduced unrooted tree of blobs
on the induced network `T_rd(𝒩⁻_Q)` is identifiable from `CF_Q`.

The hypothesis `|X| ≥ 4` is what makes a 4-taxon subset exist, so it is not needed in Lean. "Identifiable" reads: the function
`readTopology`, which does not depend on the network or on the parameters, returns the topology. -/
theorem corollary1 (hN : IsBinaryNetwork N) :
    ForGenericParams N fun θ => ∀ (a b c d : X) (h : ({a, b, c, d} : Finset X).card = 4),
      InducedTopologyIs hN a b c d h (readTopology (cfTriple N θ a b c d h)) := by
  sorry

end AllmanEtAl2023.Printed
