module

public import AllmanEtAl2023.Lemma3
public import AllmanEtAl2023.Corollary1AsPrinted

/-!
# Allman, Baños, Mitchell, Rhodes 2023: Theorem 3

"All B-quartets can be identified from the quartet `CF`s using `CF`-detectability and applications of the B-quartet Inference Rule."
`CFInferred p` is that procedure, on the CFs `p`: a function of the CFs alone. It holds of exactly the B-quartets, for generic parameters.
The rule in it is the printed one of Theorem 2, whose third hypothesis is on the induced network, that is, read off the CF of the third
set: the paper's proof shows that its part (a) suffices. Both directions are stated: "identified" needs that nothing else is inferred, which
is Theorem 2, and the proof's "all" is the induction.

The proof's first sentence reduces the theorem to the statement on topologies, which does not mention parameters: "Since the B-quartet
Inference Rule does not depend on parameters, we have only to show that this information together with the inference rule is enough to
identify all B-quartets". That is `theorem3_core`.
-/

@[expose] public noncomputable section

open Phylogenetics Phylogenetics.RootedNetwork
open scoped Classical

namespace AllmanEtAl2023.Printed

variable {V E X : Type*} [DecidableEq X] {N : RootedNetwork V E X}

/-- The closure of the first sentence of the proof of Theorem 3: what the topologies of the reduced unrooted trees of blobs of the induced
4-taxon networks give, with the Inference Rule. -/
inductive TopologyInferred (hN : IsBinaryNetwork N) : Finset X → Prop
  | detected (a b c d : X) (h : ({a, b, c, d} : Finset X).card = 4) :
      InducedHasStarTopology hN a b c d h → TopologyInferred hN {a, b, c, d}
  | rule (a b c d e : X) (t q : Finset X) :
      ({a, b, c, d, e} : Finset X).card = 5 →
      TopologyInferred hN {a, b, c, d} → TopologyInferred hN {b, c, d, e} →
      t ∈ ({{a, b, c, e}, {a, b, d, e}, {a, c, d, e}} : Finset (Finset X)) →
      (InducedTreeSeparates hN t a e ∨ InducedIsBlobQuartet hN t) →
      q ∈ ({{a, b, c, e}, {a, b, d, e}, {a, c, d, e}} : Finset (Finset X)) →
      TopologyInferred hN q

/- Inventory. `AllmanEtAl2023.closure_complete`, `closure_sound` have this on a fixed network and subgraphs: `closure_aux` inducts on a set of taxa `Y`, where the paper inducts on induced networks and
transfers by Corollary 2. To follow the paper: induct on networks, with `Claims.exists_representatives_induced`, `Claims.inducedHasQuartetTopology_induced`, `corollary2`, `lemma3`, `theorem2`. -/
/-- **The induction of the proof of Theorem 3** (`a:claim:thm3-core`). From the topologies of the reduced unrooted trees of blobs of all induced
4-taxon networks, the Inference Rule identifies all B-quartets, and only those. -/
theorem theorem3_core (hN : IsBinaryNetwork N) {Q : Finset X} (hQ : Q.card = 4) :
    TopologyInferred hN Q ↔ IsBlobQuartet N Q := by
  sorry

/- Inventory. From `theorem3_core` and `corollary1`, with `isStrictlyFirstCut_iff`, `isNonCutCF_iff`. -/
/-- **Theorem 3** (`a:thm:infer`). On an `n`-taxon rooted binary phylogenetic network `𝒩⁺` with generic numerical parameters, all
B-quartets can be identified from the quartet `CF`s using `CF`-detectability (Theorem 1) and applications of the B-quartet Inference Rule
(Theorem 2). -/
theorem theorem3 [Fintype V] [Fintype E] [Fintype X] (hN : IsBinaryNetwork N) :
    ForGenericParams N fun θ => ∀ Q : Finset X, Q.card = 4 →
      (CFInferred (nmscCF N θ 0) Q ↔ IsBlobQuartet N Q) := by
  sorry

end AllmanEtAl2023.Printed
