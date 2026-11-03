[object Object]

## New combined finite-sample pipeline proof gates

**B0 (not kernel-closed):** Establish the full finite oriented-test universe
J<=7*choose(n,4), and give an explicit finite bound H_n on the **product**
of nested Bon/BBC correction multipliers. A bound based only on the final
layer cardinality is insufficient for multi-stage composition.

**B1 (not kernel-closed):** Compose original T1/T3/LRT-star tail sandwiches,
method-of-types KL bound, and the conservative alpha_m=(m+1)^(-100) to obtain
simultaneous false-null probability <=J/(m+1)^2.

**B2 (not kernel-closed):** Prove the minimum positive off-null distance
and the single-coordinate Hoeffding event: on d_m<delta_*/6, every
alternative p-value <=exp(-m*delta_*^2/8).

**B3 (not kernel-closed):** Compose the same d_m event with the WQC bad-tree
gap and normalized guide regret, then the TOB-QMC T3 and ECToBlob Bon/BBC
deterministic reconstruction theorems. State all model/cover/selection
conditions explicitly. See [PipelineBounds.md](PipelineBounds.md), (B5).

**B4 (not kernel-closed):** Sum the finite-m error bound over m>=M,
including candidate-availability and regret failures, to prove the
(B6) tail-of-time bound. Mere convergence in probability of the guide
is not sufficient; use a.s. eventual validity or summable failures.

The companion [HANDOFF.md](HANDOFF.md) separates these new handproofs from
existing Lean-checked tail/reference lemmas and identifies the lowest-risk
first formalization gate.
