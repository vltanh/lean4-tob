# Consistent guides from vanishing optimization regret

**Status: elementary handproof and uncompiled deterministic Lean draft; not a claim about any installed optimizer.** This result is reusable by TOB-QMC, ECToBlob and QWC, but belongs with the WQC/guide theory rather than any particular contraction statistic.

## 1. Normalize the objective explicitly

Fix n>=4 taxa and let Q=choose(n,4). Let H be the finite set of unrooted binary labelled trees. For a population quartet CF function p, define

    S_p(T) = (1/Q) * sum over q of p_q(T restricted to q).

The empirical score S_hat_m replaces p by observed quartet frequencies. It is in [0,1]; the unnormalized integer WQC score is m*Q*S_hat_m. Suppose every population maximizer refines the true ToB B. Under the hypotheses of the WQC theory in this repository, this follows from strict ToB-quartet dominance and cut exchangeability; see the population theorem `ECToBlob.theorem3_1` and the margin argument used in `TOBQMC.theorem1_optimal`.

If a non-refining tree exists, define the **population bad-tree gap**

    Delta = max_T S_p(T) - max_{T not refining B} S_p(T) > 0.

Positivity is a consequence of finiteness and exclusion of every bad maximizer. If every binary tree refines B, the result is vacuous and no gap is needed.

## 2. Deterministic margin lemma

Let H_m be the candidate search space and suppose it contains a population-optimal tree T*. Let the selected guide T_m satisfy

    max_{T in H_m} S_hat_m(T) - S_hat_m(T_m) <= r_m.

Write d_m=max_{oriented quartets s}|p_hat_m(s)-p(s)|. Then

    2*d_m + r_m < Delta  ==>  T_m refines B.

**Proof.** Each tree uses exactly Q quartet probabilities, so its normalized score error is at most d_m. Therefore

    S_p(T_m) >= S_hat_m(T_m)-d_m
             >= S_hat_m(T*)-r_m-d_m
             >= max_T S_p(T)-r_m-2*d_m.

If T_m were bad, its population score would be at most max S_p-Delta, a contradiction. This uses an observable-law approximation error and an optimizer regret, not a certificate assuming the desired guide topology.

A complete proposed Lean proof of this scalar margin argument is in `drafts/ScoreGap.lean.txt`, but it has not been elaborated.

## 3. Strong and weak guide consistency

Suppose d_m->0 almost surely, some population-optimal tree is eventually in H_m almost surely, and r_m->0 almost surely. Then the margin inequality eventually holds and **every selected guide is a ToB refinement eventually almost surely**.

In raw integer WQC units, the optimization condition is

    raw regret = o(m*Q),

which is o(m) at fixed n. Exact optimization is sufficient, not necessary. A fixed positive approximation ratio does not automatically imply this condition; it can leave non-vanishing normalized regret.

If the three assumptions hold only in probability, the conclusion holds only in probability. For a randomized optimizer, a sufficient route to the almost-sure statement is summability of the probabilities of violating a prescribed vanishing regret bound. No independence between optimizer randomization, guide data and contraction data is required once the necessary pathwise events have been established.

For NMSC with positive probability for every binary gene-tree topology, an ASTRAL-style search space retaining **all observed gene-tree bipartitions** eventually contains every binary tree at fixed n. Thus candidate availability holds, even if optimization is only asymptotically near-exact. This says nothing about how large the required sample size is or about search heuristics that discard observed bipartitions.

## 4. Quantitative iid bound

For independent complete gene trees, each oriented quartet frequency is an average of m Bernoulli variables. Hoeffding and a union bound over 3Q coordinates give

    P(d_m >= x) <= 6Q exp(-2m x^2).

No independence between quartets within a locus is used. Suppose a deterministic regret bound r<Delta holds except on an event of probability b_m, and candidate availability fails with probability at most a_m. Then

    P(T_m does not refine B)
      <= a_m + b_m + min(1, 6Q exp[-m(Delta-r)^2/2]).

Equivalently one may cap the whole right-hand side at 1. Delta is an analysis constant, not an input parameter to the algorithm. A quantitative candidate-availability bound can be obtained by selecting one fixed population-optimal binary tree and requiring each of its splits to appear; if split A has probability pi_A>0 in a locus, a union bound gives a_m <= sum_A exp(-m*pi_A). These events are not assumed independent.

## 5. Why this matters for the inference pipelines

Combine the guide event with the appropriate contraction event. Pathwise correctness composes on an intersection of probability-one events; for finite samples use

    P(pipeline error) <= P(guide not refining B)
                        + P(contraction tests not simultaneously correct).

The contraction event should be established over the finite universe of oriented quartets and permissible candidate states before selecting the guide from the same loci. Simply invoking a fixed-guide theorem without this uniformity is insufficient.

This proof does **not** establish a vanishing-regret guarantee for TREE-QMC, arbitrary ASTRAL variants, NNI local optima, or a finite heuristic run. Those remain separate algorithmic proof obligations. The relaxation is mathematically useful precisely because it states the weaker condition an approximate solver would need to prove.
