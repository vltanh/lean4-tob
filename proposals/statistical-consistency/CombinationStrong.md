# ECToBlob-BBC joins Bonferroni for strong consistency; Cauchy/CBC have an endpoint obstruction

**Status: new handproof-level result, not Lean-checked.** The exact existing implementations are in [\`Basic/Testing/Combining.lean\`](../../src/Basic/Testing/Combining.lean). This note strengthens [the original-p-value theorem](OriginalPValuesStrong.md) without changing any inference code or reported default parameters.

## 1. A deterministic comparison lemma for BBC

Let \(P\) be a nonempty finite multiset of p-values in \([0,1]\), with \(k=|P|\) and \(u=\min P\).

The existing combination functions are
\[
\mathrm{Bon}(P)=\min(1,ku),\qquad
\mathrm{BBC}(P)=\min(1,2\min\{\mathrm{Bon}(P),\mathrm{Cau}(P)\}).
\]

The Cauchy transform \(f(p)=\tan(\pi(1/2-p))\) is strictly **decreasing** on \((0,1)\); its inverse is decreasing too. Therefore, for all p-values strictly between 0 and 1, \(\min P\le\mathrm{Cau}(P)\le\max P\) because the average of the transformed values lies between the minimum and maximum transformed values. The special definition at endpoints does not invalidate the **lower** bound:

- If \(0\in P\), \(\mathrm{Cau}(P)=0=u\).
- Otherwise if \(1\in P\), \(\mathrm{Cau}(P)=1\ge u\).
- Otherwise the interior argument applies.

Because \(\mathrm{Bon}(P)\ge u\), we obtain the **deterministic sandwich**
\[
\boxed{
u\le \mathrm{BBC}(P)\le \min(1,2ku).
}\tag{B1}
\]

It also holds for \(\mathrm{Bon}(P)\) with upper factor \(k\). For the empty multiset, the existing wrapper \(\mathrm{combineP}\) returns 1 and no rejection is appropriate.

**Consequences for a collection of scalar tests:**

- If **every** constituent is a true null and each constituent p-value is eventually larger than \(\alpha_m\), then BBC is also larger than \(\alpha_m\) and cannot falsely reject.
- If **some** constituent is off-null, with its p-value eventually smaller than \(\alpha_m/(2K_{\max})\), BBC is smaller than \(\alpha_m\). For Bon, use \(K_{\max}\) rather than \(2K_{\max}\).

No independence among quartet p-values is required: B1 is a pointwise deterministic inequality.

## 2. Strengthened ECToBlob theorem target

Assume the same conditions as the ECToBlob theorem in [OriginalPValuesStrong.md](OriginalPValuesStrong.md): fixed taxa; iid complete binary gene-tree distribution; both directions of Assumption 1; LRT star test; and a sequence of possibly same-data binary guide trees \(T_m\).

For either \(\mathrm{testCo}=\mathrm{bon}\) **or** \(\mathrm{testCo}=\mathrm{bbc}\), any prescribed positive levels satisfying
\[
\log\log m=o(-\log\alpha_m),\quad -\log\alpha_m=o(m)
\]
and the same conditions for \(\beta_m\) where true star-null quartets occur, yield the **handproof-level strong conclusion**
\[
\Pr\left(\exists M\;\forall m\ge M:
  \mathrm{ECToBlob}_{\mathrm{testCo,LRT}}(T_m)=
     \mathrm{limitTree}(N,T_m)\right)=1.
\]
The explicit, conservative \(\alpha_m=\beta_m=(m+1)^{-100}\) additionally admits the finite-sample per-scalar-test \((m+1)^{-2}\) true-null error bound from the method of types. Under binary network Assumption-1 conditions, fixed \(\beta\in(0,1)\) remains sufficient.

At a particular \(m\), the BBC alternative power inequality in the earlier note uses \(K_{\max}\) replaced by \(2K_{\max}\), adding only \(\log 2\) to the sample-size separation condition. The null bound is unchanged. This covers **the actual BBC implementation**, with no extra positivity assumption on population quartet coordinates.

B1 is an elementary deterministic proof obligation, not a finished Lean theorem in this PR. The underlying analytic, probability-one and reconstruction compositions also remain open in the kernel.

## 3. Why pure Cauchy and CBC are different: a concrete recurrent-null mechanism

The *existing* \`cauchyP\` is defined to return **1 whenever \(1\in P\) but \(0\notin P\)**. Because \(\mathrm{CBC}(P)=\mathrm{Cau}(\{\mathrm{Bon}(P),\mathrm{Cau}(P)\})\), CBC also returns 1 if \(\mathrm{Cau}(P)=1\) while \(\mathrm{Bon}(P)>0\).

A scalar p-value can equal exactly 1 infinitely often, even at a **strictly positive, regular T1 null**. Fix a quartet population
\[
p_s=(\theta,q,q),\quad 1/3<\theta<1,\quad q=(1-\theta)/2>0.
\]
On the infinite iid gene-tree sequence, let \(a_m,b_m\) be the counts of the two discordant resolutions. The difference \(D_m=a_m-b_m\) has iid increments in \(\{-1,0,+1\}\), with probabilities \((q,\theta,q)\). Its embedded nonzero-step process is a simple symmetric random walk and returns to zero **infinitely many times almost surely**.

For every sufficiently large \(m\), the matching count \(c_m\) exceeds \((a_m+b_m)/2\) because \(\theta>1/3\). On every later return \(D_m=0\), the original T1 likelihood-ratio statistic is **zero** (\(\mathrm{lineStat}=0\)); the original T1 p-value therefore equals **exactly 1**. This happens infinitely often almost surely despite the population remaining strictly inside the null.

Now suppose a fixed combined quartet family also contains an off-T1 comparison whose original p-value tends to zero exponentially but stays strictly positive at each finite sample size. Such a scalar configuration is compatible with iid data; no independence between the two quartet statistics is required. On infinitely many sample sizes, the family contains an **exact 1** and a **tiny positive** constituent. The existing pure Cauchy rule returns
\[
\mathrm{Cau}(P_m)=1,
\]
and the CBC rule also returns 1, regardless of how strong the nonnull evidence becomes. For any level sequence eventually less than 1, these mixed-family tests **fail to reject infinitely often almost surely**.

**Scope of the obstruction:** this is a counterexample to a universal *eventual rejection theorem for the raw Cauchy/CBC combined scalar tests*, not yet a fully constructed biological network whose final ECToBlob output is incorrect infinitely often. A network-level failure requires a specified guide edge, fixed mixed quartet family and proof that other tests cannot repair its decision. Do not claim that result without constructing it.

This explains why the BBC strong-consistency extension is materially different from the pure Cauchy/CBC variants. It also shows that **positive quartet CF coordinates alone do not prevent exact p=1 events**. Any strong theorem for Cauchy/CBC needs additional restrictions, a modified endpoint rule, or a different control of mixed comparisons.

## 4. Formalization gates

1. Prove B1 in the existing \`Basic/Testing/Combining\` API, with nonempty multiset and \(0\le p\le1\) for every value. Check endpoint precedence \(0\in P\) before \(1\in P\).
2. Instantiate the original-test strong-consistency proof for \(\mathrm{testCo}=\mathrm{bbc}\) by B1, with an alternative multiplier \(2K_{\max}\).
3. Optionally formalize the recurrence statement for the lazy symmetric random walk and the exact \(\mathrm{t1PValue}=1\) at discordant count equality. This should be kept separate from the positive consistency theorem.
4. Do not add a blanket Cauchy/CBC almost-sure theorem based solely on the fixed-threshold asymptotic uniformity or the positivity of population CF coordinates.

**Verification:** none of these new steps has been compiled; no \`src/\` changes or kernel audit was performed in this PR.
