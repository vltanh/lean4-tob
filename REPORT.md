# Preliminary source audit

**Status: incomplete formalization, at the inventory and statement-design gate.**
No numbered result of the three papers has been stated or proved in the library.
The project scaffold builds. The scripts described below check several source-audit
counterexamples; they do not establish the papers' network or consistency theorems.

The source texts are ECToBlob bioRxiv v1, TOB-QMC bioRxiv v5 (the user authorized
fallback from the inaccessible journal), and published TINNiK. Exact links and
download hashes are in [sources.json](docs/sources.json), with version decisions in
[CONFIGURATION.md](docs/CONFIGURATION.md). The audit used PDFs and publisher XML,
not original author TeX. TINNiK XML embeds equation TeX; ECToBlob XML uses graphics.
All three main papers were read. Both bioRxiv supplements remain inaccessible.
Consequently neither the full inventory nor independent statement review is complete.

## Immediate statement decision: ECToBlob Theorem 8.2

The printed theorem quantifies over any model meeting Assumption 1, without
restricting the network's numerical parameters to the generic set. Assumption 1
only promises its identifiability converses generically. No standing genericity
assumption was found in the preceding text. The proof, by contrast, explicitly
invokes generic numerical parameters. Its intended scope appears to be the generic
one, but adopting that scope adds a hypothesis to the printed statement.

Here is a counterexample to the literal general-model statement. It is not a claim
that an NMSC-specific counterexample has been established.

Take four taxa and a rooted four-cycle network with one pendant taxon at each
cycle vertex. Its reduced tree of blobs is the star. One concrete rooted graph has
arcs `s→r`, `s→d`, `r→u`, `r→v`, `u→h`, `v→h`, `u→a`, `v→b`, `h→c`.
The root s is the LSA. This binary directed graph is acyclic and has a single
nontrivial four-blob on r,u,h,v. Its fourth pendant branch reaches d through s;
suppressing s after contraction yields the star. All tree edges may have positive
lengths and the hybrid inheritance parameters may lie strictly between zero and one.

Choose one positive tree-edge length t as a parameter and assign the iid resolved
gene-tree distribution

\[
p(t)=\left(\tfrac12,\tfrac14+h(t),\tfrac14-h(t)\right),\qquad
h(t)=\frac{t-1}{8(1+(t-1)^2)},\quad t>0.
\]

Since `|h(t)| ≤ 1/16`, all probabilities are positive. Their sum is one. Except
at t=1, all three coordinates are distinct; at t=1 the vector is `(1/2,1/4,1/4)`.
The exceptional locus t=1 is null for the parameter measure because t is a tree-edge
length with Lebesgue measure. Thus the blob model satisfies the generic converse
in Assumption 1. It is never a centroid CF.

On a resolved tree with split ab/cd, assign the constant gene-tree law
`(1/2,1/4,1/4)`. This satisfies the required strict cut equality and dominance.
On trivial four-blob networks assign the uniform law, on other resolved four-taxon
networks assign the corresponding permuted cut law, and on other nontrivial
four-blob topologies assign a positive vector with distinct coordinates. These
assignments extend the example to a model on the fixed four-taxon set obeying
Assumption 1. The theorem allows such general models; it does not require NMSC.

The same starting tree ab/cd refines both targets. At the blob parameter t=1,
the input count distributions are identical to those from the resolved tree at
every sample size. Every fixed algorithm variant with the same network-independent
test-level sequences therefore has the same output distribution in the two cases.
Consistency for the resolved tree requires the probability of output ab/cd to tend
to one, while consistency for the blob requires it to tend to zero. Both are
impossible. Randomized tie breaking does not change this argument if it uses the
same randomization law.

Two independent readers checked the source scope and this argument. **No genericity
hypothesis has been silently added to a Lean statement.** The proposed correction
is to quantify Theorem 8.2 over parameters outside the exceptional sets in
Assumption 1, as its proof uses. User approval is pending. The entire graph/model
counterexample is presently a written mathematical argument; any Lean certificates
below establish only their explicitly stated algebraic or statistical components.

## Other verified findings

The identifiers below follow ECToBlob then TINNiK; TOB-QMC issues remain provisional
until its supplement is read.

| ID | Location | Finding and effect |
| --- | --- | --- |
| E1 | ECToBlob (3.3), PDF p. 9 | Representative tuples overcount a quartet by the product of the sizes of the unused blocks. Blocks of sizes `(2,1,1,1,1)` with cross-block CFs all `1/3` give left side `3`, right side `10/3`. This refutes the identity, not Theorem 3.1. |
| E2 | ECToBlob Corollary 3.6 proof | Uniform convergence on a finite set does not imply equality of estimated and true argmax sets when the limit has ties. Containment in the true argmax set is sufficient and follows from the gap to nonmaximizers. |
| E3 | ECToBlob Corollary 4.3 proof | The complement forming B₂ uses the wrong index: `j′ ≠ i` should be `j′ ≠ j`. Unique index correction. |
| E4 | ECToBlob Lemma 6.1 proof | `Bon(P)=k min(P)` omits clipping at one. For `(3/4,3/4)`, Bon is `1`, not `3/2`. The needed inequality remains true. |
| E5 | ECToBlob §6 / Lemma 6.1 | Cauchy combination needs endpoint conventions: inputs may include zero, and CBC can feed Bon=1 into the transform. Lean's total tangent is not an interpretation of the undefined classical expression. |
| E6 | ECToBlob Algorithm 7.1, step 10 | The late rule needs a convention when there is no rejected iteration. Choosing the first iteration agrees with the intended selection rule. |
| E7 | ECToBlob Theorem 8.2 | Missing explicit generic-parameter restriction under the literal general-model reading; counterexample and pending decision above. |
| E8 | TINNiK B-inference, step 3(a)(i) | The number of quartets sharing exactly three taxa with a fixed quartet is `4(N−4)`, not `4(N−1)`: choose the removed taxon and one outside the quartet. At N=5 the counts are 4 and 16. The asymptotic complexity order is unchanged. |
| E9 | TINNiK Appendix C.1 | A maximum need not exist on the stated open cut model. Counts `(1,0,0)` provide a counterexample. The user approved the closed simplex for estimation, retaining strictly positive generating parameters. |
| E10 | TINNiK Theorem 4 proof | For anomalous strictly cut CFs, μ₀ tends to negative infinity; the required statement is `abs(μ₀)→∞`. Weak convergence alone does not justify the comparison at growing tail thresholds. The minimum formula gives pointwise domination by Z², providing a local repair. |

For E1, uniform cross-block CFs are realized by a rooted multifurcating species
tree with one positive-length two-taxon cherry and four other pendant taxa.
Four taxa in distinct center blocks enter the root singly, so exchangeability gives
probability 1/3 for each quartet. Quartets using both cherry taxa have strict
cut dominance. This meets Theorem 3.1's assumptions. The finite counting certificate
checks the cardinalities and arithmetic, not this coalescent realization.

A repair of E1 keeps the simultaneous-maximization argument: let
`W=∏ᵢ |Xᵢ|`, weight each local four-block term by the product of its four block
sizes, sum over representative tuples and divide by W. Each actual quartet then
has coefficient one. The local objective used for splicing must also be weighted.
This retains the route through Lemma 3.5; it is a proposed repair, not yet a Lean proof.

For E2, even `f(a)=f(b)=0`, `fₙ(a)=1/(n+1)`, `fₙ(b)=0` has uniform convergence
and different argmax sets for every n. This disproves the inference made in the
proof; it does not refute Corollary 3.6. For E5, use continuous endpoint extensions
on the actual permitted inputs. Simultaneous zero and one inputs to the general
Cauchy operator have no path-independent continuous extension. That conflict does
not occur in CBC on the lemma's input domain: Bon=1 forces every input positive.

For E9, if `(p₁,p₂,p₃)` is any positive simplex point, set
`q=((1+p₁)/2,(1−p₁)/4,(1−p₁)/4)`. Then q is an open cut-model point and
`q₁>p₁`. The likelihood for counts `(1,0,0)` is p₁, proving nonexistence of a
maximum even over the whole open cut model. On the closed cut model `(1,0,0)`
attains the maximum. The approved correction concerns estimation only.

Additional proof obligations remain: TINNiK's data-dependent choice of fitted
line and the all-cut case; ECToBlob's bounds across every possible contraction
state and whole-tree test, slack in asymptotic inequalities, and the unnecessary
claimed upper bound below one for clipped combined null p-values. These are
pending proof reviews, not additional false-theorem claims.

## Checked artifacts and their limits

- [SourceChecks.lean](scripts/SourceChecks.lean) proves the finite quartet counts,
  the arithmetic mismatch in (3.3), and Bonferroni saturation using kernel-checked
  `decide` and arithmetic tactics.
- [BoundaryCheck.lean](scripts/BoundaryCheck.lean) proves nonexistence of the open
  cut-model MLE for `(1,0,0)`, attainment in the closed model, and the inclusion
  of the generating parameter space in the estimation space.
- [IndistinguishabilityCheck.lean](scripts/IndistinguishabilityCheck.lean) checks
  positivity and normalization of the whole real parameter family, non-cutness
  exactly when t≠1, the exact probability collision, and the incompatible-limit
  argument. It does not formalize the network construction, the product-measure
  null-set claim, or equality of the induced output laws.
- [paper_routes.tsv](docs/paper_routes.tsv) is a preliminary manual inventory of
  paper-internal routes. Its labels are assigned locally and are not author TeX
  labels. It explicitly identifies an unread supplementary lemma. No formal
  dependency graph has yet been generated, so a passing route audit is not claimed.

Run the current checks with:

```sh
lake build
lake env lean -DautoImplicit=false -DmaxSynthPendingDepth=3 scripts/SourceChecks.lean
lake env lean -DautoImplicit=false -DmaxSynthPendingDepth=3 scripts/BoundaryCheck.lean
lake env lean -DautoImplicit=false -DmaxSynthPendingDepth=3 scripts/IndistinguishabilityCheck.lean
```

These scripts report only `propext`, `Classical.choice`, and `Quot.sound` for the
checked declarations. The library is still an empty scaffold. Zero placeholders in
an empty library are not evidence of a completed formalization. Challenge and
Solution contain no theorem statements; Comparator and Palomar checks have not run.

## Source coverage and remaining work

TINNiK: Definitions 1–7; cited Theorems 1–3; internal Theorem 4 and
Propositions 5–6; both algorithms; 22 displayed equations inventoried. The exact
NMSC, genericity, LR approximation, density calculation, quartet-distance bridge,
and neighbor-joining justification remain to be formalized or sourced faithfully.

ECToBlob: Theorems 3.1, 4.1, 8.2; Lemmas 3.5, 6.1, 8.1; Corollaries 3.6,
4.2, 4.3; Proposition 5.1; Assumption 1; Algorithm 7.1; numbered equations,
remarks and running-time claims inventoried. Supplementary A/B is still unread.

TOB-QMC v5: Definitions 1–2; cited Lemmas 1–2; internal Lemmas 3–4,
Theorems 1–2, Corollary 1 and Equations 1–4 inventoried. The supplement contains
another Lemma 4 (the perturbation bound used by Theorem 1) and Algorithms 1–2;
these are explicitly unverified. The arbitrary-level WQC result must not be
confused with the level-1 contraction theorem, and neither establishes the
consistency of TREE-QMC's heuristic search.

No cited theorem has been installed as an axiom or assumed result. Selection of
any future named external hypotheses awaits exact source statements and a library
survey. Paper-internal results cannot be turned into assumptions to close gaps.
A full statements baseline, independent statement review, proofs, axiom audit,
route audit, nonvacuity checks, cleanup, final report and packaging all remain.

## Literature and next work

The dated search (2026-10-27 America/Chicago) found the later TOB-QMC journal
publication and the ECToBlob authors' announcement of a forthcoming SIALS article.
No revised ECToBlob manuscript or published erratum was located. No exact Lean
formalization of these three papers surfaced in the searches; this is a bounded
search result, not an exhaustive nonexistence claim.

The public [Phylogenetics library](https://github.com/vltanh/lean4-phylogenetics)
and [CAMUS formalization](https://github.com/vltanh/lean4-camus) are relevant prior
work. The former supplies tree, coalescent and level-1 network foundations. Its
network type does not establish the arbitrary-level or correlated-inheritance
claims needed here. Its README and sources were inspected; neither project was
copied into the library or added as a dependency.

The main immediate work is to settle E7's statement scope, retrieve both
supplements, and finish the definitions and statements before proving paper
results. Private follow-up-paper research and NEXT.md have not been developed;
there is no novelty claim or completed research recommendation at this stage.
