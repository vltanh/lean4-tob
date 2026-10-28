# Preliminary source audit

**Status: incomplete formalization, at the inventory and statement-design gate.**
No numbered result of the three papers has been stated or proved in the library.
The compiled foundations include finite-score stability and multigraph/network data.
The scripts described below check several source-audit
counterexamples; they do not establish the papers' network or consistency theorems.

The source texts are ECToBlob bioRxiv v1, TOB-QMC bioRxiv v5 (the user authorized
fallback from the inaccessible journal), and published TINNiK. Exact links and
download hashes are in [sources.json](docs/sources.json), with version decisions in
[CONFIGURATION.md](docs/CONFIGURATION.md). The audit used PDFs and publisher XML,
not original author TeX. TINNiK XML embeds equation TeX; ECToBlob XML uses graphics.
All three main papers and both user-supplied supplements were read. The TOB-QMC
supplement is internally dated February 26, 2026 and has some numbering differences
from main v5. Their exact version linkage remains unconfirmed. The supplement's
claims are recorded separately; an earlier internal date does not prove it was
superseded. The full independent Lean statement review is not yet complete.

## Approved statement correction: ECToBlob Theorem 8.2

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
Assumption 1, as its proof uses. The user approved this correction on 2026-10-27. The entire graph/model
counterexample is presently a written mathematical argument; any Lean certificates
below establish only their explicitly stated algebraic or statistical components.

## Other verified findings

The identifiers below follow the order in which findings were independently checked.

| ID | Location | Finding and effect |
| --- | --- | --- |
| E1 | ECToBlob (3.3), PDF p. 9 | Representative tuples overcount a quartet by the product of the sizes of the unused blocks. Blocks of sizes `(2,1,1,1,1)` with cross-block CFs all `1/3` give left side `3`, right side `10/3`. This refutes the identity, not Theorem 3.1. |
| E2 | ECToBlob Corollary 3.6 proof | Uniform convergence on a finite set does not imply equality of estimated and true argmax sets when the limit has ties. Containment in the true argmax set is sufficient and follows from the gap to nonmaximizers. |
| E3 | ECToBlob Corollary 4.3 proof | The complement forming B₂ uses the wrong index: `j′ ≠ i` should be `j′ ≠ j`. Unique index correction. |
| E4 | ECToBlob Lemma 6.1 proof | `Bon(P)=k min(P)` omits clipping at one. For `(3/4,3/4)`, Bon is `1`, not `3/2`. The needed inequality remains true. |
| E5 | ECToBlob §6 / Lemma 6.1 | Cauchy combination needs endpoint conventions: inputs may include zero, and CBC can feed Bon=1 into the transform. Lean's total tangent is not an interpretation of the undefined classical expression. |
| E6 | ECToBlob Algorithm 7.1, step 10 | The late rule needs a convention when there is no rejected iteration. Choosing the first iteration agrees with the intended selection rule. |
| E7 | ECToBlob Theorem 8.2 | Missing explicit generic-parameter restriction under the literal general-model reading; counterexample and approved correction above. |
| E8 | TINNiK B-inference, step 3(a)(i) | The number of quartets sharing exactly three taxa with a fixed quartet is `4(N−4)`, not `4(N−1)`: choose the removed taxon and one outside the quartet. At N=5 the counts are 4 and 16. The asymptotic complexity order is unchanged. |
| E9 | TINNiK Appendix C.1 | A maximum need not exist on the stated open cut model. Counts `(1,0,0)` provide a counterexample. The user approved the closed simplex for estimation, retaining strictly positive generating parameters. |
| E10 | TINNiK Theorem 4 proof | For anomalous strictly cut CFs, μ₀ tends to negative infinity; the required statement is `abs(μ₀)→∞`. Weak convergence alone does not justify the comparison at growing tail thresholds. The minimum formula gives pointwise domination by Z², providing a local repair. |
| E11 | Supplied TOB-QMC supplement Lemma 2 | Its converse is false: a treelike induced quartet can restrict a star on the full tree of blobs. The user approved retaining only the forward direction, consistent with main v5. |
| E12 | Supplied TOB-QMC supplement Lemma 4, Eq. (1), and main v5 lines 503–505 | The minimum of all three pairwise CF differences can be zero even for a species tree. Thus the asserted positivity fails and the perturbation premise can be impossible. This is a gap in the consistency proof, not a counterexample to the conditional perturbation implication. |
| E13 | Supplied TOB-QMC supplement Lemma 4 proof | Strict coordinate errors are weakened to non-strict bounds, after which strict positivity is incorrectly claimed at the chosen boundary radius. Retaining strict inequalities repairs this step at the same radius. Equations (6)–(7) must cancel agreeing quartet terms before identifying the sums; the final intermediate line also repeats the tree index where the star index is needed. |
| E14 | Supplied TOB-QMC supplement Lemma 8 | A trivial blob need not contain a reticulation: every singleton internal blob of a binary tree is a counterexample. The user approved requiring a nontrivial blob. |

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

For E11, take the rooted binary network with arcs `s→e`, `s→r`, `r→u`,
`u→v`, `v→h`, `r→w`, `w→h`, `u→a`, `v→b`, `w→c`, `h→d`.
Its single cycle has five incident taxon blocks, so its full reduced tree of blobs
is the five-leaf star. Restricting to `{e,a,b,c}` deletes the hybrid vertex h and
its descendant d; the remaining tree displays `ab|ce`. This example fits both
the directed ancestral restriction and the main text's semidirected restriction.
The supplement's attempted converse actually proves the contrapositive of its
forward implication a second time. Main v5 explicitly recognizes this distinction
in Figure 1D and its definitions. Two readers checked this counterexample.

For E12, the species-tree CF `(1/2,1/4,1/4)` makes the minimum in Eq. (1)
zero. The requirement `absolute error < 0` is then impossible, so Lemma 4 as a
conditional implication is vacuous in this case. To repair the consistency proof
along its existing route, use the positive differences between the displayed
dominant quartet and each alternative, minimized over T-quartets. Retain the
strict coordinate-error inequalities for E13; the radius remains `π/(2|f₄(S)|)`.
The corrected probability margin is a proposed local proof repair, not yet a
formal proof of the paper's theorem.

For E14, take a rooted binary four-taxon tree `((a,b),(c,d))` and its singleton
blob at the parent of a and b. It contains no reticulation. Two readers verified
this against the supplement's explicit allowance of trivial blobs. The minimal
intended correction is a nontrivial-blob hypothesis, approved by the user. The
source's descendant-chain proof still needs its directed-path choices checked;
approval of the statement correction does not certify that proof.

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
- [SunletCheck.lean](scripts/SunletCheck.lean) checks the full graph's acyclicity,
  binary network validity, all 2,048 vertex cuts, and the exact ancestral vertex
  and arc sets. An explicit isomorphism identifies the pruned graph with the
  actual original-root ancestral restriction, where `ab|ce` is a certified cut
  split. It does not yet execute LSA reduction, suppression or the reduced-tree-
  of-blobs construction.
- [TOBQMCGapCheck.lean](scripts/TOBQMCGapCheck.lean) checks the zero all-pairs
  gap, positivity of the dominant gap, and specialization of the usual quartet
  formula at length `log(4/3)`. It does not prove that coalescent formula.
- [AuditFoundations.lean](scripts/AuditFoundations.lean) checks every declaration
  in the implemented libraries, including private/auxiliary declarations. This
  is separate from the still-pending numbered-paper-result and proof-route audits.
- [paper_routes.tsv](docs/paper_routes.tsv) is a preliminary manual inventory of
  paper-internal routes. Its labels are assigned locally and are not author TeX
  labels. Supplied supplementary statements have distinct labels and a provisional
  crosswalk. No formal
  dependency graph has yet been generated, so a passing route audit is not claimed.

Run the current checks with:

```sh
lake build
lake env lean scripts/AuditFoundations.lean
lake env lean -DautoImplicit=false -DmaxSynthPendingDepth=3 scripts/SourceChecks.lean
lake env lean -DautoImplicit=false -DmaxSynthPendingDepth=3 scripts/BoundaryCheck.lean
lake env lean -DautoImplicit=false -DmaxSynthPendingDepth=3 scripts/IndistinguishabilityCheck.lean
lake env lean scripts/SunletCheck.lean
lake env lean scripts/TOBQMCGapCheck.lean
```

These scripts report only `propext`, `Classical.choice`, and `Quot.sound` for the
checked declarations. The library contains shared foundations but no numbered
paper results. Zero placeholders in those foundations are not evidence of a
completed formalization. Challenge and
Solution contain no theorem statements; Comparator and Palomar checks have not run.

At the 2026-10-27 22:13 America/Chicago checkpoint, `lake build` passed without
warnings and the foundations audit checked all 388 library declarations using
only the standard axioms. This includes definitions and generated/private
declarations; it is not a count of paper results.

At the 22:42 checkpoint, the build of 16 implemented modules and the expanded
foundations audit passed for 522 declarations. The exact ancestral restriction,
hierarchy graph realization and binary quartet-display bridges are now proved.
Reduced-graph suppression, the arbitrary-network coalescent construction and
the numbered paper results remain pending.

## Source coverage and remaining work

TINNiK: Definitions 1–7; cited Theorems 1–3; internal Theorem 4 and
Propositions 5–6; both algorithms; 22 displayed equations inventoried. The exact
NMSC, genericity, LR approximation, density calculation, quartet-distance bridge,
and neighbor-joining justification remain to be formalized or sourced faithfully.

ECToBlob: Theorems 3.1, 4.1, 8.2; Lemmas 3.5, 6.1, 8.1; Corollaries 3.6,
4.2, 4.3; Proposition 5.1; Assumption 1; Algorithm 7.1; numbered equations,
remarks and running-time claims inventoried. Supplementary A/B was read: simulations,
Tables S1–S4 and Figures S1–S3, with no additional numbered mathematical results.

TOB-QMC v5: Definitions 1–2; cited Lemmas 1–2; internal Lemmas 3–4,
Theorems 1–2, Corollary 1 and Equations 1–4 inventoried. The supplement contains
Lemmas 2, 4, 7, 8, Definition 2, Theorem 1, Equations (1)–(8), Algorithms 1–2,
and sampling/complexity claims. Its internal numbering is recorded separately
from the main text. These are inventoried and reviewed, not formally proved.
The arbitrary-level WQC result must not be
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
claims needed here. A small tree-only hierarchy kernel was extracted with its
existing proof arguments and independently checked; [ADAPTED_SOURCES.md](docs/ADAPTED_SOURCES.md)
records the commit, source regions, license and wrapper adaptations. Its network
and coalescent modules were not imported. CAMUS remains a surveyed source only.

The main immediate work is to implement the approved scopes and finish the
definitions, source crosswalk and statements before proving paper
results. Private follow-up-paper research and NEXT.md have not been developed;
there is no novelty claim or completed research recommendation at this stage.
