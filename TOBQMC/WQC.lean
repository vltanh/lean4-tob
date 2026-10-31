module

public import Basic.Phylogenetics.NMSC.Basic
public import Basic.Probability.IID
public import External.AneEtAl2024.Exchangeability
public import Mathlib.Probability.StrongLaw

/-!
# TOB-QMC §4.1–4.2: quartet-based species tree methods give a refinement of the tree of blobs

Definition 1, Equations (1)–(4), Lemma 3, the perturbation Lemma 4 of the Supplement, Theorem 1 and the
ASTRAL corollary. These results take the exchangeability of taxa on one side of a cut edge from the
literature (`External.AneEtAl2024.Exchangeability`), so they are conditional on it.
-/

@[expose] public noncomputable section

open Phylogenetics Phylogenetics.RootedNetwork Finset Filter Topology MeasureTheory ProbabilityTheory
open scoped Classical

namespace TOBQMC

variable {V E X : Type*} [Fintype X] [DecidableEq X]

/-- A choice of a parent at each vertex: the display trees of the network. -/
def IsDisplayChoice (N : RootedNetwork V E X) (c : V → E) : Prop :=
  ∀ v, 2 ≤ N.graph.indegree v → N.graph.target (c v) = v

/-- The arcs of the display tree of the choice `c`. -/
def displayArcs (N : RootedNetwork V E X) (c : V → E) : Set E :=
  {e | N.IsTreeArc e ∨ e = c (N.graph.target e)}

/-- A taxon is below an arc in the display tree of the choice `c`. -/
def BelowInDisplay (N : RootedNetwork V E X) (c : V → E) (u : V) (x : X) : Prop :=
  Relation.ReflTransGen (fun a b => ∃ f ∈ displayArcs N c, N.graph.source f = a ∧ N.graph.target f = b)
    u (N.leaf x)

/-- The network displays the quartet tree `s`: some display tree restricted to the taxa of `s` has
an edge with one cherry of `s` below it. -/
def NetworkDisplays (N : RootedNetwork V E X) (s : QuartetTree X) : Prop :=
  ∃ c, IsDisplayChoice N c ∧ ∃ e ∈ displayArcs N c,
    (s.taxa.filter fun x => BelowInDisplay N c (N.graph.target e) x) ∈ s.val

/-- **Definition 1** (`tob2025:definition1`), quartet-nonanomalous: every induced 4-taxon network
displays more than one quartet tree, or displays one, which has the largest concordance factor. -/
def IsQuartetNonanomalous (N : RootedNetwork V E X) (F : QuartetTree X → ℝ) : Prop :=
  ∀ q : Finset X, q.card = 4 →
    (∃ s ∈ treesOn q, ∃ s' ∈ treesOn q, s ≠ s' ∧ NetworkDisplays N s ∧ NetworkDisplays N s') ∨
    ∃ s ∈ treesOn q, NetworkDisplays N s ∧ ∀ r ∈ s.alternatives, F r < F s

/-- The tree part `QS^tree` of the quartet score of `t`: the quartet trees on the 4-taxon sets that `TN`
resolves. -/
def treePart (TN : Finset (Finset X)) (F : QuartetTree X → ℝ) (t : Finset (Finset X)) : ℝ :=
  ∑ s, if (∃ r ∈ treesOn s.taxa, Displays TN r) ∧ Displays t s then F s else 0

/-- The star part `QS^star` of the quartet score of `t`: the 4-taxon sets that `TN` does not resolve. -/
def starPart (TN : Finset (Finset X)) (F : QuartetTree X → ℝ) (t : Finset (Finset X)) : ℝ :=
  ∑ s, if (∀ r ∈ treesOn s.taxa, ¬ Displays TN r) ∧ Displays t s then F s else 0

/-- The part `QS^v` of the quartet score of `t` from the 4-taxon sets around the vertex `P` of `TN`. -/
def vertexPart (P : Finset (Finset X)) (F : QuartetTree X → ℝ) (t : Finset (Finset X)) : ℝ :=
  ∑ s, if InDistinctBlocks P s.taxa ∧ Displays t s then F s else 0

/-- The part `QS^{v(x)}` of the quartet score of `t` from the 4-taxon sets around the vertex `P`
containing the taxon `x`. -/
def vertexTaxonPart (P : Finset (Finset X)) (x : X) (F : QuartetTree X → ℝ)
    (t : Finset (Finset X)) : ℝ :=
  ∑ s, if InDistinctBlocks P s.taxa ∧ x ∈ s.taxa ∧ Displays t s then F s else 0

/-- **Equation (1)** (`tob2025:equation1`). -/
theorem equation1 (TN : Finset (Finset X)) (F : QuartetTree X → ℝ) (t : Finset (Finset X)) :
    quartetScore F t = treePart TN F t + starPart TN F t := by
  sorry

/-- **Equation (2)** (`tob2025:equation2`). For a T-quartet-nonanomalous network, the tree part of the
score is larger at any tree resolving `T_N`, in particular at `T_N`, than at a tree not resolving it.
The score of a tree that resolves `T_N` is that of `T_N`. -/
theorem equation2 {V E : Type*} {N : RootedNetwork V E X} (hN : N.IsPhylogenetic)
    {F : QuartetTree X → ℝ} (hF : ∀ s, 0 < F s) (hNon : IsTQuartetNonanomalous N F)
    {B T : Finset (Finset X)} (hB : IsUnrootedTree B) (hBT : treeOfBlobs N ⊆ B)
    (hT : IsBinaryTree T) (hTN : ¬ treeOfBlobs N ⊆ T) :
    treePart (treeOfBlobs N) F T < treePart (treeOfBlobs N) F B := by
  sorry

/-- **Equation (3)** (`tob2025:equation3`). The star part is the sum over the vertices of degree greater
than three of `T_N` of their parts. -/
theorem equation3 {TN : Finset (Finset X)} (hTN : IsUnrootedTree TN) (F : QuartetTree X → ℝ)
    (t : Finset (Finset X)) :
    starPart TN F t = ∑ P ∈ multifurcations TN, vertexPart P F t := by
  sorry

/-- **Equation (4)** (`tob2025:equation4`), the partial score: summing it over all taxa counts each
4-taxon set four times. -/
theorem equation4 (P : Finset (Finset X)) (F : QuartetTree X → ℝ) (t : Finset (Finset X)) :
    ∑ x, vertexTaxonPart P x F t = 4 * vertexPart P F t := by
  sorry

/-- **Lemma 3**, in the form its proof gives, for weights `F` with the properties that the proof uses:
there is a binary refinement `B` of the tree of blobs that maximizes the star part and the tree part of
the score over binary trees, and has a larger score than every binary tree not refining the tree of
blobs. -/
theorem lemma3_of_properties {V E : Type*} {N : RootedNetwork V E X} (hN : N.IsPhylogenetic)
    {F : QuartetTree X → ℝ} (hF : ∀ s, 0 < F s) (hEx : CutExchangeable N F)
    (hNon : IsTQuartetNonanomalous N F) (hX : 4 ≤ Fintype.card X) :
    ∃ B, IsBinaryTree B ∧ treeOfBlobs N ⊆ B ∧
      (∀ T, IsBinaryTree T → starPart (treeOfBlobs N) F T ≤ starPart (treeOfBlobs N) F B) ∧
      ∀ T, IsBinaryTree T → ¬ treeOfBlobs N ⊆ T → quartetScore F T < quartetScore F B := by
  sorry

/-- **Lemma 3** (`tob2025:lemma3`), conditional on exchangeability. For a network under the standard
assumptions that is T-quartet-nonanomalous, with the exact expected concordance factors, there is a
binary refinement of the tree of blobs with higher quartet score than every binary tree that does
not refine it. -/
theorem lemma3 [Fintype V] [Fintype E] {N : RootedNetwork V E X} {θ : MetricData E} {ρ : ℝ}
    (hStd : StandardAssumptions N θ ρ) (hEx : External.AneEtAl2024.Exchangeability N θ ρ)
    (hNon : IsTQuartetNonanomalous N (nmscCF N θ ρ)) (hX : 4 ≤ Fintype.card X) :
    ∃ B, IsBinaryTree B ∧ treeOfBlobs N ⊆ B ∧ ∀ T, IsBinaryTree T → ¬ treeOfBlobs N ⊆ T →
      quartetScore (nmscCF N θ ρ) T < quartetScore (nmscCF N θ ρ) B := by
  sorry

/-- The margin `π` of the perturbation lemma: the least difference, over the 4-taxon sets that `T_N`
resolves, between the concordance factor of the quartet tree `T_N` displays and those of the
alternatives. E12 of the report: the printed "minimum of all differences" can vanish. -/
def Margin (N : RootedNetwork V E X) (F : QuartetTree X → ℝ) (π : ℝ) : Prop :=
  ∀ s, Displays (treeOfBlobs N) s → ∀ r ∈ s.alternatives, π ≤ F s - F r

/-- **Supplement, Lemma 4** (`tob2025:supplement_lemma4`), with the corrected margin (E12) and strict
bounds (E13). If all the errors of the weights `w` are below `π / (2 |f₄(S)|)`, the score of a
refinement `B` maximizing the star part exceeds that of every binary tree not refining `T_N`. -/
theorem supplementLemma4 {V E : Type*} {N : RootedNetwork V E X} (hN : N.IsPhylogenetic)
    {F w : QuartetTree X → ℝ} {π : ℝ} (hπ : 0 < π) (hmargin : Margin N F π)
    (herr : ∀ s, |w s - F s| < π / (2 * ((Fintype.card X).choose 4 : ℝ)))
    {B T : Finset (Finset X)} (hB : IsBinaryTree B) (hBT : treeOfBlobs N ⊆ B)
    (hstar : starPart (treeOfBlobs N) F T ≤ starPart (treeOfBlobs N) F B)
    (hT : IsBinaryTree T) (hTN : ¬ treeOfBlobs N ⊆ T) :
    quartetScore w T < quartetScore w B := by
  sorry

/-- **Theorem 1** (`tob2025:theorem1`), conditional on exchangeability. For a network under the
standard assumptions that is T-quartet-nonanomalous and independent gene trees from the NMSC, for any
binary tree `T` not refining the tree of blobs and any `ε > 0` there are a binary refinement `B` and
`K` such that `QS_k(B) > QS_k(T)` for all `k ≥ K` with probability at least `1 - ε`. -/
theorem theorem1 [Fintype V] [Fintype E] {N : RootedNetwork V E X} {θ : MetricData E} {ρ : ℝ}
    (hStd : StandardAssumptions N θ ρ) (hEx : External.AneEtAl2024.Exchangeability N θ ρ)
    (hNon : IsTQuartetNonanomalous N (nmscCF N θ ρ)) (hX : 4 ≤ Fintype.card X)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (G : ℕ → Ω → Finset (Finset X)) (hG : IsGeneTreeSample P N θ ρ G)
    (T : Finset (Finset X)) (hT : IsBinaryTree T) (hTN : ¬ treeOfBlobs N ⊆ T) {ε : ℝ} (hε : 0 < ε) :
    ∃ (B : Finset (Finset X)) (K : ℕ), IsBinaryTree B ∧ treeOfBlobs N ⊆ B ∧
      1 - ε ≤ P.real {ω | ∀ k, K ≤ k → quartetScore (geneCount G k ω) T < quartetScore (geneCount G k ω) B} := by
  sorry

/-- **Theorem 1** (`tob2025:theorem1`), "put simply": almost surely, for all large `k`, every optimal
solution of Weighted Quartet Consensus is a refinement of the tree of blobs. -/
theorem theorem1_optimal [Fintype V] [Fintype E] {N : RootedNetwork V E X} {θ : MetricData E} {ρ : ℝ}
    (hStd : StandardAssumptions N θ ρ) (hEx : External.AneEtAl2024.Exchangeability N θ ρ)
    (hNon : IsTQuartetNonanomalous N (nmscCF N θ ρ)) (hX : 4 ≤ Fintype.card X)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (G : ℕ → Ω → Finset (Finset X)) (hG : IsGeneTreeSample P N θ ρ G) :
    ∀ᵐ ω ∂P, ∃ K, ∀ k, K ≤ k → ∀ B, IsBinaryTree B →
      (∀ T, IsBinaryTree T → quartetScore (geneCount G k ω) T ≤ quartetScore (geneCount G k ω) B) →
      treeOfBlobs N ⊆ B := by
  sorry

/-- The constrained search space of ASTRAL (versions up to 3): binary trees whose splits all occur on
the first `k` gene trees. -/
def AstralSpace {Ω : Type*} (G : ℕ → Ω → Finset (Finset X)) (k : ℕ) (ω : Ω) (B : Finset (Finset X)) :
    Prop :=
  IsBinaryTree B ∧ ∀ A ∈ B, ∃ i < k, A ∈ unroot (G i ω)

/-- **Corollary of Theorem 1** (`tob2025:astral_corollary`), conditional on exchangeability: almost
surely, for all large `k`, every optimum of the score in ASTRAL's search space is a refinement of the
tree of blobs, since every split has positive probability under the NMSC. -/
theorem astral_corollary [Fintype V] [Fintype E] {N : RootedNetwork V E X} {θ : MetricData E} {ρ : ℝ}
    (hStd : StandardAssumptions N θ ρ) (hEx : External.AneEtAl2024.Exchangeability N θ ρ)
    (hNon : IsTQuartetNonanomalous N (nmscCF N θ ρ)) (hX : 4 ≤ Fintype.card X)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (G : ℕ → Ω → Finset (Finset X)) (hG : IsGeneTreeSample P N θ ρ G) :
    ∀ᵐ ω ∂P, ∃ K, ∀ k, K ≤ k → ∀ B, AstralSpace G k ω B →
      (∀ T, AstralSpace G k ω T → quartetScore (geneCount G k ω) T ≤ quartetScore (geneCount G k ω) B) →
      treeOfBlobs N ⊆ B := by
  sorry

end TOBQMC
