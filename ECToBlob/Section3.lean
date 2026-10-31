module

public import Basic.Phylogenetics.TreeSplits
public import Basic.Probability.IID
public import Mathlib.Order.Filter.AtTopBot.Basic

/-!
# ECToBlob §3: resolving the tree of blobs

Lemma 3.5, Theorem 3.1, Remark 3.2, Corollary 3.6, and the objective decompositions (3.2) and (3.3).
Equation (3.3) as printed overcounts quartets (E1 of the report): `equation3_3` is the repaired
identity, with the weights by block sizes, and the proof of Theorem 3.1 follows the paper's route
with these weights.
-/

@[expose] public noncomputable section

open Phylogenetics Phylogenetics.RootedNetwork Finset Filter Topology
open scoped Classical

namespace ECToBlob

variable {V E X : Type*} [Fintype X] [DecidableEq X] {N : RootedNetwork V E X}

/-- **Lemma 3.5** (`ecto:lem3_5`). If `x₀` simultaneously maximizes each of the `fᵢ`, it maximizes
their sum, and every maximizer of the sum maximizes each of the `fᵢ`. -/
theorem lemma3_5 {ι U : Type*} (t : Finset ι) (f : ι → U → ℝ) (x₀ : U)
    (h : ∀ i ∈ t, ∀ x, f i x ≤ f i x₀) :
    (∀ x, ∑ i ∈ t, f i x ≤ ∑ i ∈ t, f i x₀) ∧
      ∀ x₁, (∀ x, ∑ i ∈ t, f i x ≤ ∑ i ∈ t, f i x₁) → ∀ i ∈ t, ∀ x, f i x ≤ f i x₁ := by
  sorry

/-- The part `f_R` of the objective from the 4-taxon sets that the tree `TB` resolves. -/
def resolvedPart (TB : Finset (Finset X)) (w : QuartetTree X → ℝ) (T : Finset (Finset X)) : ℝ :=
  ∑ s, if (∃ r ∈ treesOn s.taxa, Displays TB r) ∧ Displays T s then w s else 0

/-- The part `f_m` of the objective from the 4-taxon sets with centre the multifurcation `P`. -/
def starPart (P : Finset (Finset X)) (w : QuartetTree X → ℝ) (T : Finset (Finset X)) : ℝ :=
  ∑ s, if InDistinctBlocks P s.taxa ∧ Displays T s then w s else 0

/-- **Equation (3.2)** (`ecto:eq3_2`): the objective is `f_R + ∑_m f_m`. -/
theorem equation3_2 {TB : Finset (Finset X)} (hTB : IsUnrootedTree TB) (w : QuartetTree X → ℝ)
    (T : Finset (Finset X)) :
    quartetScore w T = resolvedPart TB w T + ∑ P ∈ multifurcations TB, starPart P w T := by
  sorry

/-- The weight of a quartet tree in the repaired (3.3): the product of the sizes of the blocks of `P`
meeting its taxa. -/
def blockWeight (P : Finset (Finset X)) (s : QuartetTree X) : ℝ :=
  ∏ B ∈ P.filter fun B => (B ∩ s.taxa).Nonempty, (B.card : ℝ)

/-- **Equation (3.3)** (`ecto:eq3_3`), repaired (E1 of the report). The printed identity repeats a
quartet once for each choice of representatives of the blocks it does not use. Weighted by the
block sizes and divided by the product of all block sizes, the representative sum is `f_m`. A
representative tuple `x` chooses a taxon in each block. -/
theorem equation3_3 {P : Finset (Finset X)} (hdisj : ∀ B ∈ P, ∀ C ∈ P, B ≠ C → Disjoint B C)
    (hne : ∀ B ∈ P, B.Nonempty) (w : QuartetTree X → ℝ) (T : Finset (Finset X)) :
    (∏ B ∈ P, (B.card : ℝ)) * starPart P w T =
      ∑ x ∈ (univ : Finset ({B // B ∈ P} → X)).filter (fun x => ∀ B, x B ∈ B.val),
        ∑ s, if InDistinctBlocks P s.taxa ∧ Displays T s ∧ s.taxa ⊆ univ.image x then
            blockWeight P s * w s else 0 := by
  sorry

/-- **Theorem 3.1** (`ecto:thm3_1`). Consider weights `p` on quartet trees, the probabilities
of a gene tree distribution, such that

1. (`ecto:eq3_1`) if a cut edge of the network separates `a, b` from `c, d`, then
   `p_ab|cd > max(p_ac|bd, p_ad|bc)`;
2. replacing a taxon by one on the same side of a cut edge, with the other three on the other side,
   does not change `p`. By `pendantChainInvariant_cutExchangeable`, this follows from the condition
   as printed, that `p_xy|zw` is determined by the induced network but does not depend on its pendant
   chains of 2-blobs and edges leading to single taxa.

Then every unrooted tree maximizing the sum over its displayed quartet trees of `p` is a resolution
of the tree of blobs. The paper's `p` is a probability; only its nonnegativity is used. -/
theorem theorem3_1 (hN : N.IsPhylogenetic) (p : QuartetTree X → ℝ) (hp : ∀ s, 0 ≤ p s)
    (h₁ : ∀ s, Displays (treeOfBlobs N) s → ∀ r ∈ s.alternatives, p r < p s)
    (h₂ : CutExchangeable N p) {T : Finset (Finset X)} (hT : IsUnrootedTree T)
    (hmax : ∀ T', IsUnrootedTree T' → quartetScore p T' ≤ quartetScore p T) :
    treeOfBlobs N ⊆ T := by
  sorry

/-- **Remark 3.2** (`ecto:rem3_2`). If on each set of four taxa the weights are the probabilities of
the three resolved quartet trees, every maximizer is binary: a multifurcation can always be resolved
so as to increase the score. -/
theorem remark3_2 (p : QuartetTree X → ℝ) (hp : ∀ s, 0 ≤ p s)
    (hsum : ∀ q : Finset X, q.card = 4 → ∑ r ∈ treesOn q, p r = 1) {T : Finset (Finset X)}
    (hT : IsUnrootedTree T)
    (hmax : ∀ T', IsUnrootedTree T' → quartetScore p T' ≤ quartetScore p T) :
    IsBinaryTree T := by
  sorry

/-! ### The literal form of condition 2 -/

/-- The arcs of the network induced on `Y`: those ancestral to `Y` below its LSA. -/
def inducedArcs (N : RootedNetwork V E X) (Y : Set X) : Set E :=
  {e | e ∈ N.ancestralArcs Y ∧ ∃ v, N.IsLeastStableAncestor Y v ∧ N.graph.Reaches v (N.graph.source e)}

/-- `e`, with side `S`, is a cut edge of the network induced on `Y` separating exactly the taxon `x`. -/
def IsPendantCut (N : RootedNetwork V E X) (Y : Set X) (x : X) (e : E) (S : Set V) : Prop :=
  e ∈ inducedArcs N Y ∧ (∀ f ∈ inducedArcs N Y, N.graph.Crosses f S ↔ f = e) ∧
    ∀ y ∈ Y, N.leaf y ∈ S ↔ y = x

/-- The arcs of the induced network on `Y` that are not on the pendant chain leading to a taxon of
`Y`: what remains without the pendant chains of 2-blobs and edges. -/
def coreArcs (N : RootedNetwork V E X) (Y : Set X) : Set E :=
  {f | f ∈ inducedArcs N Y ∧ ¬ ∃ x ∈ Y, ∃ e S, IsPendantCut N Y x e S ∧
    (f = e ∨ (N.graph.source f ∈ S ∧ N.graph.target f ∈ S))}

/-- `v` is the vertex at which the pendant chain of the taxon `x` of `Y` attaches to the rest of the
network induced on `Y`. -/
def AttachesAt (N : RootedNetwork V E X) (Y : Set X) (x : X) (v : V) : Prop :=
  ∃ e S, IsPendantCut N Y x e S ∧ v ∉ S ∧ (N.graph.source e = v ∨ N.graph.target e = v) ∧
    ∀ e' S', IsPendantCut N Y x e' S' → ∀ u ∈ S', N.graph.Reaches N.root u → u ∈ S

/-- Condition 2 of Theorem 3.1 as printed, for a network with fixed numerical parameters: `p_xy|zw`
depends on the induced network on `x, y, z, w` only through what remains without its pendant chains,
and where those chains attach. It is stated for two quartet trees on sets of taxa of the same
network, for which the same arcs carry the same numerical parameters. -/
def PendantChainInvariant (N : RootedNetwork V E X) (p : QuartetTree X → ℝ) : Prop :=
  ∀ (s s' : QuartetTree X) (g : X → X), Set.InjOn g s.taxa →
    s'.val = s.val.image (fun B => B.image g) →
    coreArcs N (s.taxa : Set X) = coreArcs N (s'.taxa : Set X) →
    (∀ x ∈ s.taxa, ∀ v, AttachesAt N (s.taxa : Set X) x v ↔ AttachesAt N (s'.taxa : Set X) (g x) v) →
    p s = p s'

/-- The printed condition 2 implies the form used in `theorem3_1`: if a cut edge groups `a, a'` away
from `b, c, d`, then the induced networks on `a, b, c, d` and on `a', b, c, d` differ only in the
pendant chain to `a` or `a'`. -/
theorem pendantChainInvariant_cutExchangeable (hN : N.IsPhylogenetic) {p : QuartetTree X → ℝ}
    (h : PendantChainInvariant N p) : CutExchangeable N p := by
  sorry

/-! ### Empirical concordance factors -/

/-- Unrooted gene trees, resolved or not. -/
abbrev UnrootedGeneTree (X : Type*) [Fintype X] [DecidableEq X] :=
  {T : Finset (Finset X) // IsUnrootedTree T}

/-- What a gene tree contributes to the concordance factor of `s` (ECToBlob §2): `1` if it displays
`s`, and `1/3` if it does not resolve the taxa of `s`. -/
def geneContribution (T : Finset (Finset X)) (s : QuartetTree X) : ℝ :=
  if Displays T s then 1 else if ∀ r ∈ treesOn s.taxa, ¬ Displays T r then 1 / 3 else 0

/-- The concordance factor of a distribution on gene trees. -/
def expectedCF (dist : UnrootedGeneTree X → ℝ) (s : QuartetTree X) : ℝ :=
  ∑ G, dist G * geneContribution G.val s

/-- The empirical concordance factor of a sample of gene trees. -/
def empiricalCF {n : ℕ} (ω : Fin n → UnrootedGeneTree X) (s : QuartetTree X) : ℝ :=
  (∑ i, geneContribution (ω i).val s) / n

/-- **Corollary 3.6** (`ecto:cor3_6`). For `n` independent gene trees from a distribution
satisfying the assumptions of Theorem 3.1, with probability tending to one every tree optimal for the
Maximum Quartet Support criterion is a resolution of the tree of blobs. -/
theorem corollary3_6 (hN : N.IsPhylogenetic) (dist : UnrootedGeneTree X → ℝ)
    (hdist : (∀ G, 0 ≤ dist G) ∧ ∑ G, dist G = 1)
    (h₁ : ∀ s, Displays (treeOfBlobs N) s → ∀ r ∈ s.alternatives, expectedCF dist r < expectedCF dist s)
    (h₂ : CutExchangeable N (expectedCF dist)) :
    Tendsto (fun n => iidProb dist n fun ω =>
      ∀ T, IsUnrootedTree T →
        (∀ T', IsUnrootedTree T' → quartetScore (empiricalCF ω) T' ≤ quartetScore (empiricalCF ω) T) →
        treeOfBlobs N ⊆ T) atTop (𝓝 1) := by
  sorry

end ECToBlob
